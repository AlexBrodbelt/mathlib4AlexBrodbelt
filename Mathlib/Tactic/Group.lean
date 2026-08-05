module

public import Mathlib.Algebra.Group.Commutator  -- shake: keep (tactic dependency)
public import Mathlib.Algebra.Order.Sub.Basic  -- shake: keep (tactic dependency)
public import Mathlib.Tactic.FailIfNoProgress
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Util.Qq

/-!
# `group`

`group` normalizes expressions in a `Group`, allowing variables in the exponent, and closes goals
which are equalities between such expressions.
-/

public section

namespace Mathlib.Tactic.Group

open Lean Meta Mathlib Tactic AtomM Qq Elab.Tactic
open Mathlib.Tactic.Ring (RatCoeff ringCompute rcℕ ringCompare)
open Mathlib.Tactic.Ring.Common (ExSum Cache evalAdd evalNeg)

meta section

/-- `CommSemiring ℤ` / cache / coefficient normalizer for exponents (cf. `sℕ`, `Cache.nat`, `rcℕ`).
-/
def sℤ : Q(CommSemiring ℤ) := q(Int.instCommSemiring)
def cℤ : Cache sℤ :=
  { rα := some q(Int.instCommRing), dsα := none, czα := some q(Int.instCharZero) }
def rcℤ := ringCompute cℤ
/-- `CommRing ℤ` from `cℤ` (always present). -/
def rℤ : Q(CommRing ℤ) := cℤ.rα.get!

mutual

/-- `ExBase gα e` is a normalized base of a power `e ^ n` in a group. -/
inductive ExBase {u : Lean.Level} {α : Q(Type u)}
    (gα : Q(Group $α)) : (e : Q($α)) → Type
  /-- An atomic expression with atom id `id`. -/
  | atom {e} (id : ℕ) : ExBase gα e
  /-- A product of group elements, used as a base of a power. -/
  | prod {e} (va : ExProd gα e) : ExBase gα e

/-- `ExProd gα e` is a normalized product of powers in a group. -/
inductive ExProd {u : Lean.Level} {α : Q(Type u)}
    (gα : Q(Group $α)) : (e : Q($α)) → Type
  /-- The identity. -/
  | one : ExProd gα q(1)
  /-- A product `x ^ e * b`. Where `x` is stored as an `ExBase`, `e` is stored as an `ExSum` and
   `b` is stored as an `ExProd`. -/
  | mul {x b : Q($α)} {e : Q(ℤ)}:
    ExBase gα x → ExSum RatCoeff sℤ e → ExProd gα b → ExProd gα q($x ^ $e * $b)

end

variable {u : Lean.Level} {α : Q(Type u)} {gα : Q(Group $α)}


/--
The result of evaluating an (unnormalized) expression `e` into the type family `E`
(typically one of `ExProd` or `ExBase`) is a (normalized) element `expr`
and a representation `E e'` for it, and a proof of `e = expr`.
-/
structure Result {α : Q(Type u)} (E : Q($α) → Type*) (e : Q($α)) where
  /-- The normalized result. -/
  expr : Q($α)
  /-- The data associated to the normalization. -/
  val : E expr
  /-- A proof that the original expression is equal to the normalized result. -/
  proof : Q($e = $expr)

instance {α : Q(Type u)} {E : Q($α) → Type} {e : Q($α)} [Inhabited (Σ e, E e)] :
    Inhabited (Result E e) :=
  let ⟨e', v⟩ : Σ e, E e := default; ⟨e', v, default⟩

initialize registerTraceClass `Tactic.group

def evalAtom (e : Q($α)) : AtomM (Result (ExProd gα) e) :=
  withTraceNode `Tactic.group (fun _ => return m!"atom: {e}") do
    let (i, ⟨a', _⟩) ← addAtomQ e
    let ⟨_, va, pa⟩ ← Mathlib.Tactic.Ring.Common.eval rcℕ rcℤ cℤ q(1)
    return ⟨_, .mul (.atom (e := a') i) va .one, q(by rw [← «$pa», zpow_one, mul_one])⟩

mutual

/--
A total order on normalized expressions. This is not an `Ord` instance because it is heterogeneous.
-/
partial def ExBase.cmp {a b : Q($α)} :
    ExBase gα a → ExBase gα b → Ordering
  | .atom i, .atom j => compare i j
  | .atom .., .prod .. => .lt
  | .prod .., .atom .. => .gt
  | .prod a, .prod b => a.cmp b

partial def ExProd.cmp {a b : Q($α)} :
    ExProd gα a → ExProd gα b → Ordering
  | .one, .one => .eq
  | .mul (x := x₁) vx₁ ve₁ vt₁, .mul (x := x₂) vx₂ ve₂ vt₂ =>
    (vx₁.cmp vx₂).then (ve₁.cmp rcℕ ringCompare ve₂) |>.then (vt₁.cmp vt₂)
  | .one, .mul .. => .lt
  | .mul .., .one => .gt

end

variable {G : Type*} [Group G]

theorem zpow_zero_mul_one (a : G) : a ^ (0 : ℤ) * (1 : G) = 1 := by simp

theorem mul_zpow_add_overlap (a : G) (n m nm : ℤ) (c : G) (h : n + m = nm) :
    a ^ n * (a ^ m * c) = a ^ nm * c := by
  rw [← mul_assoc, ← zpow_add, h]

theorem mul_zpow_cancel (a : G) (n m : ℤ) (c : G) (h : n + m = 0) :
    a ^ n * (a ^ m * c) = c := by
  rw [← mul_assoc, ← zpow_add, h, zpow_zero, one_mul]

/--
`a ^ n * 1 = a ^ n`

`a ^ n * (a ^ m * c) = a ^ (n + m) * c`
-/
partial def evalExBaseMul {a b : Q($α)} (va : ExBase gα a) {n : Q(ℤ)}
    (vn : ExSum RatCoeff sℤ n) (vb : ExProd gα b) :
  AtomM (Result (ExProd gα) q($a ^ $n * $b)) :=
  withTraceNode `Tactic.group (fun _ => return m!"evalExBaseMul: {a} ^ {n} * {b}") do
    match va, vb with
    | _, .one =>
      withTraceNode `Tactic.group (fun _ => return m!"mul_one") do
        match vn with
        | .zero => return ⟨_, .one, q(zpow_zero_mul_one $a)⟩ -- `a ^ 0 * 1 = 1`
        | vn => return ⟨_, .mul va vn .one, q(rfl)⟩
    | va, .mul (x := x) (e := m) vx vm (b := c) vc =>
      if !(va.cmp vx == .eq) then
        withTraceNode `Tactic.group (fun _ => return m!"cons") do
          return ⟨_, .mul va vn (.mul vx vm vc), q(rfl)⟩
      else
        withTraceNode `Tactic.group (fun _ => return m!"combine exponents") do
          have : $x =Q $a := ⟨⟩
          let ⟨nm, vnm, pnm⟩ ← evalAdd rcℤ rcℕ vn vm
          match vnm with
          | .zero => return ⟨_, vc, q(mul_zpow_cancel $a $n $m $c $pnm)⟩ -- `a ^ n * a ^ m * c = c`
          | vnm => return ⟨_, .mul va vnm vc, q(mul_zpow_add_overlap $a $n $m $nm $c $pnm)⟩

/-
| .prod vc, .mul vx vm vd =>
      withTraceNode `Tactic.group (fun _ => return m!"prod") do
        let ⟨_, vn', _⟩ ← Mathlib.Tactic.Ring.Common.eval rcℕ rcℤ cℤ n
        let ⟨_, ve, _⟩ ← evalPow vc vn'
        let ⟨_, vf, _⟩ ← evalExBaseMul vx vm vd
        return ⟨_, .mul (.prod ve) vn vf, q(sorry)⟩
        -/

theorem mul_cons_congr (x : G) (n : ℤ) {c b d e : G} (h₁ : c * b = d) (h₂ : x ^ n * d = e) :
    (x ^ n * c) * b = e := by
  rw [mul_assoc, h₁, h₂]

/--
`1 * b = b`

`a * (x ^ n * b) = a * x ^ n * b`
-/
partial def evalMul {a b : Q($α)} (va : ExProd gα a) (vb : ExProd gα b) :
    AtomM (Result (ExProd gα) q($a * $b)) :=
  withTraceNode `Tactic.group (fun _ => return m!"evalMul: {a} * {b}") do
    match va with
    | .one =>
      return ⟨_, vb, q(one_mul _)⟩
    | .mul (x := x) (e := n) vx vn (b := c) vc =>
      let ⟨_, vd, pd⟩ ← evalMul vc vb
      let ⟨_, ve, pe⟩ ← evalExBaseMul vx vn vd
      return ⟨_, ve, q(mul_cons_congr $x $n $pd $pe)⟩

theorem inv_zpow_mul_one (x : G) (n n' : ℤ) (h : -n = n') :
    (x ^ n * (1 : G))⁻¹ = x ^ n' * 1 := by
  rw [mul_one, ← zpow_neg, h, mul_one]

theorem inv_mul_eq_one_zpow (x b : G) (n n' : ℤ) (hb : b⁻¹ = 1) (hn : -n = n') :
    (x ^ n * b)⁻¹ = x ^ n' * 1 := by
  rw [inv_eq_one.mp hb, inv_zpow_mul_one x n n' hn]

theorem inv_mul_mul (x : G) (n : ℤ) (b y : G) (m : ℤ) (d f e : G)
    (hb : b⁻¹ = y ^ m * d) (hf : (x ^ n * (1 : G))⁻¹ = f) (he : d * f = e) :
    (x ^ n * b)⁻¹ = y ^ m * e := by
  rw [mul_inv_rev, ← mul_one (x ^ n), hf, hb, mul_assoc, he]

/--
1⁻¹ = 1

(x ^ n * 1)⁻¹ = x ^ (-n) * 1

(x ^ n * b)⁻¹ = b⁻¹ * (x ^ (-n) * 1)

(x ^ n * b)^(-n) = (x ^ n * b)⁻¹ ^ n
-/
partial def evalInv {a : Q($α)} (va : ExProd gα a) :
    AtomM (Result (ExProd gα) q($a⁻¹)) :=
  withTraceNode `Tactic.group (fun _ => return m!"evalInv: {a}⁻¹") do
    match va with
    -- `1⁻¹ = 1`
    | .one =>
      return ⟨_ , .one, q(inv_one)⟩
    -- `(x ^ n * 1)⁻¹ = x ^ (-n) * 1`
    | .mul (x := x) (e := n) vx vn .one =>
      let ⟨n', vneg, pneg⟩ ← evalNeg rcℤ rℤ vn
      return ⟨_, .mul vx vneg .one, q(inv_zpow_mul_one $x $n $n' $pneg)⟩
    -- `(x ^ n * b)⁻¹ = b⁻¹ * (x ^ (-n) * 1)`
    | .mul (x := x) (e := n) vx vn (b := b) vb =>
      let ⟨c, vc, pc⟩ ← evalInv vb
      match vc with
      | .one =>
        let ⟨n', vneg, pneg⟩ ← evalNeg rcℤ rℤ vn
        return ⟨_, .mul vx vneg .one, q(inv_mul_eq_one_zpow $x $b $n $n' $pc $pneg)⟩
      | .mul (x := y) (e := m) vy vm (b := d) vd =>
        let ⟨f, vf, pf⟩ ← evalInv (.mul vx vn .one)
        let ⟨e, ve, pe⟩ ← evalMul vd vf
        return ⟨_, .mul vy vm ve, q(inv_mul_mul $x $n $b $y $m $d $f $e $pc $pf $pe)⟩

theorem zpow_neg_of (a b c : G) (n m : ℤ) (hn : -n = m) (hb : a⁻¹ = b) (hc : b ^ m = c) :
    a ^ n = c := by
  rw [← neg_neg n, show -n = m from hn, ← inv_zpow', hb, hc]

theorem zpow_zpow_mul_one (x : G) (k n kn : ℤ) (h : k * n = kn) :
    (x ^ k * (1 : G)) ^ n = x ^ kn * 1 := by
  simp [← zpow_mul, h]

partial def evalPowCycle {a : Q($α)} (va : ExProd gα a) (n : Q(ℤ)) :
    AtomM (Result (ExProd gα) q($a ^ $n)) :=
  withTraceNode `Tactic.group (fun _ => return m!"evalPowCycle: {a} ^ {n}") do
    return ⟨_, va, q(sorry)⟩

/--
( · )^0 = 1

( · )^1 = ( · )

( · )^(- n) = ( · )⁻¹ ^ n

(c * a * b)^n = c * (a * b * c)^(n - 1) * a * b
-/
partial def evalPow {a : Q($α)} {n : Q(ℤ)} (va : ExProd gα a) (vn : ExSum RatCoeff sℤ n) :
    AtomM (Result (ExProd gα) q($a ^ $n)) :=
  withTraceNode `Tactic.group (fun _ => return m!"evalPow: {a} ^ {n}") do
    match vn, va with
    -- `a ^ 0 = 1`
    | .zero, _ => return ⟨_, .one, q(zpow_zero _)⟩
    -- `1 ^ n = 1`
    | _, .one => return ⟨_, .one, q(one_zpow _)⟩
    | vn, va =>
      -- `(a)^(-m) = (a⁻¹)^m` when the leading coefficient of the exponent is negative
      let leadingNeg : Bool := match vn with
        | .add vp _ =>
          decide <|
            (Mathlib.Tactic.Ring.Common.ExProd.coeff (bt := RatCoeff) (sα := sℤ) vp).2.value < 0
        | .zero => false
      if leadingNeg then
        withTraceNode `Tactic.group (fun _ => return m!"neg exponent") do
          let ⟨m, vm, pm⟩ ← evalNeg rcℤ rℤ vn
          let ⟨b, vb, pb⟩ ← evalInv va
          let ⟨c, vc, pc⟩ ← evalPow vb vm
          return ⟨_, vc, q(zpow_neg_of $a $b $c $n $m $pm $pb $pc)⟩
      else
        match va with
        -- `(x ^ k) ^ n = x ^ (k * n)`
        | .mul (x := x) vx (e := k) vk .one =>
          let ⟨kn, vkn, pkn⟩ ← Mathlib.Tactic.Ring.Common.evalMul rcℤ rcℕ vk vn
          return ⟨_, .mul vx vkn .one, q(zpow_zpow_mul_one $x $k $n $kn $pkn)⟩
        -- `(b * a * c) ^ n`
        | va => evalPowCycle va n

theorem npow_eq (a a' c : G) (n : ℕ) (n' : ℤ)
    (ha : a = a') (hn : (n : ℤ) = n') (hc : a' ^ n' = c) : a ^ n = c := by
  rw [← zpow_natCast, ha, hn, hc]

/-- A proof of `(e : ℤ)` equal to the integer reading of a `ℕ` exponent expression,
interpreting nat subtraction as integer subtraction when both sides are definitionally
equal (e.g. `n - n`). -/
partial def natExpToInt_eq (e : Q(ℕ)) : MetaM ((eℤ : Q(ℤ)) × Q(($e : ℤ) = $eℤ)) := do
  match e with
  | ~q($a + $b) =>
    let ⟨aℤ, pa⟩ ← natExpToInt_eq a; let ⟨bℤ, pb⟩ ← natExpToInt_eq b
    pure ⟨q($aℤ + $bℤ), q(by rw [Int.natCast_add, «$pa», «$pb»])⟩
  | ~q($a * $b) =>
    let ⟨aℤ, pa⟩ ← natExpToInt_eq a; let ⟨bℤ, pb⟩ ← natExpToInt_eq b
    pure ⟨q($aℤ * $bℤ), q(by rw [Int.natCast_mul, «$pa», «$pb»])⟩
  | ~q($a - $b) =>
    let ⟨aℤ, pa⟩ ← natExpToInt_eq a
    if a.equal b then
      have : $a =Q $b := ⟨⟩
      -- Use `aℤ - aℤ` so both sides rewrite with the same proof `pa`.
      pure ⟨q($aℤ - $aℤ),
        q(by rw [Int.natCast_sub (Nat.le_refl _), «$pa»])⟩
    else
      -- Fall back to the (possibly truncated) nat cast; ring may still simplify.
      pure ⟨q(($e : ℤ)), q(rfl)⟩
  | ~q($a ^ $b) =>
    let ⟨aℤ, pa⟩ ← natExpToInt_eq a
    pure ⟨q($aℤ ^ $b), q(by rw [Int.natCast_pow, «$pa»])⟩
  | _ => pure ⟨q(($e : ℤ)), q(rfl)⟩

partial def eval (e : Q($α)) : AtomM (Result (ExProd gα) e) := Lean.withIncRecDepth do
  withTraceNode `Tactic.group (fun _ => return m!"eval: {e}") do
    match e with
    | ~q(1) => return ⟨_, .one, q(rfl)⟩
    | _ =>
      let els := do
        evalAtom e
      let .const n _ := (← withReducible <| whnf e).getAppFn | els
      match n with
      | ``HMul.hMul | ``Mul.mul => match e with
        | ~q($a * $b) =>
          withTraceNode `Tactic.group (fun _ => return m!"mul") do
            let ⟨_, va, pa⟩ ← eval a
            let ⟨_, vb, pb⟩ ← eval b
            let ⟨_, vc, p⟩ ← evalMul va vb
            pure ⟨_, vc, q(by rw [← «$p», ← «$pb» , ← «$pa»])⟩
        | _ => els
      | ``HPow.hPow | ``Pow.pow => match e with
        | ~q($a ^ ($n : ℤ)) =>
          withTraceNode `Tactic.group (fun _ => return m!"pow ℤ") do
            let ⟨_, va, pa⟩ ← eval a
            let ⟨_, vn, pn⟩ ← Mathlib.Tactic.Ring.Common.eval rcℕ rcℤ cℤ n
            let ⟨_, vc, pc⟩ ← evalPow va vn
            pure ⟨_, vc, q(by rw [← «$pc», ← «$pn», ← «$pa»])⟩
        | ~q($a ^ ($n : ℕ)) =>
          withTraceNode `Tactic.group (fun _ => return m!"pow ℕ") do
            let ⟨a', va, pa⟩ ← eval a
            let ⟨nℤ, pnat⟩ ← natExpToInt_eq n
            let ⟨n', vn, pn⟩ ← Mathlib.Tactic.Ring.Common.eval rcℕ rcℤ cℤ nℤ
            let ⟨c, vc, pc⟩ ← evalPow va vn
            pure ⟨_, vc, q(npow_eq $a $a' $c $n $n' $pa (Eq.trans «$pnat» «$pn») $pc)⟩
        | _ => els
      | ``Inv.inv => match e with
        | ~q($a⁻¹) =>
          withTraceNode `Tactic.group (fun _ => return m!"inv") do
            let ⟨_, va, pa⟩ ← eval a
            let ⟨_, vc, pc⟩ ← evalInv va
            pure ⟨_, vc, q(by rw [← «$pc», ← «$pa»])⟩
        | _ => els
      | _ => els


/-- Frontend of `group`: attempt to close a goal `g`, assuming it is an equality in a group. -/
def proveEq (g : MVarId) : AtomM Unit := do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
    | throwError "group failed: not an equality"
  let ⟨v, α⟩ ← getLevelQ' α
  have α : Q(Type v) := α
  let gα ←
    try Except.ok <$> synthInstanceQ q(Group $α)
    catch e => pure (.error e)
  have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
  let eq ← match gα with
  | .ok gα => groupCore gα e₁ e₂
  | .error e => throw e
  g.assign eq
where
  /-- The core of `proveEq` takes expressions `e₁ e₂ : α` where `α` is a `Group`,
  and returns a proof that they are equal (or fails). -/
  groupCore {v : Level} {α : Q(Type v)} (gα : Q(Group $α))
      (e₁ e₂ : Q($α)) : AtomM Q($e₁ = $e₂) := do
    profileitM Exception "group" (← getOptions) do
      withTraceNode `Tactic.group (fun _ => return m!"group: {e₁} =?= {e₂}") do
        let ⟨a, va, pa⟩ ← withTraceNode `Tactic.group (fun
          | .ok r => return m!"LHS ==> {r.expr}"
          | .error _ => return m!"LHS") do
          eval (gα := gα) e₁
        let ⟨b, vb, pb⟩ ← withTraceNode `Tactic.group (fun
          | .ok r => return m!"RHS ==> {r.expr}"
          | .error _ => return m!"RHS") do
          eval (gα := gα) e₂
        unless va.cmp vb == .eq do
          let g ← mkFreshExprMVar q($a = $b)
          throwError "group failed, group expressions not equal\n{g.mvarId!}"
        have : $a =Q $b := ⟨⟩
        return q(Eq.trans «$pa» (Eq.symm «$pb»))

/--
`group` solves the goal when it is an equality in a *group*,
allowing variables in the exponent.

This version of `group` fails if the target is not an equality.

* `group!` uses a more aggressive reducibility setting to determine equality of atoms.
* Use `set_option trace.Tactic.group true` to see the evaluation trace
-/
elab (name := group) "group" tk:"!"? : tactic => liftMetaMAtMain fun g ↦ do
  AtomM.run (if tk.isSome then .default else .reducible) (proveEq g)

@[tactic_alt group] macro "group!" : tactic => `(tactic| group !)


example {G : Type*} [Group G] (a _b _c : G) : a = a := by group

-- `sudo` is needed in the same file that registers the trace class via `meta section`.
sudo set_option trace.Tactic.group true in
example {G : Type*} [Group G] (a _b _c : G) : a * a = a^2 := by group

example {G : Type*} [Group G] (a _b _c : G) (n : ℤ) : a * a⁻¹ * a * a ^ n = a ^ (n + 1) := by group

sudo set_option trace.Tactic.group true in
example {G : Type*} [Group G] (a _b _c : G) : a * a⁻¹ = 1 := by group

example {G : Type*} [Group G] (a b c : G) : a * a * b * c^2 = a^2 * b * c ^ 2 := by group

example {G : Type*} [Group G] (a b c : G) : a ^ 2 * a * b * c^2 = a^3 * b * c ^ 2 := by group

example {G : Type*} [Group G] (a _b _c : G) (n m : ℤ) :
    a * a⁻¹ * a ^ m * a ^ m * a ^ n = a ^ (m * 2 + n) := by
  group

example {G : Type*} [Group G] (n m : ℕ) (a : G) : a^n*a^m = a^(n+m) := by group

example {G : Type*} [Group G] (a _b _c : G) : a ^ (-2 : ℤ) * a = a⁻¹ := by group

example {G : Type*} [Group G] (n : ℕ) (a : G) : a^(n-n) = 1 := by group



-- (a⁻¹ * b * c * c⁻¹ * a) ^ 300 -- cycling happens when the power has been reached
--  a⁻¹ * b ^ 300 * a

-- (c * a * b)^300 -> c * (a * b * c)^299 * a * b <- c * (a * b * c)^300 * c⁻¹

-- ((a * b^2) * c * (a * b^2)⁻¹)^300
-- .one = 1
-- .mul va q(1) .one = a
-- .mul vb q(1) (.mul va q(1) .one) = b * a
-- .mul a q(-1) (.mul vb q(1) (.mul va q(1) .one)) = a⁻¹ * b * a
-- .mul (.prod (.mul a q(-1) (.mul vb q(1) (.mul va q(1) .one)))) q(300) .one = (a⁻¹ * b * a) ^ 300 * 1

-- ((b * c)^3 * (a * b)^3)^n = (b * c)^3 * ((a * b)^3 * (b * c)^3) ^ (n - 1) * (a * b)^3

section Test

open Lean Qq Mathlib.Tactic.Group in
/-- info: false -/
#guard_msgs in
#eval show MetaM Bool from do
  -- A concrete (but only syntactic) setup: `α := ℤ` and a placeholder `Group ℤ` instance.
  -- `ExBase.eq`/`ExProd.eq` only inspect the stored structure, so the instance is never used.
  let gα : Q(Group ℤ) ← mkFreshExprMVarQ q(Group ℤ)
  have a : Q(ℤ) := q(0)
  have b : Q(ℤ) := q(1)
  let atomA : ExBase gα a := .atom 0
  let atomB : ExBase gα b := .atom 0
  -- let atomC : ExBase gα b := .atom 1

  -- atoms compare by id, independent of the (syntactic) base expression
  let atomsOk := atomA.cmp atomB ==.eq && !(atomA.cmp atomB == .eq)
  -- `.one` only equals `.one`
  -- let oneOk := (ExProd.one (gα := gα)).eq .one && !prodA0.eq .one && !ExProd.eq .one prodA0
  -- `.mul` compares base, exponent and tail componentwise
  -- let mulOk := prodA0.eq prodB0 && !(prodA0.eq prodB1) && !(prodB0.eq prodB0')

  return atomsOk

end Test

end

end Mathlib.Tactic.Group
