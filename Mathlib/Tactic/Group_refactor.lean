module

public import Mathlib.Algebra.Group.Commutator  -- shake: keep (tactic dependency)
public import Mathlib.Algebra.Order.Sub.Basic  -- shake: keep (tactic dependency)
public import Mathlib.Tactic.FailIfNoProgress
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Ring.Common
import Mathlib.Util.Qq

open Lean Meta Mathlib Tactic AtomM Qq Elab.Tactic
open Mathlib.Tactic.Ring (RatCoeff ringCompute rcℕ ringCompare)
open Mathlib.Tactic.Ring.Common (ExSum mkCache evalAdd evalNeg)

section Group

/-- The canonical `CommSemiring ℤ` instance used to normalize integer exponents. -/
meta def sℤ : Q(CommSemiring ℤ) := q(Int.instCommSemiring)

mutual

/-- `ExBase BaseType gα e` stores the structure of a normalized expression `e`, which appears
as the base of an exponent expression `e^n`.
-/
meta inductive ExBase {u : Lean.Level} {α : Q(Type u)}
    (gα : Q(Group $α)) : (e : Q($α)) → Type
  /--
  An atomic expression `e` with id `id`.

  Atomic expressions are those which a `group`-like tactic cannot parse any further.
  For instance, `a + (a % b)` has `a` and `(a % b)` as atoms.
  The `ring1` tactic does not normalize the subexpressions in atoms, but `ring_nf` does.

  Atoms in fact represent equivalence classes of expressions, modulo definitional equality.
  The field `index : ℕ` should be a unique number for each class,
  while `e : Q($α)` contains a representative of this class.
  -/
  | atom {e} (id : ℕ) : ExBase gα e
  -- /-- A product of group elements. -/
  | prod {e} (va : ExProd gα e) : ExBase gα e



/-- `ExProd BaseType gα e` stores the structure of a normalized monomial expression `e`.
A monomial here is a product of powers of `ExBase` expressions, terminated by a (nonzero) constant
coefficient. The data of the constant coefficient is stored in the `BaseType`. -/
meta inductive ExProd {u : Lean.Level} {α : Q(Type u)}
    (gα : Q(Group $α)) : (e : Q($α)) → Type
  /-- A coefficient `value`, which must not be `0`. `e` is a raw rat cast.
  If `value` is not an integer, then `hyp` should be a proof of `(value.den : α) ≠ 0`. -/
  | one : ExProd gα q(1)
  /-- A product `x ^ e * b` is a monomial if `b` is a monomial. Here `x` is an `ExBase`
  and `e` is an `ExProdNat` representing a monomial expression in `ℕ` (it is a monomial instead of
  a polynomial because we eagerly normalize `x ^ (a + b) = x ^ a * x ^ b`.)
  -/
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


meta section

initialize registerTraceClass `Tactic.group

/-- Normalize an integer exponent `e : ℤ` with the `ring` normalizer, returning the canonical
form `e'`, its normalized `ExSum` structure, and a proof `e = e'`. -/
def normExp (e : Q(ℤ)) :
    AtomM ((e' : Q(ℤ)) × ExSum RatCoeff sℤ e' × Q($e = $e')) := do
  let c ← mkCache sℤ
  let ⟨e', ve, pf⟩ ← Mathlib.Tactic.Ring.Common.eval rcℕ (ringCompute c) c e
  return ⟨e', ve, pf⟩

/-- A total order on normalized integer exponents, via the `ring` comparator. -/
def cmpExp {a b : Q(ℤ)} (va : ExSum RatCoeff sℤ a) (vb : ExSum RatCoeff sℤ b) : Ordering :=
  va.cmp rcℕ ringCompare vb

/-- Return `true` if the normalized exponent is `0`. -/
def isZeroExp {a : Q(ℤ)} : ExSum RatCoeff sℤ a → Bool
  | .zero => true
  | _ => false

def evalAtom (e : Q($α)) : AtomM (Result (ExProd gα) e) :=
  withTraceNode `Tactic.group (fun _ => return m!"atom: {e}") do
    let (i, ⟨a', _⟩) ← addAtomQ e
    let ⟨_, va, pa⟩ ← normExp q(1)
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
    (vx₁.cmp vx₂).then (cmpExp ve₁ ve₂) |>.then (vt₁.cmp vt₂)
  | .one, .mul .. => .lt
  | .mul .., .one => .gt

end



mutual

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
        if isZeroExp vn then
          return ⟨_, .one, q(sorry)⟩ -- `a ^ 0 * 1 = 1`
        else
          return ⟨_, .mul va vn .one, q(rfl)⟩
    | .atom .., .mul (x := x) vx vm vc =>
      if !(va.cmp vx == .eq) then
        withTraceNode `Tactic.group (fun _ => return m!"cons") do
          return ⟨_, .mul va vn (.mul vx vm vc), q(sorry)⟩
      else
        withTraceNode `Tactic.group (fun _ => return m!"combine exponents") do
          have : $x =Q $a := ⟨⟩
          let c ← mkCache sℤ
          let ⟨_, vnm, _⟩ ← evalAdd (ringCompute c) rcℕ vn vm
          if isZeroExp vnm then
            return ⟨_, vc, q(sorry)⟩ -- `a ^ n * a ^ (-n) * c = c`
          else
            return ⟨_, .mul va vnm vc, q(sorry)⟩
    | .prod vc, .mul vx vm vd =>
      withTraceNode `Tactic.group (fun _ => return m!"prod") do
        let ⟨_, ve, _⟩ ← evalPow vc n
        let ⟨_, vf, _⟩ ← evalExBaseMul vx vm vd
        return ⟨_, .mul (.prod ve) vn vf, q(sorry)⟩


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
    | .mul vx vn vc =>
      let ⟨_, vd, _⟩ ← evalMul vc vb
      let ⟨_, ve, _⟩ ← evalExBaseMul vx vn vd
      return ⟨_, ve, q(sorry)⟩

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
    | .mul vx vn .one =>
      let c ← mkCache sℤ
      let some rα := c.rα | failure
      let ⟨_, vneg, _⟩ ← evalNeg (ringCompute c) rα vn
      return ⟨_, .mul vx vneg .one, q(sorry)⟩
    -- `(x ^ n * b)⁻¹ = b⁻¹ * (x ^ (-n) * 1)`
    | .mul vx vn vb =>
      let ⟨_, vc, _⟩ ← evalInv vb
      match vc with
      | .one =>
        let c ← mkCache sℤ
        let some rα := c.rα | failure
        let ⟨_, vneg, _⟩ ← evalNeg (ringCompute c) rα vn
        return ⟨_, .mul vx vneg .one, q(sorry)⟩
      | .mul vy vm vd =>
        let ⟨_, vf, _⟩ ← evalInv (.mul vx vn .one)
        let ⟨_, ve, _⟩ ← evalMul vd vf
        return ⟨_, .mul vy vm ve, q(sorry)⟩


/--
( · )^0 = 1

( · )^1 = ( · )

( · )^(- n) = ( · )⁻¹ ^ n

(c * a * b)^n = c * (a * b * c)^(n - 1) * a * b
-/
partial def evalPow {a : Q($α)} (va : ExProd gα a) (n : Q(ℤ)) :
    AtomM (Result (ExProd gα) q($a ^ $n)) :=
  withTraceNode `Tactic.group (fun _ => return m!"evalPow: {a} ^ {n}") do
    match va, n with
    -- `a ^ 0 = 1`
    | _, ~q(0) => return ⟨_, .one, q(zpow_zero _)⟩
    -- `a ^ 1 = a`
    | va, ~q(1) =>
      have n_eq_one : $n =Q 1 := ⟨⟩
      return ⟨_, va, q(sorry)⟩
    -- `1 ^ n = 1`
    | .one, _ => return ⟨_, .one, q(one_zpow _)⟩
    -- `(a)^(-m) = (a⁻¹)^m`
    | .mul vx vk vb, ~q(-$m) =>
      withTraceNode `Tactic.group (fun _ => return m!"neg exponent") do
        let ⟨_, vc, _⟩ ← evalInv (.mul vx vk vb)
        let ⟨_, vd, _⟩ ← evalPow vc m
        return ⟨_, vd, q(sorry)⟩
    -- `(x ^ k) ^ n = x ^ (k * n)`
    | .mul vx vk .one, _ =>
      let ⟨_, vn, _⟩ ← normExp n
      let c ← mkCache sℤ
      let ⟨_, vkn, _⟩ ← Mathlib.Tactic.Ring.Common.evalMul (ringCompute c) rcℕ vk vn
      return ⟨_, .mul vx vkn .one, q(sorry)⟩
    -- `(b * a * c) ^ n`
    | va, _ => evalPowCycle va n



partial def evalPowCycle {a : Q($α)} (va : ExProd gα a) (n : Q(ℤ)) :
    AtomM (Result (ExProd gα) q($a ^ $n)) :=
  withTraceNode `Tactic.group (fun _ => return m!"evalPowCycle: {a} ^ {n}") do
    return ⟨_, va, q(sorry)⟩

end


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
            let ⟨_, vc, pc⟩ ← evalPow va n
            pure ⟨_, vc, q(by rw [← «$pc», ← «$pa»])⟩
        | ~q($a ^ ($n : ℕ)) =>
          withTraceNode `Tactic.group (fun _ => return m!"pow ℕ") do
            let ⟨_, va, pa⟩ ← eval a
            let ⟨_, vc, pc⟩ ← evalPow va q((($n : ℤ)))
            pure ⟨_, vc, q(by rw [← «$pc», ← «$pa», zpow_natCast])⟩
        | _ => els
      | ``Inv.inv => match e with
        | ~q($a⁻¹) =>
          withTraceNode `Tactic.group (fun _ => return m!"inv") do
            let ⟨_, va, pa⟩ ← eval a
            let ⟨_, vc, pc⟩ ← evalInv va
            pure ⟨_, vc, q(by rw [← «$pc», ← «$pa»])⟩
        | _ => els
      | _ => els


/-- Frontend of `group1`: attempt to close a goal `g`, assuming it is an equality in a group. -/
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
  groupCore {v : Level} {α : Q(Type v)} (gα : Q(CommSemiring $α))
      (e₁ e₂ : Q($α)) : AtomM Q($e₁ = $e₂) := do
    profileitM Exception "group" (← getOptions) do
      withTraceNode `Tactic.group (fun _ => return m!"group1: {e₁} =?= {e₂}") do
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
        return q(sorry)

end
/--
`group1` solves the goal when it is an equality in a *group*,
allowing variables in the exponent.

This version of `group` fails if the target is not an equality.

* `group1!` uses a more aggressive reducibility setting to determine equality of atoms.
* Use `set_option trace.Tactic.group true` to see the evaluation trace
-/
elab (name := group1) "group1" tk:"!"? : tactic => liftMetaMAtMain fun g ↦ do
  AtomM.run (if tk.isSome then .default else .reducible) (proveEq g)

@[tactic_alt group1] macro "group1!" : tactic => `(tactic| group1 !)


end Group

example {G : Type*} [Group G] (a b c : G) : a = a := by group1

-- `sudo` is needed in the same file that registers the trace class via `meta section`.
sudo set_option trace.Tactic.group true in
example {G : Type*} [Group G] (a b c : G) : a * a = a^2 := by group1

example {G : Type*} [Group G] (a b c : G) (n : ℤ) : a * a⁻¹ * a * a ^ n = a ^ (n + 1) := by group1

sudo set_option trace.Tactic.group true in
example {G : Type*} [Group G] (a b c : G) : a * a⁻¹ = 1 := by group1

example {G : Type*} [Group G] (a b c : G) : a * a * b * c^2 = a^2 * b * c ^ 2 := by group1

example {G : Type*} [Group G] (a b c : G) : a ^ 2 * a * b * c^2 = a^3 * b * c ^ 2 := by group1

example {G : Type*} [Group G] (a b c : G) (n m : ℤ) :
    a * a⁻¹ * a ^ m * a ^ m * a ^ n = a ^ (m * 2 + n) := by
  group1



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

open Lean Qq in
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
