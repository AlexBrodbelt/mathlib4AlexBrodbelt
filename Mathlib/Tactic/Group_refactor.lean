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

section Group



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
  -- /-- A sum of monomials. -/
  -- | prod {e} (_ : ExProd gα e) : ExBase gα e


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
  | mul {x : Q($α)} {b : Q($α)} :
    ExBase gα x → (e : Q(ℤ)) → ExProd gα b → ExProd gα q($x ^ $e * $b)



-- /-- `ExSum BaseType gα e` stores the structure of a normalized polynomial expression `e`, which is
-- a sum of monomials. -/
-- meta inductive ExSum {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) → Type)
--     (gα : Q(CommSemiring $α)) : (e : Q($α)) → Type
--   /-- Zero is a polynomial. `e` is the expression `0`. -/
--   | zero : ExSum BaseType gα q(0 : $α)
--   /-- A sum `a + b` is a polynomial if `a` is a monomial and `b` is another polynomial. -/
--   | add {a b : Q($α)} :
--     ExProd BaseType gα a → ExSum BaseType gα b → ExSum BaseType gα q($a + $b)

end

variable {u : Lean.Level} {α : Q(Type u)} {gα : Q(Group $α)}


/--
The result of evaluating an (unnormalized) expression `e` into the type family `E`
(typically one of `ExSum`, `ExProd`, `ExBase` or `BaseType`) is a (normalized) element `e'`
and a representation `E e'` for it, and a proof of `e = e'`.
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

def evalAtom (e : Q($α)) : AtomM (Result (ExProd gα) e) := do
  let (i, ⟨a', _⟩) ← addAtomQ e
  return ⟨_, .mul (.atom  (e := a') i) q(1) .one, q(by simp; rfl)⟩

partial def ExBase.eq {a b : Q($α)} : ExBase gα a → ExBase gα b → Bool
  | .atom i, .atom j => i == j

partial def ExProd.eq {a b : Q($α)} : ExProd gα a → ExProd gα b → Bool
  | .one, .one => true
  | .one, .mul _ _ _ => false
  | .mul _ _ _, .one => false
  | .mul x₁ m₁ b₁, .mul x₂ m₂ b₂ => x₁.eq x₂ && m₁ == m₂ && b₁.eq b₂

/--
a ^ n * 1 = a ^ n

a ^ n * (a ^ m * c) = a ^ (n + m) * c
-/
def evalExBaseMul {a b : Q($α)} (va : ExBase gα a) (n : Q(ℤ)) (vb : ExProd gα b) :
  AtomM (Result (ExProd gα) q($a ^ $n * $b)) := do
  match vb with
  | .one =>
    return ⟨_, .mul va n .one, q(rfl)⟩
  | .mul (x := x) vx m vc =>
    if !(va.eq vx) then
      return ⟨_, .mul va n (.mul vx m vc), q(rfl)⟩
    else
      have : $x =Q $a := ⟨⟩
      return ⟨_, .mul va q($n + $m) vc, q(by simp [zpow_add, mul_assoc]; rfl)⟩

/--
1 * b = b

a * (x ^ n * b) = a * x ^ n * b
-/
def evalMul {a b : Q($α)} (va : ExProd gα a)
  (vb : ExProd gα b) : AtomM (Result (ExProd gα) q($a * $b)) := do
  match va with
  | .one =>
    return ⟨_, vb, q(one_mul _)⟩
  | .mul (x := x) vx n (b := c) vc =>
    let ⟨d, vd, pd⟩ ← (evalMul vc vb)
    let ⟨e, ve, pe⟩ ← evalExBaseMul vx n vd
    return ⟨_, ve, q(by rw [← «$pe», ← «$pd», mul_assoc])⟩

/--
1⁻¹ = 1

(x ^ n * 1)⁻¹ = x ^ (-n) * 1

(x ^ n * b)⁻¹ = b⁻¹ * (x ^ (-n) * 1)
-/
def evalInv {a : Q($α)} (va : ExProd gα a) : AtomM (Result (ExProd gα) q($a⁻¹)) := do
  match va with
  | .one =>
    return ⟨_ , .one, q(inv_one)⟩
  | .mul (x := x) vx n .one =>
    return ⟨_, .mul vx q(-$n) .one, q(by rw [mul_one, mul_one, zpow_neg])⟩
  | .mul (x := x) vx n (b := b) vb =>
    let ⟨_, vc, pc⟩ ← evalInv vb
    match vc with
    | .one =>
      return ⟨_, .mul vx q(-$n) .one, q(by rw [mul_inv_rev, «$pc», one_mul, zpow_neg, mul_one])⟩
    | .mul (x := y) vy m (b := d) vd =>
      let ⟨_, vf, pf⟩ ← evalInv (.mul vx n .one)
      let ⟨_, ve, pe⟩ ← evalMul vd vf
      return ⟨
        _,
        .mul vy m ve,
        q(by rw [mul_inv_rev, «$pc», ← «$pe», ← mul_one («$x» ^ «$n»), «$pf», mul_assoc])⟩

/--
( · )^0 = 1

( · )^1 = ( · )

( · )^(- n) = ( · )⁻¹ ^ n
-/
def evalPow {a : Q($α)} (va : ExProd gα a) (n : Q(ℤ)) : AtomM (Result (ExProd gα) q($a ^ $n)) := do
  match va, n with
  | _, ~q(0) => return ⟨_, .one, q(zpow_zero _)⟩
  | va, ~q(1) =>
    have n_eq_one : $n =Q 1 := ⟨⟩
    return ⟨_, va, q(by rw [«$n_eq_one», zpow_one])⟩
  | .one, _ => return ⟨_, .one, q(one_zpow _)⟩
  -- need to check if it is a literal or if it is a variable
  | .mul vx k vb, ~q(-$m) =>
    let ⟨c, vc, pc⟩ ← evalInv (.mul vx k vb)
    -- convert to a positive power
    let ⟨d, vd, pd⟩ ← evalPow vc q(-$n)
    return ⟨_, vd, q(sorry)⟩
  | .mul vx k vb, ~q($n) => sorry
  -- need to feed in (a ^ -$n)⁻¹ to `evalInv`
  --   let ⟨c, vc, pc⟩ ← evalInv a z
  -- | , ~q(-$m) =>
  --   -- does one have to deal with (· * ·) case




  -- match va with
  -- | .one =>
  --   return ⟨_, .one, q(one_zpow $n)⟩
  --   -- not sure if this one is necessary
  -- | .mul (x := x) vx m .one =>
  --   return ⟨_, .mul vx q($m * $m) .one, q(sorry)⟩
  --   -- should case split when the exponent is zero, positive or negative
  -- | .mul (x := x) vx m (b := b) vb =>
  --   -- return ⟨_, .mul ⟩
  --   sorry




partial def eval (e : Q($α)) : AtomM (Result (ExProd gα) e) := Lean.withIncRecDepth do
  let els := do
    evalAtom e
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n with
  | ``HMul.hMul | ``Mul.mul => match e with
    | ~q($a * $b) =>
      let ⟨_, va, pa⟩ ← eval a
      let ⟨_, vb, pb⟩ ← eval b
      let ⟨_, vc, p⟩ ← evalMul va vb
      pure ⟨_, vc, q(by rw [← «$p», ← «$pb» , ← «$pa»])⟩
    | _ => els
  -- | ``HPow.hPow | ``Pow.pow => match e with
  --   | ~q($a ^ $n) =>
  --     let ⟨_, va, pa⟩ ← eval a
  --     let ⟨_, vn, pn⟩ ← eval n
  --     let ⟨_, vc, pc⟩ ← evalPow va vn
  --     evalPow va n
  | _ => els


/-- Frontend of `group1`: attempt to close a goal `g`, assuming it is an equation of semirings. -/
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
  /-- The core of `proveEq` takes expressions `e₁ e₂ : α` where `α` is a `CommSemiring`,
  and returns a proof that they are equal (or fails). -/
  groupCore {v : Level} {α : Q(Type v)} (gα : Q(CommSemiring $α))
      (e₁ e₂ : Q($α)) : AtomM Q($e₁ = $e₂) := do
    profileitM Exception "group" (← getOptions) do
      let ⟨a, va, pa⟩ ← eval (gα := gα) e₁
      let ⟨b, vb, pb⟩ ← eval (gα := gα) e₂
      unless va.eq vb do
        let g ← mkFreshExprMVar q($a = $b)
        throwError "group failed, group expressions not equal\n{g.mvarId!}"
      have : $a =Q $b := ⟨⟩ -- a ^ 2 * b * a^2 * b
      return q(sorry)

end
/--
`group1` solves the goal when it is an equality in a *group*,
allowing variables in the exponent.

This version of `group` fails if the target is not an equality.

* `group1!` uses a more aggressive reducibility setting to determine equality of atoms.
-/
elab (name := group1) "group1" tk:"!"? : tactic => liftMetaMAtMain fun g ↦ do
  AtomM.run (if tk.isSome then .default else .reducible) (proveEq g)

@[tactic_alt group1] macro "group1!" : tactic => `(tactic| group1 !)


end Group

example {G : Type*} [Group G] (a b c : G) : a * a * b * c^2 = a^2 * b * c ^ 2 := by
  group1
  sorry

example {G : Type*} [Group G] (a b c : G) : a ^ 2 * a * b * c^2 = a^3 * b * c ^ 2 := by
  group1
  sorry
