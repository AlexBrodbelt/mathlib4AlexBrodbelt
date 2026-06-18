module

public import Mathlib.Algebra.Group.Commutator  -- shake: keep (tactic dependency)
public import Mathlib.Algebra.Order.Sub.Basic  -- shake: keep (tactic dependency)
public import Mathlib.Tactic.FailIfNoProgress
public import Mathlib.Tactic.Ring

@[to_additive]
theorem _zpow_trick {G : Type*} [Group G] (a b : G) (n m : ℤ) :
    a * b ^ n * b ^ m = a * b ^ (n + m) := by rw [mul_assoc, ← zpow_add]

@[to_additive _zsmul_trick_one]
theorem _zpow_trick_one {G : Type*} [Group G] (a b : G) (m : ℤ) :
    a * b * b ^ m = a * b ^ (m + 1) := by rw [mul_assoc, mul_self_zpow]

@[to_additive _zsmul_trick_one']
theorem _zpow_trick_one' {G : Type*} [Group G] (a b : G) (n : ℤ) :
    a * b ^ n * b = a * b ^ (n + 1) := by rw [mul_assoc, mul_zpow_self]

@[to_additive]
theorem _mul_pow_eq_mul_pow_iff_mul_pow_sub_eq_of_le {G : Type*} [Group G] (a b c : G) (n m : ℤ)
  (_hmn : m ≤ n) : a * b ^ n = c * b ^ m ↔ a * b ^ (n - m) = c := by
  rw [zpow_sub,  ← mul_assoc, mul_inv_eq_iff_eq_mul]

@[to_additive]
theorem _mul_pow_eq_mul_pow_iff_mul_pow_sub_eq_of_ge {G : Type*} [Group G] (a b c : G) (n m : ℤ)
  (_hmn : m ≥ n) : a * b ^ n = c * b ^ m ↔ a = c * b ^ (m - n) := by
  rw [zpow_sub,  ← mul_assoc, eq_mul_inv_iff_mul_eq]

@[to_additive]
theorem _pow_mul_eq_pow_mul_iff_pow_sub_mul_eq_of_le {G : Type*} [Group G] (a b c : G) (n m : ℤ)
  (_hmn : n ≤ m) : b ^ n * a = b ^ m * c ↔ b ^ (n - m) * a = c := by
  rw [zpow_sub, ← zpow_neg, zpow_mul_comm, zpow_neg, mul_assoc, inv_mul_eq_iff_eq_mul]

@[to_additive]
theorem _pow_mul_eq_pow_mul_iff_pow_sub_mul_eq_of_ge {G : Type*} [Group G] (a b c : G) (n m : ℤ)
  (_hmn : m ≤ n) : b ^ n * a = b ^ m * c ↔ a = b ^ (m - n) * c := by
  rw [zpow_sub, ← zpow_neg, zpow_mul_comm, zpow_neg, mul_assoc, eq_inv_mul_iff_mul_eq]
