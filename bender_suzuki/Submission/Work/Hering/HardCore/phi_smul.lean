import Mathlib
import Submission.Work.Hering.HardCore.abelian_setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.HardCore

/-- Exponent bookkeeping for `ZMod n`: if `g ^ n = 1` then for `a b : ZMod n`,
`g ^ (a * b).val = (g ^ b.val) ^ a.val`.

Indeed `(a * b).val = a.val * b.val % n` (`ZMod.val_mul`), and exponents may be reduced
modulo `n` because `g ^ n = 1` (`pow_eq_pow_mod`); the rest is `pow_mul` and `mul_comm`. -/
lemma pow_val_mul {G : Type*} [Group G] {n : ℕ} (g : G) (hg : g ^ n = 1) (a b : ZMod n) :
    g ^ ((a * b).val) = (g ^ b.val) ^ a.val := by
  rw [ZMod.val_mul, ← pow_eq_pow_mod (a.val * b.val) hg, ← pow_mul, mul_comm b.val a.val]

/-- `Φ` is compatible with the scalar multiplication of `(ℤ/2^m)³` by an element `a`
of `ℤ/2^m`: `Φ c (a • x) = (Φ c x) ^ a.val`.  This is the multiplicative behaviour of the
coordinate map, companion to the additivity `Φ c x * Φ c y = Φ c (x + y)` (`phi_mul`).

The three powers `cᵢ ^ (xᵢ).val` pairwise commute (they lie in the abelian group `C`), so the
power of the product distributes over them, and each factor is handled by `pow_val_mul`. -/
theorem phi_smul {G : Type*} [Group G] {C : Subgroup G} (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    {m : ℕ} {c : Fin 3 → G} (hc : ∀ i, c i ∈ C) (hpow : ∀ i, (c i) ^ (2 ^ m) = 1)
    (a : ZMod (2 ^ m)) (x : Fin 3 → ZMod (2 ^ m)) :
    Phi c (a • x) = (Phi c x) ^ a.val := by
  have key : ∀ i : Fin 3, c i ^ ((a * x i).val) = (c i ^ (x i).val) ^ a.val :=
    fun i => pow_val_mul (c i) (hpow i) a (x i)
  have hc01 : Commute (c 0) (c 1) := (commute_iff_eq _ _).mpr (hCab _ (hc 0) _ (hc 1))
  have hc02 : Commute (c 0) (c 2) := (commute_iff_eq _ _).mpr (hCab _ (hc 0) _ (hc 2))
  have hc12 : Commute (c 1) (c 2) := (commute_iff_eq _ _).mpr (hCab _ (hc 1) _ (hc 2))
  have hAB : Commute (c 0 ^ (x 0).val) (c 1 ^ (x 1).val) := hc01.pow_pow _ _
  have hABC : Commute (c 0 ^ (x 0).val * c 1 ^ (x 1).val) (c 2 ^ (x 2).val) :=
    (hc02.pow_pow _ _).mul_left (hc12.pow_pow _ _)
  simp only [Phi, Pi.smul_apply, smul_eq_mul]
  rw [key 0, key 1, key 2, hABC.mul_pow a.val, hAB.mul_pow a.val]

end Work.Hering.HardCore
