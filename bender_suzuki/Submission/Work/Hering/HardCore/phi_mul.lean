import Mathlib
import Submission.Work.Hering.HardCore.abelian_setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.HardCore

/-! ## Reordering helpers for the proof of `phi_mul`

`Φ c x = c₀^x₀ · c₁^x₁ · c₂^x₂` is a product of six factors (three for `x`, three for `y`) that
are pairwise commuting, since each is a power of one of the pairwise commuting elements `c₀, c₁, c₂`.
The two lemmas below reorder such a product into its "aligned" shape `(a·a')·(b·b')·(d·d')` and then
collapse the adjacent equal bases. -/

/-- Swap the two leading factors of a product whose first factor is already a power:
`a ^ m * (a ^ n * X) = a ^ (m + n) * X`. -/
lemma pow_mul_pow_assoc {M : Type*} [Monoid M] (a : M) (m n : ℕ) (X : M) :
    a ^ m * (a ^ n * X) = a ^ (m + n) * X := by rw [← mul_assoc, ← pow_add]

/-- Collapse the three adjacent equal-base pairs in a right-associated product of six powers. -/
lemma collect3_phi {M : Type*} [Monoid M] (a b d : M) (m n m' n' m'' n'' : ℕ) :
    a ^ m * (a ^ n * (b ^ m' * (b ^ n' * (d ^ m'' * d ^ n''))))
      = a ^ (m + n) * (b ^ (m' + n') * d ^ (m'' + n'')) := by
  rw [pow_mul_pow_assoc, pow_mul_pow_assoc, ← pow_add]

/-- The coordinate map `Φ` is additive: `Φ c x * Φ c y = Φ c (x + y)`.

The three powers `cᵢ ^ (xᵢ).val` pairwise commute (they lie in the abelian group `C`), so the
product `Φ c x * Φ c y` can be reordered into `(c₀^x₀ · c₀^y₀) · (c₁^x₁ · c₁^y₁) · (c₂^x₂ · c₂^y₂)`;
each pair collapses to `cᵢ ^ ((xᵢ).val + (yᵢ).val) = cᵢ ^ ((xᵢ + yᵢ).val)` because
`(xᵢ + yᵢ).val = ((xᵢ).val + (yᵢ).val) % 2^m` (`ZMod.val_add`) and exponents may be reduced
modulo `2^m` (`pow_eq_pow_mod`, using `hpow`). -/
theorem phi_mul {G : Type*} [Group G] {C : Subgroup G} (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    {m : ℕ} {c : Fin 3 → G} (hc : ∀ i, c i ∈ C) (hpow : ∀ i, (c i) ^ (2 ^ m) = 1)
    (x y : Fin 3 → ZMod (2 ^ m)) : Phi c x * Phi c y = Phi c (x + y) := by
  have hc01 : Commute (c 0) (c 1) := (commute_iff_eq _ _).mpr (hCab _ (hc 0) _ (hc 1))
  have hc02 : Commute (c 0) (c 2) := (commute_iff_eq _ _).mpr (hCab _ (hc 0) _ (hc 2))
  have hc12 : Commute (c 1) (c 2) := (commute_iff_eq _ _).mpr (hCab _ (hc 1) _ (hc 2))
  have hda' : Commute (c 2 ^ (x 2).val) (c 0 ^ (y 0).val) := hc02.symm.pow_pow _ _
  have hdb' : Commute (c 2 ^ (x 2).val) (c 1 ^ (y 1).val) := hc12.symm.pow_pow _ _
  have hba' : Commute (c 1 ^ (x 1).val) (c 0 ^ (y 0).val) := hc01.symm.pow_pow _ _
  calc Phi c x * Phi c y
      = c 0 ^ ((x 0).val + (y 0).val) *
          (c 1 ^ ((x 1).val + (y 1).val) * c 2 ^ ((x 2).val + (y 2).val)) := by
        simp only [Phi, mul_assoc]
        rw [Commute.left_comm hda', Commute.left_comm hdb', Commute.left_comm hba']
        exact collect3_phi (M := G) (c 0) (c 1) (c 2) _ _ _ _ _ _
    _ = Phi c (x + y) := by
        simp only [Phi, mul_assoc, Pi.add_apply]
        rw [ZMod.val_add (x 0) (y 0), ZMod.val_add (x 1) (y 1), ZMod.val_add (x 2) (y 2),
            ← pow_eq_pow_mod ((x 0).val + (y 0).val) (hpow 0),
            ← pow_eq_pow_mod ((x 1).val + (y 1).val) (hpow 1),
            ← pow_eq_pow_mod ((x 2).val + (y 2).val) (hpow 2)]

end Work.Hering.HardCore
