import Mathlib
import Submission.Work.EKLContract.Defs

/-!
# The product-box plaque and its coordinate maps (C5b, step 4)

For the product structure (`P_Product`, Pisa Cor. 8.8) the *aligned* σ-algebras used in the
tower identity of Pisa Lemma 8.10 must have **fibre-independent shapes**.  With the ball plaque
`EKLComp.orbitPlaque H x₀ ε` and the T-slice algebra of `EKLProd/aligned_T_plaqueAlgebra` the
T-slice through the fibre with U-part `u` has shape `(V ε ∩ H)·u⁻¹ ∩ T`, which *does* depend on
`u`; with the **product box** of this module and the **strip algebras** (the level sets of the
U-part / T-part maps) it is the constant `V ε ∩ T`, which is what makes the substitution of
step 3 produce a fibre-independent answer (see `EKLComp/ProductPlan.md` §8).

Note (referee finding): the coordinate predicate must use the *product box*
`(V ε ∩ T) * (V ε ∩ U)`, **not** `V ε ∩ H`: the product box is not contained in the ball `V ε`
(e.g. for the unipotent `N` with `T = ⟨U₁₂,U₁₃⟩`, `U = U₂₃`, the product of two `ε`-small
elements has an entry of size up to `ε + ε²`), so a predicate phrased with `V ε ∩ H` would be
junk at legitimate points of the plaque.

This module contains only definitions and their elementary projection lemmas.
-/

open MeasureTheory Topology Filter
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLProd

open Work.EKLContract

/-- The product box `(V ε ∩ T) * (V ε ∩ U)` as a set of group elements. -/
def prodBox (T U : Subgroup SL3) (ε : ℝ) : Set SL3 :=
  (V ε ∩ (T : Set SL3)) * (V ε ∩ (U : Set SL3))

/-- The **product-box plaque** of `H = T·U` at `x₀`: the orbit image of the product box. -/
def prodPlaque (H T U : Subgroup SL3) (x₀ : X3) (ε : ℝ) : Set X3 :=
  (fun h : SL3 => h • x₀) '' prodBox T U ε

theorem prodBox_subset_H {H T U : Subgroup SL3} (hTH : T ≤ H) (hUH : U ≤ H) {ε : ℝ} :
    prodBox T U ε ⊆ (H : Set SL3) := by
  rintro g ⟨a, ha, b, hb, rfl⟩
  exact H.mul_mem (hTH ha.2) (hUH hb.2)

/-- A chosen decomposition `g = a * b` with `a ∈ T`, `b ∈ U`, when one exists (junk value
`(1,1)` otherwise). -/
noncomputable def decompose (T U : Subgroup SL3) (g : SL3) : SL3 × SL3 := by
  classical
  exact if h : ∃ p : SL3 × SL3, p.1 ∈ T ∧ p.2 ∈ U ∧ p.1 * p.2 = g then h.choose else (1, 1)

/-- The `T`-part of an element admitting a decomposition over `T` and `U`. -/
noncomputable def hT (T U : Subgroup SL3) (g : SL3) : SL3 := (decompose T U g).1

/-- The `U`-part of an element admitting a decomposition over `T` and `U`. -/
noncomputable def hU (T U : Subgroup SL3) (g : SL3) : SL3 := (decompose T U g).2

theorem exists_decomp_of {T U : Subgroup SL3} {g : SL3}
    (hg : ∃ a ∈ T, ∃ b ∈ U, g = a * b) :
    ∃ p : SL3 × SL3, p.1 ∈ T ∧ p.2 ∈ U ∧ p.1 * p.2 = g :=
  ⟨(hg.choose, hg.choose_spec.2.choose), hg.choose_spec.1,
    hg.choose_spec.2.choose_spec.1, hg.choose_spec.2.choose_spec.2.symm⟩

theorem hT_mem {T U : Subgroup SL3} {g : SL3} (hg : ∃ a ∈ T, ∃ b ∈ U, g = a * b) :
    hT T U g ∈ T := by
  have h2 := exists_decomp_of hg
  simp only [hT, hU, decompose, dif_pos h2]
  exact (Classical.choose_spec h2).1

theorem hU_mem {T U : Subgroup SL3} {g : SL3} (hg : ∃ a ∈ T, ∃ b ∈ U, g = a * b) :
    hU T U g ∈ U := by
  have h2 := exists_decomp_of hg
  simp only [hT, hU, decompose, dif_pos h2]
  exact (Classical.choose_spec h2).2.1

theorem hT_mul_hU {T U : Subgroup SL3} {g : SL3} (hg : ∃ a ∈ T, ∃ b ∈ U, g = a * b) :
    hT T U g * hU T U g = g := by
  have h2 := exists_decomp_of hg
  simp only [hT, hU, decompose, dif_pos h2]
  exact (Classical.choose_spec h2).2.2

/-- Uniqueness of the decomposition when `T ⊓ U = 1`. -/
theorem hT_hU_unique {T U : Subgroup SL3} (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {a a' b b' : SL3} (ha : a ∈ T) (hb : b ∈ U) (ha' : a' ∈ T) (hb' : b' ∈ U)
    (h : a * b = a' * b') : a = a' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ U := by rw [h1]; exact U.mul_mem hb' (U.inv_mem hb)
  have h3 : a'⁻¹ * a = 1 := hdisj _ (T.mul_mem (T.inv_mem ha') ha) h2
  calc a = a' * (a'⁻¹ * a) := by group
    _ = a' * 1 := by rw [h3]
    _ = a' := by rw [mul_one]

/-- The chosen coordinate of a point of the product-box plaque: the element of the product box
acting as `x₀` on it (junk value `1` outside the plaque). -/
noncomputable def plaqueCoord (H T U : Subgroup SL3) (x₀ : X3) (ε : ℝ) (y : X3) : SL3 := by
  classical
  exact if h : ∃ h' : SL3, h' ∈ prodBox T U ε ∧ h' • x₀ = y then h.choose else 1

theorem plaqueCoord_spec {H T U : Subgroup SL3} {x₀ : X3} {ε : ℝ} {y : X3}
    (hy : ∃ h' : SL3, h' ∈ prodBox T U ε ∧ h' • x₀ = y) :
    plaqueCoord H T U x₀ ε y ∈ prodBox T U ε ∧ plaqueCoord H T U x₀ ε y • x₀ = y := by
  simp only [plaqueCoord, dif_pos hy]
  exact ⟨(Classical.choose_spec hy).1, (Classical.choose_spec hy).2⟩

/-- Uniqueness of the plaque coordinate, from injectivity of the orbit map on `H`. -/
theorem plaqueCoord_eq_of {H T U : Subgroup SL3} (hTH : T ≤ H) (hUH : U ≤ H) {x₀ : X3} {ε : ℝ}
    (hinj : ∀ h₁ ∈ H, ∀ h₂ ∈ H, h₁ • x₀ = h₂ • x₀ → h₁ = h₂)
    {y : X3} (hy : ∃ h' : SL3, h' ∈ prodBox T U ε ∧ h' • x₀ = y) {h : SL3}
    (hh : h ∈ prodBox T U ε) (hhy : h • x₀ = y) : h = plaqueCoord H T U x₀ ε y := by
  obtain ⟨h1, h2⟩ := plaqueCoord_spec hy
  exact hinj h (prodBox_subset_H hTH hUH hh) (plaqueCoord H T U x₀ ε y)
    (prodBox_subset_H hTH hUH h1) (by rw [hhy, h2])

/-- The `U`-part of the plaque coordinate of a point (junk outside the plaque); its level sets
inside the plaque are the **T-strips** `{t u₀}`. -/
noncomputable def uPartOn (H T U : Subgroup SL3) (x₀ : X3) (ε : ℝ) (y : X3) : SL3 :=
  hU T U (plaqueCoord H T U x₀ ε y)

/-- The `T`-part of the plaque coordinate of a point (junk outside the plaque). -/
noncomputable def tPartOn (H T U : Subgroup SL3) (x₀ : X3) (ε : ℝ) (y : X3) : SL3 :=
  hT T U (plaqueCoord H T U x₀ ε y)

end Work.EKLProd
