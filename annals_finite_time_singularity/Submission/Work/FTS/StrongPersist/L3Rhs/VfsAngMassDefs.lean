/-
# `VfsAngMassDefs` — the angular majorant `VfsJetMaj` of the profile `Γ/c`

This module fixes the auxiliary objects used by the proof of
`Work.FTS.StrongPersist.L3Rhs.VfsAngMass`.  Writing `X = VfsGc α = Γ/c` and
`T θ = sin(2θ)`, the *angular majorant of `X`* is

  `VfsJetMaj α θ = (X θ)²·T θ^{-η} + α²·(X θ)²·T θ^{-γ(α)}
      + Σ_{1 ≤ m ≤ 4} (dthU^[m] X θ)²·T θ^{-γ(α)}`.

Three features are essential and explain the shape.

* The `m = 0` summand is weighted by `T^{-η}` (not `T^{-γ}`): `∫ Γ² T^{-γ}` is *not*
  uniformly bounded in `α` (it behaves like `1/α`), while `∫ Γ² T^{-η}` is bounded by
  `10^15` — this is item (2) of `Work.FTS.StrongPersist.L3Aux.GamJetBounds`.
* The `α²·(X)²·T^{-γ}` summand is the one place where the `γ`-weight is applied to the
  *underived* profile, and the factor `α²` exactly compensates the `1/α` of the singular
  integral `∫ T^{17α/30-1}`, so this piece is uniformly bounded as well (same mechanism as
  in `Work.FTS.LocData.angMaj_mem`).
* The derived summands `1 ≤ m ≤ 4` are the `γ`-masses supplied by
  `Work.FTS.StrongPersist.L3Aux.GamJetBounds`, again bounded by `10^15`
  (`Work.FTS.LocData.DthIter_rad_eq` identifies its `DthIter i (fun _ θ => Γ θ / c)` with
  `dthU^[i] (Γ/c)`).

Hence `∫_{Iθ} VfsJetMaj α ≤ 10^15 + 2·10^4 + 4·10^15 ≤ 10^16` uniformly for `α ∈ (0,1]`
(lemma `VfsJetMaj_mass`).

The elementary `rpow` bookkeeping on `(0, π/2)` is collected here as well:

* `sin_two_nonneg_Iθ`, `sin_two_pos_Ioo`;  `rpow_le_rpow_of_le_one`;
* `eta_le_gam : η ≤ γ(α)`, hence `sin_two_rpow_eta_le_gam : T^{-η} ≤ T^{-γ}`;
* `sin_two_sq_mul_rpow_eta_le_gam : T²·T^{-η} ≤ T^{-γ}` and
  `sin_two_sq_mul_rpow_gam_le : T²·T^{-γ} ≤ T^{-γ}`;
* `sum_five_sq_le : (Σ_{m<5} a m)² ≤ 5 Σ_{m<5} (a m)²`.

Nothing here is a proof obligation.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gAuxDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The angular majorant -/

/-- The `γ`-weighted jet sum `Σ_{1 ≤ m ≤ 4} (dthU^[m] (Γ/c))² sin(2θ)^{-γ}`. -/
def VfsJetSum (α : ℝ) (θ : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 4,
    (Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

/-- The angular majorant of the profile `Γ/c`:
`(Γ/c)² sin(2θ)^{-η} + α² (Γ/c)² sin(2θ)^{-γ} + VfsJetSum α θ`. -/
def VfsJetMaj (α : ℝ) (θ : ℝ) : ℝ :=
  (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    + α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
    + VfsJetSum α θ

@[simp] theorem VfsJetMaj_apply (α θ : ℝ) : VfsJetMaj α θ =
    (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      + α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      + VfsJetSum α θ := rfl

@[simp] theorem VfsJetSum_apply (α θ : ℝ) : VfsJetSum α θ =
    ∑ m ∈ Finset.Icc 1 4,
      (Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := rfl

/-! ## Elementary trigonometric and `rpow` facts -/

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  obtain ⟨h0, h1⟩ := hθ
  rw [Real.sin_two_mul]
  exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_mem_Icc ⟨h0, by linarith [h1, Real.pi_pos]⟩))
    (Real.cos_nonneg_of_mem_Icc ⟨by linarith [h0, Real.pi_pos],
      by linarith [h1, Real.pi_pos]⟩)

/-- `sin(2θ) > 0` on `(0,π/2)`. -/
theorem sin_two_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) := by
  rw [Real.sin_two_mul]
  have h1 : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h2 : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  positivity

/-- Antitonicity in the exponent of `x ↦ x^p` on `(0,1]`. -/
theorem rpow_le_rpow_of_le_one {x a b : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hab : a ≤ b) :
    x ^ b ≤ x ^ a :=
  Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hab

/-- `η ≤ γ(α)` for `0 ≤ α`. -/
theorem eta_le_gam {α : ℝ} (hα : 0 ≤ α) : Work.Spaces.eta ≤ Work.Spaces.gam α := by
  simp only [Work.Spaces.eta, Work.Spaces.gam]
  linarith

/-- `sin(2θ)^{-η} ≤ sin(2θ)^{-γ(α)}` on `(0,π/2)`. -/
theorem sin_two_rpow_eta_le_gam {α θ : ℝ} (hα : 0 ≤ α)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
  rpow_le_rpow_of_le_one (x := Real.sin (2 * θ)) (a := -(Work.Spaces.gam α))
    (b := -(Work.Spaces.eta)) (sin_two_pos_Ioo hθ) (Real.sin_le_one _)
    (by linarith [eta_le_gam hα])

/-- `sin(2θ)² · sin(2θ)^{-γ} ≤ sin(2θ)^{-γ}` on `(0,π/2)`. -/
theorem sin_two_sq_mul_rpow_gam_le {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hx0 : 0 < Real.sin (2 * θ) := sin_two_pos_Ioo hθ
  have hx1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsq : (Real.sin (2 * θ)) ^ 2 ≤ 1 := pow_le_one₀ hx0.le hx1
  calc (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ 1 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hx0.le _)
    _ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := one_mul _

/-- `sin(2θ)² · sin(2θ)^{-η} ≤ sin(2θ)^{-γ}` on `(0,π/2)`. -/
theorem sin_two_sq_mul_rpow_eta_le_gam {α θ : ℝ} (hα : 0 ≤ α)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hx0 : 0 < Real.sin (2 * θ) := sin_two_pos_Ioo hθ
  have hx1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsq : (Real.sin (2 * θ)) ^ 2 ≤ 1 := pow_le_one₀ hx0.le hx1
  calc (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ 1 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hx0.le _)
    _ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := one_mul _
    _ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := sin_two_rpow_eta_le_gam hα hθ

/-- Cauchy–Schwarz for the five-term sum: `(Σ_{m<5} a m)² ≤ 5 Σ_{m<5} (a m)²`. -/
theorem sum_five_sq_le (a : ℕ → ℝ) :
    (∑ m ∈ Finset.range 5, a m) ^ 2 ≤ 5 * ∑ m ∈ Finset.range 5, (a m) ^ 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  nlinarith [sq_nonneg (a 0 - a 1), sq_nonneg (a 0 - a 2), sq_nonneg (a 0 - a 3),
    sq_nonneg (a 0 - a 4), sq_nonneg (a 1 - a 2), sq_nonneg (a 1 - a 3),
    sq_nonneg (a 1 - a 4), sq_nonneg (a 2 - a 3), sq_nonneg (a 2 - a 4),
    sq_nonneg (a 3 - a 4)]

/-! ## Basic properties of `VfsJetMaj` -/

/-- `VfsJetSum` is nonnegative on `Iθ`. -/
theorem VfsJetSum_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ VfsJetSum α θ := by
  rw [VfsJetSum]
  exact Finset.sum_nonneg (fun m _ =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))

/-- `VfsJetMaj` is nonnegative on `Iθ`. -/
theorem VfsJetMaj_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ VfsJetMaj α θ := by
  have hs := sin_two_nonneg_Iθ hθ
  rw [VfsJetMaj]
  exact add_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _))
    (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg hs _)))
    (VfsJetSum_nonneg α hθ)

/-- The `η`-summand of `VfsJetMaj`. -/
theorem VfsJetMaj_ge_eta (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ≤ VfsJetMaj α θ := by
  have h1 : 0 ≤ α ^ 2 * (VfsGc α θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)
  rw [VfsJetMaj]
  linarith [h1, VfsJetSum_nonneg α hθ]

/-- The `α²`-summand of `VfsJetMaj`. -/
theorem VfsJetMaj_ge_alpha (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ VfsJetMaj α θ := by
  have h0 : 0 ≤ (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)
  rw [VfsJetMaj]
  linarith [h0, VfsJetSum_nonneg α hθ]

/-- Every `γ`-weighted jet summand of `VfsJetMaj`. -/
theorem VfsJetMaj_ge_gam (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) {m : ℕ}
    (hm1 : 1 ≤ m) (hm4 : m ≤ 4) :
    (Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ VfsJetMaj α θ := by
  have hs := sin_two_nonneg_Iθ hθ
  have hmem : m ∈ Finset.Icc 1 4 := Finset.mem_Icc.mpr ⟨hm1, hm4⟩
  have hle : (Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ VfsJetSum α θ := by
    rw [VfsJetSum]
    exact Finset.single_le_sum
      (s := Finset.Icc 1 4)
      (f := fun i => (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (fun i _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)) hmem
  have h0 : 0 ≤ (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)
  have h1 : 0 ≤ α ^ 2 * (VfsGc α θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg hs _)
  rw [VfsJetMaj]
  linarith

end Work.FTS.StrongPersist.L3Rhs
