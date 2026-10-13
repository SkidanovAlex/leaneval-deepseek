/-
# `zProdIntLe` — the `(j,i) = (5,1)` mixed slot against the `γ`-weight

The statement is the membership-and-bound pair for the single slot

  `∫_z w(z)² ∫_θ sin(2θ)^{-γ} (D_z⁵D_θf)²  ≤  |f|²_{ℋ⁶}`

of the level-six norm, where the membership is the honest (iterated, i.e. a.e.-slice) form.

The mathematical content is entirely in the *unfolding*: the corresponding slot of
`HkIntegrand α 6 f` is `(D_z⁵D_θf · Wt)²` with `Wt α z θ = w z · sin(2θ)^{-γ/2}`, and
`(w · s^{-γ/2})² = w² s^{-γ}` (for `s = sin 2θ ≥ 0`, which holds on `Iθ`).  With that
identity the two halves are the `j = 5`, `θw = sin(2θ)^{-γ}` instance of

* the integrability of the `z`-marginal of a weighted mixed slot, and
* `Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq` (a single slot of `HkIntegrand` is
  pointwise dominated by the full integrand),

both already available (`Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.mixedSlotL2`).
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.mixedSlotL2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

/-- `sin (2θ) ≥ 0` for `θ ∈ Iθ = [0,π/2]`. -/
private lemma sin_two_nonneg_Iθ' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- The square of the mixed weight `Wt α z θ = w z · sin(2θ)^{-γ/2}` is
`w z² · sin(2θ)^{-γ}`, for nonnegative `sin(2θ)`. -/
private lemma Wt_sq_eq' (α z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  rw [show ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ ((2 : ℝ)) from
      (Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2).symm]
  rw [← Real.rpow_mul hs]
  rw [show (-(Work.Spaces.gam α / 2)) * (2 : ℝ) = -(Work.Spaces.gam α) by ring]

/-- The squared weighted mixed slot, in the unfolded `w² s^{-γ} (D_z⁵D_θf)²` form of the
statement (valid where `sin(2θ) ≥ 0`). -/
private lemma slot_sq_eq' (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hs : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 5 1 f z θ) ^ 2) := by
  rw [mul_pow, Wt_sq_eq' α z θ hs]
  ring

theorem zProdIntLe : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 5 1 f z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
    (∫ z, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 5 1 f z θ) ^ 2)
      ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      ≤ Work.Spaces.HkSq α 6 f := by
  intro α f hα hα1 hsm hmem
  -- The weighted slot `j = 5` of `HkIntegrand α 6 f`: integrability and value bound.
  obtain ⟨hint, hle⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.mixedSlotL2 α ⟨hα, hα1⟩ f 5 hsm hmem le_rfl
  -- The pointwise unfolding `(D_z⁵D_θf · Wt)² = w² · (s^{-γ} · (D_z⁵D_θf)²)` of the slot.
  have hident : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        = (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 5 1 f z θ) ^ 2) := by
    intro z
    rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      (fun θ hθ => slot_sq_eq' α f z θ (sin_two_nonneg_Iθ' hθ)))]
    rw [MeasureTheory.integral_const_mul]
  refine ⟨hint.congr (Filter.Eventually.of_forall hident), ?_⟩
  calc (∫ z, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 5 1 f z θ) ^ 2)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      = ∫ z, (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) :=
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun z => (hident z).symm)
    _ = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := rfl
    _ ≤ Work.Spaces.HkSq α 6 f := hle

end

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
