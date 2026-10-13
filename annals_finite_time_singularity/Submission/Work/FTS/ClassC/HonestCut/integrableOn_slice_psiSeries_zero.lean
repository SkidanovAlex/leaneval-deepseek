/-
# `Work.FTS.ClassC.HonestCut.integrableOn_slice_psiSeries_zero`

The `θ`-slice at a fixed `z > 0` of the level-`0` `ℋ`-integrand of the modal solution
`Ψ = psiSeries α F = Σ_m a_m(z)·e_m(θ)` is integrable on `Iθ = [0, π/2]`, as soon as the
radial coefficients satisfy the weighted summability

  `Σ_m (m+1)·|a_m(z)| < ∞`.

The mechanism is the sharp linear sup bound `|e_m(θ)| ≤ 3(m+1)` on `Iθ`
(`Work.FTS.ClassC.abs_eFam_le`), which turns the weighted summability of the coefficients into
the *uniform* majorant

  `|Ψ(z,θ)| ≤ Σ_m |a_m| |e_m(θ)| ≤ 3·Σ_m (m+1)|a_m|  =: 3S`     (`abs_psiSeries_slice_le`),

valid on all of `Iθ`.  The level-`0` integrand is `(w(z)² Ψ²)·σ(θ)` with `σ = sin(2θ)^{-η}`
(`HkIntegrand_zero_eq'`), so it is dominated by the constant multiple `9 S² w(z)²·σ` of the
integrable weight `σ` (`sEta_integrableOn`), and integrability follows from `Integrable.mono'`.
Measurability is free: `Ψ(z,·)` is an unconditionally convergent series of continuous functions,
hence `AEStronglyMeasurable` (`AEStronglyMeasurable.tsum`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.ClassC.ModeSumZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.HonestCut

set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "w" => Work.Spaces.w
local notation "eFam" => Work.FTS.PhiStar.Gegenbauer.eFam
local notation "acoeff" => Work.FTS.PhiStar.Series.acoeff
local notation "psiSeries" => Work.FTS.PhiStar.Series.psiSeries

/-- **The pointwise sup bound for the mode series on `Iθ`.**  Under the weighted summability
`Σ_m (m+1)|a_m(z)| < ∞` of the radial coefficients, the series `Σ_m a_m(z)·e_m(θ)` is absolutely
convergent for every `θ ∈ Iθ` and

  `|psiSeries α F z θ| ≤ 3 · Σ_m (m+1)·|a_m(z)|`.

The bound is the Weierstrass majorant `|a_m e_m θ| ≤ 3(m+1)|a_m|` coming from the sharp linear
sup bound on the eigenfamily. -/
lemma abs_psiSeries_slice_le {α : ℝ} {F : ℝ → ℝ → ℝ} {z : ℝ}
    (hcoef : Summable (fun m : ℕ => ((m : ℝ) + 1) * |acoeff α m F z|)) {θ : ℝ}
    (hθ : θ ∈ Iθ) :
    |psiSeries α F z θ| ≤ 3 * ∑' m : ℕ, ((m : ℝ) + 1) * |acoeff α m F z| := by
  have hmode : ∀ m : ℕ, ‖acoeff α m F z * eFam m θ‖ ≤ 3 * (((m : ℝ) + 1) * |acoeff α m F z|) := by
    intro m
    rw [Real.norm_eq_abs, abs_mul]
    calc |acoeff α m F z| * |eFam m θ| ≤ |acoeff α m F z| * (3 * ((m : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (Work.FTS.ClassC.abs_eFam_le m hθ) (abs_nonneg _)
      _ = 3 * (((m : ℝ) + 1) * |acoeff α m F z|) := by ring
  have hu : Summable (fun m : ℕ => 3 * (((m : ℝ) + 1) * |acoeff α m F z|)) := hcoef.mul_left 3
  have hs : Summable (fun m : ℕ => acoeff α m F z * eFam m θ) :=
    Summable.of_norm_bounded hu hmode
  have h1 : ‖∑' m : ℕ, acoeff α m F z * eFam m θ‖
      ≤ ∑' m : ℕ, ‖acoeff α m F z * eFam m θ‖ :=
    norm_tsum_le_tsum_norm hs.norm
  have h2 : (∑' m : ℕ, ‖acoeff α m F z * eFam m θ‖)
      ≤ ∑' m : ℕ, 3 * (((m : ℝ) + 1) * |acoeff α m F z|) :=
    Summable.tsum_le_tsum hmode hs.norm hu
  have h3 : (∑' m : ℕ, 3 * (((m : ℝ) + 1) * |acoeff α m F z|))
      = 3 * ∑' m : ℕ, ((m : ℝ) + 1) * |acoeff α m F z| := tsum_mul_left
  rw [Real.norm_eq_abs] at h1
  exact h1.trans (h2.trans (le_of_eq h3))

/-- **The level-`0` `θ`-slice of the modal solution is integrable.** -/
theorem integrableOn_slice_psiSeries_zero {α : ℝ} {F : ℝ → ℝ → ℝ} (z : ℝ) (hz : 0 < z)
    (hcoef : Summable (fun m : ℕ =>
      ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|)) :
    MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 0
        (Work.FTS.PhiStar.Series.psiSeries α F) z θ) Work.Spaces.Iθ := by
  set S : ℝ := ∑' m : ℕ, ((m : ℝ) + 1) * |acoeff α m F z| with hS
  have hSnn : 0 ≤ S := by
    rw [hS]
    exact tsum_nonneg fun m => by positivity
  -- the uniform sup bound on the slice
  have hψ : ∀ θ ∈ Iθ, |psiSeries α F z θ| ≤ 3 * S := by
    intro θ hθ
    simpa only [hS] using abs_psiSeries_slice_le hcoef hθ
  -- measurability: the slice is a series of continuous functions
  have hψaesm : AEStronglyMeasurable (fun θ : ℝ => psiSeries α F z θ)
      (volume.restrict Iθ) := by
    show AEStronglyMeasurable
      (fun θ : ℝ => ∑' m : ℕ, acoeff α m F z * eFam m θ) _
    exact AEStronglyMeasurable.tsum
      (fun m => (continuous_const.mul (Work.FTS.PhiStar.Series.continuous_eFam m)).aestronglyMeasurable)
  have hsEta_aesm : AEStronglyMeasurable (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Iθ) :=
    Work.FTS.EllipticEst.Honest.sEta_integrableOn.aestronglyMeasurable
  have hasm2 : AEStronglyMeasurable
      (fun θ : ℝ => (w z) ^ 2 * ((psiSeries α F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      (volume.restrict Iθ) :=
    ((hψaesm.pow 2).mul hsEta_aesm).const_mul ((w z) ^ 2)
  have hasm : AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 (psiSeries α F) z θ) (volume.restrict Iθ) :=
    hasm2.congr (Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq_ae α (psiSeries α F) z).symm
  -- the integrable dominating slice
  have hdom : IntegrableOn
      (fun θ : ℝ => (w z) ^ 2 * (9 * S ^ 2) * Work.FTS.EllipticEst.sEta θ) Iθ :=
    (Work.FTS.EllipticEst.Honest.sEta_integrableOn).const_mul ((w z) ^ 2 * (9 * S ^ 2))
  refine hdom.mono' hasm ?_
  rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  refine Filter.Eventually.of_forall (fun θ hθ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 0 _ z θ),
    Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq' hθ (psiSeries α F) z]
  have hb := hψ θ hθ
  have hsq : (psiSeries α F z θ) ^ 2 ≤ (3 * S) ^ 2 := by
    rcases abs_le.mp hb with ⟨h1, h2⟩
    exact sq_le_sq' h1 h2
  have h3 : (3 * S) ^ 2 = 9 * S ^ 2 := by ring
  rw [h3] at hsq
  have hse := Work.FTS.EllipticEst.Honest.sEta_nonneg hθ
  have hw := sq_nonneg (w z)
  calc (w z) ^ 2 * ((psiSeries α F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ (w z) ^ 2 * ((9 * S ^ 2) * Work.FTS.EllipticEst.sEta θ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hse) hw
    _ = (w z) ^ 2 * (9 * S ^ 2) * Work.FTS.EllipticEst.sEta θ := by ring

end Work.FTS.ClassC.HonestCut
