import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.WPQ.Dth_DzIter_comm_smoothQuad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2.T1Q

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## Elementary almost-everywhere and weight facts

The estimates below are stated for the *open* quadrant: `SmoothQuad` constrains nothing on
`z = 0` nor on the lines `θ = 0`, `θ = π/2`.  Every function that occurs is continuous on the
open quadrant, so the boundary lines are almost everywhere irrelevant for the angular slices
and the origin `z = 0` for the radial ones. -/

/-- Almost everywhere on `Iz = [0,∞)`, the variable is positive. -/
theorem ae_pos_Iz : ∀ᵐ s ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < s := by
  have hset : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))
  rw [← hset]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => hs)

/-- Almost everywhere on `Iθ = [0,π/2]`, the angle lies in the open interval. -/
theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have hset : MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := π / 2))
  rw [← hset]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun s hs => hs)

/-- A function continuous on the open half-line `(0,∞)` is a.e. strongly measurable for the
restricted measure `volume.restrict Iz`. -/
theorem aesm_Iz_of_continuousOn {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioi (0 : ℝ))) :
    MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have h1 : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hg.aestronglyMeasurable measurableSet_Ioi
  have h2 : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))).symm
  rwa [h2]

/-- A function continuous on the open interval `(0,π/2)` is a.e. strongly measurable for the
restricted measure `volume.restrict Iθ`. -/
theorem aesm_Iθ_of_continuousOn {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioo (0 : ℝ) (π / 2))) :
    MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have h1 : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
    hg.aestronglyMeasurable measurableSet_Ioo
  have h2 : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := π / 2))).symm
  rwa [h2]

/-- The radial weight dominates `1` on the open half-line. -/
theorem one_le_w_of_pos {z : ℝ} (hz : 0 < z) : (1 : ℝ) ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith [hz]

/-- `1 ≤ x ^ (-p)` for `0 < x ≤ 1` and `p ≥ 0`. -/
theorem one_le_rpow_neg {x p : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hp : 0 ≤ p) :
    (1 : ℝ) ≤ x ^ (-p) := by
  rw [Real.rpow_neg (le_of_lt hx0) p]
  exact (one_le_inv₀ (Real.rpow_pos_of_pos hx0 p)).mpr (Real.rpow_le_one (le_of_lt hx0) hx1 hp)

/-- `(a / x^{c/2})² = a² x^{-c}` for `x > 0`. -/
theorem div_rpow_sq (a x c : ℝ) (hx : 0 < x) :
    (a / x ^ (c / 2)) ^ 2 = a ^ 2 * x ^ (-c) := by
  have h : (x ^ (c / 2)) ^ 2 = x ^ c := by
    rw [pow_two, ← Real.rpow_add hx, show c / 2 + c / 2 = c by ring]
  rw [div_pow, h, Real.rpow_neg (le_of_lt hx), div_eq_mul_inv]

/-- The squared product weight in terms of the radial weight and the angular `rpow`. -/
theorem Wt_sq_eq (α z θ : ℝ) (hsin : 0 < Real.sin (2 * θ)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have h : (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by
    rw [pow_two, ← Real.rpow_add hsin,
      show -(Work.Spaces.gam α / 2) + -(Work.Spaces.gam α / 2) = -(Work.Spaces.gam α) by ring]
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, h]

/-- On the open quadrant `(w z)² ≤ (Wt α z θ)²`. -/
theorem w_sq_le_Wt_sq (α : ℝ) (hα : 0 < α) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hsin : 0 < Real.sin (2 * θ)) :
    (Work.Spaces.w z) ^ 2 ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
  have h1 : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    one_le_rpow_neg hsin (Real.sin_le_one _) (le_of_lt (Work.Spaces.gam_pos hα))
  rw [Wt_sq_eq α z θ hsin]
  calc (Work.Spaces.w z) ^ 2 = (Work.Spaces.w z) ^ 2 * 1 := by ring
    _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)

/-! ## The pointwise domination of a mixed slot of order `≤ 4` -/

/-- On the open quadrant, the squared weighted mixed slot `(D_z^b D_θ^a f)² w²` of order
`a + b ≤ 4` is dominated by the `ℋ⁴`-integrand of `f`. -/
theorem mixed_sq_w_sq_le_HkIntegrand (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ) (b a : ℕ)
    (hab : a + b ≤ 4) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    (Work.Spaces.mixed b a f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    rw [Work.Spaces.mixed_zero_right]
    have h1 : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      one_le_rpow_neg hsin hs1 Work.Spaces.eta_nonneg
    have hrew : (Work.Spaces.DzIter b f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.DzIter b f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [mul_pow, div_rpow_sq (Work.Spaces.w z) (Real.sin (2 * θ)) Work.Spaces.eta hsin]
      ring
    have hz2 := Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ b (by omega)
    rw [hrew] at hz2
    calc (Work.Spaces.DzIter b f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (Work.Spaces.DzIter b f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) (sq_nonneg _)) h1
      _ ≤ Work.Spaces.HkIntegrand α 4 f z θ := hz2
  · calc (Work.Spaces.mixed b a f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (Work.Spaces.mixed b a f z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 :=
          mul_le_mul_of_nonneg_left (w_sq_le_Wt_sq α hα hθIθ hsin) (sq_nonneg _)
      _ = (Work.Spaces.mixed b a f z θ * Work.Spaces.Wt α z θ) ^ 2 := (mul_pow _ _ 2).symm
      _ ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
          Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ a b ha (by omega)

/-- On the open quadrant, the squared mixed slot itself is dominated by the `ℋ⁴`-integrand. -/
theorem mixed_sq_le_HkIntegrand (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ) (b a : ℕ)
    (hab : a + b ≤ 4) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  calc (Work.Spaces.mixed b a f z θ) ^ 2
      = (Work.Spaces.mixed b a f z θ) ^ 2 * 1 := by ring
    _ ≤ (Work.Spaces.mixed b a f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        nlinarith [one_le_w_of_pos hz]
    _ ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
        mixed_sq_w_sq_le_HkIntegrand α hα f b a hab hz hθ0 hθ1

/-! ## Swapping the two integrations in `HkSq` (interior class) -/

/-- The `SmoothQuad` version of `Work.FTS.H2.HkSqSwap`: the iterated integral of the integrand
in the `θ`-outer order equals `HkSq`, the partially integrated function is integrable, and the
`s`-slices are integrable at almost every angle. -/
theorem HkSqSwapQ (α : ℝ) (f : ℝ → ℝ → ℝ) (hsq : Work.FTS.LocData.SmoothQuad f)
    (hmem : Work.Spaces.HkMem α 4 f) :
    (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ
        = Work.Spaces.HkSq α 4 f) ∧
      MeasureTheory.Integrable
        (fun σ : ℝ => ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α 4 f s σ)
          Work.Spaces.Iz) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 4 f hsq
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry fun z θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hmem.1 z hz)
  have houter : MeasureTheory.Integrable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmem.2
  obtain ⟨h1, h2, h3⟩ :=
    Work.FTS.H2.swap_iterated_integral_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) hnn haesm hslice houter
  exact ⟨by rw [Work.Spaces.HkSq]; exact h1, h2, h3⟩

/-! ## The radial Hardy step at a fixed angle -/


/-! ## The angular average and the angular Hardy integral of a mixed slot

Both are bounded by `HkSq α 4 f`, uniformly in `z > 0`; the proofs are the same Hardy step
(`hardyZQ_mixed_slice`) followed by the pointwise domination of the resulting `s`-integral by
the `θ`-slice of `HkIntegrand`, summed over `θ` with the swap `HkSqSwapQ`. -/



/-! ## `∂_θ` versus `D_θ` in the interior class -/



/-! ## The boundedness of the angular Hardy integral -/




/-! ## A point of the middle half of `Iθ` with value at most the average -/


/-! ## The target -/


end Work.H2.T1Q
