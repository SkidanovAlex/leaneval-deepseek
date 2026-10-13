import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.HQ.HardyZQ
import Submission.Work.FTS.H2.HQ.HardyThetaQ
import Submission.Work.FTS.H2.MinLeAvg
import Submission.Work.FTS.H2.OscSqLe
import Submission.Work.FTS.H2.HkSqSwap
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

/-- The radial Hardy inequality `HardyZQ` applied to the `z`-slice of a mixed derivative.
For `σ ∈ (0,π/2)`, if the `σ`-slice of `(D_z^{b+1}D_θ^a f)² w²` is integrable then

`(D_z^bD_θ^a f(z,σ))² ≤ ∫_{Iz} (D_z^{b+1}D_θ^a f(s,σ))² w(s)² ds`

for every `z > 0`. -/
theorem hardyZQ_mixed_slice (f : ℝ → ℝ → ℝ) (hsq : Work.FTS.LocData.SmoothQuad f)
    (hdec : Work.Spaces.DecayAll 4 f) (b a : ℕ) (hab : a + b ≤ 4) {σ : ℝ}
    (hσ : σ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (hint : MeasureTheory.IntegrableOn
      (fun s => (Work.Spaces.mixed (b + 1) a f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      Work.Spaces.Iz) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Spaces.mixed b a f z σ) ^ 2
        ≤ ∫ s in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) a f s σ) ^ 2 * (Work.Spaces.w s) ^ 2 := by
  intro z hz
  have hcd : ContDiffOn ℝ 1 (fun s => Work.Spaces.mixed b a f s σ) (Set.Ioi (0 : ℝ)) :=
    (((hsq.mixed b a).curry_z hσ).of_le
      (by simp [Work.Stability.smoothOrder])).mono (Set.Ioi_subset_Ioi (by norm_num))
  have hdec' : Filter.Tendsto (fun s => Work.Spaces.mixed b a f s σ) Filter.atTop (nhds 0) :=
    hdec.2 a b hab σ ⟨le_of_lt hσ.1, le_of_lt hσ.2⟩
  have hDz : ∀ s : ℝ,
      s * deriv (fun z' => Work.Spaces.mixed b a f z' σ) s
        = Work.Spaces.mixed (b + 1) a f s σ := by
    intro s
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
  have hint' : MeasureTheory.IntegrableOn
      (fun s => (s * deriv (fun z' => Work.Spaces.mixed b a f z' σ) s) ^ 2
        * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz := by
    refine hint.congr_fun ?_ measurableSet_Ici
    intro s _
    simp only [← hDz s]
  exact Work.FTS.H2.HQ.HardyZQ (fun s => Work.Spaces.mixed b a f s σ) hcd hdec' hint' z hz

/-! ## The angular average and the angular Hardy integral of a mixed slot

Both are bounded by `HkSq α 4 f`, uniformly in `z > 0`; the proofs are the same Hardy step
(`hardyZQ_mixed_slice`) followed by the pointwise domination of the resulting `s`-integral by
the `θ`-slice of `HkIntegrand`, summed over `θ` with the swap `HkSqSwapQ`. -/

/-- The angular slice of `(D_z^b D_θ^a f)²` is integrable on `Iθ`, for `z > 0`. -/
theorem avgIntegrand_integrable (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ)
    (hsq : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α 4 f)
    (b a : ℕ) (hab : a + b ≤ 2) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.mixed b a f z σ) ^ 2)
      Work.Spaces.Iθ := by
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := by
    show (-1 : ℝ) < z
    linarith
  refine MeasureTheory.Integrable.mono' (hmem.1 z (le_of_lt hz)) ?_ ?_
  · have hcd : ContinuousOn (fun σ => Work.Spaces.mixed b a f z σ) (Set.Ioo (0 : ℝ) (π / 2)) :=
      ((hsq.mixed b a).curry_θ hz1).continuousOn
    exact aesm_Iθ_of_continuousOn (g := fun σ => (Work.Spaces.mixed b a f z σ) ^ 2)
      (hcd.pow 2)
  · filter_upwards [ae_mem_Ioo_Iθ] with σ hσ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact mixed_sq_le_HkIntegrand α hα f b a (by omega) hz hσ.1 hσ.2

/-- The angular average of `(D_z^b D_θ^a f)²` is bounded by `HkSq α 4 f`, for `z > 0` and
`a + b ≤ 2`. -/
theorem avg_le_HkSq (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ)
    (hsq : Work.FTS.LocData.SmoothQuad f) (hdec : Work.Spaces.DecayAll 4 f)
    (hmem : Work.Spaces.HkMem α 4 f) (b a : ℕ) (hab : a + b ≤ 2) {z : ℝ} (hz : 0 < z) :
    ∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f z σ) ^ 2 ≤ Work.Spaces.HkSq α 4 f := by
  obtain ⟨hswap, hΨint, hsliceae⟩ := HkSqSwapQ α f hsq hmem
  have hpoint : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.mixed b a f z σ) ^ 2
        ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
    filter_upwards [hsliceae, ae_mem_Ioo_Iθ] with σ hslice hσ
    have hsliceL : MeasureTheory.IntegrableOn
        (fun s => (Work.Spaces.mixed (b + 1) a f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
        Work.Spaces.Iz := by
      refine MeasureTheory.Integrable.mono' hslice ?_ ?_
      · have h1 : ContinuousOn (fun s : ℝ => Work.Spaces.mixed (b + 1) a f s σ)
            (Set.Ioi (0 : ℝ)) :=
          (((hsq.mixed (b + 1) a).curry_z hσ).continuousOn).mono
            (Set.Ioi_subset_Ioi (by norm_num))
        have h2 : ContinuousOn (fun s : ℝ => Work.Spaces.w s) (Set.Ioi (0 : ℝ)) := by
          unfold Work.Spaces.w
          refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
            (continuousOn_id.pow 2) (fun s hs => pow_ne_zero 2 (ne_of_gt hs))
        exact aesm_Iz_of_continuousOn ((h1.pow 2).mul (h2.pow 2))
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun s hs => ?_)
        rcases eq_or_lt_of_le (show (0 : ℝ) ≤ s from hs) with h0 | hpos
        · subst h0
          have hw0 : Work.Spaces.w (0 : ℝ) = 0 := by simp [Work.Spaces.w]
          simp only [hw0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, norm_zero]
          exact Work.Spaces.HkIntegrand_nonneg α 4 f 0 σ
        · rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
          exact mixed_sq_w_sq_le_HkIntegrand α hα f (b + 1) a (by omega) hpos hσ.1 hσ.2
    have hHZ := hardyZQ_mixed_slice f hsq hdec b a (by omega) hσ hsliceL z hz
    have hcmp : (∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed (b + 1) a f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
        ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
      refine MeasureTheory.integral_mono_ae hsliceL hslice ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun s hs => ?_)
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ s from hs) with h0 | hpos
      · subst h0
        have hw0 : Work.Spaces.w (0 : ℝ) = 0 := by simp [Work.Spaces.w]
        simp only [hw0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
        exact Work.Spaces.HkIntegrand_nonneg α 4 f 0 σ
      · exact mixed_sq_w_sq_le_HkIntegrand α hα f (b + 1) a (by omega) hpos hσ.1 hσ.2
    exact le_trans hHZ hcmp
  have hmono := MeasureTheory.integral_mono_ae
    (avgIntegrand_integrable α hα f hsq hmem b a hab hz) hΨint hpoint
  calc ∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f z σ) ^ 2
      ≤ ∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
          Work.Spaces.HkIntegrand α 4 f s σ := hmono
    _ = Work.Spaces.HkSq α 4 f := hswap

/-! ## `∂_θ` versus `D_θ` in the interior class -/

/-- `sin(2θ)·∂_θ(D_z^bD_θ^a f) = D_z^bD_θ^{a+1} f` on the open quadrant: the plain
`θ`-derivative of a mixed derivative is the next mixed derivative divided by `sin(2θ)`. -/
theorem sin_mul_pth_mixed_quad (f : ℝ → ℝ → ℝ) (hsq : Work.FTS.LocData.SmoothQuad f)
    (b a : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed b a f) z θ
      = Work.Spaces.mixed b (a + 1) f z θ := by
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hθ0, hθ1⟩
  have h := Work.H2.WPQ.Dth_DzIter_comm_smoothQuad (g := Work.Spaces.DthIter a f)
    (hsq.DthIter a) b (le_of_lt hz) hθ
  have h2 : Work.Spaces.mixed b 1 (Work.Spaces.DthIter a f)
      = Work.Spaces.mixed b (a + 1) f := by
    simp only [Work.Spaces.mixed]
    rw [Work.Spaces.DthIter_add_right (1) a f, Nat.add_comm (1 : ℕ) a]
  have h1 : Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
      = Work.Spaces.mixed b (a + 1) f z θ := by
    rw [← h2]
    exact h
  simpa only [Work.Spaces.Dth] using h1

/-- The weight bookkeeping that turns `∂_θ` into `D_θ` on the open quadrant:
`(∂_θu)² sin(2θ)^{2-γ} = (D_θu)² sin(2θ)^{-γ}`. -/
theorem pth_sq_sin_eq_quad (α : ℝ) (f : ℝ → ℝ → ℝ) (hsq : Work.FTS.LocData.SmoothQuad f)
    (b a : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    (Work.Spaces.pth (Work.Spaces.mixed b a f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      = (Work.Spaces.mixed b (a + 1) f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hkey := sin_mul_pth_mixed_quad f hsq b a hz hθ0 hθ1
  have hD : Work.Spaces.pth (Work.Spaces.mixed b a f) z θ
      = Work.Spaces.mixed b (a + 1) f z θ / Real.sin (2 * θ) := by
    rw [eq_div_iff (ne_of_gt hsin), mul_comm]
    exact hkey
  have hsplit : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * θ)) ^ (2 : ℕ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [show (2 : ℝ) - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring,
      Real.rpow_add hsin, Real.rpow_two]
  rw [hD, hsplit, div_pow]
  field_simp

/-! ## The boundedness of the angular Hardy integral -/

/-- At every angle `σ ∈ (0,π/2)`, the angular Hardy integrand of a mixed slot of order `≤ 2` is
dominated by the `σ`-slice of the `ℋ⁴`-integrand, provided that slice is integrable. -/
theorem ang_slice_le_avg (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ)
    (hsq : Work.FTS.LocData.SmoothQuad f) (hdec : Work.Spaces.DecayAll 4 f)
    (b a : ℕ) (hab : a + b ≤ 2) {z σ : ℝ} (hz : 0 < z) (hσ : σ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (hslice : MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α 4 f s σ)
      Work.Spaces.Iz) :
    (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
      ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
  have hsin : 0 < Real.sin (2 * σ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
  have hsliceL : MeasureTheory.IntegrableOn
      (fun s => (Work.Spaces.mixed (b + 1) (a + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' hslice ?_ ?_
    · have h1 : ContinuousOn (fun s : ℝ => Work.Spaces.mixed (b + 1) (a + 1) f s σ)
          (Set.Ioi (0 : ℝ)) :=
        (((hsq.mixed (b + 1) (a + 1)).curry_z hσ).continuousOn).mono
          (Set.Ioi_subset_Ioi (by norm_num))
      have h2 : ContinuousOn (fun s : ℝ => Work.Spaces.w s) (Set.Ioi (0 : ℝ)) := by
        unfold Work.Spaces.w
        refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
          (continuousOn_id.pow 2) (fun s hs => pow_ne_zero 2 (ne_of_gt hs))
      exact aesm_Iz_of_continuousOn ((h1.pow 2).mul (h2.pow 2))
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun s hs => ?_)
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ s from hs) with h0 | hpos
      · subst h0
        have hw0 : Work.Spaces.w (0 : ℝ) = 0 := by simp [Work.Spaces.w]
        simp only [hw0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, norm_zero]
        exact Work.Spaces.HkIntegrand_nonneg α 4 f 0 σ
      · rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        exact mixed_sq_w_sq_le_HkIntegrand α hα f (b + 1) (a + 1) (by omega) hpos hσ.1 hσ.2
  have hHZ := hardyZQ_mixed_slice f hsq hdec b (a + 1) (by omega) hσ hsliceL z hz
  have hwe := pth_sq_sin_eq_quad α f hsq b a hz hσ.1 hσ.2
  rw [hwe]
  have hsnn : 0 ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
    Real.rpow_nonneg (le_of_lt hsin) _
  have hmul : (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      ≤ (∫ s in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) (a + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
    mul_le_mul_of_nonneg_right hHZ hsnn
  rw [← MeasureTheory.integral_mul_const] at hmul
  refine le_trans hmul ?_
  refine MeasureTheory.integral_mono_ae (hsliceL.mul_const _) hslice ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun s hs => ?_)
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ s from hs) with h0 | hpos
  · subst h0
    have hw0 : Work.Spaces.w (0 : ℝ) = 0 := by simp [Work.Spaces.w]
    simp only [hw0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul]
    exact Work.Spaces.HkIntegrand_nonneg α 4 f 0 σ
  · show (Work.Spaces.mixed (b + 1) (a + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) ≤ Work.Spaces.HkIntegrand α 4 f s σ
    rw [mul_assoc, ← Wt_sq_eq α s σ hsin, ← mul_pow]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f s σ (a + 1) (b + 1) (by omega) (by omega)

/-- The angular Hardy integrand of a mixed slot of order `≤ 2` is integrable on `Iθ`. -/
theorem angIntegrand_integrable (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ)
    (hsq : Work.FTS.LocData.SmoothQuad f) (hdec : Work.Spaces.DecayAll 4 f)
    (hmem : Work.Spaces.HkMem α 4 f) (b a : ℕ) (hab : a + b ≤ 2) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun σ => (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  obtain ⟨hswap, hΨint, hsliceae⟩ := HkSqSwapQ α f hsq hmem
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := by
    show (-1 : ℝ) < z
    linarith
  refine MeasureTheory.Integrable.mono' hΨint ?_ ?_
  · have hpthsq : Work.FTS.LocData.SmoothQuad (Work.Spaces.pth (Work.Spaces.mixed b a f)) :=
      Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU (hsq.mixed b a)
    have h1 : ContinuousOn (fun σ : ℝ => Work.Spaces.pth (Work.Spaces.mixed b a f) z σ)
        (Set.Ioo (0 : ℝ) (π / 2)) :=
      ((hpthsq.curry_θ hz1)).continuousOn
    have h2 : ContinuousOn (fun σ : ℝ => (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
        (Set.Ioo (0 : ℝ) (π / 2)) := by
      refine ((Real.continuous_sin.comp
        (continuous_const.mul continuous_id)).continuousOn).rpow_const ?_
      intro σ hσ
      have hpos : 0 < Real.sin (2 * σ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
      exact Or.inl (ne_of_gt hpos)
    exact aesm_Iθ_of_continuousOn ((h1.pow 2).mul h2)
  · filter_upwards [hsliceae, ae_mem_Ioo_Iθ] with σ hslice hσ
    have hsin : 0 < Real.sin (2 * σ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
    have hnn : 0 ≤ (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hsin) _)
    rw [Real.norm_of_nonneg hnn]
    exact ang_slice_le_avg α hα f hsq hdec b a hab hz hσ hslice

/-- The angular Hardy integral of `∂_θ(D_z^bD_θ^a f)` is bounded by `HkSq α 4 f`. -/
theorem ang_le_HkSq (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ)
    (hsq : Work.FTS.LocData.SmoothQuad f) (hdec : Work.Spaces.DecayAll 4 f)
    (hmem : Work.Spaces.HkMem α 4 f) (b a : ℕ) (hab : a + b ≤ 2) {z : ℝ} (hz : 0 < z) :
    ∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) ≤ Work.Spaces.HkSq α 4 f := by
  obtain ⟨hswap, hΨint, hsliceae⟩ := HkSqSwapQ α f hsq hmem
  have hpoint : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
    filter_upwards [hsliceae, ae_mem_Ioo_Iθ] with σ hslice hσ
    exact ang_slice_le_avg α hα f hsq hdec b a hab hz hσ hslice
  have hmono := MeasureTheory.integral_mono_ae
    (angIntegrand_integrable α hα f hsq hdec hmem b a hab hz) hΨint hpoint
  calc ∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
      ≤ ∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
          Work.Spaces.HkIntegrand α 4 f s σ := hmono
    _ = Work.Spaces.HkSq α 4 f := hswap

/-! ## A point of the middle half of `Iθ` with value at most the average -/

/-- Some point of the middle half `[π/8, 3π/8]` of `Iθ` has value at most `(4/π)` times the
integral of a nonnegative integrable function. -/
theorem exists_Icc_min_le_avg {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Set.Icc (π / 8) (3 * π / 8)))
    (hint : MeasureTheory.IntegrableOn φ Work.Spaces.Iθ)
    (hnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ φ θ) :
    ∃ θ₀ ∈ Set.Icc (π / 8) (3 * π / 8),
      φ θ₀ ≤ (4 / Real.pi) * ∫ θ in Work.Spaces.Iθ, φ θ := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hle : π / 8 ≤ 3 * π / 8 := by linarith
  obtain ⟨θ₀, hθ₀, hmin⟩ :=
    (isCompact_Icc (a := π / 8) (b := 3 * π / 8)).exists_isMinOn
      ⟨π / 8, by simp only [Set.mem_Icc]; exact ⟨le_rfl, hle⟩⟩ hcont
  refine ⟨θ₀, hθ₀, ?_⟩
  have hsub : Set.Icc (π / 8) (3 * π / 8) ⊆ Work.Spaces.Iθ := by
    intro x hx
    simp only [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hmeas : MeasurableSet (Set.Icc (π / 8) (3 * π / 8)) := measurableSet_Icc
  have hIccint : MeasureTheory.IntegrableOn φ (Set.Icc (π / 8) (3 * π / 8)) :=
    hcont.integrableOn_compact isCompact_Icc
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => φ θ₀)
      (Set.Icc (π / 8) (3 * π / 8)) :=
    integrableOn_const (μ := MeasureTheory.volume)
      (isCompact_Icc (a := π / 8) (b := 3 * π / 8)).measure_lt_top.ne (by simp)
  have hmono : ∫ θ in Set.Icc (π / 8) (3 * π / 8), φ θ₀
      ≤ ∫ θ in Set.Icc (π / 8) (3 * π / 8), φ θ :=
    setIntegral_mono_on hconst hIccint hmeas (fun θ hθ => hmin hθ)
  have hval : ∫ θ in Set.Icc (π / 8) (3 * π / 8), φ θ₀ = φ θ₀ * (π / 4) := by
    rw [setIntegral_const, MeasureTheory.Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 3 * π / 8 - π / 8)]
    ring
  have h2 : (∫ θ in Set.Icc (π / 8) (3 * π / 8), φ θ)
      ≤ ∫ θ in Work.Spaces.Iθ, φ θ := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
    exact MeasureTheory.setIntegral_mono_set hint
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hnn)
      (Filter.Eventually.of_forall (fun x hx => hsub hx))
  have h3 : φ θ₀ * (π / 4) ≤ ∫ θ in Work.Spaces.Iθ, φ θ := by
    rw [← hval]
    exact hmono.trans h2
  have h4 : φ θ₀ ≤ (∫ θ in Work.Spaces.Iθ, φ θ) / (π / 4) :=
    (le_div_iff₀ (by linarith : (0 : ℝ) < π / 4)).mpr (by linarith [h3])
  calc φ θ₀ ≤ (∫ θ in Work.Spaces.Iθ, φ θ) / (π / 4) := h4
    _ = (4 / Real.pi) * ∫ θ in Work.Spaces.Iθ, φ θ := by
        rw [div_eq_mul_inv, inv_div]
        ring

/-! ## The target -/

/-- For a `SmoothQuad` datum `f` of class `ℋ⁴` with `DecayAll`, every mixed derivative `D_z^bD_θ^a f` with `a + b ≤ 2` is bounded on the *open* quadrant by `C/(γ-1)·|f|²_{ℋ⁴}` (in squared form), with `C` universal: this is Elgindi's Corollary `SecondDerivativesBounded` in the interior class.  Route (avoiding the boundary-vanishing hypothesis of `HardyThetaQ`): at `z > 0` and `b + a ≤ 2` the angular oscillation bound `OscSqLe` applied to the slice `θ ↦ D_z^bD_θ^a f z θ` gives
`(u z θ)² ≤ 2u(z,θ₀)² + (200/(γ-1))·∫_θ (∂_θu(z,σ))²sin(2σ)^{2-γ}` for some `θ₀ ∈ (0,π/2)`, where `u(z,θ₀)² ≤ (2/π)∫_θu(z,σ)²dσ` (a minimum exists because `u(z,·)` is continuous on the open interval and integrable); then the radial Hardy inequality `HQ.HardyZQ` applied to the `z`-slice `z' ↦ u(z',θ)` (decay from `DecayAll`) bounds `u(z,θ)² ≤ ∫_{z'}(D_zu(z',θ))²w(z')²` uniformly in `z` and `θ`, and both θ-integrals are bounded by `HkSq α 4 f` (`D_zu` is the slot `D_z^{b+1}D_θ^af`, `∂_θu` turns into the slot `D_z^bD_θ^{a+1}f` through `(∂_θu)²sin(2σ)^{2-γ} = (D_θu)²sin(2σ)^{-γ}`). -/
theorem PwBdQ : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 →
    Work.FTS.LocData.SmoothQuad f → Work.Spaces.DecayAll 4 f → Work.Spaces.HkMem α 4 f →
    Work.FTS.H2.HQ.PwBd α f C := by
  refine ⟨204, by norm_num, ?_⟩
  intro α f hα hα1 hsq hdec hmem
  refine ⟨by norm_num, ?_⟩
  intro b a hab z hz θ hθ0 hθ1
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := by
    show (-1 : ℝ) < z
    linarith
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hγ1le : Work.Spaces.gam α - 1 ≤ 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hHk : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  -- the `θ`-slice of `u := mixed b a f` at `z`
  have hslice_cont : ContinuousOn (fun σ : ℝ => Work.Spaces.mixed b a f z σ)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    ((hsq.mixed b a).curry_θ hz1).continuousOn
  have hcontφ : ContinuousOn (fun σ : ℝ => (Work.Spaces.mixed b a f z σ) ^ 2)
      (Set.Icc (π / 8) (3 * π / 8)) :=
    (hslice_cont.mono (by
      intro x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)).pow 2
  obtain ⟨θ₀, hθ₀mem, hθ₀le⟩ :=
    exists_Icc_min_le_avg (φ := fun σ => (Work.Spaces.mixed b a f z σ) ^ 2)
      hcontφ (avgIntegrand_integrable α hα f hsq hmem b a hab hz) (fun σ _ => sq_nonneg _)
  have hθ₀Ioo : θ₀ ∈ Set.Ioo (0 : ℝ) (π / 2) :=
    ⟨by linarith [hθ₀mem.1, Real.pi_pos], by linarith [hθ₀mem.2, Real.pi_pos]⟩
  have huIcc : Set.uIcc θ θ₀ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith [hθ0, h1], by linarith [h2, hθ₀Ioo.2]⟩
    · exact ⟨by linarith [hθ₀Ioo.1, h1], by linarith [h2, hθ1]⟩
  have hderiv : ∀ x ∈ Set.uIcc θ θ₀,
      HasDerivAt (fun σ : ℝ => Work.Spaces.mixed b a f z σ)
        (deriv (fun σ : ℝ => Work.Spaces.mixed b a f z σ) x) x := by
    intro x hx
    have hxIoo := huIcc hx
    have hd : DifferentiableOn ℝ (fun σ : ℝ => Work.Spaces.mixed b a f z σ)
        (Set.Ioo (0 : ℝ) (π / 2)) :=
      ((hsq.mixed b a).curry_θ hz1).differentiableOn
        Work.FTS.LocData.smoothOrder_ne_zero
    exact (hd.differentiableAt (isOpen_Ioo.mem_nhds hxIoo)).hasDerivAt
  have hcontd : ContinuousOn (deriv (fun σ : ℝ => Work.Spaces.mixed b a f z σ))
      (Set.uIcc θ θ₀) := by
    have hpthsq : Work.FTS.LocData.SmoothQuad (Work.Spaces.pth (Work.Spaces.mixed b a f)) :=
      Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU (hsq.mixed b a)
    have hpth : ContinuousOn (fun σ : ℝ => Work.Spaces.pth (Work.Spaces.mixed b a f) z σ)
        (Set.Ioo (0 : ℝ) (π / 2)) :=
      (hpthsq.curry_θ hz1).continuousOn
    exact hpth.mono huIcc
  have hosc := Work.FTS.H2.OscSqLe α hα hα1 (fun σ : ℝ => Work.Spaces.mixed b a f z σ)
    ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    (⟨le_of_lt hθ₀Ioo.1, le_of_lt hθ₀Ioo.2⟩ : θ₀ ∈ Work.Spaces.Iθ)
    hderiv hcontd (angIntegrand_integrable α hα f hsq hdec hmem b a hab hz)
  have hAvg := avg_le_HkSq α hα f hsq hdec hmem b a hab hz
  have hAng := ang_le_HkSq α hα f hsq hdec hmem b a hab hz
  have h1 : (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ 2 * (Work.Spaces.mixed b a f z θ - Work.Spaces.mixed b a f z θ₀) ^ 2
        + 2 * (Work.Spaces.mixed b a f z θ₀) ^ 2 := by
    nlinarith [sq_nonneg (Work.Spaces.mixed b a f z θ - 2 * Work.Spaces.mixed b a f z θ₀)]
  have h2 := mul_le_mul_of_nonneg_left hosc (by norm_num : (0 : ℝ) ≤ 2)
  have h3 := mul_le_mul_of_nonneg_left hθ₀le (by norm_num : (0 : ℝ) ≤ 2)
  have hcoef : 200 / (Work.Spaces.gam α - 1) + 8 / Real.pi
      ≤ 204 / (Work.Spaces.gam α - 1) := by
    have h8 : 8 / Real.pi ≤ 8 / Real.pi / (Work.Spaces.gam α - 1) := by
      have h8nn : 0 ≤ 8 / Real.pi := by positivity
      rw [le_div_iff₀ hγ1]
      nlinarith [hγ1le, h8nn]
    have h200 : 200 / (Work.Spaces.gam α - 1) + 8 / Real.pi / (Work.Spaces.gam α - 1)
        = (200 + 8 / Real.pi) / (Work.Spaces.gam α - 1) := by ring
    have h8pi : 8 / Real.pi ≤ 4 := by
      rw [div_le_iff₀ Real.pi_pos]
      linarith [Real.pi_gt_three]
    have hfin : (200 + 8 / Real.pi) / (Work.Spaces.gam α - 1)
        ≤ 204 / (Work.Spaces.gam α - 1) :=
      div_le_div_of_nonneg_right (by linarith) hγ1.le
    linarith [h8, h200, hfin]
  calc (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ 2 * (Work.Spaces.mixed b a f z θ - Work.Spaces.mixed b a f z θ₀) ^ 2
        + 2 * (Work.Spaces.mixed b a f z θ₀) ^ 2 := h1
    _ ≤ 2 * ((100 / (Work.Spaces.gam α - 1))
            * ∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
                * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
        + 2 * ((4 / Real.pi)
            * ∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f z σ) ^ 2) :=
        add_le_add h2 h3
    _ = (200 / (Work.Spaces.gam α - 1))
          * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
              * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
        + (8 / Real.pi) * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f z σ) ^ 2) := by
        ring
    _ ≤ (200 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f
        + (8 / Real.pi) * Work.Spaces.HkSq α 4 f := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left hAng (by positivity)
        · exact mul_le_mul_of_nonneg_left hAvg (by positivity)
    _ ≤ (204 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := by
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_right hcoef hHk

end Work.H2.T1Q
