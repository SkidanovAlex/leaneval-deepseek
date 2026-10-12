import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.NewtonId
import Submission.RadialHarmonic
import Submission.ScatG
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Newton-potential representation of the scattering solution (Layer 3)
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

set_option maxHeartbeats 800000

open Filter Metric MeasureTheory Laplacian MeasureTheory.Measure
open scoped ContDiff Topology Real ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The Newton kernel `(x,y) ↦ ‖x−y‖⁻¹` (real valued, `0⁻¹ = 0`). -/
def nPotKernel (x y : ℝ³) : ℝ := (‖x - y‖ : ℝ)⁻¹

lemma nPotKernel_nonneg (x y : ℝ³) : 0 ≤ nPotKernel x y := by
  dsimp [nPotKernel]
  exact inv_nonneg.mpr (norm_nonneg _)

lemma nPotKernel_symm (x y : ℝ³) : nPotKernel x y = nPotKernel y x := by
  dsimp [nPotKernel]
  congr 1
  rw [norm_sub_rev]

lemma nPotKernel_measurable : Measurable fun p : ℝ³ × ℝ³ => nPotKernel p.1 p.2 := by
  dsimp [nPotKernel]
  refine Measurable.inv ?_
  exact measurable_norm.comp ((measurable_fst : Measurable fun p : ℝ³ × ℝ³ => p.1).sub measurable_snd)

lemma nPotKernel_measurable_left (y : ℝ³) : Measurable fun x : ℝ³ => nPotKernel x y := by
  dsimp [nPotKernel]
  refine Measurable.inv ?_
  exact measurable_norm.comp ((measurable_id : Measurable fun x : ℝ³ => x).sub measurable_const)

lemma nPotKernel_measurable_right (x : ℝ³) : Measurable fun y : ℝ³ => nPotKernel x y := by
  dsimp [nPotKernel]
  refine Measurable.inv ?_
  exact measurable_norm.comp (measurable_const.sub (measurable_id : Measurable fun y : ℝ³ => y))

/-- The extended norm of a real is `ofReal |·|`. -/
lemma enorm_real (r : ℝ) : ‖(r : ℝ)‖ₑ = ENNReal.ofReal |r| := by
  exact Real.enorm_eq_ofReal_abs r

/-- `∫⁻ z in ball 0 T, ‖z‖⁻¹ < ∞` for `0 ≤ T` (dimension three). -/
lemma lintegral_inv_norm_ball_ofReal_lt_top (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ x : ℝ³ in ball (0 : ℝ³) T, ENNReal.ofReal ((‖x‖ : ℝ)⁻¹)) < (⊤ : ℝ≥0∞) := by
  have hI : IntegrableOn (fun x : ℝ³ => (‖x‖ : ℝ)⁻¹) (ball (0 : ℝ³) T) := by
    exact integrableOn_inv_norm_ball T hT
  have hI' : Integrable (fun x : ℝ³ => (‖x‖ : ℝ)⁻¹) (volume.restrict (ball (0 : ℝ³) T)) := hI
  have hfin : (∫⁻ x : ℝ³, ‖((‖x‖ : ℝ)⁻¹ : ℝ)‖ₑ ∂(volume.restrict (ball (0 : ℝ³) T))) < (⊤ : ℝ≥0∞) :=
    hI'.hasFiniteIntegral
  convert hfin using 1
  apply lintegral_congr
  intro x
  rw [enorm_real]
  rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]

/-- The extended-norm form of the Newton kernel (equals `ofReal` by nonnegativity). -/
def kernEN (x y : ℝ³) : ℝ≥0∞ := ENNReal.ofReal (nPotKernel x y)

lemma kernEN_ofReal (x y : ℝ³) : kernEN x y = ENNReal.ofReal (nPotKernel x y) := rfl

/-- The extended-norm form of `|g|`. -/
def gEN (g : ℝ³ → ℝ) (y : ℝ³) : ℝ≥0∞ := ‖(g y : ℝ)‖ₑ

lemma gEN_ofReal_abs (g : ℝ³ → ℝ) (y : ℝ³) : gEN g y = ENNReal.ofReal |g y| := by
  exact enorm_real (g y)

/-- For fixed `y`, the integral over `x ∈ ball 0 M` of the kernel is bounded by
the same kernel integrated over the ball `ball 0 (M + ‖y‖)` (translation). -/
lemma kernel_lintegral_ball_le (y : ℝ³) (M : ℝ) :
    (∫⁻ x in ball (0 : ℝ³) M, kernEN x y) ≤
    (∫⁻ z in ball (0 : ℝ³) (M + ‖y‖), ENNReal.ofReal ((‖z‖ : ℝ)⁻¹)) := by
  have hstepA :
      (∫⁻ x in ball (0 : ℝ³) M, kernEN x y)
        = ∫⁻ x : ℝ³, (ball (0 : ℝ³) M).indicator (fun x : ℝ³ => kernEN x y) x := by
    exact (MeasureTheory.lintegral_indicator measurableSet_ball (f := fun x : ℝ³ => kernEN x y)).symm
  have hpt : ∀ x : ℝ³,
      (ball (0 : ℝ³) M).indicator (fun x : ℝ³ => kernEN x y) x ≤
      (ball (0 : ℝ³) (M + ‖y‖)).indicator (fun z : ℝ³ => ENNReal.ofReal ((‖z‖ : ℝ)⁻¹)) (x - y) := by
    intro x
    by_cases hx : x ∈ ball (0 : ℝ³) M
    · have hxM : ‖x‖ < M := by simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg] using hx
      have hlt : ‖x - y‖ < M + ‖y‖ := by
        have h1 : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
        nlinarith
      have hmem : x - y ∈ ball (0 : ℝ³) (M + ‖y‖) := by
        simpa [Metric.mem_ball, dist_eq_norm] using hlt
      simp [kernEN, nPotKernel, hx, hmem]
    · simp [kernEN, hx]
  have hstepC :
      (∫⁻ x : ℝ³, (ball (0 : ℝ³) (M + ‖y‖)).indicator (fun z : ℝ³ => ENNReal.ofReal ((‖z‖ : ℝ)⁻¹)) (x - y))
        = ∫⁻ x : ℝ³, (ball (0 : ℝ³) (M + ‖y‖)).indicator (fun z : ℝ³ => ENNReal.ofReal ((‖z‖ : ℝ)⁻¹)) x := by
    have := MeasureTheory.lintegral_add_right_eq_self (μ := (volume : Measure ℝ³))
      (f := fun z : ℝ³ => (ball (0 : ℝ³) (M + ‖y‖)).indicator (fun z : ℝ³ => ENNReal.ofReal ((‖z‖ : ℝ)⁻¹)) z) (-y)
    simpa [sub_eq_add_neg] using this
  calc
    (∫⁻ x in ball (0 : ℝ³) M, kernEN x y)
        = ∫⁻ x : ℝ³, (ball (0 : ℝ³) M).indicator (fun x : ℝ³ => kernEN x y) x := hstepA
    _ ≤ ∫⁻ x : ℝ³, (ball (0 : ℝ³) (M + ‖y‖)).indicator (fun z : ℝ³ => ENNReal.ofReal ((‖z‖ : ℝ)⁻¹)) (x - y) := by
        exact MeasureTheory.lintegral_mono hpt
    _ = ∫⁻ x : ℝ³, (ball (0 : ℝ³) (M + ‖y‖)).indicator (fun z : ℝ³ => ENNReal.ofReal ((‖z‖ : ℝ)⁻¹)) x := hstepC
    _ = ∫⁻ z in ball (0 : ℝ³) (M + ‖y‖), ENNReal.ofReal ((‖z‖ : ℝ)⁻¹) :=
        MeasureTheory.lintegral_indicator measurableSet_ball (f := fun z : ℝ³ => ENNReal.ofReal ((‖z‖ : ℝ)⁻¹))

/-- S(T) is increasing in `T`. -/
lemma lpot_mono_T {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    (∫⁻ z in ball (0 : ℝ³) T₁, ENNReal.ofReal ((‖z‖ : ℝ)⁻¹)) ≤
    (∫⁻ z in ball (0 : ℝ³) T₂, ENNReal.ofReal ((‖z‖ : ℝ)⁻¹)) := by
  exact MeasureTheory.lintegral_mono' (Measure.restrict_mono (Metric.ball_subset_ball hT) (le_refl volume))
    (le_refl _)

/-- ENNReal-valued double integral of `|g(y)|·‖x−y‖⁻¹` over `(ball 0 M) × ℝ³`
is finite (`g` integrable with `g = 0` outside `closedBall 0 R`). -/
lemma kernel_abs_lintegral_prod_lt_top {g : ℝ³ → ℝ} {R M : ℝ} (hg : Integrable g)
    (hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0) (hR : 0 ≤ R) (hM : 0 ≤ M) :
    (∫⁻ z : ℝ³ × ℝ³, gEN g z.2 * kernEN z.1 z.2
      ∂((volume.restrict (ball (0 : ℝ³) M)).prod volume)) < (⊤ : ℝ≥0∞) := by
  let S : ℝ → ℝ≥0∞ := fun T => ∫⁻ z : ℝ³, ENNReal.ofReal ((‖z‖ : ℝ)⁻¹)
      ∂(volume.restrict (ball (0 : ℝ³) T))
  have hinner (y : ℝ³) (hy : ‖y‖ ≤ R) :
      (∫⁻ x : ℝ³, kernEN x y ∂(volume.restrict (ball (0 : ℝ³) M))) ≤ S (M + R) := by
    calc
      (∫⁻ x : ℝ³, kernEN x y ∂(volume.restrict (ball (0 : ℝ³) M))) ≤ S (M + ‖y‖) := by
        simpa [S] using (kernel_lintegral_ball_le y M)
      _ ≤ S (M + R) := lpot_mono_T (by linarith)
  have hSfin : S (M + R) < (⊤ : ℝ≥0∞) := by
    dsimp [S]
    exact lintegral_inv_norm_ball_ofReal_lt_top (M + R) (by linarith)
  have hae_g : AEMeasurable (fun z : ℝ³ × ℝ³ => gEN g z.2)
      ((volume.restrict (ball (0 : ℝ³) M)).prod volume) := by
    dsimp [gEN]
    have hgA : AEStronglyMeasurable (fun z : ℝ³ × ℝ³ => g z.2)
        ((volume.restrict (ball (0 : ℝ³) M)).prod volume) := by
      exact (hg.aestronglyMeasurable.comp_snd (μ := volume.restrict (ball (0 : ℝ³) M)) (ν := volume))
    exact hgA.enorm
  have hae_k : AEMeasurable (fun z : ℝ³ × ℝ³ => kernEN z.1 z.2)
      ((volume.restrict (ball (0 : ℝ³) M)).prod volume) := by
    dsimp [kernEN]
    exact ((ENNReal.measurable_ofReal.comp nPotKernel_measurable).aemeasurable)
  have hae : AEMeasurable (fun z : ℝ³ × ℝ³ => gEN g z.2 * kernEN z.1 z.2)
      ((volume.restrict (ball (0 : ℝ³) M)).prod volume) := by
    exact hae_g.mul hae_k
  have hm : (volume.restrict (ball (0 : ℝ³) M)).prod volume
        = (volume.prod volume).restrict ((ball (0 : ℝ³) M) ×ˢ (Set.univ : Set ℝ³)) := by
    rw [← Measure.prod_restrict (s := ball (0 : ℝ³) M) (t := (Set.univ : Set ℝ³))]
    rw [Measure.restrict_univ]
  have hsplit :
      (∫⁻ z : ℝ³ × ℝ³, gEN g z.2 * kernEN z.1 z.2
          ∂((volume.restrict (ball (0 : ℝ³) M)).prod volume))
        = ∫⁻ y : ℝ³, (∫⁻ x : ℝ³ in ball (0 : ℝ³) M, gEN g y * kernEN x y) := by
    let f : ℝ³ × ℝ³ → ℝ≥0∞ := fun z => gEN g z.2 * kernEN z.1 z.2
    have hfae : AEMeasurable f ((volume.prod volume).restrict ((ball (0 : ℝ³) M) ×ˢ (Set.univ : Set ℝ³))) := by
      simpa [hm] using hae
    calc
      (∫⁻ z : ℝ³ × ℝ³, gEN g z.2 * kernEN z.1 z.2
          ∂((volume.restrict (ball (0 : ℝ³) M)).prod volume))
          = ∫⁻ z : ℝ³ × ℝ³, f z ∂((volume.prod volume).restrict ((ball (0 : ℝ³) M) ×ˢ (Set.univ : Set ℝ³))) := by
              rw [hm]
      _ = ∫⁻ y : ℝ³, (∫⁻ x : ℝ³ in ball (0 : ℝ³) M, f (x, y)) := by
              simpa [f] using (MeasureTheory.setLIntegral_prod_symm (μ := (volume : Measure ℝ³)) (ν := (volume : Measure ℝ³))
                (s := ball (0 : ℝ³) M) (t := (Set.univ : Set ℝ³)) (f := f) hfae)
      _ = ∫⁻ y : ℝ³, (∫⁻ x : ℝ³ in ball (0 : ℝ³) M, gEN g y * kernEN x y) := by
          refine lintegral_congr (fun y => ?_)
          exact lintegral_congr (fun x => rfl)

  have hconst (y : ℝ³) :
      (∫⁻ x : ℝ³ in ball (0 : ℝ³) M, gEN g y * kernEN x y)
        = gEN g y * (∫⁻ x : ℝ³ in ball (0 : ℝ³) M, kernEN x y) := by
    have hmeas : Measurable (fun x : ℝ³ => kernEN x y) := by
      dsimp [kernEN]
      exact ENNReal.measurable_ofReal.comp (nPotKernel_measurable_left y)
    exact MeasureTheory.lintegral_const_mul'' (r := gEN g y)
      (f := fun x : ℝ³ => kernEN x y) hmeas.aemeasurable.restrict
  have hybound : (∫⁻ y : ℝ³, gEN g y * S (M + R)) < (⊤ : ℝ≥0∞) := by
    have hgfin0 : (∫⁻ y : ℝ³, ‖(g y : ℝ)‖ₑ) < (⊤ : ℝ≥0∞) := hg.hasFiniteIntegral
    have hgfin : (∫⁻ y : ℝ³, gEN g y) < (⊤ : ℝ≥0∞) := by
      simpa [gEN] using hgfin0
    have hgAem : AEMeasurable (fun y : ℝ³ => gEN g y) := by
      dsimp [gEN]
      exact hg.aestronglyMeasurable.enorm
    have hprod : (∫⁻ y : ℝ³, gEN g y * S (M + R)) = (∫⁻ y : ℝ³, gEN g y) * S (M + R) := by
      exact MeasureTheory.lintegral_mul_const'' (r := S (M + R)) hgAem
    rw [hprod]
    exact ENNReal.mul_lt_top hgfin hSfin
  calc
    (∫⁻ z : ℝ³ × ℝ³, gEN g z.2 * kernEN z.1 z.2
        ∂((volume.restrict (ball (0 : ℝ³) M)).prod volume))
    = ∫⁻ y : ℝ³, (∫⁻ x : ℝ³ in ball (0 : ℝ³) M, gEN g y * kernEN x y) := hsplit
    _ ≤ ∫⁻ y : ℝ³, gEN g y * S (M + R) := by
        refine lintegral_mono (fun y => ?_)
        rw [hconst y]
        by_cases hyR : ‖y‖ ≤ R
        · rcases em (gEN g y = 0) with hc | hc
          · simp [hc]
          · have hinf : gEN g y ≠ (∞ : ℝ≥0∞) := by
              rw [gEN_ofReal_abs]
              exact ENNReal.ofReal_ne_top
            exact (ENNReal.mul_le_mul_iff_right hc hinf).2 (hinner y hyR)
        · have hg0 : g y = 0 := hgsupp y (le_of_not_ge hyR)
          have hgEN0 : gEN g y = 0 := by
            rw [gEN_ofReal_abs, hg0, abs_zero, ENNReal.ofReal_zero]
          simp [hgEN0]
    _ < (⊤ : ℝ≥0∞) := hybound

/-- The (absolute) kernel product is Bochner-integrable on the restricted product
`(ball 0 M) × ℝ³` whenever `g ∈ L¹` with `g = 0` outside `closedBall 0 R`. -/
lemma kernel_abs_integrable_prod_ball {g : ℝ³ → ℝ} {R M : ℝ} (hg : Integrable g)
    (hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0) (hR : 0 ≤ R) (hM : 0 ≤ M) :
    Integrable (fun z : ℝ³ × ℝ³ => (|g z.2| * nPotKernel z.1 z.2 : ℝ))
      ((volume.restrict (ball (0 : ℝ³) M)).prod volume) := by
  have hAEs : AEStronglyMeasurable (fun z : ℝ³ × ℝ³ => (|g z.2| * nPotKernel z.1 z.2 : ℝ))
      ((volume.restrict (ball (0 : ℝ³) M)).prod volume) := by
    have h1 : AEStronglyMeasurable (fun z : ℝ³ × ℝ³ => (g z.2 : ℝ))
        ((volume.restrict (ball (0 : ℝ³) M)).prod volume) := by
      exact (hg.aestronglyMeasurable.comp_snd (μ := volume.restrict (ball (0 : ℝ³) M)) (ν := volume))
    have hk : AEStronglyMeasurable (fun z : ℝ³ × ℝ³ => (nPotKernel z.1 z.2 : ℝ))
        ((volume.restrict (ball (0 : ℝ³) M)).prod volume) := by
      exact nPotKernel_measurable.stronglyMeasurable.aestronglyMeasurable
    exact h1.norm.mul hk
  have hpt : ∀ z : ℝ³ × ℝ³, ‖(|g z.2| * nPotKernel z.1 z.2 : ℝ)‖ₑ
      = gEN g z.2 * kernEN z.1 z.2 := by
    intro z
    rw [enorm_real]
    rw [abs_of_nonneg (mul_nonneg (abs_nonneg (g z.2)) (nPotKernel_nonneg z.1 z.2))]
    rw [ENNReal.ofReal_mul (abs_nonneg (g z.2))]
    rw [gEN_ofReal_abs, kernEN_ofReal]
  have hfin : (∫⁻ z : ℝ³ × ℝ³, ‖(|g z.2| * nPotKernel z.1 z.2 : ℝ)‖ₑ
      ∂((volume.restrict (ball (0 : ℝ³) M)).prod volume)) < (⊤ : ℝ≥0∞) := by
    have := kernel_abs_lintegral_prod_lt_top (g := g) (R := R) (M := M) hg hgsupp hR hM
    convert this using 1
    apply lintegral_congr
    intro z
    exact hpt z
  exact ⟨hAEs, hfin⟩

/-- The `x`-marginal of the absolute kernel product is integrable on `ball 0 M`:
`x ↦ ∫_y |g y|·‖x−y‖⁻¹ dy ∈ L¹(ball 0 M)`. -/
lemma kernel_abs_marginal_integrableOn_ball {g : ℝ³ → ℝ} {R M : ℝ} (hg : Integrable g)
    (hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0) (hR : 0 ≤ R) (hM : 0 ≤ M) :
    IntegrableOn (fun x : ℝ³ => (∫ y : ℝ³, |g y| * nPotKernel x y))
      (ball (0 : ℝ³) M) := by
  have hprod := kernel_abs_integrable_prod_ball (g := g) (R := R) (M := M) hg hgsupp hR hM
  have hmar := hprod.integral_norm_prod_left
  have hmar' : Integrable (fun x : ℝ³ => (∫ y : ℝ³, ‖(|g y| * nPotKernel x y : ℝ)‖))
      (volume.restrict (ball (0 : ℝ³) M)) := by
    simpa using hmar
  have hcongr : (fun x : ℝ³ => ∫ y : ℝ³, ‖(|g y| * nPotKernel x y : ℝ)‖) =ᵐ[volume.restrict (ball (0 : ℝ³) M)]
      (fun x : ℝ³ => ∫ y : ℝ³, |g y| * nPotKernel x y) := by
    filter_upwards with x
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg (g y)) (nPotKernel_nonneg x y))]
  exact hmar'.congr hcongr

/-- For almost every `x ∈ ball 0 M`, `y ↦ |g y|·‖x−y‖⁻¹` is integrable. -/
lemma kernel_abs_slice_integrable_ae {g : ℝ³ → ℝ} {R M : ℝ} (hg : Integrable g)
    (hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0) (hR : 0 ≤ R) (hM : 0 ≤ M) :
    ∀ᵐ x ∂(volume.restrict (ball (0 : ℝ³) M)),
      Integrable (fun y : ℝ³ => (|g y| * nPotKernel x y : ℝ)) := by
  have hprod := kernel_abs_integrable_prod_ball (g := g) (R := R) (M := M) hg hgsupp hR hM
  have hslice := hprod.prod_right_ae
  filter_upwards [hslice] with x hx
  have hx' : Integrable (fun y : ℝ³ => (|g y| * nPotKernel x y : ℝ)) := by
    simpa using hx
  exact hx'



/-- The Newton potential `N_g(x) := (8π)⁻¹·∫_y g(y)·‖x−y‖⁻¹ dy`. -/
noncomputable def newtonPotential (g : ℝ³ → ℝ) (x : ℝ³) : ℝ :=
  (1 / (8 * π)) * (∫ y : ℝ³, g y * nPotKernel x y)

/-- Newton potential bound: `|N_g x| ≤ (8π)⁻¹·∫_y |g y|·‖x−y‖⁻¹`. -/
lemma newtonPotential_abs_le (g : ℝ³ → ℝ) (x : ℝ³) :
    |newtonPotential g x| ≤
      (1 / (8 * π)) * (∫ y : ℝ³, |g y| * nPotKernel x y) := by
  dsimp [newtonPotential]
  have hc : 0 ≤ (1 / (8 * π) : ℝ) := by positivity
  calc
    |(1 / (8 * π)) * (∫ y : ℝ³, g y * nPotKernel x y)|
        = (1 / (8 * π)) * |∫ y : ℝ³, g y * nPotKernel x y| := by
            rw [abs_mul]
            rw [abs_of_nonneg hc]
    _ ≤ (1 / (8 * π)) * (∫ y : ℝ³, |g y * nPotKernel x y|) := by
        exact mul_le_mul_of_nonneg_left (MeasureTheory.abs_integral_le_integral_abs
          (f := fun y : ℝ³ => g y * nPotKernel x y)) hc
    _ = (1 / (8 * π)) * (∫ y : ℝ³, |g y| * nPotKernel x y) := by
        congr 1
        apply MeasureTheory.integral_congr_ae
        filter_upwards with y
        rw [abs_mul]
        rw [abs_of_nonneg (nPotKernel_nonneg x y)]

/-- `N_g` is integrable on every ball (Newton potential of an integrable
compactly supported function). -/
lemma newtonPotential_IntegrableOn_ball {g : ℝ³ → ℝ} {R M : ℝ} (hg : Integrable g)
    (hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0) (hR : 0 ≤ R) (hM : 0 ≤ M) :
    IntegrableOn (newtonPotential g) (ball (0 : ℝ³) M) := by
  let P : ℝ³ → ℝ := fun x => ∫ y : ℝ³, |g y| * nPotKernel x y
  let c : ℝ := 1 / (8 * π)
  have hP : IntegrableOn P (ball (0 : ℝ³) M) := by
    dsimp [P]
    exact kernel_abs_marginal_integrableOn_ball (g := g) (R := R) (M := M) hg hgsupp hR hM
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hD : Integrable (fun x : ℝ³ => c * P x) (volume.restrict (ball (0 : ℝ³) M)) := by
    exact (MeasureTheory.Integrable.const_mul hP c)
  have hNsm : AEStronglyMeasurable (fun x : ℝ³ => newtonPotential g x)
      (volume.restrict (ball (0 : ℝ³) M)) := by
    have hprod : AEStronglyMeasurable (fun z : ℝ³ × ℝ³ => (g z.2 * nPotKernel z.1 z.2 : ℝ))
        ((volume.restrict (ball (0 : ℝ³) M)).prod volume) := by
      have h1 : AEStronglyMeasurable (fun z : ℝ³ × ℝ³ => (g z.2 : ℝ))
          ((volume.restrict (ball (0 : ℝ³) M)).prod volume) := by
        exact (hg.aestronglyMeasurable.comp_snd (μ := volume.restrict (ball (0 : ℝ³) M)) (ν := volume))
      have hk : AEStronglyMeasurable (fun z : ℝ³ × ℝ³ => (nPotKernel z.1 z.2 : ℝ))
          ((volume.restrict (ball (0 : ℝ³) M)).prod volume) := by
        exact nPotKernel_measurable.stronglyMeasurable.aestronglyMeasurable
      exact h1.mul hk
    have hmarg : AEStronglyMeasurable (fun x : ℝ³ => ∫ y : ℝ³, g y * nPotKernel x y)
        (volume.restrict (ball (0 : ℝ³) M)) := by
      exact hprod.integral_prod_right'
    -- N = c · (∫_y g·K) pointwise
    have hN : (fun x : ℝ³ => newtonPotential g x)
        = (fun x : ℝ³ => c * (∫ y : ℝ³, g y * nPotKernel x y)) := by
      funext x
      dsimp [newtonPotential, c]
    rw [hN]
    exact hmarg.const_mul c
  have hbd : ∀ x : ℝ³, ‖newtonPotential g x‖ ≤ c * P x := by
    intro x
    calc
      ‖newtonPotential g x‖ = |newtonPotential g x| := Real.norm_eq_abs _
      _ ≤ c * P x := by
        simpa [c, P] using newtonPotential_abs_le g x
  exact MeasureTheory.Integrable.mono' hD hNsm (ae_of_all _ hbd)

/-- `N_g` is locally integrable. -/
lemma newtonPotential_locallyIntegrable {g : ℝ³ → ℝ} {R : ℝ} (hg : Integrable g)
    (hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0) (hR : 0 ≤ R) :
    LocallyIntegrable (newtonPotential g) := by
  intro x
  refine ⟨ball (0 : ℝ³) (‖x‖ + 1), ?_, ?_⟩
  · have hx : x ∈ ball (0 : ℝ³) (‖x‖ + 1) := by
      simp [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg]
    exact Metric.isOpen_ball.mem_nhds hx
  · exact newtonPotential_IntegrableOn_ball (g := g) (R := R) (M := ‖x‖ + 1) hg hgsupp hR (by positivity)


/-- The Newton potential is invariant under linear isometries of `ℝ³` when `g`
is radial. -/
lemma newtonPotential_isometry {g : ℝ³ → ℝ} (hgrad : IsRadial g)
    (U : ℝ³ ≃ₗᵢ[ℝ] ℝ³) (x : ℝ³) :
    newtonPotential g (U x) = newtonPotential g x := by
  have hinteg :
      (∫ y : ℝ³, g y * nPotKernel (U x) y) = ∫ y : ℝ³, g y * nPotKernel x y := by
    calc
      (∫ y : ℝ³, g y * nPotKernel (U x) y)
          = ∫ y : ℝ³, g y * nPotKernel x (U.symm y) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with y
              congr 1
              dsimp [nPotKernel]
              congr 1
              -- ‖U x − y‖ = ‖x − U⁻¹ y‖
              have h1 : ‖U x - y‖ = ‖x - U.symm y‖ := by
                have hmap : U.symm (U x - y) = x - U.symm y := by
                  simp
                calc
                  ‖U x - y‖ = ‖U.symm (U x - y)‖ := (U.symm.norm_map (U x - y)).symm
                  _ = ‖x - U.symm y‖ := by rw [hmap]
              exact h1
      _ = ∫ z : ℝ³, g (U z) * nPotKernel x z := by
              symm
              simpa using (MeasureTheory.integral_comp U (fun w : ℝ³ => g w * nPotKernel x (U.symm w)))
      _ = ∫ y : ℝ³, g y * nPotKernel x y := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with z
              have hg : g (U z) = g z := hgrad (U z) z (U.norm_map z)
              rw [hg]
  have hc : (1 / (8 * π)) * (∫ y : ℝ³, g y * nPotKernel (U x) y)
      = (1 / (8 * π)) * (∫ y : ℝ³, g y * nPotKernel x y) := by
    rw [hinteg]
  unfold newtonPotential
  exact hc

/-- For two vectors of equal norm there is a linear isometry mapping one to the
other. -/
lemma exists_linearIsometry_of_norm_eq {x y : ℝ³} (h : ‖x‖ = ‖y‖) :
    ∃ U : ℝ³ ≃ₗᵢ[ℝ] ℝ³, U x = y := by
  by_cases hxy : x = y
  · refine ⟨1, ?_⟩
    simp [hxy]
  · let d : ℝ³ := x - y
    have hd : d ≠ 0 := by
      intro hd0
      apply hxy
      dsimp [d] at hd0
      exact sub_eq_zero.mp hd0
    let K : Submodule ℝ ℝ³ := (Submodule.span ℝ ({d} : Set ℝ³))ᗮ
    haveI hK : K.HasOrthogonalProjection := by
      dsimp [K]
      infer_instance
    let U : ℝ³ ≃ₗᵢ[ℝ] ℝ³ := K.reflection
    let m : ℝ³ := (1 / 2 : ℝ) • (x + y)
    refine ⟨U, ?_⟩
    have hmain : inner ℝ (x + y) (x - y) = 0 := by
      rw [inner_add_left, inner_sub_right, inner_sub_right]
      rw [real_inner_comm x y]
      rw [real_inner_self_eq_norm_sq x, real_inner_self_eq_norm_sq y]
      ring_nf
      rw [h]
      ring
    have hmd : inner ℝ m d = 0 := by
      dsimp [m, d]
      rw [real_inner_smul_left (x + y) (x - y) (1 / 2)]
      rw [hmain]
      norm_num
    have hmK : m ∈ K := by
      dsimp [K]
      rw [Submodule.mem_orthogonal]
      intro u hu
      rw [Submodule.mem_span_singleton] at hu
      rcases hu with ⟨c, hc⟩
      rw [← hc]
      rw [real_inner_smul_left d m c]
      have hid : inner ℝ d m = 0 := by
        rw [real_inner_comm m d]
        exact hmd
      rw [hid]
      simp
    have hxmsub : x - m ∈ Kᗮ := by
      dsimp [K]
      rw [Submodule.mem_orthogonal]
      intro u hu
      have hdu : inner ℝ d u = 0 := by
        rw [Submodule.mem_orthogonal] at hu
        exact hu d (by
          rw [Submodule.mem_span_singleton]
          exact ⟨1, by simp⟩)
      have hud : inner ℝ u d = 0 := by
        rw [← real_inner_comm u d]
        exact hdu
      have hxm : x - m = (1 / 2 : ℝ) • d := by
        dsimp [m, d]
        ext i
        simp
        ring_nf
      rw [hxm]
      rw [real_inner_smul_right u d (1 / 2)]
      rw [hud]
      simp
    have hproj : K.starProjection x = m := by
      exact Submodule.eq_starProjection_of_mem_orthogonal (u := x) (v := m) hmK hxmsub
    have hUx : U x = y := by
      dsimp [U]
      rw [Submodule.reflection_apply]
      rw [hproj]
      dsimp [m]
      ext i
      simp
    exact hUx

/-- The Newton potential of a radial function is radial. -/
lemma newtonPotential_IsRadial {g : ℝ³ → ℝ} (hgrad : IsRadial g) :
    IsRadial (newtonPotential g) := by
  intro x y hxy
  rcases exists_linearIsometry_of_norm_eq (x := x) (y := y) hxy with ⟨U, hU⟩
  calc
    newtonPotential g x = newtonPotential g y := by
      rw [← hU]
      exact (newtonPotential_isometry (g := g) hgrad U x).symm


/-- Kernel pointwise bound: for `2·R ≤ ‖x‖` and `‖y‖ ≤ R`, `‖x−y‖⁻¹ ≤ 2/‖x‖`. -/
lemma nPotKernel_le_of_norm_ge {x y : ℝ³} {R : ℝ} (hx0 : 0 < ‖x‖)
    (hxR : 2 * R ≤ ‖x‖) (hy : ‖y‖ ≤ R) : nPotKernel x y ≤ 2 / ‖x‖ := by
  have hxy : ‖x‖ / 2 ≤ ‖x - y‖ := by
    have h1 : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := by
      have hh : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
        have hh' : ‖(x - y) + y‖ ≤ ‖x - y‖ + ‖y‖ := norm_add_le (x - y) y
        simpa using hh'
      linarith
    have hyhalf : ‖y‖ ≤ ‖x‖ / 2 := by linarith
    linarith
  have hxy0 : 0 < ‖x - y‖ := lt_of_lt_of_le (by linarith) hxy
  have hxhalf : 0 < ‖x‖ / 2 := by linarith
  have hi0 : (‖x - y‖ : ℝ)⁻¹ ≤ (‖x‖ / 2 : ℝ)⁻¹ := (inv_le_inv₀ hxy0 hxhalf).2 hxy
  have hid : (‖x‖ / 2 : ℝ)⁻¹ = 2 / ‖x‖ := by
    field_simp [hx0.ne']
  dsimp [nPotKernel]
  rw [← hid]
  exact hi0

/-- Pointwise domination of the absolute kernel integrand: for `2R ≤ ‖x‖`, on the
support of `g` the kernel is bounded by `2/‖x‖`; outside it `g` vanishes. -/
lemma kernel_abs_dominated {g : ℝ³ → ℝ} {R : ℝ} (hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0)
    {x : ℝ³} (hx0 : 0 < ‖x‖) (hxR : 2 * R ≤ ‖x‖) :
    ∀ y : ℝ³, |g y| * nPotKernel x y ≤ |g y| * (2 / ‖x‖) := by
  intro y
  by_cases hy : ‖y‖ ≤ R
  · exact mul_le_mul_of_nonneg_left (nPotKernel_le_of_norm_ge (x := x) (y := y) (R := R) hx0 hxR hy)
      (abs_nonneg (g y))
  · have hg0 : g y = 0 := hgsupp y (le_of_not_ge hy)
    have h0 : 0 ≤ 2 / ‖x‖ := by positivity
    calc
      |g y| * nPotKernel x y = 0 := by simp [hg0]
      _ ≤ |g y| * (2 / ‖x‖) := by simp [hg0, h0]

/-- `∫_y |g(y)|·‖x−y‖⁻¹ ≤ (2/‖x‖)·∫|g|` for `2R ≤ ‖x‖`. -/
lemma kernel_abs_integral_le_of_norm_ge {g : ℝ³ → ℝ} {R : ℝ} (hg : Integrable g)
    (hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0) {x : ℝ³} (hx0 : 0 < ‖x‖)
    (hxR : 2 * R ≤ ‖x‖) :
    (∫ y : ℝ³, |g y| * nPotKernel x y) ≤ (2 / ‖x‖) * (∫ y : ℝ³, |g y|) := by
  have hgabs : Integrable (fun y : ℝ³ => |g y|) := by
    refine MeasureTheory.Integrable.congr hg.norm ?_
    filter_upwards with y
    change ‖(g y : ℝ)‖ = |g y|
    rw [Real.norm_eq_abs]
  have hbd : ∀ y : ℝ³, |g y| * nPotKernel x y ≤ |g y| * (2 / ‖x‖) :=
    kernel_abs_dominated (g := g) (R := R) hgsupp hx0 hxR
  have hD : Integrable (fun y : ℝ³ => |g y| * (2 / ‖x‖)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hgabs.const_mul (2 / ‖x‖)
  have hgabsA : AEStronglyMeasurable (fun y : ℝ³ => |g y|) := by
    apply MeasureTheory.AEStronglyMeasurable.congr (hg.aestronglyMeasurable.norm)
    filter_upwards with y
    change ‖(g y : ℝ)‖ = |g y|
    rw [Real.norm_eq_abs]
  have hAEs : AEStronglyMeasurable (fun y : ℝ³ => |g y| * nPotKernel x y) := by
    have hk : AEStronglyMeasurable (fun y : ℝ³ => nPotKernel x y) := by
      exact nPotKernel_measurable_right x |>.stronglyMeasurable.aestronglyMeasurable
    exact hgabsA.mul hk
  have hbnd2 : ∀ y : ℝ³, ‖(|g y| * nPotKernel x y : ℝ)‖ ≤ |g y| * (2 / ‖x‖) := by
    intro y
    calc
      ‖(|g y| * nPotKernel x y : ℝ)‖ = |g y| * nPotKernel x y := by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg (g y)) (nPotKernel_nonneg x y))]
      _ ≤ |g y| * (2 / ‖x‖) := hbd y
  have hInt : Integrable (fun y : ℝ³ => |g y| * nPotKernel x y) := by
    exact MeasureTheory.Integrable.mono' hD hAEs (ae_of_all volume hbnd2)
  have hle : (∫ y : ℝ³, |g y| * nPotKernel x y) ≤ (∫ y : ℝ³, |g y| * (2 / ‖x‖)) := by
    exact MeasureTheory.integral_mono hInt hD hbd
  calc
    (∫ y : ℝ³, |g y| * nPotKernel x y) ≤ (∫ y : ℝ³, |g y| * (2 / ‖x‖)) := hle
    _ = (2 / ‖x‖) * (∫ y : ℝ³, |g y|) := by
        rw [MeasureTheory.integral_mul_const (r := (2 / ‖x‖)) (f := fun y : ℝ³ => |g y|)]
        ring


/-- The Newton potential of an integrable compactly supported function decays
at infinity. -/
lemma newtonPotential_tendsto_zero {g : ℝ³ → ℝ} {R : ℝ} (hg : Integrable g)
    (hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0) (hR : 0 ≤ R) :
    Tendsto (newtonPotential g) (cocompact ℝ³) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let c : ℝ := 1 / (8 * π)
  let G : ℝ := ∫ y : ℝ³, |g y|
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hG0 : 0 ≤ G := by
    dsimp [G]
    exact integral_nonneg (fun y => abs_nonneg (g y))
  have hcG0 : 0 ≤ c * G := mul_nonneg (le_of_lt hc0) hG0
  let a : ℝ := 2 * (c * G)
  let r : ℝ := max (2 * R) (a / ε + 1)
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have hden : 0 < a / ε + 1 := by
    have h1 : 0 ≤ a / ε := div_nonneg ha0 (le_of_lt hε)
    linarith
  have hr0 : 0 < r := by
    dsimp [r]
    exact lt_of_lt_of_le hden (le_max_right (2 * R) (a / ε + 1))
  have hle_ar : a / r ≤ a / (a / ε + 1) := by
    have hr' : a / ε + 1 ≤ r := by dsimp [r]; exact le_max_right (2 * R) (a / ε + 1)
    exact div_le_div_of_nonneg_left ha0 hden hr'
  have hfac : ε * (a / ε + 1) = a + ε := by
    field_simp [hε.ne']
  have hmul : a < ε * (a / ε + 1) := by
    calc
      a < a + ε := by linarith
      _ = ε * (a / ε + 1) := hfac.symm
  have hlt : a / (a / ε + 1) < ε := (div_lt_iff₀ hden).2 hmul
  have hbnd : ∀ x : ℝ³, r ≤ ‖x‖ → |newtonPotential g x| < ε := by
    intro x hx
    have hx0 : 0 < ‖x‖ := lt_of_lt_of_le hr0 hx
    have hxR : 2 * R ≤ ‖x‖ := by
      have h1 : 2 * R ≤ r := by dsimp [r]; exact le_max_left (2 * R) (a / ε + 1)
      linarith
    have hP : (∫ y : ℝ³, |g y| * nPotKernel x y) ≤ (2 / ‖x‖) * G := by
      dsimp [G]
      exact kernel_abs_integral_le_of_norm_ge (g := g) (R := R) hg hgsupp hx0 hxR
    have h1 : |newtonPotential g x| ≤ c * ((2 / ‖x‖) * G) := by
      have ha := newtonPotential_abs_le g x
      exact le_trans ha (mul_le_mul_of_nonneg_left hP (le_of_lt hc0))
    have h2 : c * ((2 / ‖x‖) * G) = a / ‖x‖ := by
      dsimp [a]
      ring
    have hinv : a / ‖x‖ ≤ a / r := by
      exact div_le_div_of_nonneg_left ha0 hr0 hx
    have h3 : a / ‖x‖ ≤ a / (a / ε + 1) := by
      exact le_trans hinv hle_ar
    calc
      |newtonPotential g x| ≤ c * ((2 / ‖x‖) * G) := h1
      _ = a / ‖x‖ := h2
      _ ≤ a / (a / ε + 1) := h3
      _ < ε := hlt
  have hS : {x : ℝ³ | |newtonPotential g x| < ε} ∈ Filter.cocompact ℝ³ := by
    refine Filter.mem_cocompact.mpr ⟨Metric.closedBall (0 : ℝ³) r, ?_, ?_⟩
    · exact ProperSpace.isCompact_closedBall (0 : ℝ³) r
    · intro x hx
      have hxr : r < ‖x‖ := by
        have hnot : ¬‖x‖ ≤ r := by
          simpa [Metric.mem_closedBall, dist_eq_norm, abs_of_nonneg (norm_nonneg x)] using hx
        linarith
      exact hbnd x (le_of_lt hxr)
  -- eventually: dist (N x) 0 < ε outside a compact set
  change {x : ℝ³ | dist (newtonPotential g x) (0 : ℝ) < ε} ∈ Filter.cocompact ℝ³
  rw [show {x : ℝ³ | dist (newtonPotential g x) (0 : ℝ) < ε} = {x : ℝ³ | |newtonPotential g x| < ε} by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [Real.dist_eq, sub_zero]]
  exact hS


/-- A smooth compactly supported `φ` gives a bounded `Δφ` with compact support:
`∃ C B ≥ 0` with `|Δφ x| ≤ C` everywhere and `Δφ x = 0` for `B ≤ ‖x‖`. -/
lemma exists_bound_support_laplacian {φ : ℝ³ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφcs : HasCompactSupport φ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ (∀ x : ℝ³, |(Δ φ) x| ≤ C) ∧
      (∀ x : ℝ³, B ≤ ‖x‖ → (Δ φ) x = 0) := by
  have hLc : Continuous (Δ φ) := continuous_laplacian φ hφ
  have hLcs : HasCompactSupport (Δ φ) := hasCompactSupport_laplacian φ hφcs
  rcases hLcs.isBounded.subset_closedBall (0 : ℝ³) with ⟨B₀, hB₀⟩
  let B : ℝ := max B₀ 0 + 1
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hsupp0 : ∀ x : ℝ³, B ≤ ‖x‖ → (Δ φ) x = 0 := by
    intro x hx
    by_contra hz
    have hxsupp : x ∈ Function.support (Δ φ) := by simpa [Function.support] using hz
    have hx' : x ∈ Metric.closedBall (0 : ℝ³) B₀ := hB₀ (subset_tsupport (Δ φ) hxsupp)
    have hnorm : ‖x‖ ≤ B₀ := by simpa [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg] using hx'
    have hBgt : B₀ < B := by
      dsimp [B]
      have h1 : B₀ ≤ max B₀ 0 := le_max_left B₀ 0
      linarith
    dsimp [B] at hx
    linarith
  let K : Set ℝ³ := Metric.closedBall (0 : ℝ³) B
  have hK : IsCompact K := ProperSpace.isCompact_closedBall (0 : ℝ³) B
  have hKne : K.Nonempty := ⟨0, by simp [K, hB0, Metric.mem_closedBall]⟩
  have hcontOn : ContinuousOn (fun x : ℝ³ => |(Δ φ) x|) K := by
    exact (continuous_abs.comp hLc).continuousOn
  rcases IsCompact.exists_isMaxOn hK hKne hcontOn with ⟨x₀, hx₀, hmax⟩
  let C₀ : ℝ := |(Δ φ) x₀|
  have hmaxall : ∀ x : ℝ³, x ∈ K → |(Δ φ) x| ≤ C₀ := by
    intro x hx
    simpa [C₀] using hmax hx
  let C : ℝ := max C₀ 0
  have hC0 : 0 ≤ C := by dsimp [C]; exact le_max_right C₀ 0
  refine ⟨C, B, hC0, hB0, ?_, hsupp0⟩
  · intro x
    by_cases hx : x ∈ K
    · exact le_trans (hmaxall x hx) (by dsimp [C]; exact le_max_left C₀ 0)
    · have hxbig : B < ‖x‖ := by
        have hnot : ¬‖x‖ ≤ B := by
          simpa [K, Metric.mem_closedBall, dist_eq_norm, abs_of_nonneg (norm_nonneg x)] using hx
        linarith
      have hz : (Δ φ) x = 0 := hsupp0 x (le_of_lt hxbig)
      simp [hz, hC0]

/-- Integrability on a restricted product extends to integrability of the
indicator-multiplied function on the full product. -/
lemma indicator_extend_integrable {F : ℝ³ × ℝ³ → ℝ} (s : Set ℝ³) (hs : MeasurableSet s)
    (hF : Integrable F ((volume.restrict s).prod volume)) :
    Integrable ((s ×ˢ (Set.univ : Set ℝ³)).indicator F) (volume.prod volume) := by
  have hI : IntegrableOn F (s ×ˢ (Set.univ : Set ℝ³)) (volume.prod volume) := by
    change Integrable F ((volume.prod volume).restrict (s ×ˢ (Set.univ : Set ℝ³)))
    rw [← Measure.prod_restrict (s := s) (t := (Set.univ : Set ℝ³))]
    simpa using hF
  exact (MeasureTheory.integrable_indicator_iff (hs.prod MeasurableSet.univ)).2 hI


/-- Green/Fubini identity for the Newton potential: for smooth compactly
supported `φ`, `∫_x N_g(x)·(Δφ)(x) = −(1/2)·∫_y g(y)·φ(y)`. -/
lemma newtonPotential_test_integral {g : ℝ³ → ℝ} {R : ℝ} (hg : Integrable g)
    (hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0) (hR : 0 ≤ R) (φ : ℝ³ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hφcs : HasCompactSupport φ) :
    (∫ x : ℝ³, (newtonPotential g x) * (Δ φ) x) = - (1 / 2) * (∫ y : ℝ³, g y * φ y) := by
  let c : ℝ := 1 / (8 * π)
  rcases exists_bound_support_laplacian (φ := φ) hφ hφcs with ⟨C, B, hC0, hB0, hbdd, hsupp⟩
  have hF0 : Integrable (fun z : ℝ³ × ℝ³ => (|g z.2| * nPotKernel z.1 z.2 : ℝ))
      ((volume.restrict (ball (0 : ℝ³) B)).prod volume) :=
      kernel_abs_integrable_prod_ball (g := g) (R := R) (M := B) hg hgsupp hR hB0
  let F : ℝ³ × ℝ³ → ℝ := fun z => |g z.2| * nPotKernel z.1 z.2
  let D : ℝ³ × ℝ³ → ℝ := fun z => C * ((ball (0 : ℝ³) B) ×ˢ (Set.univ : Set ℝ³)).indicator F z
  have hind := indicator_extend_integrable (s := ball (0 : ℝ³) B) (F := F) measurableSet_ball
      (by simpa [F] using hF0)
  have hD : Integrable D (volume.prod volume) := by
    dsimp [D]
    exact hind.const_mul C
  have hDdom : ∀ z : ℝ³ × ℝ³, ‖(((Δ φ) z.1) * (g z.2) * nPotKernel z.1 z.2 : ℝ)‖ ≤ D z := by
    intro z
    by_cases hzb : z.1 ∈ ball (0 : ℝ³) B
    · have hindv : ((ball (0 : ℝ³) B) ×ˢ (Set.univ : Set ℝ³)).indicator F z = F z := by
        simp [hzb]
      have hK0 : 0 ≤ |g z.2| * nPotKernel z.1 z.2 :=
        mul_nonneg (abs_nonneg (g z.2)) (nPotKernel_nonneg z.1 z.2)
      dsimp [D]
      rw [hindv]
      calc
        ‖(((Δ φ) z.1) * (g z.2) * nPotKernel z.1 z.2 : ℝ)‖
            = |(Δ φ) z.1| * (|g z.2| * nPotKernel z.1 z.2) := by
                rw [Real.norm_eq_abs, abs_mul, abs_mul]
                rw [abs_of_nonneg (nPotKernel_nonneg z.1 z.2)]
                rw [mul_assoc]
        _ ≤ C * (|g z.2| * nPotKernel z.1 z.2) := by
                exact mul_le_mul_of_nonneg_right (hbdd z.1) hK0
        _ = C * F z := by
                dsimp [F]
    · have hbig : B ≤ ‖z.1‖ := by
        have hnot : ¬‖z.1‖ < B := by
          simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg] using hzb
        linarith
      have hz0 : (Δ φ) z.1 = 0 := hsupp z.1 hbig
      have hindv : ((ball (0 : ℝ³) B) ×ˢ (Set.univ : Set ℝ³)).indicator F z = 0 := by
        simp [hzb]
      dsimp [D]
      rw [hindv]
      simp [hz0]
  have htestsm : AEStronglyMeasurable (fun z : ℝ³ × ℝ³ => (((Δ φ) z.1) * (g z.2) * nPotKernel z.1 z.2 : ℝ))
      (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun z : ℝ³ × ℝ³ => ((Δ φ) z.1 : ℝ)) (volume.prod volume) := by
      exact (continuous_laplacian φ hφ).measurable.comp measurable_fst |>.stronglyMeasurable.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun z : ℝ³ × ℝ³ => (g z.2 : ℝ)) (volume.prod volume) := by
      exact (hg.aestronglyMeasurable.comp_snd (μ := volume) (ν := volume))
    have h3 : AEStronglyMeasurable (fun z : ℝ³ × ℝ³ => (nPotKernel z.1 z.2 : ℝ)) (volume.prod volume) := by
      exact nPotKernel_measurable.stronglyMeasurable.aestronglyMeasurable
    exact (h1.mul h2).mul h3
  have htest : Integrable (fun z : ℝ³ × ℝ³ => (((Δ φ) z.1) * (g z.2) * nPotKernel z.1 z.2 : ℝ))
      (volume.prod volume) := by
    exact MeasureTheory.Integrable.mono' hD htestsm (ae_of_all volume hDdom)
  -- Fubini swap
  have hswap : (∫ x : ℝ³, ∫ y : ℝ³, (((Δ φ) x) * (g y) * nPotKernel x y : ℝ))
      = ∫ y : ℝ³, ∫ x : ℝ³, (((Δ φ) x) * (g y) * nPotKernel x y : ℝ) := by
    have hs := MeasureTheory.integral_integral_swap (μ := volume) (ν := volume)
      (f := fun x y : ℝ³ => (((Δ φ) x) * (g y) * nPotKernel x y : ℝ))
    simpa using (hs htest)
  -- inner integral over y at fixed x
  have hL1 :
      (∫ x : ℝ³, ∫ y : ℝ³, (((Δ φ) x) * (g y) * nPotKernel x y : ℝ))
        = ∫ x : ℝ³, ((Δ φ) x) * (∫ y : ℝ³, g y * nPotKernel x y) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    calc
      (∫ y : ℝ³, (((Δ φ) x) * (g y) * nPotKernel x y : ℝ))
          = ∫ y : ℝ³, (((Δ φ) x) * ((g y) * nPotKernel x y) : ℝ) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with y
              ring
      _ = ((Δ φ) x) * (∫ y : ℝ³, (g y) * nPotKernel x y) := by
              exact MeasureTheory.integral_const_mul ((Δ φ) x) (fun y : ℝ³ => (g y) * nPotKernel x y)
  -- inner integral over x at fixed y: Newton identity
  have hinner (y : ℝ³) :
      (∫ x : ℝ³, (((Δ φ) x) * (g y) * nPotKernel x y : ℝ))
        = (g y) * (-(4 * π) * φ y) := by
    calc
      (∫ x : ℝ³, (((Δ φ) x) * (g y) * nPotKernel x y : ℝ))
          = ∫ x : ℝ³, ((g y) * (((Δ φ) x) * nPotKernel x y) : ℝ) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              ring
      _ = (g y) * (∫ x : ℝ³, ((Δ φ) x) * nPotKernel x y) := by
              exact MeasureTheory.integral_const_mul (g y) (fun x : ℝ³ => ((Δ φ) x) * nPotKernel x y)
      _ = (g y) * (-(4 * π) * φ y) := by
              congr 1
              have hid : (∫ x : ℝ³, ((Δ φ) x) * nPotKernel x y) = -(4 * π) * φ y := by
                calc
                  (∫ x : ℝ³, ((Δ φ) x) * nPotKernel x y) = (∫ x : ℝ³, ((Δ φ) x) * (‖x - y‖ : ℝ)⁻¹) := by
                      dsimp [nPotKernel]
                  _ = -4 * π * φ y := newton_integral_delta (y := y) φ hφ hφcs
                  _ = -(4 * π) * φ y := by ring
              exact hid
  have hR1 :
      (∫ y : ℝ³, ∫ x : ℝ³, (((Δ φ) x) * (g y) * nPotKernel x y : ℝ))
        = - (4 * π) * (∫ y : ℝ³, g y * φ y) := by
    calc
      (∫ y : ℝ³, ∫ x : ℝ³, (((Δ φ) x) * (g y) * nPotKernel x y : ℝ))
          = ∫ y : ℝ³, ((g y) * (-(4 * π) * φ y)) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with y
              simpa using hinner y
      _ = - (4 * π) * (∫ y : ℝ³, g y * φ y) := by
          calc
            (∫ y : ℝ³, (g y) * (-(4 * π) * φ y))
                = ∫ y : ℝ³, (-(4 * π)) * ((g y) * φ y) := by
                    apply MeasureTheory.integral_congr_ae
                    filter_upwards with y
                    ring
            _ = -(4 * π) * (∫ y : ℝ³, (g y) * φ y) := by
                    exact MeasureTheory.integral_const_mul (-(4 * π)) (fun y : ℝ³ => (g y) * φ y)
  have hS : (∫ x : ℝ³, ((Δ φ) x) * (∫ y : ℝ³, g y * nPotKernel x y))
      = - (4 * π) * (∫ y : ℝ³, g y * φ y) := by
    calc
      (∫ x : ℝ³, ((Δ φ) x) * (∫ y : ℝ³, g y * nPotKernel x y))
          = ∫ x : ℝ³, ∫ y : ℝ³, (((Δ φ) x) * (g y) * nPotKernel x y : ℝ) := hL1.symm
      _ = ∫ y : ℝ³, ∫ x : ℝ³, (((Δ φ) x) * (g y) * nPotKernel x y : ℝ) := hswap
      _ = - (4 * π) * (∫ y : ℝ³, g y * φ y) := hR1
  have hrel : (∫ x : ℝ³, (newtonPotential g x) * (Δ φ) x)
      = c * (∫ x : ℝ³, ((Δ φ) x) * (∫ y : ℝ³, g y * nPotKernel x y)) := by
    calc
      (∫ x : ℝ³, (newtonPotential g x) * (Δ φ) x)
          = ∫ x : ℝ³, c * (((Δ φ) x) * (∫ y : ℝ³, g y * nPotKernel x y)) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              dsimp [newtonPotential, c]
              ring_nf
      _ = c * (∫ x : ℝ³, ((Δ φ) x) * (∫ y : ℝ³, g y * nPotKernel x y)) := by
              exact MeasureTheory.integral_const_mul c (fun x : ℝ³ => ((Δ φ) x) * (∫ y : ℝ³, g y * nPotKernel x y))
  calc
    (∫ x : ℝ³, (newtonPotential g x) * (Δ φ) x)
        = c * (∫ x : ℝ³, ((Δ φ) x) * (∫ y : ℝ³, g y * nPotKernel x y)) := hrel
    _ = c * (- (4 * π) * (∫ y : ℝ³, g y * φ y)) := by rw [hS]
    _ = - (1 / 2) * (∫ y : ℝ³, g y * φ y) := by
        dsimp [c]
        field_simp [Real.pi_ne_zero]
        ring


/-- A locally integrable function times a bounded compactly-supported function
is integrable. -/
lemma integrable_mul_supported {f b : ℝ³ → ℝ} {S C : ℝ} (hf : LocallyIntegrable f)
    (hbm : Measurable b) (hS : 0 ≤ S) (hC : 0 ≤ C) (hbdd : ∀ x : ℝ³, |b x| ≤ C)
    (hsupp : ∀ x : ℝ³, S ≤ ‖x‖ → b x = 0) :
    Integrable (fun x : ℝ³ => f x * b x) := by
  let K : Set ℝ³ := Metric.closedBall (0 : ℝ³) S
  have hK : IsCompact K := ProperSpace.isCompact_closedBall (0 : ℝ³) S
  have hfK : IntegrableOn f K := hf.integrableOn_isCompact hK
  have hfn : IntegrableOn (fun x : ℝ³ => ‖f x‖) K := hfK.norm
  have hIn : Integrable (fun x : ℝ³ => ‖f x‖ * K.indicator (fun _ : ℝ³ => (1 : ℝ)) x) := by
    have heq : (fun x : ℝ³ => ‖f x‖ * K.indicator (fun _ : ℝ³ => (1 : ℝ)) x)
        = fun x : ℝ³ => K.indicator (fun x : ℝ³ => ‖f x‖) x := by
      funext x
      by_cases hx : x ∈ K <;> simp [hx]
    rw [heq]
    exact (MeasureTheory.integrable_indicator_iff (s := K) (f := fun x : ℝ³ => ‖f x‖)
      measurableSet_closedBall).2 hfn
  have hD : Integrable (fun x : ℝ³ => C * (‖f x‖ * K.indicator (fun _ : ℝ³ => (1 : ℝ)) x)) := by
    exact hIn.const_mul C
  have hbd2 : ∀ x : ℝ³, ‖(f x * b x : ℝ)‖ ≤ C * (‖f x‖ * K.indicator (fun _ : ℝ³ => (1 : ℝ)) x) := by
    intro x
    by_cases hx : x ∈ K
    · have hb : |b x| ≤ C := hbdd x
      have hIK : K.indicator (fun _ : ℝ³ => (1 : ℝ)) x = 1 := by simp [hx]
      calc
        ‖(f x * b x : ℝ)‖ = |f x| * |b x| := by rw [Real.norm_eq_abs, abs_mul]
        _ = ‖f x‖ * |b x| := by rw [← Real.norm_eq_abs (f x)]
        _ ≤ ‖f x‖ * C := by exact mul_le_mul_of_nonneg_left hb (norm_nonneg (f x))
        _ = C * (‖f x‖ * K.indicator (fun _ : ℝ³ => (1 : ℝ)) x) := by rw [hIK]; ring
    · have hnot : S < ‖x‖ := by
        have hle : ¬‖x‖ ≤ S := by
          simpa [K, Metric.mem_closedBall, dist_eq_norm, abs_of_nonneg (norm_nonneg x)] using hx
        linarith
      have hb0 : b x = 0 := hsupp x (le_of_lt hnot)
      have hIK : K.indicator (fun _ : ℝ³ => (1 : ℝ)) x = 0 := by simp [hx]
      simp [hb0, hIK]
  have hsm : AEStronglyMeasurable (fun x : ℝ³ => f x * b x) := by
    exact hf.aestronglyMeasurable.mul hbm.stronglyMeasurable.aestronglyMeasurable
  exact MeasureTheory.Integrable.mono' hD hsm (ae_of_all volume hbd2)

/-- The difference `w − N_g` is weakly harmonic: `∫ (w − N_g)·Δφ = 0` for
every smooth compactly supported `φ`, when `w` is a weak scattering solution
of `v` with `g = v(1−w)`. -/
lemma scattering_h_weakHarmonic {v w g : ℝ³ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hw : IsScatteringSolution w v) (hgdef : ∀ y : ℝ³, g y = v y * (1 - w y))
    (hg : Integrable g) (hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0) :
    ∀ φ : ℝ³ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x : ℝ³, (w x - newtonPotential g x) * (Δ φ) x) = 0 := by
  intro φ hφ hφcs
  let h : ℝ³ → ℝ := fun x => w x - newtonPotential g x
  have hwh0 : (∫ x : ℝ³, w x * (Δ φ) x) = - (1 / 2) * (∫ y : ℝ³, g y * φ y) := by
    have heq := hw.eq φ ⟨hφ, hφcs⟩
    have hg' : (∫ y : ℝ³, v y * (1 - w y) * φ y) = ∫ y : ℝ³, g y * φ y := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      rw [hgdef]
    have heq' : - (∫ x : ℝ³, w x * (Δ φ) x) = (1 / 2) * (∫ y : ℝ³, g y * φ y) := by
      simpa [hg'] using heq
    linarith
  have hN0 : (∫ x : ℝ³, (newtonPotential g x) * (Δ φ) x)
      = - (1 / 2) * (∫ y : ℝ³, g y * φ y) :=
      newtonPotential_test_integral (g := g) (R := R) hg hgsupp hR φ hφ hφcs
  rcases exists_bound_support_laplacian (φ := φ) hφ hφcs with ⟨C, B, hC0, hB0, hbdd, hsupp⟩
  have hΔm : Measurable (Δ φ) := (continuous_laplacian φ hφ).measurable
  have hwI : Integrable (fun x : ℝ³ => w x * (Δ φ) x) := by
    exact integrable_mul_supported (f := w) (b := (Δ φ)) hw.lhs_integrable hΔm hB0 hC0 hbdd hsupp
  have hNI : Integrable (fun x : ℝ³ => (newtonPotential g x) * (Δ φ) x) := by
    have hNli : LocallyIntegrable (newtonPotential g) :=
      newtonPotential_locallyIntegrable (g := g) (R := R) hg hgsupp hR
    exact integrable_mul_supported (f := newtonPotential g) (b := (Δ φ)) hNli hΔm hB0 hC0 hbdd hsupp
  have hsplit : (∫ x : ℝ³, (w x - newtonPotential g x) * (Δ φ) x)
      = (∫ x : ℝ³, w x * (Δ φ) x) - (∫ x : ℝ³, (newtonPotential g x) * (Δ φ) x) := by
    have hc1 : (fun x : ℝ³ => (w x - newtonPotential g x) * (Δ φ) x)
        = (fun x : ℝ³ => w x * (Δ φ) x - (newtonPotential g x) * (Δ φ) x) := by
      funext x
      ring
    rw [hc1]
    exact MeasureTheory.integral_sub hwI hNI
  rw [hsplit, hwh0, hN0]
  ring

/-- The scattering solution is the Newton potential of `g := v(1−w)`: for a
radial weak scattering solution `w` of the radial potential `v` (supported in
`ball 0 R`), `w x = (8π)⁻¹·∫_y v y·(1−w y)/‖x−y‖ dy` for almost every `x`. -/
theorem scattering_newton_representation {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) :
    (∀ᵐ x : ℝ³,
      w x = (1 / (8 * π)) * (∫ y : ℝ³, (v y * (1 - w y)) * (‖x - y‖ : ℝ)⁻¹)) := by
  let g : ℝ³ → ℝ := fun y => v y * (1 - w y)
  have hR0 : 0 ≤ R := le_of_lt hR
  have hg : Integrable g := by
    have h := scatG_integrable (v := v) (w := w) hv_supp hw
    simpa [g] using h
  have hgrad : IsRadial g := by
    intro x y hxy
    dsimp [g]
    rw [hvrad x y hxy, hrad x y hxy]
  have hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0 := by
    intro y hy
    have hv0 : v y = 0 := v_eq_zero_of_norm_ge hv_supp hy
    dsimp [g]
    simp [hv0]
  let h : ℝ³ → ℝ := fun x => w x - newtonPotential g x
  have hNrad : IsRadial (newtonPotential g) := newtonPotential_IsRadial hgrad
  have hradh : IsRadial h := by
    intro x y hxy
    dsimp [h]
    rw [hrad x y hxy, hNrad x y hxy]
  have hNli : LocallyIntegrable (newtonPotential g) :=
    newtonPotential_locallyIntegrable (g := g) (R := R) hg hgsupp hR0
  have hli : LocallyIntegrable h := by
    dsimp [h]
    exact hw.lhs_integrable.sub hNli
  have hwh : ∀ φ : ℝ³ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x : ℝ³, h x * (Δ φ) x) = 0 := by
    intro φ hφ hφcs
    have hs := scattering_h_weakHarmonic (v := v) (w := w) (g := g) (R := R) hR0 hw
      (fun y => rfl) hg hgsupp φ hφ hφcs
    simpa [h] using hs
  have hlim : Tendsto h (cocompact ℝ³) (𝓝 0) := by
    have hNlim : Tendsto (newtonPotential g) (cocompact ℝ³) (𝓝 0) :=
      newtonPotential_tendsto_zero (g := g) (R := R) hg hgsupp hR0
    dsimp [h]
    simpa [sub_eq_add_neg] using hw.lim.sub hNlim
  have hzero : h =ᵐ[volume] 0 := by
    exact radial_weaklyHarmonic_eq_zero (w := h) hradh hli hwh hlim
  filter_upwards [hzero] with x hx
  have hval : w x = newtonPotential g x := by
    dsimp [h] at hx
    exact sub_eq_zero.mp hx
  simpa [g, newtonPotential, nPotKernel] using hval

end Submission.BoseGases
