import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.sweepBlurFacts
import Submission.Work.Drive.sweepLoopProfileDefs
import Submission.Work.Drive.sweepLoopProfile_uniformCont_loop
import Submission.Work.Drive.sweepLoopProfile_uniformCont_sweep

/-!
# The doubly smoothed sweep is close to the chamfered loop

`Work.Drive.sweepFam r D lam δ₁ δ₂ σ t` is the chamfered loop `sweepLoopChamfer r D lam σ ·`
blurred (i) in the loop parameter with the bump `sweepBump` at scale `δ₁` and (ii) in the sweep
parameter at scale `δ₂`.  The bump has total mass one (`Work.Drive.integral_sweepBump`), so for
small smoothing scales the blur is a *small* perturbation of the raw loop, uniformly in the sweep
parameter `σ`, in the loop parameter `t` and - crucially for the sweep - uniformly in `lam`:

`Work.Drive.sweepFam_close_chamfer`.

The proof is a three-step reduction.

* **The blur estimate** (`Work.Drive.sweepBlur_close`): if a continuous `f : ℝ → E` satisfies
  `‖f (t + h) - f t‖ ≤ ε` for `|h| ≤ δ`, then `‖∫ u in (-1)..1, sweepBump u • f (t - δ' * u) - f t‖
  ≤ ε` for every `|δ'| ≤ δ`.  This is just `∫ sweepBump = 1` plus the triangle inequality; it is
  applied twice.
* **The moduli of the raw loop.**  Uniform continuity of `sweepLoopProfile` in its profile variable
  (uniform in `lam` and `σ`) and in its sweep variable (uniform in `lam` and the profile) are proved
  separately in `Drive/sweepLoopProfile_uniformCont_loop` and
  `Drive/sweepLoopProfile_uniformCont_sweep`.  From the first we transport back to the genuine loop
  parameter `t` (`Work.Drive.sweepLoopChamfer_t_modulus`), handling the wrap-around of the profile
  through the identities `sweepLoopProfile_zero`/`sweepLoopProfile_one`; the second is used
  directly.
* **Assembly.**  `sweepSmoothT` differs from the raw loop by at most `ε/2` (first blur), and
  `sweepFam` differs from `sweepSmoothT` by at most `ε/2` (second blur, whose hypothesis is the
  `σ`-modulus of `sweepSmoothT`, itself obtained by integrating the `σ`-modulus of the raw loop).

The three moduli are packaged as `Prop`-valued predicates (`LoopProfileModulus`,
`LoopSweepModulus`, `LoopTModulus`, `SmoothTModulus`) so that they can be passed around cheaply.
-/

set_option maxHeartbeats 4000000

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology intervalIntegral

/-! ## 0. The moduli, as predicates -/

/-- Uniform continuity of the profile loop in the *profile* variable `w`, uniform in `lam ∈ (0,1/4]`
and in the sweep parameter `σ`.  This is the statement proved in
`Drive/sweepLoopProfile_uniformCont_loop`. -/
def LoopProfileModulus (r : ℝ → Space) {d : BandArcData} (D : SweepData d) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ θ : ℝ, 0 < θ ∧
    ∀ (lam : ℝ), 0 < lam → lam ≤ 1 / 4 →
      ∀ (σ : ℝ) (w w' : ℝ), w ∈ Set.Icc (0 : ℝ) 1 → w' ∈ Set.Icc (0 : ℝ) 1 →
        |w - w'| ≤ θ →
          ‖sweepLoopProfile r D lam σ w' - sweepLoopProfile r D lam σ w‖ ≤ ε

/-- Uniform continuity of the profile loop in the *sweep* variable `σ`, uniform in `lam ∈ (0,1/4]`
and in the profile.  This is the statement proved in
`Drive/sweepLoopProfile_uniformCont_sweep`. -/
def LoopSweepModulus (r : ℝ → Space) {d : BandArcData} (D : SweepData d) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ θ : ℝ, 0 < θ ∧
    ∀ (lam : ℝ), 0 < lam → lam ≤ 1 / 4 →
      ∀ (σ σ' : ℝ) (w : ℝ), w ∈ Set.Icc (0 : ℝ) 1 → |σ - σ'| ≤ θ →
        ‖sweepLoopProfile r D lam σ' w - sweepLoopProfile r D lam σ w‖ ≤ ε

/-- Uniform continuity of the raw chamfered loop in the genuine loop parameter `t`, uniform in
`lam ∈ (0,1/4]` and in the sweep parameter.  This is the transport of `LoopProfileModulus` through
`sweepParam` (`Work.Drive.sweepLoopChamfer_t_modulus`). -/
def LoopTModulus (r : ℝ → Space) {d : BandArcData} (D : SweepData d) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧
    ∀ (lam : ℝ), 0 < lam → lam ≤ 1 / 4 → ∀ (σ t t' : ℝ), |t - t'| ≤ T →
      ‖sweepLoopChamfer r D lam σ t' - sweepLoopChamfer r D lam σ t‖ ≤ ε

/-- Uniform continuity of the single blur `sweepSmoothT` in the sweep parameter, uniform in
`lam ∈ (0,1/4]` and in the loop-parameter blur scale `δ₁` (and in the loop parameter `t`). -/
def SmoothTModulus (r : ℝ → Space) {d : BandArcData} (D : SweepData d) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ θ : ℝ, 0 < θ ∧
    ∀ (lam δ₁ : ℝ), 0 < lam → lam ≤ 1 / 4 → ∀ (σ σ' : ℝ) (t : ℝ), |σ - σ'| ≤ θ →
      ‖sweepSmoothT r D lam δ₁ σ' t - sweepSmoothT r D lam δ₁ σ t‖ ≤ ε

/-- The triangle inequality for normed differences, in the telescoped form used throughout. -/
lemma norm_sub_le_trans {E : Type*} [SeminormedAddCommGroup E] (x y z : E) :
    ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
  have h := dist_triangle x y z
  rwa [dist_eq_norm, dist_eq_norm, dist_eq_norm] at h

/-! ## 1. The blur estimate -/

/-- **Blurring is a small perturbation.**  If `f` is continuous and oscillates by at most `ε` over
every window of length `2δ`, then the blur of `f` with the bump `sweepBump` at any scale
`|δ'| ≤ δ` is within `ε` of `f`, pointwise. -/
lemma sweepBlur_close {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Continuous f) {ε δ δ' : ℝ} (hε : 0 ≤ ε)
    (hbd : ∀ t h : ℝ, |h| ≤ δ → ‖f (t + h) - f t‖ ≤ ε) (hδ : |δ'| ≤ δ) (t : ℝ) :
    ‖(∫ u in (-1 : ℝ)..1, sweepBump u • f (t - δ' * u)) - f t‖ ≤ ε := by
  have hcont : Continuous (fun u : ℝ => sweepBump u • f (t - δ' * u)) :=
    sweepBump_continuous.smul
      (hf.comp (continuous_const.sub (continuous_const.mul continuous_id)))
  have hcont' : Continuous (fun u : ℝ => sweepBump u • (f (t - δ' * u) - f t)) :=
    sweepBump_continuous.smul
      ((hf.comp (continuous_const.sub (continuous_const.mul continuous_id))).sub
        continuous_const)
  have hconstcont : Continuous (fun u : ℝ => sweepBump u • f t) :=
    sweepBump_continuous.smul continuous_const
  have hconst : (∫ u in (-1 : ℝ)..1, sweepBump u • f t) = f t := by
    rw [intervalIntegral.integral_smul_const, integral_sweepBump, one_smul]
  have hdiff : (∫ u in (-1 : ℝ)..1, sweepBump u • f (t - δ' * u)) - f t
      = ∫ u in (-1 : ℝ)..1, sweepBump u • (f (t - δ' * u) - f t) := by
    nth_rewrite 1 [← hconst]
    rw [← intervalIntegral.integral_sub (hcont.intervalIntegrable (-1) 1)
      (hconstcont.intervalIntegrable (-1) 1)]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    rw [smul_sub]
  rw [hdiff]
  refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans ?_
  have hpt : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      ‖sweepBump u • (f (t - δ' * u) - f t)‖ ≤ sweepBump u * ε := by
    intro u hu
    rw [Set.mem_Icc] at hu
    rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg u)]
    have habs : |δ' * u| ≤ δ := by
      rw [abs_mul]
      calc |δ'| * |u| ≤ |δ'| * 1 :=
            mul_le_mul_of_nonneg_left (abs_le.mpr hu) (abs_nonneg _)
        _ = |δ'| := by ring
        _ ≤ δ := hδ
    have habs' : |-(δ' * u)| ≤ δ := by simpa using habs
    have h := hbd t (-(δ' * u)) habs'
    have h' : ‖f (t - δ' * u) - f t‖ ≤ ε := by
      simpa [show t + -(δ' * u) = t - δ' * u by ring] using h
    exact mul_le_mul_of_nonneg_left h' (sweepBump_nonneg u)
  have hmono : (∫ u in (-1 : ℝ)..1, ‖sweepBump u • (f (t - δ' * u) - f t)‖)
      ≤ ∫ u in (-1 : ℝ)..1, sweepBump u * ε :=
    intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1)
      ((hcont'.norm).intervalIntegrable (-1) 1)
      ((sweepBump_continuous.mul continuous_const).intervalIntegrable (-1) 1) hpt
  calc (∫ u in (-1 : ℝ)..1, ‖sweepBump u • (f (t - δ' * u) - f t)‖)
      ≤ ∫ u in (-1 : ℝ)..1, sweepBump u * ε := hmono
    _ = ε := by rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]

/-! ## 2. From the profile modulus to the loop-parameter modulus -/

/-- **Profiles are either close or wrap around.**  If the loop parameters `a`, `b` differ by at
most `θ * period / 2` with `0 < θ ≤ 1`, then their profiles differ by at most `θ`, or else one of
the two profiles is close to `1` and the other to `0` - the wrap-around cases. -/
lemma sweepParam_near_or_wrap {a b θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (h : |a - b| ≤ θ * period / 2) :
    |sweepParam a - sweepParam b| ≤ θ ∨
      (sweepParam a ≤ θ ∧ 1 - sweepParam b ≤ θ) ∨
      (sweepParam b ≤ θ ∧ 1 - sweepParam a ≤ θ) := by
  have hp : 0 < period := period_pos
  have hu : (0 : ℝ) ≤ sweepParam a ∧ sweepParam a < 1 := sweepParam_mem a
  have hu' : (0 : ℝ) ≤ sweepParam b ∧ sweepParam b < 1 := sweepParam_mem b
  set m : ℤ := ⌊a / period⌋ - ⌊b / period⌋ with hmdef
  have hrel : sweepParam a - sweepParam b = (a - b) / period - (m : ℝ) := by
    rw [sweepParam, sweepParam, hmdef]
    push_cast
    ring
  have hhalf : |(a - b) / period| ≤ θ / 2 := by
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
    nlinarith [h]
  have huu : |sweepParam a - sweepParam b| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hu'.1, hu'.2]
  by_cases hm0 : m = 0
  · left
    have hsub : sweepParam a - sweepParam b = (a - b) / period := by
      rw [hrel, hm0]; push_cast; ring
    rw [hsub]
    linarith
  · have hm1 : m = 1 ∨ m = -1 := by
      have hmdiff : (m : ℝ) = (a - b) / period - (sweepParam a - sweepParam b) := by linarith [hrel]
      have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast (Int.one_le_abs hm0)
      have h2 : |(m : ℝ)| < 2 := by
        calc |(m : ℝ)| = |(a - b) / period - (sweepParam a - sweepParam b)| := by rw [hmdiff]
          _ ≤ |(a - b) / period| + |sweepParam a - sweepParam b| := by
              have h := abs_sub_le ((a - b) / period) 0 (sweepParam a - sweepParam b)
              simpa only [sub_zero, zero_sub, abs_neg] using h
          _ ≤ θ / 2 + 1 := add_le_add hhalf huu
          _ < 2 := by linarith
      rcases le_or_gt 0 (m : ℝ) with hpos | hneg
      · left
        have h1' : (1 : ℤ) ≤ m := by
          have : (1 : ℝ) ≤ (m : ℝ) := by rwa [abs_of_nonneg hpos] at h1
          exact_mod_cast this
        have h2' : m < 2 := by
          have : (m : ℝ) < 2 := by rwa [abs_of_nonneg hpos] at h2
          exact_mod_cast this
        omega
      · right
        have h1' : m ≤ -1 := by
          have : (m : ℝ) ≤ -1 := by
            rw [abs_of_neg hneg] at h1
            linarith
          exact_mod_cast this
        have h2' : -2 < m := by
          have : (-2 : ℝ) < (m : ℝ) := by
            rw [abs_of_neg hneg] at h2
            linarith
          exact_mod_cast this
        omega
    rcases hm1 with hm1 | hm1
    · right; left
      have hh : (a - b) / period = sweepParam a - sweepParam b + 1 := by
        have hh0 := hrel
        rw [hm1] at hh0
        push_cast at hh0
        linarith [hh0]
      have hnn : 0 ≤ (a - b) / period := by rw [hh]; linarith [hu.1, hu'.2]
      have hle : (a - b) / period ≤ θ / 2 := by
        have h2 := hhalf
        rwa [abs_of_nonneg hnn] at h2
      constructor
      · have : sweepParam a = (a - b) / period + (sweepParam b - 1) := by linarith [hh]
        linarith [hu'.2, hle, hθ0]
      · have : 1 - sweepParam b = (a - b) / period - sweepParam a := by linarith [hh]
        linarith [hu.1, hle, hθ0]
    · right; right
      have hh : (a - b) / period = sweepParam a - sweepParam b - 1 := by
        have hh0 := hrel
        rw [hm1] at hh0
        push_cast at hh0
        linarith [hh0]
      have hnp : (a - b) / period ≤ 0 := by rw [hh]; linarith [hu.2, hu'.1]
      have hle : -((a - b) / period) ≤ θ / 2 := by
        have h2 := hhalf
        rwa [abs_of_nonpos hnp] at h2
      constructor
      · have : sweepParam b = sweepParam a - (a - b) / period - 1 := by linarith [hh]
        linarith [hu.2, hle, hθ0]
      · have : 1 - sweepParam a = -sweepParam b - (a - b) / period := by linarith [hh]
        linarith [hu'.1, hle, hθ0]

/-- **The raw loop is uniformly continuous in the loop parameter**, uniformly in `lam ≤ 1/4` and
in the sweep parameter.  This is `LoopProfileModulus` transported through the profile, with the
wrap-around handled by the matching endpoints of the profile loop. -/
lemma sweepLoopChamfer_t_modulus {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    (hloop : LoopProfileModulus r D) : LoopTModulus r D := by
  intro ε hε
  obtain ⟨θ, hθ0, hθ⟩ := hloop (ε / 2) (by linarith)
  set θ' : ℝ := min θ 1 with hθ'def
  have hθ'0 : 0 < θ' := lt_min hθ0 one_pos
  have hθ'θ : θ' ≤ θ := min_le_left _ _
  have hθ'1 : θ' ≤ 1 := min_le_right _ _
  refine ⟨θ' * period / 2, by have hp := period_pos; positivity, ?_⟩
  intro lam hlam0 hlam14 σ t t' hdist
  have hlam1 : lam < 1 := by linarith
  have hmem : ∀ z : ℝ, sweepParam z ∈ Set.Icc (0 : ℝ) 1 := fun z =>
    ⟨(sweepParam_mem z).1, (sweepParam_mem z).2.le⟩
  have hkey : ∀ w w' : ℝ, w ∈ Set.Icc (0 : ℝ) 1 → w' ∈ Set.Icc (0 : ℝ) 1 → |w - w'| ≤ θ →
      ‖sweepLoopProfile r D lam σ w' - sweepLoopProfile r D lam σ w‖ ≤ ε / 2 :=
    fun w w' hw hw' hww => hθ lam hlam0 hlam14 σ w w' hw hw' hww
  have hz1 : sweepLoopProfile r D lam σ 1 = sweepLoopProfile r D lam σ 0 := by
    rw [sweepLoopProfile_one D hlam0 hlam1 σ, sweepLoopProfile_zero r D lam σ]
  have hone : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  rw [sweepLoopChamfer_eq_profile r D hlam0 hlam1 σ t',
    sweepLoopChamfer_eq_profile r D hlam0 hlam1 σ t]
  rcases sweepParam_near_or_wrap hθ'0 hθ'1 hdist with hc | hc | hc
  · exact le_trans (hkey _ _ (hmem t) (hmem t') (hc.trans hθ'θ)) (by linarith)
  · obtain ⟨h1, h2⟩ := hc
    have hb1 : ‖sweepLoopProfile r D lam σ (sweepParam t') - sweepLoopProfile r D lam σ 1‖
        ≤ ε / 2 :=
      hkey 1 (sweepParam t') hone (hmem t')
        (by rw [abs_of_nonneg (by linarith [(hmem t').2])]; linarith [h2, hθ'θ])
    have hb2 : ‖sweepLoopProfile r D lam σ 0 - sweepLoopProfile r D lam σ (sweepParam t)‖
        ≤ ε / 2 :=
      hkey (sweepParam t) 0 (hmem t) hzero
        (by rw [sub_zero, abs_of_nonneg (hmem t).1]; linarith [h1, hθ'θ])
    calc ‖sweepLoopProfile r D lam σ (sweepParam t') - sweepLoopProfile r D lam σ (sweepParam t)‖
        ≤ ‖sweepLoopProfile r D lam σ (sweepParam t') - sweepLoopProfile r D lam σ 1‖
          + ‖sweepLoopProfile r D lam σ 1 - sweepLoopProfile r D lam σ (sweepParam t)‖ :=
          norm_sub_le_trans _ _ _
      _ = ‖sweepLoopProfile r D lam σ (sweepParam t') - sweepLoopProfile r D lam σ 1‖
          + ‖sweepLoopProfile r D lam σ 0 - sweepLoopProfile r D lam σ (sweepParam t)‖ := by
          rw [← hz1]
      _ ≤ ε / 2 + ε / 2 := add_le_add hb1 hb2
      _ = ε := by ring
  · obtain ⟨h1, h2⟩ := hc
    have hb1 : ‖sweepLoopProfile r D lam σ (sweepParam t') - sweepLoopProfile r D lam σ 0‖
        ≤ ε / 2 :=
      hkey 0 (sweepParam t') hzero (hmem t')
        (by rw [zero_sub, abs_neg, abs_of_nonneg (hmem t').1]; linarith [h1, hθ'θ])
    have hb2 : ‖sweepLoopProfile r D lam σ 1 - sweepLoopProfile r D lam σ (sweepParam t)‖
        ≤ ε / 2 :=
      hkey (sweepParam t) 1 (hmem t) hone
        (by rw [abs_of_nonpos (by linarith [(hmem t).2])]; linarith [h2, hθ'θ])
    have hmid : ‖sweepLoopProfile r D lam σ 0 - sweepLoopProfile r D lam σ 1‖ = 0 := by
      rw [hz1, sub_self, norm_zero]
    calc ‖sweepLoopProfile r D lam σ (sweepParam t') - sweepLoopProfile r D lam σ (sweepParam t)‖
        ≤ ‖sweepLoopProfile r D lam σ (sweepParam t') - sweepLoopProfile r D lam σ 0‖
          + ‖sweepLoopProfile r D lam σ 0 - sweepLoopProfile r D lam σ (sweepParam t)‖ :=
          norm_sub_le_trans _ _ _
      _ ≤ ‖sweepLoopProfile r D lam σ (sweepParam t') - sweepLoopProfile r D lam σ 0‖
          + (‖sweepLoopProfile r D lam σ 0 - sweepLoopProfile r D lam σ 1‖
            + ‖sweepLoopProfile r D lam σ 1 - sweepLoopProfile r D lam σ (sweepParam t)‖) := by
          have := norm_sub_le_trans (sweepLoopProfile r D lam σ 0)
            (sweepLoopProfile r D lam σ 1) (sweepLoopProfile r D lam σ (sweepParam t))
          linarith
      _ = ‖sweepLoopProfile r D lam σ (sweepParam t') - sweepLoopProfile r D lam σ 0‖
          + ‖sweepLoopProfile r D lam σ 1 - sweepLoopProfile r D lam σ (sweepParam t)‖ := by
          rw [hmid]; ring
      _ ≤ ε / 2 + ε / 2 := add_le_add hb1 hb2
      _ = ε := by ring

/-! ## 3. Continuity and the sweep-parameter modulus of the single blur `sweepSmoothT` -/

/-- **The raw loop is continuous in the loop parameter** (for `0 < lam ≤ 1/4`), as an immediate
consequence of the modulus `LoopTModulus`. -/
lemma sweepLoopChamfer_continuous_tCC {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    (ht : LoopTModulus r D) {lam : ℝ} (h0 : 0 < lam) (h4 : lam ≤ 1 / 4) (σ : ℝ) :
    Continuous (fun t : ℝ => sweepLoopChamfer r D lam σ t) := by
  rw [Metric.continuous_iff]
  intro b ε hε
  obtain ⟨T, hT0, hT⟩ := ht (ε / 2) (by linarith)
  refine ⟨T, hT0, fun a ha => ?_⟩
  rw [Real.dist_eq] at ha
  have h := hT lam h0 h4 σ b a (le_of_lt (by rw [abs_sub_comm]; exact ha))
  rw [dist_eq_norm]
  linarith

/-- **The single blur `sweepSmoothT` is uniformly continuous in the sweep parameter**, uniformly in
`lam ≤ 1/4` and in the smoothing scale `δ₁` (and in the loop parameter). -/
lemma sweepSmoothT_sigma_modulus {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    (ht : LoopTModulus r D) (hsweep : LoopSweepModulus r D) : SmoothTModulus r D := by
  intro ε hε
  obtain ⟨θ, hθ0, hθ⟩ := hsweep ε hε
  refine ⟨θ, hθ0, ?_⟩
  intro lam δ₁ hlam0 hlam14 σ σ' t hσ
  have hlam1 : lam < 1 := by linarith
  have hc1 := sweepLoopChamfer_continuous_tCC D ht hlam0 hlam14 σ'
  have hc2 := sweepLoopChamfer_continuous_tCC D ht hlam0 hlam14 σ
  have hcomp1 : Continuous (fun u : ℝ => sweepLoopChamfer r D lam σ' (t - δ₁ * u)) :=
    hc1.comp (continuous_const.sub (continuous_const.mul continuous_id))
  have hcomp2 : Continuous (fun u : ℝ => sweepLoopChamfer r D lam σ (t - δ₁ * u)) :=
    hc2.comp (continuous_const.sub (continuous_const.mul continuous_id))
  have hcont1 : Continuous (fun u : ℝ =>
      sweepBump u • sweepLoopChamfer r D lam σ' (t - δ₁ * u)) :=
    sweepBump_continuous.smul hcomp1
  have hcont2 : Continuous (fun u : ℝ =>
      sweepBump u • sweepLoopChamfer r D lam σ (t - δ₁ * u)) :=
    sweepBump_continuous.smul hcomp2
  have hcontd : Continuous (fun u : ℝ => sweepBump u •
      (sweepLoopChamfer r D lam σ' (t - δ₁ * u) - sweepLoopChamfer r D lam σ (t - δ₁ * u))) :=
    sweepBump_continuous.smul (hcomp1.sub hcomp2)
  have hsplit : sweepSmoothT r D lam δ₁ σ' t - sweepSmoothT r D lam δ₁ σ t
      = ∫ u in (-1 : ℝ)..1, sweepBump u •
          (sweepLoopChamfer r D lam σ' (t - δ₁ * u)
            - sweepLoopChamfer r D lam σ (t - δ₁ * u)) := by
    simp only [sweepSmoothT]
    rw [← intervalIntegral.integral_sub (hcont1.intervalIntegrable (-1) 1)
      (hcont2.intervalIntegrable (-1) 1)]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    rw [smul_sub]
  rw [hsplit]
  refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans ?_
  have hpt : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      ‖sweepBump u • (sweepLoopChamfer r D lam σ' (t - δ₁ * u)
        - sweepLoopChamfer r D lam σ (t - δ₁ * u))‖ ≤ sweepBump u * ε := by
    intro u hu
    rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg u)]
    refine mul_le_mul_of_nonneg_left ?_ (sweepBump_nonneg u)
    rw [sweepLoopChamfer_eq_profile r D hlam0 hlam1 σ' (t - δ₁ * u),
      sweepLoopChamfer_eq_profile r D hlam0 hlam1 σ (t - δ₁ * u)]
    exact hθ lam hlam0 hlam14 σ σ' (sweepParam (t - δ₁ * u))
      ⟨(sweepParam_mem _).1, (sweepParam_mem _).2.le⟩ hσ
  have hmono : (∫ u in (-1 : ℝ)..1, ‖sweepBump u • (sweepLoopChamfer r D lam σ' (t - δ₁ * u)
        - sweepLoopChamfer r D lam σ (t - δ₁ * u))‖)
      ≤ ∫ u in (-1 : ℝ)..1, sweepBump u * ε :=
    intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1)
      ((hcontd.norm).intervalIntegrable (-1) 1)
      ((sweepBump_continuous.mul continuous_const).intervalIntegrable (-1) 1) hpt
  calc (∫ u in (-1 : ℝ)..1, ‖sweepBump u • (sweepLoopChamfer r D lam σ' (t - δ₁ * u)
        - sweepLoopChamfer r D lam σ (t - δ₁ * u))‖)
      ≤ ∫ u in (-1 : ℝ)..1, sweepBump u * ε := hmono
    _ = ε := by rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]

/-- **`sweepSmoothT` is continuous in the sweep parameter**, for `0 < lam ≤ 1/4`. -/
lemma sweepSmoothT_sigma_continuous {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    (ht : LoopTModulus r D) (hsweep : LoopSweepModulus r D)
    {lam δ₁ : ℝ} (h0 : 0 < lam) (h4 : lam ≤ 1 / 4) (t : ℝ) :
    Continuous (fun σ' : ℝ => sweepSmoothT r D lam δ₁ σ' t) := by
  rw [Metric.continuous_iff]
  intro b ε hε
  obtain ⟨θ, hθ0, hθ⟩ := sweepSmoothT_sigma_modulus D ht hsweep (ε / 2) (by linarith)
  refine ⟨θ, hθ0, fun a ha => ?_⟩
  rw [Real.dist_eq] at ha
  have h := hθ lam δ₁ h0 h4 b a t (le_of_lt (by rw [abs_sub_comm]; exact ha))
  rw [dist_eq_norm]
  linarith


/-- Continuity of `sweepSmoothT` in the sweep parameter, from its modulus. -/
lemma smoothTModulus_continuous {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    (hs : SmoothTModulus r D) {lam δ₁ : ℝ} (h0 : 0 < lam) (h4 : lam ≤ 1 / 4) (t : ℝ) :
    Continuous (fun σ' : ℝ => sweepSmoothT r D lam δ₁ σ' t) := by
  rw [Metric.continuous_iff]
  intro b ε hε
  obtain ⟨θ, hθ0, hθ⟩ := hs (ε / 2) (by linarith)
  refine ⟨θ, hθ0, fun a ha => ?_⟩
  rw [Real.dist_eq] at ha
  have h := hθ lam δ₁ h0 h4 b a t (le_of_lt (by rw [abs_sub_comm]; exact ha))
  rw [dist_eq_norm]
  linarith

/-! ## 4. The master estimate -/

theorem sweepFam_close_chamfer_aux {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    (ht : LoopTModulus r D) (hs : SmoothTModulus r D) :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, 0 < L ∧
      ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ L → 0 < δ₁ → δ₁ ≤ L → 0 < δ₂ → δ₂ ≤ L →
        ∀ σ t : ℝ,
          ‖sweepFam r D lam δ₁ δ₂ σ t - sweepLoopChamfer r D lam σ t‖ ≤ ε := by
  intro ε hε
  obtain ⟨T, hT0, hT⟩ := ht (ε / 2) (by linarith)
  obtain ⟨S, hS0, hS⟩ := hs (ε / 2) (by linarith)
  have hT' : ∀ (lam : ℝ), 0 < lam → lam ≤ 1 / 4 → ∀ (σ t t' : ℝ), |t - t'| ≤ T →
      ‖sweepLoopChamfer r D lam σ t' - sweepLoopChamfer r D lam σ t‖ ≤ ε / 2 := hT
  have hS' : ∀ (lam δ₁ : ℝ), 0 < lam → lam ≤ 1 / 4 → ∀ (σ σ' : ℝ) (t : ℝ), |σ - σ'| ≤ S →
      ‖sweepSmoothT r D lam δ₁ σ' t - sweepSmoothT r D lam δ₁ σ t‖ ≤ ε / 2 := hS
  refine ⟨min (1 / 4) (min T S), lt_min (by norm_num) (lt_min hT0 hS0), ?_⟩
  intro lam δ₁ δ₂ hlam0 hlamL hδ₁0 hδ₁L hδ₂0 hδ₂L σ t
  have hlam14 : lam ≤ 1 / 4 := hlamL.trans (min_le_left _ _)
  have hδ₁T : δ₁ ≤ T := hδ₁L.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ₂S : δ₂ ≤ S := hδ₂L.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hstep1 : ‖sweepSmoothT r D lam δ₁ σ t - sweepLoopChamfer r D lam σ t‖ ≤ ε / 2 := by
    have key : ‖(∫ u in (-1 : ℝ)..1, sweepBump u • sweepLoopChamfer r D lam σ (t - δ₁ * u))
        - sweepLoopChamfer r D lam σ t‖ ≤ ε / 2 :=
      sweepBlur_close (f := fun x : ℝ => sweepLoopChamfer r D lam σ x) (δ := T) (δ' := δ₁)
        (ε := ε / 2) (sweepLoopChamfer_continuous_tCC D ht hlam0 hlam14 σ) (by linarith)
        (fun x h hh => hT' lam hlam0 hlam14 σ x (x + h)
          (by rw [show x - (x + h) = -h by ring, abs_neg]; exact hh))
        (by rw [abs_of_pos hδ₁0]; exact hδ₁T) t
    simpa only [sweepSmoothT] using key
  have hstep2 : ‖sweepFam r D lam δ₁ δ₂ σ t - sweepSmoothT r D lam δ₁ σ t‖ ≤ ε / 2 := by
    have key : ‖(∫ v in (-1 : ℝ)..1, sweepBump v • sweepSmoothT r D lam δ₁ (σ - δ₂ * v) t)
        - sweepSmoothT r D lam δ₁ σ t‖ ≤ ε / 2 :=
      sweepBlur_close (f := fun x : ℝ => sweepSmoothT r D lam δ₁ x t) (δ := S) (δ' := δ₂)
        (ε := ε / 2) (smoothTModulus_continuous D hs hlam0 hlam14 t) (by linarith)
        (fun x h hh => hS' lam δ₁ hlam0 hlam14 x (x + h) t
          (by rw [show x - (x + h) = -h by ring, abs_neg]; exact hh))
        (by rw [abs_of_pos hδ₂0]; exact hδ₂S) σ
    simpa only [sweepFam] using key
  calc ‖sweepFam r D lam δ₁ δ₂ σ t - sweepLoopChamfer r D lam σ t‖
      ≤ ‖sweepFam r D lam δ₁ δ₂ σ t - sweepSmoothT r D lam δ₁ σ t‖
        + ‖sweepSmoothT r D lam δ₁ σ t - sweepLoopChamfer r D lam σ t‖ :=
        norm_sub_le_trans _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hstep2 hstep1
    _ = ε := by ring

/-- The target, from the two moduli of the profile loop. -/
theorem sweepFam_close_chamfer_of_moduli {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    (hloop : LoopProfileModulus r D) (hsweep : LoopSweepModulus r D) :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, 0 < L ∧
      ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ L → 0 < δ₁ → δ₁ ≤ L → 0 < δ₂ → δ₂ ≤ L →
        ∀ σ t : ℝ,
          ‖sweepFam r D lam δ₁ δ₂ σ t - sweepLoopChamfer r D lam σ t‖ ≤ ε := by
  have ht : LoopTModulus r D := sweepLoopChamfer_t_modulus D hloop
  have hs : SmoothTModulus r D := sweepSmoothT_sigma_modulus D ht hsweep
  exact sweepFam_close_chamfer_aux D ht hs

/-! ## 5. The target -/

theorem sweepFam_close_chamfer {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space} (hr : Continuous r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, 0 < L ∧
      ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ L → 0 < δ₁ → δ₁ ≤ L → 0 < δ₂ → δ₂ ≤ L →
        ∀ σ t : ℝ,
          ‖Work.Drive.sweepFam r D lam δ₁ δ₂ σ t - Work.Drive.sweepLoopChamfer r D lam σ t‖ ≤ ε := by
  have hloop : LoopProfileModulus r D := sweepLoopProfile_uniformCont_loop D hr
  have hsweep : LoopSweepModulus r D := sweepLoopProfile_uniformCont_sweep D hr
  exact sweepFam_close_chamfer_of_moduli D hloop hsweep

end Work.Drive
