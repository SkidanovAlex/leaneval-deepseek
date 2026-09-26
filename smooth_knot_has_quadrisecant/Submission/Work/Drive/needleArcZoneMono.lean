import Mathlib
import Submission.Work.Drive.needleProfileDefs
import Submission.Work.Drive.needleFam_inner_eq_devAvg
import Submission.Work.Drive.chordFrame
import Submission.Work.Drive.sweepFamFarSep
import Submission.Work.Drive.arcZoneWindow
import Submission.Work.Drive.sweepFam_arcZone

set_option maxHeartbeats 1000000

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

/-! ## 1. The loop parameter is affine on an arc zone

If `sweepParam (t - δ₁ * u) ≤ 1/2` throughout a window `u ∈ [-1,1]` and the window is shorter than
half a period, then the fractional part `sweepParam (t - δ₁ * u)` is *affine* in `u` there, with
slope `-δ₁ / period`.  In particular the arc fractions of the two loop parameters `t₁ < t₂` differ
by the constant `(t₂ - t₁)/period`. -/

/-- Two points whose fractional parts are `≤ 1/2` and which are closer than half a period lie in
the same period cell. -/
lemma floor_div_eq_of_sweepParam_le {x y : ℝ} (hx : sweepParam x ≤ 1 / 2)
    (hy : sweepParam y ≤ 1 / 2) (hxy : |x - y| < period / 2) :
    ⌊x / period⌋ = ⌊y / period⌋ := by
  have hp : (0 : ℝ) < period := period_pos
  have hxge : ((⌊x / period⌋ : ℤ) : ℝ) ≤ x / period := Int.floor_le _
  have hxle : x / period ≤ ((⌊x / period⌋ : ℤ) : ℝ) + 1 / 2 := by
    have h := hx; rw [sweepParam] at h; linarith
  have hyge : ((⌊y / period⌋ : ℤ) : ℝ) ≤ y / period := Int.floor_le _
  have hyle : y / period ≤ ((⌊y / period⌋ : ℤ) : ℝ) + 1 / 2 := by
    have h := hy; rw [sweepParam] at h; linarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : ((⌊x / period⌋ : ℤ) : ℝ) + 1 ≤ ((⌊y / period⌋ : ℤ) : ℝ) := by
      have hcast : ⌊x / period⌋ + 1 ≤ ⌊y / period⌋ := by omega
      exact_mod_cast hcast
    have h2 : x / period ≤ y / period - 1 / 2 := by linarith
    have h3 : x ≤ y - period / 2 := by
      have h4 : x ≤ (y / period - 1 / 2) * period := (div_le_iff₀ hp).mp h2
      have h5 : (y / period - 1 / 2) * period = y - period / 2 := by
        rw [sub_mul, div_mul_cancel₀ y (ne_of_gt hp)]; ring
      linarith [h4, h5]
    have h6 : period / 2 ≤ |x - y| := by
      have h7 : 0 ≤ y - x := by linarith
      rw [abs_sub_comm, abs_of_nonneg h7]; linarith
    linarith [hxy, h6]
  · have h1 : ((⌊y / period⌋ : ℤ) : ℝ) + 1 ≤ ((⌊x / period⌋ : ℤ) : ℝ) := by
      have hcast : ⌊y / period⌋ + 1 ≤ ⌊x / period⌋ := by omega
      exact_mod_cast hcast
    have h2 : y / period ≤ x / period - 1 / 2 := by linarith
    have h3 : y ≤ x - period / 2 := by
      have h4 : y ≤ (x / period - 1 / 2) * period := (div_le_iff₀ hp).mp h2
      have h5 : (x / period - 1 / 2) * period = x - period / 2 := by
        rw [sub_mul, div_mul_cancel₀ x (ne_of_gt hp)]; ring
      linarith [h4, h5]
    have h6 : period / 2 ≤ |x - y| := by
      have h7 : 0 ≤ x - y := by linarith
      rw [abs_of_nonneg h7]; linarith
    linarith [hxy, h6]

/-- In the same situation the difference of the fractional parts is `(x - y)/period`. -/
lemma sweepParam_sub_eq_of_le_half {x y : ℝ} (hx : sweepParam x ≤ 1 / 2)
    (hy : sweepParam y ≤ 1 / 2) (hxy : |x - y| < period / 2) :
    sweepParam x - sweepParam y = (x - y) / period := by
  have hk := floor_div_eq_of_sweepParam_le hx hy hxy
  rw [sweepParam, sweepParam, hk, sub_div]
  ring

/-- **The loop parameter is affine on an arc zone.** -/
lemma sweepParam_sub_eq {t δ₁ u : ℝ} (hδ0 : 0 < δ₁) (hδ : δ₁ < period / 2)
    (hu : u ∈ Set.Icc (-1 : ℝ) 1)
    (hzone : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → sweepParam (t - δ₁ * u) ≤ 1 / 2) :
    sweepParam (t - δ₁ * u) = sweepParam t - δ₁ * u / period := by
  have h0 : sweepParam t ≤ 1 / 2 := by
    have h := hzone 0 (by norm_num); simpa using h
  have hxy : |(t - δ₁ * u) - t| < period / 2 := by
    have he : (t - δ₁ * u) - t = -(δ₁ * u) := by ring
    rw [he, abs_neg, abs_mul, abs_of_pos hδ0]
    have hu' : |u| ≤ 1 := by rw [abs_le]; exact hu
    nlinarith [hδ, hu', hδ0]
  have h := sweepParam_sub_eq_of_le_half (hzone u hu) h0 hxy
  have h1 : (t - δ₁ * u) - t = -(δ₁ * u) := by ring
  rw [h1, neg_div] at h
  linarith [h]

/-- **The arc fraction of an orthogonal (arc-branch) loop parameter is affine.** -/
lemma arcFrac_eq_affine {lam δ₁ t u : ℝ} (hδ0 : 0 < δ₁) (hδ : δ₁ < period / 2)
    (hu : u ∈ Set.Icc (-1 : ℝ) 1)
    (hzone : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → sweepParam (t - δ₁ * u) ≤ 1 / 2) :
    arcFrac lam δ₁ t u = lam + (1 - 2 * lam) * (2 * (sweepParam t - δ₁ * u / period)) := by
  rw [arcFrac, sweepParam_sub_eq hδ0 hδ hu hzone]

/-! ## 2. Two elementary calculus facts -/

/-- The derivative of the arc parameterization `ξ ↦ sweepArc' r D σ ξ`. -/
lemma deriv_sweepArc' {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d)
    (sg ξ : ℝ) :
    deriv (fun ξ : ℝ => sweepArc' r D sg ξ) ξ
      = sweepW' D sg • velocity r (taR D sg + ξ * sweepW' D sg) := by
  have hdiffr : DifferentiableAt ℝ r (taR D sg + ξ * sweepW' D sg) :=
    (hr.smooth.differentiable (by simp)).differentiableAt
  have hlin : DifferentiableAt ℝ (fun ξ : ℝ => taR D sg + ξ * sweepW' D sg) ξ := by fun_prop
  have hcomp := deriv.scomp ξ hdiffr hlin
  have hlin_deriv : deriv (fun ξ : ℝ => taR D sg + ξ * sweepW' D sg) ξ = sweepW' D sg := by
    have h : HasDerivAt (fun ξ : ℝ => taR D sg + ξ * sweepW' D sg) (sweepW' D sg) ξ := by
      simpa using ((hasDerivAt_id ξ).mul_const (sweepW' D sg)).const_add (taR D sg)
    exact h.deriv
  have hfun : (fun ξ : ℝ => sweepArc' r D sg ξ)
      = (fun y : ℝ => r y) ∘ (fun ξ : ℝ => taR D sg + ξ * sweepW' D sg) := rfl
  rw [hfun, hcomp, hlin_deriv]
  rfl

/-- **The velocity pairing at two close parameters is bounded below.** -/
lemma inner_velocity_lower {r : ℝ → Space} {m M C : ℝ} (hm : 0 < m) (hM : 0 < M) (hC : 0 < C)
    (hmin : ∀ t : ℝ, m ≤ ‖velocity r t‖) (hmax : ∀ t : ℝ, ‖velocity r t‖ ≤ M)
    (hlip : ∀ t t' : ℝ, ‖velocity r t - velocity r t'‖ ≤ C * |t' - t|)
    {x y : ℝ} (hxy : |x - y| ≤ m ^ 2 / (2 * M * C)) :
    m ^ 2 / 2 ≤ inner ℝ (velocity r x) (velocity r y) := by
  have hsplit : inner ℝ (velocity r x) (velocity r y)
      = ‖velocity r x‖ ^ 2 - inner ℝ (velocity r x) (velocity r x - velocity r y) := by
    have h : velocity r y = velocity r x - (velocity r x - velocity r y) := by abel
    conv_lhs => rw [h]
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
  have hb : inner ℝ (velocity r x) (velocity r x - velocity r y)
      ≤ ‖velocity r x‖ * ‖velocity r x - velocity r y‖ :=
    le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)
  have hb2 : ‖velocity r x‖ * ‖velocity r x - velocity r y‖ ≤ M * (C * |x - y|) := by
    have h1 : ‖velocity r x‖ ≤ M := hmax x
    have h2 : ‖velocity r x - velocity r y‖ ≤ C * |x - y| := by
      have h := hlip x y
      rwa [abs_sub_comm] at h
    exact mul_le_mul h1 h2 (norm_nonneg _) hM.le
  have hspd : m ^ 2 ≤ ‖velocity r x‖ ^ 2 := by nlinarith [hmin x, hm]
  have hMC : M * (C * |x - y|) ≤ m ^ 2 / 2 := by
    have hpos : 0 < 2 * M * C := by positivity
    have h := (le_div_iff₀ hpos).mp hxy
    linarith [h]
  linarith [hsplit, hb, hb2, hspd, hMC]

/-- The arc parameterization `ξ ↦ sweepArc' r D σ ξ` is continuous. -/
lemma continuous_sweepArc'_arcZoneMono {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) (sg : ℝ) : Continuous (fun ξ : ℝ => sweepArc' r D sg ξ) := by
  have hc : Continuous (fun ξ : ℝ => taR D sg + ξ * sweepW' D sg) := by fun_prop
  exact hr.smooth.continuous.comp hc

/-- The velocity along a retained arc is continuous. -/
lemma continuous_velocity_comp {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) (sg : ℝ) :
    Continuous (fun t : ℝ => velocity r (taR D sg + t * sweepW' D sg)) := by
  have hc : Continuous (fun t : ℝ => taR D sg + t * sweepW' D sg) := by fun_prop
  exact (hr.smooth.continuous_deriv (by simp)).comp hc

/-- **The key pointwise estimate.**  The increment of the retained arc between the arc fractions
`ξ₁ ≤ ξ₂`, paired with the chord `r (tb σ') - r (ta σ')` of a (possibly different) short retained
arc, is bounded below by `W (σ) * W (σ') * (ξ₂ - ξ₁) * m² / 2`. -/
theorem arcInner_lower {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d)
    {m M C : ℝ} (hm : 0 < m) (hM : 0 < M) (hC : 0 < C)
    (hmin : ∀ t : ℝ, m ≤ ‖velocity r t‖) (hmax : ∀ t : ℝ, ‖velocity r t‖ ≤ M)
    (hlip : ∀ t t' : ℝ, ‖velocity r t - velocity r t'‖ ≤ C * |t' - t|)
    {sg sg' : ℝ} (hW : 0 ≤ sweepW' D sg) (hW' : 0 ≤ sweepW' D sg')
    (hsmall : |taR D sg - taR D sg'| + sweepW' D sg + sweepW' D sg' ≤ m ^ 2 / (2 * M * C))
    {ξ₁ ξ₂ : ℝ} (h1 : 0 ≤ ξ₁) (h12 : ξ₁ ≤ ξ₂) (h2 : ξ₂ ≤ 1) :
    sweepW' D sg * sweepW' D sg' * (ξ₂ - ξ₁) * (m ^ 2 / 2)
      ≤ inner ℝ (sweepArc' r D sg ξ₂ - sweepArc' r D sg ξ₁)
          (sweepArc' r D sg' 1 - sweepArc' r D sg' 0) := by
  have hthr : 0 < m ^ 2 / (2 * M * C) := by positivity
  have hΓ : sweepArc' r D sg' 1 - sweepArc' r D sg' 0
      = ∫ t in (0 : ℝ)..1, sweepW' D sg' • velocity r (taR D sg' + t * sweepW' D sg') := by
    have hd : deriv (fun x : ℝ => sweepArc' r D sg' x)
        = fun t : ℝ => sweepW' D sg' • velocity r (taR D sg' + t * sweepW' D sg') := by
      funext x
      exact deriv_sweepArc' hr D sg' x
    refine (intervalIntegral.integral_deriv_eq_sub' (a := (0 : ℝ)) (b := 1)
      (f := fun x : ℝ => sweepArc' r D sg' x) hd ?_ ?_).symm
    · intro x _
      show DifferentiableAt ℝ (fun y : ℝ => r (taR D sg' + y * sweepW' D sg')) x
      exact (hr.smooth.differentiable (by simp)).differentiableAt.comp x (by fun_prop)
    · exact ((continuous_velocity_comp hr D sg').const_smul (sweepW' D sg')).continuousOn
  have hG : ∀ x : ℝ, |x - taR D sg'| + sweepW' D sg' ≤ m ^ 2 / (2 * M * C) →
      sweepW' D sg' * (m ^ 2 / 2)
        ≤ inner ℝ (velocity r x) (sweepArc' r D sg' 1 - sweepArc' r D sg' 0) := by
    intro x hx
    rw [hΓ]
    rw [inner_intervalIntegral_comm
      (f := fun t : ℝ => sweepW' D sg' • velocity r (taR D sg' + t * sweepW' D sg'))
      (((continuous_velocity_comp hr D sg').const_smul (sweepW' D sg')).intervalIntegrable (0 : ℝ) 1)
      (velocity r x)]
    have hconst : (∫ t in (0 : ℝ)..1, sweepW' D sg' * (m ^ 2 / 2))
        = sweepW' D sg' * (m ^ 2 / 2) := by
      rw [intervalIntegral.integral_const]; simp
    rw [← hconst]
    refine intervalIntegral.integral_mono_on (by norm_num : ((0 : ℝ) ≤ 1)) ?_ ?_ ?_
    · exact continuous_const.intervalIntegrable _ _
    · exact (Continuous.inner (continuous_const : Continuous fun _ : ℝ => velocity r x)
        ((continuous_velocity_comp hr D sg').const_smul (sweepW' D sg'))).intervalIntegrable
        (0 : ℝ) 1
    · intro t ht
      rw [real_inner_smul_right]
      have hdist : |x - (taR D sg' + t * sweepW' D sg')| ≤ m ^ 2 / (2 * M * C) := by
        have he : x - (taR D sg' + t * sweepW' D sg') = (x - taR D sg') - t * sweepW' D sg' := by
          ring
        have h3 : |(x - taR D sg') - t * sweepW' D sg'|
            ≤ |x - taR D sg'| + |t * sweepW' D sg'| := abs_sub _ _
        have h4 : |t * sweepW' D sg'| ≤ sweepW' D sg' := by
          rw [abs_mul, abs_of_nonneg hW', abs_of_nonneg ht.1]
          nlinarith [hW', ht.1, ht.2]
        rw [he]; linarith [h3, h4, hx]
      have hlow := inner_velocity_lower hm hM hC hmin hmax hlip hdist
      nlinarith [hlow, hW']
  rcases lt_or_eq_of_le h12 with hlt | heq
  · set φ : ℝ → ℝ := fun x => inner ℝ (sweepArc' r D sg x - sweepArc' r D sg ξ₁)
      (sweepArc' r D sg' 1 - sweepArc' r D sg' 0) with hφ
    have hφξ₁ : φ ξ₁ = 0 := by simp [hφ]
    have hcont : ContinuousOn φ (Set.Icc ξ₁ ξ₂) := by
      rw [hφ]
      refine Continuous.continuousOn ?_
      exact Continuous.inner ((continuous_sweepArc'_arcZoneMono hr D sg).sub continuous_const) continuous_const
    have hdiff : DifferentiableOn ℝ φ (Set.Ioo ξ₁ ξ₂) := by
      intro x _
      rw [hφ]
      refine DifferentiableAt.differentiableWithinAt ?_
      have h1' : DifferentiableAt ℝ (fun x : ℝ => sweepArc' r D sg x - sweepArc' r D sg ξ₁) x := by
        refine DifferentiableAt.sub ?_ (differentiableAt_const _)
        show DifferentiableAt ℝ (fun y : ℝ => r (taR D sg + y * sweepW' D sg)) x
        exact (hr.smooth.differentiable (by simp)).differentiableAt.comp x (by fun_prop)
      exact h1'.inner ℝ (differentiableAt_const _)
    obtain ⟨xs, hxs, hder⟩ := exists_deriv_eq_slope φ hlt hcont hdiff
    have hderiv_eq : deriv φ xs
        = inner ℝ (sweepW' D sg • velocity r (taR D sg + xs * sweepW' D sg))
            (sweepArc' r D sg' 1 - sweepArc' r D sg' 0) := by
      rw [hφ]
      have h1' : DifferentiableAt ℝ (fun x : ℝ => sweepArc' r D sg x - sweepArc' r D sg ξ₁) xs := by
        refine DifferentiableAt.sub ?_ (differentiableAt_const _)
        show DifferentiableAt ℝ (fun y : ℝ => r (taR D sg + y * sweepW' D sg)) xs
        exact (hr.smooth.differentiable (by simp)).differentiableAt.comp xs (by fun_prop)
      have hd1 : deriv (fun x : ℝ => sweepArc' r D sg x - sweepArc' r D sg ξ₁) xs
          = sweepW' D sg • velocity r (taR D sg + xs * sweepW' D sg) := by
        rw [deriv_sub_const, deriv_sweepArc' hr D sg xs]
      have hmain := deriv_inner_apply (𝕜 := ℝ)
        (f := fun x : ℝ => sweepArc' r D sg x - sweepArc' r D sg ξ₁)
        (g := fun _ : ℝ => sweepArc' r D sg' 1 - sweepArc' r D sg' 0)
        h1' (differentiableAt_const
          (c := sweepArc' r D sg' 1 - sweepArc' r D sg' 0) (x := xs))
      rw [hd1] at hmain
      simpa using hmain
    have hmono : sweepW' D sg * (sweepW' D sg' * (m ^ 2 / 2)) ≤ deriv φ xs := by
      rw [hderiv_eq, real_inner_smul_left]
      have hx : |(taR D sg + xs * sweepW' D sg) - taR D sg'| + sweepW' D sg'
          ≤ m ^ 2 / (2 * M * C) := by
        have he : (taR D sg + xs * sweepW' D sg) - taR D sg'
            = (taR D sg - taR D sg') + xs * sweepW' D sg := by ring
        have h3 : |(taR D sg + xs * sweepW' D sg) - taR D sg'|
            ≤ |taR D sg - taR D sg'| + |xs * sweepW' D sg| := by
          rw [he]; exact abs_add_le _ _
        have h4 : |xs * sweepW' D sg| ≤ sweepW' D sg := by
          rw [abs_mul, abs_of_nonneg hW, abs_of_nonneg (le_trans h1 hxs.1.le)]
          nlinarith [hW, le_trans hxs.2.le h2]
        rw [he] at h3
        rw [he]
        linarith [h3, h4, hsmall]
      exact mul_le_mul_of_nonneg_left (hG _ hx) hW
    have hpos : 0 < ξ₂ - ξ₁ := sub_pos.mpr hlt
    have hkey : (ξ₂ - ξ₁) * (sweepW' D sg * (sweepW' D sg' * (m ^ 2 / 2))) ≤ φ ξ₂ - φ ξ₁ := by
      rw [hder] at hmono
      rw [le_div_iff₀ hpos] at hmono
      linarith [hmono]
    have hfin : sweepW' D sg * sweepW' D sg' * (ξ₂ - ξ₁) * (m ^ 2 / 2) ≤ φ ξ₂ := by
      rw [hφξ₁, sub_zero] at hkey
      nlinarith [hkey]
    simpa only [hφ] using hfin
  · subst heq
    have hzero : ξ₁ - ξ₁ = 0 := by ring
    rw [hzero]
    simp

/-! ## 4. Continuity and integrability of the blur integrands -/

lemma continuous_arcComp {r : ℝ → Space} (hr : Continuous r) {d : BandArcData} (D : SweepData d)
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun u : ℝ => sweepArc' r D (f u) (g u)) := by
  have h1 : Continuous (fun u : ℝ => taR D (f u) + g u * sweepW' D (f u)) :=
    ((arcWin_taR_continuous D).comp hf).add (hg.mul ((arcWin_sweepW'_continuous D).comp hf))
  exact hr.comp h1

lemma continuous_arcComp2 {r : ℝ → Space} (hr : Continuous r) {d : BandArcData} (D : SweepData d)
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun p : ℝ × ℝ => sweepArc' r D (f p.1) (g p.2)) := by
  have h1 : Continuous (fun p : ℝ × ℝ => taR D (f p.1) + g p.2 * sweepW' D (f p.1)) :=
    ((arcWin_taR_continuous D).comp (hf.comp continuous_fst)).add
      ((hg.comp continuous_snd).mul ((arcWin_sweepW'_continuous D).comp (hf.comp continuous_fst)))
  exact hr.comp h1

/-- The blur `v ↦ ∫ u, bump u • sweepArc' r D (f v) (g u)` is continuous. -/
lemma continuous_blur_arc {r : ℝ → Space} (hr : Continuous r) {d : BandArcData} (D : SweepData d)
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun v : ℝ => ∫ u in (-1 : ℝ)..1, sweepBump u • sweepArc' r D (f v) (g u)) := by
  have hjoint : Continuous
      (Function.uncurry (fun v u : ℝ => sweepBump u • sweepArc' r D (f v) (g u))) := by
    show Continuous (fun p : ℝ × ℝ => sweepBump p.2 • sweepArc' r D (f p.1) (g p.2))
    exact (sweepBump_continuous.comp continuous_snd).smul (continuous_arcComp2 hr D hf hg)
  simpa using intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (a₀ := (-1 : ℝ)) hjoint (continuous_const : Continuous fun _ : ℝ => (1 : ℝ))

/-- The blur of an arc increment `v ↦ ∫ u, bump u • (arc (f v) (g₂ u) - arc (f v) (g₁ u))` is
continuous. -/
lemma continuous_blur_sub_arc {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) {f g₁ g₂ : ℝ → ℝ} (hf : Continuous f) (hg₁ : Continuous g₁)
    (hg₂ : Continuous g₂) :
    Continuous (fun v : ℝ => ∫ u in (-1 : ℝ)..1, sweepBump u •
      (sweepArc' r D (f v) (g₂ u) - sweepArc' r D (f v) (g₁ u))) := by
  have hjoint : Continuous
      (Function.uncurry (fun v u : ℝ => sweepBump u •
        (sweepArc' r D (f v) (g₂ u) - sweepArc' r D (f v) (g₁ u)))) := by
    show Continuous (fun p : ℝ × ℝ => sweepBump p.2 •
      (sweepArc' r D (f p.1) (g₂ p.2) - sweepArc' r D (f p.1) (g₁ p.2)))
    exact (sweepBump_continuous.comp continuous_snd).smul
      ((continuous_arcComp2 hr D hf hg₂).sub (continuous_arcComp2 hr D hf hg₁))
  simpa using intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (a₀ := (-1 : ℝ)) hjoint (continuous_const : Continuous fun _ : ℝ => (1 : ℝ))

/-! ## 5. The needle on the arc zone and its difference -/

/-- The needle on the arc zone, as a double blur of the retained arc at a *given* arc-fraction map
`ξ` agreeing with `arcFrac` on the window. -/
lemma needleFam_eq_blur {r : ℝ → Space} (hr : Continuous r) {d : BandArcData} (D : SweepData d)
    {lam δ₁ δ₂ ε t : ℝ} (hlam : lam < 1 / 2) (hδ₁0 : 0 < δ₁) (hδ₁ : δ₁ < period / 2)
    (hzone : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → sweepParam (t - δ₁ * u) ≤ 1 / 2)
    {ξ : ℝ → ℝ} (hξ : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → arcFrac lam δ₁ t u = ξ u) :
    needleFam r D lam δ₁ δ₂ ε t
      = ∫ v in (-1 : ℝ)..1, sweepBump v •
          (∫ u in (-1 : ℝ)..1, sweepBump u • sweepArc' r D (ε - δ₂ * v) (ξ u)) := by
  rw [needleFam_apply, sweepFam_arcZone hr D hlam hzone]
  refine intervalIntegral.integral_congr (fun v _ => ?_)
  congr 1
  refine intervalIntegral.integral_congr (fun u hu => ?_)
  rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hu
  rw [sweepArc']
  have h : lam + (1 - 2 * lam) * (2 * sweepParam (t - δ₁ * u)) = ξ u := by
    have h' := hξ u hu
    rw [arcFrac] at h'
    exact h'
  rw [h]

/-- **The needle's increment is the double blur of the arc increments.** -/
lemma needleFam_diff_eq_blur {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) {lam δ₁ δ₂ ε t₁ t₂ : ℝ} (hlam : lam < 1 / 2) (hδ₁0 : 0 < δ₁)
    (hδ₁ : δ₁ < period / 2)
    (hzone1 : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → sweepParam (t₁ - δ₁ * u) ≤ 1 / 2)
    (hzone2 : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → sweepParam (t₂ - δ₁ * u) ≤ 1 / 2)
    {ξ1 ξ2 : ℝ → ℝ} (hξ1c : Continuous ξ1) (hξ2c : Continuous ξ2)
    (hξ1 : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → arcFrac lam δ₁ t₁ u = ξ1 u)
    (hξ2 : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → arcFrac lam δ₁ t₂ u = ξ2 u) :
    needleFam r D lam δ₁ δ₂ ε t₂ - needleFam r D lam δ₁ δ₂ ε t₁
      = ∫ v in (-1 : ℝ)..1, sweepBump v •
          (∫ u in (-1 : ℝ)..1, sweepBump u •
            (sweepArc' r D (ε - δ₂ * v) (ξ2 u) - sweepArc' r D (ε - δ₂ * v) (ξ1 u))) := by
  rw [needleFam_eq_blur hr D hlam hδ₁0 hδ₁ hzone2 hξ2,
    needleFam_eq_blur hr D hlam hδ₁0 hδ₁ hzone1 hξ1]
  have hI2 : IntervalIntegrable (fun v : ℝ => sweepBump v •
      (∫ u in (-1 : ℝ)..1, sweepBump u • sweepArc' r D (ε - δ₂ * v) (ξ2 u)))
      volume (-1 : ℝ) 1 :=
    (sweepBump_continuous.smul
      (continuous_blur_arc hr D (f := fun v : ℝ => ε - δ₂ * v) (g := ξ2)
        (by fun_prop) hξ2c)).intervalIntegrable _ _
  have hI1 : IntervalIntegrable (fun v : ℝ => sweepBump v •
      (∫ u in (-1 : ℝ)..1, sweepBump u • sweepArc' r D (ε - δ₂ * v) (ξ1 u)))
      volume (-1 : ℝ) 1 :=
    (sweepBump_continuous.smul
      (continuous_blur_arc hr D (f := fun v : ℝ => ε - δ₂ * v) (g := ξ1)
        (by fun_prop) hξ1c)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hI2 hI1]
  refine intervalIntegral.integral_congr (fun v _ => ?_)
  have hJ2 : IntervalIntegrable (fun u : ℝ => sweepBump u • sweepArc' r D (ε - δ₂ * v) (ξ2 u))
      volume (-1 : ℝ) 1 :=
    ((sweepBump_continuous.smul
      (continuous_arcComp hr D (continuous_const : Continuous fun _ : ℝ => ε - δ₂ * v)
        hξ2c)).intervalIntegrable _ _)
  have hJ1 : IntervalIntegrable (fun u : ℝ => sweepBump u • sweepArc' r D (ε - δ₂ * v) (ξ1 u))
      volume (-1 : ℝ) 1 :=
    ((sweepBump_continuous.smul
      (continuous_arcComp hr D (continuous_const : Continuous fun _ : ℝ => ε - δ₂ * v)
        hξ1c)).intervalIntegrable _ _)
  have hstep : (∫ u in (-1 : ℝ)..1, sweepBump u •
        (sweepArc' r D (ε - δ₂ * v) (ξ2 u) - sweepArc' r D (ε - δ₂ * v) (ξ1 u)))
      = (∫ u in (-1 : ℝ)..1, sweepBump u • sweepArc' r D (ε - δ₂ * v) (ξ2 u))
        - (∫ u in (-1 : ℝ)..1, sweepBump u • sweepArc' r D (ε - δ₂ * v) (ξ1 u)) := by
    rw [← intervalIntegral.integral_sub hJ2 hJ1]
    exact intervalIntegral.integral_congr (fun u _ => by rw [smul_sub])
  rw [hstep, smul_sub]

/-- **The needle's chord vector** as the blur of the loops' chords (in the `sweepArc'` form). -/
lemma chordEnd_sub_eq' {r : ℝ → Space} (hr : Continuous r) {d : BandArcData} (D : SweepData d)
    (δ₂ ε : ℝ) :
    chordEndB r D δ₂ ε - chordEndA r D δ₂ ε
      = ∫ v in (-1 : ℝ)..1, sweepBump v •
          (sweepArc' r D (ε - δ₂ * v) 1 - sweepArc' r D (ε - δ₂ * v) 0) := by
  rw [chordEndB_sub_chordEndA r D hr δ₂ ε]
  refine intervalIntegral.integral_congr (fun v _ => ?_)
  congr 1
  rw [sweepArc', sweepArc']
  simp only [one_mul, zero_mul, add_zero]
  rw [show taR D (ε - δ₂ * v) + sweepW' D (ε - δ₂ * v) = tbR D (ε - δ₂ * v) by
    rw [sweepW']; ring]

/-- **Positivity of the weighted width.** -/
lemma integral_sweepBump_mul_sweepW_pos {d : BandArcData} (D : SweepData d) {δ₂ ε : ℝ}
    (hε0 : 0 < ε) (hδ₂0 : 0 ≤ δ₂) (hδ₂ : δ₂ ≤ ε / 2) (hε1 : 3 * ε / 2 < 1) :
    0 < ∫ v in (-1 : ℝ)..1, sweepBump v * sweepW' D (ε - δ₂ * v) := by
  have hσ : ∀ v ∈ Set.Icc (-1 : ℝ) 1, 0 < ε - δ₂ * v ∧ ε - δ₂ * v < 1 := by
    intro v hv
    constructor
    · nlinarith [hε0, hδ₂0, hδ₂, hv.1, hv.2]
    · nlinarith [hε0, hδ₂0, hδ₂, hε1, hv.1, hv.2]
  have hWc : ∀ v ∈ Set.Icc (-1 : ℝ) 1, 0 < sweepW' D (ε - δ₂ * v) := by
    intro v hv
    obtain ⟨h1, h2⟩ := hσ v hv
    have hs : 0 < sweepW D (⟨ε - δ₂ * v, ⟨h1.le, h2.le⟩⟩ : Set.Icc (0 : ℝ) 1) :=
      (sweepW_pos_lt D _ ⟨h1, h2⟩).1
    have hc : clampI (ε - δ₂ * v) = (⟨ε - δ₂ * v, ⟨h1.le, h2.le⟩⟩ : Set.Icc (0 : ℝ) 1) :=
      clampI_coe' (⟨ε - δ₂ * v, ⟨h1.le, h2.le⟩⟩ : Set.Icc (0 : ℝ) 1)
    rw [sweepW', taR, tbR, hc]
    exact hs
  refine intervalIntegral.integral_pos (by norm_num : (-1 : ℝ) < 1) ?_ ?_ ⟨0, by norm_num, ?_⟩
  · exact (sweepBump_continuous.mul
      ((arcWin_sweepW'_continuous D).comp (by fun_prop))).continuousOn
  · intro v hv
    exact mul_nonneg (sweepBump_nonneg v) (hWc v ⟨hv.1.le, hv.2⟩).le
  · have hb : 0 < sweepBump 0 := by
      rw [sweepBump]
      exact mul_pos (Real.smoothTransition.pos_of_pos (by norm_num))
        (Real.smoothTransition.pos_of_pos (by norm_num))
    have hw := hWc 0 (by norm_num)
    simpa using mul_pos hb hw

theorem needleArcZoneMono {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    ∃ ε₀ L : ℝ, 0 < ε₀ ∧ 0 < L ∧
      ∀ (lam δ₁ δ₂ ε t₁ t₂ : ℝ), 0 < lam → lam ≤ L → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ L →
        0 < δ₂ → δ₂ ≤ L → 0 < ε → ε ≤ ε₀ → δ₂ ≤ ε / 2 → t₁ < t₂ →
        t₂ - t₁ < LeanEval.KnotTheory.Quadrisecant.period / 2 →
        (∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → Work.Drive.sweepParam (t₁ - δ₁ * u) ≤ 1 / 2) →
        (∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → Work.Drive.sweepParam (t₂ - δ₁ * u) ≤ 1 / 2) →
        0 < inner ℝ
              (Work.Drive.needleFam r D lam δ₁ δ₂ ε t₂ - Work.Drive.needleFam r D lam δ₁ δ₂ ε t₁)
              (Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε) := by
  obtain ⟨m, M, C, hm, hM, hC, hmin, hmax, hlip⟩ := exists_knot_c2_bounds hr
  have hrc : Continuous r := hr.smooth.continuous
  have hper : (0 : ℝ) < period := period_pos
  obtain ⟨η, hη, hηspec⟩ := exists_window_small D (w := m ^ 2 / (8 * M * C)) (by positivity)
  refine ⟨min (η / 2) (1 / 2), period / 4, lt_min (by positivity) (by norm_num), by positivity, ?_⟩
  intro lam δ₁ δ₂ ε t₁ t₂ hlam0 hlamL hlam1 hδ₁0 hδ₁L hδ₂0 hδ₂L hε0 hεε₀ hδ₂ε ht12 ht12per
    hzone1 hzone2
  have hδ₁2 : δ₁ < period / 2 := by linarith [hδ₁L, hper]
  have hεη : ε ≤ η / 2 := le_trans hεε₀ (min_le_left _ _)
  have hεh : ε ≤ 1 / 2 := le_trans hεε₀ (min_le_right _ _)
  have hlam2 : (0 : ℝ) < 1 - 2 * lam := by linarith
  set σv : ℝ → ℝ := fun v => ε - δ₂ * v with hσv
  have hσvc : Continuous σv := by rw [hσv]; fun_prop
  have hσlo : ∀ v ∈ Set.Icc (-1 : ℝ) 1, ε / 2 ≤ σv v := by
    intro v hv
    have h1 : δ₂ * v ≤ δ₂ := by nlinarith [hδ₂0, hv.2]
    rw [hσv]; linarith [hδ₂ε]
  have hσhi : ∀ v ∈ Set.Icc (-1 : ℝ) 1, σv v ≤ 3 * ε / 2 := by
    intro v hv
    have h1 : -δ₂ ≤ δ₂ * v := by nlinarith [hδ₂0, hv.1]
    rw [hσv]; linarith
  have hσpos : ∀ v ∈ Set.Icc (-1 : ℝ) 1, 0 < σv v := fun v hv => by
    linarith [hσlo v hv, hε0]
  have hσlt1 : ∀ v ∈ Set.Icc (-1 : ℝ) 1, σv v < 1 := fun v hv => by
    have h := hσhi v hv; linarith [hεh]
  have hσleη : ∀ v ∈ Set.Icc (-1 : ℝ) 1, σv v ≤ η := fun v hv => by
    have h := hσhi v hv; linarith [hεη, hη]
  have hWpos : ∀ v ∈ Set.Icc (-1 : ℝ) 1, 0 < sweepW' D (σv v) := by
    intro v hv
    have h1 := hσpos v hv
    have h2 := hσlt1 v hv
    have hs : 0 < sweepW D (⟨σv v, ⟨h1.le, h2.le⟩⟩ : Set.Icc (0 : ℝ) 1) :=
      (sweepW_pos_lt D _ ⟨h1, h2⟩).1
    have hc : clampI (σv v) = (⟨σv v, ⟨h1.le, h2.le⟩⟩ : Set.Icc (0 : ℝ) 1) :=
      clampI_coe' (⟨σv v, ⟨h1.le, h2.le⟩⟩ : Set.Icc (0 : ℝ) 1)
    rw [sweepW', taR, tbR, hc]
    exact hs
  have hWnonneg : ∀ v ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ sweepW' D (σv v) := fun v hv => (hWpos v hv).le
  have hsmall : ∀ v ∈ Set.Icc (-1 : ℝ) 1, ∀ v' ∈ Set.Icc (-1 : ℝ) 1,
      |taR D (σv v) - taR D (σv v')| + sweepW' D (σv v) + sweepW' D (σv v')
        ≤ m ^ 2 / (2 * M * C) := by
    intro v hv v' hv'
    obtain ⟨hA, hB⟩ := hηspec (σv v) (hσpos v hv).le (hσleη v hv)
    obtain ⟨hA', hB'⟩ := hηspec (σv v') (hσpos v' hv').le (hσleη v' hv')
    have hsum : |taR D (σv v) - taR D (σv v')| ≤ 2 * (m ^ 2 / (8 * M * C)) := by
      have h := abs_sub_le (taR D (σv v)) (taR D 0) (taR D (σv v'))
      rw [abs_sub_comm (taR D 0) (taR D (σv v'))] at h
      linarith [h, hA, hA']
    have hkey : 2 * (m ^ 2 / (8 * M * C)) + m ^ 2 / (8 * M * C) + m ^ 2 / (8 * M * C)
        = m ^ 2 / (2 * M * C) := by
      field_simp
      ring
    linarith [hsum, hB, hB', hkey]
  set ξ1 : ℝ → ℝ := fun u => lam + (1 - 2 * lam) * (2 * (sweepParam t₁ - δ₁ * u / period)) with hξ1
  set ξ2 : ℝ → ℝ := fun u => lam + (1 - 2 * lam) * (2 * (sweepParam t₂ - δ₁ * u / period)) with hξ2
  have hξ1c : Continuous ξ1 := by rw [hξ1]; fun_prop
  have hξ2c : Continuous ξ2 := by rw [hξ2]; fun_prop
  have harc1 : ∀ u ∈ Set.Icc (-1 : ℝ) 1, arcFrac lam δ₁ t₁ u = ξ1 u := by
    intro u hu
    rw [arcFrac_eq_affine hδ₁0 hδ₁2 hu hzone1, hξ1]
  have harc2 : ∀ u ∈ Set.Icc (-1 : ℝ) 1, arcFrac lam δ₁ t₂ u = ξ2 u := by
    intro u hu
    rw [arcFrac_eq_affine hδ₁0 hδ₁2 hu hzone2, hξ2]
  have hgap : sweepParam t₂ - sweepParam t₁ = (t₂ - t₁) / period := by
    have h0 : sweepParam t₁ ≤ 1 / 2 := by simpa using hzone1 0 (by norm_num)
    have h2' : sweepParam t₂ ≤ 1 / 2 := by simpa using hzone2 0 (by norm_num)
    have hxy : |t₂ - t₁| < period / 2 := by
      rw [abs_of_pos (by linarith : (0 : ℝ) < t₂ - t₁)]; exact ht12per
    exact sweepParam_sub_eq_of_le_half h2' h0 hxy
  have hξdiff : ∀ u : ℝ, ξ2 u - ξ1 u = (1 - 2 * lam) * (2 * ((t₂ - t₁) / period)) := by
    intro u
    rw [hξ1, hξ2]
    calc (lam + (1 - 2 * lam) * (2 * (sweepParam t₂ - δ₁ * u / period)))
          - (lam + (1 - 2 * lam) * (2 * (sweepParam t₁ - δ₁ * u / period)))
        = (1 - 2 * lam) * (2 * (sweepParam t₂ - sweepParam t₁)) := by ring
      _ = (1 - 2 * lam) * (2 * ((t₂ - t₁) / period)) := by rw [hgap]
  have hGpos : 0 < (1 - 2 * lam) * (2 * ((t₂ - t₁) / period)) := by
    have h2 : (0 : ℝ) < (t₂ - t₁) / period := div_pos (by linarith) hper
    positivity
  have hξ1nn : ∀ u ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ ξ1 u := by
    intro u hu
    rw [← harc1 u hu, arcFrac]
    have h1 : (0 : ℝ) ≤ sweepParam (t₁ - δ₁ * u) := (sweepParam_mem _).1
    have h2 : sweepParam (t₁ - δ₁ * u) ≤ 1 / 2 := hzone1 u hu
    nlinarith [hlam0, h1, h2, hlam2]
  have hξ2le : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ξ2 u ≤ 1 := by
    intro u hu
    rw [← harc2 u hu, arcFrac]
    have h1 : (0 : ℝ) ≤ sweepParam (t₂ - δ₁ * u) := (sweepParam_mem _).1
    have h2 : sweepParam (t₂ - δ₁ * u) ≤ 1 / 2 := hzone2 u hu
    nlinarith [hlam0, h1, h2, hlam2]
  have hξ12 : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ξ1 u ≤ ξ2 u := by
    intro u hu
    have h := hξdiff u
    linarith [hGpos]
  -- the pointwise bound
  have hpt : ∀ v ∈ Set.Icc (-1 : ℝ) 1, ∀ v' ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      sweepW' D (σv v) * sweepW' D (σv v') * ((1 - 2 * lam) * (2 * ((t₂ - t₁) / period))) * (m ^ 2 / 2)
        ≤ inner ℝ (sweepArc' r D (σv v) (ξ2 u) - sweepArc' r D (σv v) (ξ1 u))
            (sweepArc' r D (σv v') 1 - sweepArc' r D (σv v') 0) := by
    intro v hv v' hv' u hu
    have h := arcInner_lower hr D hm hM hC hmin hmax hlip (hWnonneg v hv) (hWnonneg v' hv')
      (hsmall v hv v' hv') (hξ1nn u hu) (hξ12 u hu) (hξ2le u hu)
    rwa [hξdiff u] at h
  -- the weighted width
  set I : ℝ := ∫ v in (-1 : ℝ)..1, sweepBump v * sweepW' D (σv v) with hI
  have hIpos : 0 < I := by
    rw [hI]
    exact integral_sweepBump_mul_sweepW_pos D hε0 hδ₂0.le hδ₂ε (by linarith)
  -- Step A: the difference and the chord
  rw [needleFam_diff_eq_blur hrc D hlam1 hδ₁0 hδ₁2 hzone1 hzone2 hξ1c hξ2c harc1 harc2,
    chordEnd_sub_eq' hrc D δ₂ ε]
  set e : Space :=
    ∫ v' in (-1 : ℝ)..1, sweepBump v' • (sweepArc' r D (σv v') 1 - sweepArc' r D (σv v') 0) with he
  set Z : ℝ → Space := fun v =>
    ∫ u in (-1 : ℝ)..1, sweepBump u •
      (sweepArc' r D (σv v) (ξ2 u) - sweepArc' r D (σv v) (ξ1 u)) with hZ
  have hZc : Continuous Z := by
    rw [hZ]
    exact continuous_blur_sub_arc hrc D hσvc hξ1c hξ2c
  have hDc : Continuous (fun v' : ℝ => sweepArc' r D (σv v') 1 - sweepArc' r D (σv v') 0) :=
    (continuous_arcComp hrc D hσvc continuous_const).sub
      (continuous_arcComp hrc D hσvc continuous_const)
  have hDint : IntervalIntegrable
      (fun v' : ℝ => sweepBump v' • (sweepArc' r D (σv v') 1 - sweepArc' r D (σv v') 0))
      volume (-1 : ℝ) 1 :=
    (sweepBump_continuous.smul hDc).intervalIntegrable _ _
  -- Step B: pull the outer inner product into the `v`-integral
  rw [inner_intervalIntegral_comm_left (f := fun v : ℝ => sweepBump v • Z v)
    ((sweepBump_continuous.smul hZc).intervalIntegrable _ _) e]
  rw [show (∫ v in (-1 : ℝ)..1, inner ℝ (sweepBump v • Z v) e)
      = ∫ v in (-1 : ℝ)..1, sweepBump v * inner ℝ (Z v) e from
    intervalIntegral.integral_congr (fun v _ => by rw [real_inner_smul_left])]
  -- the evaluation of the comparison integral over the chord side
  have heval : ∀ v : ℝ, (∫ v' in (-1 : ℝ)..1,
        sweepBump v' * (sweepW' D (σv v) * sweepW' D (σv v') *
          ((1 - 2 * lam) * (2 * ((t₂ - t₁) / period))) * (m ^ 2 / 2)))
      = sweepW' D (σv v) * ((1 - 2 * lam) * (2 * ((t₂ - t₁) / period))) * (m ^ 2 / 2) * I := by
    intro v
    rw [show (fun v' : ℝ => sweepBump v' * (sweepW' D (σv v) * sweepW' D (σv v') *
          ((1 - 2 * lam) * (2 * ((t₂ - t₁) / period))) * (m ^ 2 / 2)))
        = (fun v' : ℝ => (sweepW' D (σv v) * ((1 - 2 * lam) * (2 * ((t₂ - t₁) / period))) *
            (m ^ 2 / 2)) * (sweepBump v' * sweepW' D (σv v'))) from by funext v'; ring]
    rw [intervalIntegral.integral_const_mul, hI]
  -- the pointwise bound against the chord
  have hu_lb : ∀ v ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      sweepW' D (σv v) * ((1 - 2 * lam) * (2 * ((t₂ - t₁) / period))) * (m ^ 2 / 2) * I
        ≤ inner ℝ (sweepArc' r D (σv v) (ξ2 u) - sweepArc' r D (σv v) (ξ1 u)) e := by
    intro v hv u hu
    have hWc' : Continuous (fun v' : ℝ => sweepW' D (σv v')) :=
      (arcWin_sweepW'_continuous D).comp hσvc
    rw [he, inner_intervalIntegral_comm
      (f := fun v' : ℝ => sweepBump v' • (sweepArc' r D (σv v') 1 - sweepArc' r D (σv v') 0))
      hDint _]
    rw [show (∫ v' in (-1 : ℝ)..1, inner ℝ
          (sweepArc' r D (σv v) (ξ2 u) - sweepArc' r D (σv v) (ξ1 u))
          (sweepBump v' • (sweepArc' r D (σv v') 1 - sweepArc' r D (σv v') 0)))
        = ∫ v' in (-1 : ℝ)..1, sweepBump v' * inner ℝ
          (sweepArc' r D (σv v) (ξ2 u) - sweepArc' r D (σv v) (ξ1 u))
          (sweepArc' r D (σv v') 1 - sweepArc' r D (σv v') 0) from
      intervalIntegral.integral_congr (fun v' _ => by rw [real_inner_smul_right])]
    have hfc : Continuous (fun v' : ℝ => sweepBump v' * (sweepW' D (σv v) * sweepW' D (σv v') *
        ((1 - 2 * lam) * (2 * ((t₂ - t₁) / period))) * (m ^ 2 / 2))) :=
      sweepBump_continuous.mul (((continuous_const.mul hWc').mul continuous_const).mul continuous_const)
    have hgc : Continuous (fun v' : ℝ => sweepBump v' * inner ℝ
        (sweepArc' r D (σv v) (ξ2 u) - sweepArc' r D (σv v) (ξ1 u))
        (sweepArc' r D (σv v') 1 - sweepArc' r D (σv v') 0)) :=
      sweepBump_continuous.mul (Continuous.inner continuous_const hDc)
    have hmono := intervalIntegral.integral_mono_on (a := (-1 : ℝ)) (b := 1) (μ := volume)
      (f := fun v' : ℝ => sweepBump v' * (sweepW' D (σv v) * sweepW' D (σv v') *
          ((1 - 2 * lam) * (2 * ((t₂ - t₁) / period))) * (m ^ 2 / 2)))
      (g := fun v' : ℝ => sweepBump v' * inner ℝ
          (sweepArc' r D (σv v) (ξ2 u) - sweepArc' r D (σv v) (ξ1 u))
          (sweepArc' r D (σv v') 1 - sweepArc' r D (σv v') 0))
      (by norm_num : (-1 : ℝ) ≤ 1)
      (hfc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)
      (fun v' hv' => mul_le_mul_of_nonneg_left (hpt v hv v' hv' u hu) (sweepBump_nonneg v'))
    rw [heval v] at hmono
    exact hmono
  -- the outer pointwise bound against the needle difference
  have hlow : ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      sweepW' D (σv v) * ((1 - 2 * lam) * (2 * ((t₂ - t₁) / period))) * (m ^ 2 / 2) * I
        ≤ inner ℝ (Z v) e := by
    intro v hv
    have hZu : IntervalIntegrable (fun u : ℝ => sweepBump u •
        (sweepArc' r D (σv v) (ξ2 u) - sweepArc' r D (σv v) (ξ1 u))) volume (-1 : ℝ) 1 :=
      (sweepBump_continuous.smul
        ((continuous_arcComp hrc D (continuous_const : Continuous fun _ : ℝ => σv v) hξ2c).sub
          (continuous_arcComp hrc D (continuous_const : Continuous fun _ : ℝ => σv v) hξ1c))
        ).intervalIntegrable _ _
    rw [hZ, inner_intervalIntegral_comm_left
      (f := fun u : ℝ => sweepBump u •
        (sweepArc' r D (σv v) (ξ2 u) - sweepArc' r D (σv v) (ξ1 u))) hZu e]
    rw [show (∫ u in (-1 : ℝ)..1, inner ℝ (sweepBump u •
          (sweepArc' r D (σv v) (ξ2 u) - sweepArc' r D (σv v) (ξ1 u))) e)
        = ∫ u in (-1 : ℝ)..1, sweepBump u * inner ℝ
          (sweepArc' r D (σv v) (ξ2 u) - sweepArc' r D (σv v) (ξ1 u)) e from
      intervalIntegral.integral_congr (fun u _ => by rw [real_inner_smul_left])]
    have hΔc : Continuous (fun u : ℝ => inner ℝ
        (sweepArc' r D (σv v) (ξ2 u) - sweepArc' r D (σv v) (ξ1 u)) e) :=
      Continuous.inner
        ((continuous_arcComp hrc D (continuous_const : Continuous fun _ : ℝ => σv v) hξ2c).sub
          (continuous_arcComp hrc D (continuous_const : Continuous fun _ : ℝ => σv v) hξ1c))
        continuous_const
    have hfc2 : Continuous (fun u : ℝ => sweepBump u *
        (sweepW' D (σv v) * ((1 - 2 * lam) * (2 * ((t₂ - t₁) / period))) * (m ^ 2 / 2) * I)) :=
      sweepBump_continuous.mul continuous_const
    have hmono := intervalIntegral.integral_mono_on (a := (-1 : ℝ)) (b := 1) (μ := volume)
      (f := fun u : ℝ => sweepBump u *
        (sweepW' D (σv v) * ((1 - 2 * lam) * (2 * ((t₂ - t₁) / period))) * (m ^ 2 / 2) * I))
      (g := fun u : ℝ => sweepBump u * inner ℝ
        (sweepArc' r D (σv v) (ξ2 u) - sweepArc' r D (σv v) (ξ1 u)) e)
      (by norm_num : (-1 : ℝ) ≤ 1)
      (hfc2.intervalIntegrable _ _)
      ((sweepBump_continuous.mul hΔc).intervalIntegrable _ _)
      (fun u hu => mul_le_mul_of_nonneg_left (hu_lb v hv u hu) (sweepBump_nonneg u))
    rw [show (∫ u in (-1 : ℝ)..1, sweepBump u *
          (sweepW' D (σv v) * ((1 - 2 * lam) * (2 * ((t₂ - t₁) / period))) * (m ^ 2 / 2) * I))
        = sweepW' D (σv v) * ((1 - 2 * lam) * (2 * ((t₂ - t₁) / period))) * (m ^ 2 / 2) * I from by
      rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]] at hmono
    exact hmono
  have hWc : Continuous (fun v : ℝ => sweepW' D (σv v)) :=
    (arcWin_sweepW'_continuous D).comp hσvc
  have hfc3 : Continuous (fun v : ℝ => sweepBump v *
      (sweepW' D (σv v) * ((1 - 2 * lam) * (2 * ((t₂ - t₁) / period))) * (m ^ 2 / 2) * I)) :=
    sweepBump_continuous.mul (((hWc.mul continuous_const).mul continuous_const).mul continuous_const)
  have hgc3 : Continuous (fun v : ℝ => sweepBump v * inner ℝ (Z v) e) :=
    sweepBump_continuous.mul (Continuous.inner hZc continuous_const)
  have hfinal := intervalIntegral.integral_mono_on (a := (-1 : ℝ)) (b := 1) (μ := volume)
    (f := fun v : ℝ => sweepBump v *
      (sweepW' D (σv v) * ((1 - 2 * lam) * (2 * ((t₂ - t₁) / period))) * (m ^ 2 / 2) * I))
    (g := fun v : ℝ => sweepBump v * inner ℝ (Z v) e)
    (by norm_num : (-1 : ℝ) ≤ 1)
    (hfc3.intervalIntegrable _ _) (hgc3.intervalIntegrable _ _)
    (fun v hv => mul_le_mul_of_nonneg_left (hlow v hv) (sweepBump_nonneg v))
  have heval2 : (∫ v in (-1 : ℝ)..1, sweepBump v *
        (sweepW' D (σv v) * ((1 - 2 * lam) * (2 * ((t₂ - t₁) / period))) * (m ^ 2 / 2) * I))
      = ((1 - 2 * lam) * (2 * ((t₂ - t₁) / period))) * (m ^ 2 / 2) * I * I := by
    rw [show (fun v : ℝ => sweepBump v *
          (sweepW' D (σv v) * ((1 - 2 * lam) * (2 * ((t₂ - t₁) / period))) * (m ^ 2 / 2) * I))
        = (fun v : ℝ => (((1 - 2 * lam) * (2 * ((t₂ - t₁) / period))) * (m ^ 2 / 2) * I) * (sweepBump v * sweepW' D (σv v))) from by
      funext v; ring]
    rw [intervalIntegral.integral_const_mul, hI]
  rw [heval2] at hfinal
  have hpos : 0 < ((1 - 2 * lam) * (2 * ((t₂ - t₁) / period))) * (m ^ 2 / 2) * I * I := by
    have : (0 : ℝ) < m ^ 2 / 2 := by positivity
    positivity
  linarith [hfinal, hpos]

end Work.Drive
