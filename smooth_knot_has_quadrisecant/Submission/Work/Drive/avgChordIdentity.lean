import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.velNzDefs
import Submission.Work.Drive.sweepLoopChamfer_locallyIntegrable
import Submission.Work.Drive.sweepFam_contDiff_periodic

/-!
# The averaged-chord identity for the doubly smoothed sweep family

This module proves `Work.Drive.avgChordIdentity`: the pairing of the increment of the doubly
smoothed sweep slice `Φ_σ = sweepFam r D lam δ₁ δ₂ σ` with a direction `n` is exactly the
`(v,u)`-average `avgChord` of the `n`-components of the forward chords of the raw chamfered loop
`Γ = sweepLoopChamfer`, together with the passage from a positive lower bound on `avgChord` to
non-vanishing of the velocity of the slice.

The point of this module (relative to `velNz_inner_sweepFam_sub_eq` in `sweepFamVelNz.lean`) is
that **no hypothesis on `lam` is needed**: the only input is the joint *measurability* and
*boundedness* of the raw loop in the pair `(s,t)`, which hold for every real `lam`.  That is what
makes the identity available as `hAn` in the window assembly.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology intervalIntegral
open MeasureTheory

set_option maxHeartbeats 4000000

variable {r : ℝ → Space} {d : BandArcData} {D : SweepData d}

/-! ## The bump is bounded by one -/

lemma sweepBump_nonneg_local (u : ℝ) : 0 ≤ sweepBump u :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma sweepBump_le_one_local (u : ℝ) : sweepBump u ≤ 1 := by
  rw [sweepBump]
  exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

lemma abs_sweepBump_le_one_local (u : ℝ) : |sweepBump u| ≤ 1 := by
  rw [abs_of_nonneg (sweepBump_nonneg_local u)]
  exact sweepBump_le_one_local u

/-! ## A global bound for the raw chamfered loop -/

/-- The raw chamfered loop is globally bounded, for every real `lam`.  (Same computation as in
`Work.Drive.sweepLoopChamfer_locallyIntegrable`, with the constants exposed.) -/
lemma exists_sweepLoopChamfer_bound (hr : Continuous r) (D : SweepData d) (lam : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : ℝ, ‖sweepLoopChamfer r D lam s t‖ ≤ C := by
  obtain ⟨A₀, hA₀⟩ :=
    (isCompact_univ (X := Set.Icc (0:ℝ) 1)).exists_bound_of_continuousOn D.cont_ta.continuousOn
  obtain ⟨B₀, hB₀⟩ :=
    (isCompact_univ (X := Set.Icc (0:ℝ) 1)).exists_bound_of_continuousOn D.cont_tb.continuousOn
  set A : ℝ := max A₀ B₀ with hAdef
  have hA : ∀ x : ℝ, |taR D x| ≤ A ∧ |tbR D x| ≤ A := by
    intro x
    constructor
    · refine le_trans ?_ (le_max_left A₀ B₀)
      simpa [taR, Real.norm_eq_abs] using hA₀ (clampI x) (Set.mem_univ _)
    · refine le_trans ?_ (le_max_right A₀ B₀)
      simpa [tbR, Real.norm_eq_abs] using hB₀ (clampI x) (Set.mem_univ _)
  obtain ⟨K, hK0, hKlam, hK1m⟩ : ∃ K : ℝ, 0 ≤ K ∧ |lam| ≤ K ∧ |1 - lam| ≤ K :=
    ⟨|lam| + |1 - lam|, by positivity, by linarith [abs_nonneg (1 - lam)],
      by linarith [abs_nonneg lam]⟩
  set R₀ : ℝ := A * (1 + 2 * K) with hR₀def
  obtain ⟨R₁, hR₁⟩ :=
    (isCompact_Icc (a := -|R₀|) (b := |R₀|)).exists_bound_of_continuousOn hr.continuousOn
  set R : ℝ := max R₁ 0 with hRdef
  have hR : ∀ x : ℝ, |x| ≤ A * (1 + 2 * K) → ‖r x‖ ≤ R := by
    intro x hx
    have hx2 : |x| ≤ |R₀| := le_trans hx (le_abs_self R₀)
    have hmem : x ∈ Set.Icc (-|R₀|) |R₀| := by rw [Set.mem_Icc]; exact abs_le.mp hx2
    exact le_trans (hR₁ x hmem) (le_max_left R₁ 0)
  have hR0 : 0 ≤ R := le_max_right R₁ 0
  refine ⟨(2 * K + 1) * R, by nlinarith [hK0, hR0], ?_⟩
  intro s t
  exact sweepLoopChamfer_norm_bound D lam A K R hA hK0 hR hKlam hK1m s t

/-! ## Interval integrability from measurability and a bound -/

lemma intervalIntegrable_of_bound {g : ℝ → Space} {C : ℝ} (hm : Measurable g)
    (hb : ∀ u : ℝ, ‖g u‖ ≤ C) : IntervalIntegrable g volume (-1) 1 := by
  have hfin : volume (Set.Ioc (-1:ℝ) 1) < ⊤ := by rw [Real.volume_Ioc]; simp
  have hfin' : volume (Set.Ioc (1:ℝ) (-1)) < ⊤ := by rw [Real.volume_Ioc]; simp
  exact ⟨IntegrableOn.of_bound hfin hm.aestronglyMeasurable C (Filter.Eventually.of_forall hb),
    IntegrableOn.of_bound hfin' hm.aestronglyMeasurable C (Filter.Eventually.of_forall hb)⟩

/-! ## Passing `inner` through a bump-weighted interval integral -/

lemma inner_bump_integral {F : ℝ → Space}
    (hF : IntervalIntegrable (fun u : ℝ => sweepBump u • F u) volume (-1) 1) (n : Space) :
    inner ℝ n (∫ u in (-1:ℝ)..1, sweepBump u • F u)
      = ∫ u in (-1:ℝ)..1, sweepBump u * inner ℝ n (F u) := by
  have hint : Integrable (fun u : ℝ => sweepBump u • F u)
      (volume.restrict (Set.Ioc (-1:ℝ) 1)) := hF.1
  rw [intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  rw [← integral_inner (f := fun u : ℝ => sweepBump u • F u) hint]
  exact integral_congr_ae (Filter.Eventually.of_forall
    (fun u => inner_smul_right n (F u) (sweepBump u)))

lemma bump_integral_sub {F₁ F₂ : ℝ → Space}
    (h₁ : IntervalIntegrable (fun u : ℝ => sweepBump u • F₁ u) volume (-1) 1)
    (h₂ : IntervalIntegrable (fun u : ℝ => sweepBump u • F₂ u) volume (-1) 1) :
    (∫ u in (-1:ℝ)..1, sweepBump u • F₁ u) - (∫ u in (-1:ℝ)..1, sweepBump u • F₂ u)
      = ∫ u in (-1:ℝ)..1, sweepBump u • (F₁ u - F₂ u) := by
  refine (intervalIntegral.integral_sub h₁ h₂).symm.trans ?_
  exact intervalIntegral.integral_congr (fun u _ => (smul_sub (sweepBump u) (F₁ u) (F₂ u)).symm)

/-! ## The single smoothing: bounds and measurability -/

lemma norm_sweepSmoothT_le {lam δ₁ C : ℝ}
    (hΓb : ∀ s t : ℝ, ‖sweepLoopChamfer r D lam s t‖ ≤ C) (s t : ℝ) :
    ‖sweepSmoothT r D lam δ₁ s t‖ ≤ C * 2 := by
  have h : ‖∫ u in (-1:ℝ)..1, sweepBump u • sweepLoopChamfer r D lam s (t - δ₁ * u)‖
      ≤ C * |(1:ℝ) - (-1)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun u _ => by
      rw [norm_smul, Real.norm_eq_abs]
      calc |sweepBump u| * ‖sweepLoopChamfer r D lam s (t - δ₁ * u)‖
          ≤ 1 * C := mul_le_mul (abs_sweepBump_le_one_local u) (hΓb s _) (norm_nonneg _)
              zero_le_one
        _ = C := one_mul C)
  have h3 : C * |(1:ℝ) - (-1)| = C * 2 := by
    rw [show |(1:ℝ) - (-1)| = 2 by norm_num]
  simpa [sweepSmoothT] using h.trans (le_of_eq h3)

lemma measurable_sweepSmoothT_fst {lam δ₁ : ℝ}
    (hΓ : Measurable (fun p : ℝ × ℝ => sweepLoopChamfer r D lam p.1 p.2))
    (c e t : ℝ) : Measurable (fun v : ℝ => sweepSmoothT r D lam δ₁ (c - e * v) t) := by
  have hφ : Measurable (fun p : ℝ × ℝ => sweepBump p.2) :=
    (continuous_sweepBump.comp continuous_snd).measurable
  have hG : Measurable
      (fun p : ℝ × ℝ => sweepLoopChamfer r D lam (c - e * p.1) (t - δ₁ * p.2)) :=
    hΓ.comp (((by fun_prop : Measurable fun p : ℝ × ℝ => c - e * p.1)).prodMk
      (by fun_prop : Measurable fun p : ℝ × ℝ => t - δ₁ * p.2))
  have hraw : StronglyMeasurable
      (fun p : ℝ × ℝ => sweepBump p.2 • sweepLoopChamfer r D lam (c - e * p.1) (t - δ₁ * p.2)) :=
    (hφ.smul hG).stronglyMeasurable
  have h := hraw.integral_prod_right' (ν := volume)
  have heq : (fun v : ℝ => ∫ u : ℝ, sweepBump u •
        sweepLoopChamfer r D lam (c - e * v) (t - δ₁ * u) ∂volume)
      = fun v : ℝ => sweepSmoothT r D lam δ₁ (c - e * v) t := by
    funext v
    rw [show sweepSmoothT r D lam δ₁ (c - e * v) t
        = ∫ u in (-1:ℝ)..1, sweepBump u • sweepLoopChamfer r D lam (c - e * v) (t - δ₁ * u)
        from rfl]
    have hkey := integral_eq_integral_interval_of_support (δ := (1:ℝ))
      (fun u : ℝ => sweepBump u • sweepLoopChamfer r D lam (c - e * v) (t - δ₁ * u)) 0 ?_
    · simpa using hkey
    · intro y hy
      have hlt : ∀ h : |y| ≤ 1, False := by
        intro h
        apply hy
        rw [Set.mem_Icc]
        simpa [abs_one] using abs_le.mp h
      rw [sweepBump_eq_zero_of_one_le_abs (le_of_lt (lt_of_not_ge hlt)), zero_smul]
  rw [← heq]
  exact h.measurable

/-! ## The two inner-identity lemmas -/

lemma inner_sweepSmoothT_sub {lam δ₁ C : ℝ}
    (hΓ : Measurable (fun p : ℝ × ℝ => sweepLoopChamfer r D lam p.1 p.2))
    (hΓb : ∀ s t : ℝ, ‖sweepLoopChamfer r D lam s t‖ ≤ C)
    (s t₁ t₂ : ℝ) (n : Space) :
    inner ℝ n (sweepSmoothT r D lam δ₁ s t₂ - sweepSmoothT r D lam δ₁ s t₁)
      = ∫ u in (-1 : ℝ)..1, sweepBump u *
          inner ℝ n (sweepLoopChamfer r D lam s (t₂ - δ₁ * u)
            - sweepLoopChamfer r D lam s (t₁ - δ₁ * u)) := by
  have hmΓ : ∀ t : ℝ, Measurable (fun u : ℝ => sweepLoopChamfer r D lam s (t - δ₁ * u)) := by
    intro t
    exact hΓ.comp (measurable_const.prodMk (by fun_prop : Measurable fun u : ℝ => t - δ₁ * u))
  have hm : ∀ t : ℝ, Measurable
      (fun u : ℝ => sweepBump u • sweepLoopChamfer r D lam s (t - δ₁ * u)) :=
    fun t => continuous_sweepBump.measurable.smul (hmΓ t)
  have hbnd : ∀ (t : ℝ) (u : ℝ),
      ‖sweepBump u • sweepLoopChamfer r D lam s (t - δ₁ * u)‖ ≤ C := by
    intro t u
    rw [norm_smul, Real.norm_eq_abs]
    calc |sweepBump u| * ‖sweepLoopChamfer r D lam s (t - δ₁ * u)‖
        ≤ 1 * C := mul_le_mul (abs_sweepBump_le_one_local u) (hΓb s _) (norm_nonneg _) zero_le_one
      _ = C := one_mul C
  have hsub := bump_integral_sub (intervalIntegrable_of_bound (hm t₂) (hbnd t₂))
    (intervalIntegrable_of_bound (hm t₁) (hbnd t₁))
  have hmain : sweepSmoothT r D lam δ₁ s t₂ - sweepSmoothT r D lam δ₁ s t₁
      = ∫ u in (-1:ℝ)..1, sweepBump u • (sweepLoopChamfer r D lam s (t₂ - δ₁ * u)
          - sweepLoopChamfer r D lam s (t₁ - δ₁ * u)) := by
    simpa only [sweepSmoothT] using hsub
  rw [hmain]
  refine inner_bump_integral ?_ n
  refine intervalIntegrable_of_bound (C := C + C) ?_ ?_
  · exact continuous_sweepBump.measurable.smul ((hmΓ t₂).sub (hmΓ t₁))
  · intro u
    rw [norm_smul, Real.norm_eq_abs]
    have h2 : ‖sweepLoopChamfer r D lam s (t₂ - δ₁ * u)
        - sweepLoopChamfer r D lam s (t₁ - δ₁ * u)‖ ≤ C + C :=
      (norm_sub_le _ _).trans (add_le_add (hΓb s _) (hΓb s _))
    calc |sweepBump u| * ‖sweepLoopChamfer r D lam s (t₂ - δ₁ * u)
          - sweepLoopChamfer r D lam s (t₁ - δ₁ * u)‖
        ≤ 1 * (C + C) := mul_le_mul (abs_sweepBump_le_one_local u) h2 (norm_nonneg _) zero_le_one
      _ = C + C := one_mul _

lemma inner_sweepFam_sub {lam δ₁ δ₂ C : ℝ}
    (hΓ : Measurable (fun p : ℝ × ℝ => sweepLoopChamfer r D lam p.1 p.2))
    (hΓb : ∀ s t : ℝ, ‖sweepLoopChamfer r D lam s t‖ ≤ C)
    (σ t₁ t₂ : ℝ) (n : Space) :
    inner ℝ n (sweepFam r D lam δ₁ δ₂ σ t₂ - sweepFam r D lam δ₁ δ₂ σ t₁)
      = ∫ v in (-1 : ℝ)..1, sweepBump v *
          inner ℝ n (sweepSmoothT r D lam δ₁ (σ - δ₂ * v) t₂
            - sweepSmoothT r D lam δ₁ (σ - δ₂ * v) t₁) := by
  have hψ : ∀ t : ℝ, Measurable (fun v : ℝ => sweepSmoothT r D lam δ₁ (σ - δ₂ * v) t) :=
    fun t => measurable_sweepSmoothT_fst hΓ σ δ₂ t
  have hm : ∀ t : ℝ, Measurable
      (fun v : ℝ => sweepBump v • sweepSmoothT r D lam δ₁ (σ - δ₂ * v) t) :=
    fun t => continuous_sweepBump.measurable.smul (hψ t)
  have hbnd : ∀ (t : ℝ) (v : ℝ),
      ‖sweepBump v • sweepSmoothT r D lam δ₁ (σ - δ₂ * v) t‖ ≤ C * 2 := by
    intro t v
    rw [norm_smul, Real.norm_eq_abs]
    calc |sweepBump v| * ‖sweepSmoothT r D lam δ₁ (σ - δ₂ * v) t‖
        ≤ 1 * (C * 2) := mul_le_mul (abs_sweepBump_le_one_local v)
            (norm_sweepSmoothT_le hΓb (σ - δ₂ * v) t) (norm_nonneg _) zero_le_one
      _ = C * 2 := one_mul _
  have hsub := bump_integral_sub (intervalIntegrable_of_bound (hm t₂) (hbnd t₂))
    (intervalIntegrable_of_bound (hm t₁) (hbnd t₁))
  have hmain : sweepFam r D lam δ₁ δ₂ σ t₂ - sweepFam r D lam δ₁ δ₂ σ t₁
      = ∫ v in (-1:ℝ)..1, sweepBump v • (sweepSmoothT r D lam δ₁ (σ - δ₂ * v) t₂
          - sweepSmoothT r D lam δ₁ (σ - δ₂ * v) t₁) := by
    simpa only [sweepFam] using hsub
  rw [hmain]
  refine inner_bump_integral ?_ n
  refine intervalIntegrable_of_bound (C := C * 2 + C * 2) ?_ ?_
  · exact continuous_sweepBump.measurable.smul ((hψ t₂).sub (hψ t₁))
  · intro v
    rw [norm_smul, Real.norm_eq_abs]
    have h2 : ‖sweepSmoothT r D lam δ₁ (σ - δ₂ * v) t₂
        - sweepSmoothT r D lam δ₁ (σ - δ₂ * v) t₁‖ ≤ C * 2 + C * 2 :=
      (norm_sub_le _ _).trans (add_le_add (norm_sweepSmoothT_le hΓb _ _)
        (norm_sweepSmoothT_le hΓb _ _))
    calc |sweepBump v| * ‖sweepSmoothT r D lam δ₁ (σ - δ₂ * v) t₂
          - sweepSmoothT r D lam δ₁ (σ - δ₂ * v) t₁‖
        ≤ 1 * (C * 2 + C * 2) := mul_le_mul (abs_sweepBump_le_one_local v) h2 (norm_nonneg _)
            zero_le_one
      _ = C * 2 + C * 2 := one_mul _

/-! ## The identity, without any hypothesis on `lam` -/

theorem sweepFam_inner_sub_eq_avgChord (hr : Continuous r) (D : SweepData d) (lam δ₁ δ₂ σ : ℝ) :
    ∀ (t g : ℝ) (n : Space),
      inner ℝ n (sweepFam r D lam δ₁ δ₂ σ (t + g) - sweepFam r D lam δ₁ δ₂ σ t)
        = avgChord r D lam δ₁ δ₂ σ n t g := by
  obtain ⟨C, hC0, hΓb⟩ := exists_sweepLoopChamfer_bound hr D lam
  have hΓ : Measurable (fun p : ℝ × ℝ => sweepLoopChamfer r D lam p.1 p.2) :=
    sweepLoopChamfer_measurable D hr lam
  intro t g n
  have hβ := inner_sweepFam_sub (lam := lam) (δ₁ := δ₁) (δ₂ := δ₂) (C := C) hΓ hΓb σ t (t + g) n
  refine hβ.trans ?_
  refine intervalIntegral.integral_congr (fun v _ => ?_)
  rw [inner_sweepSmoothT_sub (lam := lam) (δ₁ := δ₁) (C := C) hΓ hΓb (σ - δ₂ * v) t (t + g) n]

/-! ## The target -/

theorem avgChordIdentity {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    (hr : Continuous r) :
    (∀ (lam δ₁ δ₂ σ t g : ℝ) (n : LeanEval.KnotTheory.Quadrisecant.Space), δ₁ ≠ 0 → δ₂ ≠ 0 →
        inner ℝ n (Work.Drive.sweepFam r D lam δ₁ δ₂ σ (t + g)
            - Work.Drive.sweepFam r D lam δ₁ δ₂ σ t)
          = Work.Drive.avgChord r D lam δ₁ δ₂ σ n t g) ∧
      (∀ (lam δ₁ δ₂ σ t : ℝ) (n : LeanEval.KnotTheory.Quadrisecant.Space) (c h : ℝ),
        δ₁ ≠ 0 → δ₂ ≠ 0 → 0 < c → 0 < h →
        (∀ g : ℝ, 0 < g → g ≤ h →
          c * g ≤ Work.Drive.avgChord r D lam δ₁ δ₂ σ n t g) →
        LeanEval.KnotTheory.Quadrisecant.velocity
          (fun u : ℝ => Work.Drive.sweepFam r D lam δ₁ δ₂ σ u) t ≠ 0) := by
  constructor
  · intro lam δ₁ δ₂ σ t g n _ _
    exact sweepFam_inner_sub_eq_avgChord hr D lam δ₁ δ₂ σ t g n
  · intro lam δ₁ δ₂ σ t n c h hδ₁ hδ₂ hc hh hmain
    have hC := sweepFam_contDiff_periodic hr D lam δ₁ δ₂ hδ₁ hδ₂
    have hslice : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ u) := hC.2.2 σ
    have hdiff : DifferentiableAt ℝ (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ u) t :=
      hslice.differentiable (by simp) t
    have hslope : Filter.Tendsto
        (slope (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ u) t) (𝓝[>] t)
        (𝓝 (deriv (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ u) t)) :=
      hdiff.hasDerivAt.tendsto_slope.mono_left (nhdsGT_le_nhdsNE t)
    have hlim : Filter.Tendsto
        (fun y : ℝ => inner ℝ n (slope (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ u) t y))
        (𝓝[>] t) (𝓝 (inner ℝ n (deriv (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ u) t))) :=
      (tendsto_const_nhds (x := n)).inner hslope
    have hev : ∀ᶠ y in 𝓝[>] t,
        c ≤ inner ℝ n (slope (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ u) t y) := by
      refine Filter.mem_of_superset (Ioc_mem_nhdsGT (a := t + h) (by linarith : t < t + h)) ?_
      intro y hy
      show c ≤ inner ℝ n (slope (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ u) t y)
      rw [Set.mem_Ioc] at hy
      obtain ⟨hyt, hyh⟩ := hy
      have hg : 0 < y - t := by linarith
      have hg' : y - t ≤ h := by linarith
      have hy_eq : t + (y - t) = y := by ring
      have hstep := hmain (y - t) hg hg'
      have hconv : avgChord r D lam δ₁ δ₂ σ n t (y - t)
          = inner ℝ n (sweepFam r D lam δ₁ δ₂ σ (t + (y - t))
              - sweepFam r D lam δ₁ δ₂ σ t) :=
        (sweepFam_inner_sub_eq_avgChord hr D lam δ₁ δ₂ σ t (y - t) n).symm
      rw [hconv, hy_eq] at hstep
      have hsl : slope (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ u) t y
          = (y - t)⁻¹ • (sweepFam r D lam δ₁ δ₂ σ y - sweepFam r D lam δ₁ δ₂ σ t) := rfl
      rw [hsl, inner_smul_right, inv_mul_eq_div]
      exact (le_div_iff₀ hg).mpr hstep
    have hfinal : c ≤ inner ℝ n (velocity (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ u) t) :=
      ge_of_tendsto hlim hev
    intro hzero
    rw [hzero, inner_zero_right] at hfinal
    exact absurd hfinal (not_le.mpr hc)

end Work.Drive
