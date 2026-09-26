import Mathlib
import Submission.Work.Drive.cInfKnot
import Submission.Work.Drive.uniformCurveBounds

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-!
# Uniform geometric bounds for a `C¹` family of `C^∞` knots

This is the `C¹` counterpart of `Work.Drive.uniformCurveBounds`.  There the family is
`ContDiff ℝ ⊤` (i.e. *analytic*, since `⊤ = ω` in this Mathlib) and the slices are analytic
knots; here the family is only jointly `C¹` and the slices are `C^∞` knots (`IsCInfKnot`).

The whole compactness argument only ever uses

* joint *continuity* of the `t`-partial derivative `famPhi F`, which for a `C¹` family is
  `ContDiff.contDiff_fderiv_apply` with `m = 0`, and
* the `HasDerivAt` of the slice at every point, which follows from joint differentiability.

So we prove the `C¹` versions of the four helper lemmas of `uniformCurveBounds.lean`
(`hasDerivAt_slice`, `deriv_slice_eq`, `continuous_famPhi`, `hasDerivAt_sub_smul`,
`local_bound`) and then transcribe the main argument.
-/

/-- Projection: an `IsCInfKnot` is `period`-periodic. -/
theorem IsCInfKnot.periodic {r : ℝ → Space} (h : IsCInfKnot r) :
    Function.Periodic r period := h.2.1

/-- Projection: an `IsCInfKnot` is injective on one period. -/
theorem IsCInfKnot.injOn {r : ℝ → Space} (h : IsCInfKnot r) :
    Set.InjOn r (Set.Ico (0 : ℝ) period) := h.2.2.1

/-- Projection: an `IsCInfKnot` has nonvanishing velocity. -/
theorem IsCInfKnot.regular {r : ℝ → Space} (h : IsCInfKnot r) :
    ∀ t : ℝ, velocity r t ≠ 0 := h.2.2.2

/-- The `t`-derivative of a slice, expressed through `famPhi`, for a merely `C¹` family. -/
lemma hasDerivAt_slice_c1 (F : ℝ → ℝ → Space) (hF : ContDiff ℝ 1 (fam F)) (t s : ℝ) :
    HasDerivAt (fun u : ℝ => F u s) (famPhi F (t, s)) t := by
  have h1 : HasFDerivAt (fun u : ℝ => (u, s)) (ContinuousLinearMap.inl ℝ ℝ ℝ) t :=
    hasFDerivAt_prodMk_left t s
  have h2 : HasFDerivAt (fam F) (fderiv ℝ (fam F) (t, s)) (t, s) :=
    (hF.differentiable (by simp) (t, s)).hasFDerivAt
  have h3 : HasFDerivAt (fun u : ℝ => fam F (u, s))
      ((fderiv ℝ (fam F) (t, s)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) t := by
    simpa only [Function.comp_def] using h2.comp t h1
  have h4 : HasDerivAt (fun u : ℝ => fam F (u, s))
      (((fderiv ℝ (fam F) (t, s)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) 1) t := h3.hasDerivAt
  have h5 : (((fderiv ℝ (fam F) (t, s)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) 1)
      = famPhi F (t, s) := by
    simp [famPhi, ContinuousLinearMap.comp_apply]
  rw [h5] at h4
  simpa only [fam] using h4

lemma deriv_slice_eq_c1 (F : ℝ → ℝ → Space) (hF : ContDiff ℝ 1 (fam F)) (t s : ℝ) :
    deriv (fun u : ℝ => F u s) t = famPhi F (t, s) :=
  (hasDerivAt_slice_c1 F hF t s).deriv

/-- Joint continuity of the `t`-partial derivative, for a `C¹` family. -/
lemma continuous_famPhi_c1 (F : ℝ → ℝ → Space) (hF : ContDiff ℝ 1 (fam F)) :
    Continuous (famPhi F) := by
  have h1 : ContDiff ℝ 0 (fun q : (ℝ × ℝ) × (ℝ × ℝ) => (fderiv ℝ (fam F) q.1) q.2) :=
    ContDiff.contDiff_fderiv_apply hF (m := 0) (by simp)
  have h2 : ContDiff ℝ 0 (fun p : ℝ × ℝ => ((p, (1, 0)) : (ℝ × ℝ) × (ℝ × ℝ))) := by fun_prop
  exact (h1.comp h2).continuous

/-- Derivative of `u ↦ F u s - u • v`, for a `C¹` family. -/
lemma hasDerivAt_sub_smul_c1 (F : ℝ → ℝ → Space) (hF : ContDiff ℝ 1 (fam F)) (s u : ℝ)
    (v : Space) :
    HasDerivAt (fun x : ℝ => F x s - x • v) (famPhi F (u, s) - v) u := by
  have h1 : HasDerivAt (fun x : ℝ => F x s) (famPhi F (u, s)) u := hasDerivAt_slice_c1 F hF u s
  have h2 : HasDerivAt (fun x : ℝ => x • v) v u := by
    simpa using (hasDerivAt_id u).smul_const v
  have h := h1.sub h2
  have hfun : (fun x : ℝ => F x s - x • v) = ((fun x : ℝ => F x s) - fun x : ℝ => x • v) := by
    ext x; rfl
  rw [hfun]
  exact h

/-- The local "chord versus parameter" bound, for a `C¹` family. -/
lemma local_bound_c1 (F : ℝ → ℝ → Space) (hF : ContDiff ℝ 1 (fam F))
    {m η δ : ℝ} (hη : 0 < η) (hδ4 : δ ≤ period/4) (hδη : δ ≤ η/2)
    (huc : ∀ x ∈ Wbox, ∀ y ∈ Wbox, dist x y < η → ‖famPhi F x - famPhi F y‖ < m/2)
    (hmle : ∀ p ∈ Kbox, m ≤ ‖famPhi F p‖)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1)
    {a b : ℝ} (ha : a ∈ Set.Ico (0:ℝ) period) (hab : |b - a| ≤ δ) :
    (m/2) * |b - a| ≤ ‖F a s - F b s‖ := by
  have hper : 0 < period := by unfold period; positivity
  set v : Space := famPhi F (a, s) with hv
  set I : Set ℝ := Set.Icc (a - |b - a|) (a + |b - a|) with hI
  set g : ℝ → Space := fun u => F u s - u • v with hg
  have hderivg : ∀ u, deriv g u = famPhi F (u, s) - v := by
    intro u
    rw [hg]
    exact (hasDerivAt_sub_smul_c1 F hF s u v).deriv
  have hdiff : ∀ u ∈ I, DifferentiableAt ℝ g u := by
    intro u _
    rw [hg]
    exact (hasDerivAt_sub_smul_c1 F hF s u v).differentiableAt
  have hua : ∀ u ∈ I, |u - a| ≤ |b - a| := by
    intro u hu
    rw [hI, Set.mem_Icc] at hu
    rw [abs_le]
    constructor <;> linarith [hu.1, hu.2]
  have haI : a ∈ I := by
    rw [hI, Set.mem_Icc]
    exact ⟨by linarith [abs_nonneg (b - a)], by linarith [abs_nonneg (b - a)]⟩
  have hbI : b ∈ I := by
    rw [hI, Set.mem_Icc]
    have h := abs_le.mp (le_rfl : |b - a| ≤ |b - a|)
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hbdd : ∀ u ∈ I, ‖deriv g u‖ ≤ m / 2 := by
    intro u hu
    rw [hderivg u]
    have hua_ : |u - a| ≤ |b - a| := hua u hu
    have huI := hu
    rw [hI, Set.mem_Icc] at huI
    have hmem : (u, s) ∈ Wbox := by
      rw [Wbox, Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
      exact ⟨⟨by linarith [huI.1, hab, hδ4, hper, ha.1],
              by linarith [huI.2, hab, hδ4, hper, ha.2]⟩, hs⟩
    have hlt : dist ((u, s) : ℝ × ℝ) (a, s) < η := by
      have hd : dist ((u, s) : ℝ × ℝ) (a, s) = |u - a| := by
        rw [Prod.dist_eq, Real.dist_eq]; simp
      rw [hd]
      have h3 : |u - a| ≤ δ := le_trans hua_ hab
      linarith [h3, hδη]
    have hres := huc (u, s) hmem (a, s)
      ⟨⟨by linarith [hper, ha.1], by linarith [hper, ha.2]⟩, hs⟩ hlt
    rw [← hv] at hres
    exact hres.le
  have hconv : Convex ℝ I := by rw [hI]; exact convex_Icc _ _
  have hmvt : ‖g b - g a‖ ≤ (m/2) * ‖b - a‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := g) (s := I)
      (x := a) (y := b) (C := m/2) hdiff hbdd hconv haI hbI
  rw [Real.norm_eq_abs] at hmvt
  have hvnorm : m ≤ ‖v‖ := hmle (a, s)
    ⟨⟨by linarith [hper, ha.1], by linarith [hper, ha.2]⟩, hs⟩
  have hkey : F b s - F a s = (g b - g a) + (b - a) • v := by
    rw [hg]; module
  have hstep1 : ‖(b - a) • v‖ - ‖g b - g a‖ ≤ ‖(g b - g a) + (b - a) • v‖ := by
    have h := norm_sub_le ((g b - g a) + (b - a) • v) (g b - g a)
    rw [add_sub_cancel_left] at h
    linarith
  have hfinal : (m/2) * |b - a| ≤ ‖(g b - g a) + (b - a) • v‖ := by
    have h1 : |b - a| * m ≤ |b - a| * ‖v‖ := mul_le_mul_of_nonneg_left hvnorm (abs_nonneg _)
    have h2 : ‖g b - g a‖ ≤ (m/2) * |b - a| := hmvt
    rw [norm_smul, Real.norm_eq_abs] at hstep1
    nlinarith [hstep1, h1, h2, abs_nonneg (b - a)]
  have hgoal : (m/2) * |b - a| ≤ ‖F b s - F a s‖ := by
    rw [hkey]; exact hfinal
  simpa only [norm_sub_rev] using hgoal

/-- **Uniform geometric bounds for a `C¹` family of `C^∞` knots.** -/
theorem uniformBoundsC1 {F : ℝ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hF : ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2))
    (hslice : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      Work.Drive.IsCInfKnot (fun t : ℝ => F t s)) :
    ∃ m δ σ : ℝ, 0 < m ∧ 0 < δ ∧ δ ≤ LeanEval.KnotTheory.Quadrisecant.period / 2 ∧ 0 < σ ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (∀ t : ℝ, m ≤ ‖LeanEval.KnotTheory.Quadrisecant.velocity (fun u : ℝ => F u s) t‖) ∧
        (∀ t t' : ℝ, |t' - t| ≤ δ → (m / 2) * |t' - t| ≤ ‖F t s - F t' s‖) ∧
        (∀ t t' : ℝ, δ ≤ |t' - t| → |t' - t| ≤ LeanEval.KnotTheory.Quadrisecant.period - δ →
          σ ≤ ‖F t s - F t' s‖) := by
  have hper : 0 < period := by unfold period; positivity
  have hF' : ContDiff ℝ 1 (fam F) := hF
  have hcontPhi : Continuous (famPhi F) := continuous_famPhi_c1 F hF'
  -- minimal speed
  have hKc : IsCompact Kbox := isCompact_Icc.prod isCompact_Icc
  have hKne : Kbox.Nonempty := ⟨(0, 0), by
    rw [Kbox, Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
    exact ⟨⟨le_rfl, hper.le⟩, ⟨le_rfl, zero_le_one⟩⟩⟩
  obtain ⟨p0, hp0K, hp0min⟩ := hKc.exists_isMinOn hKne hcontPhi.norm.continuousOn
  have hp0K' : p0.1 ∈ Set.Icc (0:ℝ) period ∧ p0.2 ∈ Set.Icc (0:ℝ) 1 := by
    rw [Kbox, Set.mem_prod] at hp0K; exact hp0K
  set m : ℝ := ‖famPhi F p0‖ with hmdef
  have hmpos : 0 < m := by
    rw [hmdef]
    refine norm_pos_iff.mpr ?_
    intro h0
    exact (hslice p0.2 hp0K'.2).regular p0.1 (by
      rw [velocity, deriv_slice_eq_c1 F hF' p0.1 p0.2]
      simpa using h0)
  have hmle : ∀ p ∈ Kbox, m ≤ ‖famPhi F p‖ := by
    intro p hp
    have h := hp0min hp
    simp only [Set.mem_ofPred_eq] at h
    simpa only [hmdef] using h
  -- uniform continuity scale
  have hWc : IsCompact Wbox := isCompact_Icc.prod isCompact_Icc
  have hucW : UniformContinuousOn (famPhi F) Wbox :=
    hWc.uniformContinuousOn_of_continuous hcontPhi.continuousOn
  obtain ⟨η, hηpos, hη⟩ := (Metric.uniformContinuousOn_iff.mp hucW) (m/2) (by linarith)
  have hη' : ∀ x ∈ Wbox, ∀ y ∈ Wbox, dist x y < η → ‖famPhi F x - famPhi F y‖ < m/2 := by
    intro x hx y hy h
    have := hη x hx y hy h
    rwa [dist_eq_norm] at this
  set δ : ℝ := min (period/4) (η/2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ4 : δ ≤ period/4 := min_le_left _ _
  have hδη : δ ≤ η/2 := min_le_right _ _
  have hδ2 : δ ≤ period/2 := by linarith
  -- separation
  set Dbox : Set ((ℝ × ℝ) × ℝ) :=
    (Set.Icc (0:ℝ) period ×ˢ Set.Icc δ (period - δ)) ×ˢ Set.Icc (0:ℝ) 1 with hDbox
  have hDc : IsCompact Dbox := (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have hDne : Dbox.Nonempty := ⟨((0, δ), 0), by
    rw [hDbox, Set.mem_prod, Set.mem_prod, Set.mem_Icc, Set.mem_Icc, Set.mem_Icc]
    exact ⟨⟨⟨le_rfl, hper.le⟩, ⟨le_rfl, by linarith⟩⟩, ⟨le_rfl, zero_le_one⟩⟩⟩
  have hg1 : Continuous (fun q : (ℝ × ℝ) × ℝ => ((q.1.1, q.2) : ℝ × ℝ)) := by fun_prop
  have hg2 : Continuous (fun q : (ℝ × ℝ) × ℝ => ((q.1.1 + q.1.2, q.2) : ℝ × ℝ)) := by fun_prop
  have hDcont : ContinuousOn
      (fun q : (ℝ × ℝ) × ℝ => ‖fam F (q.1.1, q.2) - fam F (q.1.1 + q.1.2, q.2)‖) Dbox :=
    ((hF'.continuous.comp hg1).sub (hF'.continuous.comp hg2)).norm.continuousOn
  obtain ⟨q0, hq0D, hq0min⟩ := hDc.exists_isMinOn hDne hDcont
  set σ : ℝ := ‖fam F (q0.1.1, q0.2) - fam F (q0.1.1 + q0.1.2, q0.2)‖ with hσdef
  have hq0D' : q0.1.1 ∈ Set.Icc (0:ℝ) period ∧ q0.1.2 ∈ Set.Icc δ (period - δ) ∧
      q0.2 ∈ Set.Icc (0:ℝ) 1 := by
    rw [hDbox, Set.mem_prod, Set.mem_prod] at hq0D
    exact ⟨hq0D.1.1, hq0D.1.2, hq0D.2⟩
  have hσpos : 0 < σ := by
    rw [hσdef]
    refine norm_pos_iff.mpr ?_
    intro h0
    obtain ⟨hq0t, hq0Δ, hq0s⟩ := hq0D'
    have heq : fam F (q0.1.1, q0.2) = fam F (q0.1.1 + q0.1.2, q0.2) := sub_eq_zero.mp h0
    rw [fam] at heq
    have hp := (hslice q0.2 hq0s).periodic
    have e1 : F (resid q0.1.1) q0.2 = F q0.1.1 q0.2 :=
      (hp.int_mul ⌊q0.1.1/period⌋).sub_eq q0.1.1
    have e2 : F (resid (q0.1.1 + q0.1.2)) q0.2 = F (q0.1.1 + q0.1.2) q0.2 :=
      (hp.int_mul ⌊(q0.1.1 + q0.1.2)/period⌋).sub_eq (q0.1.1 + q0.1.2)
    have heqab : F (resid q0.1.1) q0.2 = F (resid (q0.1.1 + q0.1.2)) q0.2 := by
      rw [e1, e2]; exact heq
    have hab : resid q0.1.1 = resid (q0.1.1 + q0.1.2) :=
      (hslice q0.2 hq0s).injOn (resid_mem _) (resid_mem _) heqab
    have hΔeq : q0.1.2 = ((⌊(q0.1.1 + q0.1.2)/period⌋ - ⌊q0.1.1/period⌋ : ℤ) : ℝ) * period := by
      have h := hab
      unfold resid at h
      push_cast
      nlinarith [h]
    have hΔpos : 0 < q0.1.2 := by linarith [hδpos, hq0Δ.1]
    have hΔlt : q0.1.2 < period := by linarith [hq0Δ.2, hδpos]
    have hmZpos : 0 < ((⌊(q0.1.1 + q0.1.2)/period⌋ - ⌊q0.1.1/period⌋ : ℤ) : ℝ) := by
      nlinarith [hΔeq, hΔpos, hper]
    have hmZlt : ((⌊(q0.1.1 + q0.1.2)/period⌋ - ⌊q0.1.1/period⌋ : ℤ) : ℝ) < 1 := by
      nlinarith [hΔeq, hΔlt, hper]
    have hzero := int_eq_zero_of_pos_lt_one hmZpos hmZlt
    rw [hzero] at hΔeq
    simp at hΔeq
    linarith [hΔpos]
  refine ⟨m, δ, σ, hmpos, hδpos, hδ2, hσpos, ?_⟩
  intro s hs
  refine ⟨?_, ?_, ?_⟩
  · -- (1) uniform lower bound on the speed
    intro t
    have hp := (hslice s hs).periodic
    have hpd : Function.Periodic (deriv (fun u : ℝ => F u s)) period := periodic_deriv hp
    have hstep : deriv (fun u : ℝ => F u s) t = deriv (fun u : ℝ => F u s) (resid t) := by
      have h := (hpd.int_mul ⌊t/period⌋).sub_eq t
      show deriv (fun u : ℝ => F u s) t
        = deriv (fun u : ℝ => F u s) (t - (⌊t/period⌋:ℝ)*period)
      rw [← h]
    have hge : m ≤ ‖deriv (fun u : ℝ => F u s) (resid t)‖ := by
      have hh := hmle (resid t, s) ⟨⟨resid_nonneg t, (resid_lt t).le⟩, hs⟩
      rwa [← deriv_slice_eq_c1 F hF' (resid t) s] at hh
    show m ≤ ‖velocity (fun u : ℝ => F u s) t‖
    show m ≤ ‖deriv (fun u : ℝ => F u s) t‖
    rw [hstep]; exact hge
  · -- (2) local chord lower bound
    intro t t' ht
    have ha : resid t ∈ Set.Ico (0:ℝ) period := resid_mem t
    have hbsub : (t' - (⌊t/period⌋:ℝ)*period) - resid t = t' - t := by unfold resid; ring
    have habs : |(t' - (⌊t/period⌋:ℝ)*period) - resid t| = |t' - t| := by rw [hbsub]
    have hle : |(t' - (⌊t/period⌋:ℝ)*period) - resid t| ≤ δ := by rw [habs]; exact ht
    have hloc := local_bound_c1 F hF' hηpos hδ4 hδη hη' hmle hs ha hle
    have e1 : F (resid t) s = F t s := ((hslice s hs).periodic.int_mul ⌊t/period⌋).sub_eq t
    have e2 : F (t' - (⌊t/period⌋:ℝ)*period) s = F t' s := by
      have hp := (hslice s hs).periodic
      have h : F (t' - (⌊t/period⌋:ℝ)*period) s
          = F ((t' - (⌊t/period⌋:ℝ)*period) + (⌊t/period⌋:ℝ)*period) s :=
        ((hp.int_mul ⌊t/period⌋) (t' - (⌊t/period⌋:ℝ)*period)).symm
      rwa [sub_add_cancel] at h
    rw [habs, e1, e2] at hloc
    exact hloc
  · -- (3) uniform separation
    intro t t' h1 h2
    have key : ∀ (u Δ : ℝ), u ∈ Set.Icc (0:ℝ) period → Δ ∈ Set.Icc δ (period - δ) →
        σ ≤ ‖F u s - F (u + Δ) s‖ := by
      intro u Δ hu hΔ
      have hmin := hq0min (show ((u, Δ), s) ∈ Dbox from ⟨⟨hu, hΔ⟩, hs⟩)
      simpa only [hσdef, fam, Set.mem_ofPred_eq] using hmin
    rcases le_or_gt t t' with hle | hlt
    · have hΔ : t' - t ∈ Set.Icc δ (period - δ) := by
        constructor
        · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t' - t)] at h1; exact h1
        · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t' - t)] at h2; exact h2
      have hra : resid t ∈ Set.Icc (0:ℝ) period := ⟨resid_nonneg t, (resid_lt t).le⟩
      have e1 : F (resid t) s = F t s := ((hslice s hs).periodic.int_mul ⌊t/period⌋).sub_eq t
      have e2 : F (resid t + (t' - t)) s = F t' s := by
        have hp := (hslice s hs).periodic
        have h : F (resid t + (t' - t)) s
            = F ((resid t + (t' - t)) + (⌊t/period⌋:ℝ)*period) s :=
          ((hp.int_mul ⌊t/period⌋) (resid t + (t' - t))).symm
        have harg : (resid t + (t' - t)) + (⌊t/period⌋:ℝ)*period = t' := by
          unfold resid; ring
        rwa [harg] at h
      calc σ ≤ ‖F (resid t) s - F (resid t + (t' - t)) s‖ := key _ _ hra hΔ
        _ = ‖F t s - F t' s‖ := by rw [e1, e2]
    · have hΔ : t - t' ∈ Set.Icc δ (period - δ) := by
        constructor
        · rw [abs_of_neg (by linarith : t' - t < 0)] at h1; linarith
        · rw [abs_of_neg (by linarith : t' - t < 0)] at h2; linarith
      have hrb : resid t' ∈ Set.Icc (0:ℝ) period := ⟨resid_nonneg t', (resid_lt t').le⟩
      have e1 : F (resid t') s = F t' s := ((hslice s hs).periodic.int_mul ⌊t'/period⌋).sub_eq t'
      have e2 : F (resid t' + (t - t')) s = F t s := by
        have hp := (hslice s hs).periodic
        have h : F (resid t' + (t - t')) s
            = F ((resid t' + (t - t')) + (⌊t'/period⌋:ℝ)*period) s :=
          ((hp.int_mul ⌊t'/period⌋) (resid t' + (t - t'))).symm
        have harg : (resid t' + (t - t')) + (⌊t'/period⌋:ℝ)*period = t := by
          unfold resid; ring
        rwa [harg] at h
      calc σ ≤ ‖F (resid t') s - F (resid t' + (t - t')) s‖ := key _ _ hrb hΔ
        _ = ‖F t' s - F t s‖ := by rw [e1, e2]
        _ = ‖F t s - F t' s‖ := norm_sub_rev _ _

end Work.Drive
