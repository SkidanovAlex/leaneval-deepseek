import Mathlib
import Submission.Work.Drive.KnotDefs

open LeanEval.KnotTheory.Quadrisecant

namespace Work.Drive

/-! # Uniform geometric bounds for an analytic family of knots

We prove that a `C^∞` (indeed analytic) family `R : ℝ → ℝ → ℝ³` whose slices
`R · s` are smooth knots for `s ∈ [0,1]` admits *uniform* geometric constants on
the compact parameter slab `s ∈ [0,1]`:

* a positive minimal speed `m`,
* a positive parameter scale `δ ≤ period/2`,
* a positive separation `σ`,

such that every slice has speed `≥ m`, is "almost an arclength parametrisation"
up to a factor `m/2` on parameter intervals of length `≤ δ`, and separates
distinct points whose parameters differ by between `δ` and `period - δ`.

The proof is a compactness argument.  The essential input is that the
`t`-derivative of the family, `(t,s) ↦ (fderiv ℝ (fun p => R p.1 p.2) (t,s)) (1,0)`,
is continuous, obtained from `ContDiff ℝ ⊤` via `ContDiff.contDiff_fderiv_apply`.
-/

/-- The uncurried family `(t,s) ↦ R t s`. -/
noncomputable def fam (R : ℝ → ℝ → Space) : ℝ × ℝ → Space := fun p => R p.1 p.2

/-- The `t`-partial derivative of the family, evaluated through `fderiv`. -/
noncomputable def famPhi (R : ℝ → ℝ → Space) : ℝ × ℝ → Space :=
  fun p => (fderiv ℝ (fam R) p) (1, 0)

/-- The representative of `t` in `[0, period)`. -/
noncomputable def resid (t : ℝ) : ℝ := t - (⌊t / period⌋ : ℝ) * period

/-- The slab on which the minimal speed is computed. -/
def Kbox : Set (ℝ × ℝ) := Set.Icc (0:ℝ) period ×ˢ Set.Icc (0:ℝ) 1

/-- A slightly larger slab, closed under the local parameter window. -/
def Wbox : Set (ℝ × ℝ) := Set.Icc (-period) (2*period) ×ˢ Set.Icc (0:ℝ) 1

/-- The `t`-derivative of a slice, expressed through `famPhi`. -/
lemma hasDerivAt_slice (R : ℝ → ℝ → Space) (hR : ContDiff ℝ ⊤ (fam R)) (t s : ℝ) :
    HasDerivAt (fun u : ℝ => R u s) (famPhi R (t, s)) t := by
  have h1 : HasFDerivAt (fun u : ℝ => (u, s)) (ContinuousLinearMap.inl ℝ ℝ ℝ) t :=
    hasFDerivAt_prodMk_left t s
  have h2 : HasFDerivAt (fam R) (fderiv ℝ (fam R) (t, s)) (t, s) :=
    (hR.differentiable (by simp) (t, s)).hasFDerivAt
  have h3 : HasFDerivAt (fun u : ℝ => fam R (u, s))
      ((fderiv ℝ (fam R) (t, s)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) t := by
    simpa only [Function.comp_def] using h2.comp t h1
  have h4 : HasDerivAt (fun u : ℝ => fam R (u, s))
      (((fderiv ℝ (fam R) (t, s)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) 1) t := h3.hasDerivAt
  have h5 : (((fderiv ℝ (fam R) (t, s)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) 1)
      = famPhi R (t, s) := by
    simp [famPhi, ContinuousLinearMap.comp_apply]
  rw [h5] at h4
  simpa only [fam] using h4

lemma deriv_slice_eq (R : ℝ → ℝ → Space) (hR : ContDiff ℝ ⊤ (fam R)) (t s : ℝ) :
    deriv (fun u : ℝ => R u s) t = famPhi R (t, s) :=
  (hasDerivAt_slice R hR t s).deriv

/-- Joint continuity of the `t`-partial derivative. -/
lemma continuous_famPhi (R : ℝ → ℝ → Space) (hR : ContDiff ℝ ⊤ (fam R)) :
    Continuous (famPhi R) := by
  have h1 : ContDiff ℝ ⊤ (fun q : (ℝ × ℝ) × (ℝ × ℝ) => (fderiv ℝ (fam R) q.1) q.2) :=
    ContDiff.contDiff_fderiv_apply hR (m := ⊤) (by simp)
  have h2 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => ((p, (1, 0)) : (ℝ × ℝ) × (ℝ × ℝ))) := by fun_prop
  exact (h1.comp h2).continuous

/-- The derivative of a `period`-periodic function is `period`-periodic. -/
lemma periodic_deriv {f : ℝ → Space} (hf : Function.Periodic f period) :
    Function.Periodic (deriv f) period := by
  intro x
  rw [← deriv_comp_add_const f period x]
  congr 1
  funext u
  exact hf u

/-- An integer strictly between `0` and `1` is zero. -/
lemma int_eq_zero_of_pos_lt_one {m : ℤ} (h1 : 0 < (m:ℝ)) (h2 : (m:ℝ) < 1) : m = 0 := by
  have hp : 0 < m := Int.cast_pos.mp h1
  have hq : m < 1 := by
    rw [← Int.cast_one (R := ℝ)] at h2
    exact Int.cast_lt.mp h2
  omega

lemma resid_nonneg (t : ℝ) : 0 ≤ resid t := by
  have hper : 0 < period := by unfold period; positivity
  have h1 : (⌊t / period⌋ : ℝ) ≤ t / period := Int.floor_le _
  have h2 : (⌊t / period⌋ : ℝ) * period ≤ t := by
    have := mul_le_mul_of_nonneg_right h1 hper.le
    rwa [div_mul_cancel₀ t hper.ne'] at this
  unfold resid; linarith

lemma resid_lt (t : ℝ) : resid t < period := by
  have hper : 0 < period := by unfold period; positivity
  have h1 : t / period < (⌊t / period⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have h2 : t < ((⌊t / period⌋ : ℝ) + 1) * period := by
    have := mul_lt_mul_of_pos_right h1 hper
    rwa [div_mul_cancel₀ t hper.ne'] at this
  unfold resid; nlinarith

lemma resid_mem (t : ℝ) : resid t ∈ Set.Ico (0:ℝ) period :=
  ⟨resid_nonneg t, resid_lt t⟩

/-- Derivative of `u ↦ R u s - u • v`. -/
lemma hasDerivAt_sub_smul (R : ℝ → ℝ → Space) (hR : ContDiff ℝ ⊤ (fam R)) (s u : ℝ) (v : Space) :
    HasDerivAt (fun x : ℝ => R x s - x • v) (famPhi R (u, s) - v) u := by
  have h1 : HasDerivAt (fun x : ℝ => R x s) (famPhi R (u, s)) u := hasDerivAt_slice R hR u s
  have h2 : HasDerivAt (fun x : ℝ => x • v) v u := by
    simpa using (hasDerivAt_id u).smul_const v
  have h := h1.sub h2
  have hfun : (fun x : ℝ => R x s - x • v) = ((fun x : ℝ => R x s) - fun x : ℝ => x • v) := by
    ext x; rfl
  rw [hfun]
  exact h

/-- The local "chord versus parameter" bound: on a parameter interval of length
`≤ δ`, the chord length is at least `(m/2)` times the parameter length. -/
lemma local_bound (R : ℝ → ℝ → Space) (hR : ContDiff ℝ ⊤ (fam R))
    {m η δ : ℝ} (hη : 0 < η) (hδ4 : δ ≤ period/4) (hδη : δ ≤ η/2)
    (huc : ∀ x ∈ Wbox, ∀ y ∈ Wbox, dist x y < η → ‖famPhi R x - famPhi R y‖ < m/2)
    (hmle : ∀ p ∈ Kbox, m ≤ ‖famPhi R p‖)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1)
    {a b : ℝ} (ha : a ∈ Set.Ico (0:ℝ) period) (hab : |b - a| ≤ δ) :
    (m/2) * |b - a| ≤ ‖R a s - R b s‖ := by
  have hper : 0 < period := by unfold period; positivity
  set v : Space := famPhi R (a, s) with hv
  set I : Set ℝ := Set.Icc (a - |b - a|) (a + |b - a|) with hI
  set g : ℝ → Space := fun u => R u s - u • v with hg
  have hderivg : ∀ u, deriv g u = famPhi R (u, s) - v := by
    intro u
    rw [hg]
    exact (hasDerivAt_sub_smul R hR s u v).deriv
  have hdiff : ∀ u ∈ I, DifferentiableAt ℝ g u := by
    intro u _
    rw [hg]
    exact (hasDerivAt_sub_smul R hR s u v).differentiableAt
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
  have hkey : R b s - R a s = (g b - g a) + (b - a) • v := by
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
  have hgoal : (m/2) * |b - a| ≤ ‖R b s - R a s‖ := by
    rw [hkey]; exact hfinal
  simpa only [norm_sub_rev] using hgoal

/-- Uniform geometric bounds for a family of smooth knots over the slab `[0,1]`:
some positive minimal speed `m`, a positive parameter scale `δ ≤ period/2`, and a
positive separation `σ`, all uniform in the slice parameter `s ∈ [0,1]`.  The
family is analytic on `ℝ × ℝ` (the workspace's `⊤` is the analytic order) and
each slice `R · s`, `s ∈ [0,1]`, is a smooth knot. -/
theorem uniformCurveBounds {R : ℝ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hR : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => R p.1 p.2))
    (hslice : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot (fun t : ℝ => R t s)) :
    ∃ m δ σ : ℝ, 0 < m ∧ 0 < δ ∧ δ ≤ LeanEval.KnotTheory.Quadrisecant.period / 2 ∧ 0 < σ ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (∀ t : ℝ, m ≤ ‖LeanEval.KnotTheory.Quadrisecant.velocity (fun u : ℝ => R u s) t‖) ∧
        (∀ t t' : ℝ, |t' - t| ≤ δ → (m / 2) * |t' - t| ≤ ‖R t s - R t' s‖) ∧
        (∀ t t' : ℝ, δ ≤ |t' - t| → |t' - t| ≤ LeanEval.KnotTheory.Quadrisecant.period - δ →
          σ ≤ ‖R t s - R t' s‖) := by
  have hper : 0 < period := by unfold period; positivity
  have hR' : ContDiff ℝ ⊤ (fam R) := hR
  have hcontPhi : Continuous (famPhi R) := continuous_famPhi R hR'
  -- minimal speed
  have hKc : IsCompact Kbox := isCompact_Icc.prod isCompact_Icc
  have hKne : Kbox.Nonempty := ⟨(0, 0), by
    rw [Kbox, Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
    exact ⟨⟨le_rfl, hper.le⟩, ⟨le_rfl, zero_le_one⟩⟩⟩
  obtain ⟨p0, hp0K, hp0min⟩ := hKc.exists_isMinOn hKne hcontPhi.norm.continuousOn
  have hp0K' : p0.1 ∈ Set.Icc (0:ℝ) period ∧ p0.2 ∈ Set.Icc (0:ℝ) 1 := by
    rw [Kbox, Set.mem_prod] at hp0K; exact hp0K
  set m : ℝ := ‖famPhi R p0‖ with hmdef
  have hmpos : 0 < m := by
    rw [hmdef]
    refine norm_pos_iff.mpr ?_
    intro h0
    exact (hslice p0.2 hp0K'.2).regular p0.1 (by
      rw [velocity, deriv_slice_eq R hR' p0.1 p0.2]
      simpa using h0)
  have hmle : ∀ p ∈ Kbox, m ≤ ‖famPhi R p‖ := by
    intro p hp
    have h := hp0min hp
    simp only [Set.mem_ofPred_eq] at h
    simpa only [hmdef] using h
  -- uniform continuity scale
  have hWc : IsCompact Wbox := isCompact_Icc.prod isCompact_Icc
  have hucW : UniformContinuousOn (famPhi R) Wbox :=
    hWc.uniformContinuousOn_of_continuous hcontPhi.continuousOn
  obtain ⟨η, hηpos, hη⟩ := (Metric.uniformContinuousOn_iff.mp hucW) (m/2) (by linarith)
  have hη' : ∀ x ∈ Wbox, ∀ y ∈ Wbox, dist x y < η → ‖famPhi R x - famPhi R y‖ < m/2 := by
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
      (fun q : (ℝ × ℝ) × ℝ => ‖fam R (q.1.1, q.2) - fam R (q.1.1 + q.1.2, q.2)‖) Dbox :=
    ((hR'.continuous.comp hg1).sub (hR'.continuous.comp hg2)).norm.continuousOn
  obtain ⟨q0, hq0D, hq0min⟩ := hDc.exists_isMinOn hDne hDcont
  set σ : ℝ := ‖fam R (q0.1.1, q0.2) - fam R (q0.1.1 + q0.1.2, q0.2)‖ with hσdef
  have hq0D' : q0.1.1 ∈ Set.Icc (0:ℝ) period ∧ q0.1.2 ∈ Set.Icc δ (period - δ) ∧
      q0.2 ∈ Set.Icc (0:ℝ) 1 := by
    rw [hDbox, Set.mem_prod, Set.mem_prod] at hq0D
    exact ⟨hq0D.1.1, hq0D.1.2, hq0D.2⟩
  have hσpos : 0 < σ := by
    rw [hσdef]
    refine norm_pos_iff.mpr ?_
    intro h0
    obtain ⟨hq0t, hq0Δ, hq0s⟩ := hq0D'
    have heq : fam R (q0.1.1, q0.2) = fam R (q0.1.1 + q0.1.2, q0.2) := sub_eq_zero.mp h0
    rw [fam] at heq
    have hp := (hslice q0.2 hq0s).periodic
    have e1 : R (resid q0.1.1) q0.2 = R q0.1.1 q0.2 :=
      (hp.int_mul ⌊q0.1.1/period⌋).sub_eq q0.1.1
    have e2 : R (resid (q0.1.1 + q0.1.2)) q0.2 = R (q0.1.1 + q0.1.2) q0.2 :=
      (hp.int_mul ⌊(q0.1.1 + q0.1.2)/period⌋).sub_eq (q0.1.1 + q0.1.2)
    have heqab : R (resid q0.1.1) q0.2 = R (resid (q0.1.1 + q0.1.2)) q0.2 := by
      rw [e1, e2]; exact heq
    have hab : resid q0.1.1 = resid (q0.1.1 + q0.1.2) :=
      (hslice q0.2 hq0s).injective_on_period (resid_mem _) (resid_mem _) heqab
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
    have hpd : Function.Periodic (deriv (fun u : ℝ => R u s)) period := periodic_deriv hp
    have hstep : deriv (fun u : ℝ => R u s) t = deriv (fun u : ℝ => R u s) (resid t) := by
      have h := (hpd.int_mul ⌊t/period⌋).sub_eq t
      show deriv (fun u : ℝ => R u s) t
        = deriv (fun u : ℝ => R u s) (t - (⌊t/period⌋:ℝ)*period)
      rw [← h]
    have hge : m ≤ ‖deriv (fun u : ℝ => R u s) (resid t)‖ := by
      have hh := hmle (resid t, s) ⟨⟨resid_nonneg t, (resid_lt t).le⟩, hs⟩
      rwa [← deriv_slice_eq R hR' (resid t) s] at hh
    show m ≤ ‖velocity (fun u : ℝ => R u s) t‖
    show m ≤ ‖deriv (fun u : ℝ => R u s) t‖
    rw [hstep]; exact hge
  · -- (2) local chord lower bound
    intro t t' ht
    have ha : resid t ∈ Set.Ico (0:ℝ) period := resid_mem t
    have hbsub : (t' - (⌊t/period⌋:ℝ)*period) - resid t = t' - t := by unfold resid; ring
    have habs : |(t' - (⌊t/period⌋:ℝ)*period) - resid t| = |t' - t| := by rw [hbsub]
    have hle : |(t' - (⌊t/period⌋:ℝ)*period) - resid t| ≤ δ := by rw [habs]; exact ht
    have hloc := local_bound R hR' hηpos hδ4 hδη hη' hmle hs ha hle
    have e1 : R (resid t) s = R t s := ((hslice s hs).periodic.int_mul ⌊t/period⌋).sub_eq t
    have e2 : R (t' - (⌊t/period⌋:ℝ)*period) s = R t' s := by
      have hp := (hslice s hs).periodic
      have h : R (t' - (⌊t/period⌋:ℝ)*period) s
          = R ((t' - (⌊t/period⌋:ℝ)*period) + (⌊t/period⌋:ℝ)*period) s :=
        ((hp.int_mul ⌊t/period⌋) (t' - (⌊t/period⌋:ℝ)*period)).symm
      rwa [sub_add_cancel] at h
    rw [habs, e1, e2] at hloc
    exact hloc
  · -- (3) uniform separation
    intro t t' h1 h2
    have key : ∀ (u Δ : ℝ), u ∈ Set.Icc (0:ℝ) period → Δ ∈ Set.Icc δ (period - δ) →
        σ ≤ ‖R u s - R (u + Δ) s‖ := by
      intro u Δ hu hΔ
      have hmin := hq0min (show ((u, Δ), s) ∈ Dbox from ⟨⟨hu, hΔ⟩, hs⟩)
      simpa only [hσdef, fam, Set.mem_ofPred_eq] using hmin
    rcases le_or_gt t t' with hle | hlt
    · have hΔ : t' - t ∈ Set.Icc δ (period - δ) := by
        constructor
        · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t' - t)] at h1; exact h1
        · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t' - t)] at h2; exact h2
      have hra : resid t ∈ Set.Icc (0:ℝ) period := ⟨resid_nonneg t, (resid_lt t).le⟩
      have e1 : R (resid t) s = R t s := ((hslice s hs).periodic.int_mul ⌊t/period⌋).sub_eq t
      have e2 : R (resid t + (t' - t)) s = R t' s := by
        have hp := (hslice s hs).periodic
        have h : R (resid t + (t' - t)) s
            = R ((resid t + (t' - t)) + (⌊t/period⌋:ℝ)*period) s :=
          ((hp.int_mul ⌊t/period⌋) (resid t + (t' - t))).symm
        have harg : (resid t + (t' - t)) + (⌊t/period⌋:ℝ)*period = t' := by
          unfold resid; ring
        rwa [harg] at h
      calc σ ≤ ‖R (resid t) s - R (resid t + (t' - t)) s‖ := key _ _ hra hΔ
        _ = ‖R t s - R t' s‖ := by rw [e1, e2]
    · have hΔ : t - t' ∈ Set.Icc δ (period - δ) := by
        constructor
        · rw [abs_of_neg (by linarith : t' - t < 0)] at h1; linarith
        · rw [abs_of_neg (by linarith : t' - t < 0)] at h2; linarith
      have hrb : resid t' ∈ Set.Icc (0:ℝ) period := ⟨resid_nonneg t', (resid_lt t').le⟩
      have e1 : R (resid t') s = R t' s := ((hslice s hs).periodic.int_mul ⌊t'/period⌋).sub_eq t'
      have e2 : R (resid t' + (t - t')) s = R t s := by
        have hp := (hslice s hs).periodic
        have h : R (resid t' + (t - t')) s
            = R ((resid t' + (t - t')) + (⌊t'/period⌋:ℝ)*period) s :=
          ((hp.int_mul ⌊t'/period⌋) (resid t' + (t - t'))).symm
        have harg : (resid t' + (t - t')) + (⌊t'/period⌋:ℝ)*period = t := by
          unfold resid; ring
        rwa [harg] at h
      calc σ ≤ ‖R (resid t') s - R (resid t' + (t - t')) s‖ := key _ _ hrb hΔ
        _ = ‖R t' s - R t s‖ := by rw [e1, e2]
        _ = ‖R t s - R t' s‖ := norm_sub_rev _ _

end Work.Drive
