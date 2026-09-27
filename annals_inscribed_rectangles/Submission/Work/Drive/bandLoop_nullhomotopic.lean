import Mathlib
import Submission.Work.Drive.bandLoop_periodic_argument
import Submission.Work.Drive.periodic_argument_of_homotopy
import Submission.Work.Drive.directionStabilization_of_nullhomotopic

namespace Work.Drive

open scoped ContDiff Topology
open Filter
open Work.Drive.Neutral

noncomputable section

/-!
# From a periodic argument of the band loop to the unit extension `G`

`Work.Drive.directionStabilization_of_nullhomotopic` needs a *continuous unit-valued* `G` on the disc
`‖x‖ ≤ 1/4` agreeing with the loop `x ↦ c · conj (w_h (x,τ₁))` on `‖x‖ ≥ 1/4`.  The content of that
hypothesis is the winding-zero condition of `PLANE_CHART_FINAL.md` §9.1.  In
`bandLoop_periodic_argument.lean` this is produced as a continuous `2π`-periodic real argument of the
loop *as a function of the loop parameter* `σ`; this file converts such an argument into the unit
extension `G`.

## The two steps

**1. A continuous `2π`-periodic function of `Complex.arg` is continuous on the punctured plane.**
(`continuousOn_comp_arg`.)  `Complex.arg` is continuous on the slit plane
`ℂ ∖ (-∞,0]` but *not* at the negative reals, where its value jumps by `2π`; the periodicity of `Ψ`
makes the jump invisible, and the argument is closed by covering the punctured plane with the slit
plane and its *reflection* `{x | -x ∈ slitPlane}`, on which the *other* argument
`x ↦ (-x).arg + π` is continuous and differs from `Complex.arg` by an integer multiple of `2π`.
No homotopy theory is used.

**2. The radial extension.**  With `κ r := min (4 r) 1` the function

> `G x := if ‖x‖ ≤ 1/4 then exp (i · κ ‖x‖ · ψ (arg x)) else (the loop value at x)`

is continuous (the two pieces agree on the circle `‖x‖ = 1/4`), unit-valued on the disc (the exponent
is real), and equal to the loop on `‖x‖ ≥ 1/4`; its continuity at the origin is the boundedness of `ψ`
on the compact range of `arg` together with `κ 0 = 0`.
-/

/-- **A `2π`-periodic continuous function of the argument is continuous.**  For `Ψ : ℝ → β` continuous
and `2π`-periodic, the function `x ↦ Ψ (Complex.arg x)` is continuous on the punctured plane.  (The
periodicity is what repairs the jump of `Complex.arg` across the negative reals.) -/
theorem continuousOn_comp_arg {β : Type*} [TopologicalSpace β] {Ψ : ℝ → β} (hΨ : Continuous Ψ)
    (hper : Function.Periodic Ψ (2 * Real.pi)) :
    ContinuousOn (fun x : ℂ => Ψ (Complex.arg x)) {x : ℂ | x ≠ 0} := by
  -- the two charts
  have hVopen : IsOpen {x : ℂ | -x ∈ Complex.slitPlane} :=
    Complex.isOpen_slitPlane.preimage continuous_neg
  have hU : ContinuousOn (fun x : ℂ => Ψ (Complex.arg x)) Complex.slitPlane :=
    hΨ.comp_continuousOn Complex.continuousOn_arg
  have hV : ContinuousOn (fun x : ℂ => Ψ (Complex.arg x)) {x : ℂ | -x ∈ Complex.slitPlane} := by
    have harg : ContinuousOn (fun x : ℂ => (-x).arg + Real.pi) {x : ℂ | -x ∈ Complex.slitPlane} :=
      (Complex.continuousOn_arg.comp continuous_neg.continuousOn (fun x hx => hx)).add
        continuousOn_const
    refine (hΨ.comp_continuousOn harg).congr ?_
    intro x hx
    -- `(-x).arg + π ≡ arg x` modulo `2π`
    have hxne : x ≠ 0 := fun h => by
      rw [h] at hx
      simp [Complex.slitPlane] at hx
    show Ψ (Complex.arg x) = Ψ ((-x).arg + Real.pi)
    rcases em (x.im < 0 ∨ (x.im = 0 ∧ 0 < x.re)) with h | h
    · have h1 : (-x).arg = x.arg + Real.pi := Complex.arg_neg_eq_arg_add_pi_iff.mpr h
      rw [h1, show (x.arg + Real.pi) + Real.pi = x.arg + 2 * Real.pi from by ring]
      exact (hper x.arg).symm
    · have h1 : (-x).arg = x.arg - Real.pi := by
        refine Complex.arg_neg_eq_arg_sub_pi_iff.mpr ?_
        rcases lt_trichotomy x.im 0 with hlt | heq | hgt
        · exact absurd (Or.inl hlt) h
        · refine Or.inr ⟨heq, ?_⟩
          have h2 : x.re ≤ 0 := le_of_not_gt fun hpos => h (Or.inr ⟨heq, hpos⟩)
          have h3 : x.re ≠ 0 := fun hzero =>
            hxne (by apply Complex.ext <;> simp [hzero, heq])
          exact lt_of_le_of_ne h2 h3
        · exact Or.inl hgt
      rw [h1]
      ring_nf
  -- the cover
  refine (hU.union_of_isOpen hV Complex.isOpen_slitPlane hVopen).mono ?_
  intro x hx
  by_cases h : x ∈ Complex.slitPlane
  · exact Or.inl h
  · refine Or.inr ?_
    show -x ∈ Complex.slitPlane
    rw [Complex.mem_slitPlane_iff] at h ⊢
    push Not at h
    have hre : x.re < 0 := by
      have h3 : x.re ≠ 0 := fun hzero => hx (by apply Complex.ext <;> simp [hzero, h.2])
      exact lt_of_le_of_ne h.1 h3
    exact Or.inl (by simp only [Complex.neg_re]; linarith)


/-- `‖exp (i θ)‖ = 1` for real `θ`. -/
lemma norm_exp_mul_I (θ : ℝ) : ‖Complex.exp (((θ : ℝ) : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  have : ((((θ : ℝ) : ℂ) * Complex.I).re) = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero]

/-- The radial profile of the extension: `0` at the origin, `1` on `‖x‖ ≥ 1/4`. -/
def extLambda (r : ℝ) : ℝ := min (4 * r) 1

lemma extLambda_continuous : Continuous extLambda :=
  (continuous_const.mul continuous_id).min continuous_const

lemma extLambda_zero : extLambda 0 = 0 := by simp [extLambda]

lemma extLambda_one {r : ℝ} (hr : 1 / 4 ≤ r) : extLambda r = 1 := by
  simp only [extLambda]
  exact min_eq_right (by linarith)

lemma extLambda_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ extLambda r := by
  rw [extLambda]
  exact le_min (by linarith) zero_le_one

/-- **The radial unit extension of a loop given by a periodic argument.**

If `ψ : ℝ → ℝ` is continuous and `2π`-periodic and the loop `L` takes on the circle `‖x‖ = 1/4` the
value `exp (i ψ (arg x))`, then `L` is the boundary value of a continuous *unit-valued* function on the
disc: the radial interpolation of the argument.  This turns a periodic argument of a loop into the
unit extension `G` required by `Work.Drive.directionStabilization_of_nullhomotopic`. -/
theorem exists_unit_extension_of_periodic {L : ℂ → ℂ} {ψ : ℝ → ℝ} (hψc : Continuous ψ)
    (hψper : Function.Periodic ψ (2 * Real.pi))
    (hLc : ContinuousOn L {x : ℂ | 1 / 4 ≤ ‖x‖})
    (hL : ∀ x : ℂ, ‖x‖ = 1 / 4 →
      L x = Complex.exp (((ψ (Complex.arg x) : ℝ) : ℂ) * Complex.I)) :
    ∃ G : ℂ → ℂ, Continuous G ∧ (∀ x : ℂ, ‖x‖ ≤ 1 / 4 → ‖G x‖ = 1) ∧
      (∀ x : ℂ, 1 / 4 ≤ ‖x‖ → G x = L x) := by
  classical
  set A : ℂ → ℝ := fun x => extLambda ‖x‖ * ψ (Complex.arg x) with hAdef
  have hA0 : A 0 = 0 := by
    show extLambda ‖(0 : ℂ)‖ * ψ (Complex.arg 0) = 0
    simp [extLambda_zero]
  have hbdd : ∃ M, ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, ‖ψ θ‖ ≤ M :=
    isCompact_Icc.exists_bound_of_continuousOn hψc.continuousOn
  have hEcont : Continuous fun x : ℂ =>
      Complex.exp (((A x : ℝ) : ℂ) * Complex.I) := by
    refine Complex.continuous_exp.comp ((Complex.ofRealCLM.continuous.comp ?_).mul continuous_const)
    obtain ⟨M, hM⟩ := hbdd
    have hargmem : ∀ x : ℂ, Complex.arg x ∈ Set.Icc (-Real.pi) Real.pi := fun x =>
      ⟨(Complex.neg_pi_lt_arg x).le, Complex.arg_le_pi x⟩
    have hbound : ∀ x : ℂ, ‖A x‖ ≤ extLambda ‖x‖ * M := by
      intro x
      have h1 : ‖A x‖ = |extLambda ‖x‖| * |ψ (Complex.arg x)| := by
        rw [hAdef, Real.norm_eq_abs, abs_mul]
      rw [h1, abs_of_nonneg (extLambda_nonneg (norm_nonneg x))]
      exact mul_le_mul_of_nonneg_left (hM _ (hargmem x)) (extLambda_nonneg (norm_nonneg x))
    have hlim : Tendsto (fun x : ℂ => extLambda ‖x‖ * M) (𝓝 0) (𝓝 0) := by
      have h1 : Tendsto (fun x : ℂ => extLambda ‖x‖) (𝓝 0) (𝓝 0) := by
        have h2 := extLambda_continuous.continuousAt.tendsto.comp
          (tendsto_norm_zero (E := ℂ))
        rwa [extLambda_zero] at h2
      simpa using h1.mul tendsto_const_nhds
    have hAt0 : Tendsto A (𝓝 0) (𝓝 0) :=
      squeeze_zero_norm (f := A) (a := fun x : ℂ => extLambda ‖x‖ * M) hbound hlim
    refine continuous_iff_continuousAt.mpr fun x => ?_
    rcases eq_or_ne x 0 with rfl | hx
    · show ContinuousAt A 0
      rw [ContinuousAt, hA0]
      exact hAt0
    · have hopen : {y : ℂ | y ≠ 0} ∈ 𝓝 x := isOpen_ne.mem_nhds hx
      have hcont : ContinuousOn A {y : ℂ | y ≠ 0} := by
        rw [hAdef]
        exact ((extLambda_continuous.comp continuous_norm).continuousOn).mul
          ((continuousOn_comp_arg hψc hψper).comp continuous_id.continuousOn fun y hy => hy)
      exact hcont.continuousAt hopen

  refine ⟨(Metric.closedBall (0 : ℂ) (1 / 4)).piecewise
    (fun x => Complex.exp (((A x : ℝ) : ℂ) * Complex.I)) L, ?_, ?_, ?_⟩
  · refine continuous_piecewise (fun a ha => ?_) hEcont.continuousOn ?_
    · have ha' : ‖a‖ = 1 / 4 := by
        rw [frontier_closedBall (0 : ℂ) (by norm_num : (1 / 4 : ℝ) ≠ 0), Metric.mem_sphere,
          dist_eq_norm] at ha
        simpa using ha
      have h2 : A a = ψ (Complex.arg a) := by
        rw [hAdef]
        show extLambda ‖a‖ * ψ (Complex.arg a) = ψ (Complex.arg a)
        rw [extLambda_one (le_of_eq ha'.symm), one_mul]
      show Complex.exp (((A a : ℝ) : ℂ) * Complex.I) = L a
      rw [h2]
      exact (hL a ha').symm
    · refine hLc.mono (closure_minimal ?_ (isClosed_le continuous_const continuous_norm))
      intro y hy
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hy
      exact hy.le
  · intro x hx
    have hx' : x ∈ Metric.closedBall (0 : ℂ) (1 / 4) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hx
    have h1 : (Metric.closedBall (0 : ℂ) (1 / 4)).piecewise
        (fun x => Complex.exp (((A x : ℝ) : ℂ) * Complex.I)) L x
        = Complex.exp (((A x : ℝ) : ℂ) * Complex.I) :=
      Set.piecewise_eq_of_mem _ _ _ hx'
    rw [h1, norm_exp_mul_I]
  · intro x hx
    rcases eq_or_lt_of_le hx with heq | hlt
    · have heq' : ‖x‖ = 1 / 4 := heq.symm
      have hx' : x ∈ Metric.closedBall (0 : ℂ) (1 / 4) := by
        rw [Metric.mem_closedBall, dist_zero_right, heq']
      have h1 : (Metric.closedBall (0 : ℂ) (1 / 4)).piecewise
          (fun x => Complex.exp (((A x : ℝ) : ℂ) * Complex.I)) L x
          = Complex.exp (((A x : ℝ) : ℂ) * Complex.I) :=
        Set.piecewise_eq_of_mem _ _ _ hx'
      rw [h1]
      have h2 : A x = ψ (Complex.arg x) := by
        rw [hAdef]
        show extLambda ‖x‖ * ψ (Complex.arg x) = ψ (Complex.arg x)
        rw [heq', extLambda_one le_rfl, one_mul]
      rw [h2]
      exact (hL x heq').symm
    · have hx' : x ∉ Metric.closedBall (0 : ℂ) (1 / 4) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact not_le.mpr hlt
      have h1 : (Metric.closedBall (0 : ℂ) (1 / 4)).piecewise
          (fun x => Complex.exp (((A x : ℝ) : ℂ) * Complex.I)) L x
          = L x := Set.piecewise_eq_of_notMem _ _ _ hx'
      rw [h1]


/-- `exp (i · arg x) = x / ‖x‖` for `x ≠ 0`. -/
lemma exp_arg_eq_div (x : ℂ) (hx : x ≠ 0) :
    Complex.exp (((Complex.arg x : ℝ) : ℂ) * Complex.I) = x / ((‖x‖ : ℝ) : ℂ) := by
  rw [eq_div_iff (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx))]
  rw [mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I x

/-- The clamp of the homotopy parameter: `0` for `s ≤ 0`, `1` for `s ≥ 1`. -/
def homClamp (s : ℝ) : ℝ := min (max s 0) 1

lemma homClamp_continuous : Continuous homClamp :=
  (continuous_id.max continuous_const).min continuous_const

lemma homClamp_zero {s : ℝ} (h : s ≤ 0) : homClamp s = 0 := by
  simp only [homClamp]
  rw [max_eq_right h]
  norm_num

lemma homClamp_one {s : ℝ} (h : 1 ≤ s) : homClamp s = 1 := by
  simp only [homClamp]
  rw [max_eq_left (by linarith : (0:ℝ) ≤ s), min_eq_right h]

lemma homClamp_nonneg (s : ℝ) : 0 ≤ homClamp s := by
  simp only [homClamp]
  exact le_min (le_max_right _ _) zero_le_one

lemma homClamp_le_one (s : ℝ) : homClamp s ≤ 1 := min_le_right _ _

lemma homClamp_ne_zero_of_pos {s : ℝ} (h : 0 < s) : homClamp s ≠ 0 := by
  intro h0
  rw [homClamp, max_eq_left h.le] at h0
  have hpos : 0 < min s 1 := lt_min h zero_lt_one
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

/-- **Continuity of the direction datum along a path that avoids the zeros of `M` and `W`.** -/
lemma continuous_dirDatum_comp {M W : ℂ × ℝ → ℂ}
    (hM : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    {α : Type*} [TopologicalSpace α] {f : α → ℂ × ℝ} (hf : Continuous f)
    (hMne : ∀ a : α, M (f a) ≠ 0) (hWne : ∀ a : α, W (f a) ≠ 0) :
    Continuous fun a : α => dirDatum M W (f a) := by
  refine continuous_iff_continuousAt.mpr fun a => ?_
  have hMc : ContinuousAt (fun b : α => M (f b)) a := (hM.continuous.comp hf).continuousAt
  have hWc : ContinuousAt (fun b : α => W (f b)) a := (hW.continuous.comp hf).continuousAt
  have hMx : M (f a) ≠ 0 := hMne a
  have hWx : W (f a) ≠ 0 := hWne a
  have hMn : ContinuousAt (fun b : α => ((‖M (f b)‖ : ℝ) : ℂ)) a :=
    Complex.ofRealCLM.continuous.continuousAt.comp (continuous_norm.continuousAt.comp hMc)
  have hWn : ContinuousAt (fun b : α => ((‖W (f b)‖ : ℝ) : ℂ)) a :=
    Complex.ofRealCLM.continuous.continuousAt.comp (continuous_norm.continuousAt.comp hWc)
  have h1 : ContinuousAt (fun b : α => M (f b) / ((‖M (f b)‖ : ℝ) : ℂ)) a :=
    hMc.div hMn (by simpa using (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hMx)))
  have h2 : ContinuousAt (fun b : α => W (f b) / ((‖W (f b)‖ : ℝ) : ℂ)) a :=
    hWc.div hWn (by simpa using (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hWx)))
  exact h2.mul (continuous_star.continuousAt.comp h1)

/-- **Continuity of the direction datum along a path** (within-set form). -/
lemma continuousOn_dirDatum_comp {M W : ℂ × ℝ → ℂ}
    (hM : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    {α : Type*} [TopologicalSpace α] {f : α → ℂ × ℝ} {s : Set α} (hf : ContinuousOn f s)
    (hMne : ∀ a ∈ s, M (f a) ≠ 0) (hWne : ∀ a ∈ s, W (f a) ≠ 0) :
    ContinuousOn (fun a : α => dirDatum M W (f a)) s := by
  have hMc : ContinuousOn (fun b : α => M (f b)) s := hM.continuous.comp_continuousOn hf
  have hWc : ContinuousOn (fun b : α => W (f b)) s := hW.continuous.comp_continuousOn hf
  have hMn : ContinuousOn (fun b : α => ((‖M (f b)‖ : ℝ) : ℂ)) s :=
    Complex.ofRealCLM.continuous.comp_continuousOn (continuous_norm.comp_continuousOn hMc)
  have hWn : ContinuousOn (fun b : α => ((‖W (f b)‖ : ℝ) : ℂ)) s :=
    Complex.ofRealCLM.continuous.comp_continuousOn (continuous_norm.comp_continuousOn hWc)
  have h1 : ContinuousOn (fun b : α => M (f b) / ((‖M (f b)‖ : ℝ) : ℂ)) s :=
    hMc.div hMn (fun b hb => by
      simpa using (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hMne b hb))))
  have h2 : ContinuousOn (fun b : α => W (f b) / ((‖W (f b)‖ : ℝ) : ℂ)) s :=
    hWc.div hWn (fun b hb => by
      simpa using (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hWne b hb))))
  exact h2.mul (h1.star)

/-- **The null-homotopy witness of the band loop.**

For the descended chord data `(M, W)` of `Work.Drive.chordWideAnnulusDescent` (its value clauses and
band estimates are the hypotheses here), the geometric input `Work.Drive.WrapData γ` produces a
continuous *unit-valued* `G` on the disc `‖x‖ ≤ 1/4` agreeing with the loop
`x ↦ c₀ · conj (w_h (x,τ₁))` on `‖x‖ ≥ 1/4`.  This is exactly the hypothesis
`Work.Drive.directionStabilization_of_nullhomotopic` consumes, i.e. the winding-zero condition
`deg w_h = ε − m = 0` of `PLANE_CHART_FINAL.md` §9.1. -/
theorem bandLoop_unit_extension (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hU : Submission.Drive.UmlaufProp) (hWrap : WrapData γ)
    {M W : ℂ × ℝ → ℂ} {c : ℝ}
    (hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hMval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 →
      M (x, τ) = dataMid γ x (Real.sqrt τ))
    (hWval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 →
      W (x, τ) = dchW γ (x, Real.sqrt τ))
    (hband : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 →
      ‖M (x, τ)‖ ^ 2 ≥ 2 * |τ| * ‖W (x, τ)‖ ^ 2)
    (hWne : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 → W (x, τ) ≠ 0)
    (hM0 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → M (x, 0) ≠ 0)
    (hW0 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → W (x, 0) ≠ 0)
    {τ₁ : ℝ} (hτ₁ : τ₁ < 0) (hτ₁c : -c ≤ τ₁)
    (hMneτ : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → M (x, τ₁) ≠ 0)
    (hWneτ : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → W (x, τ₁) ≠ 0)
    {c₀ : ℂ} (hc₀ : ‖c₀‖ = 1) :
    ∃ G : ℂ → ℂ, Continuous G ∧ (∀ x : ℂ, ‖x‖ ≤ 1 / 4 → ‖G x‖ = 1) ∧
      (∀ x : ℂ, 1 / 4 ≤ ‖x‖ → G x = c₀ * star (dirDatum M W (x, τ₁))) := by
  classical
  have hMval0 : ∀ x : ℂ, ‖x‖ = 1 → M (x, 0) = dataMid γ x 0 := fun x hx => by
    simpa using hMval x 0 le_rfl hx
  have hWval0 : ∀ x : ℂ, ‖x‖ = 1 → W (x, 0) = dchW γ (x, 0) := fun x hx => by
    simpa using hWval x 0 le_rfl hx
  have hMne1 : ∀ x : ℂ, ‖x‖ = 1 → M (x, 0) ≠ 0 := fun x hx =>
    hM0 x (by norm_num [hx]) (by norm_num [hx])
  have hWne1 : ∀ x : ℂ, ‖x‖ = 1 → W (x, 0) ≠ 0 := fun x hx =>
    hW0 x (by norm_num [hx]) (by norm_num [hx])
  obtain ⟨θ, hθc, hθper, hθ⟩ :=
    seam_periodic_argument γ hγ hγne hU hWrap hMsm hWsm hMval0 hWval0 hMne1 hWne1 hc₀
  set ρ : ℝ → ℝ := fun s => 1 - (3 / 4) * homClamp s with hρdef
  set τ : ℝ → ℝ := fun s => τ₁ * homClamp s with hτdef
  set f : ℝ × ℝ → ℂ × ℝ :=
    fun p => (ρ p.1 * Complex.exp ((p.2 : ℂ) * Complex.I), τ p.1) with hfdef
  have hρcont : Continuous ρ := by
    rw [hρdef]
    exact continuous_const.sub (continuous_const.mul homClamp_continuous)
  have hτcont : Continuous τ := by
    rw [hτdef]
    exact continuous_const.mul homClamp_continuous
  have hρle : ∀ s : ℝ, ρ s ≤ 1 := fun s => by
    have h := homClamp_nonneg s
    simp only [hρdef]
    linarith
  have hρge : ∀ s : ℝ, 1 / 4 ≤ ρ s := fun s => by
    have h := homClamp_le_one s
    simp only [hρdef]
    linarith
  have hρnonneg : ∀ s : ℝ, 0 ≤ ρ s := fun s => le_trans (by norm_num) (hρge s)
  have hρzero : ρ 0 = 1 := by
    simp only [hρdef, homClamp_zero le_rfl]
    norm_num
  have hρone : ∀ s : ℝ, 1 ≤ s → ρ s = 1 / 4 := fun s hs => by
    simp only [hρdef, homClamp_one hs]
    norm_num
  have hτzero : τ 0 = 0 := by simp only [hτdef, homClamp_zero le_rfl, mul_zero]
  have hτone : ∀ s : ℝ, 1 ≤ s → τ s = τ₁ := fun s hs => by
    simp only [hτdef, homClamp_one hs, mul_one]
  have hτge : ∀ s : ℝ, τ₁ ≤ τ s := fun s => by
    have h0 := homClamp_nonneg s
    have h1 := homClamp_le_one s
    simp only [hτdef]
    nlinarith [hτ₁]
  have hfzero : ∀ (s σ : ℝ), s ≤ 0 →
      f (s, σ) = (Complex.exp ((σ : ℂ) * Complex.I), 0) := by
    intro s σ hs
    show (ρ s * Complex.exp ((σ : ℂ) * Complex.I), τ s)
      = (Complex.exp ((σ : ℂ) * Complex.I), 0)
    rw [show ρ s = 1 from by simp only [hρdef, homClamp_zero hs]; norm_num,
      show τ s = 0 from by simp only [hτdef, homClamp_zero hs, mul_zero],
      Complex.ofReal_one, one_mul]
  have hfone : ∀ (s σ : ℝ), 1 ≤ s →
      f (s, σ) = ((((1 / 4 : ℝ)) : ℂ) * Complex.exp ((σ : ℂ) * Complex.I), τ₁) := by
    intro s σ hs
    show (ρ s * Complex.exp ((σ : ℂ) * Complex.I), τ s)
      = ((((1 / 4 : ℝ)) : ℂ) * Complex.exp ((σ : ℂ) * Complex.I), τ₁)
    rw [hρone s hs, hτone s hs]
  have hnorm_exp : ∀ σ : ℝ, ‖Complex.exp ((σ : ℂ) * Complex.I)‖ = 1 := fun σ => by
    rw [Complex.norm_exp]
    simp
  have hnorm_quarter : ∀ σ : ℝ,
      ‖((((1 / 4 : ℝ)) : ℂ)) * Complex.exp ((σ : ℂ) * Complex.I)‖ = 1 / 4 := by
    intro σ
    rw [norm_mul, hnorm_exp σ, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by norm_num)]
  have hxge : ∀ (s σ : ℝ), 1 / 4 ≤ ‖ρ s * Complex.exp ((σ : ℂ) * Complex.I)‖ := by
    intro s σ
    rw [norm_mul, hnorm_exp σ, mul_one, Complex.norm_real, Real.norm_of_nonneg (hρnonneg s)]
    exact hρge s
  have hxle : ∀ (s σ : ℝ), ‖ρ s * Complex.exp ((σ : ℂ) * Complex.I)‖ ≤ 2 := by
    intro s σ
    rw [norm_mul, hnorm_exp σ, mul_one, Complex.norm_real, Real.norm_of_nonneg (hρnonneg s)]
    linarith [hρle s]
  have hτs_neg : ∀ s : ℝ, 0 < s → τ s < 0 := by
    intro s hs
    have h1 := homClamp_nonneg s
    have h2 : homClamp s ≠ 0 := homClamp_ne_zero_of_pos hs
    simp only [hτdef]
    exact mul_neg_of_neg_of_pos hτ₁ (lt_of_le_of_ne h1 (Ne.symm h2))
  have hMne : ∀ p : ℝ × ℝ, M (f p) ≠ 0 := by
    rintro ⟨s, σ⟩
    rcases le_or_gt s 0 with hs | hs
    · rw [hfzero s σ hs]
      exact hM0 _ (by norm_num [hnorm_exp σ]) (by norm_num [hnorm_exp σ])
    · rcases le_or_gt 1 s with hs1 | hs1
      · have hne : M ((((1 / 4 : ℝ)) : ℂ) * Complex.exp ((σ : ℂ) * Complex.I), τ₁) ≠ 0 := by
          intro hzero
          have h := hband ((((1 / 4 : ℝ)) : ℂ) * Complex.exp ((σ : ℂ) * Complex.I)) τ₁
            (by rw [hnorm_quarter σ]) (by rw [hnorm_quarter σ]; norm_num) hτ₁c hτ₁
          rw [hzero, norm_zero] at h
          have hWnz : W ((((1 / 4 : ℝ)) : ℂ) * Complex.exp ((σ : ℂ) * Complex.I), τ₁) ≠ 0 :=
            hWne _ τ₁ (by rw [hnorm_quarter σ]) (by rw [hnorm_quarter σ]; norm_num) hτ₁c hτ₁
          have h2 : (0 : ℝ) < 2 * |τ₁| * ‖W ((((1 / 4 : ℝ)) : ℂ)
              * Complex.exp ((σ : ℂ) * Complex.I), τ₁)‖ ^ 2 := by
            have h3 : 0 < |τ₁| := abs_pos.mpr (ne_of_lt hτ₁)
            have h4 : 0 < ‖W ((((1 / 4 : ℝ)) : ℂ)
                * Complex.exp ((σ : ℂ) * Complex.I), τ₁)‖ := norm_pos_iff.mpr hWnz
            positivity
          linarith [h, h2]
        rwa [hfone s σ hs1]
      · intro hzero
        have h := hband (ρ s * Complex.exp ((σ : ℂ) * Complex.I)) (τ s) (hxge s σ) (hxle s σ)
          (le_trans hτ₁c (hτge s)) (hτs_neg s hs)
        rw [hzero, norm_zero] at h
        have hWnz : W (ρ s * Complex.exp ((σ : ℂ) * Complex.I), τ s) ≠ 0 :=
          hWne _ (τ s) (hxge s σ) (hxle s σ) (le_trans hτ₁c (hτge s)) (hτs_neg s hs)
        have h2 : (0 : ℝ) < 2 * |τ s| * ‖W (ρ s * Complex.exp ((σ : ℂ) * Complex.I), τ s)‖ ^ 2 := by
          have h3 : 0 < |τ s| := abs_pos.mpr (ne_of_lt (hτs_neg s hs))
          have h4 : 0 < ‖W (ρ s * Complex.exp ((σ : ℂ) * Complex.I), τ s)‖ :=
            norm_pos_iff.mpr hWnz
          positivity
        linarith [h, h2]
  have hWne' : ∀ p : ℝ × ℝ, W (f p) ≠ 0 := by
    rintro ⟨s, σ⟩
    rcases le_or_gt s 0 with hs | hs
    · rw [hfzero s σ hs]
      exact hW0 _ (by norm_num [hnorm_exp σ]) (by norm_num [hnorm_exp σ])
    · rcases le_or_gt 1 s with hs1 | hs1
      · have hne : W ((((1 / 4 : ℝ)) : ℂ) * Complex.exp ((σ : ℂ) * Complex.I), τ₁) ≠ 0 :=
          hWne _ τ₁ (by rw [hnorm_quarter σ]) (by rw [hnorm_quarter σ]; norm_num) hτ₁c hτ₁
        rwa [hfone s σ hs1]
      · exact hWne _ (τ s) (hxge s σ) (hxle s σ) (le_trans hτ₁c (hτge s)) (hτs_neg s hs)
  set F : ℝ → ℝ → ℂ := fun s σ => c₀ * star (dirDatum M W (f (s, σ))) with hFdef
  have hfc : Continuous f := by
    show Continuous fun p : ℝ × ℝ =>
      (ρ p.1 * Complex.exp ((p.2 : ℂ) * Complex.I), τ p.1)
    have h1 : Continuous fun p : ℝ × ℝ => ((p.2 : ℂ) * Complex.I) :=
      (Complex.ofRealCLM.continuous.comp continuous_snd).mul
        (continuous_const : Continuous fun _ : ℝ × ℝ => Complex.I)
    have h2 : Continuous fun p : ℝ × ℝ => Complex.exp ((p.2 : ℂ) * Complex.I) :=
      Complex.continuous_exp.comp h1
    have h3 : Continuous fun p : ℝ × ℝ =>
        (((ρ p.1 : ℝ)) : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) :=
      (Complex.ofRealCLM.continuous.comp (hρcont.comp continuous_fst)).mul h2
    exact h3.prodMk (hτcont.comp continuous_fst)
  have hdir : Continuous fun p : ℝ × ℝ => dirDatum M W (f p) :=
    continuous_dirDatum_comp hMsm hWsm hfc (fun p => hMne p) (fun p => hWne' p)
  have hFc : Continuous fun p : ℝ × ℝ => F p.1 p.2 := by
    rw [hFdef]
    exact continuous_const.mul (continuous_star.comp hdir)
  have hFun : ∀ s σ : ℝ, ‖F s σ‖ = 1 := by
    intro s σ
    show ‖c₀ * star (dirDatum M W (f (s, σ)))‖ = 1
    rw [norm_mul, hc₀, norm_star, norm_dirDatum (hMne (s, σ)) (hWne' (s, σ)), mul_one]
  have hexp_shift : Complex.exp ((((2 * Real.pi : ℝ)) : ℂ) * Complex.I) = 1 := by
    rw [show ((((2 * Real.pi : ℝ)) : ℂ) * Complex.I)
      = ((1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
      Complex.exp_int_mul_two_pi_mul_I]
  have hFper : ∀ s : ℝ, Function.Periodic (F s) (2 * Real.pi) := by
    intro s σ
    show c₀ * star (dirDatum M W (f (s, σ + 2 * Real.pi)))
      = c₀ * star (dirDatum M W (f (s, σ)))
    congr 3
    show (ρ s * Complex.exp (((σ + 2 * Real.pi : ℝ) : ℂ) * Complex.I), τ s)
      = (ρ s * Complex.exp ((σ : ℂ) * Complex.I), τ s)
    rw [show (((σ + 2 * Real.pi : ℝ) : ℂ)) * Complex.I
        = ((σ : ℂ) * Complex.I) + ((((2 * Real.pi : ℝ)) : ℂ) * Complex.I) by push_cast; ring,
      Complex.exp_add, hexp_shift, mul_one]
  have hF0 : ∀ σ : ℝ, Complex.exp (((θ σ : ℝ) : ℂ) * Complex.I) = F 0 σ := by
    intro σ
    show Complex.exp (((θ σ : ℝ) : ℂ) * Complex.I) = c₀ * star (dirDatum M W (f (0, σ)))
    rw [hfzero 0 σ le_rfl]
    exact hθ σ
  obtain ⟨ψ, hψc, hψper, hψ⟩ :=
    periodic_argument_of_homotopy F hFc hFun hFper hθc hθper hF0
  have hsm : ContinuousOn (fun x : ℂ => (x, τ₁)) {x : ℂ | 1 / 4 ≤ ‖x‖} :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hLc : ContinuousOn (fun x : ℂ => c₀ * star (dirDatum M W (x, τ₁)))
      {x : ℂ | 1 / 4 ≤ ‖x‖} :=
    continuousOn_const.mul (continuous_star.continuousOn.comp
      (continuousOn_dirDatum_comp hMsm hWsm hsm
        (fun x hx => hMneτ x hx) (fun x hx => hWneτ x hx))
      (fun x _ => Set.mem_univ _))
  have hL : ∀ x : ℂ, ‖x‖ = 1 / 4 → c₀ * star (dirDatum M W (x, τ₁))
      = Complex.exp (((ψ (Complex.arg x) : ℝ) : ℂ) * Complex.I) := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, norm_zero] at hx
      norm_num at hx
    have h1 : x = (((1 / 4 : ℝ)) : ℂ) * Complex.exp (((Complex.arg x : ℝ) : ℂ) * Complex.I) := by
      have hc : ((((1 / 4 : ℝ)) : ℂ)) ≠ 0 := by norm_num
      rw [exp_arg_eq_div x hx0, hx]
      field_simp
    have h3 : F 1 (Complex.arg x) = c₀ * star (dirDatum M W (x, τ₁)) := by
      show c₀ * star (dirDatum M W (f (1, Complex.arg x)))
        = c₀ * star (dirDatum M W (x, τ₁))
      rw [hfone 1 (Complex.arg x) le_rfl, ← h1]
    rw [← h3, ← hψ]
  exact exists_unit_extension_of_periodic hψc hψper hLc hL

/-- **The direction stabiliser of the band, with the winding-zero input discharged.**

Composing `Work.Drive.bandLoop_unit_extension` (which produces the null-homotopy witness `G` from
`Work.Drive.WrapData γ`) with `Work.Drive.directionStabilization_of_nullhomotopic` turns the descent
data of the band into data whose direction datum is *constant* at the level `τ₁`.  This is the full
content of §9.2 of `PLANE_CHART_FINAL.md`, with no hypothesis left beyond the descent's own clauses
and the (pointwise) non-vanishing of the two data on the half-band `τ ≤ 0`, `1/4 ≤ ‖x‖`.

(The non-vanishing on the whole half-band is what `Work.Drive.chordWideAnnulusDescent` provides on
`1/4 ≤ ‖x‖ ≤ 2`; the plane chart evaluates the data only on the image of the closed unit disk, so the
hypothesis used by the chart is the restricted one.  The unrestricted form is stated here because it is
the form the device `Work.Drive.directionStabilization_of_nullhomotopic` consumes.) -/
theorem directionStabilization_of_descent (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hU : Submission.Drive.UmlaufProp) (hWrap : WrapData γ)
    {M W : ℂ × ℝ → ℂ} {c c₀ : ℂ}
    (hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hc₀ : ‖c₀‖ = 1)
    (hMval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 →
      M (x, τ) = dataMid γ x (Real.sqrt τ))
    (hWval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 →
      W (x, τ) = dchW γ (x, Real.sqrt τ))
    {cR : ℝ} (hband : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -cR ≤ τ → τ < 0 →
      ‖M (x, τ)‖ ^ 2 ≥ 2 * |τ| * ‖W (x, τ)‖ ^ 2)
    (hWne : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -cR ≤ τ → τ < 0 → W (x, τ) ≠ 0)
    (hM0 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → M (x, 0) ≠ 0)
    (hW0 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → W (x, 0) ≠ 0)
    (hMh : ∀ p : ℂ × ℝ, p.2 ≤ 0 → 1 / 4 ≤ ‖p.1‖ → M p ≠ 0)
    (hWh : ∀ p : ℂ × ℝ, p.2 ≤ 0 → 1 / 4 ≤ ‖p.1‖ → W p ≠ 0)
    {τ₁ : ℝ} (hτ₁ : τ₁ < 0) (hτ₁c : -cR ≤ τ₁) :
    ∃ W' : ℂ × ℝ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W' ∧
      (∀ p : ℂ × ℝ, 0 ≤ p.2 → W' p = W p) ∧
      (∀ p : ℂ × ℝ, p.2 ≤ 0 → 1 / 4 ≤ ‖p.1‖ → W' p ≠ 0) ∧
      (∀ p : ℂ × ℝ, p.2 ≤ 0 → 1 / 4 ≤ ‖p.1‖ → ‖W' p‖ = ‖W p‖) ∧
      (∀ x : ℂ, 1 / 2 ≤ ‖x‖ → dirDatum M W' (x, τ₁) = c₀) := by
  obtain ⟨G, hGc, hG1, hG2⟩ :=
    bandLoop_unit_extension γ hγ hγne hU hWrap hMsm hWsm hMval hWval hband hWne hM0 hW0
      hτ₁ hτ₁c (fun x hx => hMh (x, τ₁) hτ₁.le hx) (fun x hx => hWh (x, τ₁) hτ₁.le hx) hc₀
  exact directionStabilization_of_nullhomotopic M W hMsm hWsm hMh hWh hτ₁ c₀ hc₀
    ⟨G, hGc, hG1, hG2⟩

end

end Work.Drive
