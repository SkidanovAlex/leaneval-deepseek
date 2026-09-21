import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Smooth.Q_regularity
import Submission.Work.OddVolterra.Abel.abel_transform_diff
import Submission.Work.OddVolterra.Smooth.E1_E2_regularity

/-!
# `Ξ` is `C^∞` near the anchor window

`Ξ n h s = (profileX 1, profileX 1, Q̃(s) 0, Q̃(s) 1)` where `Q̃` is the derivative of the Abel
transform of the Cauchy datum `Q n h`:

`Q̃(s) i = deriv (fun u => ∫ v in u..1, (Q n h v) i / √(v-u)) s`.

The first two components are constant; the last two are the *derivative of the Abel transform*
of a function `f : ℝ → ℝ` which is
* `C^∞` on `(0,1)` (`Work.OddVolterra.Existence.E1_E2_contDiff` for the two inhomogeneities
  `E₁`, `E₂` plus the smooth `momentRHS`), and
* continuous on `[1/4,1]` (`Work.OddVolterra.Smooth.E1_E2_regularity`).

The Abel transform `A(x) = ∫_x^1 (√(v-x))⁻¹ f v dv` is handled by splitting at a fixed slope
`c = 972/1000 ∈ (0,1)`, *strictly above* the window `V = (48/100, 971/1000)` on which we work
but strictly below `1`:

* the **head** `∫_x^c (√(v-x))⁻¹ f v dv`: the substitution `v = x + (c-x)u²` turns it into
  `2√(c-x) · ∫_0^1 f (x + (c-x)u²) du`, a parametric integral over the *fixed* window `[0,1]`
  of a jointly smooth function (`c < 1` is what gives room for the open tube in `u`), so
  `Work.OddVolterra.Smooth.Alt.contDiffAt_integral_of_contDiffOn` applies;
* the **tail** `∫_c^1 (√(v-x))⁻¹ f v dv`: here `v - x ≥ c - x > 0` throughout, so the only
  `x`-dependence is through the kernel and `f` is only ever evaluated *inside* `[c,1]`.  The
  family `A_k(x) = ∫_c^1 ((√(v-x))⁻¹)^{2k+1} f v dv` satisfies `A_k' = ((2k+1)/2) A_{k+1}`
  (differentiation under the integral sign, the dominating function being a constant since
  `|f|` is bounded on the compact `[c,1]`), which bootstraps to `C^∞`.

Both halves are proved here in general form (`abelTail_contDiffOn`, `abelHead_contDiffOn`) and
then instantiated at `f = (Q n h) i`, `c = 972/1000`, `V = (48/100, 971/1000)`, the numeric
inclusions being `XiAux.map_mem` and friends.
-/

namespace Work.Anchor

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

namespace XiAux

/-! ## The two halves of the Abel transform -/

/-- The relevant slice of the kernel `(√(v-u))⁻¹` is continuous in `v` once `u < c`. -/
lemma abelKernel_cont {m : ℕ} {c u : ℝ} (hu : u < c) :
    ContinuousOn (fun v : ℝ => ((Real.sqrt (v - u))⁻¹) ^ m) (Set.Icc c 1) := by
  have h1 : ContinuousOn (fun v : ℝ => Real.sqrt (v - u)) (Set.Icc c 1) :=
    Real.continuous_sqrt.comp_continuousOn ((continuous_id.sub continuous_const).continuousOn)
  have hne : ∀ v ∈ Set.Icc c 1, Real.sqrt (v - u) ≠ 0 := by
    intro v hv
    exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hv.1]))
  exact (h1.inv₀ hne).pow m

/-- The `x`-derivative of the `(2k+1)`-st power of the inverse square root. -/
lemma abelKernel_hasDerivAt (k : ℕ) {t x : ℝ} (hx : x < t) :
    HasDerivAt (fun y : ℝ => ((Real.sqrt (t - y))⁻¹) ^ (2 * k + 1))
      (((2 * k + 1 : ℕ) : ℝ) / 2 * ((Real.sqrt (t - x))⁻¹) ^ (2 * k + 3)) x := by
  have hpos : 0 < t - x := sub_pos.mpr hx
  have hsqrt : Real.sqrt (t - x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  have h1 : HasDerivAt (fun y : ℝ => t - y) (-1) x := (hasDerivAt_id x).const_sub t
  have h2 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (t - x))) (t - x) :=
    Real.hasDerivAt_sqrt (ne_of_gt hpos)
  have h3 : HasDerivAt (fun y : ℝ => Real.sqrt (t - y))
      ((-1) * (1 / (2 * Real.sqrt (t - x)))) x := by
    have hh := h2.comp x h1
    simpa [Function.comp_def, mul_comm] using hh
  have h4val : -((-1) * (1 / (2 * Real.sqrt (t - x)))) / (Real.sqrt (t - x)) ^ 2
      = 1 / (2 * (Real.sqrt (t - x) * Real.sqrt (t - x)) * Real.sqrt (t - x)) := by
    field_simp
  have h4 : HasDerivAt (fun y : ℝ => (Real.sqrt (t - y))⁻¹)
      (1 / (2 * (Real.sqrt (t - x) * Real.sqrt (t - x)) * Real.sqrt (t - x))) x :=
    h4val ▸ h3.inv hsqrt
  have h5 : HasDerivAt ((fun y : ℝ => (Real.sqrt (t - y))⁻¹) ^ (2 * k + 1))
      (((2 * k + 1 : ℕ) : ℝ) * ((Real.sqrt (t - x))⁻¹) ^ (2 * k + 1 - 1)
        * (1 / (2 * (Real.sqrt (t - x) * Real.sqrt (t - x)) * Real.sqrt (t - x)))) x :=
    h4.pow (2 * k + 1)
  have hval : ((2 * k + 1 : ℕ) : ℝ) * ((Real.sqrt (t - x))⁻¹) ^ (2 * k + 1 - 1)
        * (1 / (2 * (Real.sqrt (t - x) * Real.sqrt (t - x)) * Real.sqrt (t - x)))
      = ((2 * k + 1 : ℕ) : ℝ) / 2 * ((Real.sqrt (t - x))⁻¹) ^ (2 * k + 3) := by
    have hker : ((2 * k + 1 : ℕ) : ℝ) * (Real.sqrt (t - x))⁻¹ ^ (2 * k)
        * (1 / (2 * Real.sqrt (t - x) * Real.sqrt (t - x) * Real.sqrt (t - x)))
        = ((2 * k + 1 : ℕ) : ℝ) / 2 * (Real.sqrt (t - x))⁻¹ ^ (2 * k + 3) := by
      rw [show 2 * k + 3 = (2 * k) + 3 by omega, pow_add]
      field_simp
    rw [show 2 * k + 1 - 1 = 2 * k by omega]
    simpa [mul_assoc] using hker
  rw [← hval]
  exact h5

/-- The `k`-th member of the tail family `∫_c^1 ((√(v-·))⁻¹)^{2k+1} f v dv`. -/
def abelTailFamily (c : ℝ) (f : ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  fun x => ∫ v in c..1, ((Real.sqrt (v - x))⁻¹) ^ (2 * k + 1) * f v

/-- Differentiation under the integral sign for the tail family. -/
lemma abelTail_hasDerivAt (k : ℕ) {c : ℝ} (hc : c ≤ 1) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc c 1)) {x : ℝ} (hx : x < c) :
    HasDerivAt (fun u : ℝ => ∫ v in c..1, ((Real.sqrt (v - u))⁻¹) ^ (2 * k + 1) * f v)
      (((2 * k + 1 : ℕ) : ℝ) / 2 *
        ∫ v in c..1, ((Real.sqrt (v - x))⁻¹) ^ (2 * k + 3) * f v) x := by
  have huIoc : ∀ v : ℝ, v ∈ Set.uIoc c 1 → v ∈ Set.Icc c 1 := by
    intro v hv
    rw [Set.uIoc_of_le hc] at hv
    exact ⟨hv.1.le, hv.2⟩
  set δ : ℝ := (c - x) / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδc : ∀ u ∈ Metric.ball x δ, u < c - δ := by
    intro u hu
    rw [Metric.mem_ball, Real.dist_eq] at hu
    have h1 : u < x + δ := by have := (abs_lt.mp hu).2; linarith
    have h2 : x + δ = c - δ := by rw [hδdef]; ring
    linarith
  have hdu : ∀ u ∈ Metric.ball x δ, ∀ v ∈ Set.Icc c 1, δ ≤ v - u := by
    intro u hu v hv
    have h1 := hδc u hu
    linarith [hv.1]
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hMabs : ∀ v ∈ Set.Icc c 1, |f v| ≤ M := by
    intro v hv
    simpa [Real.norm_eq_abs] using hM v hv
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hMabs c ⟨le_rfl, hc⟩)
  set A : ℝ := ((2 * k + 1 : ℕ) : ℝ) / 2 with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  set C : ℝ := ((Real.sqrt δ)⁻¹) ^ (2 * k + 3) * M * A with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    exact mul_nonneg (mul_nonneg (by positivity) hM0) hA0
  have hF_meas : ∀ᶠ u in 𝓝 x,
      AEStronglyMeasurable (fun v : ℝ => ((Real.sqrt (v - u))⁻¹) ^ (2 * k + 1) * f v)
        (volume.restrict (Set.uIoc c 1)) := by
    filter_upwards [Metric.ball_mem_nhds x hδpos] with u hu
    have huc : u < c := lt_of_lt_of_le (hδc u hu) (by linarith)
    have h1 : ContinuousOn (fun v : ℝ => ((Real.sqrt (v - u))⁻¹) ^ (2 * k + 1))
        (Set.uIoc c 1) :=
      (abelKernel_cont (m := 2 * k + 1) huc).mono (fun v hv => huIoc v hv)
    exact (h1.mul (hf.mono (fun v hv => huIoc v hv))).aestronglyMeasurable measurableSet_uIoc
  have hF_int : IntervalIntegrable (fun v : ℝ => ((Real.sqrt (v - x))⁻¹) ^ (2 * k + 1) * f v)
      volume c 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hc]
    exact (abelKernel_cont (m := 2 * k + 1) hx).mul hf
  have hF'_meas : AEStronglyMeasurable
      (fun v : ℝ => ((Real.sqrt (v - x))⁻¹) ^ (2 * k + 3) * f v * A)
      (volume.restrict (Set.uIoc c 1)) := by
    have h1 : ContinuousOn (fun v : ℝ => ((Real.sqrt (v - x))⁻¹) ^ (2 * k + 3) * f v)
        (Set.uIoc c 1) :=
      ((abelKernel_cont (m := 2 * k + 3) hx).mono (fun v hv => huIoc v hv)).mul
        (hf.mono (fun v hv => huIoc v hv))
    exact (h1.mul continuousOn_const).aestronglyMeasurable measurableSet_uIoc
  have h_bound : ∀ᵐ v ∂volume, v ∈ Set.uIoc c 1 →
      ∀ u ∈ Metric.ball x δ,
        ‖((Real.sqrt (v - u))⁻¹) ^ (2 * k + 3) * f v * A‖ ≤ (fun _ => C) v := by
    filter_upwards with v hv u hu
    have hvI : v ∈ Set.Icc c 1 := huIoc v hv
    have hdv : δ ≤ v - u := hdu u hu v hvI
    have hle1 : (Real.sqrt (v - u))⁻¹ ≤ (Real.sqrt δ)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hδpos) (Real.sqrt_le_sqrt hdv)
    have hle2 : ((Real.sqrt (v - u))⁻¹) ^ (2 * k + 3) ≤ ((Real.sqrt δ)⁻¹) ^ (2 * k + 3) :=
      pow_le_pow_left₀ (by positivity) hle1 _
    have hkn : ‖((Real.sqrt (v - u))⁻¹) ^ (2 * k + 3)‖ = ((Real.sqrt (v - u))⁻¹) ^ (2 * k + 3) := by
      rw [Real.norm_eq_abs, abs_of_nonneg]; positivity
    calc ‖((Real.sqrt (v - u))⁻¹) ^ (2 * k + 3) * f v * A‖
        = ((Real.sqrt (v - u))⁻¹) ^ (2 * k + 3) * |f v| * A := by
          rw [norm_mul, norm_mul, hkn, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hA0]
      _ ≤ ((Real.sqrt δ)⁻¹) ^ (2 * k + 3) * M * A := by
          apply mul_le_mul_of_nonneg_right _ hA0
          exact mul_le_mul hle2 (hMabs v hvI) (abs_nonneg _) (by positivity)
      _ = C := by rw [hCdef]
  have h_diff : ∀ᵐ v ∂volume, v ∈ Set.uIoc c 1 →
      ∀ u ∈ Metric.ball x δ,
        HasDerivAt (fun y : ℝ => ((Real.sqrt (v - y))⁻¹) ^ (2 * k + 1) * f v)
          (((Real.sqrt (v - u))⁻¹) ^ (2 * k + 3) * f v * A) u := by
    filter_upwards with v hv u hu
    have hvI : v ∈ Set.Icc c 1 := huIoc v hv
    have huv : u < v := by have := hdu u hu v hvI; linarith [hδpos]
    have h := (abelKernel_hasDerivAt k huv).mul_const (f v)
    have hvv : ((2 * k + 1 : ℕ) : ℝ) / 2 * ((Real.sqrt (v - u))⁻¹) ^ (2 * k + 3) * f v
        = ((Real.sqrt (v - u))⁻¹) ^ (2 * k + 3) * f v * A := by
      rw [hAdef]; ring
    rwa [hvv] at h
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := c) (b := 1) (bound := fun _ => C)
    (F := fun u v => ((Real.sqrt (v - u))⁻¹) ^ (2 * k + 1) * f v)
    (F' := fun u v => ((Real.sqrt (v - u))⁻¹) ^ (2 * k + 3) * f v * A)
    (x₀ := x) (s := Metric.ball x δ)
    (Metric.ball_mem_nhds x hδpos) hF_meas hF_int hF'_meas h_bound
    intervalIntegrable_const h_diff
  have hpush : (∫ v in c..1, (((Real.sqrt (v - x))⁻¹) ^ (2 * k + 3) * f v * A))
      = A * ∫ v in c..1, ((Real.sqrt (v - x))⁻¹) ^ (2 * k + 3) * f v := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun v _ => by ring)
  rw [hpush, hAdef] at hmain
  exact hmain.2

/-- The same statement in terms of `abelTailFamily`. -/
lemma abelTailFamily_hasDerivAt (k : ℕ) {c : ℝ} (hc : c ≤ 1) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc c 1)) {x : ℝ} (hx : x < c) :
    HasDerivAt (abelTailFamily c f k)
      (((2 * k + 1 : ℕ) : ℝ) / 2 * abelTailFamily c f (k + 1) x) x := by
  have h := abelTail_hasDerivAt k hc hf hx
  have hexp : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
  unfold abelTailFamily
  rw [hexp]
  exact h

/-- **The tail of the Abel transform of a function continuous on `[c,1]` is `C^∞` below `c`.** -/
lemma abelTail_contDiffOn {c : ℝ} (hc : c ≤ 1) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc c 1)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => ∫ v in c..1, (Real.sqrt (v - x))⁻¹ * f v)
      (Set.Iio c) := by
  have hCD : ∀ k j : ℕ, ContDiffOn ℝ ((k : ℕ) : ℕ∞) (abelTailFamily c f j) (Set.Iio c) := by
    intro k
    induction k with
    | zero =>
      intro j
      refine contDiffOn_zero.mpr ?_
      exact DifferentiableOn.continuousOn
        (fun x hx => (abelTailFamily_hasDerivAt j hc hf hx).differentiableAt.differentiableWithinAt)
    | succ k ih =>
      intro j
      have hcast : (((k + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) = (((k : ℕ) : ℕ∞) : WithTop ℕ∞) + 1 := by
        simp only [Nat.cast_succ, WithTop.coe_add, WithTop.coe_one]
      rw [hcast, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Iio]
      refine ⟨fun x hx => (abelTailFamily_hasDerivAt j hc hf hx).differentiableAt.differentiableWithinAt,
        ?_, ?_⟩
      · intro htop; exact absurd htop (by simp)
      · refine ((contDiffOn_const (c := (((2 * j + 1 : ℕ) : ℝ) / 2))).mul (ih (j + 1))).congr
          (fun x hx => ?_)
        exact (abelTailFamily_hasDerivAt j hc hf hx).deriv
  rw [contDiffOn_iff_forall_nat_le]
  intro m _
  exact (hCD m 0).congr (fun x _ => by simp [abelTailFamily])

/-- **The head of the Abel transform is `C^∞`.**  `W` is the open set on which `f` is smooth,
`O` the open set of parameters, `J` an open neighbourhood of `[0,1]` (inside which the
substitution path `u ↦ x + (c-x)u²` must stay in `W`). -/
lemma abelHead_contDiffOn {c : ℝ} {W J O : Set ℝ} {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f W)
    (hJ : IsOpen J) (hJ01 : ∀ u ∈ Set.Icc (0 : ℝ) 1, u ∈ J)
    (hO : IsOpen O) (hOc : ∀ x ∈ O, x < c)
    (hmap : ∀ x ∈ O, ∀ u ∈ J, x + (c - x) * u ^ 2 ∈ W) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => ∫ v in x..c, (Real.sqrt (v - x))⁻¹ * f v) O := by
  intro x₀ hx₀
  have hx₀c : x₀ < c := hOc x₀ hx₀
  set F : ℝ × ℝ → ℝ := fun p => f (p.1 + (c - p.1) * p.2 ^ 2) with hFdef
  have hFcd : ContDiffOn ℝ (⊤ : ℕ∞) F (O ×ˢ J) := by
    have hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => p.1 + (c - p.1) * p.2 ^ 2) (O ×ˢ J) := by
      fun_prop
    exact hf.comp hg (fun p hp => hmap p.1 hp.1 p.2 hp.2)
  have hseg : ∀ u ∈ Set.uIcc (0 : ℝ) 1, (x₀, u) ∈ O ×ˢ J := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    exact ⟨hx₀, hJ01 u hu⟩
  have hcd : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => ∫ u in (0 : ℝ)..1, F (x, u)) x₀ :=
    Work.OddVolterra.Smooth.Alt.contDiffAt_integral_of_contDiffOn (hO.prod hJ) hFcd hseg
  have hsqrt : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => 2 * Real.sqrt (c - x)) x₀ := by
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => c - x) x₀ := contDiffAt_const.sub contDiffAt_id
    exact contDiffAt_const.mul (h1.sqrt (by simp [sub_ne_zero.mpr hx₀c.ne']))
  have hgoal : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : ℝ => 2 * Real.sqrt (c - x) * ∫ u in (0 : ℝ)..1, F (x, u)) x₀ :=
    hsqrt.mul hcd
  have hev : (fun x : ℝ => ∫ v in x..c, (Real.sqrt (v - x))⁻¹ * f v) =ᶠ[𝓝 x₀]
      (fun x : ℝ => 2 * Real.sqrt (c - x) * ∫ u in (0 : ℝ)..1, F (x, u)) := by
    filter_upwards [hO.mem_nhds hx₀] with x hx
    have hxc : x < c := hOc x hx
    have hsub := Commons.Analysis.Abel.intervalIntegral_abel_subst (x := x) (b := c)
      (le_of_lt hxc) (fun _ v => f v)
    simpa [F, smul_eq_mul] using hsub
  exact (hgoal.congr_of_eventuallyEq hev).contDiffWithinAt

/-! ## The numerical window -/

/-- The slope at which the Abel transform is split. -/
def cSplit : ℝ := 972 / 1000

/-- Lower end of the working window. -/
def vLo : ℝ := 48 / 100

/-- Upper end of the working window. -/
def vHi : ℝ := 971 / 1000

/-- The open set of parameters on which everything is proved. -/
def workSet : Set ℝ := Set.Ioo vLo vHi

/-- The target window of the statement. -/
def targetSet : Set ℝ := Set.Ioo (481 / 1000) (97 / 100)

/-- The window of the substitution variable `u`, an open neighbourhood of `[0,1]`. -/
def uWindow : Set ℝ := Set.Ioo (-(1 / 2)) (102 / 100)

/-- The open set on which `Q n h` is `C^∞`. -/
def smoothWindow : Set ℝ := Set.Ioo (0 : ℝ) 1

lemma cSplit_le_one : cSplit ≤ 1 := by norm_num [cSplit]

lemma cSplit_lt_one : cSplit < 1 := by norm_num [cSplit]

lemma isOpen_uWindow : IsOpen uWindow := isOpen_Ioo

lemma isOpen_workSet : IsOpen workSet := isOpen_Ioo

lemma isOpen_smoothWindow : IsOpen smoothWindow := isOpen_Ioo

lemma uWindow_mem : ∀ u ∈ Set.Icc (0 : ℝ) 1, u ∈ uWindow := by
  intro u hu
  rw [uWindow]
  exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

lemma quarter_le_cSplit : (1 / 4 : ℝ) ≤ cSplit := by norm_num [cSplit]

lemma workSet_lt_cSplit : ∀ x ∈ workSet, x < cSplit := by
  intro x hx
  rw [workSet, vLo, vHi] at hx
  rw [cSplit]
  linarith [hx.2]

lemma workSet_subset_Iio : workSet ⊆ Set.Iio cSplit := fun x hx => workSet_lt_cSplit x hx

lemma target_subset_workSet : targetSet ⊆ workSet := by
  intro x hx
  rw [targetSet] at hx
  rw [workSet, vLo, vHi]
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- The substitution path `u ↦ x + (c-x)u²` maps the working window times `uWindow` into
`(0,1)`.  This is where all the numeric content of the lemma is concentrated. -/
lemma map_mem {x u : ℝ} (hx : x ∈ workSet) (hu : u ∈ uWindow) :
    x + (cSplit - x) * u ^ 2 ∈ smoothWindow := by
  rw [workSet, vLo, vHi] at hx
  rw [uWindow] at hu
  rw [smoothWindow, cSplit]
  have hx1 : (48 : ℝ) / 100 < x := hx.1
  have hx2 : x < 971 / 1000 := hx.2
  have hux : u ^ 2 < 10404 / 10000 := by
    have h1 : u < 102 / 100 := hu.2
    have h2 : -(102 / 100) < u := by linarith [hu.1]
    nlinarith
  constructor
  · have h : 0 ≤ ((972 : ℝ) / 1000 - x) * u ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg u)
    linarith
  · by_cases hu2 : u ^ 2 ≤ 1
    · have hprod : 0 ≤ ((972 : ℝ) / 1000 - x) * (1 - u ^ 2) :=
        mul_nonneg (by linarith) (by linarith)
      have hle : x + ((972 : ℝ) / 1000 - x) * u ^ 2 ≤ 972 / 1000 := by nlinarith
      linarith
    · have hu2' : (1 : ℝ) < u ^ 2 := not_le.mp hu2
      have hprod : 0 ≤ (x - (48 : ℝ) / 100) * (u ^ 2 - 1) :=
        mul_nonneg (by linarith) (by linarith)
      have hb : x + ((972 : ℝ) / 1000 - x) * u ^ 2
          < 48 / 100 + (972 / 1000 - 48 / 100) * (10404 / 10000) := by nlinarith
      have hnum : (48 : ℝ) / 100 + (972 / 1000 - 48 / 100) * (10404 / 10000) < 1 := by
        norm_num
      linarith

end XiAux

open XiAux

/-- **Smoothness of the paper's source `Ξ` near the anchor window.** -/
theorem Xi_contDiffOn (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => Work.OddVolterra.Xi n h s)
      (Set.Ioo (481 / 1000) (97 / 100)) := by
  -- the pointwise bound on `h`
  have hsmall' : ∀ t : ℝ, |h t| ≤ 1 / 100 := by
    intro t
    have h0 := hsmall 0 (by norm_num) t
    rwa [iteratedDeriv_zero] at h0
  -- the radicand is positive on the ball's sections
  have hmid : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1)) (Commons.Geometry.Ulam.profileX 1),
      0 < Work.OddVolterra.psi h Commons.Geometry.Ulam.semicircle s t := by
    intro s hs t ht
    have ht' : |t| ≤ Commons.Geometry.Ulam.profileX 1 := by
      rw [abs_le]
      exact ⟨by linarith [ht.1], ht.2⟩
    exact Work.OddVolterra.Smooth.psi_pos_of_window hsupp hsmall' hs.1 hs.2 ht'
  -- `Q n h` is smooth on `(0,1)` and continuous on `[1/4,1]`
  have hQcont : ContinuousOn (Work.OddVolterra.Q n h) (Set.Icc (1 / 4 : ℝ) 1) :=
    (Work.OddVolterra.Smooth.Q_regularity n hn hh (by norm_num) hsupp hsmall' hmid).1
  have hQsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (Work.OddVolterra.Q n h) (Set.Ioo (0 : ℝ) 1) := by
    obtain ⟨hE1, hE2⟩ := Work.OddVolterra.Existence.E1_E2_contDiff n hn hh hmid
    have hRHS : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun s : ℝ => iteratedDeriv (n + 1) (Work.OddVolterra.momentRHS n) s)
        (Set.Ioo (0 : ℝ) 1) :=
      (Work.OddVolterra.Smooth.Qreg_contDiffOn_iteratedDeriv_momentRHS n).mono (Set.subset_univ _)
    rw [contDiffOn_pi]
    intro i
    fin_cases i
    · simpa [Work.OddVolterra.Q] using hE1.neg.add hRHS
    · simpa [Work.OddVolterra.Q] using hE2.neg
  -- componentwise versions
  have hf_smooth : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v : ℝ => (Work.OddVolterra.Q n h v) i) (Set.Ioo (0 : ℝ) 1) :=
    fun i => (contDiffOn_pi.mp hQsmooth) i
  have hf_cont : ∀ i : Fin 2, ContinuousOn (fun v : ℝ => (Work.OddVolterra.Q n h v) i)
      (Set.Icc (1 / 4 : ℝ) 1) :=
    fun i => (continuousOn_pi.mp hQcont) i
  have hf_cont_tail : ∀ i : Fin 2, ContinuousOn (fun v : ℝ => (Work.OddVolterra.Q n h v) i)
      (Set.Icc cSplit 1) := by
    intro i
    refine (hf_cont i).mono ?_
    intro v hv
    exact ⟨by linarith [hv.1, quarter_le_cSplit], hv.2⟩
  -- the Abel transform of each component is `C^∞` on the working window
  have hG : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u : ℝ => ∫ v in u..1, (Work.OddVolterra.Q n h v) i / Real.sqrt (v - u)) workSet := by
    intro i
    have hhead : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun x : ℝ => ∫ v in x..cSplit, (Real.sqrt (v - x))⁻¹ * (Work.OddVolterra.Q n h v) i)
        workSet :=
      abelHead_contDiffOn (hf_smooth i) isOpen_uWindow uWindow_mem isOpen_workSet
        (fun x hx => workSet_lt_cSplit x hx)
        (fun x hx u hu => map_mem hx hu)
    have htail : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun x : ℝ => ∫ v in cSplit..1, (Real.sqrt (v - x))⁻¹ * (Work.OddVolterra.Q n h v) i)
        workSet :=
      (abelTail_contDiffOn cSplit_le_one (hf_cont_tail i)).mono workSet_subset_Iio
    refine (hhead.add htail).congr (fun x hx => ?_)
    have hxc : x < cSplit := workSet_lt_cSplit x hx
    have hxpos : (1 / 4 : ℝ) ≤ x := by
      rw [workSet, vLo, vHi] at hx
      linarith [hx.1]
    have hI1 : IntervalIntegrable
        (fun v : ℝ => (Real.sqrt (v - x))⁻¹ * (Work.OddVolterra.Q n h v) i) volume x cSplit := by
      refine (Commons.Analysis.Abel.intervalIntegrable_invSqrt_sub hxc).smul_continuousOn ?_
      rw [Set.uIcc_of_le (le_of_lt hxc)]
      exact (hf_cont i).mono
        (fun v hv => ⟨by linarith [hv.1, hxpos], by linarith [hv.2, cSplit_le_one]⟩)
    have hI2 : IntervalIntegrable
        (fun v : ℝ => (Real.sqrt (v - x))⁻¹ * (Work.OddVolterra.Q n h v) i) volume cSplit 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le cSplit_le_one]
      exact ((abelKernel_cont (m := 1) hxc).mul (hf_cont_tail i)).congr
        (fun v _ => by simp [pow_one])
    rw [show (∫ v in x..1, (Work.OddVolterra.Q n h v) i / Real.sqrt (v - x))
        = ∫ v in x..1, (Real.sqrt (v - x))⁻¹ * (Work.OddVolterra.Q n h v) i from
        intervalIntegral.integral_congr (fun v _ => by rw [div_eq_mul_inv, mul_comm])]
    exact (intervalIntegral.integral_add_adjacent_intervals hI1 hI2).symm
  -- the `Ξ`-function, component by component
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun (s : ℝ) (i : Fin 4) => Work.OddVolterra.Xi n h s i)
    (Set.Ioo (481 / 1000) (97 / 100))
  rw [contDiffOn_pi]
  intro i
  fin_cases i
  · refine (contDiffOn_const (c := Commons.Geometry.Ulam.profileX 1)).congr (fun s _ => ?_)
    simp [Work.OddVolterra.Xi]
  · refine (contDiffOn_const (c := Commons.Geometry.Ulam.profileX 1)).congr (fun s _ => ?_)
    simp [Work.OddVolterra.Xi]
  · have hder := (hG 0).deriv_of_isOpen isOpen_workSet
      Work.OddVolterra.Smooth.top_coe_add_one_le
    refine (hder.mono target_subset_workSet).congr (fun s _ => ?_)
    simp [Work.OddVolterra.Xi, Work.OddVolterra.Qtilde]
  · have hder := (hG 1).deriv_of_isOpen isOpen_workSet
      Work.OddVolterra.Smooth.top_coe_add_one_le
    refine (hder.mono target_subset_workSet).congr (fun s _ => ?_)
    simp [Work.OddVolterra.Xi, Work.OddVolterra.Qtilde]

end

end Work.Anchor
