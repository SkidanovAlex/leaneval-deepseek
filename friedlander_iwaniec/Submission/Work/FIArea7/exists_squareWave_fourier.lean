import Mathlib
import Submission.Work.FIArea7.multEps_separation
import Submission.Work.FIArea7.smoothTransition_deriv_bounds
import Submission.Work.FIArea7.finset_sum_coeff_le

namespace Work.FIArea7

open MeasureTheory intervalIntegral Filter
open scoped Topology BigOperators

noncomputable section

/-! ## The smoothed square wave `t(x) = sign(cos x)` -/

/-- The threshold `β_R = 1 / R`. -/
noncomputable def sqBeta (R : ℕ) : ℝ := 1 / (R : ℝ)

/-- Smooth clamp in the `cos` variable: `clamp β v = 1` for `v ≥ β`, `= -1` for `v ≤ -β`. -/
noncomputable def clamp (β : ℝ) (v : ℝ) : ℝ :=
  2 * Real.smoothTransition ((v + β) / (2 * β)) - 1

/-- First derivative of `clamp`. -/
noncomputable def clampD (β : ℝ) (v : ℝ) : ℝ :=
  deriv Real.smoothTransition ((v + β) / (2 * β)) / β

/-- Second derivative of `clamp`. -/
noncomputable def clampDD (β : ℝ) (v : ℝ) : ℝ :=
  deriv (deriv Real.smoothTransition) ((v + β) / (2 * β)) / (2 * β ^ 2)

/-- The smoothed square wave. -/
noncomputable def sqWave (β : ℝ) (x : ℝ) : ℝ := clamp β (Real.cos x)

/-- Complex-valued smoothed square wave. -/
noncomputable def sqWaveC (β : ℝ) (x : ℝ) : ℂ := (sqWave β x : ℂ)

noncomputable def sqD1R (β : ℝ) (x : ℝ) : ℝ := clampD β (Real.cos x) * (-Real.sin x)

noncomputable def sqD2R (β : ℝ) (x : ℝ) : ℝ :=
  clampDD β (Real.cos x) * (Real.sin x) ^ 2 - clampD β (Real.cos x) * Real.cos x

noncomputable def sqD1 (β : ℝ) (x : ℝ) : ℂ := (sqD1R β x : ℂ)

noncomputable def sqD2 (β : ℝ) (x : ℝ) : ℂ := (sqD2R β x : ℂ)

/-! ## Vanishing of the derivatives of `smoothTransition` outside `(0,1)` -/

/-- A continuous function that vanishes on `(a, ∞)` vanishes at `a`. -/
lemma continuous_eq_zero_of_pos_side {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ)
    (h : ∀ y, a < y → f y = 0) : f a = 0 := by
  have h3 : Tendsto f (nhdsWithin a (Set.Ioi a)) (𝓝 (f a)) :=
    hf.continuousAt.tendsto.mono_left inf_le_left
  have h4 : Tendsto f (nhdsWithin a (Set.Ioi a)) (𝓝 0) := by
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact h y hy
  exact tendsto_nhds_unique h3 h4

/-- A continuous function that vanishes on `(-∞, b)` vanishes at `b`. -/
lemma continuous_eq_zero_of_neg_side {f : ℝ → ℝ} (hf : Continuous f) (b : ℝ)
    (h : ∀ y, y < b → f y = 0) : f b = 0 := by
  have h3 : Tendsto f (nhdsWithin b (Set.Iio b)) (𝓝 (f b)) :=
    hf.continuousAt.tendsto.mono_left inf_le_left
  have h4 : Tendsto f (nhdsWithin b (Set.Iio b)) (𝓝 0) := by
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact h y hy
  exact tendsto_nhds_unique h3 h4

lemma deriv_smoothTransition_eq_zero_of_one_lt {u : ℝ} (hu : 1 < u) :
    deriv Real.smoothTransition u = 0 := by
  have hev : Real.smoothTransition =ᶠ[𝓝 u] (fun _ => (1 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with y hy
    exact Real.smoothTransition.one_of_one_le hy.le
  rw [hev.deriv_eq, deriv_const]

lemma deriv_smoothTransition_eq_zero_of_neg {u : ℝ} (hu : u < 0) :
    deriv Real.smoothTransition u = 0 := by
  have hev : Real.smoothTransition =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hu] with y hy
    exact Real.smoothTransition.zero_of_nonpos hy.le
  rw [hev.deriv_eq, deriv_const]

lemma deriv_smoothTransition_eq_zero_of_one_le {u : ℝ} (hu : 1 ≤ u) :
    deriv Real.smoothTransition u = 0 := by
  rcases lt_or_eq_of_le hu with h | h
  · exact deriv_smoothTransition_eq_zero_of_one_lt h
  · rw [← h]
    exact continuous_eq_zero_of_pos_side (by fun_prop) 1
      (fun y hy => deriv_smoothTransition_eq_zero_of_one_lt hy)

lemma deriv_smoothTransition_eq_zero_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    deriv Real.smoothTransition u = 0 := by
  rcases lt_or_eq_of_le hu with h | h
  · exact deriv_smoothTransition_eq_zero_of_neg h
  · rw [h]
    exact continuous_eq_zero_of_neg_side (by fun_prop) 0
      (fun y hy => deriv_smoothTransition_eq_zero_of_neg hy)

lemma deriv2_smoothTransition_eq_zero_of_one_lt {u : ℝ} (hu : 1 < u) :
    deriv (deriv Real.smoothTransition) u = 0 := by
  have hev : deriv Real.smoothTransition =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with y hy
    exact deriv_smoothTransition_eq_zero_of_one_le hy.le
  rw [hev.deriv_eq, deriv_const]

lemma deriv2_smoothTransition_eq_zero_of_neg {u : ℝ} (hu : u < 0) :
    deriv (deriv Real.smoothTransition) u = 0 := by
  have hev : deriv Real.smoothTransition =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hu] with y hy
    exact deriv_smoothTransition_eq_zero_of_nonpos hy.le
  rw [hev.deriv_eq, deriv_const]

lemma deriv2_smoothTransition_eq_zero_of_one_le {u : ℝ} (hu : 1 ≤ u) :
    deriv (deriv Real.smoothTransition) u = 0 := by
  rcases lt_or_eq_of_le hu with h | h
  · exact deriv2_smoothTransition_eq_zero_of_one_lt h
  · rw [← h]
    exact continuous_eq_zero_of_pos_side (by fun_prop) 1
      (fun y hy => deriv2_smoothTransition_eq_zero_of_one_lt hy)

lemma deriv2_smoothTransition_eq_zero_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    deriv (deriv Real.smoothTransition) u = 0 := by
  rcases lt_or_eq_of_le hu with h | h
  · exact deriv2_smoothTransition_eq_zero_of_neg h
  · rw [h]
    exact continuous_eq_zero_of_neg_side (by fun_prop) 0
      (fun y hy => deriv2_smoothTransition_eq_zero_of_neg hy)

/-! ## Values of the clamp -/

lemma clamp_eq_one {β v : ℝ} (hβ : 0 < β) (hv : β ≤ v) : clamp β v = 1 := by
  rw [clamp, Real.smoothTransition.one_of_one_le]
  · ring
  · rw [le_div_iff₀ (by positivity)]; linarith

lemma clamp_eq_neg_one {β v : ℝ} (hβ : 0 < β) (hv : v ≤ -β) : clamp β v = -1 := by
  rw [clamp, Real.smoothTransition.zero_of_nonpos]
  · ring
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

lemma sqWave_eq_one {β : ℝ} (hβ : 0 < β) {x : ℝ} (hx : β ≤ Real.cos x) :
    sqWave β x = 1 := by
  change clamp β (Real.cos x) = 1
  rw [clamp_eq_one hβ hx]

lemma sqWave_eq_neg_one {β : ℝ} (hβ : 0 < β) {x : ℝ} (hx : Real.cos x ≤ -β) :
    sqWave β x = -1 := by
  change clamp β (Real.cos x) = -1
  rw [clamp_eq_neg_one hβ hx]

lemma sqWave_abs_le_one (β x : ℝ) : |sqWave β x| ≤ 1 := by
  change |clamp β (Real.cos x)| ≤ 1
  rw [clamp]
  have h1 : 0 ≤ Real.smoothTransition ((Real.cos x + β) / (2 * β)) :=
    Real.smoothTransition.nonneg _
  have h2 : Real.smoothTransition ((Real.cos x + β) / (2 * β)) ≤ 1 :=
    Real.smoothTransition.le_one _
  rw [abs_le]
  constructor <;> linarith

/-! ## Differentiability of the clamp -/

lemma hasDerivAt_clamp (β : ℝ) (hβ : 0 < β) (v : ℝ) :
    HasDerivAt (clamp β) (clampD β v) v := by
  have hw : HasDerivAt (fun x : ℝ => (x + β) / (2 * β)) (1 / (2 * β)) v := by
    have h2 : HasDerivAt (fun x : ℝ => x + β) 1 v := (hasDerivAt_id v).add_const β
    exact h2.div_const (2 * β)
  have hs : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((v + β) / (2 * β))) ((v + β) / (2 * β)) :=
    (by fun_prop : DifferentiableAt ℝ Real.smoothTransition _).hasDerivAt
  have key := (hs.comp v hw).const_mul 2 |>.sub_const 1
  have hval : 2 * (deriv Real.smoothTransition ((v + β) / (2 * β)) * (1 / (2 * β)))
      = clampD β v := by
    rw [clampD]; field_simp
  rw [hval] at key
  convert key using 1 <;> try rfl

lemma hasDerivAt_clampD (β : ℝ) (hβ : 0 < β) (v : ℝ) :
    HasDerivAt (clampD β) (clampDD β v) v := by
  have hw : HasDerivAt (fun x : ℝ => (x + β) / (2 * β)) (1 / (2 * β)) v := by
    have h2 : HasDerivAt (fun x : ℝ => x + β) 1 v := (hasDerivAt_id v).add_const β
    exact h2.div_const (2 * β)
  have hs : HasDerivAt (deriv Real.smoothTransition)
      (deriv (deriv Real.smoothTransition) ((v + β) / (2 * β))) ((v + β) / (2 * β)) :=
    (by fun_prop : DifferentiableAt ℝ (deriv Real.smoothTransition) _).hasDerivAt
  have key := (hs.comp v hw).div_const β
  have hval : (deriv (deriv Real.smoothTransition) ((v + β) / (2 * β)) * (1 / (2 * β))) / β
      = clampDD β v := by
    rw [clampDD]; field_simp
  rw [hval] at key
  convert key using 1 <;> try rfl

/-! ## Vanishing of `clampD`, `clampDD` off `(-β, β)` -/

lemma clampD_eq_zero_of_ge {β v : ℝ} (hβ : 0 < β) (hv : β ≤ v) : clampD β v = 0 := by
  rw [clampD, deriv_smoothTransition_eq_zero_of_one_le (u := (v + β) / (2 * β))]
  · simp
  · rw [le_div_iff₀ (by positivity)]; linarith

lemma clampD_eq_zero_of_le {β v : ℝ} (hβ : 0 < β) (hv : v ≤ -β) : clampD β v = 0 := by
  rw [clampD, deriv_smoothTransition_eq_zero_of_nonpos (u := (v + β) / (2 * β))]
  · simp
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

lemma clampDD_eq_zero_of_ge {β v : ℝ} (hβ : 0 < β) (hv : β ≤ v) : clampDD β v = 0 := by
  rw [clampDD, deriv2_smoothTransition_eq_zero_of_one_le (u := (v + β) / (2 * β))]
  · simp
  · rw [le_div_iff₀ (by positivity)]; linarith

lemma clampDD_eq_zero_of_le {β v : ℝ} (hβ : 0 < β) (hv : v ≤ -β) : clampDD β v = 0 := by
  rw [clampDD, deriv2_smoothTransition_eq_zero_of_nonpos (u := (v + β) / (2 * β))]
  · simp
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

/-! ## Bounds on `clampD`, `clampDD` -/

lemma abs_clampD_le {β M : ℝ} (hβ : 0 < β) (hM : ∀ v : ℝ, |deriv Real.smoothTransition v| ≤ M)
    (v : ℝ) : |clampD β v| ≤ M / β := by
  rw [clampD, abs_div, abs_of_pos hβ]
  exact div_le_div_of_nonneg_right (hM _) hβ.le

lemma abs_clampDD_le {β M : ℝ} (hβ : 0 < β)
    (hM : ∀ v : ℝ, |deriv (deriv Real.smoothTransition) v| ≤ M) (v : ℝ) :
    |clampDD β v| ≤ M / (2 * β ^ 2) := by
  have hpos : 0 < 2 * β ^ 2 := by positivity
  rw [clampDD, abs_div, abs_of_pos hpos]
  exact div_le_div_of_nonneg_right (hM _) hpos.le

/-! ## Continuity -/

lemma continuous_clamp (β : ℝ) : Continuous (clamp β) := by
  change Continuous (fun v => 2 * Real.smoothTransition ((v + β) / (2 * β)) - 1)
  exact (continuous_const.mul (Real.smoothTransition.continuous.comp (by fun_prop))).sub
    continuous_const

lemma continuous_clampD (β : ℝ) : Continuous (clampD β) := by
  change Continuous (fun v => deriv Real.smoothTransition ((v + β) / (2 * β)) / β)
  exact ((by fun_prop : Continuous (deriv Real.smoothTransition)).comp (by fun_prop)).div_const β

lemma continuous_clampDD (β : ℝ) : Continuous (clampDD β) := by
  change Continuous (fun v => deriv (deriv Real.smoothTransition) ((v + β) / (2 * β)) / (2 * β ^ 2))
  exact ((by fun_prop : Continuous (deriv (deriv Real.smoothTransition))).comp
    (by fun_prop)).div_const (2 * β ^ 2)

lemma continuous_sqWave (β : ℝ) : Continuous (sqWave β) := by
  change Continuous (fun x => clamp β (Real.cos x))
  exact (continuous_clamp β).comp Real.continuous_cos

lemma continuous_sqWaveC (β : ℝ) : Continuous (sqWaveC β) := by
  change Continuous (fun x => (clamp β (Real.cos x) : ℂ))
  exact Complex.continuous_ofReal.comp ((continuous_clamp β).comp Real.continuous_cos)

lemma continuous_sqD1R (β : ℝ) : Continuous (sqD1R β) := by
  change Continuous (fun x => clampD β (Real.cos x) * (-Real.sin x))
  exact ((continuous_clampD β).comp Real.continuous_cos).mul Real.continuous_sin.neg

lemma continuous_sqD1 (β : ℝ) : Continuous (sqD1 β) := by
  change Continuous (fun x => (sqD1R β x : ℂ))
  exact Complex.continuous_ofReal.comp (continuous_sqD1R β)

lemma continuous_sqD2 (β : ℝ) : Continuous (sqD2 β) := by
  change Continuous (fun x => (sqD2R β x : ℂ))
  have h : Continuous (sqD2R β) := by
    change Continuous (fun x => clampDD β (Real.cos x) * (Real.sin x) ^ 2
      - clampD β (Real.cos x) * Real.cos x)
    exact (((continuous_clampDD β).comp Real.continuous_cos).mul (Real.continuous_sin.pow 2)).sub
      (((continuous_clampD β).comp Real.continuous_cos).mul Real.continuous_cos)
  exact Complex.continuous_ofReal.comp h

/-! ## Periodicity -/

lemma periodic_sqWave (β : ℝ) : Function.Periodic (sqWave β) (2 * Real.pi) := by
  intro x
  change clamp β (Real.cos (x + 2 * Real.pi)) = clamp β (Real.cos x)
  rw [Real.cos_periodic x]

lemma periodic_sqWaveC (β : ℝ) : Function.Periodic (sqWaveC β) (2 * Real.pi) := by
  intro x
  change (sqWave β (x + 2 * Real.pi) : ℂ) = (sqWave β x : ℂ)
  rw [periodic_sqWave β x]

lemma periodic_sqD1 (β : ℝ) : Function.Periodic (sqD1 β) (2 * Real.pi) := by
  intro x
  change (((clampD β (Real.cos (x + 2 * Real.pi)) * (-Real.sin (x + 2 * Real.pi)) : ℝ) : ℂ))
    = (((clampD β (Real.cos x) * (-Real.sin x) : ℝ) : ℂ))
  rw [Real.cos_periodic x, Real.sin_periodic x]

/-! ## Derivatives of the square wave -/

lemma hasDerivAt_sqWave (β : ℝ) (hβ : 0 < β) (x : ℝ) :
    HasDerivAt (sqWave β) (sqD1R β x) x := by
  have hcl : HasDerivAt (clamp β) (clampD β (Real.cos x)) (Real.cos x) :=
    hasDerivAt_clamp β hβ (Real.cos x)
  have h := hcl.comp x (Real.hasDerivAt_cos x)
  change HasDerivAt (fun x => clamp β (Real.cos x))
    (clampD β (Real.cos x) * (-Real.sin x)) x
  convert h using 1 <;> try rfl

lemma hasDerivAt_sqWaveC (β : ℝ) (hβ : 0 < β) (x : ℝ) :
    HasDerivAt (sqWaveC β) (sqD1 β x) x := by
  have h := (hasDerivAt_sqWave β hβ x).ofReal_comp
  change HasDerivAt (fun y => (sqWave β y : ℂ)) ((sqD1R β x : ℝ) : ℂ) x
  convert h using 1 <;> try rfl

lemma hasDerivAt_sqD1R (β : ℝ) (hβ : 0 < β) (x : ℝ) :
    HasDerivAt (sqD1R β) (sqD2R β x) x := by
  have h1 : HasDerivAt (fun x => clampD β (Real.cos x))
      (clampDD β (Real.cos x) * (-Real.sin x)) x := by
    have hcl : HasDerivAt (clampD β) (clampDD β (Real.cos x)) (Real.cos x) :=
      hasDerivAt_clampD β hβ (Real.cos x)
    have h := hcl.comp x (Real.hasDerivAt_cos x)
    convert h using 1 <;> try rfl
  have h2 : HasDerivAt (fun x : ℝ => -Real.sin x) (-Real.cos x) x := (Real.hasDerivAt_sin x).neg
  have h := h1.mul h2
  have hval : (clampDD β (Real.cos x) * (-Real.sin x)) * (-Real.sin x)
      + clampD β (Real.cos x) * (-Real.cos x) = sqD2R β x := by
    rw [sqD2R]; ring
  rw [hval] at h
  change HasDerivAt (fun x => clampD β (Real.cos x) * (-Real.sin x)) (sqD2R β x) x
  convert h using 1 <;> try rfl

lemma hasDerivAt_sqD1 (β : ℝ) (hβ : 0 < β) (x : ℝ) :
    HasDerivAt (sqD1 β) (sqD2 β x) x := by
  have h := (hasDerivAt_sqD1R β hβ x).ofReal_comp
  change HasDerivAt (fun y => (sqD1R β y : ℂ)) ((sqD2R β x : ℝ) : ℂ) x
  convert h using 1 <;> try rfl

lemma deriv_sqWaveC (β : ℝ) (hβ : 0 < β) : deriv (sqWaveC β) = sqD1 β := by
  funext x; exact (hasDerivAt_sqWaveC β hβ x).deriv

lemma deriv_sqD1 (β : ℝ) (hβ : 0 < β) : deriv (sqD1 β) = sqD2 β := by
  funext x; exact (hasDerivAt_sqD1 β hβ x).deriv

/-! ## Pointwise bounds -/

lemma norm_sqD1_le {β M : ℝ} (hβ : 0 < β) (hM : ∀ v : ℝ, |deriv Real.smoothTransition v| ≤ M)
    (x : ℝ) : ‖sqD1 β x‖ ≤ M / β := by
  have hsq : ‖sqD1 β x‖ = |sqD1R β x| := by
    change ‖((sqD1R β x : ℝ) : ℂ)‖ = |sqD1R β x|
    simp
  rw [hsq]
  change |clampD β (Real.cos x) * (-Real.sin x)| ≤ M / β
  calc |clampD β (Real.cos x) * (-Real.sin x)|
      = |clampD β (Real.cos x)| * |Real.sin x| := by rw [abs_mul, abs_neg]
    _ ≤ |clampD β (Real.cos x)| * 1 := by
        gcongr; exact Real.abs_sin_le_one x
    _ = |clampD β (Real.cos x)| := by ring
    _ ≤ M / β := abs_clampD_le hβ hM _

lemma norm_sqD2_le {β M : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hM : 0 ≤ M)
    (hM1 : ∀ v : ℝ, |deriv Real.smoothTransition v| ≤ M)
    (hM2 : ∀ v : ℝ, |deriv (deriv Real.smoothTransition) v| ≤ M)
    (x : ℝ) : ‖sqD2 β x‖ ≤ 3 * M / (2 * β ^ 2) := by
  have hpos : 0 < β ^ 2 := by positivity
  have h1 : |sqD2R β x| ≤ M / (2 * β ^ 2) + M / β := by
    change |clampDD β (Real.cos x) * (Real.sin x) ^ 2 - clampD β (Real.cos x) * Real.cos x|
      ≤ M / (2 * β ^ 2) + M / β
    calc |clampDD β (Real.cos x) * (Real.sin x) ^ 2 - clampD β (Real.cos x) * Real.cos x|
        ≤ |clampDD β (Real.cos x) * (Real.sin x) ^ 2| + |clampD β (Real.cos x) * Real.cos x| :=
          abs_sub _ _
      _ = |clampDD β (Real.cos x)| * (Real.sin x) ^ 2 + |clampD β (Real.cos x)| * |Real.cos x| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin x))]
      _ ≤ M / (2 * β ^ 2) * 1 + M / β * 1 := by
          gcongr
          · exact abs_clampDD_le hβ hM2 _
          · exact Real.sin_sq_le_one x
          · exact abs_clampD_le hβ hM1 _
          · exact Real.abs_cos_le_one x
      _ = M / (2 * β ^ 2) + M / β := by ring
  have h3 : M / β ≤ M / β ^ 2 := by
    rw [div_le_div_iff₀ hβ hpos]
    have hb2 : β ^ 2 ≤ β := by nlinarith [hβ, hβ1]
    nlinarith [hM, hb2]
  change ‖((sqD2R β x : ℝ) : ℂ)‖ ≤ 3 * M / (2 * β ^ 2)
  rw [show ‖((sqD2R β x : ℝ) : ℂ)‖ = |sqD2R β x| by simp]
  calc |sqD2R β x| ≤ M / (2 * β ^ 2) + M / β := h1
    _ ≤ M / (2 * β ^ 2) + M / β ^ 2 := by linarith
    _ = 3 * M / (2 * β ^ 2) := by field_simp; ring

/-! ## Vanishing of `sqD1`, `sqD2` where `|cos x| ≥ β` -/

lemma sqD1R_eq_zero_of_ge {β : ℝ} (hβ : 0 < β) {x : ℝ} (hx : β ≤ Real.cos x) :
    sqD1R β x = 0 := by
  rw [sqD1R, clampD_eq_zero_of_ge hβ hx, zero_mul]

lemma sqD1R_eq_zero_of_le {β : ℝ} (hβ : 0 < β) {x : ℝ} (hx : Real.cos x ≤ -β) :
    sqD1R β x = 0 := by
  rw [sqD1R, clampD_eq_zero_of_le hβ hx, zero_mul]

lemma sqD2R_eq_zero_of_ge {β : ℝ} (hβ : 0 < β) {x : ℝ} (hx : β ≤ Real.cos x) :
    sqD2R β x = 0 := by
  rw [sqD2R, clampDD_eq_zero_of_ge hβ hx, clampD_eq_zero_of_ge hβ hx]
  ring

lemma sqD2R_eq_zero_of_le {β : ℝ} (hβ : 0 < β) {x : ℝ} (hx : Real.cos x ≤ -β) :
    sqD2R β x = 0 := by
  rw [sqD2R, clampDD_eq_zero_of_le hβ hx, clampD_eq_zero_of_le hβ hx]
  ring

lemma sqD1_eq_zero_of_ge {β : ℝ} (hβ : 0 < β) {x : ℝ} (hx : β ≤ Real.cos x) :
    sqD1 β x = 0 := by
  change ((sqD1R β x : ℝ) : ℂ) = 0
  rw [sqD1R_eq_zero_of_ge hβ hx]; simp

lemma sqD1_eq_zero_of_le {β : ℝ} (hβ : 0 < β) {x : ℝ} (hx : Real.cos x ≤ -β) :
    sqD1 β x = 0 := by
  change ((sqD1R β x : ℝ) : ℂ) = 0
  rw [sqD1R_eq_zero_of_le hβ hx]; simp

lemma sqD2_eq_zero_of_ge {β : ℝ} (hβ : 0 < β) {x : ℝ} (hx : β ≤ Real.cos x) :
    sqD2 β x = 0 := by
  change ((sqD2R β x : ℝ) : ℂ) = 0
  rw [sqD2R_eq_zero_of_ge hβ hx]; simp

lemma sqD2_eq_zero_of_le {β : ℝ} (hβ : 0 < β) {x : ℝ} (hx : Real.cos x ≤ -β) :
    sqD2 β x = 0 := by
  change ((sqD2R β x : ℝ) : ℂ) = 0
  rw [sqD2R_eq_zero_of_le hβ hx]; simp

/-! ## Trigonometric location bounds -/

lemma le_sin_sqBeta_aux {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    β ≤ Real.sin (Real.pi * β / 2) := by
  have hx0 : 0 ≤ Real.pi * β / 2 := by positivity
  have hx1 : Real.pi * β / 2 ≤ Real.pi / 2 := by nlinarith [Real.pi_pos, hβ1]
  have h := Real.mul_le_sin hx0 hx1
  have heq : 2 / Real.pi * (Real.pi * β / 2) = β := by field_simp
  rw [heq] at h
  exact h

lemma cos_ge_of_mem_Icc_left {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {x : ℝ}
    (hx : x ∈ Set.Icc 0 (Real.pi / 2 - Real.pi * β / 2)) : β ≤ Real.cos x := by
  have hx1 : 0 ≤ x := hx.1
  have hx2 : x ≤ Real.pi / 2 - Real.pi * β / 2 := hx.2
  have hle : Real.pi / 2 - Real.pi * β / 2 ≤ Real.pi := by nlinarith [Real.pi_pos, hβ, hβ1]
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hx1 hle hx2
  have h1 : Real.cos (Real.pi / 2 - Real.pi * β / 2) = Real.sin (Real.pi * β / 2) :=
    Real.cos_pi_div_two_sub _
  rw [h1] at hcos
  exact (le_sin_sqBeta_aux hβ hβ1).trans hcos

lemma cos_le_neg_of_mem_Icc_mid {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {x : ℝ}
    (hx : x ∈ Set.Icc (Real.pi / 2 + Real.pi * β / 2) (3 * Real.pi / 2 - Real.pi * β / 2)) :
    Real.cos x ≤ -β := by
  have hy1 : Real.pi * β / 2 ≤ x - Real.pi / 2 := by linarith [hx.1]
  have hy2 : x - Real.pi / 2 ≤ Real.pi - Real.pi * β / 2 := by linarith [hx.2]
  have hsin : Real.sin (Real.pi * β / 2) ≤ Real.sin (x - Real.pi / 2) := by
    rcases le_or_gt (x - Real.pi / 2) (Real.pi / 2) with hy | hy
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two
        (by nlinarith [Real.pi_pos, hβ, hβ1]) hy hy1
    · have e1 : Real.sin (x - Real.pi / 2) = Real.sin (Real.pi - (x - Real.pi / 2)) :=
        (Real.sin_pi_sub _).symm
      rw [e1]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [Real.pi_pos, hβ, hβ1])
        (by linarith [hy]) (by linarith [hy2])
  have hcos : Real.cos x = -Real.sin (x - Real.pi / 2) := by
    rw [show x = Real.pi / 2 + (x - Real.pi / 2) by ring, Real.cos_add]
    simp
  rw [hcos]
  linarith [hsin, le_sin_sqBeta_aux hβ hβ1]

lemma cos_ge_of_mem_Icc_tail {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {x : ℝ}
    (hx : x ∈ Set.Icc (3 * Real.pi / 2 + Real.pi * β / 2) (2 * Real.pi)) :
    β ≤ Real.cos x := by
  have hcos : Real.cos x = Real.cos (2 * Real.pi - x) := (Real.cos_two_pi_sub x).symm
  rw [hcos]
  apply cos_ge_of_mem_Icc_left hβ hβ1
  exact ⟨by linarith [hx.2], by linarith [hx.1]⟩

/-! ## Integral bounds -/

lemma integral_norm_sqD1_le {β M : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hM : ∀ v : ℝ, |deriv Real.smoothTransition v| ≤ M) :
    ∫ x in (0 : ℝ)..(2 * Real.pi), ‖sqD1 β x‖ ≤ 2 * Real.pi * M := by
  set a : ℝ := Real.pi / 2 - Real.pi * β / 2 with ha
  set b : ℝ := Real.pi / 2 + Real.pi * β / 2 with hb
  set c : ℝ := 3 * Real.pi / 2 - Real.pi * β / 2 with hc
  set d : ℝ := 3 * Real.pi / 2 + Real.pi * β / 2 with hd
  have ha0 : 0 ≤ a := by rw [ha]; nlinarith [Real.pi_pos, hβ, hβ1]
  have hab : a ≤ b := by rw [ha, hb]; nlinarith [Real.pi_pos, hβ]
  have hbc : b ≤ c := by rw [hb, hc]; nlinarith [Real.pi_pos, hβ1]
  have hcd : c ≤ d := by rw [hc, hd]; nlinarith [Real.pi_pos, hβ]
  have hd2 : d ≤ 2 * Real.pi := by rw [hd]; nlinarith [Real.pi_pos, hβ1]
  have hcont1 : Continuous fun x : ℝ => ‖sqD1 β x‖ := continuous_norm.comp (continuous_sqD1 β)
  have hii : ∀ (x y : ℝ), IntervalIntegrable (fun t : ℝ => ‖sqD1 β t‖) volume x y :=
    fun x y => hcont1.intervalIntegrable (μ := volume) x y
  have hzero1 : ∫ x in (0 : ℝ)..a, ‖sqD1 β x‖ = 0 := by
    rw [show (∫ x in (0 : ℝ)..a, ‖sqD1 β x‖) = ∫ x in (0 : ℝ)..a, (0 : ℝ) by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le ha0] at hx
      have hcos := cos_ge_of_mem_Icc_left hβ hβ1 hx
      change ‖sqD1 β x‖ = (0 : ℝ)
      rw [sqD1_eq_zero_of_ge hβ hcos, norm_zero]]
    simp
  have hzero2 : ∫ x in b..c, ‖sqD1 β x‖ = 0 := by
    rw [show (∫ x in b..c, ‖sqD1 β x‖) = ∫ x in b..c, (0 : ℝ) by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hbc] at hx
      have hcos := cos_le_neg_of_mem_Icc_mid hβ hβ1 hx
      change ‖sqD1 β x‖ = (0 : ℝ)
      rw [sqD1_eq_zero_of_le hβ hcos, norm_zero]]
    simp
  have hzero3 : ∫ x in d..(2 * Real.pi), ‖sqD1 β x‖ = 0 := by
    rw [show (∫ x in d..(2 * Real.pi), ‖sqD1 β x‖) = ∫ x in d..(2 * Real.pi), (0 : ℝ) by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hd2] at hx
      have hcos := cos_ge_of_mem_Icc_tail hβ hβ1 hx
      change ‖sqD1 β x‖ = (0 : ℝ)
      rw [sqD1_eq_zero_of_ge hβ hcos, norm_zero]]
    simp
  have hbnd_ab : ∫ x in a..b, ‖sqD1 β x‖ ≤ M / β * (b - a) := by
    have := intervalIntegral.integral_mono hab (hii a b)
      (intervalIntegrable_const (μ := volume)) (fun x => norm_sqD1_le hβ hM x)
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm (b - a)] at this
    exact this
  have hbnd_cd : ∫ x in c..d, ‖sqD1 β x‖ ≤ M / β * (d - c) := by
    have := intervalIntegral.integral_mono hcd (hii c d)
      (intervalIntegrable_const (μ := volume)) (fun x => norm_sqD1_le hβ hM x)
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm (d - c)] at this
    exact this
  have hlen1 : b - a = Real.pi * β := by rw [ha, hb]; ring
  have hlen2 : d - c = Real.pi * β := by rw [hc, hd]; ring
  rw [hlen1] at hbnd_ab
  rw [hlen2] at hbnd_cd
  have htot : ∫ x in (0 : ℝ)..(2 * Real.pi), ‖sqD1 β x‖
      = (∫ x in (0 : ℝ)..a, ‖sqD1 β x‖)
        + (∫ x in a..b, ‖sqD1 β x‖)
        + (∫ x in b..c, ‖sqD1 β x‖)
        + (∫ x in c..d, ‖sqD1 β x‖)
        + (∫ x in d..(2 * Real.pi), ‖sqD1 β x‖) := by
    have e1 : ∫ x in (0 : ℝ)..b, ‖sqD1 β x‖
        = (∫ x in (0 : ℝ)..a, ‖sqD1 β x‖) + (∫ x in a..b, ‖sqD1 β x‖) :=
      (integral_add_adjacent_intervals (hii 0 a) (hii a b)).symm
    have e2 : ∫ x in b..d, ‖sqD1 β x‖
        = (∫ x in b..c, ‖sqD1 β x‖) + (∫ x in c..d, ‖sqD1 β x‖) :=
      (integral_add_adjacent_intervals (hii b c) (hii c d)).symm
    have e3 : ∫ x in (0 : ℝ)..d, ‖sqD1 β x‖
        = (∫ x in (0 : ℝ)..b, ‖sqD1 β x‖) + (∫ x in b..d, ‖sqD1 β x‖) :=
      (integral_add_adjacent_intervals (hii 0 b) (hii b d)).symm
    have e4 : ∫ x in (0 : ℝ)..(2 * Real.pi), ‖sqD1 β x‖
        = (∫ x in (0 : ℝ)..d, ‖sqD1 β x‖) + (∫ x in d..(2 * Real.pi), ‖sqD1 β x‖) :=
      (integral_add_adjacent_intervals (hii 0 d) (hii d (2 * Real.pi))).symm
    rw [e4, e3, e2, e1]; abel
  rw [htot, hzero1, hzero2, hzero3]
  simp only [zero_add, add_zero]
  have hv : M / β * (Real.pi * β) = Real.pi * M := by field_simp
  linarith [hbnd_ab, hbnd_cd, hv]

lemma integral_norm_sqD2_le {β M : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hM : 0 ≤ M)
    (hM1 : ∀ v : ℝ, |deriv Real.smoothTransition v| ≤ M)
    (hM2 : ∀ v : ℝ, |deriv (deriv Real.smoothTransition) v| ≤ M) :
    ∫ x in (0 : ℝ)..(2 * Real.pi), ‖sqD2 β x‖ ≤ 3 * Real.pi * M / β := by
  set a : ℝ := Real.pi / 2 - Real.pi * β / 2 with ha
  set b : ℝ := Real.pi / 2 + Real.pi * β / 2 with hb
  set c : ℝ := 3 * Real.pi / 2 - Real.pi * β / 2 with hc
  set d : ℝ := 3 * Real.pi / 2 + Real.pi * β / 2 with hd
  have ha0 : 0 ≤ a := by rw [ha]; nlinarith [Real.pi_pos, hβ, hβ1]
  have hab : a ≤ b := by rw [ha, hb]; nlinarith [Real.pi_pos, hβ]
  have hbc : b ≤ c := by rw [hb, hc]; nlinarith [Real.pi_pos, hβ1]
  have hcd : c ≤ d := by rw [hc, hd]; nlinarith [Real.pi_pos, hβ]
  have hd2 : d ≤ 2 * Real.pi := by rw [hd]; nlinarith [Real.pi_pos, hβ1]
  have hcont2 : Continuous fun x : ℝ => ‖sqD2 β x‖ := continuous_norm.comp (continuous_sqD2 β)
  have hii : ∀ (x y : ℝ), IntervalIntegrable (fun t : ℝ => ‖sqD2 β t‖) volume x y :=
    fun x y => hcont2.intervalIntegrable (μ := volume) x y
  have hzero1 : ∫ x in (0 : ℝ)..a, ‖sqD2 β x‖ = 0 := by
    rw [show (∫ x in (0 : ℝ)..a, ‖sqD2 β x‖) = ∫ x in (0 : ℝ)..a, (0 : ℝ) by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le ha0] at hx
      have hcos := cos_ge_of_mem_Icc_left hβ hβ1 hx
      change ‖sqD2 β x‖ = (0 : ℝ)
      rw [sqD2_eq_zero_of_ge hβ hcos, norm_zero]]
    simp
  have hzero2 : ∫ x in b..c, ‖sqD2 β x‖ = 0 := by
    rw [show (∫ x in b..c, ‖sqD2 β x‖) = ∫ x in b..c, (0 : ℝ) by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hbc] at hx
      have hcos := cos_le_neg_of_mem_Icc_mid hβ hβ1 hx
      change ‖sqD2 β x‖ = (0 : ℝ)
      rw [sqD2_eq_zero_of_le hβ hcos, norm_zero]]
    simp
  have hzero3 : ∫ x in d..(2 * Real.pi), ‖sqD2 β x‖ = 0 := by
    rw [show (∫ x in d..(2 * Real.pi), ‖sqD2 β x‖) = ∫ x in d..(2 * Real.pi), (0 : ℝ) by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hd2] at hx
      have hcos := cos_ge_of_mem_Icc_tail hβ hβ1 hx
      change ‖sqD2 β x‖ = (0 : ℝ)
      rw [sqD2_eq_zero_of_ge hβ hcos, norm_zero]]
    simp
  have hbnd_ab : ∫ x in a..b, ‖sqD2 β x‖ ≤ 3 * M / (2 * β ^ 2) * (b - a) := by
    have := intervalIntegral.integral_mono hab (hii a b)
      (intervalIntegrable_const (μ := volume)) (fun x => norm_sqD2_le hβ hβ1 hM hM1 hM2 x)
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm (b - a)] at this
    exact this
  have hbnd_cd : ∫ x in c..d, ‖sqD2 β x‖ ≤ 3 * M / (2 * β ^ 2) * (d - c) := by
    have := intervalIntegral.integral_mono hcd (hii c d)
      (intervalIntegrable_const (μ := volume)) (fun x => norm_sqD2_le hβ hβ1 hM hM1 hM2 x)
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm (d - c)] at this
    exact this
  have hlen1 : b - a = Real.pi * β := by rw [ha, hb]; ring
  have hlen2 : d - c = Real.pi * β := by rw [hc, hd]; ring
  rw [hlen1] at hbnd_ab
  rw [hlen2] at hbnd_cd
  have htot : ∫ x in (0 : ℝ)..(2 * Real.pi), ‖sqD2 β x‖
      = (∫ x in (0 : ℝ)..a, ‖sqD2 β x‖)
        + (∫ x in a..b, ‖sqD2 β x‖)
        + (∫ x in b..c, ‖sqD2 β x‖)
        + (∫ x in c..d, ‖sqD2 β x‖)
        + (∫ x in d..(2 * Real.pi), ‖sqD2 β x‖) := by
    have e1 : ∫ x in (0 : ℝ)..b, ‖sqD2 β x‖
        = (∫ x in (0 : ℝ)..a, ‖sqD2 β x‖) + (∫ x in a..b, ‖sqD2 β x‖) :=
      (integral_add_adjacent_intervals (hii 0 a) (hii a b)).symm
    have e2 : ∫ x in b..d, ‖sqD2 β x‖
        = (∫ x in b..c, ‖sqD2 β x‖) + (∫ x in c..d, ‖sqD2 β x‖) :=
      (integral_add_adjacent_intervals (hii b c) (hii c d)).symm
    have e3 : ∫ x in (0 : ℝ)..d, ‖sqD2 β x‖
        = (∫ x in (0 : ℝ)..b, ‖sqD2 β x‖) + (∫ x in b..d, ‖sqD2 β x‖) :=
      (integral_add_adjacent_intervals (hii 0 b) (hii b d)).symm
    have e4 : ∫ x in (0 : ℝ)..(2 * Real.pi), ‖sqD2 β x‖
        = (∫ x in (0 : ℝ)..d, ‖sqD2 β x‖) + (∫ x in d..(2 * Real.pi), ‖sqD2 β x‖) :=
      (integral_add_adjacent_intervals (hii 0 d) (hii d (2 * Real.pi))).symm
    rw [e4, e3, e2, e1]; abel
  rw [htot, hzero1, hzero2, hzero3]
  simp only [zero_add, add_zero]
  have hv : 3 * M / (2 * β ^ 2) * (Real.pi * β) = 3 * Real.pi * M / (2 * β) := by
    field_simp
  have htwo : 2 * (3 * Real.pi * M / (2 * β)) = 3 * Real.pi * M / β := by field_simp
  linarith [hbnd_ab, hbnd_cd, hv, htwo]

/-! ## Integration by parts for Fourier integrals -/

instance instFactTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

private lemma hasDerivAt_exp_lin (c : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ))) (c * Complex.exp (c * (x : ℂ))) x := by
  have h1 : HasDerivAt (fun y : ℝ => c * (y : ℂ)) c x := by
    have h2 : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := (hasDerivAt_id (x : ℂ)).comp_ofReal
    simpa using h2.const_mul c
  have := h1.cexp
  simpa [mul_comm] using this

private lemma ibp_key (n : ℤ) (h : ℝ → ℂ)
    (hdiff : ∀ x, HasDerivAt h (deriv h x) x) (hcont : Continuous h)
    (hdcont : Continuous (deriv h)) (hper : Function.Periodic h (2 * Real.pi)) :
    (-(n : ℂ) * Complex.I) * (∫ x in (0 : ℝ)..(2 * Real.pi),
        h x * Complex.exp ((-(n : ℂ) * Complex.I) * (x : ℂ)))
      = - ∫ x in (0 : ℝ)..(2 * Real.pi),
          deriv h x * Complex.exp ((-(n : ℂ) * Complex.I) * (x : ℂ)) := by
  have hv_deriv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Complex.exp ((-(n : ℂ) * Complex.I) * (y : ℂ)))
      ((-(n : ℂ) * Complex.I) * Complex.exp ((-(n : ℂ) * Complex.I) * (x : ℂ))) x :=
    fun x => hasDerivAt_exp_lin (-(n : ℂ) * Complex.I) x
  have hv_cont : Continuous (fun y : ℝ => Complex.exp ((-(n : ℂ) * Complex.I) * (y : ℂ))) :=
    Continuous.cexp (continuous_const.mul Complex.continuous_ofReal)
  have hcontOn : ContinuousOn h (Set.uIcc 0 (2 * Real.pi)) :=
    hcont.continuousOn.mono (Set.subset_univ _)
  have hvcontOn : ContinuousOn (fun y : ℝ => Complex.exp ((-(n : ℂ) * Complex.I) * (y : ℂ)))
      (Set.uIcc 0 (2 * Real.pi)) := hv_cont.continuousOn.mono (Set.subset_univ _)
  have hv'i : IntervalIntegrable
      (fun x => (-(n : ℂ) * Complex.I) * Complex.exp ((-(n : ℂ) * Complex.I) * (x : ℂ)))
      volume 0 (2 * Real.pi) :=
    (continuous_const.mul hv_cont).intervalIntegrable (μ := volume) _ _
  have hIBP := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hcontOn hvcontOn
    (fun x _ => hdiff x) (fun x _ => hv_deriv x)
    (hdcont.intervalIntegrable (μ := volume) _ _) hv'i
  have hv0 : Complex.exp ((-(n : ℂ) * Complex.I) * ((0 : ℝ) : ℂ)) = 1 := by simp
  have hv2 : Complex.exp ((-(n : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    have hcast : (-(n : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)
        = (((-n : ℤ) : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
    rw [hcast]; exact Complex.exp_int_mul_two_pi_mul_I (-n)
  have hbound : h (2 * Real.pi) * Complex.exp ((-(n : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ))
      - h 0 * Complex.exp ((-(n : ℂ) * Complex.I) * ((0 : ℝ) : ℂ)) = 0 := by
    rw [hv0, hv2, mul_one, mul_one]
    have hp := hper 0; simp only [zero_add] at hp
    rw [hp, sub_self]
  have hprod : (∫ x in (0 : ℝ)..(2 * Real.pi),
        h x * ((-(n : ℂ) * Complex.I) * Complex.exp ((-(n : ℂ) * Complex.I) * (x : ℂ))))
      = (-(n : ℂ) * Complex.I) * (∫ x in (0 : ℝ)..(2 * Real.pi),
          h x * Complex.exp ((-(n : ℂ) * Complex.I) * (x : ℂ))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr; intro x _; ring
  rw [← hprod, hIBP, hbound]; ring

lemma fourier_integral_deriv (n : ℤ) (hn : n ≠ 0) (h : ℝ → ℂ)
    (hdiff : ∀ x, HasDerivAt h (deriv h x) x) (hcont : Continuous h)
    (hdcont : Continuous (deriv h)) (hper : Function.Periodic h (2 * Real.pi)) :
    (∫ x in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(n : ℂ) * Complex.I * x) * h x)
      = (-(Complex.I) / (n : ℂ)) * (∫ x in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (-(n : ℂ) * Complex.I * x) * deriv h x) := by
  have hc0 : (-(n : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (by exact_mod_cast hn)) Complex.I_ne_zero
  have hmul : (-(n : ℂ) * Complex.I) * (-(Complex.I) / (n : ℂ)) = -1 := by
    field_simp
    rw [pow_two, Complex.I_mul_I]
  have key := ibp_key n h hdiff hcont hdcont hper
  set J' : ℂ := ∫ x in (0 : ℝ)..(2 * Real.pi), h x * Complex.exp ((-(n : ℂ) * Complex.I) * (x : ℂ))
    with hJ'def
  set I2' : ℂ := ∫ x in (0 : ℝ)..(2 * Real.pi),
    deriv h x * Complex.exp ((-(n : ℂ) * Complex.I) * (x : ℂ)) with hI2'def
  have hJ : J' = (-(Complex.I) / (n : ℂ)) * I2' := by
    have h1 : (-(n : ℂ) * Complex.I) * J' = (-(n : ℂ) * Complex.I) * ((-(Complex.I) / (n : ℂ)) * I2') := by
      rw [hJ'def, hI2'def]
      rw [key, ← mul_assoc (-(n : ℂ) * Complex.I) (-(Complex.I) / (n : ℂ)) I2', hmul, neg_one_mul]
    exact mul_left_cancel₀ hc0 h1
  rw [hJ'def, hI2'def] at hJ
  have e1 : (∫ x in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(n : ℂ) * Complex.I * x) * h x)
      = ∫ x in (0 : ℝ)..(2 * Real.pi), h x * Complex.exp ((-(n : ℂ) * Complex.I) * (x : ℂ)) := by
    apply intervalIntegral.integral_congr; intro x _; ring
  have e2 : (∫ x in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(n : ℂ) * Complex.I * x) * deriv h x)
      = ∫ x in (0 : ℝ)..(2 * Real.pi),
          deriv h x * Complex.exp ((-(n : ℂ) * Complex.I) * (x : ℂ)) := by
    apply intervalIntegral.integral_congr; intro x _; ring
  rw [e1, e2]; exact hJ

lemma norm_fourier_integral_le (n : ℤ) (hn : n ≠ 0) (h : ℝ → ℂ)
    (hdiff : ∀ x, HasDerivAt h (deriv h x) x) (hcont : Continuous h)
    (hdcont : Continuous (deriv h)) (hper : Function.Periodic h (2 * Real.pi)) :
    ‖∫ x in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(n : ℂ) * Complex.I * x) * h x‖
      ≤ (1 / |(n : ℝ)|) * ∫ x in (0 : ℝ)..(2 * Real.pi), ‖deriv h x‖ := by
  set J : ℂ := ∫ x in (0 : ℝ)..(2 * Real.pi),
      h x * Complex.exp ((-(n : ℂ) * Complex.I) * (x : ℂ)) with hJdef
  set I2 : ℂ := ∫ x in (0 : ℝ)..(2 * Real.pi),
      deriv h x * Complex.exp ((-(n : ℂ) * Complex.I) * (x : ℂ)) with hI2def
  have key : (-(n : ℂ) * Complex.I) * J = -I2 := by
    rw [hJdef, hI2def]; exact ibp_key n h hdiff hcont hdcont hper
  have hnorm_v : ∀ x : ℝ, ‖Complex.exp ((-(n : ℂ) * Complex.I) * (x : ℂ))‖ = 1 := by
    intro x
    have hcast : (-(n : ℂ) * Complex.I) * (x : ℂ) = ((↑(-(n : ℝ) * x)) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hcast]; exact Complex.norm_exp_ofReal_mul_I _
  have hI2 : ‖I2‖ ≤ ∫ x in (0 : ℝ)..(2 * Real.pi), ‖deriv h x‖ := by
    rw [hI2def]
    calc ‖∫ x in (0 : ℝ)..(2 * Real.pi), deriv h x * Complex.exp ((-(n : ℂ) * Complex.I) * (x : ℂ))‖
        ≤ ∫ x in (0 : ℝ)..(2 * Real.pi),
            ‖deriv h x * Complex.exp ((-(n : ℂ) * Complex.I) * (x : ℂ))‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by positivity)
      _ = ∫ x in (0 : ℝ)..(2 * Real.pi), ‖deriv h x‖ := by
          apply intervalIntegral.integral_congr; intro x _
          change ‖deriv h x * Complex.exp ((-(n : ℂ) * Complex.I) * (x : ℂ))‖ = ‖deriv h x‖
          rw [norm_mul, hnorm_v x, mul_one]
  have hcn : ‖(-(n : ℂ) * Complex.I)‖ = |(n : ℝ)| := by
    rw [norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_intCast]
  have hJpos : 0 < |(n : ℝ)| := by rw [abs_pos]; exact_mod_cast hn
  have hmain : |(n : ℝ)| * ‖J‖ ≤ ∫ x in (0 : ℝ)..(2 * Real.pi), ‖deriv h x‖ := by
    have h1 : ‖(-(n : ℂ) * Complex.I) * J‖ = |(n : ℝ)| * ‖J‖ := by rw [norm_mul, hcn]
    rw [← h1, key, norm_neg]
    exact hI2
  have e1 : (∫ x in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(n : ℂ) * Complex.I * x) * h x) = J := by
    rw [hJdef]
    apply intervalIntegral.integral_congr; intro x _; ring
  rw [e1]
  rw [show (1 / |(n : ℝ)|) * (∫ x in (0 : ℝ)..(2 * Real.pi), ‖deriv h x‖)
      = (∫ x in (0 : ℝ)..(2 * Real.pi), ‖deriv h x‖) / |(n : ℝ)| by ring]
  rw [le_div_iff₀ hJpos, mul_comm]
  exact hmain

/-! ## The square wave as a function on the circle -/

noncomputable def sqWaveF (β : ℝ) : C(AddCircle (2 * Real.pi), ℂ) :=
  ⟨(periodic_sqWaveC β).lift, continuous_coinduced_dom.mpr (continuous_sqWaveC β)⟩

lemma sqWaveF_coe (β : ℝ) (x : ℝ) :
    sqWaveF β (x : AddCircle (2 * Real.pi)) = sqWaveC β x :=
  Function.Periodic.lift_coe (periodic_sqWaveC β) x

lemma fourierCoeff_sqWaveF (β : ℝ) (n : ℤ) :
    fourierCoeff (sqWaveF β) n = ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ x in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(n : ℂ) * Complex.I * x) * sqWaveC β x) := by
  rw [fourierCoeff_eq_intervalIntegral (sqWaveF β) n 0, zero_add]
  simp only [smul_eq_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  change (fourier (-n) (x : AddCircle (2 * Real.pi))) * sqWaveF β (x : AddCircle (2 * Real.pi))
      = Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ)) * sqWaveC β x
  rw [sqWaveF_coe, fourier_coe_apply]
  congr 1
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (↑(-n) : ℂ) * (↑x : ℂ)) / (↑(2 * Real.pi) : ℂ)
      = -(n : ℂ) * Complex.I * (x : ℂ) by push_cast; field_simp]

lemma norm_fourierCoeff_sqWaveF_zero (β : ℝ) : ‖fourierCoeff (sqWaveF β) 0‖ ≤ 1 := by
  rw [fourierCoeff_sqWaveF]
  have hint : (∫ x in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(((0 : ℤ) : ℂ)) * Complex.I * x) * sqWaveC β x)
      = ∫ x in (0 : ℝ)..(2 * Real.pi), sqWaveC β x := by
    apply intervalIntegral.integral_congr; intro x _; simp
  rw [hint]
  have hc : ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ = |(1 / (2 * Real.pi) : ℝ)| by simp,
      abs_of_pos (by positivity)]
  calc ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ x in (0 : ℝ)..(2 * Real.pi), sqWaveC β x)‖
      = (1 / (2 * Real.pi)) * ‖∫ x in (0 : ℝ)..(2 * Real.pi), sqWaveC β x‖ := by
        rw [norm_mul, hc]
    _ ≤ (1 / (2 * Real.pi)) * (2 * Real.pi) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ‖∫ x in (0 : ℝ)..(2 * Real.pi), sqWaveC β x‖
            ≤ ∫ x in (0 : ℝ)..(2 * Real.pi), ‖sqWaveC β x‖ :=
              intervalIntegral.norm_integral_le_integral_norm (by positivity)
          _ ≤ ∫ x in (0 : ℝ)..(2 * Real.pi), (1 : ℝ) := by
              apply intervalIntegral.integral_mono (by positivity)
                ((continuous_norm.comp (continuous_sqWaveC β)).intervalIntegrable (μ := volume) _ _)
                (intervalIntegrable_const (μ := volume))
              intro x
              change ‖((sqWave β x : ℝ) : ℂ)‖ ≤ (1 : ℝ)
              rw [show ‖((sqWave β x : ℝ) : ℂ)‖ = |sqWave β x| by simp]
              exact sqWave_abs_le_one β x
          _ = 2 * Real.pi := by rw [intervalIntegral.integral_const]; simp
    _ = 1 := by field_simp <;> ring_nf

lemma fourierCoeff_sqWaveF_bound1 {β M : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hM : ∀ v : ℝ, |deriv Real.smoothTransition v| ≤ M) (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeff (sqWaveF β) n‖ ≤ M / |(n : ℝ)| := by
  have hΦ : ‖∫ x in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(n : ℂ) * Complex.I * x) * sqWaveC β x‖
      ≤ (1 / |(n : ℝ)|) * (∫ x in (0 : ℝ)..(2 * Real.pi), ‖sqD1 β x‖) := by
    have h := norm_fourier_integral_le n hn (sqWaveC β)
      (fun x => by rw [deriv_sqWaveC β hβ]; exact hasDerivAt_sqWaveC β hβ x)
      (continuous_sqWaveC β)
      (by rw [deriv_sqWaveC β hβ]; exact continuous_sqD1 β)
      (periodic_sqWaveC β)
    rw [deriv_sqWaveC β hβ] at h
    exact h
  have hI : (∫ x in (0 : ℝ)..(2 * Real.pi), ‖sqD1 β x‖) ≤ 2 * Real.pi * M :=
    integral_norm_sqD1_le hβ hβ1 hM
  rw [fourierCoeff_sqWaveF]
  have hc : ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ = |(1 / (2 * Real.pi) : ℝ)| by simp,
      abs_of_pos (by positivity)]
  calc ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ x in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(n : ℂ) * Complex.I * x) * sqWaveC β x)‖
      = (1 / (2 * Real.pi)) * ‖∫ x in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (-(n : ℂ) * Complex.I * x) * sqWaveC β x‖ := by rw [norm_mul, hc]
    _ ≤ (1 / (2 * Real.pi)) * ((1 / |(n : ℝ)|) * (2 * Real.pi * M)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ‖∫ x in (0 : ℝ)..(2 * Real.pi),
              Complex.exp (-(n : ℂ) * Complex.I * x) * sqWaveC β x‖
            ≤ (1 / |(n : ℝ)|) * (∫ x in (0 : ℝ)..(2 * Real.pi), ‖sqD1 β x‖) := hΦ
          _ ≤ (1 / |(n : ℝ)|) * (2 * Real.pi * M) := by
              apply mul_le_mul_of_nonneg_left hI (by positivity)
    _ = M / |(n : ℝ)| := by field_simp <;> ring_nf

lemma fourierCoeff_sqWaveF_bound2 {β M : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hM : 0 ≤ M)
    (hM1 : ∀ v : ℝ, |deriv Real.smoothTransition v| ≤ M)
    (hM2 : ∀ v : ℝ, |deriv (deriv Real.smoothTransition) v| ≤ M) (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeff (sqWaveF β) n‖ ≤ 3 * M / (2 * β * (n : ℝ) ^ 2) := by
  have hrel : (∫ x in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(n : ℂ) * Complex.I * x) * sqWaveC β x)
      = (-(Complex.I) / (n : ℂ)) * (∫ x in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (-(n : ℂ) * Complex.I * x) * sqD1 β x) := by
    have h := fourier_integral_deriv n hn (sqWaveC β)
      (fun x => by rw [deriv_sqWaveC β hβ]; exact hasDerivAt_sqWaveC β hβ x)
      (continuous_sqWaveC β)
      (by rw [deriv_sqWaveC β hβ]; exact continuous_sqD1 β)
      (periodic_sqWaveC β)
    rwa [deriv_sqWaveC β hβ] at h
  have hΦ2 : ‖∫ x in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(n : ℂ) * Complex.I * x) * sqD1 β x‖
      ≤ (1 / |(n : ℝ)|) * (∫ x in (0 : ℝ)..(2 * Real.pi), ‖sqD2 β x‖) := by
    have h := norm_fourier_integral_le n hn (sqD1 β)
      (fun x => by rw [deriv_sqD1 β hβ]; exact hasDerivAt_sqD1 β hβ x)
      (continuous_sqD1 β)
      (by rw [deriv_sqD1 β hβ]; exact continuous_sqD2 β)
      (periodic_sqD1 β)
    rw [deriv_sqD1 β hβ] at h
    exact h
  have hI2 : (∫ x in (0 : ℝ)..(2 * Real.pi), ‖sqD2 β x‖) ≤ 3 * Real.pi * M / β :=
    integral_norm_sqD2_le hβ hβ1 hM hM1 hM2
  have hcI : ‖(-(Complex.I) / (n : ℂ))‖ = 1 / |(n : ℝ)| := by
    rw [norm_div, norm_neg, Complex.norm_I]
    rw [show ‖(n : ℂ)‖ = |(n : ℝ)| by exact Complex.norm_intCast n]
  have hmain : ‖∫ x in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(n : ℂ) * Complex.I * x) * sqWaveC β x‖
      ≤ 3 * Real.pi * M / (β * (n : ℝ) ^ 2) := by
    rw [hrel, norm_mul, hcI]
    calc (1 / |(n : ℝ)|) * ‖∫ x in (0 : ℝ)..(2 * Real.pi),
            Complex.exp (-(n : ℂ) * Complex.I * x) * sqD1 β x‖
        ≤ (1 / |(n : ℝ)|) * ((1 / |(n : ℝ)|) * (3 * Real.pi * M / β)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc ‖∫ x in (0 : ℝ)..(2 * Real.pi),
                Complex.exp (-(n : ℂ) * Complex.I * x) * sqD1 β x‖
              ≤ (1 / |(n : ℝ)|) * (∫ x in (0 : ℝ)..(2 * Real.pi), ‖sqD2 β x‖) := hΦ2
            _ ≤ (1 / |(n : ℝ)|) * (3 * Real.pi * M / β) := by
                apply mul_le_mul_of_nonneg_left hI2 (by positivity)
      _ = 3 * Real.pi * M / (β * (n : ℝ) ^ 2) := by field_simp <;> rw [sq_abs] <;> ring
  rw [fourierCoeff_sqWaveF]
  have hc : ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ = |(1 / (2 * Real.pi) : ℝ)| by simp,
      abs_of_pos (by positivity)]
  calc ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ x in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(n : ℂ) * Complex.I * x) * sqWaveC β x)‖
      = (1 / (2 * Real.pi)) * ‖∫ x in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (-(n : ℂ) * Complex.I * x) * sqWaveC β x‖ := by rw [norm_mul, hc]
    _ ≤ (1 / (2 * Real.pi)) * (3 * Real.pi * M / (β * (n : ℝ) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = 3 * M / (2 * β * (n : ℝ) ^ 2) := by field_simp <;> ring_nf

/-- **Friedlander–Iwaniec (20.17)–(20.19)**: the Fourier coefficients of the smoothed square
wave `t(α) = sign(cos α)` form an `ℓ¹` sequence of size `≪ log(2R)` on the arc `|cos α| ≥ 1/R`,
on which the series sums to `sign(cos α)`. -/
theorem exists_squareWave_fourier :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 2 ≤ R → ∃ ĉ : ℤ → ℂ,
      (∀ s : Finset ℤ, ∑ k ∈ s, ‖ĉ k‖ ≤ C * Real.log (2 * (R : ℝ))) ∧
      ∀ z : ℂ, ‖z‖ = 1 → (1 : ℝ) / (R : ℝ) ≤ |z.re| →
        HasSum (fun k : ℤ => ĉ k * z ^ k) (if 0 < z.re then 1 else -1) := by
  obtain ⟨M, hM0, hM1, hM2⟩ := smoothTransition_deriv_bounds
  refine ⟨7 * M + 1, by positivity, fun R hR => ?_⟩
  set β : ℝ := 1 / (R : ℝ) with hβdef
  have hβ : 0 < β := by rw [hβdef]; positivity
  have hβ1 : β ≤ 1 := by
    rw [hβdef, div_le_one (by positivity)]; exact_mod_cast (by omega : 1 ≤ R)
  have hconv2 : ∀ n : ℤ, 3 * M / (2 * β * (n : ℝ) ^ 2) = 3 * M * (R : ℝ) / (2 * (n : ℝ) ^ 2) := by
    intro n; rw [hβdef]; field_simp <;> ring_nf
  refine ⟨fun k => fourierCoeff (sqWaveF β) k, ?_, ?_⟩
  · intro s
    apply finset_sum_coeff_le R hR M hM0 (fun k => fourierCoeff (sqWaveF β) k)
    · exact norm_fourierCoeff_sqWaveF_zero β
    · intro k hk
      exact fourierCoeff_sqWaveF_bound1 hβ hβ1 hM1 k hk
    · intro k hk
      rw [← hconv2 k]
      exact fourierCoeff_sqWaveF_bound2 hβ hβ1 hM0 hM1 hM2 k hk
  · intro z hz hzre
    have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
    have hzw : Complex.exp ((z.arg : ℂ) * Complex.I) = z := by
      have h := Complex.norm_mul_exp_arg_mul_I z
      simpa [hz] using h
    have hfour : ∀ i : ℤ, (fourier i) (z.arg : AddCircle (2 * Real.pi)) = z ^ i := by
      intro i
      rw [fourier_coe_apply]
      have harg : (2 * (Real.pi : ℂ) * Complex.I * (i : ℂ) * (z.arg : ℂ)) / (↑(2 * Real.pi) : ℂ)
          = (i : ℂ) * ((z.arg : ℂ) * Complex.I) := by push_cast; field_simp
      rw [harg, Complex.exp_int_mul, hzw]
    have hval : sqWaveF β (z.arg : AddCircle (2 * Real.pi))
        = (if 0 < z.re then (1 : ℂ) else -1) := by
      rw [sqWaveF_coe]
      change ((sqWave β z.arg : ℝ) : ℂ) = (if 0 < z.re then (1 : ℂ) else -1)
      have hcz : Real.cos z.arg = z.re := by rw [Complex.cos_arg hz0, hz, div_one]
      rcases lt_or_ge (0 : ℝ) z.re with hp | hp
      · have hcos : β ≤ Real.cos z.arg := by
          rw [hcz, hβdef]
          rw [abs_of_pos hp] at hzre
          exact hzre
        rw [sqWave_eq_one hβ hcos, if_pos hp]; simp
      · have hcos : Real.cos z.arg ≤ -β := by
          rw [hcz, hβdef]
          rw [abs_of_nonpos hp] at hzre
          linarith
        rw [sqWave_eq_neg_one hβ hcos, if_neg (not_lt.mpr hp)]; simp
    have hsumm : Summable (fun k : ℤ => ‖fourierCoeff (sqWaveF β) k‖) := by
      have hs1 : Summable (fun k : ℤ => 3 * M * (R : ℝ) / (2 * (k : ℝ) ^ 2)) := by
        have h := (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num : (1:ℕ) < 2)
        have h2 := h.mul_left (3 * M * (R : ℝ) / 2)
        refine h2.congr (fun k => ?_)
        ring_nf
      have hs2 : Summable (fun k : ℤ => if k = 0 then (1 : ℝ) else 0) :=
        (hasSum_single (0 : ℤ) (fun b hb => by rw [if_neg hb])).summable
      have hb := hs1.add hs2
      apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) _ hb
      intro k
      rcases eq_or_ne k 0 with h | h
      · rw [h, if_pos rfl]
        simpa using norm_fourierCoeff_sqWaveF_zero β
      · rw [if_neg h, add_zero]
        rw [← hconv2 k]
        exact fourierCoeff_sqWaveF_bound2 hβ hβ1 hM0 hM1 hM2 k h
    have hps := has_pointwise_sum_fourier_series_of_summable hsumm.of_norm
      (z.arg : AddCircle (2 * Real.pi))
    rw [← hval]
    convert hps using 1
    ext i
    rw [hfour i, smul_eq_mul]

end

end Work.FIArea7
