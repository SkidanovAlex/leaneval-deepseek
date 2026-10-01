import Mathlib
import Submission.Work.ZeroFreeTables.HB88TentDefs

namespace Work.ZeroFreeTables

open scoped Classical BigOperators
noncomputable section

/-! ## Real-analysis extraction lemmas for the tent test function

This file proves `TentExtract`: the elementary real-analysis inequalities on
`tentFm`, `tentFive`, `tentSame` (definitions in `HB88TentDefs`) that the tent route to
Heath-Brown's Lemma 8.8 needs.

The only non-elementary input is the integral representation of `tentFm`: for `0 ≤ X`,
`tentFm σ X = ∫₀^X (X - t) e^{σ t} dt`, from which everything follows by pointwise
integral comparison. -/

/-- Derivative of the primitive of `t ↦ (X - t) e^{σ t}` (the `σ ≠ 0` case). -/
private theorem hasDerivAt_tentFm_prim (X σ x : ℝ) (hσ : σ ≠ 0) :
    HasDerivAt (fun t : ℝ => ((X - t)/σ + 1/σ^2) * Real.exp (σ*t)) ((X - x)*Real.exp (σ*x)) x := by
  have hb : HasDerivAt (fun t : ℝ => X - t) (-1) x := (hasDerivAt_id x).const_sub X
  have hp : HasDerivAt (fun t : ℝ => (X - t)/σ + 1/σ^2) ((-1)/σ) x := by
    have h1 : HasDerivAt (fun t : ℝ => (X - t)/σ) ((-1)/σ) x := hb.div_const σ
    exact h1.add_const (1/σ^2)
  have hE : HasDerivAt (fun t : ℝ => Real.exp (σ*t)) (Real.exp (σ*x)*σ) x := by
    have hlin : HasDerivAt (fun t : ℝ => σ * t) σ x := by
      simpa using (hasDerivAt_id x).const_mul σ
    exact (Real.hasDerivAt_exp (σ*x)).comp x hlin
  have hm := hp.mul hE
  have hfe : (fun t : ℝ => ((X - t)/σ + 1/σ^2) * Real.exp (σ*t))
      = ((fun t : ℝ => (X - t)/σ + 1/σ^2) * fun t => Real.exp (σ*t)) := by
    funext t; rw [Pi.mul_apply]
  rw [← hfe] at hm
  refine hm.congr_deriv ?_
  field_simp
  ring

/-- Derivative of the primitive of `t ↦ (X - t) t e^{σ t}` (the `σ ≠ 0` case). -/
private theorem hasDerivAt_moment1_prim (X σ x : ℝ) (hσ : σ ≠ 0) :
    HasDerivAt (fun t : ℝ => (X*t/σ - X/σ^2 - t^2/σ + 2*t/σ^2 - 2/σ^3) * Real.exp (σ*t))
      ((X - x)*x*Real.exp (σ*x)) x := by
  have hQ : HasDerivAt (fun t : ℝ => X*t/σ - X/σ^2 - t^2/σ + 2*t/σ^2 - 2/σ^3)
      (X/σ - 2*x/σ + 2/σ^2) x := by
    have h1 : HasDerivAt (fun t : ℝ => X*t/σ) (X/σ) x := by
      have : HasDerivAt (fun t : ℝ => X*t) X x := by simpa using (hasDerivAt_id x).const_mul X
      simpa using this.div_const σ
    have h2 : HasDerivAt (fun t : ℝ => X/σ^2) 0 x := hasDerivAt_const x _
    have h3 : HasDerivAt (fun t : ℝ => t^2/σ) ((2*x)/σ) x := by
      have : HasDerivAt (fun t : ℝ => t^2) (2*x) x := by simpa using hasDerivAt_pow 2 x
      simpa using this.div_const σ
    have h4 : HasDerivAt (fun t : ℝ => 2*t/σ^2) (2/σ^2) x := by
      have : HasDerivAt (fun t : ℝ => 2*t) 2 x := by simpa using (hasDerivAt_id x).const_mul 2
      simpa using this.div_const (σ^2)
    have h5 : HasDerivAt (fun t : ℝ => 2/σ^3) 0 x := hasDerivAt_const x _
    have hQ0 := (((h1.sub h2).sub h3).add h4).sub h5
    have hQfe : (fun t : ℝ => X*t/σ - X/σ^2 - t^2/σ + 2*t/σ^2 - 2/σ^3)
        = ((((fun t : ℝ => X*t/σ) - fun t => X/σ^2) - fun t => t^2/σ) + fun t => 2*t/σ^2)
            - fun t => 2/σ^3 := by
      funext t; simp only [Pi.sub_apply, Pi.add_apply]
    rw [← hQfe] at hQ0
    refine hQ0.congr_deriv ?_
    ring
  have hE : HasDerivAt (fun t : ℝ => Real.exp (σ*t)) (Real.exp (σ*x)*σ) x := by
    have hlin : HasDerivAt (fun t : ℝ => σ * t) σ x := by
      simpa using (hasDerivAt_id x).const_mul σ
    exact (Real.hasDerivAt_exp (σ*x)).comp x hlin
  have hm := hQ.mul hE
  have hfe : (fun t : ℝ => (X*t/σ - X/σ^2 - t^2/σ + 2*t/σ^2 - 2/σ^3) * Real.exp (σ*t))
      = ((fun t : ℝ => X*t/σ - X/σ^2 - t^2/σ + 2*t/σ^2 - 2/σ^3) * fun t => Real.exp (σ*t)) := by
    funext t; rw [Pi.mul_apply]
  rw [← hfe] at hm
  refine hm.congr_deriv ?_
  field_simp
  ring

/-- **Integral representation of the tent Laplace transform.**  For `0 ≤ X`,
`tentFm σ X = ∫₀^X (X - t) e^{σ t} dt`. -/
theorem tentFm_eq_integral (X σ : ℝ) (hX : 0 ≤ X) :
    tentFm σ X = ∫ t in (0:ℝ)..X, (X - t) * Real.exp (σ * t) := by
  rcases eq_or_ne σ 0 with hσ | hσ
  · subst hσ
    rw [tentFm, if_pos rfl]
    have hcongr : (∫ t in (0:ℝ)..X, (X - t) * Real.exp (0 * t)) = ∫ t in (0:ℝ)..X, (X - t) := by
      apply intervalIntegral.integral_congr
      intro t _; simp
    rw [hcongr]
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => X) (g := fun t : ℝ => t)
          (continuous_const.intervalIntegrable 0 X) (continuous_id.intervalIntegrable 0 X)]
    rw [intervalIntegral.integral_const, integral_id]
    ring
  · rw [tentFm, if_neg hσ]
    have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) X,
        HasDerivAt (fun t : ℝ => ((X - t)/σ + 1/σ^2) * Real.exp (σ*t))
          ((X - x)*Real.exp (σ*x)) x := fun x _ => hasDerivAt_tentFm_prim X σ x hσ
    have hint : IntervalIntegrable (fun t : ℝ => (X - t)*Real.exp (σ*t)) MeasureTheory.volume (0:ℝ) X :=
      (by fun_prop : Continuous (fun t : ℝ => (X - t)*Real.exp (σ*t))).intervalIntegrable 0 X
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp only [sub_self, zero_div, zero_add, sub_zero, mul_zero, Real.exp_zero, mul_one]
    field_simp
    ring

/-- The closed form of `∫₀^X (X - t) t e^{σ t} dt`, in the shape used by the extraction
inequalities. -/
def tentM1 (X σ : ℝ) : ℝ :=
  Real.exp (X * σ) * ((X * σ - 2) + (X * σ + 2) * Real.exp (-(X * σ))) / σ ^ 3

/-- **First moment of the tent.**  For `σ ≠ 0`, the first moment of the tent transform is
`∫₀^X (X - t) t e^{σ t} dt = tentM1 X σ`. -/
theorem moment1_integral (X σ : ℝ) (hσ : σ ≠ 0) :
    (∫ t in (0:ℝ)..X, (X - t) * t * Real.exp (σ * t)) = tentM1 X σ := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) X,
      HasDerivAt (fun t : ℝ => (X*t/σ - X/σ^2 - t^2/σ + 2*t/σ^2 - 2/σ^3) * Real.exp (σ*t))
        ((X - x)*x*Real.exp (σ*x)) x := fun x _ => hasDerivAt_moment1_prim X σ x hσ
  have hint : IntervalIntegrable (fun t : ℝ => (X - t)*t*Real.exp (σ*t)) MeasureTheory.volume (0:ℝ) X :=
    (by fun_prop : Continuous (fun t : ℝ => (X - t)*t*Real.exp (σ*t))).intervalIntegrable 0 X
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  unfold tentM1
  have hexpmul : Real.exp (X * σ) * Real.exp (-(X * σ)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hE : Real.exp (X * σ) * ((X * σ - 2) + (X * σ + 2) * Real.exp (-(X * σ)))
      = Real.exp (X * σ)*(X*σ - 2) + (X*σ + 2) := by
    rw [mul_add]
    congr 1
    calc Real.exp (X * σ) * ((X * σ + 2) * Real.exp (-(X * σ)))
        = (X * σ + 2) * (Real.exp (X * σ) * Real.exp (-(X * σ))) := by ring
      _ = (X * σ + 2) := by rw [hexpmul, mul_one]
  rw [hE]
  have harg : σ * X = X * σ := by ring
  rw [harg]
  simp only [mul_zero, Real.exp_zero, mul_one, zero_pow (by norm_num : (2:ℕ) ≠ 0),
    zero_div, sub_zero]
  field_simp
  ring

/-- The elementary inequality `1 - e^{-s} ≤ s`. -/
theorem one_sub_exp_neg_le (s : ℝ) : 1 - Real.exp (-s) ≤ s := by
  have := Real.add_one_le_exp (-s); linarith

/-- `σ ↦ tentFm σ X` is nondecreasing (for `0 ≤ X`). -/
theorem tentFm_mono (X : ℝ) (hX : 0 ≤ X) : Monotone (fun σ : ℝ => tentFm σ X) := by
  intro σ₁ σ₂ h
  change tentFm σ₁ X ≤ tentFm σ₂ X
  rw [tentFm_eq_integral X σ₁ hX, tentFm_eq_integral X σ₂ hX]
  apply intervalIntegral.integral_mono_on hX
  · exact (by fun_prop : Continuous (fun t : ℝ => (X - t)*Real.exp (σ₁*t))).intervalIntegrable 0 X
  · exact (by fun_prop : Continuous (fun t : ℝ => (X - t)*Real.exp (σ₂*t))).intervalIntegrable 0 X
  · intro t ht
    rw [Set.mem_Icc] at ht
    have hXt : 0 ≤ X - t := by linarith [ht.2]
    have hexp : Real.exp (σ₁*t) ≤ Real.exp (σ₂*t) := Real.exp_le_exp.mpr (by nlinarith [ht.1])
    exact mul_le_mul_of_nonneg_left hexp hXt

/-- For `0 ≤ X` and `0 ≤ b`, `c ↦ tentFm c X - tentFm (c - b) X` is nondecreasing. -/
theorem tentFm_sub_mono_c (X : ℝ) (hX : 0 ≤ X) (b : ℝ) (hb : 0 ≤ b) :
    Monotone (fun c : ℝ => tentFm c X - tentFm (c - b) X) := by
  intro c₁ c₂ h
  change tentFm c₁ X - tentFm (c₁ - b) X ≤ tentFm c₂ X - tentFm (c₂ - b) X
  have hI1 : IntervalIntegrable (fun t : ℝ => (X - t)*Real.exp (c₁*t)) MeasureTheory.volume 0 X :=
    (by fun_prop : Continuous (fun t : ℝ => (X - t)*Real.exp (c₁*t))).intervalIntegrable 0 X
  have hI2 : IntervalIntegrable (fun t : ℝ => (X - t)*Real.exp ((c₁-b)*t)) MeasureTheory.volume 0 X :=
    (by fun_prop : Continuous (fun t : ℝ => (X - t)*Real.exp ((c₁-b)*t))).intervalIntegrable 0 X
  have hI3 : IntervalIntegrable (fun t : ℝ => (X - t)*Real.exp (c₂*t)) MeasureTheory.volume 0 X :=
    (by fun_prop : Continuous (fun t : ℝ => (X - t)*Real.exp (c₂*t))).intervalIntegrable 0 X
  have hI4 : IntervalIntegrable (fun t : ℝ => (X - t)*Real.exp ((c₂-b)*t)) MeasureTheory.volume 0 X :=
    (by fun_prop : Continuous (fun t : ℝ => (X - t)*Real.exp ((c₂-b)*t))).intervalIntegrable 0 X
  rw [tentFm_eq_integral X c₁ hX, tentFm_eq_integral X (c₁-b) hX,
      tentFm_eq_integral X c₂ hX, tentFm_eq_integral X (c₂-b) hX]
  rw [← intervalIntegral.integral_sub hI1 hI2, ← intervalIntegral.integral_sub hI3 hI4]
  apply intervalIntegral.integral_mono_on hX
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      (X - t)*Real.exp (c₁*t) - (X - t)*Real.exp ((c₁-b)*t))).intervalIntegrable 0 X
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      (X - t)*Real.exp (c₂*t) - (X - t)*Real.exp ((c₂-b)*t))).intervalIntegrable 0 X
  · intro t ht
    rw [Set.mem_Icc] at ht
    have hXt : 0 ≤ X - t := by linarith [ht.2]
    have hn : 0 ≤ 1 - Real.exp (-(b*t)) := by
      have : Real.exp (-(b*t)) ≤ 1 := by
        rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith [ht.1, hb])
      linarith
    have hexp : Real.exp (c₁*t) ≤ Real.exp (c₂*t) := Real.exp_le_exp.mpr (by nlinarith [ht.1])
    have hmm := mul_le_mul_of_nonneg_left hexp (mul_nonneg hXt hn)
    calc (X - t)*Real.exp (c₁*t) - (X - t)*Real.exp ((c₁-b)*t)
        = (X - t)*(1 - Real.exp (-(b*t)))*Real.exp (c₁*t) := by
          rw [show (c₁-b)*t = c₁*t + -(b*t) by ring, Real.exp_add]; ring
      _ ≤ (X - t)*(1 - Real.exp (-(b*t)))*Real.exp (c₂*t) := hmm
      _ = (X - t)*Real.exp (c₂*t) - (X - t)*Real.exp ((c₂-b)*t) := by
          rw [show (c₂-b)*t = c₂*t + -(b*t) by ring, Real.exp_add]; ring

/-- **Sharp (tangent) extraction.**  For `b ≥ 0`, `c > 0`,
`tentFm c X - tentFm (c - b) X ≤ b · tentM1 X c`. -/
theorem tentFm_sharp (X : ℝ) (hX : 0 < X) (b c : ℝ) (hb : 0 ≤ b) (hc : 0 < c) :
    tentFm c X - tentFm (c - b) X ≤ b * tentM1 X c := by
  have hXle : (0:ℝ) ≤ X := le_of_lt hX
  have hcne : c ≠ 0 := ne_of_gt hc
  have hI1 : IntervalIntegrable (fun t : ℝ => (X - t)*Real.exp (c*t)) MeasureTheory.volume 0 X :=
    (by fun_prop : Continuous (fun t : ℝ => (X - t)*Real.exp (c*t))).intervalIntegrable 0 X
  have hI2 : IntervalIntegrable (fun t : ℝ => (X - t)*Real.exp ((c-b)*t)) MeasureTheory.volume 0 X :=
    (by fun_prop : Continuous (fun t : ℝ => (X - t)*Real.exp ((c-b)*t))).intervalIntegrable 0 X
  have hI3 : IntervalIntegrable (fun t : ℝ =>
      (X - t)*Real.exp (c*t) - (X - t)*Real.exp ((c-b)*t)) MeasureTheory.volume 0 X :=
    (by fun_prop : Continuous _).intervalIntegrable 0 X
  have hI4 : IntervalIntegrable (fun t : ℝ => (X - t)*Real.exp (c*t)*(b*t)) MeasureTheory.volume 0 X :=
    (by fun_prop : Continuous _).intervalIntegrable 0 X
  rw [tentFm_eq_integral X c hXle, tentFm_eq_integral X (c-b) hXle,
      ← intervalIntegral.integral_sub hI1 hI2]
  have hmono : (∫ t in (0:ℝ)..X, ((X - t)*Real.exp (c*t) - (X - t)*Real.exp ((c-b)*t)))
      ≤ ∫ t in (0:ℝ)..X, (X - t)*Real.exp (c*t)*(b*t) := by
    apply intervalIntegral.integral_mono_on hXle hI3 hI4
    intro t ht
    rw [Set.mem_Icc] at ht
    have hXt : 0 ≤ X - t := by linarith [ht.2]
    have hkey : 1 - Real.exp (-(b*t)) ≤ b*t := one_sub_exp_neg_le (b*t)
    have hfac : 0 ≤ (X - t)*Real.exp (c*t) := mul_nonneg hXt (Real.exp_pos _).le
    have hmm := mul_le_mul_of_nonneg_left hkey hfac
    calc (X - t)*Real.exp (c*t) - (X - t)*Real.exp ((c-b)*t)
        = (X - t)*Real.exp (c*t)*(1 - Real.exp (-(b*t))) := by
          rw [show (c-b)*t = c*t + -(b*t) by ring, Real.exp_add]; ring
      _ ≤ (X - t)*Real.exp (c*t)*(b*t) := hmm
  calc (∫ t in (0:ℝ)..X, ((X - t)*Real.exp (c*t) - (X - t)*Real.exp ((c-b)*t)))
      ≤ ∫ t in (0:ℝ)..X, (X - t)*Real.exp (c*t)*(b*t) := hmono
    _ = b * (∫ t in (0:ℝ)..X, (X - t)*t*Real.exp (c*t)) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t _; ring
    _ = b * tentM1 X c := by rw [moment1_integral X c hcne]

/-- **Crude extraction.**  For `b ≥ 0`, `c > 0`, `tentFm c X - tentFm (c - b) X ≤ b X e^{Xc}/c²`. -/
theorem tentFm_crude (X : ℝ) (hX : 0 < X) (b c : ℝ) (hb : 0 ≤ b) (hc : 0 < c) :
    tentFm c X - tentFm (c - b) X ≤ b * X * Real.exp (X * c) / c ^ 2 := by
  have hsharp := tentFm_sharp X hX b c hb hc
  have hmain : tentM1 X c ≤ X * Real.exp (X*c)/c^2 := by
    unfold tentM1
    have hexpmul : Real.exp (X*c)*Real.exp (-(X*c)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hE : Real.exp (X*c)*((X*c-2)+(X*c+2)*Real.exp (-(X*c)))
        = Real.exp (X*c)*(X*c-2)+(X*c+2) := by
      rw [mul_add]; congr 1
      calc Real.exp (X*c)*((X*c+2)*Real.exp (-(X*c)))
          = (X*c+2)*(Real.exp (X*c)*Real.exp (-(X*c))) := by ring
        _ = (X*c+2) := by rw [hexpmul, mul_one]
    rw [hE]
    have hc3 : (0:ℝ) < c^3 := by positivity
    have hc2 : (0:ℝ) < c^2 := by positivity
    have h2exp : X*c + 2 ≤ 2*Real.exp (X*c) := by
      have := Real.add_one_le_exp (X*c); nlinarith [mul_nonneg hX.le hc.le]
    rw [div_le_div_iff₀ hc3 hc2]
    nlinarith [h2exp, sq_nonneg c, mul_pos hX hc]
  have hfac : b * tentM1 X c ≤ b * X * Real.exp (X*c)/c^2 := by
    have := mul_le_mul_of_nonneg_left hmain hb
    calc b * tentM1 X c ≤ b * (X * Real.exp (X*c)/c^2) := this
      _ = b * X * Real.exp (X*c)/c^2 := by ring
  linarith [hsharp, hfac]

theorem TentExtract (X A : ℝ) (hX : 0 < X) (hA : A < X / 2) :
    (∀ b c : ℝ, 0 ≤ b → 0 < c →
      Work.ZeroFreeTables.tentFm c X - Work.ZeroFreeTables.tentFm (c - b) X
        ≤ b * X * Real.exp (X * c) / c ^ 2) ∧
    (∀ b c : ℝ, 0 ≤ b → 0 < c →
      Work.ZeroFreeTables.tentFm c X - Work.ZeroFreeTables.tentFm (c - b) X ≤
        b * Real.exp (X * c) * ((X * c - 2) + (X * c + 2) * Real.exp (-(X * c))) / c ^ 3) ∧
    (∀ b c : ℝ, 0 ≤ b → 0 < c →
      b * Real.exp (X * c) * ((X * c - 2) + (X * c + 2) * Real.exp (-(X * c)))
        < X * (X / 2 - A) * c ^ 3 → Work.ZeroFreeTables.tentFive X A b c < 0) ∧
    (∀ b c : ℝ, 0 ≤ b → 0 < c → 2 * b < (X / 2 - A) * c ^ 2 * Real.exp (-(X * c)) →
      Work.ZeroFreeTables.tentSame X A b c < 0) ∧
    (∀ b c b' c' : ℝ, 0 ≤ b → b ≤ b' → c ≤ c' →
      Work.ZeroFreeTables.tentFive X A b c ≤ Work.ZeroFreeTables.tentFive X A b' c') ∧
    (∀ A' : ℝ, A ≤ A' → ∀ b c : ℝ,
      Work.ZeroFreeTables.tentFive X A b c ≤ Work.ZeroFreeTables.tentFive X A' b c) := by
  have hXle : (0:ℝ) ≤ X := le_of_lt hX
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b c hb hc
    exact tentFm_crude X hX b c hb hc
  · intro b c hb hc
    have h := tentFm_sharp X hX b c hb hc
    have heq : b * tentM1 X c
        = b * Real.exp (X * c) * ((X * c - 2) + (X * c + 2) * Real.exp (-(X * c))) / c ^ 3 := by
      unfold tentM1; ring
    rw [heq] at h
    exact h
  · intro b c hb hc hH
    have hsharp := tentFm_sharp X hX b c hb hc
    have hlt : b * tentM1 X c < X * (X / 2 - A) := by
      have hc3 : (0:ℝ) < c^3 := by positivity
      have heq : b * tentM1 X c
          = b * Real.exp (X * c) * ((X * c - 2) + (X * c + 2) * Real.exp (-(X * c))) / c ^ 3 := by
        unfold tentM1; ring
      rw [heq, div_lt_iff₀ hc3]
      exact hH
    have hkey : X * (X / 2 - A) = X^2/2 - X*A := by ring
    unfold tentFive
    linarith [hsharp, hlt, hkey]
  · intro b c hb hc h4
    have hcrude := tentFm_crude X hX b c hb hc
    have hmult := mul_lt_mul_of_pos_right h4 (by positivity : (0:ℝ) < X * Real.exp (X*c)/c^2)
    have hrhs : ((X/2 - A)*c^2*Real.exp (-(X*c))) * (X*Real.exp (X*c)/c^2) = X*(X/2 - A) := by
      have hexpmul' : Real.exp (-(X*c)) * Real.exp (X*c) = 1 := by
        rw [mul_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
      field_simp
      rw [mul_assoc, hexpmul', mul_one]
    have h2 : 2 * (b * X * Real.exp (X*c)/c^2) < X*(X/2 - A) := by
      rw [hrhs] at hmult
      have heq : 2*b*(X*Real.exp (X*c)/c^2) = 2*(b*X*Real.exp (X*c)/c^2) := by ring
      linarith [hmult, heq]
    have hkey : X * (X / 2 - A) = X^2/2 - X*A := by ring
    have hstep : (2:ℝ)*(tentFm c X - tentFm (c-b) X) ≤ 2*(b*X*Real.exp (X*c)/c^2) := by
      linarith [hcrude]
    unfold tentSame
    linarith [hstep, h2, hkey]
  · intro b c b' c' hb hbb hcc
    have h1 : tentFive X A b c ≤ tentFive X A b c' := by
      unfold tentFive
      have := (tentFm_sub_mono_c X hXle b hb) hcc
      linarith [this]
    have h2 : tentFive X A b c' ≤ tentFive X A b' c' := by
      unfold tentFive
      have := (tentFm_mono X hXle) (show c' - b' ≤ c' - b by linarith)
      linarith [this]
    exact le_trans h1 h2
  · intro A' hA' b c
    unfold tentFive
    have := mul_le_mul_of_nonneg_left hA' hXle
    linarith [this]

end
end Work.ZeroFreeTables
