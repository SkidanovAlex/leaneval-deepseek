import Submission.NBody.Action
import Submission.NBody.MadernaEstimate
import Submission.NBody.CollisionFreeLimit
import Mathlib

/-!
# The length of action minimisers (Liu--Yan--Zhou route, Sections 3--4)

This module proves the *upper bound on the length* of an action minimiser with canonical
parameter, the basic quantitative input of the Liu--Yan--Zhou geometric proof of the
hyperbolic-motion theorem.

Ingredients:

* the trivial upper bound (`lyz_length_le_actionPot`): since
  `(1/2)‖v‖_[m]² + h ≥ √(2h)‖v‖_[m]`, the *mass length* `∫ ‖γ̇‖_[m]` of a minimiser joining `x` to
  `y` is at most `(√(2h))⁻¹ φ_h(x,y)`;
* the straight-line bound (`actionPot_le_of_straight`): the action potential between two
  configurations joined by a collision-free segment is bounded by `√(2h)·D` plus the potential
  integral along the segment, where `D = ‖y - x‖_[m]`.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- Along a segment `x + t • b` (`t ∈ [0,D]`) that is collision free, the rescaled configurations
`x + s • (c • b)` (`s ∈ [0, D/c]`) are collision free. -/
lemma withoutCollisions_add_mul_smul {x b : EN E N} {c D s : ℝ} (hc : 0 < c)
    (hs : s ∈ Set.Icc 0 (D / c)) (hnc : ∀ t ∈ Set.Icc (0:ℝ) D, WithoutCollisions (x + t • b)) :
    WithoutCollisions (x + s • (c • b)) := by
  have hs0 : 0 ≤ s := hs.1
  have hs1 : s ≤ D / c := hs.2
  have hsc : s * c ≤ D := by
    rw [← le_div_iff₀ hc]
    exact hs1
  have hmem : s * c ∈ Set.Icc (0:ℝ) D := ⟨mul_nonneg hs0 hc.le, hsc⟩
  have heq : x + s • (c • b) = x + (s * c) • b := by rw [smul_smul]
  rw [heq]
  exact hnc (s * c) hmem

/-- The derivative of the straight path `s ↦ x + s • v`. -/
lemma deriv_const_add_const_smul (x v : EN E N) (s : ℝ) :
    deriv (fun u : ℝ => x + u • v) s = v := by
  simpa using (((hasDerivAt_id s).smul_const v).const_add x).deriv

/-- The straight path is absolutely continuous. -/
lemma absolutelyContinuousOnInterval_const_add_const_smul (x v : EN E N) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun u : ℝ => x + u • v) a b := by
  have hLip : LipschitzWith ‖v‖₊ (fun u : ℝ => x + u • v) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro s t
    have h1 : (x + s • v) - (x + t • v) = (s - t) • v := by module
    rw [dist_eq_norm, h1, norm_smul, Real.dist_eq]
    exact le_of_eq (mul_comm _ _)
  exact hLip.lipschitzOnWith.absolutelyContinuousOnInterval

/-- **Straight-line bound for the action potential.**  If `‖b‖_[m] = 1`, `D > 0` and the whole
segment `{x + t • b : t ∈ [0,D]}` is collision free, then

    `φ_h(x, x + D • b) ≤ √(2h) D + (√(2h))⁻¹ ∫₀^D U(x + t b) dt`.

The path used is the constant-speed curve `η s = x + (√(2h) s) • b`. -/
theorem actionPot_le_of_straight {m : Fin N → ℝ} {h : ℝ} (hh : 0 < h)
    (hm : ∀ i, 0 ≤ m i) {b : EN E N} (hb : ‖b‖_[m] = 1) {D : ℝ} (hD : 0 < D) (x : EN E N)
    (hnc : ∀ t ∈ Set.Icc (0:ℝ) D, WithoutCollisions (x + t • b)) :
    actionPot m h x (x + D • b) ≤
      ENNReal.ofReal (Real.sqrt (2 * h) * D) +
        ENNReal.ofReal ((Real.sqrt (2 * h))⁻¹ * ∫ t in (0:ℝ)..D, U m (x + t • b)) := by
  set c : ℝ := Real.sqrt (2 * h) with hcdef
  have hc : 0 < c := Real.sqrt_pos.mpr (by linarith)
  have hc2 : c ^ 2 = 2 * h := by rw [hcdef, Real.sq_sqrt (by linarith)]
  set τ : ℝ := D / c with hτdef
  have hτ : 0 < τ := div_pos hD hc
  have hτc : τ * c = D := by rw [hτdef, div_mul_cancel₀ _ hc.ne']
  set η : ℝ → EN E N := fun s => x + s • (c • b) with hηdef
  have hηeq : ∀ s : ℝ, η s = x + s • (c • b) := fun s => rfl
  have hη0 : η 0 = x := by simp [hηdef]
  have hητ : η τ = x + D • b := by
    rw [hηeq]
    rw [show τ • (c • b) = D • b by rw [smul_smul, hτc]]
  refine (actionPot_le_of hτ hη0 hητ
    (absolutelyContinuousOnInterval_const_add_const_smul x (c • b) 0 τ)).trans (le_of_eq ?_)
  have hderiv : ∀ s : ℝ, deriv η s = c • b := fun s => deriv_const_add_const_smul x (c • b) s
  have hkin : (1 / 2) * ∑ i, m i * ‖(c • b) i‖ ^ 2 = h := by
    have hsum : ∑ i, m i * ‖(c • b) i‖ ^ 2 = c ^ 2 * ‖b‖_[m] ^ 2 := by
      have hnn : 0 ≤ ∑ i, m i * ‖b i‖ ^ 2 :=
        Finset.sum_nonneg fun i _ => mul_nonneg (hm i) (sq_nonneg _)
      rw [weightedNorm, Real.sq_sqrt hnn, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [PiLp.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    rw [hsum, hb, one_pow, mul_one]
    linarith [hc2]
  have hpt : ∀ s ∈ Set.Ioc (0:ℝ) τ, lagrangian m h (η s) (deriv η s)
      = ENNReal.ofReal (2 * h) + ENNReal.ofReal (U m (η s)) := by
    intro s hs
    have hnc' : WithoutCollisions (η s) := by
      rw [hηeq]
      exact withoutCollisions_add_mul_smul (c := c) hc ⟨hs.1.le, hs.2⟩ hnc
    rw [hderiv s, lagrangian, if_pos hnc']
    have hU : 0 ≤ U m (η s) := U_nonneg hm (η s)
    have hkey : (1 / 2) * ∑ i, m i * ‖(c • b) i‖ ^ 2 + U m (η s) + h = 2 * h + U m (η s) := by
      rw [hkin]; ring
    rw [hkey, ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ 2 * h) hU]
  have hsub : (∫⁻ s in Set.Ioc (0:ℝ) τ, ENNReal.ofReal (U m (η s)))
      = ENNReal.ofReal c⁻¹ * ∫⁻ u in Set.Ioc (0:ℝ) D, ENNReal.ofReal (U m (x + u • b)) := by
    set F : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (U m (x + u • b)) with hFdef
    have hfun : ∀ s : ℝ, ENNReal.ofReal (U m (η s)) = F (c * s) := by
      intro s
      rw [hηeq, show x + s • (c • b) = x + (c * s) • b by rw [smul_smul, mul_comm]]
    rw [setLIntegral_congr_fun measurableSet_Ioc (fun s _ => hfun s)]
    rw [Commons.MeasureTheory.Integral.setLIntegral_Ioc_comp_mul_left F hc, mul_zero,
      show c * τ = D by rw [mul_comm, hτc]]
  have hUcont : ContinuousOn (fun u : ℝ => U m (x + u • b)) (Set.Icc (0:ℝ) D) := by
    have hcont : ContinuousOn (fun u : ℝ => x + u • b) (Set.Icc (0:ℝ) D) := by fun_prop
    exact continuousOn_U.comp hcont (fun u hu => hnc u hu)
  have hint : IntervalIntegrable (fun u : ℝ => U m (x + u • b)) volume (0:ℝ) D := by
    refine hUcont.intervalIntegrable_of_Icc hD.le
  have hint2 : Integrable (fun u : ℝ => U m (x + u • b)) (volume.restrict (Set.Ioc (0:ℝ) D)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hD.le).mp hint
  have hbridge : (∫⁻ u in Set.Ioc (0:ℝ) D, ENNReal.ofReal (U m (x + u • b)))
      = ENNReal.ofReal (∫ u in (0:ℝ)..D, U m (x + u • b)) := by
    rw [intervalIntegral.integral_of_le hD.le]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint2
      (Filter.Eventually.of_forall fun u => U_nonneg hm _)).symm
  have h2hτ : 2 * h * τ = c * D := by
    have h2hc : 2 * h = c * c := by linarith [hc2]
    rw [h2hc, hτdef]
    field_simp
  rw [actionOn, setLIntegral_congr_fun measurableSet_Ioc hpt,
    lintegral_add_left measurable_const, setLIntegral_const,
    Real.volume_Ioc, sub_zero, hsub, hbridge, ← ENNReal.ofReal_mul (by linarith : (0:ℝ) ≤ 2 * h),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), h2hτ]



section MassLength

/-- The **mass length** of a curve: `∫ ‖γ̇(t)‖_[m] dt` (the length measured with the mass norm,
which is the configuration norm adapted to the action). -/
noncomputable def massLength (m : Fin N → ℝ) (γ : ℝ → EN E N) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖deriv γ t‖_[m]

lemma kinetic_eq_half_weightedNorm_sq' {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (v : EN E N) :
    kinetic m v = (1 / 2) * (‖v‖_[m]) ^ 2 := by
  have h : 0 ≤ ∑ i, m i * ‖v i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hm i) (sq_nonneg _)
  show (1 / 2) * ∑ i, m i * ‖v i‖ ^ 2 = (1 / 2) * (weightedNorm m v) ^ 2
  rw [weightedNorm, Real.sq_sqrt h]

/-- The weighted norm is continuous. -/
lemma continuous_weightedNorm' (m : Fin N → ℝ) : Continuous (fun v : EN E N => ‖v‖_[m]) := by
  simp only [weightedNorm]
  fun_prop

/-- **AM--GM for the Lagrangian.**  `√(2h)‖v‖_[m] ≤ L_h(q,v)`. -/
lemma ofReal_sqrt_mul_weightedNorm_le_lagrangian {m : Fin N → ℝ} {h : ℝ} (hh : 0 < h)
    (hm : ∀ i, 0 ≤ m i) (q v : EN E N) :
    ENNReal.ofReal (Real.sqrt (2 * h) * ‖v‖_[m]) ≤ lagrangian m h q v := by
  by_cases hq : WithoutCollisions q
  · rw [lagrangian, if_pos hq]
    refine ENNReal.ofReal_le_ofReal ?_
    have hU : 0 ≤ U m q := U_nonneg hm q
    have hk : kinetic m v = (1 / 2) * (‖v‖_[m]) ^ 2 := kinetic_eq_half_weightedNorm_sq' hm v
    have hx : 0 ≤ ‖v‖_[m] := weightedNorm_nonneg m v
    have hamgm : Real.sqrt (2 * h) * ‖v‖_[m] ≤ (1 / 2) * (‖v‖_[m]) ^ 2 + h := by
      have h2 : Real.sqrt (2 * h) * ‖v‖_[m] ≤ (1 / 2) * (‖v‖_[m]) ^ 2 + h := by
        nlinarith [sq_nonneg (‖v‖_[m] - Real.sqrt (2 * h)),
          Real.sq_sqrt (show (0:ℝ) ≤ 2 * h by linarith), Real.sqrt_nonneg (2 * h)]
      exact h2
    have hsum : (1 / 2) * ∑ i, m i * ‖v i‖ ^ 2 = (1 / 2) * (‖v‖_[m]) ^ 2 := by
      rw [← hk]
      rfl
    rw [hsum]
    linarith
  · rw [lagrangian, if_neg hq]
    exact le_top

/-- The mass norm of the derivative is ae-strongly-measurable along an absolutely continuous
curve. -/
lemma aestronglyMeasurable_weightedNorm_deriv {m : Fin N → ℝ} {γ : ℝ → EN E N} {a b : ℝ}
    (hac : AbsolutelyContinuousOnInterval γ a b) :
    AEStronglyMeasurable (fun t : ℝ => ‖deriv γ t‖_[m])
      (volume.restrict (Set.Ioc a b)) := by
  exact (continuous_weightedNorm' m).comp_aestronglyMeasurable
    (Commons.MeasureTheory.Integral.aestronglyMeasurable_deriv_of_absolutelyContinuousOnInterval hac)

/-- **The length of an action minimiser.**  For a collision-free absolutely continuous curve with
finite action, `√(2h) · massLength ≤ actionOn`, because the Lagrangian dominates
`√(2h)‖γ̇‖_[m]` pointwise (AM--GM). -/
theorem massLength_le_actionOn {m : Fin N → ℝ} {h : ℝ} (hh : 0 < h) (hm : ∀ i, 0 ≤ m i)
    {γ : ℝ → EN E N} {a b : ℝ} (hab : a ≤ b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hnc : ∀ t ∈ Set.Icc a b, WithoutCollisions (γ t))
    (hfin : actionOn m h γ a b < ⊤) :
    Real.sqrt (2 * h) * massLength m γ a b ≤ (actionOn m h γ a b).toReal := by
  have hsqrt : 0 < Real.sqrt (2 * h) := Real.sqrt_pos.mpr (by linarith)
  have hpt : ∀ t ∈ Set.Ioc a b,
      ENNReal.ofReal (Real.sqrt (2 * h) * ‖deriv γ t‖_[m]) ≤ lagrangian m h (γ t) (deriv γ t) := by
    intro t ht
    have hnc' : WithoutCollisions (γ t) := hnc t ⟨ht.1.le, ht.2⟩
    exact ofReal_sqrt_mul_weightedNorm_le_lagrangian hh hm (γ t) (deriv γ t)
  have h1 : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (Real.sqrt (2 * h) * ‖deriv γ t‖_[m]))
      ≤ actionOn m h γ a b := by
    rw [actionOn]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hpt t ht
  have hsplit : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (Real.sqrt (2 * h) * ‖deriv γ t‖_[m]))
      = ENNReal.ofReal (Real.sqrt (2 * h)) * ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv γ t‖_[m]) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun t => ?_
    rw [ENNReal.ofReal_mul hsqrt.le]
  have hne : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv γ t‖_[m])) ≠ ⊤ := by
    intro htop
    have hAtop : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (Real.sqrt (2 * h) * ‖deriv γ t‖_[m])) = ⊤ := by
      rw [hsplit, htop, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hsqrt))]
    rw [hAtop] at h1
    exact absurd h1 (not_le.mpr hfin)
  have hmeas := aestronglyMeasurable_weightedNorm_deriv (m := m) hac
  have hint : Integrable (fun t : ℝ => ‖deriv γ t‖_[m]) (volume.restrict (Set.Ioc a b)) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas
      (Filter.Eventually.of_forall fun t => weightedNorm_nonneg m _)).mp hne
  have hbridge : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv γ t‖_[m]))
      = ENNReal.ofReal (massLength m γ a b) := by
    rw [massLength, intervalIntegral.integral_of_le hab]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun t => weightedNorm_nonneg m _)).symm
  have hmain : ENNReal.ofReal (Real.sqrt (2 * h) * massLength m γ a b) ≤ actionOn m h γ a b := by
    rw [hsplit, hbridge, ← ENNReal.ofReal_mul hsqrt.le] at h1
    exact h1
  have hml : 0 ≤ massLength m γ a b :=
    intervalIntegral.integral_nonneg_of_forall hab fun t => weightedNorm_nonneg m _
  have := ENNReal.toReal_mono hfin.ne hmain
  rwa [ENNReal.toReal_ofReal (mul_nonneg hsqrt.le hml)] at this

end MassLength

/-- The mass length is non-negative on a non-degenerate interval. -/
lemma massLength_nonneg {m : Fin N → ℝ} {γ : ℝ → EN E N} {a b : ℝ} (hab : a ≤ b) :
    0 ≤ massLength m γ a b :=
  intervalIntegral.integral_nonneg_of_forall hab fun t => weightedNorm_nonneg m _

/-- **Lintegral chord bound.**  The mass norm of the displacement is at most the `∫⁻` of the mass
norm of the derivative. -/
theorem ofReal_weightedNorm_sub_le_lintegral [Nontrivial E] {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    {γ : ℝ → EN E N} {a b : ℝ} (hab : a ≤ b) (hac : AbsolutelyContinuousOnInterval γ a b) :
    ENNReal.ofReal (‖γ b - γ a‖_[m])
      ≤ ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv γ t‖_[m]) := by
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  set Γ : ℝ → EN E N := fun s => γ s - γ a with hΓ
  set g : ℝ → ℝ := fun s => ‖Γ s‖_[m] with hg
  have hΓac : AbsolutelyContinuousOnInterval Γ a b :=
    hac.sub (LipschitzWith.const (γ a)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hgac : AbsolutelyContinuousOnInterval g a b :=
    absolutelyContinuousOnInterval_weightedNorm_comp hm0 hΓac
  have hz : Γ a = 0 := by
    show γ a - γ a = 0
    exact sub_self _
  have hga : g a = 0 := by
    show ‖Γ a‖_[m] = 0
    rw [hz, weightedNorm]
    simp
  have hintg : IntervalIntegrable (fun t => deriv g t) volume a b := hgac.intervalIntegrable_deriv
  have hintabs : IntervalIntegrable (fun t => |deriv g t|) volume a b := hintg.abs
  have hftc : ∫ t in a..b, deriv g t = g b - g a := hgac.integral_deriv_eq_sub
  have hmono : ∫ t in a..b, deriv g t ≤ ∫ t in a..b, |deriv g t| :=
    intervalIntegral.integral_mono_on hab hintg hintabs fun t _ => le_abs_self _
  have hstep : ENNReal.ofReal (g b - g a) ≤ ENNReal.ofReal (∫ t in a..b, |deriv g t|) := by
    rw [← hftc]; exact ENNReal.ofReal_le_ofReal hmono
  have hgb' : g b - g a = ‖γ b - γ a‖_[m] := by rw [hga, sub_zero, hg, hΓ]
  rw [hgb'] at hstep
  refine hstep.trans ?_
  rw [intervalIntegral.integral_of_le hab,
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hintabs)
      (Filter.Eventually.of_forall fun t => abs_nonneg _)]
  refine lintegral_mono_ae ?_
  have hae := ae_deriv_weightedNorm_le (m := m) hm hΓac
  filter_upwards [hae] with t ht
  have hderiv : deriv Γ t = deriv γ t := by rw [hΓ]; exact deriv_sub_const (γ a)
  rw [hderiv] at ht
  exact ENNReal.ofReal_le_ofReal ht

/-- **Chord bound.**  The mass norm of the displacement is at most the mass length. -/
theorem weightedNorm_sub_le_massLength [Nontrivial E] {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    {γ : ℝ → EN E N} {a b : ℝ} (hab : a ≤ b) (hac : AbsolutelyContinuousOnInterval γ a b)
    (hint : Integrable (fun t : ℝ => ‖deriv γ t‖_[m]) (volume.restrict (Set.Ioc a b))) :
    ‖γ b - γ a‖_[m] ≤ massLength m γ a b := by
  have h := ofReal_weightedNorm_sub_le_lintegral hm hab hac
  have hbridge : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv γ t‖_[m]))
      = ENNReal.ofReal (massLength m γ a b) := by
    rw [massLength, intervalIntegral.integral_of_le hab]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun t => weightedNorm_nonneg m _)).symm
  rw [hbridge] at h
  exact (ENNReal.ofReal_le_ofReal_iff (massLength_nonneg hab)).mp h

end Submission.NBody
