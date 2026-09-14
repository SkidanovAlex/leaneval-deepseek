import ChallengeDeps
import Submission.NBody.ChazyTube
import Submission.Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_deriv_integral_vector
import Submission.Commons.MeasureTheory.Integral.intervalIntegrable_deriv_of_absolutelyContinuousOnInterval
import Submission.Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
import Submission.Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_concat
import Submission.Commons.Analysis.Calculus.lowerSemicontinuous_pairSum_inv_dist
import Submission.Commons.MeasureTheory.Integral.ofReal_chord_sq_div_add_le_lintegral_deriv
import Mathlib

/-!
# The Lagrangian, the action and the action potential

First stone of the variational chapter.  The Lagrangian of the `N`-body problem at the energy
level `h` is

    `L_h(x, v) = (1/2) ∑ᵢ mᵢ ‖vᵢ‖² + U(x) + h`

(compare the paper, where `L(x,v) = (1/2)‖v‖² + U(x)` and the action is `A_{L+h}`), with the
convention that `L_h(x,v) = ⊤` when the configuration `x` has a collision, so that a curve
meeting a collision has infinite action.

The action of a curve `γ` on the interval `(a,b]` is the (non-negative, extended) integral
`∫⁻ (L_h (γ t) (γ̇ t))`, and the *action potential* `φ_h(x,y)` is the infimum of the actions of
the absolutely continuous curves joining `x` to `y` in *some* positive time — the infimum is
taken over all times, as in the paper, so that concatenation of curves (and hence the triangle
inequality for `φ_h`) involves no reparametrisation.

Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators
open scoped Topology
open scoped ENNReal
open MeasureTheory

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The Newtonian potential is non-negative for non-negative masses. -/
lemma U_nonneg {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (x : EN E N) : 0 ≤ U m x := by
  rw [U_eq_pairFinset]
  refine Finset.sum_nonneg fun p _ => ?_
  have hr : 0 ≤ (r x p.1 p.2)⁻¹ := inv_nonneg.mpr dist_nonneg
  exact mul_nonneg (mul_nonneg (hm p.1) (hm p.2)) hr

/-- The non-negative, extended-valued Lagrangian of the `N`-body problem at level `h`:
`(1/2)∑ᵢ mᵢ‖vᵢ‖² + U(x) + h` on collision-free configurations, and `⊤` on colliding ones. -/
noncomputable def lagrangian (m : Fin N → ℝ) (h : ℝ) (x v : EN E N) : ℝ≥0∞ := by
  classical
  exact if WithoutCollisions x then
    ENNReal.ofReal ((1 / 2) * (∑ i, m i * ‖v i‖ ^ 2) + U m x + h)
  else ⊤

/-- The action of a curve on a time interval `(a,b]` (endpoints have measure zero, so this is the
usual `∫ (L_h (γ t) (γ̇ t))`): a `ℝ≥0∞`-valued integral, so a curve meeting a collision has
infinite action. -/
noncomputable def actionOn (m : Fin N → ℝ) (h : ℝ) (γ : ℝ → EN E N) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioc a b, lagrangian m h (γ t) (deriv γ t)

/-- The action potential `φ_h(x,y)`: the infimum, over *all* positive times `τ` and all absolutely
continuous curves `γ` on `[0,τ]` with `γ 0 = x` and `γ τ = y`, of the action of `γ`. -/
noncomputable def actionPot (m : Fin N → ℝ) (h : ℝ) (x y : EN E N) : ℝ≥0∞ :=
  ⨅ p : {p : ℝ × (ℝ → EN E N) //
      0 < p.1 ∧ p.2 0 = x ∧ p.2 p.1 = y ∧ AbsolutelyContinuousOnInterval p.2 0 p.1},
    actionOn m h p.1.2 0 p.1.1

/-- **Pointwise AM–GM bound for the Lagrangian.**  If all masses are at least `c > 0`, then
`√(2ch) ‖v‖ ≤ L_h(x,v)`, where `‖·‖` is the Euclidean norm of the configuration space. -/
lemma ofReal_sqrt_mul_norm_le_lagrangian {m : Fin N → ℝ} {c h : ℝ} (hc : 0 < c)
    (hm : ∀ i, c ≤ m i) (hh : 0 ≤ h) (x v : EN E N) :
    ENNReal.ofReal (Real.sqrt (2 * c * h) * ‖v‖) ≤ lagrangian m h x v := by
  by_cases hx : WithoutCollisions x
  · rw [lagrangian, if_pos hx]
    refine ENNReal.ofReal_le_ofReal ?_
    have hmsq : c * ‖v‖ ^ 2 ≤ ∑ i, m i * ‖v i‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin N => E), Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hm i) (sq_nonneg _)
    have hU : 0 ≤ U m x := U_nonneg (fun i => le_trans hc.le (hm i)) x
    have hsq : (0 : ℝ) ≤ (Real.sqrt c * ‖v‖ - Real.sqrt (2 * h)) ^ 2 := sq_nonneg _
    have hA : (Real.sqrt c * ‖v‖) * Real.sqrt (2 * h) = Real.sqrt (2 * c * h) * ‖v‖ := by
      have h1 : Real.sqrt c * Real.sqrt (2 * h) = Real.sqrt (2 * c * h) := by
        rw [← Real.sqrt_mul hc.le (2 * h)]
        congr 1
        ring
      rw [← h1]
      ring
    have hc2 : (Real.sqrt c * ‖v‖) ^ 2 = c * ‖v‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc.le]
    have hh2 : (Real.sqrt (2 * h)) ^ 2 = 2 * h := Real.sq_sqrt (by positivity)
    linarith [hsq, hA, hc2, hh2, mul_le_mul_of_nonneg_left hmsq (by norm_num : (0:ℝ) ≤ 1/2),
      hU]
  · rw [lagrangian, if_neg hx]
    exact le_top

/-- The Lagrangian is `⊤` exactly on colliding configurations. -/
lemma lagrangian_eq_top_iff {m : Fin N → ℝ} {h : ℝ} {x v : EN E N} :
    lagrangian m h x v = ⊤ ↔ ¬ WithoutCollisions x := by
  by_cases hx : WithoutCollisions x
  · rw [lagrangian, if_pos hx]
    exact ⟨fun hcontra => absurd hcontra ENNReal.ofReal_ne_top, fun h => absurd hx h⟩
  · rw [lagrangian, if_neg hx]
    exact ⟨fun _ => hx, fun _ => rfl⟩

/-- The action potential is at most the action of any admissible curve. -/
lemma actionPot_le_of {m : Fin N → ℝ} {h : ℝ} {x y : EN E N} {τ : ℝ} (hτ : 0 < τ)
    {γ : ℝ → EN E N} (h0 : γ 0 = x) (h1 : γ τ = y)
    (hac : AbsolutelyContinuousOnInterval γ 0 τ) :
    actionPot m h x y ≤ actionOn m h γ 0 τ :=
  iInf_le (f := fun p : {p : ℝ × (ℝ → EN E N) //
      0 < p.1 ∧ p.2 0 = x ∧ p.2 p.1 = y ∧ AbsolutelyContinuousOnInterval p.2 0 p.1} =>
        actionOn m h p.1.2 0 p.1.1) ⟨(τ, γ), hτ, h0, h1, hac⟩

/-- The action is monotone in the energy level. -/
lemma actionOn_mono {m : Fin N → ℝ} {h h' : ℝ} (hh : h ≤ h') (γ : ℝ → EN E N) (a b : ℝ) :
    actionOn m h γ a b ≤ actionOn m h' γ a b := by
  refine lintegral_mono fun t => ?_
  by_cases hc : WithoutCollisions (γ t)
  · rw [lagrangian, if_pos hc, lagrangian, if_pos hc]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · rw [lagrangian, if_neg hc, lagrangian, if_neg hc]

/-- The action potential is monotone in the energy level. -/
lemma actionPot_mono {m : Fin N → ℝ} {h h' : ℝ} (hh : h ≤ h') (x y : EN E N) :
    actionPot m h x y ≤ actionPot m h' x y := by
  refine le_iInf fun p => ?_
  exact (actionPot_le_of p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2).trans
    (actionOn_mono hh p.1.2 0 p.1.1)

/-- **Lower bound for the action potential.**  If every mass is at least `c > 0`, then for every
pair of configurations `φ_h(x,y) ≥ √(2ch) ‖x - y‖`.  In particular `φ_h(x,y) > 0` for `x ≠ y`
when `h > 0`. -/
theorem ofReal_sqrt_mul_norm_le_actionPot {m : Fin N → ℝ} {c h : ℝ} (hc : 0 < c)
    (hm : ∀ i, c ≤ m i) (hh : 0 ≤ h) (x y : EN E N) :
    ENNReal.ofReal (Real.sqrt (2 * c * h) * ‖x - y‖) ≤ actionPot m h x y := by
  refine le_iInf fun p => ?_
  obtain ⟨hτ, h0, h1, hac⟩ := p.2
  have hint : IntervalIntegrable (fun t : ℝ => Real.sqrt (2 * c * h) * ‖deriv p.1.2 t‖)
      volume 0 p.1.1 :=
    (Commons.MeasureTheory.Integral.intervalIntegrable_deriv_of_absolutelyContinuousOnInterval
      hac).norm.const_mul _
  -- the pointwise AM–GM bound passes to the integral
  have hstep1 : (∫⁻ t in Set.Ioc (0 : ℝ) p.1.1,
        ENNReal.ofReal (Real.sqrt (2 * c * h) * ‖deriv p.1.2 t‖))
      ≤ actionOn m h p.1.2 0 p.1.1 :=
    lintegral_mono fun t => ofReal_sqrt_mul_norm_le_lagrangian hc hm hh (p.1.2 t) (deriv p.1.2 t)
  -- the extended integral of the pointwise bound is the `ofReal` of the real integral
  have hofreal : ENNReal.ofReal (∫ t in (0 : ℝ)..p.1.1,
        Real.sqrt (2 * c * h) * ‖deriv p.1.2 t‖)
      = ∫⁻ t in Set.Ioc (0 : ℝ) p.1.1,
          ENNReal.ofReal (Real.sqrt (2 * c * h) * ‖deriv p.1.2 t‖) := by
    rw [intervalIntegral.integral_of_le hτ.le]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint.1
      (Filter.Eventually.of_forall fun t => by positivity)
  -- the chord bound for absolutely continuous curves
  have hchord : ‖x - y‖ ≤ ∫ t in (0 : ℝ)..p.1.1, ‖deriv p.1.2 t‖ := by
    have hFTC := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_deriv_integral_vector
      hac
    have hsub : x - y = -(p.1.2 p.1.1 - p.1.2 0) := by rw [h0, h1]; abel
    rw [hsub, norm_neg, ← hFTC]
    exact intervalIntegral.norm_integral_le_integral_norm hτ.le
  calc ENNReal.ofReal (Real.sqrt (2 * c * h) * ‖x - y‖)
      ≤ ENNReal.ofReal (Real.sqrt (2 * c * h) * ∫ t in (0 : ℝ)..p.1.1, ‖deriv p.1.2 t‖) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hchord (Real.sqrt_nonneg _))
    _ = ENNReal.ofReal (∫ t in (0 : ℝ)..p.1.1,
          Real.sqrt (2 * c * h) * ‖deriv p.1.2 t‖) := by
        rw [intervalIntegral.integral_const_mul]
    _ = _ := hofreal
    _ ≤ actionOn m h p.1.2 0 p.1.1 := hstep1

theorem setLIntegral_Ioc_comp_sub (F : ℝ → ℝ≥0∞) (a L : ℝ) :
    (∫⁻ t in Set.Ioc a (a + L), F (t - a)) = ∫⁻ s in Set.Ioc 0 L, F s := by
  have h := MeasureTheory.MeasurePreserving.setLIntegral_comp_emb
      (ν := volume) (μ := volume) (g := fun x : ℝ => x + a)
      (measurePreserving_add_right volume a)
      (Homeomorph.measurableEmbedding (Homeomorph.addRight a))
      (fun y : ℝ => F (y - a)) (Set.Ioc 0 L)
  rw [image_add_const_Ioc] at h
  have h1 : (fun x : ℝ => F (x + a - a)) = F := by funext x; rw [add_sub_cancel_right]
  rw [h1] at h
  rw [zero_add] at h
  rw [add_comm L a] at h
  exact h.symm

omit [FiniteDimensional ℝ E] in
lemma actionOn_concat {m : Fin N → ℝ} {h : ℝ} {γ₁ γ₂ : ℝ → EN E N} {τ₁ τ₂ : ℝ}
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) :
    actionOn m h (fun t => if t ≤ τ₁ then γ₁ t else γ₂ (t - τ₁)) 0 (τ₁ + τ₂)
      = actionOn m h γ₁ 0 τ₁ + actionOn m h γ₂ 0 τ₂ := by
  set γ : ℝ → EN E N := fun t => if t ≤ τ₁ then γ₁ t else γ₂ (t - τ₁) with hγdef
  have hleft : ∀ t ∈ Set.Ioo (0:ℝ) τ₁,
      lagrangian m h (γ t) (deriv γ t) = lagrangian m h (γ₁ t) (deriv γ₁ t) := by
    intro t ht
    have hev : γ =ᶠ[𝓝 t] γ₁ := by
      refine Eventually.mono (IsOpen.mem_nhds isOpen_Iio ht.2) ?_
      intro s hs
      simp only [hγdef]
      rw [if_pos (le_of_lt hs)]
    have hval : γ t = γ₁ t := by simp only [hγdef]; rw [if_pos (le_of_lt ht.2)]
    rw [hev.deriv_eq, hval]
  have hright : ∀ t ∈ Set.Ioc τ₁ (τ₁ + τ₂),
      lagrangian m h (γ t) (deriv γ t)
        = lagrangian m h (γ₂ (t - τ₁)) (deriv γ₂ (t - τ₁)) := by
    intro t ht
    have hev : γ =ᶠ[𝓝 t] (fun s => γ₂ (s - τ₁)) := by
      refine Eventually.mono (IsOpen.mem_nhds isOpen_Ioi ht.1) ?_
      intro s hs
      simp only [hγdef]
      rw [if_neg (not_le_of_gt hs)]
    have hval : γ t = γ₂ (t - τ₁) := by simp only [hγdef]; rw [if_neg (not_le_of_gt ht.1)]
    rw [hev.deriv_eq, deriv_comp_sub_const, hval]
  have hsplit : actionOn m h γ 0 (τ₁ + τ₂) = actionOn m h γ 0 τ₁ + actionOn m h γ τ₁ (τ₁ + τ₂) := by
    unfold actionOn
    rw [← Set.Ioc_union_Ioc_eq_Ioc (le_of_lt hτ₁) (by linarith)]
    rw [lintegral_union measurableSet_Ioc]
    exact Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le_of_gt hx'.1)
  rw [hsplit]
  congr 1
  · unfold actionOn
    refine setLIntegral_congr_fun_ae measurableSet_Ioc ?_
    filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp (measure_singleton τ₁)]
      with t ht hmem
    exact hleft t ⟨hmem.1, lt_of_le_of_ne hmem.2 ht⟩
  · unfold actionOn
    rw [setLIntegral_congr_fun measurableSet_Ioc hright]
    exact setLIntegral_Ioc_comp_sub (fun s => lagrangian m h (γ₂ s) (deriv γ₂ s)) τ₁ τ₂

/-- The action potential is subadditive along a concatenation of two admissible curves. -/
lemma actionPot_le_add_of {m : Fin N → ℝ} {h : ℝ} {x y z : EN E N} {τ₁ τ₂ : ℝ}
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) {γ₁ γ₂ : ℝ → EN E N}
    (h10 : γ₁ 0 = x) (h11 : γ₁ τ₁ = y) (h20 : γ₂ 0 = y) (h21 : γ₂ τ₂ = z)
    (hac₁ : AbsolutelyContinuousOnInterval γ₁ 0 τ₁)
    (hac₂ : AbsolutelyContinuousOnInterval γ₂ 0 τ₂) :
    actionPot m h x z ≤ actionOn m h γ₁ 0 τ₁ + actionOn m h γ₂ 0 τ₂ := by
  have hfc : γ₁ τ₁ = (fun t : ℝ => γ₂ (t - τ₁)) τ₁ := by
    simp only [sub_self, h20, h11]
  have hγ₂ac : AbsolutelyContinuousOnInterval (fun t : ℝ => γ₂ (t - τ₁)) τ₁ (τ₁ + τ₂) := by
    have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
      (f := γ₂) (a := 0) (b := τ₂) (c := 1) (d := -τ₁) (by norm_num) hac₂
    simpa only [one_mul, zero_add, div_one, sub_eq_add_neg, neg_neg, add_comm τ₂ τ₁] using h
  have hconcat : AbsolutelyContinuousOnInterval
      (fun t : ℝ => if t ≤ τ₁ then γ₁ t else γ₂ (t - τ₁)) 0 (τ₁ + τ₂) :=
    Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_concat
      (le_of_lt hτ₁) (by linarith) hfc hac₁ hγ₂ac
  have hle := actionPot_le_of (m := m) (h := h) (x := x) (y := z) (τ := τ₁ + τ₂)
    (by linarith) (γ := fun t : ℝ => if t ≤ τ₁ then γ₁ t else γ₂ (t - τ₁))
    (by simp only [if_pos (le_of_lt hτ₁), h10])
    (by
      have hlt : τ₁ < τ₁ + τ₂ := by linarith
      simp only [if_neg (not_le_of_gt hlt)]
      rw [show τ₁ + τ₂ - τ₁ = τ₂ by ring, h21])
    hconcat
  exact hle.trans (le_of_eq (actionOn_concat hτ₁ hτ₂))


/-- **Triangle inequality for the action potential.** -/
lemma actionPot_triangle (m : Fin N → ℝ) (h : ℝ) (x y z : EN E N) :
    actionPot m h x z ≤ actionPot m h x y + actionPot m h y z := by
  let P : Type _ := {p : ℝ × (ℝ → EN E N) //
      0 < p.1 ∧ p.2 0 = x ∧ p.2 p.1 = y ∧ AbsolutelyContinuousOnInterval p.2 0 p.1}
  let Q : Type _ := {q : ℝ × (ℝ → EN E N) //
      0 < q.1 ∧ q.2 0 = y ∧ q.2 q.1 = z ∧ AbsolutelyContinuousOnInterval q.2 0 q.1}
  have hxy : actionPot m h x y = ⨅ p : P, actionOn m h p.1.2 0 p.1.1 := rfl
  have hyz : actionPot m h y z = ⨅ q : Q, actionOn m h q.1.2 0 q.1.1 := rfl
  have key : ∀ (p : P) (q : Q),
      actionPot m h x z ≤ actionOn m h p.1.2 0 p.1.1 + actionOn m h q.1.2 0 q.1.1 :=
    fun p q => actionPot_le_add_of p.2.1 q.2.1 p.2.2.1 p.2.2.2.1 q.2.2.1 q.2.2.2.1 p.2.2.2.2 q.2.2.2.2
  calc actionPot m h x z
      ≤ ⨅ (p : P), ⨅ (q : Q),
          (actionOn m h p.1.2 0 p.1.1 + actionOn m h q.1.2 0 q.1.1) :=
        le_iInf fun p => le_iInf fun q => key p q
    _ = (⨅ (p : P), actionOn m h p.1.2 0 p.1.1)
          + (⨅ (q : Q), actionOn m h q.1.2 0 q.1.1) := by
        trans ⨅ (p : P),
            (actionOn m h p.1.2 0 p.1.1 + ⨅ (q : Q), actionOn m h q.1.2 0 q.1.1)
        · exact iInf_congr fun p =>
            (ENNReal.add_iInf (a := actionOn m h p.1.2 0 p.1.1)).symm
        · exact (ENNReal.iInf_add (f := fun p : P => actionOn m h p.1.2 0 p.1.1)
            (a := ⨅ q : Q, actionOn m h q.1.2 0 q.1.1)).symm
    _ = actionPot m h x y + actionPot m h y z := by rw [hxy, hyz]

lemma setLIntegral_Ico_eq_Ioc (F : ℝ → ℝ≥0∞) (τ : ℝ) :
    (∫⁻ s in Set.Ico 0 τ, F s) = ∫⁻ s in Set.Ioc 0 τ, F s := by
  refine le_antisymm ?_ ?_
  · calc (∫⁻ s in Set.Ico 0 τ, F s)
        ≤ ∫⁻ s in Set.Ioc 0 τ ∪ ({0} : Set ℝ), F s := by
          refine lintegral_mono_set ?_
          intro x hx
          rw [Set.mem_Ico] at hx
          rcases eq_or_lt_of_le hx.1 with h | h
          · exact Or.inr (Set.mem_singleton_iff.mpr h.symm)
          · exact Or.inl (Set.mem_Ioc.mpr ⟨h, le_of_lt hx.2⟩)
      _ = (∫⁻ s in Set.Ioc 0 τ, F s) + ∫⁻ s in ({0} : Set ℝ), F s := by
          rw [lintegral_union (measurableSet_singleton (0:ℝ))]
          exact Set.disjoint_left.mpr fun x hx hx' => by
            rw [Set.mem_Ioc] at hx
            rw [Set.mem_singleton_iff] at hx'
            rw [hx'] at hx
            exact absurd hx.1 (lt_irrefl (0:ℝ))
      _ = (∫⁻ s in Set.Ioc 0 τ, F s) := by
          have hz : (∫⁻ s in ({0} : Set ℝ), F s) = 0 := by simp
          rw [hz, add_zero]
  · calc (∫⁻ s in Set.Ioc 0 τ, F s)
        ≤ ∫⁻ s in Set.Ico 0 τ ∪ ({τ} : Set ℝ), F s := by
          refine lintegral_mono_set ?_
          intro x hx
          rw [Set.mem_Ioc] at hx
          rcases lt_or_eq_of_le hx.2 with h | h
          · exact Or.inl (Set.mem_Ico.mpr ⟨le_of_lt hx.1, h⟩)
          · exact Or.inr (Set.mem_singleton_iff.mpr h)
      _ = (∫⁻ s in Set.Ico 0 τ, F s) + ∫⁻ s in ({τ} : Set ℝ), F s := by
          rw [lintegral_union (measurableSet_singleton τ)]
          exact Set.disjoint_left.mpr fun x hx hx' => by
            rw [Set.mem_Ico] at hx
            rw [Set.mem_singleton_iff] at hx'
            rw [hx'] at hx
            exact absurd hx.2 (lt_irrefl τ)
      _ = (∫⁻ s in Set.Ico 0 τ, F s) := by
          have hz : (∫⁻ s in ({τ} : Set ℝ), F s) = 0 := by simp
          rw [hz, add_zero]

theorem setLIntegral_Ioc_comp_reflect (F : ℝ → ℝ≥0∞) (τ : ℝ) :
    (∫⁻ t in Set.Ioc 0 τ, F (τ - t)) = ∫⁻ s in Set.Ioc 0 τ, F s := by
  have hneg : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    ⟨measurable_neg, Measure.map_neg_eq_self volume⟩
  have h2 : MeasurePreserving (fun x : ℝ => -(x - τ)) volume volume :=
    hneg.comp (measurePreserving_sub_right volume τ)
  have hmp : MeasurePreserving (fun t : ℝ => τ - t) volume volume := by
    rwa [show (fun x : ℝ => -(x - τ)) = fun t : ℝ => τ - t from by funext t; rw [neg_sub]] at h2
  have hme : MeasurableEmbedding (fun t : ℝ => τ - t) := by
    simpa only [Homeomorph.coe_subLeft] using
      Homeomorph.measurableEmbedding (Homeomorph.subLeft τ)
  have h := MeasureTheory.MeasurePreserving.setLIntegral_comp_emb hmp hme F (Set.Ioc 0 τ)
  rw [image_const_sub_Ioc, sub_self, sub_zero] at h
  rw [h, setLIntegral_Ico_eq_Ioc]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma lagrangian_neg (m : Fin N → ℝ) (h : ℝ) (x v : EN E N) :
    lagrangian m h x (-v) = lagrangian m h x v := by
  unfold lagrangian
  simp only [WithLp.ofLp_neg, Pi.neg_apply, norm_neg]

lemma actionPot_comm (m : Fin N → ℝ) (h : ℝ) (x y : EN E N) :
    actionPot m h x y = actionPot m h y x := by
  have main : ∀ u w : EN E N, actionPot m h u w ≤ actionPot m h w u := by
   intro u w
   refine le_iInf fun p => ?_
   have key : actionPot m h u w ≤ actionOn m h p.1.2 0 p.1.1 := by
    obtain ⟨hτ, hp0, hp1, hpac⟩ := p.2
    let γ : ℝ → EN E N := p.1.2
    let τ : ℝ := p.1.1
    have hp0' : γ 0 = w := hp0
    have hp1' : γ τ = u := hp1
    have hpac' : AbsolutelyContinuousOnInterval γ 0 τ := hpac
    have hγrac : AbsolutelyContinuousOnInterval (fun t : ℝ => γ (τ - t)) 0 τ := by
      have h1 : AbsolutelyContinuousOnInterval (fun t : ℝ => γ (τ - t)) τ 0 := by
        have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
          (f := γ) (a := 0) (b := τ) (c := -1) (d := τ) (by norm_num) hpac'
        have hfn : (fun t : ℝ => γ (-1 * t + τ)) = fun t : ℝ => γ (τ - t) := by
          funext t
          rw [show (-1:ℝ) * t + τ = τ - t by ring]
        rw [hfn] at h
        simpa using h
      exact h1.symm
    have haux : actionOn m h (fun t : ℝ => γ (τ - t)) 0 τ = actionOn m h γ 0 τ := by
      unfold actionOn
      calc (∫⁻ t in Set.Ioc 0 τ,
              lagrangian m h ((fun s : ℝ => γ (τ - s)) t) (deriv (fun s : ℝ => γ (τ - s)) t))
          = ∫⁻ t in Set.Ioc 0 τ, lagrangian m h (γ (τ - t)) (-deriv γ (τ - t)) := by
            refine setLIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
            rw [deriv_comp_const_sub]
          _ = ∫⁻ t in Set.Ioc 0 τ, lagrangian m h (γ (τ - t)) (deriv γ (τ - t)) := by
            refine setLIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
            rw [lagrangian_neg]
          _ = ∫⁻ s in Set.Ioc 0 τ, lagrangian m h (γ s) (deriv γ s) :=
            setLIntegral_Ioc_comp_reflect (fun s => lagrangian m h (γ s) (deriv γ s)) τ
    have hle := actionPot_le_of (m := m) (h := h) (x := u) (y := w) (τ := τ) hτ
      (γ := fun t : ℝ => γ (τ - t))
      (by show γ (τ - 0) = u; rw [sub_zero]; exact hp1')
      (by show γ (τ - τ) = w; rw [sub_self]; exact hp0')
      hγrac
    exact hle.trans (le_of_eq haux)
   exact key
  exact le_antisymm (main x y) (main y x)

/-- The Newtonian potential as an extended non-negative quantity: `⊤` on colliding
configurations.  This is the lower-semicontinuous version of `U`. -/
noncomputable def potTop (m : Fin N → ℝ) (x : EN E N) : ℝ≥0∞ := by
  classical
  exact if WithoutCollisions x then ENNReal.ofReal (U m x) else ⊤


lemma potTop_le_lagrangian {m : Fin N → ℝ} {h : ℝ} (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h)
    (x v : EN E N) : potTop m x ≤ lagrangian m h x v := by
  unfold potTop lagrangian
  by_cases hx : WithoutCollisions x
  · rw [if_pos hx, if_pos hx]
    refine ENNReal.ofReal_le_ofReal ?_
    have hU : 0 ≤ U m x := U_nonneg hm x
    have hk : 0 ≤ (1 / 2) * ∑ i, m i * ‖v i‖ ^ 2 :=
      mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => mul_nonneg (hm i) (sq_nonneg _))
    linarith
  · rw [if_neg hx, if_neg hx]

lemma actionPot_pos {m : Fin N → ℝ} {c h : ℝ} (hc : 0 < c) (hm : ∀ i, c ≤ m i) (hh : 0 < h)
    {x y : EN E N} (hxy : x ≠ y) : 0 < actionPot m h x y := by
  have h1 := ofReal_sqrt_mul_norm_le_actionPot hc hm hh.le x y
  have h2 : 0 < Real.sqrt (2 * c * h) * ‖x - y‖ := by
    have hs : 0 < Real.sqrt (2 * c * h) := Real.sqrt_pos.mpr (by positivity)
    have hn : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    positivity
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr h2) h1

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma lagrangian_const {m : Fin N → ℝ} {h : ℝ} {x : EN E N} (hx : WithoutCollisions x) :
    lagrangian m h x (0 : EN E N) = ENNReal.ofReal (U m x + h) := by
  rw [lagrangian, if_pos hx]
  congr 1
  have hzero : (∑ i, m i * ‖(0 : EN E N) i‖ ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    simp
  rw [hzero]
  ring

lemma actionOn_const {m : Fin N → ℝ} {h : ℝ} {x : EN E N} (hx : WithoutCollisions x) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    actionOn m h (fun _ : ℝ => x) 0 τ = ENNReal.ofReal (τ * (U m x + h)) := by
  unfold actionOn
  have hderiv : ∀ t : ℝ, deriv (fun _ : ℝ => x) t = 0 := fun t => deriv_const t x
  simp only [hderiv]
  rw [setLIntegral_const, lagrangian_const hx, Real.volume_Ioc, sub_zero]
  rw [← ENNReal.ofReal_mul' hτ]
  ring_nf

lemma actionPot_self_le {m : Fin N → ℝ} {h : ℝ} {x : EN E N} (hx : WithoutCollisions x) {τ : ℝ}
    (hτ : 0 < τ) : actionPot m h x x ≤ ENNReal.ofReal (τ * (U m x + h)) := by
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => x) 0 τ :=
    (LipschitzWith.const x).lipschitzOnWith.absolutelyContinuousOnInterval
  exact (actionPot_le_of hτ rfl (by simp) hconst).trans (le_of_eq (actionOn_const hx hτ.le))

lemma ofReal_kinetic_add_h_le_lagrangian {m : Fin N → ℝ} {c h : ℝ} (hc : 0 < c)
    (hm : ∀ i, c ≤ m i) (hh : 0 ≤ h) (x v : EN E N) :
    ENNReal.ofReal ((1 / 2) * c * ‖v‖ ^ 2 + h) ≤ lagrangian m h x v := by
  by_cases hx : WithoutCollisions x
  · rw [lagrangian, if_pos hx]
    refine ENNReal.ofReal_le_ofReal ?_
    have hmsq : c * ‖v‖ ^ 2 ≤ ∑ i, m i * ‖v i‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin N => E), Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hm i) (sq_nonneg _)
    have hU : 0 ≤ U m x := U_nonneg (fun i => le_trans hc.le (hm i)) x
    linarith [mul_le_mul_of_nonneg_left hmsq (by norm_num : (0:ℝ) ≤ 1/2)]
  · rw [lagrangian, if_neg hx]
    exact le_top

lemma ofReal_chord_sq_div_add_le_actionOn {m : Fin N → ℝ} {c h : ℝ} (hc : 0 < c)
    (hm : ∀ i, c ≤ m i) (hh : 0 ≤ h) {x y : EN E N} {τ : ℝ} (hτ : 0 < τ)
    {γ : ℝ → EN E N} (h0 : γ 0 = x) (h1 : γ τ = y)
    (hac : AbsolutelyContinuousOnInterval γ 0 τ) :
    ENNReal.ofReal ((1 / 2) * c * ‖x - y‖ ^ 2 / τ + h * τ) ≤ actionOn m h γ 0 τ := by
  have hkey := Commons.MeasureTheory.Integral.ofReal_chord_sq_div_add_le_lintegral_deriv
    (f := γ) hτ hc.le hh hac
  rw [h0, h1, norm_sub_rev] at hkey
  refine hkey.trans ?_
  rw [actionOn]
  exact lintegral_mono fun t =>
    ofReal_kinetic_add_h_le_lagrangian hc hm hh (γ t) (deriv γ t)

noncomputable def pairPot (m : Fin N → ℝ) (x : EN E N) : ℝ≥0∞ :=
  ∑ j, ∑ i < j, ENNReal.ofReal (m i * m j) * (ENNReal.ofReal (dist (x i) (x j)))⁻¹

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma pairPot_eq_ofReal_U {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) {x : EN E N}
    (hx : WithoutCollisions x) : pairPot m x = ENNReal.ofReal (U m x) := by
  have hpos : ∀ i j : Fin N, i ≠ j → 0 < dist (x i) (x j) := by
    intro i j hij
    have h : dist (x i) (x j) ≠ 0 := by have := hx i j hij; rwa [r] at this
    exact lt_of_le_of_ne dist_nonneg (Ne.symm h)
  have hterm : ∀ i j : Fin N, i ≠ j →
      ENNReal.ofReal (m i * m j) * (ENNReal.ofReal (dist (x i) (x j)))⁻¹
        = ENNReal.ofReal (m i * m j * (dist (x i) (x j))⁻¹) := by
    intro i j hij
    rw [ENNReal.ofReal_mul (mul_nonneg (hm i) (hm j)),
      ENNReal.ofReal_inv_of_pos (hpos i j hij)]
  have hnn : ∀ i j : Fin N, i ≠ j → 0 ≤ m i * m j * (dist (x i) (x j))⁻¹ :=
    fun i j hij => mul_nonneg (mul_nonneg (hm i) (hm j)) (inv_nonneg.mpr (hpos i j hij).le)
  have hinner : ∀ j : Fin N,
      (∑ i < j, ENNReal.ofReal (m i * m j) * (ENNReal.ofReal (dist (x i) (x j)))⁻¹)
        = ENNReal.ofReal (∑ i < j, m i * m j * (dist (x i) (x j))⁻¹) := by
    intro j
    rw [Finset.sum_congr rfl (fun i hi => hterm i j (ne_of_lt (Finset.mem_Iio.mp hi)))]
    exact (ENNReal.ofReal_sum_of_nonneg (s := Finset.Iio j) (fun i hi =>
      hnn i j (ne_of_lt (Finset.mem_Iio.mp hi)))).symm
  calc pairPot m x
      = ∑ j, ENNReal.ofReal (∑ i < j, m i * m j * (dist (x i) (x j))⁻¹) :=
        Finset.sum_congr rfl fun j _ => hinner j
    _ = ENNReal.ofReal (∑ j, ∑ i < j, m i * m j * (dist (x i) (x j))⁻¹) :=
        (ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (fun j _ =>
          Finset.sum_nonneg fun i hi =>
            hnn i j (ne_of_lt (Finset.mem_Iio.mp hi)))).symm
    _ = ENNReal.ofReal (U m x) := rfl

lemma pairPot_le_lagrangian {m : Fin N → ℝ} {h : ℝ} (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h)
    (x v : EN E N) : pairPot m x ≤ lagrangian m h x v := by
  by_cases hx : WithoutCollisions x
  · rw [pairPot_eq_ofReal_U hm hx, lagrangian, if_pos hx]
    refine ENNReal.ofReal_le_ofReal ?_
    have hU : 0 ≤ U m x := U_nonneg hm x
    have hk : 0 ≤ (1 / 2) * ∑ i, m i * ‖v i‖ ^ 2 :=
      mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => mul_nonneg (hm i) (sq_nonneg _))
    linarith
  · rw [lagrangian, if_neg hx]
    exact le_top

/-- The sum of the kinetic energy, the extended pair potential `pairPot` and the constant `h` is
at most the Lagrangian: the pointwise input for Fatou's lemma applied to the action. -/
lemma ofReal_kinetic_add_pairPot_add_h_le_lagrangian {m : Fin N → ℝ} {h : ℝ}
    (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h) (x v : EN E N) :
    ENNReal.ofReal ((1 / 2) * ∑ i, m i * ‖v i‖ ^ 2) + pairPot m x + ENNReal.ofReal h
      ≤ lagrangian m h x v := by
  by_cases hx : WithoutCollisions x
  · have hU : 0 ≤ U m x := U_nonneg hm x
    have hk : 0 ≤ (1 / 2) * ∑ i, m i * ‖v i‖ ^ 2 :=
      mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => mul_nonneg (hm i) (sq_nonneg _))
    have h1 : ENNReal.ofReal ((1 / 2) * ∑ i, m i * ‖v i‖ ^ 2) + ENNReal.ofReal (U m x)
        = ENNReal.ofReal ((1 / 2) * ∑ i, m i * ‖v i‖ ^ 2 + U m x) :=
      (ENNReal.ofReal_add hk hU).symm
    have h2 : ENNReal.ofReal ((1 / 2) * ∑ i, m i * ‖v i‖ ^ 2 + U m x) + ENNReal.ofReal h
        = ENNReal.ofReal ((1 / 2) * ∑ i, m i * ‖v i‖ ^ 2 + U m x + h) :=
      (ENNReal.ofReal_add (add_nonneg hk hU) hh).symm
    rw [pairPot_eq_ofReal_U hm hx, lagrangian, if_pos hx, h1, h2]
  · rw [lagrangian, if_neg hx]
    exact le_top

/-- `φ_h(x,x) = 0` for a collision-free `x` and `U m x + h ≥ 0`. -/
lemma actionPot_self_eq_zero {m : Fin N → ℝ} {h : ℝ} {x : EN E N} (hx : WithoutCollisions x)
    (hC : 0 ≤ U m x + h) : actionPot m h x x = 0 := by
  set C := U m x + h with hCdef
  have hle : ∀ τ : {τ : ℝ // 0 < τ}, actionPot m h x x ≤ ENNReal.ofReal (τ.1 * C) :=
    fun τ => actionPot_self_le hx τ.2
  set a : ℝ≥0∞ := ⨅ (τ : {τ : ℝ // 0 < τ}), ENNReal.ofReal (τ.1 * C) with hadef
  have ha : actionPot m h x x ≤ a := le_iInf hle
  have haε : ∀ ε : ℝ, 0 < ε → a ≤ ENNReal.ofReal ε := by
    intro ε hε
    have hC1 : (0 : ℝ) < C + 1 := by linarith
    refine (iInf_le _ ⟨ε / (C + 1), div_pos hε hC1⟩).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hC1]
    nlinarith [hε.le, hC]
  have ha1 : a ≤ ENNReal.ofReal 1 := haε 1 one_pos
  have hatop : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top ha1
  have htoReal : a.toReal ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h1 := haε ε hε
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    simpa [ENNReal.toReal_ofReal hε.le] using h2
  refine le_antisymm (ha.trans ?_) bot_le
  rw [← ENNReal.ofReal_toReal hatop, ← ENNReal.ofReal_zero]
  exact ENNReal.ofReal_le_ofReal htoReal

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma pairPot_le_liminf_pairPot {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) {ι : Type*} {l : Filter ι}
    {xs : ι → EN E N} {x : EN E N} (h : Tendsto xs l (𝓝 x)) :
    pairPot m x ≤ liminf (fun n => pairPot m (xs n)) l := by
  have h' : Tendsto (fun n => (xs n).ofLp) l (𝓝 x.ofLp) := by
    simpa only [Function.comp_def] using
      ((PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin N => E)).tendsto x).comp h
  exact Commons.Analysis.Calculus.lowerSemicontinuous_pairSum_inv_dist hm h'

/-! ## The action potential is bounded by the action on any interval -/

lemma actionOn_comp_add_const {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {a L : ℝ} :
    actionOn m h (fun t => γ (t + a)) 0 L = actionOn m h γ a (a + L) := by
  unfold actionOn
  have hcov := setLIntegral_Ioc_comp_sub
    (fun s => lagrangian m h (γ (s + a)) (deriv (fun u => γ (u + a)) s)) a L
  rw [← hcov]
  refine setLIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  have h1 : (fun s => lagrangian m h (γ (s + a)) (deriv (fun u => γ (u + a)) s))
      (t - a) = lagrangian m h (γ t) (deriv γ t) := by
    show lagrangian m h (γ (t - a + a)) (deriv (fun u => γ (u + a)) (t - a)) = _
    rw [sub_add_cancel, deriv_comp_add_const, sub_add_cancel]
  exact h1

lemma actionOn_comp_add_const' {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {c d : ℝ} :
    actionOn m h (fun t => γ (t + c)) 0 (d - c) = actionOn m h γ c d := by
  rw [actionOn_comp_add_const]
  congr 1
  ring

/-- **The action potential is bounded by the action on an arbitrary interval.** -/
lemma actionPot_le_of_interval {m : Fin N → ℝ} {h : ℝ} {x y : EN E N} {a b : ℝ}
    (hab : a < b) {γ : ℝ → EN E N} (h0 : γ a = x) (h1 : γ b = y)
    (hac : AbsolutelyContinuousOnInterval γ a b) :
    actionPot m h x y ≤ actionOn m h γ a b := by
  have hL : (0:ℝ) < b - a := by linarith
  have hcomp := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
    (f := γ) (a := a) (b := b) (c := 1) (d := a) (by norm_num) hac
  have hcomp' : AbsolutelyContinuousOnInterval (fun t => γ (t + a)) 0 (b - a) := by
    simpa using hcomp
  have h0' : (fun t : ℝ => γ (t + a)) 0 = x := by simpa using h0
  have h1' : (fun t : ℝ => γ (t + a)) (b - a) = y := by
    simp only [sub_add_cancel]; exact h1
  have hle := actionPot_le_of (m := m) (h := h) (x := x) (y := y) (τ := b - a) hL h0' h1' hcomp'
  rwa [actionOn_comp_add_const'] at hle


end Submission.NBody
