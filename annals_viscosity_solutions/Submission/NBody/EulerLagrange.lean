import Submission.NBody.Minimizer
import Submission.NBody.Force
import Submission.Commons.MeasureTheory.Integral.aestronglyMeasurable_deriv_of_absolutelyContinuousOnInterval
import Submission.Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_ae_differentiableAt_vector
import Mathlib

/-!
# The Euler--Lagrange equation for `h`-minimisers

First stone of the "minimisers are genuine motions" chapter: the real-valued Lagrangian
`lagR m h q v = (1/2) ∑ᵢ mᵢ ‖vᵢ‖² + U(q) + h`, the mass inner product, and the derivative of the
kinetic energy in a perturbation parameter.  The first variation of the action and the
weak-to-strong upgrade of the corresponding Euler--Lagrange equation are built on top of this.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The **mass inner product** `∑ᵢ mᵢ ⟪vᵢ, wᵢ⟫` on configurations. -/
noncomputable def massInner (m : Fin N → ℝ) (v w : EN E N) : ℝ :=
  ∑ i, m i * inner ℝ (v i) (w i)

omit [FiniteDimensional ℝ E] in
lemma massInner_comm (m : Fin N → ℝ) (v w : EN E N) :
    massInner m v w = massInner m w v := by
  simp only [massInner, real_inner_comm]

/-- **The derivative of the Newtonian potential is the mass inner product with the
mass-weighted gradient.** -/
lemma fderiv_U_eq_massInner {m : Fin N → ℝ} (hm : ∀ i, m i ≠ 0) (x : EN E N)
    (hx : WithoutCollisions x) (d : EN E N) :
    (fderiv ℝ (U m) x) d = massInner m (∇_[m] (U m) x) d := by
  rw [← inner_gradient_eq_fderiv]
  simp only [massInner, weightedGrad]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ (hm i), one_mul]

/-- The real-valued Lagrangian `L(q,v) = (1/2)∑ᵢ mᵢ‖vᵢ‖² + U(q) + h`. -/
noncomputable def lagR (m : Fin N → ℝ) (h : ℝ) (q v : EN E N) : ℝ :=
  (1 / 2) * ∑ i, m i * ‖v i‖ ^ 2 + U m q + h

lemma lagrangian_eq_ofReal_lagR {m : Fin N → ℝ} {h : ℝ} {q v : EN E N}
    (hq : WithoutCollisions q) :
    lagrangian m h q v = ENNReal.ofReal (lagR m h q v) := by
  rw [lagrangian, if_pos hq, lagR]

lemma add_smul_apply (v w : EN E N) (ε : ℝ) (i : Fin N) :
    (v + ε • w) i = v i + ε • w i := by
  simp only [PiLp.add_apply, PiLp.smul_apply]

/-- Expansion of the kinetic energy of a perturbed velocity. -/
lemma kinetic_perturb {m : Fin N → ℝ} (v w : EN E N) (ε : ℝ) :
    (1 / 2) * ∑ i, m i * ‖(v + ε • w) i‖ ^ 2
      = (1 / 2) * ∑ i, m i * ‖v i‖ ^ 2 + ε * massInner m v w
        + ε ^ 2 * ((1 / 2) * ∑ i, m i * ‖w i‖ ^ 2) := by
  have hL : (1 / 2) * ∑ i, m i * ‖(v + ε • w) i‖ ^ 2
      = ∑ i, ((1 / 2) * (m i * ‖v i‖ ^ 2) + ε * (m i * inner ℝ (v i) (w i))
          + ε ^ 2 * ((1 / 2) * (m i * ‖w i‖ ^ 2))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_smul_apply, norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_right]
    ring
  have hR : (1 / 2) * ∑ i, m i * ‖v i‖ ^ 2 + ε * massInner m v w
        + ε ^ 2 * ((1 / 2) * ∑ i, m i * ‖w i‖ ^ 2)
      = ∑ i, ((1 / 2) * (m i * ‖v i‖ ^ 2) + ε * (m i * inner ℝ (v i) (w i))
          + ε ^ 2 * ((1 / 2) * (m i * ‖w i‖ ^ 2))) := by
    simp only [massInner, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [hL, hR]

/-- **Derivative of the kinetic energy in the perturbation parameter.** -/
lemma hasDerivAt_kinetic {m : Fin N → ℝ} (v w : EN E N) :
    HasDerivAt (fun ε : ℝ => (1 / 2) * ∑ i, m i * ‖(v + ε • w) i‖ ^ 2) (massInner m v w) 0 := by
  have hterm : ∀ i : Fin N, HasDerivAt (fun ε : ℝ => (1 / 2) * (m i * ‖(v + ε • w) i‖ ^ 2))
      (m i * inner ℝ (v i) (w i)) 0 := by
    intro i
    have h1 : HasDerivAt (fun ε : ℝ => (v + ε • w) i) (w i) 0 := by
      have h2 : HasDerivAt (fun ε : ℝ => v i + ε • (w i)) (w i) 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).smul_const (w i)).const_add (v i)
      simpa only [add_smul_apply] using h2
    have h3 : HasDerivAt (fun ε : ℝ => ‖(v + ε • w) i‖ ^ 2)
        (2 * inner ℝ (v i) (w i)) 0 := by
      simpa using h1.norm_sq
    have h4 : HasDerivAt (fun ε : ℝ => (1 / 2) * (m i * ‖(v + ε • w) i‖ ^ 2))
        ((1 / 2) * (m i * (2 * inner ℝ (v i) (w i)))) 0 :=
      (h3.const_mul (m i)).const_mul (1 / 2 : ℝ)
    convert h4 using 1
    ring
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun i _ => hterm i)
  have hEq : (∑ i : Fin N, (fun ε : ℝ => (1 / 2) * (m i * ‖(v + ε • w) i‖ ^ 2)))
      = fun ε : ℝ => (1 / 2) * ∑ i, m i * ‖(v + ε • w) i‖ ^ 2 := by
    funext ε
    simp only [Finset.sum_apply, Finset.mul_sum]
  rw [hEq] at hsum
  simpa [massInner] using hsum

/-- **Derivative of the kinetic energy in the perturbation parameter** (at an arbitrary point). -/
lemma hasDerivAt_kinetic_at {m : Fin N → ℝ} (v w : EN E N) (x : ℝ) :
    HasDerivAt (fun ε : ℝ => (1 / 2) * ∑ i, m i * ‖(v + ε • w) i‖ ^ 2)
      (massInner m (v + x • w) w) x := by
  have hterm : ∀ i : Fin N, HasDerivAt (fun ε : ℝ => (1 / 2) * (m i * ‖(v + ε • w) i‖ ^ 2))
      (m i * inner ℝ ((v + x • w) i) (w i)) x := by
    intro i
    have h1 : HasDerivAt (fun ε : ℝ => (v + ε • w) i) (w i) x := by
      have h2 : HasDerivAt (fun ε : ℝ => v i + ε • (w i)) (w i) x := by
        simpa using ((hasDerivAt_id x).smul_const (w i)).const_add (v i)
      simpa only [add_smul_apply] using h2
    have h3 : HasDerivAt (fun ε : ℝ => ‖(v + ε • w) i‖ ^ 2)
        (2 * inner ℝ ((v + x • w) i) (w i)) x := h1.norm_sq
    have h4 : HasDerivAt (fun ε : ℝ => (1 / 2) * (m i * ‖(v + ε • w) i‖ ^ 2))
        ((1 / 2) * (m i * (2 * inner ℝ ((v + x • w) i) (w i)))) x :=
      (h3.const_mul (m i)).const_mul (1 / 2 : ℝ)
    convert h4 using 1
    ring
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun i _ => hterm i)
  have hEq : (∑ i : Fin N, (fun ε : ℝ => (1 / 2) * (m i * ‖(v + ε • w) i‖ ^ 2)))
      = fun ε : ℝ => (1 / 2) * ∑ i, m i * ‖(v + ε • w) i‖ ^ 2 := by
    funext ε
    simp only [Finset.sum_apply, Finset.mul_sum]
  rw [hEq] at hsum
  simpa [massInner] using hsum

/-- **Pointwise derivative of the Lagrangian along a linear perturbation.** -/
lemma hasDerivAt_lagR_perturb {m : Fin N → ℝ} {h : ℝ} {q v w v' : EN E N} (x : ℝ)
    (hq : WithoutCollisions (q + x • w)) :
    HasDerivAt (fun ε : ℝ => lagR m h (q + ε • w) (v + ε • v'))
      (massInner m (v + x • v') v' + (fderiv ℝ (U m) (q + x • w)) w) x := by
  have hkin := hasDerivAt_kinetic_at (m := m) v v' x
  have hU : HasDerivAt (fun ε : ℝ => U m (q + ε • w)) ((fderiv ℝ (U m) (q + x • w)) w) x := by
    have h1 : HasDerivAt (fun ε : ℝ => q + ε • w) w x := by
      simpa using ((hasDerivAt_id x).smul_const w).const_add q
    have hf := hasFDerivAt_U_pair m (q + x • w) hq
    rw [hf.fderiv]
    simpa only [Function.comp_def] using hf.comp_hasDerivAt x h1
  have hmain : HasDerivAt (fun ε : ℝ => (1 / 2) * ∑ i, m i * ‖(v + ε • v') i‖ ^ 2
      + U m (q + ε • w) + h)
      (massInner m (v + x • v') v' + (fderiv ℝ (U m) (q + x • w)) w) x := by
    simpa only [Pi.add_apply, add_zero] using (hkin.add hU).add_const h
  have hfun : (fun ε : ℝ => lagR m h (q + ε • w) (v + ε • v'))
      = fun ε : ℝ => (1 / 2) * ∑ i, m i * ‖(v + ε • v') i‖ ^ 2 + U m (q + ε • w) + h := by
    funext ε
    simp only [lagR]
  rw [hfun]
  exact hmain

/-- The derivative of a linearly perturbed absolutely continuous curve, almost everywhere. -/
lemma deriv_add_smul_ae {γ ξ : ℝ → EN E N} {ε a b : ℝ}
    (hac : AbsolutelyContinuousOnInterval γ a b) (hξ : Differentiable ℝ ξ) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc a b →
      deriv (γ + ε • ξ) t = deriv γ t + ε • deriv ξ t := by
  filter_upwards [Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_ae_differentiableAt_vector
    hac] with t ht
  intro hmem
  have hmem' : t ∈ Set.uIcc a b := by
    rw [Set.uIcc_of_le (a := a) (b := b) ((le_of_lt hmem.1).trans hmem.2)]
    exact Set.Ioc_subset_Icc_self hmem
  have h1 : HasDerivAt γ (deriv γ t) t := (ht hmem').hasDerivAt
  have h2 : HasDerivAt ξ (deriv ξ t) t := (hξ t).hasDerivAt
  exact (h1.add (h2.const_smul ε)).deriv


/-- The mass-weighted kinetic energy as a function of the configuration is continuous. -/
lemma continuous_kinetic (m : Fin N → ℝ) : Continuous (fun v : EN E N => kinetic m v) := by
  have : (fun v : EN E N => kinetic m v)
      = fun v => (1 / 2) * ∑ i, m i * ‖v i‖ ^ 2 := rfl
  rw [this]
  fun_prop

/-- **On a collision-free interval the action is the real integral of the real Lagrangian.** -/
theorem actionOn_eq_ofReal_integral_lagR {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {a b : ℝ}
    (hab : a ≤ b) (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hnc : ∀ t ∈ Set.Icc a b, WithoutCollisions (γ t))
    (hfin : actionOn m h γ a b < ⊤) :
    actionOn m h γ a b = ENNReal.ofReal (∫ t in a..b, lagR m h (γ t) (deriv γ t)) := by
  have hnn : ∀ t, 0 ≤ lagR m h (γ t) (deriv γ t) := by
    intro t
    rw [lagR]
    have hU := U_nonneg hm (γ t)
    have hK := kinetic_nonneg m hm (deriv γ t)
    rw [kinetic] at hK
    linarith
  have hpt : ∀ t ∈ Set.Ioc a b,
      lagrangian m h (γ t) (deriv γ t) = ENNReal.ofReal (lagR m h (γ t) (deriv γ t)) :=
    fun t ht => lagrangian_eq_ofReal_lagR (hnc t ⟨ht.1.le, ht.2⟩)
  have h1 : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (lagR m h (γ t) (deriv γ t)))
      = actionOn m h γ a b := by
    rw [actionOn, setLIntegral_congr_fun measurableSet_Ioc hpt]
  have hγcont : ContinuousOn γ (Set.Icc a b) := by
    have h := hac.continuousOn
    rwa [uIcc_of_le hab] at h
  have hUcont : ContinuousOn (fun t => U m (γ t)) (Set.Icc a b) :=
    continuousOn_U.comp hγcont (fun t ht => hnc t ht)
  letI : MeasurableSpace (EN E N) := borel (EN E N)
  haveI : BorelSpace (EN E N) := ⟨rfl⟩
  have hmeas : AEStronglyMeasurable (fun t => lagR m h (γ t) (deriv γ t))
      (volume.restrict (Set.Ioc a b)) := by
    have hK : AEStronglyMeasurable (fun t => kinetic m (deriv γ t))
        (volume.restrict (Set.Ioc a b)) :=
      (continuous_kinetic m).aestronglyMeasurable.comp_aemeasurable
        (Commons.MeasureTheory.Integral.aestronglyMeasurable_deriv_of_absolutelyContinuousOnInterval
          hac).aemeasurable
    have hU : AEStronglyMeasurable (fun t => U m (γ t)) (volume.restrict (Set.Ioc a b)) :=
      (hUcont.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    have hconst : AEStronglyMeasurable (fun _ : ℝ => h) (volume.restrict (Set.Ioc a b)) :=
      aestronglyMeasurable_const
    have hsum := hK.add (hU.add hconst)
    have hfun : (fun t : ℝ => lagR m h (γ t) (deriv γ t))
        = (fun t : ℝ => kinetic m (deriv γ t)) + ((fun t : ℝ => U m (γ t)) + fun _ => h) := by
      funext t
      simp only [lagR, kinetic, Pi.add_apply]
      ring
    rw [hfun]
    exact hsum
  have hInt : Integrable (fun t => lagR m h (γ t) (deriv γ t)) (volume.restrict (Set.Ioc a b)) := by
    refine ⟨hmeas, ?_⟩
    have h4 : (∫⁻ t in Set.Ioc a b, ‖lagR m h (γ t) (deriv γ t)‖ₑ)
        = ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (lagR m h (γ t) (deriv γ t)) :=
      lintegral_congr fun t => by
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn t)]
    have h3 : (∫⁻ t in Set.Ioc a b, ‖lagR m h (γ t) (deriv γ t)‖ₑ) < ⊤ := by
      rw [h4, h1]
      exact hfin
    simpa only [HasFiniteIntegral] using h3
  have h2 : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (lagR m h (γ t) (deriv γ t)))
      = ENNReal.ofReal (∫ t in Set.Ioc a b, lagR m h (γ t) (deriv γ t)) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt (Eventually.of_forall hnn)).symm
  have hfin' : actionOn m h γ a b
      = ENNReal.ofReal (∫ t in Set.Ioc a b, lagR m h (γ t) (deriv γ t)) := by
    rw [← h2]
    exact h1.symm
  rwa [intervalIntegral.integral_of_le hab]


end Submission.NBody
