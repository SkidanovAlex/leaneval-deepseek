import Submission.NBody.Assembly
import Submission.NBody.EnergyLevel
import Submission.NBody.ChazyContinuity

/-!
# The limit shape of a calibrating curve

This module isolates the two inputs of the Maderna--Venturelli proof that concern the *asymptotic
shape* of a calibrating curve `γ` of a horofunction directed by a configuration `a`:

* **Marchal--Saari's theorem** (Marchal & Saari 1976): a motion which is not superhyperbolic has a
  limit shape, i.e. `t⁻¹ x(t)` converges.  We record only this consequence (the paper does not need
  the sharper `O(t^{2/3})` rate).  It is a genuine theorem of celestial mechanics which is *not* yet
  formalised; it enters here as the hypothesis `MarchalSaari`.

* The **normalisation of the limit shape**: if the limit shape `b` is collision free and the motion
  has energy `h`, then `‖b‖_[m]² = 2h` (`norm_limitShape_sq_eq_two_h`).  The proof is the identity
  `energy_eq_of_asymptotic`: the energy of a solution asymptotic to `(c t) • b` is
  `(1/2) c² ∑ᵢ mᵢ ‖bᵢ‖²`.

We also introduce the **configurational measure** `configMeasure m x = ‖x‖_[m] * U m x`, homogeneous
of degree `0`, whose finiteness is exactly the collision-freeness of `x` (for `x ≠ 0`).
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-! ## The configurational measure -/

/-- The **configurational measure** `μ(x) = ‖x‖_[m] · U(x)`: a function of degree `0`.  The paper's
`μ` is `U I^{1/2}`; on the sphere `‖x‖_[m] = 1` it coincides with `U`. -/
noncomputable def configMeasure (m : Fin N → ℝ) (x : EN E N) : ℝ := ‖x‖_[m] * U m x

lemma configMeasure_nonneg {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (x : EN E N) :
    0 ≤ configMeasure m x :=
  mul_nonneg (weightedNorm_nonneg m x) (U_nonneg hm x)

/-- The configurational measure is homogeneous of degree `0`. -/
lemma configMeasure_smul {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) {c : ℝ} (hc : 0 < c)
    (x : EN E N) : configMeasure m (c • x) = configMeasure m x := by
  unfold configMeasure
  rw [weightedNorm_smul hm, U_smul, abs_of_pos hc]
  field_simp

/-! ## The normalisation of the limit shape -/

/-- The squared mass-weighted norm is the mass-weighted sum of the squared components. -/
lemma weightedNorm_sq {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (x : EN E N) :
    (‖x‖_[m]) ^ 2 = ∑ i, m i * ‖x i‖ ^ 2 := by
  unfold weightedNorm
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hm i) (sq_nonneg _)

/-- **The limit shape of an energy-`h` motion is normalised**: `‖b‖_[m]² = 2h`. -/
theorem norm_limitShape_sq_eq_two_h {m : Fin N → ℝ} {h : ℝ} {b : EN E N} {x : ℝ → EN E N}
    (hm : ∀ i, 0 < m i) (hb : WithoutCollisions b)
    (hsol : IsNBodySolution m x) (hnc : ∀ t > 0, WithoutCollisions (x t))
    (henergy : ∀ t > 0, energy m x t = h)
    (hshape : Tendsto (fun t : ℝ => t⁻¹ • x t) atTop (𝓝 b)) :
    (‖b‖_[m]) ^ 2 = 2 * h := by
  have hmne : ∀ i, m i ≠ 0 := fun i => ne_of_gt (hm i)
  set o : ℝ → EN E N := fun t => x t - t • b with ho
  have h1 : Tendsto (fun t : ℝ => t⁻¹ • o t) atTop (𝓝 (0 : EN E N)) := by
    have hsub : (fun t : ℝ => t⁻¹ • o t) =ᶠ[atTop] fun t => t⁻¹ • x t - b := by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      rw [ho, smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul]
    rw [show (0 : EN E N) = b - b from (sub_self b).symm]
    exact (hshape.sub tendsto_const_nhds).congr' hsub.symm
  have h1n : Tendsto (fun t : ℝ => ‖t⁻¹ • o t‖) atTop (𝓝 0) := by
    simpa using h1.norm
  have ho_little : o =o[atTop] (fun t : ℝ => t) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have h2 : ∀ᶠ t in atTop, ‖t⁻¹ • o t‖ < c := (tendsto_order.1 h1n).2 c hc
    filter_upwards [eventually_ge_atTop (1:ℝ), h2] with t ht1 ht2
    rw [norm_smul, Real.norm_eq_abs, abs_inv] at ht2
    have htpos : (0:ℝ) < |t| := abs_pos.mpr (by linarith)
    have hstep : ‖o t‖ < c * ‖t‖ := by
      have h3 : |t| * (|t|⁻¹ * ‖o t‖) = ‖o t‖ := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt htpos), one_mul]
      have h4 : |t| * c = c * ‖t‖ := by rw [Real.norm_eq_abs, mul_comm]
      have h5 := mul_lt_mul_of_pos_left ht2 htpos
      rw [h3, h4] at h5
      exact h5
    exact hstep.le
  have hasym : ∀ᶠ t in atTop, x t = ((1:ℝ) * t) • b + o t := by
    filter_upwards with t
    rw [one_mul]; exact (add_sub_cancel _ _).symm
  have hE := energy_eq_of_asymptotic m hmne hb one_pos hsol hnc ho_little hasym
  have hE2 : (1 / 2) * (1:ℝ) ^ 2 * (∑ i, m i * ‖b i‖ ^ 2) = h := by
    have := hE 1 one_pos
    rw [henergy 1 one_pos] at this
    linarith
  rw [weightedNorm_sq (fun i => (hm i).le) b]
  linarith

/-! ## Marchal--Saari -/

/-- **Marchal--Saari** (1976): a non-superhyperbolic motion has a limit shape.  Formulated in the
(weaker) form needed here: a solution of Newton's equations which is collision free and grows at
most linearly has convergent normalised configuration `t ↦ t⁻¹ x(t)`. -/
def MarchalSaari (m : Fin N → ℝ) : Prop :=
  ∀ (x : ℝ → EN E N), IsNBodySolution m x → (∀ t > 0, WithoutCollisions (x t)) →
    (∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖x t‖ ≤ C * t) →
    ∃ b : EN E N, Tendsto (fun t : ℝ => t⁻¹ • x t) atTop (𝓝 b)

/-- The calibrating curve of a horofunction has a limit shape, assuming Marchal--Saari. -/
theorem exists_limitShape_of_calibrating {m : Fin N → ℝ} {h : ℝ} {𝔲 : EN E N → ℝ}
    {γs : ℝ → EN E N} (hN : 0 < N) (hm : ∀ i, 0 < m i) (hh : 0 < h)
    (hMS : MarchalSaari (E := E) (N := N) m)
    (hM : MarchalProperty (E := E) m h)
    (hcal : ∀ t : ℝ, 0 < t → AbsolutelyContinuousOnInterval γs 0 t ∧
      IsHMinimizer m h γs 0 t ∧ actionOn m h γs 0 t = ENNReal.ofReal (𝔲 (γs 0) - 𝔲 (γs t))) :
    ∃ b : EN E N, Tendsto (fun t : ℝ => t⁻¹ • γs t) atTop (𝓝 b) := by
  obtain ⟨hsol, hnc⟩ := isNBodySolution_extendLeft_of_calibrating (γ := γs) hN hm hh hM hcal
  obtain ⟨C, hC0, hC⟩ := norm_sub_le_of_calibrating_curve (u := 𝔲) (γ := γs) hN hm hh
    (fun t ht => ⟨(hcal t ht).1, (hcal t ht).2.1⟩)
  have hgrow : ∃ C' : ℝ, ∀ t : ℝ, 1 ≤ t → ‖extendLeft γs t‖ ≤ C' * t := by
    refine ⟨2 * C + ‖γs 0‖, fun t ht => ?_⟩
    rw [extendLeft_of_pos (lt_of_lt_of_le zero_lt_one ht)]
    have h1 : ‖γs t - γs 0‖ ≤ C * (1 + t) := hC t (lt_of_lt_of_le zero_lt_one ht)
    calc ‖γs t‖ ≤ ‖γs t - γs 0‖ + ‖γs 0‖ := by
          simpa using norm_add_le (γs t - γs 0) (γs 0)
      _ ≤ C * (1 + t) + ‖γs 0‖ := by linarith
      _ ≤ (2 * C + ‖γs 0‖) * t := by
          have h3 : ‖γs 0‖ ≤ ‖γs 0‖ * t := le_mul_of_one_le_right (norm_nonneg _) ht
          nlinarith [hC0]
  have hext_nc : ∀ t > 0, WithoutCollisions (extendLeft γs t) := fun t ht => by
    rw [extendLeft_of_pos ht]; exact hnc t ht
  obtain ⟨b, hb⟩ := hMS (extendLeft γs) hsol hext_nc hgrow
  refine ⟨b, ?_⟩
  refine hb.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  rw [extendLeft_of_pos ht]

/-- **The calibrating curve has energy `h` everywhere** (when its initial configuration is
collision free). -/
theorem energy_eq_of_calibrating {m : Fin N → ℝ} {h : ℝ} {𝔲 : EN E N → ℝ} {γs : ℝ → EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 < h)
    (h0nc : WithoutCollisions (γs 0)) (hnc : ∀ t > 0, WithoutCollisions (γs t))
    (hcal : ∀ t : ℝ, 0 < t → AbsolutelyContinuousOnInterval γs 0 t ∧
      IsHMinimizer m h γs 0 t ∧ actionOn m h γs 0 t = ENNReal.ofReal (𝔲 (γs 0) - 𝔲 (γs t))) :
    ∀ t > 0, energy m γs t = h := by
  intro t ht
  have h2t : 0 < t + 1 := by linarith
  have hmin : IsHMinimizer m h γs 0 (t + 1) := (hcal (t+1) h2t).2.1
  have hncI : ∀ s ∈ Set.Icc 0 (t+1), WithoutCollisions (γs s) := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h]; exact h0nc
    · exact hnc s h
  exact minimizer_energy_eq_level hm hh h2t (hcal (t+1) h2t).1 hncI hmin
    (by
      have h1 : actionOn m h γs 0 (t+1) = actionPot m h (γs 0) (γs (t+1)) := hmin
      rw [← h1]
      exact (hcal (t+1) h2t).2.2 ▸ ENNReal.ofReal_lt_top)
    t ⟨ht, by linarith⟩

/-- **The limit shape of a calibrating curve is normalised**: if moreover it is collision free then
`‖b‖_[m]² = 2h`. -/
theorem norm_limitShape_sq_eq_two_h_of_calibrating {m : Fin N → ℝ} {h : ℝ} {𝔲 : EN E N → ℝ}
    {γs : ℝ → EN E N} {b : EN E N} (hN : 0 < N) (hm : ∀ i, 0 < m i) (hh : 0 < h)
    (hM : MarchalProperty (E := E) m h)
    (h0nc : WithoutCollisions (γs 0)) (hnc : ∀ t > 0, WithoutCollisions (γs t))
    (hcal : ∀ t : ℝ, 0 < t → AbsolutelyContinuousOnInterval γs 0 t ∧
      IsHMinimizer m h γs 0 t ∧ actionOn m h γs 0 t = ENNReal.ofReal (𝔲 (γs 0) - 𝔲 (γs t)))
    (hb : WithoutCollisions b) (hshape : Tendsto (fun t : ℝ => t⁻¹ • γs t) atTop (𝓝 b)) :
    (‖b‖_[m]) ^ 2 = 2 * h := by
  obtain ⟨hsol, _⟩ := isNBodySolution_extendLeft_of_calibrating (γ := γs) hN hm hh hM hcal
  have henergy := energy_eq_of_calibrating (γs := γs) hm hh h0nc hnc hcal
  have hext_nc : ∀ t > 0, WithoutCollisions (extendLeft γs t) := fun t ht => by
    rw [extendLeft_of_pos ht]; exact hnc t ht
  have hEext : ∀ t > 0, energy m (extendLeft γs) t = h := by
    intro t ht
    have hagree : extendLeft γs =ᶠ[𝓝 t] γs := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs using extendLeft_of_pos hs
    have hderiv : deriv (extendLeft γs) t = deriv γs t := hagree.deriv_eq
    simp only [energy]
    rw [hderiv, hagree.eq_of_nhds]
    exact henergy t ht
  have hshape' : Tendsto (fun t : ℝ => t⁻¹ • extendLeft γs t) atTop (𝓝 b) := by
    refine hshape.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    rw [extendLeft_of_pos ht]
  exact norm_limitShape_sq_eq_two_h hm hb hsol hext_nc hEext hshape'

end Submission.NBody
