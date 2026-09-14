import Submission.NBody.LYZEnergy
import Submission.NBody.LYZSub
import Mathlib

/-!
# The energy identity with collision-freeness only on `(0, T]`

The chain of lemmas `actionOn_eq_ofReal_integral_lagR`,
`minimizer_energy_eq_level`, `lagR_eq_weightedNorm_sq_of_minimizer`,
`sqrt_two_h_le_weightedNorm_of_minimizer` and `integral_weightedNorm_sq_eq_actionOn` assumes the
curve to be collision free on the *closed* interval `[0,T]`.  For the limiting construction of
Liu--Yan--Zhou one has to allow the initial configuration `γ 0 = x₀` to be a collision (the theorem
is stated for an arbitrary `x₀`), so the same results are needed with the hypothesis weakened to
`WithoutCollisions (γ t)` for `t ∈ (0,T]`.

Every use of the hypothesis in the original proofs is at an interior point or almost everywhere, so
the statements transfer verbatim; the only lemma that genuinely has to be re-proved from scratch is
`minimizer_energy_eq_level_ioc`, and it is deduced from the closed-interval statement by applying
the latter to the shifted curve `u ↦ γ (u + s/2)` on `[0, T/2]` (which *is* collision free on a
closed interval because `s > 0`), using that `IsHMinimizer` is stable under sub-intervals.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **On a collision-free `(a,b]` the action is a real integral.**  Same as
`actionOn_eq_ofReal_integral_lagR` with the collision-freeness hypothesis only on `Ioc a b`. -/
theorem actionOn_eq_ofReal_integral_lagR_ioc {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {a b : ℝ}
    (hab : a ≤ b) (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hnc : ∀ t ∈ Set.Ioc a b, WithoutCollisions (γ t))
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
    fun t ht => lagrangian_eq_ofReal_lagR (hnc t ht)
  have h1 : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (lagR m h (γ t) (deriv γ t)))
      = actionOn m h γ a b := by
    rw [actionOn, setLIntegral_congr_fun measurableSet_Ioc hpt]
  have hγcont : ContinuousOn γ (Set.Ioc a b) := by
    have h := hac.continuousOn
    rw [uIcc_of_le hab] at h
    exact h.mono Set.Ioc_subset_Icc_self
  have hUcont : ContinuousOn (fun t => U m (γ t)) (Set.Ioc a b) :=
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
      hUcont.aestronglyMeasurable measurableSet_Ioc
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

/-- **The energy of an `h`-minimiser is `h`**, assuming collision-freeness only on `(0,T]`. -/
theorem minimizer_energy_eq_level_ioc {m : Fin N → ℝ} {h T : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hT : 0 < T)
    (hac : AbsolutelyContinuousOnInterval γ 0 T)
    (hnc : ∀ t ∈ Set.Ioc 0 T, WithoutCollisions (γ t))
    (hmin : IsHMinimizer m h γ 0 T)
    (hfin : actionPot m h (γ 0) (γ T) < ⊤) :
    ∀ s ∈ Set.Ioo 0 T, energy m γ s = h := by
  intro s hs
  have hs2 : 0 < s / 2 := by linarith [hs.1]
  have hs2T : s / 2 < T / 2 := by linarith [hs.2]
  have hT2 : 0 < T / 2 := by linarith [hs.1, hs.2]
  have hfin' : actionOn m h γ 0 T < ⊤ := by rw [hmin]; exact hfin
  -- the sub-minimiser on `[s/2, T/2 + s/2]`
  have hbd : T / 2 + s / 2 < T := by linarith [hs.2]
  have hmin_sub : IsHMinimizer m h γ (s / 2) (T / 2 + s / 2) :=
    IsHMinimizer.sub hac hmin hfin' hs2 (by linarith [hs2T]) hbd
  -- shift it to `[0, T/2]`
  have hmin_shift : IsHMinimizer m h (fun u : ℝ => γ (u + s / 2)) 0 (T / 2) := by
    show actionOn m h (fun u : ℝ => γ (u + s / 2)) 0 (T / 2)
      = actionPot m h ((fun u : ℝ => γ (u + s / 2)) 0) ((fun u : ℝ => γ (u + s / 2)) (T / 2))
    rw [actionOn_comp_add_const]
    simp only [zero_add]
    rw [show (s : ℝ) / 2 + T / 2 = T / 2 + s / 2 by ring]
    exact hmin_sub
  -- absolute continuity of the shifted curve on `[0, T/2]`
  have hac_shift : AbsolutelyContinuousOnInterval (fun u : ℝ => γ (u + s / 2)) 0 (T / 2) := by
    have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
      (f := γ) (a := 0) (b := T) (c := 1) (d := s / 2) one_ne_zero hac
    have h' : AbsolutelyContinuousOnInterval (fun u : ℝ => γ (u + s / 2)) (-(s / 2)) (T - s / 2) := by
      simpa only [one_mul, div_one, zero_sub] using h
    refine h'.mono ?_
    rw [uIcc_of_le hT2.le, uIcc_of_le (by linarith [hs.1] : -(s / 2) ≤ T - s / 2)]
    exact Set.Icc_subset_Icc (by linarith [hs.1]) (by linarith [hs.2])
  -- collision freeness of the shifted curve on `[0, T/2]`
  have hnc_shift : ∀ t ∈ Set.Icc 0 (T / 2),
      WithoutCollisions ((fun u : ℝ => γ (u + s / 2)) t) := by
    intro t ht
    exact hnc (t + s / 2) ⟨by linarith [ht.1, hs2], by linarith [ht.2, hs2T]⟩
  have hfin_shift : actionPot m h ((fun u : ℝ => γ (u + s / 2)) 0)
      ((fun u : ℝ => γ (u + s / 2)) (T / 2)) < ⊤ := by
    have hsplit : actionOn m h γ 0 T
        = actionOn m h γ 0 (s / 2) + actionOn m h γ (s / 2) T :=
      actionOn_add γ hs2.le (by linarith [hs.2] : s / 2 ≤ T)
    have hlt : actionOn m h γ (s / 2) T < ⊤ := by
      rw [hsplit] at hfin'
      exact (ENNReal.add_lt_top.mp hfin').2
    have hsplit2 : actionOn m h γ (s / 2) T
        = actionOn m h γ (s / 2) (T / 2 + s / 2) + actionOn m h γ (T / 2 + s / 2) T :=
      actionOn_add γ (by linarith [hs2T]) (by linarith [hs.2])
    have hfin_sub : actionOn m h γ (s / 2) (T / 2 + s / 2) < ⊤ := by
      rw [hsplit2] at hlt
      exact (ENNReal.add_lt_top.mp hlt).1
    refine lt_of_le_of_lt (le_of_eq ?_) hfin_sub
    show actionPot m h (γ (0 + s / 2)) (γ (T / 2 + s / 2)) = _
    rw [zero_add]
    exact hmin_sub.symm
  have hmain := minimizer_energy_eq_level hm hh hT2 hac_shift hnc_shift hmin_shift hfin_shift
    (s / 2) ⟨hs2, hs2T⟩
  -- transfer the energy back
  have henergy : energy m (fun u : ℝ => γ (u + s / 2)) (s / 2) = energy m γ s := by
    simp only [energy, deriv_comp_add_const]
    ring_nf
  rwa [henergy] at hmain

/-- **On a collision-free `(0,t]` `h`-minimiser the Lagrangian is the squared mass norm of the
velocity.** -/
theorem lagR_eq_weightedNorm_sq_of_minimizer_ioc {m : Fin N → ℝ} {h T : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hT : 0 < T)
    (hac : AbsolutelyContinuousOnInterval γ 0 T)
    (hnc : ∀ t ∈ Set.Ioc 0 T, WithoutCollisions (γ t))
    (hmin : IsHMinimizer m h γ 0 T)
    (hfin : actionPot m h (γ 0) (γ T) < ⊤) :
    ∀ s ∈ Set.Ioo 0 T, lagR m h (γ s) (deriv γ s) = ‖deriv γ s‖_[m] ^ 2 := by
  intro s hs
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have he := minimizer_energy_eq_level_ioc hm hh hT hac hnc hmin hfin s hs
  have hk : (1 / 2) * ∑ i, m i * ‖(deriv γ s) i‖ ^ 2 = (1 / 2) * (‖deriv γ s‖_[m]) ^ 2 :=
    kinetic_eq_half_weightedNorm_sq' hm0 (deriv γ s)
  have hw := weightedNorm_sq hm0 (deriv γ s)
  rw [energy] at he
  rw [lagR, hw]
  linarith [he, hk]

/-- The speed of a collision-free `h`-minimiser is at least `√(2h)`. -/
theorem sqrt_two_h_le_weightedNorm_of_minimizer_ioc {m : Fin N → ℝ} {h T : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hT : 0 < T)
    (hac : AbsolutelyContinuousOnInterval γ 0 T)
    (hnc : ∀ t ∈ Set.Ioc 0 T, WithoutCollisions (γ t))
    (hmin : IsHMinimizer m h γ 0 T)
    (hfin : actionPot m h (γ 0) (γ T) < ⊤) :
    ∀ s ∈ Set.Ioo 0 T, Real.sqrt (2 * h) ≤ ‖deriv γ s‖_[m] := by
  intro s hs
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have he := minimizer_energy_eq_level_ioc hm hh hT hac hnc hmin hfin s hs
  have hk : (1 / 2) * ∑ i, m i * ‖(deriv γ s) i‖ ^ 2 = (1 / 2) * (‖deriv γ s‖_[m]) ^ 2 :=
    kinetic_eq_half_weightedNorm_sq' hm0 (deriv γ s)
  have hU := U_nonneg hm0 (γ s)
  have hx : 0 ≤ ‖deriv γ s‖_[m] := weightedNorm_nonneg m _
  rw [energy] at he
  have h2 : (‖deriv γ s‖_[m]) ^ 2 = 2 * (U m (γ s) + h) := by linarith [he, hk]
  have h3 : 2 * h ≤ (‖deriv γ s‖_[m]) ^ 2 := by linarith [h2, hU]
  calc Real.sqrt (2 * h) ≤ Real.sqrt ((‖deriv γ s‖_[m]) ^ 2) := Real.sqrt_le_sqrt h3
    _ = ‖deriv γ s‖_[m] := Real.sqrt_sq hx

/-- **The integral of the squared speed is the action**, for an `h`-minimiser that is collision
free only on `(0,t]`. -/
theorem integral_weightedNorm_sq_eq_actionOn_ioc {m : Fin N → ℝ} {h : ℝ} (hh : 0 < h)
    (hm : ∀ i, 0 < m i) (hh0 : 0 ≤ h) {γ : ℝ → EN E N} {t : ℝ} (ht : 0 < t)
    (hac : AbsolutelyContinuousOnInterval γ 0 t)
    (hnc : ∀ s ∈ Set.Ioc 0 t, WithoutCollisions (γ s))
    (hmin : IsHMinimizer m h γ 0 t)
    (hfin : actionPot m h (γ 0) (γ t) < ⊤) :
    ∫ s in (0:ℝ)..t, ‖deriv γ s‖_[m] ^ 2 = (actionOn m h γ 0 t).toReal := by
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hfin' : actionOn m h γ 0 t < ⊤ := by rw [hmin]; exact hfin
  have h1 : actionOn m h γ 0 t
      = ENNReal.ofReal (∫ s in (0:ℝ)..t, lagR m h (γ s) (deriv γ s)) :=
    actionOn_eq_ofReal_integral_lagR_ioc ht.le hm0 hh0 hac hnc hfin'
  have h2 : ∫ s in (0:ℝ)..t, lagR m h (γ s) (deriv γ s)
      = ∫ s in (0:ℝ)..t, ‖deriv γ s‖_[m] ^ 2 := by
    have hnull : volume ({0, t} : Set ℝ) = 0 := (Set.toFinite _).measure_zero volume
    rw [intervalIntegral.integral_congr_ae
      (f := fun s => lagR m h (γ s) (deriv γ s)) (g := fun s => ‖deriv γ s‖_[m] ^ 2) ?_]
    filter_upwards [compl_mem_ae_iff.mpr hnull] with s hs hsI
    rw [Set.uIoc_of_le ht.le] at hsI
    have hst : s < t := by
      rcases lt_or_eq_of_le hsI.2 with h | h
      · exact h
      · exact absurd (by simp [h] : s ∈ ({0, t} : Set ℝ)) hs
    exact lagR_eq_weightedNorm_sq_of_minimizer_ioc hm hh ht hac hnc hmin hfin s ⟨hsI.1, hst⟩
  have hnn : 0 ≤ ∫ s in (0:ℝ)..t, ‖deriv γ s‖_[m] ^ 2 :=
    intervalIntegral.integral_nonneg ht.le fun s _ => sq_nonneg _
  rw [h1, h2, ENNReal.toReal_ofReal hnn]

end Submission.NBody
