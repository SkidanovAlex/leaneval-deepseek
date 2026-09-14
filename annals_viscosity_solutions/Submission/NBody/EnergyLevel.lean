import ChallengeDeps
import Submission.NBody.WeakToStrong
import Submission.Commons.MeasureTheory.Integral.aestronglyMeasurable_deriv_of_absolutelyContinuousOnInterval
import Submission.NBody.Tonelli
import Submission.NBody.ActionTau

/-!
# The energy of an `h`-minimiser is `h`

An `h`-minimiser of the Newtonian action (a free-time minimiser of `A_{L+h}`) has energy exactly
`h`.  This is the paper's implicit step: for every `τ > 0`, the linear reparametrisation
`s ↦ γ (T s / τ)` of `γ|[0,T]` onto `[0,τ]` has action

`(T/τ) K + (τ/T) P + h τ`     (`K` = total kinetic energy, `P` = total potential),

which is `≥ φ_h(γ 0, γ T) = A_{L+h}(γ|[0,T])` because `γ` is an `h`-minimiser.  Hence `τ = T` is a
minimum of that function of `τ`, so (as the right and left differential quotients have opposite
signs there) its derivative vanishes:

`-K/T + P/T + h = 0`,   i.e.   `K - P = h T`.

On the other hand, since `γ` is a genuine motion on `(0,T)` (`minimizer_energy_eq`), the pointwise
energy `½∑ᵢmᵢ‖γ̇ᵢ‖² - U(γ)` is constant, equal to `E`, so `K - P = E T`.  Comparing gives `E = h`.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- Total kinetic energy integral `∫⁻ ½∑ᵢmᵢ‖γ̇ᵢ‖²` of a curve on `[0,T]`, as a real number. -/
noncomputable def kineticIntegral (m : Fin N → ℝ) (γ : ℝ → EN E N) (T : ℝ) : ℝ :=
  (∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal (kinetic m (deriv γ s))).toReal

/-- Total potential energy integral `∫⁻ U(γ)` of a curve on `[0,T]`, as a real number. -/
noncomputable def potentialIntegral (m : Fin N → ℝ) (γ : ℝ → EN E N) (T : ℝ) : ℝ :=
  (∫⁻ s in Set.Ioc 0 T, pairPot m (γ s)).toReal

lemma kineticIntegral_nonneg (m : Fin N → ℝ) (γ : ℝ → EN E N) (T : ℝ) :
    0 ≤ kineticIntegral m γ T := ENNReal.toReal_nonneg

lemma potentialIntegral_nonneg (m : Fin N → ℝ) (γ : ℝ → EN E N) (T : ℝ) :
    0 ≤ potentialIntegral m γ T := ENNReal.toReal_nonneg

/-- Elementary `ℝ≥0∞` arithmetic: `ofReal K + ofReal P + ofReal h * ofReal T`. -/
lemma ofReal_add_mul_ofReal {K P h T : ℝ} (hT : 0 ≤ T) (hKg : 0 ≤ K) (hPg : 0 ≤ P)
    (hhg : 0 ≤ h) :
    ENNReal.ofReal K + ENNReal.ofReal P + ENNReal.ofReal h * ENNReal.ofReal T
      = ENNReal.ofReal (K + P + h * T) := by
  rw [← ENNReal.ofReal_add hKg hPg, ← ENNReal.ofReal_mul hhg,
    ← ENNReal.ofReal_add (add_nonneg hKg hPg) (mul_nonneg hhg hT)]

/-- Elementary `ℝ≥0∞` arithmetic for the reparametrised action. -/
lemma ofReal_mul_add_reparam {K P h T τ : ℝ} (hT : 0 < T) (hτ : 0 < τ)
    (hKg : 0 ≤ K) (hPg : 0 ≤ P) (hhg : 0 ≤ h) :
    ENNReal.ofReal (T / τ) * ENNReal.ofReal K + ENNReal.ofReal (τ / T) * ENNReal.ofReal P
        + ENNReal.ofReal h * ENNReal.ofReal τ
      = ENNReal.ofReal ((T / τ) * K + (τ / T) * P + h * τ) := by
  rw [← ENNReal.ofReal_mul (show 0 ≤ T / τ by positivity),
    ← ENNReal.ofReal_mul (show 0 ≤ τ / T by positivity), ← ENNReal.ofReal_mul hhg,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- **Reparametrisation of the decomposed action, in `ℝ≥0∞` form.** -/
lemma actionDec_comp_mul_left_eq {m : Fin N → ℝ} {h T τ : ℝ} {γ : ℝ → EN E N}
    (hT : 0 < T) (hτ : 0 < τ) :
    actionDec m h (fun s : ℝ => γ ((T / τ) * s)) τ
      = ENNReal.ofReal (T / τ) * (∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal (kinetic m (deriv γ s)))
        + ENNReal.ofReal (τ / T) * (∫⁻ s in Set.Ioc 0 T, pairPot m (γ s))
        + ENNReal.ofReal h * ENNReal.ofReal τ := by
  have hκ : 0 < T / τ := div_pos hT hτ
  have h := actionDec_comp_mul_left (m := m) (h := h) (γ := γ) (κ := T / τ) (τ := T) hκ
  rw [show T / (T / τ) = τ by field_simp] at h
  rw [show (T / τ)⁻¹ = τ / T by field_simp] at h
  exact h

/-- The two components of the action are finite when the action is finite. -/
lemma lintegral_kinetic_lt_top_of_actionOn_lt_top {m : Fin N → ℝ} {h T : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h)
    (hnc : ∀ t ∈ Set.Icc 0 T, WithoutCollisions (γ t))
    (hfin : actionOn m h γ 0 T < ⊤) :
    (∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal (kinetic m (deriv γ s))) < ⊤ ∧
      (∫⁻ s in Set.Ioc 0 T, pairPot m (γ s)) < ⊤ := by
  have hAT : actionOn m h γ 0 T = actionDec m h γ T :=
    actionOn_eq_actionDec_of_ae hh hm (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      exact hnc t ⟨ht.1.le, ht.2⟩)
  have hdec : actionDec m h γ T
      = (∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal (kinetic m (deriv γ s)))
        + (∫⁻ s in Set.Ioc 0 T, pairPot m (γ s)) + ENNReal.ofReal h * ENNReal.ofReal T :=
    actionDec_eq h γ T
  have hlt : (∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal (kinetic m (deriv γ s)))
      + (∫⁻ s in Set.Ioc 0 T, pairPot m (γ s)) + ENNReal.ofReal h * ENNReal.ofReal T < ⊤ := by
    rw [← hdec, ← hAT]; exact hfin
  exact ⟨lt_of_le_of_lt (le_trans le_self_add le_self_add) hlt,
    lt_of_le_of_lt (le_trans (le_add_left le_rfl) le_self_add) hlt⟩

/-- **The action of a linearly reparametrised curve, in real terms.** -/
lemma actionOn_comp_mul_left {m : Fin N → ℝ} {h T τ : ℝ} {γ : ℝ → EN E N}
    (hT : 0 < T) (hτ : 0 < τ) (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h)
    (hac : AbsolutelyContinuousOnInterval γ 0 T)
    (hnc : ∀ t ∈ Set.Icc 0 T, WithoutCollisions (γ t))
    (hfin : actionOn m h γ 0 T < ⊤) :
    actionOn m h (fun s : ℝ => γ ((T / τ) * s)) 0 τ
      = ENNReal.ofReal ((T / τ) * kineticIntegral m γ T + (τ / T) * potentialIntegral m γ T
          + h * τ) := by
  obtain ⟨hK1, hP1⟩ := lintegral_kinetic_lt_top_of_actionOn_lt_top hm hh hnc hfin
  have hK : (∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal (kinetic m (deriv γ s)))
      = ENNReal.ofReal (kineticIntegral m γ T) := (ENNReal.ofReal_toReal hK1.ne).symm
  have hP : (∫⁻ s in Set.Ioc 0 T, pairPot m (γ s))
      = ENNReal.ofReal (potentialIntegral m γ T) := (ENNReal.ofReal_toReal hP1.ne).symm
  have hAO : actionDec m h (fun s : ℝ => γ ((T / τ) * s)) τ
      = actionOn m h (fun s : ℝ => γ ((T / τ) * s)) 0 τ :=
    (actionOn_eq_actionDec_of_ae hh hm (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      refine hnc _ ⟨?_, ?_⟩
      · exact (mul_pos (div_pos hT hτ) ht.1).le
      · calc (T / τ) * t ≤ (T / τ) * τ :=
              mul_le_mul_of_nonneg_left ht.2 (div_pos hT hτ).le
          _ = T := by field_simp)).symm
  have hcomp := actionDec_comp_mul_left_eq (m := m) (h := h) (γ := γ) hT hτ
  rw [hAO, hK, hP] at hcomp
  have hKm : 0 ≤ kineticIntegral m γ T := kineticIntegral_nonneg m γ T
  have hPm : 0 ≤ potentialIntegral m γ T := potentialIntegral_nonneg m γ T
  rw [hcomp, ofReal_mul_add_reparam hT hτ hKm hPm hh]

/-- Real integral form of the kinetic component. -/
lemma integral_kinetic_eq_kineticIntegral {m : Fin N → ℝ} {T : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 ≤ m i) (hac : AbsolutelyContinuousOnInterval γ 0 T)
    (h : (∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal (kinetic m (deriv γ s))) < ⊤) :
    ∫ s in Set.Ioc 0 T, kinetic m (deriv γ s) = kineticIntegral m γ T := by
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 T)] fun s => kinetic m (deriv γ s) :=
    Filter.Eventually.of_forall fun s => kinetic_nonneg m hm (deriv γ s)
  letI : MeasurableSpace (EN E N) := borel (EN E N)
  haveI : BorelSpace (EN E N) := ⟨rfl⟩
  have hmeas : AEStronglyMeasurable (fun s : ℝ => kinetic m (deriv γ s))
      (volume.restrict (Set.Ioc 0 T)) :=
    (continuous_kinetic m).aestronglyMeasurable.comp_aemeasurable
      (Commons.MeasureTheory.Integral.aestronglyMeasurable_deriv_of_absolutelyContinuousOnInterval
        hac).aemeasurable
  have hint : Integrable (fun s : ℝ => kinetic m (deriv γ s))
      (volume.restrict (Set.Ioc 0 T)) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas hnn).mp h.ne
  have hbridge := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn
  have h1 : ENNReal.ofReal (∫ s in Set.Ioc 0 T, kinetic m (deriv γ s))
      = ENNReal.ofReal (kineticIntegral m γ T) := by
    rw [hbridge]
    exact (ENNReal.ofReal_toReal h.ne).symm
  have h2 : 0 ≤ ∫ s in Set.Ioc 0 T, kinetic m (deriv γ s) :=
    MeasureTheory.integral_nonneg fun s => kinetic_nonneg m hm (deriv γ s)
  have h3 : 0 ≤ kineticIntegral m γ T := kineticIntegral_nonneg m γ T
  have h4 := congrArg ENNReal.toReal h1
  rwa [ENNReal.toReal_ofReal h2, ENNReal.toReal_ofReal h3] at h4

/-- Off collisions the extended pair potential is `ofReal` of the Newtonian potential. -/
lemma lintegral_ofReal_U_eq_lintegral_pairPot {m : Fin N → ℝ} {T : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 ≤ m i) (hnc : ∀ t ∈ Set.Icc 0 T, WithoutCollisions (γ t)) :
    (∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal (U m (γ s)))
      = ∫⁻ s in Set.Ioc 0 T, pairPot m (γ s) := by
  refine lintegral_congr_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
  exact (pairPot_eq_ofReal_U hm (hnc s ⟨hs.1.le, hs.2⟩)).symm

/-- Real integral form of the potential component. -/
lemma integral_U_eq_potentialIntegral {m : Fin N → ℝ} {T : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 ≤ m i) (hcont : ContinuousOn γ (Set.Ioc 0 T))
    (hnc : ∀ t ∈ Set.Icc 0 T, WithoutCollisions (γ t))
    (h : (∫⁻ s in Set.Ioc 0 T, pairPot m (γ s)) < ⊤) :
    ∫ s in Set.Ioc 0 T, U m (γ s) = potentialIntegral m γ T := by
  have hpair := lintegral_ofReal_U_eq_lintegral_pairPot (m := m) (T := T) hm hnc
  have hUcont : ContinuousOn (fun s : ℝ => U m (γ s)) (Set.Ioc 0 T) :=
    (continuousOn_U (m := m)).comp hcont fun s hs => hnc s ⟨hs.1.le, hs.2⟩
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 T)] fun s => U m (γ s) :=
    Filter.Eventually.of_forall fun s => U_nonneg hm (γ s)
  have hint : Integrable (fun s : ℝ => U m (γ s)) (volume.restrict (Set.Ioc 0 T)) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      (hUcont.aestronglyMeasurable measurableSet_Ioc) hnn).mp (by rw [hpair]; exact h.ne)
  have hbridge := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn
  have h1 : ENNReal.ofReal (∫ s in Set.Ioc 0 T, U m (γ s))
      = ENNReal.ofReal (potentialIntegral m γ T) := by
    rw [hbridge, hpair]
    exact (ENNReal.ofReal_toReal h.ne).symm
  have h2 : 0 ≤ ∫ s in Set.Ioc 0 T, U m (γ s) :=
    MeasureTheory.integral_nonneg fun s => U_nonneg hm (γ s)
  have h3 : 0 ≤ potentialIntegral m γ T := potentialIntegral_nonneg m γ T
  have h4 := congrArg ENNReal.toReal h1
  rwa [ENNReal.toReal_ofReal h2, ENNReal.toReal_ofReal h3] at h4

/-- **Elementary calculus.**  If `τ ↦ (T/τ)·K + (τ/T)·P + hτ` has a minimum at `τ = T > 0`, then
`K - P = h·T`. -/
lemma sub_eq_of_reparam_min {K P h T : ℝ} (hT : 0 < T)
    (hineq : ∀ τ : ℝ, 0 < τ → K + P + h * T ≤ (T / τ) * K + (τ / T) * P + h * τ) :
    K - P = h * T := by
  set F : ℝ → ℝ := fun τ => (T / τ) * K + (τ / T) * P + h * τ - (K + P + h * T) with hF
  have hFT : F T = 0 := by
    rw [hF]; field_simp; ring
  have hquot : ∀ ε : ℝ, ε ≠ 0 → T + ε ≠ 0 →
      (F (T + ε) - F T) / ε = -K / (T + ε) + P / T + h := by
    intro ε hε _
    rw [hFT, hF]
    field_simp
    ring
  have hlim : Tendsto (fun ε : ℝ => -K / (T + ε) + P / T + h) (𝓝 0)
      (𝓝 (-K / T + P / T + h)) := by
    have hconv : Tendsto (fun ε : ℝ => -K / (T + ε)) (𝓝 0) (𝓝 (-K / T)) := by
      have hc : ContinuousAt (fun ε : ℝ => -K / (T + ε)) 0 :=
        ContinuousAt.div continuousAt_const (continuousAt_id.const_add T) (by simpa using hT.ne')
      simpa using hc.tendsto
    have h2 : Tendsto (fun _ : ℝ => P / T + h) (𝓝 0) (𝓝 (P / T + h)) := tendsto_const_nhds
    have h3 := hconv.add h2
    simpa only [add_assoc] using h3
  have hge : 0 ≤ -K / T + P / T + h := by
    have hev : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 ≤ -K / (T + ε) + P / T + h := by
      filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hT] with ε hε hεI
      have hpos : 0 ≤ F (T + ε) := by
        rw [hF]
        have := hineq (T + ε) (by linarith [hεI.1, hεI.2])
        linarith
      have hTε : 0 < T + ε := by linarith [hεI.1, hεI.2]
      rw [← hquot ε (ne_of_gt hε) hTε.ne']
      exact div_nonneg (by linarith [hpos, hFT]) hε.le
    have hlim' : Tendsto (fun ε : ℝ => -K / (T + ε) + P / T + h) (𝓝[>] (0:ℝ))
        (𝓝 (-K / T + P / T + h)) := hlim.mono_left nhdsWithin_le_nhds
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim' hev
  have hle : -K / T + P / T + h ≤ 0 := by
    have hev : ∀ᶠ ε : ℝ in 𝓝[<] (0:ℝ), -K / (T + ε) + P / T + h ≤ 0 := by
      filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsLT (show -T < (0:ℝ) by linarith)] with ε hε hεI
      have hpos : 0 ≤ F (T + ε) := by
        rw [hF]
        have := hineq (T + ε) (by linarith [hεI.1, hεI.2])
        linarith
      have hTε : 0 < T + ε := by linarith [hεI.1, hεI.2]
      rw [← hquot ε (ne_of_lt hε) hTε.ne']
      exact div_nonpos_of_nonneg_of_nonpos (by linarith [hpos, hFT]) hε.le
    have hlim' : Tendsto (fun ε : ℝ => -K / (T + ε) + P / T + h) (𝓝[<] (0:ℝ))
        (𝓝 (-K / T + P / T + h)) := hlim.mono_left nhdsWithin_le_nhds
    exact le_of_tendsto_of_tendsto hlim' tendsto_const_nhds hev
  have hzero : -K / T + P / T + h = 0 := le_antisymm hle hge
  field_simp at hzero
  linarith

/-- **The energy of an `h`-minimiser is `h`.** -/
theorem minimizer_energy_eq_level {m : Fin N → ℝ} {h T : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hT : 0 < T)
    (hac : AbsolutelyContinuousOnInterval γ 0 T)
    (hnc : ∀ t ∈ Set.Icc 0 T, WithoutCollisions (γ t))
    (hmin : IsHMinimizer m h γ 0 T)
    (hfin : actionPot m h (γ 0) (γ T) < ⊤) :
    ∀ s ∈ Set.Ioo 0 T, energy m γ s = h := by
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hh0 : 0 ≤ h := hh.le
  obtain ⟨hK1, hP1⟩ := lintegral_kinetic_lt_top_of_actionOn_lt_top hm0 hh0 hnc (by rw [hmin]; exact hfin)
  -- the action of `γ` at its own travel time
  have hA : actionOn m h γ 0 T
      = ENNReal.ofReal (kineticIntegral m γ T + potentialIntegral m γ T + h * T) := by
    have hAT : actionOn m h γ 0 T = actionDec m h γ T :=
      actionOn_eq_actionDec_of_ae hh0 hm0 (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        exact hnc t ⟨ht.1.le, ht.2⟩)
    have hKof : (∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal (kinetic m (deriv γ s)))
        = ENNReal.ofReal (kineticIntegral m γ T) := (ENNReal.ofReal_toReal hK1.ne).symm
    have hPof : (∫⁻ s in Set.Ioc 0 T, pairPot m (γ s))
        = ENNReal.ofReal (potentialIntegral m γ T) := (ENNReal.ofReal_toReal hP1.ne).symm
    rw [hAT, actionDec_eq h γ T, hKof, hPof,
      ofReal_add_mul_ofReal hT.le (kineticIntegral_nonneg m γ T)
        (potentialIntegral_nonneg m γ T) hh0]
  -- the reparametrisation inequality
  have hineq : ∀ τ : ℝ, 0 < τ →
      kineticIntegral m γ T + potentialIntegral m γ T + h * T
        ≤ (T / τ) * kineticIntegral m γ T + (τ / T) * potentialIntegral m γ T + h * τ := by
    intro τ hτ
    have hAC : AbsolutelyContinuousOnInterval (fun s : ℝ => γ ((T / τ) * s)) 0 τ := by
      have h1 : T / (T / τ) = τ := by field_simp
      have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
        (f := γ) (a := 0) (b := T) (c := T / τ) (d := 0) (div_ne_zero hT.ne' hτ.ne') hac
      simpa [h1] using h
    have hle : actionPot m h (γ 0) (γ T) ≤ actionOn m h (fun s : ℝ => γ ((T / τ) * s)) 0 τ :=
      actionPot_le_of hτ (by simp) (by
        show γ ((T / τ) * τ) = γ T
        rw [show (T / τ) * τ = T by field_simp]) hAC
    rw [← hmin, hA, actionOn_comp_mul_left hT hτ hm0 hh0 hac hnc (by rw [hmin]; exact hfin)] at hle
    have hnn : 0 ≤ (T / τ) * kineticIntegral m γ T + (τ / T) * potentialIntegral m γ T + h * τ :=
      add_nonneg (add_nonneg (mul_nonneg (div_pos hT hτ).le (kineticIntegral_nonneg m γ T))
        (mul_nonneg (div_pos hτ hT).le (potentialIntegral_nonneg m γ T))) (mul_nonneg hh0 hτ.le)
    exact (ENNReal.ofReal_le_ofReal_iff hnn).mp hle
  have hKP : kineticIntegral m γ T - potentialIntegral m γ T = h * T :=
    sub_eq_of_reparam_min hT hineq
  -- the pointwise energy is constant on `(0,T)`
  have hEconst : ∀ s ∈ Set.Ioo 0 T, energy m γ s = energy m γ (T / 2) := fun s hs =>
    minimizer_energy_eq hm hh hT hac hnc hmin hfin s hs (T / 2) ⟨by linarith, by linarith⟩
  have hae : (fun t => energy m γ t) =ᵐ[volume.restrict (Set.Ioc 0 T)]
      fun _ => energy m γ (T / 2) := by
    show ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)), energy m γ t = energy m γ (T / 2)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [show ∀ᵐ t ∂(volume : Measure ℝ), t ≠ T by
      rw [MeasureTheory.ae_iff]; simp] with t ht htI
    exact hEconst t ⟨htI.1, lt_of_le_of_ne htI.2 ht⟩
  -- the two computations of `∫ energy`
  have h1 : ∫ t in Set.Ioc 0 T, energy m γ t = T * energy m γ (T / 2) := by
    rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.setIntegral_const,
      MeasureTheory.measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hT.le]
    ring
  have hγcont : ContinuousOn γ (Set.Ioc 0 T) := by
    have h := hac.continuousOn
    rw [uIcc_of_le hT.le] at h
    exact h.mono Set.Ioc_subset_Icc_self
  letI : MeasurableSpace (EN E N) := borel (EN E N)
  haveI : BorelSpace (EN E N) := ⟨rfl⟩
  have hintK : Integrable (fun s : ℝ => kinetic m (deriv γ s)) (volume.restrict (Set.Ioc 0 T)) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      ((continuous_kinetic m).aestronglyMeasurable.comp_aemeasurable
        (Commons.MeasureTheory.Integral.aestronglyMeasurable_deriv_of_absolutelyContinuousOnInterval
          hac).aemeasurable)
      (Filter.Eventually.of_forall fun s => kinetic_nonneg m hm0 (deriv γ s))).mp hK1.ne
  have hUcont : ContinuousOn (fun s : ℝ => U m (γ s)) (Set.Ioc 0 T) :=
    (continuousOn_U (m := m)).comp hγcont fun s hs => hnc s ⟨hs.1.le, hs.2⟩
  have hU1 : (∫⁻ a in Set.Ioc 0 T, ENNReal.ofReal (U m (γ a))) < ⊤ := by
    rw [lintegral_ofReal_U_eq_lintegral_pairPot (m := m) (T := T) hm0 hnc]
    exact hP1
  have hintU : Integrable (fun s : ℝ => U m (γ s)) (volume.restrict (Set.Ioc 0 T)) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      (hUcont.aestronglyMeasurable measurableSet_Ioc)
      (Filter.Eventually.of_forall fun s => U_nonneg hm0 (γ s))).mp hU1.ne
  have h2 : ∫ t in Set.Ioc 0 T, energy m γ t
      = kineticIntegral m γ T - potentialIntegral m γ T := by
    rw [MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun t => rfl : (fun t => energy m γ t) =ᵐ[volume.restrict (Set.Ioc 0 T)]
        fun t => kinetic m (deriv γ t) - U m (γ t)),
      integral_sub hintK hintU, integral_kinetic_eq_kineticIntegral hm0 hac hK1,
      integral_U_eq_potentialIntegral hm0 hγcont hnc hP1]
  intro s hs
  have hEt : energy m γ (T / 2) = h := by
    have h3 : T * energy m γ (T / 2) = T * h := by rw [← h1, h2, hKP, mul_comm h T]
    exact mul_left_cancel₀ hT.ne' h3
  rw [hEconst s hs, hEt]

end Submission.NBody
