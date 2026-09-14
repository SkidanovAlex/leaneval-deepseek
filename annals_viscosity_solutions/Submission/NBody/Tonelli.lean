import ChallengeDeps
import Submission.NBody.Action
import Submission.NBody.MassNorm
import Submission.Commons.Topology.Metric.exists_tendstoUniformlyOn_subseq_of_holder_of_properSpace
import Submission.Commons.MeasureTheory.Integral.norm_sub_le_sqrt_mul_sqrt_of_absolutelyContinuousOnInterval
import Submission.Commons.MeasureTheory.Integral.setLIntegral_Ioc_comp_mul_left
import Submission.Commons.MeasureTheory.Integral.massWeighted_kinetic_le_liminf
import Submission.Commons.Analysis.Calculus.deriv_comp_min_of_lt
import Submission.Commons.Analysis.Calculus.deriv_comp_min_of_gt
import Submission.Commons.Topology.Metric.exists_path_avoiding_collisions_with_deriv_bound
import Mathlib

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-! ## Fatou's lemma for the extended pair potential along a curve -/

/-- Fatou for the extended pair potential, with convergence only required on the interval. -/
lemma lintegral_pairPot_le_liminf' {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) {τ : ℝ}
    {γs : ℕ → ℝ → EN E N} {γ : ℝ → EN E N}
    (hconv : ∀ t ∈ Set.Ioc 0 τ, Tendsto (fun n => γs n t) atTop (𝓝 (γ t)))
    (hcont : ∀ n, ContinuousOn (γs n) (Set.Ioc 0 τ)) :
    ∫⁻ t in Set.Ioc 0 τ, pairPot m (γ t)
      ≤ liminf (fun n => ∫⁻ t in Set.Ioc 0 τ, pairPot m (γs n t)) atTop := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace (EN E N) := borel (EN E N)
  haveI : BorelSpace (EN E N) := ⟨rfl⟩
  have hterm : ∀ i j : Fin N, Measurable (fun x : EN E N =>
      ENNReal.ofReal (m i * m j) * (ENNReal.ofReal (dist (x i) (x j)))⁻¹) := by
    intro i j
    refine Measurable.mul measurable_const ?_
    refine Measurable.inv ?_
    refine ENNReal.measurable_ofReal.comp ?_
    exact ((PiLp.continuous_apply 2 (fun _ : Fin N => E) i).dist
      (PiLp.continuous_apply 2 (fun _ : Fin N => E) j)).measurable
  have hmeasPair : Measurable (fun x : EN E N => pairPot m x) := by
    have : (fun x : EN E N => pairPot m x) = fun x =>
        ∑ j, ∑ i < j, ENNReal.ofReal (m i * m j) * (ENNReal.ofReal (dist (x i) (x j)))⁻¹ :=
      rfl
    rw [this]
    exact Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun i _ => hterm i j
  have hmeas : ∀ n, AEMeasurable (fun t => pairPot m (γs n t)) (volume.restrict (Set.Ioc 0 τ)) :=
    fun n => hmeasPair.comp_aemeasurable ((hcont n).aemeasurable measurableSet_Ioc)
  have h1 := lintegral_liminf_le' (μ := volume.restrict (Set.Ioc 0 τ))
    (f := fun n t => pairPot m (γs n t)) (u := atTop) hmeas
  refine le_trans ?_ h1
  refine lintegral_mono_ae ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards with t ht
  exact pairPot_le_liminf_pairPot hm (hconv t ht)
/-! ## Continuity of the Newtonian potential on collision-free configurations -/

omit [FiniteDimensional ℝ E] in
theorem continuousOn_U {m : Fin N → ℝ} :
    ContinuousOn (U m) {x : EN E N | WithoutCollisions x} := by
  refine continuousOn_finset_sum _ fun j _ => continuousOn_finset_sum _ fun i hi => ?_
  have hij : i ≠ j := ne_of_lt (Finset.mem_Iio.mp hi)
  refine (ContinuousOn.const_mul ?_ (m i * m j))
  refine ContinuousOn.inv₀ ?_ ?_
  · exact (((PiLp.continuous_apply 2 (fun _ : Fin N => E) i).dist
      (PiLp.continuous_apply 2 (fun _ : Fin N => E) j))).continuousOn
  · intro x hx
    exact hx i j hij

/-! ## Finiteness of the action of a collision-free path -/

/-- A curve that stays collision-free on `[0,τ]`, is continuous there, and whose derivative has
finite `L²` norm on `(0,τ]` has finite Lagrangian action. -/
theorem actionOn_lt_top_of_path {m : Fin N → ℝ} {h : ℝ} (hm : ∀ i, 0 < m i) (hh : 0 ≤ h)
    {γ : ℝ → EN E N} {τ : ℝ}
    (hnc : ∀ t ∈ Set.Icc 0 τ, WithoutCollisions (γ t))
    (hcont : ContinuousOn γ (Set.Icc 0 τ))
    (hderiv : (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv γ t‖ ^ 2)) < ⊤) :
    actionOn m h γ 0 τ < ⊤ := by
  obtain ⟨K, hK⟩ : ∃ K, ∀ t ∈ Set.Icc 0 τ, U m (γ t) ≤ K := by
    have hmap : MapsTo γ (Set.Icc 0 τ) {x : EN E N | WithoutCollisions x} := fun t ht => hnc t ht
    have hcontU : ContinuousOn (fun t => U m (γ t)) (Set.Icc 0 τ) := continuousOn_U.comp hcont hmap
    obtain ⟨K, hK⟩ := IsCompact.bddAbove_image isCompact_Icc hcontU
    exact ⟨K, fun t ht => hK ⟨t, ht, rfl⟩⟩
  set C : ℝ := ∑ i, m i with hCdef
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => (hm i).le
  have hpt : ∀ t ∈ Set.Ioc 0 τ,
      lagrangian m h (γ t) (deriv γ t)
        ≤ ENNReal.ofReal ((1 / 2) * C * ‖deriv γ t‖ ^ 2) + ENNReal.ofReal K + ENNReal.ofReal h := by
    intro t ht
    have htIcc : t ∈ Set.Icc 0 τ := ⟨ht.1.le, ht.2⟩
    rw [lagrangian, if_pos (hnc t htIcc)]
    have hsum : ∑ i, m i * ‖deriv γ t i‖ ^ 2 ≤ C * ‖deriv γ t‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have hmi : m i ≤ C := by
        rw [hCdef]
        exact Finset.single_le_sum (fun j _ => (hm j).le) (Finset.mem_univ i)
      exact mul_le_mul_of_nonneg_right hmi (sq_nonneg _)
    calc ENNReal.ofReal ((1 / 2) * (∑ i, m i * ‖deriv γ t i‖ ^ 2) + U m (γ t) + h)
        ≤ ENNReal.ofReal ((1 / 2) * (∑ i, m i * ‖deriv γ t i‖ ^ 2) + K + h) :=
          ENNReal.ofReal_le_ofReal (by linarith [hK t htIcc])
      _ ≤ ENNReal.ofReal ((1 / 2) * C * ‖deriv γ t‖ ^ 2 + K + h) :=
          ENNReal.ofReal_le_ofReal (by linarith [hsum])
      _ ≤ ENNReal.ofReal ((1 / 2) * C * ‖deriv γ t‖ ^ 2) + ENNReal.ofReal K + ENNReal.ofReal h := by
          calc ENNReal.ofReal ((1 / 2) * C * ‖deriv γ t‖ ^ 2 + K + h)
              ≤ ENNReal.ofReal ((1 / 2) * C * ‖deriv γ t‖ ^ 2 + K) + ENNReal.ofReal h :=
                ENNReal.ofReal_add_le
            _ ≤ (ENNReal.ofReal ((1 / 2) * C * ‖deriv γ t‖ ^ 2) + ENNReal.ofReal K)
                  + ENNReal.ofReal h := add_le_add ENNReal.ofReal_add_le le_rfl
            _ = ENNReal.ofReal ((1 / 2) * C * ‖deriv γ t‖ ^ 2) + ENNReal.ofReal K
                  + ENNReal.ofReal h := rfl
  have hEq : ∫⁻ t in Set.Ioc 0 τ,
        (ENNReal.ofReal ((1 / 2) * C * ‖deriv γ t‖ ^ 2) + ENNReal.ofReal K + ENNReal.ofReal h)
      = ENNReal.ofReal ((1 / 2) * C)
          * (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv γ t‖ ^ 2))
        + ENNReal.ofReal K * ENNReal.ofReal τ + ENNReal.ofReal h * ENNReal.ofReal τ := by
    have h1 : ∀ t, ENNReal.ofReal ((1 / 2) * C * ‖deriv γ t‖ ^ 2)
        = ENNReal.ofReal ((1 / 2) * C) * ENNReal.ofReal (‖deriv γ t‖ ^ 2) :=
      fun t => ENNReal.ofReal_mul (by positivity)
    simp_rw [h1]
    rw [lintegral_add_right' _ aemeasurable_const, lintegral_add_right' _ aemeasurable_const]
    rw [setLIntegral_const, setLIntegral_const, Real.volume_Ioc, sub_zero,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hfin : ENNReal.ofReal ((1 / 2) * C)
        * (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv γ t‖ ^ 2))
      + ENNReal.ofReal K * ENNReal.ofReal τ + ENNReal.ofReal h * ENNReal.ofReal τ < ⊤ := by
    refine ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨?_, ?_⟩, ?_⟩
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hderiv
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  rw [actionOn]
  exact (setLIntegral_mono' measurableSet_Ioc hpt).trans_lt (by rw [hEq]; exact hfin)

/-! ## The decomposed action and lower semicontinuity -/

/-- The *decomposed action*: the integral of the sum of the kinetic energy, the extended pair
potential (which is `⊤` at collisions) and the constant `h`. -/
noncomputable def actionDec (m : Fin N → ℝ) (h : ℝ) (γ : ℝ → EN E N) (τ : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioc 0 τ,
    (ENNReal.ofReal (kinetic m (deriv γ t)) + pairPot m (γ t) + ENNReal.ofReal h)

lemma actionDec_eq {m : Fin N → ℝ} (h : ℝ) (γ : ℝ → EN E N) (τ : ℝ) :
    actionDec m h γ τ
      = (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv γ t)))
        + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γ t)) + ENNReal.ofReal h * ENNReal.ofReal τ := by
  letI : MeasurableSpace (EN E N) := borel (EN E N)
  haveI : BorelSpace (EN E N) := ⟨rfl⟩
  have hkin : Measurable (fun v : EN E N => kinetic m v) := by
    change Measurable (fun v : EN E N => (1 / 2) * ∑ i, m i * ‖v i‖ ^ 2)
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum _ fun i _ => ?_
    refine Measurable.const_mul ?_ _
    exact (((PiLp.continuous_apply 2 (fun _ : Fin N => E) i).norm).pow 2).measurable
  have hA : Measurable (fun t : ℝ => ENNReal.ofReal (kinetic m (deriv γ t))) :=
    ENNReal.measurable_ofReal.comp (hkin.comp (measurable_deriv γ))
  have key : (∫⁻ t in Set.Ioc 0 τ,
        (ENNReal.ofReal (kinetic m (deriv γ t)) + pairPot m (γ t) + ENNReal.ofReal h))
      = (∫⁻ t in Set.Ioc 0 τ,
          (ENNReal.ofReal (kinetic m (deriv γ t)) + (pairPot m (γ t) + ENNReal.ofReal h))) :=
    lintegral_congr fun t => add_assoc _ _ _
  rw [actionDec, key, lintegral_add_left hA, lintegral_add_right' _ aemeasurable_const,
    setLIntegral_const, Real.volume_Ioc, sub_zero, ← add_assoc]

lemma actionDec_le_actionOn {m : Fin N → ℝ} {h : ℝ} (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h)
    (γ : ℝ → EN E N) (τ : ℝ) : actionDec m h γ τ ≤ actionOn m h γ 0 τ := by
  rw [actionDec, actionOn]
  exact setLIntegral_mono' measurableSet_Ioc fun t _ =>
    ofReal_kinetic_add_pairPot_add_h_le_lagrangian hm hh (γ t) (deriv γ t)

omit [FiniteDimensional ℝ E] in
theorem liminf_add_le_atTop (a b : ℕ → ℝ≥0∞) :
    liminf a atTop + liminf b atTop ≤ liminf (fun n => a n + b n) atTop := by
  rw [liminf_eq_iSup_iInf_of_nat, liminf_eq_iSup_iInf_of_nat, liminf_eq_iSup_iInf_of_nat,
    ENNReal.iSup_add]
  simp_rw [ENNReal.add_iSup]
  refine iSup_le fun n => iSup_le fun m => ?_
  refine le_trans (le_iInf fun l => le_iInf fun hl => ?_)
    (le_iSup (fun k => ⨅ l ≥ k, (a l + b l)) (max n m))
  refine add_le_add ?_ ?_
  · exact (iInf_le (fun i => ⨅ _ : n ≤ i, a i) l).trans
      (iInf_le (fun _ : n ≤ l => a l) (le_trans (le_max_left n m) hl))
  · exact (iInf_le (fun j => ⨅ _ : m ≤ j, b j) l).trans
      (iInf_le (fun _ : m ≤ l => b l) (le_trans (le_max_right n m) hl))

/-! ## Lower semicontinuity of the action -/

omit [FiniteDimensional ℝ E] in
lemma kinetic_nonneg (m : Fin N → ℝ) (hm : ∀ i, 0 ≤ m i) (v : EN E N) : 0 ≤ kinetic m v := by
  rw [kinetic]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => mul_nonneg (hm i) (sq_nonneg _))

/-- For positive masses, a configuration with finite extended pair potential is collision-free. -/
lemma withoutCollisions_of_pairPot_lt_top {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {x : EN E N}
    (h : pairPot m x < ⊤) : WithoutCollisions x := by
  by_contra hnc
  simp only [WithoutCollisions, r] at hnc
  push_neg at hnc
  obtain ⟨i, j, hij, hd⟩ := hnc
  have hfi : ∀ a b : Fin N, dist (x a) (x b) = 0 →
      ENNReal.ofReal (m a * m b) * (ENNReal.ofReal (dist (x a) (x b)))⁻¹ = ⊤ := by
    intro a b hab
    have hpos : (0 : ℝ) < m a * m b := mul_pos (hm a) (hm b)
    rw [hab, ENNReal.ofReal_zero, ENNReal.inv_zero,
      ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hpos)]
  have hterm : ∀ a b : Fin N, a < b →
      ENNReal.ofReal (m a * m b) * (ENNReal.ofReal (dist (x a) (x b)))⁻¹ ≤ pairPot m x := by
    intro a b hab
    refine le_trans (Finset.single_le_sum (s := Finset.Iio b)
      (f := fun i => ENNReal.ofReal (m i * m b) * (ENNReal.ofReal (dist (x i) (x b)))⁻¹)
      (fun i _ => bot_le) (Finset.mem_Iio.mpr hab)) ?_
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun j => ∑ i ∈ Finset.Iio j,
        ENNReal.ofReal (m i * m j) * (ENNReal.ofReal (dist (x i) (x j)))⁻¹)
      (fun j _ => bot_le) (Finset.mem_univ b)
  have htop : pairPot m x = ⊤ := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact le_antisymm le_top (hfi i j hd ▸ hterm i j hlt)
    · rw [dist_comm] at hd
      exact le_antisymm le_top (hfi j i hd ▸ hterm j i hgt)
  rw [htop] at h
  exact lt_irrefl _ h

/-- If the configuration is a.e. collision-free on `(0,τ]`, the action and the decomposed action
coincide. -/
lemma actionOn_eq_actionDec_of_ae {m : Fin N → ℝ} {h : ℝ} (hh : 0 ≤ h) {γ : ℝ → EN E N} {τ : ℝ}
    (hm : ∀ i, 0 ≤ m i)
    (hae : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 τ)), WithoutCollisions (γ t)) :
    actionOn m h γ 0 τ = actionDec m h γ τ := by
  refine le_antisymm ?_ (actionDec_le_actionOn hm hh γ τ)
  rw [actionOn, actionDec]
  refine lintegral_mono_ae ?_
  filter_upwards [hae] with t ht
  have hA : (0 : ℝ) ≤ (1 / 2) * ∑ i, m i * ‖deriv γ t i‖ ^ 2 :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => mul_nonneg (hm i) (sq_nonneg _))
  have hU : (0 : ℝ) ≤ U m (γ t) := U_nonneg hm (γ t)
  rw [lagrangian, if_pos ht, pairPot_eq_ofReal_U hm ht, kinetic]
  rw [← ENNReal.ofReal_add hA hU, ← ENNReal.ofReal_add (add_nonneg hA hU) hh]

/-- **Lower semicontinuity of the action.**  Given a limit curve `γ` and a sequence of curves `γs n`
whose kinetic energies and extended potentials satisfy the lower semicontinuity inequalities below,
the action of `γ` is at most the `liminf` of the actions. -/
theorem actionOn_le_liminf {m : Fin N → ℝ} {h : ℝ} (hm : ∀ i, 0 < m i) (hh : 0 ≤ h)
    {τ : ℝ} {γs : ℕ → ℝ → EN E N} {γ : ℝ → EN E N}
    (hmeas : AEMeasurable (fun t => pairPot m (γ t)) (volume.restrict (Set.Ioc 0 τ)))
    (hkin : (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv γ t)))
        ≤ liminf (fun n => ∫⁻ t in Set.Ioc 0 τ,
            ENNReal.ofReal (kinetic m (deriv (γs n) t))) atTop)
    (hpot : (∫⁻ t in Set.Ioc 0 τ, pairPot m (γ t))
        ≤ liminf (fun n => ∫⁻ t in Set.Ioc 0 τ, pairPot m (γs n t)) atTop) :
    actionOn m h γ 0 τ ≤ liminf (fun n => actionOn m h (γs n) 0 τ) atTop := by
  set c : ℝ≥0∞ := ENNReal.ofReal h * ENNReal.ofReal τ with hcdef
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hsum : (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv γ t)))
        + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γ t)) + c
      ≤ liminf (fun n => (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv (γs n) t)))
        + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γs n t)) + c) atTop := by
    have h1 : (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv γ t)))
        + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γ t))
        ≤ liminf (fun n => (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv (γs n) t)))
          + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γs n t))) atTop :=
      (add_le_add hkin hpot).trans (liminf_add_le_atTop _ _)
    calc (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv γ t)))
          + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γ t)) + c
        ≤ liminf (fun n => (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv (γs n) t)))
            + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γs n t))) atTop + c := add_le_add h1 le_rfl
      _ = liminf (fun n => (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv (γs n) t)))
            + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γs n t))) atTop
            + liminf (fun _ : ℕ => c) atTop := by rw [liminf_const]
      _ ≤ liminf (fun n => (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv (γs n) t)))
            + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γs n t)) + c) atTop := liminf_add_le_atTop _ _
  have hdecγ : actionDec m h γ τ = (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv γ t)))
        + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γ t)) + c := actionDec_eq h γ τ
  have hdecN : ∀ n, actionDec m h (γs n) τ =
      (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv (γs n) t)))
        + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γs n t)) + c := fun n => actionDec_eq h (γs n) τ
  have hdec : actionDec m h γ τ ≤ liminf (fun n => actionDec m h (γs n) τ) atTop := by
    rw [hdecγ]
    simp only [hdecN]
    exact hsum
  have hdecN_le : liminf (fun n => actionDec m h (γs n) τ) atTop
      ≤ liminf (fun n => actionOn m h (γs n) 0 τ) atTop :=
    liminf_le_liminf (Eventually.of_forall fun n => actionDec_le_actionOn hm0 hh (γs n) τ)
  have hmain : actionDec m h γ τ ≤ liminf (fun n => actionOn m h (γs n) 0 τ) atTop :=
    hdec.trans hdecN_le
  rcases eq_or_lt_of_le (le_top : actionDec m h γ τ ≤ ⊤) with htop | hlt
  · have hlinf : liminf (fun n => actionOn m h (γs n) 0 τ) atTop = ⊤ :=
      le_antisymm le_top (htop ▸ hmain)
    rw [hlinf]
    exact le_top
  · have hP : (∫⁻ t in Set.Ioc 0 τ, pairPot m (γ t)) < ⊤ := by
      rw [hdecγ] at hlt
      refine lt_of_le_of_lt ?_ hlt
      calc (∫⁻ t in Set.Ioc 0 τ, pairPot m (γ t))
          ≤ (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv γ t)))
            + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γ t)) := le_add_left (le_refl _)
        _ ≤ (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv γ t)))
            + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γ t)) + c := le_add_right (le_refl _)
    have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 τ)), WithoutCollisions (γ t) := by
      filter_upwards [ae_lt_top' hmeas (ne_of_lt hP)] with t ht
      exact withoutCollisions_of_pairPot_lt_top hm ht
    rw [actionOn_eq_actionDec_of_ae hh hm0 hae]
    exact hmain

/-! ## Finiteness of the action potential -/

/-- The action potential of two configurations joined by a collision-free path with finite `L²`
derivative is finite. -/
theorem actionPot_lt_top_of_path {m : Fin N → ℝ} {h : ℝ} (hm : ∀ i, 0 < m i) (hh : 0 < h)
    {x y : EN E N} {τ : ℝ} (hτ : 0 < τ) {γ : ℝ → EN E N}
    (h0 : γ 0 = x) (h1 : γ τ = y)
    (hac : AbsolutelyContinuousOnInterval γ 0 τ)
    (hnc : ∀ t ∈ Set.Icc 0 τ, WithoutCollisions (γ t))
    (hderiv : (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv γ t‖ ^ 2)) < ⊤) :
    actionPot m h x y < ⊤ := by
  refine lt_of_le_of_lt (actionPot_le_of hτ h0 h1 hac) (actionOn_lt_top_of_path hm hh.le hnc ?_ hderiv)
  simpa only [uIcc_of_le hτ.le] using hac.continuousOn

/-! ## Equicontinuity and Arzelà--Ascoli -/

/-- The Euclidean `L²` energy of the derivative is controlled by the mass-weighted one. -/
lemma euclidean_energy_le_of_kinetic {m : Fin N → ℝ} {c : ℝ} (hc : 0 < c) (hm : ∀ i, c ≤ m i)
    {M : ℝ} {γ : ℝ → EN E N} {τ : ℝ}
    (h : (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv γ t)))
      ≤ ENNReal.ofReal (M ^ 2)) :
    (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv γ t‖ ^ 2))
      ≤ ENNReal.ofReal (M ^ 2 / ((1 / 2) * c)) := by
  have hc' : (0 : ℝ) < (1 / 2) * c := by linarith
  have hcle : ∀ v : EN E N, c * ‖v‖ ^ 2 ≤ ∑ i, m i * ‖v i‖ ^ 2 := by
    intro v
    calc c * ‖v‖ ^ 2 = c * ∑ i, ‖v i‖ ^ 2 := by rw [PiLp.norm_sq_eq_of_L2]
      _ ≤ ∑ i, m i * ‖v i‖ ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hm i) (sq_nonneg _)
  have hpoint : ∀ t : ℝ, ENNReal.ofReal ((1 / 2) * c * ‖deriv γ t‖ ^ 2)
      ≤ ENNReal.ofReal (kinetic m (deriv γ t)) := by
    intro t
    refine ENNReal.ofReal_le_ofReal ?_
    rw [kinetic, show (1 / 2) * c * ‖deriv γ t‖ ^ 2 = (1 / 2) * (c * ‖deriv γ t‖ ^ 2) by ring]
    exact mul_le_mul_of_nonneg_left (hcle (deriv γ t)) (by norm_num)
  have h1 : (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal ((1 / 2) * c * ‖deriv γ t‖ ^ 2))
      ≤ ENNReal.ofReal (M ^ 2) := (setLIntegral_mono' measurableSet_Ioc fun t _ => hpoint t).trans h
  have h2 : (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal ((1 / 2) * c * ‖deriv γ t‖ ^ 2))
      = ENNReal.ofReal ((1 / 2) * c)
        * (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv γ t‖ ^ 2)) := by
    simp_rw [ENNReal.ofReal_mul hc'.le]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h1' : ENNReal.ofReal ((1 / 2) * c)
        * (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv γ t‖ ^ 2)) ≤ ENNReal.ofReal (M ^ 2) :=
    h2 ▸ h1
  have hne : ENNReal.ofReal ((1 / 2) * c) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hc'
  have h4 : (ENNReal.ofReal ((1 / 2) * c))⁻¹ * (ENNReal.ofReal ((1 / 2) * c)
      * (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv γ t‖ ^ 2)))
      = ∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv γ t‖ ^ 2) := by
    rw [← mul_assoc, ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top, one_mul]
  calc (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv γ t‖ ^ 2))
      ≤ (ENNReal.ofReal ((1 / 2) * c))⁻¹ * (ENNReal.ofReal ((1 / 2) * c)
          * (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv γ t‖ ^ 2))) := by rw [h4]
    _ ≤ (ENNReal.ofReal ((1 / 2) * c))⁻¹ * ENNReal.ofReal (M ^ 2) :=
        mul_le_mul' le_rfl h1'
    _ = ENNReal.ofReal (M ^ 2) * (ENNReal.ofReal ((1 / 2) * c))⁻¹ := mul_comm _ _
    _ = ENNReal.ofReal (M ^ 2 / ((1 / 2) * c)) := by
        rw [ENNReal.ofReal_div_of_pos hc', ENNReal.div_eq_inv_mul, mul_comm]

/-- **Arzelà--Ascoli extraction.**  A sequence of curves with a uniform `L²` bound on the derivative
has a uniformly convergent subsequence. -/
theorem exists_uniform_subseq {M : ℝ} (hM : 0 ≤ M) {τ : ℝ} (hτ : 0 ≤ τ)
    {γs : ℕ → ℝ → EN E N}
    (hcont : ∀ n, ContinuousOn (γs n) (Set.Icc 0 τ))
    (hac : ∀ n, AbsolutelyContinuousOnInterval (γs n) 0 τ)
    (hbd : ∀ n, (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv (γs n) t‖ ^ 2))
      ≤ ENNReal.ofReal (M ^ 2))
    (hx : ∃ x₀ : EN E N, ∀ n, γs n 0 = x₀) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ γ : ℝ → EN E N, ContinuousOn γ (Set.Icc 0 τ) ∧
      TendstoUniformlyOn (fun k => γs (φ k)) γ atTop (Set.Icc 0 τ) := by
  have hholder : ∀ n (s : ℝ), s ∈ Set.Icc 0 τ → ∀ t ∈ Set.Icc 0 τ,
      dist (γs n s) (γs n t) ≤ M * Real.sqrt |s - t| := fun n s hs t ht => by
    simpa only [dist_eq_norm] using
      Commons.MeasureTheory.Integral.norm_sub_le_sqrt_mul_sqrt_of_absolutelyContinuousOnInterval
        hτ hM (hac n) hs ht (hbd n)
  exact Commons.Topology.Metric.exists_tendstoUniformlyOn_subseq_of_holder_of_properSpace
    hτ hM hcont hholder hx

/-! ## Reparametrisation of the action -/

/-- The kinetic energy is quadratic. -/
lemma kinetic_smul (m : Fin N → ℝ) (κ : ℝ) (v : EN E N) :
    kinetic m (κ • v) = κ ^ 2 * kinetic m v := by
  have h : ∀ i : Fin N, m i * ‖(κ • v) i‖ ^ 2 = κ ^ 2 * (m i * ‖v i‖ ^ 2) := by
    intro i
    rw [PiLp.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  simp only [kinetic, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]; ring

lemma deriv_comp_mul_left' (γ : ℝ → EN E N) (κ t : ℝ) :
    deriv (fun s => γ (κ * s)) t = κ • deriv γ (κ * t) :=
  deriv_comp_mul_left κ γ t

/-- Change of variables for the kinetic energy integral under the reparametrisation
`t ↦ γ (κ * t)`. -/
lemma lintegral_kinetic_comp_mul_left {m : Fin N → ℝ} {γ : ℝ → EN E N} {κ τ : ℝ} (hκ : 0 < κ) :
    (∫⁻ t in Set.Ioc 0 (τ / κ), ENNReal.ofReal (kinetic m (deriv (fun s => γ (κ * s)) t)))
      = ENNReal.ofReal κ * (∫⁻ s in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv γ s))) := by
  have hκ0 : κ ≠ 0 := hκ.ne'
  have h1 : ∀ t : ℝ, ENNReal.ofReal (kinetic m (deriv (fun s => γ (κ * s)) t))
      = ENNReal.ofReal (κ ^ 2) * ENNReal.ofReal (kinetic m (deriv γ (κ * t))) := by
    intro t
    rw [deriv_comp_mul_left', kinetic_smul, ENNReal.ofReal_mul (by positivity)]
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [Commons.MeasureTheory.Integral.setLIntegral_Ioc_comp_mul_left
    (fun s => ENNReal.ofReal (kinetic m (deriv γ s))) hκ]
  rw [mul_zero, mul_div_cancel₀ τ hκ0]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg κ),
    show κ ^ 2 * κ⁻¹ = κ from by rw [sq, mul_assoc, mul_inv_cancel₀ hκ0, mul_one]]

/-- Change of variables for the extended potential integral under the reparametrisation
`t ↦ γ (κ * t)`. -/
lemma lintegral_pairPot_comp_mul_left {m : Fin N → ℝ} {γ : ℝ → EN E N} {κ τ : ℝ} (hκ : 0 < κ) :
    (∫⁻ t in Set.Ioc 0 (τ / κ), pairPot m (γ (κ * t)))
      = ENNReal.ofReal κ⁻¹ * (∫⁻ s in Set.Ioc 0 τ, pairPot m (γ s)) := by
  have h := Commons.MeasureTheory.Integral.setLIntegral_Ioc_comp_mul_left
    (fun s => pairPot m (γ s)) (a := κ) (b := 0) (c := τ / κ) hκ
  rw [mul_zero, mul_div_cancel₀ τ hκ.ne'] at h
  exact h

/-- The decomposed action of a linearly reparametrised curve. -/
lemma actionDec_comp_mul_left {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {κ τ : ℝ}
    (hκ : 0 < κ) :
    actionDec m h (fun s => γ (κ * s)) (τ / κ)
      = ENNReal.ofReal κ * (∫⁻ s in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv γ s)))
        + ENNReal.ofReal κ⁻¹ * (∫⁻ s in Set.Ioc 0 τ, pairPot m (γ s))
        + ENNReal.ofReal h * ENNReal.ofReal (τ / κ) := by
  rw [actionDec_eq h (fun s => γ (κ * s)) (τ / κ), lintegral_kinetic_comp_mul_left hκ,
    lintegral_pairPot_comp_mul_left hκ]

/-- Measurability of the extended potential along a continuous curve. -/
lemma aemeasurable_pairPot_comp {m : Fin N → ℝ} {γ : ℝ → EN E N} {s : Set ℝ}
    (hγ : ContinuousOn γ s) (hs : MeasurableSet s) :
    AEMeasurable (fun t => pairPot m (γ t)) (volume.restrict s) := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace (EN E N) := borel (EN E N)
  haveI : BorelSpace (EN E N) := ⟨rfl⟩
  have hpair : Measurable (fun x : EN E N => pairPot m x) := by
    have hterm : ∀ i j : Fin N, Measurable (fun x : EN E N =>
        ENNReal.ofReal (m i * m j) * (ENNReal.ofReal (dist (x i) (x j)))⁻¹) := by
      intro i j
      refine Measurable.mul measurable_const ?_
      refine Measurable.inv ?_
      refine ENNReal.measurable_ofReal.comp ?_
      exact ((PiLp.continuous_apply 2 (fun _ : Fin N => E) i).dist
        (PiLp.continuous_apply 2 (fun _ : Fin N => E) j)).measurable
    have : (fun x : EN E N => pairPot m x) = fun x =>
        ∑ j, ∑ i < j, ENNReal.ofReal (m i * m j) * (ENNReal.ofReal (dist (x i) (x j)))⁻¹ := rfl
    rw [this]
    exact Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun i _ => hterm i j
  exact hpair.comp_aemeasurable (hγ.aemeasurable hs)

/-- **Lower semicontinuity of the decomposed action.** -/
theorem actionDec_le_liminf {m : Fin N → ℝ} {h : ℝ} {τ : ℝ} {γs : ℕ → ℝ → EN E N}
    {γ : ℝ → EN E N}
    (hkin : (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv γ t)))
        ≤ liminf (fun n => ∫⁻ t in Set.Ioc 0 τ,
            ENNReal.ofReal (kinetic m (deriv (γs n) t))) atTop)
    (hpot : (∫⁻ t in Set.Ioc 0 τ, pairPot m (γ t))
        ≤ liminf (fun n => ∫⁻ t in Set.Ioc 0 τ, pairPot m (γs n t)) atTop) :
    actionDec m h γ τ ≤ liminf (fun n => actionDec m h (γs n) τ) atTop := by
  set c : ℝ≥0∞ := ENNReal.ofReal h * ENNReal.ofReal τ with hcdef
  have hsum : (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv γ t)))
        + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γ t)) + c
      ≤ liminf (fun n => (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv (γs n) t)))
        + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γs n t)) + c) atTop := by
    have h1 : (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv γ t)))
        + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γ t))
        ≤ liminf (fun n => (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv (γs n) t)))
          + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γs n t))) atTop :=
      (add_le_add hkin hpot).trans (liminf_add_le_atTop _ _)
    calc (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv γ t)))
          + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γ t)) + c
        ≤ liminf (fun n => (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv (γs n) t)))
            + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γs n t))) atTop + c := add_le_add h1 le_rfl
      _ = liminf (fun n => (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv (γs n) t)))
            + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γs n t))) atTop
            + liminf (fun _ : ℕ => c) atTop := by rw [liminf_const]
      _ ≤ liminf (fun n => (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv (γs n) t)))
            + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γs n t)) + c) atTop := liminf_add_le_atTop _ _
  have hdecγ : actionDec m h γ τ = (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv γ t)))
        + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γ t)) + c := actionDec_eq h γ τ
  have hdecN : ∀ n, actionDec m h (γs n) τ =
      (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (kinetic m (deriv (γs n) t)))
        + (∫⁻ t in Set.Ioc 0 τ, pairPot m (γs n t)) + c := fun n => actionDec_eq h (γs n) τ
  rw [hdecγ]
  simp only [hdecN]
  exact hsum

/-! ## The minimising sequence -/

lemma exists_minimizing_sequence {m : Fin N → ℝ} {h : ℝ} {x y : EN E N}
    (hfin : actionPot m h x y < ⊤) :
    ∃ τ : ℕ → ℝ, ∃ γ : ℕ → ℝ → EN E N,
      (∀ n, 0 < τ n) ∧ (∀ n, γ n 0 = x) ∧ (∀ n, γ n (τ n) = y) ∧
      (∀ n, AbsolutelyContinuousOnInterval (γ n) 0 (τ n)) ∧
      (∀ n, actionOn m h (γ n) 0 (τ n)
        < actionPot m h x y + ENNReal.ofReal (1 / (n + 1 : ℝ))) := by
  have hlt : ∀ n : ℕ,
      actionPot m h x y < actionPot m h x y + ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
    intro n
    exact ENNReal.lt_add_right (ne_of_lt hfin)
      (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
  choose P hP using fun n => iInf_lt_iff.mp (hlt n)
  exact ⟨fun n => (P n).1.1, fun n => (P n).1.2, fun n => (P n).2.1,
    fun n => (P n).2.2.1, fun n => (P n).2.2.2.1, fun n => (P n).2.2.2.2, fun n => hP n⟩

/-- If the action is finite (and the curve is continuous on the half-open interval), then the
action and the decomposed action coincide. -/
lemma actionOn_eq_actionDec_of_lt_top {m : Fin N → ℝ} {h : ℝ} (hm : ∀ i, 0 < m i) (hh : 0 ≤ h)
    {γ : ℝ → EN E N} {τ : ℝ} (hcont : ContinuousOn γ (Set.Ioc 0 τ))
    (hact : actionOn m h γ 0 τ < ⊤) : actionOn m h γ 0 τ = actionDec m h γ τ := by
  have hPle : (∫⁻ t in Set.Ioc 0 τ, pairPot m (γ t)) ≤ actionDec m h γ τ := by
    rw [actionDec_eq h γ τ]
    exact (le_add_left (le_refl _)).trans (le_add_right (le_refl _))
  have hP : (∫⁻ t in Set.Ioc 0 τ, pairPot m (γ t)) < ⊤ :=
    lt_of_le_of_lt hPle (lt_of_le_of_lt (actionDec_le_actionOn (fun i => (hm i).le) hh γ τ) hact)
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 τ)), WithoutCollisions (γ t) := by
    filter_upwards [ae_lt_top' (aemeasurable_pairPot_comp hcont measurableSet_Ioc)
      (ne_of_lt hP)] with t ht
    exact withoutCollisions_of_pairPot_lt_top hm ht
  exact actionOn_eq_actionDec_of_ae hh (fun i => (hm i).le) hae

/-- The τ-bounds for a minimising sequence with action bounded by `ofReal K`. -/
lemma tau_bounds {m : Fin N → ℝ} {h : ℝ} {x y : EN E N} {c K : ℝ} (hc : 0 < c)
    (hmc : ∀ i, c ≤ m i) (hh : 0 < h) (hK : 0 < K)
    {τ : ℕ → ℝ} {γ : ℕ → ℝ → EN E N}
    (hτ0 : ∀ n, 0 < τ n) (h0 : ∀ n, γ n 0 = x) (h1 : ∀ n, γ n (τ n) = y)
    (hac : ∀ n, AbsolutelyContinuousOnInterval (γ n) 0 (τ n))
    (hbound : ∀ n, actionOn m h (γ n) 0 (τ n) ≤ ENNReal.ofReal K) :
    (∀ n, (1 / 2) * c * ‖x - y‖ ^ 2 / K ≤ τ n) ∧ (∀ n, τ n ≤ K / h) := by
  have hstep : ∀ n, (1 / 2) * c * ‖x - y‖ ^ 2 / τ n + h * τ n ≤ K := by
    intro n
    have h1' := ofReal_chord_sq_div_add_le_actionOn hc hmc hh.le (hτ0 n) (h0 n) (h1 n) (hac n)
    have h2 : ENNReal.ofReal ((1 / 2) * c * ‖x - y‖ ^ 2 / τ n + h * τ n) ≤ ENNReal.ofReal K :=
      h1'.trans (hbound n)
    exact (ENNReal.ofReal_le_ofReal_iff hK.le).mp h2
  constructor
  · intro n
    have hn := hstep n
    have hle : (1 / 2) * c * ‖x - y‖ ^ 2 / τ n ≤ K := by
      have h2 : 0 ≤ h * τ n := (mul_pos hh (hτ0 n)).le
      linarith
    have h2 := mul_le_mul_of_nonneg_left hle (hτ0 n).le
    rw [mul_comm (τ n) ((1 / 2) * c * ‖x - y‖ ^ 2 / τ n), div_mul_cancel₀ _ (hτ0 n).ne'] at h2
    rw [div_le_iff₀ hK]
    exact h2
  · intro n
    have hn := hstep n
    have hle : h * τ n ≤ K := by
      have h2 : 0 ≤ (1 / 2) * c * ‖x - y‖ ^ 2 / τ n :=
        div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc.le) (sq_nonneg _)) (hτ0 n).le
      linarith
    rw [mul_comm h (τ n)] at hle
    rw [le_div_iff₀ hh]
    exact hle

/-- Constant extension of an absolutely continuous curve past a time. -/
lemma absolutelyContinuousOnInterval_comp_min {γ : ℝ → EN E N} {a b τ : ℝ} (ha : a ≤ τ)
    (hτb : τ ≤ b) (h : AbsolutelyContinuousOnInterval γ a τ) :
    AbsolutelyContinuousOnInterval (fun t => γ (min t τ)) a b := by
  have heq : (fun t : ℝ => γ (min t τ)) = fun x : ℝ => if x ≤ τ then γ x else γ τ := by
    funext t
    by_cases ht : t ≤ τ
    · rw [if_pos ht, min_eq_left ht]
    · rw [if_neg ht, min_eq_right (le_of_lt (lt_of_not_ge ht))]
  rw [heq]
  exact Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_concat ha hτb rfl h
    ((LipschitzWith.const (γ τ)).lipschitzOnWith.absolutelyContinuousOnInterval)


/-- The action of the constant extension of `γ` past `τ`, up to a time `T ≥ τ`. -/
lemma actionOn_comp_min_eq {m : Fin N → ℝ} {h : ℝ} {y : EN E N} {γ : ℝ → EN E N} {τ T : ℝ}
    (hτ : 0 < τ) (hτT : τ ≤ T) (hy : WithoutCollisions y) (hγτ : γ τ = y) :
    actionOn m h (fun t => γ (min t τ)) 0 T
      = actionOn m h γ 0 τ + ENNReal.ofReal (U m y + h) * ENNReal.ofReal (T - τ) := by
  set γe : ℝ → EN E N := fun t => γ (min t τ) with hγedef
  have hsplit : actionOn m h γe 0 T = actionOn m h γe 0 τ + actionOn m h γe τ T := by
    unfold actionOn
    rw [← Set.Ioc_union_Ioc_eq_Ioc hτ.le hτT]
    rw [lintegral_union measurableSet_Ioc]
    exact Set.disjoint_left.mpr fun t ht ht' => absurd ht.2 (not_le_of_gt ht'.1)
  have hleft : actionOn m h γe 0 τ = actionOn m h γ 0 τ := by
    unfold actionOn
    refine setLIntegral_congr_fun_ae measurableSet_Ioc ?_
    filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp (measure_singleton τ)]
      with t ht hmem
    have hlt : t < τ := lt_of_le_of_ne hmem.2 ht
    have h1 : γe t = γ t := by
      show γ (min t τ) = γ t
      rw [min_eq_left hlt.le]
    have h2 : deriv γe t = deriv γ t := by
      show deriv (fun s : ℝ => γ (min s τ)) t = deriv γ t
      exact Commons.Analysis.Calculus.deriv_comp_min_of_lt γ hlt
    rw [h1, h2]
  have hright : actionOn m h γe τ T = ENNReal.ofReal (U m y + h) * ENNReal.ofReal (T - τ) := by
    unfold actionOn
    have hpt : ∀ t ∈ Set.Ioc τ T,
        lagrangian m h (γe t) (deriv γe t) = ENNReal.ofReal (U m y + h) := by
      intro t ht
      have hγt : γe t = y := by
        show γ (min t τ) = y
        rw [min_eq_right ht.1.le, hγτ]
      have hdt : deriv γe t = 0 := by
        show deriv (fun s : ℝ => γ (min s τ)) t = 0
        exact Commons.Analysis.Calculus.deriv_comp_min_of_gt γ ht.1
      rw [hγt, hdt, lagrangian, if_pos hy]
      simp
    rw [setLIntegral_congr_fun measurableSet_Ioc hpt, setLIntegral_const, Real.volume_Ioc]
  rw [hsplit, hleft, hright]

/-- The action of `γ ∘ min(·,τ)` up to time `τ` equals the action of `γ` up to time `τ`. -/
lemma actionOn_comp_min_self {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {τ : ℝ} :
    actionOn m h (fun t => γ (min t τ)) 0 τ = actionOn m h γ 0 τ := by
  unfold actionOn
  refine setLIntegral_congr_fun_ae measurableSet_Ioc ?_
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp (measure_singleton τ)]
    with t ht hmem
  have hlt : t < τ := lt_of_le_of_ne hmem.2 ht
  rw [congrArg γ (min_eq_left hlt.le), Commons.Analysis.Calculus.deriv_comp_min_of_lt γ hlt]


/-- `kinetic` written with the `WithLp` projection. -/
lemma ofReal_kinetic_ofLp (m : Fin N → ℝ) (v : EN E N) :
    ENNReal.ofReal (kinetic m v)
      = ENNReal.ofReal ((1 / 2) * ∑ i, m i * ‖v.ofLp i‖ ^ 2) := by
  rw [kinetic]

/-- The kinetic energy integral written with the `WithLp` projection. -/
lemma lintegral_ofReal_kinetic_eq (m : Fin N → ℝ) (F : ℝ → EN E N) (a b : ℝ) :
    (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (kinetic m (F t)))
      = ∫⁻ t in Set.Ioc a b,
          ENNReal.ofReal ((1 / 2) * ∑ i, m i * ‖(F t).ofLp i‖ ^ 2) :=
  lintegral_congr fun t => ofReal_kinetic_ofLp m (F t)


theorem exists_minimizer {m : Fin N → ℝ} {h : ℝ} {x y : EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hxy : x ≠ y) (hy : WithoutCollisions y)
    (hfin : actionPot m h x y < ⊤) :
    ∃ τ > 0, ∃ γ : ℝ → EN E N, γ 0 = x ∧ γ τ = y ∧
      AbsolutelyContinuousOnInterval γ 0 τ ∧ actionOn m h γ 0 τ = actionPot m h x y := by
  classical
  obtain ⟨τ, γ, hτ0, hγ0, hγ1, hγac, hγlt⟩ :=
    exists_minimizing_sequence (m := m) (h := h) (x := x) (y := y) hfin
  -- a positive lower bound for the masses
  obtain ⟨c, hc, hmc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ m i := by
    rcases isEmpty_or_nonempty (Fin N) with hN | hN
    · exfalso
      haveI := hN
      exact hxy (Subsingleton.elim x y)
    · refine ⟨Finset.univ.inf' Finset.univ_nonempty m, ?_, fun i => ?_⟩
      · rw [Finset.lt_inf'_iff]; intro i _; exact hm i
      · exact Finset.inf'_le _ (Finset.mem_univ i)
  set A : ℝ≥0∞ := actionPot m h x y with hAdef
  have hAne : A ≠ ⊤ := by rw [hAdef]; exact ne_of_lt hfin
  set K : ℝ := A.toReal + 1 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hAleK : A ≤ ENNReal.ofReal K := by
    rw [hKdef]
    calc A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hAne).symm
      _ ≤ ENNReal.ofReal (A.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
  set T : ℝ := K / h with hTdef
  have hTpos : 0 < T := by rw [hTdef]; positivity
  have hnormpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  set δ : ℝ := (1 / 2) * c * ‖x - y‖ ^ 2 / K with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact div_pos (mul_pos (mul_pos (by norm_num) hc) (pow_pos hnormpos 2)) hKpos
  have hactionK : ∀ n, actionOn m h (γ n) 0 (τ n) ≤ ENNReal.ofReal K := by
    intro n
    have h1 : A + ENNReal.ofReal (1 / (n + 1 : ℝ)) ≤ ENNReal.ofReal K := by
      rw [hKdef]
      calc A + ENNReal.ofReal (1 / (n + 1 : ℝ))
          ≤ ENNReal.ofReal A.toReal + ENNReal.ofReal 1 :=
            add_le_add (by rw [ENNReal.ofReal_toReal hAne])
              (ENNReal.ofReal_le_ofReal (by
                rw [div_le_one (by positivity)]
                linarith [Nat.cast_nonneg (α := ℝ) n]))
        _ = ENNReal.ofReal (A.toReal + 1) :=
            (ENNReal.ofReal_add (by positivity) zero_le_one).symm
    rw [hAdef] at h1
    exact (hγlt n).le.trans h1
  obtain ⟨hδle, hτleT⟩ := tau_bounds hc hmc hh hKpos hτ0 hγ0 hγ1 hγac hactionK
  have hδle' : ∀ n, δ ≤ τ n := fun n => by rw [hδdef]; exact hδle n
  have hτleT' : ∀ n, τ n ≤ T := fun n => by rw [hTdef]; exact hτleT n
  -- extract a subsequence with `τ → τ₀`
  obtain ⟨τ₀, hτ₀mem, φ₁, hφ₁mono, hφ₁lim⟩ := IsCompact.tendsto_subseq isCompact_Icc
    (fun n => Set.mem_Icc.mpr ⟨hδle' n, hτleT' n⟩)
  have hτ₀pos : 0 < τ₀ := (hδpos.trans_le hτ₀mem.1)
  have hτ₀T : τ₀ ≤ T := hτ₀mem.2
  have hτφlim : Tendsto (fun n => τ (φ₁ n)) atTop (𝓝 τ₀) := hφ₁lim
  -- the extended curves (constant past `τ n`)
  set γe : ℕ → ℝ → EN E N := fun n t => γ n (min t (τ n)) with hγedef
  have hγe0 : ∀ n, γe n 0 = x := by
    intro n
    show γ n (min 0 (τ n)) = x
    rw [min_eq_left (le_of_lt (hτ0 n)), hγ0 n]
  have hγeT : ∀ n, γe n T = y := by
    intro n
    show γ n (min T (τ n)) = y
    rw [min_eq_right (hτleT' n), hγ1 n]
  have hγeac : ∀ n, AbsolutelyContinuousOnInterval (γe n) 0 T := by
    intro n
    show AbsolutelyContinuousOnInterval (fun t => γ n (min t (τ n))) 0 T
    exact absolutelyContinuousOnInterval_comp_min (le_of_lt (hτ0 n)) (hτleT' n) (hγac n)
  have hγecontIcc : ∀ n, ContinuousOn (γe n) (Set.Icc 0 T) := by
    intro n
    have h := (hγeac n).continuousOn
    rwa [uIcc_of_le hTpos.le] at h
  have hγecont : ∀ n, ContinuousOn (γe n) (Set.Ioc 0 T) :=
    fun n => (hγecontIcc n).mono Set.Ioc_subset_Icc_self
  -- uniform bound for the kinetic energy of the extended curves
  have hγekin : ∀ n, (∫⁻ t in Set.Ioc 0 T,
        ENNReal.ofReal ((1 / 2) * ∑ i, m i * ‖(deriv (γe n) t).ofLp i‖ ^ 2))
      ≤ ENNReal.ofReal ((Real.sqrt K) ^ 2) := by
    intro n
    rw [Real.sq_sqrt hKpos.le, ← lintegral_ofReal_kinetic_eq]
    have hsplit : (∫⁻ t in Set.Ioc 0 T, ENNReal.ofReal (kinetic m (deriv (γe n) t)))
        = (∫⁻ t in Set.Ioc 0 (τ n), ENNReal.ofReal (kinetic m (deriv (γ n) t))) := by
      show (∫⁻ t in Set.Ioc 0 T,
          ENNReal.ofReal (kinetic m (deriv (fun s => γ n (min s (τ n))) t))) = _
      rw [← Set.Ioc_union_Ioc_eq_Ioc (le_of_lt (hτ0 n)) (hτleT' n)]
      rw [lintegral_union measurableSet_Ioc]
      · have hzero : (∫⁻ t in Set.Ioc (τ n) T,
            ENNReal.ofReal (kinetic m (deriv (fun s : ℝ => γ n (min s (τ n))) t))) = 0 := by
          have hpt : ∀ t ∈ Set.Ioc (τ n) T,
              ENNReal.ofReal (kinetic m (deriv (fun s : ℝ => γ n (min s (τ n))) t)) = 0 := by
            intro t ht
            rw [Commons.Analysis.Calculus.deriv_comp_min_of_gt (γ n) ht.1]
            simp [kinetic]
          rw [setLIntegral_congr_fun measurableSet_Ioc hpt]
          simp
        rw [hzero, add_zero]
        refine setLIntegral_congr_fun_ae measurableSet_Ioc ?_
        filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
          (measure_singleton (τ n))] with t ht hmem
        have hlt : t < τ n := lt_of_le_of_ne hmem.2 ht
        rw [Commons.Analysis.Calculus.deriv_comp_min_of_lt (γ n) hlt]
      · exact Set.disjoint_left.mpr fun t ht ht' => absurd ht.2 (not_le_of_gt ht'.1)
    rw [hsplit]
    refine (le_trans ?_ (actionDec_le_actionOn (fun i => (hm i).le) hh.le (γ n) (τ n))).trans
      (hactionK n)
    rw [actionDec_eq]
    exact le_add_right (le_add_right le_rfl)
  -- the extraction of the uniformly convergent subsequence
  obtain ⟨φ₂, hφ₂mono, γlim, hγlimcont, hconvunif⟩ :=
    exists_uniform_subseq (M := Real.sqrt (K / ((1 / 2) * c)))
      (Real.sqrt_nonneg _) hTpos.le (fun n => hγecontIcc (φ₁ n))
      (fun n => hγeac (φ₁ n))
      (fun n => by
        have h1 : (∫⁻ t in Set.Ioc 0 T, ENNReal.ofReal (kinetic m (deriv (γe (φ₁ n)) t)))
            ≤ ENNReal.ofReal ((Real.sqrt K) ^ 2) := by
          rw [lintegral_ofReal_kinetic_eq]
          exact hγekin (φ₁ n)
        have h2 := euclidean_energy_le_of_kinetic (M := Real.sqrt K) hc hmc h1
        rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ K / ((1 / 2) * c))]
        rwa [Real.sq_sqrt hKpos.le] at h2)
      ⟨x, fun n => hγe0 (φ₁ n)⟩
  set ψ : ℕ → ℕ := fun k => φ₁ (φ₂ k) with hψdef
  have hψmono : StrictMono ψ := hφ₁mono.comp hφ₂mono
  have hψtendsto : Tendsto ψ atTop atTop := hψmono.tendsto_atTop
  have hτψlim : Tendsto (fun k => τ (ψ k)) atTop (𝓝 τ₀) := by
    show Tendsto (fun k => τ (φ₁ (φ₂ k))) atTop (𝓝 τ₀)
    exact hτφlim.comp hφ₂mono.tendsto_atTop
  have hconvψ : TendstoUniformlyOn (fun k => γe (ψ k)) γlim atTop (Set.Icc 0 T) := by
    show TendstoUniformlyOn (fun k => γe (φ₁ (φ₂ k))) γlim atTop (Set.Icc 0 T)
    exact hconvunif
  -- basic facts about the limit curve
  have hγlim0 : γlim 0 = x := by
    refine tendsto_nhds_unique (hconvψ.tendsto_at (Set.left_mem_Icc.mpr hTpos.le)) ?_
    simpa only [hγe0] using tendsto_const_nhds (x := x) (f := atTop)
  have hγlimT : γlim T = y := by
    refine tendsto_nhds_unique (hconvψ.tendsto_at (Set.right_mem_Icc.mpr hTpos.le)) ?_
    simpa only [hγeT] using tendsto_const_nhds (x := y) (f := atTop)
  have hγlimy : ∀ t ∈ Set.Ioc τ₀ T, γlim t = y := by
    intro t ht
    have hev : ∀ᶠ k in atTop, τ (ψ k) < t := hτψlim.eventually (eventually_lt_nhds ht.1)
    have heq : (fun k => γe (ψ k) t) =ᶠ[atTop] (fun _ => y) := hev.mono fun k hk => by
      show γ (ψ k) (min t (τ (ψ k))) = y
      rw [min_eq_right hk.le, hγ1 (ψ k)]
    exact tendsto_nhds_unique (hconvψ.tendsto_at ⟨hτ₀pos.le.trans ht.1.le, ht.2⟩)
      (tendsto_const_nhds.congr' heq.symm)
  have hγlimτ₀ : γlim τ₀ = y := by
    set u : ℕ → ℝ := fun n => τ₀ + (T - τ₀) * ((1 : ℝ) / (n + 2)) with hudef
    have hu_tendsto : Tendsto u atTop (𝓝 τ₀) := by
      have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 2)) atTop (𝓝 0) := by
        have h2 : Tendsto (fun n : ℕ => n + 1) atTop atTop := tendsto_add_atTop_nat 1
        have h4 : Tendsto (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp h2
        have h5 : ∀ n : ℕ, (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 1) = 1 / (n + 2) := by
          intro n; push_cast; ring
        simpa only [h5] using h4
      have h5 : Tendsto (fun n : ℕ => (T - τ₀) * ((1 : ℝ) / (n + 2))) atTop (𝓝 0) := by
        simpa using h1.const_mul (T - τ₀)
      simpa [hudef] using tendsto_const_nhds.add h5
    have hu_mem : ∀ n, u n ∈ Set.Icc (0:ℝ) T := by
      intro n
      have h1 : (1 : ℝ) / (n + 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
      refine ⟨by positivity, ?_⟩
      have : (T - τ₀) * ((1:ℝ)/(n + 2)) ≤ T - τ₀ := by
        calc (T - τ₀) * ((1:ℝ)/(n+2)) ≤ (T - τ₀) * 1 := mul_le_mul_of_nonneg_left h1 (by linarith)
          _ = T - τ₀ := mul_one _
      rw [hudef]; linarith
    have hu_y : ∀ n, γlim (u n) = y := by
      intro n
      rcases lt_or_eq_of_le hτ₀T with hlt | heq
      · refine hγlimy (u n) ⟨?_, ?_⟩
        · have hpos : (T - τ₀) * ((1:ℝ)/(n+2)) > 0 := by
            exact mul_pos (by linarith) (by positivity)
          rw [hudef]; linarith
        · exact (hu_mem n).2
      · have : u n = T := by
          rw [hudef, ← heq]; ring
        rw [this, hγlimT]
    have h1 : Tendsto (fun n => γlim (u n)) atTop (𝓝 (γlim τ₀)) :=
      (show Tendsto γlim (𝓝[Set.Icc 0 T] τ₀) (𝓝 (γlim τ₀)) from hγlimcont τ₀ ⟨hτ₀pos.le, hτ₀T⟩).comp
        (tendsto_nhdsWithin_iff.mpr ⟨hu_tendsto, Eventually.of_forall hu_mem⟩)
    have h2 : Tendsto (fun n => γlim (u n)) atTop (𝓝 y) := by
      simpa only [hu_y] using tendsto_const_nhds (x := y) (f := atTop)
    exact tendsto_nhds_unique h1 h2
  -- the truncated limit curve
  set γstar : ℝ → EN E N := fun t => γlim (min t τ₀) with hγstardef
  have hγstar_eq : ∀ t ∈ Set.Icc 0 T, γstar t = γlim t := by
    intro t ht
    rcases le_or_gt t τ₀ with h | h
    · show γlim (min t τ₀) = γlim t
      rw [min_eq_left h]
    · show γlim (min t τ₀) = γlim t
      rw [min_eq_right h.le, hγlimτ₀, hγlimy t ⟨h, ht.2⟩]
  have hγstar0 : γstar 0 = x := by
    show γlim (min 0 τ₀) = x
    rw [min_eq_left hτ₀pos.le, hγlim0]
  have hγstarτ₀ : γstar τ₀ = y := by
    show γlim (min τ₀ τ₀) = y
    rw [min_self, hγlimτ₀]
  have hγstarcont : ContinuousOn γstar (Set.Icc 0 T) := by
    refine hγlimcont.comp (continuous_id.min continuous_const).continuousOn ?_
    intro t ht
    exact ⟨le_min ht.1 hτ₀pos.le, (min_le_right _ _).trans hτ₀T⟩
  have hMW := Commons.MeasureTheory.Integral.massWeighted_kinetic_le_liminf hc hmc hTpos.le
    (Real.sqrt_nonneg K) hγlimcont hconvψ (fun k => hγeac (ψ k)) (fun k => hγekin (ψ k))
  have hγstarac : AbsolutelyContinuousOnInterval γstar 0 τ₀ := by
    show AbsolutelyContinuousOnInterval (fun t => γlim (min t τ₀)) 0 τ₀
    exact absolutelyContinuousOnInterval_comp_min (le_of_lt hτ₀pos) le_rfl
      (hMW.1.mono (by
        rw [uIcc_of_le hτ₀pos.le, uIcc_of_le hTpos.le]
        exact Set.Icc_subset_Icc le_rfl hτ₀T))
  -- lower semicontinuity of the kinetic energy
  have hkin_star : (∫⁻ t in Set.Ioc 0 T, ENNReal.ofReal (kinetic m (deriv γstar t)))
      ≤ liminf (fun k => ∫⁻ t in Set.Ioc 0 T,
          ENNReal.ofReal (kinetic m (deriv (γe (ψ k)) t))) atTop := by
    simp only [lintegral_ofReal_kinetic_eq]
    refine (lintegral_mono_ae ?_).trans hMW.2
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp (measure_singleton τ₀)]
      with t htmem ht
    rcases lt_or_ge t τ₀ with hlt | hge
    · have hderiv : deriv γstar t = deriv γlim t := by
        show deriv (fun s : ℝ => γlim (min s τ₀)) t = deriv γlim t
        exact Commons.Analysis.Calculus.deriv_comp_min_of_lt γlim hlt
      rw [hderiv]
    · have hderiv : deriv γstar t = 0 := by
        show deriv (fun s : ℝ => γlim (min s τ₀)) t = 0
        exact Commons.Analysis.Calculus.deriv_comp_min_of_gt γlim (lt_of_le_of_ne hge (Ne.symm htmem))
      rw [hderiv]
      simp
  -- lower semicontinuity of the potential
  have hconv_star : ∀ t ∈ Set.Ioc 0 T, Tendsto (fun k => γe (ψ k) t) atTop (𝓝 (γstar t)) := by
    intro t ht
    have h1 := hconvψ.tendsto_at ⟨le_of_lt ht.1, ht.2⟩
    rwa [hγstar_eq t ⟨le_of_lt ht.1, ht.2⟩]
  have hpot_star : (∫⁻ t in Set.Ioc 0 T, pairPot m (γstar t))
      ≤ liminf (fun k => ∫⁻ t in Set.Ioc 0 T, pairPot m (γe (ψ k) t)) atTop :=
    lintegral_pairPot_le_liminf' (fun i => (hm i).le) hconv_star (fun k => hγecont (ψ k))
  have haction : actionOn m h γstar 0 T
      ≤ liminf (fun k => actionOn m h (γe (ψ k)) 0 T) atTop :=
    actionOn_le_liminf hm hh.le
      (aemeasurable_pairPot_comp (hγstarcont.mono Set.Ioc_subset_Icc_self) measurableSet_Ioc)
      hkin_star hpot_star
  -- the tail estimate
  have hc0 : 0 < U m y + h := by
    have := U_nonneg (fun i => (hm i).le) y
    linarith
  have htail : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      ENNReal.ofReal (U m y + h) * ENNReal.ofReal (T - τ (ψ k))
        ≤ ENNReal.ofReal (U m y + h) * ENNReal.ofReal (T - τ₀) + ENNReal.ofReal ε := by
    intro ε hε
    have hδ' : 0 < ε / (U m y + h + 1) := by positivity
    have hτlim' : Tendsto (fun k => T - τ (ψ k)) atTop (𝓝 (T - τ₀)) :=
      tendsto_const_nhds.sub hτψlim
    have hev : ∀ᶠ k in atTop, T - τ (ψ k) ≤ T - τ₀ + ε / (U m y + h + 1) :=
      hτlim'.eventually (eventually_le_nhds (by linarith))
    filter_upwards [hev] with k hk
    have hstep : (U m y + h) * (T - τ (ψ k)) ≤ (U m y + h) * (T - τ₀) + ε := by
      have h1 : (U m y + h) * (T - τ (ψ k)) ≤ (U m y + h) * (T - τ₀ + ε / (U m y + h + 1)) :=
        mul_le_mul_of_nonneg_left hk hc0.le
      have h2 : (U m y + h) * (ε / (U m y + h + 1)) ≤ ε := by
        rw [← mul_div_assoc, div_le_iff₀ (by linarith : (0:ℝ) < U m y + h + 1)]
        nlinarith [hc0, hε.le]
      linarith
    calc ENNReal.ofReal (U m y + h) * ENNReal.ofReal (T - τ (ψ k))
        = ENNReal.ofReal ((U m y + h) * (T - τ (ψ k))) := (ENNReal.ofReal_mul hc0.le).symm
      _ ≤ ENNReal.ofReal ((U m y + h) * (T - τ₀) + ε) := ENNReal.ofReal_le_ofReal hstep
      _ ≤ ENNReal.ofReal ((U m y + h) * (T - τ₀)) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
      _ = ENNReal.ofReal (U m y + h) * ENNReal.ofReal (T - τ₀) + ENNReal.ofReal ε := by
            rw [ENNReal.ofReal_mul hc0.le]
  have heps : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      ENNReal.ofReal (1 / (ψ k + 1 : ℝ)) ≤ ENNReal.ofReal ε := by
    intro ε hε
    have h1 : Tendsto (fun k : ℕ => (1 : ℝ) / (ψ k + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hψtendsto
    filter_upwards [h1.eventually (Iio_mem_nhds hε)] with k hk
    exact ENNReal.ofReal_le_ofReal hk.le
  have hS : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      actionOn m h (γe (ψ k)) 0 T
        ≤ A + ENNReal.ofReal (U m y + h) * ENNReal.ofReal (T - τ₀) + ENNReal.ofReal ε := by
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    filter_upwards [htail (ε / 2) hε2, heps (ε / 2) hε2] with k hk1 hk2
    have h1 : actionOn m h (γe (ψ k)) 0 T = actionOn m h (γ (ψ k)) 0 (τ (ψ k))
        + ENNReal.ofReal (U m y + h) * ENNReal.ofReal (T - τ (ψ k)) := by
      show actionOn m h (fun t => γ (ψ k) (min t (τ (ψ k)))) 0 T = _
      exact actionOn_comp_min_eq (hτ0 (ψ k)) (hτleT' (ψ k)) hy (hγ1 (ψ k))
    rw [h1]
    have h3 : ENNReal.ofReal (1 / (ψ k + 1 : ℝ)) + ENNReal.ofReal (ε / 2) ≤ ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hk2' : (1 : ℝ) / (ψ k + 1) ≤ ε / 2 := by
        have h := (ENNReal.ofReal_le_ofReal_iff (show (0:ℝ) ≤ ε / 2 by positivity)).mp hk2
        simpa using h
      linarith
    calc actionOn m h (γ (ψ k)) 0 (τ (ψ k))
            + ENNReal.ofReal (U m y + h) * ENNReal.ofReal (T - τ (ψ k))
        ≤ (A + ENNReal.ofReal (1 / (ψ k + 1 : ℝ)))
            + (ENNReal.ofReal (U m y + h) * ENNReal.ofReal (T - τ₀) + ENNReal.ofReal (ε / 2)) :=
          add_le_add (hγlt (ψ k)).le hk1
      _ = A + ENNReal.ofReal (U m y + h) * ENNReal.ofReal (T - τ₀)
            + (ENNReal.ofReal (1 / (ψ k + 1 : ℝ)) + ENNReal.ofReal (ε / 2)) := by ac_rfl
      _ ≤ A + ENNReal.ofReal (U m y + h) * ENNReal.ofReal (T - τ₀) + ENNReal.ofReal ε :=
          add_le_add le_rfl h3
  have hlimB : ∀ ε : ℝ, 0 < ε →
      liminf (fun k => actionOn m h (γe (ψ k)) 0 T) atTop
        ≤ A + ENNReal.ofReal (U m y + h) * ENNReal.ofReal (T - τ₀) + ENNReal.ofReal ε := by
    intro ε hε
    have hbdd : Filter.IsBoundedUnder (· ≥ ·) atTop
        (fun k : ℕ => actionOn m h (γe (ψ k)) 0 T) :=
      ⟨0, Eventually.of_forall fun k => bot_le⟩
    refine liminf_le_of_le hbdd ?_
    intro b hb
    obtain ⟨k, hk1, hk2⟩ := (hb.and (hS ε hε)).exists
    exact hk1.trans hk2
  have hboundA : actionOn m h γstar 0 T
      ≤ A + ENNReal.ofReal (U m y + h) * ENNReal.ofReal (T - τ₀) := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε' : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    have h := haction.trans (hlimB (ε : ℝ) hε')
    simpa [ENNReal.ofReal_coe_nnreal] using h
  -- split off the constant tail and cancel it
  have hsplitstar : actionOn m h γstar 0 T
      = actionOn m h γstar 0 τ₀ + ENNReal.ofReal (U m y + h) * ENNReal.ofReal (T - τ₀) := by
    have h1 : actionOn m h (fun t => γlim (min t τ₀)) 0 T
        = actionOn m h γlim 0 τ₀ + ENNReal.ofReal (U m y + h) * ENNReal.ofReal (T - τ₀) :=
      actionOn_comp_min_eq hτ₀pos hτ₀T hy hγlimτ₀
    rw [hγstardef, h1, actionOn_comp_min_self]
  have hcTne : ENNReal.ofReal (U m y + h) * ENNReal.ofReal (T - τ₀) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hfinal : actionOn m h γstar 0 τ₀ ≤ A := by
    have h1 : actionOn m h γstar 0 τ₀ + ENNReal.ofReal (U m y + h) * ENNReal.ofReal (T - τ₀)
        ≤ A + ENNReal.ofReal (U m y + h) * ENNReal.ofReal (T - τ₀) := by
      rw [← hsplitstar]; exact hboundA
    exact (ENNReal.add_le_add_iff_right hcTne).mp h1
  have hAle : A ≤ actionOn m h γstar 0 τ₀ := by
    rw [hAdef]
    exact actionPot_le_of hτ₀pos hγstar0 hγstarτ₀ hγstarac
  exact ⟨τ₀, hτ₀pos, γstar, hγstar0, hγstarτ₀, hγstarac, le_antisymm hfinal hAle⟩


/-! ## Finiteness of the action potential and Tonelli's theorem -/

/-- **Finiteness of the action potential.**  In dimension at least two, two collision-free
configurations are joined by an absolutely continuous collision-free curve with finite `L²`
derivative norm, hence have finite action potential. -/
theorem actionPot_lt_top {m : Fin N → ℝ} {h : ℝ} (hm : ∀ i, 0 < m i) (hh : 0 < h)
    (hdim : 2 ≤ Module.finrank ℝ E) {x y : EN E N} (hx : WithoutCollisions x)
    (hy : WithoutCollisions y) : actionPot m h x y < ⊤ := by
  obtain ⟨τ, γ, hτ, hγ0, hγ1, hγac, hγderiv, hγnc⟩ :=
    Commons.Topology.Metric.exists_path_avoiding_collisions_with_deriv_bound hdim
      (fun i j hij h => hx i j hij (by rw [r, h, dist_self]))
      (fun i j hij h => hy i j hij (by rw [r, h, dist_self]))
  exact actionPot_lt_top_of_path hm hh hτ hγ0 hγ1 hγac
    (fun t ht i j hij => by rw [r]; exact fun h => hγnc t ht i j hij (dist_eq_zero.mp h))
    hγderiv

/-- **Tonelli's theorem**: for collision-free distinct endpoint configurations in dimension at
least two there is an absolutely continuous curve realising the action potential. -/
theorem exists_minimizer_of_avoiding {m : Fin N → ℝ} {h : ℝ} (hm : ∀ i, 0 < m i) (hh : 0 < h)
    (hdim : 2 ≤ Module.finrank ℝ E) {x y : EN E N} (hxy : x ≠ y) (hx : WithoutCollisions x)
    (hy : WithoutCollisions y) :
    ∃ τ > 0, ∃ γ : ℝ → EN E N, γ 0 = x ∧ γ τ = y ∧
      AbsolutelyContinuousOnInterval γ 0 τ ∧ actionOn m h γ 0 τ = actionPot m h x y :=
  exists_minimizer hm hh hxy hy (actionPot_lt_top hm hh hdim hx hy)

end Submission.NBody
