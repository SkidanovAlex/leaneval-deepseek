import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Smoothness of the parameter-dependent integral `p ↦ ∫ x in k, F p x` when `k` is compact.
-/

universe u

open scoped ContDiff Topology
open MeasureTheory ContinuousLinearMap Filter

namespace Commons.Analysis.Calculus

/-- Joint smoothness of the partial derivative. -/
theorem contDiff_uncurry_partialFDeriv {P X E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : P → X → E} {m : ℕ}
    (hF : ContDiff ℝ ((m+1 : ℕ) : ℕ∞) (Function.uncurry F)) :
    ContDiff ℝ (m : ℕ∞)
      (Function.uncurry fun p x => fderiv ℝ (fun q : P => F q x) p) := by
  set σ : ((P × X) × P) →L[ℝ] (P × X) :=
    (ContinuousLinearMap.snd ℝ (P × X) P).prod
      ((ContinuousLinearMap.snd ℝ P X).comp (ContinuousLinearMap.fst ℝ (P × X) P))
    with hσ
  have hσapp : ∀ (z : P × X) (q : P), σ (z, q) = (q, z.2) := by
    intro z q
    simp [hσ, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply]
  have h1 : (fun w : (P × X) × P => F w.2 w.1.2) = Function.uncurry F ∘ σ := by
    funext w
    obtain ⟨⟨p, x⟩, q⟩ := w
    simp only [Function.comp_apply, Function.uncurry]
    rw [hσapp (p, x) q]
  have h2 : ContDiff ℝ ((m+1 : ℕ) : ℕ∞)
      (Function.uncurry fun z : P × X => fun q : P => F q z.2) := by
    show ContDiff ℝ ((m+1 : ℕ) : ℕ∞) (fun w : (P × X) × P => F w.2 w.1.2)
    rw [h1]
    exact hF.comp σ.contDiff
  have h3 := ContDiff.fderiv (f := fun z : P × X => fun q : P => F q z.2)
      (g := fun z : P × X => z.1) (n := (m : ℕ∞)) h2
      (contDiff_fst (𝕜 := ℝ) (E := P) (F := X)) (by simp [Nat.cast_succ])
  convert h3 using 1
  ext z
  simp [Function.uncurry]

/-- Continuity of a parametric integral over a compact set. -/
theorem continuous_setIntegral_isCompact {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : Set (EuclideanSpace ℝ (Fin 3))} (hk : IsCompact k)
    {F : P → EuclideanSpace ℝ (Fin 3) → E} (hF : Continuous (Function.uncurry F)) :
    Continuous (fun p => ∫ x in k, F p x) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  obtain ⟨v, hv_nhds, hv⟩ : ∃ v ∈ 𝓝 p₀, ∀ q ∈ v, ∀ x ∈ k, dist (F q x) (F p₀ x) < 1 := by
    have hu : {z : E × E | dist z.1 z.2 < 1} ∈ uniformity E :=
      Metric.dist_mem_uniformity one_pos
    obtain ⟨v, hv, hv'⟩ := hk.mem_uniformity_of_prod (s := Set.univ) (q := p₀)
      (f := F) (u := {z : E × E | dist z.1 z.2 < 1}) hF.continuousOn (Set.mem_univ p₀) hu
    exact ⟨v, by simpa using hv, hv'⟩
  have hconv : ∀ q ∈ v, ∀ x ∈ k, ‖F q x‖ ≤ ‖F p₀ x‖ + 1 := by
    intro q hq x hx
    have h := hv q hq x hx
    rw [dist_eq_norm] at h
    calc ‖F q x‖ = ‖(F q x - F p₀ x) + F p₀ x‖ := by rw [sub_add_cancel]
      _ ≤ ‖F q x - F p₀ x‖ + ‖F p₀ x‖ := norm_add_le _ _
      _ ≤ ‖F p₀ x‖ + 1 := by linarith
  refine continuousAt_of_dominated (μ := volume.restrict k) (x₀ := p₀) (F := F)
    (bound := fun x => ‖F p₀ x‖ + 1) ?_ ?_ ?_ ?_
  · filter_upwards with q
    exact (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [hv_nhds] with q hq
    rw [ae_restrict_iff' hk.measurableSet]
    filter_upwards with x hx
    exact hconv q hq x hx
  · exact ((ContinuousOn.integrableOn_compact hk
      ((hF.comp (continuous_const.prodMk continuous_id)).continuousOn).norm).add
      (integrableOn_const hk.measure_ne_top))
  · filter_upwards with x
    exact (hF.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : P => x))).continuousAt

/-- Differentiation under the integral sign over a compact set. -/
theorem hasFDerivAt_setIntegral_isCompact {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {k : Set (EuclideanSpace ℝ (Fin 3))} (hk : IsCompact k)
    {F : P → EuclideanSpace ℝ (Fin 3) → E} {m : ℕ}
    (hF : ContDiff ℝ ((m+1 : ℕ) : ℕ∞) (Function.uncurry F)) (p₀ : P) :
    HasFDerivAt (fun p => ∫ x in k, F p x)
      (∫ x in k, fderiv ℝ (fun q : P => F q x) p₀) p₀ := by
  have hFc : Continuous (Function.uncurry F) := hF.continuous
  have hFtc : ContDiff ℝ (m : ℕ∞)
      (Function.uncurry fun p x => fderiv ℝ (fun q : P => F q x) p) := contDiff_uncurry_partialFDeriv hF
  let F' : P → EuclideanSpace ℝ (Fin 3) → (P →L[ℝ] E) :=
    fun p x => fderiv ℝ (fun q : P => F q x) p
  have hF'c : Continuous (Function.uncurry F') := by
    simpa only [Function.uncurry, F'] using hFtc.continuous
  obtain ⟨v, hv_nhds, hv⟩ : ∃ v ∈ 𝓝 p₀, ∀ q ∈ v, ∀ x ∈ k, dist (F' q x) (F' p₀ x) < 1 := by
    have hu : {z : (P →L[ℝ] E) × (P →L[ℝ] E) | dist z.1 z.2 < 1} ∈ uniformity (P →L[ℝ] E) :=
      Metric.dist_mem_uniformity one_pos
    obtain ⟨v, hv, hv'⟩ := hk.mem_uniformity_of_prod (s := Set.univ) (q := p₀)
      (f := fun q (x : EuclideanSpace ℝ (Fin 3)) => F' q x)
      (u := {z : (P →L[ℝ] E) × (P →L[ℝ] E) | dist z.1 z.2 < 1})
      hF'c.continuousOn (Set.mem_univ p₀) hu
    exact ⟨v, by simpa using hv, hv'⟩
  have hconv : ∀ q ∈ v, ∀ x ∈ k, ‖F' q x‖ ≤ ‖F' p₀ x‖ + 1 := by
    intro q hq x hx
    have h := hv q hq x hx
    rw [dist_eq_norm] at h
    calc ‖F' q x‖ = ‖(F' q x - F' p₀ x) + F' p₀ x‖ := by rw [sub_add_cancel]
      _ ≤ ‖F' q x - F' p₀ x‖ + ‖F' p₀ x‖ := norm_add_le _ _
      _ ≤ ‖F' p₀ x‖ + 1 := by linarith
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume.restrict k)
    (F := F) (F' := fun q x => F' q x) (x₀ := p₀) (s := v) (bound := fun x => ‖F' p₀ x‖ + 1)
    hv_nhds ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards with q
    exact (hFc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ContinuousOn.integrableOn_compact hk
      ((hFc.comp (continuous_const.prodMk continuous_id)).continuousOn)
  · exact (hF'c.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · rw [ae_restrict_iff' hk.measurableSet]
    filter_upwards with x hx
    exact fun q hq => hconv q hq x hx
  · exact ((ContinuousOn.integrableOn_compact hk
      ((hF'c.comp (continuous_const.prodMk continuous_id)).continuousOn).norm).add
      (integrableOn_const hk.measure_ne_top))
  · filter_upwards with x
    intro p hp
    have hd : DifferentiableAt ℝ (fun y : P => F y x) p :=
      (((hF.differentiable (by simp)).differentiableAt (x := (p, x))).comp
        (f := fun y : P => (y, x)) (g := Function.uncurry F) p
        (((hasFDerivAt_id (𝕜 := ℝ) p).prodMk (hasFDerivAt_const x p)).differentiableAt))
    simpa only [F'] using hd.hasFDerivAt

/-- The main induction, for parameters and values in the same universe. -/
theorem contDiff_setIntegral_isCompact_aux {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {k : Set (EuclideanSpace ℝ (Fin 3))} (hk : IsCompact k) :
    ∀ (m : ℕ) (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (F : P → EuclideanSpace ℝ (Fin 3) → E),
      ContDiff ℝ (m : ℕ∞) (Function.uncurry F) →
      ContDiff ℝ (m : ℕ∞) (fun p => ∫ x in k, F p x) := by
  intro m
  induction m with
  | zero =>
    intro E _ _ _ F hF
    simp only [Nat.cast_zero, WithTop.coe_zero] at hF ⊢
    rw [contDiff_zero] at hF ⊢
    exact continuous_setIntegral_isCompact hk hF
  | succ m ih =>
    intro E _ _ _ F hF
    have hgoal : ContDiff ℝ (((m : ℕ∞) : ℕ∞ω) + 1) (fun p => ∫ x in k, F p x) := by
      refine (contDiff_succ_iff_hasFDerivAt (E := P) (F := E) (f := fun p => ∫ x in k, F p x)
        (n := m)).mpr ?_
      refine ⟨fun p => ∫ x in k, fderiv ℝ (fun q : P => F q x) p, ?_, ?_⟩
      · have hj := contDiff_uncurry_partialFDeriv (X := EuclideanSpace ℝ (Fin 3)) (E := E) hF
        exact ih (P →L[ℝ] E) (fun p x => fderiv ℝ (fun q : P => F q x) p) hj
      · intro p
        exact hasFDerivAt_setIntegral_isCompact hk hF p
    convert hgoal using 1
    push_cast
    rfl

/-- Finite smoothness order, for real-valued integrands. -/
theorem contDiff_setIntegral_isCompact_nat {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {k : Set (EuclideanSpace ℝ (Fin 3))} (hk : IsCompact k) :
    ∀ (m : ℕ) (F : P → EuclideanSpace ℝ (Fin 3) → ℝ),
      ContDiff ℝ (m : ℕ∞) (Function.uncurry F) →
      ContDiff ℝ (m : ℕ∞) (fun p => ∫ x in k, F p x) := by
  intro m
  induction m with
  | zero =>
    intro F hF
    simp only [Nat.cast_zero, WithTop.coe_zero] at hF ⊢
    rw [contDiff_zero] at hF ⊢
    exact continuous_setIntegral_isCompact hk hF
  | succ m ih =>
    intro F hF
    have hgoal : ContDiff ℝ (((m : ℕ∞) : ℕ∞ω) + 1) (fun p => ∫ x in k, F p x) := by
      refine (contDiff_succ_iff_hasFDerivAt (E := P) (F := ℝ)
        (f := fun p => ∫ x in k, F p x) (n := m)).mpr ?_
      refine ⟨fun p => ∫ x in k, fderiv ℝ (fun q : P => F q x) p, ?_, ?_⟩
      · exact contDiff_setIntegral_isCompact_aux (P := P) hk m (P →L[ℝ] ℝ)
          (fun p x => fderiv ℝ (fun q : P => F q x) p) (contDiff_uncurry_partialFDeriv hF)
      · intro p
        exact hasFDerivAt_setIntegral_isCompact hk hF p
    convert hgoal using 1
    push_cast
    rfl

/-- The announced lemma. -/
theorem contDiff_setIntegral_isCompact
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F : P → EuclideanSpace ℝ (Fin 3) → ℝ} {k : Set (EuclideanSpace ℝ (Fin 3))}
    {n : ℕ∞} (hk : IsCompact k) (hF : ContDiff ℝ n (Function.uncurry F)) :
    ContDiff ℝ n (fun p => ∫ x in k, F p x) := by
  by_cases hn : n = ⊤
  · subst hn
    rw [contDiff_infty]
    intro m
    exact contDiff_setIntegral_isCompact_nat hk m F (contDiff_infty.mp hF m)
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hn
    subst hm
    exact contDiff_setIntegral_isCompact_nat hk m F hF

end Commons.Analysis.Calculus