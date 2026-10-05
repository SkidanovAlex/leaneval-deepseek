import Mathlib
import Submission.Work.RPB.B5.paramIntegralHasFDerivAt

/-!
# Smoothness of a parametric interval integral from a *local* hypothesis

The target statement `Work.RPB.B5.contDiffAt_param_intervalIntegral` says that if the integrand
`(s, u) ↦ g s u` is jointly `C^n` **at each point** `(s₀, u)` with `u ∈ uIcc a b` (and nowhere else
is anything assumed), then `s ↦ ∫ u in a..b, g s u` is `C^n` at `s₀`.

Proof.  Compactness of `{s₀} × uIcc a b` together with openness of the set of points at which a
function is `C^m` (the tube lemma, `exists_isOpen_box_of_contDiffAt_uIcc`) upgrades the pointwise
hypothesis to `C^m`-ness on a product of open sets, and hence on a compact slab
`closedBall s₀ r ×ˢ uIcc a b`.  On that slab the classical dominated-convergence theorems for
parametric integrals apply, so the argument is an induction on `n`:

* `n = 0`: `paramIntegralContinuousOn_aux` (dominated convergence for the interval integral);
* `n + 1`: differentiate under the integral sign on a ball around `s₀`
  (`Work.RPB.B5.paramIntegralHasFDerivAt`), the derivative being
  `s ↦ ∫ u in a..b, (fderiv ℝ (fun z => g z.1 z.2) (s,u)) ∘ inl`, which is `C^n` by the induction
  hypothesis applied to `(s,u) ↦ (fderiv ℝ (fun z => g z.1 z.2) (s,u)) ∘ inl`; conclude with
  `contDiffAt_succ_iff_hasFDerivAt`.

This is the local, `ContDiffAt`-form counterpart of the team's global results
`Work.RPA3.contDiff_param_intervalIntegral` and `Work.RPB.B2.paramIntegral_contDiff_inf`.
-/

open MeasureTheory Set Filter
open scoped Interval ContDiff Topology

noncomputable section

namespace Work.RPB.B5

/-- **Tube lemma.**  If `G` is `C^m` at every point `(s₀, u)` with `u ∈ uIcc a b`, then it is `C^m`
on a product of open sets containing `s₀` (in the first variable) and `uIcc a b` (in the second).
Indeed `{z | ContDiffAt ℝ m G z}` is open, and the compact set `{s₀} ×ˢ uIcc a b` is contained in
it, so `generalized_tube_lemma` applies. -/
theorem exists_isOpen_box_of_contDiffAt_uIcc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (G : ℝ × ℝ → F) (s₀ a b : ℝ)
    (hG : ∀ u ∈ Set.uIcc a b, ContDiffAt ℝ m G (s₀, u)) :
    ∃ u v : Set ℝ, IsOpen u ∧ IsOpen v ∧ s₀ ∈ u ∧ Set.uIcc a b ⊆ v ∧ ContDiffOn ℝ m G (u ×ˢ v) := by
  have hO : IsOpen {z : ℝ × ℝ | ContDiffAt ℝ m G z} := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    exact (show ContDiffAt ℝ m G z from hz).eventually (by simp)
  have hsub : ({s₀} : Set ℝ) ×ˢ Set.uIcc a b ⊆ {z : ℝ × ℝ | ContDiffAt ℝ m G z} := by
    rintro ⟨x, y⟩ ⟨rfl, hy⟩
    exact hG y hy
  obtain ⟨u, v, hu, hv, hsu, hsv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_uIcc hO hsub
  refine ⟨u, v, hu, hv, hsu (mem_singleton s₀), hsv, fun z hz => ?_⟩
  exact (show ContDiffAt ℝ m G z from huv hz).contDiffWithinAt

/-- Continuity of a parametric interval integral from a local continuity hypothesis: if `G` is
continuous on an open `U` containing `{s₀} ×ˢ uIcc a b`, then `s ↦ ∫ u in a..b, G (s,u)` is
continuous on a ball around `s₀`.  This is the `n = 0` case of the induction. -/
private theorem paramIntegralContinuousOn_aux {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (G : ℝ × ℝ → F) {s₀ a b : ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hG : ContinuousOn G U) (hsub : {s₀} ×ˢ Set.uIcc a b ⊆ U) :
    ∃ r > 0, ContinuousOn (fun s : ℝ => ∫ u in a..b, G (s, u)) (Metric.ball s₀ r) := by
  obtain ⟨u, v, hu, hv, hsu, hsv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_uIcc hU hsub
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hu.mem_nhds (hsu (mem_singleton s₀)))
  have hK : Metric.closedBall s₀ (ε / 2) ×ˢ Set.uIcc a b ⊆ U := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact huv ⟨hball (Metric.closedBall_subset_ball (half_lt_self hε) hx), hsv ht⟩
  obtain ⟨C, hC⟩ := ((isCompact_closedBall s₀ (ε / 2)).prod isCompact_uIcc)
    |>.exists_bound_of_continuousOn (hG.mono hK)
  have hcl : Metric.ball s₀ (ε / 2) ⊆ u := fun x hx =>
    hball (Metric.closedBall_subset_ball (half_lt_self hε) (Metric.ball_subset_closedBall hx))
  refine ⟨ε / 2, half_pos hε, fun s hs => ?_⟩
  have hsu' : s ∈ u := hcl hs
  have hnb : Metric.closedBall s₀ (ε / 2) ∈ 𝓝 s :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hs) Metric.ball_subset_closedBall
  have key : ContinuousAt (fun x : ℝ => ∫ t in a..b, G (x, t)) s := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := 𝓝 s) (F := fun x t => G (x, t)) (f := fun t => G (s, t))
      (fun _ => C) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [hnb] with x hx
      exact ((ContinuousOn.comp hG ((continuous_const.prodMk continuous_id).continuousOn)
        (fun t ht => huv ⟨hball (Metric.closedBall_subset_ball (half_lt_self hε) hx), hsv ht⟩)).mono
        Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
    · filter_upwards [hnb] with x hx
      filter_upwards with t ht
      exact hC (x, t) ⟨hx, Set.uIoc_subset_uIcc ht⟩
    · filter_upwards with t ht
      have huv_st : (s, t) ∈ u ×ˢ v := ⟨hsu', hsv (Set.uIoc_subset_uIcc ht)⟩
      have hUst : U ∈ 𝓝 (s, t) := Filter.mem_of_superset ((hu.prod hv).mem_nhds huv_st) huv
      have h1 : Tendsto G (𝓝 (s, t)) (𝓝 (G (s, t))) := hG.continuousAt hUst
      have h2 : Tendsto (fun y : ℝ => (y, t)) (𝓝 s) (𝓝 (s, t)) :=
        (continuous_id.prodMk continuous_const).continuousAt
      exact h1.comp h2
  exact key.continuousWithinAt

/-- The main induction: `C^n`-smoothness of a parametric interval integral from a pointwise
`C^n`-hypothesis on the compact segment.  Generalized over the codomain `F` so that the induction
can be applied to the `(ℝ →L[ℝ] F)`-valued partial derivative. -/
private theorem contDiffAt_param_intervalIntegral_aux : ∀ (n : ℕ),
    ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (g : ℝ → ℝ → F) (s₀ a b : ℝ),
      (∀ u ∈ Set.uIcc a b, ContDiffAt ℝ n (fun z : ℝ × ℝ => g z.1 z.2) (s₀, u)) →
      ContDiffAt ℝ n (fun s : ℝ => ∫ u in a..b, g s u) s₀ := by
  intro n
  induction n with
  | zero =>
    intro F _ _ _ g s₀ a b hg
    obtain ⟨u, v, hu, hv, hsu, hsv, hCD⟩ :=
      exists_isOpen_box_of_contDiffAt_uIcc 0 (fun z : ℝ × ℝ => g z.1 z.2) s₀ a b hg
    have hsub : ({s₀} : Set ℝ) ×ˢ Set.uIcc a b ⊆ u ×ˢ v := by
      rintro ⟨x, y⟩ ⟨rfl, hy⟩
      exact ⟨hsu, hsv hy⟩
    obtain ⟨r, hr, hcont⟩ :=
      paramIntegralContinuousOn_aux (fun z : ℝ × ℝ => g z.1 z.2) (hu.prod hv) hCD.continuousOn hsub
    refine contDiffAt_zero.mpr ⟨Metric.ball s₀ r, Metric.ball_mem_nhds s₀ hr, ?_⟩
    simpa using hcont
  | succ n ih =>
    intro F _ _ _ g s₀ a b hg
    set Ff : ℝ × ℝ → F := fun z => g z.1 z.2 with hFf
    have hg1 : ∀ u ∈ Set.uIcc a b, ContDiffAt ℝ 1 Ff (s₀, u) := fun u hu => (hg u hu).of_le (by norm_num)
    obtain ⟨u, v, hu, hv, hsu, hsv, hCD⟩ := exists_isOpen_box_of_contDiffAt_uIcc 1 Ff s₀ a b hg1
    have hsub : ({s₀} : Set ℝ) ×ˢ Set.uIcc a b ⊆ u ×ˢ v := by
      rintro ⟨x, y⟩ ⟨rfl, hy⟩
      exact ⟨hsu, hsv hy⟩
    obtain ⟨r, hr, hfd⟩ := paramIntegralHasFDerivAt Ff (hu.prod hv) hCD hsub
    set g₁ : ℝ → ℝ → (ℝ →L[ℝ] F) :=
      fun s u => (fderiv ℝ Ff (s, u)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) with hg₁
    have hg₁h : ∀ u ∈ Set.uIcc a b, ContDiffAt ℝ n (fun z : ℝ × ℝ => g₁ z.1 z.2) (s₀, u) := by
      intro u hu
      have h1 : ContDiffAt ℝ n (fderiv ℝ Ff) (s₀, u) := (hg u hu).fderiv_right (by norm_num)
      have h2 : ContDiffAt ℝ n
          (fun z : ℝ × ℝ => (fderiv ℝ Ff z).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) (s₀, u) := by
        fun_prop
      simpa only [hg₁] using h2
    have hIH : ContDiffAt ℝ n (fun s : ℝ => ∫ u in a..b, g₁ s u) s₀ := ih g₁ s₀ a b hg₁h
    rw [show (((n + 1 : ℕ)) : WithTop ℕ∞) = ((n : ℕ) : WithTop ℕ∞) + 1 from by push_cast; rfl]
    rw [contDiffAt_succ_iff_hasFDerivAt]
    refine ⟨fun s => ∫ u in a..b, g₁ s u,
      ⟨Metric.ball s₀ r, Metric.ball_mem_nhds s₀ hr, ?_⟩, ?_⟩
    · intro x hx
      simpa only [hg₁, hFf] using hfd x hx
    · simpa only [hg₁] using hIH

theorem contDiffAt_param_intervalIntegral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (n : ℕ) (g : ℝ → ℝ → F) (s₀ : ℝ) (a b : ℝ)
    (hg : ∀ u ∈ Set.uIcc a b, ContDiffAt ℝ n (fun z : ℝ × ℝ => g z.1 z.2) (s₀, u)) :
    ContDiffAt ℝ n (fun s : ℝ => ∫ u in a..b, g s u) s₀ :=
  contDiffAt_param_intervalIntegral_aux n g s₀ a b hg

end Work.RPB.B5
