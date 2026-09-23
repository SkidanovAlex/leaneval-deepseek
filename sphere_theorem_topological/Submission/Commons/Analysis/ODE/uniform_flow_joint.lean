import Mathlib
import Submission.Commons.Analysis.ODE.exists_uniform_local_flow_nhds
import Submission.Commons.Analysis.ODE.contDiffAt_solutionMap_of_contDiffOn
import Submission.Commons.Analysis.ODE.uniform_flow_compact_open

/-!
# Uniform local flow with joint smooth dependence

Given a field `F` that is `C^∞` on an open set `W` of a complete real normed space `E` and a compact
set `K ⊆ W`, there are a radius `ρ > 0`, an open neighbourhood `O` of `K` with `O ⊆ W`, and a flow
`α : E → ℝ → E` solving `α p 0 = p`, `∂_t α p t = F (α p t)` for `|t| ≤ ρ` and `p ∈ O`, staying in
`W` on that time interval, whose graph `(q, t) ↦ α q t` is `C^∞` at every `(p, t)` with `p ∈ K` and
`|t| < ρ`, and which is the unique solution (on `[-ρ, ρ]`) with the given initial condition.

The flow itself, together with membership/uniqueness, is
`Commons.Analysis.ODE.exists_uniform_local_flow_nhds`.  The joint smooth dependence is the lemma
`Commons.Analysis.ODE.contDiffAt_solutionMap_of_contDiffOn`, which is applied to the flow on the
neighbourhood `O` (whose first coordinate is open, so the “eventually in `𝓝 p`” hypotheses hold).
-/

namespace Commons.Analysis.ODE

open Set Filter
open scoped Topology ContDiff

theorem uniform_flow_joint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E} {W : Set E} (hW : IsOpen W)
    (hFW : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F W)
    {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ O : Set E, IsOpen O ∧ K ⊆ O ∧ O ⊆ W ∧ ∃ α : E → ℝ → E,
      (∀ p ∈ O, α p 0 = p) ∧
      (∀ p ∈ O, ∀ t : ℝ, |t| ≤ ρ → HasDerivAt (α p) (F (α p t)) t) ∧
      (∀ p ∈ O, ∀ t : ℝ, |t| ≤ ρ → α p t ∈ W) ∧
      (∀ p ∈ K, ∀ t : ℝ, |t| < ρ →
        ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : E × ℝ => α q.1 q.2) (p, t)) ∧
      (∀ p ∈ O, ∀ β : ℝ → E, (∀ t : ℝ, |t| ≤ ρ → HasDerivAt β (F (β t)) t) → β 0 = p →
          ∀ t : ℝ, |t| ≤ ρ → β t = α p t) := by
  -- A flow on an open neighbourhood of `K`, with uniform time, confinement and uniqueness.
  obtain ⟨ρ, hρ, O, hOopen, hKO, hOW, α, h0, hode, hmem, huniq⟩ :=
    exists_uniform_local_flow_nhds hW hFW hK hKW
  refine ⟨ρ, hρ, O, hOopen, hKO, hOW, α, h0, hode, hmem, ?_, huniq⟩
  -- Joint smoothness at `(p, t)` for `p ∈ K`, `|t| < ρ`.
  intro p hp t ht
  have hpO : p ∈ O := hKO hp
  have hOnhds : O ∈ 𝓝 p := hOopen.mem_nhds hpO
  have h0' : ∀ᶠ x in 𝓝 p, α x 0 = x :=
    Filter.eventually_of_mem hOnhds (fun x hx => h0 x hx)
  have hode' : ∀ᶠ x in 𝓝 p, ∀ t ∈ Set.Ioo (-ρ) ρ, HasDerivAt (α x) (F (α x t)) t :=
    Filter.eventually_of_mem hOnhds
      (fun x hx t ht' => hode x hx t (le_of_lt (abs_lt.mpr ht')))
  have hmem' : ∀ᶠ x in 𝓝 p, ∀ t ∈ Set.Ioo (-ρ) ρ, α x t ∈ W :=
    Filter.eventually_of_mem hOnhds
      (fun x hx t ht' => hmem x hx t (le_of_lt (abs_lt.mpr ht')))
  -- Uniqueness on the *open* interval, derived from the closed-interval uniqueness `huniq`
  -- (`ContDiffAt_solutionMap_of_contDiffOn` asks for the open-interval form).
  have huniq' : ∀ᶠ x in 𝓝 p, ∀ y : ℝ → E, (∀ t ∈ Set.Ioo (-ρ) ρ, HasDerivAt y (F (y t)) t) →
      y 0 = x → ∀ t ∈ Set.Ioo (-ρ) ρ, y t = α x t := by
    refine Filter.eventually_of_mem hOnhds ?_
    intro x hx y hy hy0 t₀ ht₀
    -- A closed subinterval `[a', b'] ⊆ (-ρ, ρ)` containing `0` and `t₀`.
    have hcgt : -ρ < min 0 t₀ := lt_min (by linarith) ht₀.1
    have hdlt : max 0 t₀ < ρ := max_lt (by linarith) ht₀.2
    set a' := (min 0 t₀ - ρ) / 2 with ha'
    set b' := (max 0 t₀ + ρ) / 2 with hb'
    have ha'gt : -ρ < a' := by rw [ha']; linarith
    have ha'le : a' ≤ min 0 t₀ := by rw [ha']; linarith
    have hb'lt : b' < ρ := by rw [hb']; linarith
    have hb'ge : max 0 t₀ ≤ b' := by rw [hb']; linarith
    have hsub : Set.Icc a' b' ⊆ Set.Ioo (-ρ) ρ := by
      intro t ht
      exact ⟨by linarith [ht.1, ha'gt, ha'le], by linarith [ht.2, hb'lt, hb'ge]⟩
    have h0eq : α x 0 = y 0 := by rw [h0 x hx, hy0]
    have heq := ufco_eqOn_of_hasDerivAt hW hFW (u := α x) (v := y)
      (a := a') (b := b') (t₀ := 0)
      (le_trans ha'le (min_le_left _ _)) (le_trans (le_max_left _ _) hb'ge)
      (fun t ht => hode x hx t (le_of_lt (abs_lt.mpr (hsub ht))))
      (fun t ht => hy t (hsub ht))
      (fun t ht => hmem x hx t (le_of_lt (abs_lt.mpr (hsub ht))))
      h0eq
    have ht₀mem : t₀ ∈ Set.Icc a' b' :=
      ⟨le_trans ha'le (min_le_right _ _), le_trans (le_max_right _ _) hb'ge⟩
    exact (heq ht₀mem).symm
  exact contDiffAt_solutionMap_of_contDiffOn hW hFW (a := -ρ) (b := ρ)
    (by linarith) (by linarith) h0' hode' hmem' huniq' (abs_lt.mp ht)

end Commons.Analysis.ODE
