/-
# `Work.FTS.Apriori.Limit.SupportBox` — boxes for compactly supported test functions

The pairing `∫∫ f ψ` of the chapter is computed against test functions `ψ` whose support is a
compact subset of the *open* quadrant `Qd = (0,∞) × (0,π/2)` (`TestQ ψ`).  This module extracts
from that hypothesis the two facts the integration-by-parts arguments need:

* a closed box `[A,B] × [C,D]` with `0 < A`, `C > 0`, `D < π/2` which contains the support, so
  that every point of the support has its `z`-coordinate bounded away from `0` and its
  `θ`-coordinate bounded away from `0` and `π/2` (`exists_box_of_isCompact_subset_Qd`);
* the resulting *strict* vanishing statements: a function supported in that box vanishes for
  `z < A`, for `z > B`, for `θ < C` and for `θ > D`, uniformly in the other variable
  (`exists_box_vanish`).

Both are purely topological; nothing here mentions the weights or the operators.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.FTS.Apriori.Limit.Defs
import Submission.Work.FTS.Apriori.Limit.SlotCalc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.Limit

set_option autoImplicit false

/-- A compact subset of the open quadrant `Qd = (0,∞) × (0,π/2)` is contained in a closed box
`[A,B] × [C,D]` with strictly positive `z`-bounds and with angular bounds inside `(0,π/2)`. -/
theorem exists_box_of_isCompact_subset_Qd {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hsub : K ⊆ Qd) :
    ∃ A B C D : ℝ, 0 < A ∧ A ≤ B ∧ 0 < C ∧ C ≤ D ∧ D < π / 2 ∧
      K ⊆ Set.Icc A B ×ˢ Set.Icc C D := by
  by_cases hne : K.Nonempty
  · have hKz : IsCompact (Prod.fst '' K) := hK.image continuous_fst
    have hKθ : IsCompact (Prod.snd '' K) := hK.image continuous_snd
    have hnez : (Prod.fst '' K).Nonempty := hne.image Prod.fst
    have hneθ : (Prod.snd '' K).Nonempty := hne.image Prod.snd
    refine ⟨sInf (Prod.fst '' K), sSup (Prod.fst '' K), sInf (Prod.snd '' K),
      sSup (Prod.snd '' K), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨p, hp, hp1⟩ := hKz.sInf_mem hnez
      rw [← hp1]
      exact (mem_Qd_iff.mp (hsub hp)).1
    · exact csInf_le hKz.bddBelow (hKz.sSup_mem hnez)
    · obtain ⟨p, hp, hp2⟩ := hKθ.sInf_mem hneθ
      rw [← hp2]
      exact (mem_Qd_iff.mp (hsub hp)).2.1
    · exact csInf_le hKθ.bddBelow (hKθ.sSup_mem hneθ)
    · obtain ⟨p, hp, hp2⟩ := hKθ.sSup_mem hneθ
      rw [← hp2]
      exact (mem_Qd_iff.mp (hsub hp)).2.2
    · intro p hp
      constructor
      · rw [Set.mem_Icc]
        exact ⟨csInf_le hKz.bddBelow ⟨p, hp, rfl⟩, le_csSup hKz.bddAbove ⟨p, hp, rfl⟩⟩
      · rw [Set.mem_Icc]
        exact ⟨csInf_le hKθ.bddBelow ⟨p, hp, rfl⟩, le_csSup hKθ.bddAbove ⟨p, hp, rfl⟩⟩
  · refine ⟨1, 1, 1, 1, one_pos, le_rfl, one_pos, le_rfl, ?_, ?_⟩
    · linarith [Real.pi_gt_three]
    · intro p hp
      exact absurd ⟨p, hp⟩ hne

/-- **The box of a compactly supported function vanishing off the open quadrant.**  There are
`A < B` and `C < D` with `0 < A`, `C > 0`, `D < π/2` such that `W` vanishes for `z < A`, for
`z > B`, for `θ < C` and for `θ > D` — with no restriction on the other variable. -/
theorem exists_box_vanish {W : ℝ → ℝ → ℝ}
    (hcomp : HasCompactSupport (Function.uncurry W))
    (hsub : tsupport (Function.uncurry W) ⊆ Qd) :
    ∃ A B C D : ℝ, 0 < A ∧ A < B ∧ 0 < C ∧ C < D ∧ D < π / 2 ∧
      (∀ z θ, z < A → W z θ = 0) ∧ (∀ z θ, B < z → W z θ = 0) ∧
      (∀ z θ, θ < C → W z θ = 0) ∧ (∀ z θ, D < θ → W z θ = 0) := by
  obtain ⟨A₀, B₀, C₀, D₀, hA₀, hAB₀, hC₀, hCD₀, hD₀, hbox⟩ :=
    exists_box_of_isCompact_subset_Qd hcomp hsub
  have hmem_of : ∀ z θ : ℝ, W z θ ≠ 0 →
      (z, θ) ∈ tsupport (Function.uncurry W) := fun z θ h =>
    subset_tsupport _ (by simpa [Function.mem_support, Function.uncurry] using h)
  refine ⟨A₀ / 2, B₀ + 1, C₀ / 2, (D₀ + π / 2) / 2, by linarith, by linarith, by linarith,
    by linarith, by linarith, ?_, ?_, ?_, ?_⟩
  · intro z θ hz
    by_contra h
    have h1 : (z, θ) ∈ Set.Icc A₀ B₀ ×ˢ Set.Icc C₀ D₀ := hbox (hmem_of z θ h)
    rw [Set.mem_prod, Set.mem_Icc] at h1
    linarith [h1.1.1]
  · intro z θ hz
    by_contra h
    have h1 : (z, θ) ∈ Set.Icc A₀ B₀ ×ˢ Set.Icc C₀ D₀ := hbox (hmem_of z θ h)
    rw [Set.mem_prod, Set.mem_Icc] at h1
    linarith [h1.1.2]
  · intro z θ hz
    by_contra h
    have h1 : (z, θ) ∈ Set.Icc A₀ B₀ ×ˢ Set.Icc C₀ D₀ := hbox (hmem_of z θ h)
    rw [Set.mem_prod, Set.mem_Icc] at h1
    linarith [h1.2.1]
  · intro z θ hz
    by_contra h
    have h1 : (z, θ) ∈ Set.Icc A₀ B₀ ×ˢ Set.Icc C₀ D₀ := hbox (hmem_of z θ h)
    rw [Set.mem_prod, Set.mem_Icc] at h1
    linarith [h1.2.2]

end Work.FTS.Apriori.Limit
