import Mathlib
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.EXT.exp_weighted_antitone
import Submission.Work.Diff.EXT.exp_weighted_monotone

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Metric equivalence along a Ricci flow with a pointwise Ricci bound

If `G` is a smooth Ricci flow on `[0,T)` whose Ricci tensor satisfies the pointwise bound
`|Ric_{g(t)}(u,u)| ≤ lam · g(t)(u,u)` for all `u ∈ TₓM` and all `t ∈ [0,T)`, then the metrics at
different times are uniformly equivalent:

`g(t)(u,u) ≤ e^{2·lam·t} · g(0)(u,u)` and `g(0)(u,u) ≤ e^{2·lam·t} · g(t)(u,u)`.

This is the classical two-sided metric estimate for the Ricci flow (Hamilton's maximum principle
for `Ric − λg` / `Ric + λg` in its weakest one-point form); it is used in the continuation /
Shi-estimate part of the sphere theorem (`Work.Diff.EXT.Extension`), where the metrics along the
flow must be uniformly comparable to a fixed one.

The whole content is the two integrating-factor (Gronwall) lemmas `exp_weighted_antitone` and
`exp_weighted_monotone` (proved in the sibling modules), applied to the real function
`s ↦ g(s)(u,u)`, whose derivative is `-2 Ric_{g(s)}(u,u)` by the Ricci-flow equation:
`∂ₜ g = -2 Ric`.

* first inequality: `s ↦ e^{-2·lam·s} g(s)(u,u)` is antitone, because
  `∂ₜ g + (-2 lam) g = -2 Ric - 2 lam g ≤ 0` follows from `-Ric ≤ |Ric| ≤ lam·g`;
* second inequality: `s ↦ e^{2·lam·s} g(s)(u,u)` is monotone, because
  `∂ₜ g + 2 lam g = -2 Ric + 2 lam g ≥ 0` follows from `Ric ≤ |Ric| ≤ lam·g`.

Note that continuity of `s ↦ g(s)(u,u)` is not taken from `JointSmooth` but from the
`HasDerivWithinAt` clauses of `IsRicciFlow`, which give `ContinuousWithinAt`.
-/

open Set Filter

namespace Work.Diff.EXT

theorem metric_equiv_of_ric_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (G : ℝ → Submission.Diff.SMet I M) (T lam : ℝ) (hT : 0 < T) (hlam : 0 ≤ lam)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hric : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      abs (Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) x u u) ≤ lam * (G t).inner x u u) :
    ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * lam * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * lam * t) * (G t).inner x u u := by
  intro t ht x u
  have ht0 : 0 ≤ t := ht.1
  have htT : t < T := ht.2
  -- Continuity of `s ↦ g(s)(u,u)` on `[0,t]`: from `HasDerivWithinAt` on `[0,T)`, using `t < T`.
  have hcontIco : ContinuousOn (fun s : ℝ => (G s).inner x u u) (Set.Ico 0 T) :=
    fun s hs => (hflow.2 s hs x u u).continuousWithinAt
  have hcont : ContinuousOn (fun s : ℝ => (G s).inner x u u) (Set.Icc 0 t) :=
    hcontIco.mono (fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 htT⟩)
  -- The derivative of `s ↦ g(s)(u,u)` on `(0,t)`: `-2 Ric`, transported from `[0,T)`.
  have hder : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      HasDerivAt (fun s : ℝ => (G s).inner x u u)
        (-2 * Submission.Diff.ricAt (Submission.Diff.lcOf (G s)) x u u) s := by
    intro s hs
    have hsIco : s ∈ Set.Ico (0 : ℝ) T := ⟨le_of_lt hs.1, lt_trans hs.2 htT⟩
    have hsIoo : s ∈ Set.Ioo (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 htT⟩
    have hnhds : Set.Ico (0 : ℝ) T ∈ nhds s :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hsIoo) (fun y hy => ⟨le_of_lt hy.1, hy.2⟩)
    exact (hflow.2 s hsIco x u u).hasDerivAt hnhds
  constructor
  · -- `g(t) ≤ e^{2 lam t} g(0)`, from antitonicity of `s ↦ e^{-2 lam s} g(s)`.
    have key : ∀ s ∈ Set.Ioo (0 : ℝ) t,
        -(2 * lam) * (G s).inner x u u +
          (-2 * Submission.Diff.ricAt (Submission.Diff.lcOf (G s)) x u u) ≤ 0 := by
      intro s hs
      have hsIco : s ∈ Set.Ico (0 : ℝ) T := ⟨le_of_lt hs.1, lt_trans hs.2 htT⟩
      have hb := (abs_le.mp (hric s hsIco x u)).1
      linarith
    have hanti := exp_weighted_antitone (c := -(2 * lam)) (T := t) hcont hder key
    have hle := hanti (left_mem_Icc.mpr ht0) (right_mem_Icc.mpr ht0) ht0
    have hle' : Real.exp (-(2 * lam) * t) * (G t).inner x u u ≤ (G 0).inner x u u := by
      simpa using hle
    have hexp : Real.exp (2 * lam * t) * Real.exp (-(2 * lam) * t) = 1 := by
      rw [← Real.exp_add, show 2 * lam * t + -(2 * lam) * t = 0 by ring, Real.exp_zero]
    have h2 := mul_le_mul_of_nonneg_left hle' (Real.exp_nonneg (2 * lam * t))
    refine le_trans ?_ h2
    rw [← mul_assoc, hexp, one_mul]
  · -- `g(0) ≤ e^{2 lam t} g(t)`, from monotonicity of `s ↦ e^{2 lam s} g(s)`.
    have key : ∀ s ∈ Set.Ioo (0 : ℝ) t,
        0 ≤ (2 * lam) * (G s).inner x u u +
          (-2 * Submission.Diff.ricAt (Submission.Diff.lcOf (G s)) x u u) := by
      intro s hs
      have hsIco : s ∈ Set.Ico (0 : ℝ) T := ⟨le_of_lt hs.1, lt_trans hs.2 htT⟩
      have hb := (abs_le.mp (hric s hsIco x u)).2
      linarith
    have hmono := exp_weighted_monotone (c := 2 * lam) (T := t) hcont hder key
    have hle := hmono (left_mem_Icc.mpr ht0) (right_mem_Icc.mpr ht0) ht0
    simpa using hle

end Work.Diff.EXT
