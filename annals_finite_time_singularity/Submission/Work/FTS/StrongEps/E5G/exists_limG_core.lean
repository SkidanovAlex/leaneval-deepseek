/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5G/exists_limG_core.lean` — the E5 leaf, at the `StarCore` hypothesis

`Submission/Work/FTS/StrongEps/exists_limG.lean` is frozen with the hypothesis
`Work.FTS.VocabO2.StarPkgo2 α Cs Φs`.  That hypothesis is **too weak** for the (now complete) E5
chain: the ℋ⁵/ℋ⁶ rows (`E5G.epsWP_hkMem5_bnd_fam`, `E5G.hlim_slots_of_tower`, hence
`E5G.hdbd_of_tower`, hence `E5G.EpsLimPkg_of_horizon_full`/`_comp`) consume
`Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs`, and

* `StrongPersist.StarPkg6OfCore` and `PhiStar.StarPkgo2OfCore` both **lift**
  `Work.FTS.VocabO2.StarCore α Cs Φs`, whose content is the order-7 flatness
  `FlatW 7 (Ycheck α Φs) (Cs * α)`;
* `StarPkgo2` carries order-4 `𝒲^{4,∞}` fields only, and **no lemma of the workspace produces a
  `StarCore` from a `StarPkgo2`** (a bridge would have to manufacture order-7 flatness from
  order-4 data).

This module provides the **ready-made replacement**: the verbatim statement of the frozen leaf with
`StarPkgo2 α Cs Φs` replaced by `StarCore α Cs Φs` (plus `0 < Cs`).  Its proof is the application of
`E5G.ExistsLimG_of_core` (already proved) with the two thresholds produced from
`StrongPersist.L3Data_exists`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsLimitDefsG
import Submission.Work.FTS.StrongEps.E5G.ExistsLimG_of_core
import Submission.Work.FTS.StrongPersist.L3DataFinal

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **E5 with the `StarCore` hypothesis** — the frozen leaf `exists_limG` with
`StarPkgo2 α Cs Φs` replaced by `StarCore α Cs Φs` and `0 < Cs` added. -/
theorem exists_limG_core {C₀ Ce Cs : ℝ} : ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂,
    ∀ {K : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    IsSmoothKernel ρ →
    (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
    EllLimOK3 α E → Work.FTS.VocabO2.StarCore α Cs Φs → 0 < Cs → MuLamOK α C₀ Φs E →
    EpsUniformMem α ρ Φs E g₀ C₀ K → ExistsLimG α C₀ K Φs E g₀ := by
  classical
  obtain ⟨α₀, C3, Cpow, hα₀pos, hC3pos, hCpow, hL3all⟩ :=
    Work.FTS.StrongPersist.L3Data_exists
  set α₂ : ℝ := min (α₀ / 2) (1 / 8) with hα₂def
  have hα₂pos : 0 < α₂ := lt_min (by linarith) (by norm_num)
  have hα₂half : α₂ ≤ α₀ / 2 := min_le_left _ _
  have hα₂eight : α₂ ≤ 1 / 8 := min_le_right _ _
  refine ⟨α₂, hα₂pos, ?_⟩
  intro α hα K ρ Φs E g₀ hρ hEll hELL3 hcore hCs hml hU
  -- the inner thresholds (strictly above the leaf's `α₂`)
  have hα₀' : α < α₀ := lt_of_le_of_lt (le_trans hα.2 hα₂half) (by linarith)
  have hαquarter : α < 1 / 4 := lt_of_le_of_lt (le_trans hα.2 hα₂eight) (by norm_num)
  set α₂' : ℝ := min α₀ (1 / 4) with hα₂'def
  have hα₂'pos : 0 < α₂' := lt_min hα₀pos (by norm_num)
  have hα₂'quarter : α₂' ≤ 1 / 4 := min_le_right _ _
  have hα_lt : α < α₂' := lt_min hα₀' hαquarter
  have hL3 : Work.FTS.StrongPersist.L3Data α₂' Ce C3 Cpow :=
    { pos := ⟨hC3pos, hα₂'pos, hCpow⟩
      lin := fun β hβ f hf =>
        (hL3all Ce).lin β ⟨hβ.1, le_trans hβ.2 (min_le_left _ _)⟩ f hf
      rhs := fun β hβ E' Φs' Φ f Cs' μ lam M hell hadm hXn hmu hlam =>
        (hL3all Ce).rhs β ⟨hβ.1, le_trans hβ.2 (min_le_left _ _)⟩
          E' Φs' Φ f Cs' μ lam M hell hadm hXn hmu hlam }
  exact ExistsLimG_of_core (α₂ := α₂') (α₄ := (α + α₂') / 2)
    hα₂'pos hα₂'quarter ⟨hα.1, le_of_lt hα_lt⟩ (by linarith) (by linarith)
    hL3 hρ hEll hELL3 hcore hCs hml hU

end Work.FTS.StrongEps.E5G
