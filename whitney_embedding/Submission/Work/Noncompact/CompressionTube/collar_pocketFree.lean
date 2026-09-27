import Mathlib

/-!
# Pocket-free collars

A **collar** around a compact set `A ⊆ M` is a closed set `L` with `A ⊆ interior L` and
`L ⊆ interior B` for a prescribed open set `B ⊇ A`.  The spine recursion
(`NOTES_new_plan_gate_balls.md`, SESSION 30/31) needs a collar which is **pocket free**: every
component of `Lᶜ` has non-compact closure.  (SESSIONS 28–31 recorded that this cannot be arranged
for collars built as finite unions of chart balls — a "ring" of balls bridging a narrow passage
creates a bounded complementary component.)

## The construction

The point of this file is that pocket freeness *is* attainable, by **subtracting an open set**:

`L := B ∩ Uᶜ`

where `U` is an open set which

* contains the frontier of `B` (so that `L ⊆ interior B`: no point of `L` lies on the boundary of
  `B`),
* avoids `A` together with a neighbourhood of `A` (so that `A ⊆ interior L`), and
* **meets `Bᶜ` in every connected component** (so that no component of `Lᶜ` is trapped: a
  complementary component of `L` which meets `U` contains a whole component of `U`, hence a point
  of `Bᶜ`, hence a full component of `Bᶜ`, whose closure is assumed non-compact; and a
  complementary component which misses `U` is a component of `Bᶜ` itself).

The hypothesis on `B` is exactly "pocket freeness of `B`": no point outside `B` is trapped by `B`.
In the application `B = K (ℓ+2)` and this is the basic hypothesis `hKpf` of the spine recursion.
The open set `U` is built from finitely many chart balls covering the frontier of `B` together with
"tubes" running from prescribed points (the base points of the next level, and a point where the
tips of the level are placed) out of `B`, avoiding `A = K (ℓ+1)` — which is possible by the same
hypothesis `hKpf` at the *previous* level.  Those tubes are the content of the companion lemma
`exists_collar_avoiding_finite`.

The main consequence used downstream is that `L` is pocket free: `∀ x ∉ L`, the component of `x`
in `Lᶜ` has non-compact closure.  This is precisely the hypothesis of
`Work.Noncompact.CompressionTube.exists_reach_of_collar'` (and of its `slits` variant), which is
what makes the level step of the spine recursion work at the points of `Lᶜ` — in particular at the
tips of the next level, which live in `Lᶜ`, and at the base points, which are placed in the tubes
`U ⊆ Lᶜ`.
-/

set_option linter.unusedSectionVars false

namespace Work.Noncompact.CompressionTube

open Set Topology

/-- **Pocket-free collars.**  For closed `B`, open `U` containing the frontier of `B` and meeting
`Bᶜ` in each of its components, and `A ⊆ interior B` at positive distance from the closure of `U`,
the set `L := B ∩ Uᶜ` is a closed collar of `A` inside `interior B`, disjoint from `U`, and pocket
free. -/
theorem isClosed_and_pocketFree_inter_compl {M : Type*} [TopologicalSpace M]
    {A B U : Set M} (hBc : IsClosed B) (hUo : IsOpen U) (hUbd : frontier B ⊆ U)
    (hAB : A ⊆ interior B) (hAU : Disjoint A (closure U))
    (hBpf : ∀ x : M, x ∉ B → ¬ IsCompact (closure (connectedComponentIn (Bᶜ) x)))
    (hUcomp : ∀ x ∈ U, ∃ y ∈ connectedComponentIn U x, y ∉ B) :
    IsClosed (B ∩ Uᶜ) ∧ A ⊆ interior (B ∩ Uᶜ) ∧ (B ∩ Uᶜ) ⊆ interior B ∧
      (B ∩ Uᶜ) ∩ U = ∅ ∧
      (∀ x : M, x ∈ (B ∩ Uᶜ)ᶜ →
        ¬ IsCompact (closure (connectedComponentIn ((B ∩ Uᶜ)ᶜ) x))) := by
  classical
  refine ⟨hBc.inter hUo.isClosed_compl, ?_, ?_, ?_, ?_⟩
  · -- `A ⊆ interior (B ∩ Uᶜ)`: `interior B \ closure U` is open, contains `A` and lies in `B ∩ Uᶜ`
    have h1 : A ∩ closure U = ∅ := Disjoint.inter_eq hAU
    have h2 : A ⊆ interior B \ closure U := by
      intro x hx
      refine ⟨hAB hx, ?_⟩
      intro hxcl
      have hxmas : x ∈ A ∩ closure U := ⟨hx, hxcl⟩
      rw [h1] at hxmas
      exact hxmas
    have h3 : interior B \ closure U ⊆ B ∩ Uᶜ := by
      intro x hx
      exact ⟨interior_subset hx.1, fun hxU => hx.2 (subset_closure hxU)⟩
    exact h2.trans (interior_maximal h3 (isOpen_interior.sdiff isClosed_closure))
  · -- `B ∩ Uᶜ ⊆ interior B`: points of `L` are not on the frontier of `B`
    intro x hx
    by_contra hxf
    have hxfr : x ∈ frontier B := by
      rw [hBc.frontier_eq]
      exact ⟨hx.1, hxf⟩
    exact hx.2 (hUbd hxfr)
  · -- `L` and `U` are disjoint
    ext x
    refine ⟨?_, ?_⟩
    · intro h
      exact h.1.2 h.2
    · intro h
      exact h.elim
  · -- pocket freeness
    intro x hx
    by_contra hc
    set P := connectedComponentIn ((B ∩ Uᶜ)ᶜ) x with hPdef
    have hxP : x ∈ P := mem_connectedComponentIn hx
    have hPsub : P ⊆ (B ∩ Uᶜ)ᶜ := connectedComponentIn_subset _ _
    have hPsub' : P ⊆ Bᶜ ∪ U := by
      intro y hy
      have hy' := hPsub hy
      simpa only [Set.compl_inter, compl_compl, Set.mem_union] using hy'
    have hUsub : U ⊆ (B ∩ Uᶜ)ᶜ := by
      intro w hw hwBU
      exact hwBU.2 hw
    have hBcsub : Bᶜ ⊆ (B ∩ Uᶜ)ᶜ := by
      intro w hw hwBU
      exact hw hwBU.1
    by_cases hPU : ∃ y ∈ P, y ∈ U
    · -- `P` meets `U`, hence contains a whole component of `U`, hence a point of `Bᶜ`
      obtain ⟨y, hyP, hyU⟩ := hPU
      obtain ⟨z, hzQ, hzB⟩ := hUcomp y hyU
      have hQsub : connectedComponentIn U y ⊆ P := by
        rw [hPdef]
        exact (connectedComponentIn_mono y hUsub).trans
          (le_of_eq (connectedComponentIn_eq hyP).symm)
      have hzP : z ∈ P := hQsub hzQ
      have hDsub : connectedComponentIn (Bᶜ) z ⊆ P := by
        rw [hPdef]
        exact (connectedComponentIn_mono z hBcsub).trans
          (le_of_eq (connectedComponentIn_eq hzP).symm)
      exact hBpf z hzB (hc.of_isClosed_subset isClosed_closure (closure_mono hDsub))
    · -- `P` misses `U`, hence is a component of `Bᶜ`
      have hPsubB : P ⊆ Bᶜ := by
        intro y hy
        rcases hPsub' hy with h | h
        · exact h
        · exact absurd ⟨y, hy, h⟩ hPU
      have hxBc : x ∈ Bᶜ := hPsubB hxP
      have hDsub : connectedComponentIn (Bᶜ) x ⊆ P := by
        rw [hPdef]
        exact connectedComponentIn_mono x hBcsub
      have hPsubD : P ⊆ connectedComponentIn (Bᶜ) x :=
        isPreconnected_connectedComponentIn.subset_connectedComponentIn hxP hPsubB
      have heq : connectedComponentIn (Bᶜ) x = P := subset_antisymm hDsub hPsubD
      have := hBpf x hxBc
      rw [heq] at this
      exact this hc

end Work.Noncompact.CompressionTube
