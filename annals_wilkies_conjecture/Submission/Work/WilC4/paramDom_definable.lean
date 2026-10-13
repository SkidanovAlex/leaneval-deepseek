import Mathlib
import Submission.Work.WilC4.ParamMonoDefs

namespace Work.WilC4

/-- The projection set produced by existentially quantifying the value coordinate of `PExt Y`
agrees with `PDom Y`. -/
lemma PDom_eq_proj {n : ℕ} (Y : Set (Fin (n + 2) → ℝ)) :
    PDom Y = {v : Fin (n + 1) → ℝ | ∃ u : Fin 1 → ℝ, Sum.elim v u ∈ PExt Y} := by
  ext p
  simp only [PDom, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨fun _ => y, (PExt_apply p y).mpr hy⟩
  · rintro ⟨u, hu⟩
    refine ⟨u 0, (PExt_apply p (u 0)).mp ?_⟩
    have huniq : (fun _ : Fin 1 => u 0) = u :=
      funext fun i => by simp [Subsingleton.elim i 0]
    rw [huniq]
    exact hu

/-- Prove in namespace `Work.WilC4` (declaration name `Work.WilC4.paramDom_definable`) in the file
`Submission/Work/WilC4/paramDom_definable.lean`.  `PDom Y ⊆ ℝ^{n+1}` is the domain of the family of
partial functions `Pfibre Y c`; it is the projection of the extended relation `PExt Y` along the
value coordinate, so it is definable.  See `Work.WilC4.PExt_apply` in
`Submission/Work/WilC4/ParamMonoDefs.lean`. -/
theorem paramDom_definable {n : ℕ} {Y : Set (Fin (n + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.PDom Y) := by
  -- The extended relation is definable: it is the preimage of `Y` under the reindexing `Pτ n`.
  have hExt : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PExt Y) :=
    hY.preimage_comp (Pτ n)
  -- Project along the value coordinate (`Fin 1`), a finite existential quantifier.
  have hproj : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {v : Fin (n + 1) → ℝ | ∃ u : Fin 1 → ℝ, Sum.elim v u ∈ PExt Y} :=
    hExt.exists_of_finite (α := Fin (n + 1)) (β := Fin 1)
  rw [PDom_eq_proj Y]
  exact hproj

end Work.WilC4
