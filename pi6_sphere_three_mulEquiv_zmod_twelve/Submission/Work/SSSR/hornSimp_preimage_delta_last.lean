import Mathlib
import Submission.Work.SSSR.serreE1PieceDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
noncomputable section

/-- The horn `hornSimp s` is the `s`-th horn `Λ[s, s]` of `Δ[s]`: the union of
all its faces except the last one. -/
theorem hornSimp_eq_horn_last (s : ℕ) :
    hornSimp s = SSet.horn s (Fin.last s) := by
  refine le_antisymm ?_ ?_
  · rw [hornSimp]
    refine iSup_le fun i => SSet.face_le_horn i.castSucc (Fin.last s) (Fin.castSucc_ne_last i)
  · rw [hornSimp, SSet.horn_eq_iSup]
    refine iSup_le fun j => ?_
    have h : j.1 ≠ Fin.last s := by
      have h2 := j.2
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at h2
      exact h2
    rw [← Fin.castSucc_castPred j.1 h]
    exact le_iSup (fun i : Fin s => SSet.stdSimplex.face {i.castSucc}ᶜ) (j.1.castPred h)

/-- Combinatorial form of "the range of `p.succAbove ∘ f` misses a point other than `p`
if and only if the range of `f` misses a point". -/
lemma exists_notMem_succAbove_iff {n m : ℕ} (i : Fin (n + 2)) (f : Fin m → Fin (n + 1)) :
    (∃ j : Fin (n + 2), ∃ (_ : j ≠ i), j ∉ Set.range (fun k => i.succAbove (f k))) ↔
      ∃ k : Fin (n + 1), k ∉ Set.range f := by
  constructor
  · rintro ⟨j, hj, hj'⟩
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hj
    refine ⟨k, ?_⟩
    rintro ⟨l, hl⟩
    exact hj' ⟨l, by simp [hl, hk]⟩
  · rintro ⟨k, hk⟩
    refine ⟨i.succAbove k, Fin.succAbove_ne _ _, ?_⟩
    rintro ⟨l, hl⟩
    exact hk ⟨l, Fin.succAbove_right_injective hl⟩

/-- The preimage of the `i`-th horn `Λ[n+1, i]` under the `i`-th face map is the boundary
`∂Δ[n]`. -/
theorem horn_preimage_delta (n : ℕ) (i : Fin (n + 2)) :
    (SSet.horn (n + 1) i).preimage (SSet.stdSimplex.δ (n := n) i) = SSet.boundary n := by
  ext ⟨⟨d⟩⟩ x
  rw [SSet.Subcomplex.preimage_obj, Set.mem_preimage]
  rw [SSet.mem_horn_iff_notMem_range, SSet.mem_boundary_iff_notMem_range]
  rw [show Set.range ⇑((SSet.stdSimplex.δ (n := n) i).app (op ⦋d⦌) x)
      = Set.range (fun k => i.succAbove (x k)) from rfl]
  exact exists_notMem_succAbove_iff i (fun k => x k)

theorem hornSimp_preimage_delta_last (t : ℕ) :
    (Work.SSSR.hornSimp (t+1)).preimage (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) =
      SSet.boundary t := by
  rw [hornSimp_eq_horn_last, horn_preimage_delta t (Fin.last (t+1))]

end

end Work.SSSR
