import Mathlib
import Submission.Work.SSS.serreE1EZ
import Submission.Work.SSS.serreE1PieceDefs
import Submission.Work.SSS.hornSimp_preimage_delta_last
import Submission.Work.KunnethEZ.EZGenX

/-!
# The `aMap23`-image of a proper face of the fundamental simplex lies in the horn

`Work.SSS.hornSimp s` is the `s`-th horn `Λ[s, s]`, the union of all faces of `Δ[s]` except the
last one; a simplex of `Δ[s]` lies in it exactly when its underlying monotone map misses some
vertex `j ≠ Fin.last s` (`Work.SSS.hornSimp_eq_horn_last` + `SSet.mem_horn_iff_notMem_range`).

The fundamental `(t+1)`-simplex `stdIdSimplex (t+1)` has underlying monotone map the identity, so
its `i`-th face `(Δ[t+1]).δ i (stdIdSimplex (t+1))` has underlying map `Fin.succAbove i`, whose
range omits exactly `i`.  Precomposing with any monotone map (here the `E`-count map
`Work.KunnethEZ.aMap23 (t+1) (Q+1) T`) only shrinks the range, so the composite still misses `i`;
as soon as `i ≠ Fin.last (t+1)` this exhibits a missing vertex other than the last one, i.e.
membership in the horn.
-/

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial

theorem hornSimp_aMap23_mem (t Q : ℕ) (T : Work.KunnethEZ.Sh23 (t+1) (Q+1)) (i : Fin (t+2))
    (hi : i ≠ Fin.last (t+1)) :
    (Δ[t+1] : SSet).map (Work.KunnethEZ.aMap23 (t+1) (Q+1) T).op
        ((Δ[t+1] : SSet).δ i (Work.SSS.stdIdSimplex (t+1)))
      ∈ (Work.SSS.hornSimp (t+1)).obj (op ⦋(t+1)+(Q+1)-1⦌) := by
  rw [Work.SSS.hornSimp_eq_horn_last, SSet.mem_horn_iff_notMem_range]
  refine ⟨i, hi, ?_⟩
  rintro ⟨k, hk⟩
  -- The `i`-th face of the identity simplex is the coface `δ i`, whose underlying map is
  -- `Fin.succAbove i`.
  have h1 : ((Δ[t+1] : SSet).δ i (Work.SSS.stdIdSimplex (t+1)))
      = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i) := by
    rw [Work.SSS.stdIdSimplex, SSet.stdSimplex.δ_objEquiv_symm_apply]
    simp
  -- Precomposing with `aMap23` postcomposes the underlying monotone maps.
  have hk' : ⇑((Δ[t+1] : SSet).map (Work.KunnethEZ.aMap23 (t+1) (Q+1) T).op
        ((Δ[t+1] : SSet).δ i (Work.SSS.stdIdSimplex (t+1)))) k
      = Fin.succAbove i (⇑(Work.KunnethEZ.aMap23 (t+1) (Q+1) T) k) := by
    rw [h1, SSet.stdSimplex.map_apply]
    simp only [Equiv.apply_symm_apply, Opposite.unop_op]
    rw [SSet.stdSimplex.objEquiv_symm_apply, SimplexCategory.comp_toOrderHom]
    rfl
  rw [hk'] at hk
  exact Fin.succAbove_ne i (⇑(Work.KunnethEZ.aMap23 (t+1) (Q+1) T) k) hk

end Work.SSS
