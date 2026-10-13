import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.reindex_component

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE7

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-!
# Dropping the last coordinate of a `*`-piece

`StarPiece.init P` for `P : StarPiece (N + 1)` is the `*`-piece in `N` variables obtained by
forgetting the `N`-th spatial coordinate: the semi-Pfaffian part of `P` (a set in
`ℝ^{(N+1)+m}`) is re-indexed along the value-preserving equivalence
`Fin ((N+1)+m) ≃ Fin (N+(m+1))`, the fibre dimension becomes `m+1`, and the base point is
transported.

This file proves `(StarPiece.init P).set = Fin.init '' P.set`: the connected component of the
re-indexed set projects (in the first `N` coordinates) exactly onto the projection of the
connected component of `P`, with the last spatial coordinate dropped.

The transport of connected components along the re-indexing is
`Work.WilE7.reindex_component` (from `Submission.Work.WilE7.reindex_component`); what remains is
the `Fin`-arithmetic identifying the two projections, which is `init_projFin` below.
-/

/-! ## Index arithmetic -/

/-- `finEquiv h` is value preserving, so it sends the `i`-th "old" index of the first `n`
coordinates to the `i`-th "new" one. -/
theorem init_finEquiv_castAdd_castSucc {N m : ℕ} (h : (N + 1) + m = N + (m + 1))
    (i : Fin N) :
    finEquiv h (Fin.castAdd m (Fin.castSucc i)) = Fin.castAdd (m + 1) i :=
  Fin.ext (by simp [finEquiv_apply_val])

/-- The inverse direction of the previous identity. -/
theorem init_finEquiv_symm_castAdd {N m : ℕ} (h : (N + 1) + m = N + (m + 1))
    (i : Fin N) :
    (finEquiv h).symm (Fin.castAdd (m + 1) i) = Fin.castAdd m (Fin.castSucc i) := by
  apply (finEquiv h).injective
  rw [Equiv.apply_symm_apply, init_finEquiv_castAdd_castSucc]

/-! ## Dropping the last coordinate commutes with the re-indexing -/

/-- Projecting a re-indexed set to its first `N` coordinates is the same as projecting the
original set to its first `N + 1` coordinates and dropping the last one. -/
theorem init_projFin {N m : ℕ} (h : (N + 1) + m = N + (m + 1))
    (S : Set (Fin ((N + 1) + m) → ℝ)) :
    projFirst N (m + 1) '' {y : Fin (N + (m + 1)) → ℝ | (fun i => y (finEquiv h i)) ∈ S}
      = Fin.init '' (projFirst (N + 1) m '' S) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨projFirst (N + 1) m (fun i => y (finEquiv h i)),
      ⟨(fun i => y (finEquiv h i)), hy, rfl⟩, ?_⟩
    funext i
    show y (finEquiv h (Fin.castAdd m (Fin.castSucc i))) = y (Fin.castAdd (m + 1) i)
    rw [init_finEquiv_castAdd_castSucc]
  · rintro ⟨w, ⟨x, hx, rfl⟩, hwz⟩
    rw [← hwz]
    refine ⟨(fun j => x ((finEquiv h).symm j)), ?_, ?_⟩
    · have hfun : (fun i => x ((finEquiv h).symm ((finEquiv h) i))) = x := by
        funext i
        simp
      show (fun i => x ((finEquiv h).symm ((finEquiv h) i))) ∈ S
      rw [hfun]
      exact hx
    · funext i
      show x ((finEquiv h).symm (Fin.castAdd (m + 1) i)) = x (Fin.castAdd m (Fin.castSucc i))
      rw [init_finEquiv_symm_castAdd]

/-! ## The statement -/

/-- The set of the `*`-piece obtained by dropping the last spatial coordinate, stated for an
explicitly written structural representative (so that the `Fin` arithmetic is transparent). -/
theorem init_set_lit {N : ℕ} (P : WilkiesDesign.E.StarPiece (N + 1))
    (h : (N + 1) + P.m = N + (P.m + 1)) :
    (⟨P.m + 1, SemiPf.reindex (finEquiv h) P.X, fun i => P.p ((finEquiv h).symm i)⟩ :
        WilkiesDesign.E.StarPiece N).set = Fin.init '' P.set := by
  have hstep : connectedComponentIn (SemiPf.reindex (finEquiv h) P.X).set
        (fun i => P.p ((finEquiv h).symm i))
      = {y : Fin (N + (P.m + 1)) → ℝ |
          (fun i => y (finEquiv h i)) ∈ connectedComponentIn P.X.set P.p} :=
    reindex_component (finEquiv h) P.X P.p
  simp only [WilkiesDesign.E.StarPiece.set]
  rw [hstep]
  exact init_projFin h _

theorem init_set {N : ℕ} (P : WilkiesDesign.E.StarPiece (N + 1)) :
    (Work.WilE7.StarPiece.init P).set = Fin.init '' P.set := by
  have h : (N + 1) + P.m = N + (P.m + 1) := by omega
  have hinit : Work.WilE7.StarPiece.init P
      = ⟨P.m + 1, SemiPf.reindex (finEquiv h) P.X, fun i => P.p ((finEquiv h).symm i)⟩ := by
    have hfin : ∀ (h' : (N + 1) + P.m = N + (P.m + 1)), finEquiv h' = finEquiv h :=
      fun h' => Equiv.ext fun i => Fin.ext (by simp only [Work.WilE7.finEquiv_apply_val])
    simp only [Work.WilE7.StarPiece.init, hfin]
  rw [hinit]
  exact init_set_lit P h

end Work.WilE7
