/-
  Area E7, item 2: the **face cell** of a cell at a constant level.

  Given a `*`-set `C ⊆ ℝ^p` presented as the projection of the connected component of a
  semi-Pfaffian set `Z ⊆ ℝ^{p+(m+1)}` through `u₀`, and presented again as a sub-Pfaffian set
  (`hCpf`), the *face* of `C` at the level `t ∈ [-1,1]`,

    `C_t = {y : Fin (p+1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = t}`,

  is a `*`-set and a sub-Pfaffian set, with bounds independent of `D` and `F`.

  Both halves are unconditional in `F`, `D` (so `a` and `c` may be taken to be the format and
  the (constant polynomial of the) degree of the constructed semi-Pfaffian set):

  * `SubPf`: this is `FaceAux.subPf_insertCoord` — `C` is the projection of a semi-Pfaffian
    set `X`, and `C_t` is the projection of its pinned extension `insertCoord X t`, which is a
    semi-Pfaffian set of one more ambient dimension and the same chain.
  * `Star`: the `*`-piece is `⟨m+1, insertCoord Z t, insCoord p (m+1) u₀ t⟩`.  Its connected
    component through the pinned point projects onto `C_t` (`FaceAux.insertCoord_component`),
    by the preconnectedness of `insCoord p (m+1) · t '' connectedComponentIn Z.set u₀`.

  The two auxiliary facts live in `FaceAux.InsertCoord`, `FaceAux.insertCoord_component` and
  `FaceAux.subPf_insertCoord`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.FaceAux.InsertCoord
import Submission.Work.WilE7.FaceAux.insertCoord_component
import Submission.Work.WilE7.FaceAux.subPf_insertCoord

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E

theorem faceCell_star {p m : ℕ} (Z : WilkiesDesign.E.SemiPf (p + (m + 1)))
    (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set) (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (hCpf : WilkiesDesign.E.SubPf p C) (t : ℝ) (ht : |t| ≤ 1) :
    ∃ (a : ℕ) (c : Polynomial ℕ), ∀ D F : ℕ, Z.fmt ≤ F → Z.deg ≤ D →
      WilkiesDesign.E.Star a (c.eval D) (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = t} ∧
      WilkiesDesign.E.SubPf (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = t} := by
  classical
  -- the `SubPf` half: the pinned extension of a presentation of `C`
  have hsub : WilkiesDesign.E.SubPf (p + 1)
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = t} :=
    FaceAux.subPf_insertCoord C ht hCpf
  -- the `*`-piece
  set Q : StarPiece (p + 1) :=
    ⟨m + 1, FaceAux.insertCoord Z t, Work.WilE8.Star.insCoord p (m + 1) u₀ t⟩ with hQdef
  -- its set is the face cell
  have hQset : Q.set = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = t} := by
    rw [hQdef]
    show WilkiesDesign.E.projFirst (p + 1) (m + 1) ''
        connectedComponentIn (FaceAux.insertCoord Z t).set
          (Work.WilE8.Star.insCoord p (m + 1) u₀ t) = _
    rw [FaceAux.insertCoord_component Z u₀ hu₀ ht, hC]
  -- the `Star` presentation
  have hstar : WilkiesDesign.E.Star Q.X.fmt Q.X.deg (p + 1)
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = t} := by
    refine ⟨[Q], ?_, ?_, ?_⟩
    · rw [show (⋃ P ∈ ([Q] : List (StarPiece (p + 1))), P.set) = Q.set from by
        ext x
        simp]
      exact hQset.symm
    · intro P hP
      rw [List.mem_singleton] at hP
      subst hP
      exact le_rfl
    · simp
  exact ⟨Q.X.fmt, Polynomial.C Q.X.deg, fun D F _ _ => ⟨by simpa using hstar, hsub⟩⟩

end Work.WilE7
