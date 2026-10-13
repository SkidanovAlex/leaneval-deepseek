/-
  `Work.WilE7.GraphCellAux.graphCellStar_subPf_of_comp`: the graph cell attached to one sheet
  `s j` is *sub-Pfaffian*, given the `SubPf`-track hypothesis that every connected component of a
  semi-Pfaffian set is sub-Pfaffian.

  The mathematical content is a three-step reduction, none of which needs the format/degree
  bookkeeping of `Star`:

  * `graphCellStar_star` (already proved) exhibits the graph cell
    `Γ_j = {y : Fin (p+1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = (s j (Fin.init y)) (Fin.last m)}`
    as a finite union `⋃ P ∈ L, P.set` of `*`-pieces `P : StarPiece (p+1)`;
  * each piece is, by definition of `StarPiece.set`, the projection `projFirst (p+1) P.m` of the
    connected component of `P.X.set` through `P.p`; that component is `SubPf` by the hypothesis
    `hcomp`, and `SubPf` is closed under dropping coordinates (`subPf_projFirst`).  So every
    `P.set` is sub-Pfaffian;
  * a finite union of sub-Pfaffian sets is sub-Pfaffian (`subPf_list_iUnion`).
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.sheetComponent
import Submission.Work.WilE7.fiberProduct_semiPf
import Submission.Work.WilE7.GraphCellAux.graphCellStar_star
import Submission.Work.WilE7.GraphCellAux.subPf_projFirst
import Submission.Work.WilE7.GraphCellAux.subPf_list_iUnion
import Submission.Work.WilE7.subPf_algebra

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE7.GraphCellAux

open WilkiesDesign WilkiesDesign.E

theorem graphCellStar_subPf_of_comp
    {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1)) (hGood : S.Good) (hj : S.j = m + 1)
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (hCpf : WilkiesDesign.E.SubPf p C)
    (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcov : ∀ z ∈ S.X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) = WilkiesDesign.E.projSnd p (m + 1) z)
    (hcomp : ∀ {n : ℕ} (X : WilkiesDesign.E.SemiPf n) (x : Fin n → ℝ),
      WilkiesDesign.E.SubPf n (connectedComponentIn X.set x))
    (j : Fin k) :
    WilkiesDesign.E.SubPf (p + 1)
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = (s j (Fin.init y)) (Fin.last m)} := by
  classical
  -- Step 1: the graph cell is a finite union of `*`-pieces (the `Star` presentation).
  obtain ⟨a, c, hstar⟩ :=
    graphCellStar_star S hGood hj Z u₀ hu₀ C hC hCpf k s hcont hinj hsub hcov j
  have hΓ : Star a (c.eval (S.deg + Z.deg)) (p + 1)
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = (s j (Fin.init y)) (Fin.last m)} :=
    hstar (S.deg + Z.deg) (S.X.fmt + Z.fmt) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨L, hL, -, -⟩ := hΓ
  rw [hL]
  -- Step 2 + 3: each piece is `SubPf` (a projected connected component), and a finite union of
  -- sub-Pfaffian sets is sub-Pfaffian.
  refine subPf_list_iUnion L (fun P => P.set) (fun P _ => ?_)
  exact subPf_projFirst (hcomp P.X P.p)

end Work.WilE7.GraphCellAux
