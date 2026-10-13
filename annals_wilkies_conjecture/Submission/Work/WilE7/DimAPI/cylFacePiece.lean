import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.faceCell_bd
import Submission.Work.WilE7.FaceAux.insertCoord_component
import Submission.Work.WilE7.FaceAux.subPf_insertCoord

namespace Work.WilE7.DimAPI

theorem cylFacePiece (F : ℕ) :
    ∃ (A : ℕ) (Cb : Polynomial ℕ),
      ∀ (p M : ℕ) (Z : WilkiesDesign.E.SemiPf (p + M)) (u₀ : Fin (p + M) → ℝ)
        (hu₀ : u₀ ∈ Z.set) (C : Set (Fin p → ℝ))
        (hC : C = Set.image (WilkiesDesign.E.projFirst p M) (connectedComponentIn Z.set u₀))
        (hCpf : WilkiesDesign.E.SubPf p C) (t : ℝ) (ht : |t| ≤ 1) (D : ℕ),
        Z.fmt ≤ F → Z.deg ≤ D →
        (∃ P : WilkiesDesign.E.StarPiece (p + 1),
          P.set = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = t} ∧
          P.X.fmt ≤ A ∧ P.X.deg ≤ Cb.eval D) ∧
        WilkiesDesign.E.SubPf (p + 1)
          {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = t} := by
  refine ⟨F + 1, Polynomial.C 3 * Polynomial.X + Polynomial.C 2, ?_⟩
  intro p M Z u₀ hu₀ C hC hCpf t ht D hfmt hdeg
  -- normalise `Z` so that the number of branches is at most `deg + 1`
  obtain ⟨Z', hZ'set, hZ'fmt, hZ'deg, hZ'len⟩ := semiPf_normalize_exists Z
  have hu₀' : u₀ ∈ Z'.set := by rw [hZ'set]; exact hu₀
  refine ⟨⟨⟨M, FaceAux.insertCoord Z' t, Work.WilE8.Star.insCoord p M u₀ t⟩, ?_, ?_, ?_⟩, ?_⟩
  · -- the set of the piece is the face cell
    show WilkiesDesign.E.projFirst (p + 1) M ''
        connectedComponentIn (FaceAux.insertCoord Z' t).set
          (Work.WilE8.Star.insCoord p M u₀ t)
        = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = t}
    rw [FaceAux.insertCoord_component Z' u₀ hu₀' ht]
    have hcomp : WilkiesDesign.E.projFirst p M '' connectedComponentIn Z'.set u₀ = C := by
      rw [hC, hZ'set]
    rw [hcomp]
  · -- format
    show (FaceAux.insertCoord Z' t).fmt ≤ F + 1
    rw [insertCoord_fmt, hZ'fmt]
    omega
  · -- degree
    show (FaceAux.insertCoord Z' t).deg
        ≤ (Polynomial.C 3 * Polynomial.X + Polynomial.C 2).eval D
    have hb : (FaceAux.insertCoord Z' t).deg ≤ Z'.deg + Z'.basics.length * 2 :=
      insertCoord_deg_le Z' t
    have hev : (Polynomial.C 3 * Polynomial.X + Polynomial.C 2).eval D = 3 * D + 2 := by
      simp
    rw [hev]
    have hD : Z'.deg ≤ D := le_trans hZ'deg hdeg
    have hmul : Z'.basics.length * 2 ≤ (Z'.deg + 1) * 2 := Nat.mul_le_mul_right 2 hZ'len
    omega
  · -- the `SubPf` half
    exact FaceAux.subPf_insertCoord C ht hCpf

end Work.WilE7.DimAPI
