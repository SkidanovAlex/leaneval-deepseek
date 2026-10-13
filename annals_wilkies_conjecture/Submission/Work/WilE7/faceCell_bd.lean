import Mathlib
import Submission.Work.WilE7.faceCell_star
import Submission.Work.WilE7.semiPf_normalize_exists
import Submission.Work.WilE7.FaceAux.insertCoord_component
import Submission.Work.WilE8.Extend.semipf_deg_extend

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E

/-! ## Degree bookkeeping for `addEq` and `insertCoord`

Adjoining one equation `Q = 0` to every branch of `X` adds `atomDeg Q` to each branch degree,
so the total degree of `addEq X Q` is `X.deg + X.basics.length * atomDeg Q`.  For the pinning
equation `pinPoly` this adds at most `2` per branch, and the number of branches can be assumed
bounded by `X.deg + 1` (`semiPf_normalize_exists`). -/

/-- Adjoining `Q` to the equations of a single basic set adds `atomDeg Q` to its degree. -/
theorem basic_cons_deg {k r : ℕ} (B : Basic k r) (Q : EAPoly k r) :
    (⟨B.eqs ++ [Q], B.pos⟩ : Basic k r).deg = B.deg + atomDeg Q := by
  simp only [Basic.deg, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  ring

/-- The list form of `addEq_deg`. -/
theorem addEq_deg_list {k r : ℕ} (l : List (Basic k r)) (Q : EAPoly k r) :
    (l.map (fun B => (⟨B.eqs ++ [Q], B.pos⟩ : Basic k r).deg)).sum
      = (l.map Basic.deg).sum + l.length * atomDeg Q := by
  induction l with
  | nil => simp
  | cons B t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [basic_cons_deg B Q, ih]
    ring

/-- Degree of `addEq`: each of the `X.basics.length` branches gains `atomDeg Q`. -/
theorem addEq_deg {k : ℕ} (X : SemiPf k) (Q : EAPoly k X.r) :
    (FaceAux.addEq X Q).deg = X.deg + X.basics.length * atomDeg Q := by
  simp only [SemiPf.deg, FaceAux.addEq, List.map_map]
  exact addEq_deg_list X.basics Q

/-- The pinning equation has atom degree at most `2`. -/
theorem atomDeg_pinPoly_le {p q r : ℕ} (t : ℝ) :
    atomDeg (FaceAux.pinPoly p q r t) ≤ 2 := by
  have h : (FaceAux.pinPoly p q r t).totalDegree ≤ 1 := by
    have := MvPolynomial.totalDegree_sub_C_le
      (MvPolynomial.X (Sum.inl (FaceAux.newIdx p q)) : EAPoly (p + 1 + q) r) t
    simpa only [FaceAux.pinPoly, MvPolynomial.totalDegree_X] using this
  simp only [atomDeg]
  omega

/-- The format of the pinned extension grows by exactly one. -/
theorem insertCoord_fmt {p q : ℕ} (X : SemiPf (p + q)) (t : ℝ) :
    (FaceAux.insertCoord X t).fmt = X.fmt + 1 := by
  rw [FaceAux.insertCoord, FaceAux.addEq_fmt]
  show (p + 1 + q) + X.r = (p + q) + X.r + 1
  omega

/-- The degree of the pinned extension is at most `X.deg + 2 * X.basics.length`. -/
theorem insertCoord_deg_le {p q : ℕ} (X : SemiPf (p + q)) (t : ℝ) :
    (FaceAux.insertCoord X t).deg ≤ X.deg + X.basics.length * 2 := by
  have hdeg : (FaceAux.insertCoord X t).deg
      = (FaceAux.extendP X).deg
        + (FaceAux.extendP X).basics.length
            * atomDeg (FaceAux.pinPoly p q (FaceAux.extendP X).r t) := by
    rw [FaceAux.insertCoord]; exact addEq_deg _ _
  have hext : (FaceAux.extendP X).deg = X.deg := by
    rw [FaceAux.extendP]
    exact Work.WilE8.Extend.semipf_deg_extend (Work.WilE8.Star.skipInj_injective p q) X
  have hlen : (FaceAux.extendP X).basics.length = X.basics.length := by
    simp only [FaceAux.extendP, Work.WilE8.SemiPf.extend, List.length_map]
  have hpin : atomDeg (FaceAux.pinPoly p q (FaceAux.extendP X).r t) ≤ 2 :=
    atomDeg_pinPoly_le t
  rw [hdeg, hext, hlen]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hpin) _

theorem faceCell_bd (F : ℕ) :
    ∃ (A : ℕ) (Cb : Polynomial ℕ), ∀ (p m : ℕ) (Z : WilkiesDesign.E.SemiPf (p + (m + 1)))
      (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set) (C : Set (Fin p → ℝ))
      (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
      (hCpf : WilkiesDesign.E.SubPf p C) (t : ℝ) (ht : |t| ≤ 1) (D : ℕ),
      Z.fmt ≤ F → Z.deg ≤ D →
      ∃ P : WilkiesDesign.E.StarPiece (p + 1),
        P.set = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = t} ∧
        P.X.fmt ≤ A ∧ P.X.deg ≤ Cb.eval D := by
  refine ⟨F + 1, Polynomial.C 3 * Polynomial.X + Polynomial.C 2, ?_⟩
  intro p m Z u₀ hu₀ C hC hCpf t ht D hfmt hdeg
  -- normalise `Z` so that the number of branches is at most `deg + 1`
  obtain ⟨Z', hZ'set, hZ'fmt, hZ'deg, hZ'len⟩ := semiPf_normalize_exists Z
  have hu₀' : u₀ ∈ Z'.set := by rw [hZ'set]; exact hu₀
  refine ⟨⟨m + 1, FaceAux.insertCoord Z' t, Work.WilE8.Star.insCoord p (m + 1) u₀ t⟩,
    ?_, ?_, ?_⟩
  · -- the set of the piece is the face cell
    show WilkiesDesign.E.projFirst (p + 1) (m + 1) ''
        connectedComponentIn (FaceAux.insertCoord Z' t).set
          (Work.WilE8.Star.insCoord p (m + 1) u₀ t)
        = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = t}
    rw [FaceAux.insertCoord_component Z' u₀ hu₀' ht]
    have hcomp : WilkiesDesign.E.projFirst p (m + 1) '' connectedComponentIn Z'.set u₀ = C := by
      rw [hC, hZ'set]
    rw [hcomp]
  · -- format
    show (FaceAux.insertCoord Z' t).fmt ≤ F + 1
    rw [insertCoord_fmt, hZ'fmt]
    omega
  · -- degree
    show (FaceAux.insertCoord Z' t).deg ≤ (Polynomial.C 3 * Polynomial.X + Polynomial.C 2).eval D
    have hb : (FaceAux.insertCoord Z' t).deg ≤ Z'.deg + Z'.basics.length * 2 :=
      insertCoord_deg_le Z' t
    have hev : (Polynomial.C 3 * Polynomial.X + Polynomial.C 2).eval D = 3 * D + 2 := by
      simp
    rw [hev]
    have hD : Z'.deg ≤ D := le_trans hZ'deg hdeg
    have hmul : Z'.basics.length * 2 ≤ (Z'.deg + 1) * 2 := Nat.mul_le_mul_right 2 hZ'len
    omega

end Work.WilE7
