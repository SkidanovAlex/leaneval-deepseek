import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.SheetData.DefsX
import Submission.Work.WilE7.SheetData.sheetComponentX
import Submission.Work.WilE7.fiberProduct_semiPf
import Submission.Work.WilE7.reindex_component
import Submission.Work.WilE7.star_proj
import Submission.Work.WilE7.imageSubsetConnectedComponentIn
import Submission.Work.WilE7.GraphCellAux.graphCellStar_star

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical
open WilkiesDesign WilkiesDesign.E

namespace Work.WilE7.SheetData

/-- **The graph cell of one sheet is a single `*`-piece.**

This is `Work.WilE7.graphCellStar_piece` (`Submission/Work/WilE7/graphCell_bd.lean`) with the
`Good` stratum `S` replaced by its underlying semi-Pfaffian set `X`: the sheet-component lemma
`Work.WilE7.sheetComponentGen` uses the stratum only through `S.X`, so the whole fibre-product
proof goes through with `X` in place of `S.X`. -/
theorem graphCellStar_piece {p m : ℕ} (X : WilkiesDesign.E.SemiPf (p + (m + 1)))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (hCpf : WilkiesDesign.E.SubPf p C)
    (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ X.set)
    (hcov : ∀ z ∈ X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) = WilkiesDesign.E.projSnd p (m + 1) z)
    (j : Fin k) :
    ∃ P : WilkiesDesign.E.StarPiece (p + 1),
      P.set = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        y (Fin.last p) = (s j (Fin.init y)) (Fin.last m)} ∧
      P.X.fmt ≤ 2 * max X.fmt Z.fmt ∧
      P.X.deg ≤ 2 * (1 + max X.fmt Z.fmt) * (1 + (Z.deg + X.deg)) ^ 2 := by
  classical
  obtain ⟨e, he⟩ := Work.WilE7.GraphCellAux.graphProj_perm p m
  obtain ⟨hsheet, hcover⟩ :=
    sheetComponentX X Z u₀ hu₀ C hC k s hcont hinj hsub hcov j
  have hbase : ∀ z ∈ connectedComponentIn (sheetProductX p (m + 1) Z X)
        (Work.WilE7.sheetProductPt u₀ s j),
      projFirst p (m + 1) (projFirst (p + (m + 1)) (p + (m + 1)) z) ∈ C :=
    sheetProductX_base_mem X Z u₀ hu₀ C hC s j
  set W : WilkiesDesign.E.SemiPf ((p + (m + 1)) + (p + (m + 1))) :=
    Work.WilE7.fiberProdZ Z X with hW
  set w₀ : Fin ((p + (m + 1)) + (p + (m + 1))) → ℝ :=
    Work.WilE7.sheetProductPt u₀ s j with hw₀
  set O : Set (Fin ((p + (m + 1)) + (p + (m + 1))) → ℝ) :=
    connectedComponentIn (sheetProductX p (m + 1) Z X) w₀ with hO
  have hWset : W.set = sheetProductX p (m + 1) Z X := by
    rw [hW]
    exact (sheetProductX_eq_fiberProdZ_set p (m + 1) Z X).symm
  -- the `*`-piece: the reindexed fibre product, based at the reindexed base point
  set P : WilkiesDesign.E.StarPiece (p + 1) :=
    ⟨(p + (m + 1)) + m, Work.WilE7.SemiPf.reindex e W,
      (Work.WilE7.pullHomeo e).symm w₀⟩ with hP
  have hkey : ∀ y : Fin ((p + 1) + ((p + (m + 1)) + m)) → ℝ,
      projFirst (p + 1) ((p + (m + 1)) + m) y
        = Work.WilE7.GraphCellAux.graphProj (Work.WilE7.pullHomeo e y) := by
    intro y
    rw [he y, Work.WilE7.pullHomeo_apply]
    rfl
  -- the piece's set is the image of the component under `graphProj`
  have hPset : P.set = Work.WilE7.GraphCellAux.graphProj '' O := by
    have hcomp := Work.WilE7.sp_reindex_component e W w₀
    rw [hP]
    show projFirst (p + 1) ((p + (m + 1)) + m) ''
        connectedComponentIn (Work.WilE7.SemiPf.reindex e W).set
          ((Work.WilE7.pullHomeo e).symm w₀)
        = Work.WilE7.GraphCellAux.graphProj '' O
    rw [hcomp, hWset, ← hO]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨Work.WilE7.pullHomeo e y, hy, (hkey y).symm⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(Work.WilE7.pullHomeo e).symm z, ?_, ?_⟩
      · rw [Set.mem_preimage, Homeomorph.apply_symm_apply]
        exact hz
      · rw [hkey, Homeomorph.apply_symm_apply]
  -- `graphProj` maps the component onto the graph cell
  have hG : Work.WilE7.GraphCellAux.graphProj '' O
      = {y : Fin (p + 1) → ℝ |
          Fin.init y ∈ C ∧ y (Fin.last p) = (s j (Fin.init y)) (Fin.last m)} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzW : z ∈ sheetProductX p (m + 1) Z X :=
        connectedComponentIn_subset (sheetProductX p (m + 1) Z X) w₀ hz
      obtain ⟨-, -, hzdiag⟩ := mem_sheetProductX.mp hzW
      refine ⟨?_, ?_⟩
      · rw [Work.WilE7.GraphCellAux.graphProj_init]
        exact hbase z hz
      · rw [Work.WilE7.GraphCellAux.graphProj_last, Work.WilE7.GraphCellAux.graphProj_init,
          hsheet z hz, ← hzdiag]
    · rintro ⟨hinit, hlast⟩
      obtain ⟨z, hzO, hzx⟩ := hcover (Fin.init y) hinit
      have hzW : z ∈ sheetProductX p (m + 1) Z X :=
        connectedComponentIn_subset (sheetProductX p (m + 1) Z X) w₀ hzO
      obtain ⟨-, -, hzdiag⟩ := mem_sheetProductX.mp hzW
      refine ⟨z, hzO, ?_⟩
      have h1 : Fin.init (Work.WilE7.GraphCellAux.graphProj z) = Fin.init y := by
        rw [Work.WilE7.GraphCellAux.graphProj_init, hzdiag]
        exact hzx
      have h2 : Work.WilE7.GraphCellAux.graphProj z (Fin.last p) = y (Fin.last p) := by
        rw [Work.WilE7.GraphCellAux.graphProj_last, hsheet z hzO, hzx]
        exact hlast.symm
      calc Work.WilE7.GraphCellAux.graphProj z
            = Fin.snoc (Fin.init (Work.WilE7.GraphCellAux.graphProj z))
                (Work.WilE7.GraphCellAux.graphProj z (Fin.last p)) :=
            (Fin.snoc_init_self (Work.WilE7.GraphCellAux.graphProj z)).symm
        _ = Fin.snoc (Fin.init y) (y (Fin.last p)) := by rw [h1, h2]
        _ = y := Fin.snoc_init_self y
  have hPG : P.set = {y : Fin (p + 1) → ℝ |
      Fin.init y ∈ C ∧ y (Fin.last p) = (s j (Fin.init y)) (Fin.last m)} := hPset.trans hG
  have hfmt : P.X.fmt ≤ 2 * max X.fmt Z.fmt := by
    rw [hP]
    show (Work.WilE7.SemiPf.reindex e W).fmt ≤ 2 * max X.fmt Z.fmt
    have hre : (Work.WilE7.SemiPf.reindex e W).fmt = W.fmt := by
      simp only [Work.WilE7.SemiPf.reindex, WilkiesDesign.E.SemiPf.fmt]
      omega
    rw [hre]
    exact Work.WilE7.fiberProdZ_fmt Z X (le_max_right _ _) (le_max_left _ _)
  have hdeg : P.X.deg ≤ 2 * (1 + max X.fmt Z.fmt) * (1 + (Z.deg + X.deg)) ^ 2 := by
    rw [hP]
    show (Work.WilE7.SemiPf.reindex e W).deg ≤ _
    rw [Work.WilE7.sp_reindex_deg]
    exact Work.WilE7.fiberProdZ_deg Z X (le_max_right _ _)
  exact ⟨P, hPG, hfmt, hdeg⟩

end Work.WilE7.SheetData
