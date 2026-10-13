import Mathlib
import Submission.Work.WilE7.SheetData.multiStrata_cellsX_aux
import Submission.Work.WilE7.SheetData.graphCellSubPfX

namespace Work.WilE7.SheetData

/-- **The graph over `C` of the level of a sheet is a single `*`-piece and sub-Pfaffian.**

Sheet data of a semi-Pfaffian set `X ⊆ ℝ^{p+(m+1)}` over the cell
`C = π_p (connectedComponentIn Z.set u₀)`: continuous sheets `s j : C → ℝ^{m+1}` whose graphs over
`C` are exactly the fibre of `X.set` (`hsub` + `hcov`), pairwise distinct over `C` (`hinj`), with
levels non-decreasing in `j` on `C` (`hmono`).  If `f` is the level of one of the sheets on `C`,
then the graph `{y : π_p y ∈ C, y (last p) = f (π_p y)}` is a single `*`-piece with format `≤ A`
and `*`-degree `≤ Cb.eval D` whenever `X.fmt, Z.fmt ≤ F` and `X.deg, Z.deg ≤ D`, and it is
sub-Pfaffian.

(The `*`-piece half is `graphCellStarX`; the sub-Pfaffian half is `graphCellSubPfX` with the fibre
cardinality `hcard` supplied by `fiber_ncard_eq_of_sheets` and the monotonicity `hmono`.) -/
theorem graphCellTT (F : ℕ) :
    ∃ (A : ℕ) (Cb : Polynomial ℕ),
      ∀ (p m : ℕ) (X : WilkiesDesign.E.SemiPf (p + (m + 1)))
        (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ)
        (hu₀ : u₀ ∈ Z.set) (C : Set (Fin p → ℝ))
        (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1))
          (connectedComponentIn Z.set u₀))
        (hCpf : WilkiesDesign.E.SubPf p C)
        (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
        (hcont : ∀ j : Fin k, ContinuousOn (s j) C)
        (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
        (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ X.set)
        (hcov : ∀ z ∈ X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
          ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) =
            WilkiesDesign.E.projSnd p (m + 1) z)
        (hmono : ∀ x ∈ C, Monotone fun j : Fin k => (s j x) (Fin.last m))
        (f : (Fin p → ℝ) → ℝ)
        (hwit : ∃ j : Fin k, ∀ x ∈ C, f x = (s j x) (Fin.last m))
        (D : ℕ)
        (hXF : X.fmt ≤ F) (hXD : X.deg ≤ D) (hZF : Z.fmt ≤ F) (hZD : Z.deg ≤ D),
      (∃ P : WilkiesDesign.E.StarPiece (p + 1),
          P.set = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = f (Fin.init y)} ∧
          P.X.fmt ≤ A ∧ P.X.deg ≤ Cb.eval D) ∧
      WilkiesDesign.E.SubPf (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = f (Fin.init y)} := by
  obtain ⟨A, Cb, hStar⟩ := graphCellStarX F
  refine ⟨A, Cb, ?_⟩
  intro p m X Z u₀ hu₀ C hC hCpf k s hcont hinj hsub hcov hmono f hwit D hXF hXD hZF hZD
  -- the witness index: `f` is the level of the `j₀`-th sheet on `C`
  obtain ⟨j₀, hf⟩ := hwit
  -- the fibre cardinality hypothesis of `graphCellSubPfX`
  have hcard : ∀ x ∈ C, (WilkiesDesign.E.fiber X.set x).ncard = k :=
    fun x hx => fiber_ncard_eq_of_sheets hinj hsub hcov x hx
  -- the graph of `f` is the graph of the `j₀`-th sheet on `C`
  have hset : {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = f (Fin.init y)}
      = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
          y (Fin.last p) = (s j₀ (Fin.init y)) (Fin.last m)} := by
    ext y
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2.trans (hf (Fin.init y) h1)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2.trans (hf (Fin.init y) h1).symm⟩
  constructor
  · -- the `*`-piece half
    obtain ⟨P, hPset, hPfmt, hPdeg⟩ :=
      hStar p m X Z u₀ hu₀ C hC hCpf k s hcont hinj hsub hcov j₀ D hXF hZF hXD hZD
    rw [hset]
    exact ⟨P, hPset, hPfmt, hPdeg⟩
  · -- the sub-Pfaffian half
    rw [hset]
    exact graphCellSubPfX X C hCpf k s hinj hsub hcov hcard hmono j₀

end Work.WilE7.SheetData
