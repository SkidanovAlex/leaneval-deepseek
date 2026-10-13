/-
  Area E7, item 2 (first half), **restated and closed**: the graph cells are `*`-sets **and**
  sub-Pfaffian.

  This is the corrected form of the statement in `Submission/Work/WilE7/graphCell_star.lean`
  (kept as the record; its `SubPf` conjunct was declared mis-stated by an independent prover,
  see that file's STATUS docstring).  Three changes, all from the review and the prover's
  finding:

  * the polynomial `c` is quantified **before** the degree bound `D` (`∃ a c, ∀ D F, …`), so `c`
    cannot depend on `D` and the bound is the `poly_F(D)` the target needs;
  * the base cell carries its own `SubPf p C` presentation (`hCpf`), which the induction supplies
    (`SubPf (p+1) Γ_j` implies `SubPf p C`, and the component-form `hC` cannot give that);
  * the `SubPf` half carries `hcomp` — *connected components of semi-Pfaffian sets are
    sub-Pfaffian* — the precise missing input, and a new named input of the E7 induction
    (`E7main_DESIGN.md` item 2).  It is independent of the dimension theory and of `hFC`.

  Both halves were already proved sorry-free in `GraphCellAux`; this file is their assembly.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.GraphCellAux.graphCellStar_star
import Submission.Work.WilE7.GraphCellAux.graphCellStar_subPf_of_comp

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesDesign WilkiesDesign.E

/-- **The graph cell of a sheet is a `*`-set and a sub-Pfaffian set.**  Under the sheet data of
`Work.WilE7.sheetAssembly` (base cell presented by a component, plus its own `SubPf`
presentation `hCpf`) and the component hypothesis `hcomp`, the graph cell
`Γ_j = {y | Fin.init y ∈ C ∧ y (Fin.last p) = (s j (Fin.init y)) (Fin.last m)}` is
`Star a (c.eval D) (p+1)` and `SubPf (p+1)`, with `a`, `c` independent of `D`. -/
theorem graphCell_star_proved
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
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z)
    (hcomp : ∀ {n : ℕ} (X : WilkiesDesign.E.SemiPf n) (x : Fin n → ℝ),
      WilkiesDesign.E.SubPf n (connectedComponentIn X.set x))
    (j : Fin k) :
    ∃ (a : ℕ) (c : Polynomial ℕ), ∀ (D F : ℕ),
      S.X.fmt ≤ F → S.deg ≤ D → Z.fmt ≤ F → Z.deg ≤ D →
      WilkiesDesign.E.Star a (c.eval D) (p + 1)
        {y : Fin (p + 1) → ℝ |
          Fin.init y ∈ C ∧ y (Fin.last p) = (s j (Fin.init y)) (Fin.last m)} ∧
      WilkiesDesign.E.SubPf (p + 1)
        {y : Fin (p + 1) → ℝ |
          Fin.init y ∈ C ∧ y (Fin.last p) = (s j (Fin.init y)) (Fin.last m)} := by
  obtain ⟨a, c, hstar⟩ :=
    GraphCellAux.graphCellStar_star S hGood hj Z u₀ hu₀ C hC hCpf k s hcont hinj hsub hcov j
  refine ⟨a, c, fun D F hF hD hZF hZD => ⟨hstar D F hF hD hZF hZD, ?_⟩⟩
  exact GraphCellAux.graphCellStar_subPf_of_comp S hGood hj Z u₀ hu₀ C hC hCpf k s
    hcont hinj hsub hcov hcomp j

end Work.WilE7
