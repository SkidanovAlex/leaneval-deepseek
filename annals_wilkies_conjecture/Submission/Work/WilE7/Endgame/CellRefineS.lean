/-
  Area E7 / the `CoreLT_succ` endgame: **the refinement predicate `CellRefineS`**.

  ## The two defects of the plan's `CellRefine`, and their repairs

  `Work.WilE7.CoreLTSuccPlan.CellRefine n K` (the lead's plan, `sources/wilkiesE7end/`) demands, for
  every decomposition `B` of `cubeC (n+1)` compatible with the inner instance `(X', Y')`, a
  base-cell-by-base-cell refinement `B'`, with `Fin.init '' κ = b` for every `κ ∈ B'` and — in the
  non-`B`-subfamily branch — a `StarPiece (n+1)` presentation of every cell of `B'` of format `≤ a`
  and degree `≤ c.eval D`, where `a, c` are fixed *before* `D`, `B` and the families.

  **Defect 1 (S55).** The refinement clause assumed only that every cell of `B` *admits* a
  `StarPiece` presentation (`∃ P, P.set = κ`) and is `SubPf`.  Since

    `(StarPiece.init P).set = Fin.init '' P.set`            (`Work.WilE7.init_set`)

  a cell `κ' ∈ B'` with `Fin.init '' κ' = b` can only exist if `b` is the projection of a connected
  component of a semi-Pfaffian set; an arbitrary compatible `B` need not have base cells of that
  form.  Hence the extra hypothesis `∀ κ ∈ B, (∃ P, P.set = κ) ∧ SubPf (n+1) κ`: the datum the inner
  call `CoreLT n K` always provides.

  **Defect 2 (S56).** Even with Defect 1 repaired the statement is *false*: the presentation is
  supplied with **no bound on its format**.  Every producer of the cells over a base cell `b` in this
  workspace (`gcase_cfs`, `gcase_family`, `multiStrata_cellsX`, `bandCellTT`, `graphCellTT`) takes
  `b = projFirst n (m+1) '' connectedComponentIn Z.set u₀` **together with** `Z.fmt ≤ F₀`,
  `Z.deg ≤ D₀`, and returns its `StarPiece` presentations with a format `A(F₀)` and a degree
  `C(F₀).eval D₀` that *increase with `F₀`*.  Taking `Z := (StarPiece.init P).X` and
  `u₀ := (StarPiece.init P).p`, the produced format is `A(P.X.fmt)`: it cannot be bounded by a number
  chosen before `P` is known.  So no fixed `a` works for arbitrary presentations; the produced bounds
  must be functions of the presentation bounds.

  ## The repaired statement

  `CellRefineS n K` is `CellRefine` with

  * the presentation hypothesis carrying the bounds `P.X.fmt ≤ Fq`, `P.X.deg ≤ Qq.eval D`
    (`Fq, Qq` universally quantified *after* the inner instance's `F', P, Nk, Nl, Ng` and *before*
    the produced bounds, so that the latter may depend on them), and
  * the produced `StarPiece` bounds `AB : ℕ` and `CB : Polynomial ℕ` chosen *after* `Fq, Qq` (and
    *before* `D`), so that the produced format is `AB` and the produced degree is `CB.eval D`.

  In the application (`Work.WilE7.Endgame.coreLT_succ_of_cellRefineS`) the inner call
  `CoreLT n K` at format `F'` supplies precisely `Fq := ai`, `Qq := ci.comp P` — both fixed once
  `F'` is fixed — and the outer bounds are `max ai AB`, `(ci.comp P) + CB`.

  Note that `AB` and `CB` are chosen before `D` because that is what the construction gives: the
  *format* `A(max Fq Ac)` of the produced cells is independent of `D` (only the *degree* carries the
  `D`-dependence, and polynomially so).
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

/-- `CellRefineS n K`: the repaired refinement predicate of the `CoreLT_succ` endgame.

For every format bound `F` there are an inner instance `(F', P, Nk, Nl, Ng)` — format bound `F'`,
degree polynomial `P`, cardinality polynomials `Nk, Nl` for the families and `Ng` for the number of
new cells per base cell — such that for every bound `(Fq, Qq)` on the *presentations* of the cells of
the decomposition to be refined there are produced-cell bounds `(AB, CB)`, so that for every
`D k l m m'` and every pair of families `X, Y` (formats `≤ F`, degrees `≤ D`) with
`NullDimLT (basePr · (X i)) (K+1)`, the produced families `X', Y'` (formats `≤ F'`, degrees
`≤ P.eval D`, `NullDimLT (basePr · ) K`, `Y`-projections preserved, cardinality bounds) admit, for
every decomposition `B` of `cubeC (n+1)` compatible with `X'`, with `Y'` and with presentations of
its cells of format `≤ Fq` and degree `≤ Qq.eval D`, a per-base-cell refinement: for every
`b ∈ B.image (Fin.init '' ·)` a family `B'` decomposing `cubeC (n+1) ∩ {z | Fin.init z ∈ b}`, each
of whose cells projects onto `b`, which is compatible with the outer `X`, and which either is a
subfamily of `B` or consists of cells carrying single `StarPiece (n+1)` presentations of format
`≤ AB` and degree `≤ CB.eval D` (and which is `SubPf`), with at most `Ng.eval ![D,k,l]` cells. -/
def CellRefineS (n K : ℕ) : Prop :=
  ∀ F : ℕ, ∃ (F' : ℕ) (P : Polynomial ℕ) (Nk Nl Ng : MvPolynomial (Fin 3) ℕ),
    ∀ (Fq : ℕ) (Qq : Polynomial ℕ), ∃ (AB : ℕ) (CB : Polynomial ℕ),
    ∀ (D k l m m' : ℕ) (X : Fin k → SemiPf ((n + 1) + m)) (Y : Fin l → SemiPf (n + m')),
      (∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D) → (∀ i, (Y i).fmt ≤ F ∧ (Y i).deg ≤ D) →
      (∀ i, NullDimLT (basePr n m '' (X i).set) (K + 1)) →
      ∃ (k' l' m₁ m₂ : ℕ) (X' : Fin k' → SemiPf ((n + 1) + m₁)) (Y' : Fin l' → SemiPf (n + m₂)),
        k' ≤ MvPolynomial.eval ![D, k, l] Nk ∧ l' ≤ MvPolynomial.eval ![D, k, l] Nl ∧
        (∀ i, (X' i).fmt ≤ F' ∧ (X' i).deg ≤ P.eval D) ∧
        (∀ i, (Y' i).fmt ≤ F' ∧ (Y' i).deg ≤ P.eval D) ∧
        (∀ i, NullDimLT (basePr n m₁ '' (X' i).set) K) ∧
        (∀ j, ∃ j', projFirst n m' '' (Y j).set = projFirst n m₂ '' (Y' j').set) ∧
        ∀ B : Finset (Set (Fin (n + 1) → ℝ)), IsCylDecompOn (n + 1) (cubeC (n + 1)) B →
          (∀ i, ∀ κ ∈ B, κ ⊆ projFirst (n + 1) m₁ '' (X' i).set ∨
            Disjoint κ (projFirst (n + 1) m₁ '' (X' i).set)) →
          (∀ i, ∀ κ ∈ B, Fin.init '' κ ⊆ projFirst n m₂ '' (Y' i).set ∨
            Disjoint (Fin.init '' κ) (projFirst n m₂ '' (Y' i).set)) →
          (∀ κ ∈ B, (∃ P₀ : StarPiece (n + 1), P₀.set = κ ∧ P₀.X.fmt ≤ Fq ∧
              P₀.X.deg ≤ Qq.eval D) ∧ SubPf (n + 1) κ) →
          ∀ b ∈ B.image (fun κ => Fin.init '' κ), ∃ B' : Finset (Set (Fin (n + 1) → ℝ)),
            ((∀ κ ∈ B', κ ∈ B) ∨
              ((∀ κ ∈ B', (∃ P₀ : StarPiece (n + 1), P₀.set = κ ∧ P₀.X.fmt ≤ AB ∧
                  P₀.X.deg ≤ CB.eval D) ∧ SubPf (n + 1) κ) ∧
                B'.card ≤ MvPolynomial.eval ![D, k, l] Ng)) ∧
            IsCylDecompOn (n + 1) (cubeC (n + 1) ∩ {z | Fin.init z ∈ b}) B' ∧
            (∀ κ ∈ B', Fin.init '' κ = b) ∧
            (∀ i, ∀ κ ∈ B', κ ⊆ projFirst (n + 1) m '' (X i).set ∨
              Disjoint κ (projFirst (n + 1) m '' (X i).set))

end Work.WilE7.Endgame
