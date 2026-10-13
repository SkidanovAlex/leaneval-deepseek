/-
  WilG4c / StepLipHighGlue — the assembly of `Work.WilkG4c.StepLipHigh` (BNZ §5.3, `r ≥ 1`).

  The design of record is `StepLip_RouteNotes.md` §15 together with the two "Session 16"
  updates of `StepLipHigh_NOTES.md` (in particular: **globalise the family before running the
  `y`-machinery**, otherwise the `Λ`-restricted `ψ`-data cannot feed `hP1`/`ChartsOfPYLipOn`).

  Everything below is *interface*: the per-`ψ` step `StepLipHighPsi` (the decomposition, the
  three-way cell dispatch, the covers and the counts for one chart `ψ` of the `y`-family) and
  then the outer strong induction on `p` (which uses `DescentP` for `hP1` at smaller `p` and
  `StepLipHighPsi` for the per-`ψ` work).  The pieces it consumes are all proved elsewhere:

  * `Work.WilkG4c.YbCharts`         — the `ih`-charts `Ξ` of the `y`-family (globally, when run
    on the clamped family);
  * `Work.WilkG4c.YPullbackBound`   — `YBound` and the `y`-Lipschitzness of the pullback;
  * `Work.WilkG4c.CurveFam`         — the near-maximising curve;
  * `Work.WilkG4c.StepTupleMem`     — the `Ω`-bounds of the §5.3 tuple;
  * `Work.WilkG4c.ChartsExactCell`  — the exact-cover per-cell chart;
  * `Work.WilG4c.GoodCellChartsG`   — the per-cell good branch (delegated, in flight);
  * `Work.WilkG4c.PinPtOfCell` + `Work.WilkG4c.PinCellCharts` — the `s`-pin branch;
  * `Work.WilG4c.CellSectionMain` + `Work.WilG4c.SectionChoice` + `Work.WilG4c.SubstCharts`
    + `DescentP` — the `λ`-thin (section) branch;
  * `Work.WilG4c.PieceChartsToF`, `Work.WilG4c.ClampCharts`, `Work.WilG4c.PiecePiecing` — the
    transport and the union/count packaging.
-/
import Mathlib
import Submission.Work.WilG4c.StepLipDefs
import Submission.Work.WilG4c.StepLipHighAux
import Submission.Work.WilG4c.StepLipAux
import Submission.Work.WilG4c.YbCharts
import Submission.Work.WilG4c.C1AllMem
import Submission.Work.WilG4c.CurveFam
import Submission.Work.WilkG4c.StepTupleMem
import Submission.Work.WilkG4c.ChartsExactCell
import Submission.Work.WilkG4c.PinCellCharts
import Submission.Work.WilkG4c.YPullbackBound
import Submission.Work.WilG4c.YPullback
import Submission.Work.WilG4c.PieceChartsToF
import Submission.Work.WilG4c.clampFamGraph
import Submission.Work.WilG4c.ClampCharts

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG4c

/-- **Step 1 of the assembly: globalise the family.**

Every `Ω`-bounded family can be replaced by a *globally* `(0,1)`-valued family with `Ω`-bounded
graphs, at a fixed cost in format and degree, in such a way that the two families agree on
`Λ × openCube n` as soon as `ValuesIn01 Λ F` holds.  This is what allows the `y`-machinery
(`ih`, `YbCharts`) to be run with `Λ` replaced by the whole parameter space, which is the
prerequisite for `hP1` (whose `PYLip` hypothesis is a global predicate) to apply to the
pullbacks. -/
theorem ValuesClamp (S : SOMin) (p n k : ℕ) :
    ∃ (a c : ℕ), ∀ (F0 D : ℕ) (Λ : Set (Fin p → ℝ)) (F : Family k p n),
      (∀ i, famGraph (F i) ∈ S.Ω F0 D (p + n + 1)) → ValuesIn01 Λ F →
      ∃ F' : Family k p n, (∀ i, famGraph (F' i) ∈ S.Ω (F0 + a) (D + c) (p + n + 1)) ∧
        (∀ i l x, x ∈ openCube n → F' i l x ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ i, ∀ l ∈ Λ, ∀ x ∈ openCube n, F' i l x = F i l x) := by
  obtain ⟨a, c, h⟩ := clampFamGraph S p n
  refine ⟨a, c, ?_⟩
  intro F0 D Λ F hΩg hval
  refine ⟨clampFam F, ?_, ?_, ?_⟩
  · intro i
    have hmem := h F0 D F hΩg i
    have hfun : (fun (l : Fin p → ℝ) (u : Fin n → ℝ) =>
        if F i l u ∈ Set.Ioo (0 : ℝ) 1 then F i l u else (1 / 2 : ℝ))
        = (clampFam F) i := by
      funext l u
      rfl
    rw [hfun] at hmem
    exact hmem
  · intro i l x _
    exact yclamp_mem (F i l x)
  · intro i l hl x hx
    exact yclamp_of_mem (hval i l hl x hx)


/-- **The per-`ψ` step of the `§5.3` assembly.**  For one chart `ψ` of the `y`-family (with
global cube/composite data and the `Λ`-restricted `ε/2`-cover), produce the charts of `F` valid
on the *whole* `Λ` and covering `Λ × openCube (n+1)` to within `ε`.

This is the decomposition of `ℝ^{p+1}` refining `badCurve (yPullback F ψ ·)`,
`C1All (yPullback F ψ ·)`, the tuple bad loci and comparison sets, plus the three-way dispatch
(good / `s`-pin / section) and the counts. -/
theorem StepLipHighPsi (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (n p : ℕ) (hn : 1 ≤ n) (h1 : ∀ q, WilkiesDesign.CG.F1Affine S q)
    (ih : ∀ q, WilkiesDesign.CG.FLem S q n) (hchoice : Work.WilkG4c.ChoiceHyp S)
    (hbdd : Work.WilkG4c.BddDxHyp S)
    (hP1 : Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PYLip p n))
    (hind : ∀ q : ℕ, q < p → Work.WilkG4c.FLemPHigh S q (n + 1) (Work.WilkG4c.PY q n)) :
    ∀ (aψ : ℕ) (bψ : MvPolynomial (Fin 2) ℕ) (F0 : ℕ),
      ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
      ∀ (D r k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hr : 1 ≤ r)
        (Λ : Set (Fin p → ℝ)) (F : Work.WilkG4c.Family k p (n + 1))
        (hΩg : ∀ i, WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 D (p + (n + 1) + 1))
        (hPY : Work.WilkG4c.PY p n r k F)
        (hval : Work.WilkG4c.ValuesIn01 Λ F)
        (ψ : Work.WilkG4c.ChartTuple (p + 1) n)
        (hψg : ∀ j, WilkiesDesign.CG.famGraph (ψ j) ∈
          S.Ω aψ (MvPolynomial.eval ![D, r] bψ) ((p + 1) + n + 1))
        (hψcube : ∀ l, ∀ x ∈ Work.WilkG4c.I, ∀ t ∈ WilkiesDesign.openCube n,
          (fun j => ψ j (Fin.snoc l x) t) ∈ WilkiesDesign.openCube n)
        (hψsm : ∀ i, ∀ l, ∀ x ∈ Work.WilkG4c.I,
          ContDiffOn ℝ r (fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)))
            (WilkiesDesign.openCube n))
        (hψnm : ∀ i, ∀ l, ∀ x ∈ Work.WilkG4c.I, ∀ m, m ≤ r →
          ∀ t ∈ WilkiesDesign.openCube n,
            ‖iteratedFDeriv ℝ m (fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t))) t‖ ≤ 1)
        (hψcov : ∀ l ∈ Λ, ∀ x ∈ Work.WilkG4c.I, ∀ y ∈ WilkiesDesign.openCube n,
          ∃ t ∈ WilkiesDesign.openCube n, ∀ i,
            |F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)) - F i l (Fin.cons x y)| < ε / 2),
        ∃ Φ : Finset (Work.WilkG4c.ChartTuple p (n + 1)),
          (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
          Work.WilkG4c.ChartsOK S a (MvPolynomial.eval ![D, r] b) r Λ F Φ ∧
          Work.WilkG4c.Covers Λ F Φ ε := by
  sorry
/-- **Step 5 of the assembly: transfer the covers back.** -/
theorem Covers_of_agree {p n k : ℕ} {Λ : Set (Fin p → ℝ)} {F F' : Family k p n}
    {Φ : Finset (ChartTuple p n)} {ε : ℝ}
    (hc : ∀ i, ∀ φ ∈ Φ, ∀ l ∈ Λ, ∀ t ∈ openCube n,
      F' i l (fun j => φ j l t) = F i l (fun j => φ j l t))
    (ht : ∀ i, ∀ l ∈ Λ, ∀ x ∈ openCube n, F' i l x = F i l x)
    (hC : Covers Λ F' Φ ε) : Covers Λ F Φ ε := by
  intro l hl x hx
  obtain ⟨φ, hφ, t, ht', hlt⟩ := hC l hl x hx
  refine ⟨φ, hφ, t, ht', fun i => ?_⟩
  rw [← hc i φ hφ l hl t ht', ← ht i l hl x hx]
  exact hlt i

end Work.WilkG4c
