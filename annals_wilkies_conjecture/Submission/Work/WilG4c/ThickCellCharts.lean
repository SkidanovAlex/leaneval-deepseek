/-
  WilG4c — the *thick-cell* (graph-cell) branch of the §5.3 per-cell dispatch, BNZ §5.2–§5.3.

  `κ ⊆ ℝ^{p+1}` is a cell of a cylindrical decomposition which

  * lies in the slab `inCubeSet p 1` (its distinguished coordinate is in `I = (0,1)`),
  * has empty interior, and
  * has a *thick* base: `interior (projLast κ)` is nonempty.

  Under these hypotheses `κ` cannot be a band cell (a band over a base with interior has
  interior, `Work.WilG4c.band_no_interior_projLast`), so it is a graph cell: its columns are
  subsingletons (`Work.WilG4c.thickBase_loOf`).  Hence every cube point `x` with
  `Fin.snoc l (x 0) ∈ κ` has its distinguished coordinate pinned to a *definable* function
  `pt` of the parameters, and one applies the `n`-dimensional F-lemma (`ih`) to the pinned
  slice of `F`.  This is `Work.WilkG4c.PinCellCharts`, with the two `Ω`-bookkeepings

  * `Work.WilG4c.PinPtOfCell` — the pin function (a definable selection of a point of every
    nonempty column, `1/2` over the empty ones, so that `pt l ∈ I` for *every* `l`), and
  * `Work.WilG4c.PinSliceGraphMem` — the `Ω`-membership of the pinned slice,

  and the degree bookkeeping (`Work.WilG4c.SectAux.PolyEvalSubst`, `Work.WilG4c.PolySubstBoth`)
  that composes the two degree polynomials into polynomials of the outer variables `(D, r)`.
  The final assembly is `Work.WilG4c.PinCellStep`.
-/
import Mathlib
import Submission.Work.WilG4c.PinCellStep
import Submission.Work.WilkG4c.PinCellCharts
import Submission.Work.WilG4c.StepLipHighMain
import Submission.Work.WilG4c.PinSliceGraphMem
import Submission.Work.WilG4c.thickBase_loOf
import Submission.Work.WilG4c.SectAux.PolyEvalSubst
import Submission.Work.WilG4c.PolySubstBoth
import Submission.Work.WilG1.Cell.isCell_of_mem_cylDecomp
import Submission.Work.WilE8.Sharp.CellTransport

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG Work.WilkG4c

/-- The distinguished coordinate of a point of the slab `inCubeSet p 1` lies in `I`. -/
private theorem mem_I_of_mem_inCubeSet_one {p : ℕ} {z : Fin (p + 1) → ℝ}
    (hz : z ∈ Work.WilG4c.inCubeSet p 1) : z (Fin.last p) ∈ Work.WilkG4c.I := by
  have h0 : Fin.natAdd p (0 : Fin 1) = Fin.last p := by ext; simp [Fin.natAdd, Fin.last]
  have h' := hz
  rw [Work.WilG4c.inCubeSet, Set.mem_ofPred_eq, openCube, Set.mem_ofPred_eq] at h'
  have h1 : z (Fin.natAdd p (0 : Fin 1)) ∈ Set.Ioo (0 : ℝ) 1 := h' 0
  rw [h0] at h1
  exact h1

theorem ThickCellCharts (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (n p : ℕ) (hn : 1 ≤ n) (hchoice : Work.WilkG4c.ChoiceHyp S)
    (ih : ∀ q, WilkiesDesign.CG.FLem S q n)
    (hind : ∀ q : ℕ, q < p → Work.WilkG4c.FLemPHigh S q (n + 1) (Work.WilkG4c.PY q n))
    (F0 F1 : ℕ) (dc : MvPolynomial (Fin 2) ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
      ∀ (D r k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hr : 1 ≤ r)
        (Λ : Set (Fin p → ℝ)) (F : Work.WilkG4c.Family k p (n + 1))
        (hΩg : ∀ i, WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 D (p + (n + 1) + 1))
        (hPY : Work.WilkG4c.PY p n r k F) (hval : Work.WilkG4c.ValuesIn01 Λ F)
        (C : Finset (Set (Fin (p + 1) → ℝ))) (hCdec : WilkiesDesign.IsCylDecomp (p + 1) C)
        (κ : Set (Fin (p + 1) → ℝ)) (hκC : κ ∈ C)
        (hκΩ : κ ∈ S.Ω F1 (MvPolynomial.eval ![D, r] dc) (p + 1))
        (hκcube : κ ⊆ Work.WilG4c.inCubeSet p 1) (hκint : interior κ = ∅)
        (hthick : (interior (WilkiesDesign.projLast κ)).Nonempty),
        ∃ Φ : Finset (Work.WilkG4c.ChartTuple p (n + 1)),
          (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
          Work.WilkG4c.ChartsOK S a (MvPolynomial.eval ![D, r] b) r Λ F Φ ∧
          (∀ l ∈ Λ, ∀ x ∈ WilkiesDesign.openCube (n + 1), Fin.snoc l (x 0) ∈ κ →
            ∃ φ ∈ Φ, ∃ t ∈ WilkiesDesign.openCube (n + 1),
              ∀ i, |F i l (fun j => φ j l t) - F i l x| < ε) := by
  -- the pin function of the cell (definable selector of a point of each nonempty column)
  obtain ⟨a_pt, b_pt, Hpt⟩ := Work.WilG4c.PinPtOfCell S hchoice p F1
  -- `Ω`-membership of the pinned slice of the family
  obtain ⟨a_ps, b_ps, Hps⟩ := Work.WilG4c.PinSliceGraphMem S p n F0 a_pt
  -- the degree bookkeeping: compose the pin degree into the slice degree
  obtain ⟨dpt, hdpt⟩ := Work.WilG4c.SectAux.PolyEvalSubst b_pt dc
  obtain ⟨dslice, hdslice⟩ := Work.WilG4c.PolySubstBoth (MvPolynomial.X 0) dpt b_ps
  obtain ⟨a, b, c, Hstep⟩ :=
    Work.WilG4c.PinCellStep S hcd hder n p hn ih (max F0 a_ps) a_pt dpt dslice
  refine ⟨a, b, c, ?_⟩
  intro D r k ε hε hε1 hr Λ F hΩg hPY hval C hCdec κ hκC hκΩ hκcube hκint hthick
  -- the cell is a graph over a set with nonempty interior
  have hcell : WilkiesDesign.IsCell (p + 1) κ :=
    Work.WilG1.Cell.isCell_of_mem_cylDecomp hCdec hκC
  obtain ⟨_, hcovlo⟩ := Work.WilG4c.thickBase_loOf (m := p) hcell hκint hthick
  -- the pin
  obtain ⟨pt, hptg, hptsel, hptc⟩ := Hpt (MvPolynomial.eval ![D, r] dc) κ hκΩ
  have hA : MvPolynomial.eval ![D, r] dpt
      = Polynomial.eval (MvPolynomial.eval ![D, r] dc) b_pt := hdpt D r
  have hptg' : WilkiesDesign.graphOf pt ∈ S.Ω a_pt (MvPolynomial.eval ![D, r] dpt) (p + 1) := by
    rw [hA]; exact hptg
  -- the pinned slice is `Ω`-bounded
  have hslice : ∀ i, WilkiesDesign.CG.famGraph
      (fun (l : Fin p → ℝ) (u : Fin n → ℝ) => F i l (Fin.cons (pt l) u))
      ∈ S.Ω (max F0 a_ps) (MvPolynomial.eval ![D, r] dslice) (p + n + 1) := by
    intro i
    have hps := Hps D (Polynomial.eval (MvPolynomial.eval ![D, r] dc) b_pt) pt (F i) hptg (hΩg i)
    have hdeg : MvPolynomial.eval
        ![D, Polynomial.eval (MvPolynomial.eval ![D, r] dc) b_pt] b_ps
        = MvPolynomial.eval ![D, r] dslice := by
      rw [hdslice D r, hA]
      simp [MvPolynomial.eval_X]
    exact Work.WilkG4c.Omega_mono_le S (le_max_right _ _) (le_of_eq hdeg) hps
  -- the pin takes values in `I` (on the whole parameter set, hence on `Λ`)
  have hptI : ∀ l ∈ Λ, pt l ∈ Work.WilkG4c.I := by
    intro l hl
    by_cases hfib : ∃ s : ℝ, Fin.snoc l s ∈ κ
    · have h2 := mem_I_of_mem_inCubeSet_one (hκcube (hptsel l hfib))
      simpa using h2
    · rw [hptc l hfib]
      exact ⟨by norm_num, by norm_num⟩
  obtain ⟨Φ, hcard, hok, hcov⟩ := Hstep D r k ε hε hε1 Λ F pt
    (fun i => Work.WilkG4c.Omega_mono_le S (le_max_left _ _) (le_refl D) (hΩg i))
    hptg' hptI hslice hval
  refine ⟨Φ, hcard, hok, ?_⟩
  -- on a graph cell the distinguished coordinate of a point of `κ` *is* the pin
  intro l hl x hx hκx
  have hx0 : x 0 = pt l := by
    have hne : ∃ s : ℝ, Fin.snoc l s ∈ κ := ⟨x 0, hκx⟩
    obtain ⟨μ1, h1⟩ := hcovlo (Fin.snoc l (x 0)) hκx
    obtain ⟨μ2, h2⟩ := hcovlo (Fin.snoc l (pt l)) (hptsel l hne)
    obtain ⟨e1, v1⟩ := Fin.snoc_inj.mp h1
    obtain ⟨e2, v2⟩ := Fin.snoc_inj.mp h2
    rw [e1] at v1
    rw [e2] at v2
    rw [← v1]; exact v2
  exact hcov l hl x hx hx0

end Work.WilG4c
