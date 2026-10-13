/-
  WilG4c / StepLipHighMain — the §5.3 assembly (`r ≥ 1` slice of `StepLip`).

  This file is the *assembly* of `Work.WilkG4c.StepLipHigh`, i.e. the proof of
  `Work.WilkG4c.FLemP S p (n+1) (PY p n)` from `Work.WilkG4c.FLemP S p (n+1) (PYLip p n)`.
  The design of record is `Submission/Work/WilG4c/StepLip_RouteNotes.md` §14 and §15.

  The ingredients proved elsewhere (all `sorry`-free) are

  * `Work.WilkG4c.ChartsExactCell` — the per-cell exact-cover chart (BNZ Lemma 5.5);
  * `Work.WilG4c.ExactChartDeriv`    — `chartFun` / `chartFun_diff`;
  * `Work.WilG4c.PiecePYLipOfChartPw` — the per-cell analytic engine;
  * `Work.WilG4c.ChartsOfPYLipOn`    — the localised `hP1` (any Lipschitz constant `C ≥ 1`);
  * `Work.WilG4c.PieceChartsToF`     — piece charts ⇒ charts for `F` on the cell's projection;
  * `Work.WilG4c.ClampCharts`        — `ChartsOK` on an `Ω`-set ⇒ `ChartsOK` on the whole `Λ`;
  * `Work.WilkG4c.PinCellCharts`     — the pin-cell (graph-cell) case, via the `n`-dimensional
    F-lemma `ih`;
  * `Work.WilG4c.CellSectionMain`    — the section of a thin cell, used by the parameter-induction;
  * `Work.WilG4c.DescentP`           — descent of `FLemP` in the number of parameters.

  What this file adds is the *glue*: the column-selection (pin) function of a cell, and then the
  three-way dispatch of the cell decomposition.
-/
import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.Hyps
import Submission.Work.WilG0.API
import Submission.Work.WilkG4c.ChartsExactCell
import Submission.Work.WilG4c.IteFamGraphMem

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The pin function of a column of a cell -/

/-- `Fin.append`, in the `Fin.snoc` spelling, for a one-element fibre. -/
theorem append_one_eq_snoc {p : ℕ} (l : Fin p → ℝ) (y : Fin 1 → ℝ) :
    Fin.append l y = Fin.snoc l (y 0) :=
  Fin.append_right_eq_snoc l y

/-- **The pin of a column of an `Ω`-bounded cell.**  For an `Ω`-bounded set
`κ ⊆ ℝ^{p+1}` there is a *definable* function `pt : ℝ^p → ℝ` whose graph is `Ω`-bounded (with a
specialisation bound `b.eval D₁`, `b` depending only on the format `F₁`), which selects a point
of every nonempty column `{s | Fin.snoc l s ∈ κ}` of `κ`, and which is the constant `1/2` over
every empty column.

This is `Work.WilkG4c.ChoiceHyp` applied to `κ` at `n = 1`.  It is the pin function that the
*graph-cell* case of the §5.3 assembly feeds to `Work.WilkG4c.PinCellCharts` (the `1/2` clause
is what makes `pt l ∈ I` true for *every* `l`, which is a hypothesis of `PinCellCharts`). -/
theorem PinPtOfCell (S : WilkiesDesign.SOMin) (hchoice : Work.WilkG4c.ChoiceHyp S)
    (p F1 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D1 : ℕ) (κ : Set (Fin (p + 1) → ℝ)),
      κ ∈ S.Ω F1 D1 (p + 1) →
      ∃ pt : (Fin p → ℝ) → ℝ,
        WilkiesDesign.graphOf pt ∈ S.Ω a (b.eval D1) (p + 1) ∧
        (∀ l : Fin p → ℝ, (∃ s : ℝ, Fin.snoc l s ∈ κ) → Fin.snoc l (pt l) ∈ κ) ∧
        (∀ l : Fin p → ℝ, ¬ (∃ s : ℝ, Fin.snoc l s ∈ κ) → pt l = 1 / 2) := by
  obtain ⟨a, b, h⟩ := hchoice F1 p 1
  refine ⟨max a (F1 + 2) + 4 * (p + 1) + 16,
    b + Polynomial.X * Polynomial.C 2 + Polynomial.C 1, ?_⟩
  intro D1 κ hκ
  obtain ⟨f, hf1, hf2⟩ := h D1 κ hκ
  -- the graph of `l ↦ f l 0` is the `Ω`-set produced by `ChoiceHyp`
  have hg0 : WilkiesDesign.graphOf (fun l : Fin p → ℝ => f l 0) ∈
      S.Ω a (Polynomial.eval D1 b) (p + 1) := by
    have hset : WilkiesDesign.graphOf (fun l : Fin p → ℝ => f l 0) =
        {z : Fin (p + 1) → ℝ | ∀ j : Fin 1,
          z (Fin.natAdd p j) = f (fun i => z (Fin.castAdd 1 i)) j} := by
      have hj : Fin.natAdd p (0 : Fin 1) = Fin.last p := by
        refine Fin.ext ?_
        simp [Fin.natAdd]
      ext z
      have hl : (fun i : Fin p => z (Fin.castAdd 1 i)) = Fin.init z := by
        funext i; rfl
      simp only [WilkiesDesign.graphOf, Set.mem_ofPred_eq]
      constructor
      · intro hz j
        have h0 : (0 : Fin 1) = j := Subsingleton.elim _ _
        rw [← h0, hj, hz, hl]
      · intro hz
        have h0 := hz 0
        rw [hj, hl] at h0
        exact h0
    rw [hset]
    exact hf2
  -- the (modifiable) pin
  set pt : (Fin p → ℝ) → ℝ :=
    fun l => if h : ∃ s : ℝ, Fin.snoc l s ∈ κ then f l 0 else 1 / 2 with hpt
  have hpt_of : ∀ l : Fin p → ℝ, (∃ s : ℝ, Fin.snoc l s ∈ κ) → pt l = f l 0 := by
    intro l hl; rw [hpt]; exact dif_pos hl
  have hpt_not : ∀ l : Fin p → ℝ, ¬ (∃ s : ℝ, Fin.snoc l s ∈ κ) → pt l = 1 / 2 := by
    intro l hl; rw [hpt]; exact dif_neg hl
  have hmemC : ∀ z : Fin (p + 1) → ℝ,
      Fin.init z ∈ WilkiesDesign.projLast κ ↔ ∃ s : ℝ, Fin.snoc (Fin.init z) s ∈ κ :=
    fun z => Iff.rfl
  -- the graph identity
  have hgraph : WilkiesDesign.graphOf pt =
      (WilkiesDesign.graphOf (fun l : Fin p → ℝ => f l 0) ∩
          {z : Fin (p + 1) → ℝ | Fin.init z ∈ WilkiesDesign.projLast κ}) ∪
        (({z : Fin (p + 1) → ℝ | Fin.init z ∈ WilkiesDesign.projLast κ})ᶜ ∩
          {z : Fin (p + 1) → ℝ | z (Fin.last p) = 1 / 2}) := by
    ext z
    have hz : Fin.snoc (Fin.init z) (z (Fin.last p)) = z := Fin.snoc_init_self z
    simp only [WilkiesDesign.graphOf, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
      Set.mem_compl_iff]
    constructor
    · intro hlast
      by_cases hc : ∃ s : ℝ, Fin.snoc (Fin.init z) s ∈ κ
      · left
        refine ⟨?_, hc⟩
        rw [hpt_of (Fin.init z) hc] at hlast
        exact hlast
      · right
        refine ⟨hc, ?_⟩
        rw [hpt_not (Fin.init z) hc] at hlast
        exact hlast
    · rintro (⟨hg, hc⟩ | ⟨hc, hlast⟩)
      · rw [hpt_of (Fin.init z) hc]; exact hg
      · rw [hpt_not (Fin.init z) hc]; exact hlast
  refine ⟨pt, ?_, ?_, hpt_not⟩
  · -- the graph is `Ω`-bounded
    rw [hgraph]
    -- the cylinder over `projLast κ`
    have hcyl : {z : Fin (p + 1) → ℝ | Fin.init z ∈ WilkiesDesign.projLast κ} ∈
        S.Ω (max a (F1 + 2)) D1 (p + 1) := by
      have hp : WilkiesDesign.projLast κ ∈ S.Ω (F1 + 1) D1 p := S.proj hκ
      have hpr := S.prod_right hp
      refine Work.WilkG4c.Omega_mono_le S ?_ (le_refl D1) hpr
      omega
    have hg0' : WilkiesDesign.graphOf (fun l : Fin p → ℝ => f l 0) ∈
        S.Ω (max a (F1 + 2)) (Polynomial.eval D1 b) (p + 1) :=
      Work.WilkG4c.Omega_mono_le S (le_max_left _ _) (by omega) hg0
    have h1 : WilkiesDesign.graphOf (fun l : Fin p → ℝ => f l 0) ∩
        {z : Fin (p + 1) → ℝ | Fin.init z ∈ WilkiesDesign.projLast κ} ∈
        S.Ω (max a (F1 + 2) + 1) (Polynomial.eval D1 b + D1) (p + 1) :=
      Work.WilG0.Omega_inter2 hg0' hcyl
    have hcc : ({z : Fin (p + 1) → ℝ | Fin.init z ∈ WilkiesDesign.projLast κ})ᶜ ∈
        S.Ω (max (max a (F1 + 2) + 1) (p + 1)) D1 (p + 1) :=
      Work.WilkG4c.Omega_mono_le S (by omega) (by omega) (S.compl hcyl)
    have hhyp : {z : Fin (p + 1) → ℝ | z (Fin.last p) = 1 / 2} ∈
        S.Ω (max (max a (F1 + 2) + 1) (p + 1)) 1 (p + 1) := by
      refine Work.WilkG4c.Omega_mono_le S ?_ (by omega) (Work.WilG4c.lastCoord_eq_mem S p (1 / 2))
      omega
    have h2 : ({z : Fin (p + 1) → ℝ | Fin.init z ∈ WilkiesDesign.projLast κ})ᶜ ∩
        {z : Fin (p + 1) → ℝ | z (Fin.last p) = 1 / 2} ∈
        S.Ω (max (max a (F1 + 2) + 1) (p + 1) + 1) (D1 + 1) (p + 1) :=
      Work.WilG0.Omega_inter2 hcc hhyp
    have h1' : WilkiesDesign.graphOf (fun l : Fin p → ℝ => f l 0) ∩
        {z : Fin (p + 1) → ℝ | Fin.init z ∈ WilkiesDesign.projLast κ} ∈
        S.Ω (max (max a (F1 + 2) + 1) (p + 1) + 1) (Polynomial.eval D1 b + D1)
          (p + 1) :=
      Work.WilkG4c.Omega_mono_le S (by omega) (by omega) h1
    have h3 := Work.WilG0.Omega_union2 h1' h2
    refine Work.WilkG4c.Omega_mono_le S (by omega) ?_ h3
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C]
    omega
  · -- the selected point lies in the column
    intro l hfib
    obtain ⟨s, hs⟩ := hfib
    have hsel : Fin.snoc l (f l 0) ∈ κ := by
      have h1 := hf1 l ⟨(fun _ : Fin 1 => s), by simpa [append_one_eq_snoc] using hs⟩
      simpa [append_one_eq_snoc] using h1
    rw [hpt_of l ⟨s, hs⟩]
    exact hsel

end Work.WilG4c
