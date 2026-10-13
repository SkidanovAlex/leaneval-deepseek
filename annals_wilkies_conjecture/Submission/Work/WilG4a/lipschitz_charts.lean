/-
  WilG4a — BNZ Lemma 5.3 ("full `C¹`"), the `n = 1` base case of the family lemma.

  The statement `Work.WilG4a.lipschitz_charts` is the `ℝ`-coordinate form of BNZ
  arXiv:2202.05305, Lemma `lem:full-C1`: given a family `F : Λ × I → I^k` of `Ω`-definable
  functions, there is a finite list of charts `φ_η` whose graphs are `Ω`-definable with
  format/degree depending only on the input format and polynomially on the input degree,
  whose number is polynomial in `(D, k)`, such that along every chart every composite
  `F i l ∘ φ_η l` is `C¹` with derivative bounded by `1` on `I`, and such that the images
  `φ_η(l, I)` cover `I` *exactly*.

  ## The strategy

  Following the paper, and writing `∂_x f(l,x)` for the `x`-derivative of a family member:

  1. **Enlarge the family by the identity** `f(l,x) = x`.  Its graph is the zero set of the
     linear polynomial `X_last - X_{last-1}`, hence `Ω`-definable with format `p+2` and
     degree `1`.  With the identity present, on every "good" cell the dominating member has
     non-vanishing derivative (`|∂_x f| ≥ 1`).

  2. **Cell decomposition** (`decomp_main`): decompose `ℝ^{p+1}` (parameters times the
     variable `x`) into `poly(D,k)` cells, `Ω`-definable with a uniform format and a degree
     depending polynomially on `D`, compatible with the loci
     * `(sliceDiff f)ᶜ`  — where the slice `x ↦ f(l,x)` is not differentiable,
     * `(sliceDerivCont f)ᶜ` — where that slice's derivative is not continuous,
     * `domSet f g` — where `|∂_x f| ≤ |∂_x g|`,
     * `posSet f`, `negSet f` — the sign of `∂_x f`,
     and with the two faces of the strip `0 < x < 1`.  Cutting with the strip, every cell is
     either **good** (`GoodCell`: all members differentiable with continuous slice
     derivative, a fixed dominating index, constant sign of the derivative, and fibres that
     are points or intervals) or **degenerate** (all fibres subsingletons).  The dichotomy is
     forced by the one-variable theory (`WilG1/OneDim`): the bad loci have finite fibres.

  3. **The chart** (`chart1`): for a cell `κ` and a dominating member `f`, put
     `φ(l,t) :=` the unique `y` with `(l,y) ∈ κ` and `f(l,y) = A(l) + (B(l)-A(l))·t`, where
     `A(l) = inf` and `B(l) = sup` of the image of the fibre of `κ` over `l` under `f`.
     Since `f(l,·)` is strictly monotone on the fibre with non-vanishing derivative, `φ(l,·)`
     maps `I` *onto* the fibre, and the chain rule gives
     `(F i l ∘ φ(l,·))' = (B-A) · (∂_x F i / ∂_x f)(φ(l,·))`,
     bounded by `1` by the domination and `B - A ≤ 1`.  For degenerate cells the same formula
     is the constant map to the fibre point.  The graph of `φ` is built from the cell, the
     graph of `f` and the graphs of `A`,`B` through polynomial/affine relations, hence is
     `Ω`-definable with uniform format and degree polynomial in `D` (`chart_graph_mem`).

  The end-point functions `A`, `B` are `Ω`-definable by the "definable choice" argument for
  infima and suprema of fibres (`endpoints_mem`); the chart's analytic properties are proved
  in `chart_props_good` / `chart_props_point`.
-/
import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.subst_mem
import Submission.Work.WilG4a.ChartUnion
import Submission.Work.WilG4a.Bounds
import Submission.Work.WilG1.Basic
import Submission.Work.WilG4a.lipschitz_chart_point
import Submission.Work.WilG4a.lipschitz_chart_graph
import Submission.Work.WilG4a.lipschitz_chart_point_on
import Submission.Work.WilG4a.lipschitz_chart_good_on
import Submission.Work.WilG4a.lipschitz_decomp
import Submission.Work.WilG4a.lipschitz_endpoints_junk
import Submission.Work.WilG4a.lipschitz_slice_tame
import Submission.Work.WilG1.Thin.sliceGraph_mem
import Submission.Work.WilG5.Basic
import Submission.Work.WilG4a.LipChartsDefs
import Submission.Work.WilG4a.LipChartsAux

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a
open WilkiesConjecture WilkiesDesign

variable {p : ℕ}

/-! ## 4. The pieces of the proof

The two remaining inputs of the assembly are the cell decomposition and the end-point functions:

* **Piece 1 — the loci are `Ω`-definable.**  For a family member of format `F0` and degree `D`,
  the complements of the differentiability locus `sliceDiff` and of the continuity locus
  `sliceDerivCont` of the slice derivative, the domination sets `domSet f g`, the sign sets
  `posSet f`, `negSet f` and the strip are all `Ω`-definable with a format independent of `D`
  and a degree polynomial in `D`.  This is used inside the cell decomposition and is proved in
  the sibling modules `sliceDerivCont_memAlt`, `domLoci_memAlt` (see
  `Submission/Work/WilG4a/lipschitz_decomp.lean`).

* **Piece 2 — the cell decomposition** (`Submission/Work/WilG4a/lipschitz_decomp`), imported
  below under its own name.

* **Piece 3 — the end points are `Ω`-definable** (`Submission/Work/WilG4a/lipschitz_endpoints_junk`),
  with the `sInf`/`sSup` junk convention handled, so that no side condition on the image of a
  fibre is needed; also imported below under its own name. -/


/-! **Piece 5 (Λ-restricted): the chart of a good cell** is proved in the sibling module
`Submission/Work/WilG4a/lipschitz_chart_good_on`, which is imported above. -/


/-! ## 6. The theorem -/

theorem lipschitz_charts (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (p : ℕ) (F0 : ℕ) : ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (cc : MvPolynomial (Fin 3) ℝ), ∀ (D k : ℕ) (Λ : Set (Fin p → ℝ)) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ), (∀ i, Work.WilG4a.graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) → (∀ i, ∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, F i l x ∈ Work.WilG4a.I) → ∃ (m : ℕ), (m : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (1 : ℝ), (k : ℝ)] cc ∧ ∃ (φ : Fin m → (Fin p → ℝ) → ℝ → ℝ), (∀ η, Work.WilG4a.graphFam (φ η) ∈ S.Ω a (MvPolynomial.eval ![D, 1] b) (p + 1 + 1)) ∧ (∀ η l, l ∈ Λ → ∀ t ∈ Work.WilG4a.I, φ η l t ∈ Work.WilG4a.I) ∧ (∀ η (i : Fin k) (l : Fin p → ℝ), l ∈ Λ → ContDiffOn ℝ 1 (fun t : ℝ => F i l (φ η l t)) Work.WilG4a.I ∧ ∀ t ∈ Work.WilG4a.I, |iteratedDeriv 1 (fun t : ℝ => F i l (φ η l t)) t| ≤ 1) ∧ (∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, ∃ η, ∃ t ∈ Work.WilG4a.I, φ η l t = x) := by
  -- The one-variable tameness input (the `n = 1` o-minimality theorem).
  obtain ⟨aD, bD, ccD, hD⟩ := lipschitz_decomp S hcd hder p (max F0 (p + 2))
    (sliceTame_oneDim S hcd hder p (max F0 (p + 2)))
  obtain ⟨aE, bE, hE⟩ := lipschitz_endpoints_junk S p (max F0 (p + 2)) aD bD
  set bCell : MvPolynomial (Fin 2) ℕ := bD + bE with hbCell
  have hbD_le : ∀ (D r : ℕ), MvPolynomial.eval ![max D 1, r] bD ≤ MvPolynomial.eval ![max D 1, r] bCell := by
    intro D r
    rw [hbCell, MvPolynomial.eval_add]
    exact Nat.le_add_right _ _
  have hbE_le : ∀ (D r : ℕ), MvPolynomial.eval ![max D 1, r] bE ≤ MvPolynomial.eval ![max D 1, r] bCell := by
    intro D r
    rw [hbCell, MvPolynomial.eval_add]
    exact Nat.le_add_left _ _
  obtain ⟨aP, bP, hP⟩ := lipschitz_chart_graph S p (max F0 (p + 2)) (max aD aE) bCell
  obtain ⟨bFin, hbFin⟩ := exists_degree_bound bP bE
  obtain ⟨ccFin, hccFin⟩ := mvpoly_eval_real_bound ccD
  refine ⟨aP, bFin, ccFin, ?_⟩
  intro D k Λ F hΩ hI
  -- Enlarge the family by the identity.
  let F' : Fin (k+1) → (Fin p → ℝ) → ℝ → ℝ :=
    fun i => if h : i.val < k then F ⟨i.val, h⟩ else fun _ x => x
  have hcastSucc : ∀ i : Fin k, F' (Fin.castSucc i) = F i := by
    intro i
    show (if h : (Fin.castSucc i).val < k then F ⟨(Fin.castSucc i).val, h⟩ else fun _ x => x) = F i
    split_ifs with h
    · congr 1
    · exact absurd (by simpa using i.isLt) h
  have hlast : F' (Fin.last k) = (fun _ x => x) := by
    show (if h : (Fin.last k).val < k then F ⟨(Fin.last k).val, h⟩ else fun _ x => x) = _
    rw [dif_neg (by simp)]
  have hgraph : ∀ i, graphFam (F' i) ∈ S.Ω (max F0 (p + 2)) (max D 1) (p + 1 + 1) := by
    intro i
    by_cases h : i.val < k
    · have hi : F' i = F ⟨i.val, h⟩ := by
        show (if h' : i.val < k then F ⟨i.val, h'⟩ else fun _ x => x) = F ⟨i.val, h⟩
        rw [dif_pos h]
      rw [hi]
      exact mono_FD_le S (hΩ ⟨i.val, h⟩) (le_max_left _ _) (le_max_left _ _)
    · have hi : F' i = (fun _ x => x) := by
        show (if h' : i.val < k then F ⟨i.val, h'⟩ else fun _ x => x) = (fun _ x => x)
        rw [dif_neg h]
      rw [hi]
      exact identity_graph_mem S p (max F0 (p + 2)) (max D 1) (le_max_right _ _) (le_max_right _ _)
  have hinto : ∀ i, ∀ l ∈ Λ, ∀ x ∈ I, F' i l x ∈ I := by
    intro i l hl x hx
    by_cases h : i.val < k
    · have hi : F' i = F ⟨i.val, h⟩ := by
        show (if h' : i.val < k then F ⟨i.val, h'⟩ else fun _ x => x) = F ⟨i.val, h⟩
        rw [dif_pos h]
      rw [hi]; exact hI ⟨i.val, h⟩ l hl x hx
    · have hi : F' i = (fun _ x => x) := by
        show (if h' : i.val < k then F ⟨i.val, h'⟩ else fun _ x => x) = (fun _ x => x)
        rw [dif_neg h]
      rw [hi]; exact hx
  obtain ⟨m, hcc, κ, i₁, hκmem, hκstrip, hcov, hdich⟩ := hD (max D 1) k Λ F' hgraph hinto hlast
  have hcc' : (m : ℝ) ≤ MvPolynomial.eval ![((max D 1 : ℕ) : ℝ), 1, (k : ℝ)] ccD := hcc
  refine ⟨m, le_trans hcc' (by simpa [Nat.cast_max] using hccFin D k),
    fun σ => chart1 (F' (i₁ σ)) (κ σ), ?_, ?_, ?_, ?_⟩
  · -- the graphs of the charts are `Ω`-definable
    intro σ
    have hmem := hκmem σ
    have hstrip := hκstrip σ
    have hinto_i : ∀ l ∈ Λ, ∀ x ∈ I, F' (i₁ σ) l x ∈ I := hinto (i₁ σ)
    obtain ⟨hA, hB⟩ := hE (max D 1) (F' (i₁ σ)) (κ σ) (hgraph (i₁ σ)) hmem
    have hmem' : κ σ ∈ S.Ω (max aD aE) (MvPolynomial.eval ![max D 1, 1] bCell) (p + 1) :=
      Work.WilG1.Omega.mono hmem (le_max_left _ _) (hbD_le D 1)
    have hA' : graphOf (Aend (κ σ) (F' (i₁ σ))) ∈
        S.Ω (max aD aE) (MvPolynomial.eval ![max D 1, 1] bCell) (p + 1) :=
      Work.WilG1.Omega.mono hA (le_max_right _ _) (hbE_le D 1)
    have hB' : graphOf (Bend (κ σ) (F' (i₁ σ))) ∈
        S.Ω (max aD aE) (MvPolynomial.eval ![max D 1, 1] bCell) (p + 1) :=
      Work.WilG1.Omega.mono hB (le_max_right _ _) (hbE_le D 1)
    have hmain := hP (max D 1) (F' (i₁ σ)) (κ σ) (hgraph (i₁ σ)) hmem' hA' hB'
      (chart1_uniq_of_dichotomy (p := p) (hdich σ))
    exact Work.WilG1.Omega.mono hmain le_rfl (hbFin D).1
  · -- the charts map `I` into `I`
    intro σ l hl t ht
    rcases hdich σ with hg | hp
    · exact (lipschitz_chart_good_on p (k+1) F' (κ σ) (i₁ σ) (i₁ σ) Λ (hκstrip σ) hg
        (fun z hz => by
          have hdom := hg.2.2.1 (Fin.last k) hz
          rw [hlast] at hdom
          exact ne_zero_of_domSet_id hdom)
        (hinto (i₁ σ)) (hinto (i₁ σ))).1 l hl t ht
    · exact (lipschitz_chart_point_on p (F' (i₁ σ)) (F' (i₁ σ)) (κ σ) Λ (hκstrip σ) hp
        (hinto (i₁ σ))).1 l hl t ht
  · -- the composite along each chart is `C¹` with derivative bounded by `1`
    intro σ i l hl
    rcases hdich σ with hg | hp
    · have hres := (lipschitz_chart_good_on p (k+1) F' (κ σ) (i₁ σ) (Fin.castSucc i) Λ (hκstrip σ) hg
        (fun z hz => by
          have hdom := hg.2.2.1 (Fin.last k) hz
          rw [hlast] at hdom
          exact ne_zero_of_domSet_id hdom)
        (hinto (i₁ σ)) (hinto (Fin.castSucc i))).2.1 l hl
      rw [hcastSucc i] at hres
      exact hres
    · have hres := (lipschitz_chart_point_on p (F' (i₁ σ)) (F' (Fin.castSucc i)) (κ σ) Λ (hκstrip σ) hp
        (hinto (Fin.castSucc i))).2.1 l hl
      rw [hcastSucc i] at hres
      exact hres
  · -- the images of the charts cover `I`
    intro l hl x hx
    obtain ⟨σ, hσ⟩ := hcov l hl x hx
    have hxf : x ∈ fibre (κ σ) l := hσ
    rcases hdich σ with hg | hp
    · obtain ⟨t, ht, htx⟩ := (lipschitz_chart_good_on p (k+1) F' (κ σ) (i₁ σ) (i₁ σ) Λ (hκstrip σ) hg
        (fun z hz => by
          have hdom := hg.2.2.1 (Fin.last k) hz
          rw [hlast] at hdom
          exact ne_zero_of_domSet_id hdom)
        (hinto (i₁ σ)) (hinto (i₁ σ))).2.2 l hl x hxf
      exact ⟨σ, t, ht, htx⟩
    · obtain ⟨t, ht, htx⟩ := (lipschitz_chart_point_on p (F' (i₁ σ)) (F' (i₁ σ)) (κ σ) Λ (hκstrip σ) hp
        (hinto (i₁ σ))).2.2 l hl x hxf
      exact ⟨σ, t, ht, htx⟩

end Work.WilG4a
