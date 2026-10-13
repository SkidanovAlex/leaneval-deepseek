/-
  WilG4c / `GoodCellStep` — the *good cell* case of the §5.3 assembly (`StepLipHigh`).

  The `r ≥ 1` slice of `Work.WilG4c.StepLip` (`Work.WilkG4c.StepLipHigh`) is proved by a
  cylindrical decomposition of the `(λ, s)`-space and a three-way dispatch of the resulting
  cells (route notes §15):

  * **good** cells (meeting none of the bad loci): BNZ §5.3's tuple of near-maximisers gives an
    exact-cover cell chart `χ` (`ChartsExactCell`), the pullback of the family along the
    `y`-chart `ψ` of the induction hypothesis is cut by `χ` into a *piece*
    (`pieceFam (yPullback F ψ) (chartFun χ)`), which is `YBound` and `C`-Lipschitz on the cell's
    parameter projection `P` (`PiecePYLipOfChartPw`); `ChartsOfPYLipOn` then produces charts for
    the piece, and `selPieceChart` transports them back to charts of `F`;
  * **pin** cells (graph cells), handled by `PinCellCharts`;
  * **thin** cells (empty-interior projections), handled by the parameter induction.

  This file contains the good-cell step as a single self-contained lemma.  Its analytic input is
  taken in the *conclusions* of `PiecePYLipOfChartPw` (the Λ-restricted `YBound`, the
  `C`-Lipschitzness on `P` and `ValuesIn01 P` of the piece), so that the step is pure
  bookkeeping: `ChartsOfPYLipOn` → `PieceChartsToF` (inlined here, with the format/degree
  witnesses `A₀,C₀,A₁,C₁` of `selPieceChart_zero_mem`/`selPieceChart_succ_mem` destructured
  *before* the parameters `D,r,k,ε` are introduced, so that the statement's format `a` and
  degree polynomial `b` can be written down explicitly) → the two-step `ε`-cover.

  The `ε`-cover is a **two-step** assembly (this is easy to get wrong): the `ε/2`-cover of the
  `y`-fibre supplied by the induction hypothesis (`hih`), then the piece's own `ε/2`-cover at
  the chart point; the exact cover of the cell chart converts the `s`-coordinate of the piece's
  chart point back into a cube point.

  All the content of this file is `sorry`-free. -/
import Mathlib
import Submission.Work.WilG4c.ChartsOfPYLipOn
import Submission.Work.WilG4c.PieceChartsToF
import Submission.Work.WilG4c.ExactChartDeriv
import Submission.Work.WilG4c.StepLipPieces
import Submission.Work.WilG4c.YPullback
import Submission.Work.WilG4c.PolySubstFirst
import Submission.Work.WilG4c.PolySubstFirst4

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilkG4c

/-! ## 0. The format/degree witnesses of the piece-chart transport

`selPieceChart_zero_mem` and `selPieceChart_succ_mem` produce the `Ω`-bounds of the coordinates
of the composite chart `selPieceChart ψ φ χ`, but their format/degree *witnesses* are opaque
(the two lemmas are stated with an existential prefix).  A consumer of the transport that has to
write down the format `a` and the degree polynomial `b` of its own conclusion — which is what
every step of the §5.3 assembly does — therefore cannot read the witnesses off `PieceChartsToF` /
`PieceChartsToFExplicit`: it must pick the witnesses *itself*, before the parameters `D, r, k, ε`
are introduced, and be able to supply the two `Ω`-bounds at exactly those witnesses.

`selPieceChart_obligations` exposes the witnesses together with their *specification*, and
`PieceChartsToFGiven` is the transport `pieceFam (yPullback F ψ) φ ⟶ F` with the format/degree
witnesses (and their specification) as *inputs*.  Together they let a caller compute `a` and `b`
explicitly. -/

/-- The two format/degree witnesses of the composite chart, bundled with the `Ω`-bounds they
witness.  The first conjunct is `selPieceChart_zero_mem`, the second `selPieceChart_succ_mem`,
both with the existential prefix replaced by the displayed witnesses. -/
theorem selPieceChart_obligations (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ (A0 C0 A1 C1 : ℕ),
      (∀ (aφ Dgφ a Dg : ℕ) (φ : ChartTuple p 1)
          (χ : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
        famGraph (φ 0) ∈ S.Ω aφ Dgφ (p + 1 + 1) →
        famGraph χ ∈ S.Ω a Dg (p + (n + 1) + 1) →
        famGraph (fun l t => φ 0 l (fun _ => χ l t)) ∈
          S.Ω (aφ + a + A0) (Dgφ + (p + 1) * Dg + C0) (p + (n + 1) + 1)) ∧
      (∀ (aψ Dgψ aφ Dgφ a Dg : ℕ) (ψ : ChartTuple (p + 1) n) (φ : ChartTuple p 1)
          (χ : ChartTuple p (n + 1)) (j : Fin n),
        (∀ i, famGraph (ψ i) ∈ S.Ω aψ Dgψ ((p + 1) + n + 1)) →
        famGraph (φ 0) ∈ S.Ω aφ Dgφ (p + 1 + 1) →
        (∀ i, famGraph (χ i) ∈ S.Ω a Dg (p + (n + 1) + 1)) →
        famGraph (fun l t => ψ j (Fin.snoc l (φ 0 l (fun _ => χ 0 l t)))
            (Fin.tail (fun i => χ i l t))) ∈
          S.Ω (aψ + (aφ + a + A1))
            (Dgψ + ((p + 1) + n) * (Dgφ + (p + 1) * Dg + C1) + C1)
            (p + (n + 1) + 1)) := by
  obtain ⟨A0, C0, h0⟩ := selPieceChart_zero_mem S p n
  obtain ⟨A1, C1, h1⟩ := selPieceChart_succ_mem S p n
  exact ⟨A0, C0, A1, C1, h0, h1⟩

/-- **The transport of piece charts to `F`, with the format/degree witnesses given.**  This is
`Work.WilG4c.PieceChartsToF` with the two witnesses of `selPieceChart_obligations` supplied by the
caller (together with their specification `hz`/`hs`), so that the format
`aφ + a + A0 + (aψ + (aφ + a + A1))` and the degree
`(Dgφ + (p+1)·Dg + C0) + (Dgψ + ((p+1)+n)·(Dgφ + (p+1)·Dg + C1) + C1)` of the conclusion are
known *in advance*. -/
theorem PieceChartsToFGiven (S : WilkiesDesign.SOMin) (p n k r : ℕ)
    (F : Family k p (n + 1)) (ψ : ChartTuple (p + 1) n) (φ : ChartTuple p 1)
    (P : Set (Fin p → ℝ)) (aψ Dgψ aφ Dgφ A0 C0 A1 C1 : ℕ)
    (hψg : ∀ j, famGraph (ψ j) ∈ S.Ω aψ Dgψ ((p + 1) + n + 1))
    (hφg : famGraph (φ 0) ∈ S.Ω aφ Dgφ (p + 1 + 1))
    (hz : ∀ (a Dg : ℕ) (χ : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
        famGraph χ ∈ S.Ω a Dg (p + (n + 1) + 1) →
        famGraph (fun l t => φ 0 l (fun _ => χ l t)) ∈
          S.Ω (aφ + a + A0) (Dgφ + (p + 1) * Dg + C0) (p + (n + 1) + 1))
    (hs : ∀ (a Dg : ℕ) (χ : ChartTuple p (n + 1)) (j : Fin n),
        (∀ i, famGraph (χ i) ∈ S.Ω a Dg (p + (n + 1) + 1)) →
        famGraph (fun l t => ψ j (Fin.snoc l (φ 0 l (fun _ => χ 0 l t)))
            (Fin.tail (fun i => χ i l t))) ∈
          S.Ω (aψ + (aφ + a + A1))
            (Dgψ + ((p + 1) + n) * (Dgφ + (p + 1) * Dg + C1) + C1)
            (p + (n + 1) + 1))
    (hφI : ∀ l ∈ P, ∀ t ∈ openCube 1, φ 0 l t ∈ I)
    (hψcube : ∀ l ∈ P, ∀ τ ∈ I, ∀ u ∈ openCube n,
      (fun j => ψ j (Fin.snoc l τ) u) ∈ openCube n)
    (a Dg : ℕ) (Ψ : Finset (ChartTuple p (n + 1)))
    (hΨ : ChartsOK S a Dg r P
      (pieceFam (yPullback F ψ) (fun l τ => φ 0 l (fun _ => τ))) Ψ) :
    ∃ (Φ : Finset (ChartTuple p (n + 1)))
        (sel : ChartTuple p (n + 1) → ChartTuple p (n + 1)),
      Φ.card ≤ Ψ.card ∧
      ChartsOK S (aφ + a + A0 + (aψ + (aφ + a + A1)))
        ((Dgφ + (p + 1) * Dg + C0)
          + (Dgψ + ((p + 1) + n) * (Dgφ + (p + 1) * Dg + C1) + C1)) r P F Φ ∧
      (∀ ψ' ∈ Ψ, sel ψ' ∈ Φ) ∧
      (∀ ψ' ∈ Ψ, ∀ l ∈ P, ∀ t ∈ openCube (n + 1), ∀ i,
        F i l (fun j => sel ψ' j l t)
          = pieceFam (yPullback F ψ) (fun l τ => φ 0 l (fun _ => τ)) i l
              (fun j => ψ' j l t)) := by
  classical
  refine ⟨Ψ.image (selPieceChart ψ φ), selPieceChart ψ φ, Finset.card_image_le, ?_, ?_, ?_⟩
  · intro φ' hφ'
    obtain ⟨ψ', hψ'Ψ, rfl⟩ := Finset.mem_image.mp hφ'
    have hψ'g : ∀ j, famGraph (ψ' j) ∈ S.Ω a Dg (p + (n + 1) + 1) := (hΨ ψ' hψ'Ψ).1
    have hψ'cube := (hΨ ψ' hψ'Ψ).2
    refine ⟨?_, fun l hl => ⟨?_, ?_⟩⟩
    · intro j
      refine Fin.cases ?_ ?_ j
      · rw [selPieceChart_zero]
        exact Omega_mono_le S (by omega) (by omega) (hz a Dg (ψ' 0) (hψ'g 0))
      · intro kk
        rw [selPieceChart_succ]
        exact Omega_mono_le S (by omega) (by omega) (hs a Dg ψ' kk hψ'g)
    · exact selPieceChart_mem_openCube ψ φ ψ' (hφI l hl) (hψcube l hl) (hψ'cube l hl).1
    · intro i
      obtain ⟨hC1, hC2⟩ := (hψ'cube l hl).2 i
      have hfe : (fun t => F i l (fun j => selPieceChart ψ φ ψ' j l t))
          = (fun t => pieceFam (yPullback F ψ) (fun l τ => φ 0 l (fun _ => τ)) i l
              (fun j => ψ' j l t)) := by
        funext t
        exact selPieceChart_apply F ψ φ ψ' i l t
      refine ⟨?_, ?_⟩
      · rw [hfe]; exact hC1
      · intro m hm t ht
        rw [hfe]; exact hC2 m hm t ht
  · intro ψ' hψ'
    exact Finset.mem_image_of_mem _ hψ'
  · intro ψ' hψ' l hl t ht i
    exact selPieceChart_apply F ψ φ ψ' i l t

/-- **The good-cell case of the §5.3 assembly.**  Given the `n`-dimensional F-lemma in the
`1`-Lipschitz form (`hP1`), a cell parameter set `P` (which is `Ω`-bounded at format `aΛ` and
degree `eval ![D,r] Dgpiece`), the `y`-chart `ψ` of the induction hypothesis, the cell chart `χ`, and
the *analytic conclusions* about the piece `pieceFam (yPullback F ψ) (chartFun χ)` on `P` (its
`Ω`-bounds, its Λ-restricted `YBound r`, its `C`-Lipschitzness on the cube and its values in
`(0,1)`), together with the exact cover of the cell chart (`hχcov`) and the `ε/2`-cover of the
`y`-fibre supplied by the induction hypothesis (`hih`), the cell contributes a finite family `Φ` of
charts of `F` on `P` with a polynomial cardinality bound in `D, r, k, -log ε` and an `ε`-cover of
`P × cube`.

**Degrees are polynomials, formats are constants.**  The `Ω`-bounds of the *inputs* of this step
(`ψ` from `YbCharts`, `χ` from `ChartsExactCell`, and the piece) all have degrees that depend on
`D` — e.g. `YbCharts` produces `famGraph (ψ j) ∈ S.Ω aψ (MvPolynomial.eval ![D, r] Dgψ) _`.  Hence
the parameters `Dgψ, Dgχ, Dgpiece : MvPolynomial (Fin 2) ℕ` and the three `Ω`-hypotheses below are
stated *inside* the `∀ D r k ε` scope, at `MvPolynomial.eval ![D, r] Dg…`.  The witnesses `a`, `b`,
`c` of the conclusion are still `D`-independent: the formats `aψ, aχ, aΛ, F0p` are constants (the
`Ω`-calculus only adds constants to formats), and the degree polynomial `b` is built from
`Dgψ, Dgχ, Dgpiece, b₁` by direct `MvPolynomial` arithmetic (no substitution needed), while the
count polynomial `c` is `c₁` with `X 3 ↦ X 3 + log 2` (the piece cover is run at `ε/2`) and
`c₁` is obtained from `ChartsOfPYLipOn`'s count at the piece's degree by `PolySubstFirst4`. -/
theorem GoodCellStep (S : WilkiesDesign.SOMin) (n p : ℕ)
    (hP1 : FLemP S p (n + 1) (PYLip p n))
    (F0p aΛ : ℕ)
    (aψ aχ : ℕ) (Dgψ Dgχ Dgpiece : MvPolynomial (Fin 2) ℕ)
    (C : ℝ) (hC : 1 ≤ C) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
      ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
      ∀ (P : Set (Fin p → ℝ)) (F : Family k p (n + 1))
        (ψ : ChartTuple (p + 1) n) (χ : ChartTuple p 1),
        P ∈ S.Ω aΛ (MvPolynomial.eval ![D, r] Dgpiece) p →
        (∀ j, famGraph (ψ j) ∈ S.Ω aψ (MvPolynomial.eval ![D, r] Dgψ) ((p + 1) + n + 1)) →
        (∀ l ∈ P, ∀ τ ∈ I, ∀ u ∈ openCube n,
          (fun j => ψ j (Fin.snoc l τ) u) ∈ openCube n) →
        (∀ j : Fin 1, famGraph (χ j) ∈ S.Ω aχ (MvPolynomial.eval ![D, r] Dgχ) (p + 1 + 1)) →
        (∀ l ∈ P, ∀ t ∈ openCube 1, χ 0 l t ∈ I) →
        (∀ i, famGraph (pieceFam (yPullback F ψ) (chartFun χ) i)
          ∈ S.Ω F0p (MvPolynomial.eval ![D, r] Dgpiece) (p + (n + 1) + 1)) →
        (∀ i, ∀ l ∈ P, ∀ x ∈ I, ∀ m, m ≤ r → ∀ y ∈ openCube n,
          ‖iteratedFDeriv ℝ m (slice (pieceFam (yPullback F ψ) (chartFun χ) i l) x) y‖ ≤ 1) →
        (∀ i, ∀ l ∈ P, ∀ z ∈ openCube (n + 1), ∀ z' ∈ openCube (n + 1),
          |pieceFam (yPullback F ψ) (chartFun χ) i l z
            - pieceFam (yPullback F ψ) (chartFun χ) i l z'| ≤ C * dist z z') →
        ValuesIn01 P (pieceFam (yPullback F ψ) (chartFun χ)) →
        (∀ l ∈ P, ∀ s ∈ I, ∃ τ ∈ I, chartFun χ l τ = s) →
        (∀ l ∈ P, ∀ s ∈ I, ∀ y ∈ openCube n,
          ∃ y' ∈ openCube n, ∀ i,
            |F i l (pt s (fun j => ψ j (Fin.snoc l s) y')) - F i l (pt s y)| < ε / 2) →
        ∃ Φ : Finset (ChartTuple p (n + 1)),
          (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
          ChartsOK S a (MvPolynomial.eval ![D, r] b) r P F Φ ∧
          (∀ l ∈ P, ∀ s ∈ I, ∀ y ∈ openCube n,
            ∃ φ ∈ Φ, ∃ t ∈ openCube (n + 1),
              ∀ i, |F i l (fun j => φ j l t) - F i l (pt s y)| < ε) := by
  classical
  obtain ⟨a₁, b₁ch, c₁ch, H₁⟩ :=
    ChartsOfPYLipOn S n p hP1 C hC F0p aΛ (MvPolynomial.X 0)
  obtain ⟨A₀, C₀, hz⟩ := selPieceChart_zero_mem S p n
  obtain ⟨A₁, C₁, hs⟩ := selPieceChart_succ_mem S p n
  -- the piece's degree is `eval ![D,r] Dgpiece`, so the polynomial witnesses of the
  -- `ChartsOfPYLipOn` call have to be composed with `Dgpiece`
  obtain ⟨b₁, hb₁⟩ := PolySubstFirst Dgpiece b₁ch
  obtain ⟨c₁, hc₁⟩ := PolySubstFirst4 Dgpiece c₁ch
  set bb : MvPolynomial (Fin 2) ℕ :=
    (Dgχ + MvPolynomial.C (p + 1) * b₁ + MvPolynomial.C C₀)
      + (Dgψ + MvPolynomial.C ((p + 1) + n)
            * (Dgχ + MvPolynomial.C (p + 1) * b₁ + MvPolynomial.C C₁)
          + MvPolynomial.C C₁) with hbb
  set cc : MvPolynomial (Fin 4) ℝ :=
    MvPolynomial.eval₂ MvPolynomial.C
      (fun i : Fin 4 => if i = 3 then MvPolynomial.X 3 + MvPolynomial.C (Real.log 2)
        else MvPolynomial.X i) c₁ with hcc
  refine ⟨aχ + a₁ + A₀ + (aψ + (aχ + a₁ + A₁)), bb, cc, ?_⟩
  intro D r k ε hε hε1 P F ψ χ hPmem hψg hψcube hχg hφI hGpiece hY hLip hvalpiece
    hχcov hih
  have hb_eval : MvPolynomial.eval ![D, r] bb
      = (MvPolynomial.eval ![D, r] Dgχ + (p + 1) * MvPolynomial.eval ![D, r] b₁ + C₀)
        + (MvPolynomial.eval ![D, r] Dgψ
            + ((p + 1) + n) * (MvPolynomial.eval ![D, r] Dgχ
              + (p + 1) * MvPolynomial.eval ![D, r] b₁ + C₁)
            + C₁) := by
    rw [hbb]
    simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  have hc_eval : MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cc
      = MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] c₁ := by
    rw [hcc, eval_eval₂_C_real]
    have hfun : (fun i : Fin 4 => MvPolynomial.eval
        ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε]
        (if i = 3 then MvPolynomial.X 3 + MvPolynomial.C (Real.log 2)
          else MvPolynomial.X i))
        = ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] := by
      funext i
      fin_cases i <;>
        simp [Real.log_div hε.ne' (by norm_num : (2 : ℝ) ≠ 0)] <;> ring
    rw [hfun]
  obtain ⟨Ψ, hΨcard0, hΨok0, hΨcov⟩ :=
    H₁ (MvPolynomial.eval ![D, r] Dgpiece) r k (ε / 2) (by linarith) (by linarith) P
      (pieceFam (yPullback F ψ) (chartFun χ)) (by simpa using hPmem) hGpiece hY hLip
      hvalpiece
  have hΨok : ChartsOK S a₁ (MvPolynomial.eval ![D, r] b₁) r P
      (pieceFam (yPullback F ψ) (chartFun χ)) Ψ :=
    ChartsOK_mono hΨok0 le_rfl (le_of_eq (hb₁ D r).symm)
  have hΨcard : (Ψ.card : ℝ)
      ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] c₁ := by
    rw [hc₁ D r k (-Real.log (ε / 2))]
    exact hΨcard0
  have hφg : famGraph (χ 0) ∈ S.Ω aχ (MvPolynomial.eval ![D, r] Dgχ) (p + 1 + 1) := hχg 0
  obtain ⟨Φ, sel, hΦcard, hΦok, hΦmem, hΦid⟩ :=
    PieceChartsToFGiven S p n k r F ψ χ P aψ (MvPolynomial.eval ![D, r] Dgψ) aχ
      (MvPolynomial.eval ![D, r] Dgχ) A₀ C₀ A₁ C₁ hψg hφg
      (fun (a Dg : ℕ) (χ' : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
          (hχ' : famGraph χ' ∈ S.Ω a Dg (p + (n + 1) + 1)) =>
        hz aχ (MvPolynomial.eval ![D, r] Dgχ) a Dg χ χ' hφg hχ')
      (fun (a Dg : ℕ) (χ' : ChartTuple p (n + 1)) (j : Fin n)
          (hχ' : ∀ i, famGraph (χ' i) ∈ S.Ω a Dg (p + (n + 1) + 1)) =>
        hs aψ (MvPolynomial.eval ![D, r] Dgψ) aχ (MvPolynomial.eval ![D, r] Dgχ) a Dg
          ψ χ χ' j hψg hφg hχ')
      hφI hψcube a₁ (MvPolynomial.eval ![D, r] b₁) Ψ hΨok
  refine ⟨Φ, ?_, ?_, ?_⟩
  · -- the cardinality bound: the transport does not increase the number of charts, and the
    -- substitution `-log ε ↦ -log (ε/2)` is absorbed by `cc`
    calc (Φ.card : ℝ) ≤ (Ψ.card : ℝ) := by exact_mod_cast hΦcard
      _ ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] c₁ := hΨcard
      _ = MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cc := hc_eval.symm
  · exact ChartsOK_mono hΦok le_rfl (by rw [hb_eval])
  · -- the two-step `ε`-cover
    intro l hl s hs y hy
    obtain ⟨y', hy'cube, hy'⟩ := hih l hl s hs y hy
    obtain ⟨τ, hτI, hτ⟩ := hχcov l hl s hs
    have hzcube : Fin.cons τ y' ∈ openCube (n + 1) := by
      intro j
      induction j using Fin.cases with
      | zero => exact hτI
      | succ j => simpa using hy'cube j
    obtain ⟨ψ', hψ'Ψ, t, ht, hcov⟩ := hΨcov l hl (Fin.cons τ y') hzcube
    refine ⟨sel ψ', hΦmem ψ' hψ'Ψ, t, ht, fun i => ?_⟩
    have h1 : F i l (fun j => sel ψ' j l t)
        = pieceFam (yPullback F ψ) (chartFun χ) i l (fun j => ψ' j l t) :=
      hΦid ψ' hψ'Ψ l hl t ht i
    have h2 : pieceFam (yPullback F ψ) (chartFun χ) i l (Fin.cons τ y')
        = F i l (pt s (fun j => ψ j (Fin.snoc l s) y')) := by
      have hpt : ∀ u : Fin n → ℝ, pt s u = Fin.cons s u := fun u => rfl
      simp only [hpt, pieceFam_apply, yPullback_apply, pullbackMap_apply,
        Fin.cons_zero, Fin.tail_cons, hτ]
    calc |F i l (fun j => sel ψ' j l t) - F i l (pt s y)|
        ≤ |F i l (fun j => sel ψ' j l t) - F i l (pt s (fun j => ψ j (Fin.snoc l s) y'))|
            + |F i l (pt s (fun j => ψ j (Fin.snoc l s) y')) - F i l (pt s y)| :=
          abs_sub_le _ _ _
      _ < ε / 2 + ε / 2 := by
          refine add_lt_add ?_ (hy' i)
          rw [h1, ← h2]
          exact hcov i
      _ = ε := by ring

end Work.WilG4c
