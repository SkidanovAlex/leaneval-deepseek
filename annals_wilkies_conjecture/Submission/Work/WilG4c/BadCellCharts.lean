/-
  WilG4c / `BadCellCharts` — the bad-cell (empty-interior) branch of the §5.3 assembly.

  The statement (verbatim, as requested) is at the bottom of the file.  The two mechanisms of
  the case split `interior (projLast κ) = ∅ ∨ (interior (projLast κ)).Nonempty` are

  * the *pin* branch (delegated, `Work.WilG4c.ThickCellCharts`): a graph cell is pinned with
    `Work.WilkG4c.PinPtOfCell` and the `n`-dimensional F-lemma `ih` is applied to the sliced
    family (`Work.WilG4c.PinCellStep`);
  * `Work.WilG4c.ThinCellCharts` (below) — the *section* branch: `cellSection_aux` at dimension
    `p` gives a parameter map `θ : ℝ^q → ℝ^p` with `q < p` covering `projLast κ`, `SectionChoice`
    a section `μ` of it, `HindUniform` the F-lemma at `q` parameters, and the charts are
    transferred back along `μ` and *clamped* off the section locus `{l | θ (μ l) = l}`
    (`Work.WilG4c.SectLocusMem`, delegated) to become valid on all of `Λ`.

  The clamped transfer is why the present statement (which only assumes `ValuesIn01 Λ F`, not
  `ValuesIn01 univ F`) needs the generalisation `ChartsOK_of_clamp`/`ClampChartsOK` below: the
  per-chart conditions are available only on `Λ ∩ P` (`P` the section locus), while the
  modification `if l ∈ P then φ l else 1/2` is `Ω`-legitimate precisely because `P` — and not
  `Λ ∩ P` — is `Ω`-bounded.
-/
import Mathlib
import Submission.Work.WilkG4c.PinCellCharts
import Submission.Work.WilG4c.StepLipHighMain
import Submission.Work.WilG4c.ThickCellCharts
import Submission.Work.WilG4c.SectLocusMem
import Submission.Work.WilG4c.CellSectionMain
import Submission.Work.WilG4c.SubstCharts
import Submission.Work.WilG4c.HindUniform
import Submission.Work.WilG4c.SectionChoice
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilG4c.StepLipAux
import Submission.Work.WilG4c.PolySubstBoth
import Submission.Work.WilG4c.ParamChartsOK
import Submission.Work.WilG4c.IteFamGraphMemGen
import Submission.Work.WilG4c.PerLambda.ChartsOK_extends
import Submission.Work.WilG4c.SectAux.PolyEvalSubst
import Submission.Work.WilG4c.SectAux.MvPolySubstVar
import Submission.Work.WilG4c.SectAux.MvPolySubstVar4
import Submission.Work.WilG4c.SectAux.PullFamGraphPolyK
import Submission.Work.WilG4c.SectAux.ParamSubstPoly
import Submission.Work.WilG4c.SectAux.ClampChartsPoly
import Submission.Work.WilkG4c.eval_mono
import Submission.Work.WilG1.Cell.isCell_of_mem_cylDecomp
import Submission.Work.WilE8.Sharp.CellTransport
import Submission.Work.WilG4a.CD.eval_bind_shift

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. Clamping the parameter variable with the chart conditions only on `Λ ∩ P`

`Work.WilG4c.PerLambda.ChartsOK_extends` (and its wrapper `SectAux.ClampChartsPoly`) transfer
the per-chart conditions from a *modification set* `Λ'` to the parameter set `Λ`, and therefore
demand those conditions on all of `Λ'`.  In the thin-cell branch the conditions are available
only on `Λ ∩ P`, while the modification must be made along the `Ω`-bounded set `P`.  The two
lemmas below are the corresponding generalisations: in `ChartsOK_of_clamp` the hypothesis `h` is
required only on `Λ ∩ P`, and `ClampChartsOK` produces the `Ω`-membership of the clamped charts
from `IteFamGraphMemGen`. -/

theorem ChartsOK_of_clamp {S : WilkiesDesign.SOMin} {p n k a Dg r : ℕ}
    {Λ P : Set (Fin p → ℝ)} {F : Work.WilkG4c.Family k p n}
    {Φ : Finset (Work.WilkG4c.ChartTuple p n)} {c : Fin n → ℝ}
    (hc : c ∈ WilkiesDesign.openCube n)
    (hval : Work.WilkG4c.ValuesIn01 Λ F)
    (mod : Work.WilkG4c.ChartTuple p n → Work.WilkG4c.ChartTuple p n)
    (hmod : ∀ φ, ∀ j : Fin n, ∀ l, l ∈ P → ∀ t : Fin n → ℝ, mod φ j l t = φ j l t)
    (hmodc : ∀ φ, ∀ j : Fin n, ∀ l, l ∉ P → ∀ t : Fin n → ℝ, mod φ j l t = c j)
    (hΩ : ∀ φ ∈ Φ, ∀ j : Fin n,
      WilkiesDesign.CG.famGraph ((mod φ) j) ∈ S.Ω a Dg (p + n + 1))
    (h : ∀ φ ∈ Φ, ∀ l, l ∈ Λ ∩ P →
      (∀ t ∈ WilkiesDesign.openCube n, (fun j => φ j l t) ∈ WilkiesDesign.openCube n) ∧
      ∀ i, ContDiffOn ℝ r (fun t => F i l (fun j => φ j l t)) (WilkiesDesign.openCube n) ∧
        ∀ m, m ≤ r → ∀ t ∈ WilkiesDesign.openCube n,
          ‖iteratedFDeriv ℝ m (fun t => F i l (fun j => φ j l t)) t‖ ≤ 1) :
    ∃ Φ' : Finset (Work.WilkG4c.ChartTuple p n),
      (∀ φ ∈ Φ, mod φ ∈ Φ') ∧ Φ'.card ≤ Φ.card ∧
      Work.WilkG4c.ChartsOK S a Dg r Λ F Φ' := by
  classical
  refine ⟨Φ.image mod, fun φ hφ => Finset.mem_image_of_mem mod hφ, Finset.card_image_le, ?_⟩
  rw [Work.WilkG4c.ChartsOK]
  intro φ' hφ'
  rw [Finset.mem_image] at hφ'
  obtain ⟨φ, hφ, rfl⟩ := hφ'
  refine ⟨fun j => hΩ φ hφ j, ?_⟩
  intro l hl
  by_cases hlP : l ∈ P
  · obtain ⟨hcube, hrest⟩ := h φ hφ l ⟨hl, hlP⟩
    have hpt : ∀ t : Fin n → ℝ, (fun j => mod φ j l t) = (fun j => φ j l t) :=
      fun t => funext (fun j => hmod φ j l hlP t)
    have hfun : ∀ i, (fun t : Fin n → ℝ => F i l (fun j => mod φ j l t))
        = (fun t : Fin n → ℝ => F i l (fun j => φ j l t)) :=
      fun i => funext (fun t => by
        congr 1
        funext j
        exact hmod φ j l hlP t)
    refine ⟨fun t ht => by rw [hpt t]; exact hcube t ht, ?_⟩
    intro i
    exact ⟨by rw [hfun i]; exact (hrest i).1,
      fun m hm t ht => by rw [hfun i]; exact (hrest i).2 m hm t ht⟩
  · have hconst : ∀ t : Fin n → ℝ, (fun j => mod φ j l t) = c :=
      fun t => funext (fun j => hmodc φ j l hlP t)
    refine ⟨fun t ht => by rw [hconst t]; exact hc, ?_⟩
    intro i
    have hfun : (fun t : Fin n → ℝ => F i l (fun j => mod φ j l t))
        = (fun _ : Fin n → ℝ => F i l c) := funext (fun t => by rw [hconst t])
    exact ⟨by rw [hfun]; exact contDiffOn_const,
      fun m hm t ht => by
        rw [hfun]
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · subst h0
          rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_pos (hval i l hl c hc).1]
          exact le_of_lt (hval i l hl c hc).2
        · rw [iteratedFDeriv_const_of_ne (ne_of_gt hpos) (F i l c)]
          simp⟩

/-- The clamping device of the thin-cell branch: replace a chart by the constant chart `1/2`
off the `Ω`-bounded set `P`, keeping it on `P`.  The per-chart conditions are needed only on
`Λ ∩ P`; the `Ω`-membership of the clamped coordinate graphs is `IteFamGraphMemGen`. -/
theorem ClampChartsOK (S : WilkiesDesign.SOMin) (p n k r : ℕ)
    (Λ P : Set (Fin p → ℝ)) (F : Work.WilkG4c.Family k p n)
    (a Dg aP dP : ℕ) (hPmem : P ∈ S.Ω aP dP p)
    (hval : Work.WilkG4c.ValuesIn01 Λ F)
    (ε : ℝ) (Φ : Finset (Work.WilkG4c.ChartTuple p n))
    (hΦ : Work.WilkG4c.ChartsOK S a Dg r (Λ ∩ P) F Φ)
    (hcov : Work.WilkG4c.Covers (Λ ∩ P) F Φ ε) :
    ∃ Φ' : Finset (Work.WilkG4c.ChartTuple p n),
      Φ'.card ≤ Φ.card ∧
      Work.WilkG4c.ChartsOK S (a + aP + 3 * (p + n + 1) + 3 * p + 6)
        (Dg + 2 * dP + 5) r Λ F Φ' ∧
      Work.WilkG4c.Covers (Λ ∩ P) F Φ' ε := by
  classical
  let sel : Work.WilkG4c.ChartTuple p n → Work.WilkG4c.ChartTuple p n :=
    fun φ j l t => if l ∈ P then φ j l t else (1 / 2 : ℝ)
  have hsel : ∀ (φ : Work.WilkG4c.ChartTuple p n) (j : Fin n) (l : Fin p → ℝ)
      (t : Fin n → ℝ), sel φ j l t = if l ∈ P then φ j l t else (1 / 2 : ℝ) :=
    fun _ _ _ _ => rfl
  have hmod : ∀ φ, ∀ j : Fin n, ∀ l, l ∈ P → ∀ t : Fin n → ℝ, sel φ j l t = φ j l t := by
    intro φ j l hl t
    simp only [hsel, hl, ite_true]
  have hmodc : ∀ φ, ∀ j : Fin n, ∀ l, l ∉ P → ∀ t : Fin n → ℝ,
      sel φ j l t = (fun _ : Fin n => (1 / 2 : ℝ)) j := by
    intro φ j l hl t
    simp only [hsel, hl, ite_false]
  have hc : (fun _ : Fin n => (1 / 2 : ℝ)) ∈ WilkiesDesign.openCube n := by
    intro j; norm_num
  have hΩ : ∀ φ ∈ Φ, ∀ j : Fin n, WilkiesDesign.CG.famGraph ((sel φ) j) ∈
      S.Ω (a + aP + 3 * (p + n + 1) + 3 * p + 6) (Dg + 2 * dP + 5) (p + n + 1) := by
    intro φ hφ j
    have hφmem : WilkiesDesign.CG.famGraph (φ j) ∈ S.Ω a Dg (p + n + 1) := (hΦ φ hφ).1 j
    exact Work.WilG4c.IteFamGraphMemGen S P (1 / 2 : ℝ) (fun _ : Fin 1 => φ j)
      (fun _ : Fin 1 => (sel φ) j) 0 aP dP a Dg hPmem hφmem
      (fun l t hl => hmod φ j l hl t) (fun l t hl => hmodc φ j l hl t)
  obtain ⟨Φ', hmem', hcard', hOK'⟩ :=
    ChartsOK_of_clamp (S := S) hc hval sel hmod hmodc hΩ
      (fun φ hφ l hl => (hΦ φ hφ).2 l hl)
  refine ⟨Φ', hcard', hOK', ?_⟩
  intro l hl x hx
  obtain ⟨φ, hφ, t, ht, hlt⟩ := hcov l hl x hx
  refine ⟨sel φ, hmem' φ hφ, t, ht, fun i => ?_⟩
  have hpt : (fun j : Fin n => sel φ j l t) = (fun j : Fin n => φ j l t) :=
    funext (fun j => hmod φ j l hl.2 t)
  rw [hpt]
  exact hlt i

/-! ## 2. The `(D,r)`-polynomial reading of a twice-shifted degree

The pin/section bookkeeping turns the `Ω`-degree `eval ![D, A] b`, where `A` is *itself* the
value `eval ![D,r] d` of a polynomial, into the evaluation of a single polynomial in `(D,r)`:
the substitution `X₀ ↦ X₀ + d`, `X₁ ↦ X₁ + d` does this, at the cost of enlarging the point
from `(D, A)` to `(D + A, r + A)`. -/

theorem eval_aeval_shift_le (b d : MvPolynomial (Fin 2) ℕ) (D r : ℕ) :
    MvPolynomial.eval ![D, MvPolynomial.eval ![D, r] d] b ≤
      MvPolynomial.eval ![D, r]
        (MvPolynomial.aeval ![MvPolynomial.X 0 + d, MvPolynomial.X 1 + d] b) := by
  rw [Work.WilG4a.CD.eval_aeval_eq]
  have hfun : (fun i : Fin 2 =>
        MvPolynomial.eval ![D, r] (![MvPolynomial.X 0 + d, MvPolynomial.X 1 + d] i))
      = ![D + MvPolynomial.eval ![D, r] d, r + MvPolynomial.eval ![D, r] d] := by
    funext i
    fin_cases i <;> simp [MvPolynomial.eval_add, MvPolynomial.eval_X]
  rw [hfun]
  refine Work.WilkG4c.eval_mono b (fun i => ?_)
  fin_cases i <;> simp

/-! ## 3. The thin-cell (section) branch -/

theorem ThinCellCharts (S : WilkiesDesign.SOMin) (hchoice : Work.WilkG4c.ChoiceHyp S)
    (n p : ℕ)
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
        (hthin : interior (WilkiesDesign.projLast κ) = ∅),
        ∃ Φ : Finset (Work.WilkG4c.ChartTuple p (n + 1)),
          (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
          Work.WilkG4c.ChartsOK S a (MvPolynomial.eval ![D, r] b) r Λ F Φ ∧
          (∀ l ∈ Λ, ∀ x ∈ WilkiesDesign.openCube (n + 1), Fin.snoc l (x 0) ∈ κ →
            ∃ φ ∈ Φ, ∃ t ∈ WilkiesDesign.openCube (n + 1),
              ∀ i, |F i l (fun j => φ j l t) - F i l x| < ε) := by
  classical
  -- ## (0) the outer data, chosen before `D r k ε Λ F κ`
  obtain ⟨a_sec, b_sec, H_sec⟩ := cellSection_aux S p (F1 + 1)
  obtain ⟨bθ, hbθ⟩ := PolySubstBoth dc (MvPolynomial.C 1) b_sec
  have hSC : ∀ q : ℕ, ∃ (aμ : ℕ) (bμ : Polynomial ℕ),
      ∀ (D' : ℕ) (θ : (Fin q → ℝ) → (Fin p → ℝ)),
        (∀ j : Fin p, WilkiesDesign.graphOf (fun ν : Fin q → ℝ => θ ν j) ∈
          S.Ω a_sec D' (q + 1)) →
        ∃ μ : (Fin p → ℝ) → (Fin q → ℝ),
          (∀ l : Fin p → ℝ, (∃ ν : Fin q → ℝ, θ ν = l) → θ (μ l) = l) ∧
          (∀ j : Fin q, WilkiesDesign.graphOf (fun l : Fin p → ℝ => μ l j) ∈
            S.Ω aμ (bμ.eval D') (p + 1)) :=
    fun q => SectionChoice S hchoice p q a_sec
  choose fAμ fbμP hSCs using hSC
  have hbμspec : ∀ q : ℕ, ∃ b' : MvPolynomial (Fin 2) ℕ, ∀ x y : ℕ,
      MvPolynomial.eval ![x, y] b' = (fbμP q).eval (MvPolynomial.eval ![x, y] bθ) :=
    fun q => Work.WilG4c.SectAux.PolyEvalSubst (fbμP q) bθ
  choose fbμ hbμeq using hbμspec
  have hPFspec : ∀ q : ℕ, ∃ (C₁ C₂ : ℕ),
      ∀ (k : ℕ) (Aθ : ℕ) (bθ' : MvPolynomial (Fin 2) ℕ) (F0' : ℕ) (D r : ℕ)
        (F : Work.WilkG4c.Family k p (n + 1)) (θ : (Fin q → ℝ) → (Fin p → ℝ)),
        (∀ i, WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0' D (p + (n + 1) + 1)) →
        (∀ j : Fin p, WilkiesDesign.graphOf (fun ν : Fin q → ℝ => θ ν j) ∈
          S.Ω Aθ (MvPolynomial.eval ![D, r] bθ') (q + 1)) →
        ∀ i, WilkiesDesign.CG.famGraph
            (fun (ν : Fin q → ℝ) (y : Fin (n + 1) → ℝ) => F i (θ ν) y) ∈
          S.Ω (F0' + Aθ + C₁)
            (MvPolynomial.eval ![D, r]
              (MvPolynomial.X 0 + MvPolynomial.C (p + (n + 1) + 1) * bθ'
                + MvPolynomial.C C₂)) (q + (n + 1) + 1) :=
    fun q => Work.WilG4c.SectAux.PullFamGraphPolyK S p q (n + 1)
  choose c1F c2F hPFu using hPFspec
  have hPMspec : ∀ q : ℕ, ∃ (AP : ℕ) (DP : ℕ),
      ∀ (Aθ : ℕ) (bθ' : MvPolynomial (Fin 2) ℕ) (Aμ : ℕ) (bμ : MvPolynomial (Fin 2) ℕ)
        (D r : ℕ) (θ : (Fin q → ℝ) → (Fin p → ℝ)) (μ : (Fin p → ℝ) → (Fin q → ℝ)),
        (∀ j : Fin p, WilkiesDesign.graphOf (fun ν : Fin q → ℝ => θ ν j) ∈
          S.Ω Aθ (MvPolynomial.eval ![D, r] bθ') (q + 1)) →
        (∀ j : Fin q, WilkiesDesign.graphOf (fun l : Fin p → ℝ => μ l j) ∈
          S.Ω Aμ (MvPolynomial.eval ![D, r] bμ) (p + 1)) →
        {l : Fin p → ℝ | θ (μ l) = l} ∈
          S.Ω (Aθ + Aμ + AP)
            (MvPolynomial.eval ![D, r]
              (MvPolynomial.C p * (bθ' + MvPolynomial.C q * bμ)
                + MvPolynomial.C DP)) p :=
    fun q => SectLocusMem S p q
  choose fAP fDP hPMu using hPMspec
  have hPSspec : ∀ q : ℕ, ∃ (C₁ C₂ : ℕ),
      ∀ (Aμ : ℕ) (bμ : MvPolynomial (Fin 2) ℕ) (a : ℕ) (bχ : MvPolynomial (Fin 2) ℕ)
        (D r : ℕ) (μ : (Fin p → ℝ) → (Fin q → ℝ)) (χ : Work.WilkG4c.ChartTuple q (n + 1)),
        (∀ j : Fin q, WilkiesDesign.graphOf (fun l : Fin p → ℝ => μ l j) ∈
          S.Ω Aμ (MvPolynomial.eval ![D, r] bμ) (p + 1)) →
        (∀ j : Fin (n + 1), WilkiesDesign.CG.famGraph (χ j) ∈
          S.Ω a (MvPolynomial.eval ![D, r] bχ) (q + (n + 1) + 1)) →
        ∀ j : Fin (n + 1), WilkiesDesign.CG.famGraph
            (fun (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) => χ j (μ l) t) ∈
          S.Ω (Aμ + a + C₁)
            (MvPolynomial.eval ![D, r]
              (bχ + MvPolynomial.C (q + (n + 1)) * bμ + MvPolynomial.C C₂))
            (p + (n + 1) + 1) :=
    fun q => Work.WilG4c.SectAux.ParamSubstPoly S p q (n + 1)
  choose c1S c2S hPSu using hPSspec
  -- the uniform (in `q < p`) format level and degree polynomials
  set F0u : ℕ := ∑ x ∈ Finset.range p, (F0 + a_sec + c1F x) with hF0u
  set bDu : MvPolynomial (Fin 2) ℕ := ∑ x ∈ Finset.range p,
      (MvPolynomial.X 0 + MvPolynomial.C (p + (n + 1) + 1) * bθ
        + MvPolynomial.C (c2F x)) with hbDu
  obtain ⟨A, B, Chind, hHind⟩ := HindUniform S n p hind F0u
  obtain ⟨bχ, hbχ⟩ := Work.WilG4c.SectAux.MvPolySubstVar B bDu
  obtain ⟨cH, hcH⟩ := Work.WilG4c.SectAux.MvPolySubstVar4 Chind bDu
  set bPU : MvPolynomial (Fin 2) ℕ := ∑ x ∈ Finset.range p,
      (MvPolynomial.C p * (bθ + MvPolynomial.C p * fbμ x) + MvPolynomial.C (fDP x))
    with hbPU
  set bSubU : MvPolynomial (Fin 2) ℕ := ∑ x ∈ Finset.range p,
      (bχ + MvPolynomial.C (x + (n + 1)) * fbμ x + MvPolynomial.C (c2S x)) with hbSubU
  set FMT : ℕ → ℕ := fun x =>
      (fAμ x + A + c1S x) + (a_sec + fAμ x + fAP x) + 3 * (p + (n + 1) + 1) + 3 * p + 6
    with hFMT
  refine ⟨∑ x ∈ Finset.range p, FMT x,
    bSubU + MvPolynomial.C 2 * bPU + MvPolynomial.C 5, cH, ?_⟩
  intro D r k ε hε hε1 hr Λ F hΩg hPY hval C hCdec κ hκC hκΩ hκcube hκint hthin
  -- ## (1) the cell section of `projLast κ`
  have hκcell : WilkiesDesign.IsCell (p + 1) κ :=
    Work.WilG1.Cell.isCell_of_mem_cylDecomp hCdec hκC
  have hZcell : WilkiesDesign.IsCell p (WilkiesDesign.projLast κ) :=
    Work.WilE8.Sharp.isCell_projLast hκcell
  have hZΩ : WilkiesDesign.projLast κ ∈ S.Ω (F1 + 1) (MvPolynomial.eval ![D, r] dc) p :=
    S.proj hκΩ
  obtain ⟨q, θ, hq, hθgraw, hθcov⟩ :=
    H_sec (MvPolynomial.eval ![D, r] dc) (WilkiesDesign.projLast κ) hZcell hZΩ hthin
  have hθg : ∀ j : Fin p, WilkiesDesign.graphOf (fun ν : Fin q → ℝ => θ ν j) ∈
      S.Ω a_sec (MvPolynomial.eval ![D, r] bθ) (q + 1) := by
    intro j
    have hpt : ![(MvPolynomial.eval ![D, r] dc : ℕ), MvPolynomial.eval ![D, r] (MvPolynomial.C 1)]
        = ![(MvPolynomial.eval ![D, r] dc : ℕ), 1] := by
      funext i
      fin_cases i <;> simp
    rw [hbθ D r, hpt]
    exact hθgraw j
  obtain ⟨μ, hsel, hμgraww⟩ := hSCs q (MvPolynomial.eval ![D, r] bθ) θ hθg
  have hμg : ∀ j : Fin q, WilkiesDesign.graphOf (fun l : Fin p → ℝ => μ l j) ∈
      S.Ω (fAμ q) (MvPolynomial.eval ![D, r] (fbμ q)) (p + 1) := by
    intro j
    rw [hbμeq q D r]
    exact hμgraww j
  -- ## (2) the section locus
  set P : Set (Fin p → ℝ) := {l : Fin p → ℝ | θ (μ l) = l} with hP
  have hPiff : ∀ l : Fin p → ℝ, l ∈ P ↔ θ (μ l) = l := fun l => by simp [hP]
  -- ## (3) the pulled-back family, and the F-lemma at `q` parameters
  set Fp : Work.WilkG4c.Family k q (n + 1) := fun i ν y => F i (θ ν) y with hFp
  have hΩFp : ∀ i, WilkiesDesign.CG.famGraph (Fp i) ∈
      S.Ω F0u (MvPolynomial.eval ![D, r] bDu) (q + (n + 1) + 1) := by
    intro i
    have h1 : F0 + a_sec + c1F q ≤ F0u := by
      let g1 : ℕ → ℕ := fun x => F0 + a_sec + c1F x
      show g1 q ≤ F0u
      rw [hF0u]
      exact Finset.single_le_sum (fun x _ => Nat.zero_le _) (Finset.mem_range.mpr hq)
    have h2 : MvPolynomial.eval ![D, r]
          (MvPolynomial.X 0 + MvPolynomial.C (p + (n + 1) + 1) * bθ
            + MvPolynomial.C (c2F q))
        ≤ MvPolynomial.eval ![D, r] bDu := by
      let g2 : ℕ → ℕ := fun x => MvPolynomial.eval ![D, r]
        (MvPolynomial.X 0 + MvPolynomial.C (p + (n + 1) + 1) * bθ
          + MvPolynomial.C (c2F x))
      show g2 q ≤ MvPolynomial.eval ![D, r] bDu
      rw [hbDu, map_sum]
      exact Finset.single_le_sum (fun x _ => Nat.zero_le _) (Finset.mem_range.mpr hq)
    exact Work.WilkG4c.Omega_mono_le S h1 h2 (hPFu q k a_sec bθ F0 D r F θ hΩg hθg i)
  have hPYF : Work.WilkG4c.PY q n r k Fp := fun i ν => hPY i (θ ν)
  have hvalFp : Work.WilkG4c.ValuesIn01 {ν : Fin q → ℝ | θ ν ∈ Λ ∩ P} Fp := by
    intro i ν hν x hx
    have hν' : θ ν ∈ Λ ∩ P := hν
    exact hval i (θ ν) hν'.1 x hx
  obtain ⟨Φh, hcardT, hOKT, hcovT⟩ :=
    hHind q hq (MvPolynomial.eval ![D, r] bDu) r k ε hε hε1 hr
      {ν : Fin q → ℝ | θ ν ∈ Λ ∩ P} Fp hPYF hΩFp hvalFp
  -- ## (4) the `Ω`-conditions of the section-transferred charts
  have hbχD : MvPolynomial.eval ![MvPolynomial.eval ![D, r] bDu, r] B
      = MvPolynomial.eval ![D, r] bχ := by
    rw [← hbχ D r]
  have hχg : ∀ χ ∈ Φh, ∀ j : Fin (n + 1), WilkiesDesign.CG.famGraph (χ j) ∈
      S.Ω A (MvPolynomial.eval ![D, r] bχ) (q + (n + 1) + 1) := by
    intro χ hχ j
    have h := (hOKT χ hχ).1 j
    rwa [hbχD] at h
  have hΦ' : Work.WilkG4c.ChartsOK S (fAμ q + A + c1S q)
      (MvPolynomial.eval ![D, r] (bχ + MvPolynomial.C (q + (n + 1)) * fbμ q
        + MvPolynomial.C (c2S q))) r {ν : Fin q → ℝ | θ ν ∈ Λ ∩ P} Fp Φh := by
    refine Work.WilkG4c.ChartsOK_mono hOKT ?_ ?_
    · omega
    · simp only [hbχD, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
      omega
  have hΩχ : ∀ χ ∈ Φh, ∀ j : Fin (n + 1), WilkiesDesign.CG.famGraph
      (fun (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) => χ j (μ l) t) ∈
      S.Ω (fAμ q + A + c1S q) (MvPolynomial.eval ![D, r]
        (bχ + MvPolynomial.C (q + (n + 1)) * fbμ q + MvPolynomial.C (c2S q)))
        (p + (n + 1) + 1) :=
    fun χ hχ j => hPSu q (fAμ q) (fbμ q) A bχ D r μ χ hμg (hχg χ hχ) j
  -- ## (5) transfer along the section
  obtain ⟨Φ', hcard', hOK', hmem'⟩ :=
    Work.WilkG4c.ParamChartsOK S θ μ (Λ ∩ P) F (fun l hl => (hPiff l).mp hl.2) Φh hΩχ hΦ'
  have hcov' : Work.WilkG4c.Covers (Λ ∩ P) F Φ' ε := by
    intro l hl x hx
    have hθμ : θ (μ l) = l := (hPiff l).mp hl.2
    have hν : μ l ∈ {ν : Fin q → ℝ | θ ν ∈ Λ ∩ P} := by
      show θ (μ l) ∈ Λ ∩ P
      rw [hθμ]
      exact hl
    obtain ⟨χ, hχ, t, ht, hlt⟩ := hcovT (μ l) hν x hx
    refine ⟨fun j l' t' => χ j (μ l') t', hmem' χ hχ, t, ht, fun i => ?_⟩
    simpa only [hFp, hθμ] using hlt i
  -- ## (6) the section locus is `Ω`-bounded
  set bPq : MvPolynomial (Fin 2) ℕ :=
    MvPolynomial.C p * (bθ + MvPolynomial.C q * fbμ q) + MvPolynomial.C (fDP q) with hbPq
  have hPΩ : P ∈ S.Ω (a_sec + fAμ q + fAP q) (MvPolynomial.eval ![D, r] bPq) p := by
    rw [hP, hbPq]
    exact hPMu q a_sec bθ (fAμ q) (fbμ q) D r θ μ hθg hμg
  have hPΩ' : P ∈ S.Ω (a_sec + fAμ q + fAP q) (MvPolynomial.eval ![D, r] bPU) p := by
    refine Work.WilkG4c.Omega_mono_le S le_rfl ?_ hPΩ
    have hstep : MvPolynomial.eval ![D, r] bPq ≤
        MvPolynomial.eval ![D, r]
          (MvPolynomial.C p * (bθ + MvPolynomial.C p * fbμ q) + MvPolynomial.C (fDP q)) := by
      have h1 : q * MvPolynomial.eval ![D, r] (fbμ q)
          ≤ p * MvPolynomial.eval ![D, r] (fbμ q) := Nat.mul_le_mul_right _ (le_of_lt hq)
      have h2 : p * (q * MvPolynomial.eval ![D, r] (fbμ q))
          ≤ p * (p * MvPolynomial.eval ![D, r] (fbμ q)) := Nat.mul_le_mul_left p h1
      simp only [hbPq, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C,
        Nat.mul_add]
      omega
    have hsum : MvPolynomial.eval ![D, r]
          (MvPolynomial.C p * (bθ + MvPolynomial.C p * fbμ q) + MvPolynomial.C (fDP q))
        ≤ ∑ x ∈ Finset.range p, MvPolynomial.eval ![D, r]
            (MvPolynomial.C p * (bθ + MvPolynomial.C p * fbμ x) + MvPolynomial.C (fDP x)) := by
      let g3 : ℕ → ℕ := fun x => MvPolynomial.eval ![D, r]
        (MvPolynomial.C p * (bθ + MvPolynomial.C p * fbμ x) + MvPolynomial.C (fDP x))
      show g3 q ≤ ∑ x ∈ Finset.range p, g3 x
      exact Finset.single_le_sum (fun x _ => Nat.zero_le _) (Finset.mem_range.mpr hq)
    rw [hbPU, map_sum]
    exact le_trans hstep hsum
  -- ## (7) clamp
  obtain ⟨Φ'', hcard'', hOK'', hcov''⟩ :=
    ClampChartsOK S p (n + 1) k r Λ P F (fAμ q + A + c1S q)
      (MvPolynomial.eval ![D, r] (bχ + MvPolynomial.C (q + (n + 1)) * fbμ q
        + MvPolynomial.C (c2S q)))
      (a_sec + fAμ q + fAP q) (MvPolynomial.eval ![D, r] bPU)
      hPΩ' hval ε Φ' hOK' hcov'
  refine ⟨Φ'', ?_, ?_, ?_⟩
  · -- cardinality
    have hchain : (Φ''.card : ℝ) ≤ MvPolynomial.eval
        ![((MvPolynomial.eval ![D, r] bDu : ℕ) : ℝ), (r : ℝ), (k : ℝ), (-Real.log ε)] Chind :=
      le_trans (le_trans (Nat.cast_le.mpr hcard'') (Nat.cast_le.mpr hcard')) hcardT
    rw [hcH D r (k : ℝ) (-Real.log ε)]
    exact hchain
  · -- `ChartsOK`
    have hbSub_le : MvPolynomial.eval ![D, r]
          (bχ + MvPolynomial.C (q + (n + 1)) * fbμ q + MvPolynomial.C (c2S q))
        ≤ MvPolynomial.eval ![D, r] bSubU := by
      let g4 : ℕ → ℕ := fun x => MvPolynomial.eval ![D, r]
        (bχ + MvPolynomial.C (x + (n + 1)) * fbμ x + MvPolynomial.C (c2S x))
      show g4 q ≤ MvPolynomial.eval ![D, r] bSubU
      rw [hbSubU, map_sum]
      exact Finset.single_le_sum (fun x _ => Nat.zero_le _) (Finset.mem_range.mpr hq)
    have hdeg : MvPolynomial.eval ![D, r]
            (bχ + MvPolynomial.C (q + (n + 1)) * fbμ q + MvPolynomial.C (c2S q))
          + 2 * MvPolynomial.eval ![D, r] bPU + 5
        ≤ MvPolynomial.eval ![D, r] (bSubU + MvPolynomial.C 2 * bPU
            + MvPolynomial.C 5) := by
      have he : MvPolynomial.eval ![D, r] (bSubU + MvPolynomial.C 2 * bPU
            + MvPolynomial.C 5)
          = MvPolynomial.eval ![D, r] bSubU + 2 * MvPolynomial.eval ![D, r] bPU + 5 := by
        simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
      rw [he]
      omega
    refine Work.WilkG4c.ChartsOK_mono hOK'' ?_ hdeg
    · exact Finset.single_le_sum (f := FMT) (fun x _ => Nat.zero_le _)
        (Finset.mem_range.mpr hq)
  · -- the cover
    intro l hl x hx hmem
    obtain ⟨ν, hν⟩ := hθcov l ⟨x 0, hmem⟩
    have hlP : l ∈ P := (hPiff l).mpr (hsel l ⟨ν, hν⟩)
    exact hcov'' l ⟨hl, hlP⟩ x hx

/-- **The bad-cell branch of the `§5.3` assembly (pin/section).**

Let `F : Family k p (n+1)` have bounded `y`-derivatives (`PY`) and `Ω`-bounded graphs, and let
`κ` be a cell of a cylindrical decomposition `C` of `ℝ^{p+1}` (the `(λ,x)`-space, `x` the last
coordinate) with `κ ⊆ inCubeSet p 1` and `interior κ = ∅`.  Then `F` admits a finite family of
charts, valid on **all** of `Λ`, with the `FLemP` per-chart conditions, covering every cube point
whose distinguished coordinate lies in the cell's fibre.

Mechanisms: if `projLast κ` is thick then `κ` is a graph cell and one pins `x` with
`PinPtOfCell` and applies the `n`-dimensional F-lemma `ih` to the sliced family
(`PinCellCharts`); if `projLast κ` is thin then `cellSection_aux`/`CellSectionProp` at dimension
`p` gives a section `θ : ℝ^q → ℝ^p`, `q < p`, and `HindUniform` + `SectionChoice` + `SubstCharts`
give the charts from `hind` at `q`. -/
theorem BadCellCharts (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
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
        (hκcube : κ ⊆ Work.WilG4c.inCubeSet p 1) (hκint : interior κ = ∅),
        ∃ Φ : Finset (Work.WilkG4c.ChartTuple p (n + 1)),
          (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
          Work.WilkG4c.ChartsOK S a (MvPolynomial.eval ![D, r] b) r Λ F Φ ∧
          (∀ l ∈ Λ, ∀ x ∈ WilkiesDesign.openCube (n + 1), Fin.snoc l (x 0) ∈ κ →
            ∃ φ ∈ Φ, ∃ t ∈ WilkiesDesign.openCube (n + 1),
              ∀ i, |F i l (fun j => φ j l t) - F i l x| < ε)  := by
  obtain ⟨aT, bT, cT, HT⟩ := ThickCellCharts S hcd hder n p hn hchoice ih hind F0 F1 dc
  obtain ⟨aN, bN, cN, HN⟩ := ThinCellCharts S hchoice n p hind F0 F1 dc
  refine ⟨max aT aN, bT + bN, (cT * cT + cN * cN) + (cT + cN) + 1, ?_⟩
  intro D r k ε hε hε1 hr Λ F hΩg hPY hval C hCdec κ hκC hκΩ hκcube hκint
  by_cases hthick : (interior (WilkiesDesign.projLast κ)).Nonempty
  · obtain ⟨Φ, hcard, hOK, hcov⟩ :=
      HT D r k ε hε hε1 hr Λ F hΩg hPY hval C hCdec κ hκC hκΩ hκcube hκint hthick
    refine ⟨Φ, ?_, ?_, hcov⟩
    · simp only [map_add, map_mul, map_one]
      exact Work.WilkG4c.le_mergePoly_left _ _ _ hcard
    · refine Work.WilkG4c.ChartsOK_mono hOK (le_max_left _ _) ?_
      rw [MvPolynomial.eval_add]
      exact Nat.le_add_right _ _
  · have hthin : interior (WilkiesDesign.projLast κ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hthick
    obtain ⟨Φ, hcard, hOK, hcov⟩ :=
      HN D r k ε hε hε1 hr Λ F hΩg hPY hval C hCdec κ hκC hκΩ hκcube hκint hthin
    refine ⟨Φ, ?_, ?_, hcov⟩
    · simp only [map_add, map_mul, map_one]
      exact Work.WilkG4c.le_mergePoly_right _ _ _ hcard
    · refine Work.WilkG4c.ChartsOK_mono hOK (le_max_right _ _) ?_
      rw [MvPolynomial.eval_add]
      exact Nat.le_add_left _ _

end Work.WilG4c
