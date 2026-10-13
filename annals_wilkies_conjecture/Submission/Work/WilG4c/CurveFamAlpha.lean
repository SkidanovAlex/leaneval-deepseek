/-
  WilG4c — `CurveFamAlpha`: the multiindex `γ`-choice with the threshold alternative
  (BNZ §5.4, the `γ`-selection used by the `StepHigher` reduction).

  The mathematical content of this file is:

  * `AlDgList p n f L` (the graph of `iterDir L (famFunHat f)` over the interior of the
    `C^{|L|}`-locus, see `CurveFamAlphaDefs.lean`) is an `Ω`-set, by `SOMin.SharpDeriv`
    (`AlDgList_mem_sharp`);
  * the selection set `AlZset p n f L E` — the *exact* set appearing in the hypothesis of the
    statement: `y ∈ openCube n`, `xPt l x y` in the interior of the `C^{|L|}`-locus, and one of
    the three disjuncts of `threshAlt` — is an `Ω`-set (`AlphaZsetMem`, delegated);
  * `mem_AlZset_midx_iff` identifies membership of `xPt l x y` in `AlZset p n f (midx p n j M) E`
    with the cube/locus conditions plus `threshAlt p n f j M E l x y`.

  Hence `ChoiceHyp` applied to `AlZset` produces a definable `γ` whose graphs are `Ω`-bounded
  with format `AlA` and degree `MvPolynomial.eval ![D,r] (AlB ...)`, and the conclusion of
  `CurveFamAlpha` is precisely the statement that `γ l x` lies in the fibre of `AlZset` over
  `(l,x)` whenever that fibre is nonempty — which is what the hypothesis supplies.
-/
import Mathlib
import Submission.Work.WilG4c.StepHigherDefs
import Submission.Work.WilG4c.Engine
import Submission.Work.WilG4c.Hyps
import Submission.Work.WilG4c.LipDefs
import Submission.Work.WilG4c.CurveFamAlphaDefs
import Submission.Work.WilG4c.CurveFam
import Submission.Work.WilG4c.Alpha.AlphaViolMem
import Submission.Work.WilG4c.Alpha.AlphaViolIff
import Submission.Work.WilG4c.Alpha.AlphaZsetMem

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG5

/-! ## 1. The derivative graph of a list of directions is `Ω`-definable -/

/-- The list form `AlDgList` of the derivative graph is the `iteratedFDeriv` form `AlSDList`
(they differ only on the `C^{|L|}`-locus, where both are defined and
`iterDir_eq_iteratedFDeriv` applies). -/
theorem AlDgList_eq_AlSDList {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (p + (n + 1)))) : AlDgList p n f L = AlSDList p n f L := by
  ext z
  rw [mem_AlDgList, mem_AlSDList]
  have hcd : ∀ h : Fin.init z ∈ AlLoc p n f L.length,
      ContDiffAt ℝ L.length (famFunHat f) (Fin.init z) := by
    intro h
    have hh : Fin.init z ∈ interior {x : Fin (p + (n + 1)) → ℝ |
        ContDiffAt ℝ L.length (famFunHat f) x} := h
    simpa only [Set.mem_ofPred_eq] using interior_subset hh
  constructor
  · rintro ⟨hl, hz⟩
    exact ⟨hl, by rw [hz, Work.WilG4c.iterDir_eq_iteratedFDeriv L (famFunHat f)
      (Fin.init z) (hcd hl)]⟩
  · rintro ⟨hl, hz⟩
    exact ⟨hl, by rw [hz, ← Work.WilG4c.iterDir_eq_iteratedFDeriv L (famFunHat f)
      (Fin.init z) (hcd hl)]⟩

/-- **`SharpDeriv` at a fixed format.** For every family member whose graph is `Ω`-bounded with
format `F0` and degree `D`, the graph of `iterDir L (famFunHat f)` over the interior of the
`C^{|L|}`-locus is `Ω`-bounded with format `a1` and degree `MvPolynomial.eval ![D, |L|] b1`. -/
theorem AlDgList_mem_sharp (S : SOMin) (hder : S.SharpDeriv) (F0 p n : ℕ) :
    ∃ (a1 : ℕ) (b1 : MvPolynomial (Fin 2) ℕ), ∀ (D : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (p + (n + 1)))),
      graphOf (famFunHat f) ∈ S.Ω F0 D (p + (n + 1) + 1) →
      AlDgList p n f L ∈ S.Ω a1 (MvPolynomial.eval ![D, L.length] b1) (p + (n + 1) + 1) := by
  obtain ⟨a1, b1, h1⟩ := hder F0 (p + (n + 1))
  refine ⟨a1, b1, fun D f L hgraph => ?_⟩
  rw [AlDgList_eq_AlSDList]
  have h := h1 D (famFunHat f) hgraph L.length L.get
  simpa only [AlSDList, AlLoc] using h

/-- The `C^{|L|}`-locus is the projection of the derivative graph. -/
theorem projLast_AlDgList {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (p + (n + 1)))) : projLast (AlDgList p n f L) = AlLoc p n f L.length := by
  ext x
  constructor
  · rintro ⟨t, ht⟩
    rw [mem_AlDgList, Fin.init_snoc] at ht
    exact ht.1
  · intro hx
    exact ⟨iterDir L (famFunHat f) x, by
      rw [mem_AlDgList, Fin.init_snoc, Fin.snoc_last]; exact ⟨hx, rfl⟩⟩

/-! ## 2. The selection set spelled out -/

/-- The violation of the near-maximality disjunct of `threshAlt` read at `u`: some
`y' ∈ openCube n` with `zPt u y'` in the `C^{|L|}`-locus and
`2|∂^{α}u| < |∂^{α}(zPt u y')|`. -/
def AlViolProp (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (p + (n + 1)))) (u : Fin (p + (n + 1)) → ℝ) : Prop :=
  u ∈ AlLoc p n f L.length ∧
    ∃ y' : Fin n → ℝ, y' ∈ openCube n ∧ zPt p n u y' ∈ AlLoc p n f L.length ∧
      2 * |iterDir L (famFunHat f) u| < |iterDir L (famFunHat f) (zPt p n u y')|

/-- The unfolding of `AlZset` into the three disjuncts of `threshAlt` (given the description of
`AlViol` provided by `AlphaViolIff`). -/
theorem mem_AlZset_iff {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {L : List (Fin (p + (n + 1)))} {E : ℝ} {w : Fin (p + (n + 1)) → ℝ}
    (hV : ∀ u : Fin (p + (n + 1)) → ℝ, (u ∈ AlViol p n f L ↔ AlViolProp p n f L u)) :
    w ∈ AlZset p n f L E ↔ (fun j : Fin n => w (yIdx p n j)) ∈ openCube n ∧
      w ∈ AlLoc p n f L.length ∧
      (2 * E ≤ iterDir L (famFunHat f) w ∨ iterDir L (famFunHat f) w ≤ -(2 * E) ∨
        ∀ y' : Fin n → ℝ, y' ∈ openCube n → zPt p n w y' ∈ AlLoc p n f L.length →
          |iterDir L (famFunHat f) (zPt p n w y')| ≤ 2 * |iterDir L (famFunHat f) w|) := by
  rw [mem_AlZset, mem_AlAlt1_iff, mem_AlAlt2_iff, Set.mem_compl_iff]
  constructor
  · rintro ⟨hc, hl, h1 | h2 | h3⟩
    · exact ⟨hc, hl, Or.inl h1.2⟩
    · exact ⟨hc, hl, Or.inr (Or.inl h2.2)⟩
    · refine ⟨hc, hl, Or.inr (Or.inr ?_)⟩
      intro y' hy' hl'
      by_contra hcon
      exact h3 ((hV w).mpr ⟨hl, y', hy', hl', lt_of_not_ge hcon⟩)
  · rintro ⟨hc, hl, h1 | h2 | h3⟩
    · exact ⟨hc, hl, Or.inl ⟨hl, h1⟩⟩
    · exact ⟨hc, hl, Or.inr (Or.inl ⟨hl, h2⟩)⟩
    · refine ⟨hc, hl, Or.inr (Or.inr ?_)⟩
      intro hv
      obtain ⟨-, y', hy', hl', hlt⟩ := (hV w).mp hv
      exact absurd (h3 y' hy' hl') (not_le.mpr hlt)

/-- Membership of `xPt l x y` in `AlZset p n f (midx p n j M) E`, in the exact form used by
`CurveFamAlpha`. -/
theorem mem_AlZset_midx_iff {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (j : ℕ) (M : List (Fin n)) (E : ℝ) (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ)
    (hV : ∀ u : Fin (p + (n + 1)) → ℝ,
      (u ∈ AlViol p n f (midx p n j M) ↔ AlViolProp p n f (midx p n j M) u)) :
    xPt l x y ∈ AlZset p n f (midx p n j M) E ↔ y ∈ openCube n ∧
      xPt l x y ∈ interior {z | ContDiffAt ℝ (j + M.length) (famFunHat f) z} ∧
      threshAlt p n f j M E l x y := by
  rw [mem_AlZset_iff hV, threshAlt]
  simp only [zPt_xPt, xPt_yIdx, midx_length, AlLoc]
  all_goals (try push_cast)
  all_goals (try exact Iff.rfl)

/-! ## 3. The polynomial bookkeeping -/

/-- `MvPolynomial.eval` is monotone in the second argument, for polynomials with natural
coefficients. -/
theorem AlphaEvalMono (b : MvPolynomial (Fin 2) ℕ) {D k r : ℕ} (h : k ≤ r) :
    MvPolynomial.eval ![D, k] b ≤ MvPolynomial.eval ![D, r] b := by
  induction b using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add]; exact add_le_add hp hq
  | mul_X p i hp =>
      rw [map_mul, map_mul]
      refine Nat.mul_le_mul hp ?_
      fin_cases i
      · simp
      · simpa using h

/-- Composition of a univariate polynomial with a two-variable one: substitution commutes with
evaluation. -/
theorem AlphaEvalEval₂ {σ : Type*} (v : σ → ℕ) (bC : Polynomial ℕ)
    (P : MvPolynomial σ ℕ) :
    MvPolynomial.eval v (bC.eval₂ MvPolynomial.C P) = bC.eval (MvPolynomial.eval v P) := by
  induction bC using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [Polynomial.eval₂_add, map_add, hp, hq, Polynomial.eval_add]
  | monomial n a _ =>
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
        Polynomial.eval₂_pow, map_mul, map_pow, MvPolynomial.eval_C, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]

/-- The format bound of the graphs produced by `CurveFamAlpha`. -/
def AlA (p n aC : ℕ) : ℕ := aC + 64 * (((p + 1) + n) + (p + 1 + 1)) + 64

/-- The constant term of the degree bound; chosen so that it dominates every constant that
enters the format/degree bookkeeping of `AlDzs`. -/
def AlK1 (p n : ℕ) : ℕ := 100000 * (p + n + 2) + 100000

/-- The coefficient of `MvPolynomial.eval ![D, r] b1` in the degree bound; chosen so that it
dominates the coefficient `5` with which that quantity enters `AlDzs`. -/
def AlK2 : ℕ := 16

/-- The slack added to the degree bound. -/
def AlK3 (p n : ℕ) : ℕ := AlK1 p n

/-- The linear polynomial `K1 + K2 * b1`, i.e. `(D,r) ↦ K1 + K2 · eval ![D,r] b1`. -/
def AlP (p n : ℕ) (b1 : MvPolynomial (Fin 2) ℕ) : MvPolynomial (Fin 2) ℕ :=
  MvPolynomial.C (AlK1 p n) + MvPolynomial.C AlK2 * b1

/-- The degree bound supplied by `CurveFamAlpha`: `bC` composed with `K1 + K2·b1`, plus the
linear term itself (so that the bound dominates its own argument) and a constant slack. -/
def AlB (p n : ℕ) (b1 : MvPolynomial (Fin 2) ℕ) (bC : Polynomial ℕ) :
    MvPolynomial (Fin 2) ℕ :=
  AlP p n b1 + bC.eval₂ MvPolynomial.C (AlP p n b1) + MvPolynomial.C (AlK3 p n)

/-- The value of the degree bound `AlB` at `![D,r]`. -/
theorem eval_AlB (p n D r : ℕ) (b1 : MvPolynomial (Fin 2) ℕ) (bC : Polynomial ℕ) :
    MvPolynomial.eval ![D, r] (AlB p n b1 bC) =
      bC.eval (AlK1 p n + AlK2 * MvPolynomial.eval ![D, r] b1) +
        (AlK1 p n + AlK2 * MvPolynomial.eval ![D, r] b1) + AlK3 p n := by
  simp only [AlB, AlP, map_add, map_mul, AlphaEvalEval₂, MvPolynomial.eval_C]
  ring

end Work.WilkG4c

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG Work.WilkG4c Work.WilG5

theorem CurveFamAlpha (S : WilkiesDesign.SOMin) (hder : WilkiesDesign.SOMin.SharpDeriv S)
    (hchoice : Work.WilkG4c.ChoiceHyp S)
    (p n : ℕ) :
    ∀ F0 : ℕ, ∃ (A : ℕ) (B : MvPolynomial (Fin 2) ℕ),
      ∀ (D r : ℕ) (E : ℝ), 0 < E →
      ∀ (Λ : Set (Fin p → ℝ)) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
        WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
        ∀ (j : ℕ) (M : List (Fin n)), M.length + j ≤ r →
          ∃ γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ),
            (∀ i : Fin n, WilkiesDesign.graphOf (fun w : Fin (p + 1) → ℝ =>
                γ (fun k => w (Fin.castSucc k)) (w (Fin.last p)) i)
              ∈ S.Ω A (MvPolynomial.eval ![D, r] B) (p + 1 + 1)) ∧
            (∀ l ∈ Λ, ∀ x : ℝ,
              (∃ y : Fin n → ℝ, y ∈ WilkiesDesign.openCube n ∧
                Work.WilkG4c.xPt l x y ∈ interior {z | ContDiffAt ℝ (j + M.length)
                  (Work.WilkG4c.famFunHat f) z} ∧
                Work.WilkG4c.threshAlt p n f j M E l x y) →
              γ l x ∈ WilkiesDesign.openCube n ∧
              Work.WilkG4c.xPt l x (γ l x) ∈ interior {z | ContDiffAt ℝ (j + M.length)
                (Work.WilkG4c.famFunHat f) z} ∧
              Work.WilkG4c.threshAlt p n f j M E l x (γ l x)) := by
  intro F0
  obtain ⟨a1, b1, hAlDg⟩ := AlDgList_mem_sharp S hder F0 p n
  obtain ⟨aC, bC, hC⟩ := hchoice (AlFzs p n a1) (p + 1) n
  refine ⟨AlA p n aC, AlB p n b1 bC, ?_⟩
  intro D r E hE Λ f hΩ j M hjr
  have hPL : p + (n + 1) = (p + 1) + n := by omega
  have hgraph : graphOf (famFunHat f) ∈ S.Ω F0 D (p + (n + 1) + 1) := by
    rw [← famGraph_eq_graphOf_famFunHat]
    exact hΩ
  have hDg : AlDgList p n f (midx p n j M) ∈
      S.Ω a1 (MvPolynomial.eval ![D, (midx p n j M).length] b1) (p + (n + 1) + 1) :=
    hAlDg D f (midx p n j M) hgraph
  have hViol := Alpha.AlphaViolMem (f := f) (midx p n j M) hDg
  have hZs := Alpha.AlphaZsetMem (E := E) (f := f) (midx p n j M) hDg hViol
  have hZs' : (hPL ▸ AlZset p n f (midx p n j M) E) ∈
      S.Ω (AlFzs p n a1)
        (AlDzs p n (MvPolynomial.eval ![D, (midx p n j M).length] b1)) ((p + 1) + n) :=
    omega_ndrec hPL hZs
  obtain ⟨fsel, hsel, hGmem⟩ := hC
    (AlDzs p n (MvPolynomial.eval ![D, (midx p n j M).length] b1))
    (hPL ▸ AlZset p n f (midx p n j M) E) hZs'
  -- the degree inequality: this is the only place where `r` enters the picture
  have hβ : MvPolynomial.eval ![D, j + M.length] b1 ≤ MvPolynomial.eval ![D, r] b1 :=
    AlphaEvalMono b1 (by omega)
  have hK1 : AlDzs p n (MvPolynomial.eval ![D, (midx p n j M).length] b1) ≤
      AlK1 p n + AlK2 * MvPolynomial.eval ![D, r] b1 := by
    rw [midx_length]
    dsimp only [AlDzs, AlDu, AlDalt, AlDviol, AlK1, AlK2]
    omega
  have hmono : bC.eval (AlDzs p n (MvPolynomial.eval ![D, (midx p n j M).length] b1)) ≤
      bC.eval (AlK1 p n + AlK2 * MvPolynomial.eval ![D, r] b1) :=
    Work.WilG1.Polynomial.eval_mono hK1
  have hdeg : bC.eval (AlDzs p n (MvPolynomial.eval ![D, (midx p n j M).length] b1)) +
      (32 * (((p + 1) + n) + (p + 1 + 1)) + 32) ≤
      MvPolynomial.eval ![D, r] (AlB p n b1 bC) := by
    rw [eval_AlB]
    have hK3 : 32 * (((p + 1) + n) + (p + 1 + 1)) + 32 ≤ AlK3 p n := by
      dsimp only [AlK3, AlK1]
      omega
    omega
  refine ⟨fun l x => fsel (Fin.snoc l x), ?_, ?_⟩
  · intro i
    have hmem := coordImage_mem (S := S)
      (ι := Fin.snoc (fun k : Fin (p + 1) => Fin.castAdd n k) (Fin.natAdd (p + 1) i)) hGmem
    have hge : graphOf (fun w : Fin (p + 1) → ℝ =>
          fsel (Fin.snoc (Fin.init w) (w (Fin.last p))) i) =
        coordImage (Fin.snoc (fun k : Fin (p + 1) => Fin.castAdd n k) (Fin.natAdd (p + 1) i))
          {z : Fin ((p + 1) + n) → ℝ | ∀ k : Fin n,
            z (Fin.natAdd (p + 1) k) = fsel (fun k' => z (Fin.castAdd n k')) k} :=
      CurveFam.graphOf_sel_eq_coordImage fsel i
    have hfun : (fun w : Fin (p + 1) → ℝ =>
          (fun l x => fsel (Fin.snoc l x)) (fun k => w (Fin.castSucc k)) (w (Fin.last p)) i)
        = (fun w : Fin (p + 1) → ℝ =>
          fsel (Fin.snoc (Fin.init w) (w (Fin.last p))) i) := rfl
    rw [hfun, hge]
    exact mem_mono hmem (AlA p n aC) (MvPolynomial.eval ![D, r] (AlB p n b1 bC)) le_rfl hdeg
  · intro l hl x hx
    obtain ⟨y, hyc, hyl, hth⟩ := hx
    have hV : ∀ u : Fin (p + (n + 1)) → ℝ,
        (u ∈ AlViol p n f (midx p n j M) ↔ AlViolProp p n f (midx p n j M) u) :=
      fun u => Alpha.AlphaViolIff f (midx p n j M) u
    have hwit : Fin.append (Fin.snoc l x) y ∈ (hPL ▸ AlZset p n f (midx p n j M) E) := by
      rw [mem_ndrec, cast_snoc_append_xPt hPL]
      exact (mem_AlZset_midx_iff f j M E l x y hV).mpr ⟨hyc, hyl, hth⟩
    have hsel' := hsel (Fin.snoc l x) ⟨y, hwit⟩
    have hZs2 : xPt l x (fsel (Fin.snoc l x)) ∈ AlZset p n f (midx p n j M) E := by
      have h := (mem_ndrec hPL (AlZset p n f (midx p n j M) E)
        (Fin.append (Fin.snoc l x) (fsel (Fin.snoc l x)))).mp hsel'
      rwa [cast_snoc_append_xPt hPL] at h
    exact (mem_AlZset_midx_iff f j M E l x (fsel (Fin.snoc l x)) hV).mp hZs2

end Work.WilG4c
