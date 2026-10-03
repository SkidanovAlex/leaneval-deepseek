import Mathlib
import Submission.Work.Peluse.UControl.histPhase1Run
import Submission.Work.Peluse.UControl.petWindowBookkeeping

/-!
# The quadratic PET chain in the `d = 2` world

The chapter `PetChapter5` is consumed with the datum `levelOneDatum 2` and the level comparison
`level1Compare`, both of which live in the world where the degree of the PET chain is
*definitionally* `2` (`HistData 2 n`, `InitIdx 2 = Fin 1 ⊕ Fin 1`), while the chain of the workspace
starts from `petHistInit P hd : HistData P.natDegree 0`, whose degree is only *propositionally* `2`.

This file fixes the vocabulary of the `d = 2` world:

* `ini2` — the initial state (the analogue of `petHistInit` with the index type `InitIdx 2`),
  together with its slot functions `ini2SlotF` and base function `ini2Base`;
* `quadX1₂` — the state after the single step of the phase-1 chain;
* `termQ2` — the terminal slot polynomial (through `HistData.stepQ`, so that no membership proof of
  the terminal state is needed);
* the constants of the chapter (`qSp`, `qW`, `qD0`, `qCpw`, `qKc`, `qCstA`, `qCstB`, `qCst1`,
  `qKconst`, `qCne0`).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

/-! ## The constants of the chapter -/

/-- The `ℓ¹`-sum of the absolute values of the coefficients of `P`. -/
def qSp (P : Polynomial ℤ) : ℕ := P.support.sum (fun k => (P.coeff k).natAbs)

/-- The window-bookkeeping constant `W = (1 + Σ|coeff|)·c^d` with `c = 2`, `d = 2`. -/
def qW (P : Polynomial ℤ) : ℝ := (1 + (qSp P : ℝ)) * 4

/-- The shift constant of the initial state of the chain, at the parameters `(A, γ)`: the general
form `⌈(1 + Σ|coeff|)·c^2·(A/γ)⌉` of `ini2SB` at `c = 2`. -/
def qDc (P : Polynomial ℤ) (c : ℕ) (A γ : ℝ) : ℕ :=
  ⌈(1 + (qSp P : ℝ)) * (c : ℝ) ^ 2 * (A / γ)⌉₊

/-- The shift constant of the initial state of the chain, at the parameters `(A, γ)`. -/
def qD0 (P : Polynomial ℤ) (A γ : ℝ) : ℕ := qDc P 2 A γ

/-- The window-bookkeeping constant `petWinConst 2 W`. -/
def qCpw (P : Polynomial ℤ) : ℝ := petWinConst 2 (qW P)

/-- The corner radius `⌈2·Cpw⌉`. -/
def qKc (P : Polynomial ℤ) : ℕ := ⌈2 * qCpw P⌉₊

/-- The constant of the conclusion in the chain regime. -/
def qCstA (P : Polynomial ℤ) : ℝ := 2000 ^ 3 * 243 * (qCpw P) ^ 3

/-- The constant of the conclusion in the corner regime. -/
def qCstB (P : Polynomial ℤ) : ℝ := (2 * (qKc P : ℝ) + 1) ^ 3 * 27

/-- The constant `Cst₁` of the chapter: the maximum of the two regimes. -/
def qCst1 (P : Polynomial ℤ) : ℝ := max (qCstA P) (qCstB P)

/-- The constant of the shift bound. -/
def qKconst (P : Polynomial ℤ) : ℝ :=
  4 * |P.leadingCoeff| * ((qKc P : ℝ) * (2 * qCpw P) + 1) + (20 * (qSp P : ℝ) + 1)

/-- The polynomial constant `Cne₀` of the shift bound. -/
def qCne0 (P : Polynomial ℤ) : ℕ := ⌈qKconst P⌉₊ + 1

/-! ## The initial state in the `d = 2` world -/

/-- The **initial state of the quadratic PET chain**: the slots `y` (the `y¹`-slot, `Sum.inl`) and
`P` (the `Sum.inr` slot), at the empty history. -/
def ini2 (P : Polynomial ℤ) (hdeg : P.natDegree = 2) : HistData 2 0 where
  H := Finset.univ
  Q := fun j _ => match j with
    | Sum.inl i => (Polynomial.X ^ (i.val + 1)).map (MvPolynomial.C)
    | Sum.inr _ => P.map (MvPolynomial.C)
  hd := by
    intro x _
    rcases x.1 with i | i
    · show (((Polynomial.X : Polynomial ℤ) ^ (i.val + 1)).map
        (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 0) ℤ)).natDegree ≤ 2
      rw [Polynomial.natDegree_map_eq_of_injective (mvC_injective _), Polynomial.natDegree_X_pow]
      have := i.isLt
      omega
    · show (P.map (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 0) ℤ)).natDegree ≤ 2
      rw [Polynomial.natDegree_map_eq_of_injective (mvC_injective _)]
      omega
  hnc := by
    intro x _
    rcases x.1 with i | i
    · show 1 ≤ (((Polynomial.X : Polynomial ℤ) ^ (i.val + 1)).map
        (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 0) ℤ)).natDegree
      rw [Polynomial.natDegree_map_eq_of_injective (mvC_injective _), Polynomial.natDegree_X_pow]
      omega
    · show 1 ≤ (P.map (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 0) ℤ)).natDegree
      rw [Polynomial.natDegree_map_eq_of_injective (mvC_injective _)]
      omega

/-- The slot functions of the initial state: `F 1` on the `y`-slot and `F 2` on the `P`-slot. -/
def ini2SlotF (P : Polynomial ℤ) (hdeg : P.natDegree = 2) (F : Fin (P.natDegree + 1) → ℤ → ℂ) :
    (ini2 P hdeg).toSym.S.ι → ℤ → ℂ :=
  fun i => match i.1.1 with
    | Sum.inl _ => F ⟨1, by omega⟩
    | Sum.inr _ => F ⟨P.natDegree, Nat.lt_succ_self _⟩

/-- The base function of the initial state: `F 0` (constant in the trivial parameter). -/
def ini2Base (H : ℕ) (P : Polynomial ℤ) (F : Fin (P.natDegree + 1) → ℤ → ℂ) :
    WinTower H 0 → ℤ → ℂ :=
  fun _ => F ⟨0, Nat.succ_pos _⟩

/-- The state reached after the *single* step of the phase-1 chain of a quadratic `P`: the step at
the `y`-slot `(Sum.inl 0, 0)` of `ini2`. -/
def quadX1₂ (P : Polynomial ℤ) (hdeg : P.natDegree = 2) : HistData 2 1 :=
  (ini2 P hdeg).step (Sum.inl ⟨0, by norm_num⟩) 0 (Finset.mem_univ _)

/-- The shift polynomial of the terminal slot of the quadratic chain, as a polynomial identity. -/
def termQ2 (P : Polynomial ℤ) (hdeg : P.natDegree = 2) (h' : Fin 2 → Bool) :
    Polynomial (MvPolynomial (Fin 2) ℤ) :=
  (quadX1₂ P hdeg).stepQ (Sum.inr 0) (0 : Fin 1 → Bool) (Sum.inr 0) h'

/-! ## The length of the phase-1 chain -/

/-- The length of `phase1Chain` started at `X` is `histLen X` (the two recursions are the same). -/
lemma phase1Chain_fst {d : ℕ} (X : HState d) : (phase1Chain X).1 = X.1 + histLen X := by
  induction X using WellFounded.induction (HState.rel_wf d) with
  | h X ih =>
    by_cases hstop : X.2.IsLinearX ∨ Phase1Done X.2
    · rw [phase1Chain_eq_of X hstop, histLen_eq_of X hstop]
      simp
    · have hgo : HState.Go X := hstop
      rw [phase1Chain_eq_not X hgo, histLen_eq_not X hgo]
      have hih := ih (histStep X hgo) (X.2.weightH_step_sel_lt (histHne X hgo))
      simp only [histStep, HState.step] at hih ⊢
      omega

end

end Work.Peluse.UControl
