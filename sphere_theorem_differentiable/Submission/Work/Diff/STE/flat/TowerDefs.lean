import Mathlib
import Submission.Work.Diff.STE.FlatPDE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The formal time-derivative tower of the flat DeTurck nonlinearity

This module fixes the **vocabulary** of the smoothness/limit step
(`Work.Diff.STE.flat.limit_solves`): the formal time-derivative tower of the nonlinearity `Φ`
and the tower of Fourier-coefficient families of the limit solution.

## The tower of the nonlinearity

`towerExp Φ j` is the `j`-th formal time derivative of the nonlinearity along a solution, written
as a function of the space point `x` and of the spatial `2`-jets `Js = (J₀, …, J_{j-1})` of the
first `j` time derivatives `W₀, …, W_{j-1}` of the unknown.  The recursion is `H₁ = Φ` and

`H_{j+2}(x, J₀, …, J_{j+1}) = Σ_{i : Fin (j+1)} (D_i H_{j+1})(x, J₀, …, J_j) [J_{i+1}]`,

which is exactly the chain rule for `∂_t (H_{j+1}(x, jets of W₀, …, W_j))` once one knows
`∂_t J_i = J_{i+1}` (where `J_i` is the spatial `2`-jet of `W_i`).  The `(j+2)`-clause below is
this formula written with `fderiv`: the base point is the first `j+1` entries of `p.2` and the
`i`-th direction has `p.2 i.succ = J_{i+1}` in slot `i` and zeros elsewhere.

## The tower of the limit solution

Given the limit coefficient family `cinf : ℝ → (Fin n → ℤ) → MatC n` (produced by the
Arzelà–Ascoli step from the Galerkin solutions), `ddseq Φ cinf j t` is the list
`(dd Φ cinf 0 t, …, dd Φ cinf (j-1) t)` of the first `j` coefficient families of the tower,
`dd Φ cinf j` is the `j`-th one, and `W Φ cinf j t` is the corresponding matrix-valued Fourier
series.  The recursion is

`dd Φ cinf 0 t = cinf t`,
`dd Φ cinf (j+1) t = fourierCoeffM (fun x ↦ towerExp Φ (j+1) (x, jets of W Φ cinf 0 t, …, W Φ cinf j t))`,

i.e. the `(j+1)`-st time derivative of the solution, whose `x ↦ …` expression is the nonlinearity's
tower evaluated at the spatial jets of the first `j+1` time derivatives.

## What has to be proved about it (the route of `limit_solves`)

1. **Identification** (`seriesFunM (dd j t) = towerExp Φ j (x, jets)` for `j ≥ 1`): Fourier
   inversion `seriesFun_fourierCoeff` applied to the (smooth, `1`-periodic) function
   `x ↦ towerExp Φ j (x, …)`, which requires the tower expressions to be smooth in `x` — they are,
   because `x ↦ W i t x` is `C^∞` (from the decay bounds, `contDiff_seriesFun`) and `Φ` is smooth
   on the open set where `reMat` of the value component is invertible, a region in which the jets
   of the tower are confined (uniform positivity of `det`).
2. **Bounds**: for every `j` and `M` the coefficients of `dd Φ cinf j` decay like `⟨k⟩^{-M}`
   uniformly in `t`, by induction on `j` using the Moser composition estimate
   (`Work.Diff.STE.flat.CSq_comp_xperiodic_le`) applied to the tower expression of the
   nonlinearity, globalised to a globally smooth `x`-periodic function outside the jet region.
3. **Derivative tower** (`HasDerivWithinAt (fun s ↦ W Φ cinf j s x) (W Φ cinf (j+1) t x) (Ico 0 τ) t`):
   termwise differentiation in `t` (coefficient level) combined with the chain rule.

The consumption at the end is `Work.Diff.STE.flat.contDiffOn_series_tower`, which turns 2 and 3
into joint `C^∞` of `(t,x) ↦ W Φ cinf 0 t x` on the slab `Ico 0 τ ×ˢ univ`.
-/

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- **The formal time-derivative tower of the nonlinearity.**  `towerExp Φ j (x, Js)` is the
`j`-th formal time derivative of `Φ` along a solution, as a function of the space point `x` and of
the spatial `2`-jets `Js = (J₀, …, J_{j-1})` of the first `j` time derivatives of the unknown.
The recursion is `H₁ = Φ` and
`H_{j+2}(x, J₀, …, J_{j+1}) = Σ_{i : Fin (j+1)} (D_i H_{j+1})(x, J₀, …, J_j) [J_{i+1}]`
(the chain rule for `∂_t (H_{j+1}(x, jets))`, using `∂_t J_i = J_{i+1}`).  The `0`-th term is a
dummy value, never used. -/
noncomputable def towerExp (Φ : (Fin n → ℝ) × Jet n → MatC n) :
    (j : ℕ) → (Fin n → ℝ) × (Fin j → Jet n) → MatC n
  | 0, _ => 0
  | 1, p => Φ (p.1, p.2 0)
  | (j + 2), p =>
      ∑ i : Fin (j + 1),
        (fderiv ℝ (fun Js : Fin (j + 1) → Jet n => towerExp Φ (j + 1) (p.1, Js))
          (fun i' : Fin (j + 1) => p.2 i'.castSucc))
          (Function.update (0 : Fin (j + 1) → Jet n) i (p.2 i.succ))

@[simp] lemma towerExp_zero (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (p : (Fin n → ℝ) × (Fin 0 → Jet n)) : towerExp Φ 0 p = 0 := rfl

@[simp] lemma towerExp_one (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (p : (Fin n → ℝ) × (Fin 1 → Jet n)) : towerExp Φ 1 p = Φ (p.1, p.2 0) := rfl

lemma towerExp_succ_succ (Φ : (Fin n → ℝ) × Jet n → MatC n) (j : ℕ)
    (p : (Fin n → ℝ) × (Fin (j + 2) → Jet n)) :
    towerExp Φ (j + 2) p =
      ∑ i : Fin (j + 1),
        (fderiv ℝ (fun Js : Fin (j + 1) → Jet n => towerExp Φ (j + 1) (p.1, Js))
          (fun i' : Fin (j + 1) => p.2 i'.castSucc))
          (Function.update (0 : Fin (j + 1) → Jet n) i (p.2 i.succ)) := rfl

/-! ## The tower of coefficient families of a limit solution -/

/-- `ddseq Φ cinf j t` is the list `(dd Φ cinf 0 t, …, dd Φ cinf (j-1) t)` of the first `j`
coefficient families of the time-derivative tower of the limit solution.  The recursion is
`ddseq (j+1) = Fin.snoc (ddseq j) (dd j)` with `dd 0 = cinf`. -/
noncomputable def ddseq (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (cinf : ℝ → (Fin n → ℤ) → MatC n) : (j : ℕ) → ℝ → (Fin j → (Fin n → ℤ) → MatC n)
  | 0, _ => Fin.elim0
  | 1, t => fun _ => cinf t
  | (j + 2), t =>
      Fin.snoc (ddseq Φ cinf (j + 1) t)
        (fourierCoeffM (fun x : Fin n → ℝ => towerExp Φ (j + 1)
          (x, fun i : Fin (j + 1) => jetM (seriesFunM (ddseq Φ cinf (j + 1) t i)) x)))

@[simp] lemma ddseq_zero (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (cinf : ℝ → (Fin n → ℤ) → MatC n) (t : ℝ) : ddseq Φ cinf 0 t = Fin.elim0 := rfl

@[simp] lemma ddseq_one (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (cinf : ℝ → (Fin n → ℤ) → MatC n) (t : ℝ) (i : Fin 1) : ddseq Φ cinf 1 t i = cinf t := rfl

lemma ddseq_succ_succ (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (cinf : ℝ → (Fin n → ℤ) → MatC n) (j : ℕ) (t : ℝ) :
    ddseq Φ cinf (j + 2) t =
      Fin.snoc (ddseq Φ cinf (j + 1) t)
        (fourierCoeffM (fun x : Fin n → ℝ => towerExp Φ (j + 1)
          (x, fun i : Fin (j + 1) => jetM (seriesFunM (ddseq Φ cinf (j + 1) t i)) x))) :=
  rfl

/-- The `j`-th family of Fourier coefficients of the time-derivative tower of the limit solution. -/
noncomputable def dd (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (cinf : ℝ → (Fin n → ℤ) → MatC n) (j : ℕ) : ℝ → (Fin n → ℤ) → MatC n :=
  fun t => ddseq Φ cinf (j + 1) t (Fin.last j)

/-- The `j`-th time derivative of the limit solution, as a matrix-valued Fourier series. -/
noncomputable def W (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (cinf : ℝ → (Fin n → ℤ) → MatC n) (j : ℕ) (t : ℝ) : Torus n :=
  seriesFunM (dd Φ cinf j t)

lemma dd_eq_last (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (cinf : ℝ → (Fin n → ℤ) → MatC n) (j : ℕ) (t : ℝ) :
    dd Φ cinf j t = ddseq Φ cinf (j + 1) t (Fin.last j) := rfl

@[simp] lemma dd_zero (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (cinf : ℝ → (Fin n → ℤ) → MatC n) (t : ℝ) : dd Φ cinf 0 t = cinf t := rfl

lemma dd_succ (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (cinf : ℝ → (Fin n → ℤ) → MatC n) (j : ℕ) (t : ℝ) (k : Fin n → ℤ) :
    dd Φ cinf (j + 1) t k = fourierCoeffM (fun x : Fin n → ℝ => towerExp Φ (j + 1)
      (x, fun i : Fin (j + 1) => jetM (seriesFunM (ddseq Φ cinf (j + 1) t i)) x)) k := by
  show ddseq Φ cinf (j + 2) t (Fin.last (j + 1)) k = _
  rw [ddseq_succ_succ, Fin.snoc_last]

@[simp] lemma W_zero (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (cinf : ℝ → (Fin n → ℤ) → MatC n) (t : ℝ) : W Φ cinf 0 t = seriesFunM (cinf t) := rfl

@[simp] lemma W_apply (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (cinf : ℝ → (Fin n → ℤ) → MatC n) (j : ℕ) (t : ℝ) :
    W Φ cinf j t = seriesFunM (dd Φ cinf j t) := rfl

/-- Every member of the list `ddseq Φ cinf (m+1) t` is one of the tower families
`dd Φ cinf i t`. -/
lemma ddseq_apply (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (cinf : ℝ → (Fin n → ℤ) → MatC n) :
    ∀ (m : ℕ) (t : ℝ) (i : Fin (m + 1)), ddseq Φ cinf (m + 1) t i = dd Φ cinf i t
  | 0, t, i => by
      rw [Fin.fin_one_eq_zero i, ddseq_one]
      exact (dd_zero Φ cinf t).symm
  | (m + 1), t, i => by
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · rw [ddseq_succ_succ, Fin.snoc_castSucc]
        exact ddseq_apply Φ cinf m t j
      · show ddseq Φ cinf (m + 2) t (Fin.last (m + 1)) = ddseq Φ cinf (m + 2) t (Fin.last (m + 1))
        rfl

/-- The tower family `dd Φ cinf i t` as a member of the list `ddseq Φ cinf (m+1) t`, `i ≤ m`. -/
lemma dd_eq_ddseq {Φ : (Fin n → ℝ) × Jet n → MatC n}
    {cinf : ℝ → (Fin n → ℤ) → MatC n} {m : ℕ} {t : ℝ} (i : Fin (m + 1)) :
    dd Φ cinf i t = ddseq Φ cinf (m + 1) t i := (ddseq_apply Φ cinf m t i).symm

lemma W_eq_of_ddseq {Φ : (Fin n → ℝ) × Jet n → MatC n}
    {cinf : ℝ → (Fin n → ℤ) → MatC n} {m : ℕ} {t : ℝ} (i : Fin (m + 1)) :
    W Φ cinf i t = seriesFunM (ddseq Φ cinf (m + 1) t i) := by
  rw [W_apply, dd_eq_ddseq i]

end

end Work.Diff.STE.flat
