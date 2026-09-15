import Mathlib
import Submission.Commons.NumberTheory.Sieve.KPseudorandom_mean

namespace Commons.Combinatorics.Transference

open Commons.NumberTheory.Sieve

/-- The equivalence `(ZMod p × (Fin d → ZMod p)) ≃ (Fin (d+1) → ZMod p)` that puts the
first coordinate in front. -/
private def cubeEquiv (p d : ℕ) : (ZMod p × (Fin d → ZMod p)) ≃ (Fin (d + 1) → ZMod p) where
  toFun y := Fin.cons y.1 y.2
  invFun x := (x 0, Fin.tail x)
  left_inv y := by
    simp only [Fin.cons_zero, Fin.tail_cons, Prod.mk.eta]
  right_inv x := Fin.cons_self_tail x

/-- The coefficient vector of the linear form `x ↦ x 0 + ∑_j (if ω j then 1 else 0) * x (j+1)`. -/
private def cubeL (d : ℕ) (ω : Fin d → Bool) : Fin (d + 1) → ℚ :=
  Fin.cases 1 (fun j => if ω j then 1 else 0)

private lemma cubeL_zero (d : ℕ) (ω : Fin d → Bool) : cubeL d ω 0 = 1 := by
  simp only [cubeL, Fin.cases_zero]

private lemma cubeL_succ (d : ℕ) (ω : Fin d → Bool) (j : Fin d) :
    cubeL d ω j.succ = if ω j then 1 else 0 := by
  simp only [cubeL, Fin.cases_succ]

private lemma qmod_one {p : ℕ} [Fact p.Prime] : qmod p (1 : ℚ) = 1 := by
  simp [qmod]

private lemma qmod_ite {p : ℕ} [Fact p.Prime] (c : Bool) :
    qmod p (if c then (1 : ℚ) else 0) = if c then (1 : ZMod p) else 0 := by
  cases c <;> simp [qmod]

private lemma linForm_cubeL {p : ℕ} [Fact p.Prime] (d : ℕ) (ω : Fin d → Bool)
    (x : Fin (d + 1) → ZMod p) :
    linForm p (cubeL d ω) (0 : ZMod p) x
      = x 0 + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * x j.succ := by
  simp only [linForm, Fin.sum_univ_succ, cubeL_zero, cubeL_succ, qmod_ite, qmod_one,
    one_mul, add_zero]

private lemma isSmallRat_cubeL (d : ℕ) (ω : Fin d → Bool) (k : Fin (d + 1)) :
    IsSmallRat 1 (cubeL d ω k) := by
  refine Fin.cases (motive := fun k => IsSmallRat 1 (cubeL d ω k)) ?_ ?_ k
  · rw [cubeL_zero]; simp [IsSmallRat]
  · intro j
    rw [cubeL_succ]
    by_cases h : ω j
    · simp [h, IsSmallRat]
    · simp [h, IsSmallRat]

private lemma nonzeroTuple_cubeL (d : ℕ) (ω : Fin d → Bool) :
    NonzeroTuple (cubeL d ω) :=
  ⟨0, by rw [cubeL_zero]; norm_num⟩

private lemma notProp_cubeL (d : ℕ) {ω ω' : Fin d → Bool} (h : ω ≠ ω') :
    NotProp (cubeL d ω) (cubeL d ω') := by
  rintro ⟨lam, hlam⟩
  have h0 : lam = 1 := by
    have h1 := hlam 0
    rw [cubeL_zero, cubeL_zero, mul_one] at h1
    exact h1.symm
  apply h
  funext j
  have h1 := hlam j.succ
  rw [cubeL_succ, cubeL_succ, h0, one_mul] at h1
  cases hb : ω' j <;> cases hc : ω j <;> simp_all

theorem lfc_cube_free {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) {ν : ZMod p → ℝ} {ε : ℝ}
    (hLFC : Commons.NumberTheory.Sieve.LinFormsCond p ν (2 ^ d) (d + 1) 1 ε) :
    |((Fintype.card (ZMod p × (Fin d → ZMod p)) : ℝ))⁻¹ *
      (∑ y : ZMod p × (Fin d → ZMod p),
        ∏ ω : Fin d → Bool,
          ν (y.1 + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * y.2 j)) - 1|
      ≤ ε := by
  have hlt : 1 ≤ Fintype.card (Fin d → Bool) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    exact Nat.one_le_two_pow
  have hle : Fintype.card (Fin d → Bool) ≤ 2 ^ d := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  have hmain := hLFC (Fin d → Bool) hlt hle (d + 1) (by omega) le_rfl
      (cubeL d) (fun ω k => isSmallRat_cubeL d ω k)
      (fun ω => nonzeroTuple_cubeL d ω)
      (fun ω ω' hne => notProp_cubeL d hne)
      (fun _ => 0)
  have hsum : (∑ y : ZMod p × (Fin d → ZMod p),
        ∏ ω : Fin d → Bool,
          ν (y.1 + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * y.2 j))
      = ∑ x : Fin (d + 1) → ZMod p,
          ∏ ω : Fin d → Bool, ν (linForm p (cubeL d ω) (0 : ZMod p) x) := by
    rw [← Equiv.sum_comp (cubeEquiv p d) (fun x : Fin (d + 1) → ZMod p =>
          ∏ ω : Fin d → Bool, ν (linForm p (cubeL d ω) (0 : ZMod p) x))]
    refine Finset.sum_congr rfl ?_
    intro y _
    refine Finset.prod_congr rfl ?_
    intro ω _
    change ν (y.1 + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * y.2 j)
        = ν (linForm p (cubeL d ω) (0 : ZMod p) (Fin.cons y.1 y.2))
    congr 1
    rw [linForm_cubeL]
    simp only [Fin.cons_zero, Fin.cons_succ]
  rw [Fintype.card_congr (cubeEquiv p d), hsum]
  exact hmain

end Commons.Combinatorics.Transference
