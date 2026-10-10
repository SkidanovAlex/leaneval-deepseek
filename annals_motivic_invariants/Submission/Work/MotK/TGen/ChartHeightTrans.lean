import Mathlib
import Submission.Work.MotK.TGen.ChartHeightAux
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TGen

open MvPolynomial

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K]

/-- `finSuccEquiv` of a constant polynomial. -/
private lemma finSuccEquiv_C_aux {n : ℕ} (r : K) :
    MvPolynomial.finSuccEquiv K n (MvPolynomial.C r) =
      Polynomial.C (MvPolynomial.C r) := by
  rw [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]
  rfl

/-- `finSuccEquiv` applied to a polynomial that does not involve `X 0`, written as a `rename`
along `Fin.succ`. -/
private lemma rename_succ_aux {n : ℕ} (p : MvPolynomial (Fin n) K) :
    MvPolynomial.finSuccEquiv K n
      (MvPolynomial.rename (Fin.succ : Fin n → Fin (n + 1)) p) = Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C r => rw [MvPolynomial.rename_C, finSuccEquiv_C_aux]
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.C_add]
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.rename_X, hp, MvPolynomial.finSuccEquiv_X_succ,
        Polynomial.C_mul]

/-- `finSuccEquiv K 2` of the first two free variables of `Fin 3`. -/
private lemma fsX_2_1 :
    (MvPolynomial.finSuccEquiv K 2) (MvPolynomial.X (1 : Fin 3)) =
      Polynomial.C (MvPolynomial.X (0 : Fin 2)) :=
  MvPolynomial.finSuccEquiv_X_succ (R := K) (j := (0 : Fin 2))

/-- `finSuccEquiv K 2` of the last free variable of `Fin 3`. -/
private lemma fsX_2_2 :
    (MvPolynomial.finSuccEquiv K 2) (MvPolynomial.X (2 : Fin 3)) =
      Polynomial.C (MvPolynomial.X (1 : Fin 2)) :=
  MvPolynomial.finSuccEquiv_X_succ (R := K) (j := (1 : Fin 2))

theorem ChartHeightTrans (K : Type) [Field K] (a b H : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : H ≠ 0) :
    (MvPolynomial.finSuccEquiv K 4 (Work.MotK.TGen.G1v a b H) = Polynomial.C (Work.MotK.TGen.G1v4 a b H)) ∧
    (MvPolynomial.finSuccEquiv K 3 (Work.MotK.TGen.G1v4 a b H)
      = Polynomial.C (MvPolynomial.C (a ^ 2)) * Polynomial.X - Polynomial.C (Work.MotK.TGen.g13 a b H)) ∧
    (MvPolynomial.finSuccEquiv K 4 (Work.MotK.TGen.Av a b H) = Polynomial.C (Work.MotK.TGen.Av4 a b H)) ∧
    (MvPolynomial.finSuccEquiv K 3 (Work.MotK.TGen.Av4 a b H) = Polynomial.C (Work.MotK.TGen.Av3 a b H)) ∧
    (MvPolynomial.finSuccEquiv K 2 (Work.MotK.TGen.Av3 a b H)
      = -Polynomial.C (MvPolynomial.C (a * b)) * Polynomial.X ^ 2
        - Polynomial.C (MvPolynomial.C (b ^ 4 * H / a ^ 2) * MvPolynomial.X 0 * MvPolynomial.X 1) * Polynomial.X
        + Polynomial.C (MvPolynomial.C (a ^ 2) * MvPolynomial.X 1 - MvPolynomial.C (b ^ 3 * H / a) * (MvPolynomial.X 0) ^ 3)) ∧
    (MvPolynomial.finSuccEquiv K 4 (Work.MotK.TGen.Resv a b H) = Polynomial.C (Work.MotK.TGen.ResPoly4 a b H)) ∧
    (MvPolynomial.finSuccEquiv K 3 (Work.MotK.TGen.ResPoly4 a b H) = Polynomial.C (Work.MotK.TGen.ResPoly3 a b H)) ∧
    (MvPolynomial.finSuccEquiv K 2 (Work.MotK.TGen.ResPoly3 a b H) = Polynomial.C (Work.MotK.TGen.ResPoly a b H)) ∧
    (Work.MotK.TGen.Resv a b H ≠ 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : G1v a b H = MvPolynomial.rename (Fin.succ : Fin 4 → Fin 5) (G1v4 a b H) := by
      simp only [G1v, G1v4, map_sub, map_mul, map_pow, map_neg, MvPolynomial.rename_C,
        MvPolynomial.rename_X]
      rfl
    rw [h, rename_succ_aux]
  · have h : G1v4 a b H = MvPolynomial.C (a ^ 2) * MvPolynomial.X 0
        - MvPolynomial.rename (Fin.succ : Fin 3 → Fin 4) (g13 a b H) := by
      simp only [G1v4, g13, map_sub, map_add, map_mul, map_pow, map_neg, MvPolynomial.rename_C,
        MvPolynomial.rename_X]
      simp only [sub_eq_add_neg, neg_add, add_assoc]
      rfl
    rw [h]
    simp only [map_sub, map_mul, finSuccEquiv_C_aux, MvPolynomial.finSuccEquiv_X_zero,
      rename_succ_aux]
  · have h : Av a b H = MvPolynomial.rename (Fin.succ : Fin 4 → Fin 5) (Av4 a b H) := by
      simp only [Av, Av4, map_sub, map_add, map_mul, map_pow, map_neg, MvPolynomial.rename_C,
        MvPolynomial.rename_X]
      rfl
    rw [h, rename_succ_aux]
  · have h : Av4 a b H = MvPolynomial.rename (Fin.succ : Fin 3 → Fin 4) (Av3 a b H) := by
      simp only [Av4, Av3, map_sub, map_add, map_mul, map_pow, map_neg, MvPolynomial.rename_C,
        MvPolynomial.rename_X]
      rfl
    rw [h, rename_succ_aux]
  · simp only [Av3, map_sub, map_add, map_mul, map_pow, map_neg, finSuccEquiv_C_aux,
      MvPolynomial.finSuccEquiv_X_zero, fsX_2_1, fsX_2_2, Polynomial.C_add, Polynomial.C_mul,
      Polynomial.C_sub, Polynomial.C_neg, Polynomial.C_pow]
    first | refl_ring1 | ring
  · have h : Resv a b H = MvPolynomial.rename (Fin.succ : Fin 4 → Fin 5) (ResPoly4 a b H) := by
      simp only [Resv, ResPoly4, map_sub, map_add, map_mul, map_pow, map_neg,
        MvPolynomial.rename_C, MvPolynomial.rename_X]
      rfl
    rw [h, rename_succ_aux]
  · have h : ResPoly4 a b H = MvPolynomial.rename (Fin.succ : Fin 3 → Fin 4) (ResPoly3 a b H) := by
      simp only [ResPoly4, ResPoly3, map_sub, map_add, map_mul, map_pow, map_neg,
        MvPolynomial.rename_C, MvPolynomial.rename_X]
      rfl
    rw [h, rename_succ_aux]
  · have h : ResPoly3 a b H = MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (ResPoly a b H) := by
      simp only [ResPoly3, ResPoly, map_sub, map_add, map_mul, map_pow, map_neg,
        MvPolynomial.rename_C, MvPolynomial.rename_X]
      rfl
    rw [h, rename_succ_aux]
  · have hval : MvPolynomial.eval (fun _ : Fin 5 => (0 : K)) (Resv a b H) = -(a * b) ^ 3 := by
      simp only [Resv, map_add, map_sub, map_mul, map_pow, map_neg, MvPolynomial.eval_C,
        MvPolynomial.eval_X, Pi.zero_apply]
      first | refl_ring1 | ring
    intro h0
    rw [h0, map_zero] at hval
    exact pow_ne_zero 3 (mul_ne_zero ha hb) (neg_eq_zero.mp hval.symm)

end Work.MotK.TGen
