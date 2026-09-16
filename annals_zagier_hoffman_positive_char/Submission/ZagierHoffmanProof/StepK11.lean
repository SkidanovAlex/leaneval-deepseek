import Submission.ZagierHoffmanProof.StepK10

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K11: the power-sum evaluation `Σ_{monic deg d} a^{-1} = 1/ℓ_d` (Thakur §5.9.1)

With `ℓ_d := ∏_{i=1}^d (X − X^{q^i})` (StepK10's `lFact`) and `U_d := Hsum F d 1 =
Σ_{p : monic deg d} p^{-1}` (StepB3's `Hsum`), the evaluation is

    (Eval)  Hsum F d 1 * (lFact F d : RatFunc F) = 1      (i.e. U_d = 1/ℓ_d)

Verified numerically (q ∈ {2,3,5}, d ≤ 4).  The clean induction on d uses the one-step
identity (also verified numerically):

    (Step)  U_d · (X − X^{q^d}) = U_{d−1}   for d ≥ 1,

together with `U_0 = 1` and `lFact_succ` (`ℓ_d = ℓ_{d−1}(X − X^{q^d})`).  This file
records both statements (sorry-free Prop forms) and the base-case claim; the proofs are
the next milestone (see PLAN Session 112 for the reduction analysis).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- the power-sum evaluation `U_d · ℓ_d = 1` (Thakur §5.9.1). -/
def EvalU (d : ℕ) : Prop :=
  Hsum F d 1 * ((lFact F d : F[X]) : RatFunc F) = 1

/-- the one-step reduction `U_d · (X − X^{q^d}) = U_{d−1}`. -/
def EvalStep (d : ℕ) : Prop :=
  Hsum F d 1 * (((X - X ^ ((Nat.card F) ^ d)) : F[X]) : RatFunc F) =
    Hsum F (d - 1) 1

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

lemma Hsum_zero_eq_one : Hsum F 0 1 = 1 := by
  classical
  -- HeadD F 0 is a singleton
  have hcard : Fintype.card (HeadD F 0) = 1 := by
    -- Subsingleton via head_zero_eq_one + Nonempty
    have hsub : Subsingleton (HeadD F 0) := ⟨by
      intro p q
      apply Subtype.ext
      exact (head_zero_eq_one F p).trans (head_zero_eq_one F q).symm⟩
    have hne : Nonempty (HeadD F 0) := ⟨⟨(1 : F[X]), ⟨Polynomial.monic_one, by simp⟩⟩⟩
    exact Fintype.card_eq_one_iff.mpr ⟨Classical.choice hne, by intro y; exact Subsingleton.elim _ _⟩
  calc
    Hsum F 0 1 = ∑ p : HeadD F 0, (((p.1 : RatFunc F) ^ 1)⁻¹) := by
          rfl
    _ = ∑ p : HeadD F 0, (1 : RatFunc F) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hz := head_zero_eq_one F p
          simp [hz]
    _ = (Fintype.card (HeadD F 0) : ℕ) • (1 : RatFunc F) := by
          rw [Finset.sum_const, Finset.card_univ]
    _ = 1 := by
          rw [hcard]
          simp


variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `Hsum F 1 1 = Σ_c (X + C c)^{-1}` in `RatFunc F`. -/
lemma Hsum_one_eq_sum_inv :
    letI : Fintype F := Fintype.ofFinite F
    Hsum F 1 1 = ∑ c : F, (((X + C c : F[X]) : RatFunc F)⁻¹) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let e : HeadD F 1 ≃ F := headD_one_equiv_F F
  dsimp [Hsum]
  rw [Fintype.sum_equiv e]
  intro x
  have hx : x.1 = X + C (e x) := by
    dsimp [e, headD_one_equiv_F, headOneConst]
    exact monic_deg_one_eq_X_add_C F x.1 x.2.1 x.2.2
  rw [hx]
  simp

/-- ★ `EvalStep` at d = 1: `U_1 · (X − X^q) = U_0 = 1`. -/
lemma EvalStep_one : EvalStep F 1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  dsimp [EvalStep]
  rw [pow_one]
  rw [Hsum_one_eq_sum_inv F]
  rw [Hsum_zero_eq_one F]
  have hpc (c : F) :
      (((X + C c : F[X]) : RatFunc F)⁻¹) *
          ((X - X ^ (Nat.card F) : F[X]) : RatFunc F) =
        -(((qPoly F c : F[X]) : RatFunc F)) := by
    have hx : (X - X ^ (Nat.card F) : F[X]) = -(carlitzOne F) := by
      dsimp [carlitzOne]
      ring
    have hcar : carlitzOne F ≠ 0 := by
      intro h0
      have hn := carlitzOne_natDegree F
      rw [h0, Polynomial.natDegree_zero] at hn
      have hq : 2 ≤ Nat.card F := card_ge_two F
      omega
    have hc0 : ((carlitzOne F : F[X]) : RatFunc F) ≠ 0 := by
      intro hz
      exact hcar (RatFunc.algebraMap_injective F (by simpa using hz))
    calc
      (((X + C c : F[X]) : RatFunc F)⁻¹) * ((X - X ^ (Nat.card F) : F[X]) : RatFunc F)
          = (((X + C c : F[X]) : RatFunc F)⁻¹) * (-(((carlitzOne F : F[X]) : RatFunc F))) := by
            rw [hx]
            have hneg : ((-(carlitzOne F) : F[X]) : RatFunc F) =
                -(((carlitzOne F : F[X]) : RatFunc F)) := by
              exact map_neg (algebraMap (F[X]) (RatFunc F)) (carlitzOne F)
            rw [hneg]
      _ = -(((qPoly F c : F[X]) : RatFunc F)) := by
            rw [rat_inv_X_add_C F c]
            field_simp [hc0]
  calc
    (∑ c : F, (((X + C c : F[X]) : RatFunc F)⁻¹)) *
        ((X - X ^ (Nat.card F) : F[X]) : RatFunc F)
        = ∑ c : F, ((((X + C c : F[X]) : RatFunc F)⁻¹) *
            ((X - X ^ (Nat.card F) : F[X]) : RatFunc F)) := by
          rw [Finset.sum_mul]
    _ = ∑ c : F, -(((qPoly F c : F[X]) : RatFunc F)) := by
          apply Finset.sum_congr rfl
          intro c hc
          exact hpc c
    _ = -(∑ c : F, ((qPoly F c : F[X]) : RatFunc F)) := by
          rw [Finset.sum_neg_distrib]
    _ = -((((∑ c : F, qPoly F c : F[X]) : RatFunc F))) := by
          exact congrArg (fun t : RatFunc F => -t)
            (map_sum (algebraMap (F[X]) (RatFunc F)) (fun c : F => qPoly F c) (Finset.univ : Finset F)).symm
    _ = -(((A F 1 : F[X]) : RatFunc F)) := by
          rw [sum_qPoly_eq_A_one F]
    _ = -((-1 : RatFunc F)) := by
          congr 1
          have hc := congrArg (fun p : F[X] => (p : RatFunc F)) (A_one_eq_neg_one F)
          have hn1 : ((-1 : F[X]) : RatFunc F) = (-1 : RatFunc F) := by
            calc
              ((-1 : F[X]) : RatFunc F) = -(((1 : F[X]) : RatFunc F)) := by
                    exact map_neg (algebraMap (F[X]) (RatFunc F)) (1 : F[X])
              _ = -1 := by
                    exact congrArg (fun x : RatFunc F => -x)
                      (map_one (algebraMap (F[X]) (RatFunc F)))
          rw [hn1] at hc
          exact hc
    _ = 1 := by
          simp


variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `ℓ_1 = X − X^q`. -/
lemma lFact_one : lFact F 1 = X - X ^ (Nat.card F) := by
  classical
  dsimp [lFact]
  simp

/-- ★ `EvalU` at d = 1: `U_1 · ℓ_1 = 1`, i.e. `P_1(1) = 1/ℓ_1`. -/
lemma EvalU_one : EvalU F 1 := by
  classical
  unfold EvalU
  rw [lFact_one F]
  have h1 := EvalStep_one F
  unfold EvalStep at h1
  rw [pow_one] at h1
  rw [Hsum_zero_eq_one F] at h1
  exact h1


end ZagierHoffmanPositiveChar
