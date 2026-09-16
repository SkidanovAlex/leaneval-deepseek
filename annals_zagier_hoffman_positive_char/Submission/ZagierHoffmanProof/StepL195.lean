import Submission.ZagierHoffmanProof.StepK34
import Submission.ZagierHoffmanProof.StepB5
import Submission.ZagierHoffmanProof.StepB3
import Submission.ZagierHoffmanProof.StepL1

set_option autoImplicit false
set_option maxHeartbeats 4000000
open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# Step L195: the depth-one power sums in closed form

The committed power-sum evaluation `Hsum_closed` (StepK33) computes
`Hsum F d 1 = ∏_{i<d} (X − X^{q^{i+1}})⁻¹` in `RatFunc F`, and `P_eq_coe_Hsum`
(StepB3) identifies the depth-one power sum `P_d(1)` with its image in the
completion.  Consequently `P_d(1)` has the CLOSED FORM

    P_d(1) = (∏_{i<d} (X − X^{q^{i+1}}))⁻¹

and its valuation at infinity is `exp (−Σ_{i<d} q^{i+1}) < 1` for every `d ≥ 1`
(`q = |F| ≥ 2`).  This is the input for the non-vanishing `ζ_A(1) ≠ 0` in StepL196.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `natDegree (X − X^{q^e}) = q^e` for `e ≥ 1`. -/
lemma natDegree_Afac (e : ℕ) (he : 1 ≤ e) :
    (Polynomial.X - Polynomial.X ^ ((Nat.card F) ^ e) : F[X]).natDegree = (Nat.card F) ^ e := by
  have hq : 2 ≤ Nat.card F := card_ge_two F
  have hlt : (Polynomial.X : F[X]).natDegree
      < (Polynomial.X ^ ((Nat.card F) ^ e) : F[X]).natDegree := by
    rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]
    exact one_lt_pow₀ (by omega : 1 < Nat.card F) (by omega)
  rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]

/-- `intDegree (Afac e) = q^e` for `e ≥ 1`. -/
lemma intDegree_Afac (e : ℕ) (he : 1 ≤ e) :
    intDegree (Afac F e) = ((Nat.card F) ^ e : ℤ) := by
  rw [show Afac F e = algebraMap F[X] (RatFunc F)
      (Polynomial.X - Polynomial.X ^ ((Nat.card F) ^ e) : F[X]) from rfl,
    RatFunc.intDegree_polynomial]
  exact_mod_cast natDegree_Afac F e he

/-- `intDegree` is additive over finite products of nonzero factors. -/
lemma intDegree_prod {ι : Type*} (s : Finset ι) (f : ι → RatFunc F)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    intDegree (∏ i ∈ s, f i) = ∑ i ∈ s, intDegree (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t hat ih =>
      have hft : ∀ i ∈ t, f i ≠ 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert hat, RatFunc.intDegree_mul (hf a (Finset.mem_insert_self a t))
        (Finset.prod_ne_zero_iff.mpr hft), ih hft, Finset.sum_insert hat]

/-- ★ The depth-one power sum `P_d(1)` in closed form (inside the completion). -/
theorem P_oneExp_eq_prod (d : ℕ) :
    P F d oneExp =
      ((∏ i ∈ Finset.range d, (Afac F (i + 1))⁻¹ : RatFunc F) :
        RatFunc.CompletionAtInfty F) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  rw [P_eq_coe_Hsum F d oneExp]
  congr 1
  exact Hsum_closed F d

/-- The `intDegree` of the closed form of `P_d(1)`. -/
theorem intDegree_P_prod (d : ℕ) :
    intDegree (∏ i ∈ Finset.range d, (Afac F (i + 1))⁻¹)
      = -(∑ i ∈ Finset.range d, ((Nat.card F) ^ (i + 1) : ℤ)) := by
  classical
  have hAfac_ne : ∀ i ∈ Finset.range d, Afac F (i + 1) ≠ 0 := by
    intro i hi hzero
    have hd := intDegree_Afac F (i + 1) (by omega)
    rw [hzero, RatFunc.intDegree_zero] at hd
    have hpos : 0 < (Nat.card F) ^ (i + 1) :=
      pow_pos (by have h := card_ge_two F; omega) _
    have hne : ((Nat.card F) ^ (i + 1) : ℤ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hpos)
    exact hne hd.symm
  rw [Finset.prod_inv_distrib, RatFunc.intDegree_inv, intDegree_prod F _ _ hAfac_ne,
    Finset.sum_congr rfl (fun i hi => intDegree_Afac F (i + 1) (by omega))]

/-- ★★ The exact valuation of the depth-one power sums: `v (P_e(1)) = exp(−Σ_{i<e} q^{i+1})`. -/
theorem val_P_oneExp (e : ℕ) (he : 1 ≤ e) :
    Valued.v (P F e oneExp)
      = WithZero.exp (-(∑ i ∈ Finset.range e, ((Nat.card F) ^ (i + 1) : ℤ))) := by
  classical
  have hne : (∏ i ∈ Finset.range e, (Afac F (i + 1))⁻¹ : RatFunc F) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi hzero
    rw [inv_eq_zero] at hzero
    have hd' := intDegree_Afac F (i + 1) (by omega)
    rw [hzero, RatFunc.intDegree_zero] at hd'
    have hpos : 0 < (Nat.card F) ^ (i + 1) :=
      pow_pos (by have h := card_ge_two F; omega) _
    have hne' : ((Nat.card F) ^ (i + 1) : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos)
    exact hne' hd'.symm
  rw [P_oneExp_eq_prod F e, inftyValued_v_ratFunc F _ hne, intDegree_P_prod F e]

/-- ★★ The valuation of the depth-one power sums `P_d(1)` for `d ≥ 1` is `< 1`. -/
theorem val_P_oneExp_lt_one (d : ℕ) (hd : 1 ≤ d) :
    Valued.v (P F d oneExp) < (1 : ℤᵐ⁰) := by
  rw [val_P_oneExp F d hd]
  have hgoal : WithZero.exp (-(∑ i ∈ Finset.range d, ((Nat.card F) ^ (i + 1) : ℤ)))
      < WithZero.exp (0 : ℤ) := by
    rw [WithZero.exp_lt_exp]
    have hmem : 0 ∈ Finset.range d := Finset.mem_range.mpr (by omega)
    have hle : ((Nat.card F) ^ (0 + 1) : ℤ)
        ≤ ∑ i ∈ Finset.range d, ((Nat.card F) ^ (i + 1) : ℤ) :=
      Finset.single_le_sum (f := fun i => ((Nat.card F) ^ (i + 1) : ℤ))
        (fun i hi => by positivity) hmem
    have hq : (2 : ℤ) ≤ ((Nat.card F) ^ (0 + 1) : ℤ) := by
      have h := card_ge_two F
      simpa using (show (2 : ℤ) ≤ ((Nat.card F : ℕ) : ℤ) from by exact_mod_cast h)
    omega
  simpa using hgoal

/-- `P_0(1) = 1`. -/
theorem P_zero_oneExp : P F 0 oneExp = 1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  rw [P_oneExp_eq_prod F 0]
  simp [completion_coe_one]

end ZagierHoffmanPositiveChar
