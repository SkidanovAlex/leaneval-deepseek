import Submission.ZagierHoffmanProof.StepK31

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K32: the UNIFORM stage collapse (general `s`) — part 1: `hh` top-monomial claims

The s=0,1 collapses (Hsum_collapse0/collapse1) are instances of ONE general statement
over `StatePoly s m u := Σ_{m'<m+1} C(if m'<m then u m' else 1)·hh 0 (s+1) m'`
(`u : Fin m`):  G(s,m) := Σ_{u:Fin m} inv(StatePoly s m u) satisfies
  ★ G(s, m+1) = A_{s+1}⁻¹·G(s+1,m),  A_{s+1} := X − X^{q^{s+1}}   (stage_collapse)
(affine head dependence with slope 1; inner level-1 power sum via Hsum_one_subst at the
head-zeroed state Z(v); glue Z−Z^q = A_{s+1}·StatePoly (s+1) m v from the general
hh-factorization; nonconstancy of Z(v) from the top-monomial coefficient 1).
This file proves the hh degree-top claims needed for that nonconstancy (and dominance):
  hh_above0 (rv0 m j) : q^{rv0}·m < j → (hh 0 (rv0+1) m).coeff j = 0   [no monomial
      above X^{q^{rv0}·m}; nested induction on rv0 and m via hh_rec]
  hh_topcoeff0 (rv0 m) (hm : 1 ≤ m) : (hh 0 (rv0+1) m).coeff (q^{rv0}·m) = 1
Both sorry-free.  (Part 2 of StepK32 — StatePoly + affine + glue + nonconst +
stage_collapse + tower + Hsum_closed ⇒ EvalU ∀d — follows in the next step.)
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- every monomial of `hh 0 (rv0+1) m` has X-degree at most `q^{rv0}·m`:
coefficients above that degree vanish. -/
lemma hh_above0 (rv0 : ℕ) : ∀ (m : ℕ), ∀ (j : ℕ),
    (Nat.card F) ^ rv0 * m < j → (hh F 0 (rv0 + 1) m).coeff j = 0 := by
  classical
  induction rv0 with
  | zero =>
      intro m j hj
      have hh1 := hh_one F 0 m
      have h1 : (Nat.card F) ^ 0 * m = m := by simp
      have hpow : ((X ^ ((Nat.card F) ^ 0) : F[X]) ^ m) = X ^ (m) := by
        rw [← pow_mul]
        rw [h1]
      rw [hh1, hpow]
      rw [Polynomial.coeff_X_pow m j]
      rw [h1] at hj
      have hnm : j ≠ m := by omega
      simp [hnm]
  | succ rv0 ihr =>
      intro m
      induction m with
      | zero =>
          intro j hj
          have hz : hh F 0 (rv0 + 2) 0 = 1 := hh_zero F 0 (rv0 + 2)
          rw [hz]
          simp at hj
          change (Polynomial.C (1 : F) : F[X]).coeff j = 0
          rw [Polynomial.coeff_C]
          simp
          omega
      | succ m' ih' =>
          intro j hj
          have hrec := hh_rec F 0 (rv0 + 1) m'
          rw [hrec]
          rw [Polynomial.coeff_add]
          have hj' : (Nat.card F) ^ (rv0 + 1) * (m' + 1) < j := hj
          -- part 1: hh 0 (rv0+1)(m'+1), vanishes above q^{rv0}(m'+1) < q^{rv0+1}(m'+1)
          have hp1 : (hh F 0 (rv0 + 1) (m' + 1)).coeff j = 0 := by
            exact ihr (m' + 1) j (by
              have hq : 2 ≤ Nat.card F := card_ge_two F
              have hlt0 : (Nat.card F) ^ rv0 < (Nat.card F) ^ (rv0 + 1) :=
                Nat.pow_lt_pow_right hq (by omega)
              have hmono : (Nat.card F) ^ rv0 * (m' + 1) < (Nat.card F) ^ (rv0 + 1) * (m' + 1) := by
                nlinarith
              exact lt_trans hmono hj')
          -- part 2: X^E·hh 0 (rv0+2) m' vanishes at j
          have hE : (Nat.card F) ^ (0 + (rv0 + 1)) = (Nat.card F) ^ (rv0 + 1) := by simp
          have hge : (Nat.card F) ^ (rv0 + 1) ≤ j := by
            have hpos : 0 < m' + 1 := by omega
            have hle : (Nat.card F) ^ (rv0 + 1) ≤ (Nat.card F) ^ (rv0 + 1) * (m' + 1) :=
              Nat.le_mul_of_pos_right ((Nat.card F) ^ (rv0 + 1)) hpos
            exact le_trans hle (le_of_lt hj')
          have hp2 : ((X ^ (Nat.card F) ^ (0 + (rv0 + 1)) : F[X]) * hh F 0 (rv0 + 2) m').coeff j = 0 := by
            let d := j - (Nat.card F) ^ (0 + (rv0 + 1))
            have hjd : j = d + (Nat.card F) ^ (0 + (rv0 + 1)) := by
              dsimp [d]
              omega
            rw [hjd]
            rw [Polynomial.coeff_X_pow_mul]
            have hjm : (Nat.card F) ^ (rv0 + 1) * (m' + 1) =
                (Nat.card F) ^ (rv0 + 1) * m' + (Nat.card F) ^ (rv0 + 1) := by ring
            have hlt : (Nat.card F) ^ (rv0 + 1) * m' + (Nat.card F) ^ (rv0 + 1) < j := by
              nlinarith [hj', hjm]
            have hlt2 : (Nat.card F) ^ (rv0 + 1) * m' < d := by
              dsimp [d]
              rw [hE]
              omega
            exact ih' d hlt2
          rw [hp1, hp2]
          simp

/-- the coefficient of the top monomial `X^{q^{rv0}·m}` of `hh 0 (rv0+1) m` (m ≥ 1)
is `1`. -/
lemma hh_topcoeff0 (rv0 : ℕ) : ∀ (m : ℕ), 1 ≤ m →
    (hh F 0 (rv0 + 1) m).coeff ((Nat.card F) ^ rv0 * m) = 1 := by
  classical
  induction rv0 with
  | zero =>
      intro m hm
      have hh1 := hh_one F 0 m
      have h1 : (Nat.card F) ^ 0 * m = m := by simp
      have hpow : ((X ^ ((Nat.card F) ^ 0) : F[X]) ^ m) = X ^ (m) := by
        rw [← pow_mul]
        rw [h1]
      rw [hh1, hpow]
      rw [h1]
      rw [Polynomial.coeff_X_pow m m]
      simp
  | succ rv0 ihr =>
      intro m hm
      induction m with
      | zero => omega
      | succ m' ih' =>
          have hrec := hh_rec F 0 (rv0 + 1) m'
          have hE : (Nat.card F) ^ (0 + (rv0 + 1)) = (Nat.card F) ^ (rv0 + 1) := by simp
          rw [hrec]
          rw [Polynomial.coeff_add]
          -- part 1: hh 0 (rv0+1)(m'+1) has nothing at E·(m'+1) (its top is q^{rv0}(m'+1))
          have hp1 : (hh F 0 (rv0 + 1) (m' + 1)).coeff
              ((Nat.card F) ^ (rv0 + 1) * (m' + 1)) = 0 := by
            have hq : 2 ≤ Nat.card F := card_ge_two F
            have hlt0 : (Nat.card F) ^ rv0 < (Nat.card F) ^ (rv0 + 1) :=
              Nat.pow_lt_pow_right hq (by omega)
            have hlt : (Nat.card F) ^ rv0 * (m' + 1) < (Nat.card F) ^ (rv0 + 1) * (m' + 1) := by
              nlinarith
            exact hh_above0 F rv0 (m' + 1) ((Nat.card F) ^ (rv0 + 1) * (m' + 1)) hlt
          -- part 2: coeff (X^E·hh 0 (rv0+2) m') at E·(m'+1) = coeff (hh 0 (rv0+2) m') at E·m' = 1
          have hp2 : ((X ^ (Nat.card F) ^ (0 + (rv0 + 1)) : F[X]) * hh F 0 (rv0 + 2) m').coeff
              ((Nat.card F) ^ (rv0 + 1) * (m' + 1)) = 1 := by
            have hjm : (Nat.card F) ^ (rv0 + 1) * (m' + 1) =
                (Nat.card F) ^ (rv0 + 1) * m' + (Nat.card F) ^ (0 + (rv0 + 1)) := by
              rw [hE]
              ring
            rw [hjm]
            rw [Polynomial.coeff_X_pow_mul]
            by_cases hm'0 : m' = 0
            · subst m'
              have hz : hh F 0 (rv0 + 2) 0 = 1 := hh_zero F 0 (rv0 + 2)
              rw [hz]
              simp
            · have hm'1 : 1 ≤ m' := by omega
              exact ih' hm'1
          rw [hp1, hp2]
          simp

end ZagierHoffmanPositiveChar
