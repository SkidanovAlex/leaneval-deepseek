import Submission.ZagierHoffmanProof.StepK28

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K29: the stage-1 inner-collapse gate and the collapse

  ★ D1_zero_nonconst (m) (u) : (D1 F (m+1)(Fin.cons 0 u)).natDegree ≠ 0
      [rw [D1_def']; the coefficient of `X^{q(m+1)}` in the range-(m+2) sum is 1:
      Finset.sum_eq_single (m+1) — the top term has coeffSeq(m+2)(·)(m+2) = 1
      (coeffSeq_d; the (m+1)+1 index is defeq m+2 — rw [hd] fires directly) times
      hh_two_topcoeff = 1; every b ≤ m term vanishes: b = 0 → hh 0 2 0 = 1 with coeff_C
      at degree q(m+1) ≠ 0; b ≥ 1 → natDegree(hh 0 2 b) = q·b < q(m+1) (hh_two_deg) so
      coeff_eq_zero_of_natDegree_lt (after coeff_C_mul); then natDegree ≠ 0 by
      by_contra (coeff_eq_zero_of_natDegree_lt with `exact he_pos` after rw [hz0])]
  ★ collapse1_inner (m) (u) : Σ_c inv(C c + D1 (m+1)(cons 0 u))
      = inv(D1 (m+1)(cons 0 u) − (…)^q)
      [Hsum_one_subst at Z := D1 (m+1)(cons 0 u) via D1_zero_nonconst; simpa [add_comm]]

This opens the stage-1 inner collapse; the remaining s=1 steps are the `D1 ↔ D2` glue
(`Z − Z^q = (X−X^{q²})·D2 m u` via St_step at stage-1 data, mirroring stage0_factor)
and the factor-extraction assembly (Hsum_collapse0 + collapse1_split + collapse1_csum +
collapse1_inner + glue).  All lemmas here are sorry-free.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]




/-- the c-independent part `Z(u) := D1 (m+1)(cons 0 u)` is nonconstant (its top term
`hh 0 2 (m+1)`, coefficient `1`, has degree `q·(m+1)` and dominates the `m' ≤ m` terms). -/
lemma D1_zero_nonconst (m : ℕ) (u : Fin m → F) :
    (D1 F (m + 1) (Fin.cons 0 u)).natDegree ≠ 0 := by
  classical
  have hq : 2 ≤ Nat.card F := card_ge_two F
  let e : ℕ := Nat.card F * (m + 1)
  have he_pos : 0 < e := by
    dsimp [e]
    have hq' : 0 < Nat.card F := by omega
    exact mul_pos hq' (by omega)
  have hc : (D1 F (m + 1) (Fin.cons 0 u)).coeff e = 1 := by
    rw [D1_def' F m (Fin.cons 0 u)]
    have hcoeff : (∑ m' ∈ Finset.range (m + 2),
        C (coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons 0 u)) (m' + 1)) * hh F 0 2 m' : F[X]).coeff e =
        ∑ m' ∈ Finset.range (m + 2),
          (C (coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons 0 u)) (m' + 1)) * hh F 0 2 m' : F[X]).coeff e := by simp
    rw [hcoeff]
    rw [Finset.sum_eq_single (m + 1)]
    · -- the m' = m+1 term: coeffSeq(m+2)(·)((m+1)+1) = 1, hh-topcoeff = 1
      have hmm : (m + 1) + 1 = m + 2 := by omega
      have hd : coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons 0 u)) (m + 2) = 1 :=
        coeffSeq_d F (m + 2) (Fin.cons 0 (Fin.cons 0 u))
      have hm' : 1 ≤ m + 1 := by omega
      have ht := hh_two_topcoeff F (m + 1) hm'
      rw [hd]
      have hC1 : C (1 : F) = 1 := by simp
      rw [hC1]
      simp
      dsimp [e]
      exact ht
    · intro b hb hbk
      -- b ≠ m+1, b ∈ range(m+2) → b ≤ m: term vanishes (hh-degree too small)
      have hb' : b < m + 2 := Finset.mem_range.mp hb
      have hb_le : b ≤ m := by omega
      by_cases hb0 : b = 0
      · subst b
        have h1 : hh F 0 2 0 = 1 := hh_zero F 0 2
        have hne : e ≠ 0 := by omega
        calc
          (C (coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons 0 u)) (0 + 1)) * hh F 0 2 0 : F[X]).coeff e
              = (C (coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons 0 u)) 1) * 1 : F[X]).coeff e := by
                congr 1
                rw [h1]
          _ = 0 := by
                rw [show (C (coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons 0 u)) 1) * 1 : F[X]) =
                    C (coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons 0 u)) 1) by simp]
                rw [Polynomial.coeff_C]
                rw [if_neg hne]
      · have hb1 : 1 ≤ b := by omega
        have hdeg := hh_two_deg F b hb1
        have hlt0 : (Nat.card F) * b < e := by
          dsimp [e]
          have hq' : 0 < Nat.card F := by omega
          exact Nat.mul_lt_mul_of_pos_left (by omega) hq'
        have hz : (hh F 0 2 b).coeff e = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)
        calc
          (C (coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons 0 u)) (b + 1)) * hh F 0 2 b : F[X]).coeff e
              = (coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons 0 u)) (b + 1)) * (hh F 0 2 b).coeff e := by
                rw [Polynomial.coeff_C_mul]
          _ = 0 := by rw [hz]; simp
    · intro hm2
      exact False.elim (hm2 (by simp))
  intro hz0
  have hz : (D1 F (m + 1) (Fin.cons 0 u)).coeff e = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hz0]; exact he_pos)
  rw [hc] at hz
  exact one_ne_zero hz


/-- ★ the stage-1 inner collapse (analogue of `Hsum_collapse0_inner`):
`Σ_c inv(C c + Z(u)) = inv(Z(u) − Z(u)^q)` with `Z(u) := D1 (m+1)(cons 0 u)`. -/
lemma collapse1_inner (m : ℕ) (u : Fin m → F) :
    letI : Fintype F := Fintype.ofFinite F
    (∑ c : F, ((((C c + D1 F (m + 1) (Fin.cons 0 u) : F[X]) : F[X]) : RatFunc F)⁻¹)) =
      ((((D1 F (m + 1) (Fin.cons 0 u) - (D1 F (m + 1) (Fin.cons 0 u)) ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)⁻¹) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have h := Hsum_one_subst F (D1 F (m + 1) (Fin.cons 0 u)) (D1_zero_nonconst F m u)
  simpa [add_comm] using h



end ZagierHoffmanPositiveChar
