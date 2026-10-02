import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.dd_criticalSumBound
import Submission.Work.LinnikBurgess.castHom_ddDefectK_three
import Submission.Work.LinnikBurgess.dvd_contAB_of_IsDD_three
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation6_primePow_local

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.LinnikBurgess

open Commons.NumberTheory.DirichletCharacter

/-- The monic cubic `∏_l (X + a_l)` over `ZMod p`, expanded in the elementary symmetric
functions of the triple `a`. -/
lemma l6_cA_eq_form {p : ℕ} [Fact p.Prime] (a : Fin 3 → ℕ) :
    cA p a = Polynomial.X ^ 3 + Polynomial.C (((esymm3 a 0 : ℤ) : ZMod p)) * Polynomial.X ^ 2
        + Polynomial.C (((esymm3 a 1 : ℤ) : ZMod p)) * Polynomial.X
        + Polynomial.C (((esymm3 a 2 : ℤ) : ZMod p)) := by
  rw [cA, Fin.prod_univ_three]
  simp only [esymm3]
  push_cast
  simp only [Polynomial.C_add, Polynomial.C_mul]
  ring

/-- **Wronskian of two monic cubics.**  For `A = X^3 + A₁X² + A₂X + A₃`,
`B = X^3 + B₁X² + B₂X + B₃` over a commutative ring, the Wronskian `A'B - B'A` has expansion
`C(-c₂)X^4 + C(-2c₁)X^3 + C(c₂B₂ - c₁B₁ - 3c₀)X² + …` with `c_j` the differences of the
corresponding coefficients.  Only the coefficients of `X^4`, `X^3`, `X^2` are needed. -/
lemma l6_cubic_wronskian_expand {R : Type*} [CommRing R] (A1 A2 A3 B1 B2 B3 : R) :
    Polynomial.derivative
        (Polynomial.X ^ 3 + Polynomial.C A1 * Polynomial.X ^ 2 + Polynomial.C A2 * Polynomial.X
          + Polynomial.C A3)
        * (Polynomial.X ^ 3 + Polynomial.C B1 * Polynomial.X ^ 2 + Polynomial.C B2 * Polynomial.X
          + Polynomial.C B3)
      - Polynomial.derivative
          (Polynomial.X ^ 3 + Polynomial.C B1 * Polynomial.X ^ 2 + Polynomial.C B2 * Polynomial.X
            + Polynomial.C B3)
        * (Polynomial.X ^ 3 + Polynomial.C A1 * Polynomial.X ^ 2 + Polynomial.C A2 * Polynomial.X
          + Polynomial.C A3)
    = Polynomial.C (-(A1 - B1)) * Polynomial.X ^ 4
      + Polynomial.C (-(2 * (A2 - B2))) * Polynomial.X ^ 3
      + Polynomial.C ((A1 - B1) * B2 - (A2 - B2) * B1 - 3 * (A3 - B3)) * Polynomial.X ^ 2
      + Polynomial.C (2 * (A1 - B1) * B3 - 2 * (A3 - B3) * B1) * Polynomial.X
      + Polynomial.C ((A2 - B2) * B3 - (A3 - B3) * B2) := by
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, Polynomial.derivative_pow,
    Polynomial.C_mul, Polynomial.C_neg, Polynomial.C_sub, Polynomial.C_ofNat,
    Polynomial.C_eq_natCast]
  ring

/-- **The content criterion for the critical polynomial.**  For `p ≥ 5`, if `p` does not divide the
content `contAB a b = gcd_k |e_k(a) - e_k(b)|` of the pair, then the critical polynomial
`cH p a b = A'B - B'A` (with `A = ∏_l (X + a_l)`, `B = ∏_l (X + b_l)` over `ZMod p`) is nonzero.

Indeed `cH = 0` forces the coefficients `−(A₁−B₁)`, `−2(A₂−B₂)` and `−3(A₃−B₃) + …` of `X^4`, `X^3`,
`X^2` to vanish; as `2` and `3` are units in `ZMod p`, this means `p` divides all three
`e_k(a) - e_k(b)`, i.e. `p ∣ contAB a b`. -/
theorem cH_ne_zero_of_not_dvd_contAB_local {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (a b : Fin 3 → ℕ)
    (hc : ¬ p ∣ contAB a b) : cH p a b ≠ 0 := by
  intro hch
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hc2
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hc2
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro hc3
    have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hc3
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  set A1 : ZMod p := ((esymm3 a 0 : ℤ) : ZMod p) with hA1
  set A2 : ZMod p := ((esymm3 a 1 : ℤ) : ZMod p) with hA2
  set A3 : ZMod p := ((esymm3 a 2 : ℤ) : ZMod p) with hA3
  set B1 : ZMod p := ((esymm3 b 0 : ℤ) : ZMod p) with hB1
  set B2 : ZMod p := ((esymm3 b 1 : ℤ) : ZMod p) with hB2
  set B3 : ZMod p := ((esymm3 b 2 : ℤ) : ZMod p) with hB3
  have hch' : Polynomial.derivative
          (Polynomial.X ^ 3 + Polynomial.C A1 * Polynomial.X ^ 2 + Polynomial.C A2 * Polynomial.X
            + Polynomial.C A3)
        * (Polynomial.X ^ 3 + Polynomial.C B1 * Polynomial.X ^ 2 + Polynomial.C B2 * Polynomial.X
          + Polynomial.C B3)
      - Polynomial.derivative
          (Polynomial.X ^ 3 + Polynomial.C B1 * Polynomial.X ^ 2 + Polynomial.C B2 * Polynomial.X
            + Polynomial.C B3)
        * (Polynomial.X ^ 3 + Polynomial.C A1 * Polynomial.X ^ 2 + Polynomial.C A2 * Polynomial.X
          + Polynomial.C A3) = 0 := by
    have h := hch
    rw [cH, l6_cA_eq_form (p := p) a, l6_cA_eq_form (p := p) b,
      ← hA1, ← hA2, ← hA3, ← hB1, ← hB2, ← hB3] at h
    exact h
  have hexp := l6_cubic_wronskian_expand A1 A2 A3 B1 B2 B3
  rw [hch'] at hexp
  have h4 := congrArg (fun q : Polynomial (ZMod p) => q.coeff 4) hexp
  have h3c := congrArg (fun q : Polynomial (ZMod p) => q.coeff 3) hexp
  have h2c := congrArg (fun q : Polynomial (ZMod p) => q.coeff 2) hexp
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C] at h4 h3c h2c
  simp at h4 h3c h2c
  have e1 : A1 = B1 := (sub_eq_zero.mp h4.symm).symm
  have e2 : A2 = B2 := by
    rcases h3c with h | h
    · exact absurd h h2
    · exact sub_eq_zero.mp h
  have e3 : A3 = B3 := by
    have h2c' : (A1 - B1) * B2 - (A2 - B2) * B1 - 3 * (A3 - B3) = 0 := h2c.symm
    rw [e1, e2] at h2c'
    have hz : 3 * (A3 - B3) = 0 := by linear_combination -h2c'
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h h3
    · exact sub_eq_zero.mp h
  have key : ∀ (x y : ℤ), ((x : ZMod p) = (y : ZMod p)) → p ∣ (x - y).natAbs := by
    intro x y hxy
    have h00 : ((x - y : ℤ) : ZMod p) = 0 := by push_cast [hxy]; ring
    have h11 : (p : ℤ) ∣ (x - y) := (ZMod.intCast_zmod_eq_zero_iff_dvd (x - y) p).mp h00
    rwa [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast] at h11
  refine hc ?_
  rw [contAB]
  refine Nat.dvd_gcd ?_ (Nat.dvd_gcd ?_ ?_)
  · apply key; rw [← hA1, ← hB1]; exact e1
  · apply key; rw [← hA2, ← hB2]; exact e2
  · apply key; rw [← hA3, ← hB3]; exact e3

/-- **U6 — the sharp local bound away from the content locus** (`BURGESS_ROUTE_LEAD.md` §2.4).  For
`p ≥ 5`, `e ≥ 4`, `χ` primitive mod `p^e` and a pair `(a,b)` with
`¬ p ∣ Work.LinnikBurgess.contAB a b` (the pencil `⟨f_a, f_b⟩` has no cube factor modulo `p`, so the
Wronskian `critN` is not divisible by `p` coefficientwise),
`‖∑_{x mod p^e} χ(∏_l (x + a_l))·conj χ(∏_l (x + b_l))‖ ≤ 12 p^(e/2) + 48 p^(2e/3)`.

A reviewer confirmed the claim and checked that the hypotheses suffice: `crit_nonbad_card_le` needs
only `cH ≠ 0` (not the uniqueness `hi`), `¬ p ∣ contAB ⟹ cH ≠ 0` (U4's content fact), and
`IsDD ⟹ IsDDCubic` (Newton + U4's triple-vanishing fact).  This follows `local_corr6_cubic`'s proof
(proved, sorry-free) verbatim apart from those two replacements; `local_corr6_cubic`'s internal sum
bound `hsumB ≤ 6A+6C` is exactly this right-hand side.  You will need to add imports for
`charCorrelation6_criticalClasses`, `charCorrelation6_levelSum_nondegenerate`,
`dd_criticalSumBound`, `cH_eq_zero_dvd_ddDefectK` and the U4 file, and you may prove the U4 facts
yourself if that file is still in flight.  Needed for the saturated menu term of U7. -/
theorem local_corr6_nonContent_sharp {p e : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (he : 4 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive) (a b : Fin 3 → ℕ)
    (hc : ¬ p ∣ Work.LinnikBurgess.contAB a b) :
    ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖
      ≤ 12 * (p : ℝ) ^ ((e : ℝ) / 2) + 48 * (p : ℝ) ^ (2 * (e : ℝ) / 3) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have he2 : 2 ≤ e := by omega
  have hHne : cH p a b ≠ 0 := cH_ne_zero_of_not_dvd_contAB_local hp5 a b hc
  have hcc := Commons.NumberTheory.DirichletCharacter.charCorrelation6_criticalClasses
      (p := p) hp2 e he2 χ hχ a b
  rw [hcc, norm_mul, Complex.norm_natCast]
  have hpp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  set A : ℝ := 2 * (p : ℝ) ^ (((e : ℝ) - 2) / 2) with hA
  set C : ℝ := 8 * (p : ℝ) ^ (2 * (e : ℝ) / 3 - 1) with hC
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hcard1 : (((cF1 p a b).card : ℕ) : ℝ) ≤ 6 := by
    have h1 : (cF1 p a b).card ≤ (cCcrit p a b).card := cF1_card_le_crit a b
    have h2 : (cCcrit p a b).card ≤ 6 := crit_nonbad_card_le a b hHne
    exact_mod_cast le_trans h1 h2
  have hcard2 : (cF2 p a b).card ≤ 6 := by
    have h1 : (cF2 p a b).card ≤ (cCcrit p a b).card := by
      refine Finset.card_le_card ?_
      intro r hr
      rw [cF2, Finset.mem_filter] at hr
      rw [cCcrit, Finset.mem_filter]
      exact ⟨Finset.mem_univ r, hr.2.1, hr.2.2.1, sub_eq_zero.mp hr.2.2.2.1⟩
    exact le_trans h1 (crit_nonbad_card_le a b hHne)
  have hpoint : ∀ r : ZMod p,
      ‖(if (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹) - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) = 0
        then (∑ z : ZMod (p ^ (e - 2)),
            χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ)))
            * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ)))))
        else 0)‖
      ≤ (if r ∈ cF1 p a b then A else 0)
        + (if r ∈ cF2 p a b ∧ (p : ℕ) ^ 2 ∣ (ddDefect p e a b r).val then C else 0) := by
    intro r
    by_cases hcrit : (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹)
        - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) = 0
    · rw [if_pos hcrit]
      by_cases hmem1 : r ∈ cF1 p a b
      · rw [if_pos hmem1]
        have hm1 := Finset.mem_filter.mp hmem1
        have hunit : ∀ l : Fin 3, (r + (a l : ZMod p)) ≠ 0 ∧ (r + (b l : ZMod p)) ≠ 0 :=
          fun l => ⟨hm1.2.1 l, hm1.2.2.1 l⟩
        have hcr : (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹)
            = (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) := sub_eq_zero.mp hm1.2.2.2.1
        have hnd : (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹ ^ 2)
            ≠ (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹ ^ 2) := fun h => hm1.2.2.2.2 h.symm
        refine le_trans (charCorrelation6_levelSum_nondegenerate (p := p) (e := e) hp2 (by omega)
          χ hχ a b r hunit hcr hnd) ?_
        rw [← hA]
        by_cases hq : r ∈ cF2 p a b ∧ (p : ℕ) ^ 2 ∣ (ddDefect p e a b r).val
        · rw [if_pos hq]; linarith [hC0]
        · rw [if_neg hq, add_zero]
      · rw [if_neg hmem1]
        by_cases hunit : (∀ l : Fin 3, (r + (a l : ZMod p)) ≠ 0)
            ∧ (∀ l : Fin 3, (r + (b l : ZMod p)) ≠ 0)
        · by_cases hdeg : (∑ l : Fin 3, ((r + (a l : ZMod p))⁻¹) ^ 2)
              = (∑ l : Fin 3, ((r + (b l : ZMod p))⁻¹) ^ 2)
          · have hmem2 : r ∈ cF2 p a b := by
              rw [cF2, Finset.mem_filter]
              exact ⟨Finset.mem_univ r, hunit.1, hunit.2, hcrit, hdeg⟩
            by_cases hdd : (p : ℕ) ^ 2 ∣ (ddDefect p e a b r).val
            · rw [if_pos ⟨hmem2, hdd⟩]
              have hIsDD : IsDD p e a b r :=
                ⟨fun l => ⟨hunit.1 l, hunit.2 l⟩, sub_eq_zero.mp hcrit, hdeg, hdd⟩
              have hcubr : ∃ r' : ZMod p, IsDDCubic p e a b r' :=
                ⟨r, hIsDD, fun h3 => hc (dvd_contAB_of_IsDD_three hp5 (by omega) a b r hIsDD h3)⟩
              refine le_trans (dd_criticalSumBound (p := p) (e := e) hp2 he χ hχ a b r hcubr hIsDD) ?_
              rw [← hC]; linarith
            · rw [if_neg (fun h => hdd h.2)]
              have hzero := charCorrelation6_levelSum_vanishing (p := p) (e := e) hp2 (by omega)
                χ hχ a b r (fun l => ⟨hunit.1 l, hunit.2 l⟩) (sub_eq_zero.mp hcrit)
                (by simpa only [ddDefect] using hdd) hdeg.symm
              rw [hzero, norm_zero]
              norm_num
          · exfalso
            apply hmem1
            rw [cF1, Finset.mem_filter]
            exact ⟨Finset.mem_univ r, hunit.1, hunit.2, hcrit, hdeg⟩
        · have hbad : (∃ l : Fin 3, (r + (a l : ZMod p)) = 0)
              ∨ (∃ l : Fin 3, (r + (b l : ZMod p)) = 0) := by
            rcases not_and_or.mp hunit with h | h
            · obtain ⟨l, hl⟩ := not_forall.mp h
              exact Or.inl ⟨l, not_not.mp hl⟩
            · obtain ⟨l, hl⟩ := not_forall.mp h
              exact Or.inr ⟨l, not_not.mp hl⟩
          rcases hbad with ⟨l, hl⟩ | ⟨l, hl⟩
          · rw [innerSum_bad_eq_zero e (by omega) χ a b r (Or.inl ⟨l, hl⟩), norm_zero]
            by_cases hq : r ∈ cF2 p a b ∧ (p : ℕ) ^ 2 ∣ (ddDefect p e a b r).val
            · rw [if_pos hq]; linarith [hC0]
            · rw [if_neg hq]; norm_num
          · rw [innerSum_bad_eq_zero e (by omega) χ a b r (Or.inr ⟨l, hl⟩), norm_zero]
            by_cases hq : r ∈ cF2 p a b ∧ (p : ℕ) ^ 2 ∣ (ddDefect p e a b r).val
            · rw [if_pos hq]; linarith [hC0]
            · rw [if_neg hq]; norm_num
    · rw [if_neg hcrit, norm_zero]
      by_cases hq : r ∈ cF2 p a b ∧ (p : ℕ) ^ 2 ∣ (ddDefect p e a b r).val
      · rw [if_pos hq]
        by_cases hq1 : r ∈ cF1 p a b
        · rw [if_pos hq1]; linarith [hA0, hC0]
        · rw [if_neg hq1]; linarith [hC0]
      · rw [if_neg hq]
        by_cases hq1 : r ∈ cF1 p a b
        · rw [if_pos hq1]; linarith [hA0]
        · rw [if_neg hq1]; norm_num
  have hsumB : ‖∑ r : ZMod p, (if (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹)
        - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) = 0
        then (∑ z : ZMod (p ^ (e - 2)),
            χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ)))
            * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ)))))
        else 0)‖ ≤ A * 6 + C * 6 := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun r _ => hpoint r)) ?_
    rw [Finset.sum_add_distrib]
    have h1 : (∑ r : ZMod p, (if r ∈ cF1 p a b then A else 0)) = A * ((cF1 p a b).card : ℝ) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have h2 : (∑ r : ZMod p, (if r ∈ cF2 p a b ∧ (p : ℕ) ^ 2 ∣ (ddDefect p e a b r).val then C else 0))
        = C * (((cF2 p a b).filter (fun r => (p : ℕ) ^ 2 ∣ (ddDefect p e a b r).val)).card : ℝ) := by
      rw [show (∑ r : ZMod p, (if r ∈ cF2 p a b ∧ (p : ℕ) ^ 2 ∣ (ddDefect p e a b r).val then C else 0))
          = ∑ r : ZMod p, (if r ∈ (cF2 p a b).filter (fun r => (p : ℕ) ^ 2 ∣ (ddDefect p e a b r).val) then C else 0) from by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        simp only [Finset.mem_filter]]
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [h1, h2]
    have h3 : (((cF2 p a b).filter (fun r => (p : ℕ) ^ 2 ∣ (ddDefect p e a b r).val)).card : ℝ) ≤ 6 := by
      have hle : ((cF2 p a b).filter (fun r => (p : ℕ) ^ 2 ∣ (ddDefect p e a b r).val)).card
          ≤ (cF2 p a b).card := Finset.card_filter_le _ _
      exact_mod_cast le_trans hle hcard2
    nlinarith [hcard1, h3, hA0, hC0]
  have hrp1 : (p : ℝ) * (p : ℝ) ^ (((e : ℝ) - 2) / 2) = (p : ℝ) ^ ((e : ℝ) / 2) := by
    have h := Real.rpow_add hpp (1 : ℝ) (((e : ℝ) - 2) / 2)
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  have hrp2 : (p : ℝ) * (p : ℝ) ^ (2 * (e : ℝ) / 3 - 1) = (p : ℝ) ^ (2 * (e : ℝ) / 3) := by
    have h := Real.rpow_add hpp (1 : ℝ) (2 * (e : ℝ) / 3 - 1)
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  have hmain : (p : ℝ) * (A * 6 + C * 6)
      = 12 * (p : ℝ) ^ ((e : ℝ) / 2) + 48 * (p : ℝ) ^ (2 * (e : ℝ) / 3) := by
    rw [hA, hC]
    rw [show (p : ℝ) * ((2 * (p : ℝ) ^ (((e : ℝ) - 2) / 2)) * 6 + (8 * (p : ℝ) ^ (2 * (e : ℝ) / 3 - 1)) * 6)
        = 12 * ((p : ℝ) * (p : ℝ) ^ (((e : ℝ) - 2) / 2)) + 48 * ((p : ℝ) * (p : ℝ) ^ (2 * (e : ℝ) / 3 - 1)) by ring]
    rw [hrp1, hrp2]
  exact le_trans (mul_le_mul_of_nonneg_left hsumB hpp.le) (le_of_eq hmain)

end Work.LinnikBurgess
