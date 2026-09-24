import Mathlib
import Submission.Commons.NumberTheory.BombieriVinogradov.sum_charSup_le_log_mul_primitive
import Submission.Commons.NumberTheory.DirichletCharacter.sum_characters_eq_sum_primitive_lifts
import Submission.Commons.NumberTheory.Totient.totient_mul_gcd
import Submission.Commons.NumberTheory.Totient.sum_inv_totient_Icc_le_powLog

set_option maxHeartbeats 1600000

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators
open Classical
open Finset

noncomputable section

/-- `‖chiSum q χ x‖` with the principal character replaced by `0`. -/
private noncomputable def charAbs (q x : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  if χ = 1 then 0 else ‖chiSum q χ x‖

private noncomputable def primAbs (c x : ℕ) : ℝ :=
  ∑ ψ ∈ (Finset.univ.filter (fun ψ : DirichletCharacter ℂ c => ψ.IsPrimitive)), ‖chiSum c ψ x‖

private lemma primAbs_nonneg (c x : ℕ) : 0 ≤ primAbs c x :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

private theorem sum_eq_sum_primitive_lifts_real (q : ℕ) [NeZero q]
    (g : DirichletCharacter ℂ q → ℝ) :
    (∑ χ : DirichletCharacter ℂ q, g χ)
      = ∑ c ∈ q.divisors.attach,
          ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
            g (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1) := by
  have h := Commons.NumberTheory.DirichletCharacter.sum_characters_eq_sum_primitive_lifts q
    (fun χ : DirichletCharacter ℂ q => ((g χ : ℝ) : ℂ))
  refine Complex.ofReal_injective ?_
  push_cast
  exact h

private lemma card_prim (q : ℕ) [NeZero q] :
    (∑ c ∈ q.divisors,
        ((Finset.univ.filter (fun ψ : DirichletCharacter ℂ c => ψ.IsPrimitive)).card : ℝ))
      = (q.totient : ℝ) := by
  have h := sum_eq_sum_primitive_lifts_real q (fun (_ : DirichletCharacter ℂ q) => (1 : ℝ))
  have hL : (∑ χ : DirichletCharacter ℂ q, (1 : ℝ)) = (q.totient : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [← Nat.card_eq_fintype_card]
    exact_mod_cast DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hR : (∑ c ∈ q.divisors.attach,
        ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive}, (1 : ℝ))
      = ∑ c ∈ q.divisors,
          ((Finset.univ.filter (fun ψ : DirichletCharacter ℂ c => ψ.IsPrimitive)).card : ℝ) := by
    rw [← Finset.sum_attach q.divisors
        (fun c => ((Finset.univ.filter (fun ψ : DirichletCharacter ℂ c => ψ.IsPrimitive)).card : ℝ))]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    congr 1
    exact Fintype.card_subtype (fun ψ : DirichletCharacter ℂ c.1 => ψ.IsPrimitive)
  rw [← hR, ← hL]
  exact h.symm

private lemma term_le (q c x : ℕ) [NeZero q] (hc : c ∣ q) (ψ : DirichletCharacter ℂ c) :
    charAbs q x (DirichletCharacter.changeLevel hc ψ)
      ≤ ‖chiSum c ψ x‖ + 2 * chiBad q x := by
  by_cases h : DirichletCharacter.changeLevel hc ψ = 1
  · simp only [charAbs, if_pos h]
    have h1 : (0 : ℝ) ≤ ‖chiSum c ψ x‖ := norm_nonneg _
    have h2 : (0 : ℝ) ≤ 2 * chiBad q x := by
      have := chiBad_nonneg q x
      linarith
    linarith
  · simp only [charAbs, if_neg h]
    have hb := chiSum_changeLevel_sub_norm_le q c hc ψ x x le_rfl
    have he : chiSum q (DirichletCharacter.changeLevel hc ψ) x
        = chiSum c ψ x
          + (chiSum q (DirichletCharacter.changeLevel hc ψ) x - chiSum c ψ x) := by ring
    rw [he]
    calc ‖chiSum c ψ x
            + (chiSum q (DirichletCharacter.changeLevel hc ψ) x - chiSum c ψ x)‖
        ≤ ‖chiSum c ψ x‖
            + ‖chiSum q (DirichletCharacter.changeLevel hc ψ) x - chiSum c ψ x‖ :=
          norm_add_le _ _
      _ ≤ ‖chiSum c ψ x‖ + 2 * chiBad q x := by linarith

private lemma q_bound (q x : ℕ) [NeZero q] (hq : 2 ≤ q) :
    (∑ χ : DirichletCharacter ℂ q, charAbs q x χ)
      ≤ (∑ c ∈ q.divisors.filter (fun c => 2 ≤ c), primAbs c x)
        + (q.totient : ℝ) * (2 * chiBad q x) := by
  rw [sum_eq_sum_primitive_lifts_real q (fun χ => charAbs q x χ)]
  have hper : ∀ c : {d // d ∈ q.divisors},
      (∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
        charAbs q x (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1))
      ≤ (if 2 ≤ c.1 then primAbs c.1 x else 0)
          + (Fintype.card {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive} : ℝ)
              * (2 * chiBad q x) := by
    intro c
    by_cases hc1 : c.1 = 1
    · have hzero : ∀ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
          charAbs q x (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1) = 0 := by
        intro ψ
        have hψ : ψ.1 = 1 := DirichletCharacter.level_one' ψ.1 hc1
        have hcl : DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1
            = (1 : DirichletCharacter ℂ q) := by
          rw [hψ, DirichletCharacter.changeLevel_one]
        rw [hcl]
        simp [charAbs]
      rw [Finset.sum_eq_zero (fun ψ _ => hzero ψ)]
      apply add_nonneg
      · split_ifs with h2
        · exact primAbs_nonneg _ _
        · norm_num
      · exact mul_nonneg (by positivity) (by have := chiBad_nonneg q x; linarith)
    · have hc2 : 2 ≤ c.1 := by
        obtain ⟨hdvd, hq0⟩ := Nat.mem_divisors.mp c.2
        have hpos : 0 < c.1 := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hq0)
        omega
      have hsum : (∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
            ‖chiSum c.1 ψ.1 x‖) = primAbs c.1 x := by
        rw [primAbs]
        exact (Finset.sum_subtype
          (Finset.univ.filter (fun ψ : DirichletCharacter ℂ c.1 => ψ.IsPrimitive))
          (fun ψ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
          (fun ψ => ‖chiSum c.1 ψ x‖)).symm
      rw [if_pos hc2]
      calc (∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
              charAbs q x (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1))
          ≤ ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
              (‖chiSum c.1 ψ.1 x‖ + 2 * chiBad q x) :=
            Finset.sum_le_sum (fun ψ _ => term_le q c.1 x (Nat.mem_divisors.mp c.2).1 ψ.1)
        _ = (∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive}, ‖chiSum c.1 ψ.1 x‖)
              + (Fintype.card {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive} : ℝ)
                  * (2 * chiBad q x) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = primAbs c.1 x + (Fintype.card {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive} : ℝ)
                  * (2 * chiBad q x) := by rw [hsum]
  refine le_trans (Finset.sum_le_sum (fun c _ => hper c)) ?_
  rw [Finset.sum_attach q.divisors
        (fun d => (if 2 ≤ d then primAbs d x else 0)
          + (Fintype.card {ψ' : DirichletCharacter ℂ d // ψ'.IsPrimitive} : ℝ) * (2 * chiBad q x))]
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_filter]
  have hcard : (∑ c ∈ q.divisors,
        (Fintype.card {ψ' : DirichletCharacter ℂ c // ψ'.IsPrimitive} : ℝ)) = (q.totient : ℝ) := by
    rw [← card_prim q]
    apply Finset.sum_congr rfl
    intro c _
    rw [Fintype.card_subtype]
  rw [← Finset.sum_mul, hcard]

private lemma swap_le_general (Q : ℕ) (g : ℕ → ℝ) (hg : ∀ c, 0 ≤ g c) :
    (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ * ∑ c ∈ q.divisors, g c)
      ≤ (∑ m ∈ Finset.Icc 1 Q, ((m.totient : ℕ) : ℝ)⁻¹)
          * (∑ c ∈ Finset.Icc 1 Q, ((c.totient : ℕ) : ℝ)⁻¹ * g c) := by
  have hswap := Commons.NumberTheory.ArithmeticFunction.sum_Icc_divisors_filter_swap Q Q
    (fun d h => (((d * h).totient : ℕ) : ℝ)⁻¹ * g d)
  have hLHS : (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ * ∑ c ∈ q.divisors, g c)
      = ∑ n ∈ Finset.Icc 1 Q,
          ∑ d ∈ n.divisors.filter (fun d => d ≤ Q),
            (((d * (n / d)).totient : ℕ) : ℝ)⁻¹ * g d := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mul_sum]
    have hnQ : n ≤ Q := (Finset.mem_Icc.mp hn).2
    have hfil : n.divisors.filter (fun d => d ≤ Q) = n.divisors := by
      apply Finset.filter_true_of_mem
      intro d hd
      obtain ⟨hdvd, hn0⟩ := Nat.mem_divisors.mp hd
      exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd) hnQ
    rw [hfil]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
  rw [hLHS, hswap]
  have hstep : ∀ d ∈ Finset.Icc 1 Q, ∀ h ∈ Finset.Icc 1 (Q / d),
      (((d * h).totient : ℕ) : ℝ)⁻¹ * g d
        ≤ (((d.totient : ℕ) : ℝ)⁻¹ * g d) * (((h.totient : ℕ) : ℝ)⁻¹) := by
    intro d hd h hh
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hφd : 0 < (d.totient : ℝ) := by exact_mod_cast (Nat.totient_pos.mpr (by omega))
    have hφh : 0 < (h.totient : ℝ) := by
      have hh1 : 1 ≤ h := (Finset.mem_Icc.mp hh).1
      exact_mod_cast (Nat.totient_pos.mpr (by omega))
    have hsup := hg d
    have hsuper := Nat.totient_super_multiplicative d h
    have hsuperR : (d.totient : ℝ) * (h.totient : ℝ) ≤ ((d * h).totient : ℝ) := by
      exact_mod_cast hsuper
    have hinv : (((d * h).totient : ℕ) : ℝ)⁻¹ ≤ ((d.totient : ℝ) * (h.totient : ℝ))⁻¹ :=
      inv_anti₀ (mul_pos hφd hφh) hsuperR
    calc (((d * h).totient : ℕ) : ℝ)⁻¹ * g d
        ≤ ((d.totient : ℝ) * (h.totient : ℝ))⁻¹ * g d :=
          mul_le_mul_of_nonneg_right hinv hsup
      _ = (((d.totient : ℕ) : ℝ)⁻¹ * g d) * (((h.totient : ℕ) : ℝ)⁻¹) := by
          rw [mul_inv]; ring
  calc ∑ d ∈ Finset.Icc 1 Q, ∑ h ∈ Finset.Icc 1 (Q / d),
          (((d * h).totient : ℕ) : ℝ)⁻¹ * g d
      ≤ ∑ d ∈ Finset.Icc 1 Q, ∑ h ∈ Finset.Icc 1 (Q / d),
          (((d.totient : ℕ) : ℝ)⁻¹ * g d) * (((h.totient : ℕ) : ℝ)⁻¹) :=
        Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun h hh => hstep d hd h hh))
    _ = ∑ d ∈ Finset.Icc 1 Q,
          (((d.totient : ℕ) : ℝ)⁻¹ * g d)
            * ∑ h ∈ Finset.Icc 1 (Q / d), (((h.totient : ℕ) : ℝ)⁻¹) := by
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.mul_sum]
    _ ≤ ∑ d ∈ Finset.Icc 1 Q,
          (((d.totient : ℕ) : ℝ)⁻¹ * g d)
            * ∑ h ∈ Finset.Icc 1 Q, (((h.totient : ℕ) : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro d hd
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (inv_nonneg.mpr (by positivity)) (hg d))
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro h hh
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hh).1,
            le_trans (Finset.mem_Icc.mp hh).2 (Nat.div_le_self Q d)⟩
        · intro h _ _
          exact inv_nonneg.mpr (by positivity)
    _ = (∑ h ∈ Finset.Icc 1 Q, (((h.totient : ℕ) : ℝ)⁻¹))
          * ∑ d ∈ Finset.Icc 1 Q, (((d.totient : ℕ) : ℝ)⁻¹ * g d) := by
        rw [← Finset.sum_mul, mul_comm]

private lemma Icc_one_eq_insert_one_Icc_two (Q : ℕ) (hQ : 1 ≤ Q) :
    Finset.Icc 1 Q = insert 1 (Finset.Icc 2 Q) := by
  ext q
  rw [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, hQ'⟩
    rcases eq_or_lt_of_le h1 with h | h
    · exact Or.inl h.symm
    · exact Or.inr ⟨by omega, hQ'⟩
  · rintro (rfl | ⟨h2, hQ'⟩)
    · exact ⟨le_rfl, hQ⟩
    · exact ⟨by omega, hQ'⟩

private lemma chiBad_sum_bound (Q X : ℕ) (hQ : 1 ≤ Q) :
    (∑ q ∈ Finset.Icc 1 Q, chiBad q X)
      ≤ (1 / Real.log 2) * (Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2
          * Real.log ((X : ℝ) + 2) := by
  have h2log : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : 0 ≤ Real.log ((X : ℝ) + 2) := by
    apply Real.log_nonneg
    have hXnn : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
    linarith
  have hlogQ : 1 ≤ Real.log (2 * (Q : ℝ) + 2) := by
    have h4 : (4 : ℝ) ≤ 2 * (Q : ℝ) + 2 := by
      have : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
      linarith
    calc (1 : ℝ) ≤ Real.log 4 := by
          rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 4)]
          have := Real.exp_one_lt_d9
          linarith
      _ ≤ Real.log (2 * (Q : ℝ) + 2) := Real.log_le_log (by norm_num) h4
  calc (∑ q ∈ Finset.Icc 1 Q, chiBad q X)
      ≤ ∑ q ∈ Finset.Icc 1 Q,
          (q.primeFactors.card : ℝ) * Real.log ((X : ℝ) + 2) :=
        Finset.sum_le_sum (fun q hq => chiBad_le q X (Finset.mem_Icc.mp hq).1)
    _ = (∑ q ∈ Finset.Icc 1 Q, (q.primeFactors.card : ℝ)) * Real.log ((X : ℝ) + 2) := by
        rw [Finset.sum_mul]
    _ ≤ ((Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2) / Real.log 2)) * Real.log ((X : ℝ) + 2) := by
        apply mul_le_mul_of_nonneg_right _ hlogX
        calc (∑ q ∈ Finset.Icc 1 Q, (q.primeFactors.card : ℝ))
            ≤ ∑ q ∈ Finset.Icc 1 Q, Real.log (q : ℝ) / Real.log 2 :=
              Finset.sum_le_sum (fun q hq => primeFactors_card_le_log q (Finset.mem_Icc.mp hq).1)
          _ ≤ ∑ _q ∈ Finset.Icc 1 Q, Real.log (2 * (Q : ℝ) + 2) / Real.log 2 := by
              apply Finset.sum_le_sum
              intro q hq
              have hqQ : q ≤ Q := (Finset.mem_Icc.mp hq).2
              have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
              have hlogq : Real.log (q : ℝ) ≤ Real.log (2 * (Q : ℝ) + 2) := by
                apply Real.log_le_log
                · exact_mod_cast (by omega : 0 < q)
                · have : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
                  linarith
              have hlog2pos : 0 < Real.log 2 := h2log
              exact div_le_div_of_nonneg_right hlogq (le_of_lt hlog2pos)
          _ = (Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2) / Real.log 2) := by
              rw [Finset.sum_const, Nat.card_Icc]
              simp
    _ ≤ (1 / Real.log 2) * (Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2
          * Real.log ((X : ℝ) + 2) := by
        have hQnn : 0 ≤ (Q : ℝ) := Nat.cast_nonneg Q
        have hfac : (Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2) / Real.log 2)
            ≤ (1 / Real.log 2) * (Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 := by
          have h1 : (Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2) / Real.log 2)
              = (1 / Real.log 2) * (Q : ℝ) * Real.log (2 * (Q : ℝ) + 2) := by
            field_simp [ne_of_gt h2log]
          rw [h1]
          have hL : (0 : ℝ) ≤ (1 / Real.log 2) * (Q : ℝ) := by positivity
          have hlogL : Real.log (2 * (Q : ℝ) + 2) ≤ (Real.log (2 * (Q : ℝ) + 2)) ^ 2 := by
            nlinarith [hlogQ]
          calc (1 / Real.log 2) * (Q : ℝ) * Real.log (2 * (Q : ℝ) + 2)
              ≤ (1 / Real.log 2) * (Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 :=
                mul_le_mul_of_nonneg_left hlogL hL
            _ = (1 / Real.log 2) * (Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 := rfl
        exact mul_le_mul_of_nonneg_right hfac hlogX

theorem character_sum_primitive_reduction :
    ∃ C : ℝ, 0 < C ∧ ∀ x Q : ℕ, 1 ≤ Q →
      (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          (if χ = 1 then 0 else ‖Commons.NumberTheory.BombieriVinogradov.chiSum q χ x‖))
      ≤ C * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 *
          (∑ c ∈ Finset.Icc 2 Q, ((c.totient : ℕ) : ℝ)⁻¹ *
            ∑ ψ ∈ (@Finset.filter (DirichletCharacter ℂ c) (fun ψ => ψ.IsPrimitive) (Classical.decPred _) Finset.univ),
              ‖Commons.NumberTheory.BombieriVinogradov.chiSum c ψ x‖)
        + C * (Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 * Real.log ((x : ℝ) + 2) := by
  classical
  obtain ⟨C1, hC1pos, hC1⟩ := Commons.NumberTheory.Totient.sum_inv_totient_Icc_le_powLog
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  set C : ℝ := C1 + 1 / (Real.log 4) ^ 2 + 2 * (1 / Real.log 2) + 1 with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    have h1 : 0 < 1 / (Real.log 4) ^ 2 := div_pos one_pos (pow_pos hlog4pos 2)
    have h2 : 0 < 2 * (1 / Real.log 2) := by
      apply mul_pos (by norm_num)
      exact div_pos one_pos hlog2pos
    linarith
  have hC1le : C1 ≤ C := by
    rw [hCdef]
    have h1 : 0 ≤ 1 / (Real.log 4) ^ 2 :=
      le_of_lt (div_pos one_pos (pow_pos hlog4pos 2))
    have h2 : 0 ≤ 2 * (1 / Real.log 2) :=
      le_of_lt (mul_pos (by norm_num) (div_pos one_pos hlog2pos))
    linarith
  have hCle : 1 / (Real.log 4) ^ 2 ≤ C := by
    rw [hCdef]
    have h1 : 0 ≤ C1 := le_of_lt hC1pos
    have h2 : 0 ≤ 2 * (1 / Real.log 2) :=
      le_of_lt (mul_pos (by norm_num) (div_pos one_pos hlog2pos))
    linarith
  have hClog : 2 * (1 / Real.log 2) ≤ C := by
    rw [hCdef]
    have h1 : 0 ≤ C1 := le_of_lt hC1pos
    have h2 : 0 ≤ 1 / (Real.log 4) ^ 2 :=
      le_of_lt (div_pos one_pos (pow_pos hlog4pos 2))
    linarith
  have htot : ∀ Q : ℕ, 1 ≤ Q →
      (∑ m ∈ Finset.Icc 1 Q, ((m.totient : ℕ) : ℝ)⁻¹)
        ≤ C * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 := by
    intro Q hQ
    rcases eq_or_lt_of_le hQ with h | h
    · rw [← h, Finset.Icc_self, Finset.sum_singleton]
      have h1 : ((1 : ℕ).totient : ℕ) = 1 := Nat.totient_one
      rw [h1]
      simp only [Nat.cast_one, inv_one]
      have hnorm : (2 : ℝ) * 1 + 2 = 4 := by norm_num
      rw [hnorm]
      have hone : (1 / (Real.log 4) ^ 2) * (Real.log 4) ^ 2 = 1 := by
        rw [one_div, inv_mul_cancel₀ (ne_of_gt (pow_pos hlog4pos 2))]
      calc (1 : ℝ) = (1 / (Real.log 4) ^ 2) * (Real.log 4) ^ 2 := hone.symm
        _ ≤ C * (Real.log 4) ^ 2 := mul_le_mul_of_nonneg_right hCle (sq_nonneg _)
    · calc (∑ m ∈ Finset.Icc 1 Q, ((m.totient : ℕ) : ℝ)⁻¹)
          ≤ C1 * (Real.log (Q : ℝ)) ^ 2 := hC1 Q h
        _ ≤ C1 * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hC1pos)
            apply pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Q)))
            apply Real.log_le_log (by exact_mod_cast (by omega : 0 < Q))
            have hQnn : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
            linarith
        _ ≤ C * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 :=
            mul_le_mul_of_nonneg_right hC1le
              (sq_nonneg (Real.log (2 * (Q : ℝ) + 2)))
  refine ⟨C, hCpos, ?_⟩
  intro x Q hQ
  have hL : (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, (if χ = 1 then 0 else ‖chiSum q χ x‖))
      = ∑ q ∈ Finset.Icc 2 Q, ((q.totient : ℕ) : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, (if χ = 1 then 0 else ‖chiSum q χ x‖) := by
    have hsub : Finset.Icc 2 Q ⊆ Finset.Icc 1 Q := by
      intro q hq
      rw [Finset.mem_Icc] at hq ⊢
      exact ⟨by omega, hq.2⟩
    refine (Finset.sum_subset hsub ?_).symm
    intro q hq hqnot
    have hq1 : q = 1 := by
      rw [Finset.mem_Icc] at hq hqnot
      omega
    subst hq1
    have h1 : ((1 : ℕ).totient : ℕ) = 1 := Nat.totient_one
    rw [h1]
    simp only [Nat.cast_one, inv_one, one_mul]
    apply Finset.sum_eq_zero
    intro χ _
    exact if_pos (DirichletCharacter.level_one χ)
  rw [hL]
  have hstep : ∀ q ∈ Finset.Icc 2 Q,
      ((q.totient : ℕ) : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (if χ = 1 then 0 else ‖chiSum q χ x‖)
      ≤ ((q.totient : ℕ) : ℝ)⁻¹ * (∑ c ∈ q.divisors.filter (fun c => 2 ≤ c), primAbs c x)
        + 2 * chiBad q x := by
    intro q hq
    have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
    have _ : NeZero q := ⟨by omega⟩
    have hφ : (((q.totient : ℕ) : ℝ)) ≠ 0 := by
      have hpos : 0 < q.totient := Nat.totient_pos.mpr (by omega)
      exact_mod_cast ne_of_gt hpos
    calc ((q.totient : ℕ) : ℝ)⁻¹ * (∑ χ : DirichletCharacter ℂ q, charAbs q x χ)
        ≤ ((q.totient : ℕ) : ℝ)⁻¹ * ((∑ c ∈ q.divisors.filter (fun c => 2 ≤ c), primAbs c x)
            + (q.totient : ℝ) * (2 * chiBad q x)) :=
          mul_le_mul_of_nonneg_left (q_bound q x hq2) (by positivity)
      _ = ((q.totient : ℕ) : ℝ)⁻¹ * (∑ c ∈ q.divisors.filter (fun c => 2 ≤ c), primAbs c x)
            + 2 * chiBad q x := by
          rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hφ, one_mul]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [Finset.sum_add_distrib]
  have hsub : Finset.Icc 2 Q ⊆ Finset.Icc 1 Q := by
    intro q hq
    rw [Finset.mem_Icc] at hq ⊢
    exact ⟨by omega, hq.2⟩
  have hA : (∑ q ∈ Finset.Icc 2 Q, ((q.totient : ℕ) : ℝ)⁻¹ *
        (∑ c ∈ q.divisors.filter (fun c => 2 ≤ c), primAbs c x))
      ≤ C * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 *
          (∑ c ∈ Finset.Icc 2 Q, ((c.totient : ℕ) : ℝ)⁻¹ * primAbs c x) := by
    have hA1 : (∑ q ∈ Finset.Icc 2 Q, ((q.totient : ℕ) : ℝ)⁻¹ *
          (∑ c ∈ q.divisors.filter (fun c => 2 ≤ c), primAbs c x))
        ≤ ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ *
          (∑ c ∈ q.divisors.filter (fun c => 2 ≤ c), primAbs c x) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun q _ _ => mul_nonneg (by positivity)
          (Finset.sum_nonneg (fun c _ => primAbs_nonneg c x)))
    have hA2 : (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ *
          (∑ c ∈ q.divisors.filter (fun c => 2 ≤ c), primAbs c x))
        ≤ (∑ m ∈ Finset.Icc 1 Q, ((m.totient : ℕ) : ℝ)⁻¹)
            * (∑ c ∈ Finset.Icc 2 Q, ((c.totient : ℕ) : ℝ)⁻¹ * primAbs c x) := by
      have hsw := swap_le_general Q (fun c => if 2 ≤ c then primAbs c x else 0)
        (fun c => by by_cases h : 2 ≤ c <;> simp [h, primAbs_nonneg])
      have hfilter : ∀ q : ℕ, (∑ c ∈ q.divisors.filter (fun c => 2 ≤ c), primAbs c x)
          = ∑ c ∈ q.divisors, (if 2 ≤ c then primAbs c x else 0) := by
        intro q
        rw [Finset.sum_filter]
      have hR : (∑ c ∈ Finset.Icc 1 Q,
            ((c.totient : ℕ) : ℝ)⁻¹ * (if 2 ≤ c then primAbs c x else 0))
          = ∑ c ∈ Finset.Icc 2 Q, ((c.totient : ℕ) : ℝ)⁻¹ * primAbs c x := by
        calc (∑ c ∈ Finset.Icc 1 Q,
              ((c.totient : ℕ) : ℝ)⁻¹ * (if 2 ≤ c then primAbs c x else 0))
            = ∑ c ∈ Finset.Icc 2 Q,
                ((c.totient : ℕ) : ℝ)⁻¹ * (if 2 ≤ c then primAbs c x else 0) := by
              refine (Finset.sum_subset hsub ?_).symm
              intro c hc hcnot
              have hc1 : c = 1 := by
                rw [Finset.mem_Icc] at hc hcnot
                omega
              subst hc1
              have h1 : ((1 : ℕ).totient : ℕ) = 1 := Nat.totient_one
              rw [h1]
              simp only [Nat.cast_one, inv_one, one_mul]
              rw [if_neg (by norm_num : ¬ (2 ≤ (1 : ℕ)))]
          _ = ∑ c ∈ Finset.Icc 2 Q, ((c.totient : ℕ) : ℝ)⁻¹ * primAbs c x := by
              apply Finset.sum_congr rfl
              intro c hc
              rw [if_pos (Finset.mem_Icc.mp hc).1]
      calc (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ *
              (∑ c ∈ q.divisors.filter (fun c => 2 ≤ c), primAbs c x))
          = ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ *
              ∑ c ∈ q.divisors, (if 2 ≤ c then primAbs c x else 0) := by
            apply Finset.sum_congr rfl
            intro q _
            rw [hfilter q]
        _ ≤ (∑ m ∈ Finset.Icc 1 Q, ((m.totient : ℕ) : ℝ)⁻¹)
              * (∑ c ∈ Finset.Icc 1 Q,
                  ((c.totient : ℕ) : ℝ)⁻¹ * (if 2 ≤ c then primAbs c x else 0)) := hsw
        _ = (∑ m ∈ Finset.Icc 1 Q, ((m.totient : ℕ) : ℝ)⁻¹)
              * (∑ c ∈ Finset.Icc 2 Q, ((c.totient : ℕ) : ℝ)⁻¹ * primAbs c x) := by rw [hR]
    have hA3 : (∑ m ∈ Finset.Icc 1 Q, ((m.totient : ℕ) : ℝ)⁻¹)
          * (∑ c ∈ Finset.Icc 2 Q, ((c.totient : ℕ) : ℝ)⁻¹ * primAbs c x)
        ≤ C * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 *
          (∑ c ∈ Finset.Icc 2 Q, ((c.totient : ℕ) : ℝ)⁻¹ * primAbs c x) :=
      mul_le_mul_of_nonneg_right (htot Q hQ)
        (Finset.sum_nonneg (fun c _ => mul_nonneg (by positivity) (primAbs_nonneg c x)))
    exact hA1.trans (hA2.trans hA3)
  have hB : (∑ q ∈ Finset.Icc 2 Q, 2 * chiBad q x)
      ≤ C * (Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 * Real.log ((x : ℝ) + 2) := by
    have h2 : (∑ q ∈ Finset.Icc 2 Q, chiBad q x) ≤ ∑ q ∈ Finset.Icc 1 Q, chiBad q x :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => chiBad_nonneg q x)
    have h3 : (∑ q ∈ Finset.Icc 1 Q, chiBad q x)
        ≤ (1 / Real.log 2) * (Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2
            * Real.log ((x : ℝ) + 2) := chiBad_sum_bound Q x hQ
    have hnn : 0 ≤ (Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 * Real.log ((x : ℝ) + 2) := by
      apply mul_nonneg
      · exact mul_nonneg (by positivity) (sq_nonneg _)
      · apply Real.log_nonneg
        have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
        linarith
    calc (∑ q ∈ Finset.Icc 2 Q, 2 * chiBad q x)
        = 2 * ∑ q ∈ Finset.Icc 2 Q, chiBad q x := by rw [Finset.mul_sum]
      _ ≤ 2 * ((1 / Real.log 2) * (Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2
              * Real.log ((x : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) (by norm_num)
      _ = (2 * (1 / Real.log 2))
            * ((Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 * Real.log ((x : ℝ) + 2)) := by ring
      _ ≤ C * ((Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 * Real.log ((x : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_right hClog hnn
      _ = C * (Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 * Real.log ((x : ℝ) + 2) := by ring
  exact add_le_add hA hB

end

end Commons.NumberTheory.BombieriVinogradov
