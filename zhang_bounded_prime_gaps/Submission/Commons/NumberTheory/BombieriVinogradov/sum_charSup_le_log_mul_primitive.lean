import Mathlib
import Submission.Commons.NumberTheory.Totient.sum_inv_totient_Icc_le_powLog
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_Icc_divisors_filter_swap
import Submission.Commons.NumberTheory.DirichletCharacter.sum_characters_eq_sum_primitive_lifts
import Submission.Commons.NumberTheory.DirichletCharacter.changeLevel_stable_nat
import Submission.Commons.NumberTheory.DirichletCharacter.conductor_lift_primitive
import Submission.Commons.NumberTheory.Goldbach.sum_vonMangoldt_not_coprime

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators
open Finset
open Classical

noncomputable def chiSum (q : ℕ) (χ : DirichletCharacter ℂ q) (y : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (y + 1), ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)

noncomputable def chiSup (q : ℕ) (χ : DirichletCharacter ℂ q) (X : ℕ) : ℝ :=
  sSup ((fun y : ℕ => ‖chiSum q χ y - (if χ = 1 then (y : ℂ) else 0)‖) '' Set.Icc 1 X)

noncomputable def chiBad (q : ℕ) (X : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range (X + 1)).filter (fun n => ¬ Nat.Coprime n q),
    ArithmeticFunction.vonMangoldt n

lemma chiBad_nonneg (q X : ℕ) : 0 ≤ chiBad q X := by
  apply Finset.sum_nonneg
  intro n _
  exact ArithmeticFunction.vonMangoldt_nonneg

lemma chiSup_nonneg (q X : ℕ) (χ : DirichletCharacter ℂ q) : 0 ≤ chiSup q χ X := by
  apply Real.sSup_nonneg
  rintro _ ⟨y, -, rfl⟩
  exact norm_nonneg _

lemma chiSup_le_of_le (q X : ℕ) (χ : DirichletCharacter ℂ q) {B : ℝ}
    (h : ∀ y ∈ Set.Icc 1 X, ‖chiSum q χ y - (if χ = 1 then (y : ℂ) else 0)‖ ≤ B)
    (hB : 0 ≤ B) : chiSup q χ X ≤ B := by
  apply Real.sSup_le _ hB
  rintro _ ⟨y, hy, rfl⟩
  exact h y hy

/-- The difference of the two von Mangoldt sums only sees the `n` that are not coprime to `q`. -/
lemma chiSum_changeLevel_sub (q c : ℕ) [NeZero q] (h : c ∣ q) (ψ : DirichletCharacter ℂ c)
    (y : ℕ) :
    chiSum q (DirichletCharacter.changeLevel h ψ) y - chiSum c ψ y
      = ∑ n ∈ (Finset.range (y + 1)).filter (fun n => ¬ Nat.Coprime n q),
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            ((DirichletCharacter.changeLevel h ψ) ((n : ℕ) : ZMod q) - ψ ((n : ℕ) : ZMod c)) := by
  have hsub : chiSum q (DirichletCharacter.changeLevel h ψ) y - chiSum c ψ y
      = ∑ n ∈ Finset.range (y + 1),
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            ((DirichletCharacter.changeLevel h ψ) ((n : ℕ) : ZMod q) - ψ ((n : ℕ) : ZMod c)) := by
    simp only [chiSum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hsub]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (y + 1))
      (fun n => Nat.Coprime n q)
      (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            ((DirichletCharacter.changeLevel h ψ) ((n : ℕ) : ZMod q) - ψ ((n : ℕ) : ZMod c)))]
  have hzero : (∑ n ∈ (Finset.range (y + 1)).filter (fun n => Nat.Coprime n q),
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        ((DirichletCharacter.changeLevel h ψ) ((n : ℕ) : ZMod q) - ψ ((n : ℕ) : ZMod c))) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [Commons.NumberTheory.DirichletCharacter.changeLevel_stable_nat h ψ hn.2, sub_self, mul_zero]
  rw [hzero, zero_add]

/-- Pointwise norm bound for the difference of the two von Mangoldt sums. -/
lemma chiSum_changeLevel_sub_norm_le (q c : ℕ) [NeZero q] (h : c ∣ q) (ψ : DirichletCharacter ℂ c)
    (X y : ℕ) (hy : y ≤ X) :
    ‖chiSum q (DirichletCharacter.changeLevel h ψ) y - chiSum c ψ y‖ ≤ 2 * chiBad q X := by
  rw [chiSum_changeLevel_sub q c h ψ y]
  calc ‖∑ n ∈ (Finset.range (y + 1)).filter (fun n => ¬ Nat.Coprime n q),
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          ((DirichletCharacter.changeLevel h ψ) ((n : ℕ) : ZMod q) - ψ ((n : ℕ) : ZMod c))‖
      ≤ ∑ n ∈ (Finset.range (y + 1)).filter (fun n => ¬ Nat.Coprime n q),
          ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            ((DirichletCharacter.changeLevel h ψ) ((n : ℕ) : ZMod q) - ψ ((n : ℕ) : ZMod c))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ (Finset.range (y + 1)).filter (fun n => ¬ Nat.Coprime n q),
          2 * ArithmeticFunction.vonMangoldt n := by
        apply Finset.sum_le_sum
        intro n _
        rw [norm_mul]
        have h1 : ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ = ArithmeticFunction.vonMangoldt n := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        rw [h1]
        have h2 : ‖(DirichletCharacter.changeLevel h ψ) ((n : ℕ) : ZMod q) - ψ ((n : ℕ) : ZMod c)‖ ≤ 2 := by
          calc ‖(DirichletCharacter.changeLevel h ψ) ((n : ℕ) : ZMod q) - ψ ((n : ℕ) : ZMod c)‖
              ≤ ‖(DirichletCharacter.changeLevel h ψ) ((n : ℕ) : ZMod q)‖ + ‖ψ ((n : ℕ) : ZMod c)‖ :=
                norm_sub_le _ _
            _ ≤ 1 + 1 := add_le_add (DirichletCharacter.norm_le_one _ _) (DirichletCharacter.norm_le_one _ _)
            _ = 2 := by norm_num
        calc ArithmeticFunction.vonMangoldt n *
              ‖(DirichletCharacter.changeLevel h ψ) ((n : ℕ) : ZMod q) - ψ ((n : ℕ) : ZMod c)‖
            ≤ ArithmeticFunction.vonMangoldt n * 2 :=
              mul_le_mul_of_nonneg_left h2 ArithmeticFunction.vonMangoldt_nonneg
          _ = 2 * ArithmeticFunction.vonMangoldt n := by ring
    _ = 2 * ∑ n ∈ (Finset.range (y + 1)).filter (fun n => ¬ Nat.Coprime n q),
          ArithmeticFunction.vonMangoldt n := by
        rw [Finset.mul_sum]
    _ ≤ 2 * chiBad q X := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          rw [Finset.mem_filter] at hn ⊢
          exact ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hn.1; omega), hn.2⟩
        · intro n _ _
          exact ArithmeticFunction.vonMangoldt_nonneg


/-- For a primitive character, lifting to a multiple level does not change whether it is
the principal character. -/
lemma changeLevel_eq_one_iff (q c : ℕ) [NeZero q] (h : c ∣ q) (ψ : DirichletCharacter ℂ c)
    (hprim : ψ.IsPrimitive) :
    (DirichletCharacter.changeLevel h ψ = 1) ↔ (ψ = 1) := by
  constructor
  · intro hχ
    have h1 : (DirichletCharacter.changeLevel h ψ).conductor = 1 :=
      (DirichletCharacter.eq_one_iff_conductor_eq_one (χ := DirichletCharacter.changeLevel h ψ)).mp hχ
    rw [DirichletCharacter.conductor_changeLevel ψ h] at h1
    have hc : c = 1 := by
      rw [← (DirichletCharacter.isPrimitive_def ψ).mp hprim]
      exact h1
    subst hc
    exact DirichletCharacter.level_one ψ
  · intro hψ
    rw [hψ]
    exact DirichletCharacter.changeLevel_one h

/-- `chiSup` at a lifted level is bounded by `chiSup` at the level of the primitive
character plus the coprime error. -/
lemma chiSup_changeLevel_le (q c : ℕ) [NeZero q] (h : c ∣ q) (ψ : DirichletCharacter ℂ c)
    (hprim : ψ.IsPrimitive) (X : ℕ) :
    chiSup q (DirichletCharacter.changeLevel h ψ) X ≤ 2 * chiBad q X + chiSup c ψ X := by
  set χ := DirichletCharacter.changeLevel h ψ with hχdef
  have hδ := changeLevel_eq_one_iff q c h ψ hprim
  have hδ' : χ = 1 ↔ ψ = 1 := hδ
  have hbdd : BddAbove ((fun y : ℕ => ‖chiSum c ψ y - (if ψ = 1 then (y : ℂ) else 0)‖)
      '' Set.Icc 1 X) := by
    have hfin : (Set.Icc 1 X : Set ℕ).Finite := Set.finite_Icc 1 X
    exact (hfin.image _).bddAbove
  have hB : 0 ≤ 2 * chiBad q X + chiSup c ψ X := by
    have h1 := chiSup_nonneg c X ψ
    have h2 := chiBad_nonneg q X
    linarith
  refine chiSup_le_of_le q X χ ?_ hB
  intro y hy
  have hyX : y ≤ X := hy.2
  have hmem : ‖chiSum c ψ y - (if ψ = 1 then (y : ℂ) else 0)‖ ∈
      ((fun y : ℕ => ‖chiSum c ψ y - (if ψ = 1 then (y : ℂ) else 0)‖) '' Set.Icc 1 X) :=
    Set.mem_image_of_mem _ hy
  have hle2 : ‖chiSum c ψ y - (if ψ = 1 then (y : ℂ) else 0)‖ ≤ chiSup c ψ X :=
    le_csSup hbdd hmem
  have hle1 : ‖chiSum q χ y - chiSum c ψ y‖ ≤ 2 * chiBad q X := by
    rw [hχdef]
    exact chiSum_changeLevel_sub_norm_le q c h ψ X y hyX
  simp only [hδ']
  have hE : chiSum q χ y - (if ψ = 1 then (y : ℂ) else 0)
      = (chiSum q χ y - chiSum c ψ y) + (chiSum c ψ y - (if ψ = 1 then (y : ℂ) else 0)) := by
    ring
  rw [hE]
  exact le_trans (norm_add_le _ _) (add_le_add hle1 hle2)


/-- The number of distinct prime factors of `q ≥ 1` is at most `log q / log 2`. -/
lemma primeFactors_card_le_log (q : ℕ) (hq : 1 ≤ q) :
    (q.primeFactors.card : ℝ) ≤ Real.log (q : ℝ) / Real.log 2 := by
  have hq0 : q ≠ 0 := by omega
  have h2log : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hprod : (2 : ℕ) ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p := by
    rw [(Finset.prod_const (s := q.primeFactors) (2 : ℕ)).symm]
    exact Finset.prod_le_prod (fun p _ => by norm_num)
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have hdvd : (∏ p ∈ q.primeFactors, p) ∣ q := Nat.prod_primeFactors_dvd q
  have hprodle : (∏ p ∈ q.primeFactors, p) ≤ q :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hdvd
  have hle : (2 : ℝ) ^ q.primeFactors.card ≤ (q : ℝ) := by
    have h' : ((2 ^ q.primeFactors.card : ℕ) : ℝ) ≤ (q : ℝ) :=
      by exact_mod_cast le_trans hprod hprodle
    simpa using h'
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2:ℝ) ^ q.primeFactors.card) hle
  rw [Real.log_pow] at hlog
  rw [le_div_iff₀ h2log]
  linarith [hlog]

/-- The von Mangoldt sum over the `n ≤ X` that are not coprime to `q ≥ 1` is at most
`ω(q) · log(X+2)`. -/
lemma chiBad_le (q X : ℕ) (hq : 1 ≤ q) :
    chiBad q X ≤ (q.primeFactors.card : ℝ) * Real.log ((X : ℝ) + 2) := by
  classical
  have hz : ArithmeticFunction.vonMangoldt 0 = 0 := by
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff, isPrimePow_nat_iff]
    rintro ⟨p, k, hp, hk, hpk⟩
    have : 0 < p ^ k := pow_pos hp.pos k
    omega
  have hlog_nonneg : 0 ≤ Real.log ((X : ℝ) + 2) := by
    apply Real.log_nonneg
    have hXnn : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
    linarith
  have hIcc : chiBad q X = ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n := by
    unfold chiBad
    symm
    refine Finset.sum_subset ?_ ?_
    · intro n hn
      rw [Finset.mem_filter] at hn ⊢
      exact ⟨Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hn.1).2; omega), hn.2⟩
    · intro n hn hnnot
      rw [Finset.mem_filter] at hn
      obtain ⟨hnrange, hn2⟩ := hn
      have hn0 : n = 0 := by
        by_contra hne
        exact hnnot (Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hne,
            Nat.lt_succ_iff.mp (Finset.mem_range.mp hnrange)⟩, hn2⟩)
      rw [hn0, hz]
  rw [hIcc, Commons.NumberTheory.Goldbach.sum_vonMangoldt_not_coprime q X]
  have hterm : ∀ p ∈ (Finset.Icc 1 X).filter (fun p => p.Prime ∧ p ∣ q),
      ((Nat.log p X : ℕ) : ℝ) * Real.log (p : ℝ) ≤ Real.log ((X : ℝ) + 2) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hp1, hpX⟩, hpprime, hpdvd⟩ := hp
    have hp2 : 2 ≤ p := hpprime.two_le
    have hX2 : 2 ≤ X := le_trans hp2 hpX
    have hpk : p ^ Nat.log p X ≤ X := Nat.pow_log_le_self p (by omega)
    calc ((Nat.log p X : ℕ) : ℝ) * Real.log (p : ℝ)
        = Real.log ((p : ℝ) ^ Nat.log p X) := (Real.log_pow (p : ℝ) (Nat.log p X)).symm
      _ = Real.log (((p ^ Nat.log p X : ℕ) : ℝ)) := by rw [Nat.cast_pow]
      _ ≤ Real.log ((X : ℝ)) := by
            apply Real.log_le_log
            · exact_mod_cast pow_pos hpprime.pos (Nat.log p X)
            · exact_mod_cast hpk
      _ ≤ Real.log ((X : ℝ) + 2) := by
            apply Real.log_le_log
            · exact_mod_cast (show 0 < X by omega)
            · linarith
  have hRsub : (Finset.Icc 1 X).filter (fun p => p.Prime ∧ p ∣ q) ⊆ q.primeFactors := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact Nat.mem_primeFactors.mpr ⟨hp.2.1, hp.2.2, by omega⟩
  calc (∑ p ∈ (Finset.Icc 1 X).filter (fun p => p.Prime ∧ p ∣ q),
          ((Nat.log p X : ℕ) : ℝ) * Real.log (p : ℝ))
      ≤ ∑ _p ∈ (Finset.Icc 1 X).filter (fun p => p.Prime ∧ p ∣ q),
          Real.log ((X : ℝ) + 2) := Finset.sum_le_sum hterm
    _ = (((Finset.Icc 1 X).filter (fun p => p.Prime ∧ p ∣ q)).card : ℝ)
          * Real.log ((X : ℝ) + 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (q.primeFactors.card : ℝ) * Real.log ((X : ℝ) + 2) := by
          apply mul_le_mul_of_nonneg_right _ hlog_nonneg
          exact_mod_cast Finset.card_le_card hRsub


/-- The primitive part of the character sum at level `c`. -/
noncomputable def primSup (c : ℕ) (X : ℕ) : ℝ :=
  ∑ ψ ∈ (Finset.univ.filter (fun ψ : DirichletCharacter ℂ c => ψ.IsPrimitive)), chiSup c ψ X

/-- Real-valued form of `sum_characters_eq_sum_primitive_lifts`. -/
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

/-- The number of primitive characters lifted from the divisors of `q` is `φ(q)`. -/
private lemma primCount (q : ℕ) [NeZero q] :
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

/-- Sum over all characters mod `q` controlled by the primitive sums and the coprimality
error. -/
lemma chiSup_sum_le (q : ℕ) [NeZero q] (X : ℕ) :
    (∑ χ : DirichletCharacter ℂ q, chiSup q χ X)
      ≤ (∑ c ∈ q.divisors, primSup c X) + (q.totient : ℝ) * (2 * chiBad q X) := by
  have hdec := sum_eq_sum_primitive_lifts_real q (fun χ => chiSup q χ X)
  rw [hdec]
  have hstep : ∀ c ∈ q.divisors.attach,
      (∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
          chiSup q (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1) X)
        ≤ primSup c.1 X
          + (Fintype.card {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive} : ℝ)
              * (2 * chiBad q X) := by
    intro c _
    have h1 : ∀ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
        chiSup q (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1) X
          ≤ 2 * chiBad q X + chiSup c.1 ψ.1 X :=
      fun ψ => chiSup_changeLevel_le q c.1 (Nat.mem_divisors.mp c.2).1 ψ.1 ψ.2 X
    have h2 : (∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive}, chiSup c.1 ψ.1 X)
        = primSup c.1 X := by
      rw [primSup]
      exact (Finset.sum_subtype (Finset.univ.filter
          (fun ψ : DirichletCharacter ℂ c.1 => ψ.IsPrimitive))
        (fun ψ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
        (fun ψ => chiSup c.1 ψ X)).symm
    calc (∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
            chiSup q (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1) X)
        ≤ ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
            (2 * chiBad q X + chiSup c.1 ψ.1 X) := Finset.sum_le_sum (fun ψ _ => h1 ψ)
      _ = (∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive}, (2 * chiBad q X))
            + ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive}, chiSup c.1 ψ.1 X :=
          Finset.sum_add_distrib
      _ = (Fintype.card {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive} : ℝ) * (2 * chiBad q X)
            + primSup c.1 X := by
          rw [h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = primSup c.1 X
            + (Fintype.card {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive} : ℝ)
                * (2 * chiBad q X) := by ring
  have hcast : (∑ c ∈ q.divisors,
        (Fintype.card {ψ' : DirichletCharacter ℂ c // ψ'.IsPrimitive} : ℝ))
      = ∑ c ∈ q.divisors,
          ((Finset.univ.filter (fun ψ : DirichletCharacter ℂ c => ψ.IsPrimitive)).card : ℝ) :=
    Finset.sum_congr rfl (fun c _ => by rw [Fintype.card_subtype])
  calc (∑ c ∈ q.divisors.attach,
          ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
            chiSup q (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1) X)
      ≤ ∑ c ∈ q.divisors.attach,
          (primSup c.1 X
            + (Fintype.card {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive} : ℝ)
                * (2 * chiBad q X)) := Finset.sum_le_sum hstep
    _ = (∑ c ∈ q.divisors.attach, primSup c.1 X)
          + ∑ c ∈ q.divisors.attach,
              (Fintype.card {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive} : ℝ)
                * (2 * chiBad q X) := Finset.sum_add_distrib
    _ = (∑ c ∈ q.divisors, primSup c X)
          + (∑ c ∈ q.divisors,
              (Fintype.card {ψ' : DirichletCharacter ℂ c // ψ'.IsPrimitive} : ℝ))
              * (2 * chiBad q X) := by
          have hA : (∑ c ∈ q.divisors.attach, primSup c.1 X)
              = ∑ c ∈ q.divisors, primSup c X :=
            Finset.sum_attach q.divisors (fun c => primSup c X)
          have hB : (∑ c ∈ q.divisors.attach,
                (Fintype.card {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive} : ℝ))
              = ∑ c ∈ q.divisors,
                  (Fintype.card {ψ' : DirichletCharacter ℂ c // ψ'.IsPrimitive} : ℝ) :=
            Finset.sum_attach q.divisors
              (fun c => (Fintype.card {ψ' : DirichletCharacter ℂ c // ψ'.IsPrimitive} : ℝ))
          rw [← Finset.sum_mul, hA, hB]
    _ = (∑ c ∈ q.divisors, primSup c X)
          + (∑ c ∈ q.divisors,
              ((Finset.univ.filter (fun ψ : DirichletCharacter ℂ c => ψ.IsPrimitive)).card : ℝ))
              * (2 * chiBad q X) := by rw [hcast]
    _ = (∑ c ∈ q.divisors, primSup c X) + (q.totient : ℝ) * (2 * chiBad q X) := by
          rw [primCount q]

/-- `primSup` is nonnegative. -/
private lemma primSup_nonneg (c X : ℕ) : 0 ≤ primSup c X :=
  Finset.sum_nonneg (fun ψ _ => chiSup_nonneg c X ψ)

/-- The weighted double divisor sum is controlled by the totient sum times the primitive sum. -/
private lemma swap_le (Q X : ℕ) (_hQ : 1 ≤ Q) :
    (∑ q ∈ Finset.Icc 1 Q,
        ((q.totient : ℕ) : ℝ)⁻¹ * ∑ c ∈ q.divisors, primSup c X)
      ≤ (∑ m ∈ Finset.Icc 1 Q, ((m.totient : ℕ) : ℝ)⁻¹)
          * (∑ c ∈ Finset.Icc 1 Q, ((c.totient : ℕ) : ℝ)⁻¹ * primSup c X) := by
  have hswap := Commons.NumberTheory.ArithmeticFunction.sum_Icc_divisors_filter_swap Q Q
    (fun d h => (((d * h).totient : ℕ) : ℝ)⁻¹ * primSup d X)
  have hLHS : (∑ q ∈ Finset.Icc 1 Q,
        ((q.totient : ℕ) : ℝ)⁻¹ * ∑ c ∈ q.divisors, primSup c X)
      = ∑ n ∈ Finset.Icc 1 Q,
          ∑ d ∈ n.divisors.filter (fun d => d ≤ Q),
            (((d * (n / d)).totient : ℕ) : ℝ)⁻¹ * primSup d X := by
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
  -- bound each term
  have hstep : ∀ d ∈ Finset.Icc 1 Q, ∀ h ∈ Finset.Icc 1 (Q / d),
      (((d * h).totient : ℕ) : ℝ)⁻¹ * primSup d X
        ≤ (((d.totient : ℕ) : ℝ)⁻¹ * primSup d X) * (((h.totient : ℕ) : ℝ)⁻¹) := by
    intro d hd h hh
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hφd : 0 < (d.totient : ℝ) := by exact_mod_cast (Nat.totient_pos.mpr (by omega))
    have hφh : 0 < (h.totient : ℝ) := by
      have hh1 : 1 ≤ h := (Finset.mem_Icc.mp hh).1
      exact_mod_cast (Nat.totient_pos.mpr (by omega))
    have hsup := primSup_nonneg d X
    have hsuper := Nat.totient_super_multiplicative d h
    have hsuperR : (d.totient : ℝ) * (h.totient : ℝ) ≤ ((d * h).totient : ℝ) := by
      exact_mod_cast hsuper
    have hinv : (((d * h).totient : ℕ) : ℝ)⁻¹ ≤ ((d.totient : ℝ) * (h.totient : ℝ))⁻¹ :=
      inv_anti₀ (mul_pos hφd hφh) hsuperR
    calc (((d * h).totient : ℕ) : ℝ)⁻¹ * primSup d X
        ≤ ((d.totient : ℝ) * (h.totient : ℝ))⁻¹ * primSup d X :=
          mul_le_mul_of_nonneg_right hinv hsup
      _ = (((d.totient : ℕ) : ℝ)⁻¹ * primSup d X) * (((h.totient : ℕ) : ℝ)⁻¹) := by
          rw [mul_inv]; ring
  calc ∑ d ∈ Finset.Icc 1 Q, ∑ h ∈ Finset.Icc 1 (Q / d),
          (((d * h).totient : ℕ) : ℝ)⁻¹ * primSup d X
      ≤ ∑ d ∈ Finset.Icc 1 Q, ∑ h ∈ Finset.Icc 1 (Q / d),
          (((d.totient : ℕ) : ℝ)⁻¹ * primSup d X) * (((h.totient : ℕ) : ℝ)⁻¹) :=
        Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun h hh => hstep d hd h hh))
    _ = ∑ d ∈ Finset.Icc 1 Q,
          (((d.totient : ℕ) : ℝ)⁻¹ * primSup d X)
            * ∑ h ∈ Finset.Icc 1 (Q / d), (((h.totient : ℕ) : ℝ)⁻¹) := by
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.mul_sum]
    _ ≤ ∑ d ∈ Finset.Icc 1 Q,
          (((d.totient : ℕ) : ℝ)⁻¹ * primSup d X)
            * ∑ h ∈ Finset.Icc 1 Q, (((h.totient : ℕ) : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro d hd
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (inv_nonneg.mpr (by positivity)) (primSup_nonneg d X))
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro h hh
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hh).1, le_trans (Finset.mem_Icc.mp hh).2 (Nat.div_le_self Q d)⟩
        · intro h _ _
          exact inv_nonneg.mpr (by positivity)
    _ = (∑ h ∈ Finset.Icc 1 Q, (((h.totient : ℕ) : ℝ)⁻¹))
          * ∑ d ∈ Finset.Icc 1 Q, (((d.totient : ℕ) : ℝ)⁻¹ * primSup d X) := by
        rw [← Finset.sum_mul, mul_comm]

/-- The sum of the coprimality errors. -/
private lemma chiBad_sum_le (Q X : ℕ) (hQ : 1 ≤ Q) :
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

/-- The totient sum bound with the stated normalisation. -/
private lemma totient_sum_le (C1 : ℝ) (hC1pos : 0 < C1)
    (hC1 : ∀ Q : ℕ, 2 ≤ Q →
      (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹) ≤ C1 * (Real.log (Q : ℝ)) ^ 2)
    (Q : ℕ) (hQ : 1 ≤ Q) :
    (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹)
      ≤ max (max C1 1) (2 * (1 / Real.log 2)) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 := by
  have hC1le : C1 ≤ max (max C1 1) (2 * (1 / Real.log 2)) :=
    le_trans (le_max_left C1 1) (le_max_left _ _)
  have h1le : (1 : ℝ) ≤ max (max C1 1) (2 * (1 / Real.log 2)) :=
    le_trans (le_max_right C1 1) (le_max_left _ _)
  have hlog4 : (1 : ℝ) ≤ Real.log (2 * ((1 : ℕ) : ℝ) + 2) := by
    have h4 : (4 : ℝ) ≤ 2 * ((1 : ℕ) : ℝ) + 2 := by norm_num
    calc (1 : ℝ) ≤ Real.log 4 := by
          rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 4)]
          have := Real.exp_one_lt_d9
          linarith
      _ ≤ Real.log (2 * ((1 : ℕ) : ℝ) + 2) := Real.log_le_log (by norm_num) h4
  rcases eq_or_lt_of_le hQ with h | h
  · subst h
    rw [Finset.Icc_self, Finset.sum_singleton, Nat.totient_one]
    have hone : (((1 : ℕ) : ℝ))⁻¹ = (1 : ℝ) := by norm_num
    rw [hone]
    have hsq : (1 : ℝ) ≤ (Real.log (2 * ((1 : ℕ) : ℝ) + 2)) ^ 2 := by nlinarith [hlog4]
    have honele : (1 : ℝ) ≤
        max (max C1 1) (2 * (1 / Real.log 2)) * (Real.log (2 * ((1 : ℕ) : ℝ) + 2)) ^ 2 := by
      have hC0 : (0 : ℝ) ≤ max (max C1 1) (2 * (1 / Real.log 2)) :=
        le_trans (by norm_num) h1le
      have h := mul_le_mul h1le hsq (by norm_num : (0 : ℝ) ≤ 1) hC0
      simpa using h
    simpa using honele
  · have hS := hC1 Q h
    have hlogQnn : 0 ≤ Real.log (Q : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Q))
    have hlogle : Real.log (Q : ℝ) ≤ Real.log (2 * (Q : ℝ) + 2) := by
      apply Real.log_le_log
      · exact_mod_cast (by omega : 0 < Q)
      · have hQnn : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
        linarith
    calc (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹)
        ≤ C1 * (Real.log (Q : ℝ)) ^ 2 := hS
      _ ≤ C1 * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hC1pos)
          exact pow_le_pow_left₀ hlogQnn hlogle 2
      _ ≤ max (max C1 1) (2 * (1 / Real.log 2)) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 :=
          mul_le_mul_of_nonneg_right hC1le (by positivity)

theorem sum_charSup_le_log_mul_primitive :
    ∃ C : ℝ, 0 < C ∧ ∀ X Q : ℕ, 1 ≤ Q →
      (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            sSup ((fun y : ℕ => ‖∑ n ∈ Finset.range (y + 1),
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)
                  - (if χ = 1 then (y : ℂ) else 0)‖) '' Set.Icc 1 X))
      ≤ C * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 *
          (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
              sSup ((fun y : ℕ => ‖∑ n ∈ Finset.range (y + 1),
                  ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)
                    - (if χ = 1 then (y : ℂ) else 0)‖) '' Set.Icc 1 X))
        + C * (Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 * Real.log ((X : ℝ) + 2) := by
  obtain ⟨C1, hC1pos, hC1⟩ :=
    Commons.NumberTheory.Totient.sum_inv_totient_Icc_le_powLog
  refine ⟨max (max C1 1) (2 * (1 / Real.log 2)), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_trans (le_max_right C1 1) (le_max_left _ _))
  · intro X Q hQ
    have hLHS : (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            sSup ((fun y : ℕ => ‖∑ n ∈ Finset.range (y + 1),
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)
                  - (if χ = 1 then (y : ℂ) else 0)‖) '' Set.Icc 1 X))
        = ∑ q ∈ Finset.Icc 1 Q,
            ((q.totient : ℕ) : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, chiSup q χ X := by
      apply Finset.sum_congr rfl
      intro q _
      congr 1
    have hRHS : (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
            sSup ((fun y : ℕ => ‖∑ n ∈ Finset.range (y + 1),
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)
                  - (if χ = 1 then (y : ℂ) else 0)‖) '' Set.Icc 1 X))
        = ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ * primSup q X := by
      apply Finset.sum_congr rfl
      intro q _
      congr 1
    rw [hLHS, hRHS]
    have hstep : ∀ q ∈ Finset.Icc 1 Q,
        ((q.totient : ℕ) : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, chiSup q χ X
          ≤ ((q.totient : ℕ) : ℝ)⁻¹ * ∑ c ∈ q.divisors, primSup c X + 2 * chiBad q X := by
      intro q hq
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      have hqne : NeZero q := ⟨by omega⟩
      have hφ : (((q.totient : ℕ) : ℝ)) ≠ 0 := by
        have : 0 < q.totient := Nat.totient_pos.mpr (by omega)
        exact_mod_cast ne_of_gt this
      have h := chiSup_sum_le q X
      calc ((q.totient : ℕ) : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, chiSup q χ X
          ≤ ((q.totient : ℕ) : ℝ)⁻¹ *
              ((∑ c ∈ q.divisors, primSup c X) + (q.totient : ℝ) * (2 * chiBad q X)) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = ((q.totient : ℕ) : ℝ)⁻¹ * ∑ c ∈ q.divisors, primSup c X + 2 * chiBad q X := by
            rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hφ, one_mul]
    calc (∑ q ∈ Finset.Icc 1 Q,
            ((q.totient : ℕ) : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, chiSup q χ X)
        ≤ ∑ q ∈ Finset.Icc 1 Q,
            (((q.totient : ℕ) : ℝ)⁻¹ * ∑ c ∈ q.divisors, primSup c X + 2 * chiBad q X) :=
          Finset.sum_le_sum hstep
      _ = (∑ q ∈ Finset.Icc 1 Q,
            ((q.totient : ℕ) : ℝ)⁻¹ * ∑ c ∈ q.divisors, primSup c X)
            + ∑ q ∈ Finset.Icc 1 Q, 2 * chiBad q X := Finset.sum_add_distrib
      _ ≤ (∑ m ∈ Finset.Icc 1 Q, ((m.totient : ℕ) : ℝ)⁻¹)
            * (∑ c ∈ Finset.Icc 1 Q, ((c.totient : ℕ) : ℝ)⁻¹ * primSup c X)
            + 2 * ∑ q ∈ Finset.Icc 1 Q, chiBad q X := by
          apply add_le_add (swap_le Q X hQ)
          rw [Finset.mul_sum]
      _ ≤ max (max C1 1) (2 * (1 / Real.log 2)) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2
            * (∑ c ∈ Finset.Icc 1 Q, ((c.totient : ℕ) : ℝ)⁻¹ * primSup c X)
            + 2 * ((1 / Real.log 2) * (Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2
                * Real.log ((X : ℝ) + 2)) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right (totient_sum_le C1 hC1pos hC1 Q hQ) (by
              apply Finset.sum_nonneg
              intro c _
              exact mul_nonneg (by positivity) (primSup_nonneg c X))
          · exact mul_le_mul_of_nonneg_left (chiBad_sum_le Q X hQ) (by norm_num)
      _ ≤ max (max C1 1) (2 * (1 / Real.log 2)) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2
            * (∑ c ∈ Finset.Icc 1 Q, ((c.totient : ℕ) : ℝ)⁻¹ * primSup c X)
            + max (max C1 1) (2 * (1 / Real.log 2)) * (Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2
                * Real.log ((X : ℝ) + 2) := by
          have hlogX : 0 ≤ Real.log ((X : ℝ) + 2) := by
            apply Real.log_nonneg
            have hXnn : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
            linarith
          have hlogQ : 0 ≤ Real.log (2 * (Q : ℝ) + 2) := by
            apply Real.log_nonneg
            have hQnn' : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
            linarith
          have hQnn : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
          have hp : 2 * (1 / Real.log 2) ≤ max (max C1 1) (2 * (1 / Real.log 2)) :=
            le_max_right _ _
          have hnonneg : 0 ≤ (Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 * Real.log ((X : ℝ) + 2) :=
            mul_nonneg (mul_nonneg hQnn (sq_nonneg _)) hlogX
          have htail : 2 * ((1 / Real.log 2) * (Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2
                * Real.log ((X : ℝ) + 2))
              ≤ max (max C1 1) (2 * (1 / Real.log 2)) * (Q : ℝ)
                  * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 * Real.log ((X : ℝ) + 2) := by
            calc 2 * ((1 / Real.log 2) * (Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2
                  * Real.log ((X : ℝ) + 2))
                = (2 * (1 / Real.log 2))
                    * ((Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 * Real.log ((X : ℝ) + 2)) := by ring
              _ ≤ max (max C1 1) (2 * (1 / Real.log 2))
                    * ((Q : ℝ) * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 * Real.log ((X : ℝ) + 2)) :=
                  mul_le_mul_of_nonneg_right hp hnonneg
              _ = max (max C1 1) (2 * (1 / Real.log 2)) * (Q : ℝ)
                    * (Real.log (2 * (Q : ℝ) + 2)) ^ 2 * Real.log ((X : ℝ) + 2) := by ring
          linarith [htail]

