import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.CorrectionDefs
import Submission.Work.NumberTheory.Chen.BTermCount.Bounds
import Submission.Commons.NumberTheory.DirichletCharacter.changeLevel_stable_nat
import Submission.Commons.NumberTheory.DirichletCharacter.sum_characters_eq_sum_primitive_lifts

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

open Commons.NumberTheory.Chen.ChenEight

attribute [local instance] Classical.propDecidable

/-!
# The corrected remainder as a character sum

This module rewrites the corrected remainder

  `bRemCorr x M Y d = #{n ∈ B̄ : d ∣ n - 2} - #{n ∈ B̄ : (n,d) = 1} / φ(d)`

of the ternary sieve sequence `B̄ = bProdSet x M Y` as a sum over the Dirichlet characters
modulo `d`:

  `φ(d) * bRemCorr x M Y d = Σ_{χ ≠ 1} χ(2)⁻¹ * Σ_{n ∈ B̄} χ(n)`   (`d` odd),

together with the resulting norm bound and the behaviour of the twisted sums under a change of
level (the conductor decomposition).
-/

/-- The twisted character sum of the ternary sequence `B̄ = bProdSet x M Y`. -/
noncomputable def bProdCharSum (x M Y c : ℕ) (ψ : DirichletCharacter ℂ c) : ℂ :=
  ∑ n ∈ bProdSet x M Y, ψ ((n : ℕ) : ZMod c)

/-- Twisted character sums are bounded by the size of `B̄`. -/
theorem bProdCharSum_norm_le (x M Y c : ℕ) (ψ : DirichletCharacter ℂ c) :
    ‖bProdCharSum x M Y c ψ‖ ≤ ((bProdSet x M Y).card : ℝ) := by
  unfold bProdCharSum
  refine le_trans (norm_sum_le _ _) ?_
  have h : (∑ n ∈ bProdSet x M Y, ‖ψ ((n:ℕ) : ZMod c)‖) ≤ ∑ n ∈ bProdSet x M Y, (1:ℝ) :=
    Finset.sum_le_sum (fun n _ => DirichletCharacter.norm_le_one ψ ((n:ℕ) : ZMod c))
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact h

/-- If `n ∈ B̄` then `n ≠ 0`. -/
theorem bProdSet_pos {x M Y n : ℕ} (hn : n ∈ bProdSet x M Y) : 0 < n := by
  have h := bProdSet_subset_Icc x M Y hn
  simp only [Finset.mem_Icc] at h
  omega

/-- `a` is not coprime to `d` iff some prime divisor of `d` divides `a`. -/
theorem not_coprime_iff_exists_prime_dvd (a d : ℕ) :
    ¬ Nat.Coprime a d ↔ ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ p ∣ a := by
  constructor
  · intro h
    rw [Nat.coprime_iff_isRelPrime] at h
    simp only [IsRelPrime] at h
    push_neg at h
    obtain ⟨k, hka, hkd, hk⟩ := h
    have hk1 : k ≠ 1 := by intro hk1; exact hk (hk1 ▸ isUnit_one)
    obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd hk1
    exact ⟨p, hp, hpk.trans hkd, hpk.trans hka⟩
  · rintro ⟨p, hp, hpd, hpa⟩ hcop
    have hrel : IsRelPrime a d := Nat.coprime_iff_isRelPrime.mp hcop
    have hunit : IsUnit p := hrel hpa hpd
    have hp1 : p = 1 := Nat.dvd_one.mp (isUnit_iff_dvd_one.mp hunit)
    exact hp.ne_one hp1

/-- `#B̄ - bShared x M Y d` is the number of elements of `B̄` coprime to `d`. -/
theorem card_sub_bShared (x M Y d : ℕ) :
    ((bProdSet x M Y).card : ℝ) - (bShared x M Y d : ℝ)
      = (((bProdSet x M Y).filter (fun n => Nat.Coprime n d)).card : ℝ) := by
  have hset : (bProdSet x M Y).filter (fun n => ¬ Nat.Coprime n d)
      = (bProdSet x M Y).filter (fun n => ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ p ∣ n) := by
    apply Finset.filter_congr
    intro n hn
    exact not_coprime_iff_exists_prime_dvd n d
  have hcard := Finset.card_filter_add_card_filter_not (s := bProdSet x M Y)
    (p := fun n => Nat.Coprime n d)
  rw [hset] at hcard
  unfold bShared
  have h4 : ((#(bProdSet x M Y) : ℕ) : ℝ)
      = (#((bProdSet x M Y).filter fun n => Nat.Coprime n d) : ℝ)
        + (#((bProdSet x M Y).filter fun n => ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ p ∣ n) : ℝ) := by
    rw [← hcard]; push_cast; ring
  linarith [h4]

theorem cast_eq_iff_dvd_sub (d n : ℕ) (hn : 2 ≤ n) :
    (((2 : ℕ) : ZMod d) = ((n : ℕ) : ZMod d)) ↔ d ∣ n - 2 := by
  rw [ZMod.natCast_eq_natCast_iff, Nat.modEq_iff_dvd]
  constructor
  · intro h
    have h2 : (((n - 2 : ℕ)) : ℤ) = (n : ℤ) - ((2 : ℕ) : ℤ) := Nat.cast_sub hn
    rw [← h2] at h
    exact_mod_cast h
  · intro h
    have h' : (d : ℤ) ∣ (((n - 2 : ℕ)) : ℤ) := by exact_mod_cast h
    rw [Nat.cast_sub hn] at h'
    exact h'

theorem tot_mul_bRemCorr_eq_sum_char (x M Y d : ℕ) [NeZero d] (hd : d % 2 = 1) :
    ((Nat.totient d : ℝ) * bRemCorr x M Y d : ℂ)
      = ∑ χ : DirichletCharacter ℂ d, if χ = 1 then 0 else
          χ (((2 : ℕ)) : ZMod d)⁻¹ * bProdCharSum x M Y d χ := by
  have hunit2 : IsUnit (((2 : ℕ)) : ZMod d) := by
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hd)
  have hfull : (∑ χ : DirichletCharacter ℂ d,
        χ (((2 : ℕ)) : ZMod d)⁻¹ * bProdCharSum x M Y d χ)
      = ((Nat.totient d : ℝ) * (((bProdSet x M Y).filter (fun n => d ∣ n - 2)).card : ℝ) : ℂ) := by
    have hstep : (∑ χ : DirichletCharacter ℂ d,
          χ (((2 : ℕ)) : ZMod d)⁻¹ * bProdCharSum x M Y d χ)
        = ∑ n ∈ bProdSet x M Y, ∑ χ : DirichletCharacter ℂ d,
            χ (((2 : ℕ)) : ZMod d)⁻¹ * χ ((n : ℕ) : ZMod d) := by
      simp only [bProdCharSum, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hstep]
    have hstep2 : ∀ n ∈ bProdSet x M Y,
        (∑ χ : DirichletCharacter ℂ d, χ (((2 : ℕ)) : ZMod d)⁻¹ * χ ((n : ℕ) : ZMod d))
          = if (((2 : ℕ)) : ZMod d) = ((n : ℕ) : ZMod d) then ((Nat.totient d : ℕ) : ℂ) else 0 :=
      fun n _ => DirichletCharacter.sum_char_inv_mul_char_eq ℂ hunit2 _
    rw [Finset.sum_congr rfl hstep2]
    have hset : (bProdSet x M Y).filter (fun n => ((2 : ℕ) : ZMod d) = ((n : ℕ) : ZMod d))
        = (bProdSet x M Y).filter (fun n => d ∣ n - 2) := by
      apply Finset.filter_congr
      intro n hn
      have hn2 : 2 ≤ n := by
        have h := bProdSet_subset_Icc x M Y hn
        simp only [Finset.mem_Icc] at h
        exact h.1
      exact cast_eq_iff_dvd_sub d n hn2
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hset]
    push_cast
    ring
  have hone : (∑ n ∈ bProdSet x M Y, (1 : DirichletCharacter ℂ d) ((n : ℕ) : ZMod d))
      = (((bProdSet x M Y).filter (fun n => Nat.Coprime n d)).card : ℂ) := by
    have hcfg : ∀ n ∈ bProdSet x M Y, (1 : DirichletCharacter ℂ d) ((n : ℕ) : ZMod d)
        = if IsUnit ((n : ℕ) : ZMod d) then (1 : ℂ) else 0 := by
      intro n _
      by_cases h : IsUnit ((n : ℕ) : ZMod d)
      · rw [if_pos h, MulChar.one_apply h]
      · rw [if_neg h, MulChar.map_nonunit _ h]
    have hfilter : (bProdSet x M Y).filter (fun n => IsUnit ((n : ℕ) : ZMod d))
        = (bProdSet x M Y).filter (fun n => Nat.Coprime n d) := by
      apply Finset.filter_congr
      intro n _
      exact ZMod.isUnit_iff_coprime n d
    rw [Finset.sum_congr rfl hcfg, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
      hfilter]
  have hsplit : (∑ χ : DirichletCharacter ℂ d, if χ = 1 then (0:ℂ) else
        χ (((2 : ℕ)) : ZMod d)⁻¹ * bProdCharSum x M Y d χ)
      = (∑ χ : DirichletCharacter ℂ d, χ (((2 : ℕ)) : ZMod d)⁻¹ * bProdCharSum x M Y d χ)
        - ((1 : DirichletCharacter ℂ d) (((2 : ℕ)) : ZMod d)⁻¹ * bProdCharSum x M Y d 1) := by
    have h1 : (∑ χ : DirichletCharacter ℂ d, if χ = 1 then (0:ℂ) else
          χ (((2 : ℕ)) : ZMod d)⁻¹ * bProdCharSum x M Y d χ)
        = ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ ≠ 1),
            χ (((2 : ℕ)) : ZMod d)⁻¹ * bProdCharSum x M Y d χ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro χ _
      by_cases h : χ = 1 <;> simp [h]
    have h2 : (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ ≠ 1),
            χ (((2 : ℕ)) : ZMod d)⁻¹ * bProdCharSum x M Y d χ)
          + ((1 : DirichletCharacter ℂ d) (((2 : ℕ)) : ZMod d)⁻¹ * bProdCharSum x M Y d 1)
        = ∑ χ : DirichletCharacter ℂ d, χ (((2 : ℕ)) : ZMod d)⁻¹ * bProdCharSum x M Y d χ := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (DirichletCharacter ℂ d)))
        (p := fun χ => χ ≠ 1) (f := fun χ => χ (((2 : ℕ)) : ZMod d)⁻¹ * bProdCharSum x M Y d χ)]
      have hsingle : (Finset.univ.filter (fun χ : DirichletCharacter ℂ d => ¬ χ ≠ 1)) = {1} := by
        ext χ; simp
      rw [hsingle, Finset.sum_singleton]
    rw [h1, eq_sub_iff_add_eq]
    exact h2
  have hf1 : (1 : DirichletCharacter ℂ d) (((2 : ℕ)) : ZMod d)⁻¹ * bProdCharSum x M Y d 1
      = (((bProdSet x M Y).filter (fun n => Nat.Coprime n d)).card : ℂ) := by
    have hcop : Nat.Coprime 2 d := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hd)
    have hunit_inv : IsUnit (((2 : ℕ) : ZMod d)⁻¹) := by
      refine isUnit_iff_exists_inv.mpr ⟨((2 : ℕ) : ZMod d), ?_⟩
      rw [mul_comm]
      exact ZMod.coe_mul_inv_eq_one 2 hcop
    have h2 : (1 : DirichletCharacter ℂ d) ((((2 : ℕ)) : ZMod d)⁻¹) = 1 :=
      MulChar.one_apply hunit_inv
    rw [h2, one_mul]
    exact hone
  rw [hsplit, hf1, hfull]
  have hcard := card_sub_bShared x M Y d
  have hreal : bRemCorr x M Y d
      = (((bProdSet x M Y).filter (fun n => d ∣ n - 2)).card : ℝ)
        - (((bProdSet x M Y).filter (fun n => Nat.Coprime n d)).card : ℝ) / (Nat.totient d : ℝ) := by
    rw [bRemCorr, ← hcard]
  rw [hreal]
  have hphi : (Nat.totient d : ℂ) ≠ 0 := by
    have h := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
    exact_mod_cast h.ne'
  push_cast
  rw [mul_sub, mul_div_assoc', mul_div_cancel_left₀ _ hphi]

theorem bProdCharSum_changeLevel_sub_le (x M Y c d : ℕ) [NeZero c] [NeZero d] (h : c ∣ d)
    (ψ : DirichletCharacter ℂ c) :
    ‖bProdCharSum x M Y d (DirichletCharacter.changeLevel h ψ) - bProdCharSum x M Y c ψ‖
      ≤ (((bProdSet x M Y).filter (fun n => ¬ Nat.Coprime n d)).card : ℝ) := by
  have hsub : bProdCharSum x M Y d (DirichletCharacter.changeLevel h ψ) - bProdCharSum x M Y c ψ
      = ∑ n ∈ bProdSet x M Y,
          ((DirichletCharacter.changeLevel h ψ) ((n:ℕ) : ZMod d) - ψ ((n:ℕ) : ZMod c)) := by
    simp only [bProdCharSum, ← Finset.sum_sub_distrib]
  rw [hsub]
  refine le_trans (norm_sum_le _ _) ?_
  have hpt : ∀ n ∈ bProdSet x M Y,
      ‖(DirichletCharacter.changeLevel h ψ) ((n:ℕ) : ZMod d) - ψ ((n:ℕ) : ZMod c)‖
        ≤ if ¬ Nat.Coprime n d then (1:ℝ) else 0 := by
    intro n hn
    by_cases hcop : Nat.Coprime n d
    · rw [if_neg (by simp [hcop]),
        Commons.NumberTheory.DirichletCharacter.changeLevel_stable_nat h ψ hcop, sub_self,
        norm_zero]
    · rw [if_pos (by simpa using hcop)]
      have hχ : (DirichletCharacter.changeLevel h ψ) ((n:ℕ) : ZMod d) = 0 :=
        MulChar.map_nonunit _ (fun hu => hcop ((ZMod.isUnit_iff_coprime n d).mp hu))
      rw [hχ, zero_sub, norm_neg]
      exact DirichletCharacter.norm_le_one ψ _
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem sum_ite_eq_filter_ne_one (x M Y d : ℕ) [NeZero d] :
    (∑ χ : DirichletCharacter ℂ d, if χ = 1 then 0 else
        χ (((2:ℕ)) : ZMod d)⁻¹ * bProdCharSum x M Y d χ)
      = ∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ ≠ 1)),
          χ (((2:ℕ)) : ZMod d)⁻¹ * bProdCharSum x M Y d χ := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro χ _
  by_cases h : χ = 1 <;> simp [h]

theorem abs_bRemCorr_le (x M Y d : ℕ) [NeZero d] (hd : d % 2 = 1) :
    |bRemCorr x M Y d| ≤ (Nat.totient d : ℝ)⁻¹ *
      ∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ ≠ 1)),
        ‖bProdCharSum x M Y d χ‖ := by
  have h2 : ‖((Nat.totient d : ℝ) * bRemCorr x M Y d : ℂ)‖
      ≤ ∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ ≠ 1)),
          ‖bProdCharSum x M Y d χ‖ := by
    rw [tot_mul_bRemCorr_eq_sum_char x M Y d hd, sum_ite_eq_filter_ne_one x M Y d]
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum (fun χ _ => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
  have hphi_pos : (0:ℝ) < Nat.totient d := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have h3 : ‖((Nat.totient d : ℝ) * bRemCorr x M Y d : ℂ)‖
      = (Nat.totient d : ℝ) * |bRemCorr x M Y d| := by
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos hphi_pos]
  calc |bRemCorr x M Y d|
      = (Nat.totient d : ℝ)⁻¹ * ((Nat.totient d : ℝ) * |bRemCorr x M Y d|) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hphi_pos), one_mul]
    _ ≤ (Nat.totient d : ℝ)⁻¹ *
          (∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ ≠ 1)),
            ‖bProdCharSum x M Y d χ‖) :=
        mul_le_mul_of_nonneg_left (by rw [← h3]; exact h2) (inv_nonneg.mpr hphi_pos.le)

theorem sum_norm_bProdCharSum_eq_lifts (x M Y d : ℕ) [NeZero d] :
    (∑ χ : DirichletCharacter ℂ d, ‖bProdCharSum x M Y d χ‖)
      = ∑ c ∈ d.divisors.attach,
          ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
            ‖bProdCharSum x M Y d
              (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1)‖ := by
  have h := Commons.NumberTheory.DirichletCharacter.sum_characters_eq_sum_primitive_lifts d
    (fun χ : DirichletCharacter ℂ d => ((‖bProdCharSum x M Y d χ‖ : ℝ) : ℂ))
  refine Complex.ofReal_injective ?_
  push_cast
  exact h

end Work.NumberTheory.Chen.BTermCount
