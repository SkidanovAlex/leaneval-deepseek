import Mathlib
import Submission.Work.FIArea2.R6.BSBoxDefs
import Submission.Work.FIArea2.R6.hL_axis_bound
import Submission.Work.FIArea2.R6.bulkPart_le_gsum
import Submission.Work.FIArea2.R6.phi_tau4_div_dsum

/-!
# `FIArea2/R6/hbox6_of_ubox3` — the exponent-generalized box estimate

`R6/hbox6_of_ubox` turns `uboxSum r X Y ≤ CB·r²XY·(1+log(r+X+Y+2))^800` into
`boxSum6 R X Y ≤ C·R²XY·(1+log(R+X+Y+2))^{1000}`.  Here the exponents are freed: the same proof
gives exponent `E'` from exponent `E` whenever `E + 16 ≤ E'` (the `16` coming from
`phi_tau4_div_dsum`).  We use `E = 2^26` (from `R6/ubox_bound3`) and `E' = 2^26 + 200 ≤ 2^27`.

The two ingredients of `R6/hbox6_of_ubox` whose exponents are hard-wired (`R6/uboxSum_div_le` at
`800`) are re-proved here in general form; `R6/hL_axis_bound`'s exponent `1000` only needs
`1000 ≤ E'`.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- `R6/uboxSum_div_le` with a general exponent `E`. -/
theorem uboxSum_div_leE (CB : ℝ) (hCB : 0 < CB) (E : ℕ)
    (hU : ∀ (r X Y : ℕ), 1 ≤ r → 1 ≤ X → 1 ≤ Y →
      Work.FIArea2.R6.uboxSum r X Y ≤ CB * (r : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
        * (1 + Real.log ((r : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ E)
    (R X Y g : ℕ) (hg : g ∈ Finset.Icc 1 R) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    Work.FIArea2.R6.uboxSum (R / g) X Y
      ≤ CB * ((R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
            * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ E)
        * ((g : ℝ) ^ 2)⁻¹ := by
  rw [Finset.mem_Icc] at hg
  obtain ⟨hg1, hgR⟩ := hg
  have hgpos : 0 < g := lt_of_lt_of_le Nat.zero_lt_one hg1
  have hr : 1 ≤ R / g := Nat.succ_le_of_lt (Nat.div_pos hgR hgpos)
  have h1 := hU (R / g) X Y hr hX hY
  have hRg_le : ((R / g : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast Nat.div_le_self R g
  have hgRpos : 0 < (g : ℝ) := by exact_mod_cast hgpos
  have hcast : ((R / g : ℕ) : ℝ) * (g : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self R g
  have hle : ((R / g : ℕ) : ℝ) ≤ (R : ℝ) * (g : ℝ)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hgRpos]; exact hcast
  have hA : ((R / g : ℕ) : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 * ((g : ℝ) ^ 2)⁻¹ := by
    have h2 := pow_le_pow_left₀ (show (0:ℝ) ≤ ((R / g : ℕ) : ℝ) by positivity) hle 2
    rwa [mul_pow, inv_pow] at h2
  have hXr : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hYr : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have ha_pos : 0 < ((R / g : ℕ) : ℝ) + (X : ℝ) + (Y : ℝ) + 2 := by
    have : (0:ℝ) ≤ ((R / g : ℕ) : ℝ) := by positivity
    linarith
  have hab : ((R / g : ℕ) : ℝ) + (X : ℝ) + (Y : ℝ) + 2 ≤ (R : ℝ) + (X : ℝ) + (Y : ℝ) + 2 := by
    linarith [hRg_le]
  have hlog := Real.log_le_log ha_pos hab
  have hbase : 0 ≤ 1 + Real.log (((R / g : ℕ) : ℝ) + (X : ℝ) + (Y : ℝ) + 2) := by
    have : (1:ℝ) ≤ ((R / g : ℕ) : ℝ) + (X : ℝ) + (Y : ℝ) + 2 := by
      have : (0:ℝ) ≤ ((R / g : ℕ) : ℝ) := by positivity
      linarith
    have := Real.log_nonneg this
    linarith
  have hLa : (1 + Real.log (((R / g : ℕ) : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ E
      ≤ (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ E :=
    pow_le_pow_left₀ hbase (by linarith) E
  have hB_nonneg : 0 ≤ (R : ℝ) ^ 2 * ((g : ℝ) ^ 2)⁻¹ :=
    mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (sq_nonneg _))
  have hfund : ((R / g : ℕ) : ℝ) ^ 2
        * (1 + Real.log (((R / g : ℕ) : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ E
      ≤ ((R : ℝ) ^ 2 * ((g : ℝ) ^ 2)⁻¹)
        * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ E :=
    mul_le_mul hA hLa (pow_nonneg hbase E) hB_nonneg
  have hc : 0 ≤ CB * (X : ℝ) * (Y : ℝ) := by positivity
  have key : CB * (X : ℝ) * (Y : ℝ)
        * (((R / g : ℕ) : ℝ) ^ 2
          * (1 + Real.log (((R / g : ℕ) : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ E)
      ≤ CB * (X : ℝ) * (Y : ℝ)
        * (((R : ℝ) ^ 2 * ((g : ℝ) ^ 2)⁻¹)
          * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ E) :=
    mul_le_mul_of_nonneg_left hfund hc
  calc Work.FIArea2.R6.uboxSum (R / g) X Y
      ≤ CB * ((R / g : ℕ) : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
          * (1 + Real.log (((R / g : ℕ) : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ E := h1
    _ = CB * (X : ℝ) * (Y : ℝ)
          * (((R / g : ℕ) : ℝ) ^ 2
            * (1 + Real.log (((R / g : ℕ) : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ E) := by ac_rfl
    _ ≤ CB * (X : ℝ) * (Y : ℝ)
          * (((R : ℝ) ^ 2 * ((g : ℝ) ^ 2)⁻¹)
            * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ E) := key
    _ = CB * ((R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
            * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ E)
        * ((g : ℝ) ^ 2)⁻¹ := by ac_rfl

/-- `boxSum6` splits into its axis part (at least one coordinate zero) and its bulk part. -/
private theorem hbox6ou_split3 (R X Y : ℕ) : boxSum6 R X Y = axisPart R X Y + bulkPart R X Y := by
  unfold boxSum6 axisPart bulkPart
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro u1 _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro u2 _
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro h1 _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro h2 _
  by_cases hp : u1 = 0 ∨ u2 = 0 ∨ h1 = 0 ∨ h2 = 0
  · rw [if_pos hp]
    have hc : ¬ (u1 ≠ 0 ∧ u2 ≠ 0 ∧ h1 ≠ 0 ∧ h2 ≠ 0) := by
      rintro ⟨a, b, c, d⟩
      rcases hp with e | e | e | e <;> simp_all
    rw [if_neg hc]; simp
  · rw [if_neg hp]
    have hc : u1 ≠ 0 ∧ u2 ≠ 0 ∧ h1 ≠ 0 ∧ h2 ≠ 0 :=
      ⟨fun h => hp (Or.inl h), fun h => hp (Or.inr (Or.inl h)),
       fun h => hp (Or.inr (Or.inr (Or.inl h))), fun h => hp (Or.inr (Or.inr (Or.inr h)))⟩
    rw [if_pos hc]; simp

/-- The bulk part at general exponents `E + 16 ≤ E'`. -/
private theorem hbox6ou_bulk3 (CB CP : ℝ) (hCB : 0 < CB) (hCP : 0 < CP)
    (E E' : ℕ) (hE : E + 16 ≤ E')
    (hU : ∀ (r X Y : ℕ), 1 ≤ r → 1 ≤ X → 1 ≤ Y →
      uboxSum r X Y ≤ CB * (r : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
        * (1 + Real.log ((r : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ E)
    (hP : ∀ R : ℕ, (∑ g ∈ Finset.Icc 1 R,
        (Nat.totient g : ℝ) * ((g.divisors.card : ℝ)) ^ 4 / (g : ℝ) ^ 2)
        ≤ CP * (Real.log ((R : ℝ) + 2) + 2) ^ 16)
    (R X Y : ℕ) (hR : 1 ≤ R) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    bulkPart R X Y ≤ CB * CP * 2 ^ 16 * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
      * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ E' := by
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have harg1 : (1 : ℝ) ≤ (R : ℝ) + (X : ℝ) + (Y : ℝ) + 2 := by linarith
  have hL0 : (0 : ℝ) ≤ 1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2) := by
    have := Real.log_nonneg harg1; linarith
  have hL1 : (1 : ℝ) ≤ 1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2) := by
    have := Real.log_nonneg harg1; linarith
  have hW0 : (0 : ℝ) ≤ (R : ℝ)^2 * (X : ℝ) * (Y : ℝ)
      * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2))^E := by
    have hp : (0 : ℝ) ≤ (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2))^E :=
      pow_nonneg hL0 E
    have hR2 : (0 : ℝ) ≤ (R : ℝ)^2 := sq_nonneg _
    have hX0 : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
    have hY0 : (0 : ℝ) ≤ (Y : ℝ) := Nat.cast_nonneg Y
    exact mul_nonneg (mul_nonneg (mul_nonneg hR2 hX0) hY0) hp
  have hterm : ∀ g ∈ Finset.Icc 1 R,
      (Nat.totient g : ℝ) * ((g.divisors.card : ℝ)) ^ 4 * uboxSum (R / g) X Y
      ≤ ((Nat.totient g : ℝ) * ((g.divisors.card : ℝ)) ^ 4 / (g : ℝ) ^ 2)
        * (CB * ((R : ℝ)^2 * (X : ℝ) * (Y : ℝ)
            * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2))^E)) := by
    intro g hg
    have hp := uboxSum_div_leE CB hCB E hU R X Y g hg hX hY
    have hn : (0 : ℝ) ≤ (Nat.totient g : ℝ) * ((g.divisors.card : ℝ))^4 := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left hp hn) (le_of_eq ?_)
    rw [div_eq_mul_inv]
    ac_rfl
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul] at hsum
  have hP16 : CP * (Real.log ((R : ℝ) + 2) + 2)^16
      ≤ CP * (2 * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)))^16 := by
    apply mul_le_mul_of_nonneg_left _ hCP.le
    apply pow_le_pow_left₀ _ _ 16
    · have h0 : (0 : ℝ) ≤ Real.log ((R : ℝ) + 2) := Real.log_nonneg (by linarith)
      linarith
    · have hlog : Real.log ((R : ℝ) + 2) ≤ Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2) := by
        apply Real.log_le_log (by linarith)
        linarith
      linarith
  have hstep : (∑ g ∈ Finset.Icc 1 R,
          (Nat.totient g : ℝ) * ((g.divisors.card : ℝ))^4 / (g : ℝ)^2)
        * (CB * ((R : ℝ)^2 * (X : ℝ) * (Y : ℝ)
            * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2))^E))
      ≤ (CP * (2 * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)))^16)
        * (CB * ((R : ℝ)^2 * (X : ℝ) * (Y : ℝ)
            * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2))^E)) :=
    mul_le_mul_of_nonneg_right (le_trans (hP R) hP16) (mul_nonneg hCB.le hW0)
  have hfinal : (CP * (2 * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)))^16)
        * (CB * ((R : ℝ)^2 * (X : ℝ) * (Y : ℝ)
            * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2))^E))
      ≤ CB * CP * 2 ^ 16 * (R : ℝ)^2 * (X : ℝ) * (Y : ℝ)
          * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ E' := by
    set L : ℝ := 1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2) with hLdef
    have hL1' : (1 : ℝ) ≤ L := by rw [hLdef]; exact hL1
    have hpw : (2 * L)^16 = 2 ^ 16 * L^16 := by rw [mul_pow]
    have h816 : L^16 * L^E ≤ L^E' := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hL1' (by omega)
    calc (CP * (2 * L)^16) * (CB * ((R : ℝ)^2 * (X : ℝ) * (Y : ℝ) * L^E))
        = CB * CP * 2 ^ 16 * ((R : ℝ)^2 * (X : ℝ) * (Y : ℝ) * (L^16 * L^E)) := by
          rw [hpw]; ac_rfl
      _ ≤ CB * CP * 2 ^ 16 * ((R : ℝ)^2 * (X : ℝ) * (Y : ℝ) * L^E') := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left h816 (by positivity)
      _ = CB * CP * 2 ^ 16 * (R : ℝ)^2 * (X : ℝ) * (Y : ℝ) * L^E' := by ac_rfl
  exact le_trans (bulkPart_le_gsum R X Y) (le_trans hsum (le_trans hstep hfinal))

/-- **The box estimate at exponent `2^26 + 200` from the unweighted box estimate at `2^26`.** -/
theorem hbox6_of_ubox3
    (hU : ∃ CB : ℝ, 0 < CB ∧ ∀ (r X Y : ℕ), 1 ≤ r → 1 ≤ X → 1 ≤ Y →
      Work.FIArea2.R6.uboxSum r X Y ≤ CB * (r : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
        * (1 + Real.log ((r : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ ((2 : ℕ) ^ (26 : ℕ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R X Y : ℕ), 1 ≤ R → 1 ≤ X → 1 ≤ Y →
      Work.FIArea2.R6.boxSum6 R X Y
        ≤ C * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
          * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2))
              ^ ((2 : ℕ) ^ (26 : ℕ) + 200) := by
  obtain ⟨CB, hCBpos, hU'⟩ := hU
  obtain ⟨Ca, hCapos, ha⟩ := hL_axis_bound
  obtain ⟨CP, hCPpos, hP⟩ := phi_tau4_div_dsum
  refine ⟨Ca + CB * CP * 2 ^ 16, by positivity, ?_⟩
  intro R X Y hR hX hY
  have harg1 : (1 : ℝ) ≤ (R : ℝ) + (X : ℝ) + (Y : ℝ) + 2 := by
    have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    linarith
  have hL1 : (1 : ℝ) ≤ 1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2) := by
    have := Real.log_nonneg harg1; linarith
  have haxis : axisPart R X Y ≤ Ca * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
      * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ ((2 : ℕ) ^ (26 : ℕ) + 200) := by
    have h := ha R X Y hR hX hY
    have h0 : (∑ u1 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), ∑ u2 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
        (Nat.gcd u1.natAbs u2.natAbs : ℝ) *
          (∑ h1 ∈ Finset.Icc (-(X : ℤ)) (X : ℤ), ∑ h2 ∈ Finset.Icc (-(Y : ℤ)) (Y : ℤ),
            (if u1 = 0 ∨ u2 = 0 ∨ h1 = 0 ∨ h2 = 0
              then (((u1 * h1 ^ 2 - u2 * h2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)
              else 0)))
        ≤ Ca * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
          * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 1000 := h
    have hpow : (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 1000
        ≤ (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ ((2 : ℕ) ^ (26 : ℕ) + 200) :=
      pow_le_pow_right₀ hL1 (by norm_num)
    have h2 : Ca * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
          * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ 1000
        ≤ Ca * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
          * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ ((2 : ℕ) ^ (26 : ℕ) + 200) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    have h3 : axisPart R X Y
        = (∑ u1 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), ∑ u2 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
            (Nat.gcd u1.natAbs u2.natAbs : ℝ) *
              (∑ h1 ∈ Finset.Icc (-(X : ℤ)) (X : ℤ), ∑ h2 ∈ Finset.Icc (-(Y : ℤ)) (Y : ℤ),
                (if u1 = 0 ∨ u2 = 0 ∨ h1 = 0 ∨ h2 = 0
                  then (((u1 * h1 ^ 2 - u2 * h2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)
                  else 0))) := rfl
    rw [h3]
    exact le_trans h0 h2
  have hbulk : bulkPart R X Y ≤ CB * CP * 2 ^ 16 * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
      * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ ((2 : ℕ) ^ (26 : ℕ) + 200) :=
    hbox6ou_bulk3 CB CP hCBpos hCPpos ((2 : ℕ) ^ (26 : ℕ)) ((2 : ℕ) ^ (26 : ℕ) + 200)
      (by norm_num) hU' hP R X Y hR hX hY
  rw [hbox6ou_split3 R X Y]
  refine le_trans (add_le_add haxis hbulk) (le_of_eq ?_)
  have e1 : Ca * ((R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
        * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ ((2 : ℕ) ^ (26 : ℕ) + 200))
      = Ca * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
        * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ ((2 : ℕ) ^ (26 : ℕ) + 200) := by
    ac_rfl
  have e2 : (CB * CP * 2 ^ 16) * ((R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
        * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ ((2 : ℕ) ^ (26 : ℕ) + 200))
      = CB * CP * 2 ^ 16 * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
        * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ ((2 : ℕ) ^ (26 : ℕ) + 200) := by
    ac_rfl
  have e3 : (Ca + CB * CP * 2 ^ 16) * ((R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
        * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ ((2 : ℕ) ^ (26 : ℕ) + 200))
      = (Ca + CB * CP * 2 ^ 16) * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
        * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ ((2 : ℕ) ^ (26 : ℕ) + 200) := by
    ac_rfl
  rw [← e1, ← e2, ← e3, add_mul]

end

end Work.FIArea2.R6
