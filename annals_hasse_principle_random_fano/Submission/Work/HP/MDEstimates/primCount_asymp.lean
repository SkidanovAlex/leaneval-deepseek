import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDEstimates.ball_count_R0
import Submission.Work.HP.MDEstimates.primCount_moebius_free
import Submission.Work.HP.MDEstimates.zeta_tail_C
import Submission.Work.HP.MDEstimates.sumIccInvSq
import Submission.Work.HP.MDEstimates.sumIccInvLeLog
import Submission.Work.HP.MDEstimates.detL_one_le
import Submission.Work.HP.FM.minkowski_lower
import Submission.Work.HP.MDEstimates.gonCleanOwn

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open Finset

namespace Work.HP.MDEstimates

/-- `ballVol` is a nonnegative real number (local copy; the global lemma lives in `IcVolAux`,
which cannot be imported here because of a duplicate `Work.HP.toE`). -/
private lemma hp_ballVol_nonneg (k : ℕ) : 0 ≤ ballVol k := ENNReal.toReal_nonneg

open Work.HP

/-- An integer vector of Euclidean norm `< 1` is zero. -/
private lemma eNorm_lt_one_eq_zero {ι : Type*} [Fintype ι] {a : ι → ℤ} {r : ℝ}
    (h : eNorm a ≤ r) (hr : r < 1) : a = 0 := by
  by_contra ha
  have h1 : (1 : ℝ) ≤ eNorm a := one_le_eNorm_of_ne_zero ha
  linarith

/-- For `0 ≤ r < 1`, the lattice points of `L` of norm at most `r` are exactly the origin. -/
private lemma ncard_ball_of_lt_one {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℤ)) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) : ({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ r}.ncard) = 1 := by
  have hset : {a : ι → ℤ | a ∈ L ∧ eNorm a ≤ r} = ({0} : Set (ι → ℤ)) := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, ha⟩
      exact eNorm_lt_one_eq_zero ha hr
    · rintro rfl
      exact ⟨L.zero_mem, by simp [eNorm]; linarith⟩
  rw [hset, Set.ncard_singleton]

section Main

open ArithmeticFunction

theorem primCount_asymp (ι : Type) [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (T Y : ℝ), 3 ≤ rk L → 1 ≤ T →
      IsPrimLat L → 0 < detL L → lam L (rk L) ≤ Y → Y ≤ T →
      |(({a : ι → ℤ | a ∈ L ∧ IsPrim a ∧ eNorm a ≤ T}.ncard : ℝ) -
          ballVol (rk L) / (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (rk L)) * T ^ (rk L) / detL L)|
        ≤ K * (T ^ (rk L) / detL L * (Y / T)) + K * T * (1 + Real.log Y) := by
  classical
  obtain ⟨Kg, hKgpos, hKg⟩ := gonCleanOwn (ι := ι)
  obtain ⟨Ks, hKspos, hKs⟩ := sum_le_target (ι := ι)
  have hzeta : ∀ R : ℕ, 1 < (R : ℝ) → ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      |(∑ ℓ ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ R) -
        1 / (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ R)| ≤ C / X ^ ((R : ℝ) - 1) := by
    intro R hR
    obtain ⟨C, hCpos, hC⟩ := zeta_tail_C (R : ℝ) hR
    refine ⟨C, hCpos, fun X hX => ?_⟩
    have h1 : (∑ ℓ ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ (R:ℝ))
        = (∑ ℓ ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ R) := by
      refine Finset.sum_congr rfl (fun ℓ _ => ?_)
      rw [Real.rpow_natCast]
    have h2 : (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (R:ℝ)) = (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ R) := by
      refine tsum_congr (fun k => ?_)
      rw [Real.rpow_natCast]
    rw [← h1, ← h2]
    exact hC X hX
  set B : ℕ → ℝ := (fun R : ℕ => if h : 1 < (R : ℝ) then Classical.choose (hzeta R h) else 1)
    with hBdef
  have hBpos : ∀ R, 0 < B R := by
    intro R
    simp only [hBdef]
    by_cases h : 1 < (R : ℝ)
    · rw [dif_pos h]
      exact (Classical.choose_spec (hzeta R h)).1
    · rw [dif_neg h]
      norm_num
  have hBbound : ∀ (R : ℕ) (hR : 1 < (R : ℝ)) (X : ℝ), 1 ≤ X →
      |(∑ ℓ ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ R) -
        1 / (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ R)| ≤ B R / X ^ ((R : ℝ) - 1) := by
    intro R hR X hX
    have h := (Classical.choose_spec (hzeta R hR)).2 X hX
    simp only [hBdef, dif_pos hR]
    exact h
  let Kf : ℕ → ℝ := fun R =>
    2 * Kg + 4 * Kg * Ks + 2 * ballVol R + ballVol R * B R * (2 : ℝ) ^ (R - 1) + 2
  set KC : ℝ := ∑ R ∈ Finset.range (Fintype.card ι + 1), Kf R with hKC
  refine ⟨KC, ?_, ?_⟩
  · rw [hKC]
    refine Finset.sum_pos (fun R _ => ?_) ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
    have hV : 0 ≤ ballVol R := hp_ballVol_nonneg R
    have hC : 0 < B R := hBpos R
    have h1 : 0 < 2 * Kg := by linarith
    have h2 : 0 ≤ 4 * Kg * Ks := by nlinarith [hKgpos, hKspos]
    have h3 : 0 ≤ 2 * ballVol R := by linarith
    have h4 : 0 ≤ ballVol R * B R * (2 : ℝ) ^ (R - 1) :=
      mul_nonneg (mul_nonneg hV hC.le) (by positivity)
    simp only [Kf]
    linarith
  · intro L T Y hR3 hT1 hprim hdet hlamY hYT
    have hR1 : 1 ≤ rk L := by omega
    have hR2 : 2 ≤ rk L := by omega
    have hT0 : (0:ℝ) ≤ T := by linarith
    have hlam1 : 1 ≤ lam L (rk L) := one_le_lam L (i := rk L) hR1 le_rfl
    have hY1 : 1 ≤ Y := le_trans hlam1 hlamY
    have hY0 : 0 < Y := lt_of_lt_of_le one_pos hY1
    have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hY1
    have hD1 : 1 ≤ detL L := detL_one_le L
    have hD0 : 0 < detL L := hdet
    have hDne : detL L ≠ 0 := ne_of_gt hdet
    have hV0 : 0 ≤ ballVol (rk L) := hp_ballVol_nonneg _
    have hdetle : detL L ≤ ∏ i ∈ Finset.range (rk L), lam L (i + 1) :=
      Work.HP.FM.minkowski_lower L
    have hTne : T ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos hT1)
    set zc : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (rk L) with hzcdef
    set TN : ℕ := ⌊T⌋₊ with hTNdef
    set L0 : ℕ := ⌊T / Y⌋₊ with hL0def
    have hTN1 : 1 ≤ TN := by
      rw [hTNdef, Nat.one_le_floor_iff]; exact hT1
    have hL0TN : L0 ≤ TN := by
      rw [hL0def, hTNdef]
      apply Nat.floor_mono
      rw [div_le_iff₀ hY0]
      nlinarith [hT0, hY1]
    have hL01 : 1 ≤ L0 := by
      rw [hL0def, Nat.one_le_floor_iff]
      exact (one_le_div hY0).mpr hYT
    have hL0le : (L0 : ℝ) ≤ T / Y := by
      rw [hL0def]; exact Nat.floor_le (by positivity)
    -- bounds for the two ranges
    have hTNle : (TN : ℝ) ≤ T := Nat.floor_le hT0
    have hTltTN : T < (TN : ℝ) + 1 := by
      have := Nat.lt_floor_add_one T
      rw [← hTNdef] at this
      exact this
    have hTle2TN : T ≤ 2 * (TN : ℝ) := by
      have h1 : (1:ℝ) ≤ (TN:ℝ) := by exact_mod_cast hTN1
      linarith
    -- The Möbius expansion
    have hNform : (({a : ι → ℤ | a ∈ L ∧ IsPrim a ∧ eNorm a ≤ T}.ncard : ℝ))
        = ∑' l : ℕ, (ArithmeticFunction.moebius l : ℝ) *
            ((ballCount L (T / (l:ℝ)) : ℝ) - 1) := by
      rw [primCount_moebius_free L hprim hT0]
      refine tsum_congr (fun l => ?_)
      have hb : (({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T / (l:ℝ)}.ncard : ℕ) : ℝ)
          = (ballCount L (T / (l:ℝ)) : ℝ) := by rw [ballCount]
      rw [hb]
    have hNsum : (({a : ι → ℤ | a ∈ L ∧ IsPrim a ∧ eNorm a ≤ T}.ncard : ℝ))
        = ∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) *
            ((ballCount L (T / (l:ℝ)) : ℝ) - 1) := by
      rw [hNform]
      refine tsum_eq_sum (s := Finset.Icc 1 TN) (fun l hl => ?_)
      by_cases h0 : l = 0
      · subst h0
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree (fun h => h.ne_zero rfl)]
        simp
      · have hl1 : 1 ≤ l := Nat.one_le_iff_ne_zero.mpr h0
        have hlTN : TN < l := by
          by_contra h
          exact hl (Finset.mem_Icc.mpr ⟨hl1, Nat.le_of_not_lt h⟩)
        have hlpos : (0:ℝ) < (l:ℝ) := by exact_mod_cast hl1
        have hTltl : T < (l:ℝ) := by
          have h1 : (TN:ℝ) + 1 ≤ (l:ℝ) := by
            exact_mod_cast (show TN + 1 ≤ l from hlTN)
          linarith [hTltTN]
        have hlt1 : T / (l:ℝ) < 1 := by rw [div_lt_one hlpos]; exact hTltl
        have hr0 : 0 ≤ T / (l:ℝ) := div_nonneg hT0 hlpos.le
        have hbc : ballCount L (T / (l:ℝ)) = 1 := by
          rw [ballCount]; exact ncard_ball_of_lt_one L hr0 hlt1
        rw [hbc]; ring
    -- split of the index set
    have hTYleT : T / Y ≤ T := by
      rw [div_le_iff₀ hY0]; nlinarith [hT0, hY1]
    have hdisj : Disjoint (Finset.Icc 1 L0) (Finset.Icc (L0 + 1) TN) := by
      rw [Finset.disjoint_left]
      intro l hl1 hl2
      rw [Finset.mem_Icc] at hl1 hl2; omega
    have hunion : Finset.Icc 1 L0 ∪ Finset.Icc (L0 + 1) TN = Finset.Icc 1 TN := by
      ext l; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    have hsplit : ∀ f : ℕ → ℝ, (∑ l ∈ Finset.Icc 1 TN, f l)
        = (∑ l ∈ Finset.Icc 1 L0, f l) + ∑ l ∈ Finset.Icc (L0 + 1) TN, f l := by
      intro f; rw [← hunion, Finset.sum_union hdisj]
    -- === Part A : the main term ===
    have hVol : (∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) *
          (ballVol (rk L) * (T / (l:ℝ)) ^ (rk L) / detL L))
        = ballVol (rk L) * T ^ (rk L) / detL L *
          (∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) / (l:ℝ) ^ (rk L)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l hl => ?_)
      have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
      have hlne : (l:ℝ) ≠ 0 := by positivity
      have hlp : (l:ℝ) ^ (rk L) ≠ 0 := pow_ne_zero _ hlne
      rw [div_pow]
      field_simp
      try ring
    have hZnn : 0 ≤ ballVol (rk L) * T ^ (rk L) / detL L := by positivity
    have hZb : |ballVol (rk L) * T ^ (rk L) / detL L *
          ((∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) / (l:ℝ) ^ (rk L)) - 1/zc)|
        ≤ ballVol (rk L) * T ^ (rk L) / detL L * (B (rk L) / (TN:ℝ) ^ ((rk L:ℝ) - 1)) := by
      rw [abs_mul, abs_of_nonneg hZnn]
      refine mul_le_mul_of_nonneg_left ?_ hZnn
      have h1r : 1 < (rk L : ℝ) := by
        have : 1 < rk L := by omega
        exact_mod_cast this
      have hc := hBbound (rk L) h1r (TN:ℝ) (by exact_mod_cast hTN1)
      rw [Nat.floor_natCast, ← hzcdef] at hc
      exact hc
    have hXeq : (TN:ℝ) ^ ((rk L:ℝ) - 1) = (TN:ℝ) ^ (rk L - 1) := by
      have hexp : (rk L:ℝ) - 1 = ((rk L - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hR1]; norm_num
      rw [hexp, Real.rpow_natCast]
    have hpowle : T ^ (rk L) / (TN:ℝ) ^ ((rk L:ℝ) - 1) ≤ T * (2:ℝ) ^ (rk L - 1) := by
      rw [hXeq]
      have hTNpos : (0:ℝ) < (TN:ℝ) := by exact_mod_cast hTN1
      have hsp2 : T * T ^ (rk L - 1) = T ^ (rk L) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [← hsp2, mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hT0
      rw [← div_pow]
      apply pow_le_pow_left₀ (div_nonneg hT0 hTNpos.le)
      rw [div_le_iff₀ hTNpos]
      exact hTle2TN
    have hterm1 : ballVol (rk L) * T ^ (rk L) / detL L * (B (rk L) / (TN:ℝ) ^ ((rk L:ℝ) - 1))
        ≤ ballVol (rk L) * B (rk L) * T * (2:ℝ) ^ (rk L - 1) := by
      have hXpos : 0 < (TN:ℝ) ^ ((rk L:ℝ) - 1) := by positivity
      have hA0 : 0 ≤ ballVol (rk L) * B (rk L) := mul_nonneg hV0 (hBpos _).le
      calc ballVol (rk L) * T ^ (rk L) / detL L * (B (rk L) / (TN:ℝ) ^ ((rk L:ℝ) - 1))
          = ballVol (rk L) * B (rk L) * (T ^ (rk L) / (detL L * (TN:ℝ) ^ ((rk L:ℝ) - 1))) := by
            ring
        _ ≤ ballVol (rk L) * B (rk L) * (T * (2:ℝ) ^ (rk L - 1)) := by
            apply mul_le_mul_of_nonneg_left _ hA0
            refine le_trans (div_le_div_of_nonneg_left (by positivity) hXpos ?_) hpowle
            nlinarith [hD1, hXpos]
        _ = ballVol (rk L) * B (rk L) * T * (2:ℝ) ^ (rk L - 1) := by ring
    have hsum_mu : |∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ)| ≤ 2*T := by
      calc |∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ)|
          ≤ ∑ l ∈ Finset.Icc 1 TN, |(ArithmeticFunction.moebius l : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _l ∈ Finset.Icc 1 TN, (1:ℝ) := by
            refine Finset.sum_le_sum (fun l _ => ?_)
            have h := ArithmeticFunction.abs_moebius_le_one (n := l)
            exact_mod_cast h
        _ ≤ ∑ _l ∈ Finset.range (TN+1), (1:ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro l hl; rw [Finset.mem_Icc] at hl; rw [Finset.mem_range]; omega
            · intro i _ _; norm_num
        _ = ((TN+1 : ℕ) : ℝ) := by simp
        _ ≤ 2*T := by
            have h1 : ((TN:ℕ):ℝ) ≤ T := hTNle
            push_cast
            linarith
    have hA : |(∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) *
          (ballVol (rk L) * (T / (l:ℝ)) ^ (rk L) / detL L - 1))
        - ballVol (rk L) / zc * T ^ (rk L) / detL L|
        ≤ (ballVol (rk L) * B (rk L) * (2:ℝ)^(rk L - 1) + 2) * (T * (1 + Real.log Y)) := by
      have hexp : (∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) *
            (ballVol (rk L) * (T / (l:ℝ)) ^ (rk L) / detL L - 1))
          = (∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) *
              (ballVol (rk L) * (T / (l:ℝ)) ^ (rk L) / detL L))
            - ∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun l _ => ?_); ring
      have hstep : (∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) *
            (ballVol (rk L) * (T / (l:ℝ)) ^ (rk L) / detL L - 1))
          - ballVol (rk L) / zc * T ^ (rk L) / detL L
          = ballVol (rk L) * T ^ (rk L) / detL L *
              ((∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) / (l:ℝ) ^ (rk L)) - 1/zc)
            - ∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) := by
        rw [hexp, hVol]; ring
      rw [hstep]
      have hsub : |ballVol (rk L) * T ^ (rk L) / detL L *
              ((∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) / (l:ℝ) ^ (rk L)) - 1/zc)
            - ∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ)|
          ≤ |ballVol (rk L) * T ^ (rk L) / detL L *
              ((∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) / (l:ℝ) ^ (rk L)) - 1/zc)|
            + |∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ)| := by
        have h := abs_add_le (ballVol (rk L) * T ^ (rk L) / detL L *
            ((∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) / (l:ℝ) ^ (rk L)) - 1/zc))
          (- ∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ))
        simpa [sub_eq_add_neg] using h
      have hM : ballVol (rk L) * T ^ (rk L) / detL L * (B (rk L) / (TN:ℝ) ^ ((rk L:ℝ) - 1))
          ≤ (ballVol (rk L) * B (rk L) * (2:ℝ)^(rk L - 1)) * T := by
        calc ballVol (rk L) * T ^ (rk L) / detL L * (B (rk L) / (TN:ℝ) ^ ((rk L:ℝ) - 1))
            ≤ ballVol (rk L) * B (rk L) * T * (2:ℝ)^(rk L - 1) := hterm1
          _ = (ballVol (rk L) * B (rk L) * (2:ℝ)^(rk L - 1)) * T := by ring
      have hsteps : ballVol (rk L) * T ^ (rk L) / detL L * (B (rk L) / (TN:ℝ) ^ ((rk L:ℝ) - 1)) + 2*T
          ≤ (ballVol (rk L) * B (rk L) * (2:ℝ)^(rk L - 1) + 2) * (T * (1 + Real.log Y)) := by
        have hExp2 : 0 ≤ ballVol (rk L) * B (rk L) * (2:ℝ)^(rk L - 1) :=
          mul_nonneg (mul_nonneg hV0 (hBpos (rk L)).le) (by positivity)
        have hT1' : T ≤ T*(1+Real.log Y) := by nlinarith [hlogY, hT1]
        have hmul := mul_le_mul_of_nonneg_left hT1' hExp2
        nlinarith [hM, hmul, hT1']
      linarith [hsub, hZb, hsum_mu, hsteps]
    -- === Part B : the error term ===
    have hptI : ∀ l ∈ Finset.Icc 1 L0,
        |(ballCount L (T/(l:ℝ)) : ℝ) - ballVol (rk L)*(T/(l:ℝ))^(rk L)/detL L|
          ≤ Kg * (Y * T^(rk L-1)/detL L) * (1/(l:ℝ)^(rk L-1)) := by
      intro l hl
      obtain ⟨hl1, hlL0⟩ := Finset.mem_Icc.mp hl
      have hlpos : (0:ℝ) < (l:ℝ) := by exact_mod_cast hl1
      have hlne : (l:ℝ) ≠ 0 := ne_of_gt hlpos
      have hYle : Y ≤ T/(l:ℝ) := by
        rw [le_div_iff₀ hlpos]
        have h1 : (l:ℝ) ≤ T/Y := le_trans (by exact_mod_cast hlL0) hL0le
        calc Y * (l:ℝ) ≤ Y * (T/Y) := mul_le_mul_of_nonneg_left h1 hY0.le
          _ = T := by field_simp; try ring
      have h1le : 1 ≤ T/(l:ℝ) := by
        rw [one_le_div hlpos]
        exact le_trans (by exact_mod_cast hlL0) (le_trans hL0le hTYleT)
      have hg := (hKg L (T/(l:ℝ)) Y hR1 h1le).2 hlamY hYle
      have hid : Kg * (T/(l:ℝ))^(rk L)/detL L * (Y/(T/(l:ℝ)))
          = Kg * (Y * T^(rk L-1)/detL L) * (1/(l:ℝ)^(rk L-1)) := by
        have hTp : T ^ (rk L) = T * T ^ (rk L - 1) := by
          rw [← pow_succ']; congr 1; omega
        have hlp : (l:ℝ) ^ (rk L) = (l:ℝ) * (l:ℝ) ^ (rk L - 1) := by
          rw [← pow_succ']; congr 1; omega
        rw [div_pow, hTp, hlp]
        have hlp' : (l:ℝ) ≠ 0 := hlne
        have hlp2 : (l:ℝ) ^ (rk L - 1) ≠ 0 := pow_ne_zero _ hlne
        have hTl : T ≠ 0 := hTne
        field_simp
        try ring
      rwa [hid] at hg
    have hB1 : (∑ l ∈ Finset.Icc 1 L0,
          |(ballCount L (T/(l:ℝ)) : ℝ) - ballVol (rk L)*(T/(l:ℝ))^(rk L)/detL L|)
        ≤ Kg * (Y * T^(rk L-1)/detL L) * 2 := by
      refine le_trans (Finset.sum_le_sum hptI) ?_
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc (∑ l ∈ Finset.Icc 1 L0, 1/(l:ℝ)^(rk L-1))
          ≤ ∑ l ∈ Finset.Icc 1 L0, 1/(l:ℝ)^2 := by
            refine Finset.sum_le_sum (fun l hl => ?_)
            have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
            have hl1' : (1:ℝ) ≤ (l:ℝ) := by exact_mod_cast hl1
            have h2 : (l:ℝ)^2 ≤ (l:ℝ)^(rk L - 1) := pow_le_pow_right₀ hl1' (by omega)
            exact one_div_le_one_div_of_le (pow_pos (by linarith) 2) h2
        _ ≤ 2 := sumIccInvSq L0
    have hTL2Y : T / (L0:ℝ) < 2*Y := by
      rw [div_lt_iff₀ (by exact_mod_cast hL01 : (0:ℝ) < (L0:ℝ))]
      have h1 : T < ((L0:ℝ)+1)*Y := by
        have h := Nat.lt_floor_add_one (T/Y)
        rw [← hL0def] at h
        rwa [div_lt_iff₀ hY0] at h
      have h2 : ((L0:ℝ)+1) ≤ 2*(L0:ℝ) := by
        have : (1:ℝ) ≤ (L0:ℝ) := by exact_mod_cast hL01
        linarith
      nlinarith [h1, h2, hY0]
    have hlog : Real.log ((TN:ℝ)/(L0:ℝ)) ≤ 1 + Real.log Y := by
      have hpos : 0 < (TN:ℝ)/(L0:ℝ) := by
        apply div_pos
        · exact_mod_cast hTN1
        · exact_mod_cast hL01
      have hle : (TN:ℝ)/(L0:ℝ) ≤ 2*Y := by
        calc (TN:ℝ)/(L0:ℝ) ≤ T/(L0:ℝ) := div_le_div_of_nonneg_right hTNle (by positivity)
          _ ≤ 2*Y := le_of_lt hTL2Y
      calc Real.log ((TN:ℝ)/(L0:ℝ)) ≤ Real.log (2*Y) := Real.log_le_log hpos hle
        _ = Real.log 2 + Real.log Y := Real.log_mul (by norm_num) (ne_of_gt hY0)
        _ ≤ 1 + Real.log Y := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
    have hkeyT : T^2 * Y^(rk L - 2) ≤ Y * T^(rk L - 1) := by
      have h1 : Y ^ (rk L - 2) = Y * Y ^ (rk L - 3) := by
        rw [show rk L - 2 = 1 + (rk L - 3) by omega, pow_add, pow_one]
      have h2 : T ^ (rk L - 1) = T ^ 2 * T ^ (rk L - 3) := by
        rw [show rk L - 1 = 2 + (rk L - 3) by omega, pow_add]
      rw [h1, h2]
      have h3 : Y ^ (rk L - 3) ≤ T ^ (rk L - 3) := pow_le_pow_left₀ hY0.le hYT (rk L - 3)
      calc T ^ 2 * (Y * Y ^ (rk L - 3)) ≤ T ^ 2 * (Y * T ^ (rk L - 3)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hY0.le) (by positivity)
        _ = Y * (T ^ 2 * T ^ (rk L - 3)) := by ring
    have hptII : ∀ l ∈ Finset.Icc (L0+1) TN,
        |(ballCount L (T/(l:ℝ)) : ℝ) - ballVol (rk L)*(T/(l:ℝ))^(rk L)/detL L|
          ≤ (Kg*Ks + ballVol (rk L)) * (Y^(rk L - 2)/detL L) * (T/(l:ℝ))^2 + Kg*Ks*(T/(l:ℝ)) := by
      intro l hl
      obtain ⟨hl1, hlTN⟩ := Finset.mem_Icc.mp hl
      have hl1' : 1 ≤ l := by omega
      have hlpos : (0:ℝ) < (l:ℝ) := by exact_mod_cast hl1'
      have hspos : 0 ≤ T/(l:ℝ) := div_nonneg hT0 hlpos.le
      have h1le : 1 ≤ T/(l:ℝ) := by
        rw [one_le_div hlpos]
        exact le_trans (by exact_mod_cast hlTN) hTNle
      have hYle : T/(l:ℝ) < Y := by
        rw [div_lt_iff₀ hlpos]
        have h1 : T < (l:ℝ)*Y := by
          have h2 : T/Y < (l:ℝ) := by
            have h3 := Nat.lt_floor_add_one (T/Y)
            rw [← hL0def] at h3
            have h4 : ((L0:ℝ)+1) ≤ (l:ℝ) := by
              have : L0 + 1 ≤ l := hl1
              exact_mod_cast this
            linarith
          rwa [div_lt_iff₀ hY0] at h2
        rw [mul_comm] at h1
        exact h1
      have hYle' : T/(l:ℝ) ≤ Y := le_of_lt hYle
      have hg := (hKg L (T/(l:ℝ)) Y hR1 h1le).1
      have hreflect : (∑ i ∈ Finset.range (rk L + 1),
            (T/(l:ℝ))^(rk L - i) / ∏ j ∈ Finset.range (rk L - i), lam L (j+1))
          = ∑ k ∈ Finset.range (rk L + 1), (T/(l:ℝ))^k / ∏ j ∈ Finset.range k, lam L (j+1) :=
        Finset.sum_range_reflect (fun k => (T/(l:ℝ))^k / ∏ j ∈ Finset.range k, lam L (j+1))
          (rk L + 1)
      rw [hreflect] at hg
      have hslt := hKs L (rk L) (rk L - 2) Y (T/(l:ℝ)) rfl hR1 (by omega) h1le hYle' hlamY hdet hdetle
      have hx1 : rk L - (rk L - 2) = 2 := by omega
      have hx2 : rk L - 1 - (rk L - 2) = 1 := by omega
      rw [hx1, hx2, pow_one] at hslt
      have hbc : (ballCount L (T/(l:ℝ)) : ℝ)
          ≤ Kg*Ks*((T/(l:ℝ))^2 * Y^(rk L-2)/detL L) + Kg*Ks*(T/(l:ℝ)) := by
        calc (ballCount L (T/(l:ℝ)) : ℝ)
            ≤ Kg * ∑ k ∈ Finset.range (rk L + 1), (T/(l:ℝ))^k / ∏ j ∈ Finset.range k, lam L (j+1) := hg
          _ ≤ Kg * (Ks * ((T/(l:ℝ))^2*Y^(rk L-2)/detL L + T/(l:ℝ))) :=
              mul_le_mul_of_nonneg_left hslt hKgpos.le
          _ = Kg*Ks*((T/(l:ℝ))^2*Y^(rk L-2)/detL L) + Kg*Ks*(T/(l:ℝ)) := by ring
      have hvol : ballVol (rk L)*(T/(l:ℝ))^(rk L)/detL L
          ≤ ballVol (rk L) * ((T/(l:ℝ))^2 * Y^(rk L-2)/detL L) := by
        have hpow2 : (T/(l:ℝ))^(rk L) ≤ (T/(l:ℝ))^2 * Y^(rk L-2) := by
          have hsplit : (T/(l:ℝ))^(rk L) = (T/(l:ℝ))^2 * (T/(l:ℝ))^(rk L - 2) := by
            rw [← pow_add]; congr 1; omega
          rw [hsplit]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hspos hYle' (rk L-2)) (by positivity)
        calc ballVol (rk L)*(T/(l:ℝ))^(rk L)/detL L
            ≤ ballVol (rk L)*((T/(l:ℝ))^2 * Y^(rk L-2))/detL L := by
              apply div_le_div_of_nonneg_right _ hD0.le
              exact mul_le_mul_of_nonneg_left hpow2 hV0
          _ = ballVol (rk L) * ((T/(l:ℝ))^2 * Y^(rk L-2)/detL L) := by ring
      have hbc0 : 0 ≤ (ballCount L (T/(l:ℝ)) : ℝ) := Nat.cast_nonneg _
      have h2nn : 0 ≤ (T/(l:ℝ))^2 := by positivity
      have h3nn : 0 ≤ Y^(rk L-2)/detL L := by positivity
      have hA2 : ballVol (rk L) * ((T/(l:ℝ))^2 * Y^(rk L-2)/detL L)
          ≤ (Kg*Ks + ballVol (rk L)) * (Y^(rk L - 2)/detL L) * (T/(l:ℝ))^2 + Kg*Ks*(T/(l:ℝ)) := by
        have h4 : ballVol (rk L) * ((T/(l:ℝ))^2 * Y^(rk L-2)/detL L)
            = ballVol (rk L) * (Y^(rk L-2)/detL L) * (T/(l:ℝ))^2 := by ring
        rw [h4]
        have hb : ballVol (rk L) * (Y^(rk L-2)/detL L) * (T/(l:ℝ))^2
            ≤ (Kg*Ks + ballVol (rk L)) * (Y^(rk L-2)/detL L) * (T/(l:ℝ))^2 := by
          have hKgKs : 0 ≤ Kg*Ks := by positivity
          apply mul_le_mul_of_nonneg_right _ h2nn
          apply mul_le_mul_of_nonneg_right _ h3nn
          linarith
        have hb2 : 0 ≤ Kg*Ks*(T/(l:ℝ)) := by positivity
        linarith [hb, hb2]
      have hB2' : Kg*Ks*((T/(l:ℝ))^2*Y^(rk L-2)/detL L) + Kg*Ks*(T/(l:ℝ))
          ≤ (Kg*Ks + ballVol (rk L)) * (Y^(rk L - 2)/detL L) * (T/(l:ℝ))^2 + Kg*Ks*(T/(l:ℝ)) := by
        have h4 : Kg*Ks*((T/(l:ℝ))^2*Y^(rk L-2)/detL L)
            = Kg*Ks*(Y^(rk L-2)/detL L)*(T/(l:ℝ))^2 := by ring
        rw [h4]
        have hb : Kg*Ks*(Y^(rk L-2)/detL L)*(T/(l:ℝ))^2
            ≤ (Kg*Ks + ballVol (rk L))*(Y^(rk L-2)/detL L)*(T/(l:ℝ))^2 := by
          apply mul_le_mul_of_nonneg_right _ h2nn
          apply mul_le_mul_of_nonneg_right _ h3nn
          linarith
        linarith [hb]
      refine abs_le.mpr ⟨?_, ?_⟩
      · have hvolT := le_trans hvol hA2
        linarith [hvolT, hbc0]
      · have hvv : 0 ≤ ballVol (rk L)*(T/(l:ℝ))^(rk L)/detL L := by positivity
        linarith [hbc, hB2', hvv]
    have hB2 : (∑ l ∈ Finset.Icc (L0+1) TN,
          |(ballCount L (T/(l:ℝ)) : ℝ) - ballVol (rk L)*(T/(l:ℝ))^(rk L)/detL L|)
        ≤ (Kg*Ks + ballVol (rk L)) * 2 * (Y * T^(rk L-1)/detL L) + Kg*Ks*(T*(1+Real.log Y)) := by
      have hsum1 : (∑ l ∈ Finset.Icc (L0+1) TN, (T/(l:ℝ))^2) ≤ 2*T^2 := by
        have hc : (∑ l ∈ Finset.Icc (L0+1) TN, (T/(l:ℝ))^2)
            = T^2 * (∑ l ∈ Finset.Icc (L0+1) TN, 1/(l:ℝ)^2) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [div_pow]; ring
        rw [hc]
        have hsub : Finset.Icc (L0 + 1) TN ⊆ Finset.Icc 1 TN := by
          intro l hl; rw [Finset.mem_Icc] at hl ⊢; omega
        calc T^2 * (∑ l ∈ Finset.Icc (L0+1) TN, 1/(l:ℝ)^2)
            ≤ T^2 * (∑ l ∈ Finset.Icc 1 TN, 1/(l:ℝ)^2) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
          _ ≤ T^2 * 2 := by
              apply mul_le_mul_of_nonneg_left (sumIccInvSq TN) (by positivity)
          _ = 2*T^2 := by ring
      have hsum2 : (∑ l ∈ Finset.Icc (L0+1) TN, T/(l:ℝ)) ≤ T*(1+Real.log Y) := by
        have hc : (∑ l ∈ Finset.Icc (L0+1) TN, T/(l:ℝ))
            = T * (∑ l ∈ Finset.Icc (L0+1) TN, 1/(l:ℝ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [mul_one_div]
        rw [hc]
        apply mul_le_mul_of_nonneg_left _ hT0
        calc (∑ l ∈ Finset.Icc (L0+1) TN, 1/(l:ℝ))
            ≤ Real.log ((TN:ℝ)/(L0:ℝ)) := sumIccInvLeLog L0 TN hL01 hL0TN
          _ ≤ 1 + Real.log Y := hlog
      refine le_trans (Finset.sum_le_sum hptII) ?_
      rw [Finset.sum_add_distrib]
      have hfac1 : (∑ l ∈ Finset.Icc (L0+1) TN,
            (Kg*Ks + ballVol (rk L)) * (Y^(rk L - 2)/detL L) * (T/(l:ℝ))^2)
          = (Kg*Ks + ballVol (rk L)) * (Y^(rk L - 2)/detL L) *
              (∑ l ∈ Finset.Icc (L0+1) TN, (T/(l:ℝ))^2) := by
        rw [Finset.mul_sum]
      have hfac2 : (∑ l ∈ Finset.Icc (L0+1) TN, Kg*Ks*(T/(l:ℝ)))
          = Kg*Ks*(∑ l ∈ Finset.Icc (L0+1) TN, T/(l:ℝ)) := by
        rw [Finset.mul_sum]
      rw [hfac1, hfac2]
      have hKY : Y^(rk L - 2)/detL L * (2*T^2) ≤ 2*(Y * T^(rk L-1)/detL L) := by
        rw [div_mul_eq_mul_div]
        rw [show Y^(rk L-2) * (2*T^2) = 2*(T^2 * Y^(rk L-2)) by ring]
        calc 2 * (T^2 * Y^(rk L-2)) / detL L ≤ 2 * (Y * T^(rk L-1)) / detL L := by
              apply div_le_div_of_nonneg_right _ hD0.le
              linarith [hkeyT]
          _ = 2*(Y*T^(rk L-1)/detL L) := by ring
      have hstep1 : (Kg*Ks + ballVol (rk L)) * (Y^(rk L - 2)/detL L) *
            (∑ l ∈ Finset.Icc (L0+1) TN, (T/(l:ℝ))^2)
          ≤ (Kg*Ks + ballVol (rk L)) * 2 * (Y * T^(rk L-1)/detL L) := by
        have hVK : 0 ≤ Kg*Ks + ballVol (rk L) := by positivity
        calc (Kg*Ks + ballVol (rk L)) * (Y^(rk L - 2)/detL L) *
              (∑ l ∈ Finset.Icc (L0+1) TN, (T/(l:ℝ))^2)
            ≤ (Kg*Ks + ballVol (rk L)) * (Y^(rk L - 2)/detL L) * (2*T^2) :=
              mul_le_mul_of_nonneg_left hsum1 (by positivity)
          _ = (Kg*Ks + ballVol (rk L)) * (Y^(rk L - 2)/detL L * (2*T^2)) := by ring
          _ ≤ (Kg*Ks + ballVol (rk L)) * (2*(Y * T^(rk L-1)/detL L)) :=
              mul_le_mul_of_nonneg_left hKY hVK
          _ = (Kg*Ks + ballVol (rk L)) * 2 * (Y * T^(rk L-1)/detL L) := by ring
      have hstep2 : Kg*Ks*(∑ l ∈ Finset.Icc (L0+1) TN, T/(l:ℝ)) ≤ Kg*Ks*(T*(1+Real.log Y)) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
      linarith [hstep1, hstep2]
    -- === assembly ===
    have hdecomp : (∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) *
          ((ballCount L (T / (l:ℝ)) : ℝ) - 1)) - ballVol (rk L) / zc * T ^ (rk L) / detL L
        = ((∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) *
              (ballVol (rk L) * (T / (l:ℝ)) ^ (rk L) / detL L - 1))
            - ballVol (rk L) / zc * T ^ (rk L) / detL L)
          + ∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) *
              ((ballCount L (T/(l:ℝ)) : ℝ) - ballVol (rk L)*(T/(l:ℝ))^(rk L)/detL L) := by
      have h1 : (∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) *
            ((ballCount L (T / (l:ℝ)) : ℝ) - 1))
          = (∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) *
              (ballVol (rk L) * (T / (l:ℝ)) ^ (rk L) / detL L - 1))
            + ∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) *
              ((ballCount L (T/(l:ℝ)) : ℝ) - ballVol (rk L)*(T/(l:ℝ))^(rk L)/detL L) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun l _ => ?_); ring
      rw [h1]; ring
    have hErrB : |∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) *
          ((ballCount L (T/(l:ℝ)) : ℝ) - ballVol (rk L)*(T/(l:ℝ))^(rk L)/detL L)|
        ≤ 2*Kg*(Y * T^(rk L-1)/detL L) + (Kg*Ks + ballVol (rk L))*2*(Y * T^(rk L-1)/detL L)
          + Kg*Ks*(T*(1+Real.log Y)) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hmu : (∑ l ∈ Finset.Icc 1 TN, |(ArithmeticFunction.moebius l : ℝ) *
            ((ballCount L (T/(l:ℝ)) : ℝ) - ballVol (rk L)*(T/(l:ℝ))^(rk L)/detL L)|)
          ≤ ∑ l ∈ Finset.Icc 1 TN,
            |(ballCount L (T/(l:ℝ)) : ℝ) - ballVol (rk L)*(T/(l:ℝ))^(rk L)/detL L| := by
        refine Finset.sum_le_sum (fun l _ => ?_)
        rw [abs_mul]
        calc |(ArithmeticFunction.moebius l : ℝ)| *
              |(ballCount L (T/(l:ℝ)) : ℝ) - ballVol (rk L)*(T/(l:ℝ))^(rk L)/detL L|
            ≤ 1 * |(ballCount L (T/(l:ℝ)) : ℝ) - ballVol (rk L)*(T/(l:ℝ))^(rk L)/detL L| :=
              mul_le_mul_of_nonneg_right (by
                have h := ArithmeticFunction.abs_moebius_le_one (n := l)
                exact_mod_cast h) (abs_nonneg _)
          _ = _ := one_mul _
      refine le_trans hmu ?_
      rw [hsplit (fun l => |(ballCount L (T/(l:ℝ)) : ℝ) - ballVol (rk L)*(T/(l:ℝ))^(rk L)/detL L|)]
      linarith [hB1, hB2]
    have hmain : |(∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) *
          ((ballCount L (T / (l:ℝ)) : ℝ) - 1)) - ballVol (rk L) / zc * T ^ (rk L) / detL L|
        ≤ Kf (rk L) * (T ^ (rk L) / detL L * (Y / T) + T * (1 + Real.log Y)) := by
      rw [hdecomp]
      refine le_trans (abs_add_le _ _) ?_
      have hAB := add_le_add hA hErrB
      have hTAeq : Y * T ^ (rk L - 1) / detL L = T ^ (rk L) / detL L * (Y / T) := by
        rw [show T ^ (rk L) = T ^ (rk L - 1) * T by
          rw [← pow_succ]; congr 1; omega]
        field_simp
        try ring
      have hBpos' : 0 < B (rk L) := hBpos _
      have hYTR : 0 ≤ Y * T ^ (rk L - 1) / detL L := by positivity
      have hTl : 0 ≤ T * (1 + Real.log Y) := by positivity
      have hp2 : 0 ≤ (2:ℝ)^(rk L - 1) := by positivity
      have hExp : 0 ≤ ballVol (rk L) * B (rk L) * (2:ℝ)^(rk L - 1) :=
        mul_nonneg (mul_nonneg hV0 hBpos'.le) hp2
      have hsub : (ballVol (rk L) * B (rk L) * (2:ℝ)^(rk L - 1) + 2) * (T * (1 + Real.log Y))
            + (2*Kg*(Y * T^(rk L-1)/detL L) + (Kg*Ks + ballVol (rk L))*2*(Y * T^(rk L-1)/detL L)
              + Kg*Ks*(T*(1+Real.log Y)))
          ≤ Kf (rk L) * (T ^ (rk L) / detL L * (Y / T) + T * (1 + Real.log Y)) := by
        rw [← hTAeq]
        simp only [Kf]
        nlinarith [hKgpos, hKspos, hV0, hBpos', hp2, hYTR, hTl, hExp,
          mul_nonneg hKgpos.le hKspos.le]
      exact le_trans (le_trans hAB hsub) le_rfl
    have hKfle : Kf (rk L) ≤ KC := by
      rw [hKC]
      refine Finset.single_le_sum (fun R _ => ?_) (Finset.mem_range.mpr ?_)
      · have hV : 0 ≤ ballVol R := hp_ballVol_nonneg R
        have hC : 0 < B R := hBpos R
        have h1 : 0 < 2 * Kg := by linarith
        have h2 : 0 ≤ 4 * Kg * Ks := by nlinarith [hKgpos, hKspos]
        have h3 : 0 ≤ 2 * ballVol R := by linarith
        have h4 : 0 ≤ ballVol R * B R * (2 : ℝ) ^ (R - 1) :=
          mul_nonneg (mul_nonneg hV hC.le) (by positivity)
        simp only [Kf]; linarith
      · exact Nat.lt_succ_of_le (rk_le_card L)
    have hfin : |(∑ l ∈ Finset.Icc 1 TN, (ArithmeticFunction.moebius l : ℝ) *
          ((ballCount L (T / (l:ℝ)) : ℝ) - 1)) - ballVol (rk L) / zc * T ^ (rk L) / detL L|
        ≤ KC * (T ^ (rk L) / detL L * (Y / T)) + KC * T * (1 + Real.log Y) := by
      refine le_trans hmain ?_
      have hc1 : 0 ≤ T ^ (rk L) / detL L * (Y / T) := by positivity
      have hc2 : 0 ≤ T * (1 + Real.log Y) := by positivity
      calc Kf (rk L) * (T ^ (rk L) / detL L * (Y / T) + T * (1 + Real.log Y))
          = Kf (rk L) * (T ^ (rk L) / detL L * (Y / T)) + Kf (rk L) * (T * (1 + Real.log Y)) := by
            ring
        _ ≤ KC * (T ^ (rk L) / detL L * (Y / T)) + KC * (T * (1 + Real.log Y)) :=
            add_le_add (mul_le_mul_of_nonneg_right hKfle hc1)
              (mul_le_mul_of_nonneg_right hKfle hc2)
        _ = KC * (T ^ (rk L) / detL L * (Y / T)) + KC * T * (1 + Real.log Y) := by ring
    rw [hNsum]
    exact hfin


end Main

end Work.HP.MDEstimates
