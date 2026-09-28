import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.MM2.Sk1_mix_ell
import Submission.Work.HP.MM2.mix_arith
import Submission.Work.HP.MM2.loc_arith
import Submission.Work.HP.MM2.moebius_gcd_zeta
import Submission.Work.HP.MM2.gcd_div_gcd_eq
import Submission.Work.HP.MM2.ss1_S1ball_aux
import Submission.Work.HP.MM2.ss1_sum_Icc_inv_le
import Submission.Work.HP.MM2.ss1_sum_inv_pow_le
import Submission.Work.HP.MM2.ss1_sum_inv_pow_tail
import Submission.Work.HP.DeltaXY_gcd_detL
import Submission.Work.HP.det_gam_gen
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.latOrth_count_degenerate
import Submission.Work.HP.Vero.finrank_latOrth
import Submission.Work.HP.isPrim_veronese
import Submission.Work.HP.MDEstimates.ball_count_R0
import Submission.Work.HP.MDEstimates.veronese_linIndep
import Submission.Work.HP.MDEstimates.zeta_tail_C
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.tendsto_wOf_atTop
import Submission.Work.HP.bigW_le_pow
import Submission.Work.HP.MM2.mix_S1ball_sum_le
import Submission.Work.HP.MM2.mix_E2_sum_le

set_option maxHeartbeats 4000000

noncomputable section

open Filter Finset MeasureTheory

namespace Work.HP.MM2

open Work.HP

/-! ## Private elementary helpers (local copies; the originals in `Sstar2_loc_pair` are `private`) -/

private lemma int_finset_gcd_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℤ) :
    0 ≤ s.gcd f := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.gcd_insert]; exact Int.gcd_nonneg _ _

private lemma one_le_bigW_real (w : ℝ) : (1 : ℝ) ≤ (bigW w : ℝ) := by
  have h := one_le_bigW w
  exact_mod_cast h

private lemma bigW_pos_real (w : ℝ) : 0 < (bigW w : ℝ) :=
  lt_of_lt_of_le zero_lt_one (one_le_bigW_real w)

private lemma natAbs_cast_of_nonneg (m : ℤ) (hm : 0 ≤ m) :
    (((m.natAbs : ℕ)) : ℝ) = (m : ℝ) := by
  rw [Nat.cast_natAbs, abs_of_nonneg (by exact_mod_cast hm)]

private lemma isPrim_ne_zero' {ι : Type*} [Fintype ι] {a : ι → ℤ} (h : IsPrim a) : a ≠ 0 := by
  intro h0
  have h1 : Finset.univ.gcd a = 0 :=
    Finset.gcd_eq_zero_iff.mpr (fun i _ => by rw [h0]; rfl)
  rw [IsPrim] at h
  rw [h] at h1
  exact one_ne_zero h1

private lemma eNorm_pos_of_ne_zero {ι : Type*} [Fintype ι] {v : ι → ℤ} (hv : v ≠ 0) :
    0 < eNorm v := by
  rw [eNorm, Real.sqrt_pos]
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hv (funext hcon)
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, by
    have h : ((v i : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hi
    positivity⟩

private lemma one_le_eNorm {ι : Type*} [Fintype ι] {v : ι → ℤ} (hv : v ≠ 0) : 1 ≤ eNorm v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hv (funext hcon)
  have h1 : (1 : ℝ) ≤ |(((v i : ℤ)) : ℝ)| := by
    have : (1 : ℤ) ≤ |v i| := Int.one_le_abs hi
    exact_mod_cast this
  have h2 : (1 : ℝ) ≤ (((v i : ℤ)) : ℝ) ^ 2 := by
    have h := sq_abs (((v i : ℤ)) : ℝ)
    nlinarith [h1, abs_nonneg (((v i : ℤ)) : ℝ)]
  have h3 : (((v i : ℤ)) : ℝ) ^ 2 ≤ ∑ j, (((v j : ℤ)) : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun j => (((v j : ℤ)) : ℝ) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (∑ j, (((v j : ℤ)) : ℝ) ^ 2) := Real.sqrt_le_sqrt (le_trans h2 h3)
    _ = eNorm v := rfl

private lemma ne_of_linIndep_pair {n : ℕ} {x y : Fin (n + 1) → ℤ}
    (h : LinearIndependent ℤ ![x, y]) : x ≠ y := by
  intro hxy
  have hc := (LinearIndependent.pair_iff.mp h) 1 (-1) (by simp [hxy])
  norm_num at hc

private lemma ne_neg_of_linIndep_pair {n : ℕ} {x y : Fin (n + 1) → ℤ}
    (h : LinearIndependent ℤ ![x, y]) : x ≠ -y := by
  intro hxy
  have hc := (LinearIndependent.pair_iff.mp h) 1 1 (by simp [hxy])
  norm_num at hc

private lemma wedgeNorm_le_mul_own {ι : Type*} [Fintype ι] (v w : ι → ℤ) :
    wedgeNorm v w ≤ eNorm v * eNorm w := by
  have h1 : eNorm v ^ 2 * eNorm w ^ 2 - (dotR (toR v) (toR w)) ^ 2
      ≤ (eNorm v * eNorm w) ^ 2 := by
    rw [mul_pow]; linarith [sq_nonneg (dotR (toR v) (toR w))]
  calc wedgeNorm v w
      = Real.sqrt (eNorm v ^ 2 * eNorm w ^ 2 - (dotR (toR v) (toR w)) ^ 2) := rfl
    _ ≤ Real.sqrt ((eNorm v * eNorm w) ^ 2) := Real.sqrt_le_sqrt h1
    _ = eNorm v * eNorm w := Real.sqrt_sq (mul_nonneg (eNorm_nonneg v) (eNorm_nonneg w))

private lemma wedgeNorm_veronese_pos (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hn : 1 ≤ n)
    (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (hxy : LinearIndependent ℤ ![x, y]) :
    0 < wedgeNorm (veronese d n x) (veronese d n y) := by
  have hD := DeltaXY_gcd_detL d n hd hn x y hx hy hxy
  have hEx : 0 < eNorm (veronese d n x) :=
    eNorm_pos_of_ne_zero (MDEstimates.veronese_ne_zero (isPrim_ne_zero' hx))
  have hEy : 0 < eNorm (veronese d n y) :=
    eNorm_pos_of_ne_zero (MDEstimates.veronese_ne_zero (isPrim_ne_zero' hy))
  have hdet : 0 < detL (Gam d n x y) := by
    have h := Lat.detL_ge_one (Gam d n x y); linarith
  have hGne : (gcdMinors2 x y : ℝ) ≠ 0 := by
    have h := DGG.gcdMinors2_ne_zero x y hxy
    exact_mod_cast h
  have hwne : wedgeNorm (veronese d n x) (veronese d n y) ≠ 0 := by
    intro h0
    have h2 : DeltaXY d n x y = 0 := by rw [DeltaXY, h0, div_zero]
    have h3 : DeltaXY d n x y * (gcdMinors2 x y : ℝ) = 0 := by rw [h2, zero_mul]
    rw [h3] at hD
    have h1 : 0 < eNorm (veronese d n x) * eNorm (veronese d n y) / detL (Gam d n x y) :=
      div_pos (mul_pos hEx hEy) hdet
    linarith
  exact lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hwne)

private lemma deltaXY_pos (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hn : 1 ≤ n)
    (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (hxy : LinearIndependent ℤ ![x, y]) :
    0 < DeltaXY d n x y := by
  have hwp := wedgeNorm_veronese_pos d n hd hn x y hx hy hxy
  have hEx : 0 < eNorm (veronese d n x) :=
    eNorm_pos_of_ne_zero (MDEstimates.veronese_ne_zero (isPrim_ne_zero' hx))
  have hEy : 0 < eNorm (veronese d n y) :=
    eNorm_pos_of_ne_zero (MDEstimates.veronese_ne_zero (isPrim_ne_zero' hy))
  rw [DeltaXY]
  exact div_pos (mul_pos hEx hEy) hwp

private lemma one_le_deltaXY (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hn : 1 ≤ n)
    (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (hxy : LinearIndependent ℤ ![x, y]) :
    1 ≤ DeltaXY d n x y := by
  have hwp := wedgeNorm_veronese_pos d n hd hn x y hx hy hxy
  rw [DeltaXY, le_div_iff₀ hwp]
  have h := wedgeNorm_le_mul_own (veronese d n x) (veronese d n y)
  linarith

private lemma abs_sum_sub_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    |(∑ i ∈ s, f i) - ∑ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

private lemma zetaR_pos_of (m : ℕ) (hm : 1 < m) : 0 < zetaR m := by
  have hsum : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ m) := by
    have h2 : Summable (fun j : ℕ => 1 / ((j : ℕ) : ℝ) ^ m) :=
      Real.summable_one_div_nat_pow.mpr hm
    have h3 := (summable_nat_add_iff (f := fun j : ℕ => 1 / ((j : ℕ) : ℝ) ^ m) 1).mpr h2
    refine h3.congr (fun k => ?_)
    simp only [Nat.cast_add, Nat.cast_one]
  rw [zetaR]
  exact Summable.tsum_pos hsum (fun k => by positivity) 0 (by norm_num)

private lemma zetaR_ge_one_of (m : ℕ) (hm : 1 < m) : 1 ≤ zetaR m := by
  have hsum : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ m) := by
    have h2 : Summable (fun j : ℕ => 1 / ((j : ℕ) : ℝ) ^ m) :=
      Real.summable_one_div_nat_pow.mpr hm
    have h3 := (summable_nat_add_iff (f := fun j : ℕ => 1 / ((j : ℕ) : ℝ) ^ m) 1).mpr h2
    refine h3.congr (fun k => ?_)
    simp only [Nat.cast_add, Nat.cast_one]
  have hle := Summable.le_tsum hsum 0 (fun j _ => by positivity :
    ∀ j : ℕ, j ≠ 0 → 0 ≤ 1 / ((j : ℝ) + 1) ^ m)
  rw [zetaR]
  refine le_trans ?_ hle
  norm_num

private lemma one_le_lamX (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    (x : Fin (n + 1) → ℤ) (hx : IsPrim x) : 1 ≤ lamX d n x := by
  have hc : IsPrim (veronese d n x) := isPrim_veronese d n (by omega) hx
  have hrk : rk (latOrth (veronese d n x)) = NN d n - 1 :=
    LCD_rk_latOrth (veronese d n x) hc
  have hN : 6 ≤ NN d n := six_le_NN d n hd hdn
  rw [lamX]
  exact MDEstimates.one_le_lam _ (by omega) (by rw [hrk])

private lemma mix_per_ell_main_eq (A al W Q g H V D E l : ℝ) (N : ℕ) (hN : 2 ≤ N)
    (hl : l ≠ 0) (hal : al ≠ 0) (hW : W ≠ 0) (hQ : Q = W / g) (hg : g ≠ 0) (hE : E ≠ 0) :
    (1 / l) * ((A / l) ^ (N - 2) * V * D * H / (al * Q * E))
      = (A ^ (N - 2) * V * D / (al * W * E)) * (H * g / l ^ (N - 1)) := by
  subst hQ
  have hpow : l ^ (N - 1) = l ^ (N - 2) * l ^ 1 := by
    rw [← pow_add]; congr 1; omega
  rw [div_pow, hpow]
  field_simp
  try ring

/-! ## Local abbreviations for the mixed per-`ℓ` terms -/

private abbrev mixH (d n : ℕ) (B : ℝ) (x y : Fin (n + 1) → ℤ) (ℓ : ℕ) : ℝ :=
  ((Nat.gcd (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))) (gcdMinors2 x y).natAbs : ℕ) : ℝ)

private abbrev mixg (d n : ℕ) (B : ℝ) (ℓ : ℕ) : ℝ := ((Nat.gcd ℓ (bigW (wOf B)) : ℕ) : ℝ)

private abbrev mixQ (d n : ℕ) (B : ℝ) (ℓ : ℕ) : ℝ :=
  (((bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B)) : ℕ) : ℝ))

private abbrev mixPerMain (d n : ℕ) (A B : ℝ) (x y : Fin (n + 1) → ℤ) (ℓ : ℕ) : ℝ :=
  (A / (ℓ : ℝ)) ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y *
    mixH d n B x y ℓ / (Real.log B * mixQ d n B ℓ * eNorm (veronese d n x))

private abbrev mixE1 (d n : ℕ) (C A B : ℝ) (x y : Fin (n + 1) → ℤ) (ℓ : ℕ) : ℝ :=
  C * mixPerMain d n A B x y ℓ * min 1 (DeltaXY d n x y ^ 2 / (Real.log B) ^ 2)

private abbrev mixE2 (d n : ℕ) (C A B : ℝ) (x y : Fin (n + 1) → ℤ) (ℓ : ℕ) : ℝ :=
  C * (A / (ℓ : ℝ)) ^ (NN d n - 3) * lamX d n x * mixH d n B x y ℓ /
    eNorm (veronese d n x)

private abbrev mixE3 (d n : ℕ) (C A B : ℝ) (x y : Fin (n + 1) → ℤ) (ℓ : ℕ) : ℝ :=
  C * S1ball d n x (mixQ d n B ℓ * lamX d n x)

private abbrev mixPerErr (d n : ℕ) (C A B : ℝ) (x y : Fin (n + 1) → ℤ) (ℓ : ℕ) : ℝ :=
  mixE1 d n C A B x y ℓ + mixE2 d n C A B x y ℓ + mixE3 d n C A B x y ℓ

private abbrev mixK (d n : ℕ) (A B : ℝ) (x y : Fin (n + 1) → ℤ) : ℝ :=
  A ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y /
    (Real.log B * (bigW (wOf B) : ℝ) * eNorm (veronese d n x))

private abbrev mixG (d n : ℕ) (x y : Fin (n + 1) → ℤ) : ℝ := (((gcdMinors2 x y).natAbs : ℕ) : ℝ)

private abbrev mixL (d n : ℕ) (A B : ℝ) (x y : Fin (n + 1) → ℤ) : ℝ :=
  mixK d n A B x y * mixG d n x y / zetaR (NN d n - 2)

/-! Temporary stand-ins for the two delegated arithmetic inputs. -/

theorem mix_small (d n : ℕ) [DecidableEq (Work.HP.Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    (h22 : (d, n) ≠ (2, 2)) :
    ∃ C B₀ : ℝ, 0 < C ∧ ∀ A B : ℝ, B₀ ≤ B → B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      ∀ x y : Fin (n + 1) → ℤ, Work.HP.IsPrim x → Work.HP.IsPrim y →
        LinearIndependent ℤ ![x, y] →
        Work.HP.eNorm x ≤ B ^ (1 / ((n : ℝ) + 1 - d)) →
        (Work.HP.bigW (Work.HP.wOf B) : ℝ) * Work.HP.MM2.lamX d n x ≤ A ^ ((3 : ℝ) / 4) →
      |(∑ ℓ ∈ Finset.Icc 1 ⌊A / ((Work.HP.bigW (Work.HP.wOf B) : ℝ) *
              Work.HP.MM2.lamX d n x)⌋₊,
          ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) *
            Work.HP.Sk d n 1 (Work.HP.GamMix d n x y (Work.HP.bigW (Work.HP.wOf B) /
                Nat.gcd ℓ (Work.HP.bigW (Work.HP.wOf B))))
              (Work.HP.TmixSet d n y (A / (ℓ : ℝ)) (Real.log B)))
        - Work.HP.MM2.mixMain d n A B (x, y)|
        ≤ C * Work.HP.MM2.mixMain d n A B (x, y) * (Work.HP.errXY d n B x y + 1 / Real.log A) := by
  classical
  obtain ⟨Csk, hCskpos, hSk⟩ := Sk1_mix_ell d n hd hdn h22
  have hCsknn : 0 ≤ Csk := le_of_lt hCskpos
  obtain ⟨K2, B2, hK2pos, hE2le⟩ := mix_E2_sum_le d n hd hdn h22 (2 * Csk) (by linarith)
  obtain ⟨K3, B3, hK3pos, hS1le⟩ := mix_S1ball_sum_le d n hd hdn h22 Csk hCskpos
  obtain ⟨Cz, hCzpos, hZ⟩ := moebius_gcd_zeta (NN d n - 2) 1 (by have h := six_le_NN d n hd hdn; omega)
  have hN6 : 6 ≤ NN d n := six_le_NN d n hd hdn
  have hVpos : 0 < ballVol (NN d n - 2) := Work.HP.ballVol_pos _ (by omega)
  have hzzpos : 0 < zetaR (NN d n - 2) := zetaR_pos_of _ (by omega)
  have hzz1 : 1 ≤ zetaR (NN d n - 2) := zetaR_ge_one_of _ (by omega)
  set K0 : ℝ := zetaR (NN d n - 2) * Cz * 2 ^ (NN d n)
    + zetaR (NN d n - 2) * 2 ^ (NN d n) + 1 with hK0def
  have hK0pos : 0 < K0 := by rw [hK0def]; positivity
  have hK0ge1 : 1 ≤ K0 := by
    rw [hK0def]
    have h1 : 0 ≤ zetaR (NN d n - 2) * Cz * 2 ^ (NN d n) := by positivity
    have h2 : 0 ≤ zetaR (NN d n - 2) * 2 ^ (NN d n) := by positivity
    linarith
  have hK0Cz : zetaR (NN d n - 2) * Cz ≤ K0 := by
    rw [hK0def]
    have h2N : (1 : ℝ) ≤ 2 ^ (NN d n) := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have h3 : 0 ≤ zetaR (NN d n - 2) * Cz := by positivity
    have h4 : zetaR (NN d n - 2) * Cz ≤ zetaR (NN d n - 2) * Cz * 2 ^ (NN d n) := by
      calc zetaR (NN d n - 2) * Cz = zetaR (NN d n - 2) * Cz * 1 := (mul_one _).symm
        _ ≤ zetaR (NN d n - 2) * Cz * 2 ^ (NN d n) := mul_le_mul_of_nonneg_left h2N h3
    have h5 : 0 ≤ zetaR (NN d n - 2) * 2 ^ (NN d n) := by positivity
    linarith
  obtain ⟨Bar, har⟩ := mix_arith d n hd hdn h22 K0
  obtain ⟨Bw, hBw⟩ : ∃ B₀ : ℝ, ∀ B : ℝ, B₀ ≤ B → 2 ≤ wOf B :=
    Filter.eventually_atTop.mp (tendsto_wOf_atTop.eventually_ge_atTop 2)
  -- `wOf B + 1 ≤ B^{5/24}` eventually
  have hwB : ∀ᶠ B in Filter.atTop, wOf B + 1 ≤ B ^ ((5 : ℝ) / 24) := by
    have hlog1 : ∀ᶠ B in Filter.atTop, (1 : ℝ) ≤ Real.log B :=
      Real.tendsto_log_atTop.eventually_ge_atTop 1
    have hloglog1 : ∀ᶠ B in Filter.atTop, (1 : ℝ) ≤ Real.log (Real.log B) :=
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1
    have hpow : ∀ᶠ B in Filter.atTop, Real.log B ≤ B ^ ((5 : ℝ) / 48) := by
      simpa [pow_one] using la_pow_log_le_rpow 1 (show (0 : ℝ) < 5 / 48 by norm_num)
    have hB1 : ∀ᶠ B in Filter.atTop, (1 : ℝ) ≤ B := Filter.eventually_ge_atTop 1
    have hbig : ∀ᶠ B in Filter.atTop, (2 : ℝ) ≤ B ^ ((5 : ℝ) / 48) :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 48)).eventually_ge_atTop 2
    filter_upwards [hlog1, hloglog1, hpow, hB1, hbig] with B hl1 hll1 hp hb1 hbig
    have hlpos : 0 < Real.log B := by linarith
    have hBpos : 0 < B := by linarith
    have hw_le : wOf B ≤ Real.log B := by
      rw [wOf, div_le_iff₀ (by linarith : 0 < Real.log (Real.log B))]
      exact le_mul_of_one_le_right hlpos.le hll1
    have hlp : 0 < B ^ ((5 : ℝ) / 48) := Real.rpow_pos_of_pos hBpos _
    calc wOf B + 1 ≤ Real.log B + 1 := by linarith
      _ ≤ 2 * Real.log B := by linarith
      _ ≤ 2 * B ^ ((5 : ℝ) / 48) := by linarith
      _ ≤ B ^ ((5 : ℝ) / 24) := by
          have hsplit : B ^ ((5 : ℝ) / 24) = B ^ ((5 : ℝ) / 48) * B ^ ((5 : ℝ) / 48) := by
            rw [← Real.rpow_add hBpos, show (5 : ℝ) / 48 + 5 / 48 = 5 / 24 by norm_num]
          rw [hsplit]
          nlinarith [hlp, hbig]
  obtain ⟨BwB, hBwB⟩ : ∃ B₀ : ℝ, ∀ B : ℝ, B₀ ≤ B → wOf B + 1 ≤ B ^ ((5 : ℝ) / 24) :=
    Filter.eventually_atTop.mp hwB
  set B0 : ℝ := max (max Bar 100) (max Bw (max B2 (max B3 BwB))) with hB0def
  set CC : ℝ := 2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2) + K2 + K3 + 1 with hCCdef
  have hCCpos : 0 < CC := by rw [hCCdef]; positivity
  refine ⟨CC, B0, hCCpos, ?_⟩
  intro A B hB hBA hAB2 x y hx hy hxy hnx hWlam
  have hBar : Bar ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hB
  have h100 : (100 : ℝ) ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hB
  have hBw' : Bw ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB
  have hB2' : B2 ≤ B := by
    have h1 : B2 ≤ max B2 (max B3 BwB) := le_max_left _ _
    have h2 : max B2 (max B3 BwB) ≤ max Bw (max B2 (max B3 BwB)) := le_max_right _ _
    have h3 : max Bw (max B2 (max B3 BwB)) ≤ B0 := le_max_right _ _
    linarith
  have hB3' : B3 ≤ B := by
    have h1 : B3 ≤ max B3 BwB := le_max_left _ _
    have h2 : max B3 BwB ≤ max B2 (max B3 BwB) := le_max_right _ _
    have h3 : max B2 (max B3 BwB) ≤ max Bw (max B2 (max B3 BwB)) := le_max_right _ _
    have h4 : max Bw (max B2 (max B3 BwB)) ≤ B0 := le_max_right _ _
    linarith
  have hBwB' : BwB ≤ B := by
    have h1 : BwB ≤ max B3 BwB := le_max_right _ _
    have h2 : max B3 BwB ≤ max B2 (max B3 BwB) := le_max_right _ _
    have h3 : max B2 (max B3 BwB) ≤ max Bw (max B2 (max B3 BwB)) := le_max_right _ _
    have h4 : max Bw (max B2 (max B3 BwB)) ≤ B0 := le_max_right _ _
    linarith
  have hw2 : 2 ≤ wOf B := hBw B hBw'
  have hwBd : wOf B + 1 ≤ B ^ ((5 : ℝ) / 24) := hBwB B hBwB'
  obtain ⟨hA1, hlogA1, hw1, hW1, hWA, har6, har7, har8, har9⟩ := har B hBar A hBA hAB2 x hnx
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hBpos : 0 < B := by linarith
  have hB1 : 1 < B := by linarith
  have hWrpos : 0 < (bigW (wOf B) : ℝ) := bigW_pos_real _
  have hWne : (bigW (wOf B) : ℝ) ≠ 0 := ne_of_gt hWrpos
  have halpos : 0 < Real.log B := Real.log_pos hB1
  have halne : Real.log B ≠ 0 := ne_of_gt halpos
  have hlogApos : 0 < Real.log A := lt_of_lt_of_le zero_lt_one hlogA1
  have hlogAne : Real.log A ≠ 0 := ne_of_gt hlogApos
  have hlogAleB : Real.log A ≤ 2 * Real.log B := by
    have h := Real.log_le_log hApos hAB2
    rwa [Real.log_pow] at h
  have hlam1 : 1 ≤ lamX d n x := one_le_lamX d n hd hdn x hx
  have hlampos : 0 < lamX d n x := lt_of_lt_of_le zero_lt_one hlam1
  have hE1 : 1 ≤ eNorm (veronese d n x) :=
    one_le_eNorm (MDEstimates.veronese_ne_zero (isPrim_ne_zero' hx))
  have hEpos : 0 < eNorm (veronese d n x) := lt_of_lt_of_le zero_lt_one hE1
  have hT1 : 1 ≤ (bigW (wOf B) : ℝ) * lamX d n x := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (bigW (wOf B) : ℝ) * lamX d n x := mul_le_mul hW1 hlam1 (by norm_num) (by linarith)
  have hDpos : 0 < DeltaXY d n x y := deltaXY_pos d n hd (by omega) x y hx hy hxy
  have hD1 : 1 ≤ DeltaXY d n x y := one_le_deltaXY d n hd (by omega) x y hx hy hxy
  have hG0pos : 0 < (gcdMinors2 x y).natAbs := by
    have h : 0 < gcdMinors2 x y := DGG.gcdMinors2_pos x y hxy
    omega
  have hG1 : 1 ≤ mixG d n x y := by rw [mixG]; exact_mod_cast hG0pos
  have hGpos : 0 < mixG d n x y := lt_of_lt_of_le zero_lt_one hG1
  have hDG1 : 1 ≤ DeltaXY d n x y * mixG d n x y := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ DeltaXY d n x y * mixG d n x y := mul_le_mul hD1 hG1 zero_le_one (by linarith)
  have hKpos : 0 < mixK d n A B x y := by
    rw [mixK]
    have h1 : 0 < A ^ (NN d n - 2) := pow_pos hApos _
    have h2 : 0 < Real.log B * (bigW (wOf B) : ℝ) * eNorm (veronese d n x) := by positivity
    exact div_pos (by positivity) h2
  have hLpos : 0 < mixL d n A B x y := by
    rw [mixL]; exact div_pos (mul_pos hKpos hGpos) hzzpos
  have hLnn : 0 ≤ mixL d n A B x y := le_of_lt hLpos
  have hLexpr : mixL d n A B x y
      = A ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y
          * (((gcdMinors2 x y).natAbs : ℕ) : ℝ)
          / (Real.log B * (bigW (wOf B) : ℝ) * eNorm (veronese d n x) * zetaR (NN d n - 2)) := by
    rw [mixL, mixK, mixG]; ring
  -- pointwise structural bounds on the `ℓ`-dependent factors
  have hHle : ∀ ℓ : ℕ, mixH d n B x y ℓ ≤ mixG d n x y := by
    intro ℓ
    rw [mixH, mixG]
    exact_mod_cast (Nat.le_of_dvd hG0pos
      (Nat.gcd_dvd_right (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))) ((gcdMinors2 x y).natAbs)))
  have hHnn : ∀ ℓ : ℕ, 0 ≤ mixH d n B x y ℓ := by
    intro ℓ; rw [mixH]; exact_mod_cast Nat.zero_le _
  have hgle : ∀ ℓ : ℕ, 1 ≤ ℓ → mixg d n B ℓ ≤ (ℓ : ℝ) := by
    intro ℓ hℓ1
    rw [mixg]
    exact_mod_cast (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left ℓ (bigW (wOf B))))
  have hgnn : ∀ ℓ : ℕ, 0 ≤ mixg d n B ℓ := by
    intro ℓ; rw [mixg]; exact_mod_cast Nat.zero_le _
  have hQle : ∀ ℓ : ℕ, mixQ d n B ℓ ≤ (bigW (wOf B) : ℝ) := by
    intro ℓ; rw [mixQ]; exact_mod_cast Nat.div_le_self _ _
  have hQnn : ∀ ℓ : ℕ, 0 ≤ mixQ d n B ℓ := by
    intro ℓ; rw [mixQ]; exact_mod_cast Nat.zero_le _
  have hQcast : ∀ ℓ : ℕ, mixQ d n B ℓ = (bigW (wOf B) : ℝ) / mixg d n B ℓ := by
    intro ℓ
    have hgne : ((Nat.gcd ℓ (bigW (wOf B)) : ℕ) : ℝ) ≠ 0 := by
      have h1 : 0 < Nat.gcd ℓ (bigW (wOf B)) :=
        Nat.gcd_pos_of_pos_right ℓ (by have h := one_le_bigW (wOf B); omega)
      exact_mod_cast (show Nat.gcd ℓ (bigW (wOf B)) ≠ 0 by omega)
    rw [mixQ, mixg, Nat.cast_div (Nat.gcd_dvd_right ℓ (bigW (wOf B))) hgne]
  set L0 : ℕ := ⌊A / ((bigW (wOf B) : ℝ) * lamX d n x)⌋₊ with hL0
  -- `λ(x) W ≤ A^{3/4}` gives `A^{1/4} ≤ A/(Wλ)`, and `wOf B + 1 ≤ B^{5/24} ≤ A^{1/4}`, so `w ≤ L0`
  have hwL0 : wOf B ≤ (L0 : ℝ) := by
    have hB524 : B ^ ((5 : ℝ) / 24) ≤ A ^ ((1 : ℝ) / 4) := by
      have h := Real.rpow_le_rpow (x := B ^ ((5 : ℝ) / 6)) (y := A) (z := (1 : ℝ) / 4)
        (Real.rpow_nonneg hBpos.le _) hBA (by norm_num)
      rw [← Real.rpow_mul hBpos.le] at h
      rw [show ((5 : ℝ) / 6) * (1 / 4) = 5 / 24 by norm_num] at h
      exact h
    have hA14 : wOf B + 1 ≤ A ^ ((1 : ℝ) / 4) := le_trans hwBd hB524
    have hfrac : A ^ ((1 : ℝ) / 4) ≤ A / ((bigW (wOf B) : ℝ) * lamX d n x) := by
      rw [le_div_iff₀ (by positivity)]
      calc A ^ ((1 : ℝ) / 4) * ((bigW (wOf B) : ℝ) * lamX d n x)
          ≤ A ^ ((1 : ℝ) / 4) * A ^ ((3 : ℝ) / 4) :=
            mul_le_mul_of_nonneg_left hWlam (Real.rpow_nonneg hApos.le _)
        _ = A := by
            rw [← Real.rpow_add hApos, show (1 : ℝ) / 4 + 3 / 4 = 1 by norm_num, Real.rpow_one]
    have hfl : ((⌊A ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℝ) ≤ (L0 : ℝ) := by
      rw [hL0]
      exact_mod_cast Nat.floor_mono hfrac
    have hwfl : wOf B ≤ ((⌊A ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℝ) := by
      have hlt : A ^ ((1 : ℝ) / 4) < ((⌊A ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      linarith
    exact le_trans hwfl hfl
  have hL0ge1 : (1 : ℝ) ≤ (L0 : ℝ) := by
    have : (2 : ℝ) ≤ (L0 : ℝ) := le_trans hw2 hwL0
    linarith
  -- per-`ℓ` estimate from `Sk1_mix_ell`
  have hper : ∀ ℓ ∈ Finset.Icc 1 L0,
      |Sk d n 1 (GamMix d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
          (TmixSet d n y (A / (ℓ : ℝ)) (Real.log B)) - mixPerMain d n A B x y ℓ|
        ≤ mixPerErr d n Csk A B x y ℓ := by
    intro ℓ hℓmem
    obtain ⟨hℓ1, hℓL0⟩ := Finset.mem_Icc.mp hℓmem
    have hℓpos : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ1
    have hℓL0R : (ℓ : ℝ) ≤ L0 := by exact_mod_cast hℓL0
    have hℓAW : (ℓ : ℝ) ≤ A / ((bigW (wOf B) : ℝ) * lamX d n x) := by
      rw [hL0] at hℓL0R
      exact le_trans hℓL0R (Nat.floor_le (by positivity))
    have hℓWlam : (ℓ : ℝ) * ((bigW (wOf B) : ℝ) * lamX d n x) ≤ A :=
      (le_div_iff₀ (by positivity)).mp hℓAW
    have hQ1 : 1 ≤ bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B)) := by
      rw [Nat.le_div_iff_mul_le (Nat.gcd_pos_of_pos_right ℓ (by have h := one_le_bigW (wOf B); omega))]
      simpa using Nat.le_of_dvd (by have h := one_le_bigW (wOf B); omega)
        (Nat.gcd_dvd_right ℓ (bigW (wOf B)))
    have hQT : ((bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B)) : ℕ) : ℝ) * lamX d n x ≤ A / (ℓ : ℝ) := by
      rw [le_div_iff₀ hℓpos]
      have hQle' : ((bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B)) : ℕ) : ℝ) ≤ (bigW (wOf B) : ℝ) := by
        exact_mod_cast Nat.div_le_self _ _
      calc ((bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B)) : ℕ) : ℝ) * lamX d n x * (ℓ : ℝ)
          ≤ (bigW (wOf B) : ℝ) * lamX d n x * (ℓ : ℝ) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hQle' (le_of_lt hlampos))
              (le_of_lt hℓpos)
        _ = (ℓ : ℝ) * ((bigW (wOf B) : ℝ) * lamX d n x) := by ring
        _ ≤ A := hℓWlam
    have hres := hSk x y hx hy hxy (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B)))
      (Real.log B) (A / (ℓ : ℝ)) hQ1 halpos hQT
    simpa only [mixPerMain, mixPerErr, mixE1, mixE2, mixE3, mixH, mixQ]
      using hres
  -- the exact per-`ℓ` main-term identity
  have hid : ∀ ℓ : ℕ, 1 ≤ ℓ →
      (1 / (ℓ : ℝ)) * mixPerMain d n A B x y ℓ
        = mixK d n A B x y * (mixH d n B x y ℓ * mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1)) := by
    intro ℓ hℓ1
    have hℓpos : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ1
    have hℓne : (ℓ : ℝ) ≠ 0 := ne_of_gt hℓpos
    have hgne : mixg d n B ℓ ≠ 0 := by
      rw [mixg]
      have h1 : 0 < Nat.gcd ℓ (bigW (wOf B)) :=
        Nat.gcd_pos_of_pos_right ℓ (by have h := one_le_bigW (wOf B); omega)
      exact_mod_cast (show Nat.gcd ℓ (bigW (wOf B)) ≠ 0 by omega)
    rw [mixPerMain, mixK, mixH]
    exact mix_per_ell_main_eq A (Real.log B) (bigW (wOf B) : ℝ) (mixQ d n B ℓ) (mixg d n B ℓ)
      (mixH d n B x y ℓ) (ballVol (NN d n - 2)) (DeltaXY d n x y) (eNorm (veronese d n x))
      (ℓ : ℝ) (NN d n) (by omega) hℓne halne hWne (hQcast ℓ) hgne (ne_of_gt hEpos)
  have hsumId : (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixPerMain d n A B x y ℓ)
      = mixK d n A B x y * (∑ ℓ ∈ Finset.Icc 1 L0,
          mixH d n B x y ℓ * mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ℓ hℓ => hid ℓ (Finset.mem_Icc.mp hℓ).1)
  have hsumBnd : (∑ ℓ ∈ Finset.Icc 1 L0,
        mixH d n B x y ℓ * mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1)) ≤ 2 * mixG d n x y := by
    have hpt : ∀ ℓ ∈ Finset.Icc 1 L0,
        mixH d n B x y ℓ * mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1)
          ≤ mixG d n x y / (ℓ : ℝ) ^ (NN d n - 2) := by
      intro ℓ hℓ
      have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
      have hℓpos : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ1
      have hHg : mixH d n B x y ℓ * mixg d n B ℓ ≤ mixG d n x y * (ℓ : ℝ) := by
        have h1 := hHle ℓ
        have h2 := hgle ℓ hℓ1
        nlinarith [hHnn ℓ, hgnn ℓ, hGpos]
      have hsplit : (ℓ : ℝ) ^ (NN d n - 1) = (ℓ : ℝ) ^ (NN d n - 2) * (ℓ : ℝ) := by
        rw [show NN d n - 1 = (NN d n - 2) + 1 by omega, pow_add, pow_one]
      have hp : 0 < (ℓ : ℝ) ^ (NN d n - 2) := by positivity
      rw [hsplit, div_le_div_iff₀ (by positivity) (by positivity)]
      calc mixH d n B x y ℓ * mixg d n B ℓ * (ℓ : ℝ) ^ (NN d n - 2)
          ≤ (mixG d n x y * (ℓ : ℝ)) * (ℓ : ℝ) ^ (NN d n - 2) :=
            mul_le_mul_of_nonneg_right hHg (le_of_lt hp)
        _ = mixG d n x y * ((ℓ : ℝ) ^ (NN d n - 2) * (ℓ : ℝ)) := by ring
    calc (∑ ℓ ∈ Finset.Icc 1 L0,
          mixH d n B x y ℓ * mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1))
        ≤ ∑ ℓ ∈ Finset.Icc 1 L0, mixG d n x y / (ℓ : ℝ) ^ (NN d n - 2) :=
          Finset.sum_le_sum hpt
      _ = mixG d n x y * (∑ ℓ ∈ Finset.Icc 1 L0, 1 / (ℓ : ℝ) ^ (NN d n - 2)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun ℓ _ => by ring)
      _ ≤ mixG d n x y * 2 :=
          mul_le_mul_of_nonneg_left (ss1_sum_inv_pow_le L0 (NN d n - 2) (by omega)) (le_of_lt hGpos)
      _ = 2 * mixG d n x y := by ring
  have hS1 : (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixE1 d n Csk A B x y ℓ)
      ≤ 2 * Csk * zetaR (NN d n - 2) * mixL d n A B x y
          * min 1 (DeltaXY d n x y ^ 2 / (Real.log B) ^ 2) := by
    have hstep : (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixE1 d n Csk A B x y ℓ)
        = Csk * min 1 (DeltaXY d n x y ^ 2 / (Real.log B) ^ 2)
            * (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixPerMain d n A B x y ℓ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ℓ _ => ?_)
      rw [mixE1]; ring
    rw [hstep, hsumId]
    have hminnn : 0 ≤ min 1 (DeltaXY d n x y ^ 2 / (Real.log B) ^ 2) :=
      le_min zero_le_one (by positivity)
    have hkey : Csk * min 1 (DeltaXY d n x y ^ 2 / (Real.log B) ^ 2)
          * (mixK d n A B x y * (2 * mixG d n x y))
        = 2 * Csk * zetaR (NN d n - 2) * mixL d n A B x y
          * min 1 (DeltaXY d n x y ^ 2 / (Real.log B) ^ 2) := by
      have hzzn : zetaR (NN d n - 2) ≠ 0 := ne_of_gt hzzpos
      rw [mixL]; field_simp; try ring
    rw [← hkey]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (le_of_lt hCskpos) hminnn)
    exact mul_le_mul_of_nonneg_left hsumBnd (le_of_lt hKpos)
  have hS2 : (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixE2 d n Csk A B x y ℓ)
      ≤ K2 * mixL d n A B x y / Real.log A := by
    have hsum := hE2le A B hB2' hBA hAB2 x y hx hy hxy hnx hWlam
    rw [← hLexpr] at hsum
    refine le_trans ?_ hsum
    have hpt : ∀ ℓ ∈ Finset.Icc 1 L0,
        (1 / (ℓ : ℝ)) * mixE2 d n Csk A B x y ℓ
          ≤ Csk * A ^ (NN d n - 3) * lamX d n x * mixH d n B x y ℓ
              / ((ℓ : ℝ) ^ (NN d n - 2) * eNorm (veronese d n x)) := by
      intro ℓ hℓ
      have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
      have hℓpos : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ1
      have hne : ((ℓ : ℝ) ^ (NN d n - 3)) ≠ 0 := by positivity
      have heq : (1 / (ℓ : ℝ)) * mixE2 d n Csk A B x y ℓ
          = Csk * A ^ (NN d n - 3) * lamX d n x * mixH d n B x y ℓ
              / ((ℓ : ℝ) ^ (NN d n - 2) * eNorm (veronese d n x)) := by
        rw [mixE2, div_pow]
        rw [show (ℓ : ℝ) ^ (NN d n - 2) = (ℓ : ℝ) ^ (NN d n - 3) * (ℓ : ℝ) by
          rw [show NN d n - 2 = (NN d n - 3) + 1 by omega, pow_add, pow_one]]
        field_simp
      rw [heq]
    calc (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixE2 d n Csk A B x y ℓ)
        ≤ ∑ ℓ ∈ Finset.Icc 1 L0,
            Csk * A ^ (NN d n - 3) * lamX d n x * mixG d n x y
              / ((ℓ : ℝ) ^ (NN d n - 2) * eNorm (veronese d n x)) := by
          refine Finset.sum_le_sum (fun ℓ hℓ => le_trans (hpt ℓ hℓ) ?_)
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact hHle ℓ
      _ = Csk * A ^ (NN d n - 3) * lamX d n x * mixG d n x y / eNorm (veronese d n x)
            * (∑ ℓ ∈ Finset.Icc 1 L0, 1 / (ℓ : ℝ) ^ (NN d n - 2)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun ℓ hℓ => ?_)
          have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
          have hℓpos : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ1
          have hne : ((ℓ : ℝ) ^ (NN d n - 2)) ≠ 0 := by positivity
          field_simp
      _ ≤ Csk * A ^ (NN d n - 3) * lamX d n x * mixG d n x y / eNorm (veronese d n x) * 2 :=
          mul_le_mul_of_nonneg_left (ss1_sum_inv_pow_le L0 (NN d n - 2) (by omega))
            (by positivity)
      _ = (2 * Csk) * (A ^ (NN d n - 3) * lamX d n x
            * (((gcdMinors2 x y).natAbs : ℕ) : ℝ) / eNorm (veronese d n x)) := by
          rw [mixG]; ring
  have hS3 : (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixE3 d n Csk A B x y ℓ)
      ≤ K3 * mixL d n A B x y / Real.log A := by
    have hsum := hS1le A B hB3' hBA hAB2 x y hx hy hxy hnx hWlam
    rw [← hLexpr] at hsum
    refine le_trans ?_ hsum
    have hmono : ∀ ℓ ∈ Finset.Icc 1 L0,
        (1 / (ℓ : ℝ)) * mixE3 d n Csk A B x y ℓ
          ≤ (1 / (ℓ : ℝ)) * (Csk * S1ball d n x ((bigW (wOf B) : ℝ) * lamX d n x)) := by
      intro ℓ hℓ
      have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
      have hℓpos : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ1
      rw [mixE3]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hCskpos)
      exact ss1_S1ball_mono d n x (by nlinarith [hQle ℓ, hlampos])
    refine le_trans (Finset.sum_le_sum hmono) ?_
    have hharm : (∑ ℓ ∈ Finset.Icc 1 L0, (1 : ℝ) / (ℓ : ℝ)) ≤ 1 + Real.log A := by
      have hlogL0 : Real.log ((L0 : ℕ) : ℝ) ≤ Real.log A := by
        rcases Nat.eq_zero_or_pos L0 with h0 | h0
        · rw [h0, Nat.cast_zero, Real.log_zero]
          linarith [hlogA1]
        · refine Real.log_le_log (by exact_mod_cast h0) ?_
          rw [hL0]
          refine le_trans (Nat.floor_le (by positivity)) ?_
          rw [div_le_iff₀ (by positivity)]
          nlinarith [hT1, hApos]
      have h1 := ss1_sum_Icc_inv_le L0
      linarith
    rw [← Finset.sum_mul]
    calc (∑ ℓ ∈ Finset.Icc 1 L0, (1 : ℝ) / (ℓ : ℝ))
          * (Csk * S1ball d n x ((bigW (wOf B) : ℝ) * lamX d n x))
        ≤ (1 + Real.log A) * (Csk * S1ball d n x ((bigW (wOf B) : ℝ) * lamX d n x)) :=
          mul_le_mul_of_nonneg_right hharm (mul_nonneg hCsknn (S1ball_nonneg d n x _))
      _ = Csk * S1ball d n x ((bigW (wOf B) : ℝ) * lamX d n x) * (1 + Real.log A) := by ring
  -- the Möbius comparison
  have hKnn : 0 ≤ mixK d n A B x y := le_of_lt hKpos
  have hGnn : 0 ≤ mixG d n x y := le_of_lt hGpos
  have hζnn : 0 ≤ zetaR (NN d n - 2) := le_of_lt hzzpos
  have hLkey : mixL d n A B x y
      = A ^ (NN d n - 2) * ballVol (NN d n - 2) * eNorm (veronese d n y)
          / (Real.log B * (bigW (wOf B) : ℝ) * detL (Gam d n x y) * zetaR (NN d n - 2)) := by
    have hGcast : (((gcdMinors2 x y).natAbs : ℕ) : ℝ) = (gcdMinors2 x y : ℝ) :=
      natAbs_cast_of_nonneg _ (int_finset_gcd_nonneg _ _)
    have hD := DeltaXY_gcd_detL d n hd (by omega) x y hx hy hxy
    rw [mixL, mixK, mixG, hGcast]
    have h1 : A ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y
          / (Real.log B * (bigW (wOf B) : ℝ) * eNorm (veronese d n x))
          * (gcdMinors2 x y : ℝ) / zetaR (NN d n - 2)
        = A ^ (NN d n - 2) * ballVol (NN d n - 2)
            * (DeltaXY d n x y * (gcdMinors2 x y : ℝ))
          / (Real.log B * (bigW (wOf B) : ℝ) * eNorm (veronese d n x)
              * zetaR (NN d n - 2)) := by ring
    rw [h1, hD]
    field_simp
  have hloc : mixL d n A B x y = mixMain d n A B (x, y) := by
    have hS : zetaR (NN d n - 2) = ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (NN d n - 2) := rfl
    have hSne : (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (NN d n - 2)) ≠ 0 := ne_of_gt hzzpos
    have hι : 8 * iotaDN d n = ballVol (NN d n - 2) / zetaR (NN d n - 2) := by
      rw [iotaDN, hS]
      field_simp
    have hdet : detL (Gam d n x y) ≠ 0 := by
      have h := Lat.detL_ge_one (Gam d n x y); linarith
    rw [hLkey, mixMain, hι]
    field_simp
  have herrXYnn : 0 ≤ errXY d n B x y := by
    rw [errXY]
    by_cases h : (gcdMinors2 x y) ∣ ((bigW (wOf B) / radW (wOf B) : ℕ) : ℤ)
    · rw [if_pos h]
      linarith [le_min zero_le_one
        (by positivity : (0 : ℝ) ≤ DeltaXY d n x y ^ 2 / (Real.log B) ^ 2)]
    · rw [if_neg h]
      linarith [le_min zero_le_one
        (by positivity : (0 : ℝ) ≤ DeltaXY d n x y ^ 2 / (Real.log B) ^ 2)]
  have herrmin : min 1 (DeltaXY d n x y ^ 2 / (Real.log B) ^ 2) ≤ errXY d n B x y := by
    rw [errXY]
    by_cases h : (gcdMinors2 x y) ∣ ((bigW (wOf B) / radW (wOf B) : ℕ) : ℤ)
    · rw [if_pos h]; linarith
    · rw [if_neg h]; linarith
  have hTEq : (∑ ℓ ∈ Finset.Icc 1 L0,
        ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) * mixPerMain d n A B x y ℓ)
      = mixK d n A B x y * (∑ ℓ ∈ Finset.Icc 1 L0,
          (ArithmeticFunction.moebius ℓ : ℝ) * (mixH d n B x y ℓ * mixg d n B ℓ
            / (ℓ : ℝ) ^ (NN d n - 1))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ℓ hℓ => ?_)
    rw [show (ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) * mixPerMain d n A B x y ℓ
        = (ArithmeticFunction.moebius ℓ : ℝ) * ((1 / (ℓ : ℝ)) * mixPerMain d n A B x y ℓ)
        from by ring,
      hid ℓ (Finset.mem_Icc.mp hℓ).1]
    ring
  have hmob_bad : ¬ ((gcdMinors2 x y) ∣ ((bigW (wOf B) / radW (wOf B) : ℕ) : ℤ)) →
      |mixK d n A B x y * (∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
            * (mixH d n B x y ℓ * mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1)))
          - mixL d n A B x y| ≤ 3 * zetaR (NN d n - 2) * mixL d n A B x y := by
    intro _
    have h1 : |(∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
            * (mixH d n B x y ℓ * mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1)))|
        ≤ 2 * mixG d n x y := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hpt : ∀ ℓ ∈ Finset.Icc 1 L0,
          |(ArithmeticFunction.moebius ℓ : ℝ)
              * (mixH d n B x y ℓ * mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1))|
            ≤ mixG d n x y / (ℓ : ℝ) ^ (NN d n - 2) := by
        intro ℓ hℓ
        have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
        have hℓpos : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ1
        have hp : 0 < (ℓ : ℝ) ^ (NN d n - 2) := by positivity
        have hmu1 : |(ArithmeticFunction.moebius ℓ : ℝ)| ≤ 1 :=
          MDEstimates.moebius_abs_cast_le_one ℓ
        have hHg : mixH d n B x y ℓ * mixg d n B ℓ ≤ mixG d n x y * (ℓ : ℝ) := by
          have h2 := hHle ℓ
          have h3 := hgle ℓ hℓ1
          nlinarith [hHnn ℓ, hgnn ℓ, hGpos]
        have hsplit : (ℓ : ℝ) ^ (NN d n - 1) = (ℓ : ℝ) ^ (NN d n - 2) * (ℓ : ℝ) := by
          rw [show NN d n - 1 = (NN d n - 2) + 1 by omega, pow_add, pow_one]
        rw [hsplit, abs_mul]
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ mixH d n B x y ℓ * mixg d n B ℓ
          / ((ℓ : ℝ) ^ (NN d n - 2) * (ℓ : ℝ)))]
        calc |(ArithmeticFunction.moebius ℓ : ℝ)|
              * (mixH d n B x y ℓ * mixg d n B ℓ
                / ((ℓ : ℝ) ^ (NN d n - 2) * (ℓ : ℝ)))
            ≤ 1 * (mixH d n B x y ℓ * mixg d n B ℓ
                / ((ℓ : ℝ) ^ (NN d n - 2) * (ℓ : ℝ))) :=
              mul_le_mul_of_nonneg_right hmu1 (by positivity)
          _ = mixH d n B x y ℓ * mixg d n B ℓ
                / ((ℓ : ℝ) ^ (NN d n - 2) * (ℓ : ℝ)) := by rw [one_mul]
          _ ≤ mixG d n x y / (ℓ : ℝ) ^ (NN d n - 2) := by
              rw [div_le_div_iff₀ (by positivity) (by positivity)]
              have hm := mul_le_mul_of_nonneg_right hHg (le_of_lt hp)
              nlinarith [hm]
      calc (∑ ℓ ∈ Finset.Icc 1 L0,
            |(ArithmeticFunction.moebius ℓ : ℝ)
              * (mixH d n B x y ℓ * mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1))|)
          ≤ ∑ ℓ ∈ Finset.Icc 1 L0, mixG d n x y / (ℓ : ℝ) ^ (NN d n - 2) :=
            Finset.sum_le_sum hpt
        _ = mixG d n x y * (∑ ℓ ∈ Finset.Icc 1 L0, 1 / (ℓ : ℝ) ^ (NN d n - 2)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun ℓ _ => by ring)
        _ ≤ mixG d n x y * 2 :=
            mul_le_mul_of_nonneg_left (ss1_sum_inv_pow_le L0 (NN d n - 2) (by omega)) (le_of_lt hGpos)
        _ = 2 * mixG d n x y := by ring
    have h3 : |(∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
            * (mixH d n B x y ℓ * mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1)))
          - mixG d n x y / zetaR (NN d n - 2)| ≤ 3 * mixG d n x y := by
      have h2 : mixG d n x y / zetaR (NN d n - 2) ≤ mixG d n x y := by
        rw [div_le_iff₀ hzzpos]; nlinarith [hGpos, hzz1]
      have habs : |(∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
            * (mixH d n B x y ℓ * mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1)))
            - mixG d n x y / zetaR (NN d n - 2)|
          ≤ |(∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
              * (mixH d n B x y ℓ * mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1)))|
            + |mixG d n x y / zetaR (NN d n - 2)| := by
        rw [sub_eq_add_neg]
        exact le_trans (abs_add_le _ _) (le_of_eq (by rw [abs_neg]))
      calc |(∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
            * (mixH d n B x y ℓ * mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1)))
            - mixG d n x y / zetaR (NN d n - 2)| ≤ _ := habs
        _ = |(∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
              * (mixH d n B x y ℓ * mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1)))|
            + mixG d n x y / zetaR (NN d n - 2) := by
            rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ mixG d n x y / zetaR (NN d n - 2))]
        _ ≤ 2 * mixG d n x y + mixG d n x y := by linarith
        _ = 3 * mixG d n x y := by ring
    rw [mixL]
    rw [show mixK d n A B x y * (∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
          * (mixH d n B x y ℓ * mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1)))
          - mixK d n A B x y * mixG d n x y / zetaR (NN d n - 2)
        = mixK d n A B x y * ((∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
            * (mixH d n B x y ℓ * mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1)))
          - mixG d n x y / zetaR (NN d n - 2)) from by ring]
    rw [abs_mul, abs_of_pos hKpos]
    calc mixK d n A B x y * |(∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
            * (mixH d n B x y ℓ * mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1)))
          - mixG d n x y / zetaR (NN d n - 2)|
        ≤ mixK d n A B x y * (3 * mixG d n x y) :=
          mul_le_mul_of_nonneg_left h3 hKnn
      _ = 3 * zetaR (NN d n - 2) * (mixK d n A B x y * mixG d n x y
            / zetaR (NN d n - 2)) := by
          field_simp
  have hmob_good : ((gcdMinors2 x y) ∣ ((bigW (wOf B) / radW (wOf B) : ℕ) : ℤ)) →
      |mixK d n A B x y * (∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
            * (mixH d n B x y ℓ * mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1)))
          - mixL d n A B x y| ≤ mixL d n A B x y / Real.log A := by
    intro hgood
    have hgoodG : (gcdMinors2 x y).natAbs ∣ (bigW (wOf B) / radW (wOf B)) := by
      have h := Int.natAbs_dvd_natAbs.mpr hgood
      have h' : ((gcdMinors2 x y).natAbs : ℤ)
          ∣ (((bigW (wOf B) / radW (wOf B) : ℕ)) : ℤ) := by
        simpa [Int.natAbs_natCast] using h
      exact_mod_cast h'
    have hT2 : (∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
          * (mixH d n B x y ℓ * mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1)))
        = mixG d n x y * (∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
            * (mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ℓ _ => ?_)
      by_cases hmu : ArithmeticFunction.moebius ℓ = 0
      · rw [hmu]; ring
      · have hsq : Squarefree ℓ := (ArithmeticFunction.moebius_ne_zero_iff_squarefree).mp hmu
        have hgcd := gcd_div_gcd_eq (wOf B) ℓ ((gcdMinors2 x y).natAbs) hsq hgoodG
        rw [mixH, mixG, hgcd]
        ring
    have hZapp := hZ (wOf B) (L0 : ℝ) hw1 hL0ge1
    have hmin : min (L0 : ℝ) (wOf B) = wOf B := min_eq_right hwL0
    have hZapp' : |(∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
          * (mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1))) - 1 / zetaR (NN d n - 2)|
        ≤ Cz / (wOf B) ^ (NN d n - 3) := by
      have h := hZapp
      rw [hmin] at h
      have h1 : (∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
            * (((Nat.gcd ℓ (bigW (wOf B)) : ℕ) : ℝ) ^ 1) / (ℓ : ℝ) ^ ((NN d n - 2) + 1))
          = (∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
            * (mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1))) := by
        refine Finset.sum_congr rfl (fun ℓ _ => ?_)
        rw [mixg, pow_one, show (NN d n - 2) + 1 = NN d n - 1 by omega]
        ring
      rw [Nat.floor_natCast] at h
      rw [h1] at h
      rw [show (NN d n - 2) - 1 = NN d n - 3 by omega] at h
      exact h
    have hkey : zetaR (NN d n - 2) * Cz * Real.log A ≤ (wOf B) ^ (NN d n - 3) := by
      have h1 : zetaR (NN d n - 2) * Cz ≤ K0 := hK0Cz
      calc zetaR (NN d n - 2) * Cz * Real.log A ≤ K0 * Real.log A :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hlogApos)
        _ ≤ (wOf B) ^ (NN d n - 3) := har9
    have hwpos : 0 < (wOf B) ^ (NN d n - 3) := pow_pos (lt_of_lt_of_le zero_lt_one hw1) _
    have hfin : Cz / (wOf B) ^ (NN d n - 3) ≤ 1 / (zetaR (NN d n - 2) * Real.log A) := by
      rw [div_le_div_iff₀ hwpos (by positivity)]
      nlinarith [hkey, hzzpos, hlogApos]
    have hKGnn : 0 ≤ mixK d n A B x y * mixG d n x y := mul_nonneg hKnn hGnn
    rw [hT2, mixL]
    rw [show mixK d n A B x y * (mixG d n x y * (∑ ℓ ∈ Finset.Icc 1 L0,
            (ArithmeticFunction.moebius ℓ : ℝ) * (mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1))))
          - mixK d n A B x y * mixG d n x y / zetaR (NN d n - 2)
        = mixK d n A B x y * mixG d n x y * ((∑ ℓ ∈ Finset.Icc 1 L0,
            (ArithmeticFunction.moebius ℓ : ℝ) * (mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1)))
          - 1 / zetaR (NN d n - 2)) from by ring]
    rw [abs_mul, abs_mul, abs_of_pos hKpos, abs_of_pos hGpos]
    calc mixK d n A B x y * mixG d n x y
          * |(∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
              * (mixg d n B ℓ / (ℓ : ℝ) ^ (NN d n - 1))) - 1 / zetaR (NN d n - 2)|
        ≤ mixK d n A B x y * mixG d n x y * (Cz / (wOf B) ^ (NN d n - 3)) :=
          mul_le_mul_of_nonneg_left hZapp' hKGnn
      _ ≤ mixK d n A B x y * mixG d n x y * (1 / (zetaR (NN d n - 2) * Real.log A)) :=
          mul_le_mul_of_nonneg_left hfin hKGnn
      _ = mixK d n A B x y * mixG d n x y / zetaR (NN d n - 2) / Real.log A := by
          field_simp
  have hmain : |(∑ ℓ ∈ Finset.Icc 1 L0,
          ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) * mixPerMain d n A B x y ℓ)
        - mixL d n A B x y|
      ≤ mixL d n A B x y / Real.log A + 3 * zetaR (NN d n - 2) * mixL d n A B x y
          * errXY d n B x y := by
    rw [hTEq]
    by_cases hgood : (gcdMinors2 x y) ∣ ((bigW (wOf B) / radW (wOf B) : ℕ) : ℤ)
    · refine le_trans (hmob_good hgood) ?_
      have h3 : 0 ≤ 3 * zetaR (NN d n - 2) * mixL d n A B x y * errXY d n B x y :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hζnn) hLnn) herrXYnn
      linarith
    · have herr1 : 1 ≤ errXY d n B x y := by
        rw [errXY, if_neg hgood]
        have h1 : 0 ≤ min 1 (DeltaXY d n x y ^ 2 / (Real.log B) ^ 2) :=
          le_min zero_le_one (by positivity)
        linarith
      refine le_trans (hmob_bad hgood) ?_
      have hLζ : 0 ≤ 3 * zetaR (NN d n - 2) * mixL d n A B x y :=
        mul_nonneg (mul_nonneg (by norm_num) hζnn) hLnn
      have hstep : 3 * zetaR (NN d n - 2) * mixL d n A B x y
          ≤ 3 * zetaR (NN d n - 2) * mixL d n A B x y * errXY d n B x y := by
        calc 3 * zetaR (NN d n - 2) * mixL d n A B x y
            = 3 * zetaR (NN d n - 2) * mixL d n A B x y * 1 := (mul_one _).symm
          _ ≤ 3 * zetaR (NN d n - 2) * mixL d n A B x y * errXY d n B x y :=
              mul_le_mul_of_nonneg_left herr1 hLζ
      have h1 : 0 ≤ mixL d n A B x y / Real.log A := div_nonneg hLnn (le_of_lt hlogApos)
      linarith
  have hstep1 : |(∑ ℓ ∈ Finset.Icc 1 L0,
        ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) *
          Sk d n 1 (GamMix d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
            (TmixSet d n y (A / (ℓ : ℝ)) (Real.log B)))
        - (∑ ℓ ∈ Finset.Icc 1 L0,
          ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) * mixPerMain d n A B x y ℓ)|
      ≤ ∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixPerErr d n Csk A B x y ℓ := by
    refine le_trans (abs_sum_sub_le (Finset.Icc 1 L0)
      (fun ℓ => ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) *
        Sk d n 1 (GamMix d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
          (TmixSet d n y (A / (ℓ : ℝ)) (Real.log B)))
      (fun ℓ => ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) * mixPerMain d n A B x y ℓ)) ?_
    refine Finset.sum_le_sum (fun ℓ hℓ => ?_)
    have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
    have hℓpos : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ1
    have hmu1 : |(ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)| ≤ 1 / (ℓ : ℝ) := by
      rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (ℓ : ℝ))]
      exact div_le_div_of_nonneg_right (MDEstimates.moebius_abs_cast_le_one ℓ) (by positivity)
    rw [show ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) *
          Sk d n 1 (GamMix d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
            (TmixSet d n y (A / (ℓ : ℝ)) (Real.log B))
        - ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) * mixPerMain d n A B x y ℓ
        = ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ))
          * (Sk d n 1 (GamMix d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
              (TmixSet d n y (A / (ℓ : ℝ)) (Real.log B))
            - mixPerMain d n A B x y ℓ) from by ring]
    rw [abs_mul]
    exact mul_le_mul hmu1 (hper ℓ hℓ) (abs_nonneg _) (by positivity)
  have hAbsS : (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixPerErr d n Csk A B x y ℓ)
      = (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixE1 d n Csk A B x y ℓ)
        + (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixE2 d n Csk A B x y ℓ)
        + (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixE3 d n Csk A B x y ℓ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    rw [mixPerErr]; ring
  have hAbsBd : (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixPerErr d n Csk A B x y ℓ)
      ≤ 2 * Csk * zetaR (NN d n - 2) * mixL d n A B x y * errXY d n B x y
        + (K2 + K3) * mixL d n A B x y / Real.log A := by
    rw [hAbsS]
    have h1 : (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixE1 d n Csk A B x y ℓ)
        ≤ 2 * Csk * zetaR (NN d n - 2) * mixL d n A B x y * errXY d n B x y := by
      refine le_trans hS1 ?_
      refine mul_le_mul_of_nonneg_left herrmin ?_
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCsknn) hζnn) hLnn
    have h23 : (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixE2 d n Csk A B x y ℓ)
        + (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixE3 d n Csk A B x y ℓ)
        ≤ K2 * mixL d n A B x y / Real.log A + K3 * mixL d n A B x y / Real.log A :=
      add_le_add hS2 hS3
    calc (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixE1 d n Csk A B x y ℓ)
          + (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixE2 d n Csk A B x y ℓ)
          + (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixE3 d n Csk A B x y ℓ)
        = (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixE1 d n Csk A B x y ℓ)
          + ((∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixE2 d n Csk A B x y ℓ)
            + (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixE3 d n Csk A B x y ℓ)) := by ring
      _ ≤ 2 * Csk * zetaR (NN d n - 2) * mixL d n A B x y * errXY d n B x y
            + (K2 * mixL d n A B x y / Real.log A
              + K3 * mixL d n A B x y / Real.log A) := add_le_add h1 h23
      _ = 2 * Csk * zetaR (NN d n - 2) * mixL d n A B x y * errXY d n B x y
            + (K2 + K3) * mixL d n A B x y / Real.log A := by ring
  have hAD : 2 * Csk * zetaR (NN d n - 2) * mixL d n A B x y * errXY d n B x y
      + 3 * zetaR (NN d n - 2) * mixL d n A B x y * errXY d n B x y
      ≤ CC * mixL d n A B x y * errXY d n B x y := by
    rw [hCCdef]
    have hcoef : 2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2)
        ≤ 2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2) + K2 + K3 + 1 := by
      linarith [hK2pos, hK3pos]
    calc 2 * Csk * zetaR (NN d n - 2) * mixL d n A B x y * errXY d n B x y
          + 3 * zetaR (NN d n - 2) * mixL d n A B x y * errXY d n B x y
        = (2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2))
          * (mixL d n A B x y * errXY d n B x y) := by ring
      _ ≤ (2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2) + K2 + K3 + 1)
          * (mixL d n A B x y * errXY d n B x y) :=
          mul_le_mul_of_nonneg_right hcoef (mul_nonneg hLnn herrXYnn)
      _ = (2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2) + K2 + K3 + 1)
          * mixL d n A B x y * errXY d n B x y := by ring
  have hBC : (K2 + K3) * mixL d n A B x y / Real.log A + mixL d n A B x y / Real.log A
      ≤ CC * mixL d n A B x y * (1 / Real.log A) := by
    rw [hCCdef]
    have hcoef : K2 + K3 + 1
        ≤ 2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2) + K2 + K3 + 1 := by
      have hpos : 0 ≤ 2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2) :=
        add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCsknn) hζnn)
          (mul_nonneg (by norm_num) hζnn)
      linarith
    calc (K2 + K3) * mixL d n A B x y / Real.log A + mixL d n A B x y / Real.log A
        = (K2 + K3 + 1) * (mixL d n A B x y * (1 / Real.log A)) := by ring
      _ ≤ (2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2) + K2 + K3 + 1)
          * (mixL d n A B x y * (1 / Real.log A)) :=
          mul_le_mul_of_nonneg_right hcoef (mul_nonneg hLnn (by positivity))
      _ = (2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2) + K2 + K3 + 1)
          * mixL d n A B x y * (1 / Real.log A) := by ring
  have hfinal : |(∑ ℓ ∈ Finset.Icc 1 L0,
        ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) *
          Sk d n 1 (GamMix d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
            (TmixSet d n y (A / (ℓ : ℝ)) (Real.log B)))
        - mixMain d n A B (x, y)|
      ≤ CC * mixMain d n A B (x, y) * (errXY d n B x y + 1 / Real.log A) := by
    have htri : |(∑ ℓ ∈ Finset.Icc 1 L0,
          ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) *
            Sk d n 1 (GamMix d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
              (TmixSet d n y (A / (ℓ : ℝ)) (Real.log B)))
          - mixMain d n A B (x, y)|
        ≤ |(∑ ℓ ∈ Finset.Icc 1 L0,
            ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) *
              Sk d n 1 (GamMix d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
                (TmixSet d n y (A / (ℓ : ℝ)) (Real.log B)))
            - mixL d n A B x y|
          + |mixL d n A B x y - mixMain d n A B (x, y)| := by
      rw [show (∑ ℓ ∈ Finset.Icc 1 L0,
            ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) *
              Sk d n 1 (GamMix d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
                (TmixSet d n y (A / (ℓ : ℝ)) (Real.log B))) - mixMain d n A B (x, y)
          = ((∑ ℓ ∈ Finset.Icc 1 L0,
              ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) *
                Sk d n 1 (GamMix d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
                  (TmixSet d n y (A / (ℓ : ℝ)) (Real.log B)))
              - mixL d n A B x y)
            + (mixL d n A B x y - mixMain d n A B (x, y)) from by ring]
      exact abs_add_le _ _
    have htri2 : |(∑ ℓ ∈ Finset.Icc 1 L0,
          ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) *
            Sk d n 1 (GamMix d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
              (TmixSet d n y (A / (ℓ : ℝ)) (Real.log B)))
          - mixL d n A B x y|
        ≤ (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixPerErr d n Csk A B x y ℓ)
          + |(∑ ℓ ∈ Finset.Icc 1 L0,
              ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) * mixPerMain d n A B x y ℓ)
            - mixL d n A B x y| := by
      rw [show (∑ ℓ ∈ Finset.Icc 1 L0,
            ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) *
              Sk d n 1 (GamMix d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
                (TmixSet d n y (A / (ℓ : ℝ)) (Real.log B))) - mixL d n A B x y
          = ((∑ ℓ ∈ Finset.Icc 1 L0,
              ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) *
                Sk d n 1 (GamMix d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
                  (TmixSet d n y (A / (ℓ : ℝ)) (Real.log B)))
              - (∑ ℓ ∈ Finset.Icc 1 L0,
                ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) * mixPerMain d n A B x y ℓ))
            + ((∑ ℓ ∈ Finset.Icc 1 L0,
                ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) * mixPerMain d n A B x y ℓ)
              - mixL d n A B x y) from by ring]
      exact le_trans (abs_add_le _ _) (add_le_add hstep1 le_rfl)
    calc |(∑ ℓ ∈ Finset.Icc 1 L0,
          ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) *
            Sk d n 1 (GamMix d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
              (TmixSet d n y (A / (ℓ : ℝ)) (Real.log B)))
          - mixMain d n A B (x, y)|
        ≤ |(∑ ℓ ∈ Finset.Icc 1 L0,
            ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) *
              Sk d n 1 (GamMix d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
                (TmixSet d n y (A / (ℓ : ℝ)) (Real.log B)))
            - mixL d n A B x y|
          + |mixL d n A B x y - mixMain d n A B (x, y)| := htri
      _ = |(∑ ℓ ∈ Finset.Icc 1 L0,
            ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) *
              Sk d n 1 (GamMix d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
                (TmixSet d n y (A / (ℓ : ℝ)) (Real.log B)))
            - mixL d n A B x y| := by rw [hloc, sub_self, abs_zero, add_zero]
      _ ≤ (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixPerErr d n Csk A B x y ℓ)
          + |(∑ ℓ ∈ Finset.Icc 1 L0,
              ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) * mixPerMain d n A B x y ℓ)
            - mixL d n A B x y| := htri2
      _ ≤ (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ)) * mixPerErr d n Csk A B x y ℓ)
          + (mixL d n A B x y / Real.log A
            + 3 * zetaR (NN d n - 2) * mixL d n A B x y * errXY d n B x y) :=
          add_le_add le_rfl hmain
      _ ≤ (2 * Csk * zetaR (NN d n - 2) * mixL d n A B x y * errXY d n B x y
            + (K2 + K3) * mixL d n A B x y / Real.log A)
          + (mixL d n A B x y / Real.log A
            + 3 * zetaR (NN d n - 2) * mixL d n A B x y * errXY d n B x y) :=
          add_le_add hAbsBd le_rfl
      _ = (2 * Csk * zetaR (NN d n - 2) * mixL d n A B x y * errXY d n B x y
            + 3 * zetaR (NN d n - 2) * mixL d n A B x y * errXY d n B x y)
          + ((K2 + K3) * mixL d n A B x y / Real.log A
            + mixL d n A B x y / Real.log A) := by ring
      _ ≤ CC * mixL d n A B x y * errXY d n B x y
          + CC * mixL d n A B x y * (1 / Real.log A) := add_le_add hAD hBC
      _ = CC * mixL d n A B x y * (errXY d n B x y + 1 / Real.log A) := by ring
      _ = CC * mixMain d n A B (x, y) * (errXY d n B x y + 1 / Real.log A) := by rw [hloc]
  exact hfinal

end Work.HP.MM2

