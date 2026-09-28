import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.MM2.Sk1_mix_ell
import Submission.Work.HP.MM2.S1ball_le
import Submission.Work.HP.MM2.mix_arith
import Submission.Work.HP.MM2.Sstar1_mix_tail
import Submission.Work.HP.MM2.mix_small
import Submission.Work.HP.MM2.ss1_S1ball_aux
import Submission.Work.HP.SstarMobiusMix
import Submission.Work.HP.DeltaXY_gcd_detL
import Submission.Work.HP.Sig2.omega_li
import Submission.Work.HP.latOrth_count_degenerate
import Submission.Work.HP.isPrim_veronese
import Submission.Work.HP.IcVolAux
import Submission.Work.HP.MDEstimates.veronese_linIndep
import Submission.Work.HP.det_gam_gen
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.MinkDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.HP.MM2

attribute [local instance] Classical.propDecidable

open Filter Finset MeasureTheory
open Work.HP

/-! ## Auxiliary lemmas -/

/-- Splitting an `Icc` sum at `c`. -/
private lemma ss1_sum_Icc_split_one {f : ℕ → ℝ} {c b : ℕ} (hcb : c ≤ b) :
    (∑ l ∈ Finset.Icc 1 b, f l)
      = (∑ l ∈ Finset.Icc 1 c, f l) + ∑ l ∈ Finset.Icc (c + 1) b, f l := by
  have hunion : Finset.Icc 1 b = Finset.Icc 1 c ∪ Finset.Icc (c + 1) b := by
    ext l
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 c) (Finset.Icc (c + 1) b) :=
    Finset.disjoint_left.mpr (fun x hx hx' => by
      simp only [Finset.mem_Icc] at hx hx'
      omega)
  rw [hunion, Finset.sum_union hdisj]

/-- `1 ≤ λ(x)` for a primitive vector `x`. -/
private lemma ss1_one_le_lamX (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    {x : Fin (n + 1) → ℤ} (hx : IsPrim x) : 1 ≤ lamX d n x := by
  have h6 : 6 ≤ NN d n := six_le_NN d n hd hdn
  have hc : IsPrim (veronese d n x) := isPrim_veronese d n (by omega) hx
  have hrk : rk (latOrth (veronese d n x)) = NN d n - 1 :=
    LCD_rk_latOrth (veronese d n x) hc
  rw [lamX]
  exact LCD_one_le_lam (latOrth (veronese d n x)) (j := NN d n - 1) (by omega) (by rw [hrk])

private lemma ss1_zetaR_pos (m : ℕ) (hm : 1 < m) : 0 < zetaR m := by
  have hsum : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ m) := by
    have h2 : Summable (fun j : ℕ => 1 / ((j : ℕ) : ℝ) ^ m) :=
      Real.summable_one_div_nat_pow.mpr hm
    have h3 := (summable_nat_add_iff (f := fun j : ℕ => 1 / ((j : ℕ) : ℝ) ^ m) 1).mpr h2
    refine h3.congr (fun k => ?_)
    simp only [Nat.cast_add, Nat.cast_one]
  rw [zetaR]
  exact Summable.tsum_pos hsum (fun k => by positivity) 0 (by norm_num)

private lemma ss1_iotaDN_pos (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) : 0 < iotaDN d n := by
  have h6 : 6 ≤ NN d n := six_le_NN d n hd hdn
  have h1 : 1 ≤ NN d n - 2 := by omega
  have h2 : 1 < NN d n - 2 := by omega
  rw [iotaDN]
  have hV : 0 < ballVol (NN d n - 2) := ballVol_pos (NN d n - 2) h1
  have hz : 0 < zetaR (NN d n - 2) := ss1_zetaR_pos (NN d n - 2) h2
  positivity

private lemma ss1_isPrim_ne_zero {ι : Type*} [Fintype ι] {a : ι → ℤ} (h : IsPrim a) : a ≠ 0 := by
  intro h0
  have h1 : Finset.univ.gcd a = 0 :=
    Finset.gcd_eq_zero_iff.mpr (fun i _ => by rw [h0]; rfl)
  rw [IsPrim] at h
  rw [h] at h1
  exact one_ne_zero h1

private lemma ss1_eNorm_pos {ι : Type*} [Fintype ι] {v : ι → ℤ} (hv : v ≠ 0) : 0 < eNorm v :=
  eNorm_pos_iff.mpr hv

private lemma ss1_mixMain_pos (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    (A B : ℝ) (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (hxy : LinearIndependent ℤ ![x, y]) (hA : 0 < A) (hB : 1 < B) :
    0 < mixMain d n A B (x, y) := by
  have hi : 0 < iotaDN d n := ss1_iotaDN_pos d n hd hdn
  have hA2 : 0 < A ^ (NN d n - 2) := pow_pos hA _
  have hEy : 0 < eNorm (veronese d n y) :=
    ss1_eNorm_pos (MDEstimates.veronese_ne_zero (ss1_isPrim_ne_zero hy))
  have hlogB : 0 < Real.log B := Real.log_pos hB
  have hW : 0 < (bigW (wOf B) : ℝ) := by
    have h : (1 : ℝ) ≤ (bigW (wOf B) : ℝ) := by exact_mod_cast one_le_bigW (wOf B)
    linarith
  have hdet : 0 < detL (Gam d n x y) := lt_of_lt_of_le zero_lt_one (Lat.detL_ge_one _)
  rw [mixMain]
  exact div_pos (by positivity) (by positivity)

private lemma ss1_errXY_nonneg (d n : ℕ) (B : ℝ) (x y : Fin (n + 1) → ℤ) :
    0 ≤ errXY d n B x y := by
  rw [errXY]
  have h1 : 0 ≤ min 1 (DeltaXY d n x y ^ 2 / Real.log B ^ 2) :=
    le_min zero_le_one (by positivity)
  split <;> linarith

/-! ## (L2a) Non-degenerate pairs, mixed -/

/-- (L2a) Non-degenerate pairs, mixed. Möbius (`SstarMobiusMix`), `Sk1_mix_ell` for
`ℓ ≤ A/(Wλ(x))` (so `L₀ ≥ A^{1/4}`), trivial `S1ball` bound for larger `ℓ`,
`gcd_div_gcd_eq` + `moebius_gcd_zeta` for the `ℓ`-sum, `DeltaXY_gcd_detL` to rewrite.
All uniform errors (`αA^{-1/4}`, `w^{-(N-3)}`, `A^{-(N-3)/4}`, small-ball) are `≤ C/log A`. -/
theorem Sstar1_mix_pair (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    (h22 : (d, n) ≠ (2, 2)) :
    ∃ C B₀ : ℝ, 0 < C ∧ ∀ A B : ℝ, B₀ ≤ B → B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      ∀ p ∈ OmegaGood d n A B,
      |Sstar d n 1 (GamMix d n p.1 p.2 (bigW (wOf B))) (TmixSet d n p.2 A (Real.log B)) -
          mixMain d n A B p|
        ≤ C * mixMain d n A B p * (errXY d n B p.1 p.2 + 1 / Real.log A) := by
  classical
  obtain ⟨Csm, Bsm, hCsmpos, hSmall⟩ := mix_small d n hd hdn h22
  obtain ⟨Ctl, Btl, hCtlpos, hTail⟩ := Sstar1_mix_tail d n hd hdn h22
  obtain ⟨Bar0, har0⟩ := mix_arith d n hd hdn h22 0
  refine ⟨Csm + Ctl + 1, max (max Bsm Btl) (max Bar0 100), by positivity, ?_⟩
  intro A B hB hBA hAB2 p hp
  have hBsm : Bsm ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hB
  have hBtl : Btl ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hB
  have hBar0 : Bar0 ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB
  have hB100 : (100 : ℝ) ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB
  have hpx : IsPrim p.1 := hp.1.1.1
  have hpy : IsPrim p.2 := hp.1.2.1.1
  have hne : p.1 ≠ p.2 := hp.1.2.2.1
  have hne' : p.1 ≠ -p.2 := hp.1.2.2.2
  have hnormx : eNorm p.1 ≤ B ^ (1 / ((n : ℝ) + 1 - d)) := hp.1.1.2
  have hWlam : (bigW (wOf B) : ℝ) * lamX d n p.1 ≤ A ^ ((3 : ℝ) / 4) := hp.2
  have hLI : LinearIndependent ℤ ![p.1, p.2] := Sig2.li_of_prim_ne_pm p.1 p.2 hpx hpy hne hne'
  obtain ⟨hA1, hlogA1, -, hW1r, -, -, -, -⟩ := har0 B hBar0 A hBA hAB2 p.1 hnormx
  have hlogApos : 0 < Real.log A := by linarith
  have hW1n : 1 ≤ bigW (wOf B) := one_le_bigW (wOf B)
  have hlam1 : 1 ≤ lamX d n p.1 := ss1_one_le_lamX d n hd hdn hpx
  have hWpos : (0 : ℝ) < (bigW (wOf B) : ℝ) := by linarith
  have hWlampos : 0 < (bigW (wOf B) : ℝ) * lamX d n p.1 :=
    mul_pos hWpos (by linarith)
  have hL0M : ⌊A / ((bigW (wOf B) : ℝ) * lamX d n p.1)⌋₊ ≤ ⌊A⌋₊ := by
    refine Nat.floor_mono ?_
    rw [div_le_iff₀ hWlampos]
    have h1W : 1 ≤ (bigW (wOf B) : ℝ) * lamX d n p.1 := by
      have h := mul_le_mul hW1r hlam1 (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
      linarith
    calc A = A * 1 := (mul_one A).symm
      _ ≤ A * ((bigW (wOf B) : ℝ) * lamX d n p.1) :=
          mul_le_mul_of_nonneg_left h1W (by linarith)
  have hmob := SstarMobiusMix d n p.1 p.2 1 A (Real.log B) (bigW (wOf B)) hW1n hA1
  have hs := hSmall A B hBsm hBA hAB2 p.1 p.2 hpx hpy hLI hnormx hWlam
  have ht := hTail A B hBtl hBA hAB2 p.1 p.2 hpx hpy hLI hnormx hWlam
  rw [hmob]
  simp only [pow_one]
  set S : ℕ → ℝ := fun ℓ => ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) *
      Sk d n 1 (GamMix d n p.1 p.2 (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
        (TmixSet d n p.2 (A / (ℓ : ℝ)) (Real.log B)) with hS
  have hs' : |(∑ ℓ ∈ Finset.Icc 1 ⌊A / ((bigW (wOf B) : ℝ) * lamX d n p.1)⌋₊, S ℓ)
        - mixMain d n A B (p.1, p.2)|
      ≤ Csm * mixMain d n A B (p.1, p.2) * (errXY d n B p.1 p.2 + 1 / Real.log A) := by
    simpa only [hS] using hs
  have ht' : |(∑ ℓ ∈ Finset.Icc (⌊A / ((bigW (wOf B) : ℝ) * lamX d n p.1)⌋₊ + 1) ⌊A⌋₊, S ℓ)|
      ≤ Ctl * mixMain d n A B (p.1, p.2) / Real.log A := by
    simpa only [hS] using ht
  have hsplit := ss1_sum_Icc_split_one (f := S) hL0M
  rw [hsplit]
  have htri : |(∑ ℓ ∈ Finset.Icc 1 ⌊A / ((bigW (wOf B) : ℝ) * lamX d n p.1)⌋₊, S ℓ)
        + (∑ ℓ ∈ Finset.Icc (⌊A / ((bigW (wOf B) : ℝ) * lamX d n p.1)⌋₊ + 1) ⌊A⌋₊, S ℓ)
        - mixMain d n A B p|
      ≤ |(∑ ℓ ∈ Finset.Icc 1 ⌊A / ((bigW (wOf B) : ℝ) * lamX d n p.1)⌋₊, S ℓ) - mixMain d n A B p|
        + |∑ ℓ ∈ Finset.Icc (⌊A / ((bigW (wOf B) : ℝ) * lamX d n p.1)⌋₊ + 1) ⌊A⌋₊, S ℓ| := by
    rw [show (∑ ℓ ∈ Finset.Icc 1 ⌊A / ((bigW (wOf B) : ℝ) * lamX d n p.1)⌋₊, S ℓ)
          + (∑ ℓ ∈ Finset.Icc (⌊A / ((bigW (wOf B) : ℝ) * lamX d n p.1)⌋₊ + 1) ⌊A⌋₊, S ℓ)
          - mixMain d n A B p
        = ((∑ ℓ ∈ Finset.Icc 1 ⌊A / ((bigW (wOf B) : ℝ) * lamX d n p.1)⌋₊, S ℓ)
            - mixMain d n A B p)
          + (∑ ℓ ∈ Finset.Icc (⌊A / ((bigW (wOf B) : ℝ) * lamX d n p.1)⌋₊ + 1) ⌊A⌋₊, S ℓ)
        from by ring]
    exact abs_add_le _ _
  have hMMpos : 0 < mixMain d n A B p := by
    have hB1 : 1 < B := by linarith
    have hA0 : 0 < A := by linarith
    exact ss1_mixMain_pos d n hd hdn A B p.1 p.2 hpx hpy hLI hA0 hB1
  have hMMnn : 0 ≤ mixMain d n A B p := le_of_lt hMMpos
  have herrnn : 0 ≤ errXY d n B p.1 p.2 := ss1_errXY_nonneg d n B p.1 p.2
  calc |(∑ ℓ ∈ Finset.Icc 1 ⌊A / ((bigW (wOf B) : ℝ) * lamX d n p.1)⌋₊, S ℓ)
        + (∑ ℓ ∈ Finset.Icc (⌊A / ((bigW (wOf B) : ℝ) * lamX d n p.1)⌋₊ + 1) ⌊A⌋₊, S ℓ)
        - mixMain d n A B p|
      ≤ |(∑ ℓ ∈ Finset.Icc 1 ⌊A / ((bigW (wOf B) : ℝ) * lamX d n p.1)⌋₊, S ℓ) - mixMain d n A B p|
        + |∑ ℓ ∈ Finset.Icc (⌊A / ((bigW (wOf B) : ℝ) * lamX d n p.1)⌋₊ + 1) ⌊A⌋₊, S ℓ| := htri
    _ ≤ Csm * mixMain d n A B (p.1, p.2) * (errXY d n B p.1 p.2 + 1 / Real.log A)
        + Ctl * mixMain d n A B (p.1, p.2) / Real.log A := add_le_add hs' ht'
    _ ≤ (Csm + Ctl + 1) * mixMain d n A B p
        * (errXY d n B p.1 p.2 + 1 / Real.log A) := by
        have hinvnn : 0 ≤ 1 / Real.log A := by positivity
        have hy : 0 ≤ errXY d n B p.1 p.2 + 1 / Real.log A := by linarith
        have hyle : 1 / Real.log A ≤ errXY d n B p.1 p.2 + 1 / Real.log A := by linarith
        have h1 : Ctl * mixMain d n A B p / Real.log A
            ≤ Ctl * mixMain d n A B p * (errXY d n B p.1 p.2 + 1 / Real.log A) := by
          have hCMnn : 0 ≤ Ctl * mixMain d n A B p := mul_nonneg hCtlpos.le hMMnn
          calc Ctl * mixMain d n A B p / Real.log A
              = Ctl * mixMain d n A B p * (1 / Real.log A) := div_eq_mul_one_div _ _
            _ ≤ Ctl * mixMain d n A B p
                  * (errXY d n B p.1 p.2 + 1 / Real.log A) :=
                mul_le_mul_of_nonneg_left hyle hCMnn
        have h2 : Csm * mixMain d n A B p * (errXY d n B p.1 p.2 + 1 / Real.log A)
            + Ctl * mixMain d n A B p * (errXY d n B p.1 p.2 + 1 / Real.log A)
            ≤ (Csm + Ctl + 1) * mixMain d n A B p
              * (errXY d n B p.1 p.2 + 1 / Real.log A) := by
          have hMD : 0 ≤ mixMain d n A B p
              * (errXY d n B p.1 p.2 + 1 / Real.log A) := mul_nonneg hMMnn hy
          nlinarith [hMD]
        linarith [h1, h2]

end Work.HP.MM2
