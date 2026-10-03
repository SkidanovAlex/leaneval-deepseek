import Mathlib
import Submission.Work.FIArea3.PairDefs6
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.LargeUBase
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FIArea3.tau_sq_trunc
import Submission.Work.FIArea3.card_polarBox_filter_dvd_absDelta_noBox
import Submission.Work.FIArea3.sum_gcd_polarBox_le
import Submission.Work.FIArea3.polarBox_delta_tau_sum_le
import Submission.Work.FIArea3.largeU_M2
import Submission.Work.FIArea2.sum_tau_pow_le
import Submission.Work.FIArea2.sum_tau_pow_div_le
import Submission.Work.FIArea4.absDelta_le_sector
import Submission.Work.FIArea3.JointCount.card_filter_le_le_arith
import Submission.Work.FIArea3.JointCount.polarBox_lattice_count_sharp
import Submission.Work.FIArea3.JointCount.box_card_le
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm
import Submission.Work.FIArea3.lemma_2_2
import Submission.Work.FIArea3.pairSumCrude6_core
import Submission.Work.FIArea3.pairSumCrude6_smallU

set_option maxHeartbeats 4000000
set_option autoImplicit false

namespace Work.FIArea3

open Finset Work.FIPlan
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable


/-- **Scaled polar-box count**: for `g ≥ 1` the points of the polar box with both coordinates
divisible by `g` number at most `(10·(θ√N)/g + 1)²`.  Dividing by `g` puts them in a disc of radius
`5(θ√N)/g`, whose two coordinate projections have `≤ 10(θ√N)/g + 1` values each. -/
theorem myScaledPolarBoxCount (Pa : Work.FITop.Params) (φ : ℝ) (g : ℕ) (hg : 1 ≤ g) :
    (((Work.FIArea3.polarBoxFinset Pa φ).filter
        (fun z => (g : ℤ) ∣ z.re ∧ (g : ℤ) ∣ z.im)).card : ℝ)
      ≤ (10 * ((Pa.θ * Real.sqrt Pa.N) / (g : ℝ)) + 1) ^ (2 : ℕ) := by
  classical
  set u : ℝ := Pa.θ * Real.sqrt Pa.N with hu
  have hu0 : 0 ≤ u := by rw [hu]; exact mul_nonneg Pa.hθ0.le (Real.sqrt_nonneg _)
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  set A : Finset GaussianInt := (Work.FIArea3.polarBoxFinset Pa φ).filter
      (fun z => (g : ℤ) ∣ z.re ∧ (g : ℤ) ∣ z.im) with hA
  set c : ℂ := (Real.sqrt Pa.N : ℂ)
      * Complex.exp (((φ + Real.pi * Pa.θ : ℝ) : ℂ) * Complex.I) with hc
  have hdist : ∀ z ∈ A, ‖z.toComplex - c‖ ≤ 5 * u := by
    intro z hz
    have hzbox : Work.FITop3.InPolarBox Pa φ z :=
      (Work.FIArea3.mem_polarBoxFinset.mp (Finset.mem_filter.mp hz).1).2
    have h := Work.FIArea4.dist_polarBox_le Pa φ z hzbox
    have h5u : 5 * Pa.θ * Real.sqrt Pa.N = 5 * u := by rw [hu]; ring
    linarith [h, h5u]
  set X : Finset ℤ := A.image (fun z => z.re / (g : ℤ)) with hX
  set Y : Finset ℤ := A.image (fun z => z.im / (g : ℤ)) with hY
  have hXle : (X.card : ℝ) ≤ 2 * (5 * u / (g : ℝ)) + 1 := by
    have h := Work.FIArea4.card_int_le_of_mem_interval X
      (t := c.re / (g : ℝ) - 5 * u / (g : ℝ)) (ρ := 5 * u / (g : ℝ)) (by positivity)
      (fun x hx => by
        rw [hX, Finset.mem_image] at hx
        obtain ⟨z, hzA, rfl⟩ := hx
        have hdvd : (g : ℤ) ∣ z.re := (Finset.mem_filter.mp hzA).2.1
        have h5 := hdist z hzA
        have h1 : |((z.toComplex - c).re)| ≤ ‖z.toComplex - c‖ := Complex.abs_re_le_norm _
        have h2 : (z.toComplex - c).re = (z.re : ℝ) - c.re := by simp
        rw [h2] at h1
        have h4 : |(z.re : ℝ) - c.re| ≤ 5 * u := by linarith
        have hcast : (((z.re / (g : ℤ) : ℤ)) : ℝ) = (z.re : ℝ) / (g : ℝ) :=
          Int.cast_div_charZero hdvd
        have hb : |(((z.re / (g : ℤ) : ℤ)) : ℝ) - c.re / (g : ℝ)| ≤ 5 * u / (g : ℝ) := by
          rw [hcast, ← sub_div, abs_div, abs_of_pos hgR]
          exact div_le_div_of_nonneg_right h4 hgR.le
        have hb1 := (abs_le.mp hb).1
        have hb2 := (abs_le.mp hb).2
        have ht : c.re / (g : ℝ) - 5 * u / (g : ℝ) + 2 * (5 * u / (g : ℝ))
            = c.re / (g : ℝ) + 5 * u / (g : ℝ) := by ring
        rw [ht]
        exact ⟨by linarith, by linarith⟩)
    linarith [h]
  have hYle : (Y.card : ℝ) ≤ 2 * (5 * u / (g : ℝ)) + 1 := by
    have h := Work.FIArea4.card_int_le_of_mem_interval Y
      (t := c.im / (g : ℝ) - 5 * u / (g : ℝ)) (ρ := 5 * u / (g : ℝ)) (by positivity)
      (fun x hx => by
        rw [hY, Finset.mem_image] at hx
        obtain ⟨z, hzA, rfl⟩ := hx
        have hdvd : (g : ℤ) ∣ z.im := (Finset.mem_filter.mp hzA).2.2
        have h5 := hdist z hzA
        have h1 : |((z.toComplex - c).im)| ≤ ‖z.toComplex - c‖ := Complex.abs_im_le_norm _
        have h2 : (z.toComplex - c).im = (z.im : ℝ) - c.im := by simp
        rw [h2] at h1
        have h4 : |(z.im : ℝ) - c.im| ≤ 5 * u := by linarith
        have hcast : (((z.im / (g : ℤ) : ℤ)) : ℝ) = (z.im : ℝ) / (g : ℝ) :=
          Int.cast_div_charZero hdvd
        have hb : |(((z.im / (g : ℤ) : ℤ)) : ℝ) - c.im / (g : ℝ)| ≤ 5 * u / (g : ℝ) := by
          rw [hcast, ← sub_div, abs_div, abs_of_pos hgR]
          exact div_le_div_of_nonneg_right h4 hgR.le
        have hb1 := (abs_le.mp hb).1
        have hb2 := (abs_le.mp hb).2
        have ht : c.im / (g : ℝ) - 5 * u / (g : ℝ) + 2 * (5 * u / (g : ℝ))
            = c.im / (g : ℝ) + 5 * u / (g : ℝ) := by ring
        rw [ht]
        exact ⟨by linarith, by linarith⟩)
    linarith [h]
  have hpair : (A.card : ℝ) ≤ (X.card : ℝ) * (Y.card : ℝ) := by
    have hinj : Set.InjOn (fun z : GaussianInt => (z.re / (g : ℤ), z.im / (g : ℤ))) ↑A := by
      intro z hz w hw hzw
      have hzA : z ∈ A := by simpa using hz
      have hwA : w ∈ A := by simpa using hw
      rw [hA, Finset.mem_filter] at hzA hwA
      obtain ⟨hzr, hzi⟩ := hzA.2
      obtain ⟨hwr, hwi⟩ := hwA.2
      have e1 : z.re / (g : ℤ) = w.re / (g : ℤ) := congrArg Prod.fst hzw
      have e2 : z.im / (g : ℤ) = w.im / (g : ℤ) := congrArg Prod.snd hzw
      have m1 : z.re = w.re := by
        have a : (g : ℤ) * (z.re / (g : ℤ)) = z.re := by
          rw [mul_comm]; exact Int.ediv_mul_cancel hzr
        have b : (g : ℤ) * (w.re / (g : ℤ)) = w.re := by
          rw [mul_comm]; exact Int.ediv_mul_cancel hwr
        rw [← a, ← b, e1]
      have m2 : z.im = w.im := by
        have a : (g : ℤ) * (z.im / (g : ℤ)) = z.im := by
          rw [mul_comm]; exact Int.ediv_mul_cancel hzi
        have b : (g : ℤ) * (w.im / (g : ℤ)) = w.im := by
          rw [mul_comm]; exact Int.ediv_mul_cancel hwi
        rw [← a, ← b, e2]
      exact Zsqrtd.ext m1 m2
    have hcard : A.card
        = (A.image (fun z : GaussianInt => (z.re / (g : ℤ), z.im / (g : ℤ)))).card :=
      (Finset.card_image_of_injOn hinj).symm
    have hsub : A.image (fun z : GaussianInt => (z.re / (g : ℤ), z.im / (g : ℤ))) ⊆ (X ×ˢ Y) := by
      intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨z, hzA, rfl⟩ := hp
      rw [hX, hY]
      exact Finset.mem_product.mpr
        ⟨Finset.mem_image_of_mem _ hzA, Finset.mem_image_of_mem _ hzA⟩
    calc (A.card : ℝ)
        = ((A.image (fun z : GaussianInt => (z.re / (g : ℤ), z.im / (g : ℤ)))).card : ℝ) := by
          rw [hcard]
      _ ≤ (((X ×ˢ Y)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ = (X.card : ℝ) * (Y.card : ℝ) := by
          rw [Finset.card_product]; push_cast; ring
  have hXY0 : (0 : ℝ) ≤ (X.card : ℝ) * (Y.card : ℝ) := by positivity
  calc (A.card : ℝ)
      ≤ (X.card : ℝ) * (Y.card : ℝ) := hpair
    _ ≤ (2 * (5 * u / (g : ℝ)) + 1) * (2 * (5 * u / (g : ℝ)) + 1) := by
        nlinarith [hXle, hYle, hXY0]
    _ = (10 * ((Pa.θ * Real.sqrt Pa.N) / (g : ℝ)) + 1) ^ (2 : ℕ) := by rw [hu]; ring

private lemma theta_le_one_D2 (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  rw [Pa.hθ]
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hlog : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
    have h3 : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      exact Real.exp_one_lt_three
    exact le_trans h3.le (Real.log_le_log (by norm_num) hx3)
  exact Real.rpow_le_one_of_one_le_of_nonpos hlog (by linarith [Pa.hA, Pa.hA'])

theorem myLargeU_D2 : ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ),
      Pa.N ^ ((1 : ℝ) / 4) ≤ Pa.θ * Real.sqrt Pa.N →
      (∑ z1 ∈ Work.FIArea3.polarBoxFinset Pa φ, ∑ z2 ∈ Work.FIArea3.polarBoxFinset Pa φ,
          (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ) ^ (2 : ℕ))
        ≤ C * (Pa.θ * Real.sqrt Pa.N) ^ (4 : ℕ) * (2 + Real.log Pa.N) ^ (262144 : ℕ) := by
  obtain ⟨C17, hC17pos, hC17⟩ := Work.FIArea2.sum_tau_pow_div_le 17
  obtain ⟨C17', hC17'pos, hC17'⟩ := Work.FIArea2.sum_tau_pow_le 17
  obtain ⟨C16, hC16pos, hC16⟩ := Work.FIArea2.sum_tau_pow_le 16
  obtain ⟨C6, hC6pos, hC6⟩ := Work.FIArea4.polarBox_card_le
  have h216 : (0 : ℝ) < 24 * C6 * C16 := by
    have h := mul_pos hC6pos hC16pos
    linarith only [h]
  have hfac : (0 : ℝ) < 120 * C17 + 4 * C17' + 24 * C6 * C16 := by
    linarith only [hC17pos, hC17'pos, h216]
  have h2pow : (0 : ℝ) < (2 : ℝ) ^ (262144 : ℕ) := by positivity
  refine ⟨65536 * 401 * (120 * C17 + 4 * C17' + 24 * C6 * C16) * (2 : ℝ) ^ (262144 : ℕ),
    mul_pos (mul_pos (mul_pos (by norm_num) (by norm_num)) hfac) h2pow, ?_⟩
  intro Pa φ hu
  classical
  set u : ℝ := Pa.θ * Real.sqrt Pa.N with huD
  set D : ℝ := 4 * Real.pi * Pa.θ * Pa.N with hD
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hNpos : (0 : ℝ) < Pa.N := by linarith only [hN1]
  have hθpos : (0 : ℝ) < Pa.θ := Pa.hθ0
  have hθ1 : Pa.θ ≤ 1 := theta_le_one_D2 Pa
  have hu0 : (0 : ℝ) ≤ u := by rw [huD]; positivity
  have hu1 : (1 : ℝ) ≤ u := by
    have h1 : (1 : ℝ) ≤ Pa.N ^ ((1 : ℝ) / 4) := Real.one_le_rpow hN1 (by norm_num)
    have h2 : Pa.N ^ ((1 : ℝ) / 4) ≤ u := by rw [huD]; exact hu
    linarith only [h1, h2]
  have hlogN0 : (0 : ℝ) ≤ Real.log Pa.N := Real.log_nonneg hN1
  have hDpos : (0 : ℝ) < D := by rw [hD]; positivity
  have hDnn : (0 : ℝ) ≤ D := le_of_lt hDpos
  have hu_sq : u ^ 2 = Pa.θ ^ 2 * Pa.N := by rw [huD, mul_pow, Real.sq_sqrt hNpos.le]
  -- every `|Δ(z₁,z₂)|` with both points in the polar box is at most `D = 4πθN`
  have hΔD : ∀ z1 ∈ Work.FIArea3.polarBoxFinset Pa φ,
      ∀ z2 ∈ Work.FIArea3.polarBoxFinset Pa φ,
      ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ D := by
    intro z1 hz1 z2 hz2
    have hp1 : Work.FITop3.InPolarBox Pa φ z1 := (Work.FIArea3.mem_polarBoxFinset.mp hz1).2
    have hp2 : Work.FITop3.InPolarBox Pa φ z2 := (Work.FIArea3.mem_polarBoxFinset.mp hz2).2
    have hs := Work.FIArea4.absDelta_le_sector Pa φ hp1 hp2
    have hn1 : Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ)) : ℝ) ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) :=
      Real.sqrt_le_sqrt hp1.2.2.1
    have hn2 : Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ)) : ℝ) ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) :=
      Real.sqrt_le_sqrt hp2.2.2.1
    have hprod : Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ)) : ℝ)
        * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ)) : ℝ) ≤ (1 + Pa.θ) * Pa.N := by
      have h := mul_le_mul hn1 hn2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      rwa [← pow_two, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (1 + Pa.θ) * Pa.N)] at h
    have hcoef : (0 : ℝ) ≤ 2 * Real.pi * Pa.θ := by positivity
    have hassoc : 2 * Real.pi * Pa.θ * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ)) : ℝ)
          * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ)) : ℝ)
        = 2 * Real.pi * Pa.θ * (Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ)) : ℝ)
            * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ)) : ℝ)) := by ring
    rw [hassoc] at hs
    have hstep : 2 * Real.pi * Pa.θ * (Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ)) : ℝ)
          * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ)) : ℝ)) ≤ 4 * Real.pi * Pa.θ * Pa.N := by
      have h1 := mul_le_mul_of_nonneg_left hprod hcoef
      have h2 : (1 + Pa.θ) ≤ 2 := by linarith only [hθ1]
      have hc2 : (0 : ℝ) ≤ 2 * Real.pi * Pa.θ * Pa.N := by positivity
      linarith only [h1, mul_le_mul_of_nonneg_left h2 hc2]
    rw [hD]
    linarith only [hs, hstep]
  by_cases hsmall : D < 1
  · -- then `|Δ| < 1` everywhere, so all the determinants vanish
    have hzero : ∀ z1 ∈ Work.FIArea3.polarBoxFinset Pa φ,
        ∀ z2 ∈ Work.FIArea3.polarBoxFinset Pa φ, Work.FIPlan.absDelta z1 z2 = 0 := by
      intro z1 hz1 z2 hz2
      have h1 : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) < 1 :=
        lt_of_le_of_lt (hΔD z1 hz1 z2 hz2) hsmall
      exact Nat.cast_lt_one.mp h1
    have hsum0 : (∑ z1 ∈ Work.FIArea3.polarBoxFinset Pa φ,
          ∑ z2 ∈ Work.FIArea3.polarBoxFinset Pa φ,
          (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ) ^ (2 : ℕ)) = 0 := by
      apply Finset.sum_eq_zero
      intro z1 hz1
      apply Finset.sum_eq_zero
      intro z2 hz2
      rw [hzero z1 hz1 z2 hz2, Nat.divisors_zero]
      simp
    have hnn1 : (0 : ℝ) ≤ (Pa.θ * Real.sqrt Pa.N) ^ (4 : ℕ) := by positivity
    have hnn2 : (0 : ℝ) ≤ (2 + Real.log Pa.N) ^ (262144 : ℕ) := by positivity
    have hR : (0 : ℝ) ≤ 65536 * 401 * (120 * C17 + 4 * C17' + 24 * C6 * C16)
        * (2 : ℝ) ^ (262144 : ℕ) * (Pa.θ * Real.sqrt Pa.N) ^ (4 : ℕ)
        * (2 + Real.log Pa.N) ^ (262144 : ℕ) := by
      have hC : (0 : ℝ) ≤ 65536 * 401 * (120 * C17 + 4 * C17' + 24 * C6 * C16)
          * (2 : ℝ) ^ (262144 : ℕ) := le_of_lt (mul_pos (mul_pos (mul_pos (by norm_num)
            (by norm_num)) hfac) h2pow)
      exact mul_nonneg (mul_nonneg hC hnn1) hnn2
    rw [hsum0]
    exact hR
  · push_neg at hsmall
    set K : ℕ := Nat.ceil (D ^ ((1 : ℝ) / 4)) with hK
    have hd14 : (0 : ℝ) ≤ D ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hDnn _
    have hKge : D ^ ((1 : ℝ) / 4) ≤ (K : ℝ) := Nat.le_ceil _
    have hD14_1 : (1 : ℝ) ≤ D ^ ((1 : ℝ) / 4) := Real.one_le_rpow hsmall (by norm_num)
    have hK1 : 1 ≤ K := by
      have h1 : (1 : ℝ) ≤ (K : ℝ) := le_trans hD14_1 hKge
      exact_mod_cast h1
    have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
    have hKlt : (K : ℝ) ≤ D ^ ((1 : ℝ) / 4) + 1 := le_of_lt (Nat.ceil_lt_add_one hd14)
    have hKle : (K : ℝ) ≤ 2 * D ^ ((1 : ℝ) / 4) := by
      calc (K : ℝ) ≤ D ^ ((1 : ℝ) / 4) + 1 := hKlt
        _ ≤ D ^ ((1 : ℝ) / 4) + D ^ ((1 : ℝ) / 4) := add_le_add le_rfl hD14_1
        _ = 2 * D ^ ((1 : ℝ) / 4) := by ring
    have hDpow : (D ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = D := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hDnn,
        show ((1 : ℝ) / 4 * ((4 : ℕ) : ℝ)) = 1 by norm_num, Real.rpow_one]
    -- `1 ≤ θ⁴N` and `1 ≤ θ³N`, from `N^{1/4} ≤ θ√N`
    have h14_4 : (Pa.N ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = Pa.N := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le,
        show ((1 : ℝ) / 4 * ((4 : ℕ) : ℝ)) = 1 by norm_num, Real.rpow_one]
    have hu4 : (Pa.θ * Real.sqrt Pa.N) ^ (4 : ℕ) = Pa.θ ^ 4 * Pa.N ^ 2 := by
      rw [mul_pow, show (Real.sqrt Pa.N) ^ (4 : ℕ) = Pa.N ^ 2 by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hNpos.le]]
    have hθ4N : (1 : ℝ) ≤ Pa.θ ^ 4 * Pa.N := by
      have h1 : Pa.N ≤ Pa.θ ^ 4 * Pa.N ^ 2 := by
        have h := pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le _) hu 4
        rwa [h14_4, hu4] at h
      have h2 : (1 : ℝ) ≤ Pa.θ ^ 4 * Pa.N ^ 2 / Pa.N := by
        rw [le_div_iff₀ hNpos]
        simpa using h1
      have h3 : Pa.θ ^ 4 * Pa.N ^ 2 / Pa.N = Pa.θ ^ 4 * Pa.N := by
        rw [div_eq_iff (ne_of_gt hNpos)]
        ring
      rwa [h3] at h2
    have hθ3N : (1 : ℝ) ≤ Pa.θ ^ 3 * Pa.N := by
      have h4 : Pa.θ ^ 4 * Pa.N = Pa.θ * (Pa.θ ^ 3 * Pa.N) := by ring
      have h5 : (0 : ℝ) ≤ Pa.θ ^ 3 * Pa.N := by positivity
      have h6 : Pa.θ * (Pa.θ ^ 3 * Pa.N) ≤ Pa.θ ^ 3 * Pa.N := by
        linarith only [mul_le_mul_of_nonneg_right hθ1 h5]
      linarith only [h4, h6, hθ4N]
    -- `D ≤ (2u)^4`, hence `D^{1/4} ≤ 2u`, hence `K ≤ 4u`
    have hDu : D ≤ (2 * u) ^ (4 : ℕ) := by
      have h16 : (2 * u) ^ (4 : ℕ) = 16 * (Pa.θ ^ 4 * Pa.N ^ 2) := by
        rw [huD, mul_pow, hu4]
        norm_num
      rw [h16, hD]
      have hθN0 : (0 : ℝ) ≤ Pa.θ * Pa.N := by positivity
      have h1 : 4 * Real.pi * Pa.θ * Pa.N ≤ 16 * (Pa.θ * Pa.N) := by
        linarith only [mul_le_mul_of_nonneg_right Real.pi_le_four hθN0]
      have h2 : 16 * (Pa.θ * Pa.N) ≤ 16 * (Pa.θ ^ 4 * Pa.N ^ 2) := by
        linarith only [mul_le_mul_of_nonneg_left hθ4N hNpos.le,
          mul_le_mul_of_nonneg_right hθ1 hNpos.le]
      linarith only [h1, h2]
    have hD14le : D ^ ((1 : ℝ) / 4) ≤ 2 * u := by
      have h2u0 : (0 : ℝ) ≤ 2 * u := by linarith only [hu0]
      calc D ^ ((1 : ℝ) / 4) ≤ ((2 * u) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) :=
            Real.rpow_le_rpow hDnn hDu (by norm_num)
        _ = 2 * u := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul h2u0,
              show ((4 : ℕ) : ℝ) * ((1 : ℝ) / 4) = 1 by norm_num, Real.rpow_one]
    have hKleu : (K : ℝ) ≤ 4 * u := by linarith only [hKle, hD14le]
    -- `K ≤ 4N`, hence `log K + 2 ≤ 2(2 + log N)`
    have hKle4N : (K : ℝ) ≤ 4 * Pa.N := by
      have h2N0 : (0 : ℝ) ≤ 2 * Pa.N := by linarith only [hNpos]
      have hD4 : D ≤ (2 * Pa.N) ^ (4 : ℕ) := by
        have h16 : (2 * Pa.N) ^ (4 : ℕ) = 16 * Pa.N ^ 4 := by
          rw [mul_pow]
          norm_num
        rw [h16, hD]
        have hθN0 : (0 : ℝ) ≤ Pa.θ * Pa.N := by positivity
        linarith only [mul_le_mul_of_nonneg_right Real.pi_le_four hθN0,
          mul_le_mul_of_nonneg_right hθ1 hNpos.le, le_self_pow₀ hN1 (by norm_num : (4 : ℕ) ≠ 0)]
      calc (K : ℝ) ≤ 2 * D ^ ((1 : ℝ) / 4) := hKle
        _ ≤ 2 * (((2 * Pa.N) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4)) := by
            have h := Real.rpow_le_rpow hDnn hD4 (by norm_num : (0 : ℝ) ≤ 1 / 4)
            linarith only [h]
        _ = 4 * Pa.N := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul h2N0,
              show ((4 : ℕ) : ℝ) * ((1 : ℝ) / 4) = 1 by norm_num, Real.rpow_one]
            ring
    have hlogK2 : Real.log (K : ℝ) + 2 ≤ 2 * (2 + Real.log Pa.N) := by
      have hlog4N : Real.log (4 * Pa.N) = Real.log 4 + Real.log Pa.N :=
        Real.log_mul (by norm_num) (ne_of_gt hNpos)
      have hlog4 : Real.log 4 ≤ 2 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by
          have h := Real.add_one_le_exp (1 : ℝ)
          linarith only [h]
        have h2 : Real.exp 2 = (Real.exp 1) ^ 2 := by
          rw [sq, ← Real.exp_add]
          norm_num
        rw [h2]
        nlinarith only [hexp1]
      have h1 : Real.log (K : ℝ) ≤ Real.log (4 * Pa.N) := Real.log_le_log hKpos hKle4N
      rw [hlog4N] at h1
      linarith only [h1, hlog4, hlogN0]
    -- the polylogarithmic factor and the three divisor sums
    set B : Finset GaussianInt := Work.FIArea3.polarBoxFinset Pa φ with hB
    set P : ℝ := (Real.log (K : ℝ) + 2) ^ (2 ^ 17) with hP
    have hLK1 : (1 : ℝ) ≤ Real.log (K : ℝ) + 2 := by
      have h0 : (0 : ℝ) ≤ Real.log (K : ℝ) := Real.log_nonneg (by exact_mod_cast hK1)
      linarith only [h0]
    have hP0 : (0 : ℝ) ≤ P := by rw [hP]; exact pow_nonneg (le_trans zero_le_one hLK1) _
    have hPbound : P ≤ (2 : ℝ) ^ (262144 : ℕ) * (2 + Real.log Pa.N) ^ (262144 : ℕ) := by
      rw [hP]
      have hb : (0 : ℝ) ≤ Real.log (K : ℝ) + 2 := le_trans zero_le_one hLK1
      have h1 : (Real.log (K : ℝ) + 2) ^ (2 ^ 17)
          ≤ (2 * (2 + Real.log Pa.N)) ^ (2 ^ 17) := pow_le_pow_left₀ hb hlogK2 _
      have h2 : (2 * (2 + Real.log Pa.N)) ^ (2 ^ 17)
          = (2 : ℝ) ^ (2 ^ 17) * (2 + Real.log Pa.N) ^ (2 ^ 17) := mul_pow _ _ _
      have h3 : (2 + Real.log Pa.N) ^ (2 ^ 17) ≤ (2 + Real.log Pa.N) ^ (262144 : ℕ) :=
        pow_le_pow_right₀ (by linarith only [hlogN0] : (1 : ℝ) ≤ 2 + Real.log Pa.N) (by norm_num)
      have h4 : (2 : ℝ) ^ (2 ^ 17) ≤ (2 : ℝ) ^ (262144 : ℕ) :=
        pow_le_pow_right₀ (by norm_num) (by norm_num)
      calc (Real.log (K : ℝ) + 2) ^ (2 ^ 17) ≤ (2 * (2 + Real.log Pa.N)) ^ (2 ^ 17) := h1
        _ = (2 : ℝ) ^ (2 ^ 17) * (2 + Real.log Pa.N) ^ (2 ^ 17) := h2
        _ ≤ (2 : ℝ) ^ (262144 : ℕ) * (2 + Real.log Pa.N) ^ (262144 : ℕ) :=
            mul_le_mul h4 h3 (pow_nonneg (by linarith only [hlogN0]) _) (by positivity)
    set S1 : ℝ := ∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)) / (d : ℝ)
      with hS1
    set S2 : ℝ := ∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)) with hS2
    set S3 : ℝ := ∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) with hS3
    clear_value P S1 S2 S3
    have hS1le : S1 ≤ C17 * P := by rw [hS1, hP]; exact hC17 K
    have hS2le : S2 ≤ C17' * (K : ℝ) * P := by rw [hS2, hP]; exact hC17' K
    have hS3le : S3 ≤ C16 * (K : ℝ) * P := by
      rw [hS3]
      refine le_trans (hC16 K) ?_
      have h1 : (Real.log (K : ℝ) + 2) ^ (2 ^ 16) ≤ P := by
        rw [hP]
        exact pow_le_pow_right₀ hLK1 (by norm_num)
      exact mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ C16 * (K : ℝ))
    -- `FI` Lemma 2.2 with `k = 4`: `τ(m)² ≤ Σ_{d ≤ K, d ∣ m} 65536·τ(d)^{16}`
    have hpt : ∀ z1 ∈ B, ∀ z2 ∈ B,
        (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ) ^ (2 : ℕ)
          ≤ ∑ d ∈ Finset.Icc 1 K, (if d ∣ Work.FIPlan.absDelta z1 z2
              then 65536 * ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) := by
      intro z1 hz1 z2 hz2
      have hK4 : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ (K : ℝ) ^ (4 : ℕ) := by
        calc ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ D := hΔD z1 hz1 z2 hz2
          _ = (D ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) := hDpow.symm
          _ ≤ (K : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ hd14 hKge 4
      have h1 := Work.FIArea3.tau_sq_trunc (Work.FIPlan.absDelta z1 z2) K hK4
      have h2 : (256 : ℝ) ^ (2 : ℕ) * (∑ d ∈ Finset.Icc 1 K,
            (if d ∣ Work.FIPlan.absDelta z1 z2
              then ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0))
          = ∑ d ∈ Finset.Icc 1 K, (if d ∣ Work.FIPlan.absDelta z1 z2
              then 65536 * ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        by_cases hd : d ∣ Work.FIPlan.absDelta z1 z2
        · rw [if_pos hd, if_pos hd]
          norm_num
        · simp [hd]
      rwa [h2] at h1
    have hswap1 : (∑ z1 ∈ B, ∑ z2 ∈ B, ∑ d ∈ Finset.Icc 1 K,
          (if d ∣ Work.FIPlan.absDelta z1 z2
            then 65536 * ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0))
        = ∑ z1 ∈ B, ∑ d ∈ Finset.Icc 1 K,
            (65536 * ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))
            * (((B.filter (fun z2 => d ∣ Work.FIPlan.absDelta z1 z2)).card : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro z1 _
      exact sum_ite_div_mul_card B (Finset.Icc 1 K)
        (fun d => 65536 * ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))
        (fun z2 => Work.FIPlan.absDelta z1 z2)
    have hswap2 : (∑ z1 ∈ B, ∑ d ∈ Finset.Icc 1 K,
          (65536 * ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))
            * (((B.filter (fun z2 => d ∣ Work.FIPlan.absDelta z1 z2)).card : ℕ) : ℝ))
        = ∑ d ∈ Finset.Icc 1 K, (65536 * ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))
            * (∑ z1 ∈ B,
                (((B.filter (fun z2 => d ∣ Work.FIPlan.absDelta z1 z2)).card : ℕ) : ℝ)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
    have hstep1 : (∑ z1 ∈ B, ∑ z2 ∈ B,
          (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ) ^ (2 : ℕ))
        ≤ ∑ d ∈ Finset.Icc 1 K, (65536 * ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))
            * (∑ z1 ∈ B,
                (((B.filter (fun z2 => d ∣ Work.FIPlan.absDelta z1 z2)).card : ℕ) : ℝ)) := by
      calc (∑ z1 ∈ B, ∑ z2 ∈ B,
            (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ) ^ (2 : ℕ))
          ≤ ∑ z1 ∈ B, ∑ z2 ∈ B, ∑ d ∈ Finset.Icc 1 K,
              (if d ∣ Work.FIPlan.absDelta z1 z2
                then 65536 * ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) :=
            Finset.sum_le_sum (fun z1 hz1 => Finset.sum_le_sum (fun z2 hz2 => hpt z1 hz1 z2 hz2))
        _ = _ := hswap1
        _ = _ := hswap2
    have hinner : ∀ d ∈ Finset.Icc 1 K,
        (∑ z1 ∈ B, (((B.filter (fun z2 => d ∣ Work.FIPlan.absDelta z1 z2)).card : ℕ) : ℝ))
          ≤ 401 * (u ^ 2 * ((∑ z1 ∈ B,
                ((Nat.gcd (Nat.gcd z1.re.natAbs z1.im.natAbs) d : ℕ) : ℝ)) / (d : ℝ))
              + (u + 1) * ((B.card : ℕ) : ℝ)) := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      calc (∑ z1 ∈ B, (((B.filter (fun z2 => d ∣ Work.FIPlan.absDelta z1 z2)).card : ℕ) : ℝ))
          ≤ ∑ z1 ∈ B, (401 * (u ^ 2 * (((Nat.gcd (Nat.gcd z1.re.natAbs z1.im.natAbs) d : ℕ) : ℝ)
                / (d : ℝ)) + u + 1)) := by
            apply Finset.sum_le_sum
            intro z1 _
            have hcnt := Work.FIArea3.card_polarBox_filter_dvd_absDelta_noBox Pa φ z1 d hd1
            simpa [hB, huD] using hcnt
        _ = 401 * (u ^ 2 * ((∑ z1 ∈ B,
                ((Nat.gcd (Nat.gcd z1.re.natAbs z1.im.natAbs) d : ℕ) : ℝ)) / (d : ℝ))
              + (u + 1) * ((B.card : ℕ) : ℝ)) := by
            have hLHS : (∑ z1 ∈ B, (401 * (u ^ 2 * (((Nat.gcd (Nat.gcd z1.re.natAbs z1.im.natAbs) d : ℕ) : ℝ)
                  / (d : ℝ)) + u + 1)))
                = ∑ z1 ∈ B, ((401 * u ^ 2 / (d : ℝ))
                    * (((Nat.gcd (Nat.gcd z1.re.natAbs z1.im.natAbs) d : ℕ) : ℝ))
                    + (401 * (u + 1))) := by
              apply Finset.sum_congr rfl
              intro z1 _
              ring
            rw [hLHS, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
            ring
    have hGdle : ∀ d ∈ Finset.Icc 1 K,
        (∑ z1 ∈ B, ((Nat.gcd (Nat.gcd z1.re.natAbs z1.im.natAbs) d : ℕ) : ℝ))
          ≤ (100 * u ^ 2 + 20 * u + (d : ℝ)) * (((d.divisors.card : ℕ) : ℝ)) := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have h := Work.FIArea3.sum_gcd_polarBox_le Pa φ d hd1
        (fun g hg => Work.FIArea3.myScaledPolarBoxCount Pa φ g hg)
      simpa [hB, huD] using h
    have hcardB : ((B.card : ℕ) : ℝ) ≤ 3 * C6 * u ^ 2 := by
      have hb := hC6 Pa φ
      have h1 : ((B.card : ℕ) : ℝ)
          ≤ C6 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) := by
        have hBeq : B = (Work.FITop.boxN Pa).filter (fun z => Work.FITop3.InPolarBox Pa φ z) := by
          rw [hB]; rfl
        rw [hBeq]
        exact hb
      have h2 : Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1 = u ^ 2 + u + 1 := by
        rw [hu_sq, huD]
      rw [h2] at h1
      have hu2 : u + 1 ≤ 2 * u ^ 2 := by nlinarith only [hu1]
      linarith only [h1, mul_le_mul_of_nonneg_left hu2 hC6pos.le]
    have hsum_perd : (∑ d ∈ Finset.Icc 1 K, (65536 * ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))
          * (∑ z1 ∈ B,
              (((B.filter (fun z2 => d ∣ Work.FIPlan.absDelta z1 z2)).card : ℕ) : ℝ)))
        ≤ ∑ d ∈ Finset.Icc 1 K, (65536 * ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))
            * (401 * (u ^ 2 * (((100 * u ^ 2 + 20 * u + (d : ℝ))
                  * (((d.divisors.card : ℕ) : ℝ))) / (d : ℝ)) + (u + 1) * (3 * C6 * u ^ 2))) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
      have hc0 : (0 : ℝ) ≤ 65536 * ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) := by positivity
      refine mul_le_mul_of_nonneg_left ?_ hc0
      have h1 := hinner d hd
      have h2 : (∑ z1 ∈ B, ((Nat.gcd (Nat.gcd z1.re.natAbs z1.im.natAbs) d : ℕ) : ℝ))
          ≤ (100 * u ^ 2 + 20 * u + (d : ℝ)) * (((d.divisors.card : ℕ) : ℝ)) := hGdle d hd
      calc (∑ z1 ∈ B, (((B.filter (fun z2 => d ∣ Work.FIPlan.absDelta z1 z2)).card : ℕ) : ℝ))
          ≤ 401 * (u ^ 2 * ((∑ z1 ∈ B,
                ((Nat.gcd (Nat.gcd z1.re.natAbs z1.im.natAbs) d : ℕ) : ℝ)) / (d : ℝ))
              + (u + 1) * ((B.card : ℕ) : ℝ)) := h1
        _ ≤ 401 * (u ^ 2 * (((100 * u ^ 2 + 20 * u + (d : ℝ))
                * (((d.divisors.card : ℕ) : ℝ))) / (d : ℝ)) + (u + 1) * (3 * C6 * u ^ 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            refine add_le_add ?_ ?_
            · exact mul_le_mul_of_nonneg_left
                (div_le_div_of_nonneg_right h2 (le_of_lt hdpos)) (sq_nonneg u)
            · exact mul_le_mul_of_nonneg_left hcardB (by linarith only [hu0])
    have hsum_eq : (∑ d ∈ Finset.Icc 1 K, (65536 * ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))
            * (401 * (u ^ 2 * (((100 * u ^ 2 + 20 * u + (d : ℝ))
                  * (((d.divisors.card : ℕ) : ℝ))) / (d : ℝ)) + (u + 1) * (3 * C6 * u ^ 2))))
        = 401 * 65536 * (100 * u ^ 4 * S1 + 20 * u ^ 3 * S1 + u ^ 2 * S2
            + 3 * C6 * u ^ 2 * (u + 1) * S3) := by
      have hLHS : (∑ d ∈ Finset.Icc 1 K, (65536 * ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))
            * (401 * (u ^ 2 * (((100 * u ^ 2 + 20 * u + (d : ℝ))
                  * (((d.divisors.card : ℕ) : ℝ))) / (d : ℝ)) + (u + 1) * (3 * C6 * u ^ 2))))
          = ∑ d ∈ Finset.Icc 1 K, ((401 * 65536 * 100 * u ^ 4)
                * (((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)) / (d : ℝ))
              + (401 * 65536 * 20 * u ^ 3) * (((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)) / (d : ℝ))
              + (401 * 65536 * u ^ 2) * (((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)))
              + (401 * 65536 * (3 * C6 * u ^ 2 * (u + 1)))
                * (((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (Finset.mem_Icc.mp hd).1; omega)
        field_simp
      rw [hLHS, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        hS1, hS2, hS3, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    have hstep5 : 100 * u ^ 4 * S1 + 20 * u ^ 3 * S1 + u ^ 2 * S2 + 3 * C6 * u ^ 2 * (u + 1) * S3
        ≤ (120 * C17 + 4 * C17' + 24 * C6 * C16) * u ^ 4 * P := by
      have hu34 : u ^ 3 ≤ u ^ 4 := pow_le_pow_right₀ hu1 (by norm_num)
      have hA1 : 100 * u ^ 4 * S1 ≤ 100 * C17 * u ^ 4 * P := by
        have h := mul_le_mul_of_nonneg_left hS1le (by positivity : (0 : ℝ) ≤ 100 * u ^ 4)
        calc 100 * u ^ 4 * S1 ≤ 100 * u ^ 4 * (C17 * P) := h
          _ = 100 * C17 * u ^ 4 * P := by ring
      have hA2 : 20 * u ^ 3 * S1 ≤ 20 * C17 * u ^ 4 * P := by
        have h := mul_le_mul_of_nonneg_left hS1le (by positivity : (0 : ℝ) ≤ 20 * u ^ 3)
        have h2 : 20 * u ^ 3 * (C17 * P) ≤ 20 * C17 * u ^ 4 * P := by
          have hc : (0 : ℝ) ≤ 20 * C17 * P := by positivity
          linarith only [mul_le_mul_of_nonneg_left hu34 hc]
        linarith only [h, h2]
      have hA3 : u ^ 2 * S2 ≤ 4 * C17' * u ^ 4 * P := by
        have h := mul_le_mul_of_nonneg_left hS2le (by positivity : (0 : ℝ) ≤ u ^ 2)
        have h2 : u ^ 2 * (C17' * (K : ℝ) * P) ≤ 4 * C17' * u ^ 4 * P := by
          have hc1 : (0 : ℝ) ≤ u ^ 2 * C17' * P := by positivity
          have hc2 : (0 : ℝ) ≤ 4 * C17' * P := by positivity
          linarith only [mul_le_mul_of_nonneg_left hKleu hc1, mul_le_mul_of_nonneg_left hu34 hc2]
        linarith only [h, h2]
      have hA4 : 3 * C6 * u ^ 2 * (u + 1) * S3 ≤ 24 * C6 * C16 * u ^ 4 * P := by
        have h := mul_le_mul_of_nonneg_left hS3le (by positivity : (0 : ℝ) ≤ 3 * C6 * u ^ 2 * (u + 1))
        have h2 : 3 * C6 * u ^ 2 * (u + 1) * (C16 * (K : ℝ) * P) ≤ 24 * C6 * C16 * u ^ 4 * P := by
          have hc1 : (0 : ℝ) ≤ 3 * C6 * u ^ 2 * (u + 1) * C16 * P := by positivity
          have hc2 : (0 : ℝ) ≤ 12 * C6 * C16 * P := by positivity
          linarith only [mul_le_mul_of_nonneg_left hKleu hc1, mul_le_mul_of_nonneg_left hu34 hc2]
        linarith only [h, h2]
      have hsum := add_le_add (add_le_add (add_le_add hA1 hA2) hA3) hA4
      have heq : 100 * C17 * u ^ 4 * P + 20 * C17 * u ^ 4 * P + 4 * C17' * u ^ 4 * P
          + 24 * C6 * C16 * u ^ 4 * P
          = (120 * C17 + 4 * C17' + 24 * C6 * C16) * u ^ 4 * P := by ring
      linarith only [hsum, heq]
    have hZ : (∑ z1 ∈ B, ∑ z2 ∈ B,
          (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ) ^ (2 : ℕ))
        ≤ 401 * 65536 * (120 * C17 + 4 * C17' + 24 * C6 * C16) * u ^ 4 * P := by
      calc (∑ z1 ∈ B, ∑ z2 ∈ B,
            (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ) ^ (2 : ℕ))
          ≤ ∑ d ∈ Finset.Icc 1 K, (65536 * ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))
              * (∑ z1 ∈ B,
                  (((B.filter (fun z2 => d ∣ Work.FIPlan.absDelta z1 z2)).card : ℕ) : ℝ)) := hstep1
        _ ≤ ∑ d ∈ Finset.Icc 1 K, (65536 * ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))
              * (401 * (u ^ 2 * (((100 * u ^ 2 + 20 * u + (d : ℝ))
                    * (((d.divisors.card : ℕ) : ℝ))) / (d : ℝ)) + (u + 1) * (3 * C6 * u ^ 2))) :=
              hsum_perd
        _ = 401 * 65536 * (100 * u ^ 4 * S1 + 20 * u ^ 3 * S1 + u ^ 2 * S2
              + 3 * C6 * u ^ 2 * (u + 1) * S3) := hsum_eq
        _ ≤ 401 * 65536 * ((120 * C17 + 4 * C17' + 24 * C6 * C16) * u ^ 4 * P) :=
              mul_le_mul_of_nonneg_left hstep5 (by norm_num)
        _ = 401 * 65536 * (120 * C17 + 4 * C17' + 24 * C6 * C16) * u ^ 4 * P := by ring
    calc (∑ z1 ∈ Work.FIArea3.polarBoxFinset Pa φ, ∑ z2 ∈ Work.FIArea3.polarBoxFinset Pa φ,
          (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ) ^ (2 : ℕ))
        = (∑ z1 ∈ B, ∑ z2 ∈ B,
            (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ) ^ (2 : ℕ)) := by rw [hB]
      _ ≤ 401 * 65536 * (120 * C17 + 4 * C17' + 24 * C6 * C16) * u ^ 4 * P := hZ
      _ ≤ 401 * 65536 * (120 * C17 + 4 * C17' + 24 * C6 * C16) * u ^ 4
            * ((2 : ℝ) ^ (262144 : ℕ) * (2 + Real.log Pa.N) ^ (262144 : ℕ)) :=
            mul_le_mul_of_nonneg_left hPbound (by positivity)
      _ = 65536 * 401 * (120 * C17 + 4 * C17' + 24 * C6 * C16) * (2 : ℝ) ^ (262144 : ℕ)
            * (Pa.θ * Real.sqrt Pa.N) ^ (4 : ℕ) * (2 + Real.log Pa.N) ^ (262144 : ℕ) := by
            rw [huD]
            generalize (2 : ℝ) ^ (262144 : ℕ) = T
            generalize (2 + Real.log Pa.N) ^ (262144 : ℕ) = Q
            ring


def POW3 : ℝ := 3 ^ (393216 : ℕ)

lemma POW3_pos : 0 < POW3 := by unfold POW3; exact pow_pos (by norm_num) _

/- **The target pair-sum bound in the regime `N^{1/4} ≤ θ√N ≤ N^{3/8}`.**

The statement is TRUE (it is a strict weakening of `Work.FIArea3.pairSumCrude6_assembly`, and the
true size of the sum is `≈ u⁴(log N)³`).  A previous attempt showed that the naive re-indexing by
`lemma_2_2` + the available joint counts does *not* work: every available count
(`JointCount.card_filter_le_le_arith`, `jointCount6`, `card_filter_le_class`) has an
`e`-independent error term (`80uτ(d)/√d`), and re-summing over `e ≤ (2πθN)^{1/4}` produces a factor
`(2πθN)^{1/4} ≥ u^{7/16} > u²` at `u = N^{1/4}`.

Recommended route (two independent pieces):

1. **The τ(|z|²) moments are provable in this regime** (this is the mechanism of
   `polarBox_sum_tau_le`, which currently assumes `u ≥ N^{3/8}` but only needs `u ≥ c N^{1/4}`):
   splitting `τ(n) ≤ 256·Σ_{d|n, d ≤ (2N)^{1/4}} τ(d)^8` and using
   `#{z ∈ polar box : d | |z|²} ≤ πu²τ(d)/d + 80uτ(d)/√d + τ(d)` (the second term is
   `≤ 80·2^{1/4}u²` because `u ≥ N^{1/4}`), the divisor sums `Σ_d τ(d)^9/d`, `Σ_d τ(d)^9/√d`
   give `Σ_{z ∈ box} τ(|z|²) ≤ C u² (log N)^{O(1)}` and the same with `τ(|z|²)²` (weights
   `τ(d)^{16}` instead of `τ(d)^8`).

2. **The remaining input is the average of `τ(Δ)`.**  It suffices to prove
   `Σ_{z₁,z₂ ∈ polar box} τ(|Δ(z₁,z₂)|)² ≤ C u⁴ (log N)^{O(1)}` (with `O(1) ≤ 2¹⁹`).
   A route that only uses level sets of the *linear* forms `Im(z̄₁ ·)`:
   for fixed `v = z₂ - z₁` one has `Δ(z₁,z₁+v) = Im(z̄₁v)`; the level sets of the linear form
   `z₁ ↦ Im(z̄₁v)` are parallel lines spaced `|v'|` apart (`v' = v/gcd(v.re,v.im)`), so
   `#{z₁ ∈ K : Im(z̄₁v) = δ} ≤ C(u·gcd(v.re,v.im)/|v| + 1)`, and there are
   `≤ C(u|v|/gcd(v.re,v.im) + 1)` values `δ`; summing over `v` (with `gcd(v.re,v.im) = g`
   occurring for `≍ u²/g²` vectors `v`) and using `Σ_{δ ∈ [A,A+L]} τ(δ)² ≤ C L (log)^{O(1)}`
   gives `Σ_{z₁,z₂} τ(Δ)² ≤ C u⁴ (log N)^{O(1)}`. -/
theorem pairSumCrude6_largeU_asm :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ),
      Work.FITop3.IsBoxCoeff Pa φ β →
      (1 / 10 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N →
      Pa.θ * Real.sqrt Pa.N ≤ Pa.N ^ ((3 : ℝ) / 8) →
      Pa.N ^ ((1 : ℝ) / 4) ≤ Pa.θ * Real.sqrt Pa.N →
      (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if β z1 ≠ 0 ∧ β z2 ≠ 0 ∧ z1 ≠ z2 then
            (((Work.FIPlan.gnorm z1).divisors.card : ℕ) : ℝ)
              * ((((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)
                  * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)))
          else 0))
        ≤ C * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
            * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1) := by
  obtain ⟨C2, hC2pos, hC2⟩ := Work.FIArea3.largeU_M2
  obtain ⟨CD, hCDpos, hCD⟩ := Work.FIArea3.myLargeU_D2
  obtain ⟨CK, hCKpos, hCK⟩ := Work.FIArea4.polarBox_card_le
  have hCfpos : 0 < (C2 * (3 * CK) + C2 * Real.sqrt CD) * POW3 :=
    mul_pos (add_pos (mul_pos hC2pos (mul_pos (by norm_num) hCKpos))
      (mul_pos hC2pos (Real.sqrt_pos.mpr hCDpos))) POW3_pos
  refine ⟨(C2 * (3 * CK) + C2 * Real.sqrt CD) * POW3, hCfpos, ?_⟩
  intro Pa φ β hβ hu1 hu2 hu3
  set u : ℝ := Pa.θ * Real.sqrt Pa.N with hUdef
  set K : Finset GaussianInt := polarBoxFinset Pa φ with hKdef
  set A : GaussianInt → ℝ := fun z => (((gnorm z).divisors.card : ℕ) : ℝ) with hAdef
  set D : GaussianInt → GaussianInt → ℝ :=
    fun z1 z2 => (((absDelta z1 z2).divisors.card : ℕ) : ℝ) with hDdef
  set R : ℝ := 2 + Real.log Pa.N with hRdef
  set L : ℝ := Real.log Pa.N with hLdef
  -- restate the goal through the abbreviations, so that their values can be cleared
  show (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (if β z1 ≠ 0 ∧ β z2 ≠ 0 ∧ z1 ≠ z2 then A z1 * (A z2 * (1 + D z1 z2)) else 0))
      ≤ (C2 * (3 * CK) + C2 * Real.sqrt CD) * POW3 * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ)
          * Pa.N ^ (2 : ℕ) * L ^ (((2 : ℕ) ^ (20 : ℕ)) - 1)
  have hN1 : (1:ℝ) ≤ Pa.N := Pa.hN1
  have hNpos : (0:ℝ) < Pa.N := lt_of_lt_of_le one_pos hN1
  have hθ10 : Pa.θ ≤ (1:ℝ)/10 := theta_le_tenth Pa
  have hθpos : 0 < Pa.θ := Pa.hθ0
  have hτpos : 0 < Pa.τ := by
    have hx1 : (1:ℝ) < (Pa.x : ℝ) := by
      have h3 : (3:ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
      linarith only [h3]
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos (Real.log_pos hx1) _) Pa.hτ1
  have hsqN0 : 0 ≤ Real.sqrt Pa.N := Real.sqrt_nonneg _
  have hu0 : 0 ≤ u := mul_nonneg hθpos.le hsqN0
  have hN14 : (1:ℝ) ≤ Pa.N ^ ((1:ℝ)/4) := Real.one_le_rpow hN1 (by norm_num)
  have hu1' : (1:ℝ) ≤ u := le_trans hN14 hu3
  have hQsq : u ^ 2 = Pa.θ ^ 2 * Pa.N := by
    rw [hUdef, mul_pow, Real.sq_sqrt hNpos.le]
  have hu4 : u ^ 4 = Pa.θ ^ (4:ℕ) * Pa.N ^ (2:ℕ) := by
    have h22 : u ^ 4 = (u ^ 2) ^ 2 := by ring
    rw [h22, hQsq]; ring
  have hlogN1 : (1:ℝ) ≤ L := by
    have h10 : (10:ℝ) ≤ Real.sqrt Pa.N := by
      have hb : u ≤ (1/10) * Real.sqrt Pa.N := by
        rw [hUdef]; exact mul_le_mul_of_nonneg_right hθ10 hsqN0
      linarith only [hu3, hb, hN14]
    have h2 : Real.log 10 ≤ Real.log (Real.sqrt Pa.N) := Real.log_le_log (by norm_num) h10
    have h3 : Real.log (Real.sqrt Pa.N) = L / 2 := by
      rw [Real.log_sqrt hNpos.le]
    have h4 : (1:ℝ) ≤ Real.log 10 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith only [Real.exp_one_lt_d9]
    linarith only [h2, h3, h4]
  have hR1 : (1:ℝ) ≤ R := by rw [hRdef]; linarith only [hlogN1]
  have hR0 : (0:ℝ) ≤ R := le_trans zero_le_one hR1
  have hR3 : R ≤ 3 * L := by rw [hRdef]; linarith only [hlogN1]
  -- the three inputs, instantiated while the abbreviations are still transparent
  have hM2b : (∑ z ∈ K, A z ^ 2) ≤ C2 * u^2 * R^(262144:ℕ) := hC2 Pa φ hu3
  have hD2b : (∑ z1 ∈ K, ∑ z2 ∈ K, D z1 z2 ^ 2) ≤ CD * u^4 * R^(262144:ℕ) := hCD Pa φ hu3
  have hKcard0 : ((K.card : ℕ) : ℝ) ≤ CK * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) :=
    hCK Pa φ
  have hsub : K ⊆ Work.FITop.boxN Pa := polarBoxFinset_subset Pa φ
  have hmemK : ∀ z ∈ Work.FITop.boxN Pa, β z ≠ 0 → z ∈ K := fun z hz hne =>
    mem_polarBoxFinset.2 ⟨hz, (hβ.2 z hne).1⟩
  have hb3 : Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1 ≤ 3 * u^2 := by
    rw [← hQsq, ← hUdef]
    have h1 : u ≤ u ^ 2 := by nlinarith only [hu1']
    have h2 : 1 ≤ u ^ 2 := le_trans hu1' h1
    linarith only [h1, h2]
  have hcross : u^4 ≤ (Pa.τ⁻¹ + Pa.θ) * Pa.θ^(3:ℕ) * Pa.N^(2:ℕ) := by
    rw [hu4]
    have hτinv : (0:ℝ) ≤ Pa.τ⁻¹ := inv_nonneg.mpr hτpos.le
    have hθN : (0:ℝ) ≤ Pa.θ^(3:ℕ) * Pa.N^(2:ℕ) := by positivity
    have h4 : Pa.θ^(4:ℕ) * Pa.N^(2:ℕ) = Pa.θ * (Pa.θ^(3:ℕ) * Pa.N^(2:ℕ)) := by ring
    have h5 : (Pa.τ⁻¹ + Pa.θ) * Pa.θ^(3:ℕ) * Pa.N^(2:ℕ)
        = (Pa.τ⁻¹ + Pa.θ) * (Pa.θ^(3:ℕ) * Pa.N^(2:ℕ)) := by ring
    rw [h4, h5]
    exact mul_le_mul_of_nonneg_right (by linarith only [hτinv]) hθN
  have hX0 : (0:ℝ) ≤ (Pa.τ⁻¹ + Pa.θ) * Pa.θ^(3:ℕ) * Pa.N^(2:ℕ) := by positivity
  clear_value u K A D R L
  -- replace the huge powers of `R` by powers of one opaque `Q = R^131072`
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, R^(131072:ℕ) = Q := ⟨_, rfl⟩
  have hQ2 : R^(262144:ℕ) = Q^2 := by rw [← hQ, ← pow_mul]
  have hQ3 : R^(393216:ℕ) = Q^3 := by rw [← hQ, ← pow_mul]
  have hQ1 : 1 ≤ Q := by rw [← hQ]; exact one_le_pow₀ hR1
  rw [hQ2] at hM2b hD2b
  have hRle : Q^3 ≤ POW3 * L^(393216:ℕ) := by
    rw [← hQ3, POW3, ← mul_pow]
    exact pow_le_pow_left₀ hR0 hR3 _
  have hlogle : L^(393216:ℕ) ≤ L^(((2:ℕ)^(20:ℕ))-1) :=
    pow_le_pow_right₀ hlogN1 (by norm_num)
  obtain ⟨Lb, hLb⟩ : ∃ Lb : ℝ, L^(((2:ℕ)^(20:ℕ))-1) = Lb := ⟨_, rfl⟩
  obtain ⟨Lp, hLp⟩ : ∃ Lp : ℝ, L^(393216:ℕ) = Lp := ⟨_, rfl⟩
  rw [hLb]
  rw [hLp] at hRle
  rw [hLp, hLb] at hlogle
  clear hQ hQ2 hQ3 hLb hLp
  have hQ0 : 0 ≤ Q := le_trans zero_le_one hQ1
  -- (1) reduce to the polar box
  have hred : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (if β z1 ≠ 0 ∧ β z2 ≠ 0 ∧ z1 ≠ z2 then A z1 * (A z2 * (1 + D z1 z2)) else 0))
      ≤ ∑ z1 ∈ K, ∑ z2 ∈ K, A z1 * (A z2 * (1 + D z1 z2)) := by
    have hA0 : ∀ z, 0 ≤ A z := fun z => by rw [hAdef]; exact Nat.cast_nonneg _
    have hD0 : ∀ z1 z2, 0 ≤ D z1 z2 := fun z1 z2 => by rw [hDdef]; exact Nat.cast_nonneg _
    have h1 : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if β z1 ≠ 0 ∧ β z2 ≠ 0 ∧ z1 ≠ z2 then A z1 * (A z2 * (1 + D z1 z2)) else 0))
        = ∑ z1 ∈ K, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if β z1 ≠ 0 ∧ β z2 ≠ 0 ∧ z1 ≠ z2 then A z1 * (A z2 * (1 + D z1 z2)) else 0) := by
      refine (Finset.sum_subset hsub ?_).symm
      intro z1 hz1 hz1K
      have hb : β z1 = 0 := by
        by_contra hne
        exact hz1K (hmemK z1 hz1 hne)
      exact Finset.sum_eq_zero (fun z2 _ => by simp [hb])
    have h2 : (∑ z1 ∈ K, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if β z1 ≠ 0 ∧ β z2 ≠ 0 ∧ z1 ≠ z2 then A z1 * (A z2 * (1 + D z1 z2)) else 0))
        = ∑ z1 ∈ K, ∑ z2 ∈ K,
          (if β z1 ≠ 0 ∧ β z2 ≠ 0 ∧ z1 ≠ z2 then A z1 * (A z2 * (1 + D z1 z2)) else 0) := by
      apply Finset.sum_congr rfl
      intro z1 _
      refine (Finset.sum_subset hsub ?_).symm
      intro z2 hz2 hz2K
      have hb : β z2 = 0 := by
        by_contra hne
        exact hz2K (hmemK z2 hz2 hne)
      simp [hb]
    have h3 : (∑ z1 ∈ K, ∑ z2 ∈ K,
          (if β z1 ≠ 0 ∧ β z2 ≠ 0 ∧ z1 ≠ z2 then A z1 * (A z2 * (1 + D z1 z2)) else 0))
        ≤ ∑ z1 ∈ K, ∑ z2 ∈ K, A z1 * (A z2 * (1 + D z1 z2)) := by
      apply Finset.sum_le_sum; intro z1 _
      apply Finset.sum_le_sum; intro z2 _
      split_ifs with hc
      · exact le_rfl
      · exact mul_nonneg (hA0 z1) (mul_nonneg (hA0 z2) (by linarith only [hD0 z1 z2]))
    calc _ = _ := h1
      _ = _ := h2
      _ ≤ _ := h3
  -- (2) split off the `1`
  have hsplit : (∑ z1 ∈ K, ∑ z2 ∈ K, A z1 * (A z2 * (1 + D z1 z2)))
      = (∑ z ∈ K, A z)^2 + ∑ z1 ∈ K, ∑ z2 ∈ K, A z1 * A z2 * D z1 z2 := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro z1 _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro z2 _
    ring
  -- (3) the two Cauchy–Schwarz steps
  have hKcard : ((K.card : ℕ) : ℝ) ≤ (3 * CK) * u^2 := by
    calc ((K.card : ℕ) : ℝ) ≤ CK * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) := hKcard0
      _ ≤ CK * (3 * u^2) := mul_le_mul_of_nonneg_left hb3 hCKpos.le
      _ = (3 * CK) * u^2 := by ring
  have hM : (0:ℝ) ≤ C2 * u^2 * Q^2 := by positivity
  have hcs1 : (∑ z ∈ K, A z)^2 ≤ (C2 * u^2 * Q^2) * ((3 * CK) * u^2) := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq K A (fun _ : GaussianInt => (1:ℝ))
    simp only [mul_one, one_pow] at h1
    have h1' : (∑ z ∈ K, (1:ℝ)) = ((K.card : ℕ) : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [h1'] at h1
    refine le_trans h1 ?_
    exact mul_le_mul hM2b hKcard (Nat.cast_nonneg _) hM
  have hcs2 : (∑ z1 ∈ K, ∑ z2 ∈ K, A z1 * A z2 * D z1 z2)
      ≤ (C2 * u^2 * Q^2) * (Real.sqrt CD * u^2 * Q) := by
    have hA0 : ∀ z, 0 ≤ A z := fun z => by rw [hAdef]; exact Nat.cast_nonneg _
    have hD0 : ∀ z1 z2, 0 ≤ D z1 z2 := fun z1 z2 => by rw [hDdef]; exact Nat.cast_nonneg _
    have hsq : (∑ z1 ∈ K, ∑ z2 ∈ K, (A z1 * A z2)^2) = (∑ z1 ∈ K, A z1 ^ 2)^2 := by
      rw [sq, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro z1 _
      apply Finset.sum_congr rfl; intro z2 _
      ring
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq (K ×ˢ K)
      (fun p : GaussianInt × GaussianInt => A p.1 * A p.2)
      (fun p : GaussianInt × GaussianInt => D p.1 p.2)
    simp only [Finset.sum_product] at hCS
    rw [hsq] at hCS
    have hm0 : (0:ℝ) ≤ ∑ z1 ∈ K, A z1 ^ 2 :=
      Finset.sum_nonneg (fun z _ => sq_nonneg (A z))
    have hd0 : (0:ℝ) ≤ ∑ z1 ∈ K, ∑ z2 ∈ K, D z1 z2 ^ 2 :=
      Finset.sum_nonneg (fun z1 _ => Finset.sum_nonneg (fun z2 _ => sq_nonneg (D z1 z2)))
    have hm1 : (∑ z1 ∈ K, A z1 ^ 2)^2 ≤ (C2 * u^2 * Q^2)^2 :=
      pow_le_pow_left₀ hm0 hM2b 2
    have h3 : (∑ z1 ∈ K, ∑ z2 ∈ K, A z1 * A z2 * D z1 z2)^2
        ≤ (C2 * u^2 * Q^2)^2 * (CD * u^4 * Q^2) :=
      calc _ ≤ (∑ z1 ∈ K, A z1 ^ 2)^2 * (∑ z1 ∈ K, ∑ z2 ∈ K, D z1 z2 ^ 2) := hCS
        _ ≤ (C2 * u^2 * Q^2)^2 * (∑ z1 ∈ K, ∑ z2 ∈ K, D z1 z2 ^ 2) :=
            mul_le_mul_of_nonneg_right hm1 hd0
        _ ≤ (C2 * u^2 * Q^2)^2 * (CD * u^4 * Q^2) :=
            mul_le_mul_of_nonneg_left hD2b (sq_nonneg _)
    have hbody : (C2 * u^2 * Q^2)^2 * (CD * u^4 * Q^2)
        = ((C2 * u^2 * Q^2) * (Real.sqrt CD * u^2 * Q))^2 := by
      rw [mul_pow (C2 * u^2 * Q^2), mul_pow (Real.sqrt CD * u^2), mul_pow (Real.sqrt CD),
        Real.sq_sqrt hCDpos.le]
      ring
    rw [hbody] at h3
    have hnn : (0:ℝ) ≤ ∑ z1 ∈ K, ∑ z2 ∈ K, A z1 * A z2 * D z1 z2 :=
      Finset.sum_nonneg (fun z1 _ => Finset.sum_nonneg (fun z2 _ =>
        mul_nonneg (mul_nonneg (hA0 z1) (hA0 z2)) (hD0 z1 z2)))
    have hr0 : (0:ℝ) ≤ (C2 * u^2 * Q^2) * (Real.sqrt CD * u^2 * Q) := by positivity
    exact (pow_le_pow_iff_left₀ hnn hr0 two_ne_zero).1 h3
  -- (4) the final numerical comparison
  have hQ23 : Q^2 ≤ Q^3 := pow_le_pow_right₀ hQ1 (by norm_num)
  have hCbig : (0:ℝ) ≤ C2 * (3 * CK) + C2 * Real.sqrt CD := by positivity
  have hmain : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (if β z1 ≠ 0 ∧ β z2 ≠ 0 ∧ z1 ≠ z2 then A z1 * (A z2 * (1 + D z1 z2)) else 0))
      ≤ (C2 * (3 * CK) + C2 * Real.sqrt CD) * u^4 * Q^3 := by
    have hA' : C2 * u^2 * Q^2 * ((3 * CK) * u^2) ≤ C2 * (3 * CK) * u^4 * Q^3 := by
      have heq : C2 * u^2 * Q^2 * ((3 * CK) * u^2) = C2 * (3 * CK) * u^4 * Q^2 := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hQ23 (by positivity)
    have hB' : C2 * u^2 * Q^2 * (Real.sqrt CD * u^2 * Q) = C2 * Real.sqrt CD * u^4 * Q^3 := by
      ring
    calc _ ≤ ∑ z1 ∈ K, ∑ z2 ∈ K, A z1 * (A z2 * (1 + D z1 z2)) := hred
      _ = (∑ z ∈ K, A z)^2 + ∑ z1 ∈ K, ∑ z2 ∈ K, A z1 * A z2 * D z1 z2 := hsplit
      _ ≤ (C2 * u^2 * Q^2) * ((3 * CK) * u^2)
            + (C2 * u^2 * Q^2) * (Real.sqrt CD * u^2 * Q) := add_le_add hcs1 hcs2
      _ ≤ C2 * (3 * CK) * u^4 * Q^3 + C2 * Real.sqrt CD * u^4 * Q^3 := by
          rw [hB']; exact add_le_add hA' le_rfl
      _ = (C2 * (3 * CK) + C2 * Real.sqrt CD) * u^4 * Q^3 := by ring
  calc _ ≤ (C2 * (3 * CK) + C2 * Real.sqrt CD) * u^4 * Q^3 := hmain
    _ ≤ (C2 * (3 * CK) + C2 * Real.sqrt CD) * ((Pa.τ⁻¹ + Pa.θ) * Pa.θ^(3:ℕ) * Pa.N^(2:ℕ))
          * Q^3 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcross hCbig) (by positivity)
    _ ≤ (C2 * (3 * CK) + C2 * Real.sqrt CD) * ((Pa.τ⁻¹ + Pa.θ) * Pa.θ^(3:ℕ) * Pa.N^(2:ℕ))
          * (POW3 * Lp) :=
        mul_le_mul_of_nonneg_left hRle (mul_nonneg hCbig hX0)
    _ ≤ (C2 * (3 * CK) + C2 * Real.sqrt CD) * ((Pa.τ⁻¹ + Pa.θ) * Pa.θ^(3:ℕ) * Pa.N^(2:ℕ))
          * (POW3 * Lb) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogle POW3_pos.le)
          (mul_nonneg hCbig hX0)
    _ = (C2 * (3 * CK) + C2 * Real.sqrt CD) * POW3 * (Pa.τ⁻¹ + Pa.θ)
          * Pa.θ^(3:ℕ) * Pa.N^(2:ℕ) * Lb := by ring




/-- **The τ-weighted off-diagonal pair sum of `pairSumCrude6`, in the crude regime.**

Split at `u = N^{1/4}`: `Work.FIArea3.pairSumCrude6_smallU` covers `u ≤ N^{1/4}` and
`pairSumCrude6_largeU_asm` covers `N^{1/4} ≤ u`; `pairSumCrude6_core_of` assembles them. -/
lemma pairSumCrude6_assembly :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ),
      Work.FITop3.IsBoxCoeff Pa φ β →
      (1 / 10 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N →
      Pa.θ * Real.sqrt Pa.N ≤ Pa.N ^ ((3 : ℝ) / 8) →
      (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if β z1 ≠ 0 ∧ β z2 ≠ 0 ∧ z1 ≠ z2 then
            (((Work.FIPlan.gnorm z1).divisors.card : ℕ) : ℝ)
              * ((((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)
                  * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)))
          else 0))
        ≤ C * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
            * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1) :=
  pairSumCrude6_core_of pairSumCrude6_smallU pairSumCrude6_largeU_asm

end

end Work.FIArea3
