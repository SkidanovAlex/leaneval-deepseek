import Mathlib
import Submission.Work.FIArea7.P231M.EpsStepExplicit
import Submission.Work.FIArea7.P231.sqrt_error_le
import Submission.Work.FIPlan.Interface

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea7.P231M

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The counting lemma with an explicit constant -/

lemma gnorm_cast_norm_pub (z : GaussianInt) : (Work.FIPlan.gnorm z : ℝ) = (z.norm : ℝ) := by
  unfold Work.FIPlan.gnorm
  rw [← Int.cast_natCast, Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg (by norm_num) z)]

lemma gnorm_eq_normSq_pub (z : GaussianInt) :
    (Work.FIPlan.gnorm z : ℝ) = Complex.normSq z.toComplex := by
  rw [gnorm_cast_norm_pub, GaussianInt.intCast_real_norm]

lemma gnorm_eq_sq_pub (z : GaussianInt) :
    (Work.FIPlan.gnorm z : ℝ) = ((z.re : ℤ) : ℝ) ^ 2 + ((z.im : ℤ) : ℝ) ^ 2 := by
  rw [gnorm_eq_normSq_pub, Complex.normSq_apply, ← GaussianInt.intCast_re, ← GaussianInt.intCast_im]
  ring

lemma mem_gBox_iff_pub {R : ℤ} {z : GaussianInt} :
    z ∈ Work.FIPlan.gBox R ↔ z.re ∈ Finset.Icc (-R) R ∧ z.im ∈ Finset.Icc (-R) R := by
  rw [Work.FIPlan.gBox, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hzp⟩
    rw [Finset.product_eq_sprod, Finset.mem_product] at hp
    rw [← hzp]
    exact hp
  · rintro ⟨h1, h2⟩
    exact ⟨(z.re, z.im),
      by rw [Finset.product_eq_sprod, Finset.mem_product]; exact ⟨h1, h2⟩, rfl⟩

/-- A finite set of Gaussian integers of norm `≤ M` has at most `25 M` elements (`M ≥ 1`). -/
theorem card_gnorm_le25 : ∀ (M : ℝ), 1 ≤ M → ∀ S : Finset GaussianInt,
    (∀ w ∈ S, (Work.FIPlan.gnorm w : ℝ) ≤ M) → ((S.card : ℝ) ≤ 25 * M) := by
  intro M hM S hS
  set K : ℕ := Nat.ceil (Real.sqrt M) with hK
  have hM0 : (0 : ℝ) < M := by linarith
  have habs : ∀ x : ℝ, x ^ 2 ≤ M → |x| ≤ (K : ℝ) := by
    intro x hx
    have h2 : |x| ≤ Real.sqrt M := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hx
    have h3 : Real.sqrt M ≤ (K : ℝ) := by rw [hK]; exact Nat.le_ceil _
    linarith
  have hsub : S ⊆ Work.FIPlan.gBox (K : ℤ) := by
    intro w hw
    rw [mem_gBox_iff_pub, Finset.mem_Icc, Finset.mem_Icc]
    have h1 : (Work.FIPlan.gnorm w : ℝ) ≤ M := hS w hw
    have hsq := gnorm_eq_sq_pub w
    have hre2 : ((w.re : ℤ) : ℝ) ^ 2 ≤ M := by nlinarith [sq_nonneg ((w.im : ℤ) : ℝ)]
    have him2 : ((w.im : ℤ) : ℝ) ^ 2 ≤ M := by nlinarith [sq_nonneg ((w.re : ℤ) : ℝ)]
    have hre := abs_le.mp (habs _ hre2)
    have him := abs_le.mp (habs _ him2)
    exact ⟨⟨by exact_mod_cast hre.1, by exact_mod_cast hre.2⟩,
           ⟨by exact_mod_cast him.1, by exact_mod_cast him.2⟩⟩
  have hcard_le : S.card ≤ (Work.FIPlan.gBox (K : ℤ)).card := Finset.card_le_card hsub
  have hgBox_card : (Work.FIPlan.gBox (K : ℤ)).card ≤ (2 * K + 1) * (2 * K + 1) := by
    unfold Work.FIPlan.gBox
    refine le_trans Finset.card_image_le ?_
    rw [Finset.product_eq_sprod, Finset.card_product]
    have hc : (Finset.Icc (-(K : ℤ)) (K : ℤ)).card = 2 * K + 1 := by
      rw [Int.card_Icc]
      have h2 : (K : ℤ) + 1 - (-(K : ℤ)) = ((2 * K + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [h2, Int.toNat_natCast]
    rw [hc]
  have hKle : (K : ℝ) ≤ Real.sqrt M + 1 := by
    have := Nat.ceil_lt_add_one (Real.sqrt_nonneg M)
    rw [hK]
    linarith
  have hsqrtM1 : 1 ≤ Real.sqrt M := Real.one_le_sqrt.mpr hM
  have h2K : (2 * (K : ℝ) + 1) ≤ 5 * Real.sqrt M := by nlinarith
  have hsq : (2 * (K : ℝ) + 1) ^ 2 ≤ 25 * M := by
    have h3 : (2 * (K : ℝ) + 1) ^ 2 ≤ (5 * Real.sqrt M) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2K 2
    have h4 : (5 * Real.sqrt M) ^ 2 = 25 * M := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hM0)]; norm_num
    linarith
  calc ((S.card : ℝ)) ≤ (((Work.FIPlan.gBox (K : ℤ)).card : ℕ) : ℝ) := by exact_mod_cast hcard_le
    _ ≤ (((2 * K + 1) * (2 * K + 1) : ℕ) : ℝ) := by exact_mod_cast hgBox_card
    _ = (2 * (K : ℝ) + 1) ^ 2 := by push_cast; ring
    _ ≤ 25 * M := hsq

/-! ## 2. The arithmetic of the reduction -/

/-- The shape `(M+N)^{1/12}(MN)^{11/12}`. -/
def PP (M N : ℝ) : ℝ := (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)

/-- The logarithm `log(MN+2)`. -/
def LL (M N : ℝ) : ℝ := Real.log (M * N + 2)

def KbadConst (Cw Ccard : ℝ) : ℝ := 2 * Cw * Ccard * (3 * Real.sqrt 2 + 6)

def KbConst (Cw Cexp Ccard Cstar : ℝ) : ℝ :=
  (1 / 2) * Cexp * (1 + Real.log 4) ^ 4 * Cstar
    + ((1 / 2) * Cexp * (1 + Real.log 4) ^ 4 + 1) * KbadConst Cw Ccard

lemma PP_nonneg {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) : 0 ≤ PP M N := by
  rw [PP]
  exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_nonneg (mul_nonneg hM hN) _)

lemma PP_rfl (M N : ℝ) : PP M N = (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12) := rfl

lemma LL_rfl (M N : ℝ) : LL M N = Real.log (M * N + 2) := rfl

lemma LL_one_le {M N : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) : 1 ≤ LL M N := by
  rw [LL]
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_one_lt_three
  refine hlog3.le.trans (Real.log_le_log (by norm_num) ?_)
  nlinarith

lemma LL_pos {M N : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) : 0 < LL M N :=
  lt_of_lt_of_le one_pos (LL_one_le hM hN)

theorem epsKbad_le {Cw Ccard M N : ℝ} (hCw : 0 < Cw) (hCcard : 0 < Ccard)
    (hM : 1 ≤ M) (hN : 1 ≤ N) :
    Work.FIArea7.P231.epsKbad Cw M Ccard N ≤ KbadConst Cw Ccard * PP M N := by
  have hN1 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
  have hN0 : (0 : ℝ) ≤ N := le_trans zero_le_one hN
  have hP0 : 0 ≤ PP M N := PP_nonneg hM0 hN0
  have hN'le : ((Work.FIArea7.P231.epsNprime N : ℕ) : ℝ) ≤ 2 * N := by
    rw [Work.FIArea7.P231.epsNprime, Nat.cast_max]
    have h1 : ((Nat.ceil N : ℕ) : ℝ) < N + 1 := Nat.ceil_lt_add_one (by linarith)
    have h2 : ((1 : ℕ) : ℝ) ≤ 2 * N := by push_cast; linarith
    exact max_le h2 (by linarith)
  have hRN : Real.sqrt (M * N) ≤ ((Work.FIArea7.P231.epsRoom M N : ℕ) : ℝ) := by
    have h := Nat.le_ceil (Real.sqrt (M * N))
    rw [Work.FIArea7.P231.epsRoom]
    push_cast
    linarith
  have hRpos : 0 < ((Work.FIArea7.P231.epsRoom M N : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ ((Work.FIArea7.P231.epsRoom M N : ℕ) : ℝ) := by
      exact_mod_cast Work.FIArea7.P231.epsRoom_ge_two M N
    linarith
  have hsqrtNle : Real.sqrt N ≤ Real.sqrt (M * N) := Real.sqrt_le_sqrt (by nlinarith)
  have hMsqrt : M * Real.sqrt N ≤ 3 * PP M N :=
    le_trans (le_add_of_nonneg_right (Real.sqrt_nonneg (M * N))) (by
      simpa [PP] using Work.FIArea7.P231.sqrt_error_le hM hN)
  have hpart1 : M * Real.sqrt ((Work.FIArea7.P231.epsNprime N : ℕ) : ℝ)
      ≤ Real.sqrt 2 * (3 * PP M N) := by
    have h1 : Real.sqrt ((Work.FIArea7.P231.epsNprime N : ℕ) : ℝ)
        ≤ Real.sqrt 2 * Real.sqrt N := by
      calc Real.sqrt ((Work.FIArea7.P231.epsNprime N : ℕ) : ℝ) ≤ Real.sqrt (2 * N) :=
            Real.sqrt_le_sqrt hN'le
        _ = Real.sqrt 2 * Real.sqrt N := Real.sqrt_mul (by norm_num) N
    calc M * Real.sqrt ((Work.FIArea7.P231.epsNprime N : ℕ) : ℝ)
        ≤ M * (Real.sqrt 2 * Real.sqrt N) := mul_le_mul_of_nonneg_left h1 hM0
      _ = Real.sqrt 2 * (M * Real.sqrt N) := by ring
      _ ≤ Real.sqrt 2 * (3 * PP M N) := mul_le_mul_of_nonneg_left hMsqrt (by positivity)
  have hpart2 : M * (((Work.FIArea7.P231.epsNprime N : ℕ) : ℝ)
        / ((Work.FIArea7.P231.epsRoom M N : ℕ) : ℝ)) ≤ 2 * (3 * PP M N) := by
    have hdiv : ((Work.FIArea7.P231.epsNprime N : ℕ) : ℝ)
          / ((Work.FIArea7.P231.epsRoom M N : ℕ) : ℝ) ≤ 2 * Real.sqrt N := by
      rw [div_le_iff₀ hRpos]
      have hsqq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (le_of_lt hN1)
      have h2 : 2 * N ≤ 2 * Real.sqrt N * Real.sqrt (M * N) := by
        nlinarith [hsqrtNle, Real.sqrt_nonneg N, Real.sqrt_nonneg (M * N), hsqq]
      have h4 : 2 * Real.sqrt N * Real.sqrt (M * N)
          ≤ 2 * Real.sqrt N * ((Work.FIArea7.P231.epsRoom M N : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hRN (by positivity)
      linarith [hN'le, h2, h4]
    calc M * (((Work.FIArea7.P231.epsNprime N : ℕ) : ℝ)
          / ((Work.FIArea7.P231.epsRoom M N : ℕ) : ℝ))
        ≤ M * (2 * Real.sqrt N) := mul_le_mul_of_nonneg_left hdiv hM0
      _ = 2 * (M * Real.sqrt N) := by ring
      _ ≤ 2 * (3 * PP M N) := mul_le_mul_of_nonneg_left hMsqrt (by norm_num)
  calc Work.FIArea7.P231.epsKbad Cw M Ccard N
      = Cw * (M * (2 * Ccard * (Real.sqrt ((Work.FIArea7.P231.epsNprime N : ℕ) : ℝ)
          + ((Work.FIArea7.P231.epsNprime N : ℕ) : ℝ)
            / ((Work.FIArea7.P231.epsRoom M N : ℕ) : ℝ)))) := by
        rw [Work.FIArea7.P231.epsKbad, Work.FIArea7.P231.epsKz]
        ring
    _ = 2 * Cw * Ccard * (M * Real.sqrt ((Work.FIArea7.P231.epsNprime N : ℕ) : ℝ)
          + M * (((Work.FIArea7.P231.epsNprime N : ℕ) : ℝ)
            / ((Work.FIArea7.P231.epsRoom M N : ℕ) : ℝ))) := by ring
    _ ≤ 2 * Cw * Ccard * (Real.sqrt 2 * (3 * PP M N) + 2 * (3 * PP M N)) :=
        mul_le_mul_of_nonneg_left (add_le_add hpart1 hpart2) (by positivity)
    _ = KbadConst Cw Ccard * PP M N := by
        rw [KbadConst]; ring

theorem epsBound0_le {Cw Cexp Ccard Cstar Astar M N : ℝ} (hCw : 0 < Cw) (hCcard : 0 < Ccard)
    (hCexp : 0 < Cexp) (hCstar : 0 < Cstar) (hAstar : 0 ≤ Astar) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    Work.FIArea7.P231.epsBound0 Cw Cexp M Ccard N (Cstar * PP M N * LL M N ^ Astar)
      ≤ KbConst Cw Cexp Ccard Cstar * PP M N * LL M N ^ (Astar + 8) := by
  have hL1 : 1 ≤ LL M N := LL_one_le hM hN
  have hL0 : 0 < LL M N := LL_pos hM hN
  have hKbad := epsKbad_le hCw hCcard hM hN
  have hLA1 : (1 : ℝ) ≤ LL M N ^ Astar := Real.one_le_rpow hL1 hAstar
  have hKB0 : 0 ≤ KbadConst Cw Ccard := by rw [KbadConst]; positivity
  have hKb0 : 0 ≤ KbConst Cw Cexp Ccard Cstar := by
    rw [KbConst]
    have h1 : (0 : ℝ) ≤ (1 / 2) * Cexp * (1 + Real.log 4) ^ 4 * Cstar := by positivity
    have h2 : (0 : ℝ) ≤ ((1 / 2) * Cexp * (1 + Real.log 4) ^ 4 + 1) * KbadConst Cw Ccard := by
      rw [KbadConst]; positivity
    linarith
  rw [Work.FIArea7.P231.epsBound0]
  simp only [LL]
  set P : ℝ := PP M N with hPdef
  set L : ℝ := Real.log (M * N + 2) with hLdef
  set LA : ℝ := L ^ Astar with hLAdef
  set A : ℝ := (1 / 2) * Cexp * (1 + Real.log 4) ^ 4 with hAdef
  have hP0 : 0 ≤ P := by rw [hPdef]; exact PP_nonneg (le_trans zero_le_one hM) (le_trans zero_le_one hN)
  have hL1' : (1 : ℝ) ≤ L := by rw [hLdef]; exact hL1
  have hL0' : 0 < L := by rw [hLdef]; exact hL0
  have hLA1' : (1 : ℝ) ≤ LA := by rw [hLAdef, hLdef]; exact hLA1
  have hLA0 : (0 : ℝ) ≤ LA := le_trans zero_le_one hLA1'
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hL4pos : (0 : ℝ) < L ^ 4 := by positivity
  have hKbadv : Work.FIArea7.P231.epsKbad Cw M Ccard N ≤ KbadConst Cw Ccard * P := by
    rw [hPdef]; exact hKbad
  have hpow4 : L ^ (Astar + 4) = LA * L ^ 4 := by
    have h1 : L ^ (Astar + 4) = L ^ Astar * L ^ (4 : ℝ) := Real.rpow_add hL0' Astar 4
    have h2 : L ^ (4 : ℝ) = L ^ 4 := Real.rpow_natCast L 4
    rw [h1, h2, hLAdef]
  have hpow8 : L ^ (Astar + 8) = L ^ (Astar + 4) * L ^ 4 := by
    have h1 : L ^ (Astar + 8) = L ^ (Astar + 4) * L ^ (4 : ℝ) := by
      rw [show Astar + 8 = (Astar + 4) + 4 by ring]
      exact Real.rpow_add hL0' (Astar + 4) 4
    have h2 : L ^ (4 : ℝ) = L ^ 4 := Real.rpow_natCast L 4
    rw [h1, h2]
  have hL4one : (1 : ℝ) ≤ L ^ 4 := one_le_pow₀ hL1'
  have hLA4one : (1 : ℝ) ≤ LA * L ^ 4 := by
    have h := mul_le_mul hLA1' hL4one (by norm_num : (0 : ℝ) ≤ 1) hLA0
    simpa using h
  have s1 : A * L ^ 4 * (Cstar * P * LA + Work.FIArea7.P231.epsKbad Cw M Ccard N)
        + Work.FIArea7.P231.epsKbad Cw M Ccard N
      ≤ A * L ^ 4 * (Cstar * P * LA + KbadConst Cw Ccard * P) + KbadConst Cw Ccard * P := by
    have h1 : A * L ^ 4 * (Cstar * P * LA + Work.FIArea7.P231.epsKbad Cw M Ccard N)
        ≤ A * L ^ 4 * (Cstar * P * LA + KbadConst Cw Ccard * P) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hKbadv) (by positivity)
    linarith [h1, hKbadv]
  have s2 : A * L ^ 4 * (Cstar * P * LA + KbadConst Cw Ccard * P) + KbadConst Cw Ccard * P
      ≤ (A * Cstar + A * KbadConst Cw Ccard + KbadConst Cw Ccard) * P * L ^ (Astar + 4) := by
    rw [hpow4]
    have hX : A * KbadConst Cw Ccard * (P * L ^ 4)
        ≤ A * KbadConst Cw Ccard * (P * (LA * L ^ 4)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine mul_le_mul_of_nonneg_left ?_ hP0
      nlinarith [hLA4one]
    have hY : KbadConst Cw Ccard * P
        ≤ KbadConst Cw Ccard * (P * (LA * L ^ 4)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact le_mul_of_one_le_right hP0 hLA4one
    have e1 : A * L ^ 4 * (Cstar * P * LA + KbadConst Cw Ccard * P)
          + KbadConst Cw Ccard * P
        = A * Cstar * (P * (LA * L ^ 4))
          + A * KbadConst Cw Ccard * (P * L ^ 4) + KbadConst Cw Ccard * P := by ring
    rw [e1]
    calc A * Cstar * (P * (LA * L ^ 4)) + A * KbadConst Cw Ccard * (P * L ^ 4)
            + KbadConst Cw Ccard * P
        ≤ A * Cstar * (P * (LA * L ^ 4)) + A * KbadConst Cw Ccard * (P * (LA * L ^ 4))
            + KbadConst Cw Ccard * (P * (LA * L ^ 4)) := by linarith [hX, hY]
      _ = (A * Cstar + A * KbadConst Cw Ccard + KbadConst Cw Ccard) * P * (LA * L ^ 4) := by ring
  have s3 : (A * Cstar + A * KbadConst Cw Ccard + KbadConst Cw Ccard) * P * L ^ (Astar + 4)
      ≤ KbConst Cw Cexp Ccard Cstar * P * L ^ (Astar + 8) := by
    have hcoef : A * Cstar + A * KbadConst Cw Ccard + KbadConst Cw Ccard
        = KbConst Cw Cexp Ccard Cstar := by
      rw [KbConst, hAdef]; ring
    rw [hcoef, hpow8]
    have hL4one' : (1 : ℝ) ≤ L ^ 4 := one_le_pow₀ hL1'
    calc KbConst Cw Cexp Ccard Cstar * P * L ^ (Astar + 4)
        = (KbConst Cw Cexp Ccard Cstar * P) * L ^ (Astar + 4) := by ring
      _ ≤ (KbConst Cw Cexp Ccard Cstar * P) * (L ^ (Astar + 4) * L ^ 4) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) hL4one')
            (by positivity)
      _ = KbConst Cw Cexp Ccard Cstar * P * (L ^ (Astar + 4) * L ^ 4) := by ring
  exact le_trans s1 (le_trans s2 s3)

theorem epsDen_le {Cstar Astar M N : ℝ} (hCstar : 0 < Cstar) (hAstar : 0 ≤ Astar)
    (hM : 1 ≤ M) (hN : 1 ≤ N) :
    Work.FIArea7.P231.epsDen M N (Cstar * PP M N * LL M N ^ Astar)
      ≤ (Cstar + 3) * PP M N * LL M N ^ (Astar + 8) := by
  have hL1 : 1 ≤ LL M N := LL_one_le hM hN
  have hL0 : 0 < LL M N := LL_pos hM hN
  have hLA1 : (1 : ℝ) ≤ LL M N ^ Astar := Real.one_le_rpow hL1 hAstar
  have hsqr : M * Real.sqrt N + Real.sqrt (M * N) ≤ 3 * PP M N := by
    simpa [PP] using Work.FIArea7.P231.sqrt_error_le hM hN
  rw [Work.FIArea7.P231.epsDen]
  simp only [LL]
  set P : ℝ := PP M N with hPdef
  set L : ℝ := Real.log (M * N + 2) with hLdef
  have hP0 : 0 ≤ P := by rw [hPdef]; exact PP_nonneg (le_trans zero_le_one hM) (le_trans zero_le_one hN)
  have hL1' : (1 : ℝ) ≤ L := by rw [hLdef]; exact hL1
  have hL0' : 0 < L := by rw [hLdef]; exact hL0
  have hLA1' : (1 : ℝ) ≤ L ^ Astar := by rw [hLdef]; exact hLA1
  have hsqr' : M * Real.sqrt N + Real.sqrt (M * N) ≤ 3 * P := by rw [hPdef]; exact hsqr
  have h1 : Cstar * P * L ^ Astar + M * Real.sqrt N + Real.sqrt (M * N)
      ≤ Cstar * P * L ^ Astar + 3 * P := by linarith [hsqr']
  have h2 : Cstar * P * L ^ Astar + 3 * P ≤ (Cstar + 3) * P * L ^ Astar := by
    have h3 : 3 * P ≤ 3 * P * L ^ Astar := le_mul_of_one_le_right (by positivity) hLA1'
    nlinarith [h3, hP0, hLA1', hCstar.le, Real.rpow_nonneg (le_of_lt hL0') Astar]
  have h5 : L ^ 8 * (Cstar * P * L ^ Astar + M * Real.sqrt N + Real.sqrt (M * N))
      ≤ L ^ 8 * ((Cstar + 3) * P * L ^ Astar) :=
    mul_le_mul_of_nonneg_left (le_trans h1 h2) (by positivity)
  have hpow : L ^ (Astar + 8) = L ^ Astar * L ^ 8 := by
    have h1 : L ^ (Astar + 8) = L ^ Astar * L ^ (8 : ℝ) := Real.rpow_add hL0' Astar 8
    have h2 : L ^ (8 : ℝ) = L ^ 8 := Real.rpow_natCast L 8
    rw [h1, h2]
  rw [hpow]
  refine h5.trans (le_of_eq ?_)
  ring

/-- The final comparison of the reduction. -/
theorem reducedArith {Cw Cexp Ccard Cstar Astar M N : ℝ} (hCw : 0 < Cw) (hCcard : 0 < Ccard)
    (hCexp : 0 < Cexp) (hCstar : 0 < Cstar) (hAstar : 0 ≤ Astar) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    Work.FIArea7.P231.epsDen M N (Cstar * PP M N * LL M N ^ Astar)
        + Work.FIArea7.P231.epsBound0 Cw Cexp M Ccard N (Cstar * PP M N * LL M N ^ Astar)
      ≤ (Cstar + 3 + KbConst Cw Cexp Ccard Cstar) * PP M N * LL M N ^ (Astar + 16) := by
  have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
  have hN0 : (0 : ℝ) ≤ N := le_trans zero_le_one hN
  have hP0 : 0 ≤ PP M N := PP_nonneg hM0 hN0
  have hL1 : 1 ≤ LL M N := LL_one_le hM hN
  have h1 := epsDen_le hCstar hAstar hM hN
  have h2 := epsBound0_le hCw hCcard hCexp hCstar hAstar hM hN
  have hKb0 : 0 ≤ KbConst Cw Cexp Ccard Cstar := by
    rw [KbConst]
    have hA : (0 : ℝ) ≤ (1 / 2) * Cexp * (1 + Real.log 4) ^ 4 := by positivity
    have hKB : (0 : ℝ) ≤ KbadConst Cw Ccard := by rw [KbadConst]; positivity
    exact add_nonneg (by positivity) (mul_nonneg (by linarith [hA]) hKB)
  have hsum : Work.FIArea7.P231.epsDen M N (Cstar * PP M N * LL M N ^ Astar)
        + Work.FIArea7.P231.epsBound0 Cw Cexp M Ccard N (Cstar * PP M N * LL M N ^ Astar)
      ≤ (Cstar + 3 + KbConst Cw Cexp Ccard Cstar) * PP M N * LL M N ^ (Astar + 8) := by
    have h3 : (Cstar + 3) * PP M N * LL M N ^ (Astar + 8)
          + KbConst Cw Cexp Ccard Cstar * PP M N * LL M N ^ (Astar + 8)
        = (Cstar + 3 + KbConst Cw Cexp Ccard Cstar) * PP M N * LL M N ^ (Astar + 8) := by ring
    linarith [h1, h2, h3]
  have hpow : LL M N ^ (Astar + 16) = LL M N ^ (Astar + 8) * LL M N ^ 8 := by
    have h1 : LL M N ^ (Astar + 16) = LL M N ^ (Astar + 8) * LL M N ^ (8 : ℝ) := by
      rw [show Astar + 16 = (Astar + 8) + 8 by ring]
      exact Real.rpow_add (LL_pos hM hN) (Astar + 8) 8
    have h2 : LL M N ^ (8 : ℝ) = LL M N ^ 8 := Real.rpow_natCast (LL M N) 8
    rw [h1, h2]
  have hL8 : (1 : ℝ) ≤ LL M N ^ 8 := one_le_pow₀ hL1
  have hstep : (Cstar + 3 + KbConst Cw Cexp Ccard Cstar) * PP M N * LL M N ^ (Astar + 8)
      ≤ (Cstar + 3 + KbConst Cw Cexp Ccard Cstar) * PP M N * LL M N ^ (Astar + 16) := by
    rw [hpow]
    have hle : LL M N ^ (Astar + 8) ≤ LL M N ^ (Astar + 8) * LL M N ^ 8 :=
      le_mul_of_one_le_right (by positivity) hL8
    calc (Cstar + 3 + KbConst Cw Cexp Ccard Cstar) * PP M N * LL M N ^ (Astar + 8)
        = ((Cstar + 3 + KbConst Cw Cexp Ccard Cstar) * PP M N) * LL M N ^ (Astar + 8) := by ring
      _ ≤ ((Cstar + 3 + KbConst Cw Cexp Ccard Cstar) * PP M N)
            * (LL M N ^ (Astar + 8) * LL M N ^ 8) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (Cstar + 3 + KbConst Cw Cexp Ccard Cstar) * PP M N
            * (LL M N ^ (Astar + 8) * LL M N ^ 8) := by ring
  exact hsum.trans hstep

end

end Work.FIArea7.P231M
