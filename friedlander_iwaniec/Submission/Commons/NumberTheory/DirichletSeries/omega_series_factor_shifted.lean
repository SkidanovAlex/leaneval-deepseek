import Mathlib
import Submission.Commons.NumberTheory.DirichletSeries.omega_euler_product
import Submission.Commons.NumberTheory.Mertens.tsum_primes_eq_sum_rpowDiff
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Submission.Commons.NumberTheory.Zeta.riemannZeta_residue_uniform_bound
import Submission.Commons.NumberTheory.LSeries.norm_riemannZeta_le_five_mul_log
import Submission.Commons.NumberTheory.Zeta.zeta_norm_le_const_of_three_le_re
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_negStrip_bound
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_logDeriv_bound
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_at_height_farLeft_neg
import Submission.Port.LogDerivCompat
set_option maxHeartbeats 4000000

open Complex Filter
open scoped Topology BigOperators

namespace Commons.NumberTheory.DirichletSeries


noncomputable def omegaLocal (w : ℂ) (z : ℂ) : ℂ := (1 - z) ^ w * (1 + w * z)

private lemma quarter_rpow_le_sixteen : (1/4:ℝ)^(-3/2:ℝ) ≤ 16 := by
  have h1 : (1/4:ℝ)^(-3/2:ℝ) ≤ (1/4:ℝ)^(-2:ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
  have h2 : (1/4:ℝ)^(-2:ℝ) = 16 := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 1/4), Real.rpow_two]
    norm_num
  exact h1.trans (le_of_eq h2)

private lemma exp_pi_half_le_nine : Real.exp (Real.pi/2) ≤ 9 := by
  have h1 : Real.exp (Real.pi/2) ≤ Real.exp 2 := by
    apply Real.exp_le_exp.mpr
    linarith [Real.pi_lt_four]
  have h2 : Real.exp (2:ℝ) = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  rw [h2] at h1
  nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]

private lemma norm_le_of_mem_segment_zero {z y : ℂ} (hy : y ∈ segment ℝ (0:ℂ) z) : ‖y‖ ≤ ‖z‖ := by
  rw [segment_eq_image] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  beta_reduce
  rw [smul_zero, zero_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact mul_le_of_le_one_left (norm_nonneg z) ht.2

private lemma one_sub_mem_slitPlane {z : ℂ} (hz : ‖z‖ ≤ 3/4) : (1 - z) ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have h1 : z.re ≤ ‖z‖ := Complex.re_le_norm z
  simp only [Complex.sub_re, Complex.one_re]
  linarith

private lemma norm_cpow_sub_one_le {w z : ℂ} (hw : ‖w‖ ≤ 1/2) (hz : ‖z‖ ≤ 3/4) :
    ‖(1 - z) ^ (w - 1)‖ ≤ 200 := by
  have hsp : (1 - z) ∈ slitPlane := one_sub_mem_slitPlane hz
  have hnorm_le : ‖(1 - z) ^ (w - 1)‖ ≤ ‖1 - z‖ ^ ((w-1).re) / Real.exp ((1 - z).arg * (w-1).im) :=
    Complex.norm_cpow_le (1 - z) (w - 1)
  have hnorm1zpos : (0:ℝ) < ‖1 - z‖ := norm_pos_iff.mpr (slitPlane_ne_zero hsp)
  have hre1 : (1:ℝ)/4 ≤ ‖1 - z‖ := by
    have h2 : (1:ℝ) - ‖z‖ ≤ ‖1 - z‖ := by
      have h3 := norm_add_le ((1:ℂ) - z) z
      rw [sub_add_cancel, norm_one] at h3
      linarith
    linarith [h2, hz]
  have hwre : |w.re| ≤ 1/2 := by
    have := Complex.abs_re_le_norm w; linarith
  have hwle : (w-1).re ≤ 0 := by simp only [Complex.sub_re, Complex.one_re]; linarith [(abs_le.mp hwre).2]
  have hwge : -3/2 ≤ (w-1).re := by simp only [Complex.sub_re, Complex.one_re]; linarith [(abs_le.mp hwre).1]
  have himw : |(w-1).im| ≤ 1/2 := by
    have h2 : (w-1).im = w.im := by simp
    rw [h2]; have := Complex.abs_im_le_norm w; linarith
  have hbase : ‖1 - z‖ ^ ((w-1).re) ≤ (1/4:ℝ)^(-3/2:ℝ) :=
    (Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ) < 1/4) hre1 hwle).trans
      (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hwge)
  have hexp : 1 / Real.exp ((1 - z).arg * (w-1).im) ≤ Real.exp (Real.pi/2) := by
    rw [div_le_iff₀ (Real.exp_pos _), ← Real.exp_add, Real.one_le_exp_iff]
    have himw2 : |(w - 1).im| ≤ (2:ℝ)⁻¹ := by simpa using himw
    have hb : |(1-z).arg * (w-1).im| ≤ Real.pi/2 := by
      rw [abs_mul]
      exact mul_le_mul (Complex.abs_arg_le_pi (1-z)) himw2 (abs_nonneg _) Real.pi_pos.le
    linarith [neg_abs_le ((1-z).arg * (w-1).im)]
  calc ‖(1 - z) ^ (w - 1)‖
        ≤ ‖1 - z‖ ^ ((w-1).re) / Real.exp ((1 - z).arg * (w-1).im) := hnorm_le
    _ = ‖1 - z‖ ^ ((w-1).re) * (1 / Real.exp ((1 - z).arg * (w-1).im)) := by rw [div_eq_mul_inv, one_div]
    _ ≤ 16 * Real.exp (Real.pi/2) := by
        apply mul_le_mul (hbase.trans quarter_rpow_le_sixteen) hexp (by positivity) (by norm_num)
    _ ≤ 200 := by
        have := exp_pi_half_le_nine
        nlinarith

private lemma hasDerivAt_omegaLocal {w z : ℂ} (hz : (1 - z) ∈ slitPlane) :
    HasDerivAt (omegaLocal w) (-(w * (1 + w) * z * (1 - z) ^ (w - 1))) z := by
  have h1 : HasDerivAt (fun z : ℂ => (1:ℂ) - z) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1:ℂ)
  have h2 : HasDerivAt (fun z : ℂ => (1 - z) ^ w) ((-1) * (w * (1 - z) ^ (w - 1))) z := by
    have h := h1.cpow_const (c := w) hz
    simpa using h
  have h3 : HasDerivAt (fun z : ℂ => (1:ℂ) + w * z) w z := by
    have hb : HasDerivAt (fun z : ℂ => w * z) (w * 1) z := (hasDerivAt_id z).const_mul w
    have h := hb.const_add (1:ℂ)
    simpa using h
  have h4 := h2.mul h3
  have hne : (1 - z) ≠ 0 := slitPlane_ne_zero hz
  have hcp : (1 - z) ^ w = (1 - z) ^ (w - 1) * (1 - z) := by
    have hw1 : (1 - z) ^ w = (1 - z) ^ ((w - 1) + 1) := by congr 1; ring
    rw [hw1, Complex.cpow_add _ _ hne, Complex.cpow_one]
  have key : ((-1) * (w * (1 - z) ^ (w - 1))) * (1 + w * z) + (1 - z) ^ w * w
      = -(w * (1 + w) * z * (1 - z) ^ (w - 1)) := by
    rw [hcp]; ring
  rw [key] at h4
  exact h4

private lemma norm_deriv_omegaLocal_le {w z y : ℂ} (hw : ‖w‖ ≤ 1/2) (hz : ‖z‖ ≤ 3/4)
    (hy : y ∈ segment ℝ (0:ℂ) z) : ‖deriv (omegaLocal w) y‖ ≤ 200 * ‖z‖ := by
  have hsp : (1 - y) ∈ slitPlane :=
    one_sub_mem_slitPlane (le_trans (norm_le_of_mem_segment_zero hy) hz)
  rw [(hasDerivAt_omegaLocal hsp).deriv]
  have hyz : ‖y‖ ≤ ‖z‖ := norm_le_of_mem_segment_zero hy
  have hbnd : ‖(1 - y) ^ (w - 1)‖ ≤ 200 := norm_cpow_sub_one_le hw (le_trans hyz hz)
  have h1w : ‖1 + w‖ ≤ 3/2 := by
    calc ‖(1:ℂ) + w‖ ≤ ‖(1:ℂ)‖ + ‖w‖ := norm_add_le _ _
      _ = 1 + ‖w‖ := by rw [norm_one]
      _ ≤ 3/2 := by linarith
  have heq : ‖-(w * (1 + w) * y * (1 - y) ^ (w - 1))‖ =
      ‖w‖ * ‖1 + w‖ * ‖y‖ * ‖(1 - y) ^ (w - 1)‖ := by
    rw [norm_neg, norm_mul, norm_mul, norm_mul]
  rw [heq]
  have hA : ‖w‖ * ‖1 + w‖ ≤ (1/2) * (3/2) :=
    mul_le_mul hw h1w (norm_nonneg _) (by norm_num)
  have hB : ‖y‖ * ‖(1 - y) ^ (w - 1)‖ ≤ ‖z‖ * 200 :=
    mul_le_mul hyz hbnd (norm_nonneg _) (norm_nonneg _)
  have hAB : ‖w‖ * ‖1 + w‖ * ‖y‖ * ‖(1 - y) ^ (w - 1)‖ ≤ (1/2)*(3/2)*(‖z‖*200) := by
    rw [mul_assoc]
    exact mul_le_mul hA hB (by positivity) (by positivity)
  nlinarith [hAB, norm_nonneg z]

lemma norm_omegaLocal_sub_one_le {w z : ℂ} (hw : ‖w‖ ≤ 1/2) (hz : ‖z‖ ≤ 3/4) :
    ‖omegaLocal w z - 1‖ ≤ 200 * ‖z‖ ^ 2 := by
  have hdiff : ∀ y ∈ segment ℝ (0:ℂ) z, DifferentiableAt ℂ (omegaLocal w) y := by
    intro y hy
    exact (hasDerivAt_omegaLocal (one_sub_mem_slitPlane
      (le_trans (norm_le_of_mem_segment_zero hy) hz))).differentiableAt
  have hbound : ∀ y ∈ segment ℝ (0:ℂ) z, ‖deriv (omegaLocal w) y‖ ≤ 200 * ‖z‖ :=
    fun y hy => norm_deriv_omegaLocal_le hw hz hy
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_segment (0:ℂ) z)
    (left_mem_segment ℝ (0:ℂ) z) (right_mem_segment ℝ (0:ℂ) z)
  have h0 : omegaLocal w 0 = 1 := by simp [omegaLocal]
  rw [h0, sub_zero] at hmain
  calc ‖omegaLocal w z - 1‖ ≤ 200 * ‖z‖ * ‖z‖ := hmain
    _ = 200 * ‖z‖ ^ 2 := by ring


section Hanalytic

private lemma two_rpow_neg_three_quarters_le : (2:ℝ)^(-3/4:ℝ) ≤ 3/4 := by
  have h1 : (2:ℝ)^(-3/4:ℝ) ≤ (2:ℝ)^(-1/2:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h2 : (2:ℝ)^(-1/2:ℝ) = (Real.sqrt 2)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have h3 : (4/3:ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h4 : (Real.sqrt 2)⁻¹ ≤ ((4:ℝ)/3)⁻¹ :=
    (inv_le_inv₀ (Real.sqrt_pos.2 (by norm_num)) (by norm_num)).mpr h3
  have h5 : (((4:ℝ)/3))⁻¹ = 3/4 := by norm_num
  rw [h2] at h1
  linarith [h1, h4, h5.le]

noncomputable def omegaLocalHat (w : ℂ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  omegaLocal w (((p:ℕ):ℂ)^(-s)) - 1

noncomputable def Hfun (w : ℂ) (s : ℂ) : ℂ :=
  ∏' p : Nat.Primes, (1 + omegaLocalHat w p s)

def omK : Set ℂ := {s : ℂ | 3/4 < s.re}

lemma isOpen_omK : IsOpen omK := isOpen_lt continuous_const continuous_re

lemma norm_prime_cpow_le {p : Nat.Primes} {s : ℂ} (hs : s ∈ omK) :
    ‖(((p:ℕ):ℂ)^(-s))‖ ≤ 3/4 := by
  have hsr : (3/4:ℝ) < s.re := hs
  have hp2 : (2:ℝ) ≤ (p:ℕ) := by exact_mod_cast p.prop.two_le
  have hp0 : (0:ℝ) < ((p:ℕ):ℝ) := by exact_mod_cast p.prop.pos
  have hpcast : (((p:ℕ):ℂ)) = ((((p:ℕ):ℝ):ℂ)) := by norm_num
  rw [hpcast, Complex.norm_cpow_eq_rpow_re_of_pos hp0]
  simp only [Complex.neg_re]
  have h1 : (((p:ℕ):ℝ)^(-s.re)) ≤ (2:ℝ)^(-s.re) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
  have h2 : (2:ℝ)^(-s.re) ≤ (2:ℝ)^(-3/4:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  linarith [h1, h2, two_rpow_neg_three_quarters_le]

lemma norm_omegaLocalHat_le {w : ℂ} (hw : ‖w‖ ≤ 1/2) {p : Nat.Primes} {s : ℂ} (hs : s ∈ omK) :
    ‖omegaLocalHat w p s‖ ≤ 200 * ((p:ℕ):ℝ)^(-(3/2:ℝ)) := by
  have hsr : (3/4:ℝ) < s.re := hs
  have h1 := norm_omegaLocal_sub_one_le hw (norm_prime_cpow_le (p:=p) hs)
  have hp0 : (0:ℝ) < ((p:ℕ):ℝ) := by exact_mod_cast p.prop.pos
  have hp1 : (1:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast p.prop.one_le
  have h2 : ‖(((p:ℕ):ℂ)^(-s))‖ ^ 2 ≤ ((p:ℕ):ℝ)^(-(3/2:ℝ)) := by
    have hpcast : (((p:ℕ):ℂ)) = ((((p:ℕ):ℝ):ℂ)) := by norm_num
    rw [hpcast, Complex.norm_cpow_eq_rpow_re_of_pos hp0]
    simp only [Complex.neg_re]
    rw [← Real.rpow_two, ← Real.rpow_mul hp0.le]
    apply Real.rpow_le_rpow_of_exponent_le hp1
    linarith
  have h3 : 200 * ‖(((p:ℕ):ℂ)^(-s))‖ ^ 2 ≤ 200 * ((p:ℕ):ℝ)^(-(3/2:ℝ)) :=
    mul_le_mul_of_nonneg_left h2 (by norm_num)
  simpa only [omegaLocalHat] using h1.trans h3

lemma differentiableOn_omegaLocal_comp {w : ℂ} (p : Nat.Primes) :
    DifferentiableOn ℂ (fun s : ℂ => omegaLocal w (((p:ℕ):ℂ)^(-s))) omK := by
  have hz : (((p:ℕ):ℂ)) ≠ 0 := by
    have hp0 : (0:ℝ) < ((p:ℕ):ℝ) := by exact_mod_cast p.prop.pos
    have : (((p:ℕ):ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hp0
    simpa using this
  haveI hzn : NeZero (((p:ℕ):ℂ)) := ⟨hz⟩
  intro s hs
  have hsp : (1 - (((p:ℕ):ℂ)^(-s))) ∈ slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left
    have h1 : (((p:ℕ):ℂ)^(-s)).re ≤ ‖(((p:ℕ):ℂ)^(-s))‖ := Complex.re_le_norm _
    have h2 : ‖(((p:ℕ):ℂ)^(-s))‖ ≤ 3/4 := norm_prime_cpow_le (p:=p) hs
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have hz_diff : DifferentiableAt ℂ (fun z : ℂ => omegaLocal w z) (((p:ℕ):ℂ)^(-s)) := by
    have h1 : DifferentiableAt ℂ (fun z : ℂ => (1 - z) ^ w) (((p:ℕ):ℂ)^(-s)) :=
      ((differentiableAt_const (c := (1:ℂ))).sub differentiableAt_id).cpow_const hsp
    have h2 : DifferentiableAt ℂ (fun z : ℂ => (1:ℂ) + w * z) (((p:ℕ):ℂ)^(-s)) :=
      (differentiableAt_const (c := (1:ℂ))).add
        ((differentiableAt_const (c := w)).mul differentiableAt_id)
    exact h1.mul h2
  have hs_diff : DifferentiableAt ℂ (fun s : ℂ => (((p:ℕ):ℂ))^(-s)) s := by
    have h2 := (differentiableAt_const_cpow_of_neZero (((p:ℕ):ℂ)) (-s)).comp s
      (show DifferentiableAt ℂ (fun s : ℂ => -s) s by fun_prop)
    exact h2
  exact (hz_diff.comp s hs_diff).differentiableWithinAt

lemma summable_omMajorant : Summable (fun p : Nat.Primes => 200 * (((p:ℕ):ℝ))^(-(3/2:ℝ))) := by
  have h : Summable (fun n : ℕ => ((n:ℝ))^(-(3/2:ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  exact (h.comp_injective Nat.Primes.coe_nat_injective).mul_left 200

theorem analyticOnNhd_Hfun {w : ℂ} (hw : ‖w‖ ≤ 1/2) :
    AnalyticOnNhd ℂ (Hfun w) omK := by
  have hfac : ∀ p : Nat.Primes,
      ContinuousOn (fun s : ℂ => omegaLocalHat w p s) omK := by
    intro p
    have h := (differentiableOn_omegaLocal_comp (w:=w) p).continuousOn
    refine (h.sub (continuousOn_const (c := (1:ℂ)))).congr ?_
    intro s hs
    simp only [omegaLocalHat, Pi.sub_apply]
  have hprod : HasProdLocallyUniformlyOn (fun p : Nat.Primes => fun s : ℂ => 1 + omegaLocalHat w p s)
      (fun s : ℂ => ∏' p : Nat.Primes, (1 + omegaLocalHat w p s)) omK :=
    Summable.hasProdLocallyUniformlyOn_one_add (isOpen_omK) (summable_omMajorant)
      (Eventually.of_forall (fun p => fun s hs => norm_omegaLocalHat_le hw hs)) hfac
  have htend := hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hprod
  have hdiff : DifferentiableOn ℂ (fun s : ℂ => ∏' p : Nat.Primes, (1 + omegaLocalHat w p s)) omK :=
    htend.differentiableOn (Eventually.of_forall (fun N => by
      have hN : DifferentiableOn ℂ (∏ i ∈ N, (fun s' : ℂ => 1 + omegaLocalHat w i s')) omK := by
        refine DifferentiableOn.finset_prod (fun p hp => ?_)
        refine (differentiableOn_omegaLocal_comp (w:=w) p).congr (fun s hs => ?_)
        simp only [omegaLocalHat]; ring
      refine hN.congr (fun x hx => ?_)
      simp only [Finset.prod_apply])) isOpen_omK
  exact hdiff.analyticOnNhd isOpen_omK

end Hanalytic


noncomputable def Dser (w : ℂ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (((1 + w) ^ n.primeFactors.card : ℂ) * (n:ℂ)^(-s))

lemma Dser_coeff_bound (w : ℂ) {e : ℝ} (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ‖(((1 + w) ^ n.primeFactors.card : ℂ))‖ ≤ C * (n:ℝ)^e := by
  obtain ⟨C, hC, hCc⟩ := pow_card_primeFactors_le_const_mul_rpow (‖1+w‖+1) e (by positivity) he
  refine ⟨C, hC, fun n hn => ?_⟩
  rw [norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _) (by linarith) _).trans (hCc n hn)

private lemma differentiableOn_term (w : ℂ) (n : ℕ) {U : Set ℂ}
    (hU : ∀ s' ∈ U, s' ≠ 0) :
    DifferentiableOn ℂ (fun s' : ℂ => (((1 + w) ^ n.primeFactors.card : ℂ) * (n:ℂ)^(-s'))) U := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine (differentiableOn_const (c := (0:ℂ))).congr ?_
    intro s' hs'
    rw [Nat.primeFactors_zero, Finset.card_empty, pow_zero, one_mul, Nat.cast_zero]
    exact Complex.zero_cpow (neg_ne_zero.mpr (hU s' hs'))
  · have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
    haveI : NeZero (n:ℂ) := ⟨hnC⟩
    exact (((differentiable_const_cpow_of_neZero (n:ℂ)).comp differentiable_neg).const_mul _).differentiableOn

lemma analyticOnNhd_Dser (w : ℂ) :
    AnalyticOnNhd ℂ (Dser w) {s : ℂ | 1 < s.re} := by
  intro s hs
  have hsr : (1:ℝ) < s.re := hs
  set e : ℝ := (s.re - 1)/2 with he
  have hepos : 0 < e := by rw [he]; linarith
  obtain ⟨C, hCpos, hC⟩ := Dser_coeff_bound w hepos
  have hopen : IsOpen {s' : ℂ | 1 + 3*e/2 < s'.re} := isOpen_lt continuous_const continuous_re
  have hsU : s ∈ {s' : ℂ | 1 + 3*e/2 < s'.re} := by
    simp only [Set.mem_ofPred_eq]; rw [he]; linarith
  have hne : ∀ s' ∈ {s' : ℂ | 1 + 3*e/2 < s'.re}, s' ≠ 0 := by
    intro s' hs'
    have hs're : 1 + 3*e/2 < s'.re := hs'
    intro h
    rw [h] at hs're
    simp at hs're
    linarith [hepos]
  have hdiff : DifferentiableOn ℂ (Dser w) {s' : ℂ | 1 + 3*e/2 < s'.re} := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun n : ℕ => C * (n:ℝ)^(-(1+e/2))) ?_ ?_ hopen ?_
    · exact (Real.summable_nat_rpow.mpr (by linarith)).mul_left C
    · intro n; exact differentiableOn_term w n hne
    · intro n s' hs'
      have hs're : 1 + 3 * e / 2 < s'.re := hs'
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        have hz : ((0:ℕ):ℂ)^(-s') = 0 := by
          rw [Nat.cast_zero]
          exact Complex.zero_cpow (neg_ne_zero.mpr (hne s' hs'))
        have h1 : ‖(((1 + w) ^ (0:ℕ).primeFactors.card : ℂ) * ((0:ℕ):ℂ)^(-s'))‖ = 0 := by
          rw [Nat.primeFactors_zero, Finset.card_empty, pow_zero, one_mul, hz, norm_zero]
        rw [h1]
        exact mul_nonneg hCpos.le (Real.rpow_nonneg (Nat.cast_nonneg 0) _)
      · have hnR' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
        rw [norm_mul]
        have hcp : ‖(n : ℂ) ^ (-s')‖ = (n:ℝ)^(-(s'.re)) := by
          rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hnR']; simp
        rw [hcp]
        have hb := hC n hn
        have hb2 : (n:ℝ)^e * (n:ℝ)^(-(s'.re)) ≤ (n:ℝ)^(-(1+e/2)) := by
          rw [← Real.rpow_add hnR']
          apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
          linarith [hs're]
        calc ‖(((1 + w) ^ n.primeFactors.card : ℂ))‖ * (n:ℝ)^(-(s'.re))
            ≤ (C * (n:ℝ)^e) * (n:ℝ)^(-(s'.re)) :=
              mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hnR'.le _)
          _ = C * ((n:ℝ)^e * (n:ℝ)^(-(s'.re))) := by ring
          _ ≤ C * (n:ℝ)^(-(1+e/2)) := mul_le_mul_of_nonneg_left hb2 hCpos.le
  exact (hdiff.analyticOnNhd hopen) s hsU


lemma Dser_euler (w : ℂ) {s : ℂ} (hs : 1 < s.re) :
    Dser w s = riemannZeta s * ∏' p : Nat.Primes, (1 + w * ((p:ℕ):ℂ)^(-s)) := by
  have h := Commons.NumberTheory.DirichletSeries.omega_euler_product (1 + w) hs
  simpa [Dser, sub_add_cancel] using h


noncomputable def Afun (w : ℂ) (s : ℂ) : ℂ :=
  if 1 < s.re then Dser w s * (s - 1) ^ ((1 + w : ℂ))
  else riemannZeta₁ s ^ ((1 + w : ℂ)) * Hfun w s

lemma Afun_mul (w : ℂ) {s : ℂ} (hs : 1 < s.re) :
    Dser w s = Afun w s * (s - 1) ^ (-(1 + w)) := by
  have hne : s - 1 ≠ 0 := by
    intro h
    have h1 : s.re - 1 = 0 := by simpa using congrArg Complex.re h
    linarith
  rw [Afun, if_pos hs, mul_assoc, ← Complex.cpow_add _ _ hne]
  have : (1 + w) + (-(1 + w)) = (0 : ℂ) := by ring
  rw [this, Complex.cpow_zero, mul_one]




section RealAxis

open scoped ComplexOrder

/-- `(↑p)^(-(σ:ℂ)) = ↑(p^(-σ))` for a positive real `p`. -/
lemma ofReal_cpow_neg {p σ : ℝ} (hp : 0 < p) :
    ((p:ℂ)) ^ (-(σ:ℂ)) = (((p ^ (-σ) : ℝ)) : ℂ) := by
  have hpne : (p:ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have key : Complex.log (p:ℂ) * (-(σ:ℂ)) = (((-σ * Real.log p : ℝ)) : ℂ) := by
    rw [(Complex.ofReal_log hp.le).symm]
    push_cast
    ring
  rw [Complex.cpow_def_of_ne_zero hpne, key, Real.rpow_def_of_pos hp, Complex.ofReal_exp]
  congr 1
  ring

/-- `(x*y)^w = x^w * y^w` for positive real `x`, `y` and complex `w`. -/
lemma cpow_ofReal_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (w : ℂ) :
    ((x:ℂ) * (y:ℂ)) ^ w = (x:ℂ)^w * (y:ℂ)^w := by
  have hxne : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hyne : (y:ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have key : Complex.log ((x:ℂ) * (y:ℂ)) * w
      = Complex.log (x:ℂ) * w + Complex.log (y:ℂ) * w := by
    rw [Complex.log_mul_ofReal y hy (x:ℂ) hxne, (Complex.ofReal_log hx.le).symm,
      (Complex.ofReal_log hy.le).symm]
    ring
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hxne hyne) w, Complex.cpow_def_of_ne_zero hxne w,
    Complex.cpow_def_of_ne_zero hyne w, key, Complex.exp_add]

end RealAxis



section EulerReal

open scoped ComplexOrder

/-- The real local factor `1 - p^{-σ}`, for `σ > 1`. -/
private noncomputable def bfun (σ : ℝ) (p : Nat.Primes) : ℝ := 1 - (((p:ℕ):ℝ)) ^ (-σ)

private lemma bfun_pos {σ : ℝ} (hσ : 1 < σ) (p : Nat.Primes) : 0 < bfun σ p := by
  have hp2 : (2:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast p.prop.two_le
  have h1 : (((p:ℕ):ℝ)) ^ (-σ) ≤ (2:ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
  have h2 : (2:ℝ) ^ (-σ) < 1 := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by linarith))
  simp only [bfun]
  linarith

private lemma prime_rpow_neg_le_half {σ : ℝ} (hσ : 1 < σ) (p : Nat.Primes) :
    (((p:ℕ):ℝ)) ^ (-σ) ≤ 1/2 := by
  have hp2 : (2:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast p.prop.two_le
  have h1 : (((p:ℕ):ℝ)) ^ (-σ) ≤ (2:ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
  have h2 : (2:ℝ) ^ (-σ) ≤ 1/2 := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    have h4 : (2:ℝ) ^ (1:ℝ) ≤ (2:ℝ) ^ σ :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h5 := (inv_le_inv₀ (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) σ)
      (by norm_num : (0:ℝ) < 2)).mpr (by simpa using h4)
    simpa using h5
  linarith

private lemma bfun_eq_cpow {σ : ℝ} (p : Nat.Primes) :
    ((1:ℂ) - ((p:ℕ):ℂ) ^ (-(σ:ℂ))) = ↑(bfun σ p) := by
  have hp : (0:ℝ) < ((p:ℕ):ℝ) := by exact_mod_cast p.prop.pos
  have h1 : ((p:ℕ):ℂ) ^ (-(σ:ℂ)) = ↑((((p:ℕ):ℝ)) ^ (-σ)) := by
    have := ofReal_cpow_neg (p := ((p:ℕ):ℝ)) (σ := σ) hp
    simpa using this
  simp only [bfun, h1]
  push_cast
  ring

private lemma abs_log_one_sub_le {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1/2) :
    |Real.log (1 - x)| ≤ 2 * x := by
  have hpos : (0:ℝ) < 1 - x := by linarith
  have h1 : Real.log (1 - x) ≤ -x := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have h2 : -Real.log (1 - x) ≤ 2 * x := by
    have hlog : Real.log ((1 - x)⁻¹) ≤ (1 - x)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_inv] at hlog
    have hsub : (1 - x)⁻¹ - 1 = x / (1 - x) := by
      field_simp
      ring
    rw [hsub] at hlog
    have hle : x / (1 - x) ≤ 2 * x := by
      rw [div_le_iff₀ hpos]
      nlinarith
    linarith
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

lemma summable_primes_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => (((p:ℕ):ℝ)) ^ (-σ)) := by
  have hε : 0 < σ - 1 := by linarith
  refine (Commons.NumberTheory.Mertens.summable_primes_rpow (ε := σ - 1) hε).congr (fun p => ?_)
  congr 1
  ring

/-- Euler product in the form `∏_p (1 - p^{-σ}) = ζ(σ)^{-1}` for real `σ > 1`. -/
lemma tprod_one_sub_eq_inv_zeta {σ : ℝ} (hσ : 1 < σ) :
    (∏' p : Nat.Primes, ((1:ℂ) - ((p:ℕ):ℂ) ^ (-(σ:ℂ)))) = (riemannZeta (σ:ℂ))⁻¹ := by
  have hs : 1 < ((σ:ℂ)).re := by simpa using hσ
  have hne : riemannZeta (σ:ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hmult : Multipliable (fun p : Nat.Primes => ((1:ℂ) - ((p:ℕ):ℂ) ^ (-(σ:ℂ)))⁻¹) :=
    (riemannZeta_eulerProduct_hasProd (s := (σ:ℂ)) hs).multipliable
  have h2 := hmult.tprod_inv₀ (by rw [riemannZeta_eulerProduct_tprod hs]; exact hne)
  rw [riemannZeta_eulerProduct_tprod hs] at h2
  simpa using h2

/-- `∏_p (1 - p^{-σ})^w = ζ(σ)^{-w}` for real `σ > 1`. -/
lemma tprod_cpow_one_sub_eq (w : ℂ) {σ : ℝ} (hσ : 1 < σ) :
    (∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-(σ:ℂ)))^w))
      = (riemannZeta (σ:ℂ)) ^ (-w) := by
  obtain ⟨hZre, hZim0⟩ := Complex.pos_iff.mp (riemannZeta_pos_of_one_lt hσ)
  have hZim : (riemannZeta (σ:ℂ)).im = 0 := hZim0.symm
  have hZeq : riemannZeta (σ:ℂ) = ↑((riemannZeta (σ:ℂ)).re) := by
    apply Complex.ext <;> simp [hZim]
  have hsummlog : Summable (fun p : Nat.Primes => Real.log (bfun σ p)) := by
    refine Summable.of_norm ?_
    refine (summable_primes_rpow_neg hσ).mul_left 2 |>.of_nonneg_of_le
      (fun p => abs_nonneg _) (fun p => ?_)
    simpa only [Real.norm_eq_abs, bfun] using
      abs_log_one_sub_le (x := (((p:ℕ):ℝ)) ^ (-σ))
        (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) (-σ)) (prime_rpow_neg_le_half hσ p)
  have hprodC : (∏' p : Nat.Primes, ((bfun σ p : ℝ) : ℂ)) = (riemannZeta (σ:ℂ))⁻¹ := by
    rw [tprod_congr (fun p => (bfun_eq_cpow (σ := σ) p).symm)]
    exact tprod_one_sub_eq_inv_zeta hσ
  have hexpC : (∏' p : Nat.Primes, ((bfun σ p : ℝ) : ℂ))
      = ↑(Real.exp (∑' p : Nat.Primes, Real.log (bfun σ p))) := by
    have hpt : ∀ p : Nat.Primes, ((bfun σ p : ℝ) : ℂ)
        = Complex.exp (((Real.log (bfun σ p) : ℝ)) : ℂ) := by
      intro p
      rw [← Complex.ofReal_exp, Real.exp_log (bfun_pos hσ p)]
    rw [tprod_congr hpt]
    have hsummC : Summable (fun p : Nat.Primes => (((Real.log (bfun σ p) : ℝ)) : ℂ)) :=
      Complex.summable_ofReal.mpr hsummlog
    have hh := (hsummC.hasSum.cexp).tprod_eq
    simp only [Function.comp_apply] at hh
    rw [hh, ← Complex.ofReal_tsum, Complex.ofReal_exp]
  have hlogsum : (∑' p : Nat.Primes, Real.log (bfun σ p))
      = -Real.log ((riemannZeta (σ:ℂ)).re) := by
    have h1 : Real.exp (∑' p : Nat.Primes, Real.log (bfun σ p)) = ((riemannZeta (σ:ℂ)).re)⁻¹ := by
      have h := (hexpC.symm.trans hprodC)
      rw [hZeq] at h
      exact_mod_cast h
    have h2 : Real.log (Real.exp (∑' p : Nat.Primes, Real.log (bfun σ p)))
        = Real.log (((riemannZeta (σ:ℂ)).re)⁻¹) := by rw [h1]
    rwa [Real.log_exp, Real.log_inv] at h2
  have hfin : (∑' p : Nat.Primes, w * (((Real.log (bfun σ p) : ℝ)) : ℂ))
      = -w * (((Real.log ((riemannZeta (σ:ℂ)).re) : ℝ)) : ℂ) := by
    rw [tsum_mul_left, ← Complex.ofReal_tsum, hlogsum]
    push_cast
    ring
  calc (∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-(σ:ℂ)))^w))
      = ∏' p : Nat.Primes, Complex.exp (w * (((Real.log (bfun σ p) : ℝ)) : ℂ)) := by
        refine tprod_congr (fun p => ?_)
        rw [bfun_eq_cpow, Complex.cpow_def_of_ne_zero (by
          have := bfun_pos hσ p; exact_mod_cast this.ne'),
          (Complex.ofReal_log (bfun_pos hσ p).le).symm, mul_comm]
    _ = Complex.exp (∑' p : Nat.Primes, w * (((Real.log (bfun σ p) : ℝ)) : ℂ)) := by
        have hsummC : Summable (fun p : Nat.Primes => (((Real.log (bfun σ p) : ℝ)) : ℂ)) :=
          Complex.summable_ofReal.mpr hsummlog
        have hh := (hsummC.mul_left w).hasSum.cexp.tprod_eq
        simp only [Function.comp_apply] at hh
        rw [hh]
    _ = (riemannZeta (σ:ℂ)) ^ (-w) := by
        have hs : 1 < ((σ:ℂ)).re := by simpa using hσ
        have hne : riemannZeta (σ:ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
        rw [Complex.cpow_def_of_ne_zero hne, hfin, hZeq, (Complex.ofReal_log hZre.le).symm]
        simp only [Complex.ofReal_re]
        congr 1
        ring

end EulerReal




section RealAxisFactor

/-- `‖cexp z - 1‖ ≤ 2‖z‖` for `‖z‖ ≤ 1`. -/
private lemma norm_cexp_sub_one_le {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ := by
  have h := Complex.norm_exp_sub_one_sub_id_le hz
  have hsplit : Complex.exp z - 1 = (Complex.exp z - 1 - z) + z := by ring
  rw [hsplit]
  calc ‖(Complex.exp z - 1 - z) + z‖ ≤ ‖Complex.exp z - 1 - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ ‖z‖ ^ 2 + ‖z‖ := by linarith
    _ ≤ 2 * ‖z‖ := by nlinarith [norm_nonneg z, hz]

/-- `‖(↑b)^w - 1‖ ≤ 2‖w‖·|log b|` for a positive real `b` with small `|log b|`. -/
private lemma norm_ofReal_cpow_sub_one_le {b : ℝ} (hb : 0 < b) (hlog1 : |Real.log b| ≤ 1)
    {w : ℂ} (hw : ‖w‖ ≤ 1/2) : ‖((b:ℂ))^w - 1‖ ≤ 2 * ‖w‖ * |Real.log b| := by
  have hcp : ((b:ℂ))^w = Complex.exp (w * ↑(Real.log b)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hb.ne'),
      (Complex.ofReal_log hb.le).symm, mul_comm]
  have hz : ‖w * ↑(Real.log b)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [hw, hlog1, norm_nonneg w, abs_nonneg (Real.log b)]
  rw [hcp]
  refine (norm_cexp_sub_one_le hz).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  ring

/-- `‖(↑n)^(-(σ:ℂ))‖ = n^(-σ)`. -/
private lemma norm_natCast_cpow_neg (n : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ‖(((n:ℕ):ℂ)) ^ (-(σ:ℂ))‖ = ((n:ℝ)) ^ (-σ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [Nat.cast_zero, Complex.zero_cpow (by simp [hσ.ne']), norm_zero, Nat.cast_zero,
      Real.zero_rpow (by linarith)]
  · rw [show ((n:ℕ):ℂ) = ((((n:ℕ):ℝ)):ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast h)]
    simp

/-- `Hfun` on the real axis splits into the `ζ^{-w}` factor and a product of `1 + w p^{-σ}`. -/
lemma Hfun_ofReal_eq (w : ℂ) (hw : ‖w‖ ≤ 1/2) {σ : ℝ} (hσ : 1 < σ) :
    Hfun w (σ:ℂ) = (∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-(σ:ℂ)))^w))
      * (∏' p : Nat.Primes, (1 + w * ((p:ℕ):ℂ) ^ (-(σ:ℂ)))) := by
  have h1 : Hfun w (σ:ℂ) = ∏' p : Nat.Primes,
      (((1:ℂ) - ((p:ℕ):ℂ) ^ (-(σ:ℂ)))^w * (1 + w * ((p:ℕ):ℂ) ^ (-(σ:ℂ)))) := by
    rw [Hfun]
    refine tprod_congr (fun p => ?_)
    simp only [omegaLocalHat, omegaLocal]
    ring
  have hsummB : Summable (fun p : Nat.Primes => w * ((p:ℕ):ℂ) ^ (-(σ:ℂ))) := by
    refine Summable.of_norm_bounded ((summable_primes_rpow_neg hσ).mul_left ‖w‖) (fun p => ?_)
    rw [norm_mul, norm_natCast_cpow_neg _ (by linarith : (0:ℝ) < σ)]
  have hsummA : Summable (fun p : Nat.Primes =>
      (((1:ℂ) - ((p:ℕ):ℂ) ^ (-(σ:ℂ)))^w - 1)) := by
    refine Summable.of_norm_bounded ((summable_primes_rpow_neg hσ).mul_left (4 * ‖w‖)) (fun p => ?_)
    have hp1 : (((p:ℕ):ℝ)) ^ (-σ) ≤ 1/2 := prime_rpow_neg_le_half hσ p
    have hp0 : (0:ℝ) < (((p:ℕ):ℝ)) ^ (-σ) :=
      Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) (-σ)
    have hlog : |Real.log (bfun σ p)| ≤ 1 := by
      have h := abs_log_one_sub_le (x := (((p:ℕ):ℝ)) ^ (-σ)) hp0 hp1
      simp only [bfun]
      linarith [h]
    have hlog2 : |Real.log (bfun σ p)| ≤ 2 * (((p:ℕ):ℝ) ^ (-σ)) := by
      simpa only [bfun] using abs_log_one_sub_le (x := (((p:ℕ):ℝ)) ^ (-σ)) hp0 hp1
    rw [bfun_eq_cpow]
    calc ‖((bfun σ p : ℝ) : ℂ)^w - 1‖ ≤ 2 * ‖w‖ * |Real.log (bfun σ p)| :=
          norm_ofReal_cpow_sub_one_le (bfun_pos hσ p) hlog hw
      _ ≤ 2 * ‖w‖ * (2 * (((p:ℕ):ℝ) ^ (-σ))) := by
          have hw0 : (0:ℝ) ≤ 2 * ‖w‖ := by positivity
          exact mul_le_mul_of_nonneg_left hlog2 hw0
      _ = 4 * ‖w‖ * (((p:ℕ):ℝ) ^ (-σ)) := by ring
  have hmultA : Multipliable (fun p : Nat.Primes => ((1:ℂ) - ((p:ℕ):ℂ) ^ (-(σ:ℂ)))^w) :=
    (Complex.multipliable_one_add_of_summable hsummA).congr (fun p => by ring)
  have hmultB : Multipliable (fun p : Nat.Primes => (1 + w * ((p:ℕ):ℂ) ^ (-(σ:ℂ)))) :=
    Complex.multipliable_one_add_of_summable hsummB
  rw [h1, Multipliable.tprod_mul hmultA hmultB]

end RealAxisFactor



section RealAxisAgreement

/-- **Agreement of the two branches on the real axis.** -/
lemma real_axis_agreement (w : ℂ) (hw : ‖w‖ ≤ 1/2) {σ : ℝ} (hσ : 1 < σ) :
    Dser w (σ:ℂ) * (((σ:ℂ) - 1) ^ ((1 + w : ℂ)))
      = riemannZeta₁ (σ:ℂ) ^ ((1 + w : ℂ)) * Hfun w (σ:ℂ) := by
  have hs : 1 < ((σ:ℂ)).re := by simpa using hσ
  obtain ⟨hZre, hZim0⟩ := Complex.pos_iff.mp (riemannZeta_pos_of_one_lt hσ)
  have hZim : (riemannZeta (σ:ℂ)).im = 0 := hZim0.symm
  have hZeq : riemannZeta (σ:ℂ) = ↑((riemannZeta (σ:ℂ)).re) := by
    apply Complex.ext <;> simp [hZim]
  have ha : (0:ℝ) < σ - 1 := by linarith
  have has : ((σ:ℂ) - 1) = ↑(σ - 1) := by push_cast; ring
  have hZre' : (0:ℝ) < (riemannZeta (σ:ℂ)).re := hZre
  have hZne : (riemannZeta (σ:ℂ)) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hz1 : riemannZeta₁ (σ:ℂ) = (((σ:ℂ) - 1)) * riemannZeta (σ:ℂ) := by
    have hs1 : (σ:ℂ) ≠ 1 := by
      intro h
      have h2 : σ = 1 := by simpa using congrArg Complex.re h
      linarith
    rw [riemannZeta₁, riemannZeta_eq_inv_sub_add hs1]
    have hne : ((σ:ℂ) - 1) ≠ 0 := sub_ne_zero.mpr hs1
    field_simp
  have hZmul : riemannZeta (σ:ℂ) * (((σ:ℂ) - 1)) ^ ((1 + w : ℂ))
      = ((((σ:ℂ) - 1)) * riemannZeta (σ:ℂ)) ^ ((1 + w : ℂ))
        * (riemannZeta (σ:ℂ)) ^ (-w) := by
    conv_lhs => rw [hZeq, has]
    conv_rhs => rw [hZeq, has]
    rw [cpow_ofReal_mul ha hZre' (1 + w)]
    have hne : ((((riemannZeta (σ:ℂ)).re : ℝ)) : ℂ) ≠ 0 := by
      simp [hZre'.ne']
    rw [mul_assoc, ← Complex.cpow_add _ _ hne, show (1 + w) + (-w) = 1 by ring,
      Complex.cpow_one]
    ring
  have hkey : riemannZeta₁ (σ:ℂ) ^ ((1 + w : ℂ))
        * (∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-(σ:ℂ)))^w))
      = (((σ:ℂ) - 1) ^ ((1 + w : ℂ))) * riemannZeta (σ:ℂ) := by
    rw [hz1, tprod_cpow_one_sub_eq w hσ, ← hZmul]
    ring
  rw [Dser_euler w hs, Hfun_ofReal_eq w hw hσ,
    show riemannZeta₁ (σ:ℂ) ^ ((1 + w : ℂ))
        * ((∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-(σ:ℂ)))^w))
          * ∏' p : Nat.Primes, (1 + w * ((p:ℕ):ℂ) ^ (-(σ:ℂ))))
      = (riemannZeta₁ (σ:ℂ) ^ ((1 + w : ℂ))
        * (∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-(σ:ℂ)))^w)))
        * (∏' p : Nat.Primes, (1 + w * ((p:ℕ):ℂ) ^ (-(σ:ℂ)))) by ring, hkey]
  ring

end RealAxisAgreement



section Analyticity

/-- Near `1`, `riemannZeta₁` takes values in the slit plane. -/
lemma eventually_slitPlane_riemannZeta₁ : ∀ᶠ s : ℂ in 𝓝 (1:ℂ), riemannZeta₁ s ∈ slitPlane := by
  have hcont : Tendsto riemannZeta₁ (𝓝 (1:ℂ)) (𝓝 (riemannZeta₁ 1)) :=
    differentiable_riemannZeta₁.continuous.continuousAt
  rw [riemannZeta₁_one] at hcont
  have hsub : Tendsto (fun s : ℂ => riemannZeta₁ s - 1) (𝓝 (1:ℂ)) (𝓝 (1 - 1)) :=
    hcont.sub (tendsto_const_nhds (x := (1:ℂ)))
  rw [sub_self] at hsub
  have hnorm : ∀ᶠ s : ℂ in 𝓝 (1:ℂ), ‖riemannZeta₁ s - 1‖ < 1/2 :=
    hsub.norm.eventually_lt_const (by norm_num)
  filter_upwards [hnorm] with s hs
  rw [Complex.mem_slitPlane_iff]
  left
  have h := Complex.re_le_norm ((1:ℂ) - riemannZeta₁ s)
  rw [norm_sub_rev] at h
  simp only [Complex.sub_re, Complex.one_re] at h
  linarith

/-- The "else branch" `ζ̃^{1+w}·Hfun` is analytic on a ball around `1`. -/
lemma analyticOnNhd_elseBranch (w : ℂ) (hw : ‖w‖ ≤ 1/2) :
    ∃ ρ : ℝ, 0 < ρ ∧ AnalyticOnNhd ℂ
      (fun s : ℂ => riemannZeta₁ s ^ ((1 + w : ℂ)) * Hfun w s) (Metric.ball 1 ρ) := by
  obtain ⟨ρ₀, hρ₀, hball₀⟩ := Metric.mem_nhds_iff.mp eventually_slitPlane_riemannZeta₁
  refine ⟨min ρ₀ (1/4), lt_min hρ₀ (by norm_num), ?_⟩
  set ρ := min ρ₀ (1/4) with hρdef
  have hζ : DifferentiableOn ℂ (fun s : ℂ => riemannZeta₁ s ^ ((1 + w : ℂ))) (Metric.ball 1 ρ) :=
    DifferentiableOn.cpow_const
      ((differentiable_riemannZeta₁.differentiableOn).mono (Set.subset_univ _))
      (fun s hs => hball₀ (by
        rw [Metric.mem_ball] at hs ⊢
        exact lt_of_lt_of_le hs (min_le_left _ _)))
  have hH : DifferentiableOn ℂ (Hfun w) (Metric.ball 1 ρ) :=
    (analyticOnNhd_Hfun hw).differentiableOn.mono (fun s hs => by
      have h4 : dist s 1 < 1/4 := lt_of_lt_of_le hs (min_le_right _ _)
      rw [dist_eq_norm] at h4
      have h := Complex.re_le_norm ((1:ℂ) - s)
      rw [norm_sub_rev] at h
      simp only [Complex.sub_re, Complex.one_re] at h
      show (3/4 : ℝ) < s.re
      linarith)
  exact (hζ.mul hH).analyticOnNhd Metric.isOpen_ball

/-- The "if branch" `Dser·(s-1)^{1+w}` is analytic on `{Re s > 1}`. -/
lemma analyticOnNhd_ifBranch (w : ℂ) :
    AnalyticOnNhd ℂ (fun s : ℂ => Dser w s * (s - 1) ^ ((1 + w : ℂ)))
      {s : ℂ | 1 < s.re} := by
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have hsub : DifferentiableOn ℂ (fun s : ℂ => s - 1) {s : ℂ | 1 < s.re} :=
    fun s _ => (differentiableAt_id.sub_const (1:ℂ)).differentiableWithinAt
  refine ((analyticOnNhd_Dser w).differentiableOn.mul (hsub.cpow_const ?_)).analyticOnNhd hopen
  intro s hs
  have hrs : (1:ℝ) < s.re := hs
  have hpos : (0:ℝ) < s.re - 1 := by linarith
  rw [Complex.mem_slitPlane_iff]
  left
  simpa only [Complex.sub_re, Complex.one_re] using hpos

/-- The two branches agree on a half-disk around `1`. -/
lemma branches_eqOn_halfDisk (w : ℂ) (hw : ‖w‖ ≤ 1/2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s : ℂ, s ∈ Metric.ball 1 ρ → 1 < s.re →
      Dser w s * (s - 1) ^ ((1 + w : ℂ))
        = riemannZeta₁ s ^ ((1 + w : ℂ)) * Hfun w s := by
  obtain ⟨ρ₁, hρ₁, hb₁⟩ := analyticOnNhd_elseBranch w hw
  refine ⟨min ρ₁ (1/4), lt_min hρ₁ (by norm_num), ?_⟩
  set ρ := min ρ₁ (1/4) with hρdef
  have hρpos : 0 < ρ := lt_min hρ₁ (by norm_num)
  have hb₁' : AnalyticOnNhd ℂ (fun s : ℂ => riemannZeta₁ s ^ ((1 + w : ℂ)) * Hfun w s)
      (Metric.ball 1 ρ) :=
    hb₁.mono (fun x hx => by
      rw [Metric.mem_ball] at hx ⊢
      exact lt_of_lt_of_le hx (min_le_left _ _))
  set U : Set ℂ := Metric.ball 1 ρ ∩ {s : ℂ | 1 < s.re} with hUdef
  have hconv1 : Convex ℝ (Metric.ball (1:ℂ) ρ) := convex_ball 1 ρ
  have hconv2 : Convex ℝ {s : ℂ | 1 < s.re} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have h1 : (a • x + b • y).re = a * x.re + b * y.re := by
      simp [Complex.add_re, Complex.smul_re]
    rw [h1]
    rcases lt_or_eq_of_le ha with ha' | ha'
    · have h : a * 1 < a * x.re := mul_lt_mul_of_pos_left hx ha'
      have h2 : b * 1 ≤ b * y.re := mul_le_mul_of_nonneg_left (le_of_lt hy) hb
      linarith
    · have hb' : 0 < b := by linarith
      have h : b * 1 < b * y.re := mul_lt_mul_of_pos_left hy hb'
      have h2 : a * 1 ≤ a * x.re := mul_le_mul_of_nonneg_left (le_of_lt hx) ha
      linarith
  have hUconn : IsPreconnected U := (hconv1.inter hconv2).isPreconnected
  set D : ℂ → ℂ := fun s => Dser w s * (s - 1) ^ ((1 + w : ℂ))
    - riemannZeta₁ s ^ ((1 + w : ℂ)) * Hfun w s with hDdef
  have hDana : AnalyticOnNhd ℂ D U :=
    ((analyticOnNhd_ifBranch w).mono Set.inter_subset_right).sub
      (hb₁'.mono Set.inter_subset_left)
  have hreal : ∀ σ : ℝ, 1 < σ → σ < 1 + ρ → D ((σ:ℂ)) = 0 := by
    intro σ h1 h2
    have h := real_axis_agreement w hw h1
    simp only [hDdef]
    rw [h]
    ring
  set z₀ : ℂ := ((1 + 3 * ρ / 4 : ℝ) : ℂ) with hz₀def
  have hz₀U : z₀ ∈ U := by
    constructor
    · rw [Metric.mem_ball]
      have h : z₀ - (1:ℂ) = ((3 * ρ / 4 : ℝ) : ℂ) := by
        simp only [hz₀def]
        push_cast
        ring
      rw [dist_eq_norm, h, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0:ℝ) < 3 * ρ / 4)]
      linarith
    · simp only [Set.mem_setOf_eq, hz₀def, Complex.ofReal_re]
      linarith
  have hz₀cl : z₀ ∈ closure ({z : ℂ | D z = 0} \ {z₀}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    set δ : ℝ := min (ε/2) (ρ/8) with hδdef
    have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
    have hδρ : 3 * ρ / 4 + δ < ρ := by
      have hle : δ ≤ ρ/8 := min_le_right _ _
      linarith
    refine ⟨((1 + 3 * ρ / 4 + δ : ℝ) : ℂ), ?_, ?_⟩
    · simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff]
      refine ⟨?_, ?_⟩
      · apply hreal
        · push_cast
          linarith
        · push_cast
          linarith
      · intro hc
        have h2 : (1 + 3 * ρ / 4 + δ : ℝ) = 1 + 3 * ρ / 4 := by
          have h3 := congrArg Complex.re hc
          simpa only [hz₀def, Complex.ofReal_re] using h3
        linarith
    · have h : dist z₀ (((1 + 3 * ρ / 4 + δ : ℝ)) : ℂ) = δ := by
        have h2 : z₀ - ((1 + 3 * ρ / 4 + δ : ℝ) : ℂ) = ((-δ : ℝ) : ℂ) := by
          simp only [hz₀def]
          push_cast
          ring
        rw [dist_eq_norm, h2, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hδpos]
      rw [h]
      have hle : δ ≤ ε/2 := min_le_left _ _
      linarith
  have hzero := hDana.eqOn_zero_of_preconnected_of_mem_closure hUconn hz₀U hz₀cl
  intro s hs hsr
  have hsU : s ∈ U := ⟨hs, hsr⟩
  have h := hzero hsU
  simp only [hDdef, Pi.zero_apply] at h
  exact sub_eq_zero.mp h

/-- `Afun w` is analytic on a ball around `1`. -/
lemma analyticOnNhd_Afun (w : ℂ) (hw : ‖w‖ ≤ 1/2) :
    ∃ ρ : ℝ, 0 < ρ ∧ AnalyticOnNhd ℂ (Afun w) (Metric.ball 1 ρ) := by
  obtain ⟨ρ₁, hρ₁, hb₁⟩ := analyticOnNhd_elseBranch w hw
  obtain ⟨ρ₂, hρ₂, hb₂⟩ := branches_eqOn_halfDisk w hw
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_⟩
  have hb₁' : AnalyticOnNhd ℂ (fun s : ℂ => riemannZeta₁ s ^ ((1 + w : ℂ)) * Hfun w s)
      (Metric.ball 1 (min ρ₁ ρ₂)) :=
    hb₁.mono (fun x hx => by
      rw [Metric.mem_ball] at hx ⊢
      exact lt_of_lt_of_le hx (min_le_left _ _))
  refine AnalyticOnNhd.congr Metric.isOpen_ball hb₁' (fun s hs => ?_)
  rw [Afun]
  by_cases h : 1 < s.re
  · rw [if_pos h]
    exact (hb₂ s (by
      rw [Metric.mem_ball] at hs ⊢
      exact lt_of_lt_of_le hs (min_le_right _ _)) h).symm
  · rw [if_neg h]

end Analyticity



/-!
## State of the proof of `omega_series_factor_shifted` (notes for the next session)

PROVEN so far in this file (everything below the `sorry`-free part):

* `ofReal_cpow_neg`, `cpow_ofReal_mul` — `cpow` on positive reals.
* `summable_primes_rpow_neg`, `abs_log_one_sub_le`, `tprod_one_sub_eq_inv_zeta`,
  `tprod_cpow_one_sub_eq` — the Euler product in the form
  `∏'_p (1 - p^{-σ})^w = ζ(σ)^{-w}` for real `σ > 1`.
* `Hfun_ofReal_eq` — the splitting `Hfun w σ = (∏_p (1-p^{-σ})^w)·(∏_p (1 + w p^{-σ}))`.
* `real_axis_agreement` — the two branches agree on the real axis:
  `Dser w σ · (σ-1)^{1+w} = ζ̃(σ)^{1+w} · Hfun w σ` for real `σ > 1`.
* `eventually_slitPlane_riemannZeta₁`, `analyticOnNhd_elseBranch`,
  `analyticOnNhd_ifBranch`, `branches_eqOn_halfDisk` (identity theorem on the half-disk),
  `analyticOnNhd_Afun`.

REMAINING (in order of assembly):

1. `Hfun w 1` bound: `‖Hfun w 1 - 1‖ ≤ 3‖w‖`.  Route: `Hfun w 1 = cexp (∑'_p c_p)` with
   `c_p = w·log(1-p^{-1}) + log(1+w/p)`; the per-term bound
   `‖c_p‖ ≤ ‖w‖/(p(p-1)) + (2/3)‖w‖²p^{-2}` (from `Complex.norm_log_one_add_sub_self_le`
   and the real estimate `|log(1-z)+z| ≤ z²/(1-z)` for `0 < z ≤ 1/2`), and
   `∑_p 1/(p(p-1)) ≤ 1`, `∑_p p^{-2} ≤ 1` (crude telescoping / p-series comparisons).
   Then `‖cexp S - 1‖ ≤ 2‖S‖` with `‖S‖ ≤ (4/3)‖w‖`.

2. Value bound on `{Re s ≥ 1}`.  Write `A_if s = (s-1)^{1+w} Dser w s` for `1 < s.re`.
   * `Dser_euler` gives `Dser w s = ζ(s)·P(s)`, `P(s) = ∏'_p (1 + w p^{-s})`.
   * The per-term expansion gives, for `1 < Re s`,
     `log ‖P(s)‖ = w.re · log‖ζ(s)‖ - w.im · Im(∑'_p p^{-s}) + O(1)`.
   * Hence `‖A_if s‖ ≤ C_w · ‖ζ̃(s)‖^{1+w.re} · exp(|w.im|·|Im(∑'_p p^{-s})|)`.
   * `‖ζ̃(s)‖ ≤ (1+‖s‖)·C·log(2+‖s‖)` on `Re s ≥ 1` (Mathlib/commons bounds
     `norm_riemannZeta_le_five_mul_log`, `riemannZeta_norm_le_inv_sub_one`, compactness for
     `|Im s| ≤ 1`).
   **The missing analytic input** is a bound on the argument of ζ on (and near) the line
   `Re s = 1`, e.g.
     `∃C, ∀ s, 1 < s.re → |(∑'_p p^{-s}).im| ≤ C·(1 + (log log (2+‖s‖))²)`
   — which would give `e^{|w.im|·|Im Σ|}` = `(1+‖s‖)^{o(1)}` and hence
   `‖A s‖ ≤ D(1+‖s‖)²` since `1 + w.re ≤ 3/2`.
   Route for that input: `Σ_p p^{-s} = log ζ(s) - F(s)` with `F(s) = Σ_{p,k≥2} p^{-ks}/k`
   absolutely convergent for `Re s > 1/2`; the identity `Σ_{n≤y} Λ(n) n^{-σ-it}/log n =
   Σ_{p≤y} p^{-σ-it} + O(1)` plus Abel summation over dyadic blocks; the blocks
   `Σ_{M<n≤R} n^{-it}` are controlled by `Commons.NumberTheory.Zeta.blocksum_cpow_neg_I_mul_le`
   (van der Corput), and the PNT with an exponential error
   (`Commons.NumberTheory.Zeta.chebyshev_psi_sub_id_exp`) is needed to bound
   `Σ_{n≤y} Λ(n) n^{-σ-it}`.  On the line `Re s = 1` the else-branch formula
   (`ζ̃(1+it)^{1+w} Hfun w (1+it)`, principal branch) already gives the required polynomial
   bound with no argument input at all.

3. Derivative bound.  For `Re s > 1` the analytic continuation makes
   `deriv A s = A s · ((1+w)·(ζ̃'/ζ̃)(s) + (H'/H)(s))`, with
   `ζ̃'/ζ̃ = 1/(s-1) + ζ'/ζ` and `H'/H = ∑_p w log p p^{-s}·[(1-p^{-s})^{-1} - (1+wp^{-s})^{-1}]`
   absolutely summable (`O(p^{-2σ})`).  `‖ζ'/ζ(σ+it)‖ ≤ C(log(|t|+3)+1)^4` on the zero-free
   region is available as `Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_logDeriv_bound`;
   for the ball part use Cauchy's estimate for `Afun w` on `Metric.ball 1 ρ` with the ball
   bound `B`.  (The ball bound `B` itself is immediate from `A = ζ̃^{1+w}Hfun` on the ball
   together with `‖Hfun‖ ≤ exp (200 ∑_p p^{-3/2})` on `omK`.)
-/









section PrimeTsumBounds

/-- The finite telescoping bound `Σ_{m=1}^{M} 1/(m(m+1)) ≤ 1`. -/
private lemma sum_Icc_inv_mul_succ_le (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / ((m:ℝ) * ((m:ℝ) + 1))) ≤ 1 := by
  have key : ∀ N : ℕ, (∑ m ∈ Finset.Icc 1 N, (1:ℝ)/((m:ℝ)*((m:ℝ)+1))) = 1 - 1/((N:ℝ)+1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih]
      have hterm : (1:ℝ) / (((N+1 : ℕ):ℝ) * (((N+1 : ℕ):ℝ) + 1))
          = 1/((N:ℝ)+1) - 1/((N:ℝ)+2) := by
        push_cast
        field_simp
        ring
      rw [hterm]
      push_cast
      field_simp
      ring
  rw [key M]
  have : (0:ℝ) ≤ 1/((M:ℝ) + 1) := div_nonneg zero_le_one (by positivity)
  linarith

/-- `Σ_{p ∈ s} 1/(p(p-1)) ≤ 1` for every finite set `s` of primes. -/
private lemma finset_primes_inv_mul_pred_le (s : Finset Nat.Primes) :
    (∑ p ∈ s, 1 / (((p:ℕ):ℝ) * (((p:ℕ):ℝ) - 1))) ≤ 1 := by
  set Ms : ℕ := s.sup (fun p : Nat.Primes => (p:ℕ)) with hMs
  have hinj : Set.InjOn (fun p : Nat.Primes => (p:ℕ) - 1) (↑s : Set Nat.Primes) := by
    intro p _ q _ hpq
    have hp1 : 1 ≤ (p:ℕ) := p.prop.one_le
    have hq1 : 1 ≤ (q:ℕ) := q.prop.one_le
    have hpq' : (p:ℕ) - 1 = (q:ℕ) - 1 := hpq
    have h1 : (p:ℕ) - 1 + 1 = (q:ℕ) - 1 + 1 := by rw [hpq']
    rw [Nat.sub_add_cancel hp1, Nat.sub_add_cancel hq1] at h1
    exact Subtype.ext h1
  have hcongr : ∀ p ∈ s, (1:ℝ)/(((p:ℕ):ℝ)*(((p:ℕ):ℝ)-1))
      = 1/(((((p:ℕ) - 1 : ℕ)):ℝ) * (((((p:ℕ) - 1 : ℕ)):ℝ) + 1)) := by
    intro p _
    have hp1 : 1 ≤ (p:ℕ) := p.prop.one_le
    have hc : ((((p:ℕ) - 1 : ℕ)) : ℝ) = ((p:ℕ):ℝ) - 1 := by
      push_cast [Nat.cast_sub hp1]
      ring
    rw [hc]
    congr 1
    ring
  rw [Finset.sum_congr rfl hcongr,
      ← Finset.sum_image (f := fun m : ℕ => 1/((m:ℝ)*((m:ℝ)+1))) hinj]
  refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => by positivity)).trans
    (sum_Icc_inv_mul_succ_le Ms)
  intro m hm
  rw [Finset.mem_image] at hm
  obtain ⟨p, hp, rfl⟩ := hm
  have hle : (p:ℕ) ≤ Ms := Finset.le_sup (s := s) (f := fun p : Nat.Primes => (p:ℕ)) hp
  exact Finset.mem_Icc.mpr
    ⟨Nat.le_sub_one_of_lt (by have := p.prop.two_le; omega), le_trans (Nat.sub_le _ _) hle⟩

/-- `∑'_p 1/(p(p-1)) ≤ 1`. -/
lemma tsum_primes_inv_mul_pred_le :
    (∑' p : Nat.Primes, 1 / (((p:ℕ):ℝ) * (((p:ℕ):ℝ) - 1))) ≤ 1 := by
  refine Real.tsum_le_of_sum_le (fun p => ?_) finset_primes_inv_mul_pred_le
  have h2 : (2:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast p.prop.two_le
  exact div_nonneg zero_le_one (by nlinarith)

/-- `∑'_p 1/p² ≤ 1`. -/
lemma tsum_primes_inv_sq_le : (∑' p : Nat.Primes, ((((p:ℕ):ℝ))⁻¹)^2) ≤ 1 := by
  have hpt : ∀ p : Nat.Primes, ((((p:ℕ):ℝ))⁻¹)^2 ≤ 1 / (((p:ℕ):ℝ) * (((p:ℕ):ℝ) - 1)) := by
    intro p
    have h2 : (2:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast p.prop.two_le
    have hp0 : (0:ℝ) < ((p:ℕ):ℝ) := by exact_mod_cast p.prop.pos
    have hpos : (0:ℝ) < ((p:ℕ):ℝ) * (((p:ℕ):ℝ) - 1) := by nlinarith
    have h1 : ((((p:ℕ):ℝ))⁻¹)^2 = 1/(((p:ℕ):ℝ)^2) := by
      rw [inv_pow, one_div]
    rw [h1, div_le_div_iff₀ (pow_pos hp0 2) hpos]
    nlinarith [sq_nonneg ((p:ℕ):ℝ)]
  refine Real.tsum_le_of_sum_le (fun p => ?_)
    (fun s => (Finset.sum_le_sum (fun p _ => hpt p)).trans (finset_primes_inv_mul_pred_le s))
  exact pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) 2

end PrimeTsumBounds





section AbsLogBound

/-- For `0 < z ≤ 1/2`: `|log (1-z) + z| ≤ z²/(1-z)`.

The two directions are obtained separately (no Taylor series, no `linarith` cancellation across
the logarithm): from `Real.log_le_sub_one_of_pos` applied to `(1-z)⁻¹` and `Real.log_inv` we get
`-z/(1-z) ≤ log (1-z)`, and from `Real.log_le_sub_one_of_pos` applied to `1-z` we get
`log (1-z) ≤ -z`. -/
private lemma abs_log_one_sub_add_self_le {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1/2) :
    |Real.log (1 - z) + z| ≤ z^2 / (1 - z) := by
  have hpos : (0:ℝ) < 1 - z := by linarith
  -- `log (1-z) ≤ -z`
  have h1 : Real.log (1 - z) ≤ -z := by
    have h := Real.log_le_sub_one_of_pos hpos
    linarith
  -- `-z/(1-z) ≤ log (1-z)`
  have h2 : -(z/(1 - z)) ≤ Real.log (1 - z) := by
    have h := Real.log_le_sub_one_of_pos (x := (1 - z)⁻¹) (by positivity)
    rw [Real.log_inv] at h
    have hsub : (1 - z)⁻¹ - 1 = z/(1 - z) := by
      field_simp
      ring
    rw [hsub] at h
    linarith
  -- the cancellation identity, supplied by hand
  have hid : -(z/(1 - z)) + z = -(z^2/(1 - z)) := by
    field_simp
    ring
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · linarith
  · have hnn : (0:ℝ) ≤ z^2/(1 - z) := div_nonneg (sq_nonneg z) hpos.le
    linarith

end AbsLogBound






/-
## Status and plan for the target theorem `omega_series_factor_shifted`

### Already proven in this file
* `omegaLocal`, `omegaLocalHat`, `Hfun`, `omK`, `Dser`, `Afun`, `norm_omegaLocal_sub_one_le`,
  `norm_prime_cpow_le`, `norm_omegaLocalHat_le`, `analyticOnNhd_Hfun`, `analyticOnNhd_Dser`,
  `Dser_euler`, `Afun_mul`, `real_axis_agreement`, `eventually_slitPlane_riemannZeta₁`,
  `analyticOnNhd_elseBranch`, `analyticOnNhd_ifBranch`, `branches_eqOn_halfDisk`, `analyticOnNhd_Afun`.
* `section HfunBounds`: `one_add_omegaLocalHat_eq`, `norm_cpow_lower`, `summable_omegaLocalHat`,
  `norm_one_add_omegaLocalHat_ge` (`1/100 ≤ ‖1+omegaLocalHat‖`), `norm_one_add_omegaLocalHat_le'`,
  `norm_log_one_add_omegaLocalHat_le` (`≤ 4000 p^{-3/2}`), `Hfun_eq_cexp`,
  `Hfun_w_ne_zero`, `norm_Hfun_bounds` (upper/lower bounds with the constant
  `T = ∑' p, p^{-3/2}`).
* `section PrimeTsumBounds`: `tsum_primes_inv_mul_pred_le`, `tsum_primes_inv_sq_le`.
* `section AbsLogBound`, `section PerTermBound` (`norm_log_series_term_le`).

### Useful commons lemmas
* `Commons.NumberTheory.Zeta.zeta_bound_halfplane_inv_sub_one` :
  `∃C>0, ∀ s, 1 ≤ s.re → ‖ζ s‖ ≤ ‖s-1‖⁻¹ + C*(log(2+‖s‖)+1)`.
* `Commons.NumberTheory.DirichletSeries.zeta_euler_log_sum` :
  `1 < s.re → ∑' p, log (1 - p^{-s}) = -∑' n, (Λ n / log n) * n^{-s}`.
* `Commons.NumberTheory.Zeta.chebyshevPsi_at_height_farLeft_neg` has
  `zeta1_ne_zero_of_one_le_re : 1 ≤ s.re → riemannZeta₁ s ≠ 0`.
* `Commons.NumberTheory.Zeta.zeta_logDeriv_negStrip_bound` has
  `logDeriv_zeta_const_bound : ∃M>0, ∀ w, 3/2 ≤ w.re → ‖ζ'/ζ w‖ ≤ M`.
* `Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_logDeriv_bound` :
  `∃c C>0, (∀ t, 1 ≤ |t|, ∀σ, 1-c/log(|t|+3) ≤ σ → ζ(σ+it) ≠ 0) ∧
   (∀ t, 1 ≤ |t|, ∀σ, 1-c/log(|t|+3) ≤ σ → σ ≤ 2 → ‖ζ'/ζ(σ+it)‖ ≤ C*(log(|t|+3)+1)^4)`.
* `Commons.NumberTheory.LSeries.exists_bound_norm_riemannZeta_log_abs_t_ge_one` :
  `∃C>0, ∀σ t, 1 ≤ σ → 1 ≤ |t| → ‖ζ(σ+it)‖ ≤ C log(|t|+2)`.
* `Complex.cexp_tsum_eq_tprod`, `Complex.summable_log_one_add_of_summable`,
  `Multipliable.tprod_mul`, `Multipliable.norm_tprod`, `Complex.norm_log_one_add_half_le_self`,
  `Complex.re_tsum`; `Real.rexp_tsum_eq_tprod` for real products.
* `riemannZeta_eulerProduct_tprod : 1 < s.re → ∏' p, (1 - p^{-s})⁻¹ = riemannZeta s`.
* `deriv_zero_of_not_differentiableAt`, `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`,
  `Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic`.

### Key mathematical reductions (verified)
1. On `{Re s > 1}`, `Afun` is *forced*: `A s = Dser s * (s-1)^{1+w}`.  The principal-branch
   expression `ζ̃ s ^ (1+w) * Hfun w s` equals it only up to a factor `e^{2π i (n-k) Im w}`
   (`n`, `k` integer winding numbers), so the two really differ in a thin region of `{Re s > 1}`
   close to the line and far up.  Consequence: the natural piecewise `Afun` is discontinuous on
   parts of `{Re s = 1}`.  Therefore the final witness should be defined as
   `A s = if s ∈ ball 1 ρ then ζ̃ s^(1+w) * Hfun w s else if 1 < s.re then Dser w s * (s-1)^(1+w) else 0`
   (the identity on `{Re s > 1}` forces the middle branch; the free region is arbitrary).
   With `A := 0` on the free part, the line points outside the ball give `deriv A s = 0`.
2. Value bound `‖A s‖ ≤ D(1+‖s‖)^2` for `1 ≤ s.re`.
   * `Re s = 1`: `A s = ζ̃ s^(1+w) Hfun w s` (else branch), and by
     `zeta_bound_halfplane_inv_sub_one` `‖ζ̃ s‖ ≤ 1 + C|s-1|(log+1)`, so
     `‖A s‖ ≤ C'(1+‖s‖)^{3/2}`.
   * `Re s > 1`: with `L s = ∑' p, log (1 - p^{-s})`,
     `‖∏(1+wp^{-s})‖ = ‖Hfun s‖ ‖ζ s‖^{Re w} e^{Im w Im L s}`, hence
     `‖A s‖ ≤ ‖ζ s‖^{1+Re w} ‖Hfun s‖ |s-1|^{1+Re w} e^{π/2} e^{|Im L s|/2}`, and
     `‖ζ s‖·|s-1| ≤ 1 + C|s-1|(log(2+‖s‖)+1)`.
   * The remaining ingredient is the **argument bound**
     `∃C>0, ∀ s, 1 < s.re → |Im L s| ≤ C*(log(log(2+‖s‖)+2)+1)`.
     Route: write `L s = -(∑_{p≤X} p^{-s}) - F(s)`, `F = ∑_{p,k≥2} p^{-ks}/k` with `|F| = O(1)`;
     the head `∑_{p≤X}p^{-s}` with `X = 2+‖s‖` is `≤ ∑_{p≤X} 1/p ≤ loglog X + C` (Mertens),
     and the tail `∑_{p>X} p^{-s}` is `O(1/log X)` by partial summation against `π(u) ≲ u/log u`
     and the oscillation of `u^{-it}` (integration by parts).  Note `loglog(2+‖s‖) ≪ log(2+‖s‖)`,
     which is what makes the exponent work out.
3. Derivative bound `‖deriv A s‖ ≤ D(1+‖s‖)^4` for `1 ≤ s.re`.
   * `Re s > 1` (away from the ball): `A = Dser s (s-1)^z` locally; prove
     `deriv A s = A s * (z * ζ̃'/ζ̃ s + Hfun'/Hfun s)` via the identity theorem for
     `V s = Dser s (s-1)^z / Hfun s` on `{Re s > 1}` (`V'/V = z ζ̃'/ζ̃`, both sides analytic on the
     connected domain and equal on the real axis by `real_axis_agreement`).
     Then use the log-derivative bound (4) and `‖A s‖ ≤ D(1+‖s‖)^2`, plus
     `(1+log(2+‖s‖))^4 ≤ (1+‖s‖)^2` for `1 ≤ ‖s‖`.
   * inside `ball 1 ρ`: `A = ζ̃^z Hfun` with `ζ̃ ∈ slitPlane` there, `ζ̃ ≠ 0`, `Hfun ≠ 0`,
     and `‖Hfun‖` bounded above and below on `balK`; use the same log-derivative formula with
     a constant bound (`logDeriv_zeroFree_ball_bound_analytic` on `omK`), giving `≤ C(1+‖s‖)^4`.
   * on the line outside the ball: `A` is discontinuous (jump from `0` to the non-zero value
     `Dser s (s-1)^z`; positivity of the right-hand limit uses `Hfun_w_ne_zero`,
     `norm_Hfun_bounds` and the argument bound), hence `deriv A s = 0`.
4. Log-derivative bound: `∃C>0, ∀ s, 1 ≤ s.re → ‖ζ̃'/ζ̃ s‖ ≤ C*(1+log(2+‖s‖))^4`.
   * `3/2 ≤ Re s`: `logDeriv_zeta_const_bound` plus `‖(s-1)⁻¹‖ ≤ 2`.
   * `Re s ≤ 3/2`, `1 ≤ |Im s|`: `zeta_zeroFreeRegion_logDeriv_bound` plus `‖(s-1)⁻¹‖ ≤ 1`.
   * `Re s ≤ 3/2`, `|Im s| ≤ 1`: compactness (`zeta1_ne_zero_of_one_le_re`).
5. `‖A 1 - 1‖ ≤ 3‖w‖`: `A 1 = ζ̃ 1^(1+w) * Hfun w 1 = Hfun w 1` (`riemannZeta₁_one`), and
   `Hfun w 1 = cexp (∑' p, log (1 + omegaLocalHat w p 1))` by `Hfun_eq_cexp`.
   For `s = 1`, `p^{-1}` is real positive, so
   `log (1 + omegaLocalHat w p 1) = w * log (1 - p⁻¹) + log (1 + w p⁻¹)`
   (the two sides differ by `2πik` with `k = 0`: the sum of the imaginary parts is
   `≤ |Im w| log 2 + arcsin(1/4) < π`), which is exactly the expression bounded by
   `norm_log_series_term_le`.  Then `‖∑‖ ≤ (4/3)‖w‖`, `‖cexp S - 1‖ ≤ 2‖S‖` and
   `tsum_primes_inv_mul_pred_le`, `tsum_primes_inv_sq_le` give `‖Hfun w 1 - 1‖ ≤ (8/3)‖w‖ ≤ 3‖w‖`.

### *** BREAKTHROUGH (session 3): the argument bound IS provable ***
Everything reduces to `∃C, ∀s, 1 < s.re → |(Lw s).im| ≤ Real.log (3 + ‖s‖) + C`
(where `Lw s = ∑' p, log (1 - p^{-s})`).  Proof sketch (two cases), with `δ := s.re - 1`:

* Case `δ ≥ 1/(3+‖s‖)`: use the SHARP trivial bound `|(Lw s).im| ≤ log ζ(σ)` (not `2ζ(σ)`!).
  For each prime `|arg (1-p^{-s})| ≤ arcsin(p^{-σ}) ≤ -log(1-p^{-σ})`, so
  `|(Lw s).im| ≤ ∑_p -log(1-p^{-σ}) = log ∏_p (1-p^{-σ})⁻¹ = log ζ(σ)`
  (`tprod_one_sub_eq_inv_zeta` in this file).  And `ζ(σ) ≤ 1 + 1/(σ-1) ≤ 4 + ‖s‖`, so
  `|(Lw s).im| ≤ log (4+‖s‖)`.
* Case `δ < 1/(3+‖s‖)`: put `σ₀ := σ + 1/(3+‖s‖)` (so `σ₀ - 1 ≥ 1/(3+‖s‖)` and
  `σ₀ ≤ σ+1`).  Then case 1 applies at `σ₀`: `|(Lw(σ₀+it)).im| ≤ log (5+‖s‖)`.  Moreover
  `Lw'(s) = -ζ'/ζ`, hence
  `|(Lw(σ+it)).im - (Lw(σ₀+it)).im| ≤ (σ₀-σ) · sup_{σ'∈[σ,σ₀]} |ζ'/ζ(σ'+it)|
     ≤ (1/(3+‖s‖)) · C log⁴(3+‖s‖) ≤ C'`
  using the log-derivative bounds: `logDeriv_zeta_const_bound` for `re ≥ 3/2` and
  `zeta_zeroFreeRegion_logDeriv_bound` for `1 ≤ σ' ≤ 2` (`σ' ≥ 1 ≥ 1-c/log(|t|+3)`!),
  plus compactness for `|t| ≤ 1`.  Done.

### DONE (session 3, later): the sharp bound is PROVEN
`norm_im_tsum_log_one_sub_le_log_zeta {s : ℂ} (hs : 1 < s.re) :
   ‖(∑' p, Complex.log (1 - p^{-s})).im‖ ≤ Real.log ((riemannZeta ((s.re:ℝ):ℂ)).re)`
proved via private helpers `summable_log_bfun`, `tsum_log_bfun_eq`
(`∑_p log (1-p^{-σ}) = -log (re ζ(σ))`, from `tprod_one_sub_eq_inv_zeta`)
and `norm_log_one_sub_le_neg_log` (`‖log (1-z)‖ ≤ -log (1-‖z‖)`, from
`Complex.hasSum_taylorSeries_log` + `Real.hasSum_pow_div_log_of_abs_lt_one`).
DONE: case 1 is PROVEN as `norm_im_tsum_log_one_sub_le_case1` (parameterised by the constant
`C` of `Commons.NumberTheory.Zeta.zeta_bound_halfplane_inv_sub_one`), giving
`|Im Lw s| ≤ log ((4+‖s‖) * ((1+C)(log (2+‖s‖)+1)))` when `s.re - 1 ≥ 1/(3+‖s‖)`.
NEXT: case 2: set `σ₀ := s.re + 1/(3+‖s‖)` and `s₀ := (σ₀:ℂ) + s.im·I` (so `σ₀ - 1 ≥ 1/(3+‖s‖)`,
`‖s₀‖ ≤ ‖s‖+1`), apply case 1 at `s₀`, and use
`|(Lw s).im - (Lw s₀).im| ≤ (σ₀ - s.re) * sup |(Lw' (σ'+i·s.im)).im| ≤ log⁴(3+‖s‖)/(3+‖s‖) ≤ 1`
via `Convex.norm_image_sub_le_of_norm_deriv_le` (as already used for `norm_omegaLocal_sub_one_le`)
once `Lw' = -ζ'/ζ` is available.  Route for `Lw' = -ζ'/ζ`: differentiate the identity
`exp (Lw z) = (ζ z)⁻¹` (`cexp_tsum_eq_tprod` + `tprod_one_sub_eq_inv_zeta`), or differentiate
`Lw = ∑'_p log (1 - p^{-·})` termwise (`hasDerivAt_tsum`), with derivative bound
`‖(log p) p^{-z}/(1-p^{-z})‖ ≤ 2 log p · p^{-re z}` and summability for `re z > 1`.
Then `|(Lw' (σ'+it)).im| ≤ ‖Lw'(σ'+it)‖ ≤ C log⁴(3+‖s‖)` for `σ' ∈ [s.re, σ₀]` using
`logDeriv_zeta_const_bound` (`σ' ≥ 3/2`) and `zeta_zeroFreeRegion_logDeriv_bound`
(`1 ≤ σ' ≤ 2`), plus compactness for `|t| ≤ 1`.

REFINED ROUTE for case 2 (avoids needing any strong bound on `ζ'/ζ`):
* `Lw` is analytic on `1 < re`: it is the locally uniform limit of the finite partial sums
  `∑_{p ≤ N} log (1 - p^{-z})` (dominate by `∑_p 2 p^{-σ}` on compacts and use
  `TendstoLocallyUniformlyOn.differentiableOn`, as done for `Hfun`).
* `cexp (Lw z) = (ζ z)⁻¹` (`cexp_tsum_eq_tprod` + `tprod_one_sub_eq_inv_zeta`).
* Chain rule: `Lw' = -ζ'/ζ` on `1 < re` (differentiate `cexp ∘ Lw`).
* Then `Lw' = ζ₁'/ζ₁ - 1/(s-1)`, so
  `(Lw (σ+it)).im - (Lw (σ₀+it)).im = -∫_σ^{σ₀} Im(ζ₁'/ζ₁)(σ'+it) dσ'
      + (arctan (t/(σ-1)) - arctan (t/(σ₀-1)))`.
  The arctangent difference is bounded by `π`; the integral is at most
  `(σ₀-σ) · sup_{[σ,σ₀]} ‖ζ₁'/ζ₁‖ ≤ log⁴(3+‖s‖)/(3+‖s‖) ≤ 1`.
* Apply case 1 at `s₀ := (σ₀ : ℂ) + s.im·I` (where `σ₀ - 1 ≥ 1/(3+‖s‖)`) and conclude.

DONE: `zeta1_logDeriv_halfplane_bound` is PROVEN (three-case split on `s.re` / `|s.im|`:
`logDeriv_zeta_const_bound` for `3/2 ≤ s.re`, `zeta_zeroFreeRegion_logDeriv_bound` for
`1 ≤ s.re ≤ 3/2` and `1 ≤ |s.im|` (note `s.re ≥ 1 ≥ 1-c/log(|t|+3)`), and
`IsCompact.exists_bound_of_continuousOn` on `[-1,1] ×ℂ [-3/2,3/2]` using
`logDeriv_zeta1_analyticAt` + `zeta1_ne_zero_of_one_le_re`; the `(s-1)⁻¹` term is bounded by
`2` resp. `1`).  Also added the imports `zeta_logDeriv_negStrip_bound`,
`zeta_zeroFreeRegion_logDeriv_bound`, `chebyshevPsi_at_height_farLeft_neg`.
REMAINING for case 2: analyticity of `Lw` (locally uniform limit of partial sums),
`cexp (Lw z) = (ζ z)⁻¹`, chain rule `Lw' = -ζ'/ζ`.

### Analyticity of `Lw` (next item, scoped)
Goal: `AnalyticOnNhd ℂ (fun z => ∑' p : Nat.Primes, Complex.log (1 - ((p:ℕ):ℂ)^(-z))) {z | 1 < z.re}`.
* `hasDerivAt_tsum` EXISTS but needs a SINGLE summable majorant `u` with `∀ n y, ‖g' n y‖ ≤ u n`
  over ALL `y : ℂ`; here `‖(log p) p^{-z}/(1-p^{-z})‖ ≍ log p · p^{-re z}` is unbounded as
  `re z → 1⁺`, so it does NOT apply directly.  (Noted so nobody wastes time on it.)
* Use the `Hfun` route instead (mirroring `analyticOnNhd_Hfun` in this file):
  `TendstoLocallyUniformlyOn.differentiableOn` applied to the finite partial sums
  `F N z = ∑ p ∈ (Nat.primesLE (N+1)), log (1 - p^{-z})`, which are differentiable (finite sums
  of analytic terms via `hasDerivAt` of `z ↦ log (1 - p^{-z})`), with
  `TendstoLocallyUniformlyOn F Lw atTop {z | 1 < z.re}` built from
  `Metric.tendstoUniformlyOn_iff` on each compact `K ⊆ {1 < re}` using the uniform tail bound
  `sup_{z ∈ K} ∑_{p > N} ‖log (1 - p^{-z})‖ ≤ ∑_{p > N} 2 p^{-σ_K} → 0`, `σ_K := inf_{z∈K} z.re > 1`.
  (`IsCompact.exists_forall_le` + `summable_primes_rpow_neg` give `σ_K` and the tail.)
  TWO EXACT TOOLS (located by probing):
  * `tendstoLocallyUniformlyOn_iff_forall_isCompact : IsOpen s →
      (TendstoLocallyUniformlyOn F f p s ↔ ∀ K ⊆ s, IsCompact K → TendstoUniformlyOn F f p K)`
    reduces the goal to the compact case;
  * `hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn :
      HasSumLocallyUniformlyOn f g s ↔ TendstoLocallyUniformlyOn (fun s z => ∑ i ∈ s, f i z) g atTop s`
    (index the family by `Finset Nat.Primes`, filter `atTop`).
  In the compact case use `Metric.tendstoUniformlyOn_iff` (`ε`-management) with the tail bound
  `‖∑'_{p ∉ s} log (1-p^{-z})‖ ≤ ∑'_{p ∉ s} 2 p^{-σ_K} → 0` as `s → atTop`.
* Then `Lw` is analytic on `{1 < re}` (`IsOpen`, `DifferentiableOn.analyticOnNhd`).

OLD: `σ₀ := s.re + 1/(3+‖s‖)`, use the sharp bound at `σ₀`
plus `|Im Lw s - Im Lw (σ₀+it)| ≤ (σ₀-σ) sup|ζ'/ζ|` with `logDeriv_zeta_const_bound`
(`σ' ≥ 3/2`) and `zeta_zeroFreeRegion_logDeriv_bound` (`1 ≤ σ' ≤ 2`).

### FINAL ingredient for case 1 and case 2: the SHARP bound `|Im Lw s| ≤ log ζ(σ)`
This (rather than the split bound, which loses an extra `log log`) is what makes
`|Im Lw s| ≤ log (3+‖s‖) + O(1)` come out with an ABSOLUTE constant.
Proof:
* For `‖z‖ < 1`, `HasSum (fun n => -z^n/n) (Complex.log (1-z))` (from
  `Complex.hasSum_taylorSeries_log` with `z → -z`).  Taking imaginary parts,
  `(Lw-term).im = -∑_n (z^n).im / n`, hence `|(log (1-z)).im| ≤ ∑_n ‖z‖^n/n = -log(1-‖z‖)`.
* `∑_p -log(1-p^{-σ}) = log ∏_p (1-p^{-σ})⁻¹ = log ζ(σ)` (`tprod_one_sub_eq_inv_zeta`).
Then case 1 (`δ ≥ 1/(3+‖s‖)`) gives `|Im Lw s| ≤ log ζ(σ) ≤ log (1+1/δ) ≤ log (4+‖s‖)`,
and case 2 uses the SAME sharp bound at `σ₀ = σ + 1/(3+‖s‖) ≥ 1 + 1/(3+‖s‖)` together with
`|Im Lw(σ+it) - Im Lw(σ₀+it)| ≤ (σ₀-σ)·sup|ζ'/ζ| ≤ log⁴(3+‖s‖)/(3+‖s‖) ≤ 1`
(`Lw' = -ζ'/ζ`; the log-derivative bounds give `|ζ'/ζ(σ'+it)| ≤ C log⁴(3+‖s‖)` for
`σ' ∈ [σ, σ₀]`: `logDeriv_zeta_const_bound` when `σ' ≥ 3/2`,
`zeta_zeroFreeRegion_logDeriv_bound` when `1 ≤ σ' ≤ 2` — note `σ' ≥ 1 ≥ 1-c/log(|t|+3)` —
and compactness when `|t| ≤ 1`).
Conclusion: `∃C, ∀s, 1 < s.re → |(Lw s).im| ≤ Real.log (4 + ‖s‖) + C`.

### Ingredients all available (details)
* Mertens upper bound is ELEMENTARY here: for `x ≥ 2`,
  `∑_{p ≤ x} 1/p ≤ log (log x + 1)` because
  `∑_{p≤x}1/p ≤ ∑_{p≤x} -log(1-1/p) = log ∏_{p≤x}(1-1/p)⁻¹ ≤ log ∏_{p≤x}(1-p^{-σ})⁻¹ ≤ log ζ(σ)`
  with `σ = 1 + 1/log x`, and `ζ(σ) ≤ 1 + 1/(σ-1) = 1 + log x`.
  (`∑_{p≤x}-log(1-p^{-σ}) ≤ log ζ(σ)` uses the same `tprod_one_sub_eq_inv_zeta` as above.)
* `arcsin r ≤ 2r` for `0 ≤ r ≤ 1/2`; `∑_{p>X} p^{-σ} ≤ X^{1-σ}/(σ-1)`.
  Hence the split bound `|(Lw s).im| ≤ ∑_{p≤X} arcsin(p^{-σ}) + ∑_{p>X} 2 p^{-σ}
   ≤ log(log X + 1) + 2 X^{1-σ}/δ`, with `δ = σ-1`, valid for every `X ≥ 2`.
* Case 1 (`δ ≥ 1/(3+‖s‖)`): take `X = exp (log 2/δ)`; then `log(log X+1) ≤ log(1/δ)+log log(2/δ)+O(1)
  ≤ log(3+‖s‖) + log log (3+‖s‖) + O(1)` and `2X^{1-σ}/δ ≤ 1`.

### *** CONSEQUENCE: the value and derivative bounds follow ***
With `|(Lw s).im| ≤ log(3+‖s‖)+C`, and `|ζ₁(s)| ≤ 1 + C|s-1| log(2+‖s‖) ≤ C'(1+‖s‖)^{1+ε}`,
`|A s| = |ζ₁(s)^{1+w}| · |Hfun w s| · |θ s|`, `|Hfun| ≤ C`, and
`|θ s| = exp (w.im·((Lw s).im + arg ζ s))` with `|arg ζ| ≤ π`, we get
`|A s| ≤ C''(1+‖s‖)^{(1+re w)(1+ε)} · (3+‖s‖)^{|w.im|}`.
Now for `‖w‖ ≤ 1/2` one has `|w.im| ≤ 1 - re w` (because `(1-x)² ≥ y²` follows from
`x²+y² ≤ 1/4`), and `1 - re w - |w.im| ≥ 1 - 1/√2 > 0`; choosing `ε` small enough gives
`|A s| ≤ D (1+‖s‖)²` as required.  The derivative bound follows from
`deriv (Afun w) s = Afun w s * ((1+w) logDeriv ζ₁ s + logDeriv (Hfun w) s)` on `1 < re s`
(V-trick: `Afun w / Hfun w` has log-derivative analytic and equal to `(1+w) logDeriv ζ₁`
on the real axis) together with `logDeriv_zeta_const_bound`,
`zeta_zeroFreeRegion_logDeriv_bound` and compactness: `|deriv A s| ≤ D'(1+‖s‖)² log⁴ ≤ D''(1+‖s‖)⁴`.

### USEFUL SIMPLIFICATION (one-sided bounds suffice)
Since `|A s| = |θ s| * ‖ζ₁(s)^{1+w}‖ * ‖Hfun w s‖` and `‖ζ₁(s)^{1+w}‖ ≤ C (log(2+‖s‖))^{1+re w}`,
and `2π M = -(Lw s).im - arg(ζ(s))` (so `|θ s| = exp (w.im * ((Lw s).im + arg ζ s))` with
`|arg ζ| ≤ π`), it is enough to have the ONE-SIDED bound matching the sign of `w.im`:
  * if `0 ≤ w.im`:   `(Lw s).im ≤ C + (1 - re w) * log (2 + ‖s‖)`,
  * if `w.im ≤ 0`:   `(Lw s).im ≥ -C - (1 - re w) * log (2 + ‖s‖)`.
(The trivial bound `(Lw s).im ≤ log ζ(σ) = log (1/(σ-1)) + O(1)` already gives the first
alternative whenever `σ - 1 ≥ c/(1+‖s‖)`; only the regime `σ - 1 < c/(1+‖s‖)` is open.
There `\|s-1\| ≈ \|s\|` and `(Lw s).im` differs from its limit `(Lw s).im` at `σ = 1` by
`O(δ log(2+\|s\|)) = O(log(2+\|s\|)/\|s\|)`, again a one-sided bound.)
Even more: it is enough that `θ` is bounded, i.e. that the winding `M` is bounded, which holds
if `Im L` is bounded — what a proof of `0 < re ζ(s)` on `1 < re s` would give immediately.

### SESSION 3 FINDINGS (the precise remaining gap)
The whole theorem now hinges on ONE statement about the prime-log series
`Lw s := ∑' p : Nat.Primes, Complex.log (1 - ((p:ℕ):ℂ)^(-s))` of its imaginary part:
   **`∃C, ∀ s, 1 < s.re → |(Lw s).im| ≤ C * (1 + Real.log (2 + ‖s‖))`.**
Facts established (numerically verified with PARI/GP, exact `zeta`):
* `θ s := (Dser w s * (s-1)^(1+w)) / (riemannZeta₁ s ^ (1+w) * Hfun w s)` is locally constant
  on `{s | 1 < s.re} \ ζ₁⁻¹((-∞,0])` and `θ = 1` on the component containing the real axis.
  `|θ s| = Real.exp (-2*π*M* w.im)` for an integer winding number `M`, and
  `2*π*M = -(Lw s).im - (riemannZeta s).arg`, so `|θ|` is controlled exactly by `|(Lw s).im|`.
* `(Lw s).im` is bounded  ⟺  `M ≡ 0`  ⟺  `θ ≡ 1`  ⟺  `0 < (riemannZeta s).re` for `1 < s.re`
  (the last equivalence: if `Re ζ > 0` on the half-plane then `ζ` misses `(-∞,0]`, so
  `Lw` and `-log ζ` (principal) are both analytic on the CONNECTED set `1 < re` and agree on
  the real axis, hence everywhere).
* NUMERICS: `min Re ζ(σ+it) > 0` for `σ > 1`, `t ≤ 10^5` (min ≈ 0.09 near `t = 32695`);
  `max |arg ζ(σ+it)| ≈ 1.485 < π/2`.  So `Re ζ > 0` is expected TRUE but proving it is a
  genuine analytic-number-theory theorem (equivalent to `arg ζ(σ+it) = O(1)`).
* Elementary bounds: `|(Lw s).im| ≤ log ζ(σ)` (termwise `|Im log(1-p^{-s})| ≤ -log(1-p^{-σ})`).
  Writing `δ = σ-1`, the sharpest splitting (Mertens head `∑_{p≤X} 1/p ≈ loglog X`, Chebyshev
  tail `∑_{p>X} sin(t log p)/p^σ ≪ X^{1-σ}/(δ log X)`) gives only `|(Lw s).im| ≲ log(1/δ)`,
  which is NOT `O(log log(2+‖s‖))` when `δ ≪ 1/(2+‖s‖)`.
* Borel–Carathéodory (`borelCaratheodory`, in Mathlib!) applied to `-log ζ` on a disk centered at
  `2+it` of radius `R < 1` gives `|(Lw s).im| ≤ (2*M*|z| + ‖f 0‖*(R+|z|))/(R-|z|)` with
  `M ≤ loglog(2+‖s‖)+O(1)`, hence `O(loglog)` for `re s ≥ 1 + η` with `η ≫ loglog/log`.
  Chaining disks geometrically down to `σ = 1+δ` loses `(η/δ)^{log₂ 3}`, i.e. it is polynomial
  in `1/δ` — NOT enough.  So BC alone does not close the gap.
* CONSEQUENCE for the value bound: `|A s| ≤ ‖ζ₁(s)^(1+w)‖ * ‖Hfun w s‖ * |θ s|` and
  `‖ζ₁(s)^(1+w)‖ ≤ C (log(2+‖s‖))^{3/2}`.  Hence it is enough to have
  `C |w.im| ≤ 2 - ε`, i.e. `C < 4` for `|w.im| ≤ 1/2`.  If `Re ζ > 0` holds then
  `|(Lw s).im| ≤ π/2` and the value bound is immediate.
* The derivative bound then follows from `deriv (Afun w) s = Afun w s * ((1+w)*logDeriv ζ₁ s +
  logDeriv (Hfun w) s)` on `1 < re` (V-trick: identity theorem for `Afun w / Hfun w`, whose
  log-derivative is analytic and equals `(1+w) * logDeriv ζ₁` on the real axis), together with
  `logDeriv_zeta_const_bound` + `zeta_zeroFreeRegion_logDeriv_bound` + compactness.
-/

section PerTermBound

/-- Per-term bound for the logarithmic series defining `Hfun w 1`:
`‖w log(1-1/p) + log(1+w/p)‖ ≤ ‖w‖/(p(p-1)) + (2/3)‖w‖²p⁻²`. -/
private lemma norm_log_series_term_le (w : ℂ) (hw : ‖w‖ ≤ 1/2) (p : Nat.Primes) :
    ‖w * Complex.log (1 - (((((p:ℕ):ℝ))⁻¹ : ℝ) : ℂ))
        + Complex.log (1 + w * (((((p:ℕ):ℝ))⁻¹ : ℝ) : ℂ))‖
      ≤ ‖w‖ * (1 / (((p:ℕ):ℝ) * (((p:ℕ):ℝ) - 1)))
        + (2/3) * ‖w‖^2 * ((((p:ℕ):ℝ))⁻¹)^2 := by
  set z : ℝ := (((p:ℕ):ℝ))⁻¹ with hz
  have hppos : (0:ℝ) < ((p:ℕ):ℝ) := by exact_mod_cast p.prop.pos
  have hp2 : (2:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast p.prop.two_le
  have hz0 : 0 < z := by rw [hz]; exact inv_pos.mpr hppos
  have hz1 : z ≤ 1/2 := by
    rw [hz, inv_le_comm₀ hppos (by norm_num : (0:ℝ) < 1/2)]
    linarith
  have h1z : (0:ℝ) < 1 - z := by linarith
  have hpm1 : (0:ℝ) < ((p:ℕ):ℝ) * (((p:ℕ):ℝ) - 1) := by nlinarith
  have hsplit : w * Complex.log (1 - (z:ℂ)) + Complex.log (1 + w * (z:ℂ))
      = (w * Complex.log (1 - (z:ℂ)) + w * (z:ℂ))
        + (Complex.log (1 + w*(z:ℂ)) - w*(z:ℂ)) := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [← mul_add]
    have hlog : Complex.log (1 - (z:ℂ)) + (z:ℂ) = (((Real.log (1 - z) + z : ℝ)) : ℂ) := by
      rw [show (1:ℂ) - (z:ℂ) = (((1 - z : ℝ)) : ℂ) by push_cast; ring,
        ← Complex.ofReal_log h1z.le, ← Complex.ofReal_add]
    rw [hlog, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have habs : |Real.log (1 - z) + z| ≤ z^2 / (1 - z) := abs_log_one_sub_add_self_le hz0 hz1
    have hzsq : z^2 / (1 - z) = 1 / (((p:ℕ):ℝ) * (((p:ℕ):ℝ) - 1)) := by
      rw [hz]
      field_simp
    exact mul_le_mul_of_nonneg_left (habs.trans hzsq.le) (norm_nonneg w)
  · have hnorm : ‖w * (z:ℂ)‖ = ‖w‖ * z := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz0]
    have hnorm' : ‖w‖ * z = ‖w * (z:ℂ)‖ := hnorm.symm
    have hle : ‖w‖ * z ≤ 1/4 := by nlinarith [hw, norm_nonneg w, hz0]
    have hlt : ‖w * (z:ℂ)‖ < 1 := by
      rw [← hnorm']; linarith
    have hpos_z : (0:ℝ) < 1 - ‖w‖ * z := by linarith
    have h43 : (0:ℝ) < 4/3 := by norm_num
    have hinv : (1 - ‖w‖ * z)⁻¹ ≤ 4/3 := by
      have h : (3:ℝ)/4 ≤ 1 - ‖w‖ * z := by linarith
      calc (1 - ‖w‖ * z)⁻¹ ≤ ((3:ℝ)/4)⁻¹ :=
            (inv_le_inv₀ hpos_z (by norm_num : (0:ℝ) < 3/4)).mpr h
        _ = 4/3 := by norm_num
    have hself : ‖Complex.log (1 + w*(z:ℂ)) - w*(z:ℂ)‖
        ≤ ‖w*(z:ℂ)‖^2 * (1 - ‖w*(z:ℂ)‖)⁻¹ / 2 :=
      Complex.norm_log_one_add_sub_self_le (z := w * (z:ℂ)) hlt
    have hstep : (‖w‖ * z)^2 * (1 - ‖w‖ * z)⁻¹ / 2 ≤ (‖w‖ * z)^2 * (4/3) / 2 := by
      have h2 : (0:ℝ) ≤ (‖w‖*z)^2 := sq_nonneg _
      have h3 : (‖w‖*z)^2 * (1 - ‖w‖ * z)⁻¹ ≤ (‖w‖*z)^2 * (4/3) :=
        mul_le_mul_of_nonneg_left hinv h2
      linarith
    calc ‖Complex.log (1 + w*(z:ℂ)) - w*(z:ℂ)‖
        ≤ ‖w*(z:ℂ)‖^2 * (1 - ‖w*(z:ℂ)‖)⁻¹ / 2 := hself
      _ = (‖w‖ * z)^2 * (1 - ‖w‖ * z)⁻¹ / 2 := by rw [hnorm]
      _ ≤ (‖w‖ * z)^2 * (4/3) / 2 := hstep
      _ = (2/3) * ‖w‖^2 * ((((p:ℕ):ℝ))⁻¹)^2 := by rw [hz]; ring

end PerTermBound


section HfunBounds
variable {w : ℂ}

/-- The local factor is nonzero (as a product of two nonvanishing factors). -/
lemma one_add_omegaLocalHat_eq (w : ℂ) (p : Nat.Primes) (s : ℂ) :
    1 + omegaLocalHat w p s = (1 - ((p:ℕ):ℂ)^(-s)) ^ w * (1 + w * ((p:ℕ):ℂ)^(-s)) := by
  simp only [omegaLocalHat, omegaLocal]
  ring

/-- Lower bound for the modulus of `z ^ w` when `z` is bounded away from `0`. -/
lemma norm_cpow_lower {z w : ℂ} (h1 : (1/4:ℝ) ≤ ‖z‖) (h2 : ‖z‖ ≤ 4) (hw : ‖w‖ ≤ 1/2) :
    (1/2) * Real.exp (-(Real.pi/2)) ≤ ‖z ^ w‖ := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at h1
    simp at h1
    linarith
  have hlog : |Real.log ‖z‖| ≤ Real.log 4 := by
    rw [abs_le]
    constructor
    · have h : Real.log (1/4) ≤ Real.log ‖z‖ := Real.log_le_log (by norm_num) h1
      have h4 : Real.log (1/4) = - Real.log 4 := by
        rw [show (1/4:ℝ) = (4:ℝ)⁻¹ by norm_num, Real.log_inv]
      linarith [h4 ▸ h]
    · exact Real.log_le_log (by linarith) h2
  have harg : |z.arg| ≤ Real.pi := by
    rw [abs_le]
    exact ⟨le_of_lt (Complex.neg_pi_lt_arg z), Complex.arg_le_pi z⟩
  have hwim : |w.im| ≤ 1/2 := by
    have h := abs_im_le_norm w
    linarith
  have hwre : |w.re| ≤ 1/2 := by
    have h := Complex.abs_re_le_norm w
    linarith
  rw [Complex.cpow_def_of_ne_zero hz0, Complex.norm_exp, Complex.mul_re, Complex.log_re,
    Complex.log_im]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  have hloghalf : Real.log (1/2) = -(Real.log 4 * (1/2)) := by
    rw [show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num, Real.log_inv, hlog4]; ring
  have hb : -(Real.log 4 * (1/2)) ≤ Real.log ‖z‖ * w.re := by
    have h3 : -(|Real.log ‖z‖| * |w.re|) ≤ Real.log ‖z‖ * w.re := by
      have := neg_abs_le (Real.log ‖z‖ * w.re)
      rw [abs_mul] at this
      linarith
    have h4 : |Real.log ‖z‖| * |w.re| ≤ Real.log 4 * (1/2) :=
      mul_le_mul hlog hwre (abs_nonneg _) (le_of_lt (Real.log_pos (by norm_num)))
    linarith
  have hc : -(z.arg * w.im) ≥ -(Real.pi * (1/2)) := by
    have h2 : z.arg * w.im ≤ |z.arg| * |w.im| := by
      rw [← abs_mul]; exact le_abs_self _
    have h4 : |z.arg| * |w.im| ≤ Real.pi * (1/2) :=
      mul_le_mul harg hwim (abs_nonneg _) (le_of_lt Real.pi_pos)
    linarith
  calc (1/2) * Real.exp (-(Real.pi/2)) = Real.exp (Real.log (1/2) - Real.pi/2) := by
        rw [Real.exp_sub, Real.exp_log (by norm_num), Real.exp_neg]; ring
    _ ≤ Real.exp (Real.log ‖z‖ * w.re - z.arg * w.im) := by
        apply Real.exp_le_exp.mpr
        rw [hloghalf]
        linarith


/-- Summability of the local factors on `omK`. -/
lemma summable_omegaLocalHat (hw : ‖w‖ ≤ 1/2) {s : ℂ} (hs : s ∈ omK) :
    Summable (fun p : Nat.Primes => omegaLocalHat w p s) :=
  (summable_omMajorant).of_norm_bounded (fun p => norm_omegaLocalHat_le (p:=p) hw hs)

/-- Lower bound for the modulus of the local factor on `omK`. -/
lemma norm_one_add_omegaLocalHat_ge (hw : ‖w‖ ≤ 1/2) {p : Nat.Primes} {s : ℂ} (hs : s ∈ omK) :
    (1/100 : ℝ) ≤ ‖1 + omegaLocalHat w p s‖ := by
  rw [one_add_omegaLocalHat_eq, norm_mul]
  have hz : ‖(((p:ℕ):ℂ)^(-s))‖ ≤ 3/4 := norm_prime_cpow_le (p:=p) hs
  have hza : ‖(((p:ℕ):ℂ)^(-s))‖ ≤ 1 := by linarith
  have h1 : (1/2) * Real.exp (-(Real.pi/2)) ≤ ‖(1 - ((p:ℕ):ℂ)^(-s)) ^ w‖ := by
    apply norm_cpow_lower
    · have h := abs_norm_sub_norm_le (1:ℂ) (((p:ℕ):ℂ)^(-s))
      rw [norm_one] at h
      have h2 : |1 - ‖(((p:ℕ):ℂ)^(-s))‖| ≤ ‖1 - (((p:ℕ):ℂ)^(-s))‖ := by
        simpa using h
      rw [abs_le] at h2
      linarith [h2.1]
    · have h := norm_sub_le (1:ℂ) (((p:ℕ):ℂ)^(-s))
      rw [norm_one] at h
      linarith
    · exact hw
  have h2 : (1/2 : ℝ) ≤ ‖1 + w * (((p:ℕ):ℂ)^(-s))‖ := by
    have h := abs_norm_sub_norm_le (1:ℂ) (-(w * (((p:ℕ):ℂ)^(-s))))
    rw [norm_one, norm_neg, norm_mul] at h
    have h3 : ‖w‖ * ‖(((p:ℕ):ℂ)^(-s))‖ ≤ 1/2 * (3/4) :=
      mul_le_mul hw hz (norm_nonneg _) (by norm_num)
    have h4 : ‖(1:ℂ) - -(w * (((p:ℕ):ℂ)^(-s)))‖ = ‖1 + w * (((p:ℕ):ℂ)^(-s))‖ := by
      rw [sub_neg_eq_add]
    rw [h4] at h
    rw [abs_le] at h
    linarith [h.1]
  have hexp : (1/9 : ℝ) ≤ Real.exp (-(Real.pi/2)) := by
    have h3 : Real.exp (-(Real.pi/2)) ≥ Real.exp (-2) :=
      Real.exp_le_exp.mpr (by linarith [Real.pi_lt_four])
    have h5 : (Real.exp 2 : ℝ) ≤ 9 := by
      have h6 : Real.exp 2 = (Real.exp 1)^2 := by
        rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add, pow_two]
      have h7 : Real.exp 1 ≤ 2.72 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
      rw [h6]
      nlinarith [Real.exp_pos 1]
    have h8 : Real.exp (-2 : ℝ) = (Real.exp 2)⁻¹ := Real.exp_neg 2
    have h9 : (1/9 : ℝ) ≤ (Real.exp 2)⁻¹ := by
      have h10 : ((9:ℝ)⁻¹) ≤ (Real.exp 2)⁻¹ :=
        (inv_le_inv₀ (by norm_num) (by positivity)).mpr h5
      linarith [h10]
    linarith [h3, h8 ▸ h9]
  calc (1/100 : ℝ) ≤ ((1/2) * (1/9)) * (1/2) := by norm_num
    _ ≤ ((1/2) * Real.exp (-(Real.pi/2))) * (1/2) := by nlinarith [hexp]
    _ ≤ ‖(1 - ((p:ℕ):ℂ)^(-s)) ^ w‖ * ‖1 + w * (((p:ℕ):ℂ)^(-s))‖ :=
        mul_le_mul h1 h2 (by norm_num) (by positivity)

/-- Upper bound for the modulus of the local factor on `omK`. -/
lemma norm_one_add_omegaLocalHat_le' {w : ℂ} (hw : ‖w‖ ≤ 1/2) {p : Nat.Primes} {s : ℂ}
    (hs : s ∈ omK) :
    ‖1 + omegaLocalHat w p s‖ ≤ 1 + 200 * (((p:ℕ):ℝ))^(-(3/2:ℝ)) := by
  have h := norm_add_le (1:ℂ) (omegaLocalHat w p s)
  rw [norm_one] at h
  linarith [h, norm_omegaLocalHat_le (p:=p) hw hs]

/-- `exp 5 ≥ 100`. -/
private lemma hundred_le_exp_five' : (100:ℝ) ≤ Real.exp 5 := by
  have h1 : Real.exp (5:ℝ) = (Real.exp 1)^5 := by
    rw [show (5:ℝ) = (5:ℕ) * 1 by norm_num, Real.exp_nat_mul]
  rw [h1]
  have h2 : (2.7182818283 : ℝ)^5 ≤ (Real.exp 1)^5 :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 5
  have h3 : (100:ℝ) ≤ (2.7182818283 : ℝ)^5 := by norm_num
  linarith

/-- Log bound for the local factor on `omK`. -/
lemma norm_log_one_add_omegaLocalHat_le {w : ℂ} (hw : ‖w‖ ≤ 1/2) {p : Nat.Primes} {s : ℂ}
    (hs : s ∈ omK) :
    ‖Complex.log (1 + omegaLocalHat w p s)‖ ≤ 4000 * (((p:ℕ):ℝ))^(-(3/2:ℝ)) := by
  have hpos : (0:ℝ) < (((p:ℕ):ℝ)) := by rw [Nat.cast_pos]; exact p.prop.pos
  have hpos' : (0:ℝ) < (((p:ℕ):ℝ))^(-(3/2:ℝ)) := Real.rpow_pos_of_pos hpos _
  by_cases hsmall : ‖omegaLocalHat w p s‖ ≤ 1/2
  · have h1 : ‖Complex.log (1 + omegaLocalHat w p s)‖ ≤ 3/2 * ‖omegaLocalHat w p s‖ :=
      Complex.norm_log_one_add_half_le_self hsmall
    have h2 := norm_omegaLocalHat_le (p:=p) hw hs
    have h3 : (3/2 : ℝ) * (200 * (((p:ℕ):ℝ))^(-(3/2:ℝ))) ≤ 4000 * (((p:ℕ):ℝ))^(-(3/2:ℝ)) := by
      nlinarith [hpos']
    linarith
  · push_neg at hsmall
    -- the crude per-term bound for the modulus is small for large `p`, so `p` is bounded
    have hp54 : (((p:ℕ):ℝ)) ≤ 54 := by
      by_contra hcon
      push_neg at hcon
      have hpnat : (54:ℕ) < (p:ℕ) := by exact_mod_cast hcon
      have hp55 : (55:ℝ) ≤ (((p:ℕ):ℝ)) := by
        have : (55:ℕ) ≤ (p:ℕ) := by omega
        exact_mod_cast this
      have h2 := norm_omegaLocalHat_le (p:=p) hw hs
      have h4 : ((((p:ℕ):ℝ))^(3/2:ℝ))⁻¹ > ((400:ℝ))⁻¹ := by
        have h5 : (((p:ℕ):ℝ))^(-(3/2:ℝ)) = ((((p:ℕ):ℝ))^(3/2:ℝ))⁻¹ := by
          rw [← Real.rpow_neg (le_of_lt hpos)]
        have h6 : (((p:ℕ):ℝ))^(-(3/2:ℝ)) > 1/400 := by nlinarith [h2, hsmall]
        rw [h5] at h6
        simpa [show (1/400 : ℝ) = ((400:ℝ))⁻¹ by norm_num] using h6
      have h7 : (((p:ℕ):ℝ))^(3/2:ℝ) < 400 :=
        (inv_lt_inv₀ (by norm_num : (0:ℝ) < 400) (Real.rpow_pos_of_pos hpos _)).mp h4
      have h8 : (55:ℝ)^(3/2:ℝ) ≤ (((p:ℕ):ℝ))^(3/2:ℝ) :=
        Real.rpow_le_rpow (by norm_num) hp55 (by norm_num)
      have h9 : (400:ℝ) < (55:ℝ)^(3/2:ℝ) := by
        rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
          ← Real.sqrt_eq_rpow]
        have hs55 : (7.4:ℝ) ≤ Real.sqrt 55 := by
          rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
        nlinarith
      linarith
    have hnum : 200 * (2:ℝ)^(-(3/2:ℝ)) ≤ 71 := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      rw [show (2:ℝ)^(3/2:ℝ) = 2 * Real.sqrt 2 by
        rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
          ← Real.sqrt_eq_rpow]]
      have hs2 : (1.414:ℝ) ≤ Real.sqrt 2 := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
      rw [← div_eq_mul_inv, div_le_iff₀ (by nlinarith [hs2] : (0:ℝ) < 2 * Real.sqrt 2)]
      nlinarith
    have h72 : ‖1 + omegaLocalHat w p s‖ ≤ 72 := by
      have h2r : (((p:ℕ):ℝ))^(-(3/2:ℝ)) ≤ (2:ℝ)^(-(3/2:ℝ)) := by
        apply Real.rpow_le_rpow_of_nonpos (show (0:ℝ) < 2 by norm_num)
        · exact_mod_cast p.prop.two_le
        · norm_num
      nlinarith [norm_one_add_omegaLocalHat_le' hw hs (p:=p), hnum, h2r, hpos']
    have h9 : ‖Complex.log (1 + omegaLocalHat w p s)‖ ≤ 9 := by
      have hre : ‖Complex.log (1 + omegaLocalHat w p s)‖ ≤
          |Real.log ‖1 + omegaLocalHat w p s‖| + |Complex.arg (1 + omegaLocalHat w p s)| := by
        have h1 : Complex.log (1 + omegaLocalHat w p s)
            = ((Real.log ‖1 + omegaLocalHat w p s‖ : ℝ) : ℂ)
              + ((Complex.arg (1 + omegaLocalHat w p s) : ℝ) : ℂ) * Complex.I := by
          apply Complex.ext <;> simp [Complex.log_re, Complex.log_im]
        calc ‖Complex.log (1 + omegaLocalHat w p s)‖
            = ‖((Real.log ‖1 + omegaLocalHat w p s‖ : ℝ) : ℂ)
                + ((Complex.arg (1 + omegaLocalHat w p s) : ℝ) : ℂ) * Complex.I‖ := by rw [h1]
          _ ≤ ‖((Real.log ‖1 + omegaLocalHat w p s‖ : ℝ) : ℂ)‖
                + ‖((Complex.arg (1 + omegaLocalHat w p s) : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
          _ = |Real.log ‖1 + omegaLocalHat w p s‖| + |Complex.arg (1 + omegaLocalHat w p s)| := by
              simp
      have harg2 : |Complex.arg (1 + omegaLocalHat w p s)| ≤ Real.pi := by
        rw [abs_le]
        exact ⟨le_of_lt (Complex.neg_pi_lt_arg _), Complex.arg_le_pi _⟩
      have hge := norm_one_add_omegaLocalHat_ge hw hs (p:=p)
      have hlog100 : Real.log (100:ℝ) ≤ 5 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        exact hundred_le_exp_five'
      have hlogb : |Real.log ‖1 + omegaLocalHat w p s‖| ≤ 5 := by
        rw [abs_le]
        constructor
        · have h : Real.log (1/100) ≤ Real.log ‖1 + omegaLocalHat w p s‖ :=
            Real.log_le_log (by norm_num) hge
          have h100 : Real.log (1/100) = -Real.log 100 := by
            rw [show (1/100:ℝ) = (100:ℝ)⁻¹ by norm_num, Real.log_inv]
          rw [h100] at h
          linarith
        · have h : Real.log ‖1 + omegaLocalHat w p s‖ ≤ Real.log 72 :=
            Real.log_le_log (by linarith [hge]) h72
          have h72' : Real.log (72:ℝ) ≤ 5 := by
            rw [Real.log_le_iff_le_exp (by norm_num)]
            linarith [hundred_le_exp_five']
          linarith
      linarith [Real.pi_lt_four]
    have h4000 : (9:ℝ) ≤ 4000 * (((p:ℕ):ℝ))^(-(3/2:ℝ)) := by
      have h3 : 4000 * (54:ℝ)^(-(3/2:ℝ)) ≤ 4000 * (((p:ℕ):ℝ))^(-(3/2:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.rpow_le_rpow_of_nonpos hpos hp54 (show (-(3/2:ℝ)) ≤ 0 by norm_num)
      have h4 : (9:ℝ) ≤ 4000 * (54:ℝ)^(-(3/2:ℝ)) := by
        rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 54)]
        rw [show (54:ℝ)^(3/2:ℝ) = 54 * Real.sqrt 54 by
          rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
            ← Real.sqrt_eq_rpow]]
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
        have hs54 : Real.sqrt 54 ≤ 7.4 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        have hfin : (9:ℝ) * (54 * Real.sqrt 54) ≤ 9 * (54 * 7.4) := by
          nlinarith [hs54]
        linarith [hfin]
      linarith
    linarith

/-- `Hfun` as the exponential of the sum of logarithms. -/
lemma Hfun_eq_cexp {w : ℂ} (hw : ‖w‖ ≤ 1/2) {s : ℂ} (hs : s ∈ omK) :
    Hfun w s = Complex.exp (∑' p : Nat.Primes, Complex.log (1 + omegaLocalHat w p s)) := by
  have hne : ∀ p : Nat.Primes, 1 + omegaLocalHat w p s ≠ 0 := by
    intro p h
    have h1 := norm_one_add_omegaLocalHat_ge hw hs (p:=p)
    rw [h, norm_zero] at h1
    linarith
  have hsum : Summable (fun p : Nat.Primes => Complex.log (1 + omegaLocalHat w p s)) :=
    Complex.summable_log_one_add_of_summable (summable_omegaLocalHat hw hs)
  exact (Complex.cexp_tsum_eq_tprod hne hsum).symm

/-- `Hfun` does not vanish on `omK`. -/
lemma Hfun_w_ne_zero {w : ℂ} (hw : ‖w‖ ≤ 1/2) {s : ℂ} (hs : s ∈ omK) : Hfun w s ≠ 0 := by
  rw [Hfun_eq_cexp hw hs]
  exact Complex.exp_ne_zero _

/-- Summability of the logarithms of the moduli of the local factors. -/
lemma summable_log_norm_one_add_omegaLocalHat {w : ℂ} (hw : ‖w‖ ≤ 1/2) {s : ℂ} (hs : s ∈ omK) :
    Summable (fun p : Nat.Primes => Real.log (1 + ‖omegaLocalHat w p s‖)) := by
  have hb : Summable (fun p : Nat.Primes => ‖omegaLocalHat w p s‖) :=
    (summable_omMajorant).of_nonneg_of_le (fun p => norm_nonneg _)
      (fun p => norm_omegaLocalHat_le (p:=p) hw hs)
  refine hb.of_nonneg_of_le (fun p => Real.log_nonneg (by linarith [norm_nonneg (omegaLocalHat w p s)]))
    (fun p => ?_)
  have hp : (0:ℝ) < 1 + ‖omegaLocalHat w p s‖ := by linarith [norm_nonneg (omegaLocalHat w p s)]
  have := Real.log_le_sub_one_of_pos hp
  linarith

/-- Upper and lower bounds for `Hfun` on `omK`. -/
lemma norm_Hfun_bounds {w : ℂ} (hw : ‖w‖ ≤ 1/2) {s : ℂ} (hs : s ∈ omK) :
    Real.exp (-(4000 * (∑' p : Nat.Primes, (((p:ℕ):ℝ))^(-(3/2:ℝ))))) ≤ ‖Hfun w s‖ ∧
      ‖Hfun w s‖ ≤ Real.exp (200 * (∑' p : Nat.Primes, (((p:ℕ):ℝ))^(-(3/2:ℝ)))) := by
  have hsumm : Summable (fun p : Nat.Primes => (((p:ℕ):ℝ))^(-(3/2:ℝ))) :=
    summable_primes_rpow_neg (by norm_num)
  have hsum : Summable (fun p : Nat.Primes => Complex.log (1 + omegaLocalHat w p s)) :=
    Complex.summable_log_one_add_of_summable (summable_omegaLocalHat hw hs)
  have hlog : Summable (fun p : Nat.Primes => ‖Complex.log (1 + omegaLocalHat w p s)‖) :=
    (hsumm.mul_left 4000).of_nonneg_of_le (fun p => norm_nonneg _)
      (fun p => norm_log_one_add_omegaLocalHat_le hw hs (p:=p))
  have hlogM : Summable (fun p : Nat.Primes => Real.log (1 + ‖omegaLocalHat w p s‖)) :=
    summable_log_norm_one_add_omegaLocalHat hw hs
  have ha : Summable (fun p : Nat.Primes => ‖omegaLocalHat w p s‖) :=
    (summable_omMajorant).of_nonneg_of_le (fun p => norm_nonneg _)
      (fun p => norm_omegaLocalHat_le (p:=p) hw hs)
  have hn : Summable (fun p : Nat.Primes => 200 * (((p:ℕ):ℝ))^(-(3/2:ℝ))) := hsumm.mul_left 200
  rw [Hfun_eq_cexp hw hs, Complex.norm_exp]
  have hsumre : Summable (fun p : Nat.Primes => (Complex.log (1 + omegaLocalHat w p s)).re) :=
    Summable.of_norm_bounded hlog (fun p => Complex.abs_re_le_norm _)
  have hre : (∑' p : Nat.Primes, Complex.log (1 + omegaLocalHat w p s)).re
      = ∑' p : Nat.Primes, (Complex.log (1 + omegaLocalHat w p s)).re := Complex.re_tsum hsum
  rw [hre]
  constructor
  · apply Real.exp_le_exp.mpr
    have h1 : (∑' p : Nat.Primes, (Complex.log (1 + omegaLocalHat w p s)).re)
        ≥ ∑' p : Nat.Primes, -(‖Complex.log (1 + omegaLocalHat w p s)‖) := by
      apply Summable.tsum_le_tsum (fun p => ?_) hlog.neg hsumre
      exact neg_le_of_abs_le (Complex.abs_re_le_norm _)
    have h2 : (∑' p : Nat.Primes, -(‖Complex.log (1 + omegaLocalHat w p s)‖))
        = -(∑' p : Nat.Primes, ‖Complex.log (1 + omegaLocalHat w p s)‖) := tsum_neg
    have h3 : (∑' p : Nat.Primes, ‖Complex.log (1 + omegaLocalHat w p s)‖)
        ≤ 4000 * (∑' p : Nat.Primes, (((p:ℕ):ℝ))^(-(3/2:ℝ))) := by
      have h := Summable.tsum_le_tsum (fun p => norm_log_one_add_omegaLocalHat_le hw hs (p:=p))
        hlog (hsumm.mul_left 4000)
      rwa [tsum_mul_left] at h
    rw [h2] at h1
    linarith
  · apply Real.exp_le_exp.mpr
    have h1 : (∑' p : Nat.Primes, (Complex.log (1 + omegaLocalHat w p s)).re)
        ≤ ∑' p : Nat.Primes, Real.log (1 + ‖omegaLocalHat w p s‖) := by
      apply Summable.tsum_le_tsum (fun p => ?_) hsumre hlogM
      rw [Complex.log_re]
      exact Real.log_le_log (by linarith [norm_one_add_omegaLocalHat_ge hw hs (p:=p)])
        (by simpa using norm_add_le (1:ℂ) (omegaLocalHat w p s))
    have h2 : (∑' p : Nat.Primes, Real.log (1 + ‖omegaLocalHat w p s‖))
        ≤ ∑' p : Nat.Primes, ‖omegaLocalHat w p s‖ :=
      Summable.tsum_le_tsum (fun p => by
        have hp : (0:ℝ) < 1 + ‖omegaLocalHat w p s‖ := by
          linarith [norm_nonneg (omegaLocalHat w p s)]
        have := Real.log_le_sub_one_of_pos hp
        linarith) hlogM ha
    have h3 : (∑' p : Nat.Primes, ‖omegaLocalHat w p s‖)
        ≤ 200 * (∑' p : Nat.Primes, (((p:ℕ):ℝ))^(-(3/2:ℝ))) := by
      have h := Summable.tsum_le_tsum (fun p => norm_omegaLocalHat_le (p:=p) hw hs) ha hn
      rwa [tsum_mul_left] at h
    linarith



section ImPrimeLogBound

/-- Per-term bound: for a prime `p` and `1 < re s`, `‖log (1 - p^{-s})‖ ≤ 2 * p^{-re s}`. -/
private lemma norm_log_one_sub_natCast_cpow_le {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    ‖Complex.log (1 - ((p:ℕ):ℂ) ^ (-s))‖ ≤ 2 * (((p:ℕ):ℝ)) ^ (-s.re) := by
  have hposn : (0:ℝ) < ((p:ℕ):ℝ) := by exact_mod_cast p.prop.pos
  have hle : (((p:ℕ):ℝ)) ^ (-s.re) ≤ 1/2 := prime_rpow_neg_le_half hs p
  have hpos : (0:ℝ) < (((p:ℕ):ℝ)) ^ (-s.re) := Real.rpow_pos_of_pos hposn _
  have hnorm : ‖((p:ℕ):ℂ) ^ (-s)‖ = (((p:ℕ):ℝ)) ^ (-s.re) :=
    Complex.norm_natCast_cpow_of_pos p.prop.pos (-s)
  have hlt : ‖((p:ℕ):ℂ) ^ (-s)‖ < 1 := by rw [hnorm]; linarith
  have hself : ‖Complex.log (1 - ((p:ℕ):ℂ) ^ (-s)) + ((p:ℕ):ℂ) ^ (-s)‖
      ≤ ‖((p:ℕ):ℂ) ^ (-s)‖ ^ 2 * (1 - ‖((p:ℕ):ℂ) ^ (-s)‖)⁻¹ / 2 := by
    have h := Complex.norm_log_one_add_sub_self_le (z := -(((p:ℕ):ℂ) ^ (-s)))
      (by simpa using hlt)
    have h1 : ‖-(((p:ℕ):ℂ) ^ (-s))‖ = ‖((p:ℕ):ℂ) ^ (-s)‖ := norm_neg _
    rw [h1] at h
    have h2 : Complex.log (1 + -(((p:ℕ):ℂ) ^ (-s))) - -(((p:ℕ):ℂ) ^ (-s))
        = Complex.log (1 - ((p:ℕ):ℂ) ^ (-s)) + ((p:ℕ):ℂ) ^ (-s) := by ring_nf
    rwa [h2] at h
  have h2 : ‖Complex.log (1 - ((p:ℕ):ℂ) ^ (-s))‖
      ≤ ‖((p:ℕ):ℂ) ^ (-s)‖ + ‖((p:ℕ):ℂ) ^ (-s)‖^2 * (1 - ‖((p:ℕ):ℂ) ^ (-s)‖)⁻¹ / 2 := by
    have hz : Complex.log (1 - ((p:ℕ):ℂ) ^ (-s)) + ((p:ℕ):ℂ) ^ (-s) + -(((p:ℕ):ℂ) ^ (-s))
        = Complex.log (1 - ((p:ℕ):ℂ) ^ (-s)) := by ring
    calc ‖Complex.log (1 - ((p:ℕ):ℂ) ^ (-s))‖
        = ‖Complex.log (1 - ((p:ℕ):ℂ) ^ (-s)) + ((p:ℕ):ℂ) ^ (-s) + -(((p:ℕ):ℂ) ^ (-s))‖ := by
          rw [hz]
      _ ≤ ‖Complex.log (1 - ((p:ℕ):ℂ) ^ (-s)) + ((p:ℕ):ℂ) ^ (-s)‖ + ‖-(((p:ℕ):ℂ) ^ (-s))‖ :=
          norm_add_le _ _
      _ = ‖Complex.log (1 - ((p:ℕ):ℂ) ^ (-s)) + ((p:ℕ):ℂ) ^ (-s)‖ + ‖((p:ℕ):ℂ) ^ (-s)‖ := by
          rw [norm_neg]
      _ ≤ _ := by linarith [hself]
  have h3 : ‖((p:ℕ):ℂ) ^ (-s)‖^2 * (1 - ‖((p:ℕ):ℂ) ^ (-s)‖)⁻¹ / 2 ≤ ‖((p:ℕ):ℂ) ^ (-s)‖^2 := by
    have h2pos : (0:ℝ) < 1 - ‖((p:ℕ):ℂ) ^ (-s)‖ := by rw [hnorm]; linarith
    have hinv : (1 - ‖((p:ℕ):ℂ) ^ (-s)‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ h2pos (by norm_num : (0:ℝ) < 2)]
      rw [hnorm]; linarith
    have hsq : (0:ℝ) ≤ ‖((p:ℕ):ℂ) ^ (-s)‖^2 := sq_nonneg _
    nlinarith [hinv, hsq]
  have h4 : ‖((p:ℕ):ℂ) ^ (-s)‖ + ‖((p:ℕ):ℂ) ^ (-s)‖^2 ≤ 2 * (((p:ℕ):ℝ)) ^ (-s.re) := by
    rw [hnorm]; nlinarith [hpos, hle]
  linarith [h2, h3, h4]

/-- The imaginary part of `∑_p log (1 - p^{-s})` is at most `∑_p 2 p^{-re s}`. -/
lemma norm_im_tsum_log_one_sub_natCast_cpow_le {s : ℂ} (hs : 1 < s.re) :
    ‖(∑' p : Nat.Primes, Complex.log (1 - ((p:ℕ):ℂ) ^ (-s))).im‖
      ≤ ∑' p : Nat.Primes, 2 * (((p:ℕ):ℝ)) ^ (-s.re) := by
  have hsummR : Summable (fun p : Nat.Primes => (((p:ℕ):ℝ)) ^ (-s.re)) :=
    summable_primes_rpow_neg hs
  have hbd : ∀ p : Nat.Primes,
      ‖Complex.log (1 - ((p:ℕ):ℂ) ^ (-s))‖ ≤ 2 * (((p:ℕ):ℝ)) ^ (-s.re) :=
    fun p => norm_log_one_sub_natCast_cpow_le hs p
  have hsumm : Summable (fun p : Nat.Primes => Complex.log (1 - ((p:ℕ):ℂ) ^ (-s))) :=
    Summable.of_norm_bounded (hsummR.mul_left 2) hbd
  have himn : Summable (fun p : Nat.Primes => ‖(Complex.log (1 - ((p:ℕ):ℂ) ^ (-s))).im‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _)
      (fun p => (Complex.abs_im_le_norm _).trans (hbd p)) (hsummR.mul_left 2)
  rw [Complex.im_tsum hsumm]
  exact (norm_tsum_le_tsum_norm himn).trans
    (Summable.tsum_le_tsum (fun p => (Complex.abs_im_le_norm _).trans (hbd p)) himn
      (hsummR.mul_left 2))

end ImPrimeLogBound

section SharpImBound

/-- `Summable (fun p => Real.log (bfun σ p))` for `σ > 1`. -/
private lemma summable_log_bfun {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => Real.log (bfun σ p)) := by
  refine Summable.of_norm ?_
  refine (summable_primes_rpow_neg hσ).mul_left 2 |>.of_nonneg_of_le
    (fun p => abs_nonneg _) (fun p => ?_)
  simpa only [Real.norm_eq_abs, bfun] using
    abs_log_one_sub_le (x := (((p:ℕ):ℝ)) ^ (-σ))
      (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) (-σ)) (prime_rpow_neg_le_half hσ p)

/-- `∑_p log (bfun σ p) = - log (re ζ(σ))` for real `σ > 1`. -/
private lemma tsum_log_bfun_eq {σ : ℝ} (hσ : 1 < σ) :
    (∑' p : Nat.Primes, Real.log (bfun σ p)) = -Real.log ((riemannZeta (σ:ℂ)).re) := by
  obtain ⟨hZre, hZim0⟩ := Complex.pos_iff.mp (riemannZeta_pos_of_one_lt hσ)
  have hZeq : riemannZeta (σ:ℂ) = ↑((riemannZeta (σ:ℂ)).re) := by
    apply Complex.ext <;> simp [hZim0.symm]
  have hsummlog := summable_log_bfun hσ
  have hprodC : (∏' p : Nat.Primes, ((bfun σ p : ℝ) : ℂ)) = (riemannZeta (σ:ℂ))⁻¹ := by
    rw [tprod_congr (fun p => (bfun_eq_cpow (σ := σ) p).symm)]
    exact tprod_one_sub_eq_inv_zeta hσ
  have hexpC : (∏' p : Nat.Primes, ((bfun σ p : ℝ) : ℂ))
      = ↑(Real.exp (∑' p : Nat.Primes, Real.log (bfun σ p))) := by
    have hpt : ∀ p : Nat.Primes, ((bfun σ p : ℝ) : ℂ)
        = Complex.exp (((Real.log (bfun σ p) : ℝ)) : ℂ) := by
      intro p
      rw [← Complex.ofReal_exp, Real.exp_log (bfun_pos hσ p)]
    rw [tprod_congr hpt]
    have hsummC : Summable (fun p : Nat.Primes => (((Real.log (bfun σ p) : ℝ)) : ℂ)) :=
      Complex.summable_ofReal.mpr hsummlog
    have hh := (hsummC.hasSum.cexp).tprod_eq
    simp only [Function.comp_apply] at hh
    rw [hh, ← Complex.ofReal_tsum, Complex.ofReal_exp]
  have h1 : Real.exp (∑' p : Nat.Primes, Real.log (bfun σ p)) = ((riemannZeta (σ:ℂ)).re)⁻¹ := by
    have h := (hexpC.symm.trans hprodC)
    rw [hZeq] at h
    exact_mod_cast h
  have h2 : Real.log (Real.exp (∑' p : Nat.Primes, Real.log (bfun σ p)))
      = Real.log (((riemannZeta (σ:ℂ)).re)⁻¹) := by rw [h1]
  rwa [Real.log_exp, Real.log_inv] at h2

/-- `‖log (1 - z)‖ ≤ -log (1 - ‖z‖)` for `‖z‖ < 1`. -/
private lemma norm_log_one_sub_le_neg_log {z : ℂ} (hz : ‖z‖ < 1) :
    ‖Complex.log (1 - z)‖ ≤ -Real.log (1 - ‖z‖) := by
  have hz0 : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
  have hlog : Complex.log (1 + -z) = Complex.log (1 - z) := by ring_nf
  have hT : HasSum (fun n : ℕ => (-1:ℂ)^(n+1) * (-z)^n / ((n:ℕ):ℂ)) (Complex.log (1 - z)) := by
    have h := Complex.hasSum_taylorSeries_log (z := -z) (by simpa using hz)
    rwa [hlog] at h
  have hterm : ∀ n : ℕ, ‖(-1:ℂ)^(n+1) * (-z)^n / ((n:ℕ):ℂ)‖ = ‖z‖^n/((n:ℕ):ℝ) := by
    intro n
    rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, norm_natCast]
    simp
  have hgeo : Summable (fun n : ℕ => ‖z‖^n) := summable_geometric_of_lt_one hz0 hz
  have hmaj : Summable (fun n : ℕ => ‖z‖^n/((n:ℕ):ℝ)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgeo
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · rw [div_le_iff₀ (by exact_mod_cast h)]
      have h1 : (1:ℝ) ≤ ((n:ℕ):ℝ) := by exact_mod_cast h
      nlinarith [pow_nonneg hz0 n]
  have hnormsumm : Summable (fun n : ℕ => ‖(-1:ℂ)^(n+1) * (-z)^n / ((n:ℕ):ℂ)‖) := by
    rw [show (fun n : ℕ => ‖(-1:ℂ)^(n+1) * (-z)^n / ((n:ℕ):ℂ)‖) = fun n => ‖z‖^n/((n:ℕ):ℝ)
      from funext hterm]
    exact hmaj
  have hval : (∑' n : ℕ, ‖z‖^n/((n:ℕ):ℝ)) = -Real.log (1 - ‖z‖) := by
    have hb : HasSum (fun n : ℕ => ‖z‖^(n+1)/((n:ℝ) + 1)) (-Real.log (1 - ‖z‖)) :=
      Real.hasSum_pow_div_log_of_abs_lt_one (by rwa [abs_of_nonneg hz0])
    rw [hmaj.tsum_eq_zero_add]
    simp only [pow_zero, Nat.cast_zero, div_zero, zero_add]
    simpa only [Nat.cast_add, Nat.cast_one] using hb.tsum_eq
  calc ‖Complex.log (1 - z)‖
      = ‖∑' n : ℕ, (-1:ℂ)^(n+1) * (-z)^n / ((n:ℕ):ℂ)‖ := by rw [hT.tsum_eq]
    _ ≤ ∑' n : ℕ, ‖z‖^n/((n:ℕ):ℝ) := (norm_tsum_le_tsum_norm hnormsumm).trans (le_of_eq
          (tsum_congr (fun n => hterm n)))
    _ = -Real.log (1 - ‖z‖) := hval

/-- Sharp bound: `|Im ∑_p log (1 - p^{-s})| ≤ log ζ(σ)` for `1 < re s`. -/
lemma norm_im_tsum_log_one_sub_le_log_zeta {s : ℂ} (hs : 1 < s.re) :
    ‖(∑' p : Nat.Primes, Complex.log (1 - ((p:ℕ):ℂ)^(-s))).im‖
      ≤ Real.log ((riemannZeta ((s.re:ℝ):ℂ)).re) := by
  have hbd : ∀ p : Nat.Primes,
      ‖Complex.log (1 - ((p:ℕ):ℂ) ^ (-s))‖ ≤ -Real.log (bfun s.re p) := by
    intro p
    have hp : ‖((p:ℕ):ℂ) ^ (-s)‖ = (((p:ℕ):ℝ)) ^ (-s.re) :=
      Complex.norm_natCast_cpow_of_pos p.prop.pos (-s)
    have hlt : ‖((p:ℕ):ℂ) ^ (-s)‖ < 1 := by
      rw [hp]; exact lt_of_le_of_lt (prime_rpow_neg_le_half hs p) (by norm_num)
    simpa only [bfun, hp] using norm_log_one_sub_le_neg_log hlt
  have hmaj : Summable (fun p : Nat.Primes => -Real.log (bfun s.re p)) :=
    (summable_log_bfun hs).neg
  have hsumm : Summable (fun p : Nat.Primes => Complex.log (1 - ((p:ℕ):ℂ) ^ (-s))) :=
    Summable.of_norm_bounded hmaj hbd
  have himn : Summable (fun p : Nat.Primes => ‖(Complex.log (1 - ((p:ℕ):ℂ) ^ (-s))).im‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _)
      (fun p => (Complex.abs_im_le_norm _).trans (hbd p)) hmaj
  calc ‖(∑' p : Nat.Primes, Complex.log (1 - ((p:ℕ):ℂ) ^ (-s))).im‖
      = ‖∑' p : Nat.Primes, (Complex.log (1 - ((p:ℕ):ℂ) ^ (-s))).im‖ := by
        rw [Complex.im_tsum hsumm]
    _ ≤ ∑' p : Nat.Primes, ‖(Complex.log (1 - ((p:ℕ):ℂ) ^ (-s))).im‖ :=
        norm_tsum_le_tsum_norm himn
    _ ≤ ∑' p : Nat.Primes, -Real.log (bfun s.re p) :=
        Summable.tsum_le_tsum (fun p => (Complex.abs_im_le_norm _).trans (hbd p)) himn hmaj
    _ = Real.log ((riemannZeta ((s.re:ℝ):ℂ)).re) := by
        rw [tsum_neg, tsum_log_bfun_eq hs, neg_neg]

/-- Case 1 of the argument bound: if `s.re - 1 ≥ 1/(3+‖s‖)` then the prime-side
imaginary part is at most `log ((4+‖s‖) * ((1+C)(log (2+‖s‖)+1)))`. -/
lemma norm_im_tsum_log_one_sub_le_case1 {s : ℂ} (hs : 1 < s.re) {C : ℝ} (hC : 0 < C)
    (hCz : ∀ z : ℂ, 1 ≤ z.re → ‖riemannZeta z‖ ≤ ‖z - 1‖⁻¹ + C * (Real.log (2 + ‖z‖) + 1))
    (hδ : 1 / (3 + ‖s‖) ≤ s.re - 1) :
    ‖(∑' p : Nat.Primes, Complex.log (1 - ((p:ℕ):ℂ) ^ (-s))).im‖
      ≤ Real.log ((4 + ‖s‖) * ((1 + C) * (Real.log (2 + ‖s‖) + 1))) := by
  have h1 := norm_im_tsum_log_one_sub_le_log_zeta hs
  obtain ⟨hzre, hzim⟩ := Complex.pos_iff.mp (riemannZeta_pos_of_one_lt hs)
  have hnormeq : ‖riemannZeta ((s.re:ℝ):ℂ)‖ = (riemannZeta ((s.re:ℝ):ℂ)).re := by
    have h2 : ‖riemannZeta ((s.re:ℝ):ℂ)‖^2 = ((riemannZeta ((s.re:ℝ):ℂ)).re)^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [hzim]
    have hnn := norm_nonneg (riemannZeta ((s.re:ℝ):ℂ))
    nlinarith [h2, hnn, hzre]
  have hsre : (1:ℝ) ≤ s.re := le_of_lt hs
  have hgap : (0:ℝ) < s.re - 1 := by
    have h3 : (0:ℝ) < 3 + ‖s‖ := by positivity
    have := one_div_pos.mpr h3
    linarith
  have h2 : (riemannZeta ((s.re:ℝ):ℂ)).re ≤ (3 + ‖s‖) + C * (Real.log (2 + ‖s‖) + 1) := by
    have h := hCz ((s.re:ℝ):ℂ) (by simpa using hsre)
    rw [hnormeq] at h
    have hinv : ‖((s.re:ℝ):ℂ) - 1‖⁻¹ ≤ 3 + ‖s‖ := by
      have heq : ((s.re:ℝ):ℂ) - 1 = (((s.re - 1 : ℝ)):ℂ) := by push_cast; ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hgap, inv_le_comm₀ hgap (by positivity)]
      simpa [one_div] using hδ
    have hlog : Real.log (2 + ‖((s.re:ℝ):ℂ)‖) ≤ Real.log (2 + ‖s‖) := by
      apply Real.log_le_log (by positivity)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ s.re)]
      have := Complex.re_le_norm s
      linarith
    have hlog' : C * Real.log (2 + ‖((s.re:ℝ):ℂ)‖) ≤ C * Real.log (2 + ‖s‖) :=
      mul_le_mul_of_nonneg_left hlog hC.le
    linarith [h, hinv, hlog']
  refine h1.trans (Real.log_le_log hzre ?_)
  have hL : (1:ℝ) ≤ Real.log (2 + ‖s‖) + 1 := by
    have : (0:ℝ) ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by have := norm_nonneg s; linarith)
    linarith
  have h4 : (1:ℝ) ≤ 4 + ‖s‖ := by have := norm_nonneg s; linarith
  have hCn : (0:ℝ) ≤ C := hC.le
  have hL0 : (0:ℝ) ≤ Real.log (2 + ‖s‖) + 1 := by linarith
  nlinarith [h2, h4, hL, hCn, hL0, mul_nonneg hCn hL0]

section Zeta1LogDerivBound

/-- The log-derivative of `ζ₁` is bounded by `C (1 + log (2+‖s‖))⁴` on `1 ≤ re s`. -/
theorem zeta1_logDeriv_halfplane_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 ≤ s.re →
      ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ ≤ C * (1 + Real.log (2 + ‖s‖)) ^ 4 := by
  obtain ⟨M, hMpos, hM⟩ := Commons.NumberTheory.Zeta.logDeriv_zeta_const_bound
  obtain ⟨c, C₂, hc, hC₂pos, hzf, hC₂⟩ :=
    Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_logDeriv_bound
  have hK : IsCompact (Complex.reProdIm (Set.Icc (1:ℝ) (3/2)) (Set.Icc (-1:ℝ) 1)) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn (fun z => logDeriv riemannZeta₁ z)
      (Complex.reProdIm (Set.Icc (1:ℝ) (3/2)) (Set.Icc (-1:ℝ) 1)) := by
    intro z hz
    obtain ⟨hzre, _⟩ := Complex.mem_reProdIm.mp hz
    exact ((Commons.NumberTheory.Zeta.logDeriv_zeta1_analyticAt
      (Commons.NumberTheory.Zeta.zeta1_ne_zero_of_one_le_re hzre.1)).continuousAt).continuousWithinAt
  obtain ⟨C₃, hC₃⟩ := hK.exists_bound_of_continuousOn hcont
  have hMnn : (0:ℝ) ≤ M := hMpos.le
  have hC₂nn : (0:ℝ) ≤ C₂ := hC₂pos.le
  refine ⟨M + 2 + 81 * C₂ + max C₃ 0 + 1,
    by have := le_max_right C₃ 0; linarith, fun s hs => ?_⟩
  change ‖logDeriv riemannZeta₁ s‖ ≤ (M + 2 + 81 * C₂ + max C₃ 0 + 1) * (1 + Real.log (2 + ‖s‖)) ^ 4
  have hL0 : (0:ℝ) ≤ Real.log (2 + ‖s‖) :=
    Real.log_nonneg (by have h := norm_nonneg s; linarith)
  have h1pow : (1:ℝ) ≤ (1 + Real.log (2 + ‖s‖)) ^ 4 :=
    one_le_pow₀ (by linarith)
  have hk : (0:ℝ) ≤ M + 2 + 81 * C₂ + max C₃ 0 + 1 := by
    have := le_max_right C₃ 0; linarith
  by_cases h32 : (3:ℝ)/2 ≤ s.re
  · -- case 1: 3/2 ≤ re s
    have hne1 : s ≠ 1 := by
      intro h; rw [h] at h32; simp only [Complex.one_re] at h32; norm_num at h32
    have hlogeq : logDeriv riemannZeta₁ s
        = deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹ :=
      Commons.NumberTheory.Zeta.logDeriv_zeta1_eq hne1
        (Commons.NumberTheory.Zeta.zeta1_ne_zero_of_one_le_re (s := s) (by linarith))
    rw [hlogeq]
    have h1 : ‖deriv riemannZeta s / riemannZeta s‖ ≤ M := hM s h32
    have h2 : ‖(s - 1)⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      have hpos : (0:ℝ) < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne1)
      have hge : (1:ℝ)/2 ≤ ‖s - 1‖ := by
        have h := Complex.re_le_norm (s - 1)
        simp only [Complex.sub_re, Complex.one_re] at h
        linarith
      calc ‖s - 1‖⁻¹ ≤ ((1:ℝ)/2)⁻¹ := (inv_le_inv₀ hpos (by norm_num)).mpr hge
        _ = 2 := by norm_num
    calc ‖deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹‖
        ≤ ‖deriv riemannZeta s / riemannZeta s‖ + ‖(s - 1)⁻¹‖ := norm_add_le _ _
      _ ≤ M + 2 := by linarith [h1, h2]
      _ ≤ (M + 2 + 81 * C₂ + max C₃ 0 + 1) * (1 + Real.log (2 + ‖s‖)) ^ 4 := by
          have hmax : (0:ℝ) ≤ max C₃ 0 := le_max_right C₃ 0
          have hle : M + 2 ≤ M + 2 + 81 * C₂ + max C₃ 0 + 1 := by linarith [hC₂nn, hmax]
          have h2 := mul_le_mul_of_nonneg_left h1pow hk
          rw [mul_one] at h2
          exact hle.trans h2
  · by_cases him : (1:ℝ) ≤ |s.im|
    · -- case 2: 1 ≤ |im s|
      have hne1 : s ≠ 1 := by
        intro h; rw [h] at him; simp only [Complex.one_im] at him; norm_num at him
      have hlogeq : logDeriv riemannZeta₁ s
          = deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹ :=
        Commons.NumberTheory.Zeta.logDeriv_zeta1_eq hne1
          (Commons.NumberTheory.Zeta.zeta1_ne_zero_of_one_le_re (s := s) (by linarith))
      rw [hlogeq]
      have hseq : s = ((s.re:ℝ):ℂ) + Complex.I * ((s.im:ℝ):ℂ) := by
        apply Complex.ext <;> simp
      have hzfre : 1 - c / Real.log (|s.im| + 3) ≤ s.re := by
        have hlog : (0:ℝ) ≤ Real.log (|s.im| + 3) :=
          Real.log_nonneg (by have ha := abs_nonneg s.im; linarith)
        have hcl : (0:ℝ) ≤ c / Real.log (|s.im| + 3) := div_nonneg hc.le hlog
        linarith
      have h32' : s.re ≤ 2 := by have h := not_le.mp h32; linarith
      have h1 : ‖deriv riemannZeta s / riemannZeta s‖
          ≤ C₂ * (Real.log (|s.im| + 3) + 1) ^ 4 := by
        have h := hC₂ s.im him s.re hzfre h32'
        rwa [← hseq] at h
      have h2 : ‖(s - 1)⁻¹‖ ≤ 1 := by
        rw [norm_inv, inv_le_one₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hne1))]
        have h := Complex.abs_im_le_norm (s - 1)
        simp only [Complex.sub_im, Complex.one_im, sub_zero] at h
        linarith
      have h3 : C₂ * (Real.log (|s.im| + 3) + 1) ^ 4
          ≤ C₂ * (81 * (1 + Real.log (2 + ‖s‖)) ^ 4) := by
        refine mul_le_mul_of_nonneg_left ?_ hC₂nn
        have h4 : Real.log (|s.im| + 3) ≤ 2 * (1 + Real.log (2 + ‖s‖)) := by
          have h5 : |s.im| + 3 ≤ 3 * (1 + ‖s‖) := by
            have := Complex.abs_im_le_norm s; linarith [norm_nonneg s]
          have h6 : Real.log (|s.im| + 3) ≤ Real.log (3 * (1 + ‖s‖)) :=
            Real.log_le_log (by positivity) h5
          rw [Real.log_mul (by norm_num) (by positivity)] at h6
          have h7 : Real.log 3 ≤ 2 := by
            have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3); linarith
          have h8 : Real.log (1 + ‖s‖) ≤ Real.log (2 + ‖s‖) :=
            Real.log_le_log (by positivity) (by linarith)
          linarith
        have h9 : (0:ℝ) ≤ Real.log (|s.im| + 3) + 1 := by
          have ha : (1:ℝ) ≤ |s.im| + 3 := by have := abs_nonneg s.im; linarith
          have : (0:ℝ) ≤ Real.log (|s.im| + 3) := Real.log_nonneg ha
          linarith
        calc (Real.log (|s.im| + 3) + 1) ^ 4
            ≤ (3 * (1 + Real.log (2 + ‖s‖))) ^ 4 := pow_le_pow_left₀ h9 (by linarith) 4
          _ = 81 * (1 + Real.log (2 + ‖s‖)) ^ 4 := by ring
      have hsum := norm_add_le (deriv riemannZeta s / riemannZeta s) ((s - 1)⁻¹)
      calc ‖deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹‖
          ≤ ‖deriv riemannZeta s / riemannZeta s‖ + ‖(s - 1)⁻¹‖ := hsum
        _ ≤ C₂ * (Real.log (|s.im| + 3) + 1) ^ 4 + 1 := by linarith [h1, h2]
        _ ≤ 81 * C₂ * (1 + Real.log (2 + ‖s‖)) ^ 4 + 1 := by linarith [h3]
        _ ≤ (M + 2 + 81 * C₂ + max C₃ 0 + 1) * (1 + Real.log (2 + ‖s‖)) ^ 4 := by
            have hmax : (0:ℝ) ≤ max C₃ 0 := le_max_right C₃ 0
            have hCL : (0:ℝ) ≤ 81 * C₂ * (1 + Real.log (2 + ‖s‖)) ^ 4 := by positivity
            nlinarith [h1pow, hCL, hMnn, hC₂nn, hmax]
    · -- case 3: re s ≤ 3/2 and |im s| ≤ 1
      have himabs : |s.im| ≤ 1 := le_of_lt (not_le.mp him)
      have hmem : s ∈ Complex.reProdIm (Set.Icc (1:ℝ) (3/2)) (Set.Icc (-1:ℝ) 1) := by
        rw [Complex.mem_reProdIm]
        obtain ⟨hlo, hhi⟩ := abs_le.mp himabs
        exact ⟨⟨hs, le_of_lt (not_le.mp h32)⟩, ⟨hlo, hhi⟩⟩
      have h1 : ‖logDeriv riemannZeta₁ s‖ ≤ max C₃ 0 :=
        (hC₃ s hmem).trans (le_max_left _ _)
      have hCK : max C₃ 0 ≤ M + 2 + 81 * C₂ + max C₃ 0 + 1 := by
        have := le_max_right C₃ 0; linarith [hC₂nn, hMnn]
      have h2 := mul_le_mul_of_nonneg_left h1pow hk
      rw [mul_one] at h2
      exact h1.trans (hCK.trans h2)

section LwPrimeLog

/-- The prime log-series `Lw s = ∑_p log (1 - p^{-s})`. -/
noncomputable def Lw (s : ℂ) : ℂ := ∑' p : Nat.Primes, Complex.log (1 - ((p:ℕ):ℂ) ^ (-s))

private lemma prime_rpow_neg_lt_one {p : Nat.Primes} {σ : ℝ} (hσ : 0 < σ) :
    (((p:ℕ):ℝ)) ^ (-σ) < 1 := by
  have hp1 : (1:ℝ) < ((p:ℕ):ℝ) := by exact_mod_cast p.prop.one_lt
  rw [Real.rpow_neg (by linarith)]
  exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by linarith) hσ)

private lemma neg_log_one_sub_mono {a b : ℝ} (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    -Real.log (1 - a) ≤ -Real.log (1 - b) := by
  have h1 : 0 < 1 - b := by linarith
  have h2 : 1 - b ≤ 1 - a := by linarith
  have := Real.log_le_log h1 h2
  linarith

private lemma norm_natCast_cpow_neg_lt_one {p : Nat.Primes} {s : ℂ} (h : 0 < s.re) :
    ‖((p:ℕ):ℂ) ^ (-s)‖ < 1 := by
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos (-s), Complex.neg_re]
  exact prime_rpow_neg_lt_one h

private lemma summable_neg_log_one_sub {c : ℝ} (hc : 1 < c) :
    Summable (fun p : Nat.Primes => -Real.log (1 - (((p:ℕ):ℝ)) ^ (-c))) := by
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
    ((summable_primes_rpow_neg hc).mul_left 2)
  · have hx1 : (((p:ℕ):ℝ)) ^ (-c) < 1 := prime_rpow_neg_lt_one (by linarith)
    have hx2 : (0:ℝ) < (((p:ℕ):ℝ)) ^ (-c) :=
      Real.rpow_pos_of_pos (show (0:ℝ) < ((p:ℕ):ℝ) by exact_mod_cast p.prop.pos) (-c)
    exact neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))
  · have hx0 : (0:ℝ) < (((p:ℕ):ℝ)) ^ (-c) :=
      Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) (-c)
    have hx1 : (((p:ℕ):ℝ)) ^ (-c) ≤ 1/2 := prime_rpow_neg_le_half hc p
    have h2 : Real.log (1 - (((p:ℕ):ℝ)) ^ (-c)) ≤ 0 :=
      Real.log_nonpos (by linarith) (by linarith)
    have h3 := abs_log_one_sub_le hx0 hx1
    rw [abs_of_nonpos h2] at h3
    linarith

lemma summable_Lw {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => Complex.log (1 - ((p:ℕ):ℂ) ^ (-s))) :=
  Summable.of_norm_bounded ((summable_primes_rpow_neg hs).mul_left 2)
    (fun p => norm_log_one_sub_natCast_cpow_le hs p)

private lemma differentiableAt_cpow_neg (p : Nat.Primes) (s : ℂ) :
    DifferentiableAt ℂ (fun z : ℂ => ((p:ℕ):ℂ) ^ (-z)) s := by
  have hsp : ((p:ℕ):ℂ) ∈ slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    rw [Complex.natCast_re]
    exact_mod_cast p.prop.pos
  exact ((hasDerivAt_const s (((p:ℕ):ℂ))).cpow ((hasDerivAt_id s).neg) hsp).differentiableAt

private lemma one_sub_cpow_mem_slitPlane {p : Nat.Primes} {s : ℂ} (h : 0 < s.re) :
    (1 - ((p:ℕ):ℂ) ^ (-s)) ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have hlt : ‖((p:ℕ):ℂ) ^ (-s)‖ < 1 := norm_natCast_cpow_neg_lt_one (p := p) h
  have h2 : (((p:ℕ):ℂ) ^ (-s)).re ≤ ‖((p:ℕ):ℂ) ^ (-s)‖ := Complex.re_le_norm _
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- `Lw` is differentiable on every half-plane `{c < re z}` with `c > 1`. -/
lemma differentiableOn_Lw {c : ℝ} (hc : 1 < c) :
    DifferentiableOn ℂ Lw {s : ℂ | c < s.re} := by
  have hU : IsOpen {s : ℂ | c < s.re} := isOpen_lt continuous_const continuous_re
  refine differentiableOn_tsum_of_summable_norm
    (u := fun p : Nat.Primes => -Real.log (1 - (((p:ℕ):ℝ)) ^ (-c)))
    (summable_neg_log_one_sub hc) (fun p => ?_) hU (fun p s hs => ?_)
  · refine DifferentiableOn.clog ?_ ?_
    · exact (differentiableOn_const (c := (1:ℂ))).sub
        (fun s _ => (differentiableAt_cpow_neg p s).differentiableWithinAt)
    · intro s hs
      have hcs : c < s.re := hs
      exact one_sub_cpow_mem_slitPlane (by linarith)
  · have hcs : c < s.re := hs
    have hlt : 0 < s.re := by linarith
    have hnlt : ‖((p:ℕ):ℂ) ^ (-s)‖ < 1 := norm_natCast_cpow_neg_lt_one (p := p) hlt
    have h1 : ‖Complex.log (1 - ((p:ℕ):ℂ) ^ (-s))‖
        ≤ -Real.log (1 - ‖((p:ℕ):ℂ) ^ (-s)‖) := norm_log_one_sub_le_neg_log hnlt
    rw [Complex.norm_natCast_cpow_of_pos p.prop.pos (-s), Complex.neg_re] at h1
    exact h1.trans (neg_log_one_sub_mono
      (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) (-s.re))
      (prime_rpow_neg_lt_one (by linarith))
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.prop.one_le) (by linarith)))

lemma differentiableAt_Lw {s : ℂ} (hs : 1 < s.re) : DifferentiableAt ℂ Lw s := by
  have h2 : 1 < (1 + s.re)/2 := by linarith
  have hmem : s ∈ {z : ℂ | (1 + s.re)/2 < z.re} := by
    simp only [Set.mem_setOf_eq]; linarith
  exact (differentiableOn_Lw h2).differentiableAt
    ((isOpen_lt continuous_const continuous_re).mem_nhds hmem)

private lemma one_sub_cpow_arg_ne_pi {p : Nat.Primes} {s : ℂ} (h : 0 < s.re) :
    (1 - ((p:ℕ):ℂ) ^ (-s)).arg ≠ Real.pi := by
  intro hpi
  obtain ⟨hre, him⟩ := Complex.arg_eq_pi_iff.mp hpi
  have hsp := one_sub_cpow_mem_slitPlane (p := p) h
  rw [Complex.mem_slitPlane_iff] at hsp
  rcases hsp with hsp | hsp
  · linarith
  · exact hsp him

lemma cexp_Lw {s : ℂ} (hs : 1 < s.re) : Complex.exp (Lw s) = (riemannZeta s)⁻¹ := by
  have hlt0 : (0:ℝ) < s.re := lt_trans one_pos hs
  have hne : ∀ p : Nat.Primes, (1 - ((p:ℕ):ℂ) ^ (-s)) ≠ 0 := by
    intro p h
    have hlt := norm_natCast_cpow_neg_lt_one (p := p) hlt0
    have hx : ((p:ℕ):ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
    have h1 : ‖((p:ℕ):ℂ) ^ (-s)‖ = 1 := by simp [hx]
    linarith
  have hsp : ∀ p : Nat.Primes, (1 - ((p:ℕ):ℂ) ^ (-s)).arg ≠ Real.pi :=
    fun p => one_sub_cpow_arg_ne_pi (p := p) hlt0
  have hsum : Summable (fun p : Nat.Primes => Complex.log ((1 - ((p:ℕ):ℂ) ^ (-s))⁻¹)) :=
    (summable_Lw hs).neg.congr (fun p => (Complex.log_inv _ (hsp p)).symm)
  have h1 : Complex.exp (∑' p : Nat.Primes, Complex.log ((1 - ((p:ℕ):ℂ) ^ (-s))⁻¹))
      = ∏' p : Nat.Primes, ((1 - ((p:ℕ):ℂ) ^ (-s))⁻¹) :=
    Complex.cexp_tsum_eq_tprod (f := fun p : Nat.Primes => ((1 - ((p:ℕ):ℂ) ^ (-s))⁻¹))
      (fun p => inv_ne_zero (hne p)) hsum
  have hneg : (∑' p : Nat.Primes, -Complex.log (1 - ((p:ℕ):ℂ) ^ (-s)))
      = -(∑' p : Nat.Primes, Complex.log (1 - ((p:ℕ):ℂ) ^ (-s))) :=
    tsum_neg (f := fun p : Nat.Primes => Complex.log (1 - ((p:ℕ):ℂ) ^ (-s)))
  have hLw : Lw s = ∑' p : Nat.Primes, Complex.log (1 - ((p:ℕ):ℂ) ^ (-s)) := rfl
  have htsum : (∑' p : Nat.Primes, Complex.log ((1 - ((p:ℕ):ℂ) ^ (-s))⁻¹)) = -Lw s := by
    rw [hLw, ← hneg]
    exact tsum_congr (fun p => Complex.log_inv _ (hsp p))
  rw [htsum] at h1
  have h2 : Complex.exp (-Lw s) = riemannZeta s := by
    rw [h1]; exact riemannZeta_eulerProduct_tprod hs
  have h3 : (riemannZeta s) * Complex.exp (Lw s) = 1 := by
    rw [← h2, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  exact (inv_eq_of_mul_eq_one_right h3).symm

lemma deriv_Lw {s : ℂ} (hs : 1 < s.re) :
    deriv Lw s = -(deriv riemannZeta s) / riemannZeta s := by
  have hne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hs; simp at hs
  have hev : (fun z : ℂ => Complex.exp (Lw z)) =ᶠ[𝓝 s] (fun z : ℂ => (riemannZeta z)⁻¹) := by
    refine Filter.eventually_of_mem ?_ (fun z hz => cexp_Lw hz)
    exact (isOpen_lt continuous_const continuous_re).mem_nhds hs
  have h1 : deriv (fun z : ℂ => Complex.exp (Lw z)) s
      = deriv (fun z : ℂ => (riemannZeta z)⁻¹) s := hev.deriv_eq
  have hL : deriv (fun z : ℂ => Complex.exp (Lw z)) s
      = Complex.exp (Lw s) * deriv Lw s := by
    change deriv (Complex.exp ∘ Lw) s = Complex.exp (Lw s) * deriv Lw s
    have h := deriv_comp (x := s) (h := Lw) (h₂ := Complex.exp)
      (differentiableAt_exp (x := Lw s)) (differentiableAt_Lw hs)
    simp only [Complex.deriv_exp] at h
    exact h
  have hR : deriv (fun z : ℂ => (riemannZeta z)⁻¹) s
      = -(riemannZeta s ^ 2)⁻¹ * deriv riemannZeta s := by
    change deriv ((fun z : ℂ => z⁻¹) ∘ riemannZeta) s
      = -(riemannZeta s ^ 2)⁻¹ * deriv riemannZeta s
    have h := deriv_comp (x := s) (h := riemannZeta) (h₂ := fun z : ℂ => z⁻¹)
      (differentiableAt_inv hne) (differentiableAt_riemannZeta hs1)
    rw [deriv_inv] at h
    simpa [neg_mul] using h
  rw [hL, hR, cexp_Lw hs] at h1
  have hkey : deriv Lw s * riemannZeta s = -deriv riemannZeta s := by
    have hh := congrArg (fun t => t * riemannZeta s ^ 2) h1
    have hA : (riemannZeta s)⁻¹ * deriv Lw s * riemannZeta s ^ 2 = deriv Lw s * riemannZeta s := by
      field_simp
    have hB : (-(riemannZeta s ^ 2)⁻¹ * deriv riemannZeta s) * riemannZeta s ^ 2
        = -deriv riemannZeta s := by
      field_simp
    rw [hA, hB] at hh
    exact hh
  rw [eq_div_iff hne, hkey]


lemma deriv_Lw_sub_log {s : ℂ} (hs : 1 < s.re) :
    deriv (fun z : ℂ => Lw z - Complex.log (z - 1)) s
      = -(deriv riemannZeta₁ s / riemannZeta₁ s) := by
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hs; simp at hs
  have hsp : (s - 1) ∈ slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hlog : deriv (fun z : ℂ => Complex.log (z - 1)) s = (s - 1)⁻¹ := by
    have h := (hasDerivAt_id s).sub_const (1:ℂ)
    have h3 := h.clog hsp
    have h4 := h3.deriv
    simpa using h4
  have h1 : deriv (fun z : ℂ => Lw z - Complex.log (z - 1)) s
      = deriv Lw s - deriv (fun z : ℂ => Complex.log (z - 1)) s :=
    deriv_sub (differentiableAt_Lw hs) ((differentiableAt_id.sub_const 1).clog hsp)
  have hz1 : riemannZeta₁ s ≠ 0 :=
    Commons.NumberTheory.Zeta.zeta1_ne_zero_of_one_le_re (by linarith : (1:ℝ) ≤ s.re)
  have hld := Commons.NumberTheory.Zeta.logDeriv_zeta1_eq (s := s) hs1 hz1
  have hld' : deriv riemannZeta₁ s / riemannZeta₁ s
      = deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹ := hld
  rw [h1, hlog, deriv_Lw hs, hld']
  ring

private lemma segment_norm_sub_le {s s' z : ℂ} (hz : z ∈ segment ℝ s s') :
    ‖z - s‖ ≤ ‖s' - s‖ := by
  rw [segment_eq_image] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have h1 : (1 - t) • s + t • s' - s = t • (s' - s) := by module
  rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact mul_le_of_le_one_left (norm_nonneg _) ht.2

private lemma segment_re_ge {s s' z : ℂ} (hz : z ∈ segment ℝ s s') (h : s.re ≤ s'.re) :
    s.re ≤ z.re := by
  rw [segment_eq_image] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have h1 : ((1 - t) • s + t • s').re = (1 - t) * s.re + t * s'.re := by
    simp [Complex.add_re, Complex.smul_re]
  rw [h1]
  have h0 : (0:ℝ) ≤ t := ht.1
  have h2 : (0:ℝ) ≤ 1 - t := by linarith [ht.2]
  nlinarith [h, h0, h2]

private lemma one_add_log_four_le {y : ℝ} (hy : 1 ≤ y) :
    (1 + Real.log y)^4 ≤ 1296 * y := by
  have hy0 : (0:ℝ) < y := by linarith
  have h4 : (1:ℝ) ≤ y ^ (1/4:ℝ) := Real.one_le_rpow hy (by norm_num)
  have hlog : Real.log y = 4 * Real.log (y ^ (1/4:ℝ)) := by
    rw [Real.log_rpow hy0]; ring
  have hlog2 : Real.log (y ^ (1/4:ℝ)) ≤ y ^ (1/4:ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hy0 _)
  have hb : 1 + Real.log y ≤ 6 * y ^ (1/4:ℝ) := by
    rw [hlog]; nlinarith
  have hb0 : (0:ℝ) ≤ 1 + Real.log y := by
    have := Real.log_nonneg hy; linarith
  calc (1 + Real.log y)^4 ≤ (6 * y ^ (1/4:ℝ))^4 := by
        exact pow_le_pow_left₀ hb0 hb 4
    _ = 1296 * y := by
        rw [mul_pow]
        have h1 : (y ^ (1/4:ℝ)) ^ (4:ℕ) = y ^ ((1/4:ℝ) * (4:ℝ)) := by
          rw [← Real.rpow_natCast]
          exact (Real.rpow_mul hy0.le (1/4) 4).symm
        rw [h1, show ((1:ℝ)/4) * 4 = 1 by norm_num, Real.rpow_one]
        norm_num

private lemma im_Lw_shift_le {Cld : ℝ} (hCldpos : 0 < Cld)
    (hCld : ∀ z : ℂ, 1 ≤ z.re →
      ‖deriv riemannZeta₁ z / riemannZeta₁ z‖ ≤ Cld * (1 + Real.log (2 + ‖z‖))^4)
    {s : ℂ} (hs : 1 < s.re) :
    ‖(Lw ((((s.re + 1/(3+‖s‖)) : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I)).im - (Lw s).im‖
      ≤ 1296 * Cld + 2 * Real.pi := by
  set σ₀ : ℝ := s.re + 1/(3+‖s‖) with hσ₀
  set s' : ℂ := ((σ₀ : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I with hs'def
  have hpos : (0:ℝ) < 3 + ‖s‖ := by have := norm_nonneg s; linarith
  have hσpos : (0:ℝ) < 1/(3+‖s‖) := by positivity
  have hsre : s.re ≤ σ₀ := by rw [hσ₀]; linarith
  have hss : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hs're : s'.re = σ₀ := by rw [hs'def]; simp
  have hsre' : s.re ≤ s'.re := by rw [hs're]; exact hsre
  have hsdiff : s' - s = (((σ₀ - s.re : ℝ)) : ℂ) := by
    have hre : (s' - s).re = σ₀ - s.re := by rw [Complex.sub_re, hs're]
    have him : (s' - s).im = 0 := by
      rw [Complex.sub_im, hs'def]
      simp
    apply Complex.ext
    · rw [hre]; simp
    · rw [him]; simp
  have hnorm_sdiff : ‖s' - s‖ = σ₀ - s.re := by
    rw [hsdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    linarith
  have hbound : ‖s' - s‖ = 1/(3+‖s‖) := by rw [hnorm_sdiff, hσ₀]; ring
  -- MVT
  have hMVT : ‖(Lw s' - Complex.log (s' - 1)) - (Lw s - Complex.log (s - 1))‖
      ≤ (Cld * (1 + Real.log (3 + ‖s‖))^4) * (1/(3+‖s‖)) := by
    have h0 : ‖(Lw s' - Complex.log (s' - 1)) - (Lw s - Complex.log (s - 1))‖
        ≤ (Cld * (1 + Real.log (3 + ‖s‖))^4) * ‖s' - s‖ :=
      Convex.norm_image_sub_le_of_norm_deriv_le (f := fun z => Lw z - Complex.log (z - 1))
        (C := Cld * (1 + Real.log (3 + ‖s‖))^4) (s := segment ℝ s s') ?_ ?_
        (convex_segment s s') (left_mem_segment ℝ s s') (right_mem_segment ℝ s s')
    · rw [hbound] at h0
      exact h0
    · intro x hx
      have hxre : 1 < x.re := lt_of_lt_of_le hs (segment_re_ge hx hsre')
      have hxsp : (x - 1) ∈ slitPlane := by
        rw [Complex.mem_slitPlane_iff]; left
        simp only [Complex.sub_re, Complex.one_re]; linarith
      exact (differentiableAt_Lw hxre).sub ((differentiableAt_id.sub_const 1).clog hxsp)
    · intro x hx
      have hxre : 1 < x.re := lt_of_lt_of_le hs (segment_re_ge hx hsre')
      have h1 : deriv (fun z : ℂ => Lw z - Complex.log (z - 1)) x
          = -(deriv riemannZeta₁ x / riemannZeta₁ x) := deriv_Lw_sub_log hxre
      rw [h1, norm_neg]
      refine (hCld x (le_of_lt hxre)).trans ?_
      have hxn : ‖x‖ ≤ ‖s‖ + 1 := by
        have h2 : ‖x - s‖ ≤ 1/(3+‖s‖) := by rw [← hbound]; exact segment_norm_sub_le hx
        have h3 : 1/(3+‖s‖) ≤ 1 := by
          rw [div_le_one hpos]; have := norm_nonneg s; linarith
        have h4 : ‖x‖ ≤ ‖x - s‖ + ‖s‖ := by
          have hh := norm_add_le (x - s) s
          rwa [sub_add_cancel] at hh
        linarith
      have h4 : (0:ℝ) ≤ 1 + Real.log (2 + ‖x‖) := by
        have : (0:ℝ) ≤ Real.log (2 + ‖x‖) := Real.log_nonneg (by linarith [norm_nonneg x])
        linarith
      have h6 : Real.log (2 + ‖x‖) ≤ Real.log (3 + ‖s‖) := by
        apply Real.log_le_log (by linarith [norm_nonneg x])
        linarith
      have h4' : (0:ℝ) ≤ 1 + Real.log (3 + ‖s‖) := by
        have : (0:ℝ) ≤ Real.log (3 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
        linarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h4 (by linarith) 4) hCldpos.le
  have hmvt' : ‖(Lw s' - Complex.log (s' - 1)) - (Lw s - Complex.log (s - 1))‖
      ≤ 1296 * Cld := by
    refine hMVT.trans ?_
    have hy : (1:ℝ) ≤ 3 + ‖s‖ := by have := norm_nonneg s; linarith
    have h6 : (1 + Real.log (3 + ‖s‖))^4 * (1/(3+‖s‖)) ≤ 1296 := by
      rw [mul_one_div, div_le_iff₀ hpos]
      exact (one_add_log_four_le hy).trans (le_of_eq (by ring))
    calc Cld * (1 + Real.log (3 + ‖s‖))^4 * (1/(3+‖s‖))
        = Cld * ((1 + Real.log (3 + ‖s‖))^4 * (1/(3+‖s‖))) := by ring
      _ ≤ Cld * 1296 := mul_le_mul_of_nonneg_left h6 hCldpos.le
      _ = 1296 * Cld := by ring
  -- imaginary parts
  have hd : Lw s' - Lw s = (Lw s' - Complex.log (s' - 1) - (Lw s - Complex.log (s - 1)))
      + (Complex.log (s' - 1) - Complex.log (s - 1)) := by ring
  have him : (Lw s').im - (Lw s).im
      = ((Lw s' - Complex.log (s' - 1) - (Lw s - Complex.log (s - 1)))).im
        + (Complex.log (s' - 1) - Complex.log (s - 1)).im := by
    have h := congrArg Complex.im hd
    simp only [Complex.add_im, Complex.sub_im] at h ⊢
    linarith [h]
  have hlogb : |(Complex.log (s' - 1) - Complex.log (s - 1)).im| ≤ 2 * Real.pi := by
    have h1 : (Complex.log (s' - 1) - Complex.log (s - 1)).im
        = (Complex.log (s' - 1)).im - (Complex.log (s - 1)).im := by simp
    rw [h1]
    have ha : |(Complex.log (s' - 1)).im| ≤ Real.pi := by
      rw [Complex.log_im]
      exact abs_le.mpr ⟨le_of_lt (Complex.neg_pi_lt_arg _), Complex.arg_le_pi _⟩
    have hb : |(Complex.log (s - 1)).im| ≤ Real.pi := by
      rw [Complex.log_im]
      exact abs_le.mpr ⟨le_of_lt (Complex.neg_pi_lt_arg _), Complex.arg_le_pi _⟩
    have h2 := abs_sub ((Complex.log (s' - 1)).im) ((Complex.log (s - 1)).im)
    linarith
  rw [him, Real.norm_eq_abs]
  calc |((Lw s' - Complex.log (s' - 1) - (Lw s - Complex.log (s - 1)))).im
        + (Complex.log (s' - 1) - Complex.log (s - 1)).im|
      ≤ |((Lw s' - Complex.log (s' - 1) - (Lw s - Complex.log (s - 1)))).im|
        + |(Complex.log (s' - 1) - Complex.log (s - 1)).im| := abs_add_le _ _
    _ ≤ 1296 * Cld + 2 * Real.pi :=
        add_le_add ((Complex.abs_im_le_norm _).trans hmvt') hlogb


private lemma log_le_two_sqrt (u : ℝ) (hu : 0 ≤ u) : Real.log u ≤ 2 * Real.sqrt u := by
  by_cases h : u ≤ 1
  · have h2 : Real.log u ≤ 0 := Real.log_nonpos hu h
    have h3 : (0:ℝ) ≤ 2 * Real.sqrt u := by positivity
    linarith
  · have h1 : 1 < u := not_le.mp h
    have h2 : Real.log (Real.sqrt u) ≤ Real.sqrt u - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith))
    have h3 : Real.log u = 2 * Real.log (Real.sqrt u) := by
      rw [Real.log_sqrt hu]; ring
    have h4 : (1:ℝ) ≤ Real.sqrt u := Real.one_le_sqrt.mpr (le_of_lt h1)
    rw [h3]; linarith

private lemma log_le_add_self (u : ℝ) (hu : 0 ≤ u) : Real.log u ≤ 400 + u/10 := by
  by_cases h : u ≤ 400
  · have h1 : Real.log u ≤ Real.log 400 := by
      rcases eq_or_lt_of_le hu with h0 | h0
      · rw [← h0, Real.log_zero]; exact le_trans le_rfl (Real.log_nonneg (by norm_num))
      · exact Real.log_le_log h0 h
    have h2 : Real.log 400 ≤ 400 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 400); linarith
    linarith
  · have h2 : Real.log u ≤ 2 * Real.sqrt u := log_le_two_sqrt u hu
    have h3 : (400:ℝ) ≤ u := le_of_lt (not_le.mp h)
    have h4 : (20:ℝ) ≤ Real.sqrt u := by
      have h20 : Real.sqrt 400 = 20 := by
        rw [show (400:ℝ) = 20^2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [← h20]
      exact Real.sqrt_le_sqrt h3
    have h5 : (0:ℝ) < Real.sqrt u := by linarith
    have h6 : 2 * Real.sqrt u ≤ u/10 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 10)]
      nlinarith [Real.sq_sqrt hu]
    linarith

private lemma log_log_le (y : ℝ) (hy : 2 ≤ y) :
    Real.log (Real.log y + 1) ≤ 401 + (1/10) * Real.log y := by
  have hy0 : (0:ℝ) < y := by linarith
  have hlog2 : (0:ℝ) < Real.log y := Real.log_pos (by linarith)
  have hlog21 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  by_cases h : Real.log y ≤ 1
  · have h1 : Real.log (Real.log y + 1) ≤ Real.log 2 := by
      apply Real.log_le_log (by linarith)
      linarith
    have h2 : (0:ℝ) ≤ (1/10) * Real.log y := by linarith
    linarith
  · have h1 : Real.log (Real.log y + 1) ≤ Real.log (2 * Real.log y) := by
      apply Real.log_le_log (by linarith)
      linarith
    have h2 : Real.log (2 * Real.log y) = Real.log 2 + Real.log (Real.log y) :=
      Real.log_mul (by norm_num) (by linarith)
    have h3 : Real.log (Real.log y) ≤ 400 + (1/10) * Real.log y := by
      have hh := log_le_add_self (Real.log y) hlog2.le
      have hh' : Real.log y / 10 = (1/10) * Real.log y := by ring
      linarith
    linarith

private lemma im_Lw_case1 {C : ℝ} (hC : 0 < C)
    (hCz : ∀ z : ℂ, 1 ≤ z.re → ‖riemannZeta z‖ ≤ ‖z - 1‖⁻¹ + C * (Real.log (2 + ‖z‖) + 1))
    {s : ℂ} (hs : 1 < s.re) (hδ : 1 / (3 + ‖s‖) ≤ s.re - 1) :
    ‖(Lw s).im‖ ≤ Real.log (4 + ‖s‖) + Real.log ((1 + C) * (Real.log (2 + ‖s‖) + 1)) := by
  have h1 := norm_im_tsum_log_one_sub_le_case1 (s := s) hs hC hCz hδ
  have hLw : Lw s = ∑' p : Nat.Primes, Complex.log (1 - ((p:ℕ):ℂ)^(-s)) := rfl
  rw [hLw]
  have ha : (4 + ‖s‖) ≠ 0 := by have := norm_nonneg s; linarith
  have hb : (1 + C) * (Real.log (2 + ‖s‖) + 1) ≠ 0 := by
    have h2 : (0:ℝ) < 1 + C := by linarith
    have h3 : (0:ℝ) < Real.log (2 + ‖s‖) + 1 := by
      have h4 : (1:ℝ) ≤ 2 + ‖s‖ := by have := norm_nonneg s; linarith
      have h5 := Real.log_nonneg h4
      linarith
    positivity
  rw [← Real.log_mul ha hb]
  exact h1

section ValueBound

private lemma norm_one_add_cpow_sub_one_le {z w : ℂ} (hz : ‖z‖ ≤ 1/2) (hw : ‖w‖ ≤ 1/2) :
    ‖(1 + z) ^ w - 1‖ ≤ 4 * ‖w‖ * ‖z‖ := by
  have hz1 : (1 + z) ∈ slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    rw [abs_le] at h1
    simp only [Complex.add_re, Complex.one_re]
    linarith [h1.1, hz]
  have hne : (1 + z) ≠ 0 := slitPlane_ne_zero hz1
  have hlog : ‖Complex.log (1 + z)‖ ≤ (3/2) * ‖z‖ := Complex.norm_log_one_add_half_le_self hz
  have h2 : ‖(1 + z) ^ w - 1‖ = ‖Complex.exp (w * Complex.log (1 + z)) - 1‖ := by
    rw [Complex.cpow_def_of_ne_zero hne, mul_comm]
  rw [h2]
  have h3 : ‖w * Complex.log (1 + z)‖ ≤ 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg w, norm_nonneg (Complex.log (1 + z)), hlog, hz]
  have h4 := norm_cexp_sub_one_le h3
  have h5 : ‖w * Complex.log (1 + z)‖ ≤ ‖w‖ * ((3/2) * ‖z‖) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hlog (norm_nonneg w)
  nlinarith [norm_nonneg w, norm_nonneg z]

private lemma summable_cpow_one_sub {w : ℂ} (hw : ‖w‖ ≤ 1/2) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => ((1:ℂ) - ((p:ℕ):ℂ) ^ (-s))^w - 1) := by
  refine Summable.of_norm_bounded ((summable_primes_rpow_neg hs).mul_left (4 * ‖w‖)) (fun p => ?_)
  have hz : ‖-((p:ℕ):ℂ) ^ (-s)‖ ≤ 1/2 := by
    rw [norm_neg, Complex.norm_natCast_cpow_of_pos p.prop.pos (-s), Complex.neg_re]
    exact prime_rpow_neg_le_half hs p
  have h3 : ((1:ℂ) - ((p:ℕ):ℂ) ^ (-s)) = 1 + (-((p:ℕ):ℂ) ^ (-s)) := by ring
  rw [h3]
  have h4 := norm_one_add_cpow_sub_one_le hz hw
  rw [norm_neg, Complex.norm_natCast_cpow_of_pos p.prop.pos (-s), Complex.neg_re] at h4
  exact h4

private lemma multipliable_cpow_one_sub {w : ℂ} (hw : ‖w‖ ≤ 1/2) {s : ℂ} (hs : 1 < s.re) :
    Multipliable (fun p : Nat.Primes => ((1:ℂ) - ((p:ℕ):ℂ) ^ (-s))^w) :=
  (Complex.multipliable_one_add_of_summable (summable_cpow_one_sub hw hs)).congr (fun p => by ring)

private lemma one_sub_cpow_ne_zero {p : Nat.Primes} {s : ℂ} (hs : 0 < s.re) :
    ((1:ℂ) - ((p:ℕ):ℂ) ^ (-s)) ≠ 0 := by
  intro h
  have hlt := norm_natCast_cpow_neg_lt_one (p := p) hs
  have hx : ((p:ℕ):ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  rw [hx, norm_one] at hlt
  exact lt_irrefl 1 hlt

/-- Multiplicativity of `Hfun` on the half-plane `1 < re s`, in complex form. -/
lemma Hfun_eq_mul {w : ℂ} (hw : ‖w‖ ≤ 1/2) {s : ℂ} (hs : 1 < s.re) :
    Hfun w s = (∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-s))^w))
      * (∏' p : Nat.Primes, (1 + w * ((p:ℕ):ℂ) ^ (-s))) := by
  have h1 : Hfun w s = ∏' p : Nat.Primes,
      (((1:ℂ) - ((p:ℕ):ℂ) ^ (-s))^w * (1 + w * ((p:ℕ):ℂ) ^ (-s))) := by
    rw [Hfun]
    refine tprod_congr (fun p => ?_)
    simp only [omegaLocalHat, omegaLocal]
    ring
  have hsummB : Summable (fun p : Nat.Primes => w * ((p:ℕ):ℂ) ^ (-s)) := by
    refine Summable.of_norm_bounded ((summable_primes_rpow_neg hs).mul_left ‖w‖) (fun p => ?_)
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.prop.pos (-s), Complex.neg_re]
  have hmultB : Multipliable (fun p : Nat.Primes => (1 + w * ((p:ℕ):ℂ) ^ (-s))) :=
    Complex.multipliable_one_add_of_summable hsummB
  rw [h1, Multipliable.tprod_mul (multipliable_cpow_one_sub hw hs) hmultB]

/-- The modulus of `∏_p (1 - p^{-s})^w` is `exp (re (w · Lw s))`. -/
lemma norm_tprod_cpow_eq {w : ℂ} (hw : ‖w‖ ≤ 1/2) {s : ℂ} (hs : 1 < s.re) :
    ‖∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-s))^w)‖ = Real.exp ((w * Lw s).re) := by
  have hs0 : (0:ℝ) < s.re := lt_trans one_pos hs
  rw [Multipliable.norm_tprod (multipliable_cpow_one_sub hw hs)]
  have hsumm : Summable (fun p : Nat.Primes => Real.log ‖((1:ℂ) - ((p:ℕ):ℂ) ^ (-s))^w‖) := by
    refine Summable.of_norm_bounded ((summable_primes_rpow_neg hs).mul_left ((3/2) * ‖w‖))
      (fun p => ?_)
    have hz : ‖-((p:ℕ):ℂ) ^ (-s)‖ ≤ 1/2 := by
      rw [norm_neg, Complex.norm_natCast_cpow_of_pos p.prop.pos (-s), Complex.neg_re]
      exact prime_rpow_neg_le_half hs p
    rw [Complex.cpow_def_of_ne_zero (one_sub_cpow_ne_zero (p := p) hs0), Complex.norm_exp,
      Real.log_exp, Real.norm_eq_abs]
    calc |(Complex.log (1 + (-((p:ℕ):ℂ) ^ (-s))) * w).re|
        ≤ ‖Complex.log (1 + (-((p:ℕ):ℂ) ^ (-s))) * w‖ := Complex.abs_re_le_norm _
      _ = ‖w‖ * ‖Complex.log (1 + (-((p:ℕ):ℂ) ^ (-s)))‖ := by rw [norm_mul, mul_comm]
      _ ≤ ‖w‖ * ((3/2) * ‖-((p:ℕ):ℂ) ^ (-s)‖) :=
          mul_le_mul_of_nonneg_left (Complex.norm_log_one_add_half_le_self hz) (norm_nonneg w)
      _ = (3/2) * ‖w‖ * (((p:ℕ):ℝ) ^ (-s.re)) := by
          rw [norm_neg, Complex.norm_natCast_cpow_of_pos p.prop.pos (-s), Complex.neg_re]; ring
  rw [← Real.rexp_tsum_eq_tprod
    (f := fun p : Nat.Primes => ‖((1:ℂ) - ((p:ℕ):ℂ) ^ (-s))^w‖)
    (fun p => by
      rw [Complex.cpow_def_of_ne_zero (one_sub_cpow_ne_zero (p := p) hs0), Complex.norm_exp]
      exact Real.exp_pos _) hsumm]
  congr 1
  have hLw : Lw s = ∑' p : Nat.Primes, Complex.log (1 - ((p:ℕ):ℂ) ^ (-s)) := rfl
  rw [hLw, ← tsum_mul_left, Complex.re_tsum ((summable_Lw hs).mul_left w)]
  refine tsum_congr (fun p => ?_)
  have hne : ((1:ℂ) - ((p:ℕ):ℂ) ^ (-s)) ≠ 0 := one_sub_cpow_ne_zero (p := p) hs0
  simp only [Complex.cpow_def_of_ne_zero hne, Complex.norm_exp, Real.log_exp, Complex.mul_re]
  ring

/-- The real part of `Lw s` is `- log ‖ζ(s)‖` on `1 < re s`. -/
lemma re_Lw {s : ℂ} (hs : 1 < s.re) : (Lw s).re = -Real.log ‖riemannZeta s‖ := by
  have h1 : Real.exp ((Lw s).re) = (‖riemannZeta s‖)⁻¹ := by
    rw [← Complex.norm_exp, cexp_Lw hs, norm_inv]
  have h2 : (Lw s).re = Real.log (Real.exp ((Lw s).re)) := (Real.log_exp _).symm
  rw [h2, h1, Real.log_inv]

private lemma re_add_abim_le {w : ℂ} (hw : ‖w‖ ≤ 1/2) : w.re + (11/10) * |w.im| ≤ 3/4 := by
  have h1 : w.re^2 + w.im^2 ≤ (1/2)^2 := by
    have h := Complex.sq_norm w
    rw [Complex.normSq_apply] at h
    nlinarith [hw, norm_nonneg w, h]
  have h2 : |w.im|^2 = w.im^2 := sq_abs _
  by_cases hre : w.re ≤ 0
  · have h3 : |w.im| ≤ 1/2 := by
      have := abs_im_le_norm w
      linarith
    nlinarith [hre, h3]
  · push Not at hre
    have h4 : (w.re + (11/10) * |w.im|)^2 ≤ (3/4)^2 := by
      nlinarith [sq_nonneg (w.re * (11/10) - |w.im|), h1, h2, abs_nonneg w.im,
        sq_nonneg (w.re + (11/10) * |w.im|)]
    nlinarith [h4, hre, abs_nonneg w.im]

private lemma log_pow_le {C : ℝ} (hC : 0 < C) :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 0 ≤ x →
      (1 + C * (Real.log (2 + x) + 1)) ^ (3/2:ℝ) ≤ D * (1 + x) ^ (3/16:ℝ) := by
  refine ⟨(1 + 9 * C) ^ (3/2:ℝ) * 2 ^ (3/16:ℝ), by positivity, fun x hx => ?_⟩
  have h2x : (1:ℝ) ≤ 2 + x := by linarith
  have hlog : Real.log (2 + x) ≤ 8 * (2 + x) ^ (1/8:ℝ) := by
    have h := Real.log_le_rpow_div (x := 2 + x) (ε := (1/8:ℝ)) (by linarith) (by norm_num)
    rw [show (2 + x) ^ ((1:ℝ)/8) / ((1:ℝ)/8) = 8 * (2 + x) ^ ((1:ℝ)/8) by ring] at h
    exact h
  have hX1 : (1:ℝ) ≤ (2 + x) ^ (1/8:ℝ) := Real.one_le_rpow h2x (by norm_num)
  have hX0 : (0:ℝ) < (2 + x) ^ (1/8:ℝ) := lt_of_lt_of_le one_pos hX1
  have h3 : 1 + C * (Real.log (2 + x) + 1) ≤ (1 + 9 * C) * (2 + x) ^ (1/8:ℝ) := by
    nlinarith [hC, hlog, hX1]
  have h4 : (1 + C * (Real.log (2 + x) + 1)) ^ (3/2:ℝ)
      ≤ ((1 + 9 * C) * (2 + x) ^ (1/8:ℝ)) ^ (3/2:ℝ) :=
    Real.rpow_le_rpow (by have := Real.log_nonneg h2x; nlinarith [hC]) h3 (by norm_num)
  have h5 : ((1 + 9 * C) * (2 + x) ^ (1/8:ℝ)) ^ (3/2:ℝ)
      = (1 + 9 * C) ^ (3/2:ℝ) * (2 + x) ^ (3/16:ℝ) := by
    rw [Real.mul_rpow (by positivity) (le_of_lt hX0),
      ← Real.rpow_mul (by linarith : (0:ℝ) ≤ 2 + x)]
    norm_num
  have h6 : (2 + x) ^ (3/16:ℝ) ≤ 2 ^ (3/16:ℝ) * (1 + x) ^ (3/16:ℝ) := by
    have h7 : 2 + x ≤ 2 * (1 + x) := by linarith
    calc (2 + x) ^ (3/16:ℝ) ≤ (2 * (1 + x)) ^ (3/16:ℝ) :=
          Real.rpow_le_rpow (by linarith) h7 (by norm_num)
      _ = 2 ^ (3/16:ℝ) * (1 + x) ^ (3/16:ℝ) := Real.mul_rpow (by norm_num) (by linarith)
  rw [h5] at h4
  calc (1 + C * (Real.log (2 + x) + 1)) ^ (3/2:ℝ)
      ≤ (1 + 9 * C) ^ (3/2:ℝ) * (2 + x) ^ (3/16:ℝ) := h4
    _ ≤ (1 + 9 * C) ^ (3/2:ℝ) * (2 ^ (3/16:ℝ) * (1 + x) ^ (3/16:ℝ)) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = (1 + 9 * C) ^ (3/2:ℝ) * 2 ^ (3/16:ℝ) * (1 + x) ^ (3/16:ℝ) := by ring

end ValueBound
section DerivBound

private lemma logDeriv_eventuallyEq {f g : ℂ → ℂ} {s : ℂ} (h : f =ᶠ[𝓝 s] g) (h0 : f s ≠ 0) :
    logDeriv f s = logDeriv g s := by
  have hfs : f s = g s := h.self_of_nhds
  simp only [logDeriv, Pi.div_apply, h.deriv_eq, hfs]

/-- `logDeriv` of `z ↦ (z - 1)^c` is `c/(s-1)`. -/
private lemma logDeriv_cpow_sub {c : ℂ} {s : ℂ} (hsp : (s - 1) ∈ slitPlane) :
    logDeriv (fun z : ℂ => (z - 1) ^ c) s = c / (s - 1) := by
  have hne : (s - 1) ≠ 0 := slitPlane_ne_zero hsp
  have hc : (s - 1) ^ c ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hne]; exact Complex.exp_ne_zero _
  have h1 : HasDerivAt (fun z : ℂ => (z - 1) ^ c) (c * (s - 1) ^ (c - 1)) s := by
    have h2 : HasDerivAt (fun z : ℂ => z - 1) 1 s := (hasDerivAt_id s).sub_const 1
    have h3 := h2.cpow (hasDerivAt_const s c) hsp
    simpa using h3
  have hc1 : (s - 1) ^ (c - 1) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hne]; exact Complex.exp_ne_zero _
  have h4 : (s - 1) ^ c = (s - 1) ^ (c - 1) * (s - 1) := by
    conv_lhs => rw [show c = (c - 1) + 1 by ring]
    rw [Complex.cpow_add _ _ hne, Complex.cpow_one]
  rw [logDeriv, Pi.div_apply, h1.deriv, h4]
  field_simp

/-- `logDeriv` of `z ↦ (exp (w · Lw z))⁻¹` is `-w·Lw'`. -/
private lemma logDeriv_exp_inv {w : ℂ} {s : ℂ} (hs : 1 < s.re) :
    logDeriv (fun z : ℂ => (Complex.exp (w * Lw z))⁻¹) s = -(w * deriv Lw s) := by
  have h1 : DifferentiableAt ℂ (fun z : ℂ => w * Lw z) s :=
    (differentiableAt_const w).mul (differentiableAt_Lw hs)
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (w * Lw z)) s :=
    Complex.differentiableAt_exp.comp s h1
  have h3 : logDeriv (fun z : ℂ => (Complex.exp (w * Lw z))⁻¹) s
      = logDeriv (fun x : ℂ => x⁻¹) (Complex.exp (w * Lw s)) * deriv (fun z => Complex.exp (w * Lw z)) s :=
    logDeriv_comp (f := fun x : ℂ => x⁻¹) (g := fun z : ℂ => Complex.exp (w * Lw z))
      (differentiableAt_inv (Complex.exp_ne_zero _)) h2
  rw [h3, logDeriv_inv]
  have h4 : deriv (fun z : ℂ => Complex.exp (w * Lw z)) s
      = Complex.exp (w * Lw s) * (w * deriv Lw s) := by
    have h5 := deriv_comp (x := s) (h := fun z : ℂ => w * Lw z) (h₂ := Complex.exp)
      (differentiableAt_exp (x := w * Lw s)) h1
    simp only [Complex.deriv_exp] at h5
    rw [deriv_const_mul w (differentiableAt_Lw hs)] at h5
    simpa [Function.comp_def] using h5
  rw [h4]
  field_simp

/-- The product `∏_p (1 - p^{-z})^w` equals `exp (w · Lw z)`. -/
lemma tprod_cpow_eq_cexp {w : ℂ} {s : ℂ} (hs : 1 < s.re) :
    (∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-s))^w)) = Complex.exp (w * Lw s) := by
  have h1 : ∀ p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-s))^w)
      = Complex.exp (Complex.log (1 - ((p:ℕ):ℂ) ^ (-s)) * w) := by
    intro p
    rw [Complex.cpow_def_of_ne_zero (one_sub_cpow_ne_zero (p := p) (lt_trans one_pos hs))]
  rw [tprod_congr h1]
  have h2 : Summable (fun p : Nat.Primes => Complex.log (1 - ((p:ℕ):ℂ) ^ (-s)) * w) :=
    (summable_Lw hs).mul_right w
  have h3' : (∏' b : Nat.Primes, Complex.exp (Complex.log (1 - ((b:ℕ):ℂ) ^ (-s)) * w))
      = Complex.exp (∑' b : Nat.Primes, Complex.log (1 - ((b:ℕ):ℂ) ^ (-s)) * w) := by
    have h3 := (h2.hasSum.cexp).tprod_eq
    simpa [Function.comp_def] using h3
  rw [h3']
  congr 1
  rw [show Lw s = ∑' x : Nat.Primes, Complex.log (1 - ((x:ℕ):ℂ) ^ (-s)) from rfl,
    tsum_mul_right]
  ring

private lemma one_add_log_pow_four_le (x : ℝ) (hx : 0 ≤ x) :
    (1 + Real.log (2 + x))^4 ≤ 64 * (1 + x)^2 := by
  have hy : (1:ℝ) < 2 + x := by linarith
  have hy0 : (0:ℝ) < 2 + x := by linarith
  have h1 : 1 + Real.log (2 + x) ≤ 2 * Real.sqrt (2 + x) := by
    have h2 : Real.log (2 + x) = 2 * Real.log (Real.sqrt (2 + x)) := by
      rw [Real.log_sqrt hy0.le]; ring
    have h3 : Real.log (Real.sqrt (2 + x)) ≤ Real.sqrt (2 + x) - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hy0)
    rw [h2]; linarith
  have h4 : (0:ℝ) ≤ 1 + Real.log (2 + x) := by
    have := Real.log_nonneg hy.le; linarith
  have h5 : (2 * Real.sqrt (2 + x))^4 = 16 * (2 + x)^2 := by
    rw [mul_pow, show (Real.sqrt (2+x))^4 = ((Real.sqrt (2+x))^2)^2 by ring,
      Real.sq_sqrt hy0.le]
    ring
  calc (1 + Real.log (2 + x))^4 ≤ (2 * Real.sqrt (2 + x))^4 := pow_le_pow_left₀ h4 h1 4
    _ = 16 * (2 + x)^2 := h5
    _ ≤ 64 * (1 + x)^2 := by nlinarith [hx]

/-- The log-derivative of `Hfun w` is bounded on the closed half-plane `1 ≤ re s`. -/
lemma norm_logDeriv_Hfun_le {w : ℂ} (hw : ‖w‖ ≤ 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 ≤ s.re → ‖logDeriv (Hfun w) s‖ ≤ C := by
  set T := ∑' p : Nat.Primes, (((p:ℕ):ℝ))^(-(3/2:ℝ)) with hTdef
  have hTnn : (0:ℝ) ≤ T := tsum_nonneg (fun p => Real.rpow_nonneg (by positivity) _)
  refine ⟨2 * (Real.log (2 * Real.exp (200 * T)) + 4000 * T)
      * (1/16) / ((1/8 - 1/16) * (1/16)), ?_, fun s hs => ?_⟩
  · have h3 : (1:ℝ) ≤ Real.exp (200 * T) := Real.one_le_exp (by linarith [hTnn])
    have h1 : (0:ℝ) < Real.log (2 * Real.exp (200 * T)) := Real.log_pos (by linarith)
    have h2 : (0:ℝ) < Real.log (2 * Real.exp (200 * T)) + 4000 * T := by linarith [hTnn, h1]
    have h4 : (0:ℝ) < (1/8 - 1/16 : ℝ) * (1/16) := by norm_num
    positivity
  have hmem : s ∈ omK := by show (3/4:ℝ) < s.re; linarith
  have hms : ∀ u : ℂ, u ∈ Metric.ball s (1/8) → u ∈ omK := by
    intro u hu
    have h1 : ‖u - s‖ < 1/8 := by
      have h1' := Metric.mem_ball.mp hu
      rwa [dist_eq_norm] at h1'
    have h2 : ‖u - s‖ ≤ 1/8 := le_of_lt h1
    have h3 : |u.re - s.re| ≤ ‖u - s‖ := Complex.abs_re_le_norm (u - s)
    show (3/4:ℝ) < u.re
    linarith [(abs_le.mp h3).1, h2, hs]
  have hg : AnalyticOnNhd ℂ (Hfun w) (Metric.ball s (1/8)) :=
    (analyticOnNhd_Hfun hw).mono (fun u hu => hms u hu)
  have hgne : ∀ u : ℂ, u ∈ Metric.ball s (1/8) → Hfun w u ≠ 0 :=
    fun u hu => Hfun_w_ne_zero hw (hms u hu)
  have hgM : ∀ u : ℂ, u ∈ Metric.ball s (1/8) → ‖Hfun w u‖ ≤ Real.exp (200 * T) := by
    intro u hu
    exact (norm_Hfun_bounds hw (s := u) (hms u hu)).2
  have hgm : Real.exp (-(4000 * T)) ≤ ‖Hfun w s‖ := by
    have h := (norm_Hfun_bounds hw (s := s) hmem).1
    rw [hTdef]
    exact h
  have hbound := Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic
    (g := Hfun w) (c := s) (R := 1/8) (m := Real.exp (-(4000 * T))) (M := Real.exp (200 * T))
    (by norm_num) (Real.exp_pos _) (Real.exp_le_exp.mpr (by linarith [hTnn]))
    hg hgne hgM hgm (z₀ := s) (Metric.mem_ball_self (by norm_num)) (1/16) (by norm_num) (by
      rw [norm_sub_rev, sub_self, norm_zero]; norm_num)
  have hfin := hbound
  refine hfin.trans (le_of_eq ?_)
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp, Real.log_exp,
    sub_self, norm_zero]
  ring

/-- The derivative of `Afun w` on `1 < re s`. -/
lemma deriv_Afun_eq {w : ℂ} (hw : ‖w‖ ≤ 1/2) {s : ℂ} (hs : 1 < s.re) :
    deriv (Afun w) s = Afun w s * ((1 + w) * logDeriv riemannZeta₁ s + logDeriv (Hfun w) s) := by
  have hmem : ∀ᶠ z : ℂ in 𝓝 s, 1 < z.re := (isOpen_lt continuous_const continuous_re).mem_nhds hs
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  have hs0 : (0:ℝ) < s.re := lt_trans one_pos hs
  have hζn : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hHn : Hfun w s ≠ 0 := Hfun_w_ne_zero hw (by show (3/4:ℝ) < s.re; linarith)
  have hAPn : (Complex.exp (w * Lw s)) ≠ 0 := Complex.exp_ne_zero _
  have hAP0 : (∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-s))^w)) ≠ 0 := by
    rw [tprod_cpow_eq_cexp hs]; exact hAPn
  have hPn : (∏' p : Nat.Primes, (1 + w * ((p:ℕ):ℂ) ^ (-s))) ≠ 0 := by
    have h1 : Hfun w s = (∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-s))^w))
        * (∏' p : Nat.Primes, (1 + w * ((p:ℕ):ℂ) ^ (-s))) := Hfun_eq_mul hw hs
    intro hcon
    rw [hcon, mul_zero] at h1
    exact hHn h1
  have hDn : Dser w s ≠ 0 := by
    rw [Dser_euler w hs]
    exact mul_ne_zero hζn hPn
  have hsp : (s - 1) ∈ slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have hcpn : (s - 1) ^ ((1 + w : ℂ)) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (slitPlane_ne_zero hsp)]
    exact Complex.exp_ne_zero _
  have hAfun_n : Afun w s ≠ 0 := by
    rw [Afun, if_pos hs]
    exact mul_ne_zero hDn hcpn
  -- Afun agrees with the product near s
  have hAfun : (fun z : ℂ => Afun w z) =ᶠ[𝓝 s]
      (fun z : ℂ => riemannZeta z * Hfun w z
        * (∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-z))^w))⁻¹
        * (z - 1) ^ ((1 + w : ℂ))) := by
    filter_upwards [hmem] with z hz
    have hz0 : (0:ℝ) < z.re := lt_trans one_pos hz
    have h1 : Hfun w z = (∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-z))^w))
        * (∏' p : Nat.Primes, (1 + w * ((p:ℕ):ℂ) ^ (-z))) := Hfun_eq_mul hw hz
    have h2 : (∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-z))^w)) ≠ 0 := by
      rw [tprod_cpow_eq_cexp hz]; exact Complex.exp_ne_zero _
    rw [Afun, if_pos hz, Dser_euler w hz, h1]
    field_simp
  -- logDeriv of the model function
  have hAPinv : (fun z : ℂ => (∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-z))^w))⁻¹)
      =ᶠ[𝓝 s] (fun z : ℂ => (Complex.exp (w * Lw z))⁻¹) := by
    filter_upwards [hmem] with z hz
    rw [tprod_cpow_eq_cexp hz]
  have hlog : logDeriv (fun z : ℂ => riemannZeta z * Hfun w z
        * (∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-z))^w))⁻¹
        * (z - 1) ^ ((1 + w : ℂ))) s
      = deriv riemannZeta s / riemannZeta s + logDeriv (Hfun w) s
        + w * (deriv riemannZeta s / riemannZeta s) + (1 + w) / (s - 1) := by
    have hdζ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
    have hdH : DifferentiableAt ℂ (Hfun w) s :=
      ((analyticOnNhd_Hfun hw) s (by show (3/4:ℝ) < s.re; linarith)).differentiableAt
    have hlogAP : logDeriv (fun z : ℂ => (∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-z))^w))⁻¹) s
        = w * (deriv riemannZeta s / riemannZeta s) := by
      have h0 : (fun z : ℂ => (∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-z))^w))⁻¹) s ≠ 0 := by
        simp only
        exact inv_ne_zero hAP0
      rw [logDeriv_eventuallyEq hAPinv h0]
      rw [logDeriv_exp_inv hs, deriv_Lw hs]
      field_simp
    have hlog3 : logDeriv (fun z : ℂ => (z - 1) ^ ((1 + w : ℂ))) s = (1 + w) / (s - 1) :=
      logDeriv_cpow_sub hsp
    -- first: logDeriv of the product of the first two
    have h12 : logDeriv (fun z : ℂ => riemannZeta z * Hfun w z) s
        = deriv riemannZeta s / riemannZeta s + logDeriv (Hfun w) s := by
      rw [Submission.Port.logDeriv_mul_fun s hζn hHn hdζ hdH]
      simp only [logDeriv, Pi.div_apply]
    have hd12 : DifferentiableAt ℂ (fun z : ℂ => riemannZeta z * Hfun w z) s := hdζ.mul hdH
    have hdAPinv : DifferentiableAt ℂ (fun z : ℂ =>
        (∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-z))^w))⁻¹) s := by
      have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (w * Lw z)) s :=
        Complex.differentiableAt_exp.comp s ((differentiableAt_const w).mul (differentiableAt_Lw hs))
      have h1 : DifferentiableAt ℂ (fun z : ℂ => (Complex.exp (w * Lw z))⁻¹) s :=
        h2.inv (Complex.exp_ne_zero _)
      exact (Filter.EventuallyEq.differentiableAt_iff hAPinv).mpr h1
    have hd3 : DifferentiableAt ℂ (fun z : ℂ => (z - 1) ^ ((1 + w : ℂ))) s := by
      have h2 : HasDerivAt (fun z : ℂ => (z - 1) ^ ((1 + w : ℂ)))
          ((1+w) * (s - 1) ^ ((1 + w : ℂ) - 1)) s := by
        have h3 : HasDerivAt (fun z : ℂ => z - 1) 1 s := (hasDerivAt_id s).sub_const 1
        simpa using h3.cpow (hasDerivAt_const s (1 + w : ℂ)) hsp
      exact h2.differentiableAt
    have hn12 : (riemannZeta s * Hfun w s) ≠ 0 := mul_ne_zero hζn hHn
    have hnAP : (∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-s))^w))⁻¹ ≠ 0 := inv_ne_zero hAP0
    rw [show (fun z : ℂ => riemannZeta z * Hfun w z
          * (∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-z))^w))⁻¹
          * (z - 1) ^ ((1 + w : ℂ)))
        = (fun z : ℂ => (riemannZeta z * Hfun w z)
          * ((∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-z))^w))⁻¹ * (z - 1) ^ ((1 + w : ℂ))))
        from funext (fun z => by ring)]
    rw [Submission.Port.logDeriv_mul_fun (x := s) (f := fun z : ℂ => riemannZeta z * Hfun w z)
        (g := fun z : ℂ => (∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-z))^w))⁻¹
          * (z - 1) ^ ((1 + w : ℂ)))
        hn12 (mul_ne_zero hnAP hcpn) hd12 (hdAPinv.mul hd3),
      Submission.Port.logDeriv_mul_fun (x := s) (f := fun z : ℂ => (∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-z))^w))⁻¹)
        (g := fun z : ℂ => (z - 1) ^ ((1 + w : ℂ))) hnAP hcpn hdAPinv hd3, h12, hlogAP, hlog3]
    simp only [logDeriv, Pi.div_apply]
    ring
  -- conclude
  have hderiv : deriv (Afun w) s = deriv (fun z : ℂ => riemannZeta z * Hfun w z
        * (∏' p : Nat.Primes, (((1:ℂ) - ((p:ℕ):ℂ) ^ (-z))^w))⁻¹
        * (z - 1) ^ ((1 + w : ℂ))) s := hAfun.deriv_eq
  have hkey : logDeriv (Afun w) s = (1 + w) * logDeriv riemannZeta₁ s + logDeriv (Hfun w) s := by
    rw [logDeriv_eventuallyEq hAfun hAfun_n, hlog]
    have hld := Commons.NumberTheory.Zeta.logDeriv_zeta1_eq (s := s) hs1
      (Commons.NumberTheory.Zeta.zeta1_ne_zero_of_one_le_re (le_of_lt hs))
    simp only [logDeriv, Pi.div_apply] at hld ⊢
    rw [hld]
    field_simp
    ring
  rw [logDeriv] at hkey
  rw [← hkey, Pi.div_apply, mul_div_cancel₀ _ hAfun_n]

end DerivBound

end LwPrimeLog


end Zeta1LogDerivBound

end SharpImBound

end HfunBounds


section FinalAssembly

/-- At a point where the function is locally zero on the open left half-plane, the derivative vanishes. -/
private lemma deriv_eq_zero_of_eventually_zero_left {A : ℂ → ℂ} {s₀ : ℂ} (hs : A s₀ = 0)
    (h : ∃ ε > 0, ∀ t : ℂ, t.im = 0 → t.re < 0 → ‖t‖ < ε → A (s₀ + t) = 0) : deriv A s₀ = 0 := by
  by_cases hd : DifferentiableAt ℂ A s₀
  · have hlim : Tendsto (fun t : ℂ => t⁻¹ • (A (s₀ + t) - A s₀)) (𝓝[≠] 0) (𝓝 (deriv A s₀)) :=
      hd.hasDerivAt.tendsto_slope_zero
    obtain ⟨ε, hε, hε'⟩ := h
    set S : Set ℂ := {t : ℂ | t.im = 0 ∧ t.re < 0} with hS
    have hsub : 𝓝[S] 0 ≤ 𝓝[≠] (0:ℂ) := by
      apply nhdsWithin_mono
      intro t ht
      rw [hS] at ht
      simp only [Set.mem_setOf_eq] at ht
      intro h0
      rw [h0] at ht
      exact absurd ht.2 (by simp only [Complex.zero_re]; norm_num)
    have hlim2 := hlim.mono_left hsub
    have hEv : ∀ᶠ t in 𝓝[S] (0:ℂ), ‖t‖ < ε := by
      have hmem2 : Metric.ball (0:ℂ) ε ∈ 𝓝[S] (0:ℂ) :=
        (Filter.le_def.mp nhdsWithin_le_nhds) (Metric.ball (0:ℂ) ε) (Metric.ball_mem_nhds _ hε)
      filter_upwards [hmem2] with t ht
      rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at ht
    have hzero : (fun t : ℂ => t⁻¹ • (A (s₀ + t) - A s₀)) =ᶠ[𝓝[S] 0] 0 := by
      filter_upwards [self_mem_nhdsWithin, hEv] with t hmem ht'
      rw [hS] at hmem
      simp only [Set.mem_setOf_eq] at hmem
      have h1 : A (s₀ + t) = 0 := hε' t hmem.1 hmem.2 ht'
      rw [h1, hs, sub_zero, smul_zero]
      rfl
    haveI : (𝓝[S] (0:ℂ)).NeBot := by
      apply mem_closure_iff_nhdsWithin_neBot.mp
      apply mem_closure_iff.mpr
      intro U hU hxU
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
      have hpos : (0:ℝ) < min δ 1 / 2 := by have := lt_min hδ one_pos; linarith
      refine ⟨-(((min δ 1 / 2) : ℝ) : ℂ), hball ?_,
        ⟨by simp only [Complex.neg_im, Complex.ofReal_im, neg_zero], ?_⟩⟩
      · rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_neg, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hpos.le]
        calc min δ 1 / 2 < min δ 1 := by linarith
          _ ≤ δ := min_le_left δ 1
      · simp only [Complex.neg_re, Complex.ofReal_re]
        linarith
    have hlim3 := tendsto_const_nhds.congr' hzero.symm
    exact tendsto_nhds_unique hlim2 hlim3
  · exact deriv_zero_of_not_differentiableAt hd

private lemma log_one_add_omegaLocalHat_one {w : ℂ} (hw : ‖w‖ ≤ 1/2) (p : Nat.Primes) :
    Complex.log (1 + omegaLocalHat w p 1)
      = w * Complex.log (1 - ((((p:ℕ):ℝ)⁻¹ : ℝ) : ℂ))
        + Complex.log (1 + w * ((((p:ℕ):ℝ)⁻¹ : ℝ) : ℂ)) := by
  have hp2 : (2:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast p.prop.two_le
  have hp0 : (0:ℝ) < ((p:ℕ):ℝ) := by linarith
  have hp1 : (1:ℝ) < ((p:ℕ):ℝ) := by linarith
  have hpinv0 : (0:ℝ) ≤ ((p:ℕ):ℝ)⁻¹ := by positivity
  have hpinv1 : ((p:ℕ):ℝ)⁻¹ ≤ 1 := by rw [inv_le_one₀ hp0]; linarith
  have hpinv : ((p:ℕ):ℝ)⁻¹ ≤ 1/2 := by
    rw [inv_le_comm₀ hp0 (by norm_num : (0:ℝ) < 1/2)]
    rw [show ((1:ℝ)/2)⁻¹ = 2 by norm_num]
    exact hp2
  set x : ℝ := 1 - (((p:ℕ):ℝ))⁻¹ with hx
  have hx0 : 0 < x := by rw [hx]; rw [sub_pos]; exact inv_lt_one_of_one_lt₀ hp1
  have hxhalf : (1/2:ℝ) ≤ x := by rw [hx]; linarith
  have hlogx_abs : |Real.log x| ≤ Real.log 2 := by
    rw [abs_le]
    exact ⟨by
      have h := Real.log_le_log (by norm_num : (0:ℝ) < 1/2) hxhalf
      rw [show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num, Real.log_inv] at h
      linarith,
      by refine Real.log_le_log hx0 ?_; rw [hx]; linarith⟩
  have hwim : |w.im| ≤ 1/2 := (abs_im_le_norm w).trans hw
  have hmain : |Real.log x * w.im| ≤ Real.log 2 / 2 := by
    have h := mul_le_mul hlogx_abs hwim (abs_nonneg _) (le_of_lt (Real.log_pos (by norm_num)))
    calc |Real.log x * w.im| = |Real.log x| * |w.im| := abs_mul _ _
      _ ≤ Real.log 2 * (1/2) := h
      _ = Real.log 2 / 2 := by ring
  have hlog2lt : Real.log 2 < Real.pi := by
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    linarith [Real.pi_gt_three]
  have hx0c : (((x:ℝ):ℂ)) ≠ 0 := by exact_mod_cast hx0.ne'
  have hlogz : Complex.log (((x:ℝ):ℂ)) = ((Real.log x : ℝ) : ℂ) :=
    (Complex.ofReal_log hx0.le).symm
  set y : ℂ := 1 + w * ((((p:ℕ):ℝ)⁻¹ : ℝ) : ℂ) with hydef
  have hy_re : y.re = 1 + w.re * ((p:ℕ):ℝ)⁻¹ := by
    rw [hydef]
    simp [Complex.mul_re]
  have hwre : -(1/2:ℝ) ≤ w.re := (abs_le.mp ((Complex.abs_re_le_norm w).trans hw)).1
  have hy_pos : 0 < y.re := by
    rw [hy_re]
    have h4 := mul_le_mul_of_nonneg_right hwre hpinv0
    have h5 := mul_le_mul_of_nonneg_left hpinv1 (by norm_num : (0:ℝ) ≤ 1/2)
    linarith
  have hy_ne : y ≠ 0 := by
    intro hcon
    have h := congrArg Complex.re hcon
    rw [Complex.zero_re] at h
    linarith [hy_pos]
  have hargy : |y.arg| < Real.pi/2 := by
    rw [Complex.abs_arg_lt_pi_div_two_iff]
    exact Or.inl hy_pos
  have hu_im : (w * Complex.log (((x:ℝ):ℂ)) + Complex.log y).im = Real.log x * w.im + y.arg := by
    have h1 : (w * Complex.log (((x:ℝ):ℂ))).im = w.re * 0 + w.im * Real.log x := by
      rw [Complex.mul_im, hlogz, Complex.ofReal_im, Complex.ofReal_re]
    rw [Complex.add_im, h1, Complex.log_im]
    ring
  have hb : |Real.log x * w.im| ≤ Real.log 2 / 2 := hmain
  have hu_bound : -Real.pi < (w * Complex.log (((x:ℝ):ℂ)) + Complex.log y).im
      ∧ (w * Complex.log (((x:ℝ):ℂ)) + Complex.log y).im ≤ Real.pi := by
    rw [hu_im]
    have h1 := (abs_le.mp hb).1
    have h2 := (abs_le.mp hb).2
    have h3 := (abs_lt.mp hargy).1
    have h4 := (abs_lt.mp hargy).2
    constructor <;> linarith [hlog2lt, Real.pi_pos]
  have hfac : (1:ℂ) + omegaLocalHat w p 1 = (((x:ℝ):ℂ)) ^ w * y := by
    have h1 : ((p:ℕ):ℂ) ^ (-(1:ℂ)) = ((((p:ℕ):ℝ)⁻¹ : ℝ) : ℂ) := by
      rw [Complex.cpow_neg, Complex.cpow_one, Complex.ofReal_inv]
      norm_num
    have h2 : (1:ℂ) - ((((p:ℕ):ℝ)⁻¹ : ℝ) : ℂ) = ((x:ℝ):ℂ) := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← hx]
    rw [one_add_omegaLocalHat_eq, h1, h2, hydef]
  have hexp : Complex.exp (w * Complex.log (((x:ℝ):ℂ)) + Complex.log y) = (((x:ℝ):ℂ)) ^ w * y := by
    rw [Complex.exp_add, Complex.exp_log hy_ne,
      Complex.cpow_def_of_ne_zero hx0c, mul_comm w]
  rw [hfac, ← hexp, Complex.log_exp hu_bound.1 hu_bound.2,
    hx, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv]

lemma norm_Hfun_one_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1/2) : ‖Hfun w 1 - 1‖ ≤ 3 * ‖w‖ := by
  have hK : (1:ℂ) ∈ omK := by show (3/4:ℝ) < (1:ℂ).re; norm_num
  have h1 : Hfun w 1 = Complex.exp (∑' p : Nat.Primes, Complex.log (1 + omegaLocalHat w p 1)) :=
    Hfun_eq_cexp hw hK
  have hsumm : Summable (fun p : Nat.Primes => Complex.log (1 + omegaLocalHat w p 1)) :=
    Complex.summable_log_one_add_of_summable (summable_omegaLocalHat hw hK)
  have htsum : (∑' p : Nat.Primes, Complex.log (1 + omegaLocalHat w p 1))
      = ∑' p : Nat.Primes, (w * Complex.log (1 - ((((p:ℕ):ℝ)⁻¹ : ℝ) : ℂ))
        + Complex.log (1 + w * ((((p:ℕ):ℝ)⁻¹ : ℝ) : ℂ))) :=
    tsum_congr (fun p => log_one_add_omegaLocalHat_one hw p)
  have hsumm1 : Summable (fun p : Nat.Primes => 1 / (((p:ℕ):ℝ) * (((p:ℕ):ℝ) - 1))) := by
    refine Summable.of_nonneg_of_le ?_ ?_
      ((summable_primes_rpow_neg (by norm_num : (1:ℝ) < 2)).mul_left 2)
    · intro p
      have hp1 : (1:ℝ) < ((p:ℕ):ℝ) := by exact_mod_cast p.prop.one_lt
      have h : (0:ℝ) < ((p:ℕ):ℝ) * (((p:ℕ):ℝ) - 1) := by nlinarith
      exact div_nonneg zero_le_one h.le
    · intro p
      have hp2 : (2:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast p.prop.two_le
      have hp0 : (0:ℝ) < ((p:ℕ):ℝ) := by linarith
      have h2 : (((p:ℕ):ℝ)) ^ (-(2:ℝ)) = 2 / ((p:ℕ):ℝ)^2 / 2 := by
        rw [Real.rpow_neg hp0.le, Real.rpow_two, inv_eq_one_div]
        ring
      rw [h2]
      have h3 : (2:ℝ) * (2 / ((p:ℕ):ℝ)^2 / 2) = 2 / ((p:ℕ):ℝ)^2 := by ring
      rw [h3, div_le_div_iff₀ (by nlinarith) (by positivity)]
      nlinarith
  have hsumm2 : Summable (fun p : Nat.Primes => ((((p:ℕ):ℝ))⁻¹)^2) := by
    refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_)
      ((summable_primes_rpow_neg (by norm_num : (1:ℝ) < 2)))
    have h2 : (((p:ℕ):ℝ)) ^ (-(2:ℝ)) = ((((p:ℕ):ℝ))⁻¹)^2 := by
      rw [Real.rpow_neg (show (0:ℝ) ≤ ((p:ℕ):ℝ) by exact_mod_cast p.prop.pos.le),
        Real.rpow_two, inv_pow]
    rw [h2]
  have hsumm3 : Summable (fun p : Nat.Primes => w * Complex.log (1 - ((((p:ℕ):ℝ)⁻¹ : ℝ) : ℂ))
        + Complex.log (1 + w * ((((p:ℕ):ℝ)⁻¹ : ℝ) : ℂ))) :=
    hsumm.congr (fun p => log_one_add_omegaLocalHat_one hw p)
  have hmaj : Summable (fun p : Nat.Primes => ‖w‖ * (1 / (((p:ℕ):ℝ) * (((p:ℕ):ℝ) - 1)))
        + (2/3) * ‖w‖^2 * ((((p:ℕ):ℝ))⁻¹)^2) :=
    (hsumm1.mul_left ‖w‖).add (hsumm2.mul_left ((2/3) * ‖w‖^2))
  have hnorm0 : Summable (fun p : Nat.Primes =>
      ‖w * Complex.log (1 - ((((p:ℕ):ℝ)⁻¹ : ℝ) : ℂ))
        + Complex.log (1 + w * ((((p:ℕ):ℝ)⁻¹ : ℝ) : ℂ))‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => norm_log_series_term_le w hw p) hmaj
  have hnorm : ‖∑' p : Nat.Primes, Complex.log (1 + omegaLocalHat w p 1)‖ ≤ (4/3) * ‖w‖ := by
    rw [htsum]
    refine (norm_tsum_le_tsum_norm hnorm0).trans ?_
    refine (Summable.tsum_le_tsum (fun p => norm_log_series_term_le w hw p) hnorm0 hmaj).trans ?_
    rw [(hsumm1.mul_left ‖w‖).tsum_add (hsumm2.mul_left ((2/3) * ‖w‖^2)),
      tsum_mul_left, tsum_mul_left]
    have hA := tsum_primes_inv_mul_pred_le
    have hB := tsum_primes_inv_sq_le
    have hw1 : (0:ℝ) ≤ ‖w‖ := norm_nonneg w
    have h1 : ∑' p : Nat.Primes, ((((p:ℕ):ℝ))⁻¹)^2 ≤ 1 := hB
    nlinarith [hw1, hw, hA, h1]
  have h2 : ‖Hfun w 1 - 1‖ ≤ 2 * ‖∑' p : Nat.Primes, Complex.log (1 + omegaLocalHat w p 1)‖ := by
    rw [h1]
    refine norm_cexp_sub_one_le ?_
    calc ‖∑' p : Nat.Primes, Complex.log (1 + omegaLocalHat w p 1)‖ ≤ (4/3) * ‖w‖ := hnorm
      _ ≤ (4/3) * (1/2) := by linarith [norm_nonneg w, hw]
      _ ≤ 1 := by norm_num
  calc ‖Hfun w 1 - 1‖ ≤ 2 * ‖∑' p : Nat.Primes, Complex.log (1 + omegaLocalHat w p 1)‖ := h2
    _ ≤ 2 * ((4/3) * ‖w‖) := by linarith [hnorm]
    _ ≤ 3 * ‖w‖ := by linarith [norm_nonneg w]

end FinalAssembly


/-- The witness function for the theorem: on a ball around 1 it is the product
`ζ₁^{1+w}·Hfun`, on the half-plane `1 < re s` it is `Dser·(s-1)^{1+w}` and elsewhere it is `0`. -/
noncomputable def Aw (w : ℂ) (ρ : ℝ) : ℂ → ℂ := by
  classical
  exact fun s =>
    if s ∈ Metric.ball 1 ρ then riemannZeta₁ s ^ (1 + w : ℂ) * Hfun w s
    else if 1 < s.re then Dser w s * (s - 1) ^ ((1 + w : ℂ)) else 0

lemma Aw_of_mem {w : ℂ} {ρ : ℝ} {s : ℂ} (h : s ∈ Metric.ball 1 ρ) :
    Aw w ρ s = riemannZeta₁ s ^ (1 + w : ℂ) * Hfun w s := by
  classical
  simp only [Aw]
  exact if_pos h

lemma Aw_of_not_mem {w : ℂ} {ρ : ℝ} {s : ℂ} (h : s ∉ Metric.ball 1 ρ) :
    Aw w ρ s = (if 1 < s.re then Dser w s * (s - 1) ^ ((1 + w : ℂ)) else 0) := by
  classical
  simp only [Aw]
  exact if_neg h

lemma Aw_of_not_mem_of_gt {w : ℂ} {ρ : ℝ} {s : ℂ} (h : s ∉ Metric.ball 1 ρ) (h2 : 1 < s.re) :
    Aw w ρ s = Dser w s * (s - 1) ^ ((1 + w : ℂ)) :=
  (Aw_of_not_mem h).trans (if_pos h2)

lemma Aw_of_not_mem_of_not_gt {w : ℂ} {ρ : ℝ} {s : ℂ} (h : s ∉ Metric.ball 1 ρ)
    (h2 : ¬ 1 < s.re) : Aw w ρ s = 0 :=
  (Aw_of_not_mem h).trans (if_neg h2)


end Commons.NumberTheory.DirichletSeries
