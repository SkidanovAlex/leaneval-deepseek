/-
# `Submission.Work.FIArea7CF.Prop213FinalB` — clash-free copy of `Submission.Work.FIArea7.Pub213.Prop213Final`

Imports redirected to the `FIArea7CF` copies; renamed: gnorm_mk_eq→cfx_gnorm_mk_eq, mem_gBox_iff→r2c_mem_gBox_iff.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7.Pub213.Defs
import Submission.Work.FIArea7.Pub213.exists_decomp
import Submission.Work.FIArea7.Pub213.dirichletSym_reciprocity_pp
import Submission.Work.FIArea7.Pub213.sum_CBox_rpow_le
import Submission.Work.FIArea7.Pub213.Prop213Pub
import Submission.Work.FIArea7.Pub213.Prop213PubB
import Submission.Work.FIArea7CF.holder6_boundB
import Submission.Work.FIArea7.dirichletSym_mul
import Submission.Work.FIArea7.Classical172Defs



set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FIArea7.Pub213

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 8. Elementary arithmetic -/

lemma tail_nonneg {M N A2 : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) :
    0 ≤ (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)
        * (Real.log (M * N + 2)) ^ A2 := by
  have h1 : (0 : ℝ) ≤ M + N := by linarith
  have h2 : (0 : ℝ) ≤ M * N := by nlinarith
  have h3 : (0 : ℝ) ≤ Real.log (M * N + 2) := Real.log_nonneg (by linarith)
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg h1 _) (Real.rpow_nonneg h2 _))
    (Real.rpow_nonneg h3 _)

lemma log_ratio_le {M N g : ℝ} (hg1 : 1 ≤ g) (hM : 0 < M) (hN : 0 ≤ N) :
    Real.log (M * (N / g) + 2) ≤ Real.log (M * N + 2) := by
  have hng0 : (0 : ℝ) ≤ N / g := div_nonneg hN (by linarith)
  have hprod : (0 : ℝ) ≤ M * (N / g) := mul_nonneg hM.le hng0
  refine Real.log_le_log (by linarith) ?_
  have hng : N / g ≤ N := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  nlinarith

lemma div_rpow_eq {N g : ℝ} (hg : 0 < g) (hN : 0 ≤ N) :
    (N / g) ^ ((11 : ℝ) / 12)
      = N ^ ((11 : ℝ) / 12) * g ^ (-((11 : ℝ) / 12)) := by
  rw [Real.div_rpow hN (le_of_lt hg), Real.rpow_neg (le_of_lt hg), div_eq_mul_inv]

lemma paf_norm_intCast_le_one_of_abs_le_one {n : ℤ} (h : |n| ≤ 1) :
    ‖(((n : ℤ)) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast, ← Int.cast_abs]
  exact_mod_cast h

lemma mem_CBox_of_isC {c : GaussianInt} {N : ℝ} (hN : 1 ≤ N) (hIsC : Prop213Aux.IsC c)
    (hgn : (Work.FIPlan.gnorm c : ℝ) ≤ N) : c ∈ CBox N := by
  rw [mem_CBox]
  refine ⟨?_, hIsC⟩
  have hre : |(c.re : ℤ)| ≤ (⌈Real.sqrt N⌉₊ : ℤ) := by
    have h1 : |((c.re : ℤ) : ℝ)| ≤ Real.sqrt ((Work.FIPlan.gnorm c : ℕ) : ℝ) :=
      abs_re_cast_le_sqrt
    have h2 : Real.sqrt ((Work.FIPlan.gnorm c : ℕ) : ℝ) ≤ Real.sqrt N :=
      Real.sqrt_le_sqrt (by exact_mod_cast hgn)
    have h3 : Real.sqrt N ≤ ((⌈Real.sqrt N⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    exact_mod_cast le_trans (le_trans h1 h2) h3
  have him : |(c.im : ℤ)| ≤ (⌈Real.sqrt N⌉₊ : ℤ) := by
    have h1 : |((c.im : ℤ) : ℝ)| ≤ Real.sqrt ((Work.FIPlan.gnorm c : ℕ) : ℝ) :=
      abs_im_cast_le_sqrt
    have h2 : Real.sqrt ((Work.FIPlan.gnorm c : ℕ) : ℝ) ≤ Real.sqrt N :=
      Real.sqrt_le_sqrt (by exact_mod_cast hgn)
    have h3 : Real.sqrt N ≤ ((⌈Real.sqrt N⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    exact_mod_cast le_trans (le_trans h1 h2) h3
  refine mem_gBox_of_coords ?_ ?_ ?_ ?_
  · have := (abs_le.mp hre).1; omega
  · have := (abs_le.mp hre).2; omega
  · have := (abs_le.mp him).1; omega
  · have := (abs_le.mp him).2; omega

/-! ## 9. The two Hölder regimes of (21.9) -/

/-- In the regime `x ≤ y` the (21.9) bound with parameters `(x,y)` is `≤ 3x^{11/12}y`. -/
lemma D_le {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hxy : x ≤ y) :
    x ^ ((11 : ℝ) / 12) * y + x ^ ((7 : ℝ) / 6) * y ^ ((3 : ℝ) / 4)
        + x ^ ((4 : ℝ) / 3) * y ^ ((1 : ℝ) / 2)
      ≤ 3 * (x ^ ((11 : ℝ) / 12) * y + y ^ ((11 : ℝ) / 12) * x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have ht2 : x ^ ((7 : ℝ) / 6) * y ^ ((3 : ℝ) / 4) ≤ x ^ ((11 : ℝ) / 12) * y := by
    have hsplit : x ^ ((7 : ℝ) / 6) = x ^ ((11 : ℝ) / 12) * x ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hx0]
      norm_num
    have hle : y ^ ((3 : ℝ) / 4) ≤ y := by
      calc y ^ ((3 : ℝ) / 4) ≤ y ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
        _ = y := Real.rpow_one y
    have hxq : x ^ ((1 : ℝ) / 4) ≤ y ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by linarith) hxy (by norm_num)
    calc x ^ ((7 : ℝ) / 6) * y ^ ((3 : ℝ) / 4)
        = x ^ ((11 : ℝ) / 12) * (x ^ ((1 : ℝ) / 4) * y ^ ((3 : ℝ) / 4)) := by
          rw [hsplit]; ring
      _ ≤ x ^ ((11 : ℝ) / 12) * (y ^ ((1 : ℝ) / 4) * y ^ ((3 : ℝ) / 4)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hx0.le _)
          exact mul_le_mul_of_nonneg_right hxq (Real.rpow_nonneg hy0.le _)
      _ = x ^ ((11 : ℝ) / 12) * y := by
          have h4 : y ^ ((1 : ℝ) / 4) * y ^ ((3 : ℝ) / 4) = y := by
            rw [← Real.rpow_add hy0]
            norm_num
          rw [h4]
  have ht3 : x ^ ((4 : ℝ) / 3) * y ^ ((1 : ℝ) / 2) ≤ x ^ ((11 : ℝ) / 12) * y := by
    have hsplit : x ^ ((4 : ℝ) / 3) = x ^ ((11 : ℝ) / 12) * x ^ ((5 : ℝ) / 12) := by
      rw [← Real.rpow_add hx0]
      norm_num
    have hx56 : x ^ ((5 : ℝ) / 6) ≤ y := by
      calc x ^ ((5 : ℝ) / 6) ≤ x ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
        _ = x := Real.rpow_one x
        _ ≤ y := hxy
    have hx512 : x ^ ((5 : ℝ) / 12) ≤ y ^ ((1 : ℝ) / 2) := by
      have h1 : x ^ ((5 : ℝ) / 12) = (x ^ ((5 : ℝ) / 6)) ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_mul hx0.le]
        norm_num
      rw [h1]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hx0.le _) hx56 (by norm_num)
    calc x ^ ((4 : ℝ) / 3) * y ^ ((1 : ℝ) / 2)
        = x ^ ((11 : ℝ) / 12) * (x ^ ((5 : ℝ) / 12) * y ^ ((1 : ℝ) / 2)) := by
          rw [hsplit]; ring
      _ ≤ x ^ ((11 : ℝ) / 12) * (y ^ ((1 : ℝ) / 2) * y ^ ((1 : ℝ) / 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hx0.le _)
          exact mul_le_mul_of_nonneg_right hx512 (Real.rpow_nonneg hy0.le _)
      _ = x ^ ((11 : ℝ) / 12) * y := by
          have h4 : y ^ ((1 : ℝ) / 2) * y ^ ((1 : ℝ) / 2) = y := by
            rw [← Real.rpow_add hy0]
            norm_num
          rw [h4]
  have hA : (0 : ℝ) ≤ x ^ ((11 : ℝ) / 12) * y :=
    mul_nonneg (Real.rpow_nonneg hx0.le _) hy0.le
  have hB : (0 : ℝ) ≤ y ^ ((11 : ℝ) / 12) * x :=
    mul_nonneg (Real.rpow_nonneg hy0.le _) hx0.le
  linarith

/-- In the regime `y ≤ x` the (21.9) bound with parameters `(y,x)` is `≤ 3y^{11/12}x`. -/
lemma T_le {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hyx : y ≤ x) :
    y ^ ((11 : ℝ) / 12) * x + y ^ ((7 : ℝ) / 6) * x ^ ((3 : ℝ) / 4)
        + y ^ ((4 : ℝ) / 3) * x ^ ((1 : ℝ) / 2)
      ≤ 3 * (x ^ ((11 : ℝ) / 12) * y + y ^ ((11 : ℝ) / 12) * x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have ht2 : y ^ ((7 : ℝ) / 6) * x ^ ((3 : ℝ) / 4) ≤ y ^ ((11 : ℝ) / 12) * x := by
    have hsplit : y ^ ((7 : ℝ) / 6) = y ^ ((11 : ℝ) / 12) * y ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hy0]
      norm_num
    have hle : x ^ ((3 : ℝ) / 4) ≤ x := by
      calc x ^ ((3 : ℝ) / 4) ≤ x ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
        _ = x := Real.rpow_one x
    have hyq : y ^ ((1 : ℝ) / 4) ≤ x ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by linarith) hyx (by norm_num)
    calc y ^ ((7 : ℝ) / 6) * x ^ ((3 : ℝ) / 4)
        = y ^ ((11 : ℝ) / 12) * (y ^ ((1 : ℝ) / 4) * x ^ ((3 : ℝ) / 4)) := by
          rw [hsplit]; ring
      _ ≤ y ^ ((11 : ℝ) / 12) * (x ^ ((1 : ℝ) / 4) * x ^ ((3 : ℝ) / 4)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hy0.le _)
          exact mul_le_mul_of_nonneg_right hyq (Real.rpow_nonneg hx0.le _)
      _ = y ^ ((11 : ℝ) / 12) * x := by
          have h4 : x ^ ((1 : ℝ) / 4) * x ^ ((3 : ℝ) / 4) = x := by
            rw [← Real.rpow_add hx0]
            norm_num
          rw [h4]
  have ht3 : y ^ ((4 : ℝ) / 3) * x ^ ((1 : ℝ) / 2) ≤ y ^ ((11 : ℝ) / 12) * x := by
    have hsplit : y ^ ((4 : ℝ) / 3) = y ^ ((11 : ℝ) / 12) * y ^ ((5 : ℝ) / 12) := by
      rw [← Real.rpow_add hy0]
      norm_num
    have hy12 : y ^ ((5 : ℝ) / 12) ≤ x ^ ((1 : ℝ) / 2) := by
      have h1 : y ^ ((5 : ℝ) / 12) ≤ y ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
      have h2 : y ^ ((1 : ℝ) / 2) ≤ x ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (by linarith) hyx (by norm_num)
      linarith
    calc y ^ ((4 : ℝ) / 3) * x ^ ((1 : ℝ) / 2)
        = y ^ ((11 : ℝ) / 12) * (y ^ ((5 : ℝ) / 12) * x ^ ((1 : ℝ) / 2)) := by
          rw [hsplit]; ring
      _ ≤ y ^ ((11 : ℝ) / 12) * (x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hy0.le _)
          exact mul_le_mul_of_nonneg_right hy12 (Real.rpow_nonneg hx0.le _)
      _ = y ^ ((11 : ℝ) / 12) * x := by
          have h4 : x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) = x := by
            rw [← Real.rpow_add hx0]
            norm_num
          rw [h4]
  have hA : (0 : ℝ) ≤ x ^ ((11 : ℝ) / 12) * y :=
    mul_nonneg (Real.rpow_nonneg hx0.le _) hy0.le
  have hB : (0 : ℝ) ≤ y ^ ((11 : ℝ) / 12) * x :=
    mul_nonneg (Real.rpow_nonneg hy0.le _) hx0.le
  linarith

/-! ## 10. The class coefficients -/

lemma betaC_pp {Rz : ℤ} {c : GaussianInt} {β : GaussianInt → ℂ} {z' : GaussianInt}
    (h : betaC Rz c β z' ≠ 0) : Prop213Aux.IsPP z' := by
  have hex : ∃ z ∈ zClassP Rz c z', β z ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (by rw [betaC]; exact Finset.sum_eq_zero fun z hz => hc z hz)
  obtain ⟨z, hz, -⟩ := hex
  obtain ⟨-, hz0, -, hzp⟩ := mem_zClassP.mp hz
  rw [← hzp]
  exact ppPart_isPP hz0

lemma betaC_gnorm {Rz : ℤ} {c : GaussianInt} {β : GaussianInt → ℂ} {N : ℝ} {z' : GaussianInt}
    (hβsupp : ∀ z, β z ≠ 0 → (Work.FIPlan.gnorm z : ℝ) ≤ N)
    (hcpos : 0 < (Work.FIPlan.gnorm c : ℝ)) (h : betaC Rz c β z' ≠ 0) :
    (Work.FIPlan.gnorm z' : ℝ) ≤ N / (Work.FIPlan.gnorm c : ℝ) := by
  have hex : ∃ z ∈ zClassP Rz c z', β z ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (by rw [betaC]; exact Finset.sum_eq_zero fun z hz => hc z hz)
  obtain ⟨z, hz, hβz⟩ := hex
  obtain ⟨-, hz0, hzc, hzp⟩ := mem_zClassP.mp hz
  have hsplit : (Work.FIPlan.gnorm c : ℝ) * (Work.FIPlan.gnorm z' : ℝ)
      = (Work.FIPlan.gnorm z : ℝ) := by
    have hh := gnorm_cPart_mul_ppPart hz0
    rw [hzc, hzp] at hh
    exact_mod_cast hh
  rw [le_div_iff₀ hcpos, mul_comm, hsplit]
  exact hβsupp z hβz

lemma betaC_bound {Rz : ℤ} {c : GaussianInt} {β : GaussianInt → ℂ} (hβ1 : ∀ z, ‖β z‖ ≤ 1) :
    ∀ z', ‖betaC Rz c β z'‖ ≤ 1 := by
  intro z'
  have hinj : ∀ z₁ ∈ zClassP Rz c z', ∀ z₂ ∈ zClassP Rz c z', z₁ = z₂ := by
    intro z₁ h₁ z₂ h₂
    obtain ⟨-, h1z, h1c, h1p⟩ := mem_zClassP.mp h₁
    obtain ⟨-, h2z, h2c, h2p⟩ := mem_zClassP.mp h₂
    calc z₁ = cPart z₁ * ppPart z₁ := (cPart_mul_ppPart h1z).symm
      _ = c * z' := by rw [h1c, h1p]
      _ = cPart z₂ * ppPart z₂ := by rw [← h2c, ← h2p]
      _ = z₂ := cPart_mul_ppPart h2z
  by_cases hemp : (zClassP Rz c z').Nonempty
  · obtain ⟨z₀, hz₀⟩ := hemp
    have hsingle : zClassP Rz c z' = {z₀} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hz₀, ?_⟩
      intro z hz
      exact hinj z hz z₀ hz₀
    rw [betaC, hsingle, Finset.sum_singleton]
    exact hβ1 z₀
  · have hempty : zClassP Rz c z' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hemp
    rw [betaC, hempty, Finset.sum_empty, norm_zero]
    norm_num

lemma alphaC_bound {c : GaussianInt} {α : GaussianInt → ℂ} (hα1 : ∀ w, ‖α w‖ ≤ 1) :
    ∀ w, ‖alphaC c α w‖ ≤ 1 := by
  intro w
  rw [alphaC]
  have hξ : ‖(((DirichletSym w c : ℤ)) : ℂ)‖ ≤ 1 :=
    paf_norm_intCast_le_one_of_abs_le_one (Work.FIArea7.abs_dirichletSym_le_one w c)
  calc ‖α w * (((DirichletSym w c : ℤ)) : ℂ)‖
      = ‖α w‖ * ‖(((DirichletSym w c : ℤ)) : ℂ)‖ := norm_mul _ _
    _ ≤ 1 * 1 := mul_le_mul (hα1 w) hξ (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

lemma alphaC_supp {c : GaussianInt} {α : GaussianInt → ℂ} {M : ℝ}
    (hαsupp : ∀ w, α w ≠ 0 →
      Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧ (Work.FIPlan.gnorm w : ℝ) ≤ M) :
    ∀ w, alphaC c α w ≠ 0 →
      Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧ (Work.FIPlan.gnorm w : ℝ) ≤ M := by
  intro w hw
  exact hαsupp w (fun h => hw (by rw [alphaC, h, zero_mul]))

/-- The two cross terms are dominated by the target shape of (21.10). -/
lemma cross_le {M N : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) :
    M ^ ((11 : ℝ) / 12) * N + M * N ^ ((11 : ℝ) / 12)
      ≤ 2 * ((M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)) := by
  have hM0 : (0 : ℝ) < M := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hMsum : M ^ ((11 : ℝ) / 12) * M ^ ((1 : ℝ) / 12) = M := by
    rw [← Real.rpow_add hM0, show (11 : ℝ) / 12 + (1 : ℝ) / 12 = 1 by norm_num, Real.rpow_one]
  have hNsum : N ^ ((11 : ℝ) / 12) * N ^ ((1 : ℝ) / 12) = N := by
    rw [← Real.rpow_add hN0, show (11 : ℝ) / 12 + (1 : ℝ) / 12 = 1 by norm_num, Real.rpow_one]
  have hMN : M ^ ((11 : ℝ) / 12) * N ^ ((11 : ℝ) / 12) = (M * N) ^ ((11 : ℝ) / 12) :=
    (Real.mul_rpow hM0.le hN0.le).symm
  have hX : (0 : ℝ) ≤ (M * N) ^ ((11 : ℝ) / 12) :=
    Real.rpow_nonneg (mul_nonneg hM0.le hN0.le) _
  have h1 : M ^ ((11 : ℝ) / 12) * N
      ≤ (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12) := by
    have e : M ^ ((11 : ℝ) / 12) * N = (M * N) ^ ((11 : ℝ) / 12) * N ^ ((1 : ℝ) / 12) := by
      calc M ^ ((11 : ℝ) / 12) * N
          = M ^ ((11 : ℝ) / 12) * (N ^ ((11 : ℝ) / 12) * N ^ ((1 : ℝ) / 12)) := by rw [hNsum]
        _ = M ^ ((11 : ℝ) / 12) * N ^ ((11 : ℝ) / 12) * N ^ ((1 : ℝ) / 12) := by ring
        _ = (M * N) ^ ((11 : ℝ) / 12) * N ^ ((1 : ℝ) / 12) := by rw [hMN]
    rw [e]
    calc (M * N) ^ ((11 : ℝ) / 12) * N ^ ((1 : ℝ) / 12)
        ≤ (M * N) ^ ((11 : ℝ) / 12) * (M + N) ^ ((1 : ℝ) / 12) := by
          refine mul_le_mul_of_nonneg_left ?_ hX
          exact Real.rpow_le_rpow hN0.le (by linarith) (by norm_num)
      _ = (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12) := by ring
  have h2 : M * N ^ ((11 : ℝ) / 12)
      ≤ (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12) := by
    have e : M * N ^ ((11 : ℝ) / 12) = (M * N) ^ ((11 : ℝ) / 12) * M ^ ((1 : ℝ) / 12) := by
      calc M * N ^ ((11 : ℝ) / 12)
          = M ^ ((11 : ℝ) / 12) * M ^ ((1 : ℝ) / 12) * N ^ ((11 : ℝ) / 12) := by rw [hMsum]
        _ = M ^ ((11 : ℝ) / 12) * N ^ ((11 : ℝ) / 12) * M ^ ((1 : ℝ) / 12) := by ring
        _ = (M * N) ^ ((11 : ℝ) / 12) * M ^ ((1 : ℝ) / 12) := by rw [hMN]
    rw [e]
    calc (M * N) ^ ((11 : ℝ) / 12) * M ^ ((1 : ℝ) / 12)
        ≤ (M * N) ^ ((11 : ℝ) / 12) * (M + N) ^ ((1 : ℝ) / 12) := by
          refine mul_le_mul_of_nonneg_left ?_ hX
          exact Real.rpow_le_rpow hM0.le (by linarith) (by norm_num)
      _ = (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12) := by ring
  linarith

/-! ## 11. *FI* Proposition 21.3 (21.10) -/

lemma scale_le {A B L C2 : ℝ} (h : A ≤ B) (hC2 : 0 ≤ C2) (hL : 0 ≤ L) :
    C2 * A * L ≤ C2 * B * L :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hC2) hL

lemma one_le_tail {M N A2 : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) (hA2 : 0 < A2) :
    (1 : ℝ) ≤ (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)
      * (Real.log (M * N + 2)) ^ A2 := by
  have h1 : (1 : ℝ) ≤ (M + N) ^ ((1 : ℝ) / 12) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 12) := (Real.one_rpow _).symm
      _ ≤ (M + N) ^ ((1 : ℝ) / 12) := Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
  have h2 : (1 : ℝ) ≤ (M * N) ^ ((11 : ℝ) / 12) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((11 : ℝ) / 12) := (Real.one_rpow _).symm
      _ ≤ (M * N) ^ ((11 : ℝ) / 12) := Real.rpow_le_rpow (by norm_num) (by nlinarith) (by norm_num)
  have hlog3 : (1 : ℝ) ≤ Real.log (M * N + 2) := by
    have h : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
      exact Real.exp_one_lt_three.le
    exact le_trans h (Real.log_le_log (by norm_num) (by nlinarith))
  have h3 : (1 : ℝ) ≤ (Real.log (M * N + 2)) ^ A2 := by
    calc (1 : ℝ) = (1 : ℝ) ^ A2 := (Real.one_rpow _).symm
      _ ≤ (Real.log (M * N + 2)) ^ A2 := Real.rpow_le_rpow (by norm_num) hlog3 hA2.le
  have h12 : (1 : ℝ) ≤ (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12) := by
    have hm := mul_le_mul h1 h2 (by norm_num : (0 : ℝ) ≤ 1)
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) h1)
    simpa using hm
  have hm := mul_le_mul h12 h3 (by norm_num : (0 : ℝ) ≤ 1)
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) h12)
  simpa using hm

theorem prop213Pub : Work.FIArea7.Prop213 := by
  obtain ⟨C2, A2, hC2, hA2, hD2⟩ := holder6_bound
  obtain ⟨K1, hK1nn, hK1raw⟩ := sum_CBox_rpow_le (s := 11 / 6) (by norm_num)
  obtain ⟨K2, hK2nn, hK2raw⟩ := sum_CBox_rpow_le (s := 2) (by norm_num)
  have hK1 : ∀ X : ℝ, 1 ≤ X →
      ∑ c ∈ CBox X, ((Work.FIPlan.gnorm c : ℝ)) ^ (-((11 : ℝ) / 12)) ≤ K1 := by
    intro X hX
    have h := hK1raw X hX
    rw [show ((11 : ℝ) / 6 / 2) = (11 : ℝ) / 12 by norm_num] at h
    exact h
  have hK2 : ∀ X : ℝ, 1 ≤ X →
      ∑ c ∈ CBox X, ((Work.FIPlan.gnorm c : ℝ)) ^ (-(1 : ℝ)) ≤ K2 := by
    intro X hX
    have h := hK2raw X hX
    rw [show ((2 : ℝ) / 2) = (1 : ℝ) by norm_num] at h
    exact h
  have hK12nn : (0 : ℝ) ≤ K1 + K2 := by linarith
  refine ⟨6 * C2 * (K1 + K2) + 1, A2, ?_, hA2, ?_⟩
  · nlinarith [hC2, hK12nn]
  intro M N Rw Rz α β hM hN hα1 hβ1 hαsupp hβsupp
  have hMN0 : (0 : ℝ) ≤ M * N := by nlinarith
  have hLnn : (0 : ℝ) ≤ (Real.log (M * N + 2)) ^ A2 :=
    Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  have hTnn : (0 : ℝ) ≤ (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)
      * (Real.log (M * N + 2)) ^ A2 := tail_nonneg hM hN
  rcases lt_or_ge Rz 0 with hRzneg | hRz
  · have hz0 : QBilin Rw Rz α β = 0 := by
      simp only [QBilin, gBox_eq_empty_of_neg hRzneg, Finset.sum_empty, Finset.sum_const_zero]
    rw [hz0, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg (by nlinarith) _)) hLnn
  rcases lt_or_ge Rw 0 with hRwneg | hRw
  · have hz0 : QBilin Rw Rz α β = 0 := by
      simp only [QBilin, gBox_eq_empty_of_neg hRwneg, Finset.sum_empty]
    rw [hz0, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg (by nlinarith) _)) hLnn
  -- main case: 0 ≤ Rz, 0 ≤ Rw
  have hmain : QBilin Rw Rz α β
      = ∑ w ∈ wSupp Rw α,
          α w * (∑ z ∈ Work.FIPlan.gBox Rz, β z * ((DirichletSym w z : ℤ) : ℂ)) :=
    QBilin_eq_filter_mul
  have hinner : ∀ w ∈ wSupp Rw α,
      α w * (∑ z ∈ Work.FIPlan.gBox Rz, β z * ((DirichletSym w z : ℤ) : ℂ))
        = (∑ c ∈ cSet Rz β, ∑ z' ∈ Work.FIPlan.gBox (ppBox Rz),
              alphaC c α w * betaC Rz c β z' * ((DirichletSym w z' : ℤ) : ℂ))
          + α w * β 0 * ((DirichletSym w 0 : ℤ) : ℂ) := by
    intro w hw
    obtain ⟨-, hαw⟩ := mem_wSupp.mp hw
    obtain ⟨hprim, hcop, -⟩ := hαsupp w hαw
    have hPP : Prop213Aux.IsPP w := ⟨hprim, hcop⟩
    have hin : (∑ z ∈ Work.FIPlan.gBox Rz, β z * ((DirichletSym w z : ℤ) : ℂ))
        = (∑ c ∈ cSet Rz β, ((DirichletSym w c : ℤ) : ℂ) *
              ∑ z' ∈ Work.FIPlan.gBox (ppBox Rz),
                betaC Rz c β z' * ((DirichletSym w z' : ℤ) : ℂ))
          + β 0 * ((DirichletSym w 0 : ℤ) : ℂ) := by
      rw [sum_box_eq_sum_ne_zero_add hRz (fun z => β z * ((DirichletSym w z : ℤ) : ℂ))]
      congr 1
      rw [fiber_split hPP]
      refine Finset.sum_congr rfl fun c _ => ?_
      exact class_sum_eq hPP
        (fun z hz => ppPart_mem_ppBox hRz (mem_zClass.mp hz).1 (mem_zClass.mp hz).2.1)
    rw [hin, mul_add]
    congr 1
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← mul_assoc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z' _ => ?_
      rw [alphaC]
      ring
    · ring
  have hQ2 : QBilin Rw Rz α β
      = (∑ c ∈ cSet Rz β, QBilin Rw (ppBox Rz) (alphaC c α) (betaC Rz c β))
        + (∑ w ∈ wSupp Rw α, α w * β 0 * ((DirichletSym w 0 : ℤ) : ℂ)) := by
    have hA : QBilin Rw Rz α β
        = (∑ c ∈ cSet Rz β, ∑ w ∈ wSupp Rw α, ∑ z' ∈ Work.FIPlan.gBox (ppBox Rz),
              alphaC c α w * betaC Rz c β z' * ((DirichletSym w z' : ℤ) : ℂ))
          + (∑ w ∈ wSupp Rw α, α w * β 0 * ((DirichletSym w 0 : ℤ) : ℂ)) := by
      rw [hmain, Finset.sum_congr rfl hinner, Finset.sum_add_distrib, Finset.sum_comm]
    rw [hA]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [QBilin]
    exact Finset.sum_subset (wSupp_subset) (fun w hw hwnot => by
      have hz : α w = 0 := by
        by_contra hc
        exact hwnot (mem_wSupp.mpr ⟨hw, hc⟩)
      have hα0 : alphaC c α w = 0 := by rw [alphaC, hz, zero_mul]
      refine Finset.sum_eq_zero fun z' _ => ?_
      rw [hα0, zero_mul, zero_mul])
  -- the z = 0 term
  have hzterm : ‖∑ w ∈ wSupp Rw α, α w * β 0 * ((DirichletSym w 0 : ℤ) : ℂ)‖ ≤ 1 := by
    have hext : (∑ w ∈ wSupp Rw α, α w * β 0 * ((DirichletSym w 0 : ℤ) : ℂ))
        = ∑ w ∈ Work.FIPlan.gBox Rw, α w * β 0 * ((DirichletSym w 0 : ℤ) : ℂ) := by
      refine Finset.sum_subset (wSupp_subset) ?_
      intro w hw hwnot
      have hz : α w = 0 := by
        by_contra hc
        exact hwnot (mem_wSupp.mpr ⟨hw, hc⟩)
      rw [hz, zero_mul, zero_mul]
    rw [hext]
    have h := zeroTerm_bound (Rw := Rw) (α := α) (β 0) hα1 (fun w hw => (hαsupp w hw).1)
    have hβ0 : ‖β 0‖ ≤ 1 := hβ1 0
    linarith
  -- per class bound
  have hclass : ∀ c ∈ cSet Rz β,
      ‖QBilin Rw (ppBox Rz) (alphaC c α) (betaC Rz c β)‖
        ≤ 3 * C2 * (M ^ ((11 : ℝ) / 12) * (N / (Work.FIPlan.gnorm c : ℝ))
              + (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((11 : ℝ) / 12) * M)
            * (Real.log (M * N + 2)) ^ A2 := by
    intro c hc
    obtain ⟨z0, hz0, hz0c⟩ := mem_cSet.mp hc
    obtain ⟨-, hz0ne, hz0β⟩ := mem_zSupp.mp hz0
    have hgcN : (Work.FIPlan.gnorm c : ℝ) ≤ N := by
      have h1 : Work.FIPlan.gnorm (cPart z0) ≤ Work.FIPlan.gnorm z0 := by
        rw [← gnorm_cPart_mul_ppPart hz0ne]
        exact Nat.le_mul_of_pos_right _ (lt_of_lt_of_le zero_lt_one (one_le_gnorm_ppPart hz0ne))
      rw [hz0c] at h1
      exact le_trans (by exact_mod_cast h1) (hβsupp z0 hz0β)
    have hcne : c ≠ 0 := by rw [← hz0c]; exact ne_zero_cPart hz0ne
    have hgcpos : (0 : ℝ) < (Work.FIPlan.gnorm c : ℝ) := by
      have h := Work.FIArea7.gnorm_pos_of_ne_zero hcne
      exact_mod_cast h
    have hgc1 : (1 : ℝ) ≤ (Work.FIPlan.gnorm c : ℝ) := by
      have h := Nat.one_le_iff_ne_zero.mpr (fun h0 => hcne (Work.FIArea7.gnorm_eq_zero_iff.mp h0))
      exact_mod_cast h
    have hNc1 : 1 ≤ N / (Work.FIPlan.gnorm c : ℝ) := by
      rw [le_div_iff₀ hgcpos]
      linarith
    have hMg0 : (0 : ℝ) ≤ M * (N / (Work.FIPlan.gnorm c : ℝ)) :=
      mul_nonneg (by linarith) (div_nonneg (by linarith) (le_of_lt hgcpos))
    have hlog : (Real.log (M * (N / (Work.FIPlan.gnorm c : ℝ)) + 2)) ^ A2
        ≤ (Real.log (M * N + 2)) ^ A2 :=
      Real.rpow_le_rpow (Real.log_nonneg (by linarith))
        (log_ratio_le hgc1 (by linarith) (by linarith)) hA2.le
    have hβcPP : ∀ z', betaC Rz c β z' ≠ 0 → Prop213Aux.IsPP z' := fun z' h => betaC_pp h
    have hβcgn : ∀ z', betaC Rz c β z' ≠ 0 →
        (Work.FIPlan.gnorm z' : ℝ) ≤ N / (Work.FIPlan.gnorm c : ℝ) :=
      fun z' h => betaC_gnorm hβsupp hgcpos h
    have hβcblk : ∀ z', betaC Rz c β z' ≠ 0 →
        Work.FIPlan.IsPrimary z' ∧ IsCoprime z'.re z'.im ∧
          (Work.FIPlan.gnorm z' : ℝ) ≤ N / (Work.FIPlan.gnorm c : ℝ) :=
      fun z' h => ⟨(hβcPP z' h).1, (hβcPP z' h).2, hβcgn z' h⟩
    have hαcgn : ∀ w, alphaC c α w ≠ 0 → (Work.FIPlan.gnorm w : ℝ) ≤ M :=
      fun w hw => (alphaC_supp hαsupp w hw).2.2
    have hαcPP : ∀ w, alphaC c α w ≠ 0 → Prop213Aux.IsPP w :=
      fun w hw => ⟨(alphaC_supp hαsupp w hw).1, (alphaC_supp hαsupp w hw).2.1⟩
    have hDirect := hD2 M (N / (Work.FIPlan.gnorm c : ℝ)) Rw (ppBox Rz)
        (alphaC c α) (betaC Rz c β) hM hNc1 (alphaC_bound hα1) (betaC_bound hβ1)
        (alphaC_supp hαsupp) hβcgn
    have hTrans := hD2 (N / (Work.FIPlan.gnorm c : ℝ)) M (ppBox Rz) Rw
        (betaC Rz c β) (alphaC c α) hNc1 hM (betaC_bound hβ1) (alphaC_bound hα1)
        hβcblk hαcgn
    have hsw : QBilin (ppBox Rz) Rw (betaC Rz c β) (alphaC c α)
        = QBilin Rw (ppBox Rz) (alphaC c α) (betaC Rz c β) :=
      QBilin_recip hβcPP hαcPP
    rw [hsw] at hTrans
    rw [mul_comm (N / (Work.FIPlan.gnorm c : ℝ)) M] at hTrans
    have hDirect' : ‖QBilin Rw (ppBox Rz) (alphaC c α) (betaC Rz c β)‖
        ≤ C2 * (M ^ ((11 : ℝ) / 12) * (N / (Work.FIPlan.gnorm c : ℝ))
            + M ^ ((7 : ℝ) / 6) * (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((3 : ℝ) / 4)
            + M ^ ((4 : ℝ) / 3) * (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((1 : ℝ) / 2))
          * (Real.log (M * N + 2)) ^ A2 :=
      le_trans hDirect (mul_le_mul_of_nonneg_left hlog (by positivity))
    have hTrans' : ‖QBilin Rw (ppBox Rz) (alphaC c α) (betaC Rz c β)‖
        ≤ C2 * ((N / (Work.FIPlan.gnorm c : ℝ)) ^ ((11 : ℝ) / 12) * M
            + (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((7 : ℝ) / 6) * M ^ ((3 : ℝ) / 4)
            + (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((4 : ℝ) / 3) * M ^ ((1 : ℝ) / 2))
          * (Real.log (M * N + 2)) ^ A2 :=
      le_trans hTrans (mul_le_mul_of_nonneg_left hlog (by positivity))
    rcases le_total (N / (Work.FIPlan.gnorm c : ℝ)) M with hcase | hcase
    · have h3 : (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((11 : ℝ) / 12) * M
          + (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((7 : ℝ) / 6) * M ^ ((3 : ℝ) / 4)
          + (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((4 : ℝ) / 3) * M ^ ((1 : ℝ) / 2)
          ≤ 3 * (M ^ ((11 : ℝ) / 12) * (N / (Work.FIPlan.gnorm c : ℝ))
              + (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((11 : ℝ) / 12) * M) :=
        T_le hM hNc1 hcase
      refine le_trans hTrans' ?_
      calc C2 * ((N / (Work.FIPlan.gnorm c : ℝ)) ^ ((11 : ℝ) / 12) * M
            + (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((7 : ℝ) / 6) * M ^ ((3 : ℝ) / 4)
            + (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((4 : ℝ) / 3) * M ^ ((1 : ℝ) / 2))
            * (Real.log (M * N + 2)) ^ A2
          ≤ C2 * (3 * (M ^ ((11 : ℝ) / 12) * (N / (Work.FIPlan.gnorm c : ℝ))
              + (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((11 : ℝ) / 12) * M))
            * (Real.log (M * N + 2)) ^ A2 := scale_le h3 hC2.le hLnn
        _ = 3 * C2 * (M ^ ((11 : ℝ) / 12) * (N / (Work.FIPlan.gnorm c : ℝ))
              + (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((11 : ℝ) / 12) * M)
            * (Real.log (M * N + 2)) ^ A2 := by ring
    · have h3 : M ^ ((11 : ℝ) / 12) * (N / (Work.FIPlan.gnorm c : ℝ))
          + M ^ ((7 : ℝ) / 6) * (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((3 : ℝ) / 4)
          + M ^ ((4 : ℝ) / 3) * (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ 3 * (M ^ ((11 : ℝ) / 12) * (N / (Work.FIPlan.gnorm c : ℝ))
              + (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((11 : ℝ) / 12) * M) :=
        D_le hM hNc1 hcase
      refine le_trans hDirect' ?_
      calc C2 * (M ^ ((11 : ℝ) / 12) * (N / (Work.FIPlan.gnorm c : ℝ))
            + M ^ ((7 : ℝ) / 6) * (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((3 : ℝ) / 4)
            + M ^ ((4 : ℝ) / 3) * (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((1 : ℝ) / 2))
            * (Real.log (M * N + 2)) ^ A2
          ≤ C2 * (3 * (M ^ ((11 : ℝ) / 12) * (N / (Work.FIPlan.gnorm c : ℝ))
              + (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((11 : ℝ) / 12) * M))
            * (Real.log (M * N + 2)) ^ A2 := scale_le h3 hC2.le hLnn
        _ = 3 * C2 * (M ^ ((11 : ℝ) / 12) * (N / (Work.FIPlan.gnorm c : ℝ))
              + (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((11 : ℝ) / 12) * M)
            * (Real.log (M * N + 2)) ^ A2 := by ring
  -- the class sum
  have hCsetSub : cSet Rz β ⊆ CBox N := by
    intro c hc
    obtain ⟨z0, hz0, hz0c⟩ := mem_cSet.mp hc
    obtain ⟨-, hz0ne, hz0β⟩ := mem_zSupp.mp hz0
    refine mem_CBox_of_isC hN ?_ ?_
    · rw [← hz0c]; exact cPart_isC hz0ne
    · have h1 : Work.FIPlan.gnorm (cPart z0) ≤ Work.FIPlan.gnorm z0 := by
        rw [← gnorm_cPart_mul_ppPart hz0ne]
        exact Nat.le_mul_of_pos_right _ (lt_of_lt_of_le zero_lt_one (one_le_gnorm_ppPart hz0ne))
      rw [hz0c] at h1
      exact le_trans (by exact_mod_cast h1) (hβsupp z0 hz0β)
  have hsumInv : ∑ c ∈ cSet Rz β, ((Work.FIPlan.gnorm c : ℝ)) ^ (-(1 : ℝ)) ≤ K2 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hCsetSub
      (fun c _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hK2 N hN)
  have hsumPow : ∑ c ∈ cSet Rz β, ((Work.FIPlan.gnorm c : ℝ)) ^ (-((11 : ℝ) / 12)) ≤ K1 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hCsetSub
      (fun c _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hK1 N hN)
  have hpos_of_mem : ∀ c ∈ cSet Rz β, (0 : ℝ) < (Work.FIPlan.gnorm c : ℝ) := by
    intro c hc
    obtain ⟨z0, hz0, hz0c⟩ := mem_cSet.mp hc
    obtain ⟨-, hz0ne, -⟩ := mem_zSupp.mp hz0
    have hcne : c ≠ 0 := by rw [← hz0c]; exact ne_zero_cPart hz0ne
    have h := Work.FIArea7.gnorm_pos_of_ne_zero hcne
    exact_mod_cast h
  have hcore : ∑ c ∈ cSet Rz β,
        (M ^ ((11 : ℝ) / 12) * (N / (Work.FIPlan.gnorm c : ℝ))
          + (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((11 : ℝ) / 12) * M)
      ≤ (K1 + K2) * (M ^ ((11 : ℝ) / 12) * N + M * N ^ ((11 : ℝ) / 12)) := by
    have e1 : ∀ c ∈ cSet Rz β,
        M ^ ((11 : ℝ) / 12) * (N / (Work.FIPlan.gnorm c : ℝ))
          = M ^ ((11 : ℝ) / 12) * N * ((Work.FIPlan.gnorm c : ℝ)) ^ (-(1 : ℝ)) := by
      intro c _
      rw [div_eq_mul_inv, Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_one]
      ring
    have e2 : ∀ c ∈ cSet Rz β,
        (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((11 : ℝ) / 12) * M
          = M * N ^ ((11 : ℝ) / 12) * ((Work.FIPlan.gnorm c : ℝ)) ^ (-((11 : ℝ) / 12)) := by
      intro c hc
      rw [div_rpow_eq (N := N) (g := (Work.FIPlan.gnorm c : ℝ)) (hpos_of_mem c hc)
        (by linarith : (0 : ℝ) ≤ N)]
      ring
    rw [Finset.sum_add_distrib, Finset.sum_congr rfl e1, Finset.sum_congr rfl e2,
      ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 : M ^ ((11 : ℝ) / 12) * N
          * (∑ c ∈ cSet Rz β, ((Work.FIPlan.gnorm c : ℝ)) ^ (-(1 : ℝ)))
        ≤ M ^ ((11 : ℝ) / 12) * N * K2 :=
      mul_le_mul_of_nonneg_left hsumInv
        (mul_nonneg (Real.rpow_nonneg (by linarith) _) (by linarith))
    have h2 : M * N ^ ((11 : ℝ) / 12)
          * (∑ c ∈ cSet Rz β, ((Work.FIPlan.gnorm c : ℝ)) ^ (-((11 : ℝ) / 12)))
        ≤ M * N ^ ((11 : ℝ) / 12) * K1 :=
      mul_le_mul_of_nonneg_left hsumPow
        (mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _))
    have hA : (0 : ℝ) ≤ M ^ ((11 : ℝ) / 12) * N :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _) (by linarith)
    have hB : (0 : ℝ) ≤ M * N ^ ((11 : ℝ) / 12) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _)
    nlinarith [h1, h2, hA, hB, hK1nn, hK2nn]
  -- assemble
  have hsumClasses : ∑ c ∈ cSet Rz β, ‖QBilin Rw (ppBox Rz) (alphaC c α) (betaC Rz c β)‖
      ≤ 3 * C2 * ((K1 + K2) * (M ^ ((11 : ℝ) / 12) * N + M * N ^ ((11 : ℝ) / 12)))
          * (Real.log (M * N + 2)) ^ A2 := by
    refine le_trans (Finset.sum_le_sum hclass) ?_
    have hstep : ∑ c ∈ cSet Rz β, 3 * C2 *
          (M ^ ((11 : ℝ) / 12) * (N / (Work.FIPlan.gnorm c : ℝ))
            + (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((11 : ℝ) / 12) * M)
          * (Real.log (M * N + 2)) ^ A2
        = 3 * C2 * (Real.log (M * N + 2)) ^ A2
          * ∑ c ∈ cSet Rz β, (M ^ ((11 : ℝ) / 12) * (N / (Work.FIPlan.gnorm c : ℝ))
            + (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((11 : ℝ) / 12) * M) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [hstep]
    calc 3 * C2 * (Real.log (M * N + 2)) ^ A2
          * (∑ c ∈ cSet Rz β, (M ^ ((11 : ℝ) / 12) * (N / (Work.FIPlan.gnorm c : ℝ))
            + (N / (Work.FIPlan.gnorm c : ℝ)) ^ ((11 : ℝ) / 12) * M))
        ≤ 3 * C2 * (Real.log (M * N + 2)) ^ A2
          * ((K1 + K2) * (M ^ ((11 : ℝ) / 12) * N + M * N ^ ((11 : ℝ) / 12))) :=
          mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = 3 * C2 * ((K1 + K2) * (M ^ ((11 : ℝ) / 12) * N + M * N ^ ((11 : ℝ) / 12)))
          * (Real.log (M * N + 2)) ^ A2 := by ring
  -- final estimate
  rw [hQ2]
  refine le_trans (norm_add_le _ _) ?_
  have hz : ‖∑ w ∈ wSupp Rw α, α w * β 0 * ((DirichletSym w 0 : ℤ) : ℂ)‖ ≤ 1 := hzterm
  have hb1 : ‖∑ c ∈ cSet Rz β, QBilin Rw (ppBox Rz) (alphaC c α) (betaC Rz c β)‖
      ≤ 3 * C2 * ((K1 + K2) * (M ^ ((11 : ℝ) / 12) * N + M * N ^ ((11 : ℝ) / 12)))
          * (Real.log (M * N + 2)) ^ A2 :=
    le_trans (norm_sum_le _ _) hsumClasses
  have hcross := cross_le hM hN
  have hK12 : (0 : ℝ) ≤ K1 + K2 := by linarith
  have h6 : 3 * C2 * ((K1 + K2) * (M ^ ((11 : ℝ) / 12) * N + M * N ^ ((11 : ℝ) / 12)))
        * (Real.log (M * N + 2)) ^ A2
      ≤ 6 * C2 * (K1 + K2)
        * ((M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12))
        * (Real.log (M * N + 2)) ^ A2 := by
    have h1 : (K1 + K2) * (M ^ ((11 : ℝ) / 12) * N + M * N ^ ((11 : ℝ) / 12))
        ≤ (K1 + K2) * (2 * ((M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12))) :=
      mul_le_mul_of_nonneg_left hcross hK12
    calc 3 * C2 * ((K1 + K2) * (M ^ ((11 : ℝ) / 12) * N + M * N ^ ((11 : ℝ) / 12)))
          * (Real.log (M * N + 2)) ^ A2
        ≤ 3 * C2 * ((K1 + K2) * (2 * ((M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12))))
          * (Real.log (M * N + 2)) ^ A2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) hLnn
      _ = 6 * C2 * (K1 + K2)
            * ((M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12))
            * (Real.log (M * N + 2)) ^ A2 := by ring
  have hgoal : (6 * C2 * (K1 + K2) + 1) * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)
        * (Real.log (M * N + 2)) ^ A2
      = 6 * C2 * (K1 + K2) * ((M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12))
          * (Real.log (M * N + 2)) ^ A2
        + ((M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12))
          * (Real.log (M * N + 2)) ^ A2 := by ring
  have hSL : (1 : ℝ) ≤ ((M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12))
      * (Real.log (M * N + 2)) ^ A2 := one_le_tail hM hN hA2
  rw [hgoal]
  linarith [hb1, hz, h6, hSL]

end

end Work.FIArea7.Pub213
