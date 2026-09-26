import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.KPlus_slash_bound_half

namespace Work.CKFinal.LineDecay

open UpperHalfPlane MeasureTheory
open scoped Topology Manifold

noncomputable section

/-- Pure real-arithmetic assembly for the segment decay of `K_±^{(8)}`: given the slashed-kernel
estimate at `(τ, z)` (with `z.im = zi ≥ 0`, `‖z‖ = zc ∈ [0,1]`, `‖τ‖ = tn`, `1+tn ≤ 3y`,
`y = Im τ ≥ 1`), the divisor lower bound `c·e^{2πy} ≤ D` and `D > 0`, the product is bounded by
`4·C·6^A/c · y^N e^{-πy}` for any `N ≥ A`. -/
private lemma segment_scalar_chain_priv {C A c y D tn zc zi N : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hc : 0 < c) (hy1 : 1 ≤ y) (hD : 0 < D) (hDlb : c * Real.exp (2 * Real.pi * y) ≤ D)
    (htn0 : 0 ≤ 1 + tn) (htn : 1 + tn ≤ 3 * y) (hzc0 : 0 ≤ zc) (hzc1 : zc ≤ 1)
    (hzi : 0 ≤ zi) (hAN : A ≤ N) :
    4 * (C * (1 + tn) ^ A * (1 + zc) ^ A * Real.exp (-(Real.pi * zi)) / D)
      ≤ 4 * C * 6 ^ A / c * y ^ N * Real.exp (-(Real.pi * y)) := by
  have hDpos : (0 : ℝ) < c * Real.exp (2 * Real.pi * y) := by positivity
  have hinvD : D⁻¹ ≤ Real.exp (-(2 * Real.pi * y)) / c := by
    have h1 : (1 : ℝ) / D ≤ Real.exp (-(2 * Real.pi * y)) / c := by
      have h2 : (1 : ℝ) / D ≤ 1 / (c * Real.exp (2 * Real.pi * y)) :=
        one_div_le_one_div_of_le hDpos hDlb
      have h3 : 1 / (c * Real.exp (2 * Real.pi * y))
          = Real.exp (-(2 * Real.pi * y)) / c := by
        rw [one_div, Real.exp_neg]
        field_simp
      rwa [h3] at h2
    rwa [one_div] at h1
  have hAB : (1 + tn) ^ A * (1 + zc) ^ A ≤ 6 ^ A * y ^ A := by
    have h2 : (1 + tn) ^ A ≤ (3 * y) ^ A := Real.rpow_le_rpow htn0 htn hA
    have h3 : (1 + zc) ^ A ≤ 2 ^ A := Real.rpow_le_rpow (by linarith) (by linarith) hA
    have h4 : (0 : ℝ) ≤ (1 + zc) ^ A := Real.rpow_nonneg (by linarith) A
    have h5 : (0 : ℝ) ≤ (3 * y) ^ A := Real.rpow_nonneg (by linarith) A
    calc (1 + tn) ^ A * (1 + zc) ^ A ≤ (3 * y) ^ A * 2 ^ A := mul_le_mul h2 h3 h4 h5
      _ = 6 ^ A * y ^ A := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]
          rw [show (3 : ℝ) ^ A * y ^ A * 2 ^ A = (3 ^ A * 2 ^ A) * y ^ A by ring]
          rw [← Real.mul_rpow (by norm_num) (by norm_num), show (3 : ℝ) * 2 = 6 by norm_num]
  have hE : Real.exp (-(Real.pi * zi)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos]
  have hnum : C * (1 + tn) ^ A * (1 + zc) ^ A * Real.exp (-(Real.pi * zi))
      ≤ C * 6 ^ A * y ^ A := by
    calc C * (1 + tn) ^ A * (1 + zc) ^ A * Real.exp (-(Real.pi * zi))
        = C * ((1 + tn) ^ A * (1 + zc) ^ A) * Real.exp (-(Real.pi * zi)) := by ring
      _ ≤ C * (6 ^ A * y ^ A) * 1 := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hAB hC
          · exact hE
          · positivity
          · positivity
      _ = C * 6 ^ A * y ^ A := by ring
  have hdiv : C * (1 + tn) ^ A * (1 + zc) ^ A * Real.exp (-(Real.pi * zi)) / D
      ≤ (C * 6 ^ A * y ^ A) * (Real.exp (-(2 * Real.pi * y)) / c) := by
    calc C * (1 + tn) ^ A * (1 + zc) ^ A * Real.exp (-(Real.pi * zi)) / D
        ≤ (C * 6 ^ A * y ^ A) / D := div_le_div_of_nonneg_right hnum hD.le
      _ ≤ (C * 6 ^ A * y ^ A) * (Real.exp (-(2 * Real.pi * y)) / c) :=
          mul_le_mul_of_nonneg_left hinvD (by positivity)
  have hyAN : y ^ A * Real.exp (-(2 * Real.pi * y)) ≤ y ^ N * Real.exp (-(Real.pi * y)) := by
    have h1 : y ^ A ≤ y ^ N := Real.rpow_le_rpow_of_exponent_le hy1 hAN
    have h2 : Real.exp (-(2 * Real.pi * y)) ≤ Real.exp (-(Real.pi * y)) := by
      rw [Real.exp_le_exp]; nlinarith [Real.pi_pos]
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  calc 4 * (C * (1 + tn) ^ A * (1 + zc) ^ A * Real.exp (-(Real.pi * zi)) / D)
      ≤ 4 * ((C * 6 ^ A * y ^ A) * (Real.exp (-(2 * Real.pi * y)) / c)) :=
        mul_le_mul_of_nonneg_left hdiv (by norm_num)
    _ = 4 * C * 6 ^ A / c * (y ^ A * Real.exp (-(2 * Real.pi * y))) := by ring
    _ ≤ 4 * C * 6 ^ A / c * (y ^ N * Real.exp (-(Real.pi * y))) :=
        mul_le_mul_of_nonneg_left hyAN (by positivity)
    _ = 4 * C * 6 ^ A / c * y ^ N * Real.exp (-(Real.pi * y)) := by ring

/-- `S` is an involution on `ℍ`. -/
private lemma S_smul_S_smul_aux (w : ℍ) : ModularGroup.S • (ModularGroup.S • w) = w := by
  apply UpperHalfPlane.ext
  rw [Work.Kernels.S_smul_coe, Work.Kernels.S_smul_coe]
  have hw : (w : ℂ) ≠ 0 := fun h => w.im_ne_zero (by rw [← UpperHalfPlane.coe_im w, h]; simp)
  field_simp

/-- `Im (S • w) = w.im / ‖w‖²`. -/
private lemma im_S_smul_aux (w : ℍ) : (ModularGroup.S • w).im = w.im / ‖(w : ℂ)‖ ^ 2 := by
  rw [← UpperHalfPlane.coe_im, Work.Kernels.S_smul_coe, Complex.neg_im, Complex.inv_im,
    Complex.normSq_eq_norm_sq, UpperHalfPlane.coe_im]
  ring

/-- `‖S • w‖ = 1/‖w‖`. -/
private lemma norm_S_smul_aux (w : ℍ) : ‖((ModularGroup.S • w : ℍ) : ℂ)‖ = 1 / ‖(w : ℂ)‖ := by
  rw [Work.Kernels.S_smul_coe, norm_neg, norm_inv, one_div]

/-- Assembly lemma: from (i) the CKMRV half-region quotient bounds for `K_+^{(8)}`
(available as `Work.Asymptotics.KPlus_slash_bound_half`, used internally) and for `K_-^{(8)}`
(the hypothesis `hminus`), and (ii) the lower bound `hD` for the divisor `Δ(S•w)(jτ - j(S•w))`,
the two kernels `K_±^{(8)}` are `O(y^N e^{-π y})` on the segment `{Im w = 1, |Re w| ≤ 1}`,
uniformly in the parameter `x = Re w`, for `τ` on the lines `Re τ = ±1/2`.

Route: `τ` on the lines with `Im τ ≥ 1` lies in `Work.Asymptotics.DomainD`; put `z := S • w`
(so `S • z = w`, `Im z = 1/‖w‖² ∈ [1/2,1]`, `‖z‖ ≤ 1`); the two quotient bounds give
`‖z²K_±(τ,w)‖ ≤ C(1+‖τ‖)^A 2^A e^{-π Im z}/‖Δ z (j τ - j z)‖`, and `hD` makes the denominator
factor `≤ e^{-2π Im τ}/c`; finally `‖z²‖ ≥ 1/2` and `(1+‖τ‖) ≤ 3 Im τ` convert this into
`C' (Im τ)^N e^{-π Im τ}` (with `N := max A A₋`). -/
theorem P2_kernel_segment_of (ℓ : Work.Kernels.LogLambdaData) (Cm Am : ℝ) (hCm : 0 ≤ Cm)
    (hAm : 0 ≤ Am)
    (hminus : ∀ (τ z : UpperHalfPlane), τ ∈ Work.Asymptotics.DomainD → (1 : ℝ) / 2 ≤ τ.im →
        (1 : ℝ) / 3 ≤ z.im →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
        ‖(z : ℂ) ^ 2 * Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • z)‖
          ≤ Cm * (1 + ‖(τ : ℂ)‖) ^ Am * (1 + ‖(z : ℂ)‖) ^ Am
              * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖)
    (c Y₀ : ℝ) (hc : 0 < c)
    (hD : ∀ (τ w : UpperHalfPlane), (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im →
        w.im = 1 → |w.re| ≤ 1 →
        c * Real.exp (2 * Real.pi * τ.im)
          ≤ ‖Work.Kernels.DeltaFun (ModularGroup.S • w)
              * (Work.Kernels.jInvariantFun τ
                  - Work.Kernels.jInvariantFun (ModularGroup.S • w))‖) :
    ∃ C N Y₁ : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ 1 ≤ Y₁ ∧
      ∀ (τ : UpperHalfPlane) (x : ℝ), (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₁ ≤ τ.im →
        |x| ≤ 1 →
        max ‖Work.CKFinal.Kax (Work.Kernels.KPlus 8) τ x 1‖
            ‖Work.CKFinal.Kax (Work.Kernels.KMinus ℓ 8) τ x 1‖
          ≤ C * τ.im ^ N * Real.exp (-(Real.pi * τ.im)) := by
  obtain ⟨Cp, Ap, hCppos, hAp, hplus⟩ :=
    Work.Asymptotics.KPlus_slash_bound_half 8 (Or.inl rfl)
  have hCp : (0 : ℝ) ≤ Cp := hCppos.le
  refine ⟨4 * max (Cp * 6 ^ Ap) (Cm * 6 ^ Am) / c + 1, max Ap Am + 1, max Y₀ 1,
    ?_, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · exact le_max_right Y₀ 1
  · intro τ x hre hy hx
    have hy1 : (1 : ℝ) ≤ τ.im := le_trans (le_max_right Y₀ 1) hy
    have hyY₀ : Y₀ ≤ τ.im := le_trans (le_max_left Y₀ 1) hy
    have hτ12 : (1 : ℝ) / 2 ≤ τ.im := by linarith
    have h1pos : (0 : ℝ) < 1 := by norm_num
    -- the point `w = x + i` of the segment
    set w : ℍ := (x : ℝ) +ᵥ Work.Kernels.imagAxis 1 h1pos with hwdef
    have hwim : w.im = 1 := by
      rw [hwdef, ← UpperHalfPlane.coe_im, UpperHalfPlane.coe_vadd]
      simp [Work.Kernels.imagAxis]
    have hwre : w.re = x := by
      rw [hwdef, ← UpperHalfPlane.coe_re, UpperHalfPlane.coe_vadd]
      simp [Work.Kernels.imagAxis]
    have hwnormSq : ‖(w : ℂ)‖ ^ 2 = x ^ 2 + 1 := by
      rw [hwdef, UpperHalfPlane.coe_vadd]
      simp only [Work.Kernels.imagAxis, UpperHalfPlane.coe_mk]
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [Complex.add_re, Complex.add_im]
      ring
    have hxabs : x ^ 2 ≤ 1 := by
      have h := abs_le.mp hx
      nlinarith [h.1, h.2]
    have hwnormSq_le : ‖(w : ℂ)‖ ^ 2 ≤ 2 := by rw [hwnormSq]; linarith
    have hwnormSq_ge : (1 : ℝ) ≤ ‖(w : ℂ)‖ ^ 2 := by rw [hwnormSq]; nlinarith [sq_nonneg x]
    have hwn_le : ‖(w : ℂ)‖ ≤ 2 := by
      have h := Complex.norm_le_abs_re_add_abs_im (w : ℂ)
      rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hwre, hwim, abs_one] at h
      linarith
    have hwn_ge : (1 : ℝ) ≤ ‖(w : ℂ)‖ := by
      have h := Complex.abs_im_le_norm (w : ℂ)
      rw [UpperHalfPlane.coe_im, hwim, abs_one] at h
      linarith
    have hwn_pos : (0 : ℝ) < ‖(w : ℂ)‖ := lt_of_lt_of_le one_pos hwn_ge
    -- the conjugate point `z = S • w`
    set z : ℍ := ModularGroup.S • w with hzdef
    have hSz : ModularGroup.S • z = w := by rw [hzdef]; exact S_smul_S_smul_aux w
    have hznorm : ‖(z : ℂ)‖ = 1 / ‖(w : ℂ)‖ := by rw [hzdef]; exact norm_S_smul_aux w
    have hzim : z.im = w.im / ‖(w : ℂ)‖ ^ 2 := by rw [hzdef]; exact im_S_smul_aux w
    have hzn_le : ‖(z : ℂ)‖ ≤ 1 := by
      rw [hznorm, div_le_one hwn_pos]
      exact hwn_ge
    have hzn_ge : (1 : ℝ) / 2 ≤ ‖(z : ℂ)‖ := by
      rw [hznorm, le_div_iff₀ hwn_pos]
      linarith
    have hzim_third : (1 : ℝ) / 3 ≤ z.im := by
      rw [hzim, hwim, le_div_iff₀ (by positivity : (0 : ℝ) < ‖(w : ℂ)‖ ^ 2)]
      linarith
    have hzim_le : z.im ≤ 1 := by
      rw [hzim, hwim, div_le_one (by positivity : (0 : ℝ) < ‖(w : ℂ)‖ ^ 2)]
      exact hwnormSq_ge
    have hzim_nn : (0 : ℝ) ≤ z.im := z.im_pos.le
    have hzn_nn : (0 : ℝ) ≤ ‖(z : ℂ)‖ := norm_nonneg _
    -- `τ` lies in the CKMRV domain
    have hDmem : τ ∈ Work.Asymptotics.DomainD := by
      rw [Work.Asymptotics.mem_DomainD]
      have hb1 : (1 : ℝ) / 2 < ‖(τ : ℂ) - (1 / 2 : ℂ)‖ := by
        have h := Complex.abs_im_le_norm ((τ : ℂ) - (1 / 2 : ℂ))
        rw [Complex.sub_im, UpperHalfPlane.coe_im,
          show ((1 / 2 : ℂ)).im = 0 by norm_num, sub_zero, abs_of_pos τ.im_pos] at h
        linarith
      have hb2 : (1 : ℝ) / 2 < ‖(τ : ℂ) + (1 / 2 : ℂ)‖ := by
        have h := Complex.abs_im_le_norm ((τ : ℂ) + (1 / 2 : ℂ))
        rw [Complex.add_im, UpperHalfPlane.coe_im,
          show ((1 / 2 : ℂ)).im = 0 by norm_num, add_zero, abs_of_pos τ.im_pos] at h
        linarith
      rcases hre with h | h
      · exact ⟨by rw [h]; norm_num, by rw [h]; norm_num, hb1, hb2⟩
      · exact ⟨by rw [h]; norm_num, by rw [h]; norm_num, hb1, hb2⟩
    -- the divisor lower bound
    set D : ℝ := ‖Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ with hDdef
    have hDval : c * Real.exp (2 * Real.pi * τ.im) ≤ D := by
      have h := hD τ w hre hyY₀ hwim (by rw [hwre]; exact hx)
      rw [← hzdef] at h
      rw [hDdef]
      exact h
    have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hDval
    have hne : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
      have hz0 : Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) ≠ 0 := by
        rw [hDdef] at hDpos
        exact norm_ne_zero_iff.mp (ne_of_gt hDpos)
      exact sub_ne_zero.mp (right_ne_zero_of_mul hz0)
    -- `(1 + ‖τ‖) ≤ 3 Im τ`
    have hτnorm : 1 + ‖(τ : ℂ)‖ ≤ 3 * τ.im := by
      have h := Complex.norm_le_abs_re_add_abs_im (τ : ℂ)
      rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, abs_of_pos τ.im_pos] at h
      have hre' : |τ.re| ≤ 1 / 2 := by rcases hre with hh | hh <;> rw [hh] <;> norm_num
      linarith
    -- the two slashed-kernel bounds
    have hplus_z := hplus τ z hDmem hτ12 hzim_third hne
    rw [show (((8 : ℕ) : ℤ) / 2 - 2) = (2 : ℤ) by norm_num, zpow_ofNat] at hplus_z
    have hminus_z := hminus τ z hDmem hτ12 hzim_third hne
    have hplus_z' : ‖(z : ℂ) ^ 2 * Work.Kernels.KPlus 8 τ (ModularGroup.S • z)‖
        ≤ Cp * (1 + ‖(τ : ℂ)‖) ^ Ap * (1 + ‖(z : ℂ)‖) ^ Ap
            * Real.exp (-(Real.pi * z.im)) / D := by
      have hge : (1 : ℝ) ≤ (1 + ‖(z : ℂ)‖) ^ Ap :=
        Real.one_le_rpow (by linarith [norm_nonneg (z : ℂ)]) hAp
      refine le_trans hplus_z (div_le_div_of_nonneg_right ?_ hDpos.le)
      have hX0 : (0 : ℝ) ≤ Cp * (1 + ‖(τ : ℂ)‖) ^ Ap * Real.exp (-(Real.pi * z.im)) := by
        positivity
      calc Cp * (1 + ‖(τ : ℂ)‖) ^ Ap * Real.exp (-(Real.pi * z.im))
          = Cp * (1 + ‖(τ : ℂ)‖) ^ Ap * Real.exp (-(Real.pi * z.im)) * 1 := by ring
        _ ≤ Cp * (1 + ‖(τ : ℂ)‖) ^ Ap * Real.exp (-(Real.pi * z.im))
              * (1 + ‖(z : ℂ)‖) ^ Ap := mul_le_mul_of_nonneg_left hge hX0
        _ = Cp * (1 + ‖(τ : ℂ)‖) ^ Ap * (1 + ‖(z : ℂ)‖) ^ Ap
              * Real.exp (-(Real.pi * z.im)) := by ring
    -- the generic conversion from a slashed bound to a pointwise bound
    have hgen : ∀ (K : ℍ → ℍ → ℂ) (Ck Ak : ℝ), 0 ≤ Ck → 0 ≤ Ak → Ak ≤ max Ap Am + 1 →
        ‖(z : ℂ) ^ 2 * K τ (ModularGroup.S • z)‖
          ≤ Ck * (1 + ‖(τ : ℂ)‖) ^ Ak * (1 + ‖(z : ℂ)‖) ^ Ak
              * Real.exp (-(Real.pi * z.im)) / D →
        ‖K τ (ModularGroup.S • z)‖
          ≤ 4 * Ck * 6 ^ Ak / c * τ.im ^ (max Ap Am + 1)
              * Real.exp (-(Real.pi * τ.im)) := by
      intro K Ck Ak hCk hAk hAkle hsla
      have h4 : ‖K τ (ModularGroup.S • z)‖ ≤ 4 * ‖(z : ℂ) ^ 2 * K τ (ModularGroup.S • z)‖ := by
        have hz2 : (1 / 4 : ℝ) ≤ ‖(z : ℂ)‖ ^ 2 := by
          nlinarith [hzn_ge, norm_nonneg (z : ℂ)]
        have h := mul_le_mul_of_nonneg_right hz2 (norm_nonneg (K τ (ModularGroup.S • z)))
        have hnorm : ‖(z : ℂ) ^ 2 * K τ (ModularGroup.S • z)‖
            = ‖(z : ℂ)‖ ^ 2 * ‖K τ (ModularGroup.S • z)‖ := by rw [norm_mul, norm_pow]
        rw [hnorm]
        nlinarith [h]
      have hsc := segment_scalar_chain_priv (C := Ck) (A := Ak) (c := c) (y := τ.im) (D := D)
        (tn := ‖(τ : ℂ)‖) (zc := ‖(z : ℂ)‖) (zi := z.im) (N := max Ap Am + 1)
        hCk hAk hc hy1 hDpos hDval (by positivity) hτnorm hzn_nn hzn_le hzim_nn hAkle
      have hbridge : 4 * ‖(z : ℂ) ^ 2 * K τ (ModularGroup.S • z)‖
          ≤ 4 * Ck * 6 ^ Ak / c * τ.im ^ (max Ap Am + 1)
              * Real.exp (-(Real.pi * τ.im)) := by
        refine le_trans ?_ hsc
        exact mul_le_mul_of_nonneg_left hsla (by norm_num)
      exact le_trans h4 hbridge
    have hP := hgen (Work.Kernels.KPlus 8) Cp Ap hCp hAp (by linarith [le_max_left Ap Am])
      hplus_z'
    have hM := hgen (Work.Kernels.KMinus ℓ 8) Cm Am hCm hAm (by linarith [le_max_right Ap Am])
      hminus_z
    have hKaxP : Work.CKFinal.Kax (Work.Kernels.KPlus 8) τ x 1
        = Work.Kernels.KPlus 8 τ (ModularGroup.S • z) := by
      rw [Work.CKFinal.Kax, dif_pos h1pos]
      congr 1
      rw [hSz]
    have hKaxM : Work.CKFinal.Kax (Work.Kernels.KMinus ℓ 8) τ x 1
        = Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • z) := by
      rw [Work.CKFinal.Kax, dif_pos h1pos]
      congr 1
      rw [hSz]
    have hCbigP : 4 * Cp * 6 ^ Ap / c ≤ 4 * max (Cp * 6 ^ Ap) (Cm * 6 ^ Am) / c + 1 := by
      have h2 : 4 * Cp * 6 ^ Ap / c ≤ 4 * max (Cp * 6 ^ Ap) (Cm * 6 ^ Am) / c := by
        apply div_le_div_of_nonneg_right _ hc.le
        linarith [le_max_left (Cp * 6 ^ Ap) (Cm * 6 ^ Am)]
      linarith
    have hCbigM : 4 * Cm * 6 ^ Am / c ≤ 4 * max (Cp * 6 ^ Ap) (Cm * 6 ^ Am) / c + 1 := by
      have h2 : 4 * Cm * 6 ^ Am / c ≤ 4 * max (Cp * 6 ^ Ap) (Cm * 6 ^ Am) / c := by
        apply div_le_div_of_nonneg_right _ hc.le
        linarith [le_max_right (Cp * 6 ^ Ap) (Cm * 6 ^ Am)]
      linarith
    have hPb : ‖Work.CKFinal.Kax (Work.Kernels.KPlus 8) τ x 1‖
        ≤ (4 * max (Cp * 6 ^ Ap) (Cm * 6 ^ Am) / c + 1) * τ.im ^ (max Ap Am + 1)
            * Real.exp (-(Real.pi * τ.im)) := by
      rw [hKaxP]
      refine le_trans hP ?_
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg τ.im_pos.le _)
      exact hCbigP
    have hMb : ‖Work.CKFinal.Kax (Work.Kernels.KMinus ℓ 8) τ x 1‖
        ≤ (4 * max (Cp * 6 ^ Ap) (Cm * 6 ^ Am) / c + 1) * τ.im ^ (max Ap Am + 1)
            * Real.exp (-(Real.pi * τ.im)) := by
      rw [hKaxM]
      refine le_trans hM ?_
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg τ.im_pos.le _)
      exact hCbigM
    exact max_le hPb hMb

end

end Work.CKFinal.LineDecay
