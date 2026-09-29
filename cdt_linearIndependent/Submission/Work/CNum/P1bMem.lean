import Mathlib
import Submission.Work.CNum.PtC1bAux
import Submission.Work.CNum.ratIvMem
import Submission.Work.CNum.ExpISpec
import Submission.Work.CNum.MemIvS
import Submission.Work.CNum.NrmSpec

/-!
# `Work.CNum.P1bMem` — soundness of the fourth-arc radicand interval `P1b`

`P1b k = IvS (X1b k)` is meant to enclose `PR θ_k = √(2A(cos θ_k - γ))`, `θ_k = kπ/512`,
on the fourth arc `780 ≤ k ≤ 1024`.  The only mathematical content is the enclosure

`X1b k ∋ 2A·(cos θ_k - γ)`

(assembled from the table `expI k ∋ e^{i kπ/1024}`, the half-angle identity
`cos θ = cos²(θ/2) - sin²(θ/2)`, and the rational enclosures `2A = 791282/10000`,
`γ = 27559/395641`), the two finite side conditions `X1b_lo_nonneg`/`X1b_hi_lt` of `PtC1bAux`,
and the interval square-root soundness `MemIvS`.
-/

namespace Work.CNum

open Work.ANum

/-! ## Splitting the table entry into real and imaginary parts -/

/-- The half-angle table `expI k` encloses the real and imaginary parts of `e^{i kπ/1024}`. -/
lemma expI_re_im_mem {k : ℕ} (hk : k ≤ 1024) :
    (expI k).re.Mem (Real.cos ((k : ℝ) * Real.pi / 1024)) ∧
      (expI k).im.Mem (Real.sin ((k : ℝ) * Real.pi / 1024)) := by
  have hE0 := ExpISpec (k := k) hk
  have h' : Cpx.Mem (expI k)
      ((↑(Real.cos ((k : ℝ) * Real.pi / 1024)) : ℂ)
        + (↑(Real.sin ((k : ℝ) * Real.pi / 1024)) : ℂ) * Complex.I) := by
    have h := hE0
    rw [show Complex.I * ((k : ℂ) * Real.pi / 1024)
        = (((k : ℝ) * Real.pi / 1024 : ℝ) : ℂ) * Complex.I by push_cast; ring] at h
    rwa [Complex.exp_ofReal_mul_I] at h
  refine ⟨?_, ?_⟩
  · simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero] using h'.1
  · simpa only [Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add] using h'.2

/-! ## The intermediate intervals -/

/-- `cT1b k` encloses `cos θ_k`, `θ_k = kπ/512`, via the half-angle formula. -/
lemma cT1bMem_aux {k : ℕ} (hk : k ≤ 1024) :
    (cT1b k).Mem (Real.cos ((k : ℝ) * Real.pi / 512)) := by
  obtain ⟨hre, him⟩ := expI_re_im_mem hk
  have h1 := Iv.mem_sub (Iv.mem_sq hre) (Iv.mem_sq him)
  have key : Real.cos ((k : ℝ) * Real.pi / 512)
      = Real.cos ((k : ℝ) * Real.pi / 1024) * Real.cos ((k : ℝ) * Real.pi / 1024)
        - Real.sin ((k : ℝ) * Real.pi / 1024) * Real.sin ((k : ℝ) * Real.pi / 1024) := by
    have h := Real.cos_two_mul' ((k : ℝ) * Real.pi / 1024)
    rw [show 2 * ((k : ℝ) * Real.pi / 1024) = (k : ℝ) * Real.pi / 512 by ring] at h
    rw [h]; ring
  rwa [← key] at h1

/-- `X1b k` encloses the radicand `2A(cos θ_k - γ)`. -/
lemma X1bMem_aux {k : ℕ} (hk : k ≤ 1024) :
    (X1b k).Mem (2 * AR * (Real.cos ((k : ℝ) * Real.pi / 512) - gamR)) := by
  have hcos := cT1bMem_aux hk
  have ha : (ratIv 791282 10000).Mem ((791282 : ℝ) / 10000) := RatIvSpec (by norm_num)
  have ha2 : (2 : ℝ) * AR = 791282 / 10000 := by norm_num [AR, cR]
  have ha' : (ratIv 791282 10000).Mem (2 * AR) := by rw [ha2]; exact ha
  have hc0 : (ratIv 27559 395641).Mem ((27559 : ℝ) / 395641) := RatIvSpec (by norm_num)
  have hc : (ratIv 27559 395641).Mem gamR := by
    have hg : gamR = 27559 / 395641 := by norm_num [gamR, cR, AR]
    rw [hg]; exact hc0
  exact IvMSpec ha' (Iv.mem_sub hcos hc)

/-! ## The main statement -/

theorem P1bMem {k : ℕ} (h1 : 780 ≤ k) (h2 : k ≤ 1024) : (Work.CNum.P1b k).Mem (Work.CNum.PR ((k : ℝ) * Real.pi / 512)) := by
  have hX := X1bMem_aux h2
  have hlo : 0 ≤ m2r (X1b k).lo :=
    div_nonneg (by exact_mod_cast X1b_lo_nonneg h1 h2) SC_posR.le
  have h := MemIvS hX hlo (X1b_hi_lt h1 h2)
  simpa [P1b, PR] using h

end Work.CNum
