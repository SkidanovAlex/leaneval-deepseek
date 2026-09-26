import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Residues.ThetaEpt
import Submission.Work.Residues.ThetaExpansion
import Submission.Work.Residues.ThetaDecay
import Submission.Work.Asymptotics.E4Fun_sub_one_explicit
import Submission.Work.Asymptotics.E14Fun_sub_one_atom

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

/-- `‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖`, the two-fold triangle inequality. -/
private lemma norm_add_three_le (a b c : ℂ) : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  have h1 := norm_add_le (a + b) c
  have h2 := norm_add_le a b
  linarith

/-!
# Third-order vanishing at the cusp of the `z`-atom `E₁₄·𝓛_S + E₄³·V`

This file proves

  `‖E₁₄(z)·𝓛_S(z) + E₄(z)³·V(z)‖ ≤ C ‖e^{πiz}‖³`   for `Im z ≥ 1`,

the `d = 24` `z`-atom decay used in the control of the `K₋` funnel tails.  The two summands are
individually of size `‖e^{πiz}‖` at the cusp — `𝓛_S = log λ_S` and `V = θ₁₀⁴` both vanish to first
order there, with the *same* linear term — and the point is that the combination vanishes to
third order.

The mechanism is purely the two first-order cusp expansions together with the first-order
cusp expansion of `E₄³ - E₁₄`.  Writing `E = e^{πiz}` (so `‖q‖ = ‖E‖²`), the library gives

* `‖𝓛_S + 16E‖ ≤ C_L ‖E‖³`  (`Work.Residues.ThetaExpansion`),
* `‖V - 16E‖ ≤ C_V ‖E‖³`    (`Work.Residues.VFun_expansion`),
* `‖E₄ - 1‖ ≤ 20000 ‖q‖`, `‖E₆ - 1‖ ≤ C₆ ‖q‖`  (`E4Fun_sub_one_explicit`, `E6Fun_decay`),
* `‖E₁₄ - 1‖ ≤ C₁₄ ‖q‖`    (`E14Fun_sub_one_atom`),

whence `‖E₄³ - E₁₄‖ = ‖E₄²(E₄ - E₆)‖ ≤ C ‖q‖ = C ‖E‖²`.  The algebraic rearrangement

  `E₁₄·𝓛_S + E₄³·V = E₁₄·(𝓛_S + 16E) + 16E·(E₄³ - E₁₄) + E₄³·(V - 16E)`

then exhibits all three terms as `O(‖E‖³)`: the first through the `𝓛_S` expansion, the second
through `‖E‖·‖E₄³ - E₁₄‖ = O(‖E‖³)`, the third through the `V` expansion.
-/

theorem Ncz24zA_high (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
      ‖Work.Kernels.E14Fun z * ℓ.L_S z + Work.Kernels.E4Fun z ^ 3 * Work.Kernels.VFun z‖
        ≤ C * ‖Work.Residues.Ept z‖ ^ 3 := by
  obtain ⟨-, ⟨CV, hCV, hV⟩, -, hLSall⟩ := Work.Residues.ThetaExpansion
  obtain ⟨CLS, hCLS, hLS⟩ := hLSall ℓ
  obtain ⟨C14, hC14, h14⟩ := Work.Asymptotics.E14Fun_sub_one_atom
  obtain ⟨C6, hC6, h6⟩ := Work.Residues.E6Fun_decay
  refine ⟨(1 + C14) * CLS + 16 * (20001 ^ 2 * (20000 + C6)) + 20001 ^ 3 * CV,
    by positivity, fun z hz => ?_⟩
  -- basic facts about `t = ‖E(z)‖` and `‖q‖ = t²`
  have ht1 : ‖Work.Residues.Ept z‖ ≤ 1 := le_of_lt (Work.Residues.norm_Ept_lt_one z)
  have ht2 : ‖Work.Residues.Ept z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (Work.Residues.Ept z)]
  have hexp : Real.exp (-(2 * Real.pi * z.im)) = ‖Work.Residues.Ept z‖ ^ 2 := by
    rw [Work.Residues.norm_Ept, sq, ← Real.exp_add]
    congr 1
    ring
  have hq : ‖Work.Kernels.qParamFun z‖ = ‖Work.Residues.Ept z‖ ^ 2 := by
    rw [Work.Asymptotics.norm_qParamFun, hexp]
  -- the three third-order inputs
  have hLSz : ‖ℓ.L_S z + 16 * Work.Residues.Ept z‖ ≤ CLS * ‖Work.Residues.Ept z‖ ^ 3 := by
    simpa only [Work.Residues.Ept] using hLS z hz
  have hVz : ‖Work.Kernels.VFun z - 16 * Work.Residues.Ept z‖
      ≤ CV * ‖Work.Residues.Ept z‖ ^ 3 := by
    simpa only [Work.Residues.Ept] using hV z hz
  have hE4 : ‖Work.Kernels.E4Fun z - 1‖ ≤ 20000 * ‖Work.Residues.Ept z‖ ^ 2 := by
    have h := Work.Asymptotics.E4Fun_sub_one_explicit (w := z) hz
    rwa [hq] at h
  have hE6 : ‖Work.Kernels.E6Fun z - 1‖ ≤ C6 * ‖Work.Residues.Ept z‖ ^ 2 := by
    have h := h6 z hz
    rwa [hexp] at h
  have hE14 : ‖Work.Kernels.E14Fun z - 1‖ ≤ C14 * ‖Work.Residues.Ept z‖ ^ 2 := by
    have h := h14 z hz
    rwa [hq] at h
  -- boundedness of `E₄`, `E₁₄`
  have hE4b : ‖Work.Kernels.E4Fun z‖ ≤ 20001 := by
    have h := norm_add_le (Work.Kernels.E4Fun z - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at h
    nlinarith [hE4, ht2]
  have hE14b : ‖Work.Kernels.E14Fun z‖ ≤ 1 + C14 := by
    have h := norm_add_le (Work.Kernels.E14Fun z - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at h
    nlinarith [hE14, ht2, hC14]
  -- `E₄³ - E₁₄` is `O(‖E‖²)`
  have hE43 : ‖Work.Kernels.E4Fun z ^ 3 - Work.Kernels.E14Fun z‖
      ≤ (20001 ^ 2 * (20000 + C6)) * ‖Work.Residues.Ept z‖ ^ 2 := by
    have hE14eq : Work.Kernels.E14Fun z = Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z := rfl
    have hid : Work.Kernels.E4Fun z ^ 3 - Work.Kernels.E14Fun z
        = Work.Kernels.E4Fun z ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E6Fun z) := by
      rw [hE14eq]; ring
    rw [hid, norm_mul, norm_pow]
    have h46 : ‖Work.Kernels.E4Fun z - Work.Kernels.E6Fun z‖
        ≤ (20000 + C6) * ‖Work.Residues.Ept z‖ ^ 2 := by
      have h := norm_sub_le (Work.Kernels.E4Fun z - 1) (Work.Kernels.E6Fun z - 1)
      have he : (Work.Kernels.E4Fun z - 1) - (Work.Kernels.E6Fun z - 1)
          = Work.Kernels.E4Fun z - Work.Kernels.E6Fun z := by ring
      rw [he] at h
      linarith
    calc ‖Work.Kernels.E4Fun z‖ ^ 2 * ‖Work.Kernels.E4Fun z - Work.Kernels.E6Fun z‖
        ≤ 20001 ^ 2 * ((20000 + C6) * ‖Work.Residues.Ept z‖ ^ 2) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hE4b 2) h46 (norm_nonneg _)
            (by positivity)
      _ = (20001 ^ 2 * (20000 + C6)) * ‖Work.Residues.Ept z‖ ^ 2 := by ring
  -- the algebraic rearrangement
  have hmain : Work.Kernels.E14Fun z * ℓ.L_S z + Work.Kernels.E4Fun z ^ 3 * Work.Kernels.VFun z
      = Work.Kernels.E14Fun z * (ℓ.L_S z + 16 * Work.Residues.Ept z)
        + 16 * Work.Residues.Ept z
            * (Work.Kernels.E4Fun z ^ 3 - Work.Kernels.E14Fun z)
        + Work.Kernels.E4Fun z ^ 3
            * (Work.Kernels.VFun z - 16 * Work.Residues.Ept z) := by ring
  rw [hmain]
  have h16 : ‖(16 : ℂ) * Work.Residues.Ept z
        * (Work.Kernels.E4Fun z ^ 3 - Work.Kernels.E14Fun z)‖
      = 16 * ‖Work.Residues.Ept z‖ * ‖Work.Kernels.E4Fun z ^ 3 - Work.Kernels.E14Fun z‖ := by
    rw [norm_mul, norm_mul]
    norm_num
  have h1 : ‖Work.Kernels.E14Fun z‖ * ‖ℓ.L_S z + 16 * Work.Residues.Ept z‖
      ≤ (1 + C14) * (CLS * ‖Work.Residues.Ept z‖ ^ 3) :=
    mul_le_mul hE14b hLSz (norm_nonneg _) (by positivity)
  have h2 : 16 * ‖Work.Residues.Ept z‖
        * ‖Work.Kernels.E4Fun z ^ 3 - Work.Kernels.E14Fun z‖
      ≤ 16 * ‖Work.Residues.Ept z‖
        * ((20001 ^ 2 * (20000 + C6)) * ‖Work.Residues.Ept z‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hE43 (by positivity)
  have h3 : ‖Work.Kernels.E4Fun z‖ ^ 3
        * ‖Work.Kernels.VFun z - 16 * Work.Residues.Ept z‖
      ≤ 20001 ^ 3 * (CV * ‖Work.Residues.Ept z‖ ^ 3) :=
    mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hE4b 3) hVz (norm_nonneg _) (by positivity)
  have hb1 : ‖Work.Kernels.E14Fun z * (ℓ.L_S z + 16 * Work.Residues.Ept z)‖
      ≤ (1 + C14) * (CLS * ‖Work.Residues.Ept z‖ ^ 3) :=
    le_trans (le_of_eq (norm_mul (Work.Kernels.E14Fun z)
      (ℓ.L_S z + 16 * Work.Residues.Ept z))) h1
  have hb2 : ‖16 * Work.Residues.Ept z
        * (Work.Kernels.E4Fun z ^ 3 - Work.Kernels.E14Fun z)‖
      ≤ 16 * ‖Work.Residues.Ept z‖
        * ((20001 ^ 2 * (20000 + C6)) * ‖Work.Residues.Ept z‖ ^ 2) :=
    le_trans (le_of_eq h16) h2
  have hb3 : ‖Work.Kernels.E4Fun z ^ 3
        * (Work.Kernels.VFun z - 16 * Work.Residues.Ept z)‖
      ≤ 20001 ^ 3 * (CV * ‖Work.Residues.Ept z‖ ^ 3) := by
    have heq : ‖Work.Kernels.E4Fun z ^ 3
          * (Work.Kernels.VFun z - 16 * Work.Residues.Ept z)‖
        = ‖Work.Kernels.E4Fun z‖ ^ 3
            * ‖Work.Kernels.VFun z - 16 * Work.Residues.Ept z‖ := by
      rw [norm_mul (Work.Kernels.E4Fun z ^ 3)
            (Work.Kernels.VFun z - 16 * Work.Residues.Ept z),
          norm_pow (Work.Kernels.E4Fun z) 3]
    rw [heq]
    exact h3
  calc ‖Work.Kernels.E14Fun z * (ℓ.L_S z + 16 * Work.Residues.Ept z)
          + 16 * Work.Residues.Ept z
              * (Work.Kernels.E4Fun z ^ 3 - Work.Kernels.E14Fun z)
          + Work.Kernels.E4Fun z ^ 3
              * (Work.Kernels.VFun z - 16 * Work.Residues.Ept z)‖
      ≤ ‖Work.Kernels.E14Fun z * (ℓ.L_S z + 16 * Work.Residues.Ept z)‖
        + ‖16 * Work.Residues.Ept z
              * (Work.Kernels.E4Fun z ^ 3 - Work.Kernels.E14Fun z)‖
        + ‖Work.Kernels.E4Fun z ^ 3
              * (Work.Kernels.VFun z - 16 * Work.Residues.Ept z)‖ :=
        norm_add_three_le _ _ _
    _ ≤ (1 + C14) * (CLS * ‖Work.Residues.Ept z‖ ^ 3)
        + 16 * ‖Work.Residues.Ept z‖
            * ((20001 ^ 2 * (20000 + C6)) * ‖Work.Residues.Ept z‖ ^ 2)
        + 20001 ^ 3 * (CV * ‖Work.Residues.Ept z‖ ^ 3) := by
        linarith [hb1, hb2, hb3]
    _ = ((1 + C14) * CLS + 16 * (20001 ^ 2 * (20000 + C6)) + 20001 ^ 3 * CV)
          * ‖Work.Residues.Ept z‖ ^ 3 := by
        ring

end Work.CKFinal.LineDecay
