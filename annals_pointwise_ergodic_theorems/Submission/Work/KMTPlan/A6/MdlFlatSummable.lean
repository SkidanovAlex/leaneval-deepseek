/-
# Summability of the flattened model sum with an arithmetic coefficient (area A6)

The model operators of Krause--Mirek--Tao §6 are bilinear convolution operators with an arithmetic
coefficient `c` in the convolution index, evaluated against the normal form

  `mdlKFG K F G x p z = K (p₁-z₁) (p₂-z₂) · F (x-p₁) · G (x-p₂)`

(`Work.KMTPlan.A6.mdlKFG`, `MdlDecayHighLow`).  Because the arithmetic coefficient is a combination
of `m_Ẑ`-averages it is bounded by `Ca · a z₁ · a' z₂` with `a`, `a'` in `ℓ¹(ℤ)`, and this module
proves that the resulting fourfold family

  `q ↦ c q.2 · mdlKFG K F G x q.1 q.2`

is summable whenever `‖K‖ ∈ ℓ¹(ℤ²)`, `F`, `G` are bounded and `a`, `a' ∈ ℓ¹(ℤ)`.  This is the
dominated-convergence prerequisite that lets every later manipulation of the model sum (Fubini,
interchange of the `t`-integral, termwise estimates) be carried out.

## The proof

The whole family is dominated by the constant `Ca ≥ 0` multiple of the *summable* majorant
`mdlMajorant a a' K CF CG` whose summability was established in `MdlNFIntegral`
(`Work.KMTPlan.A6.mdl_conv_majorant_summable`, the elementary Young inequality `ℓ¹ ⋆ ℓ¹ ⊆ ℓ¹` for
the fourfold convolution) and `Summable.of_norm_bounded` concludes.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlLowHighAux

namespace Work.KMTPlan.A6

noncomputable section

/-- **Summability of the flattened model sum with a bounded arithmetic coefficient.**  Let `K` be
`ℓ¹` on `ℤ²`, `F`, `G` bounded by `CF`, `CG`, and let the coefficient `c` on the convolution index
be dominated by `Ca · a z₁ · a' z₂` with `a`, `a'` nonnegative and in `ℓ¹(ℤ)`.  Then

  `q ↦ c q.2 · K (q.1.1 - q.2.1) (q.1.2 - q.2.2) · F (x - q.1.1) · G (x - q.1.2)`

is summable, for every `x`.

The dominating family is `Ca · mdlMajorant a a' K CF CG`, summable by
`mdl_conv_majorant_summable`. -/
theorem MdlFlatSummable {K : ℤ → ℤ → ℂ} {F G : ℤ → ℂ} {CF CG : ℝ}
    (hF : ∀ y : ℤ, ‖F y‖ ≤ CF) (hG : ∀ y : ℤ, ‖G y‖ ≤ CG)
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖)
    {c : ℤ × ℤ → ℂ} {a a' : ℤ → ℝ} (ha : Summable a) (ha' : Summable a')
    (ha0 : ∀ i : ℤ, 0 ≤ a i) (ha0' : ∀ i : ℤ, 0 ≤ a' i) {Ca : ℝ} (hCa : 0 ≤ Ca)
    (hc : ∀ z : ℤ × ℤ, ‖c z‖ ≤ Ca * (a z.1 * a' z.2)) (x : ℤ) :
    Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
      c q.2 * Work.KMTPlan.A6.mdlKFG K F G x q.1 q.2 := by
  have hCF : 0 ≤ CF := le_trans (norm_nonneg (F 0)) (hF 0)
  have hCG : 0 ≤ CG := le_trans (norm_nonneg (G 0)) (hG 0)
  have hBsum : Summable (mdlMajorant a a' K CF CG) :=
    mdl_conv_majorant_summable hK ha ha' ha0 ha0' CF CG
  refine Summable.of_norm_bounded (hBsum.mul_left Ca) (fun q => ?_)
  have h2 : ‖mdlKFG K F G x q.1 q.2‖ ≤ ‖K (q.1.1 - q.2.1) (q.1.2 - q.2.2)‖ * CF * CG := by
    rw [mdlKFG, norm_mul, norm_mul]
    gcongr
    · exact hF _
    · exact hG _
  rw [norm_mul]
  calc ‖c q.2‖ * ‖mdlKFG K F G x q.1 q.2‖
      ≤ (Ca * (a q.2.1 * a' q.2.2))
          * (‖K (q.1.1 - q.2.1) (q.1.2 - q.2.2)‖ * CF * CG) :=
        mul_le_mul (hc q.2) h2 (norm_nonneg _) (mul_nonneg hCa (mul_nonneg (ha0 _) (ha0' _)))
    _ = Ca * mdlMajorant a a' K CF CG q := by rw [mdlMajorant]; ring

end

end Work.KMTPlan.A6
