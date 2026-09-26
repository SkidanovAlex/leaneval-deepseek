import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.PhiAxis
import Submission.Work.CKFinal.LineDecay.slash_qtau_twentyfour
import Submission.Work.CKFinal.LineDecay.qParamFun_line_norm_sub
import Submission.Work.CKFinal.LineDecay.sinSqC_gaussWeight_bound
import Submission.Work.CKFinal.LineDecay.P1_axis_bound_twentyfour
import Submission.Work.CKFinal.LineDecay.P1_scalar_twentyfour

/-!
# The `P₁` bound on the lines `Re τ = ±1/2` in dimension 24

`P₁ = sinSqC r · ∫_0^1 K(τ, i t) e^{-π r² t} dt` is the low piece of the layer built from the
kernel `K = K^{(24)}` (or `K̂^{(24)}`).  Here we show that on the two lines `Re τ = ±1/2`, for
`Im τ ≥ Y₀`, it decays like `C (Im τ)^N e^{-3π Im τ}`.

The input is the quotient bound of CKMRV (4.12) for `d = 24`, proved in
`LineDecay/slash_qtau_twentyfour`:

  `‖z^{10} K_±^{(24)}(τ, S•z)‖ ≤ C (1+‖τ‖)^A ‖q(τ)‖ e^{-π Im z} / ‖Δ(z)(j τ - j z)‖`,

which is converted into the pointwise kernel bound
`‖K(τ, i t)‖ ≤ C' (Im τ)^{N} e^{-3π Im τ}` for `t ≤ 1` by `P1_axis_bound_twentyfour`
(the extra factor `‖q(τ)‖ = e^{-2π Im τ}` is what upgrades the exponent from `-π` to `-3π`).
The remaining step — integrating over `t ∈ (0,1]` against the uniformly bounded factors
`sinSqC r` and `gaussWeight r t` — is done here, using that both `K^{(24)}` and `K̂^{(24)}` are
averages of `K_+^{(24)}` and `K_-^{(24)}`.
-/

open UpperHalfPlane MeasureTheory
open scoped Topology Manifold

namespace Work.CKFinal.LineDecay

noncomputable section

theorem P1_line_bound_twentyfour (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N Y₀ : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ 1 ≤ Y₀ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im →
        (‖Work.CKFinal.P1 (Work.Kernels.Kfun ℓ 24) r τ‖
            ≤ C * τ.im ^ N * Real.exp (-(3 * Real.pi * τ.im))
          ∧ ‖Work.CKFinal.P1 (Work.Kernels.Khat ℓ 24) r τ‖
            ≤ C * τ.im ^ N * Real.exp (-(3 * Real.pi * τ.im))) := by
  obtain ⟨C, A, hC, hA, hQ⟩ := slash_qtau_twentyfour ℓ
  -- the scalar estimate, with `1/t` in place of `t⁻¹`
  have hscal : ∀ y t : ℝ, 1 ≤ y → 0 < t → t ≤ 1 →
      t ^ 10 * Real.exp (-(Real.pi * (1 / t)) - 2 * Real.pi * y)
        / (Real.exp (-(2 * Real.pi * y)) + Real.exp (-(2 * Real.pi * (1 / t))))
        ≤ Real.exp (-(Real.pi * y)) := by
    intro y t hy ht ht1
    rw [one_div]
    exact P1_scalar_twentyfour y t hy ht ht1
  -- the pointwise bound for each of the two pieces of the kernel
  obtain ⟨CP, NP, YP, hCP, hNP, hYP, hPb⟩ :=
    P1_axis_bound_twentyfour (Work.Kernels.KPlus 24) C A hC.le hA hscal
      (fun τ z hD h2 hz hne => (hQ τ z hD h2 hz hne).1)
  obtain ⟨CM, NM, YM, hCM, hNM, hYM, hMb⟩ :=
    P1_axis_bound_twentyfour (Work.Kernels.KMinus ℓ 24) C A hC.le hA hscal
      (fun τ z hD h2 hz hne => (hQ τ z hD h2 hz hne).2)
  refine ⟨4 * max CP CM, max NP NM, max (max YP YM) 1, by positivity, by positivity,
    le_max_right _ _, ?_⟩
  intro τ r hre hy
  have hy1 : (1 : ℝ) ≤ τ.im := le_trans (le_max_right (max YP YM) 1) hy
  have hyP : YP ≤ τ.im := le_trans (le_max_left YP YM) (le_trans (le_max_left (max YP YM) 1) hy)
  have hyM : YM ≤ τ.im := le_trans (le_max_right YP YM) (le_trans (le_max_left (max YP YM) 1) hy)
  set M : ℝ := max CP CM * τ.im ^ (max NP NM) * Real.exp (-(3 * Real.pi * τ.im)) with hMdef
  have hM0 : (0 : ℝ) ≤ M := by rw [hMdef]; positivity
  have hmono : ∀ a b : ℝ, a ≤ max CP CM → b ≤ max NP NM →
      a * τ.im ^ b * Real.exp (-(3 * Real.pi * τ.im)) ≤ M := by
    intro a b ha hb
    rw [hMdef]
    have hn : τ.im ^ b ≤ τ.im ^ (max NP NM) :=
      Real.rpow_le_rpow_of_exponent_le hy1 hb
    have hmul : τ.im ^ b * Real.exp (-(3 * Real.pi * τ.im))
        ≤ τ.im ^ (max NP NM) * Real.exp (-(3 * Real.pi * τ.im)) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    calc a * τ.im ^ b * Real.exp (-(3 * Real.pi * τ.im))
        = a * (τ.im ^ b * Real.exp (-(3 * Real.pi * τ.im))) := by ring
      _ ≤ max CP CM * (τ.im ^ (max NP NM) * Real.exp (-(3 * Real.pi * τ.im))) :=
          mul_le_mul ha hmul (by positivity) (by positivity)
      _ = max CP CM * τ.im ^ (max NP NM) * Real.exp (-(3 * Real.pi * τ.im)) := by ring
  have hPk : ∀ t (ht : 0 < t), t ≤ 1 →
      ‖Work.Kernels.KPlus 24 τ (Work.Kernels.imagAxis t ht)‖ ≤ M :=
    fun t ht ht1 => le_trans (hPb τ t ht hre hyP ht1)
      (hmono CP NP (le_max_left _ _) (le_max_left _ _))
  have hMk : ∀ t (ht : 0 < t), t ≤ 1 →
      ‖Work.Kernels.KMinus ℓ 24 τ (Work.Kernels.imagAxis t ht)‖ ≤ M :=
    fun t ht ht1 => le_trans (hMb τ t ht hre hyM ht1)
      (hmono CM NM (le_max_right _ _) (le_max_right _ _))
  have hKfun : ∀ t (ht : 0 < t), t ≤ 1 →
      ‖Work.Kernels.Kfun ℓ 24 τ (Work.Kernels.imagAxis t ht)‖ ≤ M := by
    intro t ht ht1
    have h1 := hPk t ht ht1
    have h2 := hMk t ht ht1
    have h3 := norm_add_le (Work.Kernels.KPlus 24 τ (Work.Kernels.imagAxis t ht))
      (Work.Kernels.KMinus ℓ 24 τ (Work.Kernels.imagAxis t ht))
    rw [Work.Kernels.Kfun, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    linarith
  have hKhat : ∀ t (ht : 0 < t), t ≤ 1 →
      ‖Work.Kernels.Khat ℓ 24 τ (Work.Kernels.imagAxis t ht)‖ ≤ M := by
    intro t ht ht1
    have h1 := hPk t ht ht1
    have h2 := hMk t ht ht1
    have h3 := norm_sub_le (Work.Kernels.KPlus 24 τ (Work.Kernels.imagAxis t ht))
      (Work.Kernels.KMinus ℓ 24 τ (Work.Kernels.imagAxis t ht))
    rw [Work.Kernels.Khat, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    linarith
  have hgw : ∀ t (ht : 0 ≤ t), ‖Work.Asymptotics.gaussWeight r t‖ ≤ 1 :=
    fun t ht => (sinSqC_gaussWeight_bound r t ht).2
  have hsin : ‖Work.Asymptotics.sinSqC r‖ ≤ 4 := (sinSqC_gaussWeight_bound r 0 le_rfl).1
  -- the interval integral against the uniformly bounded factors
  have hint : ∀ (K : UpperHalfPlane → UpperHalfPlane → ℂ), (∀ t (ht : 0 < t), t ≤ 1 →
        ‖K τ (Work.Kernels.imagAxis t ht)‖ ≤ M) →
      ‖∫ t in (0 : ℝ)..1,
          Work.CKFinal.Kax K τ 0 t * Work.Asymptotics.gaussWeight r t‖ ≤ M := by
    intro K hK
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t => Work.CKFinal.Kax K τ 0 t * Work.Asymptotics.gaussWeight r t)
      (a := (0 : ℝ)) (b := 1) (C := M) (fun x hx => ?_)
    · simpa using h
    · rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      have hx0 : 0 < x := hx.1
      have hx1 : x ≤ 1 := hx.2
      have hker : ‖Work.CKFinal.Kax K τ 0 x‖ = ‖K τ (Work.Kernels.imagAxis x hx0)‖ := by
        rw [Work.CKFinal.Kax, dif_pos hx0, zero_vadd]
      calc ‖Work.CKFinal.Kax K τ 0 x * Work.Asymptotics.gaussWeight r x‖
          = ‖Work.CKFinal.Kax K τ 0 x‖ * ‖Work.Asymptotics.gaussWeight r x‖ := norm_mul _ _
        _ ≤ M * 1 := mul_le_mul (by rw [hker]; exact hK x hx0 hx1) (hgw x hx0.le)
            (norm_nonneg _) hM0
        _ = M := by ring
  constructor
  · have h := hint (Work.Kernels.Kfun ℓ 24) hKfun
    rw [Work.CKFinal.P1, Work.CKFinal.hsplit]
    calc ‖Work.Asymptotics.sinSqC r * ∫ t in (0 : ℝ)..1,
            Work.CKFinal.Kax (Work.Kernels.Kfun ℓ 24) τ 0 t * Work.Asymptotics.gaussWeight r t‖
        = ‖Work.Asymptotics.sinSqC r‖ * ‖∫ t in (0 : ℝ)..1,
            Work.CKFinal.Kax (Work.Kernels.Kfun ℓ 24) τ 0 t * Work.Asymptotics.gaussWeight r t‖ :=
          norm_mul _ _
      _ ≤ 4 * M := mul_le_mul hsin h (norm_nonneg _) (by norm_num)
      _ = 4 * max CP CM * τ.im ^ max NP NM * Real.exp (-(3 * Real.pi * τ.im)) := by
          rw [hMdef]; ring
  · have h := hint (Work.Kernels.Khat ℓ 24) hKhat
    rw [Work.CKFinal.P1, Work.CKFinal.hsplit]
    calc ‖Work.Asymptotics.sinSqC r * ∫ t in (0 : ℝ)..1,
            Work.CKFinal.Kax (Work.Kernels.Khat ℓ 24) τ 0 t * Work.Asymptotics.gaussWeight r t‖
        = ‖Work.Asymptotics.sinSqC r‖ * ‖∫ t in (0 : ℝ)..1,
            Work.CKFinal.Kax (Work.Kernels.Khat ℓ 24) τ 0 t * Work.Asymptotics.gaussWeight r t‖ :=
          norm_mul _ _
      _ ≤ 4 * M := mul_le_mul hsin h (norm_nonneg _) (by norm_num)
      _ = 4 * max CP CM * τ.im ^ max NP NM * Real.exp (-(3 * Real.pi * τ.im)) := by
          rw [hMdef]; ring

end

end Work.CKFinal.LineDecay
