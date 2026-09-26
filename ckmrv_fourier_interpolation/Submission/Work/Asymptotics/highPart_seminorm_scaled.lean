import Mathlib
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Asymptotics.abs_pow_mul_exp_le
import Submission.Work.Asymptotics.gaussian_bound
import Submission.Work.Asymptotics.psi1_contDiff_omega
import Submission.Work.Asymptotics.highPartDefs
import Submission.Work.Asymptotics.psi1_iteratedDeriv_bound
import Submission.Work.Asymptotics.iteratedDeriv_comp_quad_bounded
import Submission.Work.Asymptotics.ExpBdd_hiA_hiB

namespace Work.Asymptotics

open Work.Kernels
open MeasureTheory UpperHalfPlane
open scoped Topology

noncomputable section

/-- **The `r`-seminorms of the explicit `high` part of the CKMRV layer.**

`Work.Asymptotics.highPart G τ r` is the explicit closed form

  `λ·psi1 λ·e^{-λ}·G₀₀ + i·psi1 λ·(λ+1)e^{-λ}·G₀₁ + μ·psi1 μ·e^{-μ}·G₁₀ + i·psi1 μ·(μ+1)e^{-μ}·G₁₁`

with `λ = πr²`, `μ = πr² - 2π` and `psi1 x = 2∫_0^1 (1-s)cos(sx)ds`, i.e. a sum of four terms
`((explicit function of r) : ℂ) · G i j τ` (mirror image of the existing, still `sorry`-bodied
`Work.Asymptotics.highPart_seminorm`, restated here so that it can be proved without editing that
file).

**Strategy.**  The `τ`-dependence enters only through the four constants `G i j τ`, so

  `|r|^k ‖∂_r^l highPart(τ,·) r‖ ≤ Σ_{i,j} ‖G i j τ‖ · sup_{r} |r|^k ‖∂_r^l T_{i j} r‖`

where `T_{i j}` are the four explicit `ℂ`-valued functions of `r`.  `hG` upgrades via
`Work.Kernels.moderateGrowthOn_iff_scale` to `‖G i j τ‖ ≤ α (scale τ)^N` on `DomainD`.  The
universal constants `sup_r |r|^k ‖∂_r^l T_{i j} r‖` follow from the facts that `psi1` is smooth
with `‖iteratedDeriv m (fun x : ℝ => (psi1 x : ℂ)) x‖ ≤ 2/((m+1)(m+2)) ≤ 2` for all `x` and all
`m` (differentiate the integral representation `psi1 = 2∫_0^1 (1-s)cos(s·)ds` under the integral
sign), that `λ ↦ πr²` is a quadratic change of variable, and that
`|r|^k (poly in |r|) e^{-πr²}` is bounded (Leibniz + the chain rule bound
`norm_iteratedFDerivWithin_comp_le`; the Gaussian factors come from `e^{-λ}` and `e^{-μ} =
e^{2π}e^{-λ}`, so both branches decay). -/
theorem highPart_seminorm_scaled (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (hG : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn Work.Asymptotics.DomainD (G i j)) :
    ∀ k l : ℕ, ∃ c N : ℝ, 0 ≤ c ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      τ ∈ Work.Asymptotics.DomainD →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highPart G τ s) r‖
        ≤ c * (Work.Kernels.scale τ) ^ N := by
  intro k l
  -- the two inputs obtained from the delegation
  have hpsi : ∀ (m : ℕ) (x : ℝ), ‖iteratedDeriv m psiC x‖ ≤ 2 := psi1_iteratedDeriv_bound
  obtain ⟨hEA, hEB⟩ := ExpBdd_hiA_hiB hpsi
  have hEAs : ExpBdd 1 1 (fun x : ℝ => hiA (x - 2 * Real.pi)) :=
    ExpBdd.sub_const hEA (2 * Real.pi)
  have hEBs : ExpBdd 1 1 (fun x : ℝ => hiB (x - 2 * Real.pi)) :=
    ExpBdd.sub_const hEB (2 * Real.pi)
  -- interface between `ExpBdd` and the composition bound
  have hbdd : ∀ {f : ℝ → ℂ}, ExpBdd 1 1 f → ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      ‖iteratedDeriv j f x‖ ≤ C * (1 + |x|) ^ 1 * Real.exp (-x) := by
    intro f hf j
    obtain ⟨C, hC0, hC⟩ := hf.2 j
    exact ⟨C, hC0, fun x => by simpa using hC x⟩
  -- the four universal shape constants
  obtain ⟨KA, hKA0, hKA⟩ := iteratedDeriv_comp_quad_bounded hiA 1 hEA.1 (hbdd hEA) k l
  obtain ⟨KB, hKB0, hKB⟩ := iteratedDeriv_comp_quad_bounded hiB 1 hEB.1 (hbdd hEB) k l
  obtain ⟨KAs, hKAs0, hKAs⟩ :=
    iteratedDeriv_comp_quad_bounded (fun x : ℝ => hiA (x - 2 * Real.pi)) 1 hEAs.1
      (hbdd hEAs) k l
  obtain ⟨KBs, hKBs0, hKBs⟩ :=
    iteratedDeriv_comp_quad_bounded (fun x : ℝ => hiB (x - 2 * Real.pi)) 1 hEBs.1
      (hbdd hEBs) k l
  -- moderate growth of the four constants
  obtain ⟨α00, N00, hα00, hN00, hb00⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale DomainD (G 0 0)).mp (hG 0 0)
  obtain ⟨α01, N01, hα01, hN01, hb01⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale DomainD (G 0 1)).mp (hG 0 1)
  obtain ⟨α10, N10, hα10, hN10, hb10⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale DomainD (G 1 0)).mp (hG 1 0)
  obtain ⟨α11, N11, hα11, hN11, hb11⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale DomainD (G 1 1)).mp (hG 1 1)
  refine ⟨KA * α00 + KB * α01 + KAs * α10 + KBs * α11,
    max (max N00 N01) (max N10 N11), by positivity, ?_⟩
  intro τ r hτ
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  -- smoothness of the four summands
  have hcont0 : ContDiff ℝ ⊤ (fun s : ℝ => hiT0 s * G 0 0 τ) :=
    (contDiff_hiT0 hEA.1).mul contDiff_const
  have hcont1 : ContDiff ℝ ⊤ (fun s : ℝ => hiT1 s * G 0 1 τ) :=
    (contDiff_hiT1 hEB.1).mul contDiff_const
  have hcont2 : ContDiff ℝ ⊤ (fun s : ℝ => hiT2 s * G 1 0 τ) :=
    (contDiff_hiT2 hEAs.1).mul contDiff_const
  have hcont3 : ContDiff ℝ ⊤ (fun s : ℝ => hiT3 s * G 1 1 τ) :=
    (contDiff_hiT3 hEBs.1).mul contDiff_const
  have hc0 : ContDiffAt ℝ (l : WithTop ℕ∞) (fun s : ℝ => hiT0 s * G 0 0 τ) r :=
    (hcont0.contDiffAt).of_le (by simp)
  have hc1 : ContDiffAt ℝ (l : WithTop ℕ∞) (fun s : ℝ => hiT1 s * G 0 1 τ) r :=
    (hcont1.contDiffAt).of_le (by simp)
  have hc2 : ContDiffAt ℝ (l : WithTop ℕ∞) (fun s : ℝ => hiT2 s * G 1 0 τ) r :=
    (hcont2.contDiffAt).of_le (by simp)
  have hc3 : ContDiffAt ℝ (l : WithTop ℕ∞) (fun s : ℝ => hiT3 s * G 1 1 τ) r :=
    (hcont3.contDiffAt).of_le (by simp)
  -- rewrite `highPart` as a sum of the four shapes times the constants
  have hfun : (fun s : ℝ => highPart G τ s)
      = fun s : ℝ => hiT0 s * G 0 0 τ + hiT1 s * G 0 1 τ + hiT2 s * G 1 0 τ
          + hiT3 s * G 1 1 τ := by
    funext s
    exact highPart_eq_T G τ s
  rw [hfun, iteratedDeriv_sum4 hc0 hc1 hc2 hc3,
    iteratedDeriv_mul_const_field (n := l) (x := r) hiT0 (G 0 0 τ),
    iteratedDeriv_mul_const_field (n := l) (x := r) hiT1 (G 0 1 τ),
    iteratedDeriv_mul_const_field (n := l) (x := r) hiT2 (G 1 0 τ),
    iteratedDeriv_mul_const_field (n := l) (x := r) hiT3 (G 1 1 τ)]
  -- unfold the two `I`-prefixed shapes
  have hT1 : iteratedDeriv l hiT1 r
      = Complex.I * iteratedDeriv l (fun s : ℝ => hiB (Real.pi * s ^ 2)) r :=
    iteratedDeriv_const_mul_field (n := l) (x := r) (Complex.I)
      (fun s : ℝ => hiB (Real.pi * s ^ 2))
  have hT3 : iteratedDeriv l hiT3 r
      = Complex.I * iteratedDeriv l (fun s : ℝ => hiB (Real.pi * s ^ 2 - 2 * Real.pi)) r :=
    iteratedDeriv_const_mul_field (n := l) (x := r) (Complex.I)
      (fun s : ℝ => hiB (Real.pi * s ^ 2 - 2 * Real.pi))
  rw [hT1, hT3]
  -- the four weighted bounds
  have b0 : |r| ^ k * ‖iteratedDeriv l hiT0 r‖ ≤ KA := hKA r
  have b1 : |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => hiB (Real.pi * s ^ 2)) r‖ ≤ KB := hKB r
  have b2 : |r| ^ k * ‖iteratedDeriv l hiT2 r‖ ≤ KAs := hKAs r
  have b3 : |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => hiB (Real.pi * s ^ 2 - 2 * Real.pi)) r‖
      ≤ KBs := hKBs r
  have q0 : |r| ^ k * ‖iteratedDeriv l hiT0 r * G 0 0 τ‖ ≤ KA * ‖G 0 0 τ‖ := by
    rw [norm_mul]
    calc |r| ^ k * (‖iteratedDeriv l hiT0 r‖ * ‖G 0 0 τ‖)
        = (|r| ^ k * ‖iteratedDeriv l hiT0 r‖) * ‖G 0 0 τ‖ := by ring
      _ ≤ KA * ‖G 0 0 τ‖ := mul_le_mul_of_nonneg_right b0 (norm_nonneg _)
  have q1 : |r| ^ k * ‖(Complex.I * iteratedDeriv l (fun s : ℝ => hiB (Real.pi * s ^ 2)) r)
        * G 0 1 τ‖ ≤ KB * ‖G 0 1 τ‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
    calc |r| ^ k * (‖iteratedDeriv l (fun s : ℝ => hiB (Real.pi * s ^ 2)) r‖ * ‖G 0 1 τ‖)
        = (|r| ^ k * ‖iteratedDeriv l (fun s : ℝ => hiB (Real.pi * s ^ 2)) r‖)
            * ‖G 0 1 τ‖ := by ring
      _ ≤ KB * ‖G 0 1 τ‖ := mul_le_mul_of_nonneg_right b1 (norm_nonneg _)
  have q2 : |r| ^ k * ‖iteratedDeriv l hiT2 r * G 1 0 τ‖ ≤ KAs * ‖G 1 0 τ‖ := by
    rw [norm_mul]
    calc |r| ^ k * (‖iteratedDeriv l hiT2 r‖ * ‖G 1 0 τ‖)
        = (|r| ^ k * ‖iteratedDeriv l hiT2 r‖) * ‖G 1 0 τ‖ := by ring
      _ ≤ KAs * ‖G 1 0 τ‖ := mul_le_mul_of_nonneg_right b2 (norm_nonneg _)
  have q3 : |r| ^ k * ‖(Complex.I * iteratedDeriv l
        (fun s : ℝ => hiB (Real.pi * s ^ 2 - 2 * Real.pi)) r) * G 1 1 τ‖
      ≤ KBs * ‖G 1 1 τ‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
    calc |r| ^ k * (‖iteratedDeriv l (fun s : ℝ => hiB (Real.pi * s ^ 2 - 2 * Real.pi)) r‖
          * ‖G 1 1 τ‖)
        = (|r| ^ k * ‖iteratedDeriv l (fun s : ℝ => hiB (Real.pi * s ^ 2 - 2 * Real.pi)) r‖)
            * ‖G 1 1 τ‖ := by ring
      _ ≤ KBs * ‖G 1 1 τ‖ := mul_le_mul_of_nonneg_right b3 (norm_nonneg _)
  -- the tail bound `(scale τ)^N`
  have hN00 : (Work.Kernels.scale τ) ^ N00
      ≤ (Work.Kernels.scale τ) ^ max (max N00 N01) (max N10 N11) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_trans (le_max_left _ _) (le_max_left _ _))
  have hN01 : (Work.Kernels.scale τ) ^ N01
      ≤ (Work.Kernels.scale τ) ^ max (max N00 N01) (max N10 N11) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_trans (le_max_right _ _) (le_max_left _ _))
  have hN10 : (Work.Kernels.scale τ) ^ N10
      ≤ (Work.Kernels.scale τ) ^ max (max N00 N01) (max N10 N11) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_trans (le_max_left _ _) (le_max_right _ _))
  have hN11 : (Work.Kernels.scale τ) ^ N11
      ≤ (Work.Kernels.scale τ) ^ max (max N00 N01) (max N10 N11) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_trans (le_max_right _ _) (le_max_right _ _))
  have f0 : KA * (α00 * (Work.Kernels.scale τ) ^ N00)
      ≤ KA * α00 * (Work.Kernels.scale τ) ^ max (max N00 N01) (max N10 N11) := by
    calc KA * (α00 * (Work.Kernels.scale τ) ^ N00)
        = KA * α00 * (Work.Kernels.scale τ) ^ N00 := by ring
      _ ≤ KA * α00 * (Work.Kernels.scale τ) ^ max (max N00 N01) (max N10 N11) :=
          mul_le_mul_of_nonneg_left hN00 (by positivity)
  have f1 : KB * (α01 * (Work.Kernels.scale τ) ^ N01)
      ≤ KB * α01 * (Work.Kernels.scale τ) ^ max (max N00 N01) (max N10 N11) := by
    calc KB * (α01 * (Work.Kernels.scale τ) ^ N01)
        = KB * α01 * (Work.Kernels.scale τ) ^ N01 := by ring
      _ ≤ KB * α01 * (Work.Kernels.scale τ) ^ max (max N00 N01) (max N10 N11) :=
          mul_le_mul_of_nonneg_left hN01 (by positivity)
  have f2 : KAs * (α10 * (Work.Kernels.scale τ) ^ N10)
      ≤ KAs * α10 * (Work.Kernels.scale τ) ^ max (max N00 N01) (max N10 N11) := by
    calc KAs * (α10 * (Work.Kernels.scale τ) ^ N10)
        = KAs * α10 * (Work.Kernels.scale τ) ^ N10 := by ring
      _ ≤ KAs * α10 * (Work.Kernels.scale τ) ^ max (max N00 N01) (max N10 N11) :=
          mul_le_mul_of_nonneg_left hN10 (by positivity)
  have f3 : KBs * (α11 * (Work.Kernels.scale τ) ^ N11)
      ≤ KBs * α11 * (Work.Kernels.scale τ) ^ max (max N00 N01) (max N10 N11) := by
    calc KBs * (α11 * (Work.Kernels.scale τ) ^ N11)
        = KBs * α11 * (Work.Kernels.scale τ) ^ N11 := by ring
      _ ≤ KBs * α11 * (Work.Kernels.scale τ) ^ max (max N00 N01) (max N10 N11) :=
          mul_le_mul_of_nonneg_left hN11 (by positivity)
  have htri : ‖iteratedDeriv l hiT0 r * G 0 0 τ
        + (Complex.I * iteratedDeriv l (fun s : ℝ => hiB (Real.pi * s ^ 2)) r) * G 0 1 τ
        + iteratedDeriv l hiT2 r * G 1 0 τ
        + (Complex.I * iteratedDeriv l (fun s : ℝ => hiB (Real.pi * s ^ 2 - 2 * Real.pi)) r)
            * G 1 1 τ‖
      ≤ ‖iteratedDeriv l hiT0 r * G 0 0 τ‖
        + ‖(Complex.I * iteratedDeriv l (fun s : ℝ => hiB (Real.pi * s ^ 2)) r) * G 0 1 τ‖
        + ‖iteratedDeriv l hiT2 r * G 1 0 τ‖
        + ‖(Complex.I * iteratedDeriv l (fun s : ℝ => hiB (Real.pi * s ^ 2 - 2 * Real.pi)) r)
            * G 1 1 τ‖ := by
    linarith [norm_add_le (iteratedDeriv l hiT0 r * G 0 0 τ)
        ((Complex.I * iteratedDeriv l (fun s : ℝ => hiB (Real.pi * s ^ 2)) r) * G 0 1 τ),
      norm_add_le (iteratedDeriv l hiT0 r * G 0 0 τ
          + (Complex.I * iteratedDeriv l (fun s : ℝ => hiB (Real.pi * s ^ 2)) r) * G 0 1 τ)
        (iteratedDeriv l hiT2 r * G 1 0 τ),
      norm_add_le (iteratedDeriv l hiT0 r * G 0 0 τ
          + (Complex.I * iteratedDeriv l (fun s : ℝ => hiB (Real.pi * s ^ 2)) r) * G 0 1 τ
          + iteratedDeriv l hiT2 r * G 1 0 τ)
        ((Complex.I * iteratedDeriv l (fun s : ℝ => hiB (Real.pi * s ^ 2 - 2 * Real.pi)) r)
          * G 1 1 τ)]
  calc |r| ^ k * ‖iteratedDeriv l hiT0 r * G 0 0 τ
        + (Complex.I * iteratedDeriv l (fun s : ℝ => hiB (Real.pi * s ^ 2)) r) * G 0 1 τ
        + iteratedDeriv l hiT2 r * G 1 0 τ
        + (Complex.I * iteratedDeriv l (fun s : ℝ => hiB (Real.pi * s ^ 2 - 2 * Real.pi)) r)
            * G 1 1 τ‖
      ≤ |r| ^ k * (‖iteratedDeriv l hiT0 r * G 0 0 τ‖
        + ‖(Complex.I * iteratedDeriv l (fun s : ℝ => hiB (Real.pi * s ^ 2)) r) * G 0 1 τ‖
        + ‖iteratedDeriv l hiT2 r * G 1 0 τ‖
        + ‖(Complex.I * iteratedDeriv l (fun s : ℝ => hiB (Real.pi * s ^ 2 - 2 * Real.pi)) r)
            * G 1 1 τ‖) := mul_le_mul_of_nonneg_left htri (by positivity)
    _ = |r| ^ k * ‖iteratedDeriv l hiT0 r * G 0 0 τ‖
        + |r| ^ k * ‖(Complex.I * iteratedDeriv l (fun s : ℝ => hiB (Real.pi * s ^ 2)) r)
            * G 0 1 τ‖
        + |r| ^ k * ‖iteratedDeriv l hiT2 r * G 1 0 τ‖
        + |r| ^ k * ‖(Complex.I * iteratedDeriv l
            (fun s : ℝ => hiB (Real.pi * s ^ 2 - 2 * Real.pi)) r) * G 1 1 τ‖ := by ring
    _ ≤ KA * ‖G 0 0 τ‖ + KB * ‖G 0 1 τ‖ + KAs * ‖G 1 0 τ‖ + KBs * ‖G 1 1 τ‖ := by
        linarith [q0, q1, q2, q3]
    _ ≤ KA * (α00 * (Work.Kernels.scale τ) ^ N00)
          + KB * (α01 * (Work.Kernels.scale τ) ^ N01)
          + KAs * (α10 * (Work.Kernels.scale τ) ^ N10)
          + KBs * (α11 * (Work.Kernels.scale τ) ^ N11) := by
        linarith [mul_le_mul_of_nonneg_left (hb00 τ hτ) hKA0,
          mul_le_mul_of_nonneg_left (hb01 τ hτ) hKB0,
          mul_le_mul_of_nonneg_left (hb10 τ hτ) hKAs0,
          mul_le_mul_of_nonneg_left (hb11 τ hτ) hKBs0]
    _ ≤ (KA * α00 + KB * α01 + KAs * α10 + KBs * α11)
          * (Work.Kernels.scale τ) ^ max (max N00 N01) (max N10 N11) := by
        calc KA * (α00 * (Work.Kernels.scale τ) ^ N00)
              + KB * (α01 * (Work.Kernels.scale τ) ^ N01)
              + KAs * (α10 * (Work.Kernels.scale τ) ^ N10)
              + KBs * (α11 * (Work.Kernels.scale τ) ^ N11)
            ≤ KA * α00 * (Work.Kernels.scale τ) ^ max (max N00 N01) (max N10 N11)
              + KB * α01 * (Work.Kernels.scale τ) ^ max (max N00 N01) (max N10 N11)
              + KAs * α10 * (Work.Kernels.scale τ) ^ max (max N00 N01) (max N10 N11)
              + KBs * α11 * (Work.Kernels.scale τ) ^ max (max N00 N01) (max N10 N11) := by
                linarith [f0, f1, f2, f3]
          _ = (KA * α00 + KB * α01 + KAs * α10 + KBs * α11)
                * (Work.Kernels.scale τ) ^ max (max N00 N01) (max N10 N11) := by ring

end
end Work.Asymptotics
