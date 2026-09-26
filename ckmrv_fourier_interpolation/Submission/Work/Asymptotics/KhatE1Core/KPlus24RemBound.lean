import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.DSm1RowBound
import Submission.Work.Asymptotics.KhatE1Core.dSm2_leading
import Submission.Work.Asymptotics.KhatE1Core.KPlusRefTailBound

/-!
# The `K₊`-side `E(z)²`-remainder of the split form of `Bracket24TailCore`

The plan (`KhatE1Core/Bracket24TailPlan.lean`, §2-§3) writes the `Sh`-cleared `d = 24` bracket as

  `X = KPlus24Ref + dKPlus24 + (3456π)⁻¹ (PolyKM + DevKM)`

and takes the explicit `E(z)²`-coefficient

  `F := -c z² KPlusQ1 + 324 c z² Φ_ref + (3456π)⁻¹ kmfd_c2 + (3456π)⁻¹ DV`.

The target `Bracket24TailCore` then follows from the two remainder bounds `(β)` and `(γ)`.  This
module supplies the `K₊` half of `(γ)`, namely the deviation-sum remainder

  `dKPlus24 - E(z)²·(324 c z² Φ_ref) = -(c z²)·(dKPlusSum + 324·q(z)·Φ_ref)`,

which is *precisely* the plan's requirement "needs the five rows, with `dSm2 + 324q_zΦ_ref`
the only surviving `q¹`-term".  The two statements are

* `Bound2_dKPlusSum_E2rem ℓ : Bound2 (dKPlusSum + 324 q Φ_ref) 0 2`, i.e.
  `‖dKPlusSum τ z + 324 q(z)Φ_ref τ z‖ ≤ C (scale τ)^N (1+t)^M ‖q(z)‖²`
  (`dSm2_leading` gives the `dSm2` part, `Bound2_dSm1`, `Bound2_dSm3`, `Bound2_dSm4`,
  `Bound2_dSm5` the rest, each shifted to the common exponent `(0,2)`), and
* `Bound2_dKPlusSum_E2rem11 ℓ : Bound2 … 1 1`, i.e.
  `‖…‖ ≤ C ‖q(τ)‖ (scale τ)^N (1+t)^M ‖q(z)‖`, the weight that `(γ)` consumes:
  multiplying by the bounded factor `|c z²|` gives `O(‖q(τ)‖(scale τ)^N(1+t)^M e^{-2πt})`.

(`(0,2)` implies `(1,1)` by `Bound2.shift`, using `‖q(z)‖ ≤ ‖q(τ)‖` on the funnel strip.)
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-- `dSm2 + 324·q(z)·Φ_ref = O((scale τ)^N(1+t)^M ‖q(z)‖²)`, in `Bound2` form. -/
theorem Bound2_dSm2_lead :
    Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
      dSm2 τ z + 324 * Work.Kernels.qParamFun z * Work.Asymptotics.K24F.Phiref τ z) 0 2 := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := dSm2_leading
  exact Bound2.of_le_qz (K := 2) (C := C) (N := N) (M := M) hC hN hM hb

/-- **The `E(z)²`-remainder of the `K₊` deviation sum.** -/
theorem Bound2_dKPlusSum_E2rem (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
      dKPlusSum τ z + 324 * Work.Kernels.qParamFun z * Work.Asymptotics.K24F.Phiref τ z) 0 2 := by
  have h1 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) => dSm1 τ z) 0 2 :=
    Bound2_dSm1
  have h2 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
      dSm2 τ z + 324 * Work.Kernels.qParamFun z * Work.Asymptotics.K24F.Phiref τ z) 0 2 :=
    Bound2_dSm2_lead
  have h3 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) => dSm3 τ z) 0 2 :=
    Bound2_dSm3.shift
  have h4 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) => dSm4 τ z) 0 2 :=
    (Bound2_dSm4 ℓ).mono (le_refl (0 : ℤ)) (by norm_num : (2 : ℤ) ≤ 3)
  have h5 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) => dSm5 τ z) 0 2 :=
    (Bound2_dSm5 ℓ).shift
  exact ((((h1.add h2).add h3).add h4).add h5).congr
    (fun τ z => by simp only [dKPlusSum]; ring)

/-- The same at the weight `(1,1)` consumed by `(γ)`. -/
theorem Bound2_dKPlusSum_E2rem11 (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
      dKPlusSum τ z + 324 * Work.Kernels.qParamFun z * Work.Asymptotics.K24F.Phiref τ z) 1 1 :=
  (Bound2_dKPlusSum_E2rem ℓ).shift

/-- **The `K₊` deviation-sum `E(z)²`-remainder, raw form.** -/
theorem dKPlusSum_E2rem_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖dKPlusSum τ z + 324 * Work.Kernels.qParamFun z * Work.Asymptotics.K24F.Phiref τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := Bound2_dKPlusSum_E2rem ℓ
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have h := hb τ z t hF ht hz0 hz1 hzim
  have hconv : C * (‖Work.Kernels.qParamFun τ‖ ^ (0 : ℤ) * (Work.Kernels.scale τ) ^ N
      * (1 + t) ^ M * ‖Work.Kernels.qParamFun z‖ ^ (2 : ℤ))
      = C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
    rw [show ‖Work.Kernels.qParamFun τ‖ ^ (0 : ℤ) = (1 : ℝ) from zpow_zero _,
      Bound2.shape1 C (Work.Kernels.scale τ) (1 + t) (‖Work.Kernels.qParamFun z‖) N M (2 : ℤ)]
    rfl
  rw [hconv] at h
  exact h

/-- **The `K₊` deviation-sum `E(z)²`-remainder at the `(γ)` weight.** -/
theorem dKPlusSum_E2rem_bound11 (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖dKPlusSum τ z + 324 * Work.Kernels.qParamFun z * Work.Asymptotics.K24F.Phiref τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
            * ‖Work.Kernels.qParamFun z‖ := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := Bound2_dKPlusSum_E2rem11 ℓ
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have h := hb τ z t hF ht hz0 hz1 hzim
  have hconv : C * (‖Work.Kernels.qParamFun τ‖ ^ (1 : ℤ) * (Work.Kernels.scale τ) ^ N
      * (1 + t) ^ M * ‖Work.Kernels.qParamFun z‖ ^ (1 : ℤ))
      = C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * ‖Work.Kernels.qParamFun z‖ := by
    rw [show ‖Work.Kernels.qParamFun τ‖ ^ (1 : ℤ) = ‖Work.Kernels.qParamFun τ‖ from zpow_one _,
      show ‖Work.Kernels.qParamFun z‖ ^ (1 : ℤ) = ‖Work.Kernels.qParamFun z‖ from zpow_one _]
    ring
  rw [hconv] at h
  exact h

/-! ## The `dKPlus24` remainder in the exact shape `(γ)` consumes

`dKPlus24 - E(z)²·(324·c·z²·Φ_ref) = -(c z²)·(dKPlusSum + 324·q(z)·Φ_ref)`, so it is
`O(‖q(τ)‖(scale τ)^N(1+t)^M e^{-2πt})` — the `(γ)` weight.  The factor `|c z²|` is handled by the
`(1+t)`-power of the calculus (`‖z‖ ≤ 2(1+t)` on the strip). -/

/-- `z = O(1+t)` on the strip `0 ≤ Re z ≤ 1`, `Im z = t`. -/
theorem Bound2_zC : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) => (z : ℂ)) 0 0 := by
  refine Bound2.of_le_qz (K := 0) (C := 2) (N := 0) (M := 1) (by norm_num) le_rfl
    (by norm_num) ?_
  intro τ z t hF ht hz0 hz1 hzim
  have h1 : ‖(z : ℂ)‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  have h2 : |z.re| ≤ 1 := abs_le.mpr ⟨by linarith, hz1⟩
  have h3 : |z.im| = t := by rw [abs_of_pos z.im_pos, hzim]
  have ht0 : (0 : ℝ) ≤ t := by have := hF.2; linarith
  rw [Real.rpow_zero, Real.rpow_one, pow_zero]
  simp only [mul_one, one_mul]
  linarith

/-- `z² = O((1+t)²)` on the strip. -/
theorem Bound2_zC_sq : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) => (z : ℂ) ^ 2) 0 0 :=
  (Bound2_zC.mul Bound2_zC).congr (fun τ z => by ring)

/-- **The `dKPlus24` `E(z)²`-remainder**, in `Bound2` form at the `(γ)` weight `(1,1)`. -/
theorem Bound2_dKPlus24_E2rem (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
      dKPlus24 ℓ τ z
        - (Work.Residues.Ept z) ^ 2
          * (324 * Work.Asymptotics.K24F.c * (z : ℂ) ^ 2
              * Work.Asymptotics.K24F.Phiref τ z)) 1 1 := by
  have hA : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
      dKPlusSum τ z + 324 * Work.Kernels.qParamFun z
        * Work.Asymptotics.K24F.Phiref τ z) 1 1 := Bound2_dKPlusSum_E2rem11 ℓ
  have h : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
      -(Work.Asymptotics.K24F.c * (z : ℂ) ^ 2)
        * (dKPlusSum τ z + 324 * Work.Kernels.qParamFun z
            * Work.Asymptotics.K24F.Phiref τ z)) 1 1 :=
    (((Bound2.const Work.Asymptotics.K24F.c).mul Bound2_zC_sq).mul hA).neg.congr
      (fun τ z => by ring)
  exact h.congr (fun τ z => by
    simp only [dKPlus24]
    rw [Work.Asymptotics.K24F.qParamFun_eq_Ept_sq' z]
    ring)

/-- **The `dKPlus24` `E(z)²`-remainder, raw form** (the `K₊` half of `(γ)`). -/
theorem dKPlus24_E2rem_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖dKPlus24 ℓ τ z
            - (Work.Residues.Ept z) ^ 2
              * (324 * Work.Asymptotics.K24F.c * (z : ℂ) ^ 2
                  * Work.Asymptotics.K24F.Phiref τ z)‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
            * ‖Work.Kernels.qParamFun z‖ := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := Bound2_dKPlus24_E2rem ℓ
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have h := hb τ z t hF ht hz0 hz1 hzim
  have hconv : C * (‖Work.Kernels.qParamFun τ‖ ^ (1 : ℤ) * (Work.Kernels.scale τ) ^ N
      * (1 + t) ^ M * ‖Work.Kernels.qParamFun z‖ ^ (1 : ℤ))
      = C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * ‖Work.Kernels.qParamFun z‖ := by
    rw [show ‖Work.Kernels.qParamFun τ‖ ^ (1 : ℤ) = ‖Work.Kernels.qParamFun τ‖ from zpow_one _,
      show ‖Work.Kernels.qParamFun z‖ ^ (1 : ℤ) = ‖Work.Kernels.qParamFun z‖ from zpow_one _]
    ring
  rw [hconv] at h
  exact h

end

end Work.Asymptotics.KhatE1Core
