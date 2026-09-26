import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.DSm1RowBound
import Submission.Work.Asymptotics.KhatE1Core.B24XMData
import Submission.Work.Asymptotics.KhatE1Core.Bracket24TailCore

/-!
# The `K₊`-truncation tail of the `d = 24` bracket

`KPlus24Group = -(c z²)(Sm1 + … + Sm5)` is the `K₊`-half of `X = Sh τ z·Bracket24`, and
`KPlus24GroupT` is the same expression with every `z`-atom replaced by its cusp truncation.
Here the truncation error is bounded by `(scale τ)^N (1+t)^M ‖Ept z‖⁴`.

The point of the file is that the `Sm_iRef`-reference of `Sm_i` (`Sm*Split`) uses the *same*
`q²`-truncated atoms as `Sm_iT`, so

* `Sm3 - Sm3T = dSm3`, `Sm4 - Sm4T = dSm4`, `Sm5 - Sm5T = dSm5`,
* `Sm1 - Sm1T = dSm1 + 324·E4Ref³·(q·Q₁ + W₀')·q`,
* `Sm2 - Sm2T = -(j(τ)·Phiref·dDq) - E4Ref³·Phiref·(Donly - 324q) - dE4c·Phiref·Donly`,

and each summand lands on weight `(0,2)` in the `Bound2` calculus
(`‖·‖ ≤ C q_τ^n (scale τ)^N (1+t)^M q_z^k`), using the `q_τ`-`q_z` trade `Bound2.shift`
(`q_z ≤ q_τ` on the strip).
-/

set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane
open Work.Residues (Ept)

noncomputable section

/-! ## Auxiliary `Bound2` atoms -/

/-- `z² = O((1+t)²)`. -/
lemma Bound2_zsq : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) => (z : ℂ) ^ 2) 0 0 := by
  refine ⟨2, 0, 2, by norm_num, le_rfl, by norm_num, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have ht0 : (0 : ℝ) ≤ t := by have := hF.2; linarith
  have h2 : ‖(z : ℂ)‖ ≤ |(z : ℂ).re| + |(z : ℂ).im| := Complex.norm_le_abs_re_add_abs_im z
  have h3 : |(z : ℂ).re| ≤ 1 := by
    rw [show (z : ℂ).re = z.re from rfl]
    exact abs_le.mpr ⟨by linarith, hz1⟩
  have h4 : |(z : ℂ).im| = t := by
    rw [show (z : ℂ).im = z.im from rfl, abs_of_pos z.im_pos, hzim]
  have h1 : ‖(z : ℂ)‖ ≤ 1 + t := by linarith
  have h5 : (0 : ℝ) ≤ 1 + t := by linarith
  have h6 : ‖(z : ℂ) ^ 2‖ = ‖(z : ℂ)‖ ^ 2 := norm_pow _ 2
  have h7 : (1 + t) ^ (2 : ℝ) = (1 + t) ^ 2 := Real.rpow_natCast (1 + t) 2
  rw [h6, h7]
  simp only [zpow_zero, Real.rpow_zero, mul_one, one_mul]
  nlinarith [h1, h5, norm_nonneg (z : ℂ)]

/-- `Δ(z)⁻¹ - (q⁻¹ + 24 + 324q) = O(‖q(z)‖²)`. -/
lemma Bound2_Donly_sub_d1T :
    Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) =>
      Donly z - 324 * Work.Kernels.qParamFun z) 0 2 := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.KhatE1Core.invDeltaSecondOrder
  refine ⟨C, 0, 0, hC, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  dsimp only
  have hz1' : (1 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
  have h := hb z hz1'
  have hE : (Work.Residues.Ept z)⁻¹ ^ 2 = (Work.Kernels.qParamFun z)⁻¹ := by
    rw [Work.Asymptotics.K24F.qParamFun_eq_Ept_sq']
    field_simp
  have hkey : Donly z - 324 * Work.Kernels.qParamFun z
      = (Work.Kernels.DeltaFun z)⁻¹ - ((Work.Kernels.qParamFun z)⁻¹ + 24
          + 324 * Work.Kernels.qParamFun z) := by
    simp only [Donly, DeltaInvRef]
    ring
  have hqE : ‖Work.Residues.Ept z‖ ^ 4 = ‖Work.Kernels.qParamFun z‖ ^ 2 := by
    rw [Work.Asymptotics.K24F.qParamFun_eq_Ept_sq', norm_pow]
    ring
  rw [hkey]
  rw [hE, hqE] at h
  have hR : C * (‖Work.Kernels.qParamFun τ‖ ^ (0 : ℤ) * (Work.Kernels.scale τ) ^ (0 : ℝ)
        * (1 + t) ^ (0 : ℝ) * ‖Work.Kernels.qParamFun z‖ ^ (2 : ℤ))
      = C * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
    rw [zpow_zero, Real.rpow_zero, Real.rpow_zero, zpow_ofNat]
    ring
  rw [hR]; exact h

/-! ## Reference/truncation comparisons -/

lemma E4Ref_eq_E4T (z : ℍ) : E4Ref z = E4T z := by
  simp only [E4Ref, E4T, Tq]

lemma E6Ref_eq_E6T (z : ℍ) : E6Ref z = E6T z := by
  simp only [E6Ref, E6T, Tq]

lemma E2SRef_eq_E2ST (z : ℍ) : E2SRef z = E2ST z := by
  simp only [E2SRef, E2ST, Tq, Work.Asymptotics.K24F.S0, Work.Asymptotics.KhatE1.S0z]

lemma S0z_eq_S0 (z : ℍ) : Work.Asymptotics.KhatE1.S0z z = Work.Asymptotics.K24F.S0 z := by
  simp only [Work.Asymptotics.KhatE1.S0z, Work.Asymptotics.K24F.S0]

lemma I4zRef_eq_invE4T (z : ℍ) : I4zRef z = invE4T z := by
  simp only [I4zRef, invE4T, Tq]

lemma E14Ref_eq_E14T (z : ℍ) : E14Ref z = E14T z := by
  simp only [E14Ref, E14T, Tq]

lemma I4Ref_eq_invE4cubeT (z : ℍ) : I4Ref z = invE4cubeT z := by
  simp only [I4Ref, invE4cubeT, Tq]

lemma DeltaRef_eq_DeltaT (z : ℍ) : DeltaRef z = DeltaT z := by
  simp only [DeltaRef, DqRef, DeltaT, Tq]
  ring

lemma DeltaInvRef_sub_invDeltaT (z : ℍ) :
    DeltaInvRef z - invDeltaT z = -324 * Work.Kernels.qParamFun z := by
  simp only [DeltaInvRef, invDeltaT, Tq]
  ring

lemma PhiRef_eq_PhiT (τ z : ℍ) : PhiRef τ z = PhiT τ z := by
  simp only [PhiRef, PhiT, PfunRef, PfunT, VfunRef, VfunT, I4Ref, invE4cubeT, E4Ref, E4T,
    E2SRef, E2ST, E14Ref, E14T, Tq, Work.Asymptotics.K24F.S0, Work.Asymptotics.KhatE1.S0z,
    Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four]
  ring

lemma UfunRef_eq_UfunT (τ z : ℍ) : UfunRef τ z = UfunT τ z := by
  simp only [UfunRef, UfunT, E4Ref, E4T, E2SRef, E2ST, Tq, S0z_eq_S0]

lemma Sm3Ref_eq_Sm3T (τ z : ℍ) : Sm3Ref τ z = Sm3T τ z := by
  simp only [Sm3Ref, Sm3T, E4Ref_eq_E4T, E6Ref_eq_E6T, E2SRef_eq_E2ST, I4zRef_eq_invE4T,
    S0z_eq_S0]

lemma Sm4Ref_eq_Sm4T (τ z : ℍ) : Sm4Ref τ z = Sm4T τ z := by
  simp only [Sm4Ref, Sm4T, UfunRef_eq_UfunT, E4Ref_eq_E4T]

lemma Sm5Ref_eq_Sm5T (τ z : ℍ) : Sm5Ref τ z = Sm5T τ z := by
  simp only [Sm5Ref, Sm5T, DeltaRef_eq_DeltaT]

/-! ## The five rows -/

theorem Bound2_Sm1T_dev (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun τ z => Work.Asymptotics.K24F.Sm1 τ z - Sm1T τ z) 0 2 := by
  have hSR : ∀ τ z : ℍ, Sm1Ref τ z - Sm1T τ z
      = 324 * E4Ref z ^ 3 * Work.Asymptotics.K24F.Q1 τ z * Work.Kernels.qParamFun z ^ 2
        + 324 * E4Ref z ^ 3 * W0' τ z * Work.Kernels.qParamFun z := by
    intro τ z
    simp only [Sm1Ref, Sm1T, W0', PhiRef, PhiT, PfunRef, PfunT, VfunRef, VfunT,
      E4Ref_eq_E4T, E6Ref_eq_E6T, E2SRef_eq_E2ST, E14Ref_eq_E14T, I4Ref_eq_invE4cubeT,
      S0z_eq_S0, DeltaInvRef, invDeltaT, Tq,
      Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four]
    ring
  have h1 : Bound2 (fun τ z => dSm1 τ z) 0 2 := Bound2_dSm1
  have h2 : Bound2 (fun τ z =>
      324 * E4Ref z ^ 3 * Work.Asymptotics.K24F.Q1 τ z * Work.Kernels.qParamFun z ^ 2) 0 2 :=
    ((((Bound2.const (324 : ℂ)).mul Bound2_E4Ref3).mul Bound2_Q1).mul
      (Bound2_qparam.mul Bound2_qparam)).congr (fun τ z => by ring)
  have h3 : Bound2 (fun τ z =>
      324 * E4Ref z ^ 3 * W0' τ z * Work.Kernels.qParamFun z) 0 2 :=
    (((Bound2.const (324 : ℂ)).mul Bound2_E4Ref3).mul Bound2_W0').mul Bound2_qparam
  refine (h1.add (h2.add h3)).congr (fun τ z => ?_)
  have hSR' := hSR τ z
  rw [Sm1_eq_ref_add]
  rw [show Sm1Ref τ z + dSm1 τ z - Sm1T τ z = dSm1 τ z + (Sm1Ref τ z - Sm1T τ z) by ring,
    hSR']

theorem Bound2_Sm2T_dev (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun τ z => Work.Asymptotics.K24F.Sm2 τ z - Sm2T τ z) 0 2 := by
  have hSR : ∀ τ z : ℍ, Sm2Ref τ z - Sm2T τ z
      = E4Ref z ^ 3 * Work.Asymptotics.K24F.Phiref τ z
          * (324 * Work.Kernels.qParamFun z) := by
    intro τ z
    have hq : Work.Kernels.qParamFun z ≠ 0 := Work.Asymptotics.qParamFun_ne_zero' z
    simp only [Sm2Ref, Sm2T, DeltaT, d1T, E4Ref, E4T, Tq]
    field_simp
    ring
  have h1 : Bound2 (fun τ z =>
      -(Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Phiref τ z * dDq z)) 0 2 :=
    ((Bound2_j.mul Bound2_Phiref).mul Bound2_dDq).neg.shift
  have h2 : Bound2 (fun τ z =>
      -(E4Ref z ^ 3 * Work.Asymptotics.K24F.Phiref τ z
          * (Donly z - 324 * Work.Kernels.qParamFun z))) 0 2 :=
    ((Bound2_E4Ref3.mul Bound2_Phiref).mul Bound2_Donly_sub_d1T).neg
  have h3 : Bound2 (fun τ z => -(dE4c z * Work.Asymptotics.K24F.Phiref τ z * Donly z)) 0 2 :=
    ((Bound2_dE4c.mul Bound2_Phiref).mul Bound2_Donly).neg.mono (le_refl 0) (by norm_num)
  refine (h1.add (h2.add h3)).congr (fun τ z => ?_)
  have hSR' := hSR τ z
  rw [Sm2_eq_ref_add]
  rw [show Sm2Ref τ z + dSm2 τ z - Sm2T τ z = dSm2 τ z + (Sm2Ref τ z - Sm2T τ z) by ring,
    hSR']
  simp only [dSm2]
  ring

theorem Bound2_Sm3T_dev (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun τ z => Work.Asymptotics.K24F.Sm3 τ z - Sm3T τ z) 0 2 := by
  have h : Bound2 (fun τ z => Work.Asymptotics.K24F.Sm3 τ z - Sm3T τ z) (-1) 3 :=
    Bound2_dSm3.congr (fun τ z => by
      rw [Sm3_eq_ref_add, Sm3Ref_eq_Sm3T]
      ring)
  simpa using h.shift

theorem Bound2_Sm4T_dev (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun τ z => Work.Asymptotics.K24F.Sm4 τ z - Sm4T τ z) 0 2 := by
  have h : Bound2 (fun τ z => Work.Asymptotics.K24F.Sm4 τ z - Sm4T τ z) 0 3 :=
    (Bound2_dSm4 ℓ).congr (fun τ z => by
      rw [Sm4_eq_ref_add, Sm4Ref_eq_Sm4T]
      ring)
  exact h.mono (le_refl 0) (by norm_num)

theorem Bound2_Sm5T_dev (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun τ z => Work.Asymptotics.K24F.Sm5 τ z - Sm5T τ z) 0 2 := by
  have h : Bound2 (fun τ z => Work.Asymptotics.K24F.Sm5 τ z - Sm5T τ z) (-1) 3 :=
    (Bound2_dSm5 ℓ).congr (fun τ z => by
      rw [Sm5_eq_ref_add, Sm5Ref_eq_Sm5T]
      ring)
  simpa using h.shift

/-! ## Assembly -/

theorem Bound2_KPlusDev (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun τ z => KPlus24Group ℓ τ z - KPlus24GroupT τ z) 0 2 := by
  have hsum : Bound2 (fun τ z =>
      (Work.Asymptotics.K24F.Sm1 τ z - Sm1T τ z)
      + ((Work.Asymptotics.K24F.Sm2 τ z - Sm2T τ z)
      + ((Work.Asymptotics.K24F.Sm3 τ z - Sm3T τ z)
      + ((Work.Asymptotics.K24F.Sm4 τ z - Sm4T τ z)
      + (Work.Asymptotics.K24F.Sm5 τ z - Sm5T τ z))))) 0 2 :=
    ((Bound2_Sm1T_dev ℓ).add ((Bound2_Sm2T_dev ℓ).add ((Bound2_Sm3T_dev ℓ).add
      ((Bound2_Sm4T_dev ℓ).add (Bound2_Sm5T_dev ℓ))))).mono (by decide) (by decide)
  have hmain : Bound2 (fun τ z =>
      (-Work.Asymptotics.K24F.c * (z : ℂ) ^ 2) *
        ((Work.Asymptotics.K24F.Sm1 τ z - Sm1T τ z)
        + ((Work.Asymptotics.K24F.Sm2 τ z - Sm2T τ z)
        + ((Work.Asymptotics.K24F.Sm3 τ z - Sm3T τ z)
        + ((Work.Asymptotics.K24F.Sm4 τ z - Sm4T τ z)
        + (Work.Asymptotics.K24F.Sm5 τ z - Sm5T τ z)))))) 0 2 :=
    (((Bound2.const (-Work.Asymptotics.K24F.c)).mul Bound2_zsq).mul hsum).mono
      (by decide) (by decide)
  exact hmain.congr (fun τ z => by
    simp only [KPlus24Group, KPlus24GroupT]
    ring)

/-- **`K₊`-truncation tail.** -/
theorem KPlus24GroupT_tail (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.KhatE1Core.KPlus24Group ℓ τ z
            - Work.Asymptotics.KhatE1Core.KPlus24GroupT τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M * ‖Ept z‖ ^ 4 := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := Bound2_KPlusDev ℓ
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have h := hb τ z t hF ht hz0 hz1 hzim
  have hqE : ‖Work.Kernels.qParamFun z‖ ^ (2 : ℤ) = ‖Work.Residues.Ept z‖ ^ 4 := by
    rw [zpow_ofNat, Work.Asymptotics.K24F.qParamFun_eq_Ept_sq', norm_pow]
    ring
  rw [hqE] at h
  refine le_trans h ?_
  apply le_of_eq
  rw [zpow_zero]
  ring

end

end Work.Asymptotics.KhatE1Core
