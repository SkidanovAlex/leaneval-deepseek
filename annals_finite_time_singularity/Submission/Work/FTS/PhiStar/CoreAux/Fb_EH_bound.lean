/-
# `FTS/PhiStar/CoreAux/Fb_EH_bound.lean` — the flat bound for the `EH`-field

`Work.FTS.PhiStar.EH α Y = 2Y + 2α sin²θ·(Y/(z+1) + z∂_zY) + sin(2θ)·∂_θY` is the
`((z+1)/z)·ℛ(Φ̃_*)`-field of `FieldsDefs.lean`.  The task `Fb_EH_bound` asks for

`Fb 6 (A(K+1)) Y  ⟹  Fb 4 (C·A⁴(K+1)(α+1)) (EH α Y)`

from the flat bounds `F0 6 A` of the six coefficient functions and `SmoothOpen Y`.

**Proof shape.**  The vocabulary is `FbEHDefs.lean`:

* `EhC α Y` is the same expression reassociated into a sum of *products* of the bounded
  coefficients with the blocks `Y`, `z∂_zY`, `∂_θY` (`eh_EH_eq_EhC`), and `EhD α Y` is the
  Leibniz expansion of `∂_θ(EH α Y)` (`eh_pth_EhC_eq`);
* each half is then bounded by the *bilinear* flat calculus `F0_mul`/`F0_add` (`F0_zpz` for
  `z∂_z`, `F0_zpz` at level `5` for `z∂_z` of the body and of `∂_θY`, `F0_Dth` for the angular
  derivative `D_θ(∂_θY)`), which is *linear* in the constant `A(K+1)` of the `Y`-blocks; the
  squared constants of `Fb_basic` are deliberately avoided (they would give `(K+1)²`);
* the bookkeeping of the powers of `A` is `ehB_mono`/`ehB_mono_alpha`: every monomial
  `c·A^j·(K+1)` and `c·α·A^j·(K+1)` with `j ≤ 4` and `c ≤ 4096` is `≤ 4096·A⁴(K+1)(α+1)`, so
  the accumulated constants are dominated by `16384·A⁴(K+1)(α+1)`.

The final constant is `16384`.  The proof is `sorry`-free and rests on
`[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.PhiStar.CoreAux.FieldsDefs
import Submission.Work.FTS.PhiStar.CoreAux.F0_mul
import Submission.Work.FTS.PhiStar.CoreAux.F0_add
import Submission.Work.FTS.PhiStar.CoreAux.F0_zpz
import Submission.Work.FTS.PhiStar.CoreAux.Fb_zpz
import Submission.Work.FTS.PhiStar.CoreAux.F0_congr
import Submission.Work.FTS.PhiStar.CoreAux.FbEHDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The two shape identities of the `EH`-field

`EhC` is `EH` reassociated (`Y z θ / (z+1)` read as `Y z θ * (1+z)⁻¹`), and `EhD` is the
Leibniz expansion of `∂_θ(EH α Y)`. -/

/-- **`EhC` is `EH`**: a pure reassociation, valid at every point (no quadrant hypothesis). -/
theorem eh_EH_eq_EhC {α : ℝ} {Y : ℝ → ℝ → ℝ} :
    ∀ z θ : ℝ, Work.FTS.PhiStar.EH α Y z θ = EhC α Y z θ := by
  intro z θ
  simp only [Work.FTS.PhiStar.EH, EhC, Work.FTS.PhiStar.Tblk, Work.Construction.s2,
    EhSin2, EhPhi1, EhX, EhRhoInv, div_eq_mul_inv]
  ring

/-- **`EhD` is `∂_θ(EhC)` on the open quadrant**: the product rule for the four factors of
`EhC`, the coefficient derivatives `∂_θ(sin²θ) = sin 2θ` and `∂_θ(sin 2θ) = 2 cos 2θ`, the
vanishing `∂_θ(1+z)⁻¹ = 0` and the two structural identities
`∂_θ(z∂_zY) = z∂_z(∂_θY)` (`pth_zpz_smoothOpen`) and
`sin(2θ)·∂_θ(∂_θY) = D_θ(∂_θY)` (definitional). -/
theorem eh_pth_EhC_eq {α : ℝ} {Y : ℝ → ℝ → ℝ} (hY : Work.FTS.EllipticEst.SmoothOpen Y) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (EhC α Y) z θ = EhD α Y z θ := by
  intro z θ hz hθ hθ'
  have sP : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => 2 * Y z θ) :=
    SmoothOpen.const_mul hY 2
  have sQ : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)) :=
    SmoothOpen.const_mul (Fbq_smoothOpen_mul eh_smooth_ph1 (eh_smooth_EhX hY)) (2 * α)
  have sR : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => EhSin2 z θ * Work.Spaces.pth Y z θ) :=
    Fbq_smoothOpen_mul eh_smooth_sin2 hY.pth
  have sQR : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)
        + EhSin2 z θ * Work.Spaces.pth Y z θ) :=
    SmoothOpen.add sQ sR
  have sV : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => Y z θ * EhRhoInv z θ) :=
    Fbq_smoothOpen_mul hY eh_smooth_rhoinv
  have sU : Work.FTS.EllipticEst.SmoothOpen (Yblk Y) := eh_smooth_yblk hY
  -- additivity
  have h1 : Work.Spaces.pth (EhC α Y) z θ
      = Work.Spaces.pth (fun z θ : ℝ => 2 * Y z θ) z θ
        + Work.Spaces.pth (fun z θ : ℝ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)
            + EhSin2 z θ * Work.Spaces.pth Y z θ) z θ :=
    pth_add_Q0 (f := fun z θ : ℝ => 2 * Y z θ)
      (g := fun z θ : ℝ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)
        + EhSin2 z θ * Work.Spaces.pth Y z θ) sP sQR z θ hz hθ hθ'
  rw [h1]
  have h2 : Work.Spaces.pth (fun z θ : ℝ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)
        + EhSin2 z θ * Work.Spaces.pth Y z θ) z θ
      = Work.Spaces.pth (fun z θ : ℝ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)) z θ
        + Work.Spaces.pth (fun z θ : ℝ => EhSin2 z θ * Work.Spaces.pth Y z θ) z θ :=
    pth_add_Q0 (f := fun z θ : ℝ => (2 * α) * (EhPhi1 z θ * EhX Y z θ))
      (g := fun z θ : ℝ => EhSin2 z θ * Work.Spaces.pth Y z θ) sQ sR z θ hz hθ hθ'
  rw [h2]
  -- constant factors
  have h3 : Work.Spaces.pth (fun z θ : ℝ => 2 * Y z θ) z θ
      = 2 * Work.Spaces.pth Y z θ :=
    congrFun (congrFun (pth_const_mul (2 : ℝ) Y) z) θ
  rw [h3]
  have h4 : Work.Spaces.pth (fun z θ : ℝ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)) z θ
      = (2 * α) * Work.Spaces.pth (fun z θ : ℝ => EhPhi1 z θ * EhX Y z θ) z θ :=
    congrFun (congrFun (pth_const_mul (2 * α)
      (fun z θ : ℝ => EhPhi1 z θ * EhX Y z θ)) z) θ
  rw [h4]
  -- the product rules
  have h5 : Work.Spaces.pth (fun z θ : ℝ => EhPhi1 z θ * EhX Y z θ) z θ
      = Work.Spaces.pth EhPhi1 z θ * EhX Y z θ
        + EhPhi1 z θ * Work.Spaces.pth (EhX Y) z θ :=
    Fbq_pth_mul eh_smooth_ph1 (eh_smooth_EhX hY) z θ hz hθ hθ'
  rw [h5]
  have h6 : Work.Spaces.pth (EhX Y) z θ
      = Work.Spaces.pth (fun z θ : ℝ => Y z θ * EhRhoInv z θ) z θ
        + Work.Spaces.pth (Yblk Y) z θ :=
    pth_add_Q0 (f := fun z θ : ℝ => Y z θ * EhRhoInv z θ) (g := Yblk Y) sV sU
      z θ hz hθ hθ'
  rw [h6]
  have h7 : Work.Spaces.pth (fun z θ : ℝ => Y z θ * EhRhoInv z θ) z θ
      = Work.Spaces.pth Y z θ * EhRhoInv z θ := by
    rw [Fbq_pth_mul (f := Y) (g := EhRhoInv) hY eh_smooth_rhoinv z θ hz hθ hθ',
      eh_pth_rhoinv z θ, mul_zero, add_zero]
  rw [h7]
  have h8 : Work.Spaces.pth (Yblk Y) z θ = Yblk (Work.Spaces.pth Y) z θ :=
    pth_zpz_smoothOpen hY z θ hz hθ hθ'
  rw [h8]
  have h9 : Work.Spaces.pth (fun z θ : ℝ => EhSin2 z θ * Work.Spaces.pth Y z θ) z θ
      = Work.Spaces.pth EhSin2 z θ * Work.Spaces.pth Y z θ
        + EhSin2 z θ * Work.Spaces.pth (Work.Spaces.pth Y) z θ :=
    Fbq_pth_mul eh_smooth_sin2 hY.pth z θ hz hθ hθ'
  rw [h9]
  -- the two coefficient derivatives
  have h10 : Work.Spaces.pth EhPhi1 z θ = EhDSinSq z θ := by
    rw [eh_pth_ph1 z θ, eh_sin2_eq_dsinsq z θ]
  rw [h10]
  have h11 : Work.Spaces.pth EhSin2 z θ = EhDSin2 z θ := eh_pth_sin2 z θ
  rw [h11]
  -- compare with `EhD`
  simp only [EhD, EhDX, Work.Spaces.Dth, EhSin2] <;> ring

/-! ## The bookkeeping of the powers of `A`

Every constant produced below is a monomial `c·A^j·(K+1)` or `c·α·A^j·(K+1)` with `j ≤ 4` and
a universal coefficient `c ≤ 4096`; these two lemmas turn each of them into the final
constant `4096·A⁴(K+1)(α+1)`. -/

private theorem ehB_mono {c C A K α : ℝ} {j : ℕ} (hA : 1 ≤ A) (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hj : j ≤ 4) (hc0 : 0 ≤ c) (hcC : c ≤ C) :
    c * A ^ j * (K + 1) ≤ C * A ^ 4 * (K + 1) * (α + 1) := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have hC0 : (0 : ℝ) ≤ C := le_trans hc0 hcC
  have hkp1 : (0 : ℝ) ≤ K + 1 := by linarith
  have hCA : c * A ^ j ≤ C * A ^ 4 :=
    calc c * A ^ j ≤ C * A ^ j := mul_le_mul_of_nonneg_right hcC (pow_nonneg hA0 j)
      _ ≤ C * A ^ 4 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA hj) hC0
  calc c * A ^ j * (K + 1) ≤ (C * A ^ 4) * (K + 1) := mul_le_mul_of_nonneg_right hCA hkp1
    _ ≤ (C * A ^ 4) * ((K + 1) * (α + 1)) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hkp1 (by linarith))
          (mul_nonneg hC0 (pow_nonneg hA0 4))
    _ = C * A ^ 4 * (K + 1) * (α + 1) := by ring

private theorem ehB_mono_alpha {c C A K α : ℝ} {j : ℕ} (hA : 1 ≤ A) (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hj : j ≤ 4) (hc0 : 0 ≤ c) (hcC : c ≤ C) :
    c * α * A ^ j * (K + 1) ≤ C * A ^ 4 * (K + 1) * (α + 1) := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have hC0 : (0 : ℝ) ≤ C := le_trans hc0 hcC
  have hkp1 : (0 : ℝ) ≤ K + 1 := by linarith
  have hC4 : (0 : ℝ) ≤ C * A ^ 4 := mul_nonneg hC0 (pow_nonneg hA0 4)
  have hCA : c * A ^ j ≤ C * A ^ 4 :=
    calc c * A ^ j ≤ C * A ^ j := mul_le_mul_of_nonneg_right hcC (pow_nonneg hA0 j)
      _ ≤ C * A ^ 4 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA hj) hC0
  calc c * α * A ^ j * (K + 1) = (c * A ^ j) * (α * (K + 1)) := by ring
    _ ≤ (C * A ^ 4) * (α * (K + 1)) := mul_le_mul hCA le_rfl (mul_nonneg hα hkp1) hC4
    _ ≤ (C * A ^ 4) * ((α + 1) * (K + 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hkp1) hC4
    _ = C * A ^ 4 * (K + 1) * (α + 1) := by ring

/-! ## The intermediate constants -/

/-- The level-`4` flat constant of the body `EhX Y = Y/(1+z) + z∂_zY` (and of `EhDX Y`). -/
private def ehBX (A K : ℝ) : ℝ := 16 * A ^ 2 * (K + 1) + 6 * A * (K + 1)

/-- The level-`4` constant of a product of one angular coefficient (`sin²θ`, `sin 2θ`,
`2 sinθcosθ`, `∂_θ(sin 2θ) = 2cos2θ`) with one of the blocks `EhX Y`, `EhDX Y`. -/
private def ehBC2 (A K : ℝ) : ℝ := 256 * A ^ 3 * (K + 1) + 96 * A ^ 2 * (K + 1)

/-- The accumulated constant of `F0 4 (EhC α Y)`. -/
private def ehBTC (A K α : ℝ) : ℝ :=
  2 * A * (K + 1) + (2 * α * ehBC2 A K + 16 * A ^ 2 * (K + 1))

/-- The accumulated constant of `F0 4 (EhD α Y)`. -/
private def ehBTD (A K α : ℝ) : ℝ :=
  2 * A * (K + 1) + (2 * α * (ehBC2 A K + ehBC2 A K)
    + (32 * A ^ 2 * (K + 1) + A * (K + 1)))

/-! ## The main theorem -/

theorem Fb_EH_bound : ∃ C : ℝ, 0 < C ∧ ∀ (α K A : ℝ) (Y : ℝ → ℝ → ℝ), 0 ≤ α → 0 ≤ K → 1 ≤ A → Work.FTS.EllipticEst.SmoothOpen Y → Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin θ ^ 2) → Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) → Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos (2 * θ)) → Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin (2 * θ)) → Work.FTS.PhiStar.F0 6 A (fun z _ => z / (1 + z)) → Work.FTS.PhiStar.F0 6 A (fun z _ => (1 + z)⁻¹) → Work.FTS.PhiStar.Fb 6 (A * (K + 1)) Y → Work.FTS.PhiStar.Fb 4 (C * A ^ 4 * (K + 1) * (α + 1)) (Work.FTS.PhiStar.EH α Y) := by
  refine ⟨16384, by norm_num, ?_⟩
  intro α K A Y hα hK hA hYs hph1 _hcc2 hcos2 hsin2 _hzrho hrhoinv hY
  -- the coefficient hypotheses in the `Eh*` vocabulary
  have hφ1 : Work.FTS.PhiStar.F0 6 A EhPhi1 := by
    show Work.FTS.PhiStar.F0 6 A (fun _ θ : ℝ => Real.sin θ ^ 2)
    exact hph1
  have hco2 : Work.FTS.PhiStar.F0 6 A EhCos2 := by
    show Work.FTS.PhiStar.F0 6 A (fun _ θ : ℝ => Real.cos (2 * θ))
    exact hcos2
  have hsi2 : Work.FTS.PhiStar.F0 6 A EhSin2 := by
    show Work.FTS.PhiStar.F0 6 A (fun _ θ : ℝ => Real.sin (2 * θ))
    exact hsin2
  have hri : Work.FTS.PhiStar.F0 6 A EhRhoInv := by
    show Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => (1 + z)⁻¹)
    exact hrhoinv
  -- basic bookkeeping
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have hkp1 : (0 : ℝ) ≤ K + 1 := by linarith
  have hM : (0 : ℝ) ≤ A * (K + 1) := mul_nonneg hA0 hkp1
  have h2A0 : (0 : ℝ) ≤ 2 * A := by linarith
  have h2a0 : (0 : ℝ) ≤ 2 * α := by linarith
  have hfc : (2 : ℝ) ^ 4 = 16 := by norm_num
  have hsix : (((5 : ℕ) : ℝ) + 1) = 6 := by norm_num
  have hKX0 : (0 : ℝ) ≤ ehBX A K := by
    have h1 : (0 : ℝ) ≤ 16 * A ^ 2 * (K + 1) :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hA0 2)) hkp1
    have h2 : (0 : ℝ) ≤ 6 * A * (K + 1) := mul_nonneg (mul_nonneg (by norm_num) hA0) hkp1
    simp only [ehBX]
    linarith
  -- the shifted blocks of `Y`
  have hY4 : Work.FTS.PhiStar.Fb 4 (A * (K + 1)) Y := hY.mono (by norm_num) le_rfl
  have hY5p : Work.FTS.PhiStar.F0 5 (A * (K + 1)) (Work.Spaces.pth Y) :=
    hY.fd.mono (by norm_num) le_rfl
  -- the coefficients at level `4`
  have hph1_4 : Work.FTS.PhiStar.F0 4 A EhPhi1 := hφ1.mono (by norm_num) le_rfl
  have hrho4 : Work.FTS.PhiStar.F0 4 A EhRhoInv := hri.mono (by norm_num) le_rfl
  have hsin2_4 : Work.FTS.PhiStar.F0 4 A EhSin2 := hsi2.mono (by norm_num) le_rfl
  have hcos2_4 : Work.FTS.PhiStar.F0 4 A EhCos2 := hco2.mono (by norm_num) le_rfl
  have hdsinsq : Work.FTS.PhiStar.F0 4 A EhDSinSq := eh_F0_dsinsq hsin2_4
  have hdsin2 : Work.FTS.PhiStar.F0 4 (2 * A) EhDSin2 := by
    have h := eh_F0_dsin2 hcos2_4
    have hc : |(2 : ℝ)| * A = 2 * A := by rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rwa [hc] at h
  -- smoothness of the blocks
  have hsX : Work.FTS.EllipticEst.SmoothOpen (EhX Y) := eh_smooth_EhX hYs
  have hsDX : Work.FTS.EllipticEst.SmoothOpen (EhDX Y) := eh_smooth_EhDX hYs
  have hsPY : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth Y) := hYs.pth
  have hsPh1X : Work.FTS.EllipticEst.SmoothOpen (fun z θ => EhPhi1 z θ * EhX Y z θ) :=
    Fbq_smoothOpen_mul eh_smooth_ph1 hsX
  have hsDSX : Work.FTS.EllipticEst.SmoothOpen (fun z θ => EhDSinSq z θ * EhX Y z θ) :=
    Fbq_smoothOpen_mul eh_smooth_dsinsq hsX
  have hsPh1DX : Work.FTS.EllipticEst.SmoothOpen (fun z θ => EhPhi1 z θ * EhDX Y z θ) :=
    Fbq_smoothOpen_mul eh_smooth_ph1 hsDX
  have hsSin2PY : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => EhSin2 z θ * Work.Spaces.pth Y z θ) :=
    Fbq_smoothOpen_mul eh_smooth_sin2 hsPY
  have hsDSin2PY : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => EhDSin2 z θ * Work.Spaces.pth Y z θ) :=
    Fbq_smoothOpen_mul eh_smooth_dsin2 hsPY
  have hsDth : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth (Work.Spaces.pth Y)) :=
    hsPY.Dth
  -- ---- the body `EhX Y` and its `θ`-derivative
  have hXmul : Work.FTS.PhiStar.F0 4 (16 * A ^ 2 * (K + 1))
      (fun z θ => Y z θ * EhRhoInv z θ) := by
    have h := F0_mul hM hA0 hYs eh_smooth_rhoinv hY4.f0 hrho4
    exact h.mono le_rfl (le_of_eq (by rw [hfc] <;> ring))
  have hYblk : Work.FTS.PhiStar.F0 4 (6 * A * (K + 1)) (Yblk Y) := by
    have h := F0_zpz (n := 5) hM hYs hY.f0
    exact h.mono (by norm_num) (le_of_eq (by rw [hsix] <;> ring))
  have hX : Work.FTS.PhiStar.F0 4 (ehBX A K) (EhX Y) :=
    F0_congr (fun z θ _ _ _ => rfl)
      ((F0_add (Fbq_smoothOpen_mul hYs eh_smooth_rhoinv) (eh_smooth_yblk hYs)
        hXmul hYblk).mono le_rfl (le_of_eq (by simp only [ehBX] <;> ring)))
  have hDXmul : Work.FTS.PhiStar.F0 4 (16 * A ^ 2 * (K + 1))
      (fun z θ => Work.Spaces.pth Y z θ * EhRhoInv z θ) := by
    have h := F0_mul hM hA0 hYs.pth eh_smooth_rhoinv hY4.fd hrho4
    exact h.mono le_rfl (le_of_eq (by rw [hfc] <;> ring))
  have hYblkP : Work.FTS.PhiStar.F0 4 (6 * A * (K + 1)) (Yblk (Work.Spaces.pth Y)) := by
    have h := F0_zpz (n := 5) hM hYs.pth hY.fd
    exact h.mono (by norm_num) (le_of_eq (by rw [hsix] <;> ring))
  have hDX : Work.FTS.PhiStar.F0 4 (ehBX A K) (EhDX Y) :=
    F0_congr (fun z θ _ _ _ => rfl)
      ((F0_add (Fbq_smoothOpen_mul hYs.pth eh_smooth_rhoinv) (eh_smooth_yblk hYs.pth)
        hDXmul hYblkP).mono le_rfl (le_of_eq (by simp only [ehBX] <;> ring)))
  -- ---- the three summands of `EhC α Y`
  have hC1 : Work.FTS.PhiStar.F0 4 (2 * A * (K + 1)) (fun z θ => 2 * Y z θ) := by
    have h := F0_const_mul (2 : ℝ) hY4.f0
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    exact h.mono le_rfl (le_of_eq (by ring))
  have hC2a : Work.FTS.PhiStar.F0 4 (ehBC2 A K) (fun z θ => EhPhi1 z θ * EhX Y z θ) := by
    have h := F0_mul hA0 hKX0 eh_smooth_ph1 hsX hph1_4 hX
    exact h.mono le_rfl (le_of_eq (by simp only [ehBC2, ehBX, hfc] <;> ring))
  have hC2b : Work.FTS.PhiStar.F0 4 (2 * α * ehBC2 A K)
      (fun z θ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)) := by
    have h := F0_const_mul (2 * α) hC2a
    rw [abs_of_nonneg h2a0] at h
    exact h.mono le_rfl (le_of_eq (by ring))
  have hC3 : Work.FTS.PhiStar.F0 4 (16 * A ^ 2 * (K + 1))
      (fun z θ => EhSin2 z θ * Work.Spaces.pth Y z θ) := by
    have h := F0_mul hA0 hM eh_smooth_sin2 hsPY hsin2_4 hY4.fd
    exact h.mono le_rfl (le_of_eq (by rw [hfc] <;> ring))
  have hEhC : Work.FTS.PhiStar.F0 4 (ehBTC A K α) (EhC α Y) := by
    have hs2Y : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 2 * Y z θ) :=
      SmoothOpen.const_mul hYs 2
    have hs2aB : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)) :=
      SmoothOpen.const_mul hsPh1X (2 * α)
    exact F0_congr (fun z θ _ _ _ => rfl)
      ((F0_add hs2Y (SmoothOpen.add hs2aB hsSin2PY) hC1
        (F0_add hs2aB hsSin2PY hC2b hC3)).mono le_rfl
          (le_of_eq (by simp only [ehBTC] <;> ring)))
  -- ---- the three summands of `EhD α Y`
  have hD1 : Work.FTS.PhiStar.F0 4 (2 * A * (K + 1))
      (fun z θ => 2 * Work.Spaces.pth Y z θ) := by
    have h := F0_const_mul (2 : ℝ) hY4.fd
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    exact h.mono le_rfl (le_of_eq (by ring))
  have hD2a : Work.FTS.PhiStar.F0 4 (ehBC2 A K) (fun z θ => EhDSinSq z θ * EhX Y z θ) := by
    have h := F0_mul hA0 hKX0 eh_smooth_dsinsq hsX hdsinsq hX
    exact h.mono le_rfl (le_of_eq (by simp only [ehBC2, ehBX, hfc] <;> ring))
  have hD2b : Work.FTS.PhiStar.F0 4 (ehBC2 A K) (fun z θ => EhPhi1 z θ * EhDX Y z θ) := by
    have h := F0_mul hA0 hKX0 eh_smooth_ph1 hsDX hph1_4 hDX
    exact h.mono le_rfl (le_of_eq (by simp only [ehBC2, ehBX, hfc] <;> ring))
  have hD3a : Work.FTS.PhiStar.F0 4 (32 * A ^ 2 * (K + 1))
      (fun z θ => EhDSin2 z θ * Work.Spaces.pth Y z θ) := by
    have h := F0_mul h2A0 hM eh_smooth_dsin2 hsPY hdsin2 hY4.fd
    exact h.mono le_rfl (le_of_eq (by rw [hfc] <;> ring))
  have hD3b : Work.FTS.PhiStar.F0 4 (A * (K + 1)) (Work.Spaces.Dth (Work.Spaces.pth Y)) :=
    F0_Dth (n := 4) hY5p
  have hD3 : Work.FTS.PhiStar.F0 4 (32 * A ^ 2 * (K + 1) + A * (K + 1))
      (fun z θ => EhDSin2 z θ * Work.Spaces.pth Y z θ
        + Work.Spaces.Dth (Work.Spaces.pth Y) z θ) :=
    F0_add hsDSin2PY hsDth hD3a hD3b
  have hD2 : Work.FTS.PhiStar.F0 4 (2 * α * (ehBC2 A K + ehBC2 A K))
      (fun z θ => (2 * α) * (EhDSinSq z θ * EhX Y z θ + EhPhi1 z θ * EhDX Y z θ)) := by
    have hsum := F0_add hsDSX hsPh1DX hD2a hD2b
    have h := F0_const_mul (2 * α) hsum
    rw [abs_of_nonneg h2a0] at h
    exact h.mono le_rfl (le_of_eq (by ring))
  have hEhD : Work.FTS.PhiStar.F0 4 (ehBTD A K α) (EhD α Y) := by
    have hs2PY : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 2 * Work.Spaces.pth Y z θ) :=
      SmoothOpen.const_mul hsPY 2
    have hs2aD : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (2 * α) * (EhDSinSq z θ * EhX Y z θ + EhPhi1 z θ * EhDX Y z θ)) :=
      SmoothOpen.const_mul (SmoothOpen.add hsDSX hsPh1DX) (2 * α)
    have hsD3 : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => EhDSin2 z θ * Work.Spaces.pth Y z θ
          + Work.Spaces.Dth (Work.Spaces.pth Y) z θ) :=
      SmoothOpen.add hsDSin2PY hsDth
    have hDE := F0_add hs2aD hsD3 hD2 hD3
    exact F0_congr (fun z θ _ _ _ => rfl)
      ((F0_add hs2PY (SmoothOpen.add hs2aD hsD3) hD1 hDE).mono le_rfl
        (le_of_eq (by simp only [ehBTD] <;> ring)))
  -- ---- transfer to `EH` and `∂_θ(EH)` with the two identities
  have hEHf0 : Work.FTS.PhiStar.F0 4 (ehBTC A K α) (Work.FTS.PhiStar.EH α Y) :=
    F0_congr (fun z θ _ _ _ => eh_EH_eq_EhC z θ) hEhC
  have hEHfd : Work.FTS.PhiStar.F0 4 (ehBTD A K α)
      (Work.Spaces.pth (Work.FTS.PhiStar.EH α Y)) :=
    F0_congr (f := Work.Spaces.pth (Work.FTS.PhiStar.EH α Y)) (g := EhD α Y)
      (fun z θ hz hθ hθ' => by
        rw [pth_congr_Q0 (f := Work.FTS.PhiStar.EH α Y) (g := EhC α Y)
          (fun z θ _ _ _ => eh_EH_eq_EhC z θ) z θ hz hθ hθ']
        exact eh_pth_EhC_eq hYs z θ hz hθ hθ') hEhD
  -- ---- the arithmetic
  have h1 : 2 * A ^ 1 * (K + 1) ≤ 4096 * A ^ 4 * (K + 1) * (α + 1) :=
    ehB_mono (c := 2) (C := 4096) (j := 1) hA hK hα (by norm_num) (by norm_num) (by norm_num)
  have h2 : 16 * A ^ 2 * (K + 1) ≤ 4096 * A ^ 4 * (K + 1) * (α + 1) :=
    ehB_mono (c := 16) (C := 4096) (j := 2) hA hK hα (by norm_num) (by norm_num) (by norm_num)
  have h3 : 512 * α * A ^ 3 * (K + 1) ≤ 4096 * A ^ 4 * (K + 1) * (α + 1) :=
    ehB_mono_alpha (c := 512) (C := 4096) (j := 3) hA hK hα (by norm_num) (by norm_num)
      (by norm_num)
  have h4 : 192 * α * A ^ 2 * (K + 1) ≤ 4096 * A ^ 4 * (K + 1) * (α + 1) :=
    ehB_mono_alpha (c := 192) (C := 4096) (j := 2) hA hK hα (by norm_num) (by norm_num)
      (by norm_num)
  have h5 : 3 * A ^ 1 * (K + 1) ≤ 4096 * A ^ 4 * (K + 1) * (α + 1) :=
    ehB_mono (c := 3) (C := 4096) (j := 1) hA hK hα (by norm_num) (by norm_num) (by norm_num)
  have h6 : 32 * A ^ 2 * (K + 1) ≤ 4096 * A ^ 4 * (K + 1) * (α + 1) :=
    ehB_mono (c := 32) (C := 4096) (j := 2) hA hK hα (by norm_num) (by norm_num) (by norm_num)
  have h7 : 1024 * α * A ^ 3 * (K + 1) ≤ 4096 * A ^ 4 * (K + 1) * (α + 1) :=
    ehB_mono_alpha (c := 1024) (C := 4096) (j := 3) hA hK hα (by norm_num) (by norm_num)
      (by norm_num)
  have h8 : 384 * α * A ^ 2 * (K + 1) ≤ 4096 * A ^ 4 * (K + 1) * (α + 1) :=
    ehB_mono_alpha (c := 384) (C := 4096) (j := 2) hA hK hα (by norm_num) (by norm_num)
      (by norm_num)
  have hTC : ehBTC A K α ≤ 16384 * A ^ 4 * (K + 1) * (α + 1) := by
    have hexp : ehBTC A K α
        = 2 * A ^ 1 * (K + 1) + (512 * α * A ^ 3 * (K + 1) + 192 * α * A ^ 2 * (K + 1))
          + 16 * A ^ 2 * (K + 1) := by
      simp only [ehBTC, ehBC2]
      ring
    rw [hexp]
    linarith
  have hTD : ehBTD A K α ≤ 16384 * A ^ 4 * (K + 1) * (α + 1) := by
    have hexp : ehBTD A K α
        = 3 * A ^ 1 * (K + 1) + (1024 * α * A ^ 3 * (K + 1) + 384 * α * A ^ 2 * (K + 1))
          + 32 * A ^ 2 * (K + 1) := by
      simp only [ehBTD, ehBC2]
      ring
    rw [hexp]
    linarith
  exact Work.FTS.PhiStar.Fb.of_both (hEHf0.mono le_rfl hTC) (hEHfd.mono le_rfl hTD)

end Work.FTS.PhiStar.CoreAux
