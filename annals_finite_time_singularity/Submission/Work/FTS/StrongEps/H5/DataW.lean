/-
# `H5/DataW` — the `𝒲^{4,∞}`-priced level-`5` product wrapper

The companion of `H5.Data.L5_mul` for the factors that are priced by the `𝒲^{4,∞}`-norm (the
star coefficients `((z+1)/z)ℛ(Φ̃_*)`, `((z+1)/z)U(Φ̃_*)/sin 2θ`, `((z+1)/z)V(Φ̃_*)` and the fixed
profiles `F_*`, `D_θF_*`, `D_zF_*`): from the level-four `𝒲^{4,∞}`-priced product rule and the
level shift,

`HkNorm α 5 (c·(F·G)) ≤ 3|c| (C α^{-1/2}) a b`

where `a` bounds `|F|_{𝒲^{4,∞}}`, `|D_zF|_{𝒲^{4,∞}}`, `|D_θF|_{𝒲^{4,∞}}` (`W5 α F a`) and `b`
bounds `|G|_{ℋ⁴}`, `|D_zG|_{ℋ⁴}`, `|D_θG|_{ℋ⁴}` (`L5 α G b`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.H5.Data

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5

open Work.Spaces
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The level-`5` product of a `𝒲^{4,∞}`-priced factor with an `ℋ⁴`-honest factor**, from the
level-four `𝒲^{4,∞}`-priced product rule and the level shift. -/
theorem W5_mul {α Cw : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCw : 0 < Cw)
    (hfield : ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g)
    {F G : Fn} {c a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hF : W5 α F a) (hG : L5 α G b) :
    Work.Spaces.HkMem α 5 (fun z θ => c * (F z θ * G z θ)) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => c * (F z θ * G z θ))
        ≤ |c| * (3 * (Cw * α ^ (-(1 / 2 : ℝ)) * a * b)) := by
  have hAr : 0 ≤ Cw * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCw.le (Real.rpow_nonneg hα.le _)
  set P : ℝ := Cw * α ^ (-(1 / 2 : ℝ)) * a * b with hPdef
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    exact mul_nonneg (mul_nonneg hAr ha) hb
  -- ### the five level-four product estimates
  have hFG := hfield F G hF.sm hF.wm hG.qo
  have hDzFG := hfield (Dz F) G hF.smDz hF.wmDz hG.qo
  have hFDzG := hfield F (Dz G) hF.sm hF.wm hG.qoDz
  have hDthFG := hfield (Dth F) G hF.smDth hF.wmDth hG.qo
  have hFDthG := hfield F (Dth G) hF.sm hF.wm hG.qoDth
  have hsqFG : Work.Spaces.HkSq α 4 (fun z θ => F z θ * G z θ) ≤ P ^ 2 := by
    have hXn : Work.FTS.Nonlin.Xn α (fun z θ => F z θ * G z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * a * b :=
      le_trans hFG.2 (Pd_le hAr ha hb hF.wb hG.bd
        (Work.Spaces.WlInf_nonneg α 4 F hF.wm) (Work.Spaces.HkNorm_nonneg α 4 G))
    rw [sq_eq_Xn_sq α, hPdef]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn 2
  have hsqDz : Work.Spaces.HkSq α 4 (fun z θ => Dz F z θ * G z θ) ≤ P ^ 2 := by
    have hXn : Work.FTS.Nonlin.Xn α (fun z θ => Dz F z θ * G z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * a * b :=
      le_trans hDzFG.2 (Pd_le hAr ha hb hF.wbDz hG.bd
        (Work.Spaces.WlInf_nonneg α 4 (Dz F) hF.wmDz) (Work.Spaces.HkNorm_nonneg α 4 G))
    rw [sq_eq_Xn_sq α, hPdef]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn 2
  have hsqFDz : Work.Spaces.HkSq α 4 (fun z θ => F z θ * Dz G z θ) ≤ P ^ 2 := by
    have hXn : Work.FTS.Nonlin.Xn α (fun z θ => F z θ * Dz G z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * a * b :=
      le_trans hFDzG.2 (Pd_le hAr ha hb hF.wb hG.bdDz
        (Work.Spaces.WlInf_nonneg α 4 F hF.wm) (Work.Spaces.HkNorm_nonneg α 4 (Dz G)))
    rw [sq_eq_Xn_sq α, hPdef]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn 2
  have hsqDth : Work.Spaces.HkSq α 4 (fun z θ => Dth F z θ * G z θ) ≤ P ^ 2 := by
    have hXn : Work.FTS.Nonlin.Xn α (fun z θ => Dth F z θ * G z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * a * b :=
      le_trans hDthFG.2 (Pd_le hAr ha hb hF.wbDth hG.bd
        (Work.Spaces.WlInf_nonneg α 4 (Dth F) hF.wmDth) (Work.Spaces.HkNorm_nonneg α 4 G))
    rw [sq_eq_Xn_sq α, hPdef]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn 2
  have hsqFDth : Work.Spaces.HkSq α 4 (fun z θ => F z θ * Dth G z θ) ≤ P ^ 2 := by
    have hXn : Work.FTS.Nonlin.Xn α (fun z θ => F z θ * Dth G z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * a * b :=
      le_trans hFDthG.2 (Pd_le hAr ha hb hF.wb hG.bdDth
        (Work.Spaces.WlInf_nonneg α 4 F hF.wm) (Work.Spaces.HkNorm_nonneg α 4 (Dth G)))
    rw [sq_eq_Xn_sq α, hPdef]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn 2
  -- ### the level shift
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ * G z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hF.sm hG.qo.1
  have hsmDzG : Work.FTS.EllipticEst.SmoothOpen (Dz G) := hG.qoDz.1
  have hsmDthG : Work.FTS.EllipticEst.SmoothOpen (Dth G) := hG.qoDth.1
  have hDzm : Work.Spaces.HkMem α 4 (Dz (fun z θ => F z θ * G z θ)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
      (Work.FTS.EllipticEst.RPFresh.HkMem_add_open α 4
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hF.smDz hG.qo.1)
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hF.sm hsmDzG)
        hDzFG.1 hFDzG.1)
      (fun z hz θ hθ => (Dz_mul_eqOn_Q0 hF.sm hG.qo.1 z θ hz hθ.1 hθ.2).symm)
  have hDthm : Work.Spaces.HkMem α 4 (Dth (fun z θ => F z θ * G z θ)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
      (Work.FTS.EllipticEst.RPFresh.HkMem_add_open α 4
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hF.smDth hG.qo.1)
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hF.sm hsmDthG)
        hDthFG.1 hFDthG.1)
      (fun z hz θ hθ => (Dth_mul_eqOn_Q0 hF.sm hG.qo.1 z θ hz hθ.1 hθ.2).symm)
  have hsq5 : Work.Spaces.HkSq α 5 (fun z θ => F z θ * G z θ) ≤ 9 * P ^ 2 := by
    have hshift := HkSq_succ_le (α := α) (k := 4) hα hsm (by norm_num) hFG.1 hDzm hDthm
    have hDzsq : Work.Spaces.HkSq α 4 (Dz (fun z θ => F z θ * G z θ))
        ≤ 2 * (Work.Spaces.HkSq α 4 (fun z θ => Dz F z θ * G z θ)
            + Work.Spaces.HkSq α 4 (fun z θ => F z θ * Dz G z θ)) := by
      have h1 := Work.FTS.GalFields.RHS.HkSq_add_le_open α 4 hα
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hF.smDz hG.qo.1)
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hF.sm hsmDzG) hDzFG.1 hFDzG.1
      rwa [Work.FTS.EllipticEst.HkSq_congr_open α 4
        (fun z θ hz hθ hθ' => (Dz_mul_eqOn_Q0 hF.sm hG.qo.1 z θ hz hθ hθ').symm)] at h1
    have hDthsq : Work.Spaces.HkSq α 4 (Dth (fun z θ => F z θ * G z θ))
        ≤ 2 * (Work.Spaces.HkSq α 4 (fun z θ => Dth F z θ * G z θ)
            + Work.Spaces.HkSq α 4 (fun z θ => F z θ * Dth G z θ)) := by
      have h1 := Work.FTS.GalFields.RHS.HkSq_add_le_open α 4 hα
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hF.smDth hG.qo.1)
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hF.sm hsmDthG) hDthFG.1 hFDthG.1
      rwa [Work.FTS.EllipticEst.HkSq_congr_open α 4
        (fun z θ hz hθ hθ' => (Dth_mul_eqOn_Q0 hF.sm hG.qo.1 z θ hz hθ hθ').symm)] at h1
    linarith [hshift, hsqFG, hsqDz, hsqFDz, hsqDth, hsqFDth, hDzsq, hDthsq, hPnn]
  -- ### the membership and the norm
  have hmem5 : Work.Spaces.HkMem α 5 (fun z θ => F z θ * G z θ) :=
    HkMem_succ_of hα hsm (k := 4) (by norm_num) hFG.1 hDzm hDthm
  refine ⟨Work.FTS.LocData.HkMem_const_mul α 5 c hmem5, ?_⟩
  have hsqc : Work.Spaces.HkSq α 5 (fun z θ => c * (F z θ * G z θ))
      = c ^ 2 * Work.Spaces.HkSq α 5 (fun z θ => F z θ * G z θ) :=
    Work.FTS.StrongEps.HkSq_const_mul α 5 c (fun z θ => F z θ * G z θ)
  have hroot : Work.Spaces.HkNorm α 5 (fun z θ => c * (F z θ * G z θ))
      = Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => c * (F z θ * G z θ))) := rfl
  have hsqc' : Work.Spaces.HkSq α 5 (fun z θ => c * (F z θ * G z θ))
      ≤ (|c| * (3 * P)) ^ 2 := by
    rw [hsqc]
    calc c ^ 2 * Work.Spaces.HkSq α 5 (fun z θ => F z θ * G z θ)
        ≤ c ^ 2 * (9 * P ^ 2) := mul_le_mul_of_nonneg_left hsq5 (sq_nonneg c)
      _ = (|c| * (3 * P)) ^ 2 := by
          rw [← sq_abs c]
          ring
  calc Work.Spaces.HkNorm α 5 (fun z θ => c * (F z θ * G z θ))
      = Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => c * (F z θ * G z θ))) := hroot
    _ ≤ Real.sqrt ((|c| * (3 * P)) ^ 2) := Real.sqrt_le_sqrt hsqc'
    _ = |c| * (3 * P) := Real.sqrt_sq (by positivity)
    _ = |c| * (3 * (Cw * α ^ (-(1 / 2 : ℝ)) * a * b)) := by rw [hPdef]

end Work.FTS.StrongEps.H5
