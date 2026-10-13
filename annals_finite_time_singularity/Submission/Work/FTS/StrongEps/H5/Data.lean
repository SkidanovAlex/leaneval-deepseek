/-
# `H5/Data` — the level-`5` data of a factor, and the level-`5` product wrappers

The `ℋ⁵`-estimates of the scheme's right-hand side are obtained from the *level-four* product
rules (`OpenPkg.prod_field`, `OpenPkg.wprod_field_winf`) plus the level shift
(`H5.HkSq_succ_le`): for a product `C·G`,

`HkSq α 5 (C·G) ≤ HkSq α 4 (C·G) + HkSq α 4 (D_z(C·G)) + HkSq α 4 (D_θ(C·G))`,

and the Leibniz rule moves the outer derivative onto one factor, so every term is again a
*level-four* product of one of the six functions `C, D_zC, D_θC, G, D_zG, D_θG`.

Accordingly the data a factor must carry for its level-`5` treatment is: its `ℋ⁴`-honesty and
`ℋ⁴`-size at level four and the same for `D_z f` and `D_θ f` (`L5`), or the `𝒲^{4,∞}`-version of
the same (`W5`, for the `𝒲`-priced factors such as the star coefficients).  With a *single*
constant per factor the wrappers below give

`HkNorm α 5 (c·(C·G)) ≤ 3·|c|·(C α^{-1/2}) a b`,
`HkNorm α 5 (c·(F·G)) ≤ 3·|c|·(C α^{-1/2}) a b` (the `𝒲^{4,∞}`-priced version).

The factor `3 = √9` is the sum of the nine level-four product estimates (`C·G`, and two each
from the two Leibniz terms of `D_z` and of `D_θ`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.H5.LevelShift
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.OpenPkg.wprod_field_winf
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.EllipticEst.RPFresh.straight_transfers
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.StrongEps.HkSq_const_mul

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

/-! ## Leibniz for the first-order operators on the open quadrant -/

/-- `D_z(f·g) = D_z f·g + f·D_z g` on the open quadrant. -/
theorem Dz_mul_eqOn_Q0 {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Dz (fun z θ => f z θ * g z θ) z θ = Dz f z θ * g z θ + f z θ * Dz g z θ := by
  intro z θ hz hθ hθ'
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ'⟩
  have hdf : DifferentiableAt ℝ (fun z' => f z' θ) z :=
    Work.Spaces.differentiableAt_slice_fst
      ((hf.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)).differentiableAt
        (by norm_num))
  have hdg : DifferentiableAt ℝ (fun z' => g z' θ) z :=
    Work.Spaces.differentiableAt_slice_fst
      ((hg.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)).differentiableAt
        (by norm_num))
  show z * deriv (fun z' => f z' θ * g z' θ) z
      = z * deriv (fun z' => f z' θ) z * g z θ + f z θ * (z * deriv (fun z' => g z' θ) z)
  rw [show (fun z' => f z' θ * g z' θ)
        = (fun z' => f z' θ) * (fun z' => g z' θ) from rfl, deriv_mul hdf hdg]
  ring

/-- `D_θ(f·g) = D_θ f·g + f·D_θ g` on the open quadrant. -/
theorem Dth_mul_eqOn_Q0 {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Dth (fun z θ => f z θ * g z θ) z θ = Dth f z θ * g z θ + f z θ * Dth g z θ := by
  intro z θ hz hθ hθ'
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ'⟩
  have hdf : DifferentiableAt ℝ (fun θ' => f z θ') θ :=
    Work.Spaces.differentiableAt_slice_snd
      ((hf.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)).differentiableAt
        (by norm_num))
  have hdg : DifferentiableAt ℝ (fun θ' => g z θ') θ :=
    Work.Spaces.differentiableAt_slice_snd
      ((hg.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)).differentiableAt
        (by norm_num))
  show Real.sin (2 * θ) * deriv (fun θ' => f z θ' * g z θ') θ
      = Real.sin (2 * θ) * deriv (fun θ' => f z θ') θ * g z θ
        + f z θ * (Real.sin (2 * θ) * deriv (fun θ' => g z θ') θ)
  rw [show (fun θ' => f z θ' * g z θ') = (fun θ' => f z θ') * (fun θ' => g z θ') from rfl,
    deriv_mul hdf hdg]
  ring

/-! ## The level-`5` data bundles -/

/-- **The level-`5` data of a factor**, at level four: `HQo α 4 f` and an `Xn`-bound, and the
same for `D_z f` and `D_θ f`.  This is exactly what the level shift (`HkSq_succ_le`) consumes
for a product of two such factors. -/
structure L5 (α : ℝ) (f : Fn) (C : ℝ) : Prop where
  qo : Work.FTS.VocabO.HQo α 4 f
  bd : Work.FTS.Nonlin.Xn α f ≤ C
  qoDz : Work.FTS.VocabO.HQo α 4 (Dz f)
  bdDz : Work.FTS.Nonlin.Xn α (Dz f) ≤ C
  qoDth : Work.FTS.VocabO.HQo α 4 (Dth f)
  bdDth : Work.FTS.Nonlin.Xn α (Dth f) ≤ C

/-- **The `𝒲^{4,∞}`-priced level-`5` data of a factor**: smoothness and a `𝒲^{4,∞}`-bound, and
the same for `D_z f` and `D_θ f`. -/
structure W5 (α : ℝ) (f : Fn) (C : ℝ) : Prop where
  sm : Work.FTS.EllipticEst.SmoothOpen f
  wm : Work.Spaces.WlInfMem α 4 f
  wb : Work.Spaces.WlInf α 4 f ≤ C
  smDz : Work.FTS.EllipticEst.SmoothOpen (Dz f)
  wmDz : Work.Spaces.WlInfMem α 4 (Dz f)
  wbDz : Work.Spaces.WlInf α 4 (Dz f) ≤ C
  smDth : Work.FTS.EllipticEst.SmoothOpen (Dth f)
  wmDth : Work.Spaces.WlInfMem α 4 (Dth f)
  wbDth : Work.Spaces.WlInf α 4 (Dth f) ≤ C

/-! ## The level-`5` product wrappers -/

/-- The rearrangement behind every level-four majorant: if `x ≤ a`, `y ≤ b` and the coefficients
are nonnegative, then `C α^{-1/2} x y ≤ C α^{-1/2} a b`. -/
theorem Pd_le {C α a b x y : ℝ} (hC : 0 ≤ C * α ^ (-(1 / 2 : ℝ))) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hx : x ≤ a) (hy : y ≤ b) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) :
    C * α ^ (-(1 / 2 : ℝ)) * x * y ≤ C * α ^ (-(1 / 2 : ℝ)) * a * b := by
  have h1 : C * α ^ (-(1 / 2 : ℝ)) * x ≤ C * α ^ (-(1 / 2 : ℝ)) * a :=
    mul_le_mul_of_nonneg_left hx hC
  have h2 : C * α ^ (-(1 / 2 : ℝ)) * x * y ≤ C * α ^ (-(1 / 2 : ℝ)) * a * y :=
    mul_le_mul_of_nonneg_right h1 hy0
  have h3 : C * α ^ (-(1 / 2 : ℝ)) * a * y ≤ C * α ^ (-(1 / 2 : ℝ)) * a * b :=
    mul_le_mul_of_nonneg_left hy (mul_nonneg hC ha)
  exact le_trans h2 h3

/-- `HkSq α 4 f = (Xn α f)²`. -/
theorem sq_eq_Xn_sq (α : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 4 f = (Work.FTS.Nonlin.Xn α f) ^ 2 := by
  have : Work.FTS.Nonlin.Xn α f = Real.sqrt (Work.Spaces.HkSq α 4 f) := rfl
  rw [this, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)]

/-- **The level-`5` product of two `ℋ⁴`-honest factors**, from the level-four product rule and
the level shift. -/
theorem L5_mul {α Cprod : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCprod : 0 < Cprod)
    (hfield : ∀ f g : Fn, Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g)
    {C G : Fn} {c a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hC : L5 α C a) (hG : L5 α G b) :
    Work.Spaces.HkMem α 5 (fun z θ => c * (C z θ * G z θ)) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => c * (C z θ * G z θ))
        ≤ |c| * (3 * (Cprod * α ^ (-(1 / 2 : ℝ)) * a * b)) := by
  have hAr : 0 ≤ Cprod * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCprod.le (Real.rpow_nonneg hα.le _)
  set P : ℝ := Cprod * α ^ (-(1 / 2 : ℝ)) * a * b with hPdef
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    exact mul_nonneg (mul_nonneg hAr ha) hb
  -- ### the six level-four product estimates
  have hCG := hfield C G hC.qo hG.qo
  have hDzCG := hfield (Dz C) G hC.qoDz hG.qo
  have hCDzG := hfield C (Dz G) hC.qo hG.qoDz
  have hDthCG := hfield (Dth C) G hC.qoDth hG.qo
  have hCDthG := hfield C (Dth G) hC.qo hG.qoDth
  have hsqCG : Work.Spaces.HkSq α 4 (fun z θ => C z θ * G z θ) ≤ P ^ 2 := by
    have hXn : Work.FTS.Nonlin.Xn α (fun z θ => C z θ * G z θ)
        ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * a * b :=
      le_trans hCG.2 (Pd_le hAr ha hb hC.bd hG.bd
        (Work.Spaces.HkNorm_nonneg α 4 C) (Work.Spaces.HkNorm_nonneg α 4 G))
    rw [sq_eq_Xn_sq α, hPdef]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn 2
  have hsqDz : Work.Spaces.HkSq α 4 (fun z θ => Dz C z θ * G z θ) ≤ P ^ 2 := by
    have hXn : Work.FTS.Nonlin.Xn α (fun z θ => Dz C z θ * G z θ)
        ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * a * b :=
      le_trans hDzCG.2 (Pd_le hAr ha hb hC.bdDz hG.bd
        (Work.Spaces.HkNorm_nonneg α 4 (Dz C)) (Work.Spaces.HkNorm_nonneg α 4 G))
    rw [sq_eq_Xn_sq α, hPdef]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn 2
  have hsqCDz : Work.Spaces.HkSq α 4 (fun z θ => C z θ * Dz G z θ) ≤ P ^ 2 := by
    have hXn : Work.FTS.Nonlin.Xn α (fun z θ => C z θ * Dz G z θ)
        ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * a * b :=
      le_trans hCDzG.2 (Pd_le hAr ha hb hC.bd hG.bdDz
        (Work.Spaces.HkNorm_nonneg α 4 C) (Work.Spaces.HkNorm_nonneg α 4 (Dz G)))
    rw [sq_eq_Xn_sq α, hPdef]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn 2
  have hsqDth : Work.Spaces.HkSq α 4 (fun z θ => Dth C z θ * G z θ) ≤ P ^ 2 := by
    have hXn : Work.FTS.Nonlin.Xn α (fun z θ => Dth C z θ * G z θ)
        ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * a * b :=
      le_trans hDthCG.2 (Pd_le hAr ha hb hC.bdDth hG.bd
        (Work.Spaces.HkNorm_nonneg α 4 (Dth C)) (Work.Spaces.HkNorm_nonneg α 4 G))
    rw [sq_eq_Xn_sq α, hPdef]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn 2
  have hsqCDth : Work.Spaces.HkSq α 4 (fun z θ => C z θ * Dth G z θ) ≤ P ^ 2 := by
    have hXn : Work.FTS.Nonlin.Xn α (fun z θ => C z θ * Dth G z θ)
        ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * a * b :=
      le_trans hCDthG.2 (Pd_le hAr ha hb hC.bd hG.bdDth
        (Work.Spaces.HkNorm_nonneg α 4 C) (Work.Spaces.HkNorm_nonneg α 4 (Dth G)))
    rw [sq_eq_Xn_sq α, hPdef]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn 2
  -- ### the level shift
  have hsmC : Work.FTS.EllipticEst.SmoothOpen C := hC.qo.1
  have hsmG : Work.FTS.EllipticEst.SmoothOpen G := hG.qo.1
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => C z θ * G z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hsmC hsmG
  have hsmDz : Work.FTS.EllipticEst.SmoothOpen (Dz (fun z θ => C z θ * G z θ)) := hsm.Dz
  have hsmDth : Work.FTS.EllipticEst.SmoothOpen (Dth (fun z θ => C z θ * G z θ)) := hsm.Dth
  have hsmDzC : Work.FTS.EllipticEst.SmoothOpen (Dz C) := hC.qoDz.1
  have hsmDzG : Work.FTS.EllipticEst.SmoothOpen (Dz G) := hG.qoDz.1
  have hsmDthC : Work.FTS.EllipticEst.SmoothOpen (Dth C) := hC.qoDth.1
  have hsmDthG : Work.FTS.EllipticEst.SmoothOpen (Dth G) := hG.qoDth.1
  have hDzm : Work.Spaces.HkMem α 4 (Dz (fun z θ => C z θ * G z θ)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
      (Work.FTS.EllipticEst.RPFresh.HkMem_add_open α 4
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hsmDzC hsmG)
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hsmC hsmDzG)
        hDzCG.1 hCDzG.1)
      (fun z hz θ hθ => (Dz_mul_eqOn_Q0 hsmC hsmG z θ hz hθ.1 hθ.2).symm)
  have hDthm : Work.Spaces.HkMem α 4 (Dth (fun z θ => C z θ * G z θ)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
      (Work.FTS.EllipticEst.RPFresh.HkMem_add_open α 4
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hsmDthC hsmG)
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hsmC hsmDthG)
        hDthCG.1 hCDthG.1)
      (fun z hz θ hθ => (Dth_mul_eqOn_Q0 hsmC hsmG z θ hz hθ.1 hθ.2).symm)
  have hsq5 : Work.Spaces.HkSq α 5 (fun z θ => C z θ * G z θ) ≤ 9 * P ^ 2 := by
    have hshift := HkSq_succ_le (α := α) (k := 4) hα hsm (by norm_num) hCG.1 hDzm hDthm
    have hDzsq : Work.Spaces.HkSq α 4 (Dz (fun z θ => C z θ * G z θ))
        ≤ 2 * (Work.Spaces.HkSq α 4 (fun z θ => Dz C z θ * G z θ)
            + Work.Spaces.HkSq α 4 (fun z θ => C z θ * Dz G z θ)) := by
      have h1 := Work.FTS.GalFields.RHS.HkSq_add_le_open α 4 hα
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hsmDzC hsmG)
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hsmC hsmDzG) hDzCG.1 hCDzG.1
      rwa [Work.FTS.EllipticEst.HkSq_congr_open α 4
        (fun z θ hz hθ hθ' => (Dz_mul_eqOn_Q0 hsmC hsmG z θ hz hθ hθ').symm)] at h1
    have hDthsq : Work.Spaces.HkSq α 4 (Dth (fun z θ => C z θ * G z θ))
        ≤ 2 * (Work.Spaces.HkSq α 4 (fun z θ => Dth C z θ * G z θ)
            + Work.Spaces.HkSq α 4 (fun z θ => C z θ * Dth G z θ)) := by
      have h1 := Work.FTS.GalFields.RHS.HkSq_add_le_open α 4 hα
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hsmDthC hsmG)
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hsmC hsmDthG) hDthCG.1 hCDthG.1
      rwa [Work.FTS.EllipticEst.HkSq_congr_open α 4
        (fun z θ hz hθ hθ' => (Dth_mul_eqOn_Q0 hsmC hsmG z θ hz hθ hθ').symm)] at h1
    linarith [hshift, hsqCG, hsqDz, hsqCDz, hsqDth, hsqCDth, hDzsq, hDthsq, hPnn]
  -- ### the membership and the norm
  have hmemCG : Work.Spaces.HkMem α 4 (fun z θ => C z θ * G z θ) := hCG.1
  have hmem5 : Work.Spaces.HkMem α 5 (fun z θ => C z θ * G z θ) :=
    HkMem_succ_of hα hsm (k := 4) (by norm_num) hmemCG hDzm hDthm
  refine ⟨Work.FTS.LocData.HkMem_const_mul α 5 c hmem5, ?_⟩
  have hsqc : Work.Spaces.HkSq α 5 (fun z θ => c * (C z θ * G z θ))
      = c ^ 2 * Work.Spaces.HkSq α 5 (fun z θ => C z θ * G z θ) :=
    Work.FTS.StrongEps.HkSq_const_mul α 5 c (fun z θ => C z θ * G z θ)
  have hroot : Work.Spaces.HkNorm α 5 (fun z θ => c * (C z θ * G z θ))
      = Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => c * (C z θ * G z θ))) := rfl
  have hsqc' : Work.Spaces.HkSq α 5 (fun z θ => c * (C z θ * G z θ))
      ≤ (|c| * (3 * P)) ^ 2 := by
    rw [hsqc]
    calc c ^ 2 * Work.Spaces.HkSq α 5 (fun z θ => C z θ * G z θ)
        ≤ c ^ 2 * (9 * P ^ 2) := mul_le_mul_of_nonneg_left hsq5 (sq_nonneg c)
      _ = (|c| * (3 * P)) ^ 2 := by
          rw [← sq_abs c]
          ring
  calc Work.Spaces.HkNorm α 5 (fun z θ => c * (C z θ * G z θ))
      = Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => c * (C z θ * G z θ))) := hroot
    _ ≤ Real.sqrt ((|c| * (3 * P)) ^ 2) := Real.sqrt_le_sqrt hsqc'
    _ = |c| * (3 * P) := Real.sqrt_sq (by positivity)
    _ = |c| * (3 * (Cprod * α ^ (-(1 / 2 : ℝ)) * a * b)) := by rw [hPdef]

end Work.FTS.StrongEps.H5
