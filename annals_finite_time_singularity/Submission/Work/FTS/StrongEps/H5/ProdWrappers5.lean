/-
# `H5/ProdWrappers5` — the two level-`5` product wrappers used by the `N`-block

The level-`5` `N`-block prices each of its twenty pieces by one of two product rules:

* `H5.prodHH5` — both factors are `ℋ⁵`-honest (`HQo α 5` with `HkNorm α 5`-bounds): the level
  shift (`H5.HkSq_succ_le`) together with the level-four rule `OpenPkg.prod_field`, packaged by
  `H5.L5_mul` via `H5.L5_of_HQo5`.  The constant carries the factor `3 = √9` of the level shift.
* `H5.prodWH5` — the first factor is `𝒲^{5,∞}`-priced (`SmoothOpen` + `WlInfMem α 5` +
  `WlInf α 5 ≤ a`) and the second `ℋ⁵`-honest: this is precisely
  `H5.wprod_field_winf5` (whose docstring explains that no derivative data of the `𝒲`-factor is
  needed), plus the scalar multiple.

Both are stated with an abstract `hfield` hypothesis (the corresponding level-four/level-five
rule instantiated), exactly as `H5.L5_mul` / `H5.W5_mul` are.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.H5.Data
import Submission.Work.FTS.StrongEps.H5.L5of
import Submission.Work.FTS.StrongEps.H5.wprod_field_winf5

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

/-- **The level-`5` product of two `ℋ⁵`-honest factors.** -/
theorem prodHH5 {α Cprod : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCprod : 0 < Cprod)
    (hfield : ∀ f g : Fn, Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g)
    {C G : Fn} {c a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hC : Work.FTS.VocabO.HQo α 5 C) (hCb : Work.Spaces.HkNorm α 5 C ≤ a)
    (hG : Work.FTS.VocabO.HQo α 5 G) (hGb : Work.Spaces.HkNorm α 5 G ≤ b) :
    Work.Spaces.HkMem α 5 (fun z θ => c * (C z θ * G z θ)) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => c * (C z θ * G z θ))
        ≤ |c| * (3 * (Cprod * α ^ (-(1 / 2 : ℝ)) * a * b)) :=
  L5_mul (α := α) (Cprod := Cprod) (c := c) (a := a) (b := b) hα hα1 hCprod hfield ha hb
    (L5_of_HQo5 hα hC hCb) (L5_of_HQo5 hα hG hGb)

/-- **The level-`5` product of a `𝒲^{5,∞}`-priced factor with an `ℋ⁵`-honest factor.** -/
theorem prodWH5 {α Cw : ℝ} (hα : 0 < α) (hCw : 0 < Cw)
    (hfield : ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 5 f →
      Work.FTS.VocabO.HQo α 5 g →
      Work.Spaces.HkMem α 5 (fun z θ => f z θ * g z θ) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => f z θ * g z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 5 f * Work.Spaces.HkNorm α 5 g)
    {F G : Fn} {c a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hFsm : Work.FTS.EllipticEst.SmoothOpen F) (hFw : Work.Spaces.WlInfMem α 5 F)
    (hFb : Work.Spaces.WlInf α 5 F ≤ a) (hG : Work.FTS.VocabO.HQo α 5 G)
    (hGb : Work.Spaces.HkNorm α 5 G ≤ b) :
    Work.Spaces.HkMem α 5 (fun z θ => c * (F z θ * G z θ)) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => c * (F z θ * G z θ))
        ≤ |c| * (Cw * α ^ (-(1 / 2 : ℝ)) * a * b) := by
  obtain ⟨hmem, hbd⟩ := hfield F G hFsm hFw hG
  have hAr : 0 ≤ Cw * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCw.le (Real.rpow_nonneg hα.le _)
  have hWnn : 0 ≤ Work.Spaces.WlInf α 5 F := Work.Spaces.WlInf_nonneg α 5 F hFw
  have hXnG : 0 ≤ Work.Spaces.HkNorm α 5 G := Work.Spaces.HkNorm_nonneg α 5 G
  set P : ℝ := Cw * α ^ (-(1 / 2 : ℝ)) * a * b with hPdef
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    exact mul_nonneg (mul_nonneg hAr ha) hb
  have hXn : Work.Spaces.HkNorm α 5 (fun z θ => F z θ * G z θ) ≤ P :=
    le_trans hbd (Pd_le hAr ha hb hFb hGb hWnn hXnG)
  refine ⟨Work.FTS.LocData.HkMem_const_mul α 5 c hmem, ?_⟩
  have hsq : Work.Spaces.HkSq α 5 (fun z θ => c * (F z θ * G z θ))
      = c ^ 2 * Work.Spaces.HkSq α 5 (fun z θ => F z θ * G z θ) :=
    Work.FTS.StrongEps.HkSq_const_mul α 5 c (fun z θ => F z θ * G z θ)
  have hbd2 : c ^ 2 * Work.Spaces.HkSq α 5 (fun z θ => F z θ * G z θ) ≤ (|c| * P) ^ 2 := by
    have h1 : Work.Spaces.HkSq α 5 (fun z θ => F z θ * G z θ) ≤ P ^ 2 := by
      have hsqrt : Work.Spaces.HkNorm α 5 (fun z θ => F z θ * G z θ)
          = Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => F z θ * G z θ)) := rfl
      rw [hsqrt] at hXn
      calc Work.Spaces.HkSq α 5 (fun z θ => F z θ * G z θ)
          = (Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => F z θ * G z θ))) ^ 2 :=
            (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 5 _)).symm
        _ ≤ P ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn 2
    calc c ^ 2 * Work.Spaces.HkSq α 5 (fun z θ => F z θ * G z θ)
        ≤ c ^ 2 * P ^ 2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
      _ = (|c| * P) ^ 2 := by
          rw [← sq_abs c]
          ring
  calc Work.Spaces.HkNorm α 5 (fun z θ => c * (F z θ * G z θ))
      = Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => c * (F z θ * G z θ))) := rfl
    _ = Real.sqrt (c ^ 2 * Work.Spaces.HkSq α 5 (fun z θ => F z θ * G z θ)) := by rw [hsq]
    _ ≤ Real.sqrt ((|c| * P) ^ 2) := Real.sqrt_le_sqrt hbd2
    _ = |c| * P := Real.sqrt_sq (by positivity)
    _ = |c| * (Cw * α ^ (-(1 / 2 : ℝ)) * a * b) := by rw [hPdef]

end Work.FTS.StrongEps.H5
