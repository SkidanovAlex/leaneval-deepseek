import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBogFS.zpScalarOf_sharpL_le_errSlot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.EzeroRow` — the `hEzeroL` row of the capstone, packaged

The capstone `Work.BoseBogFS.bogOpBoundAtFS_of_sharpMatchL` (`SharpL.lean`) takes the
zero-point error row

```
hEzeroL : zpErrorOf (ell v μ) (a v) (M μ ρ ‹_›).D.R … (M μ ρ ‹_›).D.μ ρ (M μ ρ ‹_›).n
            (zpRiemErrSharpL (M μ ρ ‹_›).n (M μ ρ ‹_›).D.K (η μ ρ) (lhyEps …))
          ≤ C₄ · errBracket v R μ ,
```

a compound expression involving `zpErrorOf`, `zpRiemErrSharpL` and `lhyEps`.  Two proved lemmas
already reduce it: `Work.BoseBogFS.zpScalarOf_sharpL_le_errSlot` (the scalar part) and
`Work.BoseBogFS.zpErrorOf_le_scalar` (the physical prefactors).  This module *performs* the
composition, so that a consumer only has to supply the **arithmetic rows**

* `hC4  : 10⁴⁵(1 + K.B) ≤ C₄/4`,
* `hEpsL : latticeMeshErr (8π) n ≤ 2·10¹¹·lhyEps …`   (= the capstone's own `hEpsLatt`),
* `hlhy  : lhyEps … ≤ 10⁸·errSlot v R μ`               (`Work.BoseBogFS.lhyEps_le_errSlot`),
* `hδl   : meshD n·log(1/meshD n) ≤ 10²⁰·errSlot`,
* `hprod : η·(1 + lhyEps + fsI2 K) ≤ 10²⁰·errSlot`,

together with `0 < a v`, `ε₀ ≤ 1` and `C₄ ≥ 0`.  The remaining inputs of
`zpErrorOf_le_scalar` — `0 ≤ ρ`, `0 < μ`, `0 ≤ ell v μ` and the ratio row
`ρ²√(ρa³) ≤ 4μ²√(μa³)` — are *derived here* from `Adm`, `CloseCondFS` and `ell_pos_bog`
(`rho_pow_sqrt_le_of_close` below), so they are not part of the interface.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR Work.BoseB7 Work.BoseB6Est

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. The ratio row of `zpErrorOf_le_scalar`, from `Adm` + `CloseCondFS` -/

/-- `K_ℓ = (μa³)^{-3/646} ≥ 1` for `0 < μa³ ≤ 1`. -/
theorem Kl_ge_one (v : ℝ³ → ℝ) {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v)
    (ht : μ * a v ^ 3 ≤ 1) : 1 ≤ (paramsAt μ (a v)).Kl := by
  have ht0 : 0 < μ * a v ^ 3 := mul_pos hμ (pow_pos hav 3)
  have h := Work.BoseBox.fsXp_le_fsXp (t := μ * a v ^ 3) (a := (0 : ℝ)) (b := -(3 / 2))
    ht0 ht (by norm_num)
  have h1 : Work.BoseBox.fsXp (μ * a v ^ 3) (0 : ℝ) = 1 := by
    rw [Work.BoseBox.fsXp, zero_div, Real.rpow_zero]
  have h2 : (paramsAt μ (a v)).Kl = Work.BoseBox.fsXp (μ * a v ^ 3) (-(3 / 2)) := by
    rw [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
  linarith [h, h1, h2]



/-! ## 1b. The ratio row of `zpErrorOf_le_scalar` -/

/-- **The two scalar rows of the close region**: `ρ ≥ 0` and
`ρ²√(ρa³) ≤ 4μ²√(μa³)`.  `CloseCondFS` gives `ρ ≤ μ(1 + K_ℓ⁻²/(2¹⁴π))`, and `K_ℓ ≥ 1` bounds
the bracket by `1 + 1/(2¹⁴π)`; then `ρ²√(ρa³) ≤ ((1+c)²√(1+c))·μ²√(μa³)` with
`c = 1/(2¹⁴π)`, and `(1+c)²√(1+c) ≤ (1+3c)(1+c) ≤ 4`. -/
theorem close_rho_rows (v : ℝ³ → ℝ) {μ ρ : ℝ} (hμ : 0 < μ) (hav : 0 < a v)
    (hKl : 1 ≤ (paramsAt μ (a v)).Kl) (hclose : CloseCondFS v μ ρ) :
    0 ≤ ρ ∧ ρ ^ 2 * Real.sqrt (ρ * a v ^ 3) ≤ 4 * μ ^ 2 * Real.sqrt (μ * a v ^ 3) := by
  have hKl1 : 0 < (paramsAt μ (a v)).Kl := lt_of_lt_of_le one_pos hKl
  have hKl2 : ((paramsAt μ (a v)).Kl) ^ (-(2 : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg hKl1.le, Real.rpow_two]
    exact inv_le_one_of_one_le₀ (by nlinarith)
  have habs := abs_le.mp hclose
  rw [closeThresholdFS] at habs
  have hc0 : 0 ≤ ((paramsAt μ (a v)).Kl) ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * π) := by positivity
  have hc1 : ((paramsAt μ (a v)).Kl) ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * π)
      ≤ 1 / ((2 : ℝ) ^ 14 * π) := div_le_div_of_nonneg_right hKl2 (by positivity)
  have hc4 : 1 / ((2 : ℝ) ^ 14 * π) ≤ 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num)
      (by nlinarith [Real.pi_gt_three] : (4 : ℝ) ≤ (2 : ℝ) ^ 14 * π)
  have hcsm : 1 / ((2 : ℝ) ^ 14 * π) ≤ 1 := by linarith
  set c : ℝ := 1 / ((2 : ℝ) ^ 14 * π) with hcdef
  have hc0' : 0 ≤ c := hcdef ▸ div_nonneg zero_le_one (by positivity)
  have hT : μ * (((paramsAt μ (a v)).Kl) ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * π)) ≤ μ * c :=
    mul_le_mul_of_nonneg_left (hcdef ▸ hc1) (le_of_lt hμ)
  have hTeq : μ * ((paramsAt μ (a v)).Kl) ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * π)
      = μ * (((paramsAt μ (a v)).Kl) ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * π)) := by ring
  have h3 : μ * c ≤ μ * 1 := mul_le_mul_of_nonneg_left (hcdef ▸ hcsm) (le_of_lt hμ)
  have hρ0 : 0 ≤ ρ := by
    have h2 := habs.1
    linarith [h2, hT, hTeq, h3, hμ]
  have hρle : ρ ≤ μ * (1 + c) := by
    have h2 := habs.2
    linarith [h2, hT, hTeq, h3, hμ]
  refine ⟨hρ0, ?_⟩
  have hρ2 : ρ ^ 2 ≤ μ ^ 2 * (1 + c) ^ 2 := by
    have h1 : ρ ^ 2 ≤ (μ * (1 + c)) ^ 2 := pow_le_pow_left₀ hρ0 hρle 2
    calc ρ ^ 2 ≤ (μ * (1 + c)) ^ 2 := h1
      _ = μ ^ 2 * (1 + c) ^ 2 := by ring
  have hs1 : Real.sqrt (ρ * a v ^ 3) ≤ Real.sqrt (μ * (1 + c) * a v ^ 3) := by
    refine Real.sqrt_le_sqrt ?_
    have h4 : 0 ≤ a v ^ 3 := pow_nonneg (le_of_lt hav) 3
    nlinarith [mul_le_mul_of_nonneg_right hρle h4]
  have hs2 : Real.sqrt (μ * (1 + c) * a v ^ 3)
      = Real.sqrt (1 + c) * Real.sqrt (μ * a v ^ 3) := by
    rw [show μ * (1 + c) * a v ^ 3 = (1 + c) * (μ * a v ^ 3) by ring]
    exact Real.sqrt_mul (by linarith [hc0']) _
  have hfac : (1 + c) ^ 2 * Real.sqrt (1 + c) ≤ 4 := by
    have h1 : Real.sqrt (1 + c) ≤ 1 + c := by
      have h2 : (1 : ℝ) ≤ 1 + c := by linarith
      nlinarith [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 + c),
        Real.sqrt_nonneg (1 + c), sq_nonneg (1 + c)]
    have h5 : (1 + c) ^ 2 ≤ 1 + 3 * c := by nlinarith
    have hc4c : c ≤ 1 / 4 := hcdef ▸ hc4
    have h6 : (1 + 3 * c) * (1 + c) ≤ 4 := by nlinarith [hc4c, hc0']
    exact le_trans (mul_le_mul h5 h1 (Real.sqrt_nonneg _) (by positivity)) h6
  calc ρ ^ 2 * Real.sqrt (ρ * a v ^ 3)
      ≤ μ ^ 2 * (1 + c) ^ 2 * Real.sqrt (μ * (1 + c) * a v ^ 3) :=
        mul_le_mul hρ2 hs1 (Real.sqrt_nonneg _) (by positivity)
    _ = μ ^ 2 * ((1 + c) ^ 2 * Real.sqrt (1 + c)) * Real.sqrt (μ * a v ^ 3) := by
        rw [hs2]; ring
    _ ≤ μ ^ 2 * 4 * Real.sqrt (μ * a v ^ 3) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac (by positivity))
          (Real.sqrt_nonneg _)
    _ = 4 * μ ^ 2 * Real.sqrt (μ * a v ^ 3) := by ring


/-! ## 2. The packaged `hEzeroL` row -/

/-- **The `hEzeroL` row of the capstone, reduced to arithmetic rows.**  See the module header
for the list (`hR`, `hC4`, `hEpsL`, `hlhy`, `hδl`, `hprod`); the ratio row and `0 ≤ ρ` come
from `close_rho_rows`. -/
theorem hEzeroL_sharpL (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ)
    (D : ℝ → KzDatum) (ε₀ : ℝ) (hε₀1 : ε₀ ≤ 1)
    (M : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ → FsMatch (D μ).F (D μ).E ρ ((D μ).gHat0))
    (η : ℝ → ℝ → ℝ) (C₄ : ℝ) (hav : 0 < a v) (hC₄ : 0 ≤ C₄)
    (hR : ∀ (μ ρ : ℝ) (hc : CloseCondFS v μ ρ), (M μ ρ hc).D.R = R)
    (hC4 : ∀ (μ ρ : ℝ) (hc : CloseCondFS v μ ρ),
      10 ^ 45 * (1 + (M μ ρ hc).D.K.B) ≤ C₄ / 4)
    (hEpsL : ∀ (μ ρ : ℝ) (hc : CloseCondFS v μ ρ),
      Work.BoseB6.latticeMeshErr (8 * Real.pi) (M μ ρ hc).n
        ≤ 2 * 10 ^ 11 * Work.BoseB6.lhyEps (M μ ρ hc).D.a R (M μ ρ hc).D.εT
            (M μ ρ hc).D.Kl (M μ ρ hc).D.s (M μ ρ hc).D.d (M μ ρ hc).D.μ)
    (hlhy : ∀ (μ ρ : ℝ) (hc : CloseCondFS v μ ρ),
      Work.BoseB6.lhyEps (M μ ρ hc).D.a R (M μ ρ hc).D.εT (M μ ρ hc).D.Kl
        (M μ ρ hc).D.s (M μ ρ hc).D.d (M μ ρ hc).D.μ ≤ 10 ^ 8 * errSlot v R μ)
    (hδl : ∀ (μ ρ : ℝ) (hc : CloseCondFS v μ ρ),
      Work.BoseB6.meshD (M μ ρ hc).n * Real.log (1 / Work.BoseB6.meshD (M μ ρ hc).n)
        ≤ 10 ^ 20 * errSlot v R μ)
    (hprod : ∀ (μ ρ : ℝ) (hc : CloseCondFS v μ ρ),
      η μ ρ * (1 + Work.BoseB6.lhyEps (M μ ρ hc).D.a R (M μ ρ hc).D.εT
          (M μ ρ hc).D.Kl (M μ ρ hc).D.s (M μ ρ hc).D.d (M μ ρ hc).D.μ
        + Work.BoseB6Est.fsI2 (M μ ρ hc).D.K) ≤ 10 ^ 20 * errSlot v R μ) :
    ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ (ρ : ℝ) (hc : CloseCondFS v μ ρ),
      zpErrorOf (ell v μ) (a v) (M μ ρ hc).D.R (M μ ρ hc).D.εT (M μ ρ hc).D.Kl
        (M μ ρ hc).D.s (M μ ρ hc).D.d (M μ ρ hc).D.μ ρ (M μ ρ hc).n
        (zpRiemErrSharpL (M μ ρ hc).n (M μ ρ hc).D.K (η μ ρ)
          (Work.BoseB6.lhyEps (M μ ρ hc).D.a (M μ ρ hc).D.R (M μ ρ hc).D.εT
            (M μ ρ hc).D.Kl (M μ ρ hc).D.s (M μ ρ hc).D.d (M μ ρ hc).D.μ))
      ≤ C₄ * errBracket v R μ := by
  intro μ hadm hview ρ hc
  have hμ : 0 < μ := hadm.1
  have ht : μ * a v ^ 3 ≤ 1 := le_trans hadm.2.1 hε₀1
  have hKl : 1 ≤ (paramsAt μ (a v)).Kl := Kl_ge_one v hμ hav ht
  obtain ⟨hρ0, hρμ⟩ := close_rho_rows v hμ hav hKl hc
  have hDμ : (M μ ρ hc).D.μ = μ := (M μ ρ hc).hμ.trans (canView_mu hview)
  have hDa : (M μ ρ hc).D.a = a v := (M μ ρ hc).ha.trans (canView_aScat hview)
  have hμ' : 0 < (M μ ρ hc).D.μ := by rw [hDμ]; exact hμ
  -- the scalar bound at the datum's `μ`
  have hscal : zpScalarOf (a v) R (M μ ρ hc).D.εT (M μ ρ hc).D.Kl (M μ ρ hc).D.s
        (M μ ρ hc).D.d (M μ ρ hc).D.μ (M μ ρ hc).n
        (zpRiemErrSharpL (M μ ρ hc).n (M μ ρ hc).D.K (η μ ρ)
          (Work.BoseB6.lhyEps (a v) R (M μ ρ hc).D.εT (M μ ρ hc).D.Kl
            (M μ ρ hc).D.s (M μ ρ hc).D.d (M μ ρ hc).D.μ))
      ≤ (C₄ / 4) * errSlot v R (M μ ρ hc).D.μ :=
    zpScalarOf_sharpL_le_errSlot v h R (M μ ρ hc).D.μ (M μ ρ hc).n (M μ ρ hc).D.K
      (εT := (M μ ρ hc).D.εT) (Kl := (M μ ρ hc).D.Kl) (s := (M μ ρ hc).D.s)
      (d := (M μ ρ hc).D.d) (η := η μ ρ) (C₄ / 4) hav hμ'
      (by simpa only [hDa] using hEpsL μ ρ hc)
      (by simpa only [hDa, hDμ] using hlhy μ ρ hc)
      (by simpa only [hDμ] using hδl μ ρ hc)
      (by simpa only [hDa, hDμ] using hprod μ ρ hc) (by linarith) (hC4 μ ρ hc)
  have hmain := zpErrorOf_le_scalar v R (M μ ρ hc).D.μ ρ (M μ ρ hc).D.εT (M μ ρ hc).D.Kl
    (M μ ρ hc).D.s (M μ ρ hc).D.d (M μ ρ hc).n
    (zpRiemErrSharpL (M μ ρ hc).n (M μ ρ hc).D.K (η μ ρ)
      (Work.BoseB6.lhyEps (a v) R (M μ ρ hc).D.εT (M μ ρ hc).D.Kl (M μ ρ hc).D.s
        (M μ ρ hc).D.d (M μ ρ hc).D.μ))
    (C₄ / 4) hav hμ' (by linarith) (by rw [hDμ]; exact (ell_pos_bog v hμ hav).le)
    hρ0 (by rw [hDμ]; exact hρμ) hscal
  rw [hDμ] at hmain
  have h4 : 4 * (C₄ / 4) = C₄ := by ring
  rw [h4] at hmain
  rw [hR μ ρ hc, hDa, hDμ]
  exact hmain

end Work.BoseBogFS
