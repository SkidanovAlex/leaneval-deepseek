import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.OpOrder

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `cutOp_isOrd`: the Friedrichs cutoff is an operator of order `0`

The cutoff `S_ε = cutOp ρ ε` of the `VarCoef` order calculus acts on Fourier coefficients by
`û ↦ (fun k => ρ (ε • k) · û k)`, so that `‖ρ‖ ≤ 1` makes it a *contraction* on every weighted
`ℓ²` mass `CSqZ t` (`Work.Diff.STE.B3.SymCalcStep8.flatCut_CSqZ_le`, here in the sharp form with
constant exactly `1`).  Consequently `S_ε` is an operator of order `0` with the constant function
`1`: `IsOrd 0 (fun _ => 1) (cutOp ρ ε)`.

The two other fields of `IsOrd` are smoothness/periodicity preservation
(`SymCalcStep1.flatCut_contDiff`, `SymCalcStep1.flatCut_periodic`) and `ℂ`-linearity on smooth
`1`-periodic functions, which is proved here from the additivity of `fourierCoeff`, the pointwise
additivity/homogeneity of `trunc`, and the linearity of `seriesFun` on `ℓ¹` coefficient families.

Note that **no smoothness hypothesis on `ρ` is used** (unlike `mulOp_isOrd`, where the multiplier is
required to be smooth): the cutoff only has to satisfy `‖ρ y‖ ≤ 1`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Diff.STE.B3.VarCoef

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. Linearity of `seriesFun` -/

/-- `seriesFun` is additive on `ℓ¹` coefficient families (termwise additivity of the `tsum`). -/
theorem seriesFun_add {a b : (ι → ℤ) → ℂ} (ha : Summable fun k => ‖a k‖)
    (hb : Summable fun k => ‖b k‖) :
    Work.Diff.STE.seriesFun (fun k => a k + b k)
      = Work.Diff.STE.seriesFun a + Work.Diff.STE.seriesFun b := by
  funext x
  simp only [Work.Diff.STE.seriesFun, Pi.add_apply]
  rw [show (fun k : ι → ℤ => (a k + b k) * Work.Diff.STE.fourierExp k x)
      = fun k : ι → ℤ => a k * Work.Diff.STE.fourierExp k x
          + b k * Work.Diff.STE.fourierExp k x from funext fun k => by ring]
  exact Summable.tsum_add
    (Summable.of_norm_bounded ha fun k => by
      rw [norm_mul, Work.Diff.STE.norm_fourierExp, mul_one])
    (Summable.of_norm_bounded hb fun k => by
      rw [norm_mul, Work.Diff.STE.norm_fourierExp, mul_one])

/-- `seriesFun` is `ℂ`-homogeneous, unconditionally (`tsum_mul_left`). -/
theorem seriesFun_const_mul (c : ℂ) (b : (ι → ℤ) → ℂ) :
    Work.Diff.STE.seriesFun (fun k => c * b k) = c • Work.Diff.STE.seriesFun b := by
  funext x
  simp only [Work.Diff.STE.seriesFun, Pi.smul_apply, smul_eq_mul]
  rw [show (fun k : ι → ℤ => (c * b k) * Work.Diff.STE.fourierExp k x)
      = fun k : ι → ℤ => c * (b k * Work.Diff.STE.fourierExp k x) from
    funext fun k => by ring]
  rw [tsum_mul_left]

/-! ## 2. Linearity of `trunc` (pointwise, no hypotheses) -/

/-- `trunc` is addititive on coefficient families. -/
theorem trunc_add (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (a b : (ι → ℤ) → ℂ) :
    Work.Diff.STE.trunc ρ ε (fun k => a k + b k)
      = fun k => Work.Diff.STE.trunc ρ ε a k + Work.Diff.STE.trunc ρ ε b k := by
  funext k
  simp only [Work.Diff.STE.trunc]
  ring

/-- `trunc` commutes with multiplication by a constant. -/
theorem trunc_const_mul (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (c : ℂ) (a : (ι → ℤ) → ℂ) :
    Work.Diff.STE.trunc ρ ε (fun k => c * a k)
      = fun k => c * Work.Diff.STE.trunc ρ ε a k := by
  funext k
  simp only [Work.Diff.STE.trunc]
  ring

/-! ## 3. The cutoff as an operator: unfolding and `ℓ¹` summability of its coefficients -/

/-- The definitional unfolding of `cutOp`. -/
@[simp] theorem cutOp_apply (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (f : (ι → ℝ) → ℂ) :
    cutOp ρ ε f = Work.Diff.STE.B3.SymCalc.flatCut ρ ε f := rfl

/-- The Fourier coefficients of `S_ε f` are `ℓ¹` for `f` smooth and `1`-periodic. -/
theorem summable_trunc_fourierCoeff (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (ε : ℝ) {f : (ι → ℝ) → ℂ} (hf : SmoothPer f) :
    Summable fun k : ι → ℤ => ‖Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff f) k‖ := by
  refine Work.Diff.STE.B3.SymCalcStep1.summable_trunc_one ρ hρ ε ?_
  have h0 := Work.Diff.STE.summable_wt_pow_norm_fourierCoeff_of_contDiff f hf.1 hf.2 0
  simpa only [pow_zero, one_mul] using h0

/-! ## 4. Additivity and homogeneity of `S_ε` on smooth periodic functions -/

/-- `S_ε` is additive on smooth `1`-periodic functions. -/
theorem flatCut_add (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ)
    {u v : (ι → ℝ) → ℂ} (hu : SmoothPer u) (hv : SmoothPer v) :
    Work.Diff.STE.B3.SymCalc.flatCut ρ ε (u + v)
      = Work.Diff.STE.B3.SymCalc.flatCut ρ ε u
        + Work.Diff.STE.B3.SymCalc.flatCut ρ ε v := by
  have hcoeff : Work.Diff.STE.fourierCoeff (u + v)
      = fun k => Work.Diff.STE.fourierCoeff u k + Work.Diff.STE.fourierCoeff v k :=
    fourierCoeff_add_of_continuous hu.1.continuous hv.1.continuous
  show Work.Diff.STE.seriesFun
        (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff (u + v)))
      = Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff u))
        + Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff v))
  rw [hcoeff, trunc_add]
  exact seriesFun_add (summable_trunc_fourierCoeff ρ hρ ε hu)
    (summable_trunc_fourierCoeff ρ hρ ε hv)

/-- `S_ε` is `ℂ`-homogeneous on smooth `1`-periodic functions. -/
theorem flatCut_smul (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (c : ℂ)
    {f : (ι → ℝ) → ℂ} (hf : SmoothPer f) :
    Work.Diff.STE.B3.SymCalc.flatCut ρ ε (c • f)
      = c • Work.Diff.STE.B3.SymCalc.flatCut ρ ε f := by
  have hcoeff : Work.Diff.STE.fourierCoeff (c • f)
      = fun k => c * Work.Diff.STE.fourierCoeff f k := by
    have hfun : (c • f : (ι → ℝ) → ℂ) = fun x => c * f x := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [hfun]
    exact fourierCoeff_const_mul_of_continuous c hf.1.continuous
  show Work.Diff.STE.seriesFun
        (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff (c • f)))
      = c • Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff f))
  rw [hcoeff, trunc_const_mul]
  exact seriesFun_const_mul c _

/-! ## 5. The contraction bound, with constant exactly `1` -/

/-- **`S_ε` never loses derivatives**: `CSqZ t` of the Fourier coefficients of `S_ε W` is at most
that of `W`, uniformly in `ε` (the proof is that of
`Work.Diff.STE.B3.SymCalcStep8.flatCut_CSqZ_le`, keeping the explicit constant `1`). -/
theorem flatCut_CSqZ_le_one (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ) (t : ℤ)
    (W : (ι → ℝ) → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W) (hper : Work.Diff.STE.Periodic1 W) :
    Work.Diff.STE.B3.SymCalcStep8.CSqZ t
        (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.flatCut ρ ε W))
      ≤ Work.Diff.STE.B3.SymCalcStep8.CSqZ t (Work.Diff.STE.fourierCoeff W) := by
  have hcoeff : Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.flatCut ρ ε W)
      = fun k : ι → ℤ => (ρ (ε • (fun i => (k i : ℝ))) : ℂ)
          * Work.Diff.STE.fourierCoeff W k :=
    funext fun k => Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_flatCut ρ hρ ε hW hper k
  rw [hcoeff]
  simp only [Work.Diff.STE.B3.SymCalcStep8.CSqZ]
  have hterm := fun m : ι → ℤ => Work.Diff.STE.B3.SymCalcStep8.flatCut_term_le ρ hρ ε t W m
  have hsumR : Summable (fun m : ι → ℤ =>
      (Work.Diff.STE.wt m) ^ t * ‖Work.Diff.STE.fourierCoeff W m‖ ^ 2) :=
    Work.Diff.STE.B3.SymCalcStep8.flatCut_summable_zpow W hW hper t
  have hsumL : Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ t
      * ‖(ρ (ε • (fun i => (m i : ℝ))) : ℂ) * Work.Diff.STE.fourierCoeff W m‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun m => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) t) (sq_nonneg _))
      hterm hsumR
  exact Summable.tsum_le_tsum hterm hsumL hsumR

/-! ## 6. The target -/

theorem cutOp_isOrd {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : (ι → ℝ) → ℝ)
    (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ) :
    Work.Diff.STE.B3.VarCoef.IsOrd 0 (fun _ => 1) (Work.Diff.STE.B3.VarCoef.cutOp ρ ε) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- preservation of smooth `1`-periodic functions
    intro f hf
    exact ⟨Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε hf.1 hf.2,
      Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε f⟩
  · -- `ℂ`-linearity on smooth `1`-periodic functions
    exact ⟨fun f g hf hg => flatCut_add ρ hρ ε hf hg,
      fun c f hf => flatCut_smul ρ ε c hf⟩
  · -- the constant is nonnegative
    intro _t
    exact zero_le_one
  · -- the order-`0` bound
    intro t f hf
    change Work.Diff.STE.B3.SymCalcStep8.CSqZ (t - 0)
        (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.flatCut ρ ε f))
      ≤ 1 * Work.Diff.STE.B3.SymCalcStep8.CSqZ t (Work.Diff.STE.fourierCoeff f)
    rw [sub_zero, one_mul]
    exact flatCut_CSqZ_le_one ρ hρ ε t f hf.1 hf.2

end Work.Diff.STE.B3.VarCoef
