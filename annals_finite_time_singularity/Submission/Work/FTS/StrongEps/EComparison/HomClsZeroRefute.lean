/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS.StrongEps.EComparison.HomClsZero` is **FALSE**

This file refutes the statement of `HomClsZero`
(`Submission/Work/FTS/StrongEps/EComparison/HomClsZero.lean`) and, with it, the uniqueness node
`EllPkgCls`-uniqueness of `Submission/Work/FTS/StrongEps/EComparison/Reduction.lean`.

## The counterexample

For `0 < α` put `s := -(3/α)` and

  `mode α z θ = z ^ s / cos θ`  (the *invisible mode*),

and let `cex α` be `mode α` with the **value at `θ = 0` reset to `0`**:

  `cex α z θ = if θ = 0 then 0 else mode α z θ`.

Then `cex α` satisfies *every* hypothesis of `HomClsZero` (at `α = 1`, say) while
`cex 1 1 (π/4) = √2 ≠ 0`.

## Why it works

1. **`mode α` solves the homogeneous law.**  `(cos θ)⁻¹` is an eigenfunction of the angular
   operator `Lzero` with eigenvalue `-6`:
   `Lzero ((cos θ)⁻¹) = -6 · (cos θ)⁻¹` (`Lzero_mode` below, via the *coincidence*
   `∂_θ²(z^s/cos θ) = ∂_θ(tan θ · z^s/cos θ)`, which is what makes `Lzero` act on the mode by
   `-6`).  Hence `Lzero (z^s cos θ⁻¹) = -6 z^s cos θ⁻¹` and

     `bslOp α (z^s cos θ⁻¹) = z^s cos θ⁻¹ · (-α²s(s-1) - α(5+α)s - 6)`,

   whose bracket is `-(αs)² - 5(αs) - 6 = -(αs+2)(αs+3)`, which vanishes exactly for
   `αs ∈ {-2,-3}`; the choice `s = -3/α` is made (`mode_bslOp`).

2. **All three modulation outputs of `mode α` vanish identically** on the open quadrant
   (`Rop_mode`, `Uop_mode`, `Vop_mode`).  This is the point missed by the docstring's
   non-vacuity check: `(cos θ)⁻¹` is a *second* eigenfunction of `Lzero` for the eigenvalue `-6`
   (the other is `tan θ`), and it is precisely the one for which the proportionality constant
   `3 + αs` of `Rop`, `Uop`, `Vop` vanishes.  The docstring's check ("the same computation kills
   every separable homogeneous mode") only covers the modes whose modulation outputs are
   non-zero; the `z^{-3/α}/cos θ` mode has *identically zero* outputs, so all three `HkMem`
   hypotheses hold trivially (`HkMem_Rop_cex`, `HkMem_Uop_div_cex`, `HkMem_Vop_cex`, all proved
   through the general fact `HkMem_of_eqOn_Q0` that a profile vanishing on the open quadrant is
   in `ℋ^k`).

3. **The Dirichlet conditions are *value* conditions at single points.**  `IsBslSol` asks only
   `w z 0 = 0` and `w z (π/2) = 0`, and `SmoothOpen` constrains only the *open* quadrant
   `(0,∞) × (0,π/2)`.  `mode α` has the trace `z^{-3/α} ≠ 0` at `θ = 0` (and it blows up like
   `cos θ⁻¹` at `θ = π/2`), so it is *not* itself a witness; resetting the single value at
   `θ = 0` (a null set, exactly as the docstring does at `z = 0`) produces `cex α`, which is
   `C^∞` on the open quadrant and satisfies both Dirichlet *values* for every `z`.

So the class is genuinely bigger than `{0}`, and the `value at a single point` loophole that the
docstring patches at `z = 0` reappears at `θ = 0` (and `θ = π/2`).

## The fix

The interface must control the angular *traces* of the slice, e.g. by adding

  `∀ z, 0 < z → Tendsto (fun θ => w z θ) (nhdsWithin 0 (Ioi 0)) (nhds 0)`

(or `SmoothNbhd`/continuity of the slices down to `θ = 0`), which excludes `cex α` because
`mode α`'s trace is `z^{-3/α} ≠ 0`.  Restricting the conclusion to `0 < θ < π/2` does not help,
and requiring `HkMem α 6 w` does not help either.

## What is proved here

* `mode_bslOp`, `Rop_mode`, `Uop_mode`, `Vop_mode` — the exact algebraic core, for *general*
  `α ≠ 0`;
* `smoothOpen_cex`, `isBslSol_cex`, `HkMem_*_cex` — the four hypotheses for the witness;
* `exists_counterexample` — the conjunction of all five hypotheses with the *negation* of the
  conclusion;
* `HomClsZero_statement_false` — the negation of the statement of `HomClsZero`, in its own
  quantifier shape.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison
set_option autoImplicit false
set_option maxHeartbeats 800000

def mode (α : ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ (-(3 / α)) / Real.cos θ

theorem cos_ne_zero_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) : Real.cos θ ≠ 0 :=
  ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos],
    by linarith [hθ.2, Real.pi_pos]⟩)

theorem alpha_mul_exp (α : ℝ) (hα : α ≠ 0) : α * (-(3 / α)) = -3 := by field_simp

theorem zp_sq (α z : ℝ) (hz : 0 < z) :
    z ^ (2 : ℕ) * z ^ (-(3 / α) - 2) = z ^ (-(3 / α)) := by
  rw [show (z : ℝ) ^ (2 : ℕ) = z ^ (2 : ℝ) from (Real.rpow_natCast z 2).symm,
    ← Real.rpow_add hz]
  norm_num

theorem zp_one (α z : ℝ) (hz : 0 < z) : z * z ^ (-(3 / α) - 1) = z ^ (-(3 / α)) := by
  calc z * z ^ (-(3 / α) - 1) = z ^ (1 : ℝ) * z ^ (-(3 / α) - 1) := by rw [Real.rpow_one]
    _ = z ^ ((1 : ℝ) + (-(3 / α) - 1)) := by rw [Real.rpow_add hz]
    _ = z ^ (-(3 / α)) := by congr 1; ring

theorem pz_mode (α z θ : ℝ) :
    Work.Spaces.pz (mode α) z θ = (-(3 / α)) * z ^ (-(3 / α) - 1) / Real.cos θ := by
  simp only [Work.Spaces.pz, mode, deriv_div_const, Real.deriv_rpow_const]

theorem pzIter_two_mode (α z θ : ℝ) (hz : 0 < z) :
    Work.Spaces.pzIter 2 (mode α) z θ
      = (-(3 / α)) * (-(3 / α) - 1) * z ^ (-(3 / α) - 2) / Real.cos θ := by
  simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
  rw [show (fun z' : ℝ => deriv (fun z'' : ℝ => mode α z'' θ) z')
      = fun z' : ℝ => (-(3 / α)) * z' ^ (-(3 / α) - 1) / Real.cos θ from
    funext fun z' => pz_mode α z' θ]
  have hmain : HasDerivAt (fun z' : ℝ => (-(3 / α)) * z' ^ (-(3 / α) - 1))
      ((-(3 / α)) * ((-(3 / α) - 1) * z ^ (-(3 / α) - 1 - 1))) z :=
    (Real.hasDerivAt_rpow_const (x := z) (p := -(3 / α) - 1) (Or.inl (ne_of_gt hz))).const_mul _
  rw [deriv_div_const, hmain.deriv]
  rw [show (-(3 / α) - 1) - 1 = -(3 / α) - 2 from by ring]
  ring

theorem pth_mode (α z θ : ℝ) (hcos : Real.cos θ ≠ 0) :
    Work.Spaces.pth (mode α) z θ = z ^ (-(3 / α)) * (Real.sin θ / Real.cos θ ^ 2) := by
  simp only [Work.Spaces.pth, mode]
  rw [deriv_const_div _ Real.differentiableAt_cos hcos, Real.deriv_cos]
  ring

theorem pthIter_two_mode (α z θ : ℝ) (hcos : Real.cos θ ≠ 0) :
    Work.Spaces.pthIter 2 (mode α) z θ
      = z ^ (-(3 / α)) * deriv (fun θ' : ℝ => Real.sin θ' / Real.cos θ' ^ 2) θ := by
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
  have hev : (fun θ' : ℝ => deriv (fun θ'' : ℝ => mode α z θ'') θ') =ᶠ[𝓝 θ]
      fun θ' : ℝ => z ^ (-(3 / α)) * (Real.sin θ' / Real.cos θ' ^ 2) := by
    filter_upwards [Real.continuous_cos.continuousAt.eventually_ne hcos] with θ' h'
    exact pth_mode α z θ' h'
  rw [Filter.EventuallyEq.deriv_eq hev]
  have hG : HasDerivAt (fun θ' : ℝ => z ^ (-(3 / α)) * (Real.sin θ' / Real.cos θ' ^ 2))
      (z ^ (-(3 / α)) * deriv (fun θ' : ℝ => Real.sin θ' / Real.cos θ' ^ 2) θ) θ :=
    HasDerivAt.const_mul (z ^ (-(3 / α)))
      ((Real.differentiableAt_sin.div ((Real.differentiableAt_cos (x := θ)).pow 2)
        (pow_ne_zero 2 hcos)).hasDerivAt)
  exact hG.deriv

theorem pth_tan_mode (α z θ : ℝ) (hcos : Real.cos θ ≠ 0) :
    Work.Spaces.pth (fun z θ => Real.tan θ * mode α z θ) z θ
      = z ^ (-(3 / α)) * deriv (fun θ' : ℝ => Real.sin θ' / Real.cos θ' ^ 2) θ := by
  simp only [Work.Spaces.pth]
  have hev : (fun θ' : ℝ => Real.tan θ' * mode α z θ') =ᶠ[𝓝 θ]
      fun θ' : ℝ => z ^ (-(3 / α)) * (Real.sin θ' / Real.cos θ' ^ 2) := by
    filter_upwards [Real.continuous_cos.continuousAt.eventually_ne hcos] with θ' h'
    simp only [mode, Real.tan_eq_sin_div_cos]
    field_simp
  rw [Filter.EventuallyEq.deriv_eq hev]
  have hG : HasDerivAt (fun θ' : ℝ => z ^ (-(3 / α)) * (Real.sin θ' / Real.cos θ' ^ 2))
      (z ^ (-(3 / α)) * deriv (fun θ' : ℝ => Real.sin θ' / Real.cos θ' ^ 2) θ) θ :=
    HasDerivAt.const_mul (z ^ (-(3 / α)))
      ((Real.differentiableAt_sin.div ((Real.differentiableAt_cos (x := θ)).pow 2)
        (pow_ne_zero 2 hcos)).hasDerivAt)
  exact hG.deriv

theorem G_eq_tan_div_cos (θ : ℝ) (hcos : Real.cos θ ≠ 0) :
    Real.sin θ / Real.cos θ ^ 2 = Real.tan θ / Real.cos θ := by
  rw [Real.tan_eq_sin_div_cos]; field_simp

theorem Lzero_mode (α z θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Elliptic.Lzero (mode α) z θ = -6 * mode α z θ := by
  have hcos := cos_ne_zero_of_mem hθ
  have hX : Work.Spaces.pthIter 2 (mode α) z θ
      = Work.Spaces.pth (fun z θ => Real.tan θ * mode α z θ) z θ := by
    rw [pthIter_two_mode α z θ hcos, pth_tan_mode α z θ hcos]
  rw [Work.Elliptic.Lzero, hX]
  ring

theorem mode_bslOp (α z θ : ℝ) (hα : α ≠ 0) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Elliptic.bslOp α (mode α) z θ = 0 := by
  have hcoef : -α ^ 2 * (-(3 / α)) * (-(3 / α) - 1) - α * (5 + α) * (-(3 / α)) - 6 = 0 := by
    field_simp
    ring
  rw [Work.Elliptic.bslOp_apply, pzIter_two_mode α z θ hz, pz_mode α z θ, Lzero_mode α z θ hθ]
  simp only [mode]
  rw [show -(α ^ 2 * z ^ 2) * ((-(3 / α)) * (-(3 / α) - 1) * z ^ (-(3 / α) - 2) / Real.cos θ)
        - (α * (5 + α) * z) * ((-(3 / α)) * z ^ (-(3 / α) - 1) / Real.cos θ)
        + (-6 * (z ^ (-(3 / α)) / Real.cos θ))
      = (Real.cos θ)⁻¹ *
          (-(α ^ 2 * (-(3 / α)) * (-(3 / α) - 1)) * (z ^ (2 : ℕ) * z ^ (-(3 / α) - 2))
            - (α * (5 + α) * (-(3 / α))) * (z * z ^ (-(3 / α) - 1))
            - 6 * z ^ (-(3 / α))) from by ring]
  rw [zp_sq α z hz, zp_one α z hz]
  rw [show -(α ^ 2 * (-(3 / α)) * (-(3 / α) - 1)) * z ^ (-(3 / α))
        - (α * (5 + α) * (-(3 / α))) * z ^ (-(3 / α)) - 6 * z ^ (-(3 / α))
      = z ^ (-(3 / α))
        * (-α ^ 2 * (-(3 / α)) * (-(3 / α) - 1) - α * (5 + α) * (-(3 / α)) - 6) from by ring]
  rw [hcoef, mul_zero, mul_zero]

theorem Uop_mode (α z θ : ℝ) (hα : α ≠ 0) (hz : 0 < z) :
    Work.Construction.Uop α (mode α) z θ = 0 := by
  have hcoef : -3 - α * (-(3 / α)) = 0 := by rw [alpha_mul_exp α hα]; ring
  rw [Work.Construction.Uop, pz_mode α z θ]
  simp only [mode]
  rw [show -3 * (z ^ (-(3 / α)) / Real.cos θ)
        - α * z * ((-(3 / α)) * z ^ (-(3 / α) - 1) / Real.cos θ)
      = (z ^ (-(3 / α)) / Real.cos θ) * (-3 - α * (-(3 / α))) from by
    rw [← zp_one α z hz]; ring]
  rw [hcoef, mul_zero]

theorem Vop_mode (α z θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Construction.Vop (mode α) z θ = 0 := by
  have hcos := cos_ne_zero_of_mem hθ
  rw [Work.Construction.Vop, pth_mode α z θ hcos, G_eq_tan_div_cos θ hcos]
  simp only [mode]
  field_simp
  ring

theorem Rop_mode (α z θ : ℝ) (hα : α ≠ 0) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Construction.Rop α (mode α) z θ = 0 := by
  have hcos := cos_ne_zero_of_mem hθ
  have hcoef : 3 + α * (-(3 / α)) = 0 := by rw [alpha_mul_exp α hα]; ring
  rw [Work.Construction.Rop, pz_mode α z θ, pth_mode α z θ hcos]
  simp only [mode]
  rw [show (2 * Real.sin θ * (z ^ (-(3 / α)) / Real.cos θ)
        + α * Real.sin θ * z * ((-(3 / α)) * z ^ (-(3 / α) - 1) / Real.cos θ)
        + Real.cos θ * (z ^ (-(3 / α)) * (Real.sin θ / Real.cos θ ^ 2))) / Real.cos θ
      = (Real.sin θ / Real.cos θ) * ((Real.cos θ)⁻¹ * ((z * z ^ (-(3 / α) - 1)) * (3 + α * (-(3 / α))))) from by
    rw [← zp_one α z hz]
    field_simp
    ring]
  rw [hcoef, mul_zero, mul_zero, mul_zero]


/-! ## 3. The witness: the mode with the value at `θ = 0` overwritten -/

/-- The witness: `z^{-3/α}/cos θ` on the open quadrant, with the *value* at `θ = 0` set to `0`.
This is a genuine function (no regularity is required at `θ = 0`: `SmoothOpen` constrains only
the open quadrant, and `IsBslSol` only the *values* at the two endpoints). -/
def cex (α : ℝ) : ℝ → ℝ → ℝ := fun z θ => if θ = 0 then 0 else mode α z θ

theorem cex_apply (α z θ : ℝ) : cex α z θ = if θ = 0 then 0 else mode α z θ := rfl

theorem cex_of_ne (α z θ : ℝ) (hθ : θ ≠ 0) : cex α z θ = mode α z θ := by
  simp only [cex, if_neg hθ]

theorem cex_zero (α z : ℝ) : cex α z 0 = 0 := by simp [cex]

theorem cex_pi_div_two (α z : ℝ) : cex α z (π / 2) = 0 := by
  simp only [cex, if_neg (by linarith [Real.pi_pos] : (π / 2 : ℝ) ≠ 0), mode,
    Real.cos_pi_div_two, div_zero]

/-! ## 4. Locality: on the open quadrant `cex` has the same derivatives as `mode` -/

theorem pz_cex (α z θ : ℝ) (hθ : θ ≠ 0) :
    Work.Spaces.pz (cex α) z θ = Work.Spaces.pz (mode α) z θ := by
  simp only [Work.Spaces.pz]
  rw [show (fun z' : ℝ => cex α z' θ) = fun z' : ℝ => mode α z' θ from
    funext fun z' => cex_of_ne α z' θ hθ]

theorem pth_cex (α z θ : ℝ) (hθ : θ ≠ 0) :
    Work.Spaces.pth (cex α) z θ = Work.Spaces.pth (mode α) z θ := by
  simp only [Work.Spaces.pth]
  rw [Filter.EventuallyEq.deriv_eq (show (fun θ' : ℝ => cex α z θ') =ᶠ[𝓝 θ]
      fun θ' : ℝ => mode α z θ' from by
    filter_upwards [compl_singleton_mem_nhds_iff.mpr hθ] with θ' h'
    exact cex_of_ne α z θ' h')]

theorem pzIter_two_cex (α z θ : ℝ) (hθ : θ ≠ 0) :
    Work.Spaces.pzIter 2 (cex α) z θ = Work.Spaces.pzIter 2 (mode α) z θ := by
  simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
  rw [show (fun z' : ℝ => deriv (fun z'' : ℝ => cex α z'' θ) z')
      = fun z' : ℝ => deriv (fun z'' : ℝ => mode α z'' θ) z' from
    funext fun z' => pz_cex α z' θ hθ]

theorem pthIter_two_cex (α z θ : ℝ) (hθ : θ ≠ 0) :
    Work.Spaces.pthIter 2 (cex α) z θ = Work.Spaces.pthIter 2 (mode α) z θ := by
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
  rw [Filter.EventuallyEq.deriv_eq (show (fun θ' : ℝ => deriv (fun θ'' : ℝ => cex α z θ'') θ')
      =ᶠ[𝓝 θ] fun θ' : ℝ => deriv (fun θ'' : ℝ => mode α z θ'') θ' from by
    filter_upwards [compl_singleton_mem_nhds_iff.mpr hθ] with θ' h'
    exact pth_cex α z θ' h')]

theorem pth_tan_cex (α z θ : ℝ) (hθ : θ ≠ 0) :
    Work.Spaces.pth (fun z θ => Real.tan θ * cex α z θ) z θ
      = Work.Spaces.pth (fun z θ => Real.tan θ * mode α z θ) z θ := by
  simp only [Work.Spaces.pth]
  rw [Filter.EventuallyEq.deriv_eq (show (fun θ' : ℝ => Real.tan θ' * cex α z θ')
      =ᶠ[𝓝 θ] fun θ' : ℝ => Real.tan θ' * mode α z θ' from by
    filter_upwards [compl_singleton_mem_nhds_iff.mpr hθ] with θ' h'
    rw [cex_of_ne α z θ' h'])]

/-! ## 5. The witness satisfies every hypothesis of `HomClsZero` -/

/-- **The witness solves the homogeneous law on the open quadrant.** -/
theorem cex_bslOp (α z θ : ℝ) (hα : α ≠ 0) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Elliptic.bslOp α (cex α) z θ = 0 := by
  have hθ0 : θ ≠ 0 := ne_of_gt hθ.1
  rw [Work.Elliptic.bslOp_apply, pzIter_two_cex α z θ hθ0, pz_cex α z θ hθ0,
    Work.Elliptic.Lzero, pthIter_two_cex α z θ hθ0, pth_tan_cex α z θ hθ0]
  rw [cex_of_ne α z θ hθ0]
  exact mode_bslOp α z θ hα hz hθ

/-- **The `Rop`-output of the witness vanishes on the open quadrant.** -/
theorem Rop_cex (α z θ : ℝ) (hα : α ≠ 0) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Construction.Rop α (cex α) z θ = 0 := by
  have hθ0 : θ ≠ 0 := ne_of_gt hθ.1
  rw [Work.Construction.Rop, pz_cex α z θ hθ0, pth_cex α z θ hθ0]
  rw [cex_of_ne α z θ hθ0]
  exact Rop_mode α z θ hα hz hθ

/-- **The `Uop`-output of the witness vanishes on the open quadrant.** -/
theorem Uop_cex (α z θ : ℝ) (hα : α ≠ 0) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Construction.Uop α (cex α) z θ = 0 := by
  have hθ0 : θ ≠ 0 := ne_of_gt hθ.1
  rw [Work.Construction.Uop, pz_cex α z θ hθ0]
  rw [cex_of_ne α z θ hθ0]
  exact Uop_mode α z θ hα hz

/-- **The `Vop`-output of the witness vanishes on the open quadrant.** -/
theorem Vop_cex (α z θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Construction.Vop (cex α) z θ = 0 := by
  have hθ0 : θ ≠ 0 := ne_of_gt hθ.1
  rw [Work.Construction.Vop, pth_cex α z θ hθ0]
  rw [cex_of_ne α z θ hθ0]
  exact Vop_mode α z θ hθ

/-- The modulation outputs of the witness, as *functions of the pair* `(z,θ)`, vanish on the
open quadrant `Q0`. -/
theorem Rop_cex_eqOn_Q0 (α : ℝ) (hα : α ≠ 0) : ∀ p ∈ Work.FTS.EllipticEst.Q0,
    Work.Construction.Rop α (cex α) p.1 p.2 = 0 := by
  intro p hp
  obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact Rop_cex α p.1 p.2 hα hz ⟨hθ1, hθ2⟩

theorem Uop_div_cex_eqOn_Q0 (α : ℝ) (hα : α ≠ 0) : ∀ p ∈ Work.FTS.EllipticEst.Q0,
    Work.Construction.Uop α (cex α) p.1 p.2 / Work.Construction.s2 p.2 = 0 := by
  intro p hp
  obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  rw [Uop_cex α p.1 p.2 hα hz ⟨hθ1, hθ2⟩, zero_div]

theorem Vop_cex_eqOn_Q0 (α : ℝ) : ∀ p ∈ Work.FTS.EllipticEst.Q0,
    Work.Construction.Vop (cex α) p.1 p.2 = 0 := by
  intro p hp
  obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact Vop_cex α p.1 p.2 ⟨hθ1, hθ2⟩


/-! ## 6. `SmoothOpen` and `IsBslSol` for the witness -/

open Work.FTS.EllipticEst in
theorem contDiffOn_uncurry_mode (α : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (mode α)) Q0 := by
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1 ^ (-(3 / α))) Q0 :=
    contDiffOn_fst.rpow_const_of_ne (fun p hp => ne_of_gt (mem_Q0.mp hp).1)
  have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.cos p.2) Q0 :=
    (Real.contDiff_cos.comp_contDiffOn contDiffOn_snd).congr (fun p _ => rfl)
  have h3 : ContDiffOn ℝ n (fun p : ℝ × ℝ => (Real.cos p.2)⁻¹) Q0 :=
    h2.inv (fun p hp => cos_ne_zero_of_mem ⟨(mem_Q0.mp hp).2.1, (mem_Q0.mp hp).2.2⟩)
  refine (h1.mul h3).congr (fun p hp => ?_)
  simp only [Function.uncurry, mode, Pi.mul_apply, div_eq_mul_inv]

open Work.FTS.EllipticEst in
theorem smoothOpen_cex (α : ℝ) : SmoothOpen (cex α) :=
  smoothOpen_of_forall fun n =>
    (contDiffOn_uncurry_mode α n).congr fun p hp => by
      simp only [Function.uncurry]
      exact cex_of_ne α p.1 p.2 (ne_of_gt (mem_Q0.mp hp).2.1)

/-- **The witness is a homogeneous solution in the class of `IsBslSol`.** -/
theorem isBslSol_cex (α : ℝ) (hα : 0 < α) :
    Work.Elliptic.IsBslSol α (fun _ _ => (0 : ℝ)) (cex α) := by
  refine ⟨?_, fun z => cex_zero α z, fun z => cex_pi_div_two α z, ?_⟩
  · intro z hz θ hθ1 hθ2
    exact cex_bslOp α z θ (ne_of_gt hα) hz ⟨hθ1, hθ2⟩
  · intro θ _
    by_cases h0 : θ = 0
    · subst h0
      simpa [cex_zero] using tendsto_const_nhds
    · have hfun : (fun z : ℝ => cex α z θ) = fun z : ℝ => z ^ (-(3 / α)) * (Real.cos θ)⁻¹ := by
        funext z
        rw [cex_of_ne α z θ h0, mode, div_eq_mul_inv]
      rw [hfun]
      have hlim : Filter.Tendsto (fun z : ℝ => z ^ (-(3 / α))) Filter.atTop (𝓝 0) :=
        tendsto_rpow_neg_atTop (by positivity)
      simpa [mul_zero] using hlim.mul_const ((Real.cos θ)⁻¹)

/-! ## 7. A function vanishing on the open quadrant is in `ℋ^k` -/

/-- On an open set where `f` vanishes, so does `∂_z f`. -/
theorem pz_eqOn_zero {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hf : ∀ p ∈ V, f p.1 p.2 = 0) : ∀ p ∈ V, Work.Spaces.pz f p.1 p.2 = 0 := by
  intro p hp
  have hnb : {z : ℝ | (z, p.2) ∈ V} ∈ 𝓝 p.1 := by
    have hpre : {z : ℝ | (z, p.2) ∈ V} = (fun z : ℝ => (z, p.2)) ⁻¹' V := rfl
    rw [hpre]
    exact (hV.preimage (by continuity)).mem_nhds hp
  have hev : (fun z : ℝ => f z p.2) =ᶠ[𝓝 p.1] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnb] with z hz
    exact hf (z, p.2) hz
  simp only [Work.Spaces.pz]
  rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]

/-- On an open set where `f` vanishes, so does `∂_θ f`. -/
theorem pth_eqOn_zero {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hf : ∀ p ∈ V, f p.1 p.2 = 0) : ∀ p ∈ V, Work.Spaces.pth f p.1 p.2 = 0 := by
  intro p hp
  have hnb : {θ : ℝ | (p.1, θ) ∈ V} ∈ 𝓝 p.2 := by
    have hpre : {θ : ℝ | (p.1, θ) ∈ V} = (fun θ : ℝ => (p.1, θ)) ⁻¹' V := rfl
    rw [hpre]
    exact (hV.preimage (by continuity)).mem_nhds hp
  have hev : (fun θ : ℝ => f p.1 θ) =ᶠ[𝓝 p.2] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnb] with θ hθ
    exact hf (p.1, θ) hθ
  simp only [Work.Spaces.pth]
  rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]

theorem dzIter_eqOn_zero {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hf : ∀ p ∈ V, f p.1 p.2 = 0) :
    ∀ i (p : ℝ × ℝ), p ∈ V → Work.Spaces.DzIter i f p.1 p.2 = 0 := by
  intro i
  induction i with
  | zero => exact hf
  | succ i ih =>
      intro p hp
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
      rw [pz_eqOn_zero hV ih p hp, mul_zero]

theorem dthIter_eqOn_zero {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hf : ∀ p ∈ V, f p.1 p.2 = 0) :
    ∀ i (p : ℝ × ℝ), p ∈ V → Work.Spaces.DthIter i f p.1 p.2 = 0 := by
  intro i
  induction i with
  | zero => exact hf
  | succ i ih =>
      intro p hp
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth]
      rw [pth_eqOn_zero hV ih p hp, mul_zero]

theorem mixed_eqOn_zero {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hf : ∀ p ∈ V, f p.1 p.2 = 0) :
    ∀ j i (p : ℝ × ℝ), p ∈ V → Work.Spaces.mixed j i f p.1 p.2 = 0 := by
  intro j i p hp
  change Work.Spaces.DzIter j (Work.Spaces.DthIter i f) p.1 p.2 = 0
  exact dzIter_eqOn_zero hV (dthIter_eqOn_zero hV hf i) j p hp

theorem hkIntegrand_eqOn_zero {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hf : ∀ p ∈ V, f p.1 p.2 = 0) (α : ℝ) (k : ℕ) :
    ∀ p ∈ V, Work.Spaces.HkIntegrand α k f p.1 p.2 = 0 := by
  intro p hp
  have h1 : ∀ i, Work.Spaces.DzIter i f p.1 p.2 = 0 := fun i => dzIter_eqOn_zero hV hf i p hp
  have h2 : ∀ j i, Work.Spaces.mixed j i f p.1 p.2 = 0 :=
    fun j i => mixed_eqOn_zero hV hf j i p hp
  simp only [Work.Spaces.HkIntegrand]
  simp [h1, h2]

/-- At `z = 0` every `HkIntegrand` vanishes, for *every* profile (the radial weight `w 0` is `0`
in Lean's totalised arithmetic, and `Wt α 0 θ = w 0 * wTheta α θ = 0`). -/
theorem hkIntegrand_zero_z (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt]

/-- **A profile vanishing on the open quadrant lies in `ℋ^k`.**  For each `z > 0` the
`θ`-integrand vanishes on `Ioo 0 (π/2)`, hence on `Iθ` up to the null set `{0, π/2}`; at `z = 0`
it vanishes identically.  So each inner integral is `0` and the outer integrand is the zero
function. -/
theorem HkMem_of_eqOn_Q0 {f : ℝ → ℝ → ℝ} (α : ℝ) (k : ℕ)
    (hf : ∀ p ∈ Work.FTS.EllipticEst.Q0, f p.1 p.2 = 0) :
    Work.Spaces.HkMem α k f := by
  have hQ0 := hkIntegrand_eqOn_zero (f := f) Work.FTS.EllipticEst.isOpen_Q0 hf α k
  constructor
  · intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      refine MeasureTheory.integrableOn_zero.congr_fun (fun θ _ => (hkIntegrand_zero_z α k f θ).symm)
        measurableSet_Icc
    · refine (integrableOn_Icc_iff_integrableOn_Ioo (f := fun θ => Work.Spaces.HkIntegrand α k f z θ)
        (a := 0) (b := π / 2)).mpr ?_
      refine MeasureTheory.integrableOn_zero.congr_fun (fun θ hθ => ?_) measurableSet_Ioo
      exact (hQ0 (z, θ) (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hzpos, hθ.1, hθ.2⟩)).symm
  · refine MeasureTheory.integrableOn_zero.congr_fun (fun z hz => ?_) measurableSet_Ici
    refine (show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) = (0 : ℝ) from ?_).symm
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      simp only [hkIntegrand_zero_z]
      simp
    · have hnull : volume ({0, π / 2} : Set ℝ) = 0 := by
        rw [show ({0, π / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {π / 2} from by
          ext x
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
        exact measure_union_null (measure_singleton 0) (measure_singleton (π / 2))
      have hcongr : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          = ∫ θ in Work.Spaces.Iθ, (0 : ℝ) := by
        refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
        refine Filter.Eventually.mono (MeasureTheory.compl_mem_ae_iff.mpr hnull) ?_
        intro θ hθ hmem
        obtain ⟨hθ0, hθ2⟩ := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hθ
        exact hQ0 (z, θ) (Work.FTS.EllipticEst.mem_Q0.mpr
          ⟨hzpos, lt_of_le_of_ne hmem.1 (Ne.symm hθ0), lt_of_le_of_ne hmem.2 hθ2⟩)
      rw [hcongr]
      simp


/-! ## 8. `ℋ⁶`-membership of the three modulation outputs of the witness -/

theorem HkMem_Rop_cex (α : ℝ) (hα : α ≠ 0) :
    Work.Spaces.HkMem α 6 (Work.Construction.Rop α (cex α)) :=
  HkMem_of_eqOn_Q0 α 6 (Rop_cex_eqOn_Q0 α hα)

theorem HkMem_Uop_div_cex (α : ℝ) (hα : α ≠ 0) :
    Work.Spaces.HkMem α 6
      (fun z θ => Work.Construction.Uop α (cex α) z θ / Work.Construction.s2 θ) :=
  HkMem_of_eqOn_Q0 α 6 (Uop_div_cex_eqOn_Q0 α hα)

theorem HkMem_Vop_cex (α : ℝ) :
    Work.Spaces.HkMem α 6 (Work.Construction.Vop (cex α)) :=
  HkMem_of_eqOn_Q0 α 6 (Vop_cex_eqOn_Q0 α)

/-! ## 9. The counterexample -/

/-- **`Work.FTS.StrongEps.EComparison.HomClsZero` is FALSE.**  At `α = 1` the witness
`cex 1` (the invisible mode `z^{-3}/cos θ`, with the *value* at `θ = 0` reset to `0`) satisfies
every hypothesis of `HomClsZero` — open-quadrant smoothness, the homogeneous elliptic law, the two
Dirichlet *values*, the decay at `z → ∞`, and the three `ℋ⁶` memberships (indeed all three outputs
vanish identically on the open quadrant) — while `cex 1 1 (π/4) = √2 ≠ 0`. -/
theorem exists_counterexample :
    ∃ (α : ℝ), 0 < α ∧ α ≤ 1 ∧ ∃ w : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen w ∧
      Work.Elliptic.IsBslSol α (fun _ _ => (0 : ℝ)) w ∧
      Work.Spaces.HkMem α 6 (Work.Construction.Rop α w) ∧
      Work.Spaces.HkMem α 6
        (fun z θ => Work.Construction.Uop α w z θ / Work.Construction.s2 θ) ∧
      Work.Spaces.HkMem α 6 (Work.Construction.Vop w) ∧
      ¬ (∀ z : ℝ, 0 < z → ∀ θ ∈ Work.Spaces.Iθ, w z θ = 0) := by
  refine ⟨1, one_pos, le_refl 1, cex 1, smoothOpen_cex 1, isBslSol_cex 1 one_pos,
    HkMem_Rop_cex 1 one_ne_zero, HkMem_Uop_div_cex 1 one_ne_zero, HkMem_Vop_cex 1, ?_⟩
  intro h
  have hmem : (π / 4 : ℝ) ∈ Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨by positivity, by linarith [Real.pi_pos]⟩
  have hval := h 1 one_pos (π / 4) hmem
  have hne : cex 1 (1 : ℝ) (π / 4) = Real.sqrt 2 := by
    rw [cex_of_ne 1 1 (π / 4) (by positivity : (π / 4 : ℝ) ≠ 0), mode, Real.one_rpow,
      Real.cos_pi_div_four]
    have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp
    linarith [hs]
  rw [hne] at hval
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  linarith


/-- **The statement of `HomClsZero` is false**, in its own quantifier shape. -/
theorem HomClsZero_statement_false :
    ¬ (∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ w : ℝ → ℝ → ℝ,
        Work.FTS.EllipticEst.SmoothOpen w →
        Work.Elliptic.IsBslSol α (fun _ _ => (0 : ℝ)) w →
        Work.Spaces.HkMem α 6 (Work.Construction.Rop α w) →
        Work.Spaces.HkMem α 6
          (fun z θ => Work.Construction.Uop α w z θ / Work.Construction.s2 θ) →
        Work.Spaces.HkMem α 6 (Work.Construction.Vop w) →
        ∀ z : ℝ, 0 < z → ∀ θ ∈ Work.Spaces.Iθ, w z θ = 0) := by
  rintro h
  obtain ⟨α, hα, hα1, w, h1, h2, h3, h4, h5, h6⟩ := exists_counterexample
  exact h6 (h α hα hα1 w h1 h2 h3 h4 h5)

end Work.FTS.StrongEps.EComparison
