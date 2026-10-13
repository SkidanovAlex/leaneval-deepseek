/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Final.Rep.Mine.TopSlotTwo` — the pointwise `Tk`-weight decomposition (clean partial copy)

Verbatim copy of the declarations of `Submission/Work/FTS/EllipticEst/Mine/TopSlotTwo.lean`
up to and including `Tk_pointwise_le_closed` (the only declarations of that file that the
level-`2` top-slot cone uses: `TopSlotTwoFts/AHalf`, `TopSlotTwoFts/BHalf`, `H2W/slot20_bound`),
under the same namespace `Work.FTS.EllipticEst.Mine`.

Reason for the copy: `Mine/TopSlotTwo.lean` acquired
`import Submission.Work.FTS.EllipticEst.Mine.ShiftLevelOne`, which drags in `RPFresh/excess_finite`
through `H2W/HkMem_zero_sliceData`; that broke the build of the whole level-`2` cone.  The
declarations below do not depend on `Mine.ShiftLevelOne`, so the consumers are re-homed onto this
copy.  It is now the *unique* provider of these names: `Final.ReHome.TkKit` is an alias of it, so
that the two trees do not clash.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.SliceDecompDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Mine

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The pointwise expansion of `D_θ²` and the weight algebra -/

/-- **The expansion of `D_θ²`**: `D_θ²f = sin²(2θ)·∂_θ²f + 2 sin(2θ)cos(2θ)·∂_θf`. -/
theorem DthIter_two_eq (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (h2 : DifferentiableAt ℝ (fun θ' => deriv (fun t => f z t) θ') θ) :
    Work.Spaces.DthIter 2 f z θ
      = (Real.sin (2 * θ)) ^ 2 * deriv (fun θ' => deriv (fun t => f z t) θ') θ
        + 2 * Real.sin (2 * θ) * Real.cos (2 * θ) * deriv (fun t => f z t) θ := by
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h2' := h1.sin
    rw [show Real.cos (2 * θ) * 2 = 2 * Real.cos (2 * θ) by ring] at h2'
    exact h2'
  have hd2 : deriv (fun t => Real.sin (2 * t) * deriv (fun t' => f z t') t) θ
      = 2 * Real.cos (2 * θ) * deriv (fun t => f z t) θ
        + Real.sin (2 * θ) * deriv (fun θ' => deriv (fun t => f z t) θ') θ := by
    have heq : (fun t : ℝ => Real.sin (2 * t) * deriv (fun t' => f z t') t)
        = (fun t : ℝ => Real.sin (2 * t)) * (fun t : ℝ => deriv (fun t' => f z t') t) := rfl
    rw [heq, deriv_mul hsin.differentiableAt h2, hsin.deriv]
  show Real.sin (2 * θ) *
      deriv (fun t => Real.sin (2 * t) * deriv (fun t' => f z t') t) θ = _
  rw [hd2]
  ring

/-- **The squared `D_θ²`-weight identity**: for `θ` in the open interval the `Tk`-integrand at
level `2` is `w(z)²` times the square of the expansion, weighted by `sGam`. -/
theorem Tk_pointwise_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : 0 < θ)
    (hθ' : θ < Real.pi / 2)
    (h2 : DifferentiableAt ℝ (fun θ' => deriv (fun t => f z t) θ') θ) :
    (Work.Spaces.DthIter 2 f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 *
          (((Real.sin (2 * θ)) ^ 2 * deriv (fun θ' => deriv (fun t => f z t) θ') θ
              + 2 * Real.sin (2 * θ) * Real.cos (2 * θ) * deriv (fun t => f z t) θ) ^ 2
            * Work.FTS.EllipticEst.sGam α θ) := by
  rw [DthIter_two_eq f z θ h2, mix_term_eq ⟨hθ.le, hθ'.le⟩ α z]

/-- `sin²(2θ)·sGam α θ = σ₂` on the open interval. -/
theorem sin_sq_mul_sGam (α : ℝ) {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    (Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.sGam α θ
      = sig2 (Work.Spaces.gam α) θ := by
  have hs : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  have h : (Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.sGam α θ
      = (Real.sin (2 * θ)) ^ ((2 : ℝ) + (-(Work.Spaces.gam α))) := by
    rw [Work.FTS.EllipticEst.sGam, ← Real.rpow_ofNat, ← Real.rpow_add hs]
  rw [h, show (2 : ℝ) + (-(Work.Spaces.gam α)) = 2 - Work.Spaces.gam α by ring]
  rfl

/-- `sin⁴(2θ)·sGam α θ = σ₄` on the open interval. -/
theorem sin_four_mul_sGam (α : ℝ) {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    (Real.sin (2 * θ)) ^ 4 * Work.FTS.EllipticEst.sGam α θ
      = sig4 (Work.Spaces.gam α) θ := by
  have hs : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  have h : (Real.sin (2 * θ)) ^ 4 * Work.FTS.EllipticEst.sGam α θ
      = (Real.sin (2 * θ)) ^ ((4 : ℝ) + (-(Work.Spaces.gam α))) := by
    rw [Work.FTS.EllipticEst.sGam, ← Real.rpow_ofNat, ← Real.rpow_add hs]
  rw [h, show (4 : ℝ) + (-(Work.Spaces.gam α)) = 4 - Work.Spaces.gam α by ring]
  rfl

/-- **The `σ₄`/`σ₂` decomposition of the level-`2` `Tk`-integrand**: pointwise,

`(D_θ²f · Wt)² ≤ 2 w²·(∂_θ²f)²·σ₄ + 8 w²·(∂_θf)²·σ₂`,

where `σ₄ = sin(2θ)^{4-γ}`, `σ₂ = sin(2θ)^{2-γ}` at `γ = gam α`.  This is the pointwise form of
`Tk α 2 f ≤ 2∫∫(∂_θ²f)²σ₄w² + 8∫∫(∂_θf)²σ₂w²`; it is the only place where the weight arithmetic
(`sin²·sGam = σ₂`, `sin⁴·sGam = σ₄`) is used. -/
theorem Tk_pointwise_le (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : 0 < θ)
    (hθ' : θ < Real.pi / 2)
    (h2 : DifferentiableAt ℝ (fun θ' => deriv (fun t => f z t) θ') θ) :
    (Work.Spaces.DthIter 2 f z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 2 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2 * sig4 (Work.Spaces.gam α) θ)
        + 8 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ) := by
  have hs : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  have hg : 0 < Work.FTS.EllipticEst.sGam α θ := by
    rw [Work.FTS.EllipticEst.sGam]
    exact Real.rpow_pos_of_pos hs _
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  set a : ℝ := deriv (fun θ' => deriv (fun t => f z t) θ') θ with hadef
  set b : ℝ := deriv (fun t => f z t) θ with hbdef
  set s : ℝ := Real.sin (2 * θ) with hsdef
  set c : ℝ := Real.cos (2 * θ) with hcdef
  have hcore : (s ^ 2 * a + 2 * s * c * b) ^ 2 * Work.FTS.EllipticEst.sGam α θ
      ≤ 2 * (a ^ 2 * sig4 (Work.Spaces.gam α) θ)
        + 8 * (b ^ 2 * sig2 (Work.Spaces.gam α) θ) := by
    have h1 : (s ^ 2 * a + 2 * s * c * b) ^ 2
        ≤ 2 * (s ^ 2 * a) ^ 2 + 2 * (2 * s * c * b) ^ 2 := by
      nlinarith [sq_nonneg (s ^ 2 * a - 2 * s * c * b)]
    have h3 : c ^ 2 ≤ 1 := by
      rw [hcdef]
      exact Real.cos_sq_le_one (2 * θ)
    have h5 : (2 * (s ^ 2 * a) ^ 2 + 2 * (2 * s * c * b) ^ 2)
          * Work.FTS.EllipticEst.sGam α θ
        ≤ (2 * (s ^ 2 * a) ^ 2 + 2 * (2 * s * b) ^ 2)
            * Work.FTS.EllipticEst.sGam α θ := by
      have hkey : (2 * s * c * b) ^ 2 ≤ (2 * s * b) ^ 2 := by
        nlinarith [h3, sq_nonneg (2 * s * b), sq_nonneg s, sq_nonneg b]
      exact mul_le_mul_of_nonneg_right (by linarith [hkey]) hg.le
    have h6 : (2 * (s ^ 2 * a) ^ 2 + 2 * (2 * s * b) ^ 2) * Work.FTS.EllipticEst.sGam α θ
        = 2 * (a ^ 2 * (s ^ 4 * Work.FTS.EllipticEst.sGam α θ))
          + 8 * (b ^ 2 * (s ^ 2 * Work.FTS.EllipticEst.sGam α θ)) := by ring
    have h7 : s ^ 4 * Work.FTS.EllipticEst.sGam α θ = sig4 (Work.Spaces.gam α) θ := by
      rw [hsdef]
      exact sin_four_mul_sGam α hθ hθ'
    have h8 : s ^ 2 * Work.FTS.EllipticEst.sGam α θ = sig2 (Work.Spaces.gam α) θ := by
      rw [hsdef]
      exact sin_sq_mul_sGam α hθ hθ'
    calc (s ^ 2 * a + 2 * s * c * b) ^ 2 * Work.FTS.EllipticEst.sGam α θ
        ≤ (2 * (s ^ 2 * a) ^ 2 + 2 * (2 * s * c * b) ^ 2)
            * Work.FTS.EllipticEst.sGam α θ := mul_le_mul_of_nonneg_right h1 hg.le
      _ ≤ (2 * (s ^ 2 * a) ^ 2 + 2 * (2 * s * b) ^ 2)
            * Work.FTS.EllipticEst.sGam α θ := h5
      _ = 2 * (a ^ 2 * (s ^ 4 * Work.FTS.EllipticEst.sGam α θ))
            + 8 * (b ^ 2 * (s ^ 2 * Work.FTS.EllipticEst.sGam α θ)) := h6
      _ = 2 * (a ^ 2 * sig4 (Work.Spaces.gam α) θ)
            + 8 * (b ^ 2 * sig2 (Work.Spaces.gam α) θ) := by rw [h7, h8]
  rw [Tk_pointwise_eq α f z θ hθ hθ' h2]
  have hone : (Work.Spaces.w z) ^ 2
        * (((Real.sin (2 * θ)) ^ 2 * deriv (fun θ' => deriv (fun t => f z t) θ') θ
              + 2 * Real.sin (2 * θ) * Real.cos (2 * θ) * deriv (fun t => f z t) θ) ^ 2
            * Work.FTS.EllipticEst.sGam α θ)
      = (Work.Spaces.w z) ^ 2 * ((s ^ 2 * a + 2 * s * c * b) ^ 2
          * Work.FTS.EllipticEst.sGam α θ) := by
    rw [hsdef, hcdef, hadef, hbdef]
  rw [hone]
  calc (Work.Spaces.w z) ^ 2 * ((s ^ 2 * a + 2 * s * c * b) ^ 2
          * Work.FTS.EllipticEst.sGam α θ)
      ≤ (Work.Spaces.w z) ^ 2 * (2 * (a ^ 2 * sig4 (Work.Spaces.gam α) θ)
          + 8 * (b ^ 2 * sig2 (Work.Spaces.gam α) θ)) := mul_le_mul_of_nonneg_left hcore hw2
    _ = 2 * (Work.Spaces.w z) ^ 2
          * ((deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2 * sig4 (Work.Spaces.gam α) θ)
        + 8 * (Work.Spaces.w z) ^ 2
          * ((deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ) := by
        rw [hadef, hbdef]; ring

/-- `Wt` vanishes wherever `sin(2θ)` does (for `α > 0`). -/
theorem Wt_zero_of_sin_eq_zero {α z θ : ℝ} (hα : 0 < α) (h : Real.sin (2 * θ) = 0) :
    Work.Spaces.Wt α z θ = 0 := by
  have hg : Work.Spaces.gam α ≠ 0 := ne_of_gt (Work.Spaces.gam_pos hα)
  have hneg : -(Work.Spaces.gam α / 2) ≠ 0 := by
    intro hc
    exact hg (by linarith)
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, h, Real.zero_rpow hneg, mul_zero]

/-- **The closed-interval form of `Tk_pointwise_le`.**  On the closed slice `Iθ` both sides
vanish at the two endpoints (`Wt` and the weights `σ₄`, `σ₂` all vanish there, `4 - gam α` and
`2 - gam α` being non-zero for `α ≤ 1/4`), so the pointwise bound holds on all of `Iθ` as soon as
it holds on the open interval. -/
theorem Tk_pointwise_le_closed (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (f : ℝ → ℝ → ℝ)
    (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ)
    (h2 : ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
      DifferentiableAt ℝ (fun t => deriv (fun s => f z s) t) θ') :
    (Work.Spaces.DthIter 2 f z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 2 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2 * sig4 (Work.Spaces.gam α) θ)
        + 8 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ) := by
  have hgam2 : Work.Spaces.gam α ≤ 11 / 10 := by
    rw [Work.Spaces.gam]
    linarith
  rcases hθ with ⟨h0, hpi⟩
  rcases lt_or_eq_of_le h0 with h | h
  · rcases lt_or_eq_of_le hpi with h' | h'
    · exact Tk_pointwise_le α f z θ h h' (h2 θ ⟨h, h'⟩)
    · subst h'
      have hsin : Real.sin (2 * (Real.pi / 2)) = 0 := by
        rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      have hW : Work.Spaces.Wt α z (Real.pi / 2) = 0 := Wt_zero_of_sin_eq_zero hα hsin
      have hlhs : (Work.Spaces.DthIter 2 f z (Real.pi / 2)
          * Work.Spaces.Wt α z (Real.pi / 2)) ^ 2 = 0 := by simp [hW]
      have h4 : sig4 (Work.Spaces.gam α) (Real.pi / 2) = 0 := by
        rw [sig4, hsin]
        exact Real.zero_rpow (x := (4 : ℝ) - Work.Spaces.gam α) (by linarith)
      have h2'' : sig2 (Work.Spaces.gam α) (Real.pi / 2) = 0 := by
        rw [sig2, hsin]
        exact Real.zero_rpow (x := (2 : ℝ) - Work.Spaces.gam α) (by linarith)
      rw [hlhs, h4, h2'']
      norm_num
  · subst h
    have hsin : Real.sin (2 * 0) = 0 := by rw [mul_zero, Real.sin_zero]
    have hW : Work.Spaces.Wt α z 0 = 0 := Wt_zero_of_sin_eq_zero hα hsin
    have hlhs : (Work.Spaces.DthIter 2 f z 0 * Work.Spaces.Wt α z 0) ^ 2 = 0 := by simp [hW]
    have h4 : sig4 (Work.Spaces.gam α) 0 = 0 := by
      rw [sig4, hsin]
      exact Real.zero_rpow (x := (4 : ℝ) - Work.Spaces.gam α) (by linarith)
    have h2'' : sig2 (Work.Spaces.gam α) 0 = 0 := by
      rw [sig2, hsin]
      exact Real.zero_rpow (x := (2 : ℝ) - Work.Spaces.gam α) (by linarith)
    rw [hlhs, h4, h2'']
    simp

end Work.FTS.EllipticEst.Mine
