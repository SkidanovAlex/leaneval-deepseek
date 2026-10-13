/-
# `Work.FTS.PhiStar.Decomp` — from `Psi0_exists` and `PhiStar_exists` to the decomposition

Two bridges:

* `Psi0AngModel` — `Psi0_exists` (P1, proved) gives an angular model `ψ` together with a bound
  `|ψ θ| ≤ C` on the angular interval: the `j = 0` clause of `Psi0_exists` is
  `|ψ θ| ≤ C sin 2θ` on the open interval, and the two Dirichlet values give the endpoints.
* `PhiStar_split_of` — given a solution `Φ_*` of the profile equation (`IsBslSol α F_* Φ_*`,
  `SmoothOpen Φ_*`), an angular model `ψ` and the smoothness of the model part, the difference
  `R := Φ_* − Model α (GzProfile α) ψ` inherits smoothness, the Dirichlet data and the decay,
  solves `bslOp α R = RemSource α ψ`, and `Φ_* = Model α (GzProfile α) ψ + R`.

The remaining inputs (`PhiStar_exists`, `contDiffOn_model`, `GzProfile_tendsto`) are separate
nodes; `PhiStar_split` below assembles them.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.PhiStar.Model
import Submission.Work.FTS.PhiStar.Assemble
import Submission.Work.FTS.PhiStar.Psi0_exists
import Submission.Work.FTS.PhiStar.contDiffOn_model

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The angular model extracted from `Psi0_exists` -/

/-- `Psi0_exists` yields an `AngModel` together with a bound on the angular interval. -/
theorem Psi0AngModel {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) :
    ∃ (C : ℝ) (ψ : ℝ → ℝ), 0 < C ∧ AngModel α ψ ∧ ∀ θ ∈ Work.Spaces.Iθ, |ψ θ| ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := Psi0_exists
  obtain ⟨ψ, hsm, hcont, h0, h1, heq, hmom, -, -, hDth⟩ := hC α hα hα4
  refine ⟨C, ψ, hCpos, ⟨hsm, hcont, h0, h1, heq, hmom⟩, ?_⟩
  intro θ hθ
  rcases eq_or_lt_of_le hθ.1 with h0' | h0'
  · rw [← h0', h0, abs_zero]; exact hCpos.le
  rcases eq_or_lt_of_le hθ.2 with h1' | h1'
  · rw [h1', h1, abs_zero]; exact hCpos.le
  have hbound := hDth 0 (by norm_num) θ ⟨h0', h1'⟩
  have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  calc |ψ θ| = |Work.Spaces.DthIter 0 (fun _ θ' => ψ θ') 0 θ| := rfl
    _ ≤ C * Real.sin (2 * θ) := hbound
    _ ≤ C * 1 := by
        exact mul_le_mul_of_nonneg_left hsin1 hCpos.le
    _ = C := mul_one C

/-! ## Smoothness of the model part -/

/-- The model part `Model α (GzProfile α) ψ` is `C^∞` on the open quadrant. -/
theorem smoothOpen_model {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {ψ : ℝ → ℝ}
    (hψ : AngModel α ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Model α (GzProfile α) ψ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  exact contDiffOn_model n (GzProfile_smooth hα hα4 n)
    (contDiffOn_iff_forall_nat_le.mp hψ.smooth n le_top)

/-! ## The decomposition of a solution -/

/-- **The decomposition of the profile's stream function.**  From a solution `Φ_*` of the
profile equation and an angular model `ψ`, the difference `R := Φ_* − Model α (GzProfile α) ψ`
solves `bslOp α R = RemSource α ψ` (the `O(α²)` separable source), inherits the Dirichlet data
and the decay, and `Φ_* = Model α (GzProfile α) ψ + R`. -/
theorem PhiStar_split_of {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {ψ : ℝ → ℝ} {C : ℝ}
    (hψ : AngModel α ψ) (hψbd : ∀ θ ∈ Work.Spaces.Iθ, |ψ θ| ≤ C)
    (hGzdec : Tendsto (GzProfile α) atTop (𝓝 0))
    {Φs : Fn} (hsol : Work.Elliptic.IsBslSol α (Work.Construction.Fstar α) Φs)
    (hsmo : Work.FTS.EllipticEst.SmoothOpen Φs)
    (hmods : Work.FTS.EllipticEst.SmoothOpen (Model α (GzProfile α) ψ)) :
    ∃ R : Fn,
      Work.FTS.EllipticEst.SmoothOpen R ∧
      (∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
        Work.Elliptic.bslOp α R z θ = RemSource α ψ z θ) ∧
      (∀ z, R z 0 = 0) ∧ (∀ z, R z (π / 2) = 0) ∧
      (∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => R z θ) atTop (𝓝 0)) ∧
      Φs = (fun z θ => Model α (GzProfile α) ψ z θ + R z θ) ∧
      Work.Elliptic.IsBslSol α (Work.Construction.Fstar α)
        (fun z θ => Model α (GzProfile α) ψ z θ + R z θ) ∧
      Work.FTS.EllipticEst.SmoothOpen (fun z θ => Model α (GzProfile α) ψ z θ + R z θ) := by
  set R : Fn := fun z θ => Φs z θ - Model α (GzProfile α) ψ z θ with hR
  have hsmoothR : Work.FTS.EllipticEst.SmoothOpen R := by
    rw [hR]
    show ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun z θ => Φs z θ - Model α (GzProfile α) ψ z θ))
      Work.FTS.EllipticEst.Q0
    exact hsmo.sub hmods
  have hdecomp : Φs = fun z θ => Model α (GzProfile α) ψ z θ + R z θ := by
    funext z θ
    simp only [R]
    ring
  refine ⟨R, hsmoothR, ?_, ?_, ?_, ?_, hdecomp, ?_, ?_⟩
  · -- the remainder equation, from the model identity and `bslOp_add`
    intro z hz θ hθ hθ2
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ, Real.pi_pos], hθ2⟩)
    have hC2M := contDiffAt_of_smoothOpen hmods hz hθ hθ2 2
    have hC2R := contDiffAt_of_smoothOpen hsmoothR hz hθ hθ2 2
    have hadd := Work.Elliptic.bslOp_add α (Model α (GzProfile α) ψ) R z θ hcos hC2M hC2R
    rw [← hdecomp] at hadd
    have hR_eq : Work.Elliptic.bslOp α R z θ
        = Work.Elliptic.bslOp α Φs z θ
          - Work.Elliptic.bslOp α (Model α (GzProfile α) ψ) z θ := by linarith [hadd]
    rw [hR_eq, hsol.1 z hz θ hθ hθ2, bslOp_model_eq' hα hα4 hψ z θ hz hθ hθ2]
    ring
  · intro z
    rw [show R z 0 = Φs z 0 - Model α (GzProfile α) ψ z 0 from rfl, hsol.2.1,
      Model_zero hψ.bdry0, sub_zero]
  · intro z
    rw [show R z (π / 2) = Φs z (π / 2) - Model α (GzProfile α) ψ z (π / 2) from rfl,
      hsol.2.2.1, Model_pi_half hψ.bdry1, sub_zero]
  · intro θ hθ
    have h1 := hsol.2.2.2 θ hθ
    have h2 := Model_tendsto (α := α) (Gz := GzProfile α) (ψ := ψ) hGzdec hψbd θ
    have h := h1.sub h2
    rw [sub_zero] at h
    exact h
  · -- `IsBslSol` of the sum
    rw [← hdecomp]; exact hsol
  · rw [← hdecomp]; exact hsmo

/-! ## End-to-end: the profile's stream function splits through the `O(α²)` equation -/

/-- **The `Φ_*` decomposition, end to end.**  Combining `Psi0_exists` (through `Psi0AngModel`)
with an existence witness for `Φ_*` and the decay of the radial profile, there are an angular
model `ψ` and a remainder `R` such that

`Φ_* = GzProfile(z)·sin 2θ + α φ(z) ψ(θ) + R(z,θ)`,   `bslOp α R = α²(𝒜φ)(z) ψ(θ)`,

with `R` smooth on the open quadrant, Dirichlet at `θ = 0, π/2`, decaying at `z = ∞`, and `Φ_*`
a solution of the profile equation.  This is the interface consumed by the sup-estimate node for
`StarPkgo`. -/
theorem PhiStar_split {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hGzdec : Tendsto (GzProfile α) atTop (𝓝 0))
    (hex : ∃ Φs : Fn, Work.Elliptic.IsBslSol α (Work.Construction.Fstar α) Φs ∧
      Work.FTS.EllipticEst.SmoothOpen Φs) :
    ∃ (C : ℝ) (ψ : ℝ → ℝ) (R : Fn),
      0 < C ∧ AngModel α ψ ∧ (∀ θ ∈ Work.Spaces.Iθ, |ψ θ| ≤ C) ∧
      Work.FTS.EllipticEst.SmoothOpen R ∧
      (∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
        Work.Elliptic.bslOp α R z θ = RemSource α ψ z θ) ∧
      (∀ z, R z 0 = 0) ∧ (∀ z, R z (π / 2) = 0) ∧
      (∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => R z θ) atTop (𝓝 0)) ∧
      Work.Elliptic.IsBslSol α (Work.Construction.Fstar α)
        (fun z θ => Model α (GzProfile α) ψ z θ + R z θ) ∧
      Work.FTS.EllipticEst.SmoothOpen (fun z θ => Model α (GzProfile α) ψ z θ + R z θ) := by
  obtain ⟨C, ψ, hC, hang, hbd⟩ := Psi0AngModel hα hα4
  obtain ⟨Φs, hsol, hsmo⟩ := hex
  obtain ⟨R, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8⟩ :=
    PhiStar_split_of hα hα4 hang hbd hGzdec hsol hsmo (smoothOpen_model hα hα4 hang)
  exact ⟨C, ψ, R, hC, hang, hbd, hR1, hR2, hR3, hR4, hR5, hR7, hR8⟩

end Work.FTS.PhiStar
