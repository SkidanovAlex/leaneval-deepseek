/-
# `Work.FTS.H2.ModalSol.ModeIdent.Defs`

The angular-moment data of the per-mode weak identity

  `Work.FTS.H2.ModalSol.ModeIdent.mode_weak_identity`.

For the angular Dirichlet eigenfunction `eFam m` of `Lzero` (eigenvalue `lam m`, self-adjoint
weight `cos θ dθ`, `Gegenbauer/eFam_Lzero.lean`) and a function `φ : ℝ → ℝ → ℝ`, put

* `pw m θ = eFam m θ · cos θ` — the angular weight of the pairing;
* `PhiM m φ k z = ∫_θ ∂_z^k φ (z,θ) · e_m(θ) cos θ dθ` over `Iθ = [0,π/2]`.

The lemma `mode_weak_identity` (a sibling module) reduces, on the box `[za,zb] × [tc,td]` that
contains the support of `φ`, to

  `∫_θ (bslOp α φ)(z,θ) · e_m(θ) cos θ dθ
      = -(α²z²)·PhiM m φ 2 z - α(5+α)z·PhiM m φ 1 z + lam m · PhiM m φ 0 z`

whose left-hand side is the self-adjoint reduction of `bslOp` (radial part unchanged, angular
part `Lzero` moved onto the eigenfunction), followed by the radial weak ODE of `radGreen`.

This file only collects the vocabulary and the elementary vanishing lemmas that every piece of
that argument needs: a function which is eventually zero in one variable has all its iterate
derivatives in that variable equal to zero (`pzIter_eq_zero_of_eventually`,
`pthIter_eq_zero_of_eventually`).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSol.ModeIdent

set_option autoImplicit false

/-- The angular weight `e_m(θ)·cos θ` of the mode-`m` pairing. -/
def pw (m : ℕ) (θ : ℝ) : ℝ := Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ

/-- The `k`-th radial-derivative angular moment of `φ`:
`PhiM m φ k z = ∫_θ ∂_z^k φ (z,θ) · e_m(θ) cos θ dθ` over `Iθ = [0,π/2]`. -/
def PhiM (m : ℕ) (φ : ℝ → ℝ → ℝ) (k : ℕ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter k φ z θ * pw m θ

/-- The angular eigenfunction is `C³` (indeed `C^∞`). -/
theorem contDiff_eFam (m : ℕ) : ContDiff ℝ 3 (Work.FTS.PhiStar.Gegenbauer.eFam m) :=
  Real.contDiff_cos.mul
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).comp Real.contDiff_sin)

/-- The angular eigenfunction is continuous. -/
theorem continuous_eFam (m : ℕ) : Continuous (Work.FTS.PhiStar.Gegenbauer.eFam m) :=
  (contDiff_eFam m).continuous

/-- The angular weight `pw m` is continuous. -/
theorem continuous_pw (m : ℕ) : Continuous (pw m) :=
  (continuous_eFam m).mul Real.continuous_cos

/-! ## Vanishing of the iterated derivatives off the support -/

/-- If `F` vanishes on an *open* set `U` of first coordinates (uniformly in the second), then
the iterated `z`-derivatives vanish at every `z ∈ U`. -/
theorem pzIter_eq_zero_of_isOpen_zero {F : ℝ → ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (h0 : ∀ z ∈ U, ∀ θ, F z θ = 0) :
    ∀ k z, z ∈ U → ∀ θ, Work.Spaces.pzIter k F z θ = 0 := by
  intro k
  induction k with
  | zero => intro z hz θ; exact h0 z hz θ
  | succ k ih =>
    intro z hz θ
    rw [Work.Spaces.pzIter_succ]
    show deriv (fun z' => Work.Spaces.pzIter k F z' θ) z = 0
    have hconst : (fun z' => Work.Spaces.pzIter k F z' θ) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [hU.mem_nhds hz] with z' hz'
      exact ih z' hz' θ
    rw [hconst.deriv_eq, deriv_const]

/-- If `F` is eventually zero in the first variable, then its iterated `z`-derivatives vanish. -/
theorem pzIter_eq_zero_of_eventually {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, ∀ θ', F z' θ' = 0) (k : ℕ) :
    Work.Spaces.pzIter k F z θ = 0 := by
  obtain ⟨U, hUN, hUopen, hzU⟩ := mem_nhds_iff.mp h
  exact pzIter_eq_zero_of_isOpen_zero hUopen (fun z' hz' θ' => hUN hz' θ') k z hzU θ

/-- If the `θ`-slice `F z ·` vanishes on an *open* set `V`, then the iterated `θ`-derivatives
vanish there. -/
theorem pthIter_eq_zero_of_isOpen_zero {F : ℝ → ℝ → ℝ} {z : ℝ} {V : Set ℝ} (hV : IsOpen V)
    (h0 : ∀ θ ∈ V, F z θ = 0) :
    ∀ k, ∀ θ ∈ V, Work.Spaces.pthIter k F z θ = 0 := by
  intro k
  induction k with
  | zero => intro θ hθ; exact h0 θ hθ
  | succ k ih =>
    intro θ hθ
    rw [Work.Spaces.pthIter_succ]
    show deriv (fun θ' => Work.Spaces.pthIter k F z θ') θ = 0
    have hconst : (fun θ' => Work.Spaces.pthIter k F z θ') =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
      filter_upwards [hV.mem_nhds hθ] with θ' hθ'
      exact ih θ' hθ'
    rw [hconst.deriv_eq, deriv_const]

/-- If the `θ`-slice `F z ·` is eventually zero at `θ`, then its iterated `θ`-derivatives
vanish at `θ`. -/
theorem pthIter_eq_zero_of_eventually {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ∀ᶠ θ' in 𝓝 θ, F z θ' = 0) (k : ℕ) :
    Work.Spaces.pthIter k F z θ = 0 := by
  obtain ⟨V, hVN, hVopen, hθV⟩ := mem_nhds_iff.mp h
  exact pthIter_eq_zero_of_isOpen_zero hVopen (fun θ' hθ' => hVN hθ') k θ hθV

end Work.FTS.H2.ModalSol.ModeIdent
