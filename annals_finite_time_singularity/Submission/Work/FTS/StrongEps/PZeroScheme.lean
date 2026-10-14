import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.SlotJets.slotPthSliceLe
-- ===== merged: Submission.Work.FTS.LocData6.RegQ6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The squared angular bound `(D_θ^i Γ)² ≤ 10¹⁰·Γ²` on `Iθ` for `i ≤ 6`, obtained by squaring
the order-`6` jet bound `LocData6.DthIter_Gam_abs_le6`. -/
theorem hGam6 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {i : ℕ} (hi : i ≤ 6) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
      ≤ (10 : ℝ) ^ 10 * (Work.Spaces.Gam α θ) ^ 2 := by
  have h := DthIter_Gam_abs_le6 i hi α hα hα1 hθ
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs, mul_pow] at h2
  have h10 : ((100000 : ℝ)) ^ 2 = (10 : ℝ) ^ 10 := by norm_num
  calc (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
      ≤ (100000 : ℝ) ^ 2 * (Work.Spaces.Gam α θ) ^ 2 := h2
    _ = (10 : ℝ) ^ 10 * (Work.Spaces.Gam α θ) ^ 2 := by rw [h10]

/-- **The localised datum lies in `RegQ α 6`** — unconditionally, for `0 < α ≤ 1`, `L ≥ 1` and
every `β`.  This is the order-`6` form of the design's `N9-ext` obligation: `SmoothQuad`,
`HkMem α 6` and the vanishing boundary traces `BdryTraces α 6`. -/
theorem regQ_locG6_uncond (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) :
    Work.FTS.Nonlin.RegQ α 6 (locG6 α L β) := by
  obtain ⟨A, hA, hAz⟩ := zfarR_jet_le6_clean
  obtain ⟨CF, hCF, hF⟩ := FM_Fstar_jet_le6
  obtain ⟨Kb, hKb0, hKb⟩ := hLoc_majorant6 α hα hα1
    (fun i hi θ hθ => hGam6 α hα hα1 hi hθ)
  refine regQ_locG6_of_jets α L β hα hα1 hL (le_of_lt hA) (by norm_num)
    (fun j hj z hz θ => hAz L hL j hj z hz θ)
    (fun i hi θ hθ => hGam6 α hα hα1 hi hθ)
    (fun i hi θ hθ => DthIter_Gam_abs_le6 i hi α hα hα1 hθ)
    hKb0 hKb (le_of_lt hCF) hF

end Work.FTS.LocData6
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.PZeroScheme =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS)

set_option autoImplicit false

/-! ## The projected family -/

/-- **The `P₀`-projected mollified family**: `JfamP ρ ε g = P₀ ∘ J_ε (slice g ·)`.

This is the family whose slices the elliptic solution operator `E`, the level-four/level-six
contexts (`L6Ctx`) and the modulation package (`MuLamOK`) are evaluated at.  Thanks to the
projection its slices lie in `ClassC` at every fake time (`Pz_l12` + `classC_Pz`), which is what
the un-projected `Jfam` cannot provide. -/
noncomputable def JfamP (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (g : Fam) : Fam :=
  fun z θ τ => Pz (Jeps ρ ε (slice g τ)) z θ


/-- The projected family has the projected profile at every fake time. -/
theorem slice_JfamP (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (g : Fam) (τ : ℝ) :
    slice (JfamP ρ ε g) τ = Pz (Jeps ρ ε (slice g τ)) := rfl


/-! ## The projected scheme -/

/-- The pre-mollified right-hand side of the projected scheme at `τ`: the paper's right-hand side
evaluated at the projected family.  It is the analogue of `Gdot.epsW` with `Jfam` replaced by
`JfamP`. -/
noncomputable def epsWP (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam)
    (τ : ℝ) : Fn :=
  fun z θ => dynLin α (JfamP ρ ε g) τ z θ
    + dynRHS α (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ z θ

/-- The right-hand side of the projected scheme: `P₀` applied to the mollified pre-mollified
right-hand side. -/
noncomputable def epsRHSP (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam)
    (τ : ℝ) : Fn :=
  Pz (Jeps ρ ε (epsWP α ρ ε Φs E g τ))

/-- The scheme's right-hand side is the projection of the mollified pre-mollified right-hand
side (definitional). -/
theorem epsRHSP_eq_Pz_Jeps_epsWP (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn)
    (g : Fam) (τ : ℝ) :
    epsRHSP α ρ ε Φs E g τ = Pz (Jeps ρ ε (epsWP α ρ ε Φs E g τ)) := rfl

/-- **The `P₀`-corrected `ε`-scheme of the design's §(B)**:
`∂_τ g = P₀ J_ε [𝓛 + 𝓡] (P₀ J_ε g)`.

The two occurrences of the projection are both load-bearing:
* the *inner* one (inside `JfamP`) keeps the profiles at which `E`, `L6Ctx` and `MuLamOK` are
  evaluated inside `ClassC`;
* the *outer* one makes `L₁₂(∂_τ g)(0) = 0`, hence `L₁₂(slice g τ)(0) = L₁₂ g₀ 0` for all `τ`
  (`Pz_l12`), so that the limit family has `P₀(slice g τ) = slice g τ` — which is what turns the
  limiting equation into the *unprojected* `IsDynEqOn` of the conclusion. -/
def IsEpsSolP (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε T : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (g : Fam) : Prop :=
  (∀ z θ, g z θ 0 = g₀ z θ) ∧
  ∀ z θ τ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → τ ∈ Set.Icc 0 T →
    HasDerivWithinAt (fun s => g z θ s) (epsRHSP α ρ ε Φs E g τ z θ) (Set.Icc 0 T) τ

/-- The scheme's initial condition. -/
theorem IsEpsSolP.init {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε T : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g : Fam} (h : IsEpsSolP α ρ ε T Φs E g₀ g) : ∀ z θ, g z θ 0 = g₀ z θ := h.1

/-- The scheme's equation, pointwise on the open quadrant. -/
theorem IsEpsSolP.eq {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε T : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g : Fam} (h : IsEpsSolP α ρ ε T Φs E g₀ g) {z θ τ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hτ : τ ∈ Set.Icc 0 T) :
    HasDerivWithinAt (fun s => g z θ s) (epsRHSP α ρ ε Φs E g τ z θ) (Set.Icc 0 T) τ :=
  h.2 z θ τ hz hθ hτ

end Work.FTS.StrongEps
end
end
