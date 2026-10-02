/-
# Joint continuity of the Green function: the `greenFun` interface

`Work.NAKANE.GreenJoint.continuous_jointGreen` (already proved) is the joint continuity of the
escape chapter's Green function `Work.Escape.green (Tantibar c) 2 z`.  This file

* bridges it to the parameter-ray chapter's `Work.ParamRays.greenFun`
  (`greenFun_eq_green`, from `Work.Bottcher.Contraction.green_eq_greenFun`),
* re-states the joint continuity as `continuous_greenFun` and `continuous_paramPotential`,
* exports the **PARIMPL (I2)** consequence `exists_greenFun_pos_near` /
  `exists_escaping_near`: positivity of the potential on a compact set at `c₀` persists on a whole
  neighbourhood of that set for nearby parameters (this is the item
  `NOTES_LEAD_mandelbar_residuals.md` §1.4 (I2) asks PARIMPL to use).
-/
import Submission.Work.NAKANE.Defs
import Submission.Work.NAKANE.GreenJoint.continuous_jointGreen
import Submission.Work.NAKANE.GreenJoint.exists_green_pos_near

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false

noncomputable section

namespace Work.NAKANE

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The bridge between the two Green functions -/

/-- The parameter-ray chapter's Green function is the escape chapter's Green function. -/
theorem greenFun_eq_green (c z : ℂ) :
    Work.ParamRays.greenFun c z = Work.Escape.green (Tantibar c) 2 z :=
  (Work.Bottcher.Contraction.green_eq_greenFun c z).symm

/-- The Green function is **jointly continuous** in `(c, z)`, in the `greenFun` formulation. -/
theorem continuous_greenFun :
    Continuous (fun p : ℂ × ℂ => Work.ParamRays.greenFun p.1 p.2) :=
  Work.NAKANE.GreenJoint.continuous_jointGreen.congr fun p => (greenFun_eq_green p.1 p.2).symm

/-- The parameter potential `c ↦ G_c(0)` is continuous (unconditional). -/
theorem continuous_paramPotential : Continuous Work.ParamRays.paramPotential := by
  have h : Continuous fun c : ℂ => Work.ParamRays.greenFun c 0 := by
    apply Continuous.comp (g := fun p : ℂ × ℂ => Work.ParamRays.greenFun p.1 p.2)
      (f := fun c : ℂ => (c, (0 : ℂ)))
    · exact continuous_greenFun
    · exact continuous_id.prodMk continuous_const
  exact h

/-! ## PARIMPL (I2): positivity of the potential survives on a neighbourhood -/

/-- **PARIMPL (I2).**  If the potential is bounded below by `s > 0` on a compact set `K` at the
parameter `c₀`, then for all parameters `c` close to `c₀` the potential is positive on a whole
neighbourhood of `K`.

With `K = Ψ (closedBall (x* - j₀) r₀)` compact and `G_{c₀} ≥ s₀ > 0` on it
(`NOTES_LEAD_mandelbar_residuals.md` §1.4), this is exactly the estimate (I2) which makes the
robust leak disc escape for all nearby parameters. -/
theorem exists_greenFun_pos_near {c₀ : ℂ} {K : Set ℂ} (hK : IsCompact K) {s : ℝ} (hs : 0 < s)
    (hKs : ∀ z ∈ K, s ≤ Work.ParamRays.greenFun c₀ z) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c : ℂ, ‖c - c₀‖ < ρ → ∀ z : ℂ,
      (∃ k ∈ K, ‖z - k‖ < ρ) → 0 < Work.ParamRays.greenFun c z := by
  obtain ⟨ρ, hρ, h⟩ :=
    Work.NAKANE.GreenJoint.exists_green_pos_near hK hs fun z hz => by
      simpa [jointGreen, greenFun_eq_green] using hKs z hz
  refine ⟨ρ, hρ, fun c hc z hz => ?_⟩
  simpa [jointGreen, greenFun_eq_green] using h c hc z hz

/-- **PARIMPL (I2), in the vocabulary of escaping.**  Points near a compact set of positive
potential at `c₀` escape for all nearby parameters, i.e. they lie outside the filled Julia set
`K_c`. -/
theorem exists_escaping_near {c₀ : ℂ} {K : Set ℂ} (hK : IsCompact K) {s : ℝ} (hs : 0 < s)
    (hKs : ∀ z ∈ K, s ≤ Work.ParamRays.greenFun c₀ z) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c : ℂ, ‖c - c₀‖ < ρ → ∀ z : ℂ,
      (∃ k ∈ K, ‖z - k‖ < ρ) → Work.ParamRays.Escaping c z := by
  obtain ⟨ρ, hρ, h⟩ := exists_greenFun_pos_near hK hs hKs
  exact ⟨ρ, hρ, fun c hc z hz => (Work.ParamRays.greenFun_pos_iff_escaping c z).mp (h c hc z hz)⟩

end Work.NAKANE
