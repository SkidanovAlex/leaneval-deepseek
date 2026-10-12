import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Submission.Work.UBBInputs9.B.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs9.B.exists_bound_fderiv_windowed_state`

The windowed state `y ↦ χ_ℓ(y 0)·Φ(y)` of a state `Φ ∈ C^∞` of compact support is `C^∞` with
compact support (`χ_ℓ` is the smooth compactly supported bump `Submission.BoseGases.chiScale ℓ`),
so its Fréchet derivative is continuous with compact support, hence bounded: there is `M ≥ 0`
with `|∂_k(χ_ℓ·Φ)(x)| ≤ M` for every `x` and every kinetic direction `k`.
-/

noncomputable section

open scoped ContDiff ENNReal Topology
open Submission.BoseGases

namespace Work.UBBInputs9.B

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

theorem exists_bound_fderiv_windowed_state (ℓ : ℝ) (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X 1 → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hcs : HasCompactSupport Φ) (k : Fin 3) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Submission.BoseGases.X 1,
      |fderiv ℝ (fun y : Submission.BoseGases.X 1 =>
        Submission.BoseGases.chiScale ℓ (y 0) * Φ y) x
          (Submission.BoseGases.kcDir 1 0 k)| ≤ M := by
  have hℓ' : ℓ ≠ 0 := ne_of_gt hℓ
  set G : Submission.BoseGases.X 1 → ℝ :=
    fun y => Submission.BoseGases.chiScale ℓ (y 0) * Φ y with hGdef
  -- `G` is smooth ...
  have hGcd : ContDiff ℝ (⊤ : ENat) G := by
    rw [hGdef]
    exact ((Submission.BoseGases.chiScale_contDiff hℓ').comp
      (ContinuousLinearMap.contDiff projX1)).mul hΦ
  -- ... and compactly supported, because `χ_ℓ` is.
  have hlift : HasCompactSupport (fun y : Submission.BoseGases.X 1 =>
      Submission.BoseGases.chiScale ℓ (y 0)) := by
    have h := (Submission.BoseGases.chiScale_hasCompactSupport hℓ').comp_homeomorph
      (Homeomorph.piUnique (fun _ : Fin 1 => ℝ³))
    simpa [Function.comp_def] using h
  have hGcpt : HasCompactSupport G := by
    rw [hGdef]
    exact hlift.mul_right (f' := Φ)
  -- hence the derivative in the direction `k` is continuous with compact support.
  have key : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Submission.BoseGases.X 1,
      |fderiv ℝ G x (Submission.BoseGases.kcDir 1 0 k)| ≤ M := by
    have hcont : Continuous (fun x : Submission.BoseGases.X 1 =>
        fderiv ℝ G x (Submission.BoseGases.kcDir 1 0 k)) :=
      (hGcd.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcpt : HasCompactSupport (fun x : Submission.BoseGases.X 1 =>
        fderiv ℝ G x (Submission.BoseGases.kcDir 1 0 k)) :=
      hGcpt.fderiv_apply ℝ (Submission.BoseGases.kcDir 1 0 k)
    have hK : IsCompact (Set.range (fun x : Submission.BoseGases.X 1 =>
        fderiv ℝ G x (Submission.BoseGases.kcDir 1 0 k))) :=
      hcpt.isCompact_range hcont
    obtain ⟨a, ha⟩ := hK.bddAbove
    obtain ⟨b, hb⟩ := hK.bddBelow
    refine ⟨max |a| |b|, le_trans (abs_nonneg a) (le_max_left _ _), fun x => ?_⟩
    have hx : fderiv ℝ G x (Submission.BoseGases.kcDir 1 0 k) ∈
        Set.range (fun x : Submission.BoseGases.X 1 =>
          fderiv ℝ G x (Submission.BoseGases.kcDir 1 0 k)) := Set.mem_range_self x
    have hu : fderiv ℝ G x (Submission.BoseGases.kcDir 1 0 k) ≤ a := ha hx
    have hl : b ≤ fderiv ℝ G x (Submission.BoseGases.kcDir 1 0 k) := hb hx
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h1 : -(max |a| |b|) ≤ -|b| := neg_le_neg (le_max_right |a| |b|)
      have h2 : -|b| ≤ b := neg_abs_le b
      linarith
    · have h1 : a ≤ |a| := le_abs_self a
      have h2 : |a| ≤ max |a| |b| := le_max_left _ _
      linarith
  simpa only [hGdef] using key

end Work.UBBInputs9.B
