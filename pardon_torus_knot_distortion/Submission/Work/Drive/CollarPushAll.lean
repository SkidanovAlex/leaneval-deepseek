import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Bicollar.StdTorusTube
import Submission.Work.CoreTopology.TorusDichotomyDefs
import Submission.Work.Drive.WPushDefs
import Submission.Work.Drive.CollarPushDefs
import Submission.Work.Drive.CollarPushStd

namespace Work.Drive

open LeanEval.KnotTheory.PardonDistortion

/-!
# The collar push of a torus `ψ (F_std)`

The push `pushStd` of `Work.Drive.CollarPushDefs` is the explicit push of the *standard* torus:
on the region where the meridian radius `s = ‖meridVec x‖` lies in `(1/4, 3/2)` it moves `x` so
that its meridian vector is scaled by `(s + δ · stdCut s)/s`, keeping the longitude.  Its level
properties are the content of the companion files.

Here we transport it to the torus `F = ψ '' Σ` of the challenge by

* `levP ψ x = ‖meridVec (ψ.symm x)‖`, whose level set `{1}` is exactly `F`, and
* `pushP ψ x δ = ψ (pushStd (ψ.symm x) δ)`,

and assemble the target statement `CollarPushAll`.
-/

open Work.CoreTopology

/-- **The standard-torus facts behind `CollarPushAll`.**  Given the continuity of the standard
push and its three nontrivial level properties, the transport along a homeomorphism `ψ` of `ℝ³`
produces the collar push of `F = ψ '' Σ`. -/
theorem collarPushAll_of_std
    (hcont : Continuous (Function.uncurry pushStd))
    (hcollar : ∀ (x : R3) (δ : ℝ), ‖meridVec x‖ ∈ Set.Icc (1 / 2) (5 / 4) → |δ| ≤ 1 / 4 →
      ‖meridVec (pushStd x δ)‖ = ‖meridVec x‖ + δ)
    (hout : ∀ (x : R3) (δ : ℝ), 0 ≤ δ → δ ≤ 1 / 4 → 5 / 4 ≤ ‖meridVec x‖ →
      5 / 4 ≤ ‖meridVec (pushStd x δ)‖)
    (hin : ∀ (x : R3) (δ : ℝ), -1 / 4 ≤ δ → δ ≤ 0 → ‖meridVec x‖ ≤ 1 →
      ‖meridVec (pushStd x δ)‖ ≤ ‖meridVec x‖) :
    ∀ ψ : R3 ≃ₜ R3, ∃ (pushP : R3 → ℝ → R3) (levP : R3 → ℝ),
      (∀ x : R3, levP x = 1 ↔ x ∈ (ParamTorus.mapHomeomorph ψ).carrier) ∧
      Continuous levP ∧
      Continuous (Function.uncurry pushP) ∧
      (∀ x : R3, pushP x 0 = x) ∧
      (∀ x : R3, ∀ δ : ℝ, levP x ∈ Set.Icc (1 / 2) (5 / 4) → |δ| ≤ 1 / 4 →
        levP (pushP x δ) = levP x + δ) ∧
      (∀ x : R3, ∀ δ : ℝ, 3 / 2 ≤ levP x → pushP x δ = x) ∧
      (∀ x : R3, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 → 5 / 4 ≤ levP x →
        5 / 4 ≤ levP (pushP x δ)) ∧
      (∀ x : R3, ∀ δ : ℝ, -1 / 4 ≤ δ → δ ≤ 0 → levP x ≤ 1 →
        levP (pushP x δ) ≤ levP x) := by
  intro ψ
  refine ⟨pushP ψ, levP ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact levP_eq_one_iff ψ
  · exact continuous_levP ψ
  · have h2 : Continuous (fun p : R3 × ℝ => pushStd (ψ.symm p.1) p.2) :=
      hcont.comp ((ψ.symm.continuous.comp continuous_fst).prodMk continuous_snd)
    exact ψ.continuous.comp h2
  · exact pushP_zero ψ
  · intro x δ hx hδ
    have hx' : ‖meridVec (ψ.symm x)‖ ∈ Set.Icc (1 / 2) (5 / 4) := hx
    rw [levP_pushP, levP]
    exact hcollar (ψ.symm x) δ hx' hδ
  · intro x δ hx
    have hx' : 3 / 2 ≤ ‖meridVec (ψ.symm x)‖ := hx
    rw [pushP, pushStd_eq_self_of_ge hx']
    exact ψ.apply_symm_apply x
  · intro x δ h0 h1 h5
    have h5' : 5 / 4 ≤ ‖meridVec (ψ.symm x)‖ := h5
    rw [levP_pushP]
    exact hout (ψ.symm x) δ h0 h1 h5'
  · intro x δ h0 h1 hle
    have hle' : ‖meridVec (ψ.symm x)‖ ≤ 1 := hle
    rw [levP_pushP, levP]
    exact hin (ψ.symm x) δ h0 h1 hle'

/-- For every torus `F = ψ(F_std)` of the challenge there is an explicit *collar push*: a level
function `levP`, whose level set `{1}` is exactly `F`, and a continuous push `pushP` moving a
point of `ℝ³` transversely across `F`: it fixes points of level `≥ 3/2`, and on the collar
`1/2 ≤ levP ≤ 5/4` it changes the level by exactly the prescribed amount, with all pushes of
size `≤ 1/4`. -/
theorem CollarPushAll :
    ∀ ψ : R3 ≃ₜ R3, ∃ (pushP : R3 → ℝ → R3) (levP : R3 → ℝ),
      (∀ x : R3, levP x = 1 ↔ x ∈ (Work.CoreTopology.ParamTorus.mapHomeomorph ψ).carrier) ∧
      Continuous levP ∧
      Continuous (Function.uncurry pushP) ∧
      (∀ x : R3, pushP x 0 = x) ∧
      (∀ x : R3, ∀ δ : ℝ, levP x ∈ Set.Icc (1/2) (5/4) → |δ| ≤ 1/4 →
        levP (pushP x δ) = levP x + δ) ∧
      (∀ x : R3, ∀ δ : ℝ, 3/2 ≤ levP x → pushP x δ = x) ∧
      (∀ x : R3, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1/4 → 5/4 ≤ levP x → 5/4 ≤ levP (pushP x δ)) ∧
      (∀ x : R3, ∀ δ : ℝ, -1/4 ≤ δ → δ ≤ 0 → levP x ≤ 1 → levP (pushP x δ) ≤ levP x) :=
  collarPushAll_of_std continuous_uncurry_pushStd
    (fun x δ hx hδ => pushStd_collar hx hδ)
    (fun x δ h0 h1 h5 => pushStd_outer h0 h1 h5)
    (fun x δ h0 h1 hle => pushStd_inner h0 h1 hle)

end Work.Drive
