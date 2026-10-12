import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.SmallBoxA0.Assembly
import Submission.Work.SmallBoxBridge.Bridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators ENNReal
open Submission BoseGases
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Shared definitions for `Work.SmallBoxA0.kinPWord_exceeds_kinWord`

The witness family is the *scaled* bump `z ↦ chiBase (c • z)` on `ℝ³`, viewed as a
one-particle state on `X 1` by `x ↦ chiBase (c • (x 0))`, normalised in
`L²(abox 1 s)`.

The whole witness rests on three elementary facts:

* `chiScale s y = chiSup` for `‖y‖ ≤ s/4` (because `chiScale s = chiSup • chiBase (·/s)`
  and `chiBase = 1` on `ball 0 (1/4)`) — `chiScale_eq_chiSup_of_norm_le` below;
* `chiSup ^ 2 ≥ 6/π > 1`, because `0 ≤ chiBase ≤ 1` is supported in `ball 0 (1/2)`
  of volume `π/6`;
* the Dirichlet energy `kwE = ∫ Σ_k (∂_k chiBase)^2` is positive, so that the
  scaling `z ↦ chiBase (c • z)` has `L²`-normalised Dirichlet energy `c²·kwE/chiNormSq`.
-/

/-- The scaled bump on `ℝ³`. -/
noncomputable def kwBump (c : ℝ) (z : ℝ³) : ℝ := chiBase (c • z)

/-- The Dirichlet energy of `chiBase`: `∫_{ℝ³} Σ_k (∂_k chiBase)²`. -/
noncomputable def kwE : ℝ := ∫ z : ℝ³, ∑ k : Fin 3, (fderiv ℝ chiBase z (kcStdBasis k)) ^ 2

/-- The `L²`-mass of the scaled bump over `ℝ³`. -/
noncomputable def kwLamR (c : ℝ) : ℝ := ∫ z : ℝ³, (kwBump c z) ^ 2

/-- The `L²`-mass of the bump, seen as a state on `X 1`, over the box `abox 1 s`. -/
noncomputable def kwLam (s c : ℝ) : ℝ := ∫ x in abox 1 s, (kwBump c (x 0)) ^ 2

/-- The normalised witness state on `X 1`. -/
noncomputable def kwPhi (s c : ℝ) : X 1 → ℝ :=
  fun x => (Real.sqrt (kwLam s c))⁻¹ * kwBump c (x 0)

/-! ## The window value on the small ball -/

/-- `chi = chiSup • chiBase`. -/
lemma chi_eq_chiSup_mul_chiBase (y : ℝ³) : chi y = chiSup * chiBase y := by
  unfold chi chiSup
  rw [div_eq_mul_inv, mul_comm]

/-- **The window is constant `= chiSup` on the ball of radius `s/4`**: the only point
where the witness state lives. -/
lemma chiScale_eq_chiSup_of_norm_le {s : ℝ} (hs : 0 < s) {y : ℝ³}
    (hy : ‖y‖ ≤ s / 4) : chiScale s y = chiSup := by
  have hsne : s ≠ 0 := ne_of_gt hs
  have hsm : chiScale s y = chiSup * chiBase ((s⁻¹) • y) := by
    unfold chiScale
    rw [chi_eq_chiSup_mul_chiBase]
  rw [hsm, chiBase_eq_one_of_norm_le]
  · ring
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
    rw [inv_mul_le_iff₀ hs]
    linarith

/-! ## The `X 1`-versus-`ℝ³` dictionary

`X 1 = Fin 1 → ℝ³` is measurably equivalent to `ℝ³` by evaluation at the unique slot,
via `MeasurableEquiv.funUnique (Fin 1) ℝ³` (measure preserving for `volume`).
This is the dictionary used by every integral computation on the witness family. -/

/-- `∫` over the one-particle box is the `∫` over the cube. -/
lemma integral_abox_one_eq {s : ℝ} (F : X 1 → ℝ) :
    (∫ x in abox 1 s, F x) = ∫ z in acube s, F (fun _ => z) := by
  let e : X 1 ≃ᵐ ℝ³ := MeasurableEquiv.funUnique (Fin 1) ℝ³
  have he : ⇑e = fun x : X 1 => x 0 := by
    funext x
    simp [e, MeasurableEquiv.funUnique_apply]
  have hpre : abox 1 s = e ⁻¹' acube s := by
    ext x
    simp only [Set.mem_preimage, he]
    rw [mem_abox_iff]
    exact Fin.forall_fin_one
  have h1 := (volume_preserving_funUnique (Fin 1) ℝ³).setIntegral_preimage_emb
    e.measurableEmbedding (fun z : ℝ³ => F (fun _ => z)) (acube s)
  rw [hpre]
  have h2 : ∀ x : X 1, F (fun _ => (fun x : X 1 => x 0) x) = F x := by
    intro x
    congr 1
    funext i
    exact Fin.eq_zero i ▸ rfl
  rw [show (∫ x in e ⁻¹' acube s, F x)
      = ∫ x in e ⁻¹' acube s, (fun z : ℝ³ => F (fun _ => z)) (e x) from ?_]
  · exact h1
  · refine setIntegral_congr_fun ?_ (fun x _ => ?_)
    · exact (MeasurableEquiv.measurableSet_preimage e).mpr (acube_measurable s)
    · show F x = F (fun _ => x 0)
      exact (h2 x).symm

/-- On `X 1` the sup-norm is the norm of the unique coordinate. -/
lemma norm_eq_norm_apply_zero (x : X 1) : ‖x‖ = ‖x 0‖ := by
  rw [Pi.norm_def]
  simp

/-- Coordinates of a one-particle configuration. -/
lemma eq_of_apply_zero {x y : X 1} (h : x 0 = y 0) : x = y := by
  funext i
  rwa [Fin.eq_zero i]

/-- `∀ i : Fin 1, p i` is `p 0`. -/
lemma forall_fin_one_iff {p : Fin 1 → Prop} : (∀ i, p i) ↔ p 0 := Fin.forall_fin_one

end Work.SmallBoxA0
