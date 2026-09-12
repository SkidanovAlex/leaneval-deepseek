import Mathlib
import Submission.Work.Lattice.TopBlockIndex
import Submission.Work.Lattice.FlowRate

/-!
# The flow rate of a subspace is the eigenvalue of its position

Combining `Submission.TopBlockIndex.isTopBlock_iMulti` (the top block of the wedge of a
subspace `P` is `finrank P − finrank (P ⊓ L)`) with the two-sided pinch of
`Submission.FlowRate`, the action of the two-scale flow `a_t = scaleMap (twoScale a b ℓ)` on the
wedge of a `j`-dimensional subspace is governed by the single eigenvalue
`a^(r) b^(j-r)`, `r = finrank (P ⊓ L)` — the **position** of `P` with respect to `L`:

* `norm_map_le_topBlock_eigen` : `‖⋀^j a_t w‖ ≤ (j+1) · e^(t·σ) · ‖w‖`;
* `norm_map_ge_topBlock_eigen` : `e^(t·σ) · ‖blockElem w (j-r)‖ ≤ ‖⋀^j a_t w‖`

where `w = ιMulti u` for an orthonormal basis `u` of `P`, `r = finrank (P ⊓ L)` and
`σ = -r/ℓ + (j-r)/(d-ℓ)`.  In particular the exponential flow rate of the *covolume* of a
rank-`j` subgroup with real span `P` is `exp (t·σ)` up to the constant `j+1`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.WedgeBlocks
open Submission.WedgeBlockZero
open Submission.FlowRate
open Submission.TopBlockIndex

namespace Submission.FlowRateSubspace

variable {d : ℕ}

/-- The top block of the wedge of an arbitrary linearly independent family spanning `P`. -/
theorem isTopBlock_iMulti_of_linearIndependent {ℓ : ℕ} (P : Submodule ℝ (RD d))
    (b : Fin (Module.finrank ℝ P) → RD d) (hb : LinearIndependent ℝ b)
    (hspan : Submodule.span ℝ (Set.range b) = P) :
    IsTopBlock (d := d) (ℓ := ℓ) (exteriorPower.ιMulti ℝ (Module.finrank ℝ P) b)
      (Module.finrank ℝ P -
        Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d))) := by
  classical
  obtain ⟨v, hv, _hvm, hvspan, _hlow⟩ :=
    Commons.Analysis.InnerProductSpace.orthonormal_family_adapted_to_inf P (modelX (d := d) ℓ)
  have ha := isTopBlock_iMulti (d := d) (ℓ := ℓ) P v hv hvspan
  obtain ⟨a, ha0, haeq⟩ :=
    Commons.LinearAlgebra.Alternating.iMulti_proportional_of_span_eq b v
      hb hv.linearIndependent (by rw [hspan, hvspan])
  constructor
  · rw [haeq, blockElem_smul (d := d) (k := Module.finrank ℝ P) (ℓ := ℓ)
      (j := Module.finrank ℝ P -
        Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d))) a _]
    intro h
    exact ha.1 ((smul_eq_zero.mp h).resolve_left ha0)
  · intro u' hu' hu'k
    rw [haeq, blockElem_smul (d := d) (k := Module.finrank ℝ P) (ℓ := ℓ) (j := u') a _,
      ha.2 u' hu' hu'k, smul_zero]

/-- **Upper flow-rate bound**: the flowed wedge of a `j`-dimensional subspace `P ≤ ℝᵈ` is at
most `(j+1)` times the eigenvalue of its position `r = finrank (P ⊓ L)` times the wedge. -/
theorem norm_map_le_topBlock_eigen {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {t : ℝ} (ht : 0 ≤ t)
    (P : Submodule ℝ (RD d)) (u : Fin (Module.finrank ℝ P) → RD d) (hu : Orthonormal ℝ u)
    (hspan : Submodule.span ℝ (Set.range u) = P) :
    ‖exteriorPower.map (Module.finrank ℝ P)
        (scaleMap (twoScale (Real.exp (-t / ↑ℓ)) (Real.exp (t / ↑(d - ℓ))) ℓ))
        (exteriorPower.ιMulti ℝ (Module.finrank ℝ P) u)‖ ≤
      ((Module.finrank ℝ P : ℝ) + 1) *
        Real.exp (t * (-((Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d)) : ℝ) / ↑ℓ)
          + (((Module.finrank ℝ P -
            Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d)) : ℕ) : ℝ) / ↑(d - ℓ)))) *
        ‖exteriorPower.ιMulti ℝ (Module.finrank ℝ P) u‖ := by
  have hbot : Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d)) ≤
      Module.finrank ℝ P :=
    Submodule.finrank_mono (R := ℝ) (inf_le_left : P ⊓ modelX (d := d) ℓ ≤ P)
  have htop := isTopBlock_iMulti (d := d) (ℓ := ℓ) P u hu hspan
  have h := norm_map_le_eigen_exp_of_isTopBlock (d := d) (k := Module.finrank ℝ P)
    (ℓ := ℓ)
    (u := Module.finrank ℝ P -
      Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d)))
    hℓ0 hℓd ht (exteriorPower.ιMulti ℝ (Module.finrank ℝ P) u)
    (Nat.sub_le _ _) htop
  have hsub : Module.finrank ℝ P -
      (Module.finrank ℝ P - Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d))) =
      Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d)) :=
    Nat.sub_sub_self hbot
  rwa [hsub] at h

/-- **Lower flow-rate bound**: the eigenvalue of the position times the corresponding block is a
lower bound for the flowed wedge. -/
theorem norm_map_ge_topBlock_eigen {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {t : ℝ} (ht : 0 ≤ t)
    (P : Submodule ℝ (RD d)) (u : Fin (Module.finrank ℝ P) → RD d) (hu : Orthonormal ℝ u)
    (hspan : Submodule.span ℝ (Set.range u) = P) :
    Real.exp (t * (-((Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d)) : ℝ) / ↑ℓ)
        + (((Module.finrank ℝ P -
          Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d)) : ℕ) : ℝ) / ↑(d - ℓ)))) *
      ‖blockElem (d := d) (k := Module.finrank ℝ P) (ℓ := ℓ)
        (exteriorPower.ιMulti ℝ (Module.finrank ℝ P) u)
        (Module.finrank ℝ P -
          Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d)))‖ ≤
      ‖exteriorPower.map (Module.finrank ℝ P)
        (scaleMap (twoScale (Real.exp (-t / ↑ℓ)) (Real.exp (t / ↑(d - ℓ))) ℓ))
        (exteriorPower.ιMulti ℝ (Module.finrank ℝ P) u)‖ := by
  have hbot : Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d)) ≤
      Module.finrank ℝ P :=
    Submodule.finrank_mono (R := ℝ) (inf_le_left : P ⊓ modelX (d := d) ℓ ≤ P)
  have htop := isTopBlock_iMulti (d := d) (ℓ := ℓ) P u hu hspan
  have h := eigen_exp_mul_norm_blockElem_le (d := d) (k := Module.finrank ℝ P) (ℓ := ℓ)
    (u := Module.finrank ℝ P -
      Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d)))
    hℓ0 hℓd ht (exteriorPower.ιMulti ℝ (Module.finrank ℝ P) u)
    (Nat.sub_le _ _)
  have hsub : Module.finrank ℝ P -
      (Module.finrank ℝ P - Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d))) =
      Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d)) :=
    Nat.sub_sub_self hbot
  rwa [hsub] at h

end Submission.FlowRateSubspace
