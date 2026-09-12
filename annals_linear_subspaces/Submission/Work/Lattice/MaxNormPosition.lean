import Mathlib
import Submission.Work.Lattice.MaxNormFlow
import Submission.Work.Lattice.FlowRateSubspace

/-!
# The paper's integers `ℓ_s` are the positions `j_s − dim (span V_{j_s} ⊓ L)`

de Saxcé's §3 defines, for the flag member `V_{j_s}` of the Harder–Narasimhan filtration of
`Λ_t = a_t s_x ℤᵈ`, the integer `ℓ_s` by

    log ‖a_t s_x V_{j_s}‖ = (j_s − ℓ_s)·(−t/ℓ) + ℓ_s·(t/(d−ℓ)),

i.e. `ℓ_s` is the index of the block whose eigenvalue governs the flow of the wedge.  This
module identifies it: for all sufficiently large `t` (and the time selected in the proof of
Theorem 9 is arbitrarily large, `Submission.Polygon.time_selection`), the *max norm* of the
flowed wedge is exactly the top-block eigenvalue, and the top block index of the wedge of a
linear family is the **position** `dim V − dim (span V ⊓ L)`:

* `topBlockIndex_eq_of_isTopBlock` — a `k`-vector whose top block is `u` has top block index `u`;
* `eventually_cnorm_map_flow_eq_top_of_linearIndependent` — for a linearly independent family
  `b : Fin (finrank P) → ℝᵈ` spanning `P`, all large `t` satisfy

      cnorm (⋀^j a_t (ιMulti b)) = exp (t·σ_{j−r}) · cnorm (blockElem (ιMulti b) (j−r)),
      j = finrank P,  r = finrank (P ⊓ modelX ℓ);

  hence `ℓ_s = j_s − r_{j_s}` (with `MaxNormFlow.eventually_cnorm_map_flow_eq_top` giving the
  exact eigenvalue and `TopBlockIndex.isTopBlock_iMulti`/`FlowRateSubspace` giving the top block).
* `eventually_cnorm_map_flow_eq_top_of_orthonormal` — the orthonormal special case.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.WedgeBlocks
open Submission.MaxNorm
open Submission.MaxNormFlow
open Submission.FlowRate
open Submission.FlowRateAsymptotic
open Submission.FlowRateSubspace
open Submission.TopBlockIndex

namespace Submission.MaxNormPosition

variable {d : ℕ}

/-- A `k`-vector whose top nonvanishing block is `u` has `topBlockIndex` equal to `u`. -/
lemma topBlockIndex_eq_of_isTopBlock {k ℓ u : ℕ} (w : WK d k) (huk : u ≤ k)
    (htop : IsTopBlock (d := d) (ℓ := ℓ) w u) :
    topBlockIndex (d := d) ℓ w = u := by
  classical
  have hw : w ≠ 0 := by
    intro h
    rw [h] at htop
    exact htop.1 (by simp)
  refine le_antisymm ?_ ?_
  · by_contra h
    have hlt : u < topBlockIndex (d := d) ℓ w := not_le.mp h
    have hle : topBlockIndex (d := d) ℓ w ≤ k := topBlockIndex_le (d := d) ℓ w
    exact blockElem_topBlockIndex_ne_zero (d := d) w hw (htop.2 _ hlt hle)
  · exact le_topBlockIndex ℓ w huk htop.1

/-- **The paper's `ℓ_s` for a lattice basis of a rank-`j` subgroup.**  For a linearly independent
family `b : Fin (finrank P) → ℝᵈ` spanning `P` and for all sufficiently large `t`, the max norm
of the flowed wedge of `b` equals the top-block eigenvalue, the top block being the position
`finrank P − finrank (P ⊓ modelX ℓ)`. -/
theorem eventually_cnorm_map_flow_eq_top_of_linearIndependent {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    (P : Submodule ℝ (RD d)) (hk : Module.finrank ℝ P ≤ d)
    (b : Fin (Module.finrank ℝ P) → RD d) (hb : LinearIndependent ℝ b)
    (hspan : Submodule.span ℝ (Set.range b) = P) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      cnorm (d := d) hk (exteriorPower.map (Module.finrank ℝ P)
          (scaleMap (twoScale (Real.exp (-t / (ℓ : ℝ)))
            (Real.exp (t / ((d - ℓ : ℕ) : ℝ))) ℓ))
          (exteriorPower.ιMulti ℝ (Module.finrank ℝ P) b)) =
        Real.exp (t * sig (d := d) (Module.finrank ℝ P) ℓ
            (Module.finrank ℝ P - Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d)))) *
          cnorm (d := d) hk (blockElem (d := d) (k := Module.finrank ℝ P) (ℓ := ℓ)
            (exteriorPower.ιMulti ℝ (Module.finrank ℝ P) b)
            (Module.finrank ℝ P - Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d)))) := by
  classical
  obtain ⟨T, hT⟩ := eventually_cnorm_map_flow_eq_top (d := d) hℓ0 hℓd hk
    (exteriorPower.ιMulti ℝ (Module.finrank ℝ P) b)
    (Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent
      (K := ℝ) (E := RD d) (k := Module.finrank ℝ P) b hb)
  have htop := isTopBlock_iMulti_of_linearIndependent (d := d) (ℓ := ℓ) P b hb hspan
  have hidx := topBlockIndex_eq_of_isTopBlock (d := d)
    (w := exteriorPower.ιMulti ℝ (Module.finrank ℝ P) b)
    (u := Module.finrank ℝ P - Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d)))
    (Nat.sub_le _ _) htop
  refine ⟨T, fun t ht => ?_⟩
  have h := hT t ht
  rw [hidx] at h
  exact h

/-- The orthonormal special case (an orthonormal family is linearly independent). -/
theorem eventually_cnorm_map_flow_eq_top_of_orthonormal {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    (P : Submodule ℝ (RD d)) (hk : Module.finrank ℝ P ≤ d)
    (u : Fin (Module.finrank ℝ P) → RD d) (hu : Orthonormal ℝ u)
    (hspan : Submodule.span ℝ (Set.range u) = P) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      cnorm (d := d) hk (exteriorPower.map (Module.finrank ℝ P)
          (scaleMap (twoScale (Real.exp (-t / (ℓ : ℝ)))
            (Real.exp (t / ((d - ℓ : ℕ) : ℝ))) ℓ))
          (exteriorPower.ιMulti ℝ (Module.finrank ℝ P) u)) =
        Real.exp (t * sig (d := d) (Module.finrank ℝ P) ℓ
            (Module.finrank ℝ P - Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d)))) *
          cnorm (d := d) hk (blockElem (d := d) (k := Module.finrank ℝ P) (ℓ := ℓ)
            (exteriorPower.ιMulti ℝ (Module.finrank ℝ P) u)
            (Module.finrank ℝ P - Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d)))) :=
  eventually_cnorm_map_flow_eq_top_of_linearIndependent (d := d) hℓ0 hℓd P hk u
    hu.linearIndependent hspan

end Submission.MaxNormPosition
