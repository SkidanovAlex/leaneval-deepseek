import Mathlib
import Submission.Work.Lattice.FlagAnnulus
import Submission.Work.Lattice.ConePerturbation
import Submission.Work.Lattice.Lemma5Second

/-!
# Prop 5, per-block step: an orthonormal family of a flag member with the cone condition

This packages two halves of the proof of de Saxcé §3, Prop 5:

* the **lattice approximation** `FlagAnnulus.exists_flagMember_near_direction`: every unit
  direction of `realSpan V` (for a nonzero tight saturated flag member `V ≤ Λ`) is
  approximated by a lattice point `v ∈ V` of controlled size;
* the **cone perturbation** `ConePerturbation.cone_perturbation_scaled`: relative errors of
  size `δ` between the lattice points and unit directions transfer the `π₊`-condition from
  the orthonormal directions to the lattice family.

Combining them: if `u₁,…,u_i` is an orthonormal family of `realSpan V` with
`c ≤ ‖π₊(u₁∧…∧u_i)‖` then, for any `M` large enough compared with the flag-member covering
radius of `V`, there is a family `v₁,…,v_i` of lattice points of `V` with
`‖v_k − M•u_k‖ ≤ δ M` and the same cone condition for the `v_k` with the explicit constant
`(c − ((1+δ)^i − 1))/(1+δ)^i`.
-/

noncomputable section
open Set Module Real
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

namespace Submission.BlockFamilyCone

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.JoinSubmodularity
open Submission.IntrinsicIndex
open Submission.PhiSlack
open Submission.PhiPolygon
open Submission.PhiPolygonCompare
open Submission.Prop42Upper
open Submission.QuotientMinima
open Submission.FlagMemberMinima
open Submission.FlagAnnulus
open Submission.ConePerturbation
open Submission.FamilySpanMinkowski
open Submission.UniformBddBelow
open Submission.LatticePolygon
open Commons.Lattice.SuccessiveMinima

/-- The flag-member covering radius constant of `FlagMemberMinima`. -/
noncomputable def flagConst (d : ℕ) (A : ℝ) (Λ : Submodule ℤ (E d)) : ℝ :=
  ((2 : ℝ) ^ (2 * d) / unitBallVol ((subDim Λ))) *
    Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2)) *
    successiveMinimum (E := E d) Λ (subDim Λ)

/-- **Prop 5, per-block lattice family with the cone condition.**  Let `Λ ≤ ℝᵈ` be full-rank,
`V ≤ Λ` a nonzero tight saturated flag member, `P` a projection of norm at most `1`,
`u : Fin i → ℝᵈ` an orthonormal family inside `realSpan V` with
`c ≤ ‖⋀^i P (u₁∧…∧u_i)‖`.  For `M > 0`, `δ ≥ 0` with `(1+δ)^i − 1 < c` and
`(subDim V)·(C λ_{subDim V}(Λ) + ε) ≤ δ M` (with `ε > 0`), there is a family `v` of lattice
points of `V` with `‖v_k − M•u_k‖ ≤ δ M` and
`((c − ((1+δ)^i − 1))/(1+δ)^i)·‖v₁∧…∧v_i‖ ≤ ‖⋀^i P (v₁∧…∧v_i)‖`. -/
theorem exists_block_family_cone {d : ℕ} (Λ V : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ}
    (hA : 0 ≤ A) (hVΛ : V ≤ Λ) (hV0 : V ≠ ⊥)
    (hVtight : phi A V = phiPolygon Λ A (subDim V))
    {i : ℕ} (P : E d →L[ℝ] E d) (hP1 : ∀ x, ‖P x‖ ≤ ‖x‖) (hP2 : ∀ x, P (P x) = P x)
    {c M δ ε : ℝ} (hM : 0 < M) (hε : 0 < ε) (hδ0 : 0 ≤ δ) (hc : (1 + δ) ^ i - 1 < c)
    (hrad : (subDim V : ℝ) *
        (((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
          Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2)) *
          successiveMinimum (E := E d) Λ (subDim V) + ε) ≤ δ * M)
    (u : Fin i → E d) (hu : Orthonormal ℝ u) (huV : ∀ k, u k ∈ realSpan V)
    (hbig : c ≤ ‖exteriorPower.map i (P : E d →ₗ[ℝ] E d) (exteriorPower.ιMulti ℝ i u)‖) :
    ∃ v : Fin i → E d, (∀ k, v k ∈ V) ∧ (∀ k, ‖v k - M • u k‖ ≤ δ * M) ∧
      ((c - ((1 + δ) ^ i - 1)) / (1 + δ) ^ i) * ‖exteriorPower.ιMulti ℝ i v‖ ≤
        ‖exteriorPower.map i (P : E d →ₗ[ℝ] E d) (exteriorPower.ιMulti ℝ i v)‖ := by
  classical
  have hchoice : ∀ k : Fin i, ∃ v : E d, v ∈ V ∧ ‖v - M • u k‖ ≤
      (subDim V : ℝ) *
        (((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
          Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2)) *
          successiveMinimum (E := E d) Λ (subDim V) + ε) := by
    intro k
    exact (exists_flagMember_near_direction (d := d) Λ V hΛfin hA hVΛ hV0 hVtight
      (huV k) (hu.norm_eq_one k) hM.le hε).imp (fun v hv => ⟨hv.1, hv.2.1⟩)
  choose v hvV hvM using hchoice
  refine ⟨v, hvV, ?_, ?_⟩
  · intro k
    exact le_trans (hvM k) hrad
  · exact cone_perturbation_scaled (E := E d) P hP1 hP2 hδ0 hc u
      (fun k => hu.norm_eq_one k) hbig (fun _ => hM) v (fun k => le_trans (hvM k) hrad)

end Submission.BlockFamilyCone
