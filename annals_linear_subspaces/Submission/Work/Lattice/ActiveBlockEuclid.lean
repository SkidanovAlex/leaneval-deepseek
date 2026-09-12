import Mathlib
import Submission.Work.Lattice.ActiveBlock
import Submission.Work.Lattice.Lemma5General
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal
import Submission.Commons.LinearAlgebra.Alternating.iMulti_proportional_of_span_eq

/-!
# The `A₂` bridge: an active block gives a Euclidean block bound for the ON wedge

`Submission.ActiveBlock` characterises the *max-norm* (paper) notion of the active block of a
flowed wedge: `u` is active at time `t` when `e^{tσ_u}·cnorm (block_u v) = cnorm (⋀^k a_t v)`,
i.e. when block `u` carries the whole sup-norm mass of the flowed wedge.  The extraction
(Prop. 5 of de Saxcé) however consumes the *Euclidean* hypothesis of
`Lemma5General.lemma5_first_assertion`:

    `c ≤ ‖blockElem (ιMulti a) u‖` for the orthonormal basis `a` of the (flowed) member.

This module proves the bridge: if `a` is an orthonormal basis of the *flowed* member
`span (a_t ∘ v)`, then the Euclidean norm of the block `u` of `ιMulti a` is bounded below by the
constant `1/√(choose d k)` — independent of the member, the time and the block.  The proof is the
max-norm/Euclidean comparability (`cnorm ≤ ‖·‖ ≤ √(choose d k)·cnorm`) plus the exact block
eigenvalue identity (`norm_blockElem_map_twoScale`) and the proportionality of the wedges.

Module `Submission.Work.Lattice.ActiveBlockEuclid`, namespace `Submission.ActiveBlockEuclid`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real Filter
open scoped BigOperators Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option linter.unnecessarySimpa false

namespace Submission.ActiveBlockEuclid

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.MaxNorm
open Submission.FlowRateAsymptotic
open Submission.MaxNormFlow
open Submission.FlowDataMax

variable {d : ℕ}

/-- The flow of a linearly independent family is linearly independent. -/
lemma linearIndependent_eFlow_comp {k ℓ : ℕ} {t : ℝ}
    {v : Fin k → RD d} (hv : LinearIndependent ℝ v) :
    LinearIndependent ℝ (fun i => eFlow (d := d) ℓ t (v i)) := by
  have hker : LinearMap.ker (eFlow (d := d) ℓ t) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (eFlow_injective (d := d) ℓ t)
  have h := hv.map (f := eFlow (d := d) ℓ t) (by rw [hker]; exact disjoint_bot_right)
  simpa [Function.comp_def] using h

/-- The wedge of the flow of a family is the flow of the wedge. -/
lemma iMulti_eFlow_comp {k ℓ : ℕ} (t : ℝ) (v : Fin k → RD d) :
    exteriorPower.ιMulti ℝ k (fun i => eFlow (d := d) ℓ t (v i)) =
      exteriorPower.map k (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ k v) := by
  simpa [Function.comp_def] using
    (exteriorPower.map_apply_ιMulti (f := eFlow (d := d) ℓ t) v).symm

/-- The eigenvalue of the block `u` under the exponential flow. -/
lemma eigen_eFlow {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {k u : ℕ} (huk : u ≤ k) {t : ℝ} :
    (Real.exp (-t / (ℓ : ℝ))) ^ (k - u) * (Real.exp (t / ((d - ℓ : ℕ) : ℝ))) ^ u =
      Real.exp (t * sig (d := d) k ℓ u) := by
  have h1 : (Real.exp (-t / (ℓ : ℝ))) ^ (k - u) = Real.exp (((k - u : ℕ) : ℝ) * (-t / (ℓ : ℝ))) :=
    (Real.exp_nat_mul _ _).symm
  have h2 : (Real.exp (t / ((d - ℓ : ℕ) : ℝ))) ^ u = Real.exp ((u : ℝ) * (t / ((d - ℓ : ℕ) : ℝ))) :=
    (Real.exp_nat_mul _ _).symm
  rw [h1, h2, ← Real.exp_add]
  congr 1
  rw [sig_eq_eigen (d := d) hℓ0 hℓd huk, Nat.cast_sub huk, Nat.cast_sub (le_of_lt hℓd)]
  field_simp

/-- **The `A₂` bridge.**  Let `v` be a linearly independent family in `ℝᵈ` (a ℤ-basis of a member
of the flowed lattice), `a` an orthonormal basis of the *flowed* span `span {a_t v_i}`, and let the
block `u` be active at time `t` in the max-norm sense.  Then the Euclidean norm of block `u` of the
ON wedge is at least `1/√(choose d k)`. -/
theorem activeBlock_blockNorm_ge {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {hk : k ≤ d} (hk0 : 0 < k)
    {t : ℝ} {v : Fin k → RD d} (hv : LinearIndependent ℝ v) {a : Fin k → RD d}
    (ha : Orthonormal ℝ a)
    (hspan : Submodule.span ℝ (Set.range a) =
      Submodule.span ℝ (Set.range (fun i => eFlow (d := d) ℓ t (v i))))
    {u : ℕ} (hu : u ≤ k)
    (hact : Real.exp (t * sig (d := d) k ℓ u) *
        cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k v) u) =
      cnorm hk (exteriorPower.map k (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ k v))) :
    (Real.sqrt ((Nat.choose d k : ℕ) : ℝ))⁻¹ ≤
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k a) u‖ := by
  classical
  set vf : Fin k → RD d := fun i => eFlow (d := d) ℓ t (v i) with hvf
  have hfli : LinearIndependent ℝ vf := linearIndependent_eFlow_comp (d := d) hv
  have hsp : Submodule.span ℝ (Set.range a) = Submodule.span ℝ (Set.range vf) := hspan
  obtain ⟨μ, hμne, hμ⟩ :=
    Commons.LinearAlgebra.Alternating.iMulti_proportional_of_span_eq a vf ha.linearIndependent hfli hsp
  have hμ' : exteriorPower.ιMulti ℝ k a = μ • exteriorPower.map k (eFlow (d := d) ℓ t)
      (exteriorPower.ιMulti ℝ k v) := by
    rw [hμ, iMulti_eFlow_comp]
  -- norms
  have hnorm_a : ‖exteriorPower.ιMulti ℝ k a‖ = 1 :=
    Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal a ha hk0
  have hwne : exteriorPower.map k (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ k v) ≠ 0 :=
    map_eFlow_iMulti_ne_zero (d := d) (ℓ := ℓ) t hv
  have hwpos : 0 < ‖exteriorPower.map k (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ k v)‖ :=
    norm_pos_iff.mpr hwne
  have hμabs : |μ| = (‖exteriorPower.map k (eFlow (d := d) ℓ t)
      (exteriorPower.ιMulti ℝ k v)‖)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    have h := congrArg norm hμ'
    rw [hnorm_a, norm_smul, Real.norm_eq_abs] at h
    exact h.symm
  -- the block identity: `block_u (ιMulti a) = μ • block_u (flowed wedge)`
  have hgoal : ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k a) u‖ =
      |μ| * ‖blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.map k (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ k v)) u‖ := by
    rw [hμ', blockElem_smul, norm_smul, Real.norm_eq_abs]
  rw [hgoal, hμabs]
  -- the flowed block norm, in terms of the unflowed one
  have hblk : ‖blockElem (d := d) (k := k) (ℓ := ℓ)
      (exteriorPower.map k (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ k v)) u‖ =
      Real.exp (t * sig (d := d) k ℓ u) *
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k v) u‖ := by
    rw [eFlow_eq, norm_blockElem_map_twoScale (d := d) (k := k) (ℓ := ℓ)
      (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d - ℓ : ℕ) : ℝ)))
      (exteriorPower.ιMulti ℝ k v) hu (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))]
    rw [eigen_eFlow (d := d) hℓ0 hℓd hu]
  rw [hblk]
  -- the active condition identifies the flowed max-norm with the block mass
  have hcnorm_le : cnorm hk (exteriorPower.map k (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ k v)) ≤
      Real.exp (t * sig (d := d) k ℓ u) *
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k v) u‖ := by
    rw [← hact]
    exact mul_le_mul_of_nonneg_left (cnorm_le_norm (d := d) hk _) (le_of_lt (Real.exp_pos _))
  have hCpos : 0 < Real.sqrt ((Nat.choose d k : ℕ) : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.choose_pos hk)
  have hstep : (Real.sqrt ((Nat.choose d k : ℕ) : ℝ))⁻¹ ≤
      cnorm hk (exteriorPower.map k (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ k v)) /
        ‖exteriorPower.map k (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ k v)‖ := by
    rw [le_div_iff₀ hwpos, inv_mul_le_iff₀ hCpos]
    linarith [norm_le_sqrt_card_mul_cnorm (d := d) hk
      (exteriorPower.map k (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ k v))]
  calc (Real.sqrt ((Nat.choose d k : ℕ) : ℝ))⁻¹
      ≤ cnorm hk (exteriorPower.map k (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ k v)) /
          ‖exteriorPower.map k (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ k v)‖ := hstep
    _ ≤ (Real.exp (t * sig (d := d) k ℓ u) *
          ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k v) u‖) /
          ‖exteriorPower.map k (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ k v)‖ :=
        div_le_div_of_nonneg_right hcnorm_le (le_of_lt hwpos)
    _ = (‖exteriorPower.map k (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ k v)‖)⁻¹ *
          (Real.exp (t * sig (d := d) k ℓ u) *
            ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k v) u‖) := by
        rw [div_eq_inv_mul]

/-! ## The ON directions with `π₊`-dominance (Lemma 5 of the paper) -/

/-- **The ON family with `π₊`-dominance supplied by an active block.**  Combining the `A₂` bridge
(`activeBlock_blockNorm_ge`) with de Saxcé's Lemma 5 (`Lemma5General.lemma5_first_assertion`): if
the block `u` is active at time `t`, then the flowed member contains `k − u` orthonormal directions
whose wedge has `π₊`-norm at least `(√(choose d k))⁻¹ / choose k (k − u)`. -/
theorem exists_orthonormal_dominated_of_activeBlock {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    {hk : k ≤ d} (hk0 : 0 < k) {t : ℝ} {v : Fin k → RD d} (hv : LinearIndependent ℝ v)
    {a : Fin k → RD d} (ha : Orthonormal ℝ a)
    (hspan : Submodule.span ℝ (Set.range a) =
      Submodule.span ℝ (Set.range (fun i => eFlow (d := d) ℓ t (v i))))
    {u : ℕ} (hu : u ≤ k)
    (hact : Real.exp (t * sig (d := d) k ℓ u) *
        cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k v) u) =
      cnorm hk (exteriorPower.map k (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ k v))) :
    ∃ w : Fin (k - u) → RD d, Orthonormal ℝ w ∧
      Submodule.span ℝ (Set.range w) ≤ Submodule.span ℝ (Set.range a) ∧
      (Real.sqrt ((Nat.choose d k : ℕ) : ℝ))⁻¹ / (Nat.choose k (k - u) : ℝ) ≤
        ‖blockElem (d := d) (k := k - u) (ℓ := ℓ)
          (exteriorPower.ιMulti ℝ (k - u) w) 0‖ := by
  have hbig := activeBlock_blockNorm_ge (d := d) hℓ0 hℓd hk0 hv ha hspan hu hact
  have hbig' : (Real.sqrt ((Nat.choose d k : ℕ) : ℝ))⁻¹ ≤
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k a) (k - (k - u))‖ := by
    rw [Nat.sub_sub_self hu]
    exact hbig
  obtain ⟨f, hf, hle⟩ :=
    Submission.Lemma5General.lemma5_first_assertion (d := d) ℓ (Nat.sub_le k u) a ha hbig'
  refine ⟨fun r => a (f r), ha.comp f hf, ?_, hle⟩
  refine Submodule.span_mono ?_
  rintro y ⟨i, rfl⟩
  exact Set.mem_range_self (f i)


end Submission.ActiveBlockEuclid

end
