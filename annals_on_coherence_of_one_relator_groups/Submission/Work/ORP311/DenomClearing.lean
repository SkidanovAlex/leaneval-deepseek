/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORP311 area (node B3 of `P311_DESIGN_LEAD.md`)

# Clearing denominators in `Mₙ(U_N)`

`U_N = Work.ORP311.closureCN N` is the `∗`-regular closure of `ι(ℂ[↥N])` inside `U(G)`, and
node B1 (`Work.ORP311.closureCN_subset_range_liftUN`) shows

  `U_N ⊆ Set.range (Work.ORP311.P311.liftUN N)`,

where `liftUN N` is the transparent inclusion `U(↥N) ↪ U(G)` attached to the diagonal embedding
`N(↥N) ↪ N(G)` (`Work.ORP311.P311.PhiN N`, `Work.ORP311.P311.cosetDataN N`).

Node B2 (`Work.ORP311.exists_common_denom`) clears denominators for a matrix all of whose entries
lie in the image of `liftUN N`: there are a non-zero-divisor `e ∈ N(↥N)` and a numerator matrix
`B ∈ Mₙ(N(↥N))` with `numG G (Φ_N e) * A i j = numG G (Φ_N (B i j))` for all `i, j`.

This file draws the consequences needed by the induction step:

* `Work.ORP311.P311.isUnit_numG_of_mem_nonZeroDivisors` — `numG G` sends a non-zero-divisor of
  `N(G)` to a **unit** of `U(G)` (because `U(G)` is the Ore localisation of `N(G)` at its
  non-zero-divisors);
* `Work.ORP311.P311.PhiN_mem_nonZeroDivisors` — `Φ_N` transports non-zero-divisors
  (`Work.ORVonNeumann.Rep.Phi_mem_nonZeroDivisors`);
* `Work.ORP311.P311.isUnit_numG_PhiN` — consequently `numG G (Φ_N e)` is a unit of `U(G)` for
  every non-zero-divisor `e` of `N(↥N)`;
* `Work.ORP311.exists_denom_clearing` — **the matrix form of B2 for `A ∈ Mₙ(U_N)`**: there are
  `e` as above and `B ∈ Mₙ(N(↥N))` with

    `Matrix.scalar (Fin n) (numG G (Φ_N e)) * A.map (closureCN.subtype N) = B.map (numG G ∘ Φ_N)`.

This is the shape `A = d⁻¹ · C` used by node B6: `d = numG G (Φ_N e)` is a unit of `U(G)` and
`C = B.map (numG G ∘ Φ_N)` is the block-diagonal lift of a matrix over `N(↥N)`.
-/
import Mathlib
import Submission.Work.ORP311.P311Defs
import Submission.Work.ORP311.exists_common_denom
import Submission.Work.ORP311.closureCN_subset_range_liftUN

set_option autoImplicit false

namespace Work.ORP311

open Work.ORVonNeumann

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- **The numerator map of a group von Neumann algebra sends non-zero-divisors to units of the
algebra of affiliated operators.**  Indeed `U(G) = N(G)[(nzd)⁻¹]` is the Ore localisation of
`N(G)` at its non-zero-divisors, so the image of a member of the localising submonoid is a
unit. -/
theorem numOf_isUnit_of_mem_nonZeroDivisors {G : Type*} [Group G] (D : GroupVonNeumannAlgebra G)
    (b : D.N) (hb : b ∈ nonZeroDivisors D.N) : IsUnit (VonNeumannAlgebra.numOf D b) := by
  rw [VonNeumannAlgebra.numOf_apply D b]
  exact OreLocalization.numerator_isUnit ⟨b, hb⟩

/-- **`numG G` sends a non-zero-divisor of `N(G)` to a unit of `U(G)`.** -/
theorem P311.isUnit_numG_of_mem_nonZeroDivisors (b : ↥(groupVonNeumann G))
    (hb : b ∈ nonZeroDivisors ↥(groupVonNeumann G)) :
    IsUnit (P311.numG G b) :=
  numOf_isUnit_of_mem_nonZeroDivisors (countableModel G) b hb

/-- **`Φ_N` preserves non-zero-divisors.** -/
theorem P311.PhiN_mem_nonZeroDivisors (N : Subgroup G) {b : ↥(groupVonNeumann ↥N)}
    (hb : b ∈ nonZeroDivisors ↥(groupVonNeumann ↥N)) :
    P311.PhiN N b ∈ nonZeroDivisors ↥(groupVonNeumann G) :=
  Rep.Phi_mem_nonZeroDivisors (P311.cosetDataN N) (P311.PhiN N) (P311.PhiN_spec N).2.1
    (P311.PhiN_spec N).2.2.2 hb

/-- **`numG G (Φ_N e)` is a unit of `U(G)` for every non-zero-divisor `e` of `N(↥N)`.** -/
theorem P311.isUnit_numG_PhiN (N : Subgroup G) (e : ↥(groupVonNeumann ↥N))
    (he : e ∈ nonZeroDivisors ↥(groupVonNeumann ↥N)) :
    IsUnit (P311.numG G (P311.PhiN N e)) :=
  P311.isUnit_numG_of_mem_nonZeroDivisors _ (P311.PhiN_mem_nonZeroDivisors N he)

/-- **Clearing denominators in `Mₙ(U_N)`.**
For `A ∈ Mₙ(U_N)` there are a non-zero-divisor `e ∈ N(↥N)` and a matrix `B ∈ Mₙ(N(↥N))` such
that

  `Matrix.scalar (Fin n) (numG G (Φ_N e)) * A.map (closureCN.subtype N) = B.map (numG G ∘ Φ_N)`

i.e. `numG G (Φ_N e) · A = B` in `Mₙ(U(G))` — the shape `A = d⁻¹ C` with `d = numG G (Φ_N e)`
a unit and `C` the block-diagonal lift of `B ∈ Mₙ(N(↥N))`. -/
theorem exists_denom_clearing (N : Subgroup G) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (closureCNty N)) :
    ∃ (e : ↥(groupVonNeumann ↥N)) (_ : e ∈ nonZeroDivisors ↥(groupVonNeumann ↥N))
      (B : Matrix (Fin n) (Fin n) ↥(groupVonNeumann ↥N)),
      Matrix.scalar (Fin n) (P311.numG G (P311.PhiN N e)) * A.map (closureCN.subtype N)
        = B.map (fun b => P311.numG G (P311.PhiN N b)) := by
  classical
  have hA : ∀ i j, (A.map (closureCN.subtype N)) i j ∈ Set.range (P311.liftUN N) := by
    intro i j
    exact closureCN_subset_range_liftUN (G := G) N (A i j).2
  obtain ⟨e, he, B, hB⟩ :=
    exists_common_denom (G := G) N n (A.map (closureCN.subtype N)) hA
  refine ⟨e, he, B, ?_⟩
  ext i j
  rw [Matrix.mul_apply, Matrix.map_apply]
  rw [Finset.sum_eq_single i]
  · rw [Matrix.scalar_apply, Matrix.diagonal_apply, if_pos rfl]
    exact hB i j
  · intro k _ hk
    rw [Matrix.scalar_apply, Matrix.diagonal_apply, if_neg (fun h => hk h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **Denominator clearing, unit form.**  Same data as `Work.ORP311.exists_denom_clearing`, with
the additional information that the denominator matrix `Matrix.scalar (Fin n) (numG G (Φ_N e))`
is a **unit** of `Mₙ(U(G))` (it is the image under the ring hom `Matrix.scalar (Fin n)` of the
unit `numG G (Φ_N e)`). -/
theorem exists_denom_clearing_unit (N : Subgroup G) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (closureCNty N)) :
    ∃ (e : ↥(groupVonNeumann ↥N)) (_ : e ∈ nonZeroDivisors ↥(groupVonNeumann ↥N))
      (B : Matrix (Fin n) (Fin n) ↥(groupVonNeumann ↥N)),
      IsUnit (Matrix.scalar (Fin n) (P311.numG G (P311.PhiN N e))) ∧
      Matrix.scalar (Fin n) (P311.numG G (P311.PhiN N e)) * A.map (closureCN.subtype N)
        = B.map (fun b => P311.numG G (P311.PhiN N b)) := by
  obtain ⟨e, he, B, hB⟩ := exists_denom_clearing (G := G) N A
  exact ⟨e, he, B, (P311.isUnit_numG_PhiN (G := G) N e he).map (Matrix.scalar (Fin n)), hB⟩

/-- **Denominator clearing, `A = d⁻¹ · c` form.**  The literal shape asked for by node B6: there are
a non-zero-divisor `e ∈ N(↥N)`, a matrix `B ∈ Mₙ(N(↥N))` and a *unit* `u` of `Mₙ(U(G))` with

  `u = Matrix.scalar (Fin n) (numG G (Φ_N e))`   and
  `A.map (closureCN.subtype N) = ↑u⁻¹ * B.map (numG G ∘ Φ_N)`. -/
theorem exists_denom_clearing_eq (N : Subgroup G) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (closureCNty N)) :
    ∃ (e : ↥(groupVonNeumann ↥N)) (_ : e ∈ nonZeroDivisors ↥(groupVonNeumann ↥N))
      (B : Matrix (Fin n) (Fin n) ↥(groupVonNeumann ↥N))
      (u : (Matrix (Fin n) (Fin n) (concreteEnvelope G).U)ˣ),
      (u : Matrix (Fin n) (Fin n) (concreteEnvelope G).U)
          = Matrix.scalar (Fin n) (P311.numG G (P311.PhiN N e)) ∧
      A.map (closureCN.subtype N)
        = ((↑(u⁻¹) : (Matrix (Fin n) (Fin n) (concreteEnvelope G).U)ˣ) :
              Matrix (Fin n) (Fin n) (concreteEnvelope G).U)
            * B.map (fun b => P311.numG G (P311.PhiN N b)) := by
  obtain ⟨e, he, B, hunit, hB⟩ := exists_denom_clearing_unit (G := G) N A
  obtain ⟨u, hu⟩ := hunit
  refine ⟨e, he, B, u, hu, ?_⟩
  have h2 : (↑u : Matrix (Fin n) (Fin n) (concreteEnvelope G).U)
      * A.map (closureCN.subtype N)
      = B.map (fun b => P311.numG G (P311.PhiN N b)) := by
    rw [hu]; exact hB
  calc A.map (closureCN.subtype N)
      = ((↑u⁻¹ : (Matrix (Fin n) (Fin n) (concreteEnvelope G).U)ˣ) :
            Matrix (Fin n) (Fin n) (concreteEnvelope G).U)
          * ((↑u : Matrix (Fin n) (Fin n) (concreteEnvelope G).U)
              * A.map (closureCN.subtype N)) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = ((↑u⁻¹ : (Matrix (Fin n) (Fin n) (concreteEnvelope G).U)ˣ) :
            Matrix (Fin n) (Fin n) (concreteEnvelope G).U)
          * B.map (fun b => P311.numG G (P311.PhiN N b)) := by rw [h2]

end Work.ORP311
