import Mathlib
import Submission.NK.NUV2.TowerRank.towerIso

/-!
# `r ≤ dualRank G ℓ` from a surjection `G ↠ (ℤ_ℓ)^r`

This file proves the *rank-theoretic* half of the elementary duality of §1 of
`Submission/Work/NUV2/TowerRank/NOTES.md`:

* if `χ_1, …, χ_r : G → ℤ_ℓ` are continuous additive characters whose product map
  `G → (Fin r → ℤ_ℓ)` is **surjective**, then `r ≤ dualRank G ℓ = rank_{ℤ_ℓ} Hom_cts(G, ℤ_ℓ)`.

The proof needs no compactness and no topology beyond the fact that the `χ_i` are additive: a
relation `∑ c_i • χ_i = 0` is evaluated at a preimage of the standard basis vector `e_j`, which
forces `c_j = 0`.  In other words the `χ_i` are `ℤ_ℓ`-linearly independent, and
`Module.le_rank_iff` converts `r` independent elements into the rank bound.

The converse (a rank bound produces such a surjection, for `G` compact) is
`NK.NUV2.TowerRank.exists_surjective_of_le_dualRank`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.NUV2.TowerRank

/-- Evaluation of a `ℤ_ℓ`-linear combination of continuous characters at a fixed group element:
`(∑ i, c i • χ i) x = ∑ i, c i * χ i x`.  (`Dual G ℓ` is an additive subgroup of the additive
monoid of functions `Additive G →+ ℤ_ℓ`, so this is `map_sum` applied twice.) -/
theorem dualSumApply {G : Type*} [CommGroup G] [TopologicalSpace G] {ℓ r : ℕ} [Fact ℓ.Prime]
    (χ : Fin r → NK.Reconstruct.Dual G ℓ) (c : Fin r → PadicInt ℓ) (x : G) :
    (∑ i, c i • χ i : NK.Reconstruct.Dual G ℓ) (Additive.ofMul x)
      = ∑ i, c i * χ i (Additive.ofMul x) := by
  have h1 : ((∑ i, c i • χ i : NK.Reconstruct.Dual G ℓ) : Additive G →+ PadicInt ℓ)
      = ∑ i, ((c i • χ i : NK.Reconstruct.Dual G ℓ) : Additive G →+ PadicInt ℓ) :=
    map_sum (AddSubgroup.subtype (NK.Reconstruct.dualCarrier G ℓ)) _ Finset.univ
  let ev : (Additive G →+ PadicInt ℓ) →+ PadicInt ℓ :=
    { toFun := fun f => f (Additive.ofMul x)
      map_zero' := rfl
      map_add' := fun f g => rfl }
  rw [h1]
  show ev (∑ i, ((c i • χ i : NK.Reconstruct.Dual G ℓ) : Additive G →+ PadicInt ℓ))
      = ∑ i, c i * χ i (Additive.ofMul x)
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ((c i • χ i : NK.Reconstruct.Dual G ℓ) : Additive G →+ PadicInt ℓ) (Additive.ofMul x)
      = c i * χ i (Additive.ofMul x)
  rw [NK.RankTheoryDeep.smul_dual_apply]

theorem le_dualRank_of_surjective {G : Type*} [CommGroup G] [TopologicalSpace G] {ℓ r : ℕ}
    [Fact ℓ.Prime] (χ : Fin r → NK.Reconstruct.Dual G ℓ)
    (h : Function.Surjective fun x : G => fun i => χ i (Additive.ofMul x)) :
    (r : Cardinal) ≤ NK.RankTheoryDeep.dualRank G ℓ := by
  rw [NK.RankTheoryDeep.dualRank, Module.le_rank_iff]
  refine ⟨χ, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  -- a preimage of the `j`-th standard basis vector of `ℤ_ℓ^r`
  obtain ⟨x, hx⟩ := h (Function.update (fun _ : Fin r => (0 : PadicInt ℓ)) j 1)
  -- evaluating the relation `∑ c i • χ i = 0` at `x` gives `c j = 0`
  have hval : (∑ i, c i • χ i : NK.Reconstruct.Dual G ℓ) (Additive.ofMul x) = c j := by
    rw [dualSumApply χ c x]
    calc ∑ i, c i * χ i (Additive.ofMul x)
        = ∑ i, c i * Function.update (fun _ : Fin r => (0 : PadicInt ℓ)) j 1 i := by
          refine Finset.sum_congr rfl fun i _ => congrArg (fun y => c i * y) (congrFun hx i)
      _ = c j := by
          rw [Finset.sum_eq_single j]
          · rw [Function.update_self, mul_one]
          · intro i _ hij
            rw [Function.update_of_ne hij, mul_zero]
          · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [← hval, hc]
  simp

end NK.NUV2.TowerRank
