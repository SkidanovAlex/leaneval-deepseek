/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The ring of integers of a local field is Henselian

A non-archimedean local field `k` (in the sense of `Work.LocalFields.IsLocalField`: a field with a
rank-one valuation whose ring of integers is compact, hence complete with discrete valuation and
finite residue field) has a Henselian ring of integers: the local field is complete, so its
valuation ring satisfies Hensel's lemma.

The chain of ideas is the classical one.

* The ring of integers `𝒪 = 𝒪[k]` is a discrete valuation ring, hence Noetherian local.
* Powers of the maximal ideal are closed in `𝒪` (they are closed balls for the valuation, and the
  ring of integers carries the subspace topology).
* Compactness of `𝒪` then shows that any adically Cauchy sequence converges adically (a nested
  intersection of closed sets of the form `f n + 𝔪ⁿ` has a point), so `𝒪` is `𝔪`-adically complete:
  `IsAdicComplete 𝔪 𝒪`.
* An `I`-adically complete ring is Henselian at `I` (`IsAdicComplete.henselianRing`), and a local
  ring Henselian at its maximal ideal is a `HenselianLocalRing`.

## Main results

* `Work.LocalFields.henselianLocalRing_intRing` : `HenselianLocalRing (Valued.integer k)`.
-/
import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.CompletionLocalField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped Valued WithZero

/-- The powers of the maximal ideal of the ring of integers of a local field are closed subsets:
a power of the maximal ideal is a closed ball for the valuation, and the ring of integers carries
the subspace topology. -/
private theorem isClosed_maximalIdeal_pow_intRing {k : Type*} [Field k]
    [Valued k (WithZero (Multiplicative ℤ))] [Work.LocalFields.IsLocalField k] (n : ℕ) :
    IsClosed (((IsLocalRing.maximalIdeal (Valued.integer k)) ^ n :
      Ideal (Valued.integer k)) : Set (Valued.integer k)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Valued.integer k)
  -- `𝓂 ^ n` is the closed ball `{y | v y ≤ v ϖ ^ n}`.
  have hpow : (((IsLocalRing.maximalIdeal (Valued.integer k)) ^ n :
        Ideal (Valued.integer k)) : Set (Valued.integer k)) =
      {y : Valued.integer k | Valued.v (y : k) ≤ Valued.v (ϖ : k) ^ n} :=
    Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (Valued.v (R := k)) hϖ n
  -- which is the preimage of a closed ball of `k` under the inclusion `𝒪[k] → k`.
  have hset : (((IsLocalRing.maximalIdeal (Valued.integer k)) ^ n :
        Ideal (Valued.integer k)) : Set (Valued.integer k)) =
        Subtype.val ⁻¹' {x : k | (Valued.v (R := k)).restrict x ≤
          ((Valued.v (R := k)).restrict (ϖ : k)) ^ n} := by
    rw [hpow]
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, ← map_pow, Valuation.restrict_le_iff]
  rw [hset]
  exact (Valued.isClosed_closedBall k (((Valued.v (R := k)).restrict (ϖ : k)) ^ n)).preimage
    continuous_subtype_val

/-- The ring of integers of a local field is complete at its maximal ideal.

`IsAdicComplete` is an algebraic condition (Hausdorffness and precompleteness for the `𝔪`-adic
topology).  Hausdorffness is Krull's intersection theorem, while precompleteness follows from
compactness of `𝒪[k]`: the sets `f n + 𝔪ⁿ` are nested, closed and nonempty, and a point `L` of
their intersection is an `𝔪`-adic limit of the sequence `f`. -/
private theorem isAdicComplete_maximalIdeal_intRing {k : Type*} [Field k]
    [Valued k (WithZero (Multiplicative ℤ))] [Work.LocalFields.IsLocalField k] :
    IsAdicComplete (IsLocalRing.maximalIdeal (Valued.integer k)) (Valued.integer k) := by
  refine { haus' := ?_, prec' := ?_ }
  · -- Krull's intersection theorem: `⋂ n, 𝔪 ^ n = ⊥`.
    intro x hx
    have hmem : ∀ n, x ∈ (IsLocalRing.maximalIdeal (Valued.integer k)) ^ n := by
      intro n
      have h := SModEq.zero.mp (hx n)
      simpa [Ideal.smul_eq_mul] using h
    have hbot : x ∈ (⊥ : Ideal (Valued.integer k)) := by
      rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal (Valued.integer k))
        ((IsLocalRing.maximalIdeal.isMaximal (Valued.integer k)).ne_top)]
      exact (Submodule.mem_iInf _).mpr hmem
    simpa using hbot
  · intro f hf
    classical
    -- the nested closed sets `f n + 𝔪ⁿ`
    let S : ℕ → Set (Valued.integer k) :=
      fun n => {x | x - f n ∈ (IsLocalRing.maximalIdeal (Valued.integer k)) ^ n}
    have hSclosed : ∀ n, IsClosed (S n) := by
      intro n
      have hc : Continuous fun x : Valued.integer k => x - f n := continuous_id.sub continuous_const
      exact (isClosed_maximalIdeal_pow_intRing n).preimage hc
    have hSmono : ∀ n, S (n + 1) ⊆ S n := by
      intro n x hx
      simp only [S, Set.mem_ofPred_eq] at hx ⊢
      have h1 : x - f (n + 1) ∈ (IsLocalRing.maximalIdeal (Valued.integer k)) ^ n :=
        Ideal.pow_le_pow_right (Nat.le_succ n) hx
      have h2 : f (n + 1) - f n ∈ (IsLocalRing.maximalIdeal (Valued.integer k)) ^ n := by
        have h := SModEq.sub_mem.mp (hf (Nat.le_succ n))
        simpa [Ideal.smul_eq_mul] using neg_mem h
      have h3 : x - f n = (x - f (n + 1)) + (f (n + 1) - f n) := by ring
      rw [h3]
      exact Ideal.add_mem _ h1 h2
    have hSne : ∀ n, (S n).Nonempty := fun n => ⟨f n, by simp [S]⟩
    have hcomp : IsCompact (S 0) :=
      isCompact_univ.of_isClosed_subset (hSclosed 0) (Set.subset_univ _)
    obtain ⟨L, hL⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      S hSmono hSne hcomp hSclosed
    refine ⟨L, fun n => ?_⟩
    have hmem : L - f n ∈ (IsLocalRing.maximalIdeal (Valued.integer k)) ^ n := by
      have := Set.mem_iInter.mp hL n
      simpa [S] using this
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
    simpa using neg_mem hmem

/-- **The ring of integers of a non-archimedean local field is a Henselian local ring.**

Indeed, a local ring that is complete at its maximal ideal is Henselian (Hensel's lemma, proved in
Mathlib as `IsAdicComplete.henselianRing`), and here completeness at the maximal ideal comes from
compactness of the ring of integers. -/
theorem henselianLocalRing_intRing {k : Type*} [Field k]
    [Valued k (WithZero (Multiplicative ℤ))] [Work.LocalFields.IsLocalField k] :
    HenselianLocalRing (Valued.integer k) := by
  have hadic : IsAdicComplete (IsLocalRing.maximalIdeal (Valued.integer k))
      (Valued.integer k) := isAdicComplete_maximalIdeal_intRing
  refine { is_henselian := ?_ }
  intro f hf a₀ h₁ h₂
  obtain ⟨a, ha, hsub⟩ := HenselianRing.is_henselian (R := Valued.integer k)
    (I := IsLocalRing.maximalIdeal (Valued.integer k)) f hf a₀ h₁ (h₂.map (Ideal.Quotient.mk _))
  exact ⟨a, ha, hsub⟩

end Work.LocalFields
