import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.S4Prop2.ncard_involutions_conj
import Submission.Work.DoubleTransitivity.Sec4.Defs
import Submission.Work.DoubleTransitivity.App2.app2_1
import Submission.Work.DoubleTransitivity.App2.app2_2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThreePoints.S4Prop2.sec4_basic`

Elementary facts about the action of a finite group `F` on `Ω = F ⧸ K` for a strongly embedded
subgroup `K`, as used in Peterfalvi I Ch. I §4 (pp. 154–157).

* point stabilisers are conjugates of `K`, hence strongly embedded, distinct for distinct points;
* the intersection of two point stabilisers has odd order;
* the number of involutions of a point stabiliser does not depend on the point;
* §3's remark (p. 154): if `P` is a `p`-subgroup fixing `ω ≠ ω'` and some `H ∈ Ω_P` has
  `|N_H(P)|` even, then `P` fixes at least three points of `Ω`.
-/

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open scoped Pointwise

namespace Work.ThreePoints.S4Prop2

variable {F : Type} [Group F]

/-! ## Point stabilisers -/

/-- **Point stabilisers of `F ⧸ K` are strongly embedded** when `K` is (they are the conjugates
of `K`, and `Ω` is the conjugacy class of `K`). -/
theorem isStronglyEmbedded_stabilizer {K : Subgroup F} (hK : IsStronglyEmbedded K)
    (ω : F ⧸ K) :
    IsStronglyEmbedded (MulAction.stabilizer F ω) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
  rw [Work.ThreePoints.stabilizer_mk]
  exact Work.ThreePoints.conj_stronglyEmbedded hK g

/-- Distinct points of `Ω` have distinct stabilisers. -/
theorem stabilizer_ne_of_ne {K : Subgroup F} (hK : IsStronglyEmbedded K) {ω ω' : F ⧸ K}
    (hne : ω ≠ ω') : MulAction.stabilizer F ω ≠ MulAction.stabilizer F ω' := by
  intro h
  obtain ⟨f, hf⟩ := MulAction.exists_smul_eq F ω ω'
  have hconj : conj f (MulAction.stabilizer F ω) = MulAction.stabilizer F ω := by
    rw [← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj f ω, hf, ← h]
  have hfN : f ∈ Subgroup.normalizer (MulAction.stabilizer F ω : Set F) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hconj
  rw [IsStronglyEmbedded.normalizer_eq (isStronglyEmbedded_stabilizer hK ω)] at hfN
  exact hne (hf.symm.trans (MulAction.mem_stabilizer_iff.mp hfN)).symm

/-- **Peterfalvi I Ch. I §2.**  The stabilisers of two distinct points of `Ω` meet in a subgroup
of odd order. -/
theorem odd_card_stabilizer_inf {K : Subgroup F} (hK : IsStronglyEmbedded K) {ω ω' : F ⧸ K}
    (hne : ω ≠ ω') :
    Odd (Nat.card ↥(MulAction.stabilizer F ω ⊓ MulAction.stabilizer F ω' : Subgroup F)) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective ω'
  rw [Work.ThreePoints.stabilizer_mk, Work.ThreePoints.stabilizer_mk]
  refine Work.ThreePoints.card_inf_conj_odd hK (fun h => hne ?_)
  exact Work.ThreePoints.mk_eq_of_conj_eq hK h

/-- The number of involutions of a point stabiliser does not depend on the point `ω ∈ Ω`. -/
theorem ncard_involutions_stabilizer_eq {K : Subgroup F} (ω ω' : F ⧸ K) :
    (involutions (MulAction.stabilizer F ω : Set F)).ncard =
      (involutions (MulAction.stabilizer F ω' : Set F)).ncard := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective ω'
  rw [Work.ThreePoints.stabilizer_mk, Work.ThreePoints.stabilizer_mk]
  exact (ncard_involutions_conj g K).trans (ncard_involutions_conj g' K).symm

end Work.ThreePoints.S4Prop2
