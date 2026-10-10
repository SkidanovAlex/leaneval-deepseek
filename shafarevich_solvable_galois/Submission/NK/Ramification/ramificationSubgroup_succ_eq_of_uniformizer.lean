import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.RamificationGroup
import Submission.NK.Ramification.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Ramification

theorem ramificationSubgroup_succ_eq_of_uniformizer
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A] (π : A)
    (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π})
    (E : IntermediateField K L)
    (hfix : ∀ (σ : A.decompositionSubgroup K),
      σ ∈ NK.Ramification.ramificationSubgroup (K := K) A 0 →
        ∀ x : E, (σ : L ≃ₐ[K] L) (x : L) = (x : L))
    (hgen : ∀ x : A, ∃ p : Polynomial ↥E,
        (∀ j, (p.coeff j : L) ∈ A) ∧ p.eval₂ (algebraMap ↥E L) (π : L) = (x : L))
    {i : ℕ} (σ : A.decompositionSubgroup K)
    (hσ : σ ∈ NK.Ramification.ramificationSubgroup (K := K) A i) :
    (σ ∈ NK.Ramification.ramificationSubgroup (K := K) A (i + 1) ↔
      σ • π - π ∈ IsLocalRing.maximalIdeal A ^ (i + 2)) := by
  constructor
  · -- `σ ∈ G_{i+1} → σ π ≡ π  (mod 𝔪^{i+2})`: evaluate at the uniformizer.
    intro h
    exact h π
  · intro hd
    -- `σ ∈ G_i ⊆ G_0`, hence `σ` fixes `E` pointwise.
    have hσ0 : σ ∈ ramificationSubgroup (K := K) A 0 :=
      ramificationSubgroup_antitone (K := K) A (Nat.zero_le i) hσ
    have hfixE : ∀ a : A, (∃ x : ↥E, (x : L) = (a : L)) → σ • a = a := by
      rintro a ⟨x, hx⟩
      apply Subtype.ext
      rw [coe_smul, ← hx]
      exact hfix σ hσ0 x
    let I : Ideal A := IsLocalRing.maximalIdeal A ^ (i + 2)
    -- The subring of `A` on which `σ` acts trivially modulo `𝔪_A^{i+2}`.
    let T : Subring A :=
      { carrier := {a : A | σ • a - a ∈ I}
        mul_mem' := by
          intro a b ha hb
          change σ • (a * b) - a * b ∈ I
          have key : σ • (a * b) - a * b = (σ • a) * (σ • b - b) + (σ • a - a) * b := by
            rw [smul_mul' (N := A) σ a b]; ring
          rw [key]
          exact add_mem (Ideal.mul_mem_left I (σ • a) hb) (Ideal.mul_mem_right b I ha)
        one_mem' := by
          change σ • (1 : A) - 1 ∈ I
          rw [smul_one σ, sub_self]; exact zero_mem I
        add_mem' := by
          intro a b ha hb
          change σ • (a + b) - (a + b) ∈ I
          have key : σ • (a + b) - (a + b) = (σ • a - a) + (σ • b - b) := by
            rw [smul_add σ a b]; ring
          rw [key]
          exact add_mem ha hb
        zero_mem' := by
          change σ • (0 : A) - 0 ∈ I
          rw [smul_zero σ, sub_self]; exact zero_mem I
        neg_mem' := by
          intro a ha
          change σ • (-a) - -a ∈ I
          have key : σ • (-a) - -a = -(σ • a - a) := by rw [smul_neg σ a]; ring
          rw [key]
          exact neg_mem ha }
    -- The generating set of `A` used by `hgen`.
    let s : Set A := {π} ∪ {a : A | ∃ x : ↥E, (x : L) = (a : L)}
    have hsT : s ⊆ T := by
      intro a ha
      rcases ha with h | ⟨x, hx⟩
      · rw [Set.mem_singleton_iff] at h
        subst h
        exact hd
      · have h1 := hfixE a ⟨x, hx⟩
        change σ • a - a ∈ I
        rw [h1, sub_self]
        exact zero_mem I
    have hB : Subring.closure s ≤ T := Subring.closure_le.mpr hsT
    -- `hgen` says precisely that `s` generates `A` as a ring.
    have hmem : ∀ x : A, x ∈ Subring.closure s := by
      intro x
      obtain ⟨p, hc, hp⟩ := hgen x
      have hxsum : x = ∑ j ∈ Finset.range (p.natDegree + 1),
          (⟨(p.coeff j : L), hc j⟩ : A) * π ^ j := by
        apply Subtype.ext
        rw [← hp, Polynomial.eval₂_eq_sum_range]
        push_cast
        refine Finset.sum_congr rfl fun j hj => ?_
        rfl
      rw [hxsum]
      refine Subring.sum_mem (Subring.closure s) (fun j hj => ?_)
      exact Subring.mul_mem (Subring.closure s)
        (Subring.subset_closure (Or.inr ⟨p.coeff j, rfl⟩))
        (Subring.pow_mem (Subring.closure s) (Subring.subset_closure (Or.inl rfl)) j)
    rw [mem_ramificationSubgroup_iff]
    intro x
    exact hB (hmem x)

end NK.Ramification
