import Mathlib

/-!
# Almost everywhere uniqueness of the group element hitting a fundamental domain

If `s` is a fundamental domain for the action of a countable group `G` on `α` with respect to a
`G`-invariant measure `μ`, and `t =ᵐ[μ] s`, then for almost every `x` the map `g ↦ g • x` is
injective on the set of `g` with `g • x ∈ t`.

The proof is the a.e. uniqueness part of the definition of a fundamental domain, transported
along the a.e. equality `t =ᵐ[μ] s`.  Both the "uniqueness" statement and the transport are a.e.
statements, and countability of `G` lets us take the countable intersection of the (a.e.) good
sets for each pair `(g, h)` and each single `g`.
-/

open MeasureTheory
open scoped Pointwise

namespace Work.Mostow

theorem ae_subsingleton_smul_of_ae_eq_fundamentalDomain
    {G α : Type*} [Group G] [Countable G] [MulAction G α] [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.SMulInvariantMeasure G α μ] {s t : Set α}
    (hs : MeasureTheory.IsFundamentalDomain G s μ) (ht : t =ᵐ[μ] s) :
    ∀ᵐ x ∂μ, ∀ g h : G, g • x ∈ t → h • x ∈ t → g = h := by
  -- `t` and `s` differ on a null set.
  have hts : μ (symmDiff s t) = 0 := (measure_symmDiff_eq_zero_iff.mpr ht.symm)
  -- A.e., membership in `s` and membership in `t` agree along every `G`-orbit.
  have hgood : ∀ᵐ x ∂μ, ∀ g : G, g • x ∈ s ↔ g • x ∈ t := by
    rw [ae_all_iff]
    intro g
    rw [ae_iff]
    have hset : {x : α | ¬ (g • x ∈ s ↔ g • x ∈ t)} = g⁻¹ • (symmDiff s t) := by
      rw [← Set.preimage_smul g (symmDiff s t)]
      ext x
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.symmDiff_def, Set.mem_union,
        Set.mem_sdiff]
      tauto
    rw [hset, measure_smul, hts]
  -- A.e., the elements of `G` mapping `x` into `s` are unique.
  have huniq : ∀ᵐ x ∂μ, ∀ g h : G, g • x ∈ s → h • x ∈ s → g = h := by
    rw [ae_all_iff]
    intro g
    rw [ae_all_iff]
    intro h
    by_cases hgh : g = h
    · exact Filter.Eventually.of_forall fun _ _ _ => hgh
    · have hk : g * h⁻¹ ≠ 1 := fun hc => hgh (mul_inv_eq_one.mp hc)
      -- `s` and its `g * h⁻¹`-translate are a.e. disjoint, being distinct translates of a
      -- fundamental domain.
      have hdisj : μ (s ∩ (g * h⁻¹) • s) = 0 := by
        have h := hs.aedisjoint (i := (1 : G)) (j := g * h⁻¹) hk.symm
        simpa [MeasureTheory.AEDisjoint] using h
      -- the bad set is the `g⁻¹`-translate of that intersection
      have hset : {x : α | g • x ∈ s ∧ h • x ∈ s} = g⁻¹ • (s ∩ (g * h⁻¹) • s) := by
        have key : ∀ x : α, g • x ∈ (g * h⁻¹) • s ↔ h • x ∈ s := by
          intro x
          rw [Set.mem_smul_set_iff_inv_smul_mem, mul_inv_rev, inv_inv, smul_smul,
            show (h * g⁻¹) * g = h by rw [mul_assoc, inv_mul_cancel, mul_one]]
        ext x
        rw [Set.mem_ofPred_eq, Set.mem_smul_set_iff_inv_smul_mem, inv_inv,
          Set.mem_inter_iff, key x]
      have hnull : μ {x : α | g • x ∈ s ∧ h • x ∈ s} = 0 := by
        rw [hset]
        exact (measure_smul μ g⁻¹ (s ∩ (g * h⁻¹) • s)).trans hdisj
      rw [ae_iff]
      -- a point where `g • x` and `h • x` both lie in `s` is a point of the bad set
      refine measure_mono_null (fun x hx => ?_) hnull
      constructor
      · by_contra hA
        exact hx (fun ha _ => absurd ha hA)
      · by_contra hB
        exact hx (fun _ hb => absurd hb hB)
  filter_upwards [hgood, huniq] with x hg hu
  intro g h hgt hht
  exact hu g h ((hg g).mpr hgt) ((hg h).mpr hht)

end Work.Mostow
