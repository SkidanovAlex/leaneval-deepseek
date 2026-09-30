import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem maximalIdeal_mul_le_of_covBy {A : Type*} [CommRing A] [IsLocalRing A]
    {I J : Ideal A} (h : I ⋖ J) : IsLocalRing.maximalIdeal A * J ≤ I := by
  obtain ⟨x, hxJ, hxI⟩ := SetLike.exists_of_lt h.lt
  -- `J` is generated over `I` by any element of `J \ I`
  have hJ : I ⊔ Ideal.span {x} = J := by
    rcases h.eq_or_eq le_sup_left
        (sup_le h.le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxJ))) with h1 | h1
    · exact absurd (h1 ▸ (Submodule.mem_sup_right (Ideal.mem_span_singleton_self x))) hxI
    · exact h1
  -- the annihilator `K` of `x` modulo `I`
  set K : Ideal A := Submodule.comap (LinearMap.mulRight A x) I with hK
  have hKmem : ∀ a : A, a ∈ K ↔ a * x ∈ I := by
    intro a
    rw [hK, Submodule.mem_comap, LinearMap.mulRight_apply]
  -- `K` is maximal: it is the kernel of the surjection `A → J/I`, whose image is simple
  have hKmax : K.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨by simpa [hKmem] using hxI, ?_⟩
    intro L a hKL haK haL
    have hax : a * x ∉ I := by simpa [hKmem] using haK
    -- `I < I + (a*x) ≤ J`, so `I + (a*x) = J` by the covering relation
    have hlt : I < I ⊔ Ideal.span {a * x} :=
      lt_of_le_of_ne le_sup_left (fun hEq => hax (hEq ▸ Submodule.mem_sup_right
        (Ideal.mem_span_singleton_self (a * x))))
    have hle : I ⊔ Ideal.span {a * x} ≤ J :=
      sup_le h.le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mul_mem_left J a hxJ)))
    rcases h.eq_or_eq le_sup_left hle with h2 | h2
    · exact absurd h2 (ne_of_gt hlt)
    · -- hence `x = i + c * (a*x)`, so `1 - c*a ∈ K ⊆ L` and `c*a ∈ L`
      have hxmem : x ∈ I ⊔ Ideal.span {a * x} := by rw [h2]; exact hxJ
      obtain ⟨i, hi, z, hz, hiz⟩ := Submodule.mem_sup.mp hxmem
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hz
      have hz' : z = (a * c) * x := by rw [hc]; ring
      have hxsub : x - z = i := by rw [← hiz]; ring
      have hsub : (1 - a * c) * x = i := by rw [← hxsub, hz']; ring
      have h1cK : 1 - a * c ∈ K := by rw [hKmem]; rw [hsub]; exact hi
      have h1cL : 1 - a * c ∈ L := hKL h1cK
      have hacL : a * c ∈ L := Ideal.mul_mem_right c L haL
      simpa using L.add_mem h1cL hacL
  -- in a local ring the maximal ideal is unique, so `K = m`
  have hKeq : K = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hKmax
  rw [← hKeq, ← hJ]
  -- finally `m * J = m * (I + (x)) ≤ I + (x) * m ≤ I`
  refine Ideal.mul_le.mpr (fun r hr s hs => ?_)
  rw [Submodule.mem_sup] at hs
  obtain ⟨i, hi, z, hz, hiz⟩ := hs
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hz
  have hrx : r * x ∈ I := (hKmem r).mp hr
  have hrsi : r * s = r * i + r * z := by rw [← hiz, mul_add]
  rw [hrsi]
  refine I.add_mem (Ideal.mul_mem_left I r hi) ?_
  rw [hc]
  convert Ideal.mul_mem_left I c hrx using 1
  ring

end Work.BW
