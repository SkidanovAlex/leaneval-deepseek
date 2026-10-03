import Mathlib

namespace Work.ORLyndon

theorem base_regularity_transport {H G : Type*} [Group H] [Group G] {K : Type*} [Field K]
    (m : H →* G) (hm : Function.Injective m) (φ : G →* Multiplicative ℤ)
    (hrange : ∀ g : G, g ∈ m.range ↔ φ g = 1)
    (E₀ : MonoidAlgebra K H) (hreg : ∀ c : MonoidAlgebra K H, c * E₀ = 0 → c = 0) :
    ∀ c : MonoidAlgebra K G, (∀ g ∈ c.coeff.support, φ g = 1) →
      c * MonoidAlgebra.mapDomainRingHom K m E₀ = 0 → c = 0 := by
  intro c hsupp hc
  -- Every group element outside `m.range = ker φ` has coefficient zero in `c`.
  have hzero : ∀ g ∉ Set.range m, c.coeff g = 0 := by
    intro g hg
    by_contra h
    exact hg ((hrange g).mpr (hsupp g (Finsupp.mem_support_iff.mpr h)))
  -- Hence `c` lies in the image of `mapDomainRingHom K m`.
  obtain ⟨c', hc'⟩ := (Finsupp.mem_range_mapDomain_iff (⇑m) hm c.coeff).mpr hzero
  have hmap : MonoidAlgebra.mapDomainRingHom K m (MonoidAlgebra.ofCoeff c') = c := by
    apply MonoidAlgebra.ext
    rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_mapDomain,
      MonoidAlgebra.coeff_ofCoeff, hc']
  -- `mapDomainRingHom K m` is injective, and `c * E₀' = 0` pulls back to `c' * E₀ = 0`.
  have hinj : Function.Injective (MonoidAlgebra.mapDomainRingHom K m) :=
    MonoidAlgebra.mapDomain_injective hm
  have hmap0 : MonoidAlgebra.mapDomainRingHom K m (MonoidAlgebra.ofCoeff c' * E₀) = 0 := by
    rw [map_mul, hmap, hc]
  have hprod : MonoidAlgebra.ofCoeff c' * E₀ = 0 := hinj (by rw [hmap0, map_zero])
  have hC' : MonoidAlgebra.ofCoeff c' = 0 := hreg _ hprod
  rw [← hmap, hC', map_zero]

end Work.ORLyndon
