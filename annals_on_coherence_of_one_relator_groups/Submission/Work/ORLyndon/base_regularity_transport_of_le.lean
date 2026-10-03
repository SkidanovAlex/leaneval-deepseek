import Mathlib
import Submission.Work.ORLyndon.base_regularity_transport
import Submission.Work.ORReductions.SubgroupAlg.ker_le_span_of_subgroup
import Submission.Work.ORReductions.SubgroupAlg.subgroupAlgMap_mem_range_iff
import Submission.Work.ORReductions.SubgroupAlg.subgroupAlgMap_injective

/-!
# Transporting regularity of a base element across a group embedding

Let `m : H →* G` be an injective homomorphism of groups, `K` a field, and `E₀ ∈ K[H]` a *right
non-zero-divisor* (`∀ c, c * E₀ = 0 → c = 0`).  We show that its image
`E = mapDomainRingHom K m E₀ ∈ K[G]` is again a right non-zero-divisor, and moreover -- the
statement requested by the coherence development -- that this remains true when one restricts
attention to elements of `K[G]` whose support lies in a subgroup `N ≥ m.range`.

The mathematical content is that `K[G]` is a *free* left `K[L]`-module for `L = m.range` (with
basis the coset representatives `Quotient.out q`, `q ∈ G ⧸ L`), so right multiplication by an
element of the subalgebra `K[L]` is injective as soon as it is injective on `K[L]` itself.  The
implementation uses the explicit decomposition
`Work.ORReductions.SubgroupAlg.assemble : ((G ⧸ L) →₀ K[L]) ≃ₗ[K] K[G]`, together with
`assemble_mapRange_mul` (which turns right multiplication by `subgroupAlgMap L K y` into the
componentwise map `c ↦ c.mapRange (· * y)`) and `sum_coset_eq_zero` (injectivity of `assemble`).

The base input `E₀ ↦ E` -- the case `N = m.range` -- is `base_regularity_transport_of_range`, whose
proof is the argument of `Work.ORLyndon.base_regularity_transport` with the homomorphism `φ`
replaced by the observation that the support of `E` already lies in `m.range`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLyndon

open MonoidAlgebra

/-- Base case of the transport: if the support of `c : K[G]` already lies in the image of the
injective homomorphism `m`, then `c * mapDomainRingHom K m E₀ = 0` forces `c = 0` whenever `E₀`
is a right non-zero-divisor in `K[H]`.

Every group element outside `m.range` then has coefficient `0` in `c`, so `c` is pulled back from
`K[H]` along `m`; injectivity of `mapDomainRingHom K m` reduces the relation to `c' * E₀ = 0` and
`hreg` finishes. -/
theorem base_regularity_transport_of_range {H G : Type*} [Group H] [Group G] {K : Type*} [Field K]
    (m : H →* G) (hm : Function.Injective m)
    (E₀ : MonoidAlgebra K H) (hreg : ∀ c : MonoidAlgebra K H, c * E₀ = 0 → c = 0) :
    ∀ c : MonoidAlgebra K G, (∀ g ∈ c.coeff.support, g ∈ m.range) →
      c * MonoidAlgebra.mapDomainRingHom K m E₀ = 0 → c = 0 := by
  intro c hsupp hc
  -- Every group element outside `m.range` has coefficient zero in `c`.
  have hzero : ∀ g ∉ Set.range m, c.coeff g = 0 := by
    intro g hg
    by_contra h
    exact hg (hsupp g (Finsupp.mem_support_iff.mpr h))
  -- Hence `c` lies in the image of `mapDomainRingHom K m`.
  obtain ⟨c', hc'⟩ := (Finsupp.mem_range_mapDomain_iff (⇑m) hm c.coeff).mpr hzero
  have hmap : MonoidAlgebra.mapDomainRingHom K m (MonoidAlgebra.ofCoeff c') = c := by
    apply MonoidAlgebra.ext
    rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_mapDomain,
      MonoidAlgebra.coeff_ofCoeff, hc']
  -- `mapDomainRingHom K m` is injective, and `c * E = 0` pulls back to `c' * E₀ = 0`.
  have hinj : Function.Injective (MonoidAlgebra.mapDomainRingHom K m) :=
    MonoidAlgebra.mapDomain_injective hm
  have hmap0 : MonoidAlgebra.mapDomainRingHom K m (MonoidAlgebra.ofCoeff c' * E₀) = 0 := by
    rw [map_mul, hmap, hc]
  have hprod : MonoidAlgebra.ofCoeff c' * E₀ = 0 := hinj (by rw [hmap0, map_zero])
  have hC' : MonoidAlgebra.ofCoeff c' = 0 := hreg _ hprod
  rw [← hmap, hC', map_zero]

/-- Transport of right-regularity from the subalgebra `K[L]` to the whole of `K[G]`.

Let `L ≤ G` and `Y ∈ K[G]` be supported in `L`, and suppose that `Y` is a right non-zero-divisor
*for elements supported in `L`* (hypothesis `hbase`).  Then `Y` is a right non-zero-divisor on all
of `K[G]`.

Indeed write `Y = subgroupAlgMap L K y` with `y ∈ K[L]`, and identify `K[G]` with the direct sum
`(G ⧸ L) →₀ K[L]` via `assemble`.  Right multiplication by `Y` becomes the componentwise
multiplication by `y`, so `c * Y = 0` means `(c q) * y = 0` for every coset `q`; applying `hbase`
to `subgroupAlgMap L K (c q)` -- whose support lies in `L` -- gives `c q = 0`. -/
theorem rightRegular_transport_subgroupAlgMap {G : Type*} [Group G] {K : Type*} [Field K]
    (L : Subgroup G) (Y : MonoidAlgebra K G) (hYsupp : ↑Y.coeff.support ⊆ (L : Set G))
    (hbase : ∀ z : MonoidAlgebra K G, (∀ g ∈ z.coeff.support, g ∈ L) → z * Y = 0 → z = 0) :
    ∀ c : MonoidAlgebra K G, c * Y = 0 → c = 0 := by
  classical
  obtain ⟨y, hy⟩ :=
    (Work.ORReductions.SubgroupAlg.subgroupAlgMap_mem_range_iff L K Y).mpr hYsupp
  intro c hc
  -- Write `c` in the coordinates of the direct sum `(G ⧸ L) →₀ K[L]`.
  obtain ⟨c', hc'⟩ := Work.ORReductions.SubgroupAlg.exists_assemble_eq L K c
  -- The relation `c * Y = 0` is the vanishing of the componentwise product with `y`.
  have h1 : Work.ORReductions.SubgroupAlg.assemble L K
      (Finsupp.mapRange (fun r => r * y) (by simp) c') = 0 := by
    rw [Work.ORReductions.SubgroupAlg.assemble_mapRange_mul, hc', hy, hc]
  have h2 : Finsupp.mapRange (fun r => r * y) (by simp) c' = 0 := by
    apply Work.ORReductions.SubgroupAlg.sum_coset_eq_zero L K
    rw [← Work.ORReductions.SubgroupAlg.assemble_apply]
    exact h1
  have h3 : ∀ q : G ⧸ L, c' q * y = 0 := by
    intro q
    have hq := congrArg (fun z : G ⧸ L →₀ MonoidAlgebra K L => z q) h2
    simpa [Finsupp.mapRange_apply] using hq
  -- Each coset component vanishes: its image in `K[G]` is supported in `L`, so `hbase` applies.
  have h4 : c' = 0 := by
    apply Finsupp.ext
    intro q
    rw [Finsupp.zero_apply]
    have hz : Work.ORReductions.subgroupAlgMap L K (c' q) * Y = 0 := by
      rw [← hy, ← map_mul, h3 q, map_zero]
    have hz0 : Work.ORReductions.subgroupAlgMap L K (c' q) = 0 :=
      hbase _ ((Work.ORReductions.SubgroupAlg.subgroupAlgMap_mem_range_iff L K _).mp
        ⟨c' q, rfl⟩) hz
    have heq : Work.ORReductions.subgroupAlgMap L K (c' q)
        = Work.ORReductions.subgroupAlgMap L K (0 : MonoidAlgebra K L) := by
      rw [hz0, map_zero]
    exact Work.ORReductions.SubgroupAlg.subgroupAlgMap_injective L K heq
  rw [← hc', h4]
  simp

theorem base_regularity_transport_of_le {H G : Type*} [Group H] [Group G] {K : Type*} [Field K]
    (m : H →* G) (hm : Function.Injective m) (N : Subgroup G) (hle : m.range ≤ N)
    (E₀ : MonoidAlgebra K H) (hreg : ∀ c : MonoidAlgebra K H, c * E₀ = 0 → c = 0) :
    ∀ c : MonoidAlgebra K G, (∀ g ∈ c.coeff.support, g ∈ N) →
      c * MonoidAlgebra.mapDomainRingHom K m E₀ = 0 → c = 0 := by
  intro c _ hc
  -- The image `E` of `E₀` is supported in `L = m.range ⊆ N`.
  have hYsupp : ↑(MonoidAlgebra.mapDomainRingHom K m E₀).coeff.support ⊆ (m.range : Set G) := by
    intro g hg
    have hcoe : (MonoidAlgebra.mapDomainRingHom K m E₀).coeff
        = Finsupp.mapDomain (⇑m) E₀.coeff := by
      rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_mapDomain]
    rw [hcoe] at hg
    exact Finsupp.mem_range_of_mapDomain_ne_zero (Finsupp.mem_support_iff.mp hg)
  -- Transport across the free `K[m.range]`-module structure of `K[G]`.
  exact rightRegular_transport_subgroupAlgMap m.range
    (MonoidAlgebra.mapDomainRingHom K m E₀) hYsupp
    (base_regularity_transport_of_range m hm E₀ hreg) c hc

end Work.ORLyndon
