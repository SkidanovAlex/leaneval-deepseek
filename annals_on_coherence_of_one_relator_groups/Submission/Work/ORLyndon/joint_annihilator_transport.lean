import Mathlib
import Submission.Work.ORReductions.SubgroupAlg.ker_le_span_of_subgroup
import Submission.Work.ORLyndon.base_regularity_transport_of_le

/-!
# Transport of the triviality of a (set-indexed) annihilator across a group embedding

Let `m : H →* G` be an **injective** group homomorphism, `K` a field, and `Q ⊆ K[H]` a set of
elements whose **left annihilator** in `K[H]` is trivial:

`hbase : ∀ c : K[H], (∀ Y ∈ Q, c * Y = 0) → c = 0`.

The theorem below shows that then the left annihilator of the image of `Q` in `K[G]` is trivial as
well: every `c : K[G]` with `c * mapDomainRingHom K m Y = 0` for all `Y ∈ Q` is zero.  This is the
set-indexed version of `Work.ORLyndon.base_regularity_transport`.

## Proof

The mathematical content is that `K[G]` is a **free left `K[S]`-module** for the subgroup
`S = m.range ≤ G`, with basis the coset representatives `Quotient.out q`, `q ∈ G ⧸ S`.  Concretely,
the `K`-linear equivalence

`Work.ORReductions.SubgroupAlg.assemble S K : ((G ⧸ S) →₀ K[S]) ≃ₗ[K] K[G]`

identifies `K[G]` with the direct sum of the coset components and turns right multiplication by an
element of `K[S]` into the componentwise map `c ↦ c.mapRange (· * y)`
(`assemble_mapRange_mul`).  Writing `c = assemble S K c'` we get, for every `Y ∈ Q`,

`assemble S K (c'.mapRange (· * ψ Y)) = c * subgroupAlgMap S K (ψ Y) = c * mapDomainRingHom K m Y = 0`

where `ψ = mapDomainRingHom K m.rangeRestrict : K[H] →+* K[S]` and the second equality is the
factorisation of `mapDomainRingHom K m` through the injective surjection
`m.rangeRestrict : H →* m.range`.  Injectivity of `assemble` (`sum_coset_eq_zero`) gives
`c' q * ψ Y = 0` for every coset `q` and every `Y ∈ Q`.

Each component `c' q ∈ K[S]` is pulled back along the (injective, surjective) `m.rangeRestrict` to
`d_q := comapDomain (m.rangeRestrict) _ (c' q) ∈ K[H]`.  Since `mapDomainRingHom K m.rangeRestrict`
is a ring homomorphism with `mapDomainRingHom K m.rangeRestrict d_q = c' q`, the relation
`c' q * ψ Y = 0` descends to `d_q * Y = 0`; by `hbase`, `d_q = 0`, whence `c' q = 0`.  All
components vanish, so `c' = 0` and `c = assemble S K c' = 0`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLyndon

open MonoidAlgebra

theorem joint_annihilator_transport {H G : Type*} [Group H] [Group G] {K : Type*} [Field K]
    (m : H →* G) (hm : Function.Injective m) (Q : Set (MonoidAlgebra K H))
    (hbase : ∀ c : MonoidAlgebra K H, (∀ Y ∈ Q, c * Y = 0) → c = 0) :
    ∀ c : MonoidAlgebra K G,
      (∀ Y ∈ Q, c * MonoidAlgebra.mapDomainRingHom K m Y = 0) → c = 0 := by
  classical
  intro c hc
  -- The canonical surjection `H →* m.range` is injective because `m` is.
  have he_inj : Function.Injective (⇑m.rangeRestrict) := by
    intro a b hab
    exact hm (by simpa using congrArg Subtype.val hab)
  have hinjψ : Function.Injective (MonoidAlgebra.mapDomainRingHom K m.rangeRestrict) :=
    MonoidAlgebra.mapDomain_injective he_inj
  have hrange : Set.range (⇑m.rangeRestrict) = Set.univ :=
    Set.range_eq_univ.mpr (MonoidHom.rangeRestrict_surjective m)
  -- `mapDomainRingHom K m` factors through `K[m.range]`.
  have hfactor : ∀ Y : MonoidAlgebra K H,
      MonoidAlgebra.mapDomainRingHom K m Y =
        Work.ORReductions.subgroupAlgMap m.range K
          (MonoidAlgebra.mapDomainRingHom K m.rangeRestrict Y) := by
    intro Y
    show MonoidAlgebra.mapDomainRingHom K m Y =
      MonoidAlgebra.mapDomainRingHom K m.range.subtype
        (MonoidAlgebra.mapDomainRingHom K m.rangeRestrict Y)
    calc MonoidAlgebra.mapDomainRingHom K m Y
        = MonoidAlgebra.mapDomainRingHom K (m.range.subtype.comp m.rangeRestrict) Y := by
            rw [MonoidHom.subtype_comp_rangeRestrict]
      _ = MonoidAlgebra.mapDomainRingHom K m.range.subtype
            (MonoidAlgebra.mapDomainRingHom K m.rangeRestrict Y) := by
            rw [MonoidAlgebra.mapDomainRingHom_comp]; rfl
  -- Decompose `c` into its `K[m.range]`-valued coset components.
  obtain ⟨c', hc'⟩ := Work.ORReductions.SubgroupAlg.exists_assemble_eq m.range K c
  -- For every `Y ∈ Q`, the componentwise product of `c'` with `ψ Y` vanishes.
  have hmap0 : ∀ Y ∈ Q, Finsupp.mapRange
      (fun r => r * MonoidAlgebra.mapDomainRingHom K m.rangeRestrict Y)
      (by simp) c' = 0 := by
    intro Y hY
    apply Work.ORReductions.SubgroupAlg.sum_coset_eq_zero m.range K
    rw [← Work.ORReductions.SubgroupAlg.assemble_apply,
        Work.ORReductions.SubgroupAlg.assemble_mapRange_mul, hc', ← hfactor Y]
    exact hc Y hY
  -- Extracted components: `c' q * ψ Y = 0` for all `q` and all `Y ∈ Q`.
  have hcomp : ∀ (q : G ⧸ m.range) (Y : MonoidAlgebra K H), Y ∈ Q →
      c' q * MonoidAlgebra.mapDomainRingHom K m.rangeRestrict Y = 0 := by
    intro q Y hY
    have h := congrArg (fun z : G ⧸ m.range →₀ MonoidAlgebra K m.range => z q) (hmap0 Y hY)
    simpa only [Finsupp.mapRange_apply, Finsupp.zero_apply] using h
  -- Pull each component back to `K[H]` and apply `hbase`.
  have hkey : ∀ q : G ⧸ m.range, c' q = 0 := by
    intro q
    have hmapd : MonoidAlgebra.mapDomainRingHom K m.rangeRestrict
        (MonoidAlgebra.comapDomain (⇑m.rangeRestrict) he_inj (c' q)) = c' q := by
      rw [MonoidAlgebra.mapDomainRingHom_apply]
      exact MonoidAlgebra.mapDomain_comapDomain (f := (⇑m.rangeRestrict)) (x := c' q)
        (by rw [hrange]; exact Set.subset_univ _) he_inj
    have hdY : ∀ Y ∈ Q,
        MonoidAlgebra.comapDomain (⇑m.rangeRestrict) he_inj (c' q) * Y = 0 := by
      intro Y hY
      refine hinjψ ?_
      rw [map_mul, hmapd, map_zero]
      exact hcomp q Y hY
    rw [← hmapd, hbase _ hdY, map_zero]
  have hc'0 : c' = 0 := Finsupp.ext fun q => by rw [hkey q, Finsupp.zero_apply]
  rw [← hc', hc'0, map_zero]

end Work.ORLyndon
