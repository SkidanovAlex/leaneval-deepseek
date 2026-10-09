/-
Copyright: no copyright.
-/
import Mathlib
import Submission.NK.LocalTame.cruxCompactExpPrimeFinite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `ℓ`-Frattini subgroup of a compact group with open index-`ℓ` subgroups is open

Let `G` be a compact Hausdorff topological group, `ℓ` a prime, and suppose that every *normal*
subgroup of `G` of index `ℓ` is open.  Then the intersection `D` of *all* normal subgroups of `G`
of index `ℓ` (the "`ℓ`-Frattini subgroup", the kernel of the evaluation map of `G` into the
product of its index-`ℓ` quotients) is open.

The proof has two halves.

* **Algebra and topology of `D`.**  Each `H` of index `ℓ` is open, hence closed, so `D = ⋂ H` is
  closed.  Every such `H` contains the commutator subgroup `[G,G]` (its quotient `G ⧸ H` has
  order the prime `ℓ`, hence is cyclic, hence commutative) and every `ℓ`-th power `g ^ ℓ`.  Hence
  `D ⊇ [G,G]` and `D ⊇ G^ℓ`, so the quotient `W = G ⧸ D` is an abelian group of exponent `ℓ`
  (a `ZMod ℓ`-vector space), it is compact Hausdorff (`D` being closed, normal), and every
  subgroup of `W` of index `ℓ` is open: it is the image of `H.comap (G → G ⧸ D)` for a suitable
  index-`ℓ` normal subgroup `H ≤ G`, and the quotient map is open.

* **Finiteness.**  By `NK.LocalTame.cruxCompactExpPrimeFinite`, a compact Hausdorff abelian
  group of prime exponent `ℓ` all of whose index-`ℓ` subgroups are open is *finite*.  Hence
  `W = G ⧸ D` is finite, `D` has finite index, and a closed finite-index subgroup of a topological
  group is open.  So `D` is open.
-/

open scoped IsMulCommutative

namespace NK.LocalTame

/-- **The `ℓ`-Frattini subgroup is open.**  In a compact Hausdorff topological group in which
every normal subgroup of index a prime `ℓ` is open, the intersection of all of them is open. -/
theorem lFrattini_isOpen {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hopen : ∀ H : Subgroup G, H.index = ℓ → H.Normal → IsOpen (H : Set G)) :
    IsOpen ((⨅ (H : {H : Subgroup G // H.index = ℓ ∧ H.Normal}), (H : Subgroup G)) : Set G) := by
  have hFactPrime : Fact ℓ.Prime := ⟨hℓ⟩
  -- The `ℓ`-Frattini subgroup, as a subgroup and as a set.
  let D : Subgroup G := ⨅ (H : {H : Subgroup G // H.index = ℓ ∧ H.Normal}), (H : Subgroup G)
  have hsub : (D : Set G) = ⨅ (H : {H : Subgroup G // H.index = ℓ ∧ H.Normal}), (H : Set G) := by
    rw [show (D : Set G) =
        ↑(⨅ (H : {H : Subgroup G // H.index = ℓ ∧ H.Normal}), (H : Subgroup G)) from rfl,
      Subgroup.coe_iInf]
    rfl
  -- `D` is normal and closed.
  have hDnormal : D.Normal := by
    show (⨅ (H : {H : Subgroup G // H.index = ℓ ∧ H.Normal}), (H : Subgroup G)).Normal
    exact Subgroup.normal_iInf_normal fun H => H.2.2
  have hDn : D.Normal := hDnormal
  have hDclosed : IsClosed (D : Set G) := by
    rw [hsub]
    exact isClosed_iInter fun H => Subgroup.isClosed_of_isOpen H.1 (hopen H.1 H.2.1 H.2.2)
  have hDc : IsClosed (D : Set G) := hDclosed
  -- Every `ℓ`-th power lies in `D`.
  have hpow : ∀ g : G, g ^ ℓ ∈ D := by
    intro g
    show g ^ ℓ ∈ ⨅ (H : {H : Subgroup G // H.index = ℓ ∧ H.Normal}), (H : Subgroup G)
    rw [Subgroup.mem_iInf]
    intro H
    have hHn := H.2.2
    have h := Subgroup.pow_index_mem H.1 g
    rwa [H.2.1] at h
  -- The commutator subgroup lies in `D`.
  have hcomm : commutator G ≤ D := by
    show commutator G ≤ ⨅ (H : {H : Subgroup G // H.index = ℓ ∧ H.Normal}), (H : Subgroup G)
    rw [le_iInf_iff]
    intro H
    have hHn := H.2.2
    -- `G ⧸ H` has order the prime `ℓ`, hence is cyclic, hence commutative.
    have hcyc : IsCyclic (G ⧸ H.1) :=
      isCyclic_of_prime_card (p := ℓ) (by rw [← Subgroup.index_eq_card, H.2.1])
    have hQcomm : IsMulCommutative (G ⧸ H.1) := hcyc.isMulCommutative
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  -- So the quotient `G ⧸ D` is an abelian group of exponent `ℓ`.
  have hQcomm : IsMulCommutative (G ⧸ D) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
  have hexp : ∀ x : G ⧸ D, x ^ ℓ = 1 := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D x
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (g ^ ℓ)).mpr (hpow g)
  -- Every index-`ℓ` subgroup of `G ⧸ D` is open (it is the image of one in `G`).
  have hopenQ : ∀ H : Subgroup (G ⧸ D), H.index = ℓ → IsOpen (H : Set (G ⧸ D)) := by
    intro H hH
    have hHN : H.Normal := Subgroup.normal_of_isMulCommutative H
    let K : Subgroup G := H.comap (QuotientGroup.mk' D)
    have hKN : K.Normal := Subgroup.Normal.comap hHN (QuotientGroup.mk' D)
    have hKidx : K.index = ℓ := by
      show (H.comap (QuotientGroup.mk' D)).index = ℓ
      rw [Subgroup.index_comap_of_surjective H (QuotientGroup.mk'_surjective D), hH]
    have hKopen : IsOpen (K : Set G) := hopen K hKidx hKN
    have himg : (H : Set (G ⧸ D)) = QuotientGroup.mk' D '' (K : Set G) := by
      ext x
      constructor
      · intro hx
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D x
        exact ⟨g, hx, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact hg
    rw [himg]
    exact (QuotientGroup.isOpenMap_coe (N := D)) K hKopen
  -- The crux: such a quotient is finite.
  have hfin : Finite (G ⧸ D) := cruxCompactExpPrimeFinite hℓ hexp hopenQ
  have hFinite : Finite (G ⧸ D) := hfin
  -- Hence `D` has finite index, and being closed it is open.
  have hFinIdx : D.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient (H := D)
  have hDopen : IsOpen (D : Set G) := Subgroup.isOpen_of_isClosed_of_finiteIndex D hDclosed
  rw [← hsub]
  exact hDopen

end NK.LocalTame
