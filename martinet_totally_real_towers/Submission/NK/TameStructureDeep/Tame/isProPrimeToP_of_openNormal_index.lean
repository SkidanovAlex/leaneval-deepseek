import Mathlib
import Submission.NK.LocalTame.Basic
import Submission.NK.TameStructureDeep.Support.isProP_of_openNormal_index_prime

set_option linter.style.haveILetI false

open scoped Pointwise

namespace NK.TameStructureDeep.Tame

/-!
# Pro-prime-to-`p`-ness tested on the open normal subgroups

Let `G` be a compact, Hausdorff, totally disconnected topological group (a profinite group) in
which every **open** normal subgroup has index coprime to the prime `p`.  Then `G` is
prime-to-`p` in the finite-quotient sense `NK.LocalTame.IsProPrimeToP p G`: **every** normal
subgroup of finite index has index coprime to `p`.

The mathematics is the same as in
`Submission/Work/TameStructureDeep/Support/isProP_of_openNormal_index_prime.lean`, only simpler:
the hypothesis "every open normal subgroup has index coprime to `p`" already *is* the statement
that the finite quotients `G ⧸ U` have order coprime to `p`, so the `p`-th power map is a
bijection on each of them.  Hence

* the `p`-th power map `G → G` has image meeting every coset of every open normal subgroup,
  i.e. it is dense; it is also compact (continuous image of a compact space) hence closed, so it
  is surjective — `G` is `p`-divisible;
* consequently every finite quotient `G ⧸ N` is `p`-divisible too, and a finite group of order
  divisible by the prime `p` never is (Cauchy's theorem).

So no finite-index normal subgroup has index divisible by `p`, i.e. `G` is pro-prime-to-`p`.

## Contents

* `forall_exists_pow_eq_of_coprime_openNormal_index` — pro-prime-to-`p`-ness of the open normal
  subgroups makes `G` `p`-divisible.
* `isProPrimeToP_of_openNormal_index` — the headline.
-/

/-- **A group all of whose open normal subgroups have index coprime to the prime `p` is
`p`-divisible**: every element is a `p`-th power.

The `p`-th power map `f : G → G` has compact image (so it is closed, `G` being Hausdorff) and its
image meets every coset `gU` of every open normal subgroup `U` — because in the finite group
`G ⧸ U`, whose order `[G : U]` is coprime to `p`, the `p`-th power map is a bijection — so the
image is dense.  A closed dense subset is everything. -/
theorem forall_exists_pow_eq_of_coprime_openNormal_index {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h : ∀ U : OpenNormalSubgroup G, Nat.Coprime ℓ U.toSubgroup.index) :
    ∀ x : G, ∃ y : G, y ^ ℓ = x := by
  have hclosed : IsClosed (Set.range fun y : G => y ^ ℓ) :=
    (isCompact_range (continuous_pow ℓ)).isClosed
  -- the image of the `ℓ`-th power map meets every coset of every open normal subgroup
  have key : ∀ (U : OpenNormalSubgroup G) (g : G),
      (Set.range (fun y : G => y ^ ℓ) ∩ (g • ((U : Subgroup G) : Set G))).Nonempty := by
    intro U g
    haveI hfin : Finite (G ⧸ (U : Subgroup G)) :=
      Subgroup.quotient_finite_of_isOpen (U : Subgroup G) U.isOpen
    have hcop : (Nat.card (G ⧸ (U : Subgroup G))).Coprime ℓ := by
      rw [← Subgroup.index_eq_card]
      exact (h U).symm
    have hsurj : Function.Surjective (fun w : G ⧸ (U : Subgroup G) => w ^ ℓ) :=
      (hcop.pow_left_bijective).2
    obtain ⟨z, hz⟩ := hsurj (QuotientGroup.mk' (U : Subgroup G) g)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (U : Subgroup G) z
    refine ⟨y ^ ℓ, ⟨y, rfl⟩, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
    have hz' : QuotientGroup.mk' (U : Subgroup G) (y ^ ℓ) =
        QuotientGroup.mk' (U : Subgroup G) g := by
      rw [map_pow]; exact hz
    have hmem : (y ^ ℓ)⁻¹ * g ∈ (U : Subgroup G) :=
      QuotientGroup.eq.mp (by simpa only [QuotientGroup.mk'_apply] using hz')
    have hinv := Subgroup.inv_mem _ hmem
    simpa [mul_inv_rev, inv_inv] using hinv
  -- so the image is dense
  have hdense : Dense (Set.range fun y : G => y ^ ℓ) := by
    rw [dense_iff_inter_open]
    intro O hO hOne
    obtain ⟨x₀, hx₀⟩ := hOne
    -- translate `O` to an open neighbourhood of `1` and take an open normal subgroup inside it
    have hWopen : IsOpen ((fun z : G => x₀⁻¹ * z) '' O) :=
      isOpenMap_mul_left x₀⁻¹ O hO
    have h1W : (1 : G) ∈ (fun z : G => x₀⁻¹ * z) '' O :=
      ⟨x₀, hx₀, by simp⟩
    obtain ⟨U, hU⟩ :=
      ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWopen h1W
    have hsub : x₀ • ((U : Subgroup G) : Set G) ⊆ O := by
      intro z hz
      rw [Set.mem_smul_set] at hz
      obtain ⟨u, hu, rfl⟩ := hz
      obtain ⟨o, ho, hoo⟩ := hU hu
      have huo : x₀⁻¹ * o = u := hoo
      have : x₀ • u = o := by
        rw [smul_eq_mul, ← huo, ← mul_assoc, mul_inv_cancel, one_mul]
      rw [this]
      exact ho
    obtain ⟨z, hz1, hz2⟩ := key U x₀
    exact ⟨z, hsub hz2, hz1⟩
  have hrange : Set.range (fun y : G => y ^ ℓ) = Set.univ := by
    rw [← hclosed.closure_eq, hdense.closure_eq]
  intro x
  exact Set.mem_range.mp (hrange.symm ▸ Set.mem_univ x)

/-- **A compact totally disconnected group all of whose open normal subgroups have index coprime
to the prime `p` is pro-prime-to-`p`** in the finite-quotient sense
`NK.LocalTame.IsProPrimeToP p G`: every normal subgroup of finite index has index coprime to
`p`. -/
theorem isProPrimeToP_of_openNormal_index {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {p : ℕ}
    (hp : p.Prime) (h : ∀ U : OpenNormalSubgroup G, Nat.Coprime p U.toSubgroup.index) :
    NK.LocalTame.IsProPrimeToP p G := by
  intro N hN hfi
  haveI := hN
  haveI := hfi
  refine hp.coprime_iff_not_dvd.mpr fun hpdvd => ?_
  -- every element of `G` is a `p`-th power, hence so is every element of the quotient `G ⧸ N`
  have hdiv : ∀ z : G ⧸ N, ∃ w : G ⧸ N, w ^ p = z := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
    obtain ⟨y, hy⟩ := forall_exists_pow_eq_of_coprime_openNormal_index hp h x
    exact ⟨QuotientGroup.mk' N y, by rw [← map_pow, hy]⟩
  have hcard : Nat.card (G ⧸ N) = N.index := (Subgroup.index_eq_card N).symm
  exact NK.TameStructureDeep.Support.not_dvd_card_of_forall_pow_eq hp hdiv (by rw [hcard]; exact hpdvd)

end NK.TameStructureDeep.Tame
