import Mathlib
import Submission.NK.TameStructureDeep.Defs
import Submission.NK.LocalTame.Basic
import Submission.NK.TameStructureDeep.Support.eq_one_of_hom_zmod_of_openNormal_index
import Submission.NK.TameStructureDeep.Support.commutative_topologicalClosure_zpowers

set_option linter.style.haveILetI false

open scoped Pointwise

namespace NK.TameStructureDeep.Support

/-!
# Pro-`p`-ness tested on the open normal subgroups

Let `G` be a compact, Hausdorff, totally disconnected topological group (a profinite group) in
which every **open** normal subgroup has index a power of the prime `p`.  Then `G` is pro-`p` in
the finite-quotient sense `NK.LocalTame.IsProP p G`: **every** normal subgroup of finite index
has `p`-power index.

This is *not* immediate from "a finite index subgroup of a profinite group is open" — that
statement is false in general (for `G = ∏ₙ ℤ/2` a non-continuous linear functional `G → ℤ/2`
has a dense kernel of index `2`).  What makes the lemma true is a different, equally classical
fact:

> **A pro-`p` group is `ℓ`-divisible for every prime `ℓ ≠ p`**: the `ℓ`-th power map is a
> bijection (it is a bijection on every finite quotient, `|G ⧸ U| = p ^ k` with
> `gcd(p ^ k, ℓ) = 1`, and `G` is the inverse limit of these quotients).

Hence every quotient of `G` is `ℓ`-divisible, while a *finite* group whose order is divisible by
the prime `ℓ` never is (Cauchy's theorem produces an element of order `ℓ`, so the `ℓ`-th power map
is not injective, hence not surjective).  So no prime `ℓ ≠ p` divides `[G : N]`, and `[G : N]` is a
power of `p`.

## Contents

* `not_dvd_card_of_forall_pow_eq` — a finite group whose order is divisible by the prime `ℓ` is not
  `ℓ`-divisible.
* `forall_exists_pow_eq_of_openNormal_index` — pro-`p`-ness of the open normal subgroups makes `G`
  `ℓ`-divisible for `ℓ ≠ p`.
* `isProP_of_openNormal_index_prime` — the headline.
-/

/-- **A finite group of order divisible by a prime `ℓ` is not `ℓ`-divisible.**

If every element of the finite group `H` were an `ℓ`-th power, the `ℓ`-th power map `H → H` would
be surjective, hence injective.  But `ℓ ∣ Nat.card H` and `ℓ` prime give (Cauchy's theorem) an
element `x` of order `ℓ`, and `x ^ ℓ = 1 = 1 ^ ℓ`, so injectivity forces `x = 1`, absurd. -/
theorem not_dvd_card_of_forall_pow_eq {H : Type*} [Group H] [Finite H] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hdiv : ∀ z : H, ∃ w : H, w ^ ℓ = z) : ¬ ℓ ∣ Nat.card H := by
  intro hdvd
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  have hinj : Function.Injective (fun z : H => z ^ ℓ) :=
    (Finite.injective_iff_surjective).mpr fun z => hdiv z
  have hx1 : x = 1 :=
    hinj (show x ^ ℓ = 1 ^ ℓ from by rw [one_pow, ← hx]; exact pow_orderOf_eq_one x)
  exact hℓ.ne_one (hx ▸ (orderOf_eq_one_iff.mpr hx1))

/-- **A group in which all open normal subgroups have `p`-power index is `ℓ`-divisible**
for every prime `ℓ ≠ p`: every element is an `ℓ`-th power.

The `ℓ`-th power map `f : G → G` has compact image (so it is closed, `G` being Hausdorff) and its
image meets every coset `gU` of every open normal subgroup `U` — because in the finite group
`G ⧸ U` of order `p ^ k` the `ℓ`-th power map is a bijection (`gcd(p ^ k, ℓ) = 1`) — so the image
is dense.  A closed dense subset is everything. -/
theorem forall_exists_pow_eq_of_openNormal_index {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {p ℓ : ℕ}
    (hp : p.Prime) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (h : ∀ U : OpenNormalSubgroup G, ∃ k : ℕ, U.toSubgroup.index = p ^ k) :
    ∀ x : G, ∃ y : G, y ^ ℓ = x := by
  have hclosed : IsClosed (Set.range fun y : G => y ^ ℓ) :=
    (isCompact_range (continuous_pow ℓ)).isClosed
  -- the image of the `ℓ`-th power map meets every coset of every open normal subgroup
  have key : ∀ (U : OpenNormalSubgroup G) (g : G),
      (Set.range (fun y : G => y ^ ℓ) ∩ (g • ((U : Subgroup G) : Set G))).Nonempty := by
    intro U g
    haveI hfin : Finite (G ⧸ (U : Subgroup G)) :=
      Subgroup.quotient_finite_of_isOpen (U : Subgroup G) U.isOpen
    obtain ⟨k, hk⟩ := h U
    have hcard : Nat.card (G ⧸ (U : Subgroup G)) = p ^ k := by
      rw [← Subgroup.index_eq_card]; exact hk
    have hcop : (Nat.card (G ⧸ (U : Subgroup G))).Coprime ℓ := by
      rw [hcard]
      refine (Nat.Coprime.pow_left k ?_)
      exact hp.coprime_iff_not_dvd.mpr fun hpd => by
        rcases hℓ.eq_one_or_self_of_dvd p hpd with h1 | h1
        · exact hp.ne_one h1
        · exact hℓp h1.symm
    have hsurj : Function.Surjective (fun w : G ⧸ (U : Subgroup G) => w ^ ℓ) :=
      (Nat.Coprime.pow_left_bijective hcop).2
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

/-- **A compact totally disconnected group all of whose open normal subgroups have `p`-power index
is pro-`p`** in the finite-quotient sense `NK.LocalTame.IsProP p G`: every normal subgroup of
finite index has `p`-power index. -/
theorem isProP_of_openNormal_index_prime {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {p : ℕ}
    (hp : p.Prime)
    (h : ∀ U : OpenNormalSubgroup G, ∃ k : ℕ, U.toSubgroup.index = p ^ k) :
    NK.LocalTame.IsProP p G := by
  intro N hN hfi
  haveI hNn : N.Normal := hN
  haveI hNf : N.FiniteIndex := hfi
  have hn : N.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  refine ⟨N.index.primeFactorsList.length, ?_⟩
  exact Nat.eq_prime_pow_of_unique_prime_dvd hn (fun {d} hd hdvd => by
    by_contra hdp
    -- every element of `G` is a `d`-th power, hence so is every element of the quotient `G ⧸ N`
    have hdiv : ∀ z : G ⧸ N, ∃ w : G ⧸ N, w ^ d = z := by
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
      obtain ⟨y, hy⟩ := forall_exists_pow_eq_of_openNormal_index hp hd hdp h x
      exact ⟨QuotientGroup.mk' N y, by rw [← map_pow, hy]⟩
    exact not_dvd_card_of_forall_pow_eq hd hdiv
      (by rw [← Subgroup.index_eq_card]; exact hdvd))

end NK.TameStructureDeep.Support
