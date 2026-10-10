import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.Work.HilbertSymbolGeneral.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Hilbert reciprocity for quadratic extensions of number fields

The target `NK.NUV2.LC.HilbertReciprocityTwo`: for a quadratic extension `L / K` of number fields
and `x ∈ Kˣ`, the set of places of `K` at which `x` fails to be a local norm is finite of *even*
cardinality.

## The argument

Write `N_v ≤ K_vˣ` for the local norm subgroup at a place `v` (the supremum of the local norm
ranges over the places of `L` above `v`), and call `S(x) = {v | x_v ∉ N_v}` the *bad set* of `x`.
Two proved arithmetic inputs are used:

* `NK.CFTLib.HilbertReciprocityOnePlace` ("one place omitted"): `S(x)` is never a singleton;
* the norm index theorem `NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic`: for cyclic `L/K` the
  norm class subgroup has index `[L : K]`, hence the subgroup `𝕀^N` of idèles that are local
  norms at every place satisfies `[𝕀_K : 𝕀^N · Kˣ] ∣ [L : K]`.

From these two a group-theoretic argument gives the evenness.  Indeed in the quotient
`Q := 𝕀_K ⧸ (𝕀^N · Kˣ)` — of order dividing `[L : K]`, hence of order two in the quadratic case —
the class of a "one-place bad idèle" at a place `v` with `N_v ≠ ⊤` is not `1` (otherwise the
one-place statement would produce a singleton bad set), so two such idèles at places `v ≠ w` have
the *same* class.  Passing to a representative in `Kˣ` shows:

  for all `v ≠ w` with `N_v ≠ ⊤ ≠ N_w` there is `k ∈ Kˣ` with bad set `S(k) = {v, w}`.

Since `S(xy) = S(x) Δ S(y)` (the local norm condition is a subgroup condition, so the bad indicator
is a character), the sets `{v, w}` generate all *even* subsets, while no odd subset can occur: an
odd bad set of size `≥ 3` can be shortened by two by multiplying with such a `k`, and size one is
excluded by the one-place statement.  Hence `S(x)` is even.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace Work.HilbertSymbolGeneral

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## The local norm subgroup has index `1` or `2` -/

/-- In the quadratic case every local norm subgroup has index dividing `2`: it is the kernel of a
homomorphism to the two-element group `Gal(L/K)`. -/
theorem localNormSubgroup_index_dvd_two (h2 : Nat.card (L ≃ₐ[K] L) = 2) (v : Place K) :
    (NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v).index ∣ 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hcyc : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card (p := 2) h2
  obtain ⟨F, hF⟩ : ∃ F : (Place.localField K v)ˣ →* (L ≃ₐ[K] L),
      F.ker = NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v := by
    cases v with
    | inl w =>
      obtain ⟨F, hF⟩ := NK.CFTLib.IdeleHasse.exists_localMap_ofInfinite (K := K) (L := L) hcyc w
      exact ⟨F, hF⟩
    | inr Q =>
      obtain ⟨F, hF, _⟩ := NK.CFTLib.IdeleHasse.exists_localMap_ofFinite (K := K) (L := L) hcyc Q
      exact ⟨F, hF⟩
  rw [← hF, Subgroup.index_ker]
  have h := Subgroup.card_subgroup_dvd_card F.range
  rwa [h2] at h

/-- The image of `x` in the completion at `v` is multiplicative in `x`. -/
@[simp] theorem localImageAt_mul (v : Place K) (x y : Kˣ) :
    NK.CFTLib.IdeleHasse.localImageAt v (x * y) =
      NK.CFTLib.IdeleHasse.localImageAt v x * NK.CFTLib.IdeleHasse.localImageAt v y :=
  map_mul (NK.CFTLib.localImageHom v) x y

/-- **The bad indicator is a character.**  In a group with a subgroup `N` of index `2`, the
indicator of the non-trivial coset is additive: membership of a product is the exclusive or of the
memberships of the factors. -/
theorem not_mem_mul_iff_of_index_two {G : Type*} [Group G] {N : Subgroup G} (h : N.index = 2)
    (a b : G) : (a * b ∉ N) ↔ (a ∉ N ∧ b ∈ N) ∨ (a ∈ N ∧ b ∉ N) := by
  rw [Subgroup.mul_mem_iff_of_index_two h]
  by_cases ha : a ∈ N <;> by_cases hb : b ∈ N <;> simp [ha, hb]

/-- The pointwise form of the multiplicativity of the bad set. -/
theorem notMem_bad_of_mul (h2 : Nat.card (L ≃ₐ[K] L) = 2) (x y : Kˣ) (v : Place K) :
    (NK.CFTLib.IdeleHasse.localImageAt v (x * y) ∉
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v) ↔
      (NK.CFTLib.IdeleHasse.localImageAt v x ∉
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v ∧
        NK.CFTLib.IdeleHasse.localImageAt v y ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v) ∨
      (NK.CFTLib.IdeleHasse.localImageAt v y ∉
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v ∧
        NK.CFTLib.IdeleHasse.localImageAt v x ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v) := by
  rw [localImageAt_mul]
  rcases (Nat.dvd_prime Nat.prime_two).mp (localNormSubgroup_index_dvd_two h2 v) with h1 | h1
  · rw [Subgroup.index_eq_one.mp h1]
    simp
  · rw [not_mem_mul_iff_of_index_two h1]
    tauto

/-! ## Finiteness of the bad set -/

/-- The bad set of `x` is finite: away from the archimedean places, the places at which `x` is not
a local unit and the places at which `L/K` is ramified, a local unit of an unramified local
extension is a local norm. -/
theorem finite_badSetSubgroup (x : Kˣ) : (badSetSubgroup K L x).Finite := by
  classical
  have hInf : ({v : Place K | Place.IsInfinite v} : Set (Place K)).Finite := by
    refine (Finset.finite_toSet (Finset.univ.image (Place.ofInfinite (K := K)))).subset ?_
    intro v hv
    obtain ⟨w, rfl⟩ := Place.isInfinite_iff.mp hv
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ w))
  have hNu : ({v : Place K | (Idele.principalIdele K x) v ∉ Place.localUnits K v}
      : Set (Place K)).Finite :=
    Filter.eventually_cofinite.mp (Idele.principalIdele K x).2
  have hRam : ({v : Place K | ∃ q : HeightOneSpectrum (𝓞 L),
      q.asIdeal.ramificationIdx (𝓞 K) ≠ 1 ∧
        NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L (Place.ofFinite q) = v}
        : Set (Place K)).Finite := by
    have hq := Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one (K := K) (L := L)
    refine (hq.image (fun q : HeightOneSpectrum (𝓞 L) =>
      NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L (Place.ofFinite q))).subset ?_
    rintro v ⟨q, hqe, hqeq⟩
    exact ⟨q, hqe, hqeq⟩
  refine Set.Finite.subset (hInf.union (hNu.union hRam)) ?_
  rintro v (hv : NK.CFTLib.IdeleHasse.localImageAt v x ∉
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v)
  by_contra hnot
  simp only [Set.mem_union, Set.mem_ofPred_eq] at hnot
  push Not at hnot
  obtain ⟨h1, h2, h3⟩ := hnot
  obtain ⟨Q, rfl⟩ := Place.isFinite_iff.mp h1
  have hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q := by
    intro q hq
    by_contra hqe
    exact h3 q hqe
      (NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder_eq_of_liesOver
        (Place.liesOver_ofFinite hq))
  have h2' : NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) x ∈
      Place.localUnits K (Place.ofFinite Q) := by
    have hEq : (Idele.principalIdele K x) (Place.ofFinite Q) =
        NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) x :=
      Idele.principalIdele_apply x (Place.ofFinite Q)
    rw [← hEq]
    exact h2
  exact hv (NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified Q hunr h2')

/-- **The bad set is multiplicative**: `S(xy) = S(x) Δ S(y)`. -/
theorem badSet_mul (h2 : Nat.card (L ≃ₐ[K] L) = 2) (x y : Kˣ) :
    badSetSubgroup K L (x * y) =
      symmDiff (badSetSubgroup K L x) (badSetSubgroup K L y) := by
  ext v
  rw [Set.mem_symmDiff, badSetSubgroup, badSetSubgroup, badSetSubgroup,
    Set.mem_ofPred_eq, Set.mem_ofPred_eq, Set.mem_ofPred_eq, not_not, not_not]
  exact notMem_bad_of_mul h2 x y v

/-- **The one-place statement**: the bad set is never a singleton. -/
theorem badSet_ne_singleton (h2 : Nat.card (L ≃ₐ[K] L) = 2) (x : Kˣ) (v : Place K) :
    badSetSubgroup K L x ≠ {v} := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hcyc : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card (p := 2) h2
  have hloc : ∀ u : Place K, u ≠ v →
      NK.CFTLib.localImageHom u x ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) u := by
    intro u hu
    by_contra hbad
    have hmem : u ∈ badSetSubgroup K L x := by
      rw [badSetSubgroup, Set.mem_ofPred_eq]
      simpa only [NK.CFTLib.IdeleHasse.localImageAt, NK.CFTLib.localImageHom] using hbad
    rw [h] at hmem
    exact hu (Set.mem_singleton_iff.mp hmem)
  have hv := NK.CFTLib.hilbertReciprocity_onePlace_aux (K := K) (L := L) x v hloc
  have hnot : v ∉ badSetSubgroup K L x := by
    rw [badSetSubgroup, Set.mem_ofPred_eq]
    exact fun hc => hc hv
  rw [h] at hnot
  exact hnot (Set.mem_singleton_iff.mpr rfl)

/-! ## The norm index bound -/

/-- The index of `𝕀^N · Kˣ` divides `[L : K]`: it is bounded by the index of the norm class
subgroup, which is `[L : K]` by the norm index theorem. -/
theorem localNormIdeles_index_dvd (h2 : Nat.card (L ≃ₐ[K] L) = 2) :
    (localNormIdeles K L ⊔ Idele.principalSubgroup K).index ∣ Nat.card (L ≃ₐ[K] L) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hcyc : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card (p := 2) h2
  have hidx : (Idele.normClassSubgroup K L).index = Nat.card (L ≃ₐ[K] L) := by
    rw [NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic (K := K) (L := L),
      IsGalois.card_aut_eq_finrank K L]
  rw [← hidx]
  have hmap : ((localNormIdeles K L ⊔ Idele.principalSubgroup K).map
      (QuotientGroup.mk' (Idele.principalSubgroup K))).index =
      (localNormIdeles K L ⊔ Idele.principalSubgroup K).index :=
    Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact le_sup_right)
  rw [← hmap]
  refine Subgroup.index_dvd_of_le ?_
  intro z hz
  obtain ⟨y, hy⟩ := Idele.mem_normClassSubgroup.mp hz
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L y
  rw [IdeleClassGroup.normClassHom_mk] at hy
  rw [← hy]
  exact Subgroup.mem_map.mpr ⟨Idele.normIdeleHom K L x,
    Subgroup.mem_sup_left (mem_localNormIdeles.mpr
      (fun v => NK.CFTLib.IdeleHasse.normIdeleFun_mem_localNormSubgroup x v)), rfl⟩

/-! ## The sets `{v, w}` are bad sets -/

/-- For a place `u` at which the local norm subgroup is proper, a one-place idèle with a component
outside `N_u` is not a local norm everywhere times a principal idèle: otherwise (by the local
subgroup structure) the bad set of the principal idèle would be the singleton `{u}`. -/
theorem onePlace_not_mem_sup (h2 : Nat.card (L ≃ₐ[K] L) = 2)
    {u : Place K} {c : (Place.localField K u)ˣ}
    (hc : c ∉ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) u) :
    NK.HassePrinciple.onePlace u c ∉
      localNormIdeles K L ⊔ Idele.principalSubgroup K := by
  intro hmem
  obtain ⟨y, hy, p, hp, hyp⟩ := Subgroup.mem_sup.mp hmem
  obtain ⟨k, rfl⟩ := Idele.mem_principalSubgroup.mp hp
  have hyz : ∀ z : Place K, y z ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) z :=
    fun z => mem_localNormIdeles.mp hy z
  -- the local membership of `k` agrees with that of the one-place idèle
  have hiff : ∀ z : Place K,
      (NK.CFTLib.IdeleHasse.localImageAt z k ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) z) ↔
        ((NK.HassePrinciple.onePlace u c) z ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) z) := by
    intro z
    have h1 : y z * (Idele.principalIdele K k) z = (NK.HassePrinciple.onePlace u c) z := by
      have h2' := congrArg (fun t : Idele K => t z) hyp
      simpa using h2'
    have hloc : (Idele.principalIdele K k) z = NK.CFTLib.IdeleHasse.localImageAt z k :=
      Idele.principalIdele_apply k z
    rw [← hloc, ← h1]
    exact (Subgroup.mul_mem_cancel_left _ (hyz z)).symm
  have hbad : badSetSubgroup K L k = {u} := by
    ext z
    rw [Set.mem_singleton_iff, badSetSubgroup, Set.mem_ofPred_eq, not_congr (hiff z)]
    by_cases hzu : z = u
    · rw [hzu, NK.HassePrinciple.onePlace_apply_self]
      simp [hc]
    · rw [NK.HassePrinciple.onePlace_apply_ne hzu]
      simp [hzu]
  exact badSet_ne_singleton h2 k u hbad

/-- **The bad sets `{v, w}` are realised.**  For two distinct places at which the local norm
subgroup is proper there is `k ∈ Kˣ` whose bad set is exactly `{v, w}`. -/
theorem exists_badSet_pair (h2 : Nat.card (L ≃ₐ[K] L) = 2) {v w : Place K} (hvw : v ≠ w)
    (hv : NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v ≠ ⊤)
    (hw : NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) w ≠ ⊤) :
    ∃ k : Kˣ, badSetSubgroup K L k = {v, w} := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : (Place.localField K v)ˣ,
      a ∉ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hv ((Subgroup.eq_top_iff' _).mpr h)
  obtain ⟨b, hb⟩ : ∃ b : (Place.localField K w)ˣ,
      b ∉ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) w := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hw ((Subgroup.eq_top_iff' _).mpr h)
  have hyv := onePlace_not_mem_sup (K := K) (L := L) h2 ha
  have hyw := onePlace_not_mem_sup (K := K) (L := L) h2 hb
  have hdiv := localNormIdeles_index_dvd (K := K) (L := L) h2
  have hne : (localNormIdeles K L ⊔ Idele.principalSubgroup K).index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one.mp h1] at hyv
    exact hyv (Subgroup.mem_top _)
  have hidx : (localNormIdeles K L ⊔ Idele.principalSubgroup K).index = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (h2 ▸ hdiv) with h | h
    · exact absurd h hne
    · exact h
  have hmem : NK.HassePrinciple.onePlace v a * NK.HassePrinciple.onePlace w b ∈
      localNormIdeles K L ⊔ Idele.principalSubgroup K :=
    (Subgroup.mul_mem_iff_of_index_two hidx).mpr
      ⟨fun hc => absurd hc hyv, fun hc => absurd hc hyw⟩
  obtain ⟨y, hy, p, hp, hyp⟩ := Subgroup.mem_sup.mp hmem
  obtain ⟨k, rfl⟩ := Idele.mem_principalSubgroup.mp hp
  have hyz : ∀ z : Place K, y z ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) z :=
    fun z => mem_localNormIdeles.mp hy z
  have hiff : ∀ z : Place K,
      (NK.CFTLib.IdeleHasse.localImageAt z k ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) z) ↔
        ((NK.HassePrinciple.onePlace v a * NK.HassePrinciple.onePlace w b) z ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) z) := by
    intro z
    have h1 : y z * (Idele.principalIdele K k) z =
        (NK.HassePrinciple.onePlace v a * NK.HassePrinciple.onePlace w b) z := by
      have h2' := congrArg (fun t : Idele K => t z) hyp
      simpa using h2'
    have hloc : (Idele.principalIdele K k) z = NK.CFTLib.IdeleHasse.localImageAt z k :=
      Idele.principalIdele_apply k z
    rw [← hloc, ← h1]
    exact (Subgroup.mul_mem_cancel_left _ (hyz z)).symm
  refine ⟨k, ?_⟩
  ext z
  rw [badSetSubgroup, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    not_congr (hiff z)]
  have hcomp : (NK.HassePrinciple.onePlace v a * NK.HassePrinciple.onePlace w b) z =
      (NK.HassePrinciple.onePlace v a) z * (NK.HassePrinciple.onePlace w b) z := rfl
  rw [hcomp]
  by_cases hzv : z = v
  · rw [hzv, NK.HassePrinciple.onePlace_apply_self, NK.HassePrinciple.onePlace_apply_ne hvw,
      mul_one]
    simp [ha]
  · by_cases hzw : z = w
    · rw [hzw, NK.HassePrinciple.onePlace_apply_self,
        NK.HassePrinciple.onePlace_apply_ne (Ne.symm hvw), one_mul]
      simp [hb]
    · rw [NK.HassePrinciple.onePlace_apply_ne hzv, NK.HassePrinciple.onePlace_apply_ne hzw,
        mul_one]
      simp [hzv, hzw]

/-! ## The evenness -/

/-- The cardinality of the symmetric difference with a two-element subset contained in it drops by
two. -/
theorem ncard_symmDiff_pair {α : Type*} {s : Set α} {v w : α} (hs : s.Finite) (hv : v ∈ s)
    (hw : w ∈ s) (hvw : v ≠ w) : (symmDiff s {v, w}).ncard = s.ncard - 2 := by
  have hsub : ({v, w} : Set α) ⊆ s := by
    intro z hz
    rcases hz with rfl | rfl
    · exact hv
    · exact hw
  have hsd : symmDiff s {v, w} = s \ {v, w} := by
    rw [symmDiff_def]
    ext z
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · rintro (⟨hz, hz'⟩ | ⟨hz, hz'⟩)
      · exact ⟨hz, hz'⟩
      · exact absurd (hsub hz) hz'
    · rintro ⟨hz, hz'⟩
      exact Or.inl ⟨hz, hz'⟩
  rw [hsd, Set.ncard_sdiff hsub, Set.ncard_pair hvw]

/-- **The bad set has even cardinality.** -/
theorem badSet_ncard_even (h2 : Nat.card (L ≃ₐ[K] L) = 2) (x : Kˣ) :
    Even (badSetSubgroup K L x).ncard := by
  classical
  suffices key : ∀ n : ℕ, ∀ x : Kˣ, (badSetSubgroup K L x).ncard = n → Even n by
    exact key _ x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx
    by_cases heven : Even n
    · exact heven
    · have hodd : Odd n := Nat.not_even_iff_odd.mp heven
      rcases Nat.lt_or_ge n 2 with hlt | hge
      · obtain ⟨j, hj⟩ := hodd
        have hn1 : n = 1 := by omega
        obtain ⟨v, hv⟩ := Set.ncard_eq_one.mp (by rw [hx, hn1])
        exact absurd hv (badSet_ne_singleton h2 x v)
      · -- `n ≥ 2` and `n` odd, so `n ≥ 3`: shorten the bad set by two
        have hcard : 1 < (badSetSubgroup K L x).ncard := by omega
        obtain ⟨v, hv, w, hw, hvw⟩ :
            ∃ v ∈ badSetSubgroup K L x, ∃ w ∈ badSetSubgroup K L x, v ≠ w := by
          by_contra h
          push Not at h
          have hle : (badSetSubgroup K L x).ncard ≤ 1 := by
            rcases Set.eq_empty_or_nonempty (badSetSubgroup K L x) with he | ⟨p, hp⟩
            · rw [he]
              simp
            · have hsingle : badSetSubgroup K L x = {p} := by
                ext z
                constructor
                · intro hz
                  exact Set.mem_singleton_iff.mpr (h z hz p hp)
                · intro hz
                  rw [Set.mem_singleton_iff.mp hz]
                  exact hp
              rw [hsingle, Set.ncard_singleton]
          omega
        have hv' : NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v ≠ ⊤ := by
          intro htop
          exact hv (htop ▸ Subgroup.mem_top _)
        have hw' : NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) w ≠ ⊤ := by
          intro htop
          exact hw (htop ▸ Subgroup.mem_top _)
        obtain ⟨k, hk⟩ := exists_badSet_pair h2 hvw hv' hw'
        have hfin : (badSetSubgroup K L x).Finite := finite_badSetSubgroup x
        have hcard' : (badSetSubgroup K L (x * k)).ncard = n - 2 := by
          rw [badSet_mul h2, hk, ← hx]
          exact ncard_symmDiff_pair hfin hv hw hvw
        have hrec := ih (n - 2) (by omega) (x * k) hcard'
        obtain ⟨m, hm⟩ := hrec
        obtain ⟨j, hj⟩ := hodd
        omega

/-! ## The dictionary with `IsLocalNorm` -/

/-- **The workspace's `IsLocalNorm` is membership in the local norm subgroup.** -/
theorem isLocalNorm_iff_localNormSubgroup (x : Kˣ) (v : Place K) :
    NK.NUV2.LC.IsLocalNorm K L x v ↔
      NK.CFTLib.IdeleHasse.localImageAt v x ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v := by
  cases v with
  | inl w =>
    constructor
    · rintro ⟨w', hw', hx⟩
      exact Subgroup.mem_iSup_of_mem ⟨w', hw'⟩ hx
    · intro hx
      obtain ⟨w₀, hw₀⟩ := NK.CFTLib.IdeleHasse.exists_liesOver_infinite (K := K) (L := L) w
      haveI : w₀.LiesOver w := hw₀
      by_cases hwc : w.IsComplex
      · have htop : (Place.localNormInfinite w₀ w).range = ⊤ :=
          NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_complex_complex hwc
            (InfinitePlace.LiesOver.isComplex_of_isComplex_under w₀ hwc)
        have hsub : NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
            (Place.ofInfinite w) = (Place.localNormInfinite w₀ w).range := by
          rw [NK.CFTLib.IdeleHasse.localNormSubgroup_eq_top_of_range_top htop, ← htop]
        rw [hsub] at hx
        exact ⟨w₀, hw₀, hx⟩
      · have hwr : w.IsReal := InfinitePlace.not_isComplex_iff_isReal.mp hwc
        by_cases hre : ∃ w' : InfinitePlace L, w'.LiesOver w ∧ w'.IsReal
        · obtain ⟨w₁, hw₁, hw₁R⟩ := hre
          haveI : w₁.LiesOver w := hw₁
          have htop : (Place.localNormInfinite w₁ w).range = ⊤ :=
            NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_real_real hwr hw₁R
          have hsub : NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
              (Place.ofInfinite w) = (Place.localNormInfinite w₁ w).range := by
            rw [NK.CFTLib.IdeleHasse.localNormSubgroup_eq_top_of_range_top htop, ← htop]
          rw [hsub] at hx
          exact ⟨w₁, hw₁, hx⟩
        · have hAllC : ∀ w' : InfinitePlace L, w'.LiesOver w → w'.IsComplex := by
            intro w' hw'
            by_contra h
            exact hre ⟨w', hw', InfinitePlace.not_isComplex_iff_isReal.mp h⟩
          have hsub : NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
              (Place.ofInfinite w) = (Place.localNormInfinite w₀ w).range := by
            rw [NK.CFTLib.IdeleHasse.localNormSubgroup_ofInfinite]
            refine le_antisymm (iSup_le fun w' => ?_) (le_iSup_of_le ⟨w₀, hw₀⟩ le_rfl)
            haveI : w'.1.LiesOver w := w'.2
            rw [NK.CFTLib.IdeleHasse.range_localNormInfinite_of_real_complex (w := w)
                (w' := w'.1) hwr (hAllC w'.1 w'.2),
              NK.CFTLib.IdeleHasse.range_localNormInfinite_of_real_complex (w := w)
                (w' := w₀) hwr (hAllC w₀ hw₀)]
          rw [hsub] at hx
          exact ⟨w₀, hw₀, hx⟩
  | inr Q =>
    constructor
    · rintro ⟨q, hq, hx⟩
      exact Subgroup.mem_iSup_of_mem ⟨q, hq⟩ hx
    · intro hx
      obtain ⟨q₀, hq₀⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) Q
      have hsub : NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
          (Place.ofFinite Q) = (Place.localNormFinite q₀ Q hq₀).range := by
        rw [NK.CFTLib.IdeleHasse.localNormSubgroup_ofFinite]
        refine le_antisymm (iSup_le fun q => ?_) (le_iSup_of_le ⟨q₀, hq₀⟩ le_rfl)
        rw [NK.CFTLib.IdeleHasse.range_localNormFinite_eq_of_liesOver Q q.1 q₀ q.2 hq₀]
      rw [hsub] at hx
      exact ⟨q₀, hq₀, hx⟩

/-! ## Hilbert reciprocity at `p = 2` -/

theorem hilbertReciprocityTwo : NK.NUV2.LC.HilbertReciprocityTwo := by
  intro K L _ _ _ _ _ _ _ h2 x
  refine ⟨(finite_badSetSubgroup (K := K) (L := L) x).toFinset, ?_, ?_⟩
  · intro v
    rw [Set.Finite.mem_toFinset, badSetSubgroup, Set.mem_ofPred_eq]
    exact (not_congr (isLocalNorm_iff_localNormSubgroup (K := K) (L := L) x v)).symm
  · rw [← Set.ncard_eq_toFinset_card (badSetSubgroup K L x)
      (finite_badSetSubgroup (K := K) (L := L) x)]
    exact badSet_ncard_even (K := K) (L := L) h2 x

end Work.HilbertSymbolGeneral
