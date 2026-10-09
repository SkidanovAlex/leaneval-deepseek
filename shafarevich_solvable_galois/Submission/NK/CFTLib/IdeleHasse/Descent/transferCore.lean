import Mathlib
import Submission.NK.CFTLib.Descent.CyclicCocycle
import Submission.NK.Cohomology.capture_two_map_eq_zero_of_cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cyclic-class / transgression toolkit for the transfer step

For a finite cyclic group `G = ⟨g⟩` and a `CoeffInt`-linear representation `A` of `G`, the
*cyclic class* of a `G`-invariant element `a ∈ A` is the cohomology class of the explicit factor
system `cycFun A g hg a (γ,δ) = carry(γ,δ) • a`.

This module records the two structure theorems of the cyclic class, expressed through the
*transgression* `T(z) = ∑_{t<|G|} z(g^t, g)` of a `2`-cocycle `z`:

* `cycClass_eq_zero_iff` : the cyclic class of `a` vanishes iff `a` is a norm;
* `exists_eq_cycClass` : every class is the cyclic class of some invariant element;

together with the *functoriality on the nose* of the explicit cocycle under a group homomorphism
with a compatible generator (`cochainsMap₂_cycFun`), which is what makes the localisations and the
level changes computable.

The vanishing criterion `T(z) ∈ range(norm) ⟹ z ∈ coboundaries₂` is the theorem
`NK.Cohomology.mem_coboundaries₂_of_transgression_mem_range`; the converse direction
(coboundaries have transgression in the norm group) is `transgression_mem_range_of_mem_coboundaries`
below.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance 5000] Rep.hV1 Rep.hV2
attribute [local instance 100] AddCommGroup.toIntModule


open CategoryTheory

namespace NK.CFTLib.IdeleHasse.Descent

open NK.CFTLib.Descent (cycFun cycClass carry carry_eq_zero_or_one dlog dlog_lt pow_dlog
  card_mul_carry cycFun_mem_cocycles₂)

variable {G : Type} [Group G] [Fintype G]

/-! ## The discrete logarithm and the carry -/

/-- The discrete logarithm of a power `g ^ t`, for `t` below the order. -/
lemma dlog_pow (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) {t : ℕ}
    (ht : t < Fintype.card G) : dlog g hg (g ^ t) = t := by
  have hord : orderOf g = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  have h1 : g ^ dlog g hg (g ^ t) = g ^ t := pow_dlog g hg (g ^ t)
  have h2 := pow_eq_pow_iff_modEq.mp h1
  rw [hord] at h2
  exact Nat.ModEq.eq_of_lt_of_lt h2 (dlog_lt g hg (g ^ t)) ht

/-- The discrete logarithm of the identity is zero. -/
lemma dlog_one (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) : dlog g hg 1 = 0 := by
  have hord : orderOf g = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  have h1 : g ^ dlog g hg 1 = g ^ (0 : ℕ) := by rw [pow_dlog g hg 1, pow_zero]
  have h2 := pow_eq_pow_iff_modEq.mp h1
  rw [hord] at h2
  exact Nat.ModEq.eq_of_lt_of_lt h2 (dlog_lt g hg 1) (Fintype.card_pos)

/-- The discrete logarithm of the chosen generator is `1` in a nontrivial group. -/
lemma dlog_gen (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (hcard : 1 < Fintype.card G) :
    dlog g hg g = 1 := by
  have h := dlog_pow g hg (t := 1) hcard
  rwa [pow_one] at h

/-- The carry of the pair `(g ^ t, g)` vanishes away from the last index. -/
lemma carry_pow_gen_of_lt (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) {t : ℕ}
    (ht : t + 1 < Fintype.card G) : carry g hg (g ^ t) g = 0 := by
  have hn : (Fintype.card G : ℤ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := G)).ne'
  have h := card_mul_carry g hg (g ^ t) g
  rw [← pow_succ] at h
  rw [dlog_pow g hg (by omega), dlog_gen g hg (by omega), dlog_pow g hg ht] at h
  have h0 : (Fintype.card G : ℤ) * carry g hg (g ^ t) g = 0 := by
    rw [h, Nat.cast_add, Nat.cast_one]; ring
  exact mul_left_cancel₀ hn (by rw [h0, mul_zero])

/-- The carry of the pair `(g ^ (n-1), g)` is `1`. -/
lemma carry_pow_gen_last (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hcard : 1 < Fintype.card G) : carry g hg (g ^ (Fintype.card G - 1)) g = 1 := by
  have hn : (Fintype.card G : ℤ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := G)).ne'
  have h := card_mul_carry g hg (g ^ (Fintype.card G - 1)) g
  rw [← pow_succ] at h
  have h3 : Fintype.card G - 1 + 1 = Fintype.card G := by omega
  rw [h3, pow_card_eq_one, dlog_one, dlog_pow g hg (by omega), dlog_gen g hg hcard] at h
  have hcast : (Fintype.card G : ℤ) = ((Fintype.card G - 1 : ℕ) : ℤ) + 1 := by omega
  have h1 : (Fintype.card G : ℤ) * carry g hg (g ^ (Fintype.card G - 1)) g
      = (Fintype.card G : ℤ) * 1 := by
    rw [h, hcast]; ring
  exact mul_left_cancel₀ hn h1

/-! ## Reindexing sums over the powers of a generator -/

/-- Summation over the powers of a generator is summation over the group. -/
lemma sum_range_pow_eq_sum (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) {M : Type*}
    [AddCommMonoid M] (φ : G → M) :
    (∑ t ∈ Finset.range (Fintype.card G), φ (g ^ t)) = ∑ γ : G, φ γ := by
  classical
  have hord : orderOf g = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  have hinj : Set.InjOn (fun t : ℕ => g ^ t) ↑(Finset.range (Fintype.card G)) := by
    intro x hx y hy hxy
    have h1 : x ≡ y [MOD orderOf g] := pow_eq_pow_iff_modEq.mp hxy
    rw [hord] at h1
    exact Nat.ModEq.eq_of_lt_of_lt h1 (Finset.mem_range.mp hx) (Finset.mem_range.mp hy)
  have himg : (Finset.range (Fintype.card G)).image (fun t : ℕ => g ^ t) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj]
    exact Finset.card_range _
  have h1 : (∑ t ∈ Finset.range (Fintype.card G), φ (g ^ t))
      = ∑ γ ∈ (Finset.range (Fintype.card G)).image (fun t : ℕ => g ^ t), φ γ :=
    (Finset.sum_image (s := Finset.range (Fintype.card G)) (f := φ)
      (g := fun t : ℕ => g ^ t) hinj).symm
  rw [h1, himg]

/-- The shifted version: summation over `g ^ (t+1)` is summation over the group. -/
lemma sum_range_pow_succ_eq_sum (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) {M : Type*}
    [AddCommMonoid M] (f : G → M) :
    (∑ t ∈ Finset.range (Fintype.card G), f (g ^ (t + 1))) = ∑ γ : G, f γ := by
  have h : ∀ t : ℕ, f (g ^ (t + 1)) = (fun γ : G => f (γ * g)) (g ^ t) := by
    intro t
    rw [pow_succ]
  rw [Finset.sum_congr rfl (fun t _ => h t), sum_range_pow_eq_sum g hg (fun γ => f (γ * g))]
  exact Equiv.sum_comp (Equiv.mulRight g) f

/-! ## The transgression of the explicit cyclic cocycle -/

/-- **The transgression of the explicit cyclic cocycle is the coefficient.**  For a nontrivial
finite cyclic group `G = ⟨g⟩` and a `G`-invariant `a`, the transgression
`∑_{t<|G|} cycFun a (g^t, g)` of the explicit cyclic cocycle is `a`. -/
theorem transgression_cycFun (A : Rep NK.HassePrinciple.CoeffInt G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (a : A) (ha : ∀ γ : G, A.ρ γ a = a)
    (hcard : 1 < Fintype.card G) :
    (∑ t ∈ Finset.range (Fintype.card G), cycFun A g hg a (g ^ t, g)) = a := by
  have hn : 0 < Fintype.card G := by omega
  have hsplit : Fintype.card G = (Fintype.card G - 1) + 1 := by omega
  rw [hsplit, Finset.sum_range_succ]
  have hzero : ∀ t ∈ Finset.range (Fintype.card G - 1), cycFun A g hg a (g ^ t, g) = 0 := by
    intro t ht
    have ht' : t + 1 < Fintype.card G := by
      have := Finset.mem_range.mp ht
      omega
    show carry g hg (g ^ t) g • a = 0
    rw [carry_pow_gen_of_lt g hg ht', zero_zsmul]
  rw [Finset.sum_eq_zero hzero, zero_add]
  show carry g hg (g ^ (Fintype.card G - 1)) g • a = a
  rw [carry_pow_gen_last g hg hcard, one_zsmul]

/-! ## The transgression of a coboundary -/

/-- **A coboundary has transgression in the norm group.** -/
theorem transgression_mem_range_of_mem_coboundaries (A : Rep NK.HassePrinciple.CoeffInt G)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (y : G → A) :
    (∑ t ∈ Finset.range (Fintype.card G),
        (groupCohomology.d₁₂ A).hom y (g ^ t, g)) ∈ LinearMap.range A.ρ.norm := by
  have hterm : ∀ t : ℕ, (groupCohomology.d₁₂ A).hom y (g ^ t, g)
      = A.ρ (g ^ t) (y g) - y (g ^ (t + 1)) + y (g ^ t) := by
    intro t
    rw [groupCohomology.d₁₂_hom_apply]
    simp only [Prod.fst, Prod.snd]
    rw [← pow_succ]
  have hsum : (∑ t ∈ Finset.range (Fintype.card G),
        (groupCohomology.d₁₂ A).hom y (g ^ t, g))
      = (∑ t ∈ Finset.range (Fintype.card G), A.ρ (g ^ t) (y g))
        - (∑ t ∈ Finset.range (Fintype.card G), y (g ^ (t + 1)))
        + (∑ t ∈ Finset.range (Fintype.card G), y (g ^ t)) := by
    rw [Finset.sum_congr rfl (fun t _ => hterm t), Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hsum]
  have h1 : (∑ t ∈ Finset.range (Fintype.card G), A.ρ (g ^ t) (y g)) = A.ρ.norm (y g) := by
    rw [show A.ρ.norm (y g) = ∑ γ : G, A.ρ γ (y g) from by
      rw [Representation.norm, LinearMap.sum_apply]]
    exact sum_range_pow_eq_sum g hg (fun γ : G => A.ρ γ (y g))
  have h2 : (∑ t ∈ Finset.range (Fintype.card G), y (g ^ (t + 1)))
      = ∑ γ : G, y γ := sum_range_pow_succ_eq_sum g hg y
  have h3 : (∑ t ∈ Finset.range (Fintype.card G), y (g ^ t)) = ∑ γ : G, y γ :=
    sum_range_pow_eq_sum g hg y
  rw [h1, h2, h3]
  exact ⟨y g, by abel⟩



variable {G : Type} [Group G] [Fintype G]

/-! ## The trivial-group cases -/

variable {G : Type} [Group G] [Fintype G]

lemma subsingleton_of_card_le_one (h : Fintype.card G ≤ 1) : Subsingleton G :=
  Fintype.card_le_one_iff_subsingleton.mp h

/-- For a group of order at most one the norm endomorphism is the identity. -/
lemma norm_eq_one_of_card_le_one (A : Rep NK.HassePrinciple.CoeffInt G)
    (h : Fintype.card G ≤ 1) : A.ρ.norm = 1 := by
  haveI : Subsingleton G := subsingleton_of_card_le_one h
  ext x
  rw [show A.ρ.norm x = ∑ γ : G, A.ρ γ x from by
      rw [Representation.norm, LinearMap.sum_apply],
    Finset.sum_eq_single (1 : G)]
  · simp
  · intro b _ hb
    exact absurd (Subsingleton.elim b 1) hb
  · intro h'
    exact absurd (Finset.mem_univ (1 : G)) h'

/-- The carry of the pair `(1,1)` vanishes. -/
lemma carry_one_one (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) : carry g hg 1 1 = 0 := by
  have hn : (Fintype.card G : ℤ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := G)).ne'
  have h := card_mul_carry g hg 1 1
  simp only [dlog_one, mul_one] at h
  have h0 : (Fintype.card G : ℤ) * carry g hg 1 1 = 0 := by rw [h]; ring
  exact mul_left_cancel₀ hn (by rw [h0, mul_zero])

/-- The explicit cyclic cocycle vanishes for a group of order one. -/
lemma cycFun_eq_zero_of_card_le_one (A : Rep NK.HassePrinciple.CoeffInt G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (a : A) (h : Fintype.card G ≤ 1) :
    cycFun A g hg a = 0 := by
  haveI : Subsingleton G := subsingleton_of_card_le_one h
  funext p
  have hp : p = (1, 1) := by
    ext <;> exact Subsingleton.elim _ _
  rw [hp]
  show carry g hg 1 1 • a = (0 : A)
  rw [carry_one_one g hg, zero_zsmul]

/-- Every `2`-cochain is a coboundary for a group of order one. -/
lemma mem_coboundaries₂_of_card_le_one (A : Rep NK.HassePrinciple.CoeffInt G)
    (z : G × G → A) (h : Fintype.card G ≤ 1) :
    z ∈ groupCohomology.coboundaries₂ A := by
  haveI : Subsingleton G := subsingleton_of_card_le_one h
  refine ⟨fun _ => z (1, 1), ?_⟩
  funext p
  have hp : p = (1, 1) := by
    ext <;> exact Subsingleton.elim _ _
  rw [hp, groupCohomology.d₁₂_hom_apply]
  simp

/-! ## The vanishing criterion -/

/-- **The vanishing criterion for the cyclic class.**  The cyclic class of a `G`-invariant element
of `A` vanishes if and only if the element is a norm: the kernel of the period map
`A^G ⧸ N(A) ≅ H²(G,A)` is the norm group. -/
theorem cycClass_eq_zero_iff (A : Rep NK.HassePrinciple.CoeffInt G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (a : A) (ha : ∀ γ : G, A.ρ γ a = a) :
    cycClass A g hg a ha = 0 ↔ a ∈ LinearMap.range A.ρ.norm := by
  classical
  constructor
  · intro hzero
    rcases lt_or_ge 1 (Fintype.card G) with hlt | hle
    · obtain ⟨y, hy⟩ := (groupCohomology.H2π_eq_zero_iff
        (⟨cycFun A g hg a, cycFun_mem_cocycles₂ A g hg a ha⟩ :
          groupCohomology.cocycles₂ A)).mp hzero
      have hT := transgression_mem_range_of_mem_coboundaries A g hg y
      have hconn : (∑ t ∈ Finset.range (Fintype.card G),
            (groupCohomology.d₁₂ A).hom y (g ^ t, g))
          = ∑ t ∈ Finset.range (Fintype.card G), cycFun A g hg a (g ^ t, g) := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        exact congrFun hy (g ^ t, g)
      rw [hconn, transgression_cycFun A g hg a ha hlt] at hT
      exact hT
    · rw [norm_eq_one_of_card_le_one A hle]
      exact ⟨a, rfl⟩
  · rintro ⟨b, hb⟩
    rcases lt_or_ge 1 (Fintype.card G) with hlt | hle
    · show (groupCohomology.H2π A) ⟨cycFun A g hg a,
          cycFun_mem_cocycles₂ A g hg a ha⟩ = 0
      refine (groupCohomology.H2π_eq_zero_iff _).mpr ?_
      refine NK.Cohomology.mem_coboundaries₂_of_transgression_mem_range g hg A _ ?_
      rw [show (∑ t ∈ Finset.range (Fintype.card G),
          (⟨cycFun A g hg a, cycFun_mem_cocycles₂ A g hg a ha⟩ :
            groupCohomology.cocycles₂ A) (g ^ t, g))
          = ∑ t ∈ Finset.range (Fintype.card G), cycFun A g hg a (g ^ t, g) from
        Finset.sum_congr rfl (fun t _ => rfl)]
      rw [transgression_cycFun A g hg a ha hlt]
      exact ⟨b, hb⟩
    · show (groupCohomology.H2π A) ⟨cycFun A g hg a,
          cycFun_mem_cocycles₂ A g hg a ha⟩ = 0
      exact (groupCohomology.H2π_eq_zero_iff _).mpr
        (mem_coboundaries₂_of_card_le_one A (cycFun A g hg a) hle)

/-- **Every second cohomology class of a cyclic group is a cyclic class.** -/
theorem exists_eq_cycClass (A : Rep NK.HassePrinciple.CoeffInt G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (β : groupCohomology A 2) :
    ∃ (a : A) (ha : ∀ γ : G, A.ρ γ a = a), cycClass A g hg a ha = β := by
  classical
  rcases lt_or_ge 1 (Fintype.card G) with hlt | hle
  · obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective _).mp
      (inferInstance : Epi (groupCohomology.H2π A)) β
    set a : A := ∑ t ∈ Finset.range (Fintype.card G), z (g ^ t, g) with ha_def
    have ha : ∀ γ : G, A.ρ γ a = a := fun γ => by
      rw [ha_def]
      exact (Representation.mem_invariants A.ρ _).mp
        (NK.Cohomology.transgression_mem_invariants g hg A z) γ
    refine ⟨a, ha, ?_⟩
    rw [← hz]
    have hcoc : (fun p : G × G => z p - cycFun A g hg a p) ∈ groupCohomology.cocycles₂ A := by
      rw [groupCohomology.mem_cocycles₂_iff]
      intro γ δ ε
      have h1 := (groupCohomology.mem_cocycles₂_iff (⇑z)).mp z.2 γ δ ε
      have h2 := (groupCohomology.mem_cocycles₂_iff (⇑(⟨cycFun A g hg a,
        cycFun_mem_cocycles₂ A g hg a ha⟩ : groupCohomology.cocycles₂ A))).mp
        (⟨cycFun A g hg a, cycFun_mem_cocycles₂ A g hg a ha⟩ :
          groupCohomology.cocycles₂ A).2 γ δ ε
      have h2' : cycFun A g hg a (γ * δ, ε) + cycFun A g hg a (γ, δ)
          = (A.ρ γ) (cycFun A g hg a (δ, ε)) + cycFun A g hg a (γ, δ * ε) := h2
      simp only [Pi.sub_apply]
      have hL : (z (γ * δ, ε) - cycFun A g hg a (γ * δ, ε))
            + (z (γ, δ) - cycFun A g hg a (γ, δ))
          = (z (γ * δ, ε) + z (γ, δ))
            - (cycFun A g hg a (γ * δ, ε) + cycFun A g hg a (γ, δ)) := by abel
      rw [hL, h1, h2', map_sub]
      abel
    have hT : (∑ t ∈ Finset.range (Fintype.card G),
          (fun p : G × G => z p - cycFun A g hg a p) (g ^ t, g))
        ∈ LinearMap.range A.ρ.norm := by
      have hsum : (∑ t ∈ Finset.range (Fintype.card G),
            (fun p : G × G => z p - cycFun A g hg a p) (g ^ t, g))
          = (∑ t ∈ Finset.range (Fintype.card G), z (g ^ t, g))
            - ∑ t ∈ Finset.range (Fintype.card G), cycFun A g hg a (g ^ t, g) := by
        rw [← Finset.sum_sub_distrib]
      rw [hsum, ha_def, transgression_cycFun A g hg a ha hlt, sub_self]
      exact Submodule.zero_mem _
    have hmem : (fun p : G × G => z p - cycFun A g hg a p)
        ∈ groupCohomology.coboundaries₂ A :=
      NK.Cohomology.mem_coboundaries₂_of_transgression_mem_range g hg A
        ⟨_, hcoc⟩ hT
    have hsub : (⟨fun p : G × G => z p - cycFun A g hg a p, hcoc⟩ :
        groupCohomology.cocycles₂ A)
        = z - ⟨cycFun A g hg a, cycFun_mem_cocycles₂ A g hg a ha⟩ := rfl
    have hzero : (groupCohomology.H2π A) (⟨fun p : G × G => z p - cycFun A g hg a p,
        hcoc⟩ : groupCohomology.cocycles₂ A) = 0 :=
      (groupCohomology.H2π_eq_zero_iff _).mpr hmem
    rw [hsub, map_sub] at hzero
    exact (sub_eq_zero.mp hzero).symm
  · have hβ : β = 0 := by
      obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective _).mp
        (inferInstance : Epi (groupCohomology.H2π A)) β
      rw [← hz]
      exact (groupCohomology.H2π_eq_zero_iff _).mpr (mem_coboundaries₂_of_card_le_one A z hle)
    refine ⟨0, fun γ => by simp, ?_⟩
    have h0 : cycClass A g hg 0 (fun γ => by simp) = 0 := by
      show (groupCohomology.H2π A) ⟨cycFun A g hg 0, _⟩ = 0
      exact (groupCohomology.H2π_eq_zero_iff _).mpr
        (mem_coboundaries₂_of_card_le_one A (cycFun A g hg 0) hle)
    rw [h0, hβ]


/-! ## Functoriality of the explicit cyclic cocycle -/

/-- The value of the degree-`2` cochain map: `x ↦ (γ, δ) ↦ φ (x (f γ, f δ))`. -/
lemma cochainsMap₂_apply {G' : Type} [Group G'] {A : Rep NK.HassePrinciple.CoeffInt G}
    {B : Rep NK.HassePrinciple.CoeffInt G'} (f : G' →* G) (φ : Rep.res f A ⟶ B)
    (z : G × G → A) (γ δ : G') :
    (groupCohomology.cochainsMap₂ f φ) z (γ, δ) = φ.hom (z (f γ, f δ)) := rfl

/-- **The carry is compatible with a group homomorphism that maps a generator to a power.**
If `ρ g' = g ^ m` and `m * |G'| = |G|`, then the carry computed in `G'` with the generator `g'`
agrees with the carry computed in `G` with the generator `g` on the images. -/
lemma carry_comp {G' : Type} [Group G'] [Fintype G'] (ρ : G' →* G)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (g' : G') (hg' : ∀ x : G', x ∈ Subgroup.zpowers g')
    (m : ℕ) (hm : ρ g' = g ^ m) (hcard : m * Fintype.card G' = Fintype.card G) (γ δ : G') :
    carry g hg (ρ γ) (ρ δ) = carry g' hg' γ δ := by
  have hn : (Fintype.card G : ℤ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := G)).ne'
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      rw [Nat.zero_mul] at hcard
      have := Fintype.card_pos (α := G)
      omega
    · exact h
  have hordg : orderOf g = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  have hordg' : orderOf g' = Fintype.card G' := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg', Nat.card_eq_fintype_card]
  set i := dlog g' hg' γ with hi
  set j := dlog g' hg' δ with hj
  have hγ : g' ^ i = γ := pow_dlog g' hg' γ
  have hδ : g' ^ j = δ := pow_dlog g' hg' δ
  have hi_lt : i < Fintype.card G' := dlog_lt g' hg' γ
  have hj_lt : j < Fintype.card G' := dlog_lt g' hg' δ
  have hr : (i + j) % Fintype.card G' < Fintype.card G' :=
    Nat.mod_lt _ (Fintype.card_pos)
  have hmi : m * i < Fintype.card G := by
    rw [← hcard]; exact Nat.mul_lt_mul_of_pos_left hi_lt hmpos
  have hmj : m * j < Fintype.card G := by
    rw [← hcard]; exact Nat.mul_lt_mul_of_pos_left hj_lt hmpos
  have hmr : m * ((i + j) % Fintype.card G') < Fintype.card G := by
    rw [← hcard]; exact Nat.mul_lt_mul_of_pos_left hr hmpos
  have hργ : ρ γ = g ^ (m * i) := by
    rw [← hγ, map_pow, hm, ← pow_mul]
  have hρδ : ρ δ = g ^ (m * j) := by
    rw [← hδ, map_pow, hm, ← pow_mul]
  have hγδ : γ * δ = g' ^ (i + j) := by rw [pow_add, hγ, hδ]
  have hpow : g ^ (m * (i + j)) = g ^ (m * ((i + j) % Fintype.card G')) := by
    rw [pow_eq_pow_iff_modEq, hordg, ← hcard]
    show m * (i + j) ≡ m * ((i + j) % Fintype.card G') [MOD m * Fintype.card G']
    rw [Nat.ModEq, Nat.mul_mod_mul_left,
      Nat.mod_eq_of_lt (Nat.mul_lt_mul_of_pos_left hr hmpos)]
  have hpow' : g' ^ (i + j) = g' ^ ((i + j) % Fintype.card G') := by
    rw [pow_eq_pow_iff_modEq, hordg', Nat.ModEq, Nat.mod_eq_of_lt hr]
  have hρpow : ρ (γ * δ) = g ^ (m * ((i + j) % Fintype.card G')) := by
    rw [hγδ, map_pow, hm, ← pow_mul, hpow]
  have d1 : dlog g hg (ρ γ) = m * i := by rw [hργ, dlog_pow g hg hmi]
  have d2 : dlog g hg (ρ δ) = m * j := by rw [hρδ, dlog_pow g hg hmj]
  have d3 : dlog g hg (ρ γ * ρ δ) = m * ((i + j) % Fintype.card G') := by
    rw [← map_mul, hρpow, dlog_pow g hg hmr]
  have d4 : dlog g' hg' (γ * δ) = (i + j) % Fintype.card G' := by
    rw [hγδ, hpow', dlog_pow g' hg' hr]
  have hA := card_mul_carry g hg (ρ γ) (ρ δ)
  rw [d1, d2, d3] at hA
  have hB := card_mul_carry g' hg' γ δ
  rw [hi.symm, hj.symm, d4] at hB
  have hcast : (Fintype.card G : ℤ) = (m : ℤ) * (Fintype.card G' : ℤ) := by
    rw [← hcard]; push_cast; ring
  have hkey : (Fintype.card G : ℤ) * carry g hg (ρ γ) (ρ δ)
      = (Fintype.card G : ℤ) * carry g' hg' γ δ := by
    rw [hA, hcast, mul_assoc, hB]
    push_cast
    ring
  exact mul_left_cancel₀ hn hkey

/-- **Functoriality of the explicit cyclic cocycle.**  For a group homomorphism `ρ : G' →* G`
taking the generator `g'` of `G'` to `g ^ m` (with `m * |G'| = |G|`) and a `ρ`-equivariant
coefficient map `φ`, the explicit cyclic cocycle of `a` is sent to the explicit cyclic cocycle
of `φ a`.  This is the "functorial on the nose" property that makes the localisations and the level
changes computable. -/
theorem cochainsMap₂_cycFun {G' : Type} [Group G'] [Fintype G']
    (A : Rep NK.HassePrinciple.CoeffInt G) (B : Rep NK.HassePrinciple.CoeffInt G')
    (ρ : G' →* G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (g' : G') (hg' : ∀ x : G', x ∈ Subgroup.zpowers g')
    (m : ℕ) (hm : ρ g' = g ^ m) (hcard : m * Fintype.card G' = Fintype.card G)
    (φ : Rep.res ρ A ⟶ B) (a : A) (a' : B) (ha' : φ.hom a = a') :
    (groupCohomology.cochainsMap₂ ρ φ) (cycFun A g hg a) = cycFun B g' hg' a' := by
  funext p
  obtain ⟨γ, δ⟩ := p
  rw [cochainsMap₂_apply]
  show φ.hom (carry g hg (ρ γ) (ρ δ) • a) = carry g' hg' γ δ • a'
  rw [map_zsmul, ha', carry_comp ρ g hg g' hg' m hm hcard γ δ]


/-- **Functoriality of the cyclic class.**  Level form of `cochainsMap₂_cycFun`: the image of the
cyclic class of `a` under the map induced by `(ρ, φ)` is the cyclic class of `φ a`. -/
theorem map_cycClass {G' : Type} [Group G'] [Fintype G']
    (A : Rep NK.HassePrinciple.CoeffInt G) (B : Rep NK.HassePrinciple.CoeffInt G')
    (ρ : G' →* G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (g' : G') (hg' : ∀ x : G', x ∈ Subgroup.zpowers g')
    (m : ℕ) (hm : ρ g' = g ^ m) (hcard : m * Fintype.card G' = Fintype.card G)
    (φ : Rep.res ρ A ⟶ B) (a : A) (ha : ∀ γ : G, A.ρ γ a = a) (a' : B)
    (ha' : φ.hom a = a') (hinv : ∀ γ : G', B.ρ γ a' = a') :
    (groupCohomology.map ρ φ 2) (cycClass A g hg a ha) = cycClass B g' hg' a' hinv := by
  have hcoe : (⇑((groupCohomology.mapCocycles₂ ρ φ) ⟨cycFun A g hg a,
      cycFun_mem_cocycles₂ A g hg a ha⟩ : groupCohomology.cocycles₂ B))
        = cycFun B g' hg' a' := by
    rw [groupCohomology.coe_mapCocycles₂]
    exact cochainsMap₂_cycFun A B ρ g hg g' hg' m hm hcard φ a a' ha'
  have hsub : ((groupCohomology.mapCocycles₂ ρ φ) ⟨cycFun A g hg a,
      cycFun_mem_cocycles₂ A g hg a ha⟩ : groupCohomology.cocycles₂ B)
      = ⟨cycFun B g' hg' a', cycFun_mem_cocycles₂ B g' hg' a' hinv⟩ := Subtype.ext hcoe
  show (groupCohomology.map ρ φ 2) ((groupCohomology.H2π A) ⟨cycFun A g hg a,
      cycFun_mem_cocycles₂ A g hg a ha⟩) = (groupCohomology.H2π B) ⟨cycFun B g' hg' a',
        cycFun_mem_cocycles₂ B g' hg' a' hinv⟩
  rw [← ConcreteCategory.comp_apply, groupCohomology.H2π_comp_map, ConcreteCategory.comp_apply,
    hsub]

end NK.CFTLib.IdeleHasse.Descent
