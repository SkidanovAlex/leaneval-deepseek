import Mathlib
import Submission.Work.DSTR.D110iDefs
import Submission.Work.DSTR.Defs
import Submission.Work.A7.Defs
import Submission.Work.DSTR.A7PtwiseStab0123
import Submission.Work.DSTR.A7PtwiseStab456
import Submission.OddOrder.GroupTheory.ConjClassCardinality

namespace Work.DSTR

open scoped MatrixGroups
open Subgroup

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-!
# The `A₇` case of Bender 1.10(i), from the model facts `ha7`

This file proves `Work.DSTR.CentInvariant Q` for a finite group `Q ≃* A₇`, using as input only
the model `Prop` `Work.GW2.A7ModelProp` (Bender 1.8 for `A₇`): `|A₇| = 2520`, every Sylow
2-subgroup is dihedral of order `8`, `|C_{A₇}(t)| = 24` for every involution `t`, and every
odd-order subgroup of `A₇` has order at most `21`.

Everything else is proved here from `Mathlib` (and the two clash-free pointwise-stabiliser
computations `A7PtwiseStab0123`, `A7PtwiseStab456`), in particular

* the orbit dichotomy for odd-order subgroups of `A₇`,
* `|N_{A₇}(⟨x⟩)| = 21` for `x` of order `7`,
* conjugacy of involutions in `A₇` (via the conjugacy-class cardinality `|A₇|/|C(t₀)| = 105`
  and the count of the `105` involutions of `A₇`),
* the classification of the `C_{A₇}(t)`-invariant subsets of the seven points.

The mathematical argument is: `P` is an odd `p`-subgroup normalised by `C = C_{A₇}(t)`; since
`|P|` divides `2520` and is at most `21`, `|P| ∈ {3,5,7,9}`.  The fixed-point set of `P` on the
seven points is `C`-invariant, hence (all involutions being conjugate, so the orbits of `C` are a
`4`-set and a `3`-set) one of `∅`, a `3`-set, a `4`-set, the whole set.  Orders `5` and `9` are
excluded with this and the pointwise stabilisers (`A₄` of order `12`, resp. `⟨(4 5 6)⟩` of order
`3`); order `3` forces `P ≤ ⟨(4 5 6)⟩ ≤ C`; order `7` is excluded because then `C ≤ N(P)` with
`|N(P)| = 21` while `|C| = 24`.
-/

namespace A7Ha7

open Equiv

/-! ## Generic transport of centralizers along an isomorphism -/

theorem map_centralizer_singleton_equiv {G H : Type*} [Group G] [Group H] (ψ : G ≃* H) (z : G) :
    Subgroup.map ψ.toMonoidHom (Subgroup.centralizer ({z} : Set G)) =
      Subgroup.centralizer ({ψ z} : Set H) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    simpa using congrArg (fun w => ψ w) hy
  · intro hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    refine Subgroup.mem_map.mpr ⟨ψ.symm x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply ψ.injective
    simpa using hx

/-! ## 1. The orbit dichotomy for odd-order subgroups of `A₇` -/

lemma odd_ncard_orbit {G : Type*} [Group G] {α : Type*} [MulAction G α]
    (hodd : Odd (Nat.card G)) (a : α) : Odd (MulAction.orbit G a).ncard := by
  rw [← MulAction.index_stabilizer G a]
  exact Odd.of_dvd_nat hodd (Subgroup.index_dvd_card _)

lemma three_le_ncard_orbit {G : Type*} [Group G] {α : Type*} [MulAction G α]
    (hodd : Odd (Nat.card G)) (hfix : ∀ a : α, ∃ x : G, x • a ≠ a) (a : α) :
    3 ≤ (MulAction.orbit G a).ncard := by
  have hne1 : (MulAction.orbit G a).ncard ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := Set.ncard_eq_one.mp h1
    obtain ⟨x, hx⟩ := hfix a
    refine hx ?_
    have hmem : x • a ∈ MulAction.orbit G a := MulAction.mem_orbit a x
    rw [hc, Set.mem_singleton_iff] at hmem
    have ha : a ∈ MulAction.orbit G a := MulAction.mem_orbit_self a
    rw [hc, Set.mem_singleton_iff] at ha
    exact hmem.trans ha.symm
  have hodd_a := odd_ncard_orbit hodd a
  obtain ⟨k, hk⟩ := hodd_a
  have : k ≠ 0 := by rintro rfl; exact hne1 (by omega)
  omega

lemma disjoint_orbit_of_not_mem {G : Type*} [Group G] {α : Type*} [MulAction G α]
    {a b : α} (hb : b ∉ MulAction.orbit G a) :
    Disjoint (MulAction.orbit G a) (MulAction.orbit G b) := by
  rcases MulAction.orbit.eq_or_disjoint (G := G) a b with heq | hd
  · rw [heq] at hb
    exact absurd (MulAction.mem_orbit_self b) hb
  · exact hd

theorem orbit_dichotomy_general {G : Type*} [Group G] [Finite G] {α : Type*} [Finite α]
    [MulAction G α] (hodd : Odd (Nat.card G)) (hcard : Nat.card α = 7) :
    (∃ p : α, ∀ x : G, x • p = p) ∨ (∀ p q : α, ∃ x : G, x • p = q) := by
  by_cases hfix : ∃ p : α, ∀ x : G, x • p = p
  · exact Or.inl hfix
  · right
    have hfix' : ∀ p : α, ∃ x : G, x • p ≠ p := by
      simpa only [not_exists, not_forall] using hfix
    have hge3 : ∀ a : α, 3 ≤ (MulAction.orbit G a).ncard :=
      fun a => three_le_ncard_orbit hodd hfix' a
    -- Every orbit is the whole set.
    have hUniv : ∀ a : α, MulAction.orbit G a = Set.univ := by
      intro a
      by_contra hne
      -- A point outside the orbit of `a`.
      obtain ⟨b, hb⟩ : ∃ b, b ∉ MulAction.orbit G a := by
        by_contra h
        rw [not_exists] at h
        exact hne (Set.eq_univ_of_forall fun b => not_not.mp (h b))
      have hdisj : Disjoint (MulAction.orbit G a) (MulAction.orbit G b) :=
        disjoint_orbit_of_not_mem hb
      have hfin_a : (MulAction.orbit G a).Finite := Finite.finite_mulAction_orbit a
      have hfin_b : (MulAction.orbit G b).Finite := Finite.finite_mulAction_orbit b
      have hunion : (MulAction.orbit G a ∪ MulAction.orbit G b).ncard
          = (MulAction.orbit G a).ncard + (MulAction.orbit G b).ncard :=
        Set.ncard_union_eq hdisj hfin_a hfin_b
      have hle7 : (MulAction.orbit G a ∪ MulAction.orbit G b).ncard ≤ 7 := by
        have h : (MulAction.orbit G a ∪ MulAction.orbit G b).ncard ≤ (Set.univ : Set α).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _) (Set.finite_univ (α := α))
        rwa [Set.ncard_univ, hcard] at h
      -- The two orbits have sizes `≥ 3`, odd, summing to at most `7`; hence both equal `3`.
      have hsum : (MulAction.orbit G a).ncard + (MulAction.orbit G b).ncard = 6 := by
        have h6 : 6 ≤ (MulAction.orbit G a).ncard + (MulAction.orbit G b).ncard := by
          have := hge3 a; have := hge3 b; omega
        have hle : (MulAction.orbit G a).ncard + (MulAction.orbit G b).ncard ≤ 7 := by
          rw [← hunion]; exact hle7
        obtain ⟨m, hm⟩ := Odd.add_odd (odd_ncard_orbit hodd a) (odd_ncard_orbit hodd b)
        omega
      have h6u : (MulAction.orbit G a ∪ MulAction.orbit G b).ncard = 6 := by
        rw [hunion, hsum]
      have hlt : (MulAction.orbit G a ∪ MulAction.orbit G b).ncard < 7 := by
        rw [h6u]; norm_num
      -- A point outside the two orbits; its orbit is disjoint from both, but only one point is
      -- left over.
      obtain ⟨c, hc⟩ : ∃ c, c ∉ MulAction.orbit G a ∪ MulAction.orbit G b := by
        by_contra h
        rw [not_exists] at h
        have hmem : ∀ c, c ∈ MulAction.orbit G a ∪ MulAction.orbit G b :=
          fun c => not_not.mp (h c)
        have heq : MulAction.orbit G a ∪ MulAction.orbit G b = Set.univ :=
          Set.eq_univ_of_forall hmem
        rw [heq, Set.ncard_univ, hcard] at hlt
        exact lt_irrefl 7 hlt
      have hca : c ∉ MulAction.orbit G a := fun h => hc (Or.inl h)
      have hcb : c ∉ MulAction.orbit G b := fun h => hc (Or.inr h)
      have hdisj_c : Disjoint (MulAction.orbit G c)
          (MulAction.orbit G a ∪ MulAction.orbit G b) :=
        ((disjoint_orbit_of_not_mem hca).symm).sup_right
          ((disjoint_orbit_of_not_mem hcb).symm)
      have hfin_c : (MulAction.orbit G c).Finite := Finite.finite_mulAction_orbit c
      have hunion_c : ((MulAction.orbit G a ∪ MulAction.orbit G b) ∪ MulAction.orbit G c).ncard
          = (MulAction.orbit G a ∪ MulAction.orbit G b).ncard + (MulAction.orbit G c).ncard :=
        Set.ncard_union_eq hdisj_c.symm (hfin_a.union hfin_b) hfin_c
      have hle7_c : ((MulAction.orbit G a ∪ MulAction.orbit G b) ∪ MulAction.orbit G c).ncard ≤ 7 := by
        have h : ((MulAction.orbit G a ∪ MulAction.orbit G b) ∪ MulAction.orbit G c).ncard ≤
            (Set.univ : Set α).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _) (Set.finite_univ (α := α))
        rwa [Set.ncard_univ, hcard] at h
      have hc_le : (MulAction.orbit G c).ncard ≤ 1 := by
        rw [hunion_c, h6u] at hle7_c
        omega
      have := hge3 c
      omega
    intro p q
    have : q ∈ MulAction.orbit G p := by rw [hUniv p]; exact Set.mem_univ q
    rwa [MulAction.mem_orbit_iff] at this

/-- **Orbit dichotomy.**  A subgroup of `A₇` of odd order either fixes a point of `Fin 7` or acts
transitively. -/
theorem orbit_dichotomy (X : Subgroup (alternatingGroup (Fin 7))) (hodd : Odd (Nat.card X)) :
    (∃ p : Fin 7, ∀ x ∈ X, (x : Equiv.Perm (Fin 7)) p = p) ∨
      (∀ p q : Fin 7, ∃ x ∈ X, (x : Equiv.Perm (Fin 7)) p = q) := by
  have hcard7 : Nat.card (Fin 7) = 7 := by simp
  rcases orbit_dichotomy_general (G := X) (α := Fin 7) hodd hcard7 with ⟨p, hp⟩ | htr
  · left
    refine ⟨p, fun x hx => ?_⟩
    have h : (⟨x, hx⟩ : X) • p = p := hp ⟨x, hx⟩
    simpa [Subgroup.smul_def] using h
  · right
    intro p q
    obtain ⟨x, hx⟩ := htr p q
    exact ⟨x.1, x.2, by simpa [Subgroup.smul_def] using hx⟩

/-! ## 2. An element of order `3` of `A₇` has one or four fixed points -/

/-- An element of order `3` of `A₇` (a `3`-cycle or a product of two disjoint `3`-cycles) has
exactly `4` or exactly `1` fixed points. -/
theorem fixFinset_card_of_order_three (x : alternatingGroup (Fin 7)) (hx : orderOf x = 3) :
    (Finset.univ.filter (fun q : Fin 7 => x • q = q)).card = 1 ∨
      (Finset.univ.filter (fun q : Fin 7 => x • q = q)).card = 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hx3 : (x : Equiv.Perm (Fin 7)) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (x : Equiv.Perm (Fin 7))
    rwa [Subgroup.orderOf_coe, hx] at h
  have hne : (x : Equiv.Perm (Fin 7)) ≠ 1 := by
    intro h
    have h1 : orderOf (x : Equiv.Perm (Fin 7)) = 1 := by rw [h, orderOf_one]
    rw [Subgroup.orderOf_coe, hx] at h1
    exact absurd h1 (by norm_num)
  have hcyc : (x : Equiv.Perm (Fin 7)).cycleType =
      Multiset.replicate ((x : Equiv.Perm (Fin 7)).cycleType.card) 3 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one hx3
  have hsum : (x : Equiv.Perm (Fin 7)).cycleType.sum =
      3 * (x : Equiv.Perm (Fin 7)).cycleType.card := by
    rw [hcyc, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul, mul_comm]
  have hle : 3 * (x : Equiv.Perm (Fin 7)).cycleType.card ≤ 7 := by
    rw [← hsum]
    simpa using Equiv.Perm.sum_cycleType_le (x : Equiv.Perm (Fin 7))
  have hkpos : 0 < (x : Equiv.Perm (Fin 7)).cycleType.card :=
    Equiv.Perm.card_cycleType_pos.mpr hne
  have hsupp : (((x : Equiv.Perm (Fin 7)).support).card) =
      3 * (x : Equiv.Perm (Fin 7)).cycleType.card := by
    rw [← Equiv.Perm.sum_cycleType, hsum]
  have hfilter : (Finset.univ.filter (fun q : Fin 7 => x • q = q)) =
      ((x : Equiv.Perm (Fin 7)).support)ᶜ := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
      Equiv.Perm.mem_support]
    exact not_not.symm
  have hcard : (Finset.univ.filter (fun q : Fin 7 => x • q = q)).card =
      7 - 3 * (x : Equiv.Perm (Fin 7)).cycleType.card := by
    rw [hfilter, Finset.card_compl, Fintype.card_fin, hsupp]
  have hk : (x : Equiv.Perm (Fin 7)).cycleType.card = 1 ∨
      (x : Equiv.Perm (Fin 7)).cycleType.card = 2 := by omega
  rcases hk with hk | hk
  · right; rw [hcard, hk]
  · left; rw [hcard, hk]

/-! ## 3. The normalizer of a subgroup of order `7` -/

/-- An element of `A₇` of order `7` is a `7`-cycle. -/
lemma isCycle_of_orderOf_seven (c : alternatingGroup (Fin 7)) (hc : orderOf c = 7) :
    ((c : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).IsCycle := by
  apply Equiv.Perm.isCycle_of_prime_order
  · rw [Subgroup.orderOf_coe, hc]; norm_num
  · rw [Subgroup.orderOf_coe, hc]
    have h : (((c : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support).card ≤ 7 := by
      have := Finset.card_le_univ (((c : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support)
      simpa using this
    omega

/-- The support of a `7`-cycle of `Fin 7` is everything. -/
lemma support_eq_univ_of_orderOf_seven (c : alternatingGroup (Fin 7)) (hc : orderOf c = 7) :
    ((c : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support = Finset.univ := by
  have hcyc := isCycle_of_orderOf_seven c hc
  apply Finset.eq_univ_of_card
  rw [← Equiv.Perm.IsCycle.orderOf hcyc]
  rw [Subgroup.orderOf_coe, hc]
  simp

/-- Transitivity of a `7`-cycle of `Fin 7`, in the form used below: every point is carried to `0`
by some power of `c`. -/
lemma exists_pow_eq_zero (c : alternatingGroup (Fin 7)) (hc : orderOf c = 7) (p : Fin 7) :
    ∃ i : ℕ, (((c : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) ^ i) p = 0 := by
  have hcyc := isCycle_of_orderOf_seven c hc
  have hsupp := support_eq_univ_of_orderOf_seven c hc
  refine Equiv.Perm.IsCycle.exists_pow_eq hcyc ?_ ?_
  · have : p ∈ (((c : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))).support := by
      rw [hsupp]; exact Finset.mem_univ p
    simpa using Equiv.Perm.mem_support.mp this
  · have : (0 : Fin 7) ∈ (((c : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))).support := by
      rw [hsupp]; exact Finset.mem_univ 0
    simpa using Equiv.Perm.mem_support.mp this

/-- The map sending `g ∈ N_{A₇}(⟨c⟩)` to the pair `(g c g⁻¹, g 0)`, where the first component is
regarded as an element of the cyclic group `⟨c⟩`. -/
noncomputable def normalizerToPair (c : alternatingGroup (Fin 7)) :
    (Subgroup.normalizer (Subgroup.zpowers c : Set (alternatingGroup (Fin 7)))) →
      ↥(Subgroup.zpowers c) × Fin 7 :=
  fun g => (⟨(g : alternatingGroup (Fin 7)) * c * (g : alternatingGroup (Fin 7))⁻¹,
      ((Subgroup.mem_normalizer_iff.mp g.2) c).mp (Subgroup.mem_zpowers c)⟩,
    ((g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) 0)

/-- The map `normalizerToPair` is injective: an element of the normalizer of `⟨c⟩` is determined
by the conjugate `g c g⁻¹` and the image of the point `0`, because `c` is transitive. -/
lemma normalizerToPair_injective (c : alternatingGroup (Fin 7)) (hc : orderOf c = 7) :
    Function.Injective (normalizerToPair c) := by
  intro g g' hgg
  have h1 : (g : alternatingGroup (Fin 7)) * c * (g : alternatingGroup (Fin 7))⁻¹ =
      (g' : alternatingGroup (Fin 7)) * c * (g' : alternatingGroup (Fin 7))⁻¹ := by
    have := congrArg (fun z => (z.1 : alternatingGroup (Fin 7))) hgg
    simpa [normalizerToPair] using this
  have h2 : (((g : alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) 0 =
      (((g' : alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) 0 := by
    have := congrArg (fun z => z.2) hgg
    simpa [normalizerToPair] using this
  set hh : alternatingGroup (Fin 7) :=
    (g' : alternatingGroup (Fin 7))⁻¹ * (g : alternatingGroup (Fin 7)) with hhdef
  have hcomm : hh * c = c * hh := by
    have hconj : hh * c * hh⁻¹ = c := by
      rw [hhdef]
      calc ((g' : alternatingGroup (Fin 7))⁻¹ * (g : alternatingGroup (Fin 7))) * c *
              ((g' : alternatingGroup (Fin 7))⁻¹ * (g : alternatingGroup (Fin 7)))⁻¹
          = (g' : alternatingGroup (Fin 7))⁻¹ *
              ((g : alternatingGroup (Fin 7)) * c * (g : alternatingGroup (Fin 7))⁻¹) *
              (g' : alternatingGroup (Fin 7)) := by group
        _ = (g' : alternatingGroup (Fin 7))⁻¹ *
              ((g' : alternatingGroup (Fin 7)) * c * (g' : alternatingGroup (Fin 7))⁻¹) *
              (g' : alternatingGroup (Fin 7)) := by rw [h1]
        _ = c := by group
    calc hh * c = hh * c * hh⁻¹ * hh := by group
      _ = c * hh := by rw [hconj]
  have hfix : ((hh : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) 0 = 0 := by
    rw [hhdef]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
    rw [h2]
    simp
  have hperm : ((hh : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) = 1 := by
    apply Equiv.ext
    intro p
    show ((hh : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) p = p
    obtain ⟨i, hi⟩ := exists_pow_eq_zero c hc p
    have hcom : Commute ((hh : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))
        (((c : alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) := by
      have := congrArg (fun z : alternatingGroup (Fin 7) => (z : Equiv.Perm (Fin 7))) hcomm
      simpa [Commute, SemiconjBy] using this
    have hcp : ((hh : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) *
        ((((c : alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) ^ i) =
        ((((c : alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) ^ i) *
        ((hh : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) := (hcom.pow_right i).eq
    have happ := congrArg (fun e : Equiv.Perm (Fin 7) => e p) hcp
    simp only [Equiv.Perm.mul_apply] at happ
    rw [hi, hfix] at happ
    have key : ((((c : alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) ^ i)
        (((hh : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) p) =
        ((((c : alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) ^ i) p := by
      rw [← happ, hi]
    exact Equiv.injective _ key
  have hh1 : hh = 1 := Subtype.ext hperm
  rw [hhdef] at hh1
  apply Subtype.ext
  have : (g : alternatingGroup (Fin 7)) = (g' : alternatingGroup (Fin 7)) := by
    have := congrArg (fun z => (g' : alternatingGroup (Fin 7)) * z) hh1
    simpa [mul_assoc] using this
  exact this

/-- The normalizer of the cyclic subgroup generated by an element of order `7` of `A₇` has at
most `7 · 7 = 49` elements. -/
lemma card_normalizer_le (c : alternatingGroup (Fin 7)) (hc : orderOf c = 7) :
    Nat.card (Subgroup.normalizer (Subgroup.zpowers c : Set (alternatingGroup (Fin 7)))) ≤ 49 := by
  have hinj := normalizerToPair_injective c hc
  have := Nat.card_le_card_of_injective (normalizerToPair c) hinj
  rw [Nat.card_prod, Nat.card_zpowers, hc, Nat.card_fin] at this
  simpa using this

/-- `|N_{A₇}(⟨c⟩)| ≡ |A₇| = 2520 ≡ 21 (mod 49)` for `c` of order `7`. -/
lemma card_normalizer_modEq (c : alternatingGroup (Fin 7)) (hc : orderOf c = 7) :
    Nat.card (Subgroup.normalizer (Subgroup.zpowers c : Set (alternatingGroup (Fin 7)))) ≡
      2520 [MOD 49] := by
  have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcard : Nat.card ↥(Subgroup.zpowers c) = 7 ^ 1 := by
    rw [Nat.card_zpowers, hc]; norm_num
  have h := Sylow.card_normalizer_modEq_card (G := alternatingGroup (Fin 7)) (p := 7) (n := 1)
    hcard
  rw [Work.A7.card_alternatingGroup_seven] at h
  norm_num at h
  exact h

/-- **`|N_{A₇}(⟨x⟩)| = 21` for `x` of order `7`.** -/
theorem normalizer_zpowers_order_seven (c : alternatingGroup (Fin 7)) (hc : orderOf c = 7) :
    Nat.card (Subgroup.normalizer (Subgroup.zpowers c : Set (alternatingGroup (Fin 7)))) = 21 := by
  have hle := card_normalizer_le c hc
  have hmod := card_normalizer_modEq c hc
  have hmod' : Nat.card
      (Subgroup.normalizer (Subgroup.zpowers c : Set (alternatingGroup (Fin 7)))) % 49 =
        2520 % 49 := hmod
  rw [show (2520 : ℕ) % 49 = 21 from by norm_num] at hmod'
  omega

/-! ## 4. The `105` nonidentity involutions of `A₇` -/

/-- An even involution of `S₇` that is not the identity is a double transposition. -/
lemma invSet_cycleType_eq_two_two {t : Equiv.Perm (Fin 7)} (ht : t * t = 1) (hne : t ≠ 1)
    (hsign : Equiv.Perm.sign t = 1) : t.cycleType = ({2,2} : Multiset ℕ) := by
  have h2 : t ^ 2 = 1 := by rw [pow_two]; exact ht
  have hrep : t.cycleType = Multiset.replicate t.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one (p := 2) h2
  have hpos : 0 < t.cycleType.card := (Equiv.Perm.card_cycleType_pos (σ := t)).mpr hne
  have hsum_le : t.cycleType.sum ≤ 7 := by
    have h := Equiv.Perm.sum_cycleType_le t
    simpa using h
  have hsum_eq : t.cycleType.sum = t.cycleType.card * 2 := by
    rw [hrep, Multiset.sum_replicate, Multiset.card_replicate, nsmul_eq_mul]
    simp
  have hle : t.cycleType.card ≤ 3 := by
    rw [hsum_eq] at hsum_le
    omega
  have hs : (-1 : ℤˣ) ^ (t.cycleType.card * 2 + t.cycleType.card) = 1 := by
    have h := Equiv.Perm.sign_of_cycleType t
    rw [hsign, hsum_eq] at h
    exact h.symm
  have hz : (-1 : ℤ) ^ (t.cycleType.card * 2 + t.cycleType.card) = 1 := by
    simpa using congrArg (Units.val) hs
  have heven' : Even (t.cycleType.card * 2 + t.cycleType.card) :=
    (neg_one_pow_eq_one_iff_even (R := ℤ) (by norm_num)).mp hz
  have heven : Even t.cycleType.card := by
    rw [Nat.even_add] at heven'
    exact heven'.mp ⟨t.cycleType.card, by ring⟩
  obtain ⟨m, hm⟩ := heven
  have hk2 : t.cycleType.card = 2 := by omega
  rw [hrep, hk2]
  rfl

/-- A permutation of `S₇` of cycle type `{2,2}` (a double transposition) is an involution. -/
lemma invSet_sq_eq_one {g : Equiv.Perm (Fin 7)} (hg : g.cycleType = ({2,2} : Multiset ℕ)) :
    g * g = 1 := by
  rw [← pow_two, Equiv.Perm.pow_prime_eq_one_iff (σ := g) (p := 2)]
  intro c hc
  rw [hg] at hc
  simpa using hc

/-- A permutation of `S₇` of cycle type `{2,2}` is not the identity. -/
lemma invSet_ne_one {g : Equiv.Perm (Fin 7)} (hg : g.cycleType = ({2,2} : Multiset ℕ)) :
    g ≠ 1 := by
  intro h
  rw [h, Equiv.Perm.cycleType_one] at hg
  exact absurd hg (by decide)

/-- A permutation of `S₇` of cycle type `{2,2}` is even. -/
lemma invSet_sign_eq_one {g : Equiv.Perm (Fin 7)} (hg : g.cycleType = ({2,2} : Multiset ℕ)) :
    Equiv.Perm.sign g = 1 := by
  rw [Equiv.Perm.sign_of_cycleType, hg]
  norm_num

/-- The nonidentity involutions of `A₇` are in bijection with the permutations of `S₇` of
cycle type `{2,2}` (the double transpositions). -/
def invSetEquiv :
    {t : alternatingGroup (Fin 7) // t ≠ 1 ∧ t * t = 1} ≃
      {g : Equiv.Perm (Fin 7) // g.cycleType = ({2,2} : Multiset ℕ)} where
  toFun t := ⟨(t.1 : Equiv.Perm (Fin 7)),
    invSet_cycleType_eq_two_two
      (by simpa using congrArg (Subtype.val) t.2.2)
      (fun h => t.2.1 (Subtype.ext h))
      ((Equiv.Perm.mem_alternatingGroup (f := (t.1 : Equiv.Perm (Fin 7)))).mp t.1.2)⟩
  invFun g :=
    ⟨⟨g.1, (Equiv.Perm.mem_alternatingGroup (f := g.1)).mpr
        (invSet_sign_eq_one g.2)⟩,
      ⟨fun h => invSet_ne_one g.2 (by simpa using congrArg (Subtype.val) h),
       by apply Subtype.ext; simpa using invSet_sq_eq_one g.2⟩⟩
  left_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv g := by
    apply Subtype.ext
    rfl

/-- **`A₇` has exactly `105` nonidentity involutions.** -/
theorem involution_card :
    (Finset.univ.filter (fun t : alternatingGroup (Fin 7) => t ≠ 1 ∧ t * t = 1)).card = 105 := by
  have hA : (Finset.univ.filter (fun t : alternatingGroup (Fin 7) => t ≠ 1 ∧ t * t = 1)).card =
      Nat.card {t : alternatingGroup (Fin 7) // t ≠ 1 ∧ t * t = 1} := by
    rw [← Fintype.card_subtype (fun t : alternatingGroup (Fin 7) => t ≠ 1 ∧ t * t = 1)]
    rw [Nat.card_eq_fintype_card]
  rw [hA, Nat.card_congr invSetEquiv]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Equiv.Perm.card_of_cycleType]
  norm_num

/-! ## 5. Conjugacy-class cardinality -/

/-- The Finset of conjugates `g * x * g⁻¹` of an element `x` of a finite group has as many
elements as the index of the centralizer of `x`. -/
theorem card_image_conj_eq_index {G : Type*} [Group G] [Fintype G] [DecidableEq G] (x : G) :
    (Finset.univ.image (fun g : G => g * x * g⁻¹)).card
      = (Subgroup.centralizer ({x} : Set G)).index := by
  classical
  have hiff : ∀ y : G, (ConjClasses.mk y = ConjClasses.mk x) ↔
      y ∈ Finset.univ.image (fun g : G => g * x * g⁻¹) := by
    intro y
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_comm, isConj_iff]
  have h1 : Nat.card {y : G // ConjClasses.mk y = ConjClasses.mk x}
      = Nat.card {y : G // y ∈ Finset.univ.image (fun g : G => g * x * g⁻¹)} :=
    Nat.card_congr (Equiv.subtypeEquivRight hiff)
  rw [← OddOrder.RepresentationTheory.card_class_eq_index_centralizer x, h1,
    Nat.card_eq_fintype_card, Fintype.card_coe]

/-! ## 6. The model involution `t₀ = (0 1)(2 3)` and the fixed-point machinery -/

/-- The model involution `(0 1)(2 3)`. -/
abbrev t0 : alternatingGroup (Fin 7) := Work.A7.a7Invol

/-- The `3`-cycle `(4 5 6)`, generating `O_3(C_{A₇}(t₀))`. -/
abbrev c3 : alternatingGroup (Fin 7) := Work.A7.a7ThreeCycle

/-- The double transposition `(0 2)(1 3)`. -/
abbrev d2 : alternatingGroup (Fin 7) := Work.A7.a7Dswap 0 2 1 3 (by decide) (by decide)

/-- The double transposition `(0 3)(1 2)`. -/
abbrev d3 : alternatingGroup (Fin 7) := Work.A7.a7Dswap 0 3 1 2 (by decide) (by decide)

/-- The centralizer of the model involution in `A₇`. -/
abbrev Cent : Subgroup (alternatingGroup (Fin 7)) :=
  Subgroup.centralizer ({t0} : Set (alternatingGroup (Fin 7)))

/-- The set of points fixed (pointwise) by all elements of `P`. -/
def ftop (P : Subgroup (alternatingGroup (Fin 7))) : Set (Fin 7) :=
  {q | ∀ x ∈ P, x • q = q}

lemma smul_eq_apply (x : alternatingGroup (Fin 7)) (q : Fin 7) :
    x • q = (x : Equiv.Perm (Fin 7)) q := rfl

lemma orderOf_t0 : orderOf t0 = 2 := Work.A7.orderOf_a7Invol

lemma t0_mem_Cent : t0 ∈ Cent := by
  rw [Subgroup.mem_centralizer_singleton_iff]

lemma c3_mem_Cent : c3 ∈ Cent := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  decide

lemma d2_mem_Cent : d2 ∈ Cent := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  decide

lemma d3_mem_Cent : d3 ∈ Cent := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  decide

/-- Auxiliary transitivity statement on `{0,1,2,3}`. -/
lemma transA_aux : ∀ q ∈ ({0,1,2,3} : Finset (Fin 7)),
    ∀ q' ∈ ({0,1,2,3} : Finset (Fin 7)), q ≠ q' →
      (t0 • q = q' ∨ d2 • q = q' ∨ d3 • q = q') := by
  decide

/-- Auxiliary transitivity statement on `{4,5,6}`. -/
lemma transB_aux : ∀ q ∈ ({4,5,6} : Finset (Fin 7)),
    ∀ q' ∈ ({4,5,6} : Finset (Fin 7)), q ≠ q' →
      (c3 • q = q' ∨ c3 ^ 2 • q = q') := by
  decide

lemma transA : ∀ q ∈ ({0,1,2,3} : Set (Fin 7)), ∀ q' ∈ ({0,1,2,3} : Set (Fin 7)),
    ∃ g ∈ Cent, g • q = q' := by
  intro q hq q' hq'
  have hqF : q ∈ ({0,1,2,3} : Finset (Fin 7)) := by simpa using hq
  have hqF' : q' ∈ ({0,1,2,3} : Finset (Fin 7)) := by simpa using hq'
  by_cases h : q = q'
  · exact ⟨1, one_mem _, by rw [one_smul, h]⟩
  · rcases transA_aux q hqF q' hqF' h with h1 | h1 | h1
    · exact ⟨t0, t0_mem_Cent, h1⟩
    · exact ⟨d2, d2_mem_Cent, h1⟩
    · exact ⟨d3, d3_mem_Cent, h1⟩

lemma transB : ∀ q ∈ ({4,5,6} : Set (Fin 7)), ∀ q' ∈ ({4,5,6} : Set (Fin 7)),
    ∃ g ∈ Cent, g • q = q' := by
  intro q hq q' hq'
  have hqF : q ∈ ({4,5,6} : Finset (Fin 7)) := by simpa using hq
  have hqF' : q' ∈ ({4,5,6} : Finset (Fin 7)) := by simpa using hq'
  by_cases h : q = q'
  · exact ⟨1, one_mem _, by rw [one_smul, h]⟩
  · rcases transB_aux q hqF q' hqF' h with h1 | h1
    · exact ⟨c3, c3_mem_Cent, h1⟩
    · exact ⟨c3 ^ 2, Subgroup.pow_mem _ c3_mem_Cent 2, h1⟩

/-! ## Invariance of the fixed point set of a normalized subgroup -/

lemma ftop_mem_smul {P : Subgroup (alternatingGroup (Fin 7))}
    (hC : Cent ≤ Subgroup.normalizer (P : Set (alternatingGroup (Fin 7))))
    {g : alternatingGroup (Fin 7)} (hg : g ∈ Cent) {q : Fin 7} (hq : q ∈ ftop P) :
    g • q ∈ ftop P := by
  intro x hx
  have hginv : g⁻¹ ∈ Subgroup.normalizer (P : Set (alternatingGroup (Fin 7))) :=
    Subgroup.inv_mem _ (hC hg)
  have hconj : g⁻¹ * x * g ∈ P := (Subgroup.mem_normalizer_iff.mp hginv x).mp hx
  calc x • (g • q) = (x * g) • q := (mul_smul x g q).symm
    _ = (g * (g⁻¹ * x * g)) • q := by rw [show x * g = g * (g⁻¹ * x * g) by group]
    _ = g • ((g⁻¹ * x * g) • q) := mul_smul g (g⁻¹ * x * g) q
    _ = g • q := by rw [hq (g⁻¹ * x * g) hconj]

lemma ftop_invariant {P : Subgroup (alternatingGroup (Fin 7))}
    (hC : Cent ≤ Subgroup.normalizer (P : Set (alternatingGroup (Fin 7)))) :
    ∀ g ∈ Cent, ∀ q : Fin 7, q ∈ ftop P ↔ g • q ∈ ftop P := by
  intro g hg q
  refine ⟨fun hq => ftop_mem_smul hC hg hq, fun hq => ?_⟩
  have h1 := ftop_mem_smul hC (Subgroup.inv_mem _ hg) hq
  rwa [inv_smul_smul] at h1

/-- **Every `C(t₀)`-invariant subset of the seven points is one of the four obvious ones.** -/
lemma invariant_classification (S : Set (Fin 7))
    (hS : ∀ g ∈ Cent, ∀ q : Fin 7, q ∈ S ↔ g • q ∈ S) :
    S = ∅ ∨ S = ({4,5,6} : Set (Fin 7)) ∨ S = ({0,1,2,3} : Set (Fin 7)) ∨
      S = Set.univ := by
  have key : ∀ B : Set (Fin 7), (∀ q ∈ B, ∀ q' ∈ B, ∃ g ∈ Cent, g • q = q') →
      S ∩ B = ∅ ∨ S ∩ B = B := by
    intro B hB
    by_cases hex : ∃ q, q ∈ S ∧ q ∈ B
    · right
      obtain ⟨q0, hq0S, hq0B⟩ := hex
      ext q'
      refine ⟨fun h => h.2, fun hq' => ?_⟩
      obtain ⟨g, hgC, hgq⟩ := hB q0 hq0B q' hq'
      refine ⟨?_, hq'⟩
      rw [← hgq]
      exact (hS g hgC q0).mp hq0S
    · left
      ext q
      exact ⟨fun ⟨h1, h2⟩ => absurd ⟨q, h1, h2⟩ hex, fun h => absurd h (Set.notMem_empty q)⟩
  have hA := key ({0,1,2,3} : Set (Fin 7)) (fun q hq q' hq' => transA q hq q' hq')
  have hB := key ({4,5,6} : Set (Fin 7)) (fun q hq q' hq' => transB q hq q' hq')
  have hcover : ({0,1,2,3} : Set (Fin 7)) ∪ ({4,5,6} : Set (Fin 7)) = Set.univ := by
    ext q
    fin_cases q <;> simp
  have hScover : S = (S ∩ ({0,1,2,3} : Set (Fin 7))) ∪ (S ∩ ({4,5,6} : Set (Fin 7))) := by
    rw [← Set.inter_union_distrib_left, hcover, Set.inter_univ]
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · left; rw [hScover, hA, hB, Set.union_empty]
  · right; left; rw [hScover, hA, Set.empty_union, hB]
  · right; right; left; rw [hScover, hB, Set.union_empty, hA]
  · right; right; right; rw [hScover, hA, hB, hcover]

/-! ## The fixed point set of a cyclic subgroup -/

lemma ftop_zpowers (x : alternatingGroup (Fin 7)) :
    ftop (Subgroup.zpowers x) = {q : Fin 7 | x • q = q} := by
  ext q
  refine ⟨fun hq => hq x (Subgroup.mem_zpowers x), fun hq y hy => ?_⟩
  have hstab : Subgroup.zpowers x ≤ MulAction.stabilizer (alternatingGroup (Fin 7)) q :=
    Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hq)
  exact MulAction.mem_stabilizer_iff.mp (hstab hy)

/-! ## Pointwise stabilizers -/

lemma fixingSubgroup456_card :
    Nat.card ↥(fixingSubgroup (alternatingGroup (Fin 7)) ({4,5,6} : Set (Fin 7))) = 12 := by
  set H : Subgroup (Equiv.Perm (Fin 7)) :=
    fixingSubgroup (Equiv.Perm (Fin 7)) ({4,5,6} : Set (Fin 7)) with hH
  have hcomap : fixingSubgroup (alternatingGroup (Fin 7)) ({4,5,6} : Set (Fin 7)) =
      H.comap (alternatingGroup (Fin 7)).subtype := by
    ext g
    rw [mem_fixingSubgroup_iff, Subgroup.mem_comap, mem_fixingSubgroup_iff]
    rfl
  rw [hcomap, ← Subgroup.card_map_of_injective
    (Subgroup.subtype_injective (alternatingGroup (Fin 7)))]
  rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
  rw [Work.A7.nat_card_subgroup_eq_filter_card (alternatingGroup (Fin 7) ⊓ H)
    (fun g : Equiv.Perm (Fin 7) =>
      Equiv.Perm.sign g = 1 ∧ ∀ q ∈ ({4,5,6} : Finset (Fin 7)), g q = q) (by
        intro g
        rw [Subgroup.mem_inf, Equiv.Perm.mem_alternatingGroup, hH, mem_fixingSubgroup_iff]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun q hq => by simpa using h2 q (by simpa using hq)⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun q hq => by simpa using h2 q (by simpa using hq)⟩)]
  exact A7PtwiseStab456

lemma fixingSubgroup0123_le_zpowers :
    fixingSubgroup (alternatingGroup (Fin 7)) ({0,1,2,3} : Set (Fin 7)) ≤
      Subgroup.zpowers c3 := by
  intro g hg
  have hg' := (mem_fixingSubgroup_iff (alternatingGroup (Fin 7))).mp hg
  have hsign : Equiv.Perm.sign (g : Equiv.Perm (Fin 7)) = 1 := g.2
  have hfix : ∀ q ∈ ({0,1,2,3} : Finset (Fin 7)), (g : Equiv.Perm (Fin 7)) q = q := by
    intro q hq
    have h := hg' q (by simpa using hq)
    simpa [smul_eq_apply] using h
  rcases A7PtwiseStab0123 (g : Equiv.Perm (Fin 7)) hsign hfix with h | h | h
  · have hg1 : g = 1 := Subtype.ext h
    rw [hg1]; exact Subgroup.one_mem _
  · have hgc : g = c3 := Subtype.ext (by simpa [c3] using h)
    rw [hgc]; exact Subgroup.mem_zpowers c3
  · have hgc : g = c3 ^ 2 := Subtype.ext (by simpa [c3] using h)
    rw [hgc]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c3) 2

lemma zpowers_c3_le_Cent : Subgroup.zpowers c3 ≤ Cent :=
  Subgroup.zpowers_le.mpr c3_mem_Cent

/-! ## Extraction of a generator of a subgroup of prime order -/

lemma exists_zpowers_of_prime_card {P : Subgroup (alternatingGroup (Fin 7))} {ℓ : ℕ}
    (hℓ : Nat.Prime ℓ) (hcard : Nat.card ↥P = ℓ) :
    ∃ x : alternatingGroup (Fin 7), x ∈ P ∧ P = Subgroup.zpowers x ∧ orderOf x = ℓ := by
  haveI : Finite ↥P := Finite.of_injective (Subgroup.subtype P) Subtype.val_injective
  haveI : Fintype ↥P := Fintype.ofFinite _
  have hlt : 1 < Fintype.card ↥P := by
    rw [← Nat.card_eq_fintype_card, hcard]
    exact hℓ.one_lt
  obtain ⟨z, hz⟩ := Fintype.exists_ne_of_one_lt_card hlt (1 : ↥P)
  have hzord : orderOf z = ℓ := by
    have hdvd : orderOf z ∣ ℓ := by
      rw [← hcard]
      exact orderOf_dvd_natCard z
    rcases (Nat.dvd_prime hℓ).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz
    · exact h
  refine ⟨(z : alternatingGroup (Fin 7)), z.2, ?_, ?_⟩
  · refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr z.2) ?_).symm
    rw [hcard, Nat.card_zpowers, Subgroup.orderOf_coe, hzord]
  · rw [Subgroup.orderOf_coe, hzord]

/-! ## The arithmetic of the order of an odd `p`-subgroup -/

lemma pow_card_cases {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpos : 0 < m)
    (hle : p ^ m ≤ 21) (hdvd : p ^ m ∣ 2520) :
    p ^ m = 3 ∨ p ^ m = 5 ∨ p ^ m = 7 ∨ p ^ m = 9 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hm2 : m ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ m := by omega
    have h27 : 27 ≤ p ^ m := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ p ^ 3 := by gcongr
        _ ≤ p ^ m := Nat.pow_le_pow_right (by omega) h3
    omega
  interval_cases m
  · simp only [pow_one] at hle hdvd ⊢
    have hp_mem : p = 3 ∨ p = 5 ∨ p = 7 := by
      have hfac : p ∣ 2 ^ 3 * 3 ^ 2 * 5 * 7 := by
        rw [show 2 ^ 3 * 3 ^ 2 * 5 * 7 = 2520 by norm_num]
        exact hdvd
      rcases hp.dvd_mul.mp hfac with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · rcases hp.dvd_mul.mp h with h | h
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
              hp2
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h))
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))
    rcases hp_mem with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  · have hp_le4 : p ≤ 4 := by
      by_contra h
      have h5 : 5 ≤ p := by omega
      have h25 : 25 ≤ p ^ 2 := by nlinarith
      omega
    have hp3' : p = 3 := by
      interval_cases p <;>
        first
          | rfl
          | (exfalso; exact absurd hp (by norm_num))
    right; right; right
    rw [hp3']
    norm_num

/-! ## Conjugacy of involutions -/

/-- **Every involution of `A₇` is conjugate to `t₀ = (0 1)(2 3)`.**  The conjugacy class of `t₀`
has `|A₇| / |C(t₀)| = 2520/24 = 105` elements, which is exactly the number of nonidentity
involutions of `A₇`. -/
theorem isConj_t0 (ha7 : Work.GW2.A7ModelProp) (t : alternatingGroup (Fin 7))
    (ht : orderOf t = 2) : IsConj t0 t := by
  rw [isConj_iff]
  obtain ⟨hcardA7, -, hcent, -⟩ := ha7
  have hcardC : Nat.card ↥Cent = 24 := hcent t0 orderOf_t0
  have hidx : (Subgroup.centralizer ({t0} : Set (alternatingGroup (Fin 7)))).index = 105 := by
    have h := Subgroup.index_mul_card (Subgroup.centralizer ({t0} : Set (alternatingGroup (Fin 7))))
    rw [hcardC, hcardA7] at h
    omega
  have hclass : (Finset.univ.image (fun g : alternatingGroup (Fin 7) => g * t0 * g⁻¹)).card = 105 := by
    rw [card_image_conj_eq_index, hidx]
  have hsub : (Finset.univ.image (fun g : alternatingGroup (Fin 7) => g * t0 * g⁻¹)) ⊆
      (Finset.univ.filter (fun x : alternatingGroup (Fin 7) => x ≠ 1 ∧ x * x = 1)) := by
    intro y hy
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hy
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro h
      have h1 : t0 = 1 := by
        have hconj := congrArg (fun z => g⁻¹ * z * g) h
        simpa [mul_assoc] using hconj
      exact Work.A7.a7Invol_ne_one h1
    · calc (g * t0 * g⁻¹) * (g * t0 * g⁻¹) = g * (t0 * t0) * g⁻¹ := by group
        _ = 1 := by rw [Work.A7.a7Invol_mul_self]; group
  have heq : (Finset.univ.image (fun g : alternatingGroup (Fin 7) => g * t0 * g⁻¹)) =
      (Finset.univ.filter (fun x : alternatingGroup (Fin 7) => x ≠ 1 ∧ x * x = 1)) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [involution_card, hclass])
  have htmem : t ∈ (Finset.univ.filter (fun x : alternatingGroup (Fin 7) => x ≠ 1 ∧ x * x = 1)) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro h
      rw [h, orderOf_one] at ht
      omega
    · rw [← pow_two, ← ht, pow_orderOf_eq_one]
  rw [← heq] at htmem
  obtain ⟨g, -, hg⟩ := Finset.mem_image.mp htmem
  exact ⟨g, hg⟩

/-! ## Excluding subgroup orders `5` and `9` -/

lemma false_of_card_five_or_nine (P : Subgroup (alternatingGroup (Fin 7)))
    (hC : Cent ≤ Subgroup.normalizer (P : Set (alternatingGroup (Fin 7))))
    (hodd : Odd (Nat.card ↥P)) (hcard : Nat.card ↥P = 5 ∨ Nat.card ↥P = 9) : False := by
  have hinv := ftop_invariant hC
  rcases invariant_classification (ftop P) hinv with h | h | h | h
  · -- the fixed point set is empty: `P` would be transitive, so `7 ∣ |P|`
    have htrans : ∀ q q' : Fin 7, ∃ x ∈ P, x • q = q' := by
      rcases orbit_dichotomy P hodd with hfix | htr
      · obtain ⟨q, hq⟩ := hfix
        exfalso
        have : q ∈ ftop P := fun x hx => hq x hx
        rw [h] at this
        exact this
      · intro q q'
        obtain ⟨x, hx, hxq⟩ := htr q q'
        exact ⟨x, hx, by simpa [smul_eq_apply] using hxq⟩
    have horbit : MulAction.orbit P (0 : Fin 7) = Set.univ := by
      ext q
      refine ⟨fun _ => Set.mem_univ q, fun _ => ?_⟩
      obtain ⟨x, hx, hxq⟩ := htrans 0 q
      exact MulAction.mem_orbit_iff.mpr ⟨⟨x, hx⟩, by simpa [Subgroup.smul_def] using hxq⟩
    have hindex : (MulAction.stabilizer P (0 : Fin 7)).index = 7 := by
      rw [MulAction.index_stabilizer, horbit, Set.ncard_univ, Nat.card_fin]
    have h7 : 7 ∣ Nat.card ↥P := by
      have h := Subgroup.index_dvd_card (MulAction.stabilizer P (0 : Fin 7))
      rwa [hindex] at h
    rcases hcard with h5 | h9 <;> omega
  · -- the fixed point set is `{4,5,6}`: `P` lies in a pointwise stabilizer of order `12`
    have hle : P ≤ fixingSubgroup (alternatingGroup (Fin 7)) ({4,5,6} : Set (Fin 7)) := by
      intro x hx
      rw [mem_fixingSubgroup_iff]
      intro q hq
      have hq' : q ∈ ftop P := by rw [h]; exact hq
      exact hq' x hx
    have hdvd : Nat.card ↥P ∣ 12 := by
      have h := Subgroup.card_dvd_of_le hle
      rwa [fixingSubgroup456_card] at h
    rcases hcard with h5 | h9
    · rw [h5] at hdvd; norm_num at hdvd
    · rw [h9] at hdvd; norm_num at hdvd
  · -- the fixed point set is `{0,1,2,3}`: `P` lies in `⟨(4 5 6)⟩`, of order `3`
    have hle : P ≤ fixingSubgroup (alternatingGroup (Fin 7)) ({0,1,2,3} : Set (Fin 7)) := by
      intro x hx
      rw [mem_fixingSubgroup_iff]
      intro q hq
      have hq' : q ∈ ftop P := by rw [h]; exact hq
      exact hq' x hx
    have hdvd : Nat.card ↥P ∣ 3 := by
      have h := Subgroup.card_dvd_of_le (hle.trans fixingSubgroup0123_le_zpowers)
      rwa [Nat.card_zpowers, Work.A7.orderOf_a7ThreeCycle] at h
    rcases hcard with h5 | h9
    · rw [h5] at hdvd; norm_num at hdvd
    · rw [h9] at hdvd; norm_num at hdvd
  · -- the fixed point set is everything: `P` is trivial
    have hbot : P = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      apply Subtype.ext
      apply Equiv.ext
      intro q
      have hq' : q ∈ ftop P := by rw [h]; exact Set.mem_univ q
      exact hq' x hx
    rw [hbot, Subgroup.card_bot] at hcard
    rcases hcard with h5 | h9 <;> omega

/-! ## The model statement -/

theorem centInvariant_at_t0 (ha7 : Work.GW2.A7ModelProp) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (P : Subgroup (alternatingGroup (Fin 7))) (hP : IsPGroup p P)
    (hC : Cent ≤ Subgroup.normalizer (P : Set (alternatingGroup (Fin 7)))) :
    P ≤ Cent := by
  obtain ⟨hcardA7, -, hcent, hodd_le⟩ := ha7
  by_cases hbot : P = ⊥
  · rw [hbot]; exact bot_le
  have hprime : Nat.Prime p := Fact.out
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
  have hodd : Odd (Nat.card ↥P) := by
    rw [hm]
    exact Odd.pow (hprime.odd_of_ne_two hp)
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, pow_zero] at hm
      exact absurd (Subgroup.card_eq_one.mp hm) hbot
    · exact h
  have hle : p ^ m ≤ 21 := by
    rw [← hm]
    exact hodd_le P hodd
  have hdvd : p ^ m ∣ 2520 := by
    rw [← hm]
    have h := Subgroup.card_subgroup_dvd_card P
    rwa [hcardA7] at h
  have hcases := pow_card_cases hprime hp hmpos hle hdvd
  rw [← hm] at hcases
  rcases hcases with h3 | h5 | h7 | h9
  · -- `|P| = 3`
    obtain ⟨x, hxP, hxgen, hxord⟩ := exists_zpowers_of_prime_card (by norm_num : Nat.Prime 3) h3
    have hinv := ftop_invariant hC
    have hfixn : (ftop (Subgroup.zpowers x)).ncard = 1 ∨
        (ftop (Subgroup.zpowers x)).ncard = 4 := by
      rw [ftop_zpowers]
      have hcoe : ({q : Fin 7 | x • q = q} : Set (Fin 7)) =
          ↑(Finset.univ.filter (fun q : Fin 7 => x • q = q)) := by
        ext q; simp
      rw [hcoe, Set.ncard_coe_finset]
      exact fixFinset_card_of_order_three x hxord
    rcases invariant_classification (ftop P) hinv with h | h | h | h
    · exfalso
      have : (ftop (Subgroup.zpowers x)).ncard = 0 := by
        rw [← hxgen, h]; simp
      omega
    · exfalso
      have h3n : ({4,5,6} : Set (Fin 7)).ncard = 3 := by
        rw [show ({4,5,6} : Set (Fin 7)) = ↑({4,5,6} : Finset (Fin 7)) by ext q; simp]
        simp
      have : (ftop (Subgroup.zpowers x)).ncard = 3 := by
        rw [← hxgen, h]; exact h3n
      omega
    · have hle : P ≤ fixingSubgroup (alternatingGroup (Fin 7)) ({0,1,2,3} : Set (Fin 7)) := by
        intro y hy
        rw [mem_fixingSubgroup_iff]
        intro q hq
        have hq' : q ∈ ftop P := by rw [h]; exact hq
        exact hq' y hy
      exact hle.trans (fixingSubgroup0123_le_zpowers.trans zpowers_c3_le_Cent)
    · exfalso
      have : (ftop (Subgroup.zpowers x)).ncard = 7 := by
        rw [← hxgen, h, Set.ncard_univ, Nat.card_fin]
      omega
  · exact (false_of_card_five_or_nine P hC hodd (Or.inl h5)).elim
  · -- `|P| = 7`
    obtain ⟨x, hxP, hxgen, hxord⟩ := exists_zpowers_of_prime_card (by norm_num : Nat.Prime 7) h7
    have hcardC : Nat.card ↥Cent = 24 := hcent t0 orderOf_t0
    have hN : Nat.card ↥(Subgroup.normalizer (P : Set (alternatingGroup (Fin 7)))) = 21 := by
      rw [hxgen]
      exact normalizer_zpowers_order_seven x hxord
    have hdvd : Nat.card ↥Cent ∣ 21 := by
      have h := Subgroup.card_dvd_of_le hC
      rwa [hN] at h
    have : (24 : ℕ) ∣ 21 := by rw [← hcardC]; exact hdvd
    omega
  · exact (false_of_card_five_or_nine P hC hodd (Or.inr h9)).elim

theorem centInvariant_a7 (ha7 : Work.GW2.A7ModelProp) : CentInvariant (alternatingGroup (Fin 7)) := by
  intro t ht p hp hp2 P hP hC
  obtain ⟨g, hg⟩ := isConj_t0 ha7 t ht
  let c : alternatingGroup (Fin 7) := ↑g
  have hc : c * t0 = t * c := hg
  let ψ : alternatingGroup (Fin 7) ≃* alternatingGroup (Fin 7) := MulAut.conj c
  have hψ : ψ t0 = t := by
    change MulAut.conj c t0 = t
    rw [MulAut.conj_apply, hc]
    group
  have hCmap : Subgroup.map ψ.toMonoidHom Cent =
      Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 7))) := by
    have h := map_centralizer_singleton_equiv ψ t0
    rw [hψ] at h
    exact h
  have hsymm : Subgroup.map ψ.symm.toMonoidHom
      (Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 7)))) = Cent := by
    rw [← hCmap, Subgroup.map_map]
    have hcomp : ψ.symm.toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id _ := by
      ext x; simp
    rw [hcomp, Subgroup.map_id]
  set P' : Subgroup (alternatingGroup (Fin 7)) := Subgroup.map ψ.symm.toMonoidHom P with hP'def
  have hP'p : IsPGroup p P' := hP.map ψ.symm.toMonoidHom
  have hC' : Cent ≤ Subgroup.normalizer (P' : Set (alternatingGroup (Fin 7))) := by
    calc Cent = Subgroup.map ψ.symm.toMonoidHom
          (Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 7)))) := hsymm.symm
      _ ≤ Subgroup.map ψ.symm.toMonoidHom
            (Subgroup.normalizer (P : Set (alternatingGroup (Fin 7)))) := Subgroup.map_mono hC
      _ = Subgroup.normalizer (P' : Set (alternatingGroup (Fin 7))) := by
            rw [hP'def]; exact Subgroup.map_equiv_normalizer_eq P ψ.symm
  have hres := centInvariant_at_t0 ha7 p hp2 P' hP'p hC'
  have hPmap : Subgroup.map ψ.toMonoidHom P' = P := by
    rw [hP'def, Subgroup.map_map]
    have hcomp : ψ.toMonoidHom.comp ψ.symm.toMonoidHom = MonoidHom.id _ := by
      ext x; simp
    rw [hcomp, Subgroup.map_id]
  calc P = Subgroup.map ψ.toMonoidHom P' := hPmap.symm
    _ ≤ Subgroup.map ψ.toMonoidHom Cent := Subgroup.map_mono hres
    _ = Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 7))) := hCmap

end A7Ha7

/-- **The `A₇` case of Bender 1.10(i)**, derived from the model facts `ha7 : Work.GW2.A7ModelProp`.

`ha7` provides `|A₇| = 2520`, `Sylow 2(A₇) ≅ DihedralGroup 4`, `|C_{A₇}(t)| = 24` for every
involution `t`, and `|P| ≤ 21` for every odd-order subgroup `P`; these are all the `A₇` facts
needed.

**IMPORTANT (clash warning).**  Do NOT import `Submission.Work.A7F.*` (nor `AUTA7`, `RED`,
`GLUE`, `BMAX`, `ASM.Assembly`): those modules re-declare the `Work.GW2` vocabulary
(`Work.GW2.A7ModelProp`, `Work.GW2.oddCore`, ...), and importing one of them together with
`Submission.Work.DSTR.Defs` is a hard error
(`environment already contains 'Work.GW2.A7ModelProp'`).  Permitted imports are
`Mathlib`, `Submission.Work.DSTR.D110iDefs`, `Submission.Work.DSTR.Defs` and
`Submission.Work.A7.Defs` (namespace `Work.A7`, clash-free).  The `A₇`-specific facts not
supplied by `ha7` (orbit dichotomy, `|N(⟨x⟩)| = 21` for `x` of order `7`, the pointwise
stabilizers, conjugacy of involutions) must be proved here from scratch. -/
theorem A7CentInvariantHa7 (ha7 : Work.GW2.A7ModelProp) (Q : Type*) [Group Q] [Finite Q]
    (e : Q ≃* alternatingGroup (Fin 7)) : Work.DSTR.CentInvariant Q := by
  intro t ht p hp hp2 P hP hC
  have ht' : orderOf (e t) = 2 := by
    rw [MulEquiv.orderOf_eq]; exact ht
  have hP' : IsPGroup p (Subgroup.map e.toMonoidHom P) := hP.map e.toMonoidHom
  have hC' : Subgroup.centralizer ({e t} : Set (alternatingGroup (Fin 7))) ≤
      Subgroup.normalizer (Subgroup.map e.toMonoidHom P :
        Set (alternatingGroup (Fin 7))) := by
    have hcen : Subgroup.centralizer ({e t} : Set (alternatingGroup (Fin 7))) =
        Subgroup.map e.toMonoidHom (Subgroup.centralizer ({t} : Set Q)) := by
      rw [A7Ha7.map_centralizer_singleton_equiv e t]
    rw [hcen]
    calc Subgroup.map e.toMonoidHom (Subgroup.centralizer ({t} : Set Q))
        ≤ Subgroup.map e.toMonoidHom (Subgroup.normalizer (P : Set Q)) := Subgroup.map_mono hC
      _ = Subgroup.normalizer (Subgroup.map e.toMonoidHom P :
            Set (alternatingGroup (Fin 7))) := Subgroup.map_equiv_normalizer_eq P e
  have hres := A7Ha7.centInvariant_a7 ha7 (e t) ht' p hp2 (Subgroup.map e.toMonoidHom P) hP' hC'
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hy' : e y ∈ Subgroup.map e.toMonoidHom P := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
  have hcomm := hres hy'
  rw [Subgroup.mem_centralizer_singleton_iff] at hcomm
  apply e.injective
  simpa using hcomm

end Work.DSTR
