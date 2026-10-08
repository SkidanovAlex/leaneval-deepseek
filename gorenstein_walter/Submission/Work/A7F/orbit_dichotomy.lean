import Mathlib
import Submission.Work.A7F.Defs

namespace Work.A7F

/-!
## The orbit dichotomy for odd-order subgroups of `A₇`

Let `X ≤ A₇` have odd order.  Then `X` acts on the seven points of `Fin 7`, and every orbit of
this action has odd size (orbit–stabiliser, since the orbit size is the index of the stabiliser and
hence divides `|X|`, which is odd).  If `X` has no fixed point, then no orbit is a singleton, so
every orbit has at least `3` points; the orbits partition `7` points, and `7` cannot be written as a
sum of two or more odd numbers each `≥ 3` (two disjoint orbits of sizes `≥ 3` already leave at most
one point, whose orbit then has at most `1` point).  Hence there is exactly one orbit, of size `7`,
i.e. `X` is transitive.

This is the main combinatorial content of the model calculation on `A₇` (Bender 1.8).
-/

/-- The orbit of a point under a finite group of odd order has odd cardinality: it is the index of
the stabiliser, which divides `Nat.card G`, and a divisor of an odd number is odd. -/
lemma odd_ncard_orbit {G : Type*} [Group G] {α : Type*} [MulAction G α]
    (hodd : Odd (Nat.card G)) (a : α) : Odd (MulAction.orbit G a).ncard := by
  rw [← MulAction.index_stabilizer G a]
  exact Odd.of_dvd_nat hodd (Subgroup.index_dvd_card _)

/-- If a finite group of odd order acts on a set without global fixed points, then every orbit has
at least three elements: it is odd (previous lemma) and cannot be a singleton, because the orbit of
`a` is the singleton `{a}` exactly when `a` is fixed. -/
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

/-- Two distinct orbits are disjoint: an element of `orbit G a` does not lie in `orbit G b` only
when the two orbits are disjoint. -/
lemma disjoint_orbit_of_not_mem {G : Type*} [Group G] {α : Type*} [MulAction G α]
    {a b : α} (hb : b ∉ MulAction.orbit G a) :
    Disjoint (MulAction.orbit G a) (MulAction.orbit G b) := by
  rcases MulAction.orbit.eq_or_disjoint (G := G) a b with heq | hd
  · rw [heq] at hb
    exact absurd (MulAction.mem_orbit_self b) hb
  · exact hd

/-- **Orbit dichotomy.**  A finite group of odd order acting on a seven-element set either fixes a
point, or acts transitively. -/
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

theorem orbit_dichotomy (X : Subgroup (alternatingGroup (Fin 7))) (hodd : Odd (Nat.card X)) :
    (∃ p : Fin 7, ∀ x ∈ X, ((x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) p = p) ∨
      (∀ p q : Fin 7, ∃ x ∈ X, ((x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) p = q) := by
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

end Work.A7F
