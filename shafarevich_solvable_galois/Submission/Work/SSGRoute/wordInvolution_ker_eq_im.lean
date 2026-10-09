import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- Auxiliary: `FreeMonoid.map σ` is an involution when `σ` is. -/
theorem wordInvolution_ker_eq_im (X : Type*) (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x)
    (hfree : ∀ x, σ x ≠ x) (j : ℕ) (hj : 1 ≤ j) (x : FreeMonoid X →₀ ZMod 2)
    (hlen : ∀ w : FreeMonoid X, x w ≠ 0 → (FreeMonoid.toList w).length = j)
    (hfix : x + Finsupp.mapDomain (FreeMonoid.map σ) x = 0) :
    ∃ t : FreeMonoid X →₀ ZMod 2,
      (∀ w : FreeMonoid X, t w ≠ 0 → (FreeMonoid.toList w).length = j) ∧
      x = t + Finsupp.mapDomain (FreeMonoid.map σ) t := by
  classical
  let φ : FreeMonoid X →* FreeMonoid X := FreeMonoid.map σ
  have hff : ∀ w, φ (φ w) = w := by
    intro w
    have hcomp : φ.comp φ = MonoidHom.id (FreeMonoid X) := by
      show (FreeMonoid.map σ).comp (FreeMonoid.map σ) = MonoidHom.id (FreeMonoid X)
      rw [← FreeMonoid.map_comp]
      rw [show (⇑σ ∘ ⇑σ) = id from funext (fun a => hσ a), FreeMonoid.map_id]
    have := congrArg (fun g : FreeMonoid X →* FreeMonoid X => g w) hcomp
    simpa [MonoidHom.comp_apply] using this
  have hinj : Function.Injective φ := by
    intro a b hab
    have h := congrArg φ hab
    rwa [hff a, hff b] at h
  have hnegx : -x = x := by
    apply Finsupp.ext
    intro w
    rw [Finsupp.neg_apply]
    exact CharTwo.neg_eq (x w)
  have hmapx : Finsupp.mapDomain φ x = x := by
    have h' : x + Finsupp.mapDomain φ x = 0 := by
      have hh := hfix
      simpa [φ] using hh
    have hM : -x = Finsupp.mapDomain φ x := neg_eq_iff_add_eq_zero.mpr h'
    rw [hM.symm, hnegx]
  have hxφ : ∀ w, x (φ w) = x w := by
    intro w
    have h := Finsupp.mapDomain_apply_of_injective (f := φ) hinj x w
    rw [hmapx] at h
    exact h
  have list_map_self : ∀ l : List X, l.map (⇑σ) = l → l = [] := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a t ih =>
      intro h
      rw [List.map_cons] at h
      have hh := (List.cons.injEq _ _ _ _).mp h
      exact absurd hh.1 (hfree a)
  have hfix_eq_one : ∀ w : FreeMonoid X, φ w = w ↔ w = 1 := by
    intro w
    constructor
    · intro h
      have hmap : (FreeMonoid.toList w).map (⇑σ) = FreeMonoid.toList w := by
        rw [← FreeMonoid.toList_map]
        exact congrArg FreeMonoid.toList h
      have hnil : FreeMonoid.toList w = [] := list_map_self (FreeMonoid.toList w) hmap
      exact FreeMonoid.toList.injective (by rw [hnil, FreeMonoid.toList_one])
    · intro h
      rw [h]; exact map_one φ
  let r : FreeMonoid X → FreeMonoid X → Prop := fun v w => v = w ∨ v = φ w
  have hr : Equivalence r := by
    refine ⟨?_, ?_, ?_⟩
    · intro a; exact Or.inl rfl
    · intro a b hab
      rcases hab with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, hff b])
    · intro a b c hab hbc
      rcases hab with h1 | h1 <;> rcases hbc with h2 | h2
      · exact Or.inl (by rw [h1, h2])
      · exact Or.inr (by rw [h1, h2])
      · exact Or.inr (by rw [h1, h2])
      · exact Or.inl (by rw [h1, h2, hff c])
  let S : Setoid (FreeMonoid X) := ⟨r, hr⟩
  let rep : FreeMonoid X → FreeMonoid X := fun w => Quotient.out (Quotient.mk S w)
  have hrep_mem : ∀ w, rep w = w ∨ rep w = φ w := by
    intro w
    have h : Quotient.mk S (rep w) = Quotient.mk S w := Quotient.out_eq (Quotient.mk S w)
    exact Quotient.exact h
  have hrep_inv : ∀ w, rep (φ w) = rep w := by
    intro w
    have h : Quotient.mk S (φ w) = Quotient.mk S w := Quotient.sound (Or.inr rfl)
    exact congrArg Quotient.out h
  let t : FreeMonoid X →₀ ZMod 2 := x.filter (fun w => rep w = w)
  have ht_apply : ∀ w, t w = (if rep w = w then x w else 0) := by
    intro w; rw [Finsupp.filter_apply]
  have htφ : ∀ w, (Finsupp.mapDomain φ t) w = t (φ w) := by
    intro w
    have h := Finsupp.mapDomain_apply_of_injective (f := φ) hinj t (φ w)
    rwa [hff w] at h
  refine ⟨t, ?_, ?_⟩
  · intro w htw
    have hxw : x w ≠ 0 := by
      intro hxw0
      apply htw
      rw [ht_apply w]
      by_cases hp : rep w = w <;> simp [hp, hxw0]
    exact hlen w hxw
  · apply Finsupp.ext
    intro w
    rw [Finsupp.add_apply, htφ w]
    by_cases hxw0 : x w = 0
    · have ht1 : t w = 0 := by
        rw [ht_apply w]
        by_cases hp : rep w = w <;> simp [hp, hxw0]
      have ht2 : t (φ w) = 0 := by
        rw [ht_apply (φ w)]
        have hxφw : x (φ w) = 0 := by rw [hxφ w, hxw0]
        by_cases hp : rep (φ w) = φ w <;> simp [hp, hxφw]
      rw [ht1, ht2, hxw0]; simp
    · have hlen_w := hlen w hxw0
      have hw_ne : w ≠ φ w := by
        intro h
        have h1 : w = 1 := (hfix_eq_one w).mp h.symm
        rw [h1, FreeMonoid.toList_one] at hlen_w
        simp at hlen_w
        omega
      by_cases hp : rep w = w
      · have ht1 : t w = x w := by rw [ht_apply w, if_pos hp]
        have ht2 : t (φ w) = 0 := by
          rw [ht_apply (φ w)]
          have hne : ¬ (rep (φ w) = φ w) := by
            intro h
            apply hw_ne
            calc w = rep w := hp.symm
              _ = rep (φ w) := (hrep_inv w).symm
              _ = φ w := h
          simp [hne]
        rw [ht1, ht2]; simp
      · have hrepw : rep w = φ w := (hrep_mem w).resolve_left hp
        have ht1 : t w = 0 := by rw [ht_apply w, if_neg hp]
        have ht2 : t (φ w) = x (φ w) := by
          rw [ht_apply (φ w), if_pos]
          rw [hrep_inv]; exact hrepw
        rw [ht1, ht2, hxφ w]; simp

end Work.SSGRoute
