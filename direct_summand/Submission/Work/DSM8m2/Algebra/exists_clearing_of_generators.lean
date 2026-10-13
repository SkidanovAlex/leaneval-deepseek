import Mathlib

namespace Work.DSM8m2.Algebra

/-- Cleared-generators principle for a subalgebra `S` of a field `L`.

If every element of a finite generating set `gens` of an `A`-algebra `B` becomes,
after multiplication by some nonzero element of `A`, an element of `S` (under the
`A`-algebra map `φ : B →ₐ[A] L`), then there is a single nonzero `c : A` which
"clears" *every* element of `B` up to a power:

`∀ b : B, ∃ k : ℕ, φ b * (algebraMap A L c) ^ k ∈ S`.

The proof proceeds by `Algebra.adjoin_induction` for the fixed element
`c₀ = ∏ g ∈ gens, c_g`: an element `x` is called cleared if some power of
`algebraMap A L c₀` brings `φ x` into `S`.  This predicate is stable under `+`,
`*` and the structure map, and holds for each generator by construction.  If the
product `c₀` is nonzero we are done; otherwise (since `L` is a field) one of the
factors `c_g` already has zero image in `L`, so it clears every element at once. -/
lemma exists_clearing_of_generators {A L B : Type*} [CommRing A] [Field L] [Algebra A L]
    [CommRing B] [Algebra A B] (φ : B →ₐ[A] L) (gens : Finset B)
    (hgens : Algebra.adjoin A (gens : Set B) = ⊤) (S : Subalgebra A L)
    (hgen : ∀ g ∈ gens, ∃ c : A, c ≠ 0 ∧ φ g * algebraMap A L c ∈ S) :
    ∃ c : A, c ≠ 0 ∧ ∀ b : B, ∃ k : ℕ, φ b * (algebraMap A L c) ^ k ∈ S := by
  classical
  -- Choose for each generator `g` a nonzero clearing element `C g`.
  let C : B → A := fun g => if h : g ∈ gens then Classical.choose (hgen g h) else 1
  have hC_spec : ∀ g (hg : g ∈ gens), C g ≠ 0 ∧ φ g * algebraMap A L (C g) ∈ S := by
    intro g hg
    have h1 : C g = Classical.choose (hgen g hg) := by
      simp only [C]; exact dite_eq_left hg
    rw [h1]; exact Classical.choose_spec (hgen g hg)
  let c0 : A := ∏ g ∈ gens, C g
  -- Every element of `B` is cleared by `c0`.
  have hP : ∀ b : B, ∃ k : ℕ, φ b * (algebraMap A L c0) ^ k ∈ S := by
    intro b
    have hb : b ∈ Algebra.adjoin A (gens : Set B) := by rw [hgens]; trivial
    refine Algebra.adjoin_induction
      (p := fun x _ => ∃ k : ℕ, φ x * (algebraMap A L c0) ^ k ∈ S) ?_ ?_ ?_ ?_ hb
    · -- generators
      intro g hg
      obtain ⟨hCne, hCS⟩ := hC_spec g hg
      refine ⟨1, ?_⟩
      have hdecomp : c0 = C g * ∏ g' ∈ gens.erase g, C g' := by
        simp only [c0]; exact (Finset.mul_prod_erase gens C hg).symm
      have ha : algebraMap A L c0
          = algebraMap A L (C g) * algebraMap A L (∏ g' ∈ gens.erase g, C g') := by
        rw [hdecomp, map_mul]
      rw [pow_one, ha, ← mul_assoc]
      exact S.mul_mem hCS (Subalgebra.algebraMap_mem S _)
    · -- the structure map
      intro r
      refine ⟨0, ?_⟩
      rw [pow_zero, mul_one, AlgHom.commutes]
      exact Subalgebra.algebraMap_mem S r
    · -- closure under addition
      intro x y hx hy hpx hpy
      obtain ⟨kx, hkx⟩ := hpx
      obtain ⟨ky, hky⟩ := hpy
      have hax : (algebraMap A L c0) ^ kx ∈ S := by
        rw [← map_pow]; exact Subalgebra.algebraMap_mem S _
      have hay : (algebraMap A L c0) ^ ky ∈ S := by
        rw [← map_pow]; exact Subalgebra.algebraMap_mem S _
      refine ⟨kx + ky, ?_⟩
      rw [map_add, add_mul, pow_add]
      apply S.add_mem
      · rw [← mul_assoc]; exact S.mul_mem hkx hay
      · rw [show φ y * ((algebraMap A L c0) ^ kx * (algebraMap A L c0) ^ ky)
            = φ y * (algebraMap A L c0) ^ ky * (algebraMap A L c0) ^ kx by ring]
        exact S.mul_mem hky hax
    · -- closure under multiplication
      intro x y hx hy hpx hpy
      obtain ⟨kx, hkx⟩ := hpx
      obtain ⟨ky, hky⟩ := hpy
      refine ⟨kx + ky, ?_⟩
      rw [map_mul, pow_add,
        show φ x * φ y * ((algebraMap A L c0) ^ kx * (algebraMap A L c0) ^ ky)
          = φ x * (algebraMap A L c0) ^ kx * (φ y * (algebraMap A L c0) ^ ky) by ring]
      exact S.mul_mem hkx hky
  by_cases hc0 : c0 = 0
  · -- `c0 = 0`: one of the factors already vanishes in the field `L`
    have h0 : (∏ g ∈ gens, algebraMap A L (C g)) = 0 := by
      rw [← map_prod]
      show algebraMap A L c0 = 0
      rw [hc0, map_zero]
    obtain ⟨g, hg, hgz⟩ := (Finset.prod_eq_zero_iff (s := gens)
      (f := fun g => algebraMap A L (C g))).mp h0
    obtain ⟨hCne, -⟩ := hC_spec g hg
    exact ⟨C g, hCne, fun b => ⟨1, by rw [pow_one, hgz, mul_zero]; exact S.zero_mem⟩⟩
  · exact ⟨c0, hc0, hP⟩

end Work.DSM8m2.Algebra
