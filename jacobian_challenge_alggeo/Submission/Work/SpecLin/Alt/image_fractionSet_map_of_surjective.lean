import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SpecLin.Alt

theorem image_fractionSet_map_of_surjective {A A' K : Type*} [CommRing A] [CommRing A'] [Field K]
    (φ : A →+* A') (hφ : Function.Surjective φ) (q : Ideal A) (hker : RingHom.ker φ ≤ q)
    (f : A →+* K) (f' : A' →+* K) (hf : ∀ a, f' (φ a) = f a) (x : K) :
    (∃ a b : A, b ∉ q ∧ x * f b = f a) ↔
      (∃ a' b' : A', b' ∉ Ideal.map φ q ∧ x * f' b' = f' a') := by
  constructor
  · rintro ⟨a, b, hbq, hx⟩
    refine ⟨φ a, φ b, ?_, ?_⟩
    · intro hmem
      have hb : b ∈ q := by
        have h1 : b ∈ Ideal.comap φ (Ideal.map φ q) := hmem
        rw [Ideal.comap_map_of_surjective φ hφ q, ← RingHom.ker_eq_comap_bot φ,
          sup_eq_left.mpr hker] at h1
        exact h1
      exact hbq hb
    · rw [hf b, hf a]
      exact hx
  · rintro ⟨a', b', hb', hx⟩
    obtain ⟨a, rfl⟩ := hφ a'
    obtain ⟨b, rfl⟩ := hφ b'
    refine ⟨a, b, ?_, ?_⟩
    · intro hbq
      exact hb' (Ideal.mem_map_of_mem φ hbq)
    · rw [hf b, hf a] at hx
      exact hx

end Work.SpecLin.Alt
