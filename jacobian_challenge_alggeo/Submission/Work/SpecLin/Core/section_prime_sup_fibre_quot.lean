import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SpecLin.Core

open scoped TensorProduct in
/- the requested statement is:
theorem section_prime_sup_fibre_quot {K : Type*} [Field K] {A : Type*} [CommRing A]
    [IsDomain A] [Algebra K A] {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (φ : A →ₐ[K] R) :
    (TensorProduct K A R ⧸ (RingHom.ker (Algebra.TensorProduct.lift (S := K) φ
      (AlgHom.id K R) (fun _ _ => Commute.all _ _)).toRingHom ⊔
        (IsLocalRing.maximalIdeal R).map (Algebra.TensorProduct.includeRight (A := A))))
      ≃+* IsLocalRing.ResidueField R
-/

/-- **Transversality of a section and the special fibre.** -/
noncomputable def section_prime_sup_fibre_quot {K : Type*} [Field K] {A : Type*} [CommRing A]
    [IsDomain A] [Algebra K A] {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (φ : A →ₐ[K] R) :
    (TensorProduct K A R ⧸ (RingHom.ker (Algebra.TensorProduct.lift (S := K) φ
      (AlgHom.id K R) (fun _ _ => Commute.all _ _)).toRingHom ⊔
        (IsLocalRing.maximalIdeal R).map (Algebra.TensorProduct.includeRight (A := A))))
      ≃+* IsLocalRing.ResidueField R := by
  let ev : A ⊗[K] R →ₐ[K] R :=
    Algebra.TensorProduct.lift (S := K) φ (AlgHom.id K R) (fun _ _ => Commute.all _ _)
  let m : Ideal R := IsLocalRing.maximalIdeal R
  have hinc : ∀ r : R,
      ev (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R) r) = r := by
    intro r
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul]
    simp
  have hsurj : Function.Surjective ev := fun r => ⟨_, hinc r⟩
  have hkey : ∀ x : A ⊗[K] R,
      x - Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R) (ev x) ∈
        RingHom.ker ev.toRingHom := by
    intro x
    rw [RingHom.mem_ker, map_sub]
    rw [show ev.toRingHom
          (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R) (ev x)) = ev x
        from hinc (ev x)]
    simp
  let g : A ⊗[K] R →+* (R ⧸ m) := (Ideal.Quotient.mk m).comp ev.toRingHom
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := m) y
    obtain ⟨x, hx⟩ := hsurj r
    exact ⟨x, by simp [g, hx]⟩
  have hker : RingHom.ker g = RingHom.ker ev.toRingHom ⊔
      (IsLocalRing.maximalIdeal R).map (Algebra.TensorProduct.includeRight (A := A)) := by
    have h1 : RingHom.ker g = Ideal.comap ev.toRingHom m := by
      rw [show g = (Ideal.Quotient.mk m).comp ev.toRingHom from rfl]
      rw [← RingHom.comap_ker (Ideal.Quotient.mk m) ev.toRingHom, Ideal.mk_ker]
    rw [h1]
    apply le_antisymm
    · intro x hx
      rw [Ideal.mem_comap] at hx
      have hx' : ev x ∈ m := hx
      have h1' : x - Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R) (ev x) ∈
          RingHom.ker ev.toRingHom ⊔
            (IsLocalRing.maximalIdeal R).map (Algebra.TensorProduct.includeRight (A := A)) :=
        Ideal.mem_sup_left (hkey x)
      have h2' : Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R) (ev x) ∈
          RingHom.ker ev.toRingHom ⊔
            (IsLocalRing.maximalIdeal R).map (Algebra.TensorProduct.includeRight (A := A)) :=
        Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hx')
      have := add_mem h1' h2'
      simpa using this
    · apply sup_le
      · intro x hx
        rw [RingHom.mem_ker] at hx
        rw [Ideal.mem_comap, hx]
        exact m.zero_mem
      · rw [Ideal.map_le_iff_le_comap]
        intro r hr
        rw [Ideal.mem_comap, Ideal.mem_comap]
        rw [show ev.toRingHom
              (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R) r) = r
            from hinc r]
        exact hr
  exact (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := g) hg)

end Work.SpecLin.Core
