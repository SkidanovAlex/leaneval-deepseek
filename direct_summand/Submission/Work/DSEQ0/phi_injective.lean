import Mathlib
import Submission.Work.DSMap.Map

open CategoryTheory AlgebraicGeometry

universe a

namespace Work.DSEQ0

/-- For `f : X ⟶ Spec A`, the ring map `DSMap.phi A X f : A → Γ(X,⊤)` (the adjoint of `f`
under the `Γ ⊣ Spec` adjunction) determines `f` via `f = X.toSpecΓ ≫ Spec.map φ`. -/
lemma f_eq_toSpecΓ_comp (A : Type a) [CommRing A] (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) :
    f = X.toSpecΓ ≫ Scheme.Spec.map
      ((ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of A))).symm f) := by
  set ψ := (ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of A))).symm f with hψdef
  have hψ : (ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of A))) ψ = f :=
    Equiv.apply_symm_apply _ f
  have hunit : (ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of A))) ψ =
      ΓSpec.adjunction.unit.app X ≫ Scheme.Spec.map ψ :=
    Adjunction.homEquiv_unit ΓSpec.adjunction X (Opposite.op (CommRingCat.of A)) ψ
  exact hψ.symm.trans hunit

/-- **DSEQ0**: for a reduced ring `A` and a surjective `f : X ⟶ Spec A`, the induced global
sections map `A → Γ(X, 𝒪_X)` is injective. Every prime of `A` lies in the image of `f`, so the
image of `a` under `A → κ(f x)` is `φ a` in the residue field; hence `φ a = 0` forces `a` to lie
in every prime of the reduced ring `A`, i.e. `a = 0`. -/
theorem phi_injective (A : Type a) [CommRing A] [IsReduced A] (X : AlgebraicGeometry.Scheme.{a})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) (hs : Function.Surjective f) :
    Function.Injective (DSMap.phi A X f) := by
  have hker : ∀ a : A, DSMap.phi A X f a = 0 → a = 0 := by
    intro a ha
    set ψ := (ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of A))).symm f with hψdef
    have hf : f = X.toSpecΓ ≫ Scheme.Spec.map ψ := by
      rw [hψdef]; exact f_eq_toSpecΓ_comp A X f
    have hφ : ψ.unop.hom = DSMap.phi A X f := rfl
    have hφa : ψ.unop.hom a = 0 := by rw [hφ]; exact ha
    have hsp : Scheme.Spec.map ψ = Spec.map ψ.unop := rfl
    have hprime : ∀ p : PrimeSpectrum A, a ∈ p.asIdeal := by
      intro p
      obtain ⟨x, hx⟩ := hs p
      have h1 : f x = Scheme.Spec.map ψ (X.toSpecΓ x) := by rw [hf]; rfl
      have hpx : Scheme.Spec.map ψ (X.toSpecΓ x) = p := h1.symm.trans hx
      have hpt : Spec.map ψ.unop (X.toSpecΓ x) =
          PrimeSpectrum.comap ψ.unop.hom (X.toSpecΓ x) := Spec.map_apply ψ.unop (X.toSpecΓ x)
      have hkey : p.asIdeal = Ideal.comap ψ.unop.hom (X.toSpecΓ x).asIdeal := by
        rw [← hpx, hsp, hpt]
        exact PrimeSpectrum.comap_asIdeal ψ.unop.hom (X.toSpecΓ x)
      rw [hkey]
      change ψ.unop.hom a ∈ (X.toSpecΓ x).asIdeal
      rw [hφa]
      exact Submodule.zero_mem _
    have hnil : IsNilpotent a := nilpotent_iff_mem_prime.mpr (fun J hJ => hprime ⟨J, hJ⟩)
    exact IsReduced.eq_zero a hnil
  intro x y hxy
  have : x - y = 0 := hker (x - y) (by rw [map_sub, hxy, sub_self])
  exact sub_eq_zero.mp this

end Work.DSEQ0
