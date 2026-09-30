import Mathlib
import Submission.Work.CurveBasics.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false

namespace Work.CurveBasics.Order

open Work.CurveBasics in
/-- **Transfer of the finiteness of `k[x]`-integral closures along a `k`-embedding.**
Let `x` be transcendental over `k`, let `ψ : L →ₐ[k] B` be an injective `k`-algebra homomorphism of
fields, and suppose that the integral closure of `k[ψ x]` in `B` is a finite `k[ψ x]`-module.
Then the integral closure of `k[x]` in `L` is a finite `k[x]`-module.

(The point is that `ψ` restricts to an isomorphism `k[x] ≅ k[ψ x]`, that `ψ` maps the integral
closure of `k[x]` in `L` into the integral closure of `k[ψ x]` in `B`, and that a submodule of a
finite module over the Noetherian ring `k[x]` is finite.) -/
theorem kx_finite_of_embedding {k L B : Type*} [Field k] [Field L] [Field B]
    [Algebra k L] [Algebra k B] (x : L) (hx : Transcendental k x) (ψ : L →ₐ[k] B)
    (hψ : Function.Injective ψ)
    (h : Module.Finite ↥(Algebra.adjoin k ({ψ x} : Set B))
      ↥(integralClosure ↥(Algebra.adjoin k ({ψ x} : Set B)) B)) :
    Module.Finite ↥(Algebra.adjoin k ({x} : Set L))
      ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set L)) L) := by
  classical
  -- Abbreviate the two subalgebras `k[x] ⊆ L` and `k[ψ x] ⊆ B`.
  let S : Subalgebra k L := Algebra.adjoin k ({x} : Set L)
  let T : Subalgebra k B := Algebra.adjoin k ({ψ x} : Set B)
  change Module.Finite ↥S ↥(integralClosure ↥S L)
  -- `ψ` maps `S = k[x]` onto `T = k[ψ x]`.
  have hmap : Subalgebra.map ψ S = T := by
    show Subalgebra.map ψ (Algebra.adjoin k ({x} : Set L)) = Algebra.adjoin k ({ψ x} : Set B)
    exact AlgHom.map_adjoin_singleton ψ x
  -- Hence `ψ` restricts to a `k`-algebra isomorphism `σ : k[x] ≅ k[ψ x]`.
  let σ : ↥S ≃ₐ[k] ↥T :=
    (Subalgebra.equivMapOfInjective S ψ hψ).trans (Subalgebra.equivOfEq _ _ hmap)
  have hcomp : (algebraMap ↥T B).comp (σ.toRingEquiv : ↥S →+* ↥T) =
      (ψ : L →+* B).comp (algebraMap ↥S L) := by
    ext s
    simp only [RingHom.comp_apply]
    show ((σ s : ↥T) : B) = ψ ((s : ↥S) : L)
    simp only [σ, AlgEquiv.trans_apply, Subalgebra.equivOfEq_apply,
      Subalgebra.coe_equivMapOfInjective_apply]
  -- `k[x] ≅ k[X]` is Noetherian, hence so is `k[ψ x]`.
  haveI hNoethS : IsNoetherianRing ↥S :=
    isNoetherianRing_of_ringEquiv (Polynomial k)
      (Polynomial.algEquivOfTranscendental k x hx).toRingEquiv
  haveI hNoethT : IsNoetherianRing ↥T :=
    isNoetherianRing_of_ringEquiv ↥S σ.toRingEquiv
  haveI hsurj : RingHomSurjective (σ.toRingEquiv : ↥S →+* ↥T) := ⟨σ.surjective⟩
  haveI hTfin : Module.Finite ↥T ↥(integralClosure ↥T B) := h
  -- `ψ` carries `k[x]`-integral elements of `L` to `k[ψ x]`-integral elements of `B`.
  have hmem : ∀ y : ↥(integralClosure ↥S L), ψ (y : L) ∈ integralClosure ↥T B := by
    intro y
    rw [mem_integralClosure_iff]
    exact IsIntegral.map_of_comp_eq (σ.toRingEquiv : ↥S →+* ↥T) (ψ : L →+* B) hcomp
      ((mem_integralClosure_iff ↥S L).mp y.2)
  -- The `σ`-semilinear injection `k[x]^int → k[ψ x]^int`.
  let Φ : ↥(integralClosure ↥S L) →ₛₗ[(σ.toRingEquiv : ↥S →+* ↥T)] ↥(integralClosure ↥T B) :=
    { toFun := fun y => ⟨ψ (y : L), hmem y⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        show ψ ((a : L) + (b : L)) = ψ (a : L) + ψ (b : L)
        rw [map_add]
      map_smul' := by
        intro s y
        apply Subtype.ext
        have hs : ((σ.toRingEquiv s : ↥T) : B) = ψ (s : L) := by
          have h1 := congrArg (fun f : ↥S →+* B => f s) hcomp
          simpa using h1
        show ψ ((s : L) * (y : L)) = ((σ.toRingEquiv s : ↥T) : B) * ψ (y : L)
        rw [hs, map_mul] }
  rw [Module.finite_def]
  have hΦinj : Function.Injective Φ := by
    have hval : ∀ y, (Φ y : B) = ψ (y : L) := fun y => rfl
    intro a b hab
    apply Subtype.ext
    apply hψ
    rw [← hval a, ← hval b, hab]
  -- The image is a submodule of the finite `k[ψ x]`-module `k[ψ x]^int`, hence finite over the
  -- Noetherian ring `k[ψ x]`; injectivity transfers this back to `k[x]`.
  have hrange : (Submodule.map Φ ⊤).FG :=
    Submodule.FG.of_le (Module.Finite.fg_top (R := ↥T) (M := ↥(integralClosure ↥T B))) le_top
  exact (Submodule.fg_map_iff Φ hΦinj).mp hrange

end Work.CurveBasics.Order
