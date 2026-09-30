import Mathlib
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 3200000

namespace Work.CurveBasics.Order

/-! ### Transport lemmas along a compatible isomorphism of the base ring -/

/-- Finiteness of a module is invariant under a compatible isomorphism of the base ring: if
`e : R ≃+* S` and the actions of `R` and `S` on `M` agree along `e` (i.e. `e r • m = r • m`),
then `Module.Finite R M` follows from `Module.Finite S M`. -/
theorem module_finite_of_ringEquiv_smul {R S M : Type*} [CommRing R] [CommRing S] [AddCommMonoid M]
    [Module R M] [Module S M] (e : R ≃+* S) (h : ∀ (r : R) (m : M), e r • m = r • m)
    (hM : Module.Finite S M) : Module.Finite R M := by
  haveI : Module.Finite S M := hM
  let f : M →ₛₗ[e.symm.toRingHom] M :=
    { toFun := fun m => m
      map_add' := fun _ _ => rfl
      map_smul' := fun s m => by
        show s • m = e.symm s • m
        simpa using h (e.symm s) m }
  exact Module.Finite.of_surjective f Function.surjective_id

/-- The minimal polynomial is stable under a compatible isomorphism of the base ring. -/
theorem minpoly_map_ringEquiv {F F' E : Type*} [Field F] [Field F'] [Field E]
    [Algebra F E] [Algebra F' E] (e : F ≃+* F')
    (h : (algebraMap F' E).comp e.toRingHom = algebraMap F E) (x : E) :
    minpoly F' x = (minpoly F x).map e.toRingHom := by
  by_cases hx : IsIntegral F x
  · have hx' : IsIntegral F' x := (RingEquiv.isIntegral_iff e h x).mp hx
    have hroot : Polynomial.aeval x ((minpoly F x).map e.toRingHom) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, h, ← Polynomial.aeval_def]
      exact minpoly.aeval F x
    have h1 : minpoly F' x ∣ (minpoly F x).map e.toRingHom := minpoly.dvd F' x hroot
    have h' : (algebraMap F E).comp e.symm.toRingHom = algebraMap F' E := by
      rw [← h]; ext a; simp
    have hroot' : Polynomial.aeval x ((minpoly F' x).map e.symm.toRingHom) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, h', ← Polynomial.aeval_def]
      exact minpoly.aeval F' x
    have h2 : minpoly F x ∣ (minpoly F' x).map e.symm.toRingHom := minpoly.dvd F x hroot'
    have hle : ((minpoly F x).map e.toRingHom).natDegree ≤ (minpoly F' x).natDegree := by
      rw [Polynomial.natDegree_map_eq_of_injective e.injective]
      calc (minpoly F x).natDegree
          ≤ ((minpoly F' x).map e.symm.toRingHom).natDegree :=
            Polynomial.natDegree_le_of_dvd h2 (by
              rw [Polynomial.map_ne_zero_iff e.symm.injective]; exact minpoly.ne_zero hx')
        _ = (minpoly F' x).natDegree := Polynomial.natDegree_map_eq_of_injective e.symm.injective _
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hx')
      ((minpoly.monic hx).map e.toRingHom) h1 hle).symm
  · have hx' : ¬ IsIntegral F' x := fun hh => hx ((RingEquiv.isIntegral_iff e h x).mpr hh)
    rw [minpoly.eq_zero hx, minpoly.eq_zero hx', Polynomial.map_zero]

/-- Normality is stable under a compatible isomorphism of the base ring. -/
theorem normal_of_ringEquiv_smul {F F' E : Type*} [Field F] [Field F'] [Field E]
    [Algebra F E] [Algebra F' E] (e : F ≃+* F')
    (h : (algebraMap F' E).comp e.toRingHom = algebraMap F E) :
    Normal F E → Normal F' E := by
  intro hN
  refine normal_iff.2 fun x => ⟨?_, ?_⟩
  · exact (RingEquiv.isIntegral_iff e h x).mp ((normal_iff.1 hN x).1)
  · rw [minpoly_map_ringEquiv e h x, Polynomial.map_map, h]
    exact (normal_iff.1 hN x).2


