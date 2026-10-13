/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Injectivity of `A → A^{1/p^∞}` for a domain `A` of characteristic `p`

The `p`-perfection `pPerfection A p` is the filtered colimit of the Frobenius tower
`A --F--> A --F--> ⋯`.  Over a domain (more generally a reduced ring) of characteristic `p`
the Frobenius endomorphism is injective, hence so is every transition map of the system;
since a filtered colimit of injective maps is injective on each component
(`Ring.DirectLimit.of_injective`), the structure map `A → A^{1/p^∞}` is injective.
-/
import Mathlib
import Submission.Work.DSEQP.Perfection

namespace Work.DSEQP

/-- The direct system `A --F--> A --F--> ⋯` underlying the `p`-perfection, with the bundled
transition maps `frobPowHom A p (j - i)`.  We need this in bundled form in order to apply
`Ring.DirectLimit.of_injective`. -/
instance directedSystem_frobPowHom (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime] [CharP A p] :
    DirectedSystem (fun _ : ℕ => A) (fun i j (_ : i ≤ j) => ⇑(frobPowHom A p (j - i))) where
  map_self := by intro i x; simp [frobPowHom]
  map_map := by
    intro k j i _ _ x
    simp only [frobPowHom, RingHom.coe_pow]
    rw [← Function.iterate_add_apply, show k - j + (j - i) = k - i from by omega]

/-- Every transition map of the Frobenius tower, `frobPowHom A p n = F^n`, is injective over a
reduced ring of characteristic `p` (in particular over a domain).  This is the `n`-th iterate of
the injective Frobenius `x ↦ x ^ p`. -/
theorem frobPowHom_injective (A : Type*) [CommRing A] [IsReduced A] (p : ℕ) [Fact p.Prime]
    [CharP A p] (n : ℕ) : Function.Injective (⇑(frobPowHom A p n)) := by
  have hf : Function.Injective (⇑(frobenius A p)) := frobenius_inj A p
  rw [frobPowHom, RingHom.coe_pow]
  exact hf.iterate n

theorem pPerfection_algebraMap_injective (A : Type*) [CommRing A] [IsDomain A] (p : ℕ) [Fact p.Prime] [CharP A p] :
    Function.Injective (algebraMap A (pPerfection A p)) := by
  have hinj : ∀ i j (_ : i ≤ j), Function.Injective (⇑(frobPowHom A p (j - i))) :=
    fun i j _ => frobPowHom_injective A p (j - i)
  -- `Ring.DirectLimit.of_injective` gives injectivity of the canonical map `of 0`.
  have h := Ring.DirectLimit.of_injective (fun i j (_ : i ≤ j) => frobPowHom A p (j - i)) hinj 0
  -- `pPerfection.of 0` is the structure map, since the `Algebra` instance was built from it.
  have hmap : (algebraMap A (pPerfection A p)) = pPerfection.of (A := A) (p := p) 0 := by
    rw [show pPerfection.of (A := A) (p := p) 0 = pPerfection.algebraMap' (A := A) (p := p)
        from rfl]
    exact RingHom.algebraMap_toAlgebra _
  rw [hmap]
  exact h

end Work.DSEQP
