import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.e9c_extLoc_conj_zero
import Submission.Work.SSGRoute.extIdele_localisation_injective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E7cOmega

open SSGRoute.PTExt CategoryTheory

noncomputable section

/-- `extLoc` is additive, hence kills differences. -/
theorem extLoc_sub_local {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r : ℕ} (u : NK.GlobalCFT.Place K)
    (a b : Abelian.Ext M (idelesK k K) r) :
    extLoc (k := k) (K := K) u (a - b)
      = extLoc (k := k) (K := K) u a - extLoc (k := k) (K := K) u b := by
  have hneg : extLoc (k := k) (K := K) u (-b) = -extLoc (k := k) (K := K) u b := by
    have h := extLoc_add (k := k) (K := K) u (-b) b
    rw [neg_add_cancel, extLoc_zero (k := k) (K := K) u] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  rw [sub_eq_add_neg, extLoc_add, hneg, sub_eq_add_neg]

/-- **Equality of orbit-supported idèle `H²`-classes from their equalisation at a single place.**

Two classes `q, q' ∈ H²(Gal(L/k), 𝕀_L)` whose localisations vanish at every place outside the
`Gal(L/k)`-orbit of `r`, and which have the same `r`-localisation, are equal: the difference
`q - q'` localises to `0` at `r`, hence — by conjugation (`e9c_extLoc_conj_zero`) — at every place
of the orbit, and it vanishes outside the orbit by hypothesis, so the idèle localisation is
injective (`extIdele_localisation_injective`) and `q - q' = 0`. -/
theorem eq_of_extLoc_eq_of_orbitSupported {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (r : NK.GlobalCFT.Place L) (q q' : SSGRoute.PTExt.extH (SSGRoute.PTExt.idelesK k L) 2)
    (hq : ∀ v : NK.GlobalCFT.Place L, (∀ σ : L ≃ₐ[k] L, σ • r ≠ v) →
      SSGRoute.PTExt.extLoc (k := k) (K := L) v q = 0)
    (hq' : ∀ v : NK.GlobalCFT.Place L, (∀ σ : L ≃ₐ[k] L, σ • r ≠ v) →
      SSGRoute.PTExt.extLoc (k := k) (K := L) v q' = 0)
    (h : SSGRoute.PTExt.extLoc (k := k) (K := L) r q
        = SSGRoute.PTExt.extLoc (k := k) (K := L) r q') : q = q' := by
  have key : q - q' = 0 := by
    refine Work.SSGRoute.extIdele_localisation_injective k L (q - q') ?_
    intro v
    rw [Work.SSGRoute.extRes_eq_extHRestrict
      (D := SSGRoute.PTExt.decompK (k := k) (K := L) v) (q - q')]
    change SSGRoute.PTExt.extLoc (k := k) (K := L) v (q - q') = 0
    by_cases hv : ∃ σ : L ≃ₐ[k] L, σ • r = v
    · obtain ⟨σ, rfl⟩ := hv
      have h0 : SSGRoute.PTExt.extLoc (k := k) (K := L) r (q - q') = 0 := by
        rw [extLoc_sub_local, h, sub_self]
      exact Work.SSGRoute.e9c_extLoc_conj_zero (k := k) (K := L) (q - q') σ r h0
    · have hv' : ∀ σ : L ≃ₐ[k] L, σ • r ≠ v := fun σ hσ => hv ⟨σ, hσ⟩
      rw [extLoc_sub_local, hq v hv', hq' v hv', sub_self]
  exact sub_eq_zero.mp key

end

end Work.SSGRoute.E7cOmega
