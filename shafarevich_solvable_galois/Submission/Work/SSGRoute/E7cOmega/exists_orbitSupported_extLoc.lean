import Mathlib
import Submission.Work.SSGRoute.ext_idele_shapiro
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.e9c_extLoc_conj_zero
import Submission.Work.SSGRoute.E7cOmega.exists_transversal_mem_of_mulAction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Orbit-supported lifts of local `H²`-classes

For a finite Galois extension `L / k` of number fields, a place `r` of `L` and a class
`a ∈ H²(D_r, L_rˣ)` (with `D_r` the decomposition group of `r`), there is a class
`q ∈ H²(Gal(L/k), 𝕀_L)` whose localisation at `r` is exactly `a` and whose localisation
vanishes at every place not in the `Gal(L/k)`-orbit of `r`.

The proof is the surjectivity half of the idèle Shapiro theorem (`ext_idele_shapiro`): choose a
transversal `R` of the `Gal(L/k)`-orbits of the places with `r ∈ R` (which exists by
`exists_transversal_mem_of_mulAction`), prescribe the value `a` at `r` and `0` at every other
place of `R`; the family is `0` and hence unramified at almost all places, so Shapiro produces a
preimage `q`.  Localisation at a place `v` outside the orbit of `r` is transported from the
vanishing of the representative of the orbit of `v` by `e9c_extLoc_conj_zero`.
-/

namespace Work.SSGRoute.E7cOmega

open CategoryTheory SSGRoute.PTExt

theorem exists_orbitSupported_extLoc {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (r : NK.GlobalCFT.Place L)
    (a : SSGRoute.PTExt.extH (SSGRoute.PTExt.localUnitsK (k := k) (K := L) r) 2) :
    ∃ q : SSGRoute.PTExt.extH (SSGRoute.PTExt.idelesK k L) 2,
      SSGRoute.PTExt.extLoc (k := k) (K := L) r q = a ∧
      ∀ v : NK.GlobalCFT.Place L, (∀ σ : L ≃ₐ[k] L, σ • r ≠ v) →
        SSGRoute.PTExt.extLoc (k := k) (K := L) v q = 0 := by
  classical
  -- a transversal of the `Gal(L/k)`-orbits of the places, containing `r`
  obtain ⟨R, hrR, hR⟩ :=
    exists_transversal_mem_of_mulAction (L ≃ₐ[k] L) (NK.GlobalCFT.Place L) r
  -- the prescribed local family: `a` at `r`, `0` at every other orbit representative
  let b : ∀ w : R, Abelian.Ext
      (Rep.res (decompK (k := k) (K := L) w.1).subtype (unitRep (L ≃ₐ[k] L)))
      (localUnitsK (k := k) (K := L) w.1) 2 :=
    fun w => if h : w.1 = r then h.symm ▸ a else 0
  have hb_r : b ⟨r, hrR⟩ = a := by
    show (if h : (⟨r, hrR⟩ : R).1 = r then h.symm ▸ a else 0) = a
    rw [dif_pos (rfl : (⟨r, hrR⟩ : R).1 = r)]
  have hb_fin : {w : R | ¬ IsUnramifiedExt w.1 (b w)}.Finite := by
    refine Set.Finite.subset (Set.finite_singleton (⟨r, hrR⟩ : R)) ?_
    intro w hw
    by_contra hne
    refine hw ?_
    have hwr : w.1 ≠ r := fun h => hne (Subtype.ext h)
    have hb0 : b w = 0 := by
      show (if h : w.1 = r then h.symm ▸ a else 0) = 0
      rw [dif_neg hwr]
    rw [hb0]
    exact ⟨0, by simp⟩
  -- Shapiro surjectivity
  obtain ⟨q, hq⟩ := (Work.SSGRoute.ext_idele_shapiro_aux (k := k) (K := L)
    (unitRep (L ≃ₐ[k] L)) (by infer_instance) 2 R hR).2.2 b hb_fin
  refine ⟨q, ?_, ?_⟩
  · rw [hq ⟨r, hrR⟩, hb_r]
  · intro v hv
    obtain ⟨w', ⟨σ, hσ⟩, -⟩ := hR v
    -- `w' ≠ r`, because otherwise `v` would lie in the orbit of `r`
    have hw'r : w'.1 ≠ r := by
      intro h
      have hσv : σ • v = r := hσ.trans h
      have hv1 : σ⁻¹ • r = v := by rw [← hσv]; simp
      exact hv σ⁻¹ hv1
    have hb0 : b w' = 0 := by
      show (if h : w'.1 = r then h.symm ▸ a else 0) = 0
      rw [dif_neg hw'r]
    have hzero : extLoc (k := k) (K := L) w'.1 q = 0 := by
      rw [hq w', hb0]
    -- vanishing transports to the whole orbit of `w'`, in particular to `v`
    have hconj := Work.SSGRoute.e9c_extLoc_conj_zero (k := k) (K := L) q σ⁻¹ w'.1 hzero
    have hv1 : σ⁻¹ • w'.1 = v := by
      calc σ⁻¹ • w'.1 = σ⁻¹ • (σ • v) := by rw [← hσ]
        _ = v := by simp
    rw [hv1] at hconj
    exact hconj

end Work.SSGRoute.E7cOmega
