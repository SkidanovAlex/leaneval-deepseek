import Mathlib
import Submission.Work.SSGRoute.E9c.Core
import Submission.Work.SSGRoute.ext_idele_defs
import Submission.Work.SSGRoute.level_decomp_bij
import Submission.Work.SSGRoute.ext_idele_shapiro
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory
open NK.GlobalCFT (Idele Place IdeleClassGroup)

variable {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K]
  [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
  [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [FiniteDimensional k L] [IsGalois k L]

/-- **A class whose transversal components are all unramified is unramified everywhere.**

If `x ∈ Ext^r_G(M, 𝕀_K)` has unramified components at all places of a transversal `R` of the
`Gal(K/k)`-orbits, then *every* local component of `x` is unramified.

Proof: the empty level `S = ∅` has `BOf k K w ∅ = 𝒪_wˣ`, and the level decomposition
`thetaL : Ext^r(M, 𝕀_K^∅) ≅ ∏_{w ∈ R} Ext^r_{D_w}(𝒪_wˣ)` is bijective
(`Work.SSGRoute.level_decomp_bijective`); choose `x₀` mapping to the unramified parts of the
components of `x`.  Then `pushLevel x₀` and `x` have the same transversal components, so they agree
by E2's injectivity (`Work.SSGRoute.ext_idele_shapiro` clause (i)), and `pushLevel x₀` is
unramified at every place outside `∅` (`Work.SSGRoute.isUnramifiedExt_extLoc_pushLevel`). -/
theorem isUnramifiedExt_of_components_unramified (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) [Finite M]
    (r : ℕ) (R : Set (Place K))
    (hR : ∀ w : Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (x : Abelian.Ext M (idelesRepP k K) r)
    (hx : ∀ v : R, IsUnramifiedExt (k := k) (K := K) v.1
      (extLoc (k := k) (K := K) v.1 x)) :
    ∀ u : Place K, IsUnramifiedExt (k := k) (K := K) u (extLoc (k := k) (K := K) u x) := by
  classical
  let S₀ : NK.HassePrinciple.GStableSet k K := ⟨∅, by intro σ v hv; simpa using hv⟩
  have hS₀ : S₀.carrier.Finite := Set.finite_empty
  -- the unramified parts of the transversal components of `x`
  have key : ∀ v : R, ∃ ζ : Abelian.Ext (Rep.res (decompK (k := k) v.1).subtype M)
      (NK.HassePrinciple.localUnitsSubRep k K v.1) r,
      extLoc (k := k) (K := K) v.1 x
        = ζ.comp (Abelian.Ext.mk₀
            (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) v.1)) (add_zero r) :=
    fun v => hx v
  choose ζ hζ using key
  -- the corresponding family over the empty level
  let a : (w : R) → Abelian.Ext (Rep.res (decompK (k := k) w.1).subtype M)
      (BOf k K w.1 S₀) r :=
    fun w => (ζ w).comp (Abelian.Ext.mk₀
      (eqToHom (BOf_of_notMem (k := k) (K := K) (w := w.1) (S := S₀) (by simp [S₀])).symm))
      (add_zero r)
  obtain ⟨x₀, hx₀⟩ := (level_decomp_bijective k K R hR M r S₀ hS₀).2 a
  have hpush : pushLevel k K M r S₀ x₀ = x := by
    have hzero : pushLevel k K M r S₀ x₀ - x = 0 :=
      (ext_idele_shapiro k K M r R hR).1 _ (by
    intro w hw
    have hcomp : extLoc (k := k) (K := K) w (pushLevel k K M r S₀ x₀)
        = extLoc (k := k) (K := K) w x := by
      rw [extLoc_pushLevel k K R M r S₀ x₀ ⟨w, hw⟩, hx₀, hζ ⟨w, hw⟩]
      show ((ζ ⟨w, hw⟩).comp (Abelian.Ext.mk₀
            (eqToHom (BOf_of_notMem (k := k) (K := K) (w := w) (S := S₀) (by simp [S₀])).symm))
            (add_zero r)).comp (Abelian.Ext.mk₀ (BOfIncl k K w S₀)) (add_zero r)
        = (ζ ⟨w, hw⟩).comp (Abelian.Ext.mk₀
            (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) w)) (add_zero r)
      exact bofIncl_cast_notMem (k := k) (K := K) (w := w) (S := S₀) (by simp [S₀])
        (Rep.res (decompK (k := k) w).subtype M) (ζ ⟨w, hw⟩)
    have hneg : extLoc (k := k) (K := K) w (-x) = -extLoc (k := k) (K := K) w x := by
      have h := extLoc_add (k := k) (K := K) w (-x) x
      rw [neg_add_cancel, extLoc_zero (k := k) (K := K) w] at h
      exact eq_neg_of_add_eq_zero_left h.symm
    rw [sub_eq_add_neg, extLoc_add (k := k) (K := K) w, hneg, hcomp, add_neg_cancel])
    exact sub_eq_zero.mp hzero
  intro u
  rw [← hpush]
  exact isUnramifiedExt_extLoc_pushLevel k K M r S₀ u (by simp [S₀]) x₀

/-- **`phiAt` is additive in the class.** -/
theorem phiAt_add (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K))
    (x y : Abelian.Ext M (classesRepP k K) 1)
    (h : extH (Rep.res (galRes k K L) M) 1) :
    phiAt (k := k) (K := K) (L := L) (x + y) h
      = phiAt (k := k) (K := K) (L := L) x h
        + phiAt (k := k) (K := K) (L := L) y h := by
  simp only [phiAt, levelPair, extRes, Abelian.Ext.mapExactFunctor_add,
    Abelian.Ext.add_comp, Abelian.Ext.comp_add]

end Work.SSGRoute
