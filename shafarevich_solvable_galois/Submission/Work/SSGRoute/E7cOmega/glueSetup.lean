import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.PT.exists_glue_extLoc
import Submission.Work.SSGRoute.e9c_extLoc_conj_zero
import Submission.Work.SSGRoute.E7cOmega.exists_transversal_mem_of_mulAction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E7cΩ: the transversal, the gluing map, and the class supported on one orbit

For a tower `k ⊆ K ⊆ Ω` of number fields (`K/k` finite Galois) and a place `w` of `K`, this file
builds the class `zfun k K w M y ∈ Ext¹_{Gal(K/k)}(M, 𝕀_K)` which is supported on the
`Gal(K/k)`-orbit of `w` and whose `w`-component is a prescribed class
`y ∈ Ext¹_{D_w}(res M, K_wˣ)`.

Ingredients:

* `transv k K w` — a transversal of the `Gal(K/k)`-orbits of `Place K` containing `w`
  (`exists_transversal_mem_of_mulAction`);
* `glueK` — E9's gluing map (clause (iii) of E2, `PT.exists_glue_extLoc`), with its two properties
  `glueK_apply` (components) and `glueK_reconstruct`;
* `zfun` — the glued class of the transversal family which is `y` at (the representative) `w` and
  `0` at every other representative;
* `zfun_extLoc_w` — `extLoc w (zfun y) = y`;
* `zfun_extLoc_eq_zero` — `extLoc u (zfun y) = 0` for every place `u` outside the orbit of `w`
  (the first clause of E7cΩ).
-/

namespace Work.SSGRoute.E7cOmega

open SSGRoute.PTExt CategoryTheory
open NK.GlobalCFT (Idele Place)
open Classical

noncomputable section

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- The chosen transversal of the `Gal(K/k)`-orbits of `Place K` containing `w`. -/
def transv (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (w : Place K) : Set (Place K) :=
  (exists_transversal_mem_of_mulAction (K ≃ₐ[k] K) (Place K) w).choose

theorem transv_mem (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (w : Place K) : w ∈ transv k K w :=
  (exists_transversal_mem_of_mulAction (K ≃ₐ[k] K) (Place K) w).choose_spec.1

theorem transv_spec (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (w : Place K) :
    ∀ v : Place K, ∃! v' : (transv k K w : Set (Place K)), ∃ σ : K ≃ₐ[k] K, σ • v = v'.1 :=
  (exists_transversal_mem_of_mulAction (K ≃ₐ[k] K) (Place K) w).choose_spec.2

/-- **The gluing map**: the chosen map from transversal local families to idèle classes
(clause (iii) of E2, `PT.exists_glue_extLoc`). -/
def glueK (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (w : Place K) (M : Rep.{0} Coeff (K ≃ₐ[k] K))
    [Finite M] :
    (∀ r : (transv k K w : Set (Place K)),
        Abelian.Ext (Rep.res (decompK (k := k) r.1).subtype M) (localUnitsK (k := k) r.1) 1) →
      Abelian.Ext M (idelesK k K) 1 :=
  (PT.exists_glue_extLoc k K M 1 (transv k K w) (transv_spec k K w)).choose

/-- The components of `glueK`. -/
theorem glueK_apply (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (w : Place K) (M : Rep.{0} Coeff (K ≃ₐ[k] K))
    [Finite M]
    (a : ∀ r : (transv k K w : Set (Place K)),
        Abelian.Ext (Rep.res (decompK (k := k) r.1).subtype M) (localUnitsK (k := k) r.1) 1)
    (hfin : {r : (transv k K w : Set (Place K)) |
      ¬ IsUnramifiedExt (k := k) (K := K) r.1 (a r)}.Finite)
    (r : (transv k K w : Set (Place K))) :
    extLoc (k := k) (K := K) r.1 (glueK k K w M a) = a r :=
  (PT.exists_glue_extLoc k K M 1 (transv k K w) (transv_spec k K w)).choose_spec.1 a hfin r

/-- `glueK` is the identity on families coming from a class. -/
theorem glueK_reconstruct (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : Place K)
    (M : Rep.{0} Coeff (K ≃ₐ[k] K)) [Finite M]
    (x : Abelian.Ext M (idelesK k K) 1) :
    glueK k K w M (fun r => extLoc (k := k) (K := K) r.1 x) = x :=
  (PT.exists_glue_extLoc k K M 1 (transv k K w) (transv_spec k K w)).choose_spec.2 x

/-- The transversal family which is `y` at the representative `w` and `0` elsewhere. -/
def zFam (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (w : Place K) (M : Rep.{0} Coeff (K ≃ₐ[k] K))
    (y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1) :
    ∀ r : (transv k K w : Set (Place K)),
      Abelian.Ext (Rep.res (decompK (k := k) r.1).subtype M) (localUnitsK (k := k) r.1) 1 :=
  fun r => if h : (r : Place K) = w then h.symm ▸ y else 0

theorem zFam_apply_of_ne (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : Place K)
    (M : Rep.{0} Coeff (K ≃ₐ[k] K))
    (y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1)
    (r : (transv k K w : Set (Place K))) (hr : (r : Place K) ≠ w) :
    zFam k K w M y r = 0 := by
  unfold zFam
  exact dif_neg hr

theorem zFam_apply_self (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : Place K)
    (M : Rep.{0} Coeff (K ≃ₐ[k] K))
    (y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1) :
    zFam k K w M y ⟨w, transv_mem k K w⟩ = y := by
  unfold zFam
  exact dif_pos rfl

/-- The class supported on the orbit of `w` with `w`-component `y`. -/
def zfun (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (w : Place K) (M : Rep.{0} Coeff (K ≃ₐ[k] K))
    [Finite M]
    (y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1) :
    Abelian.Ext M (idelesK k K) 1 :=
  glueK k K w M (zFam k K w M y)

/-- The family `zFam y` is unramified outside the single representative `w`. -/
theorem zFam_support_finite (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : Place K)
    (M : Rep.{0} Coeff (K ≃ₐ[k] K))
    (y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1) :
    {r : (transv k K w : Set (Place K)) |
      ¬ IsUnramifiedExt (k := k) (K := K) r.1 (zFam k K w M y r)}.Finite := by
  refine Set.Finite.subset (Set.finite_singleton (⟨w, transv_mem k K w⟩ :
    (transv k K w : Set (Place K)))) ?_
  intro r hr
  by_cases h : r = ⟨w, transv_mem k K w⟩
  · simpa [h]
  · have hne : (r : Place K) ≠ w := fun hw => h (Subtype.ext hw)
    have hz0 : zFam k K w M y r = 0 := zFam_apply_of_ne k K w M y r hne
    simp only [Set.mem_setOf_eq] at hr
    rw [hz0] at hr
    exact absurd ⟨0, by rw [Abelian.Ext.zero_comp]⟩ hr

/-- The `w`-component of `zfun y` is `y`. -/
theorem zfun_extLoc_w (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : Place K)
    (M : Rep.{0} Coeff (K ≃ₐ[k] K)) [Finite M]
    (y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1) :
    extLoc (k := k) (K := K) w (zfun k K w M y) = y := by
  unfold zfun
  rw [glueK_apply k K w M (zFam k K w M y) (zFam_support_finite k K w M y)
    ⟨w, transv_mem k K w⟩]
  exact zFam_apply_self k K w M y

/-- **Clause 1 of E7cΩ**: the class `zfun y` vanishes at every place outside the `Gal(K/k)`-orbit
of `w`. -/
theorem zfun_extLoc_eq_zero (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : Place K)
    (M : Rep.{0} Coeff (K ≃ₐ[k] K)) [Finite M]
    (y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1)
    (u : Place K) (hu : ∀ σ : K ≃ₐ[k] K, σ • w ≠ u) :
    extLoc (k := k) (K := K) u (zfun k K w M y) = 0 := by
  obtain ⟨r, ⟨σ, hσ⟩, -⟩ := transv_spec k K w u
  have hrw : (r : Place K) ≠ w := by
    intro h
    have h1 : σ⁻¹ • w = u := by rw [← h, ← hσ]; simp
    exact hu σ⁻¹ h1
  have hzr : extLoc (k := k) (K := K) r.1 (zfun k K w M y) = 0 := by
    unfold zfun
    rw [glueK_apply k K w M (zFam k K w M y) (zFam_support_finite k K w M y) r]
    exact zFam_apply_of_ne k K w M y r hrw
  have hconj := e9c_extLoc_conj_zero (k := k) (K := K) (zfun k K w M y) σ⁻¹ r.1 hzr
  have : σ⁻¹ • r.1 = u := by rw [← hσ]; simp
  rw [this] at hconj
  exact hconj

end

end Work.SSGRoute.E7cOmega
