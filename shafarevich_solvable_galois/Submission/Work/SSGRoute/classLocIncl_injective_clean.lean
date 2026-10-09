import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ext_units_single_place
import Submission.Work.SSGRoute.PT.pt_pairing_ext
import Submission.NK.HassePrinciple.locUnits_compatible
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- Restriction of `Ext`-cohomology to a subgroup needs no change of the coefficient module: it is
plain application of the exact functor `Rep.resFunctor D.subtype`.  (Local copy of
`Work.SSGRoute.ExtH1.extHRestrict_eq_extRes`, kept under a private name.) -/
theorem classLocIncl_extHRestrict_eq_extRes {G : Type} [Group G] (D : Subgroup G)
    {A : Rep.{0} Coeff G} {n : ℕ} (x : extH A n) :
    extHRestrict D x = extRes D.subtype x := by
  rw [extHRestrict, extHMap]
  have h : (extRes D.subtype x).comp
      (Abelian.Ext.mk₀ (𝟙 (Rep.res D.subtype A))) (add_zero n) = extRes D.subtype x :=
    Abelian.Ext.comp_mk₀_id _
  rw [h]
  exact Abelian.Ext.mk₀_id_comp _

/-- **Localisation of `extToIdeles` at a place, for an arbitrary first variable** (the general-`M`
form of `Work.SSGRoute.PTembedding.extLoc_extToIdeles_eq`, which is the case `M = ℤ`): the
`w`-component of `extToIdeles y` is the restriction of `y` to the decomposition group `D_w`
followed by the local unit embedding `Lˣ → L_wˣ`.

This is the copy of `Work.SSGRoute.extLoc_extToIdeles_eq_mk₀` that lives in
`Submission/Work/SSGRoute/ext_sha2_bridge.lean`; it is ported here so that the clean re-proof of
`classLocIncl_injective` does not have to import that (currently unbuildable) module. -/
theorem classLocIncl_extLoc_extToIdeles_eq_mk₀ (k : Type) [Field k] [NumberField k]
    (K : Type) [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (M : Rep.{0} Coeff (K ≃ₐ[k] K)) (y : Abelian.Ext.{0} M (unitsK k K) 2)
    (w : NK.GlobalCFT.Place K) :
    extLoc (k := k) w (extToIdeles (k := k) y) =
      (extRes (decompK (k := k) w).subtype y).comp
        (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k K w)) (add_zero 2) := by
  have h1 : extRes (decompK (k := k) w).subtype (extToIdeles (k := k) y)
      = (extRes (decompK (k := k) w).subtype y).comp
          (Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) w).subtype
            (NK.HassePrinciple.ideleIncl k K))) (add_zero 2) := by
    rw [extToIdeles, extRes, Abelian.Ext.mapExactFunctor_comp,
      Abelian.Ext.mapExactFunctor_mk₀]
    rfl
  rw [extLoc, h1]
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero]
  rw [Abelian.Ext.mk₀_comp_mk₀]
  rw [NK.HassePrinciple.res_ideleIncl_comp_ideleToLocalUnits]

/-- The `w`-component of `extToIdeles a`, in the `extHRestrict` form in which the single-place
Hasse–Brauer–Noether principle `ext_units_single_place` consumes it: the restriction of `a` to
the decomposition group `D_w`, followed by the local unit embedding `Lˣ → L_wˣ`. -/
theorem classLocIncl_extLoc_extToIdeles_eq (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (a : extH (unitsK k L) 2) (w : NK.GlobalCFT.Place L) :
    extLoc (k := k) w (extToIdeles (k := k) a) =
      (extHRestrict (decompK (k := k) (K := L) w) a).comp
        (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k L w)) (add_zero 2) := by
  rw [classLocIncl_extLoc_extToIdeles_eq_mk₀]
  congr 1
  exact (classLocIncl_extHRestrict_eq_extRes (decompK (k := k) (K := L) w) a).symm

/-- **Clean re-proof of `Work.SSGRoute.classLocIncl_injective`, avoiding the import of
`Submission.Work.SSGRoute.ext_sha2_bridge`** (whose dependency
`Submission.Work.SSGRoute.localField_subfield_place_compat` is currently broken, so that the
original module cannot be imported by anyone).  Put it in namespace `Work.SSGRoute.SSG` with
`open SSGRoute.PTExt CategoryTheory`.

A class of `H²(Gal(L/k), 𝕀_L)` which is locally trivial at every place outside the `Gal(L/k)`-orbit
of `w₀` and dies under the push-forward `𝕀_L → C_L` to the idèle class group is locally trivial at
`w₀`.

The existing proof is in `Submission/Work/SSGRoute/classLocIncl_injective.lean`; copy it, but drop
the `import Submission.Work.SSGRoute.ext_sha2_bridge`.  It uses only
`Work.SSGRoute.ext_units_single_place` (clean), the exactness of the class-formation short complex
`NK.HassePrinciple.ideleShortComplex_shortExact` at `H²`,
`Abelian.Ext.covariant_sequence_exact₂`, `Work.SSGRoute.extToIdeles`, and two short helpers that
live in the same file (`classLocIncl_extLoc_extToIdeles_eq`, `classLocIncl_extHRestrict_eq_extRes`)
— copy those in as well; they in turn need `extLoc_extToIdeles_eq_mk₀`, whose only copy currently
sits inside `Submission/Work/SSGRoute/ext_sha2_bridge.lean`; port it too (its proof uses only
`PTDefs.extToIdeles`, `PTDefs.extLoc`, `Abelian.Ext.*` and
`NK.HassePrinciple.res_ideleIncl_comp_ideleToLocalUnits`). -/
theorem classLocIncl_injective_clean (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w₀ : NK.GlobalCFT.Place L) (q : SSGRoute.PTExt.extH (SSGRoute.PTExt.idelesK k L) 2)
    (hq : ∀ w : NK.GlobalCFT.Place L, (∀ σ : L ≃ₐ[k] L, σ • w₀ ≠ w) →
      SSGRoute.PTExt.extLoc (k := k) (K := L) w q = 0)
    (h : q.comp (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k L))
      (add_zero 2) = 0) :
    SSGRoute.PTExt.extLoc (k := k) (K := L) w₀ q = 0 := by
  -- Exactness of the long exact sequence of the class formation at `H²(G, 𝕀_L)`:
  -- `h` exhibits `q` as the idèle-image of some global class `a ∈ H²(G, Lˣ)`.
  have hex : ∃ a : extH (unitsK k L) 2, extToIdeles (k := k) a = q := by
    have hS : (sesK k L).ShortExact := NK.HassePrinciple.ideleShortComplex_shortExact k L
    obtain ⟨a, ha⟩ := Abelian.Ext.covariant_sequence_exact₂ (unitRep (L ≃ₐ[k] L)) hS q h
    exact ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hex
  -- Its localisations vanish away from the `G`-orbit of `w₀`, so `a = 0` by Hasse–Brauer–Noether.
  have ha0 : a = 0 := by
    refine ext_units_single_place k L a w₀ (fun w hw => ?_)
    rw [← classLocIncl_extLoc_extToIdeles_eq (k := k) (L := L) a w, ha]
    exact hq w hw
  -- Hence `q = extToIdeles 0 = 0`, in particular locally trivial at `w₀`.
  have hq0 : q = 0 := by rw [← ha, ha0]; simp [extToIdeles]
  rw [hq0]
  exact extLoc_zero (k := k) (K := L) w₀

end Work.SSGRoute
