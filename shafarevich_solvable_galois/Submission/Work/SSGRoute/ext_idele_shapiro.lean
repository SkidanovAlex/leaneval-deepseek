import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ext_level_lift
import Submission.Work.SSGRoute.level_decomp_bij
import Submission.Work.SSGRoute.local_retraction_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/SSGRoute/DESIGN_EXT.md (the lead's Ext-core design for Poitou–Tate) + DESIGN_PT.md. Definitions: Submission/Work/SSGRoute/PTDefs.lean (namespace SSGRoute.PTExt; do NOT edit). NK.* CFT library available. Siblings run in parallel.

# E2 `ext_idele_shapiro` — `Ext^r_G(M, 𝕀_K)` is the restricted product of the local `Ext`

**Statement.** `R` is a set of places of `K` meeting each `G`-orbit exactly once, and `M` is finite.
Localisation `x ↦ (extLoc w x)_{w∈R}` is:
1. injective;
2. unramified (`IsUnramifiedExt`, i.e. coming from `𝒪_wˣ`) at all but finitely many `w`;
3. onto the families that are unramified at almost all `w`.

**Route.**
1. **Orbit decomposition.** `𝕀_K = colim_S (∏_{w∈S} K_wˣ × ∏_{w∉S} 𝒪_wˣ)`, and each orbit factor
   is coinduced from `D_w`. NK has this: `orbitCoindMapA_split`, `coindToIdele`, `HBNIdeleProof`.
2. **`Ext` passes through colimits and products.** `M` is finite, hence finitely presented over
   `ℤ[G]`, so `Ext^r_G(M, ·)` commutes with filtered colimits and with products. Resolve `M` by
   finite free modules; `Hom` out of a finite free module commutes with both.
3. **Shapiro for `Ext`:** `Ext^r_G(M, coind_D B) ≅ Ext^r_D(res M, B)` (res ⊣ coind, both exact).
   Mathlib has this only for `groupCohomology` (`coindIso`); prove the `Ext` version by the
   adjunction on a projective resolution.

**Deps.** E0b (optional).

**Size.** 1–2k. **Risk:** medium (the colimit and product commutation are new API).

**Imports.** `Submission.Work.SSGRoute.PTDefs`.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-! ## Interface (temporary declarations, to be replaced by the dedicated modules) -/

/-- **The finite-level lifting**: every class of `Ext^r_G(M, 𝕀_K)` comes from a finite level
containing any prescribed finite set of places. -/
theorem ext_level_lift (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (hM : Module.Finite ℤ M.V) (r : ℕ)
    (T : Set (NK.GlobalCFT.Place K)) (hT : T.Finite) (x : Abelian.Ext M (idelesK k K) r) :
    ∃ (S : NK.HassePrinciple.GStableSet k K) (xS : Abelian.Ext M (lvl k K S) r),
      T ⊆ S.carrier ∧ S.carrier.Finite ∧ pushLevel k K M r S xS = x :=
  ext_level_lift_aux k K r M hM T hT x


/-! ## The `Gal(K/k)`-stable level of the places where the local retraction fails -/

/-- The finite `Gal(K/k)`-stable set of places covering the places where the local inclusion
`𝒪_wˣ ↪ K_wˣ` has no `D_w`-equivariant retraction (a finite set by `local_retraction_ae`). -/
noncomputable def badLevel : NK.HassePrinciple.GStableSet k K :=
  Classical.choose (NK.HassePrinciple.exists_gstable_finite_superset (K := k) (L := K)
    {w : NK.GlobalCFT.Place K | ¬ HasLocalRetraction k K w}
    (local_retraction_ae k K))

theorem badLevel_finite : (badLevel k K).carrier.Finite :=
  (Classical.choose_spec (NK.HassePrinciple.exists_gstable_finite_superset (K := k) (L := K)
    {w : NK.GlobalCFT.Place K | ¬ HasLocalRetraction k K w}
    (local_retraction_ae k K))).1

theorem exists_retraction_of_notMem_badLevel (w : NK.GlobalCFT.Place K)
    (hw : w ∉ (badLevel k K).carrier) :
    ∃ r : localUnitsK (k := k) w ⟶ NK.HassePrinciple.localUnitsSubRep k K w,
      NK.HassePrinciple.localUnitsIncl (K := k) (L := K) w ≫ r
        = 𝟙 (NK.HassePrinciple.localUnitsSubRep k K w) := by
  by_contra h
  exact hw ((Classical.choose_spec (NK.HassePrinciple.exists_gstable_finite_superset
    (K := k) (L := K)
    {w : NK.GlobalCFT.Place K | ¬ HasLocalRetraction k K w}
    (local_retraction_ae k K))).2 (Set.mem_setOf.mpr h))

/-! ## The three conjuncts -/

/-- **E2**, for a `ℤ`-finitely generated module `M`: localisation of `Ext^r_G(M, 𝕀_K)` at a
transversal `R` of the orbits is injective, almost everywhere unramified, and surjective onto the
families which are almost everywhere unramified. -/
theorem ext_idele_shapiro_aux (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K))
    (hM : Module.Finite ℤ M.V) (r : ℕ) (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1) :
    (∀ x : Abelian.Ext M (idelesK k K) r, (∀ w ∈ R, extLoc w x = 0) → x = 0) ∧
    (∀ x : Abelian.Ext M (idelesK k K) r,
      {w : NK.GlobalCFT.Place K | ¬ IsUnramifiedExt w (extLoc w x)}.Finite) ∧
    ∀ a : ∀ w : R, Abelian.Ext (Rep.res (decompK (k := k) w.1).subtype M)
        (localUnitsK (k := k) w.1) r,
      {w : R | ¬ IsUnramifiedExt w.1 (a w)}.Finite →
        ∃ x : Abelian.Ext M (idelesK k K) r, ∀ w : R, extLoc w.1 x = a w := by
  constructor
  · -- injectivity
    intro x hx
    obtain ⟨S, xS, hTS, hSfin, hpush⟩ :=
      ext_level_lift k K M hM r (badLevel k K).carrier (badLevel_finite k K) x
    have hzero : thetaL k K R M r S xS = 0 := by
      funext w
      have h1 := extLoc_pushLevel k K R M r S xS w
      rw [hpush, hx w.1 w.2] at h1
      by_cases hw : w.1 ∈ S.carrier
      · rw [BOfIncl_of_mem (k := k) (K := K) hw] at h1
        exact (ext_comp_mk₀_eqToHom_eq_zero_iff
          (BOf_of_mem (k := k) (K := K) hw)
          (thetaL k K R M r S xS w)).mp h1.symm
      · obtain ⟨rr, hrr⟩ :=
          exists_retraction_of_notMem_badLevel k K w.1 (fun hmem => hw (hTS hmem))
        rw [BOfIncl_of_notMem (k := k) (K := K) hw] at h1
        have h3 : ((thetaL k K R M r S xS w).comp
            (Abelian.Ext.mk₀ (eqToHom (BOf_of_notMem (k := k) (K := K) hw) ≫
              NK.HassePrinciple.localUnitsIncl (K := k) (L := K) w.1)) (add_zero r)).comp
            (Abelian.Ext.mk₀ rr) (add_zero r) = 0 := by
          rw [← h1]
          simp
        rw [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
          show (eqToHom (BOf_of_notMem (k := k) (K := K) hw) ≫
              NK.HassePrinciple.localUnitsIncl (K := k) (L := K) w.1) ≫ rr
            = eqToHom (BOf_of_notMem (k := k) (K := K) hw) from by
            rw [Category.assoc, hrr, Category.comp_id]] at h3
        exact (ext_comp_mk₀_eqToHom_eq_zero_iff
          (BOf_of_notMem (k := k) (K := K) hw)
          (thetaL k K R M r S xS w)).mp h3
    have hzero0 := thetaL_zero k K R M r S
    have hxS : xS = 0 :=
      (level_decomp_bijective k K R hR M r S hSfin).injective (by rw [hzero, hzero0])
    rw [← hpush, hxS]
    simp [pushLevel]
  constructor
  · -- almost everywhere unramified
    intro x
    obtain ⟨S, xS, -, hSfin, hpush⟩ := ext_level_lift k K M hM r ∅ Set.finite_empty x
    refine hSfin.subset ?_
    intro w hw
    by_contra hwS
    exact hw (by rw [← hpush]; exact isUnramifiedExt_extLoc_pushLevel k K M r S w hwS xS)
  · -- surjectivity onto the almost everywhere unramified families
    intro a ha
    let T : Set (NK.GlobalCFT.Place K) := {v | ∃ hv : v ∈ R, ¬ IsUnramifiedExt v (a ⟨v, hv⟩)}
    have hT : T.Finite := Set.Finite.subset (ha.image Subtype.val) (fun v hv => by
      obtain ⟨hvR, hbad⟩ := hv
      exact ⟨⟨v, hvR⟩, hbad, rfl⟩)
    let S : NK.HassePrinciple.GStableSet k K :=
      Classical.choose (NK.HassePrinciple.exists_gstable_finite_superset (K := k) (L := K) T hT)
    have hSfin : S.carrier.Finite :=
      (Classical.choose_spec (NK.HassePrinciple.exists_gstable_finite_superset (K := k) (L := K)
        T hT)).1
    have hTS : T ⊆ S.carrier :=
      (Classical.choose_spec (NK.HassePrinciple.exists_gstable_finite_superset (K := k) (L := K)
        T hT)).2
    have hb : ∀ w : R, ∃ b : Abelian.Ext (Rep.res (decompK (k := k) w.1).subtype M)
        (BOf k K w.1 S) r,
        b.comp (Abelian.Ext.mk₀ (BOfIncl k K w.1 S)) (add_zero r) = a w := by
      intro w
      by_cases hw : w.1 ∈ S.carrier
      · refine ⟨(a w).comp
          (Abelian.Ext.mk₀ (eqToHom (BOf_of_mem (k := k) (K := K) hw).symm)) (add_zero r), ?_⟩
        rw [bofIncl_cast_mem (k := k) (K := K) (X := Rep.res (decompK (k := k) w.1).subtype M)
          (n := r) hw (a w)]
      · have hnr : IsUnramifiedExt w.1 (a w) := by
          by_contra hbad
          exact hw (hTS (Set.mem_setOf.mpr ⟨w.2, hbad⟩))
        obtain ⟨z, hz⟩ := hnr
        refine ⟨z.comp (Abelian.Ext.mk₀
          (eqToHom (BOf_of_notMem (k := k) (K := K) hw).symm)) (add_zero r), ?_⟩
        rw [hz, bofIncl_cast_notMem (k := k) (K := K)
          (X := Rep.res (decompK (k := k) w.1).subtype M) (n := r) hw z]
    choose b hb' using hb
    obtain ⟨xS, hxS⟩ := (level_decomp_bijective k K R hR M r S hSfin).surjective b
    refine ⟨pushLevel k K M r S xS, ?_⟩
    intro w
    rw [extLoc_pushLevel k K R M r S xS w, hxS]
    exact hb' w

/-- **E2.** Idèle Shapiro: for a finite `Gal(K/k)`-module `M` and a set `R` of places of `K`
meeting every `Gal(K/k)`-orbit exactly once, `Ext^r_G(M, 𝕀_K)` is the restricted product over
`w ∈ R` of the local groups `Ext^r_{D_w}(M, K_wˣ)` with respect to the unramified classes
(those coming from `𝒪_wˣ`): localisation is injective, almost always unramified, and every
almost-everywhere-unramified family is attained. -/
theorem ext_idele_shapiro (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (r : ℕ) (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1) :
    (∀ x : Abelian.Ext M (idelesK k K) r, (∀ w ∈ R, extLoc w x = 0) → x = 0) ∧
    (∀ x : Abelian.Ext M (idelesK k K) r,
      {w : NK.GlobalCFT.Place K | ¬ IsUnramifiedExt w (extLoc w x)}.Finite) ∧
    ∀ a : ∀ w : R, Abelian.Ext (Rep.res (decompK (k := k) w.1).subtype M)
        (localUnitsK (k := k) w.1) r,
      {w : R | ¬ IsUnramifiedExt w.1 (a w)}.Finite →
        ∃ x : Abelian.Ext M (idelesK k K) r, ∀ w : R, extLoc w.1 x = a w :=
  ext_idele_shapiro_aux k K M (module_finite_int k K M) r R hR

end Work.SSGRoute
