import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.classLocIncl_injective_clean
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

Lead guidance. The design is in the workspace at _lead_design/ssg_pt_design_1002/DESIGN.md. Read the section for your statement FIRST (§2 C6 via the induced module from the normal closure of inertia; §3 CRUX-a 3-step; §4 G1+COUNT via the canonical class-formation pairing). It gives the proof route as numbered steps and the proved workspace names to reuse (local_duality_ext_in, detectsAt_of_coeff_surjection, grunwald_over_K_general, countingIdentity_of_reciprocity_and_converse, ...). Do not re-derive what is proved.
Memory: Lean only through the harness; no sleep loops around lake.
-/

namespace Work.SSGRoute.PT

/-- An idèle class in `H²` that is supported on one orbit of places and dies in `C_L` is zero.

`z ∈ H²(Gal(L/k), 𝕀_L)` (as `extH (idelesK k L) 2`) whose local components vanish at every place
outside the `Gal(L/k)`-orbit of `w`, and whose image in `H²(Gal(L/k), C_L)` is zero, is zero.
Consumer: the injectivity of the local-to-global map `ι_w : H²(D_w, L_wˣ) → H²(Gal(L/k), C_L)`,
which makes the canonical local pairing perfect (design `DESIGN.md` §B).

Route.  (1) The long exact `Ext(unitRep, ·)` sequence of the class formation
`0 → Lˣ → 𝕀_L → C_L → 0` (`NK.HassePrinciple.ideleShortComplex_shortExact`, `extClass`,
the covariant exact sequence of `Abelian.Ext`) gives `y ∈ H²(Gal(L/k), Lˣ)` with
`extToIdeles y = z`.  (2) For `u` off the orbit, `extLoc u (extToIdeles y) = extLoc u z = 0`;
transport to `groupCohomology (unitsRep k L) 2` with the `E0b` bridge (`Work.SSGRoute.Bridge.E`)
and identify `extLoc` with `NK.HassePrinciple.locUnits` there.  (3) `Work.SSGRoute.brauer_single_place`
(proved, any place `w₀`, finite or infinite) gives `y = 0`, hence `z = 0`. -/
theorem pt_orbitIdele_H2_eq_zero (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place L)
    (z : SSGRoute.PTExt.extH (SSGRoute.PTExt.idelesK k L) 2)
    (hsupp : ∀ u : NK.GlobalCFT.Place L, (∀ σ : L ≃ₐ[k] L, σ • w ≠ u) →
      SSGRoute.PTExt.extLoc (k := k) u z = 0)
    (hcl : SSGRoute.PTExt.extToClasses (k := k) z = 0) :
    z = 0 := by
  classical
  -- (1) Exactness of the class formation `0 → Lˣ → 𝕀_L → C_L → 0` at `H²(Gal(L/k), 𝕀_L)`
  -- (`covariant_sequence_exact₂`): a class of `H²(Gal(L/k), 𝕀_L)` killed by the push-forward to
  -- `C_L` is the idèle-image of a global unit class `a ∈ H²(Gal(L/k), Lˣ)`.
  have hz : z.comp (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k L))
      (add_zero 2) = 0 := hcl
  have hex : ∃ a : SSGRoute.PTExt.extH (SSGRoute.PTExt.unitsK k L) 2,
      SSGRoute.PTExt.extToIdeles (k := k) a = z := by
    have hS : (SSGRoute.PTExt.sesK k L).ShortExact :=
      NK.HassePrinciple.ideleShortComplex_shortExact k L
    obtain ⟨a, ha⟩ :=
      CategoryTheory.Abelian.Ext.covariant_sequence_exact₂ (SSGRoute.PTExt.unitRep (L ≃ₐ[k] L))
        hS z hz
    exact ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hex
  -- (2) + (3) Localisation at any place off the orbit of `w` is "restrict to the decomposition
  -- group, then push along `Lˣ → L_uˣ`"; by hypothesis it vanishes, so `a = 0` by the single-place
  -- Hasse–Brauer–Noether principle (`Work.SSGRoute.ext_units_single_place`, which is
  -- `Work.SSGRoute.brauer_single_place` transported across the `E0b` comparison).
  have ha0 : a = 0 := by
    refine Work.SSGRoute.ext_units_single_place k L a w (fun u hu => ?_)
    rw [← Work.SSGRoute.classLocIncl_extLoc_extToIdeles_eq (k := k) (L := L) a u, ha]
    exact hsupp u hu
  -- (4) Hence `z = extToIdeles 0 = 0`.
  rw [← ha, ha0]
  simp [SSGRoute.PTExt.extToIdeles]

end Work.SSGRoute.PT
