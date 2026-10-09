import Mathlib
import Submission.Work.SSGRoute.E9c.Core
import Submission.Work.SSGRoute.decompK_restrict_exists
import Submission.Work.SSGRoute.localUnitsMap_exists
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_mem_localUnits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory
open NK.GlobalCFT (Idele Place IdeleClassGroup)

/-!
# E9c: the decomposition group restriction map `D_w → D_u` for `w | u`

For a tower `k ⊆ K ⊆ L` of number fields with `K/k`, `L/k` finite Galois and places `w | u` of
`L | K`, the restriction `Gal(L/k) →* Gal(K/k)` maps the decomposition group `D_w` into `D_u`.
Here we record this map as a *reducible* definition (`decompKRestrict`), so that the
identifications that depend on its defining formula — e.g. that the two composites
`D_w → Gal(L/k) → Gal(K/k)` and `D_w → D_u → Gal(K/k)` are definitionally equal, hence that the
two ways of restricting a `Gal(K/k)`-module to `D_w` agree definitionally — are available to
`rfl`/`exact` without explicit transports.
-/

variable (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K] [Field L] [NumberField L] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] [FiniteDimensional k L] [IsGalois k L]

/-- **The restriction map on decomposition groups.**  For `w` a place of `L` lying over a place `u`
of `K`, restriction of automorphisms `Gal(L/k) →* Gal(K/k)` carries `D_w ≤ Gal(L/k)` into
`D_u ≤ Gal(K/k)`.  (Existence is `Work.SSGRoute.decompK_restrict_exists`; here we take the
explicit `codRestrict` so that the definition is transparent.) -/
noncomputable def decompKRestrict (u : Place K) (w : Place L) (hw : Place.LiesOver w u) :
    decompK (k := k) w →* decompK (k := k) u :=
  MonoidHom.codRestrict ((galRes k K L).comp (decompK (k := k) w).subtype)
    (decompK (k := k) u) (fun σ => by
      rw [MulAction.mem_stabilizer_iff]
      have hσ : (σ : L ≃ₐ[k] L) • w = w := MulAction.mem_stabilizer_iff.mp σ.2
      have h2 := NK.HassePrinciple.liesOver_smul_of_restrict (K := k) (F := K) (L := L)
        (σ : L ≃ₐ[k] L) (galRes k K L (σ : L ≃ₐ[k] L))
        (fun y => AlgEquiv.restrictNormal_commutes (σ : L ≃ₐ[k] L) K y) hw
      rw [hσ] at h2
      exact (place_liesOver_unique (w := u)
        (w₂ := galRes k K L (σ : L ≃ₐ[k] L) • u) w hw h2).symm)

/-- The defining formula of `decompKRestrict`. -/
@[simp] theorem decompKRestrict_coe (u : Place K) (w : Place L) (hw : Place.LiesOver w u)
    (σ : decompK (k := k) w) :
    ((decompKRestrict k K L u w hw σ : decompK (k := k) u) : K ≃ₐ[k] K)
      = galRes k K L (σ : L ≃ₐ[k] L) := rfl

/-- **The two composites `D_w → Gal(K/k)` agree definitionally.** -/
theorem decompKRestrict_comp_subtype (u : Place K) (w : Place L) (hw : Place.LiesOver w u) :
    (decompK (k := k) u).subtype.comp (decompKRestrict k K L u w hw)
      = (galRes k K L).comp (decompK (k := k) w).subtype := rfl

/-- **The two ways of restricting a `Gal(K/k)`-module to `D_w` agree definitionally.** -/
theorem decompKRestrict_res_res (u : Place K) (w : Place L) (hw : Place.LiesOver w u)
    (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) :
    Rep.res (decompKRestrict k K L u w hw) (Rep.res (decompK (k := k) u).subtype M)
      = Rep.res (decompK (k := k) w).subtype (Rep.res (galRes k K L) M) := rfl

end Work.SSGRoute
