import Mathlib
import Submission.NK.GlobalCFT.Norm
import Submission.NK.GlobalCFT.Norm.globalCFT_localNorm_mem_localUnits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm of an idèle is a local unit at almost every place

Let `L / K` be a finite extension of number fields and `x ∈ 𝕀 L` an idèle of `L`.  The
componentwise norm formula `NK.GlobalCFT.Idele.normIdeleFun K L x` is a well defined idèle of
`K`, i.e. it lies in the restricted product: at all but finitely many places `v` of `K` the value
`N_v(x) = ∏_{w | v} N_{L_w/K_v}(x_w)` is a local unit `𝒪_vˣ`.

The proof is the classical one: `x` itself is a local unit at all but finitely many places `w` of
`L`, and the norm of a local unit is a local unit
(`NK.GlobalCFT.Norm.globalCFT_localNorm_mem_localUnits`).  Since only finitely many places of
`K` lie below a given finite set of places of `L`, the product `∏_{w | v}` is a product of local
units for all but finitely many `v`, hence a local unit.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT

namespace Norm

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- The nonzero prime of `𝓞 K` below a nonzero prime of `𝓞 L`. -/
def underHeightOne (q : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 K) :=
  ⟨q.asIdeal.under (𝓞 K), inferInstance, Ideal.under_ne_bot (𝓞 K) q.ne_bot⟩

@[simp] theorem underHeightOne_asIdeal (q : HeightOneSpectrum (𝓞 L)) :
    (underHeightOne q).asIdeal = q.asIdeal.under (𝓞 K) := rfl

/-- **The norm of an idèle is a local unit at almost every place.**  For a finite extension of
number fields `L / K` and an idèle `x` of `L`, the componentwise norm `N_{L/K} x` lies in the
local units `𝒪_vˣ` for all but finitely many places `v` of `K`. -/
theorem globalCFT_eventually_normIdeleFun_mem {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (x : NK.GlobalCFT.Idele L) :
    ∀ᶠ v in Filter.cofinite,
      NK.GlobalCFT.Idele.normIdeleFun K L x v ∈ NK.GlobalCFT.Place.localUnits K v := by
  rw [Filter.eventually_cofinite]
  -- the set of places of `L` at which `x` is not a local unit is finite
  have hBfin : {w : Place L | x.1 w ∉ Place.localUnits L w}.Finite :=
    Filter.eventually_cofinite.mp x.2
  -- hence so is the set of *finite* places of `L` with that property
  have hSfin : (Place.ofFinite ⁻¹' {w : Place L | x.1 w ∉ Place.localUnits L w}).Finite :=
    Set.Finite.preimage (f := Place.ofFinite) (s := {w : Place L | x.1 w ∉ Place.localUnits L w})
      (fun _ _ _ _ h => Place.ofFinite_inj.mp h) hBfin
  -- the finite set of places of `K` below such a place
  refine (hSfin.image fun q : HeightOneSpectrum (𝓞 L) => Place.ofFinite (underHeightOne q)).subset ?_
  rintro v hv
  rcases v with w | Q
  · exact absurd Place.mem_localUnits_ofInfinite hv
  · by_cases h : ∀ q' ∈ Place.primesOverFinite (K := K) (L := L) Q,
        x (Place.ofFinite q') ∈ Place.localUnits L (Place.ofFinite q')
    · refine absurd ?_ hv
      rw [Idele.normIdeleFun_ofFinite]
      refine Subgroup.prod_mem _ ?_
      intro q' _
      exact globalCFT_localNorm_mem_localUnits q'.1 Q
        ((Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := q'.1)).mp q'.2)
        (h q'.1 q'.2)
    · push Not at h
      obtain ⟨q', hq'mem, hq'bad⟩ := h
      refine ⟨q', hq'bad, ?_⟩
      rw [Place.ofFinite_inj]
      refine HeightOneSpectrum.ext ?_
      rw [underHeightOne_asIdeal]
      have hlies : q'.asIdeal.LiesOver Q.asIdeal :=
        (Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := q')).mp hq'mem
      exact (Ideal.over_def (p := Q.asIdeal) q'.asIdeal).symm

end Norm

end NK.GlobalCFT
