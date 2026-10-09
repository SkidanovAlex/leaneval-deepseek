import Mathlib
import Submission.NK.GlobalCFT.NormFunctorial
import Submission.NK.GlobalCFT.Idele
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib.Existence

open NK.GlobalCFT

/-- The idèlic norm `N_{K'/K} : 𝕀 K' →* 𝕀 K` maps the idèles of `K'` which are integral at every
finite place into the idèles of `K` which are integral at every finite place.

Indeed, at a finite place `v` of `K` the `v`-component of `N x` is the finite product
`∏_{w | v} N_{K'_w/K_v} (x_w)` of local norms, and each local norm of a local unit is again a
local unit (`globalCFT_localNorm_mem_localUnits`), the product being taken inside the subgroup of
local units `𝒪_vˣ`. -/
theorem map_normIdeleHom_integralIdeles_le
    {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    [FiniteDimensional K K'] :
    (NK.GlobalCFT.Idele.integralIdeles K').map (NK.GlobalCFT.Idele.normIdeleHom K K') ≤
      NK.GlobalCFT.Idele.integralIdeles K := by
  rintro y ⟨x, hx, rfl⟩
  have hx' := Idele.mem_integralIdeles.mp hx
  intro v hv
  obtain ⟨Q, rfl⟩ := Place.isFinite_iff.mp hv
  rw [Idele.normIdeleHom_apply, Idele.normIdeleFun_ofFinite]
  refine Subgroup.prod_mem _ ?_
  intro q' _
  exact Norm.globalCFT_localNorm_mem_localUnits q'.1 Q
    ((Place.mem_primesOverFinite (K := K) (L := K') (Q := Q) (q := q'.1)).mp q'.2)
    (hx' (Place.ofFinite q'.1) (Place.isFinite_ofFinite q'.1))

end NK.CFTLib.Existence
