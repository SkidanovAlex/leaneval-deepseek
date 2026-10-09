/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Naturality of the square `F(m)/F(m)^2 ≅ N/N^p[N,N]`

This file proves the naturality of the identification `flowNormalSquareEquiv` of
`Submission.Work.CohomologicalShrinking.flow.flowNormalSquareEquiv`: the "square quotient"
`F(d)/F(d)^2` for the rank-change map `Φ : F(m) ⇢ F(n)` computes the same map on the bottom
`p`-central quotients of the normal subgroups `N_m = F(m)/F(m)^{(ν)}` whether one goes through
`F(m)/F(m)^2 → N_m/N_m^p[N_m,N_m]` first and then applies `Φ`, or applies `Φ` on the square
quotients first and then uses the identification for `n`.

Concretely, both composites fit into the commuting square

  `F(m) --Φ.toHom--> F(n)`
  `  | flowNormalSurj    | flowNormalSurj`
  `  v                   v`
  `N_m --flowNormalSubMap--> N_n`

of group homomorphisms (`flowNormalSurj_sq`), and the induced `𝔽_p`-linear maps on the bottom
`p`-central quotients commute by the general naturality `pQMapLin_square`.

## Main results

* `quotMapLin_eq_pQMapLin` : the two definitions of the induced map on `F(d)/F(d)^2`
  (`quotMapLin` of `Functorial.lean`, resp. `pQMapLin` of `Defs.lean`) agree;
* `flowNormalSurj_sq` : the group-level square commutes;
* `sqLin_natural` : the target statement.
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.naturalAlpha.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.naturalAlpha

open Work.Shrinking
open Work.CohomologicalShrinking

variable {p : ℕ}

/-- The two definitions of the induced map `F(d)/F(d)^2 → F(e)/F(e)^2` agree: `quotMapLin`
(`Functorial.lean`) and `pQMapLin` (`Defs.lean`) coincide on a surjective homomorphism of free
operator groups.  Both are the map induced by `pCentralMapMul` on the bottom quotient, and
`pCentralMapMul p ψ hψ 0 = pQMapMul p ψ`. -/
theorem quotMapLin_eq_pQMapLin (p : ℕ) (G : Type) [Group G] {m n : ℕ}
    (ψ : freeOperatorGroup G m →* freeOperatorGroup G n) (hψ : Function.Surjective ψ) :
    quotMapLin p G ψ hψ = pQMapLin p ψ := by
  have hmon : pCentralMapMul p ψ hψ 0 = pQMapMul p ψ := by
    refine MonoidHom.ext (fun z => ?_)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      ((pCentralSeries p (freeOperatorGroup G m) 1).subgroupOf
        (pCentralSeries p (freeOperatorGroup G m) 0)) z
    rw [pQMapMul_mk, pCentralMapMul, QuotientGroup.map_mk', QuotientGroup.mk'_apply]
    congr 1
  refine LinearMap.ext (fun z => ?_)
  show Additive.ofMul (pCentralMapMul p ψ hψ 0 (Additive.toMul z))
      = Additive.ofMul (pQMapMul p ψ (Additive.toMul z))
  rw [hmon]

/-- **The group-level square commutes**: the canonical surjection `F(d) ↠ N_d` is natural for a
rank-change map `Φ`, i.e. `flowNormalSubMap Φ ∘ flowNormalSurj_m = flowNormalSurj_n ∘ Φ`. -/
theorem flowNormalSurj_sq (p : ℕ) (G : Type) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) :
    (flowNormalSubMap p G i j Φ).comp (flow.flowNormalSurj p G m i j)
      = (flow.flowNormalSurj p G n i j).comp Φ.toHom := by
  refine MonoidHom.ext (fun x => ?_)
  refine (flowNormalEquiv (G := G) p n i j).symm.injective ?_
  simp only [MonoidHom.comp_apply, flowNormalSubMap, flow.flowNormalSurj]
  simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  rw [flowQuotMap_mk, Subgroup.topEquiv_symm_apply_coe]
  congr 1

/-- **Naturality of the square `F(d)/F(d)^2 ≅ N/N^p[N,N]`.**

The identification of the paper's square quotient `F(d)/F(d)^2` with the bottom `p`-central
quotient of the normal subgroup `N_d = F(d)/F(d)^{(ν)}` is natural in the rank `d`: for a
surjective `G`-operator homomorphism `Φ : F(m) → F(n)` both ways of going from
`F(m)/F(m)^2` to `N_n/N_n^p[N_n,N_n]` agree. -/
theorem sqLin_natural (p : ℕ) [Fact p.Prime] (G : Type) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) (q : squareQuotient p G m) :
    pQMapLin p (flowNormalSubMap p G i j Φ) (pQMapLin p (flow.flowNormalSurj p G m i j) q)
      = pQMapLin p (flow.flowNormalSurj p G n i j)
          (quotMapLin p G Φ.toHom Φ.surjective q) := by
  have hlin : quotMapLin p G Φ.toHom Φ.surjective = pQMapLin p Φ.toHom :=
    quotMapLin_eq_pQMapLin p G Φ.toHom Φ.surjective
  have hsq : (flow.flowNormalSurj p G n i j).comp Φ.toHom
      = (flowNormalSubMap p G i j Φ).comp (flow.flowNormalSurj p G m i j) :=
    (flowNormalSurj_sq p G i j Φ).symm
  have h := pQMapLin_square p Φ.toHom (flowNormalSubMap p G i j Φ)
    (flow.flowNormalSurj p G m i j) (flow.flowNormalSurj p G n i j) hsq
  rw [← LinearMap.comp_apply, ← h, LinearMap.comp_apply, hlin]

end Work.CohomologicalShrinking.naturalAlpha
