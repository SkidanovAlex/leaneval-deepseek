import Mathlib
import Submission.Work.MotT.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.MotT

/-- **Bridge node B1** (for route V).  `Good` transports along the base change of Klein data
`Work.MotT.kleinDataBaseChange` (`a`, `b`, `coord` are mapped, `E` is base changed).  This is what
lets the generic nodes `Work.MotT.twistFieldTK_descent`, `Work.MotT.twistFieldTK_regular`,
`Work.MotT.twist_iso_pointK` — proved for an arbitrary base field `K` — be applied at
`K = RatFunc 𝕜` to a Klein model `D : Work.MotV.KleinData 𝕜` coming from route V.

Route: every field of `Work.MotV.KleinData.Good` transports.  `ab_ne` and `elliptic` are immediate
(`Work.MotT.kleinDataBaseChange`, the `WeierstrassCurve.map` instance); `j_ne_zero`/`j_ne` follow
from `WeierstrassCurve.map_j` and injectivity of `algebraMap 𝕜 L`.  The content is
`klein_eq`/`T_diag`/`spans`, for which one first identifies the Klein coordinates:
`kleinCoord (Work.MotT.kleinDataBaseChange D L) M = kleinCoord D M` for `[Algebra L M]`; then the
corresponding field of `hD` at `M` gives the claim.  Note `hD`'s fields need an `Algebra 𝕜 M`
structure, which the prover must manufacture locally (`(algebraMap 𝕜 L).comp (algebraMap L M)`),
and `(D.E.baseChange L).baseChange M = D.E.baseChange M` is propositional
(`WeierstrassCurve.ext` and pointwise `IsScalarTower.algebraMap_apply`).
Declare it in namespace `Work.MotT` so that its full name is
`Work.MotT.kleinDataBaseChange_good`. -/
theorem kleinDataBaseChange_good {𝕜 L : Type} [Field 𝕜] [Field L] [Algebra 𝕜 L]
    (D : Work.MotV.KleinData 𝕜) (hD : D.Good) :
    (Work.MotT.kleinDataBaseChange D L).Good := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `elliptic`: the base change of an elliptic curve is elliptic
    haveI := hD.elliptic
    show (D.E.map (algebraMap 𝕜 L)).IsElliptic
    infer_instance
  · -- `ab_ne`: `algebraMap` is injective and `L` is a domain
    have h := hD.ab_ne
    rw [mul_ne_zero_iff] at h
    show algebraMap 𝕜 L D.a * algebraMap 𝕜 L D.b ≠ 0
    exact mul_ne_zero ((map_ne_zero (algebraMap 𝕜 L)).mpr h.1)
      ((map_ne_zero (algebraMap 𝕜 L)).mpr h.2)
  · -- `j_ne_zero`: `j` is mapped by `WeierstrassCurve.map_j`
    haveI := hD.elliptic
    show (D.E.map (algebraMap 𝕜 L)).j ≠ 0
    rw [WeierstrassCurve.map_j]
    exact (map_ne_zero (algebraMap 𝕜 L)).mpr hD.j_ne_zero
  · -- `j_ne`: `1728` is the `𝕜`-constant `1728`, so injectivity of `algebraMap` forbids `j = 1728`
    haveI := hD.elliptic
    show (D.E.map (algebraMap 𝕜 L)).j ≠ 1728
    rw [WeierstrassCurve.map_j, ← map_ofNat (algebraMap 𝕜 L) 1728]
    intro h
    exact hD.j_ne ((algebraMap 𝕜 L).injective h)
  · -- `klein_eq`: `kleinCoord` does not see the base change of the Klein data
    intro M _ _ k
    letI : Algebra 𝕜 M := RingHom.toAlgebra ((algebraMap L M).comp (algebraMap 𝕜 L))
    haveI : IsScalarTower 𝕜 L M := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    have h := hD.klein_eq M k
    simp only [Work.MotT.kleinDataBaseChange] at h ⊢
    exact h
  · -- `coord0_ne`
    intro M _ _
    letI : Algebra 𝕜 M := RingHom.toAlgebra ((algebraMap L M).comp (algebraMap 𝕜 L))
    haveI : IsScalarTower 𝕜 L M := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    exact hD.coord0_ne M
  · -- `T_diag`: the Kleinian `μ₅`-action is unaffected by the base change
    intro M _ _ ζ hζ
    letI : Algebra 𝕜 M := RingHom.toAlgebra ((algebraMap L M).comp (algebraMap 𝕜 L))
    haveI : IsScalarTower 𝕜 L M := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    obtain ⟨σ, hσ⟩ := hD.T_diag M ζ hζ
    exact ⟨σ, hσ⟩
  · -- `spans`: transport the matrix `e` witnessing that the `κ_i` generate `1, x, y, x², xy`
    obtain ⟨e, he⟩ := hD.spans
    refine ⟨fun m i => algebraMap 𝕜 L (e m i), fun M _ _ m => ?_⟩
    letI : Algebra 𝕜 M := RingHom.toAlgebra ((algebraMap L M).comp (algebraMap 𝕜 L))
    haveI : IsScalarTower 𝕜 L M := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    have h := he M m
    simp only [Work.MotT.kleinDataBaseChange] at h ⊢
    exact h

end Work.MotT
