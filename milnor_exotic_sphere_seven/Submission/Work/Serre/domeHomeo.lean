import Mathlib
import Submission.Work.Serre.SweepRelDefs
import Submission.Work.RatHurewicz.DomeMap
import Submission.Work.RatHurewicz.domePt_surj_dome

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The dome homeomorphism `I^m ≅ ∂I^{m+1} ∖ int (bottom face)`

`Work.RatHurewicz.domePt` is the explicit parametrisation of the "dome"
`∂I^{m+1} ∖ int {z | z (Fin.last m) = 0}` by the cube `I^m`.  It is continuous and injective
(`DomeMap.lean`), and surjective onto the dome (`domePt_surj_dome.lean`).  Since `I^m` is compact
and the dome is Hausdorff, it is a homeomorphism; this file packages it as such and verifies the
three properties recorded in `Work.Serre.IsDomeHomeo`.
-/

namespace Work.Serre

open scoped unitInterval Topology

open Work.RatHurewicz (IsDomePt domePt domePt_isDomePt domePt_injective continuous_domePt
  domePt_surj_dome domePt_last domePt_castSucc domePt_last_eq_zero_of_mem_boundary
  mem_boundary_of_domePt_last_eq_zero domeR domeR_eq domeTime domeTime_eq_zero_iff domeSpace
  domeSpace_coe)
open Work.ThomBordism.TwoSet (rad rad_boundary_eq_one)

noncomputable section

/-- **The dome is homeomorphic to the cube.**  The homeomorphism is the explicit dome
parametrisation `domePt hm`. -/
theorem domeHomeo {m : ℕ} (hm : 1 ≤ m) :
    ∃ e : (Fin m → unitInterval) ≃ₜ
      ↥{z : Fin (m + 1) → unitInterval | Work.RatHurewicz.IsDomePt z},
      Work.Serre.IsDomeHomeo hm e := by
  let F : (Fin m → unitInterval) → ↥{z : Fin (m + 1) → unitInterval | IsDomePt z} :=
    fun y => ⟨domePt hm y, domePt_isDomePt hm y⟩
  have hFc : Continuous F := Continuous.subtype_mk (continuous_domePt hm) _
  have hFi : Function.Injective F :=
    fun a b h => domePt_injective hm (Subtype.ext_iff.mp h)
  have hFs : Function.Surjective F := by
    intro z
    obtain ⟨y, hy⟩ := domePt_surj_dome m hm z.2.1 z.2.2
    exact ⟨y, Subtype.ext hy⟩
  refine ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hFi, hFs⟩) hFc,
    ?_, ?_, ?_⟩
  · intro y
    show (F y : Fin (m + 1) → unitInterval) = domePt hm y
    rfl
  · intro y
    change y ∈ Cube.boundary (Fin m) ↔ domePt hm y (Fin.last m) = 0
    exact ⟨domePt_last_eq_zero_of_mem_boundary hm, mem_boundary_of_domePt_last_eq_zero hm⟩
  · intro y hy
    change domePt hm y = snocPt y 0
    have hrad : rad hm y = 1 := rad_boundary_eq_one hm hy
    have hR : domeR hm y = 1 := by
      rw [domeR_eq (show (1 / 2 : ℝ) ≤ rad hm y by rw [hrad]; norm_num), hrad]
    have htime : domeTime hm y = 0 := (domeTime_eq_zero_iff hm y).mpr hrad
    have hspace : domeSpace hm y = y := by
      funext i
      apply Subtype.ext
      rw [domeSpace_coe, hR, div_one]
      ring
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [domePt_castSucc, snocPt_castSucc, hspace]
    · rw [domePt_last, snocPt_last, htime]

end

end Work.Serre
