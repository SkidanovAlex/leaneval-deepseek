import Mathlib
import Submission.Work.PSU3.StageB.Omega.API

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.Omega

theorem exists_zcQF_eq_of_mem_Q0 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (fr : Work.PSU3.CoarseFrame H Q t n) {x : ↥Q} (hx : (x : G) ∈ fr.Q0) (hx1 : x ≠ 1) :
    ∃ u : ↥(Work.PSU3.StageB.FX n), Work.PSU3.StageB.zcQF fr u = x := by
  obtain ⟨v, hv, hvz⟩ := fr.zc_surj (x : G) hx
  have hv0 : v ≠ 0 := by
    intro hc
    rw [hc, Work.PSU3.StageB.zc_zero fr] at hvz
    exact hx1 (Subtype.ext hvz.symm)
  refine ⟨Work.PSU3.StageB.mkFX v hv hv0, ?_⟩
  apply Subtype.ext
  rw [Work.PSU3.StageB.zcQF_coe, Work.PSU3.StageB.fval_mkFX]
  exact hvz

end Work.PSU3.StageB.Omega
