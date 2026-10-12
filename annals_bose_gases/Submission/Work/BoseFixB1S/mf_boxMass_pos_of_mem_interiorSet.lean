import ChallengeDeps
import Submission.Work.BoseFixB1S.flatBranchDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

/-- **The sliding box has positive measure at an admissible interior point.**  Route:
`mfV v μ u = boxMass ℓ d u` with `ℓ = sideAt μ (a v)`, `d = (paramsAt μ (a v)).d`;
`d ≤ 1` because `d = fsXp (μ(a v)³) 6 = (μ(a v)³)^{6/323} ≤ 1` (`Work.BoseFixB1.d_eq_fsXp`,
`μ(a v)³ ≤ ε₀ ≤ 1`), so `Work.BoseFixB1S.oneBodyB1.sqrtW.boxMassProdB1` writes
`boxMass ℓ d u = ∏ j, max 0 (shortSide ℓ d u j)`; each factor is positive:
`shortSide ℓ d u j = min (ℓd) (½ℓ(1+d) − |((ℓd)•u)_j|) > 0` since `ℓd > 0`
(`Work.BoseFixB1.adm_ell_pos`, `Work.BoseFixB1.adm_d_pos`) and
`|((ℓd)•u)_j| ≤ ½ℓ(1+d) − 2μ^{-1/3} < ½ℓ(1+d)` (`hu` read through
`Work.SmallBoxSliding.mem_interiorSet_iff`, `μ^{-1/3} > 0` from `0 < μ`). -/
theorem mf_boxMass_pos_of_mem_interiorSet {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε₀ μ : ℝ}
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) (hε₀ : ε₀ ≤ 1) {u : EuclideanSpace ℝ (Fin 3)}
    (hu : Work.BoseFixB1S.mfInt v μ u) :
    0 < Work.BoseFixB1S.mfV v μ u := by
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hav : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
    Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
    Work.BoseFixB1.adm_d_pos hAdm
  have ht : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
    Work.BoseFixB1.adm_dilute_le_one hAdm hε₀
  -- `d = (μa³)^{6/323} ≤ 1` since `0 < μa³ ≤ 1`
  have hd1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 := by
    rw [Work.BoseFixB1.d_eq_fsXp]
    exact Work.BoseBox.fsXp_le_one ht ht1 (by norm_num)
  have hδ : 0 < μ ^ (-1 / 3 : ℝ) := Real.rpow_pos_of_pos hμ _
  -- the product formula for the box volume
  rw [Work.BoseFixB1S.mfV_def,
    Work.BoseFixB1S.oneBodyB1.sqrtW.boxMassProdB1 hℓ hd hd1 u]
  refine Finset.prod_pos (fun j _ => ?_)
  rw [Work.SmallBoxSliding.shortSide]
  -- the interior hypothesis, coordinate `j`
  have hj : |((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) • u).ofLp j|
      ≤ 1 / 2 * Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (1 + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
        - 2 * μ ^ (-1 / 3 : ℝ) :=
    (Work.SmallBoxSliding.mem_interiorSet_iff.mp hu) j
  refine lt_max_iff.mpr (Or.inr (lt_min (mul_pos hℓ hd) ?_))
  linarith

end Work.BoseFixB1S
