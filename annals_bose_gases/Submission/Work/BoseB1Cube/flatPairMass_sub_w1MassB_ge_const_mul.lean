import ChallengeDeps
import Submission.Work.BoseFixB1B.bareVPairMassExcess
import Submission.Work.BoseFixB1B.w0_ge_const_on_ball
import Submission.Work.BoseFixB1C.PotsplitBddClean
import Submission.Work.BoseFixB1S.chiSmallB_eq_zero_of_volume_dlBox_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

/-- **The bare-`v` pair-mass excess at FS's parameter block.**

`Work.BoseFixB1B.bareVPairMassExcess` already proves exactly the claim

    c₀ · ∬ w_{1,B(u)}  ≤  (∬ w_{B(u)}[v]) − (∬ w_{1,B(u)})

uniformly over admissible `μ` and all sliding positions `u`, for a *fixed* regularity `M`
with `1 ≤ M` and the raw side/ratio `sideAt μ (a v)`, `(paramsAt μ (a v)).d`.  The present
statement is that same claim with `M` instantiated at FS's own regularity
`M = mValue = 48` (i.e. `pM v μ`) and the side/ratio written through the abbreviations
`pL`, `pD`; `flatPairMass` is *by definition* the nested integral `∫∫ wSmallPair … v`, so
only the definitional unfoldings `pM`, `pL`, `pD`, `flatPairMass` separate the two.
(Note `(paramsAt μ (a v)).M = (fsParams (μ (a v)³)).M = mValue` holds definitionally, so
the constant pair supplied by `bareVPairMassExcess` is `μ`-uniform for free.) -/

theorem flatPairMass_sub_w1MassB_ge_const_mul {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ c₀ : ℝ, 0 < ε₀ ∧ 0 < c₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ u : EuclideanSpace ℝ (Fin 3),
        c₀ * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u
          ≤ Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u
            - Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u := by
  obtain ⟨ε₀, c₀, hε₀, hc₀, hkey⟩ :=
    Work.BoseFixB1B.bareVPairMassExcess (v := v) (R := R) hv_supp hR hv hvrad hv1 h hav
      (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue])
  refine ⟨ε₀, c₀, hε₀, hc₀, fun μ hAdm u => ?_⟩
  have hmain := hkey μ hAdm u
  simpa only [Work.BoseFixB1.pM, Work.BoseFixB1.pL, Work.BoseFixB1.pD,
    Work.BoseFixB1.flatPairMass, Work.BoseBox.paramsAt, Work.BoseBox.fsParams] using hmain

end Work.BoseB1Cube
