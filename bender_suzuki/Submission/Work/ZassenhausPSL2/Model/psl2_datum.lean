import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Model.psl2_isSplitRankOne
import Submission.Work.ZassenhausPSL2.Model.psl2_frel
import Submission.Work.RankOneUniqueness.All
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.Models.Port.PSL2Model

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausPSL2.Model

/-- **The model rank-one datum of `PSL(2, 2ⁿ)`.**

Taking the split rank-one data `(B, U, w)` of `Submission.PSL2.pSL2BenderPair n hn` (the Borel
subgroup, the unipotent radical and the Weyl element of the model `PSL(2, 2ⁿ)`) and
coordinatising the root group `U` by `Multiplicative (GaloisField 2 n)` through the injective
map `u ↦ unipotentPSLHom (ofAdd u)`, the Zassenhaus `f`-relation `psl2_frel` exhibits this as a
`ModelRankOneDatum` whose `f`-map is `psl2F : b ↦ b⁻¹`. -/
theorem psl2_datum (n : ℕ) (hn : 2 ≤ n) :
    Nonempty (Work.RankOneUniqueness.ModelRankOneDatum (LeanEval.GroupTheory.Defs.PSL2Model n)
      (Multiplicative (GaloisField 2 n)) (Work.ZassenhausPSL2.psl2F n)) := by
  classical
  have hchar : CharP (GaloisField 2 n) 2 := inferInstance
  let P := Submission.PSL2.pSL2BenderPair n hn
  refine ⟨{ H := P.B, Q := P.U, t := P.w,
            split := Work.ZassenhausPSL2.Model.psl2_isSplitRankOne n hn,
            simple := Submission.PSL2Model_isSimpleGroup n hn,
            c := MonoidHom.ofInjective
                   (f := Commons.GroupTheory.SL2.unipotentPSLHom (GaloisField 2 n))
                   (Commons.GroupTheory.SL2.unipotentPSLHom_injective hchar),
            frel := ?_ }⟩
  intro u hu
  -- `u ≠ 1` in the multiplicative group is `toAdd u ≠ 0` in the field.
  have hb : Multiplicative.toAdd u ≠ 0 := by
    intro h
    exact hu (by rw [← show Multiplicative.ofAdd (Multiplicative.toAdd u) = u from rfl, h]; rfl)
  obtain ⟨m, hm, hEq⟩ := Work.ZassenhausPSL2.Model.psl2_frel n hn (Multiplicative.toAdd u) hb
  refine ⟨m, hm, ?_⟩
  simp only [Work.ZassenhausPSL2.psl2F]
  exact hEq

end Work.ZassenhausPSL2.Model
