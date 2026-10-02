import Mathlib
import Submission.Work.Gen.CruxDefs
import Submission.Work.Cohomology.h0Evaluation
import Submission.Work.Thom.Coh_zero_cover_injective
import Submission.Work.Thom.isOrientedOver_of_det_pos
import Submission.Work.Thom.chartCoeffAux
import Submission.Work.Cohomology.punit

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Gen

open Work.TangentClasses Work.Thom in
/-- **A degree-`0` class of `H⁰(B;ℤ)` whose value at every point is `k` is `k · 1`.**  Here "the
value at `b`" is the pullback along the constant map `constFibre Z b : ProjFibre Z b → B` to the
fibre of `P(Z) → B` (nonempty because `m ≥ 1`).  `H⁰(B;ℤ)` is the group of locally constant
`ℤ`-valued functions on `B` (`Work.Cohomology.h0Ev` separates classes, `Work.Thom.h0Ev_ext`), so if
the value at every point is the same integer `k` then the class is `k · 1`.  The hypothesis
`1 ≤ m` is necessary: for `m = 0` the fibre is empty and the hypothesis is vacuous. -/
theorem Coh_zero_eq_smul_oneH_of_constFibre {B : Type} [TopologicalSpace B]
    {ι : Type} [Fintype ι] {m : ℕ} (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (z : Work.Thom.Coh ℤ 0 B) (k : ℤ)
    (h : ∀ b : B,
      (ModuleCat.Hom.hom (Work.Thom.CohMap (Work.Gen.constFibre Z b) ℤ 0)) z
        = k • Work.Cohomology.oneH ℤ (Work.Whitney.ssB (Work.LerayHirsch.ProjFibre Z b))) :
    z = k • Work.Cohomology.oneH ℤ (Work.Whitney.ssB B) := by
  -- `H⁰` is detected by its evaluations at the points of `B`.
  refine Work.Thom.ptEv_ext (fun b => ?_)
  -- The fibre of `P(Z)` over `b` is nonempty because `m ≥ 1`.
  obtain ⟨x, hx⟩ := Work.LerayHirsch.surjective_projMap Z hm b
  set s : Work.LerayHirsch.ProjFibre Z b := ⟨x, hx⟩ with hs
  -- The value of `k · 1` at any point is `k`.
  have hR : ptEv b (k • Work.Cohomology.oneH ℤ (Work.Whitney.ssB B)) = k := by
    have h1 : ptEv b (k • Work.Cohomology.oneH ℤ (Work.Whitney.ssB B))
        = k * ptEv b (Work.Cohomology.oneH ℤ (Work.Whitney.ssB B)) :=
      ptEv_smul b k (Work.Cohomology.oneH ℤ (Work.Whitney.ssB B))
    rw [h1, ptEv_one, mul_one]
  have hL : ptEv s (k • Work.Cohomology.oneH ℤ
      (Work.Whitney.ssB (Work.LerayHirsch.ProjFibre Z b))) = k := by
    have h1 : ptEv s (k • Work.Cohomology.oneH ℤ
          (Work.Whitney.ssB (Work.LerayHirsch.ProjFibre Z b)))
        = k * ptEv s (Work.Cohomology.oneH ℤ
            (Work.Whitney.ssB (Work.LerayHirsch.ProjFibre Z b))) :=
      ptEv_smul s k (Work.Cohomology.oneH ℤ
        (Work.Whitney.ssB (Work.LerayHirsch.ProjFibre Z b)))
    rw [h1, ptEv_one, mul_one]
  -- Naturality of the evaluation under the pullback along the constant map to the fibre.
  have hnat := Work.Thom.ptEv_pullback (Work.Gen.constFibre Z b) s z
  rw [show (Work.Gen.constFibre Z b) s = b from rfl] at hnat
  -- Combine.
  rw [hR, ← hL, ← hnat, h b]

end Work.Gen
