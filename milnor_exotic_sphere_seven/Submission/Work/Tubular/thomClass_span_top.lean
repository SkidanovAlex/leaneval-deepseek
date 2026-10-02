import Submission.Work.Tubular.modelClass_fibre_span_top
import Submission.Work.Thom.ThomClass

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-!
# A Thom class generates the relative cohomology of the Thom pair

For a rank-`n` real bundle `Z → B` over a path-connected base and a Thom class `T` of `Z`
(`Work.Thom.ThomClass`), the class `T.τ ∈ H^n(X, X∖0)` alone generates the whole (free) `ℤ`-module
`H^n(X, X∖0)`: this is the `k = 0` slice of the Thom isomorphism `T.isThom`.  It is the input that
turns the Thom class into an *orientation*: the relative fundamental class of the Thom pair is a
`ℤ`-basis element, and the local-degree computations of `Submission/Work/Tubular/LocalStep.lean`
need exactly this.

The degree bookkeeping is the usual one: `thomMap Z n T.τ 0` lands in degree `0 + n`, while `T.τ`
lives in degree `n`; the transport lemmas of
`Submission/Work/Tubular/modelClass_fibre_span_top.lean` mediate.

**Not** to be confused with the *fibrewise* generator property: this statement is about the whole
module `H^n(X, X∖0)`, and does not by itself say that the restriction of `T.τ` to the fibre over a
point generates — that is `Work.Tubular.modelClassPunct_fibre_span_top` and
`Work.Tubular.localThomOfChart_fibre_span_top`, and it needs the explicit chart description of the
class, not just the Thom isomorphism.
-/

open CategoryTheory Limits
open scoped Topology

namespace Work.Tubular

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- **A Thom class generates `H^n(X, X∖0)`.** -/
theorem thomClass_span_top [PathConnectedSpace B]
    (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ) (T : Work.Thom.ThomClass Z n) :
    Submodule.span ℤ {((Nat.zero_add n).symm ▸ T.τ)} = ⊤ := by
  have h0 : Submodule.span ℤ
      {Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of B))} = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun x => ?_
    rw [Submodule.mem_span_singleton]
    obtain ⟨m, hm⟩ := Work.Cohomology.exists_smul_oneH (TopCat.of B) x
    refine ⟨m, ?_⟩
    rw [hm]
    exact int_smul_eq_zsmul (inferInstance : Module ℤ (Work.Thom.Coh ℤ 0 B)) m
      (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of B)))
  have hval : (Work.Thom.thomMap Z n T.τ 0)
      (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of B)))
      = (Nat.zero_add n).symm ▸ T.τ := by
    rw [Work.Thom.thomMap_apply, Work.Thom.CohMap_oneH, Work.Thom.mixedCupC_eq_mixedCup,
      Work.Thom.mixedCup_oneH_zero]
  rw [← hval]
  exact span_singleton_map_eq_top (Work.Thom.thomMap Z n T.τ 0) (T.isThom 0).2 _
    h0

end

end Work.Tubular
