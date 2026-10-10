import Mathlib
import Submission.Work.CrauderKatz.Defs
import Submission.Work.Motivic.cInv_add
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CrauderKatz

/-- **Conjugation creates nothing new.**  For a birational map `ψ : S ⤏ T` over `𝕜` and a birational
self-map `σ` of `T` over `𝕜`, the conjugate `ψ ∘ σ ∘ ψ⁻¹` of `σ` by `ψ` has the same invariant
coefficient as `σ` at every base point.  Consequently a one-sided link (whose own coefficient is
non-zero, see `Work.CrauderKatz.cInv_eq_one_of_oneSidedLink`) yields *no* non-trivial element of
`Cr 𝕜 3` when transported by its own inverse: the contribution of the link is exactly cancelled by
that of the transport, because `cInv` is additive (`Work.Motivic.cInv_add`) and
`cInv 𝕜 z ψ⁻¹ = -cInv 𝕜 z ψ` (`Work.LLink.cInv_eq_neg_symm`).  This is the formal content of
§6.3(a) of `Submission/Work/CrauderKatz/NOTES.md`, where it is used to explain why the Crauder–Katz
link has to be genuinely two-sided.

The two `IsOver` hypotheses are needed: `Work.Motivic.cInv_add` requires them (through the
`IsOver`-instances of `ψ.symm` and `σ.trans ψ.symm`, which are provided by the `IsOver.symm` and
`IsOver.trans` instances of the workspace). -/
theorem cInv_conj_eq (𝕜 : Type) [Field 𝕜] {S T : AlgebraicGeometry.Scheme.{0}}
    [MotivicInvariants.Variety 𝕜 S] [MotivicInvariants.Variety 𝕜 T]
    {Z : AlgebraicGeometry.Scheme.{0}}
    [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] (z : Z) (ψ : S.BirationalMap T)
    [ψ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] (σ : T.BirationalMap T)
    [σ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] :
    cInv 𝕜 z (ψ.trans (σ.trans ψ.symm)) = cInv 𝕜 z σ := by
  haveI hψs : (ψ.symm).IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) :=
    inferInstanceAs (ψ.inv.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
  haveI hcomp : (σ.trans ψ.symm).IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) := by
    change (σ.hom.comp ψ.inv).IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))
    infer_instance
  have h1 : cInv 𝕜 z (ψ.trans (σ.trans ψ.symm))
      = cInv 𝕜 z ψ + cInv 𝕜 z (σ.trans ψ.symm) :=
    Work.Motivic.cInv_add 𝕜 z ψ (σ.trans ψ.symm)
  have h2 : cInv 𝕜 z (σ.trans ψ.symm) = cInv 𝕜 z σ + cInv 𝕜 z ψ.symm :=
    Work.Motivic.cInv_add 𝕜 z σ ψ.symm
  have h3 : cInv 𝕜 z ψ.symm = -cInv 𝕜 z ψ := Work.LLink.cInv_eq_neg_symm 𝕜 z ψ
  rw [h1, h2, h3]
  first | refl_ring1 | ring

end Work.CrauderKatz
