import Mathlib
import Submission.Work.LLink.Count
import Submission.Work.LLink.isPseudoIso_symm
import Submission.Work.LLink.cInv_eq_zero_of_exDiv_eq_empty
import Submission.Work.Motivic.cInv_eq_zero_of_pseudoReg

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.LLink

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

/-- A partial isomorphism that is an isomorphism in codimension one (`IsPseudoIso`) has no
exceptional divisors in either direction, hence vanishing `[κ(w)]`-coefficient.  This is the
paper's `c(γ) = 0` for a pseudo-isomorphism, in the general form `γ : X ⇢ Y`; Part A
(`Work.Motivic.pseudoReg_cInv_toBirationalMap`) only has the case `X = Y`.

This is the result a caller needs to discharge the hypotheses `cInv 𝕜 z₀ ε = 0` and
`cInv 𝕜 z₀ δ = 0` of `Work.LLink.QuadroCubicLink` whenever the transports to affine space are
pseudo-isomorphisms. -/
theorem cInv_eq_zero_of_isPseudoIso (𝕜 : Type) [Field 𝕜] {X Y : Scheme.{0}}
    [IrreducibleSpace X] [IrreducibleSpace Y] [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))]
    {W : Scheme.{0}} [W.Over (Spec (.of 𝕜))] (w : W) (γ : X.PartialIso Y)
    (hγ : γ.IsPseudoIso) : cInv 𝕜 w γ.toBirationalMap = 0 := by
  have h1 : exDiv γ.toBirationalMap = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hnx⟩
    exact hnx (Work.Motivic.pseudoReg_isIsoAt_toBirationalMap γ hγ hx)
  have h2 : exDiv (γ.toBirationalMap).symm = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hy, hny⟩
    refine hny ⟨γ.symm, ?_, ?_⟩
    · simpa [PartialIso.symm_source] using
        Work.Motivic.pseudoReg_mem_target_of_coheight_one γ hγ hy
    · simp [BirationalMap.symm_hom, PartialIso.toBirationalMap_inv]
  simp [cInv, excCount, h1, h2]

end Work.LLink
