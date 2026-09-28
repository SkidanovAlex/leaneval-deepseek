import Mathlib
import Submission.Work.Kunneth.HomCross
import Submission.Work.Kunneth.cohomologyClassOf_comp_normP
import Submission.Work.Kunneth.crossH_cohomologyClassOf
import Submission.Work.KunnethEZ.normalizedDetectedPairSph

/-!
# The Kronecker rule for the cross products, unconditional form

The Kronecker rule `Work.Kunneth.kronH_homCrossLin` asks for a *normalized* cocycle
representative of the second factor's class.  Every cohomology class has one:
`β.∘ normP` is a cocycle (`cochainDiff_comp_normP`), it annihilates the degenerate simplices
(`normP_degenerate`) and it represents the same class
(`Work.Kunneth.cohomologyClassOf_comp_normP`).  Replacing the representative by this one gives the
rule with no hypothesis on the cochains:

  `⟨a × b, x × y⟩ = ⟨a, x⟩ · ⟨b, y⟩`

for all simplicial sets `X`, `Y` with free (projective) homology, all degrees `p, q`, all classes
`a ∈ Hᵖ(X)`, `b ∈ H^q(Y)`, `x ∈ H_p(X)`, `y ∈ H_q(Y)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

open Work.Cohomology

attribute [-instance] AddCommGroup.toIntModule

/-- **The Kronecker rule for the cross products**: `⟨a × b, x × y⟩ = ⟨a,x⟩·⟨b,y⟩`. -/
theorem kronH_crossH_homCrossLin (X Y : SSet) (p q : ℕ)
    (hX : ∀ n, Module.Projective ℤ ↥((sChain X).homology n))
    (hY : ∀ n, Module.Projective ℤ ↥((sChain Y).homology n))
    (a : ↥((cochainC ℤ X).homology p)) (b : ↥((cochainC ℤ Y).homology q))
    (x : ↥((sChain X).homology p)) (y : ↥((sChain Y).homology q)) :
    kronH ℤ (sProd X Y) (p + q) (crossH X Y p q a b)
        (homCrossLin X Y p q hX hY (x ⊗ₜ[ℤ] y))
      = kronH ℤ X p a x * kronH ℤ Y q b y := by
  obtain ⟨α, hα, rfl⟩ := exists_cohomologyClassOf ℤ X p a
  obtain ⟨β, hβ, rfl⟩ := exists_cohomologyClassOf ℤ Y q b
  obtain ⟨hβn, hclass⟩ := cohomologyClassOf_comp_normP Y q β hβ
  have hn : ∀ z ∈ Y.degenerate q, genEval ℤ Y (β.comp (Work.KunnethEZ.normP Y q)) z = 0 := by
    intro z hz
    rw [show genEval ℤ Y (β.comp (Work.KunnethEZ.normP Y q)) z
        = β (Work.KunnethEZ.normP Y q ((Y.ιChainComplex (R := zz) z).hom 1)) from rfl,
      Work.KunnethEZ.normP_degenerate Y q z hz, map_zero]
  have hc : cochainDiff ℤ (sProd X Y)
      (crossCochain X Y p q α (β.comp (Work.KunnethEZ.normP Y q))) = 0 :=
    crossCochain_isCocycle X Y p q α _ hα hβn
  rw [← hclass,
    crossH_cohomologyClassOf X Y p q α (β.comp (Work.KunnethEZ.normP Y q)) hα hβn hc]
  exact kronH_homCrossLin X Y p q hX hY x y α (β.comp (Work.KunnethEZ.normP Y q))
    hα hβn hn hc

end

end Work.Kunneth
