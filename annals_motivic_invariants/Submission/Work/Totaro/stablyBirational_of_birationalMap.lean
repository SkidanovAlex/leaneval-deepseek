import Mathlib
import Submission.Work.Totaro.Defs
import Submission.Work.Totaro.partialIso_prod_affine
import Submission.Work.K3Inputs.exists_variety_prodOver_affineSpace
import Submission.Work.Motivic.exists_partialIso_toBirationalMap

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Totaro

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- **A birational map gives stable birationality.**  `Work.Totaro.StablyBirational 𝕜 X Y` holds with exponents `0, 0`: a birational map `X ⤏ Y` is represented by a partial isomorphism (`Work.Motivic.exists_partialIso_toBirationalMap`), and `X × 𝔸⁰ ≅ X`, `Y × 𝔸⁰ ≅ Y`.  This is the closure fact that stable birationality contains birationality, the natural companion of `Work.Totaro.StablyBirational_of_isoOver` (isomorphisms being the invertible case), and the ingredient which the "stable birational class" invariant of `NOTES.md` §6 needs for its birational invariance; `Work.Totaro.partialIso_prod_affine`, also in this directory, is the version with a general affine exponent. -/
theorem stablyBirational_of_birationalMap {𝕜 : Type} [Field 𝕜]
    {X Y : AlgebraicGeometry.Scheme.{0}} [MotivicInvariants.Variety 𝕜 X]
    [MotivicInvariants.Variety 𝕜 Y] (h : Nonempty (X.BirationalMap Y)) :
    Work.Totaro.StablyBirational 𝕜 X Y := by
  -- A birational map is represented by a partial isomorphism of dense opens.
  obtain ⟨φ⟩ := h
  obtain ⟨i, _⟩ := Work.Motivic.exists_partialIso_toBirationalMap φ
  -- Multiply by affine `0`-space: `i` stays a partial isomorphism of the (unchanged) products.
  have hX : MotivicInvariants.Variety 𝕜 (Work.K3.prodOver 𝕜 X (𝔸(Fin 0; Spec (.of 𝕜)))) :=
    Classical.choice (Work.K3Inputs.exists_variety_prodOver_affineSpace 𝕜 X 0)
  have hY : MotivicInvariants.Variety 𝕜 (Work.K3.prodOver 𝕜 Y (𝔸(Fin 0; Spec (.of 𝕜)))) :=
    Classical.choice (Work.K3Inputs.exists_variety_prodOver_affineSpace 𝕜 Y 0)
  haveI := hX
  haveI := hY
  exact ⟨0, 0, hX, hY, (partialIso_prod_affine i 0).map PartialIso.toBirationalMap⟩

end

end Work.Totaro
