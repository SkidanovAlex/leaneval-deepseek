import Mathlib
import Submission.Work.CY3Stab.Defs
import Submission.Work.CY3Stab.Variety

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.CY3Stab.Prod

theorem prodMap_symm (𝕜 : Type) [Field 𝕜] (k : ℕ) {X Y : AlgebraicGeometry.Scheme.{0}}
    [MotivicInvariants.Variety 𝕜 X] [MotivicInvariants.Variety 𝕜 Y] (φ : X.BirationalMap Y)
    [hφ : φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [hwX : MotivicInvariants.Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)]
    [hwY : MotivicInvariants.Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k)]
    [hSY : (φ.symm).IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] :
    (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ).symm = Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ.symm := by
  classical
  apply AlgebraicGeometry.Scheme.BirationalMap.ext
  rw [AlgebraicGeometry.Scheme.BirationalMap.symm_hom]
  obtain ⟨g, hgOver, hgtr⟩ :=
    φ.inv.exists_partialMap_over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))
  haveI : g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) := hgOver
  rw [← (Work.CY3Stab.prodMap_spec (𝕜 := 𝕜) k φ).2.2 g hgtr]
  exact (Work.CY3Stab.prodMap_spec (𝕜 := 𝕜) k φ.symm).2.1 g
    (by rw [AlgebraicGeometry.Scheme.BirationalMap.symm_hom]; exact hgtr)

end Work.CY3Stab.Prod
