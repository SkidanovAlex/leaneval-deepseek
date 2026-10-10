import Mathlib
import Submission.Work.Twist.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open CategoryTheory AlgebraicGeometry
open Work.Twist

/-- **The local obstruction from a Galois-equivariant map.**  An additive map `φ` out of `E(L)`
which is invariant under the Galois action (`φ ∘ σ = φ`, which is what holds for the reduction
map at a place at which `σ` acts trivially on the residue field) and which does not kill `P`
produces the local-obstruction datum of `D`, hence `D.Pointless`
(`localObstruction_pointless`).  Together with `LocalObstruction` this is the form in which the
paper decides `cls ≠ 0`.

`LocalObstruction D` and `HasLocalObstruction D` are defined in
`Submission/Work/Twist/Defs.lean`; the field `map_shift` follows from additivity of `φ` and
`hgal`, so the proof is `⟨G, φ, hP, fun R => by rw [map_sub, hgal R, sub_self]⟩`. -/
theorem localObstruction_of_galTrivial {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) (G : Type) [AddCommGroup G] (φ : D.LPoints →+ G)
    (hgal : ∀ x : D.LPoints, φ (D.galMap x) = φ x) (hP : φ D.PL ≠ 0) :
    HasLocalObstruction D :=
  ⟨{ G := G
     toFun := φ
     map_PL := hP
     map_shift := fun R => by
       rw [map_sub, hgal R, sub_self] }⟩

end Work.Twist
