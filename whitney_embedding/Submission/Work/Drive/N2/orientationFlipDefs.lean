import Mathlib
import Submission.Work.Drive.Morse

/-!
# The round planar picture and the half-turn path used by the orientation flip

`roundPic : ℝ → ℝ³` is the standard round planar picture of the circle (`t ↦ (cos t, sin t, 0)`,
`2π`-periodic, injective mod the period, immersive), and `rotX s` is the rotation of `ℝ³` about the
first coordinate axis by the angle `s * π`: a path of linear isometries with `rotX 0 = id` and
`rotX 1` the half-turn, which reverses the round picture.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff

noncomputable section

/-- The standard round planar picture of the circle in `ℝ³`, lifted `2π`-periodically in `t`. -/
def roundPic (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![Real.cos t, Real.sin t, (0 : ℝ)]

/-- Rotation of `ℝ³` about the first coordinate axis by the angle `s * π`, as a continuous linear map.
At `s = 0` this is the identity map and at `s = 1` the half-turn in the second and third
coordinates. -/
def rotX (s : ℝ) : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin 3 =>
      if i = (0 : Fin 3) then EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0
      else if i = (1 : Fin 3) then
        Real.cos (s * Real.pi) • EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 1 -
          Real.sin (s * Real.pi) • EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2
      else
        Real.sin (s * Real.pi) • EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 1 +
          Real.cos (s * Real.pi) • EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2))

end

end Work.Drive.N2
