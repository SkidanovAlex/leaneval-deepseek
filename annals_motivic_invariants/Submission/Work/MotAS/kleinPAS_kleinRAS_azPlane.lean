/-
# `Work.MotAS.kleinPAS_kleinRAS_azPlane`

The `I2^AS` identity `P^AS (R^AS z) = s'^AS(z) · z` of the Artin--Schreier (characteristic `5`)
branch of the Crauder--Katz quadro-cubic link, in the single case used by the plane section
`z = ![0, u, v, 1, 0]` (`z₀ = z₄ = 0`, `z₃ = 1`).

Both sides are integer polynomials in `a, b, g, u, v` whose difference is divisible by `5`; the
proof is the resulting certificate `(P^AS(R^AS z) − s'^AS(z)·z) / 5`, applied componentwise by
`linear_combination ... * h5`, after the definitions and the `![...]`-coercions have been unfolded.

The auxiliary lemmas evaluate the inverse-map vector `R^AS` and the dual secant quintic at the
plane point, and state the five component identities with *numeral* indices `(0 : Fin 5), …`; the
final assembly then only has to match the `fin_cases` index against the numeral (a definitional
equality).
-/
import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Work.MotAS

/-- The inverse quadro-cubic map `R^AS` at the plane point `z = ![0, u, v, 1, 0]`. -/
private lemma az_kleinRAS_0 {R : Type*} [CommRing R] (a b g u v : R) :
    Work.MotAS.kleinRAS a b g (![0, u, v, 1, 0] : Fin 5 → R) (0 : Fin 5) = (
2*a^(4:ℕ)*g*u^(2:ℕ) + 2*a^(4:ℕ)*g*u*v^(2:ℕ) + 2*a^(4:ℕ)*g*u - a^(4:ℕ)*g*v^(2:ℕ) + a^(4:ℕ)*g + a^(3:ℕ)*b*g*u^(2:ℕ) + a^(3:ℕ)*b*g*u*v^(2:ℕ) - 2*a^(3:ℕ)*b*g*u + a^(3:ℕ)*b*g*v^(2:ℕ) + a^(3:ℕ)*b*g - a^(3:ℕ)*b*u*v + 2*a^(3:ℕ)*b*v^(3:ℕ) + a^(3:ℕ)*b*v - 2*a^(2:ℕ)*b^(2:ℕ)*g*u^(2:ℕ) - 2*a^(2:ℕ)*b^(2:ℕ)*g*u*v^(2:ℕ) + a^(2:ℕ)*b^(2:ℕ)*g - a*b^(3:ℕ)*g*u^(2:ℕ) - a*b^(3:ℕ)*g*u*v^(2:ℕ) - 2*a*b^(3:ℕ)*g*u + a*b^(3:ℕ)*g*v^(2:ℕ) - a*b^(3:ℕ)*g - a*b^(3:ℕ)*u*v + 2*a*b^(3:ℕ)*v^(3:ℕ) - a*b^(3:ℕ)*v + 2*b^(4:ℕ)*g*u^(2:ℕ) + 2*b^(4:ℕ)*g*u*v^(2:ℕ) - 2*b^(4:ℕ)*g*u + b^(4:ℕ)*g*v^(2:ℕ) + b^(4:ℕ)*g) := by
  simp only [kleinRAS, kleinRAS0,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]
  refl_ring1

private lemma az_kleinRAS_1 {R : Type*} [CommRing R] (a b g u v : R) :
    Work.MotAS.kleinRAS a b g (![0, u, v, 1, 0] : Fin 5 → R) (1 : Fin 5) = (
-a^(4:ℕ)*g*u*v - a^(4:ℕ)*g*v^(3:ℕ) - 2*a^(4:ℕ)*g*v - a^(4:ℕ)*u^(3:ℕ) - a^(4:ℕ)*u^(2:ℕ) + a^(4:ℕ)*u*v^(2:ℕ) + a^(4:ℕ)*u - a^(4:ℕ)*v^(2:ℕ) + a^(4:ℕ) + 2*a^(3:ℕ)*b*g*u*v + 2*a^(3:ℕ)*b*g*v^(3:ℕ) + 2*a^(3:ℕ)*b*g*v + a^(3:ℕ)*b*u^(3:ℕ) - a^(3:ℕ)*b*u*v^(2:ℕ) + 2*a^(3:ℕ)*b*v^(2:ℕ) - a^(3:ℕ)*b + a^(2:ℕ)*b^(2:ℕ)*g*u*v + a^(2:ℕ)*b^(2:ℕ)*g*v^(3:ℕ) - 2*a^(2:ℕ)*b^(2:ℕ)*u^(2:ℕ) - 2*a^(2:ℕ)*b^(2:ℕ)*u*v^(2:ℕ) + a^(2:ℕ)*b^(2:ℕ) - 2*a*b^(3:ℕ)*g*u*v - 2*a*b^(3:ℕ)*g*v^(3:ℕ) + 2*a*b^(3:ℕ)*g*v + a*b^(3:ℕ)*u^(3:ℕ) + a*b^(3:ℕ)*u*v^(2:ℕ) + 2*a*b^(3:ℕ)*v^(2:ℕ) + a*b^(3:ℕ) - b^(4:ℕ)*g*u*v - b^(4:ℕ)*g*v^(3:ℕ) + 2*b^(4:ℕ)*g*v + b^(4:ℕ)*u^(3:ℕ) - b^(4:ℕ)*u^(2:ℕ) + b^(4:ℕ)*u*v^(2:ℕ) - b^(4:ℕ)*u + b^(4:ℕ)*v^(2:ℕ) + b^(4:ℕ)) := by
  simp only [kleinRAS, kleinRAS1,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]
  refl_ring1

private lemma az_kleinRAS_2 {R : Type*} [CommRing R] (a b g u v : R) :
    Work.MotAS.kleinRAS a b g (![0, u, v, 1, 0] : Fin 5 → R) (2 : Fin 5) = (
2*a^(4:ℕ)*g*u + 2*a^(4:ℕ)*g*v^(2:ℕ) + 2*a^(4:ℕ)*g + 2*a^(4:ℕ)*u^(2:ℕ)*v - a^(4:ℕ)*u*v - 2*a^(4:ℕ)*v^(3:ℕ) + 2*a^(4:ℕ)*v + a^(3:ℕ)*b*g*u + a^(3:ℕ)*b*g*v^(2:ℕ) - 2*a^(3:ℕ)*b*g - 2*a^(3:ℕ)*b*u^(2:ℕ)*v + 2*a^(3:ℕ)*b*u*v + 2*a^(3:ℕ)*b*v - 2*a^(2:ℕ)*b^(2:ℕ)*g*u - 2*a^(2:ℕ)*b^(2:ℕ)*g*v^(2:ℕ) + a^(2:ℕ)*b^(2:ℕ)*u*v + a^(2:ℕ)*b^(2:ℕ)*v^(3:ℕ) - a*b^(3:ℕ)*g*u - a*b^(3:ℕ)*g*v^(2:ℕ) - 2*a*b^(3:ℕ)*g - 2*a*b^(3:ℕ)*u^(2:ℕ)*v - 2*a*b^(3:ℕ)*u*v + 2*a*b^(3:ℕ)*v + 2*b^(4:ℕ)*g*u + 2*b^(4:ℕ)*g*v^(2:ℕ) - 2*b^(4:ℕ)*g - 2*b^(4:ℕ)*u^(2:ℕ)*v - b^(4:ℕ)*u*v - 2*b^(4:ℕ)*v^(3:ℕ) - 2*b^(4:ℕ)*v) := by
  simp only [kleinRAS, kleinRAS2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]
  refl_ring1

private lemma az_kleinRAS_3 {R : Type*} [CommRing R] (a b g u v : R) :
    Work.MotAS.kleinRAS a b g (![0, u, v, 1, 0] : Fin 5 → R) (3 : Fin 5) = (
2*a^(4:ℕ)*g*v - a^(4:ℕ)*u^(3:ℕ) - a^(4:ℕ)*u^(2:ℕ) + a^(4:ℕ)*u*v^(2:ℕ) + a^(4:ℕ)*u - a^(4:ℕ)*v^(2:ℕ) + a^(4:ℕ) + a^(3:ℕ)*b*g*v + 2*a^(3:ℕ)*b*u^(3:ℕ) + a^(3:ℕ)*b*u^(2:ℕ) - a^(3:ℕ)*b*u*v^(2:ℕ) - a^(3:ℕ)*b*u - 2*a^(3:ℕ)*b - 2*a^(2:ℕ)*b^(2:ℕ)*g*v + a^(2:ℕ)*b^(2:ℕ)*u^(3:ℕ) - 2*a^(2:ℕ)*b^(2:ℕ)*u - 2*a^(2:ℕ)*b^(2:ℕ)*v^(2:ℕ) - a*b^(3:ℕ)*g*v - 2*a*b^(3:ℕ)*u^(3:ℕ) + a*b^(3:ℕ)*u^(2:ℕ) - a*b^(3:ℕ)*u*v^(2:ℕ) + a*b^(3:ℕ)*u - 2*a*b^(3:ℕ) + 2*b^(4:ℕ)*g*v - b^(4:ℕ)*u^(3:ℕ) + b^(4:ℕ)*u^(2:ℕ) - b^(4:ℕ)*u*v^(2:ℕ) + b^(4:ℕ)*u - b^(4:ℕ)*v^(2:ℕ) - b^(4:ℕ)) := by
  simp only [kleinRAS, kleinRAS3,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]
  refl_ring1

private lemma az_kleinRAS_4 {R : Type*} [CommRing R] (a b g u v : R) :
    Work.MotAS.kleinRAS a b g (![0, u, v, 1, 0] : Fin 5 → R) (4 : Fin 5) = (
-a^(4:ℕ)*g + 2*a^(4:ℕ)*u^(2:ℕ)*v - a^(4:ℕ)*u*v - 2*a^(4:ℕ)*v^(3:ℕ) + 2*a^(4:ℕ)*v + 2*a^(3:ℕ)*b*g + a^(3:ℕ)*b*u^(2:ℕ)*v + a^(3:ℕ)*b*u*v + 2*a^(3:ℕ)*b*v^(3:ℕ) + a^(3:ℕ)*b*v + a^(2:ℕ)*b^(2:ℕ)*g - 2*a^(2:ℕ)*b^(2:ℕ)*u^(2:ℕ)*v - 2*a^(2:ℕ)*b^(2:ℕ)*v - 2*a*b^(3:ℕ)*g - a*b^(3:ℕ)*u^(2:ℕ)*v + a*b^(3:ℕ)*u*v + 2*a*b^(3:ℕ)*v^(3:ℕ) - a*b^(3:ℕ)*v - b^(4:ℕ)*g + 2*b^(4:ℕ)*u^(2:ℕ)*v + b^(4:ℕ)*u*v + 2*b^(4:ℕ)*v^(3:ℕ) + 2*b^(4:ℕ)*v) := by
  simp only [kleinRAS, kleinRAS4,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]
  refl_ring1

/-- The dual secant quintic `s'^AS` at the plane point `z = ![0, u, v, 1, 0]`. -/
private lemma az_kleinSecDualAS_az {R : Type*} [CommRing R] (a b g u v : R) :
    Work.MotAS.kleinSecDualAS a b g (![0, u, v, 1, 0] : Fin 5 → R) = (
a^(10:ℕ)*g^(3:ℕ) + a^(10:ℕ)*g^(2:ℕ)*v^(5:ℕ) - a^(10:ℕ)*g^(2:ℕ)*v + a^(10:ℕ)*g*u^(5:ℕ) - 2*a^(10:ℕ)*g*u^(3:ℕ) - a^(10:ℕ)*g*u^(2:ℕ)*v^(2:ℕ) - a^(10:ℕ)*g*u*v^(4:ℕ) + a^(10:ℕ)*g*u - 2*a^(9:ℕ)*b*g*u - a^(9:ℕ)*b*g*v^(2:ℕ) + 2*a^(9:ℕ)*b*g - a^(9:ℕ)*b*u^(3:ℕ)*v + 2*a^(9:ℕ)*b*u^(2:ℕ)*v^(3:ℕ) - a^(9:ℕ)*b*u^(2:ℕ)*v + a^(9:ℕ)*b*u*v - 2*a^(9:ℕ)*b*v^(5:ℕ) + a^(9:ℕ)*b*v^(3:ℕ) + a^(9:ℕ)*b*v - 2*a^(8:ℕ)*b^(2:ℕ)*g*u - a^(8:ℕ)*b^(2:ℕ)*g*v^(2:ℕ) + 2*a^(8:ℕ)*b^(2:ℕ)*g - a^(8:ℕ)*b^(2:ℕ)*u^(3:ℕ)*v + 2*a^(8:ℕ)*b^(2:ℕ)*u^(2:ℕ)*v^(3:ℕ) - 2*a^(8:ℕ)*b^(2:ℕ)*u^(2:ℕ)*v + 2*a^(8:ℕ)*b^(2:ℕ)*u*v + 2*a^(8:ℕ)*b^(2:ℕ)*v^(5:ℕ) - 2*a^(8:ℕ)*b^(2:ℕ)*v^(3:ℕ) + a^(8:ℕ)*b^(2:ℕ)*v + a^(7:ℕ)*b^(3:ℕ)*g*u - 2*a^(7:ℕ)*b^(3:ℕ)*g*v^(2:ℕ) + a^(7:ℕ)*b^(3:ℕ)*g - 2*a^(7:ℕ)*b^(3:ℕ)*u^(3:ℕ)*v - a^(7:ℕ)*b^(3:ℕ)*u^(2:ℕ)*v^(3:ℕ) - a^(7:ℕ)*b^(3:ℕ)*u^(2:ℕ)*v - a^(7:ℕ)*b^(3:ℕ)*u*v + a^(7:ℕ)*b^(3:ℕ)*v^(5:ℕ) + a^(7:ℕ)*b^(3:ℕ)*v^(3:ℕ) - 2*a^(7:ℕ)*b^(3:ℕ)*v - a^(6:ℕ)*b^(4:ℕ)*g*u + 2*a^(6:ℕ)*b^(4:ℕ)*g*v^(2:ℕ) - a^(6:ℕ)*b^(4:ℕ)*g + 2*a^(6:ℕ)*b^(4:ℕ)*u^(3:ℕ)*v + a^(6:ℕ)*b^(4:ℕ)*u^(2:ℕ)*v^(3:ℕ) - 2*a^(6:ℕ)*b^(4:ℕ)*u^(2:ℕ)*v - 2*a^(6:ℕ)*b^(4:ℕ)*u*v + a^(6:ℕ)*b^(4:ℕ)*v^(5:ℕ) - 2*a^(6:ℕ)*b^(4:ℕ)*v^(3:ℕ) + 2*a^(6:ℕ)*b^(4:ℕ)*v - a^(5:ℕ)*b^(5:ℕ)*g^(3:ℕ) - a^(5:ℕ)*b^(5:ℕ)*g^(2:ℕ)*v^(5:ℕ) + a^(5:ℕ)*b^(5:ℕ)*g^(2:ℕ)*v - a^(5:ℕ)*b^(5:ℕ)*g*u^(5:ℕ) + 2*a^(5:ℕ)*b^(5:ℕ)*g*u^(3:ℕ) + a^(5:ℕ)*b^(5:ℕ)*g*u^(2:ℕ)*v^(2:ℕ) + a^(5:ℕ)*b^(5:ℕ)*g*u*v^(4:ℕ) - a^(5:ℕ)*b^(5:ℕ)*g*u + a^(4:ℕ)*b^(6:ℕ)*g*u - 2*a^(4:ℕ)*b^(6:ℕ)*g*v^(2:ℕ) - a^(4:ℕ)*b^(6:ℕ)*g - 2*a^(4:ℕ)*b^(6:ℕ)*u^(3:ℕ)*v - a^(4:ℕ)*b^(6:ℕ)*u^(2:ℕ)*v^(3:ℕ) - 2*a^(4:ℕ)*b^(6:ℕ)*u^(2:ℕ)*v + 2*a^(4:ℕ)*b^(6:ℕ)*u*v + a^(4:ℕ)*b^(6:ℕ)*v^(5:ℕ) + 2*a^(4:ℕ)*b^(6:ℕ)*v^(3:ℕ) + 2*a^(4:ℕ)*b^(6:ℕ)*v + a^(3:ℕ)*b^(7:ℕ)*g*u - 2*a^(3:ℕ)*b^(7:ℕ)*g*v^(2:ℕ) - a^(3:ℕ)*b^(7:ℕ)*g - 2*a^(3:ℕ)*b^(7:ℕ)*u^(3:ℕ)*v - a^(3:ℕ)*b^(7:ℕ)*u^(2:ℕ)*v^(3:ℕ) + a^(3:ℕ)*b^(7:ℕ)*u^(2:ℕ)*v - a^(3:ℕ)*b^(7:ℕ)*u*v - a^(3:ℕ)*b^(7:ℕ)*v^(5:ℕ) + a^(3:ℕ)*b^(7:ℕ)*v^(3:ℕ) + 2*a^(3:ℕ)*b^(7:ℕ)*v + 2*a^(2:ℕ)*b^(8:ℕ)*g*u + a^(2:ℕ)*b^(8:ℕ)*g*v^(2:ℕ) + 2*a^(2:ℕ)*b^(8:ℕ)*g + a^(2:ℕ)*b^(8:ℕ)*u^(3:ℕ)*v - 2*a^(2:ℕ)*b^(8:ℕ)*u^(2:ℕ)*v^(3:ℕ) - 2*a^(2:ℕ)*b^(8:ℕ)*u^(2:ℕ)*v - 2*a^(2:ℕ)*b^(8:ℕ)*u*v + 2*a^(2:ℕ)*b^(8:ℕ)*v^(5:ℕ) + 2*a^(2:ℕ)*b^(8:ℕ)*v^(3:ℕ) + a^(2:ℕ)*b^(8:ℕ)*v - 2*a*b^(9:ℕ)*g*u - a*b^(9:ℕ)*g*v^(2:ℕ) - 2*a*b^(9:ℕ)*g - a*b^(9:ℕ)*u^(3:ℕ)*v + 2*a*b^(9:ℕ)*u^(2:ℕ)*v^(3:ℕ) + a*b^(9:ℕ)*u^(2:ℕ)*v + a*b^(9:ℕ)*u*v + 2*a*b^(9:ℕ)*v^(5:ℕ) + a*b^(9:ℕ)*v^(3:ℕ) - a*b^(9:ℕ)*v - b^(10:ℕ)*g^(3:ℕ) - b^(10:ℕ)*g^(2:ℕ)*v^(5:ℕ) + b^(10:ℕ)*g^(2:ℕ)*v - b^(10:ℕ)*g*u^(5:ℕ) + 2*b^(10:ℕ)*g*u^(3:ℕ) + b^(10:ℕ)*g*u^(2:ℕ)*v^(2:ℕ) + b^(10:ℕ)*g*u*v^(4:ℕ) - b^(10:ℕ)*g*u) := by
  simp only [kleinSecDualAS,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]
  refl_ring1

/-- Component 0 of `I2^AS` at the plane point. -/
private lemma az_comp_0 {R : Type*} [CommRing R] (h5 : (5 : R) = 0)
    (a b g u v : R) :
    Work.MotAS.kleinPAS a b g (Work.MotAS.kleinRAS a b g (![0, u, v, 1, 0] : Fin 5 → R)) (0 : Fin 5)
      = Work.MotAS.kleinSecDualAS a b g (![0, u, v, 1, 0] : Fin 5 → R) * (![0, u, v, 1, 0] : Fin 5 → R) (0 : Fin 5) := by
  simp only [kleinPAS, kleinPAS0, az_kleinRAS_0, az_kleinRAS_1, az_kleinRAS_2,
    az_kleinRAS_3, az_kleinRAS_4, az_kleinSecDualAS_az,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]
  linear_combination (norm := refl_ring1 (mod := 5))

/-- Component 1 of `I2^AS` at the plane point. -/
private lemma az_comp_1 {R : Type*} [CommRing R] (h5 : (5 : R) = 0)
    (a b g u v : R) :
    Work.MotAS.kleinPAS a b g (Work.MotAS.kleinRAS a b g (![0, u, v, 1, 0] : Fin 5 → R)) (1 : Fin 5)
      = Work.MotAS.kleinSecDualAS a b g (![0, u, v, 1, 0] : Fin 5 → R) * (![0, u, v, 1, 0] : Fin 5 → R) (1 : Fin 5) := by
  simp only [kleinPAS, kleinPAS1, az_kleinRAS_0, az_kleinRAS_1, az_kleinRAS_2,
    az_kleinRAS_3, az_kleinRAS_4, az_kleinSecDualAS_az,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]
  linear_combination (norm := refl_ring1 (mod := 5))

/-- Component 2 of `I2^AS` at the plane point. -/
private lemma az_comp_2 {R : Type*} [CommRing R] (h5 : (5 : R) = 0)
    (a b g u v : R) :
    Work.MotAS.kleinPAS a b g (Work.MotAS.kleinRAS a b g (![0, u, v, 1, 0] : Fin 5 → R)) (2 : Fin 5)
      = Work.MotAS.kleinSecDualAS a b g (![0, u, v, 1, 0] : Fin 5 → R) * (![0, u, v, 1, 0] : Fin 5 → R) (2 : Fin 5) := by
  simp only [kleinPAS, kleinPAS2, az_kleinRAS_0, az_kleinRAS_1, az_kleinRAS_2,
    az_kleinRAS_3, az_kleinRAS_4, az_kleinSecDualAS_az,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]
  linear_combination (norm := refl_ring1 (mod := 5))

/-- Component 3 of `I2^AS` at the plane point. -/
private lemma az_comp_3 {R : Type*} [CommRing R] (h5 : (5 : R) = 0)
    (a b g u v : R) :
    Work.MotAS.kleinPAS a b g (Work.MotAS.kleinRAS a b g (![0, u, v, 1, 0] : Fin 5 → R)) (3 : Fin 5)
      = Work.MotAS.kleinSecDualAS a b g (![0, u, v, 1, 0] : Fin 5 → R) * (![0, u, v, 1, 0] : Fin 5 → R) (3 : Fin 5) := by
  simp only [kleinPAS, kleinPAS3, az_kleinRAS_0, az_kleinRAS_1, az_kleinRAS_2,
    az_kleinRAS_3, az_kleinRAS_4, az_kleinSecDualAS_az,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]
  linear_combination (norm := refl_ring1 (mod := 5))

/-- Component 4 of `I2^AS` at the plane point. -/
private lemma az_comp_4 {R : Type*} [CommRing R] (h5 : (5 : R) = 0)
    (a b g u v : R) :
    Work.MotAS.kleinPAS a b g (Work.MotAS.kleinRAS a b g (![0, u, v, 1, 0] : Fin 5 → R)) (4 : Fin 5)
      = Work.MotAS.kleinSecDualAS a b g (![0, u, v, 1, 0] : Fin 5 → R) * (![0, u, v, 1, 0] : Fin 5 → R) (4 : Fin 5) := by
  simp only [kleinPAS, kleinPAS4, az_kleinRAS_0, az_kleinRAS_1, az_kleinRAS_2,
    az_kleinRAS_3, az_kleinRAS_4, az_kleinSecDualAS_az,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]
  linear_combination (norm := refl_ring1 (mod := 5))

theorem kleinPAS_kleinRAS_azPlane {R : Type*} [CommRing R] (h5 : (5 : R) = 0)
    (a b g u v : R) :
    Work.MotAS.kleinPAS a b g (Work.MotAS.kleinRAS a b g (![0, u, v, 1, 0] : Fin 5 → R))
      = fun k => Work.MotAS.kleinSecDualAS a b g (![0, u, v, 1, 0] : Fin 5 → R)
          * (![0, u, v, 1, 0] : Fin 5 → R) k := by
  funext k
  fin_cases k
  · show Work.MotAS.kleinPAS a b g (Work.MotAS.kleinRAS a b g (![0, u, v, 1, 0] : Fin 5 → R)) (0 : Fin 5)
        = Work.MotAS.kleinSecDualAS a b g (![0, u, v, 1, 0] : Fin 5 → R) * (![0, u, v, 1, 0] : Fin 5 → R) (0 : Fin 5)
    exact az_comp_0 h5 a b g u v
  · show Work.MotAS.kleinPAS a b g (Work.MotAS.kleinRAS a b g (![0, u, v, 1, 0] : Fin 5 → R)) (1 : Fin 5)
        = Work.MotAS.kleinSecDualAS a b g (![0, u, v, 1, 0] : Fin 5 → R) * (![0, u, v, 1, 0] : Fin 5 → R) (1 : Fin 5)
    exact az_comp_1 h5 a b g u v
  · show Work.MotAS.kleinPAS a b g (Work.MotAS.kleinRAS a b g (![0, u, v, 1, 0] : Fin 5 → R)) (2 : Fin 5)
        = Work.MotAS.kleinSecDualAS a b g (![0, u, v, 1, 0] : Fin 5 → R) * (![0, u, v, 1, 0] : Fin 5 → R) (2 : Fin 5)
    exact az_comp_2 h5 a b g u v
  · show Work.MotAS.kleinPAS a b g (Work.MotAS.kleinRAS a b g (![0, u, v, 1, 0] : Fin 5 → R)) (3 : Fin 5)
        = Work.MotAS.kleinSecDualAS a b g (![0, u, v, 1, 0] : Fin 5 → R) * (![0, u, v, 1, 0] : Fin 5 → R) (3 : Fin 5)
    exact az_comp_3 h5 a b g u v
  · show Work.MotAS.kleinPAS a b g (Work.MotAS.kleinRAS a b g (![0, u, v, 1, 0] : Fin 5 → R)) (4 : Fin 5)
        = Work.MotAS.kleinSecDualAS a b g (![0, u, v, 1, 0] : Fin 5 → R) * (![0, u, v, 1, 0] : Fin 5 → R) (4 : Fin 5)
    exact az_comp_4 h5 a b g u v

end Work.MotAS
