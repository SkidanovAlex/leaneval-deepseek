import Mathlib
import Submission.Work.MotAS.ASTransportR
import Submission.Work.MotAS.ASMatrix
import Submission.Work.MotAS.asTransportS
import Submission.Work.MotAS.asTransportSD
import Submission.Work.MotK.KleinLinkUnit
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The AS link data and the transported Crauder–Katz identities

Part of the subproject `Submission/Work/MotAS` (`Work.MotAS`), `MOTIVIC_KDATA_LEAD.md` §6.  Here we
assemble the *link data* of the quadro-cubic (Crauder–Katz) transformation in Artin–Schreier Galois
coordinates, exactly as `Work.MotK.LinkData` / `Work.MotK.KleinLinkUnit` do for the split model:

* `kleinBilinAS` is the polar form of the twisted quadric `kleinQAS`;
* `kleinStereoAS a b p v` is the inverse stereographic projection from a point `p` of that quadric;
* `kleinFhomAS a b g p v = b(p,v)·s^AS(y(v))` the source equation,
* `kleinGhomAS a b g p w = b(p, R^AS(w))·s'^AS(w)` the target equation.

The *stereographic point* used downstream is the all-ones vector `p = ![1,1,1,1,1]`: it satisfies
`kleinQAS p = 0` in characteristic `5` (`kleinQAS_ones`), lies off the twisted curve
(`kleinPAS_ones`, using `a² − ab − b² ≠ 0` of `ASGood`) and off the twisted secant variety
(`kleinSecAS_ones`).  The **target hyperplane** is `ẑ₄ = 0`, since `Σ_k z_k = −ẑ₄`.

Each identity below is the transport of the corresponding *split* identity of `Work.MotK` along
`x = asM w · y`, `z = asN w · ẑ`, using the transport lemmas of `Work.MotAS.ASTransport`,
`Work.MotAS.ASTransportR` and the reduction algebra `Work.MotAS.ASRed`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Work.MotAS

variable {R : Type*} [CommRing R]

/-! ## The transported link data -/

/-- The polar form of the twisted quadric: `b^AS(u,v) = q^AS(u+v) − q^AS(u) − q^AS(v)`. -/
def kleinBilinAS (a b : R) (u v : Fin 5 → R) : R :=
  kleinQAS a b (u + v) - kleinQAS a b u - kleinQAS a b v

/-- Inverse stereographic projection from `p` on the quadric `q^AS = 0`:
`y(v) = q^AS(v)·p − b^AS(p,v)·v`. -/
def kleinStereoAS (a b : R) (p v : Fin 5 → R) : Fin 5 → R :=
  fun i => kleinQAS a b v * p i - kleinBilinAS a b p v * v i

/-- The source equation of the AS link: `F^AS = b^AS(p,v) · s^AS(y(v))`. -/
def kleinFhomAS (a b g : R) (p v : Fin 5 → R) : R :=
  kleinBilinAS a b p v * kleinSecAS a b g (kleinStereoAS a b p v)

/-- The target equation of the AS link: `G^AS = b^AS(p, R^AS(w)) · s'^AS(w)`. -/
def kleinGhomAS (a b g : R) (p w : Fin 5 → R) : R :=
  kleinBilinAS a b p (kleinRAS a b g w) * kleinSecDualAS a b g w

/-- The all-ones (stereographic) point `e₀ = ![1,1,1,1,1]`; its shifts are the five sections. -/
def onesVec : Fin 5 → R := ![1, 1, 1, 1, 1]

/-! ## The two transport identities of the secant quintics

`asTransportS` (`s(asM w · y) = s^AS(y)`) and `asTransportSD` (`s'(asN w · ẑ) = s'^AS(ẑ)`) are
proved in the sibling modules `Submission.Work.MotAS.asTransportS` and
`Submission.Work.MotAS.asTransportSD`.  They are the two large certificates: a direct
`linear_combination` expands to `O(10⁷)` monomials, so the reduction is staged through the
multiplication `Work.MotAS.redMul` of the algebra `R[w]/(w⁵ − w − g)` (see
`Submission/Work/MotAS/ASRed.lean`). -/

/-! ## The transported split identities -/

/-- **I1^AS**: `R^AS(P^AS(y)) = s^AS(y) · y`. -/
theorem kleinRAS_kleinPAS (a b g w : R) (h5 : (5 : R) = 0) (hw : w ^ 5 = w + g)
    (y : Fin 5 → R) :
    kleinRAS a b g (kleinPAS a b g y) = fun i => kleinSecAS a b g y * y i := by
  apply asM_mulVec_injective h5 w
  rw [← asTransportR a b g w h5 hw (kleinPAS a b g y)]
  change Work.MotK.kleinR a b ((asN w).mulVec (kleinPAS a b g y))
    = (asM w).mulVec (fun i => kleinSecAS a b g y * y i)
  rw [← asTransportP a b g w h5 hw y]
  rw [show Work.MotK.kleinR a b (Work.MotK.kleinP a b (fun i => ∑ j, asM w i j * y j))
      = fun i => Work.MotK.kleinSec a b (fun i => ∑ j, asM w i j * y j)
          * (∑ j, asM w i j * y j) from
    funext fun i => Work.MotK.kleinR_kleinP a b _ i]
  rw [asTransportS a b g w h5 hw y]
  ext i
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **I2^AS**: `P^AS(R^AS(w)) = s'^AS(w) · w`. -/
theorem kleinPAS_kleinRAS (a b g w : R) (h5 : (5 : R) = 0) (hw : w ^ 5 = w + g)
    (z : Fin 5 → R) :
    kleinPAS a b g (kleinRAS a b g z) = fun i => kleinSecDualAS a b g z * z i := by
  apply asN_mulVec_injective h5 w
  rw [← asTransportP a b g w h5 hw (kleinRAS a b g z)]
  change Work.MotK.kleinP a b ((asM w).mulVec (kleinRAS a b g z))
    = (asN w).mulVec (fun i => kleinSecDualAS a b g z * z i)
  rw [← asTransportR a b g w h5 hw z]
  rw [show Work.MotK.kleinP a b (Work.MotK.kleinR a b (fun k => ∑ j, asN w k j * z j))
      = fun i => Work.MotK.kleinSecDual a b (fun k => ∑ j, asN w k j * z j)
          * (∑ j, asN w i j * z j) from
    funext fun i => Work.MotK.kleinP_kleinR a b _ i]
  rw [asTransportSD a b g w h5 hw z]
  ext i
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **I3^AS**: `s'^AS(P^AS(y)) = s^AS(y)²`. -/
theorem kleinSecDualAS_kleinPAS (a b g w : R) (h5 : (5 : R) = 0) (hw : w ^ 5 = w + g)
    (y : Fin 5 → R) :
    kleinSecDualAS a b g (kleinPAS a b g y) = kleinSecAS a b g y ^ 2 := by
  rw [← asTransportSD a b g w h5 hw (kleinPAS a b g y)]
  change Work.MotK.kleinSecDual a b ((asN w).mulVec (kleinPAS a b g y))
    = kleinSecAS a b g y ^ 2
  rw [← asTransportP a b g w h5 hw y,
    Work.MotK.kleinSecDual_kleinP, asTransportS a b g w h5 hw y]

/-- **I4^AS**: `s^AS(R^AS(w)) = s'^AS(w)³` (in the divided form; the unconditional multiplied form
is `Work.MotK.kleinI4_mul`).  The scalar `kleinR`-value of the transported point is the
nonvanishing hypothesis. -/
theorem kleinSecAS_kleinRAS (a b g w : R) [IsDomain R] (h5 : (5 : R) = 0) (hw : w ^ 5 = w + g)
    (z : Fin 5 → R) (hz : Work.MotK.kleinR a b ((asN w).mulVec z) 0 ≠ 0) :
    kleinSecAS a b g (kleinRAS a b g z) = kleinSecDualAS a b g z ^ 3 := by
  rw [← asTransportS a b g w h5 hw (kleinRAS a b g z)]
  change Work.MotK.kleinSec a b ((asM w).mulVec (kleinRAS a b g z))
    = kleinSecDualAS a b g z ^ 3
  rw [← asTransportR a b g w h5 hw z]
  change Work.MotK.kleinSec a b (Work.MotK.kleinR a b ((asN w).mulVec z))
    = kleinSecDualAS a b g z ^ 3
  rw [Work.MotK.kleinSec_kleinR a b _ hz]
  change Work.MotK.kleinSecDual a b (fun i => ∑ j, asN w i j * z j) ^ 3
    = kleinSecDualAS a b g z ^ 3
  rw [← asTransportSD a b g w h5 hw z]

/-- The quadric on the stereographic image: `q^AS(y(v)) = q^AS(v)² · q^AS(p)`. -/
theorem kleinQAS_stereoAS (a b : R) (p v : Fin 5 → R) :
    kleinQAS a b (kleinStereoAS a b p v) = kleinQAS a b v ^ 2 * kleinQAS a b p := by
  simp only [kleinQAS, kleinBilinAS, kleinStereoAS, Pi.add_apply]
  refl_ring1

/-- The polar identity on the stereographic image:
`b^AS(p, y(v)) = 2 q^AS(v) q^AS(p) − b^AS(p,v)²`. -/
theorem kleinBilinAS_stereoAS (a b : R) (p v : Fin 5 → R) :
    kleinBilinAS a b p (kleinStereoAS a b p v)
      = 2 * kleinQAS a b v * kleinQAS a b p - kleinBilinAS a b p v ^ 2 := by
  simp only [kleinQAS, kleinBilinAS, kleinStereoAS, Pi.add_apply]
  refl_ring1

/-! ## The stereographic point

`MOTIVIC_KDATA_LEAD.md` §6.2 asserts that the AS stereographic point is the all-ones vector `e₀`
(because `q(e₀) = 5(a²−ab−b²) = 0` in characteristic `5`).  **This is not right as stated**: the
all-ones vector is the point `x = e₀` of the *split* quadric, and in the AS coordinates
`q^AS(y) = q(asM w · y)` its image is `p = (asM w)⁻¹ e₀`, not `e₀`.  Indeed
`kleinQAS a b e₀ = −2a² + ab + 2b² ≠ 0`.

`stereoPt w` is the correct transported point, written without division through the adjugate
(`asM w · stereoPt w = 288 • e₀`); the scalar `288` is the (constant) determinant of `asM` and is a
unit in characteristic `5`, so it does not change the projective point.  Its entries are
`σ`-invariant (`asM (w+1) = S·asM w` and `S e₀ = e₀`), hence lie in `K = 𝕜(t)`. -/

/-- The transported stereographic point: `p := (asM w)† · e₀`, so that `asM w · p = 288 • e₀`.
It is the AS-coordinate image of the split point `x = e₀`. -/
def stereoPt (w : R) : Fin 5 → R := (asM w).adjugate.mulVec onesVec

/-- `asM w · p = 288 • e₀`. -/
theorem asM_mulVec_stereoPt (w : R) :
    (asM w).mulVec (stereoPt w) = (288 : R) • (onesVec : Fin 5 → R) := by
  unfold stereoPt
  rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, asM_det, Matrix.smul_mulVec,
    Matrix.one_mulVec]

/-- `q^AS(stereoPt) = 0`: the transported point lies on the twisted quadric. -/
theorem kleinQAS_stereoPt (a b g w : R) (h5 : (5 : R) = 0) (hw : w ^ 5 = w + g) :
    kleinQAS a b (stereoPt w) = 0 := by
  rw [← asTransportQ a b g w h5 hw (stereoPt w)]
  change Work.MotK.kleinQ a b ((asM w).mulVec (stereoPt w)) = 0
  rw [asM_mulVec_stereoPt]
  have hhom : Work.MotK.kleinQ a b ((288 : R) • (onesVec : Fin 5 → R))
      = 288 ^ 2 * Work.MotK.kleinQ a b (onesVec : Fin 5 → R) := by
    simp only [Work.MotK.kleinQ, Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2,
      Work.MotK.kleinP3, Work.MotK.kleinP4, Pi.smul_apply, smul_eq_mul]
    refl_ring1
  rw [hhom]
  have hones : Work.MotK.kleinQ a b (onesVec : Fin 5 → R)
      = 5 * (a ^ 2 - a * b - b ^ 2) := by
    simp only [Work.MotK.kleinQ, Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2,
      Work.MotK.kleinP3, Work.MotK.kleinP4, onesVec, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]
    refl_ring1
  rw [hones, show (5 : R) = 0 from h5, zero_mul, mul_zero]

/-- `stereoPt` lies off the twisted curve `C^AS` (the first twisted Pfaffian at `stereoPt` is
`−a² + ab + b²` and the others vanish), so it is off `C^AS` exactly under `a² − ab − b² ≠ 0`. -/
theorem kleinPAS_stereoPt (a b g w : R) (h5 : (5 : R) = 0) (hw : w ^ 5 = w + g) :
    kleinPAS a b g (stereoPt w)
      = fun k => if k = 0 then -(a ^ 2 - a * b - b ^ 2) else 0 := by
  have hsq : (288 : R) ^ 2 = -1 := by
    have h : (288 : R) ^ 2 + 1 = 0 := by
      linear_combination (norm := refl_ring1 (mod := 5))
    linear_combination (norm := refl_ring1) h
  apply asN_mulVec_injective h5 w
  rw [← asTransportP a b g w h5 hw (stereoPt w)]
  change Work.MotK.kleinP a b ((asM w).mulVec (stereoPt w))
    = (asN w).mulVec (fun k => if k = 0 then -(a ^ 2 - a * b - b ^ 2) else 0)
  rw [asM_mulVec_stereoPt]
  change Work.MotK.kleinP a b (fun i => (288 : R) * (onesVec : Fin 5 → R) i)
    = (asN w).mulVec (fun k => if k = 0 then -(a ^ 2 - a * b - b ^ 2) else 0)
  rw [Work.MotK.kleinP_homog]
  have h1 : ∀ k : Fin 5, Work.MotK.kleinP a b (onesVec : Fin 5 → R) k
      = a ^ 2 - a * b - b ^ 2 := by
    intro k
    fin_cases k <;>
      simp only [Work.MotK.kleinP_zero', Work.MotK.kleinP_one',
        Work.MotK.kleinP_two', Work.MotK.kleinP_three', Work.MotK.kleinP_four', Work.MotK.kleinP0,
        Work.MotK.kleinP1, Work.MotK.kleinP2, Work.MotK.kleinP3, Work.MotK.kleinP4, onesVec,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] <;>
      refl_ring1
  ext k
  rw [h1 k, hsq]
  fin_cases k <;>
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five, asN, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.reduceFinMk] <;>
    simp <;>
    refl_ring1

/-- `s^AS(stereoPt) = 2(a² − ab − b²)⁵ ≠ 0` under `ASGood`. -/
theorem kleinSecAS_stereoPt (a b g w : R) (h5 : (5 : R) = 0) (hw : w ^ 5 = w + g) :
    kleinSecAS a b g (stereoPt w) = 2 * (a ^ 2 - a * b - b ^ 2) ^ 5 := by
  have h5th : (288 : R) ^ 5 = -2 := by
    have h : (288 : R) ^ 5 + 2 = 0 := by
      linear_combination (norm := refl_ring1 (mod := 5))
    linear_combination (norm := refl_ring1) h
  rw [← asTransportS a b g w h5 hw (stereoPt w)]
  change Work.MotK.kleinSec a b ((asM w).mulVec (stereoPt w))
    = 2 * (a ^ 2 - a * b - b ^ 2) ^ 5
  rw [asM_mulVec_stereoPt]
  change Work.MotK.kleinSec a b (fun i => (288 : R) * (onesVec : Fin 5 → R) i)
    = 2 * (a ^ 2 - a * b - b ^ 2) ^ 5
  rw [Work.MotK.kleinSec_homog]
  have h1 : Work.MotK.kleinSec a b (onesVec : Fin 5 → R)
      = -(a ^ 2 - a * b - b ^ 2) ^ 5 := by
    simp only [Work.MotK.kleinSec, onesVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    refl_ring1
  rw [h1, h5th]
  refl_ring1

end Work.MotAS
