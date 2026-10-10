import Mathlib
import Submission.Work.MotK.TGen.ThetaSTDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.ThPolyST` — the ruling parametrisation of the source divisor `sT`

`thPoly a b h : K[x₀,x₁,x₂] →ₐ[K] K[x₀,x₁,x₂][T]` is the *ruling parametrisation* of the source
divisor `{sT = 0}` of the T-twisted Crauder--Katz link, sending the `j`-th chart coordinate to
`T·RVS (j+1) + RWS (j+1)` (see `Submission/Work/MotK/TGen/STRulingTheta.lean`).  The point of the
present file is the single identity

  `thPoly a b h (sT a b h) = (-(BmL a b h)) ^ 5 * SmL a b h`,

which describes `thPoly` of the *source divisor* `sT = kleinTwS (kleinTwStereo p chart3)` in terms
of the ruling line `Z(T) = T·rv + rw` of the base point `chart3`:

* `SmL a b h = kleinTwS (Z(T))` is the (degree five in the coordinates) secant quintic evaluated on
  the ruling line, and
* `BmL a b h = b(p, Z(T))` is the polar form of the ruling line with respect to the projection
  centre `p = kleinPointT a b h`.

Mathematically: `thPoly` acts on the *stereographic* point `y = kleinTwStereo p chart3` by sending
`chart3` to the ruling point `V(T) = π_p(Z(T))` and fixing the point `p`; hence by naturality
`thPoly (sT) = kleinTwS (kleinTwStereo p V(T))`.  Since `V(T) = π_p Z(T)` and both `p` and `Z(T)`
lie on the quadric `{q = 0}`, the inverse-stereographic identity `KleinTwStereo_pi` gives
`kleinTwStereo p V(T) = q(Z(T))·p - b(p,Z(T))·Z(T) = -(BmL)·Z(T)` (the first hypothesis `hQ` is
exactly `q(Z(T)) = 0`, while `q(p) = 0` is hypothesis-free), and the quintic `kleinTwS` is
homogeneous of degree `5` in the coordinates, which yields the stated right-hand side.

The identity is the source-side input of the ruling presentation `theta` of `{sT = 0}`: it exhibits
`thPoly (sT)` as the fifth power of the polar form `BmL` times a polynomial in the ruling parameter
whose class is the equation of the base curve.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-! ## 1. `thPoly` on constants -/

/-- `thPoly` is a `K`-algebra homomorphism, so it fixes the constants `K → K[x₀,x₁,x₂]`. -/
lemma thPolyST_C (a b h : K) (c : K) :
    thPoly a b h (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by
  rw [MvPolynomial.C_eq_algebraMap, AlgHom.commutes]
  exact (IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 3) K)
    (Polynomial (MvPolynomial (Fin 3) K)) c).symm

/-! ## 2. `thPoly` on the two vectors defining `sT` -/

/-- The projection centre `pRa a b h = kleinPointT a b h` is a constant vector, so `thPoly` sends it
to `PvL a b h` (its image in the polynomial ring `K[x₀,x₁,x₂][T]`). -/
lemma thPolyST_pRa (a b h : K) :
    (fun i => thPoly a b h (Work.MotK.pRa a b h i)) = PvL a b h := by
  funext i
  simp only [Work.MotK.pRa, PvL]
  exact thPolyST_C a b h (Work.MotK.kleinPointT a b h i)

/-- The affine chart `chart3 = (0, x₀, x₁, x₂, 1)` is sent by `thPoly` to the ruling chart point
`VvL a b h = T·RVS + RWS`. -/
lemma thPolyST_chart3 (a b h : K) :
    (fun i => thPoly a b h (Work.MotK.chart3 K i)) = VvL a b h := by
  funext i
  fin_cases i <;>
    simp [VvL, Work.MotK.chart3, RVS, RWS, Work.MotK.TwCensus.rv, Work.MotK.TwCensus.rw,
      Work.MotK.kleinPointT, ch3', thPoly]

/-! ## 3. Naturality of `t ↦ s(y(t))` under `thPoly` -/

/-- **Naturality of the inverse stereographic projection under `thPoly`.**  Since `thPoly` is a
`K`-algebra homomorphism and `kleinTwStereo` is a polynomial expression in its arguments, it
commutes with it: the `thPoly`-image of the stereographic point `y = kleinTwStereo p chart3` used in
`sT` is the stereographic point of the ruling chart point at the same centre. -/
lemma thPolyST_stereo (a b h : K) :
    (fun i => thPoly a b h (Work.MotK.kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b)
      (MvPolynomial.C h) (Work.MotK.pRa a b h) (Work.MotK.chart3 K) i))
      = Work.MotK.kleinTwStereo (Polynomial.C (MvPolynomial.C a))
          (Polynomial.C (MvPolynomial.C b)) (Polynomial.C (MvPolynomial.C h))
          (PvL a b h) (VvL a b h) := by
  have hnat := map_kleinTwStereo' (R := MvPolynomial (Fin 3) K)
    (S := Polynomial (MvPolynomial (Fin 3) K)) (thPoly a b h).toRingHom
    (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (Work.MotK.pRa a b h)
    (Work.MotK.chart3 K)
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hnat
  rw [thPolyST_pRa, thPolyST_chart3, thPolyST_C, thPolyST_C, thPolyST_C] at hnat
  exact hnat

/-- **The substitution of `theta` on the source divisor `sT`.**  The image of
`sT = kleinTwS (kleinTwStereo p chart3)` is the secant quintic of the stereographic point of the
ruling chart point. -/
lemma thPolyST_sT (a b h : K) :
    thPoly a b h (sT a b h)
      = Work.MotK.kleinTwS (Polynomial.C (MvPolynomial.C a)) (Polynomial.C (MvPolynomial.C b))
          (Polynomial.C (MvPolynomial.C h))
          (Work.MotK.kleinTwStereo (Polynomial.C (MvPolynomial.C a))
            (Polynomial.C (MvPolynomial.C b)) (Polynomial.C (MvPolynomial.C h))
            (PvL a b h) (VvL a b h)) := by
  have hnat := map_kleinTwS' (R := MvPolynomial (Fin 3) K)
    (S := Polynomial (MvPolynomial (Fin 3) K)) (thPoly a b h).toRingHom
    (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (Work.MotK.kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (Work.MotK.pRa a b h) (Work.MotK.chart3 K))
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hnat
  rw [thPolyST_stereo, thPolyST_C, thPolyST_C, thPolyST_C] at hnat
  simpa only [sT] using hnat

/-! ## 4. The ruling chart point is the projection of the ruling line, and both lie on the quadric -/

/-- The ruling chart point `VvL a b h = T·RVS + RWS` is the projection `π_p` of the ruling line
`ZvL a b h = T·rv + rw` from the centre `PvL a b h`. -/
lemma thPolyST_VvL_eq_pi (a b h : K) :
    VvL a b h = Work.MotK.kleinTwPi (PvL a b h) (ZvL a b h) := by
  funext i
  fin_cases i <;>
    simp [VvL, PvL, ZvL, Work.MotK.kleinTwPi, RVS, RWS, Work.MotK.kleinPointT,
      Work.MotK.TwCensus.rv, Work.MotK.TwCensus.rw] <;>
    first | refl_ring1 | ring

/-- The projection centre `PvL a b h` lies on the twisted quadric, after base change to
`K[x₀,x₁,x₂][T]`.  (This is `kleinTwQ_pRa` transported along `Polynomial.C`; hypotheses-free apart
from `a h ≠ 0`, which is the condition for `kleinPointT` to have its last-but-one coordinate
defined.) -/
lemma thPolyST_kleinTwQ_PvL (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) :
    Work.MotK.kleinTwQ (Polynomial.C (MvPolynomial.C a)) (Polynomial.C (MvPolynomial.C b))
      (Polynomial.C (MvPolynomial.C h)) (PvL a b h) = 0 := by
  have hnat := map_kleinTwQ' (Polynomial.C) (MvPolynomial.C a) (MvPolynomial.C b)
    (MvPolynomial.C h) (Work.MotK.pRa a b h)
  rw [Work.MotK.kleinTwQ_pRa a b h ha hh, map_zero] at hnat
  exact hnat.symm

/-! ## 5. The target identity -/

theorem ThPolyST (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (hQ : Work.MotK.kleinTwQ (Polynomial.C (MvPolynomial.C a)) (Polynomial.C (MvPolynomial.C b))
      (Polynomial.C (MvPolynomial.C h)) (ZvL a b h) = 0) :
    Work.MotK.TGen.thPoly a b h (Work.MotK.TGen.sT a b h)
      = (-(BmL a b h)) ^ 5 * SmL a b h := by
  -- `thPoly` sends `sT` to the secant quintic of the stereographic point of the ruling line
  rw [thPolyST_sT]
  -- the ruling chart point is the projection of the ruling line from the centre `PvL`
  rw [thPolyST_VvL_eq_pi]
  -- the inverse-stereographic identity, with the projection centre on the quadric
  have hp : Work.MotK.kleinTwQ (Polynomial.C (MvPolynomial.C a))
      (Polynomial.C (MvPolynomial.C b)) (Polynomial.C (MvPolynomial.C h)) (PvL a b h) = 0 :=
    thPolyST_kleinTwQ_PvL a b h ha hh
  rw [Work.MotK.KleinTwStereo_pi (Polynomial.C (MvPolynomial.C a))
    (Polynomial.C (MvPolynomial.C b)) (Polynomial.C (MvPolynomial.C h)) (PvL a b h)
    (ZvL a b h) hp]
  -- the ruling line lies on the quadric (`hQ`), leaving the polar form
  simp only [hQ, zero_mul, zero_sub]
  have hshape : (fun i => -(Work.MotK.kleinTwBilin (Polynomial.C (MvPolynomial.C a))
        (Polynomial.C (MvPolynomial.C b)) (Polynomial.C (MvPolynomial.C h)) (PvL a b h)
        (ZvL a b h) * ZvL a b h i))
      = fun i => (-(Work.MotK.kleinTwBilin (Polynomial.C (MvPolynomial.C a))
        (Polynomial.C (MvPolynomial.C b)) (Polynomial.C (MvPolynomial.C h)) (PvL a b h)
        (ZvL a b h))) * ZvL a b h i := by
    funext i
    first | refl_ring1 | ring
  rw [hshape]
  -- homogeneity of the secant quintic
  rw [Work.MotK.kleinTwS_homog]
  rfl

end Work.MotK.TGen
