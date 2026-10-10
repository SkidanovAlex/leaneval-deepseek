import Mathlib
import Submission.Work.MotAS.ASLink
import Submission.Work.MotAS.asM_det
import Submission.Work.MotK.TwAmbh
import Submission.Work.MotK.KleinTwLink

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ChartDefs` — the two chart maps of the AS link as polynomials

Part of the subproject `Submission/Work/MotAS` (`Work.MotAS`), node **LK_AS′**
(`MOTIVIC_KDATA_LEAD.md` §6): the definition layer of the affine chart isomorphism
`Φ : R[1/Fdiv] ≃ₐ[K] R[1/Gdiv]` of the Crauder–Katz link in Artin–Schreier Galois coordinates.

This mirrors `Submission/Work/MotK/TGen/ChartDefs.lean` for the split/T-twisted link:

* the source chart map `fwVec a b g = P^AS ∘ y^AS` (the inverse stereographic parametrisation
  followed by the twisted Pfaffians), evaluated at the affine chart `chart3 = ![0,X₀,X₁,X₂,1]`
  and at the `K`-rational stereographic point `stereoPt` (which is the *constant* vector
  `288 • e₁` by `stereoPt_eq` below);
* the target chart map `bwVec a b g = π_p ∘ R^AS` (the inverse quadro-cubic map followed by the
  linear projection from `p` to the hyperplane `{v₀ = 0}`);
* the two link equations `GambAS = b(p,v)·s^AS(y(v))` and `FambAS = b(p,R^AS(w))·s'^AS(w)`
  (dehomogenised at the chart), and the two divisor polynomials
  `FdivAS = GambAS · (fwVec 4)`, `GdivAS = FambAS · (bwVec 4)`.

The value lemmas (`Φ(GambAS) = unit·GdivAS` etc.), the unit conditions making the chart maps
descend to the localisations, and the identification of the two composites are the rest of the
node.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Work.MotAS

open MvPolynomial

variable {K : Type*} [Field K]

/-! ## The stereographic point is constant -/

/-- **WARNING (open issue, found by review).**  This is `stereoPt w = (asM w)† · e₀ = 288 • e₁`,
the *image of the split all-ones point* `x = e₀`.  It is `K`-rational (`stereoPt_eq`) and lies on
the twisted quadric, but it is **not** the chart point used by the affine chart of the link: with
`p = 288 • e₁` the polar form is `b^AS(p, v) = -576 (a²-ab-b²) · v₄`, so at the chart
`v = chart3 = ![0,X₀,X₁,X₂,1]` the polar factor `linAS` collapses to the *constant*
`-576 (a²-ab-b²)` (a unit under `ASGood`), and the source equation of the chart has no linear
factor at all.  The chart point of the AS link is instead the image of the split chart point
`Work.MotK.kleinPointT a b h = (1,0,1,b/(a·h),0)` under `x = asM w · y`, i.e. `(asM w)† · kleinPointT`
(up to the determinant scalar), whose entries are again `σ`-invariant and hence `K`-rational; the
definitions below must be re-pointed at it before the census is meaningful. -/
def stereoPtConst : Fin 5 → K := fun i => if i = 0 then 288 else 0

/-- `stereoPt w = 288 • e₁` for every `w`, in any commutative ring: `e₁` spans the kernel of
`asM w` (its zeroth column is the all-ones vector), so `adj(asM w) · e₁ = det(asM w) • e₁`, and
`det (asM w) = 288`. -/
theorem stereoPt_eq {R : Type*} [CommRing R] (w : R) :
    stereoPt w = fun i => if i = 0 then (288 : R) else 0 := by
  have hcol : (asM w).mulVec (Pi.single (0 : Fin 5) (1 : R)) = onesVec (R := R) := by
    ext k
    fin_cases k <;>
      simp [asM, onesVec, Matrix.mulVec, dotProduct, Fin.sum_univ_five, Pi.single, Function.update]
  have hclosed : (asM w).adjugate.mulVec (onesVec (R := R))
      = (288 : R) • (Pi.single (0 : Fin 5) (1 : R)) := by
    rw [← hcol, Matrix.mulVec_mulVec, Matrix.adjugate_mul, asM_det, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  ext i
  rw [stereoPt, hclosed, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i = 0
  · subst hi; simp
  · simp [hi]

/-- The `K`-rational stereographic point of the AS chart, as a constant vector in the polynomial
ring: `p = 288 • e₁`. -/
noncomputable def pAS (K : Type*) [CommRing K] : Fin 5 → MvPolynomial (Fin 3) K :=
  fun i => C (if i = 0 then (288 : K) else 0)

@[simp] theorem pAS_apply (i : Fin 5) : pAS K i = C (if i = 0 then (288 : K) else 0) := rfl

/-! ## The two chart maps and the two link equations -/

/-- **The forward link map on the affine AS chart**: `P^AS ∘ y^AS` at the chart vector
`chart3 = ![0,X₀,X₁,X₂,1]` and the stereographic point `pAS`. -/
noncomputable def fwVecAS (a b g : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  kleinPAS (C a) (C b) (C g)
    (kleinStereoAS (C a) (C b) (pAS K) (Work.MotK.chart3 K))

/-- **The inverse link map on the affine AS chart**: `π_p ∘ R^AS` at the chart vector. -/
noncomputable def bwVecAS (a b g : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  Work.MotK.kleinTwPi (pAS K) (kleinRAS (C a) (C b) (C g) (Work.MotK.chart3 K))

/-- **The source divisor of the affine AS link**: `b(p,v)·s^AS(y(v))` dehomogenised at the chart. -/
noncomputable def GambAS (a b g : K) : MvPolynomial (Fin 3) K :=
  kleinFhomAS (C a) (C b) (C g) (pAS K) (Work.MotK.chart3 K)

/-- **The target divisor of the affine AS link**: `b(p,R^AS(w))·s'^AS(w)` dehomogenised. -/
noncomputable def FambAS (a b g : K) : MvPolynomial (Fin 3) K :=
  kleinGhomAS (C a) (C b) (C g) (pAS K) (Work.MotK.chart3 K)

/-! ## The four prime factors of the two divisors

The two link equations factor by definition into a *polar* (linear in the chart coordinates) piece
and a *secant-quintic* piece:

* `GambAS = linAS · sAS` with `linAS = b^AS(p, chart)` and
  `sAS = s^AS(y^AS(chart))` (the source ruling quintic),
* `FambAS = cubAS · sdualAS` with `cubAS = b^AS(p, R^AS(chart))` and
  `sdualAS = s'^AS(chart)` (the target dual ruling quintic).

(The names follow `Work.MotK.TGen`: `linT`/`cubT` are the junk polar factors, `sT` the degree-10
source ruling and `sdualT` the target ruling quintic.) -/

/-- The polar factor `b^AS(p, chart)` of the source equation. -/
noncomputable def linAS (a b : K) : MvPolynomial (Fin 3) K :=
  kleinBilinAS (C a) (C b) (pAS K) (Work.MotK.chart3 K)

/-- The source ruling quintic `s^AS(y^AS(chart))`. -/
noncomputable def sAS (a b g : K) : MvPolynomial (Fin 3) K :=
  kleinSecAS (C a) (C b) (C g) (kleinStereoAS (C a) (C b) (pAS K) (Work.MotK.chart3 K))

/-- The polar factor `b^AS(p, R^AS(chart))` of the target equation. -/
noncomputable def cubAS (a b g : K) : MvPolynomial (Fin 3) K :=
  kleinBilinAS (C a) (C b) (pAS K) (kleinRAS (C a) (C b) (C g) (Work.MotK.chart3 K))

/-- The target dual ruling quintic `s'^AS(chart)`. -/
noncomputable def sdualAS (a b g : K) : MvPolynomial (Fin 3) K :=
  kleinSecDualAS (C a) (C b) (C g) (Work.MotK.chart3 K)

/-- The source equation is the product of the polar factor and the source ruling quintic. -/
theorem GambAS_eq (a b g : K) : GambAS a b g = linAS a b * sAS a b g := rfl

/-- The target equation is the product of the polar factor and the target ruling quintic. -/
theorem FambAS_eq (a b g : K) : FambAS a b g = cubAS a b g * sdualAS a b g := rfl

/-- The **source-side** divisor of the certificate: the source equation times the denominator
`fwVecAS 4` of the forward chart map, in the factored form `linAS · sAS · fwVecAS 4` (equal to
`GambAS · fwVecAS 4` by `GambAS_eq`), so that its height-one primes decompose directly. -/
noncomputable def FdivAS (a b g : K) : MvPolynomial (Fin 3) K :=
  linAS a b * sAS a b g * fwVecAS a b g 4

/-- The **target-side** divisor of the certificate: the target equation times the denominator
`bwVecAS 4` of the inverse chart map, in the factored form `cubAS · sdualAS · bwVecAS 4`. -/
noncomputable def GdivAS (a b g : K) : MvPolynomial (Fin 3) K :=
  cubAS a b g * sdualAS a b g * bwVecAS a b g 4

end Work.MotAS
