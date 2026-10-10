import Mathlib
import Submission.Work.MotK.TGen.STRulingTheta
import Submission.Work.MotK.KleinTwI1
import Submission.Work.MotK.KleinTwQ_stereo
import Submission.Work.MotK.KleinTwLink
import Submission.Work.MotK.TwDataMod5
import Submission.Work.MotK.KleinTwData.map_data

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.ThetaSTDefs` — the local vocabulary of the proof of `theta (sT) = 0`

The ruling presentation `theta a b h : K[x₀,x₁,x₂] →ₐ[K] R[T]` (`R = ZRing a b h`) of the source
ruling divisor `sT` substitutes `x_j ↦ T·RVS (j+1) + RWS (j+1)`, where `RVS`, `RWS` are the ruling
vectors `rv`, `rw` projected from the base point `c' = chartPt` through the point
`p = kleinPointT a b h`.

The proof of `theta (sT a b h) = 0` goes through the *unprojected* ruling line
`Z(T) = T·rv + rw` of the fibre of the quadro map `kleinTwP` over the chart point `c'` (the
"source ruling"), so this file collects the three vectors of polynomials in
`R' := K[x₀,x₁,x₂][T] = Polynomial (MvPolynomial (Fin 3) K)`:

* `ZvL a b h` — the ruling line `T·rv + rw` of the fibre of `kleinTwP` over `chartPt`
  (the base point of the ruling of `{sT = 0}`);
* `PvL a b h` — the projection centre `p = kleinPointT a b h` as a constant vector;
* `VvL a b h` — the ruling chart point `π_p (Z(T)) = T·RVS + RWS`, i.e. the image of `chart3`
  under `theta`'s substitution (`VvL = thPoly ∘ chart3`, `VvL = kleinTwPi PvL ZvL`);
* `WL a b h` — the kernel defect `T·Pt1 + Pt2` of the ruling matrix, i.e. the only non-vanishing
  component of `AmatP a b h chartPt ·ᵥ Z(T) = h·(T·Pt1 + Pt2)·e₀`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-- The ruling line `Z(T) = T·rv + rw` of the fibre of the twisted quadro map `kleinTwP` over the
chart point `chartPt a b h = (0, x₀, x₁, x₂, 1)`.  This is the *unprojected* ruling point; the
chart point of the ruling of `{sT = 0}` is `VvL = π_p (ZvL)`. -/
noncomputable def ZvL (a b h : K) : Fin 5 → Polynomial (MvPolynomial (Fin 3) K) :=
  fun i => Polynomial.C (Work.MotK.TwCensus.rv a b h i) * Polynomial.X
    + Polynomial.C (Work.MotK.TwCensus.rw a b h i)

/-- The projection centre `p = kleinPointT a b h = (1, 0, 1, b/(a h), 0)` as a constant vector. -/
noncomputable def PvL (a b h : K) : Fin 5 → Polynomial (MvPolynomial (Fin 3) K) :=
  fun i => Polynomial.C (MvPolynomial.C (Work.MotK.kleinPointT a b h i))

/-- The ruling chart point `π_p (Z(T)) = T·RVS + RWS`: the point of the ruling of `{sT = 0}` whose
base point is `chartPt` and whose ruling parameter is `T`.  It is the image of `chart3` under
`theta`'s substitution. -/
noncomputable def VvL (a b h : K) : Fin 5 → Polynomial (MvPolynomial (Fin 3) K) :=
  fun i => Polynomial.C (RVS a b h i) * Polynomial.X + Polynomial.C (RWS a b h i)

/-- The kernel defect `T·Pt1 + Pt2`: the only non-vanishing component of
`AmatP a b h chartPt ·ᵥ ZvL = h·(T·Pt1 + Pt2)·e₀`. -/
noncomputable def WL (a b h : K) : Polynomial (MvPolynomial (Fin 3) K) :=
  Polynomial.X * Polynomial.C (Work.MotK.TwCensus.Pt1 a b h)
    + Polynomial.C (Work.MotK.TwCensus.Pt2 a b h)

/-- The kernel defect `T·Zcub 4 − Zcub 3` of the ruling matrix, in terms of the generators of the
residual-curve ideal `ZI`; it is `C (a b²) · WL`. -/
noncomputable def WZL (a b h : K) : Polynomial (MvPolynomial (Fin 3) K) :=
  Polynomial.X * Polynomial.C (Work.MotK.TwCensus.Zcub a b h 4)
    - Polynomial.C (Work.MotK.TwCensus.Zcub a b h 3)

/-- The twisted quadro map at the ruling line `ZvL`, over the coefficient ring `K[x₀,x₁,x₂][T]`. -/
noncomputable def PmL (a b h : K) : Fin 5 → Polynomial (MvPolynomial (Fin 3) K) :=
  Work.MotK.kleinTwP (Polynomial.C (MvPolynomial.C a)) (Polynomial.C (MvPolynomial.C b))
    (Polynomial.C (MvPolynomial.C h)) (ZvL a b h)

/-- The twisted secant quintic at the ruling line `ZvL`. -/
noncomputable def SmL (a b h : K) : Polynomial (MvPolynomial (Fin 3) K) :=
  Work.MotK.kleinTwS (Polynomial.C (MvPolynomial.C a)) (Polynomial.C (MvPolynomial.C b))
    (Polynomial.C (MvPolynomial.C h)) (ZvL a b h)

/-- The polar form `b(p, Z(T))` of the ruling line with the projection centre. -/
noncomputable def BmL (a b h : K) : Polynomial (MvPolynomial (Fin 3) K) :=
  Work.MotK.kleinTwBilin (Polynomial.C (MvPolynomial.C a)) (Polynomial.C (MvPolynomial.C b))
    (Polynomial.C (MvPolynomial.C h)) (PvL a b h) (ZvL a b h)

end Work.MotK.TGen
