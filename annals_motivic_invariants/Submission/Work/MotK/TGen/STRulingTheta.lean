import Mathlib
import Submission.Work.MotK.TGen.STRulingAux
import Submission.Work.MotK.TGen.CensusFactors
import Submission.Work.MotK.TwCensus.Defs
import Submission.Work.MotK.TGen.KleinTwFibre_eq_ker

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.STRulingTheta` — the ruling presentation `θ` of the source divisor `sT`

For the residual curve `Z = V(Zcub a b h) ⊆ 𝔸³` (the curve of positive-dimensional fibres of the
twisted quadro map `kleinTwP`), put

* `ZRing a b h = K[x₀,x₁,x₂] ⧸ Ideal.radical (ZI a b h)`, the coordinate ring of `Z`;
* `thPoly a b h : K[x₀,x₁,x₂] →ₐ[K] K[x₀,x₁,x₂][T]`, the *ruling parametrisation*, sending
  `x_j ↦ C (RVS (ch3' j)) · T + C (RWS (ch3' j))` — i.e. the chart coordinate of the ruling line
  over the base point `c'` (with `RVS`, `RWS` the ruling vectors projected through the
  stereographic point `kleinPointT`, `Submission/Work/MotK/TGen/STRulingAux.lean`);
* `theta a b h : K[x₀,x₁,x₂] →ₐ[K] ZRing a b h [T]`, the reduction of `thPoly` modulo `radical (ZI)`.

The three facts about `theta` that the divisor statement `Work.MotK.TGen.STRulingDiv` uses are
recorded here: the ruling equation `kleinTwS (T·rv + rw) = 0` of the base curve, the recovery of
the ruling parameter `T` from `kleinTwS ∘ kleinTwStereo ∘ chart3`, and the recovery of the base
point coordinates from `f̂₄ = fwVec a b h 4`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-- The coordinate ring of the residual curve `Z = V(Ideal.radical (ZI a b h))`. -/
abbrev ZRing (a b h : K) : Type :=
  MvPolynomial (Fin 3) K ⧸ Ideal.radical (Work.MotK.TwCensus.ZI a b h)

/-- The `i`-th coordinate of the stereographic point `kleinTwStereo pRa chart3`, i.e. the `i`-th
component of the forward chart map `f̂` before the quadro map: `S_i = y_i` with `y = f̂/ kleinTwP`.
This is the polynomial whose image under `theta` is the `i`-th coordinate of the point `y` of the
ruling line (in particular `S_3/S_4` is the ruling parameter). -/
noncomputable def Sklein (a b h : K) (i : Fin 5) : MvPolynomial (Fin 3) K :=
  Work.MotK.kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (pRa a b h) (chart3 K) i

/-- **The ruling parametrisation**, as an algebra map into the polynomial ring `K[x₀,x₁,x₂][T]`:
`x_j ↦ C (RVS (ch3' j))·T + C (RWS (ch3' j))`.

This is the pullback of the ruling of `{sT = 0}` over the base curve `Z`: a point of the surface is
determined by the base point `c' = (0,x₀,x₁,x₂,1)` and the ruling parameter `T`, and its `j`-th
chart coordinate is `T·RVS (j+1)(c') + RWS (j+1)(c')` (`AmatP_ker_iff`,
`Submission/Work/MotK/TGen/STRulingAux.lean`). -/
noncomputable def thPoly (a b h : K) :
    MvPolynomial (Fin 3) K →ₐ[K] Polynomial (MvPolynomial (Fin 3) K) :=
  MvPolynomial.aeval (fun j : Fin 3 => Polynomial.C (RVS a b h (ch3' (K := K) j)) * Polynomial.X
    + Polynomial.C (RWS a b h (ch3' (K := K) j)))

/-- **The ruling presentation of the source divisor**, `theta a b h : K[x₀,x₁,x₂] →ₐ[K] R[T]`
with `R = ZRing a b h`. -/
noncomputable def theta (a b h : K) : MvPolynomial (Fin 3) K →ₐ[K] Polynomial (ZRing a b h) :=
  (Polynomial.mapAlgHom (Ideal.Quotient.mkₐ K
      (Ideal.radical (Work.MotK.TwCensus.ZI a b h)))).comp (thPoly a b h)

/-- The `j`-th chart coordinate of a ruled point is linear in the ruling parameter. -/
theorem theta_X (a b h : K) (j : Fin 3) :
    theta a b h (MvPolynomial.X j)
      = Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotK.TwCensus.ZI a b h))
            (RVS a b h (ch3' (K := K) j))) * Polynomial.X
        + Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotK.TwCensus.ZI a b h))
            (RWS a b h (ch3' (K := K) j))) := by
  simp [theta, thPoly, MvPolynomial.aeval_X]

end Work.MotK.TGen
