import Mathlib
import Submission.Work.MotAS.ASZChartSetup
import Submission.Work.MotAS.AK
import Submission.Work.MotAS.asChartPhi_height_le
import Submission.Work.MotAS.asChartKernelLe
import Submission.Work.MotAS.asChartHomogenisation
import Submission.Work.MotAS.kerAevalKleinPAS_gen

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASZChartPresentation` — the chart presentation of the AS twisted Klein curve

The chart `y₀ = 1` of the AS (Artin–Schreier) twisted Klein curve `C_g = V(kleinPAS a b g) ⊂ ℙ⁴`
has function field the AS twist field `twistFieldAS D g = K(y_j/y_0)`, where
`y = asM (asRoot g)⁻¹ κ` are the Lagrange coordinates of the Klein coordinates.

The setup (the chart evaluation `asChartPhi`, the inclusion `asChartIdeal_le_ker` and the
assembly `asChartPresentation_of_ker`, which reduces everything to
`RingHom.ker (asChartPhi D g) ≤ asChartIdeal a b g`) lives in
`Submission/Work/MotAS/ASZChartSetup.lean`; `asChartKernelLe_of_prime` there reduces the kernel
inclusion further to the three geometric inputs

* `(asChartIdeal a b g).IsPrime` — the chart of the AS twisted Klein curve is irreducible,
* `4 ≤ (asChartIdeal a b g).height` — it is one-dimensional,
* `(RingHom.ker (asChartPhi D g)).height ≤ 4` — the kernel is one-dimensional (not maximal),

the third of which is proved in `Submission/Work/MotAS/asChartPhi_height_le.lean` (module
`Submission.Work.MotAS.asChartPhi_height_le`, together with the reusable brick
`Work.MotAS.transcendental_twistFieldAS_gen` for the general AS parameter `g`, which also serves
the first two inputs).

## Status of the two remaining inputs (survey of the routes, for whoever continues)

Let `S = K[X₀,…,X₄]`, `K = RatFunc 𝕜`, `J = span (kleinPAS a b g ∘ X)`,
`asQideal = √J`, `asChartIdeal = asQideal + (X₀-1)`, and `φ = asChartPhi D g` with `g = 2•fAS`.

1. `IsPrime (asChartIdeal a b g)`.  Equivalently (`ReducedChartQuot` from the T-route is already
   proved and applies verbatim: `asQideal` is radical and — `QidealHomogeneous`-style — homogeneous,
   so `S/asChartIdeal` is reduced) the *twisted Klein cone* `V (asQideal) ⊂ 𝔸⁵` is irreducible,
   i.e. `asQideal` is prime on the nose.  Two exact reductions that are worth formalising:
   * **`asQideal` homogeneous prime from the graded argument.**  If `P = asQideal` is a homogeneous
     prime and `X 0 ∉ P`, then `S/(P + (X₀-1)) ≅ (S/P)[X₀⁻¹]₀`, the degree-zero part of the
     localisation of the graded domain `S/P` at the homogeneous element `X 0`; a subring of a
     domain is a domain, whence `IsPrime (asChartIdeal a b g)`.  So the chart input reduces to the
     *cone* input.
   * **`asQideal` prime by base change to `L = K[w]/(w⁵-w-g)`** (a *separable* `K`-algebra, so
     reducedness — hence radicals — commutes with the base change): over `L` the transport identity
     `asTransportP` gives `kleinPAS y = asN w⁻¹ · kleinP (asM w · y)`, i.e.
     `asQideal · L[X] = (Φ⁻¹)^*(Qideal a b 1 · L[X])` for the invertible linear substitution
     `Φ = asM w`; hence `S/asQideal` is a domain whenever `(K[X]/Qideal a b 1) ⊗_K L` is, and the
     latter is the base change of the **split** Klein cone.  A child proving the split statement
     (for `a*b ≠ 0`, `a²-ab-b² ≠ 0`, char 5) unblocks this route; the remaining content there is
     the classical fact that the Klein quintic `V (kleinP a b) ⊂ ℙ⁴`, being the image of the
     elliptic curve `E` under the `|5·O|` embedding (`D.Good.klein_eq`, `D.Good.spans`), is an
     irreducible genus-`1` curve.
2. `4 ≤ (asChartIdeal a b g).height`.  The T-route's `Work.MotK.TGen.ChartHeightBound` is now
   **fully proved** and is the exact template: find explicit elements of the chart ideal that peel
   the variables (`G1v`, `Av` linear/quadratic in successive variables, a resultant `Resv` in the
   last two variables with `Resv ≠ 0`), then run the height chain via
   `Work.MotK.TGen.HeightStepMonic` and `MvPolynomial.finSuccEquiv`.  For each variable `X i`
   (`i = 1,…,4`) a `ℚ(a,b,g)`-linear combination of the five `kleinPAS` which is linear in `X i`
   exists: the coefficient matrix of the four monomials `X i², X i·X j` (`j ≠ i`) has a
   one-dimensional nullspace (checked in this session with sympy, over `ℚ(a,b,g)`), and the
   resulting peeling element has coefficient of `X i` equal to a nonzero rational function of
   `(a,b,g)`.  The cleanest is `i = 1`, where the coefficient is
   `3g(a²-ab-b²)⁴/(ab(a-b)(a+b)(a²+9ab-b²))` — a *nonzero element of the field* `K = RatFunc 𝕜`
   (hence a unit) whenever the listed factors do not vanish; but `ASGood` only gives `ab ≠ 0` and
   `a²-ab-b² ≠ 0`, and values such as `a = b` are admissible and make this particular formula
   degenerate.  So the height proof must either split into the finitely many cases of the
   vanishing of `(a-b)(a+b)(a²+9ab-b²)` (recomputing the peeling element in each case), or use a
   peeling element whose leading coefficient is a *unit of `𝕜`* directly.
-/


set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotAS

open MvPolynomial

/-- **The chart presentation of the AS twisted Klein curve, for an arbitrary AS class `g`.**  This is
the general form of `ASZChartPresentation` (which is the case `g = 2 • fAS 𝕜`); the two inputs
(`kerAevalKleinPAS_gen` — the transported Klein kernel statement, which carries no hypothesis on
`g` — and `asChartHomogenise`) are available for every `g`. -/
theorem ASZChartPresentation_gen (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜) :
    Nonempty (FractionRing (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸
        asChartIdeal (aK D) (bK D) g) ≃ₐ[RatFunc 𝕜]
      ↥(twistFieldAS D g)) := by
  -- Instead of the two geometric inputs (irreducibility + one-dimensionality of the chart), we use
  -- the *kernel inclusion* route: homogenise (node `asChartHomogenise`) and reduce by the
  -- transported Klein kernel statement (node `kerAevalKleinPAS_gen`).  This avoids the height
  -- bound `4 ≤ asChartIdeal.height`, for which no peeling argument is available in the AS chart.
  refine asChartPresentation_of_ker D hD.1 g ?_
  exact asChartKernelLe_of_aux D hD g
    (fun n F hF hF0 => kerAevalKleinPAS_gen 𝕜 D hD g n F hF hF0)
    (asChartHomogenise D hD g)

theorem ASZChartPresentation (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) :
    Nonempty (FractionRing (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸
        asChartIdeal (aK D) (bK D) (2 • Work.MotV.fAS 𝕜)) ≃ₐ[RatFunc 𝕜]
      ↥(twistFieldAS D (2 • Work.MotV.fAS 𝕜))) :=
  ASZChartPresentation_gen 𝕜 D hD (2 • Work.MotV.fAS 𝕜)

end Work.MotAS
