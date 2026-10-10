import Mathlib
import Submission.Work.MotK.TGen.CensusFactors

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The residual curve of the T-twisted link, in the affine chart

This file collects the definitions that the census clause `Work.MotK.TwCensus.STClassNondeg` (the
class of the source ruling divisor `sT`) needs beyond the existing `Work.MotK`/`Work.MotV`
vocabulary; it is sorry-free so that the lemmas about them can be proved in parallel.

* `Zcub a b h k` (`k : Fin 5`): the five cubics of the inverse map `kleinTwR` of the T-twisted link,
  `kleinTwR a b h` evaluated at the affine chart vector `chart3 = (0, x₀, x₁, x₂, 1)`.
* `ZI a b h`: the ideal they generate in `K[x₀,x₁,x₂]`.

Their common zero locus

  `Z = V(Zcub a b h) ⊆ 𝔸³ = {z₀ = 0, z₄ = 1} ⊂ ℙ⁴`

is the chart part of the **residual curve** `C' = V(kleinTwR) ∩ H` of the T-twisted Crauder--Katz
link (`H = {z₀ = 0}` is the T-invariant hyperplane, `V(kleinTwR)` the base locus of the inverse
map).  By the Crauder--Katz description of the quadro-cubic transformation, `C'` is a section of
the ruling of the secant surface, hence `C' ≅ Pic²(C_h) ≅ Jac²(C_h)`, and its twist class is `2T`:
its function field is `twistFieldTG K D (h²)`.  This is node **K6** of the area's design notes
(`GUIDE_CENSUS.md`, `GUIDE_K5K6.md`, `MOTIVIC_S45_LEAD.md` §2.3).

Numerical check (over `𝔽₁₃`, `(a,b,h) = (2,3,5)`): `Z` has `19` points in the chart (`20` in `ℙ³`),
the point count of a genus-one curve; `V(kleinTwR)` itself has many more points (the area's guides
record `140` for the split data), i.e. `Z` is a proper section of `V(kleinTwR)` and is *not* the
source Klein curve.

The linear-algebra form of the ruling (node K5) is available elsewhere in the workspace: the
fibres of the twisted quadro map are the kernels of the twisted Klein matrix
`Work.MotK.TwCensus.kleinTwM` (`Submission/Work/MotK/TwCensus/STClass.lean`), which is the exact
twisted transport of the split lemma, and is established in
`Submission/Work/MotK/TGen/KleinTwFibre_eq_ker.lean`.

## Findings of this stretch (machine-checked, for the two proofs that consume this file)

**`Z` is the right base curve.**  The base curve of the ruling of `{sT = 0}` is the
*positive-dimensional fibre locus* of the twisted quadro map `kleinTwP a b h`, i.e. the set of
`c' ∈ ℙ⁴` where the ruling matrix `Amat a b h c'` (the linear-in-`y` form of `kleinTwM`, in
`Submission/Work/MotK/TwCensus/STClass.lean`) has rank `≤ 3`.  Exhaustive computation over the
`13³` chart points for `(a,b,h) = (2,3,5)`, `p = 13`: this locus has exactly `19` points and is
*equal as a set* to the zero locus of `Zcub a b h` in the chart.  (Note the chart is
`{z₀ = 0, z₄ = 1}`; the locus is cut out by the five `4×4` minors of `Amat`, which for the *split*
matrix factor as
`det ((kleinMlin a b c').submatrix j.succAbove j.succAbove) = ± c'_j · kleinR a b (shift² c')_{j+1}`;
for the twisted `Amat` the analogous minors are the same cubics with the `h`-weights of `twW` on
their monomials, so the locus is *not* simply a shift of `V(kleinTwR)` — the chart identification
above was verified directly, and is the form a proof needs.)

**The ruling lines.**  For `c'` in that locus the kernel of `Amat a b h c'` is a plane in `K⁵`
(a line in `ℙ⁴`), and it is spanned by explicit `4×4` minors of `Amat` (polynomial in `c'`, linear
in nothing).  In the *source* chart `chart3` a point of the ruling line has coordinates obtained
by evaluating a linear function of the ruling parameter against those minors; `{sT = 0}` is ruled
by these lines over `Z`, and this is what gives `Frac (K[x]/(sT)) ≅ RatFunc (κ(Z))`
(`Work.MotK.TwCensus.STRuling`).  The identity to prove is `sT ∈ ker θ` for that presentation,
i.e. an identity modulo the ideal of `Z`.

**K6.**  For `c' ∈ Z` the ruling line meets the twisted Klein curve `C_h ⊆ Q̃` in two points
`c₁, c₂` (the zeros of the proportionality factor), and `c' ↦ c₁ + c₂ ∈ Pic²(C_h)` identifies
`Z ≅ Pic²(C_h) ≅ Jac²(C_h)`; the T'-action is translation by `2T`, and the resulting `E`-torsor
class `2 c_h` is the twist class of `h²`, i.e. `κ(Z) ≅ twistFieldTG K D (h²)`
(`Work.MotK.TwCensus.ZTwist`).  In the degenerate case `h² ∈ (Kˣ)⁵` the twist is trivial and one
uses `Work.MotK.TwCensus.KummerInvariance` (proved, sorry-free) to replace the `h²`-field by
`twistFieldTG K D 1`; the two coordinate systems then differ by the `K̄`-linear automorphism
`y_i ↦ u^i y_i` (`u⁵ = 1`) supplied by `KleinData.Good.T_diag`, so the fields are `K`-isomorphic
but not equal as subfields of `OmG K D`.

**K6 is a *monomial* isomorphism (machine-checked, and the key to proving it).**  Let
`C_{h²} = V(kleinTwP a b (h²)) ⊆ ℙ⁴` (coordinates `y`) and `Z = V(Zcub) ∩ chart ⊆ ℙ³`, both
degree-`5` genus-`1` curves.  For every tested `(a,b,h)` (over `𝔽₁₃`, `(a,b,h)` running over
`(2,3,5)`, `(3,2,5)`, `(2,3,7)`, `(1,2,3)`, `(2,5,3)`, `(5,2,3)`, `(2,1,3)`, `(3,5,2)`,
`(3,4,5)`) there is a *monomial* linear map

  `z_j = λ_j · y_{σ(j)}`  (`σ(j) = 2j` or `3j` mod `5`, or the identity for some parameters),

with scalars `λ_j ∈ 𝔽₁₃ˣ` (e.g. `(a,b,h) = (2,3,5)`, `σ(j) = 2j`, `(λ_1,λ_2,λ_3,λ_4) = (1,1,5,8)`;
`(3,2,5)` gives `(1,12,8,8)`, `(2,3,7)` gives `(1,4,5,6)`, `(2,1,3)` gives `(1,7,2,10)`, …) whose
image is *exactly* `Z`: on the `20` (resp. `10`/`15`) points of `C_{h²}(𝔽₁₃)` the test
"image ⊆ Z" is satisfied for every point, and the solutions form a coset under the (small) group
of curve automorphisms.

**Consequence for the proof of K6.**  One does *not* need the group law: it suffices to exhibit
scalars `λ_1,…,λ_4 ∈ K` (nonzero, `K`-rational!) such that the monomial substitution makes the
two curve ideals correspond, e.g. as the pair of polynomial-identity statements

* `R_k (0, λ_4 y_4, λ_3 y_3, λ_2 y_2, λ_1 y_1) ∈ (kleinTwP a b (h²))` for `k = 0,…,4`
  (the monomial image of `C_{h²}` lies on `Z`), and
* the converse for the inverse monomial substitution (the image is all of `Z`, using that the
  image is a degree-`5` genus-`1 curve and the two agree on `ℙ³`).

Both are finite polynomial computations (a `linear_combination`/`ring` certificate against the
five quadrics).  A `K`-rational monomial map then gives the field isomorphism
`κ(Z) ≅ κ(C_{h²})` for free (a monomial substitution is a linear change of coordinates), which is
what `Work.MotK.TwCensus.ZTwist` asserts.  The remaining work is thus: *find* the `λ_i` as
rational functions of `(a,b,h)` (they are *not* determined canonically — the source coordinates
`twCoordG K D (h²)_i` are canonical only up to `ζ^i`, `ζ⁵ = 1`, and isomorphisms are unique only up
to curve automorphisms — so `λ` is only well defined in `(K̄ˣ)⁴ / (μ₅ · Kˣ)`; any representative
with `λ_i ∈ K` suffices).

**Non-vanishing.**  `Work.MotK.TwCensus.sT_ne_zero` (sorry-free, in
`Submission/Work/MotK/TwCensus/STClass.lean`) shows `sT a b h ≠ 0` for `a b h ≠ 0`, which is what
makes the height-one bookkeeping (`Work.MotK.HeightSpanSingletonPrime`) applicable:
`sT a b h` evaluated at `(0,0,1)` equals `a^15 b^5 h^8 (h+1)` (machine-checked).
-/

namespace Work.MotK.TwCensus

open MvPolynomial

variable {K : Type*}

/-- The five cubics of the inverse map `kleinTwR` of the T-twisted link, in the affine chart
`chart3 = (0, x₀, x₁, x₂, 1)`: the equations of the residual curve `C'`. -/
noncomputable def Zcub [Field K] (a b h : K) (k : Fin 5) : MvPolynomial (Fin 3) K :=
  Work.MotK.kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (Work.MotK.chart3 K) k

/-- The ideal of the chart part of the residual curve `C'` of the T-twisted link. -/
noncomputable def ZI [Field K] (a b h : K) : Ideal (MvPolynomial (Fin 3) K) :=
  Ideal.span (Set.range (Zcub a b h))

/-- The (radical) ideal of the **twisted Klein curve of class `h`**: the five twisted quadrics
`kleinTwP a b h` read in the coordinate ring `K[y₀,…,y₄]` of `ℙ⁴`.  Its zero locus is the twisted
Klein curve `C_h`, whose function field (generated by the twisted coordinates `twCoordG K D h`) is
`Work.MotK.twistFieldTG K D h` once `D : KleinData K` is fixed — this identification is
`Work.MotK.TwCensus.ZCurvePresentation` (the presentation half of node K6). -/
noncomputable def Qideal [Field K] (a b h : K) : Ideal (MvPolynomial (Fin 5) K) :=
  Ideal.radical (Ideal.span (Set.range (fun k : Fin 5 =>
    Work.MotK.kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (fun i => MvPolynomial.X i) k)))

end Work.MotK.TwCensus
