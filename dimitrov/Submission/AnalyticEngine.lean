import Mathlib
import Submission.Minpoly
import Submission.Powers
import Submission.Conjugates
import Submission.EngineAlg
import Submission.Induction
import Submission.Gnorm
import Submission.E1Content
import Submission.E2cMain

/-!
# The analytic engine (single remaining gap, isolated)

`Submission.Induction.dimitrov_of_engine` reduces the challenge theorem to
`Submission.Engine.house_bound_of_pow2_irreducible` (proved in Engine.lean),
whose algebraic tail is verified (`Submission.EngineAlg`).  The *only*
unproved statement left in the whole tree is

    AnalyticEngine.hankel_eventually_zero :

        house α < 2^(1/(4·|argSet α|))   ⟹   HankelInput α hα

i.e.: if the house is strictly below the phase bound then the integer
sequence `a` (formal square root `√(R₂R₄)` of the reversed power product,
`Submission.PowRev.powRev_sqrt_integral`, whose analytic continuation `g` off
the hedgehog over `{z²,z⁴}` is `Submission.BranchX.exists_laurent_branch`)
has Hankel determinants `hankelDet a k = det(a(i+j))_{i,j<k}` that vanish
for all large `k`.

## Structure of the proof (wired; the single deep input is Step 3)

`hankel_eventually_zero` is proved by the composition of the two machine-
verified E1/E2 layers:

    E1  E1Content.e1_hedgehogBound : house α < 2^(1/(4·|argSet α|))
        ⟹ HedgehogBound (conjugateValues α)   (Submission/E1Content.lean)
    E2  E2c.hankelDet_zero_of_hedgehogBound : HedgehogBound (conjugateValues α)
        ⟹ HankelInput α hα                   (Submission/E2cMain.lean)

HedgehogBound (`Submission.PolyaCore`) asserts monic polynomials of every
degree bounded by `C·θ^n` (θ < 1) on an ε-fattening of the hedgehog
`star (conjugateValues α) = ⋃_{z} ([0,z²] ∪ [0,z⁴])`; the E2 layer then
deforms the Hankel contour to the fattened star and applies Hadamard +
integrality to conclude `hankelDet a k = 0` for large k.

Both layers are fully machine-verified and depend, through E1Content, on
exactly ONE deep statement (the Dubinin content, in Fekete form):

    Step3.sym_maximality (Submission/Step3.lean):
        any hedgehog of s unit-length spikes in arbitrary directions
        u has Fekete root limsup ≤ L·4^(-1/s):
        limsup_n (feketeNumber (dirStar u L) (n+1))^(2/((n+1)·n)) ≤ L·4^(-1/u.card)

The E1 reduction (SS1.dubinin_fekete_limsup -> SS1.fekete_decay_of_short_
spikes -> Dubinin.polyDecay_* -> ChebPower -> E1Content) converts
`sym_maximality` + the spike geometry (≤ 2·|argSet α| spikes, length ≤ H⁴,
margin arithmetic `H⁴ < 4^(1/s)`) into `e1_hedgehogBound`.  All those
reduction steps are verified (zero sorries); the only unproved declaration
of the whole tree is `Step3.sym_maximality` (Dubinin's inequality:
cap(⋃[0,a_j]) ≤ 4^(-1/s)·max |a_j| -- research-level potential theory).
-/

noncomputable section

open scoped Polynomial

namespace Submission.AnalyticEngine

open Submission.Conjugates
open Submission.Powers
open Submission.EngineAlg

variable {K : Type*} [Field K] [NumberField K]

/-- **The analytic engine.**  If the house of the nonzero algebraic integer
`α` is strictly below `2^(1/(4·|argSet α|))`, then the formal square-root
sequence `a` of `Gpoly (minpoly ℤ α)` has eventually vanishing integer Hankel
determinants (the input of `EngineAlg.no_hankelInput`, which then contradicts
the engine hypotheses). -/
theorem hankel_eventually_zero (α : K) (hα : IsIntegral ℤ α) (hα0 : α ≠ 0)
    (hH : NumberField.house α < (2 : ℝ) ^ (1 / (4 * ((argSet α).card : ℝ))))
    (h2irr : Irreducible (pow2 (minpoly ℤ α))) :
    HankelInput α hα := by
  -- E1 (house bound -> polynomial control on the fattened hedgehog) then
  -- E2 (polynomial control -> Hankel determinants eventually zero).
  exact Submission.E2c.hankelDet_zero_of_hedgehogBound α hα hα0
    (Submission.E1Content.e1_hedgehogBound α hα hα0 hH)

end Submission.AnalyticEngine

end
