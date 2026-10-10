import Mathlib
import Submission.Work.MotK.TwRuling.TwSixCoeffDefs
import Submission.Work.MotK.TGen.SdualTBrick
import Submission.Work.MotK.TGen.TwCoordGKleinTw

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Assembly vocabulary for the T-twisted ruling nonvanishing

`rpEval K D h` is the polynomial `R₀(A(κ) + T·B(κ))` in `OmG K D [T]`, where
`κ = twCoordG K D h` is the twisted Klein point of `D`, `A = kleinTwRuleA` and `B = kleinTwRuleB`
are the two ruling vectors (`T = Polynomial.X`).

The two facts needed to pass from the (purely polynomial) nonvanishing statements about
`sdCoeff6` to the target `sdW_kleinTwR_ne_zero` are:

* `coeff_rpEval` : `(rpEval K D h).coeff j = aeval κ (sdCoeff6 (KbG K) a b h j)`, i.e. the
  coefficient of `T^j` of the ruling polynomial at the Klein point is the polynomial
  `sdCoeff6 … j` evaluated at `κ` (naturality of the whole construction);
* `sdW_ne_zero_of_coeff` : `(rpEval K D h).coeff j ≠ 0` implies the target
  `kleinTwR … (sdW K D h) ≠ 0` (via `sdW_kleinTwR_eq` and the injection
  `sdA K D h ↪ RatFunc (OmG K D)`, `OmG K D` being the function field of `D.E` over `K̄`).
-/

set_option autoImplicit false

namespace Work.MotK.TwRuling

open WeierstrassCurve WeierstrassCurve.Affine

/-- `R₀(A(κ) + T·B(κ))` as a polynomial in `T` over the function field `OmG K D` of `D`. -/
noncomputable def rpEval (K : Type) [Field K] (D : Work.MotV.KleinData K) (h : K) :
    Polynomial (Work.MotK.OmG K D) :=
  Work.MotK.kleinTwR0 (Polynomial.C (algebraMap K (Work.MotK.OmG K D) D.a))
    (Polynomial.C (algebraMap K (Work.MotK.OmG K D) D.b))
    (Polynomial.C (algebraMap K (Work.MotK.OmG K D) h))
    (fun k => Polynomial.C (Work.MotK.kleinTwRuleA (algebraMap K (Work.MotK.OmG K D) D.a)
        (algebraMap K (Work.MotK.OmG K D) D.b) (algebraMap K (Work.MotK.OmG K D) h)
        (Work.MotK.twCoordG K D h) k)
      + Polynomial.X * Polynomial.C (Work.MotK.kleinTwRuleB (algebraMap K (Work.MotK.OmG K D) D.a)
        (algebraMap K (Work.MotK.OmG K D) D.b) (algebraMap K (Work.MotK.OmG K D) h)
        (Work.MotK.twCoordG K D h) k))

/-- **The basis of `L(5·O)` adapted to the T-twist**, needed to apply
`Work.MotK.TwRuling.sexticTw_notMem_kernel` (whose `κ` must lie in `span (sdBas E) = L(5·O)`).

⚠ The twisted coordinates `twCoordG K D h i = w^{-i}·(κ_i/κ_0)` are **not** in `L(5·O)` (the ratio
has poles at the zeros of `κ_0`), so they cannot be fed to the abstract kernel lemma directly.
`kappaP` is the corrected choice: `κ'_i = w^{-i}·κ_i = κ_0 · twCoordG K D h i`, which

* is a `KbG K`-scalar multiple of `kleinCoord D (KbG K) i`, hence `κ' ∈ span (sdBas E)` and
  `sdBas E ⊆ span κ'` (both spans are `L(5·O)`, by `D.Good.spans`);
* satisfies the twisted Pfaffians `kleinTwP a b h κ' = 0`: by `TwCoordGKleinTw` the *ratio*
  `twCoordG` does, `κ' = κ_0 · twCoordG` and `kleinTwP` is homogeneous of degree `2`
  (`Work.MotK.kleinTwP_homog`), so `kleinTwP a b h κ' = κ_0² · kleinTwP a b h (twCoordG) = 0`.

The transfer back to `twCoordG` (which is what `rpEval` and hence the target are built from) uses
the same homogeneity: `aeval κ' F = κ_0 ^ 6 * aeval (twCoordG K D h) F` for `F` of degree `6`, and
`κ_0 ≠ 0` by `D.Good.coord0_ne`. -/
noncomputable def kappaP (K : Type) [Field K] (D : Work.MotV.KleinData K) (h : K) :
    Fin 5 → Work.MotK.OmG K D :=
  fun i => ((algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h))⁻¹) ^ (i : ℕ)
    * Work.MotV.kleinCoord D (Work.MotK.KbG K) i

end Work.MotK.TwRuling
