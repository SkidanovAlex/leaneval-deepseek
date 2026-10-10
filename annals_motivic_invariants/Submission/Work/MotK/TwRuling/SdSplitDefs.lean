/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TwRuling.SdSextDefs
import Submission.Work.MotK.TwRuling.aeval_sdGform
import Submission.Work.MotK.TwRuling.TwSixAssemblyDefs
import Submission.Work.MotK.TGen.SdualTBrick
import Submission.Work.MotK.TGen.TwCoordGKleinTw

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Vocabulary for `Work.MotK.TwRuling.twistedVanishing`

The lemma `twistedVanishing` transports the vanishing of the *twisted* inverse map
`kleinTwR0 … (sdW K D h) = 0` over the target ruling divisor (a statement in
`sdA K D h = RatFunc ↥(twistFieldTG K D h)`) into the vanishing of the *split* ruling sextic
`σ ↦ aeval (kleinCoord D (KbG K)) (sdGform a b σ)` at the Klein coordinates.

The route (see `GUIDE_twistedVanishing.md`) is

1. `rpEval_eq_zero_of_kleinTwR0_sdW` : the image of `kleinTwR0 … (sdW K D h)` under the ring
   homomorphism `RatFunc ↥(twistFieldTG K D h) →+* RatFunc (OmG K D)` is the image of
   `rpEval K D h ∈ OmG K D [T]`, so `hzero` forces `rpEval K D h = 0`;
2. `sdSplitPoly_eq_zero_of_rpEval` : the Kummer transport (`SdSextTransport`) of
   `rpEval K D h = 0` is the split ruling polynomial `sdSplitPoly K D h = 0` (this is the
   `w·T`-shifted polynomial `R₀(A(κ) + (w·T)·B(κ))`);
3. `twistedVanishing_of_sdSplitPoly` : the evaluation of `sdSplitPoly` at `T = σ/w`
   (`w = sdWL K D h`) gives the split sextic at `κ` and the parameter `σ`, for every `σ ∈ KbG K`.

This file only sets up the vocabulary used by those three lemmas.

* `sdKbL K D` is the Klein tuple `kleinCoord D (KbG K)` pushed into the function field
  `OmG K D = K̄(E)` of `D.E` over `KbG K = AlgebraicClosure K`;
* `sdWL K D h` is the chosen fifth root `root5G K h` of `h`, pushed into `OmG K D`;
* `sdSplitPoly K D h` is `R₀(A(κ) + (w·T)·B(κ)) ∈ OmG K D [T]`, the split ruling polynomial at
  the Klein point `κ = sdKbL K D` with the ruling parameter scaled by the Kummer root `w`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.MotK.TwRuling

open WeierstrassCurve WeierstrassCurve.Affine

/-- The Klein tuple of `D` over `KbG K`, pushed into the function field `OmG K D`. -/
noncomputable def sdKbL (K : Type) [Field K] (D : Work.MotV.KleinData K) :
    Fin 5 → Work.MotK.OmG K D :=
  Work.MotV.kleinCoord D (Work.MotK.KbG K)

/-- The chosen fifth root of `h`, pushed into the function field `OmG K D`. -/
noncomputable def sdWL (K : Type) [Field K] (D : Work.MotV.KleinData K) (h : K) :
    Work.MotK.OmG K D :=
  algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h)

/-- The split ruling polynomial at the Klein point `κ = sdKbL K D`, with the ruling parameter
scaled by the Kummer root `w = sdWL K D h`:
`sdSplitPoly K D h = R₀(A(κ) + (w·T)·B(κ)) ∈ OmG K D [T]`. -/
noncomputable def sdSplitPoly (K : Type) [Field K] (D : Work.MotV.KleinData K) (h : K) :
    Polynomial (Work.MotK.OmG K D) :=
  Work.MotK.kleinTwR0
    (Polynomial.C (algebraMap K (Work.MotK.OmG K D) D.a))
    (Polynomial.C (algebraMap K (Work.MotK.OmG K D) D.b))
    (Polynomial.C (1 : Work.MotK.OmG K D))
    (fun i =>
      Polynomial.C (Work.MotK.kleinTwRuleA (algebraMap K (Work.MotK.OmG K D) D.a)
            (algebraMap K (Work.MotK.OmG K D) D.b) 1 (sdKbL K D) i)
        + (Polynomial.C (sdWL K D h) * Polynomial.X) *
          Polynomial.C (Work.MotK.kleinTwRuleB (algebraMap K (Work.MotK.OmG K D) D.a)
            (algebraMap K (Work.MotK.OmG K D) D.b) 1 (sdKbL K D) i))

/-! ## Elementary properties of the vocabulary -/

/-- `sdWL K D h` is a fifth root of (the image of) `h`. -/
theorem sdWL_pow_five (K : Type) [Field K] (D : Work.MotV.KleinData K) (h : K) :
    sdWL K D h ^ 5 = algebraMap K (Work.MotK.OmG K D) h := by
  rw [sdWL, ← map_pow, Work.MotK.TGen.root5G_spec,
    IsScalarTower.algebraMap_apply K (Work.MotK.KbG K) (Work.MotK.OmG K D)]

/-- `sdWL K D h ≠ 0` for `h ≠ 0`. -/
theorem sdWL_ne_zero (K : Type) [Field K] (D : Work.MotV.KleinData K) {h : K} (hh : h ≠ 0) :
    sdWL K D h ≠ 0 := by
  intro h0
  have h5 := sdWL_pow_five K D h
  rw [h0, zero_pow (by norm_num : (5 : ℕ) ≠ 0)] at h5
  exact hh ((algebraMap K (Work.MotK.OmG K D)).injective (by simpa using h5.symm))

/-- The image of `κ_0` in `OmG K D` is nonzero, for a good Klein datum. -/
theorem sdKbL_zero_ne (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good) :
    sdKbL K D 0 ≠ 0 :=
  hD.coord0_ne (Work.MotK.KbG K)

/-- The defining identity of the twisted coordinates, pushed into `OmG K D`. -/
theorem sdWL_pow_mul_twCoordG (K : Type) [Field K] (D : Work.MotV.KleinData K) (h : K)
    (hh : h ≠ 0) (i : Fin 5) :
    sdWL K D h ^ (i : ℕ) * Work.MotK.twCoordG K D h i = sdKbL K D i / sdKbL K D 0 := by
  rw [sdWL, sdKbL]
  exact Work.MotK.TGen.pow_mul_twCoordG D h hh i

end Work.MotK.TwRuling
