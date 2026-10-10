/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotC2

# `Work.MotC2`: automorphisms of the function field of an elliptic curve

The chapter target is `aut_functionField`: for an elliptic Weierstrass curve `E` over a field `L`
with `j(E) ≠ 0, 1728`, every `L`-algebra automorphism of `L(E)` is a translation composed with
`±1`.

This module is the single entry point; it imports the whole chapter.

* `Submission.Work.MotC2.Defs` — definitions (`Coord`, `Func`, `genX`, `genY`, `baseE`, `infU`,
  `infW`, `infCoordRing`, `infIdeal`, `infPlace`, `affRing`, `affPlaceAt`, `IsRatPlace`, `plugHom`)
  and their basic API.
* `Submission.Work.MotC2.Relations` — the Weierstrass relation in the three coordinate systems.
* `Submission.Work.MotC2.Integral` — integrality of `y` over `L[x]` and of `y/x²` over `L[1/x]`.
* `Submission.Work.MotC2.Negation` — `negAlgEquiv`, the automorphism `[-1]`.
* `Submission.Work.MotC2.Translation` — `transAlgEquiv`, the translation action of `E(L)`.
* `Submission.Work.MotC2.InfPlace`, `AffPlace` — the local rings of `O` and of affine points.
  `InfPlace` is the statement that `infPlace E` is a rational place with maximal ideal generated
  by `infW E`; it is proved from `InfAux`, `InfPlaceSetup`, `InfPlaceLocalization`, `InfPlaceCore`
  and `infPlace_nonunit_eq_infW_mul`.
* `Submission.Work.MotC2.DVRMaximal` — maximality of places among DVR subalgebras.
* `Submission.Work.MotC2.Classification` — rational places of `L(E)/L` are exactly `E(L) ∪ {O}`.
* `Submission.Work.MotC2.IsRatPlaceMap` — rationality of places is preserved by `L`-algebra
  automorphisms of `L(E)`.
* `Submission.Work.MotC2.TransPlace` — the translation action on places: translation by `T`
  carries the place at `T` to the point at infinity.
* `Submission.Work.MotC2.PoleOrder` — `𝓛(2O) = ⟨1,x⟩`, `𝓛(3O) = ⟨1,x,y⟩`.
* `Submission.Work.MotC2.AffRingNormalCharTwo`, `AffRingNormalNeTwo` — normality of `L[x,y]`
  (needed by `CoordPreserved`).
* `Submission.Work.MotC2.CoordPreserved` — fixing `O` fixes the affine coordinate ring.
* `Submission.Work.MotC2.VariableChange` — automorphisms fixing `O` are variable changes.
* `Submission.Work.MotC2.AutE` — `Aut(E) = {±1}` for `j ≠ 0, 1728`.
* `Submission.Work.MotC2.FuncExt` — extensionality of automorphisms of `L(E)` and the
  characterisation of `[-1]`.
* `Submission.Work.MotC2.negAlgEquiv_transX`, `negAlgEquiv_transY`,
  `negAlgEquiv_mul_transAlgEquiv` — the action of `[-1]` on the coordinates of a translate, and the
  twisted homomorphism identity `[-1]·τ_Q = τ_{-Q}·[-1]`.
* `Submission.Work.MotC2.transAlgEquiv_injective` — `τ : E(L) → Aut_L(L(E))` is injective.
* `Submission.Work.MotC2.aut_functionField` — **the chapter target**.
* `Submission.Work.MotC2.Places` — standalone, reusable export of the place theory.
-/

import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.Integral
import Submission.Work.MotC2.Negation
import Submission.Work.MotC2.Translation
import Submission.Work.MotC2.InfAux
import Submission.Work.MotC2.InfPlaceSetup
import Submission.Work.MotC2.InfPlaceLocalization
import Submission.Work.MotC2.InfPlaceCore
import Submission.Work.MotC2.infPlace_nonunit_eq_infW_mul
import Submission.Work.MotC2.InfPlace
import Submission.Work.MotC2.infPlace_frac
import Submission.Work.MotC2.AffPlace
import Submission.Work.MotC2.DVRMaximal
import Submission.Work.MotC2.Classification
import Submission.Work.MotC2.IsRatPlaceMap
import Submission.Work.MotC2.TransPlace
import Submission.Work.MotC2.PoleOrder
import Submission.Work.MotC2.AffRingBasisForm
import Submission.Work.MotC2.ConjFunc
import Submission.Work.MotC2.EllipticCharTwoNonsingular
import Submission.Work.MotC2.CharTwoCrux
import Submission.Work.MotC2.NeTwoSetup
import Submission.Work.MotC2.NeTwoDecomp
import Submission.Work.MotC2.NeTwoIsIntegralMap
import Submission.Work.MotC2.NeTwoSquarefreeCubic
import Submission.Work.MotC2.NeTwoNoDoubleRoot
import Submission.Work.MotC2.NeTwoSquarefreeDAux
import Submission.Work.MotC2.NeTwoSquarefreeD
import Submission.Work.MotC2.NeTwoRatFuncCrux
import Submission.Work.MotC2.NormNeTwoCrux
import Submission.Work.MotC2.CharTwoNormCrux
import Submission.Work.MotC2.AffRingNormalCharTwo
import Submission.Work.MotC2.AffRingNormalNeTwo
import Submission.Work.MotC2.CoordPreserved
import Submission.Work.MotC2.VariableChange
import Submission.Work.MotC2.AutE
import Submission.Work.MotC2.FuncExt
import Submission.Work.MotC2.negAlgEquiv_transX
import Submission.Work.MotC2.negAlgEquiv_transY
import Submission.Work.MotC2.negAlgEquiv_mul_transAlgEquiv
import Submission.Work.MotC2.transAlgEquiv_injective
import Submission.Work.MotC2.aut_functionField

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
