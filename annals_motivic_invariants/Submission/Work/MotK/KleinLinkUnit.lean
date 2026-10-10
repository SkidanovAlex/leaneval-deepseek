/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.LinkData
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The unit condition of the link: `G_hom(f(v)) = -s(y(v))^2 · b(p,v) · F_hom(v)`

Audit part of node **K3**: with `y(v) = kleinStereo a b p v` the inverse stereographic
projection from a point `p` of the quadric `q = 0`, and `f = kleinP ∘ kleinStereo`, the
"target" equation `G_hom` pulled back along `f` is a unit multiple of the "source" equation
`F_hom`:

  `kleinGhom a b p (kleinP a b y) = -s(y)^2 · b(p,v) · kleinFhom a b p v`.

The proof uses, on the nose,

* **I1** `kleinR_kleinP`:  `R(P(y)) = s(y)·y`,
* the bilinearity of the polar `b = kleinBilin` of `q`,
* **I3** `kleinSecDual_kleinP`:  `s'(P(y)) = s(y)^2`,
* `kleinBilin_stereo`:  `b(p, y(v)) = 2 q(v) q(p) - b(p,v)^2`, together with `q(p) = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotK

variable {R : Type*} [CommRing R]

/-- The polar form `b = kleinBilin` of the quadric `q` is bilinear: it is linear in the
second argument (and hence — the form being symmetric — in either).  This is the
polarisation identity `b(u, c·v) = c·b(u,v)` for a homogeneous quadratic form `q`. -/
theorem kleinBilin_smul_right (a b : R) (u v : Fin 5 → R) (c : R) :
    kleinBilin a b u (fun i => c * v i) = c * kleinBilin a b u v := by
  simp only [kleinBilin, kleinQ, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, Pi.add_apply]
  first | refl_ring1 | ring

/-- **The unit condition of the link** (audit node K3): pulling back the target equation
`G_hom` along the Cremona map `f = kleinP ∘ kleinStereo` gives `-s(y)^2 · b(p,v) · F_hom`,
so `G_hom ∘ f` and `F_hom` differ by a unit of the localisation. -/
theorem KleinLinkUnit {R : Type*} [CommRing R] (a b : R) (p v : Fin 5 → R)
    (hp : Work.MotK.kleinQ a b p = 0) :
    Work.MotK.kleinGhom a b p (Work.MotK.kleinP a b (Work.MotK.kleinStereo a b p v))
      = -(Work.MotK.kleinSec a b (Work.MotK.kleinStereo a b p v)) ^ 2 * Work.MotK.kleinBilin a b p v
          * Work.MotK.kleinFhom a b p v := by
  set y : Fin 5 → R := kleinStereo a b p v with hy
  -- I1: `R(P(y)) = s(y)·y`
  have hI1 : kleinR a b (kleinP a b y) = fun i => kleinSec a b y * y i :=
    funext fun i => kleinR_kleinP a b y i
  -- I3: `s'(P(y)) = s(y)^2`
  have hI3 : kleinSecDual a b (kleinP a b y) = kleinSec a b y ^ 2 :=
    kleinSecDual_kleinP a b y
  -- `q_y`: `b(p, y(v)) = 2 q(v) q(p) - b(p,v)^2`
  have hst : kleinBilin a b p y
      = 2 * kleinQ a b v * kleinQ a b p - kleinBilin a b p v ^ 2 := by
    rw [hy]; exact kleinBilin_stereo a b p v
  rw [kleinGhom, kleinFhom, hI1, kleinBilin_smul_right a b p y (kleinSec a b y), hI3, hst, hp]
  first | refl_ring1 | ring

end Work.MotK
