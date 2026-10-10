/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Submission.Work.MotK.KleinIdents
import Submission.Work.MotK.KleinI5

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The link data of the quadro-cubic (Crauder–Katz) transformation

The Cremona map of the link (audit §2.1, `MOTIVIC_AUDIT_LEAD.md`) is

* `f = P ∘ y`, with `y(v) = kleinStereo a b p v` the inverse stereographic projection from a
  point `p` of the quadric `q = 0` (so `q(p) = 0`), and `P = kleinP` the Pfaffian map;
* `f⁻¹ = π_p ∘ R`, with `R = kleinR` the inverse quadro-cubic map and `π_p` the projection
  from `p`.

The two polynomials whose divisors are counted in the census (audit K4/K5) are

* `kleinFhom a b p v = b(p, v) · s(y(v))`   (degree 1 + 10), the "source" equation;
* `kleinGhom a b p w = b(p, R(w)) · s'(w)`  (degree 3 + 5), the "target" equation.

The *unit* conditions making `f^*` an isomorphism of the localisations are the two identities
(proved below, resp. in `KleinLinkUnit`)

* `G_hom(f(v)) = -s(y(v))^2 · b(p,v) · F_hom(v)`  (uses I1, I3, homogeneity, `b_y`);
* `F_hom(f⁻¹(w)) = (unit) · G_hom(w)` (uses I2, I4, `b_y`, and `y(π_p(x)) = x` on `Q`).
Together with `F_hom = b(p,v)·s(y(v))` and `G_hom = b(p,R w)·s'(w)` this shows that
`V(G_hom ∘ f) ⊆ V(F_hom)` and conversely, i.e. both are units in the respective localisations.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Work.MotK

variable {R : Type*} [CommRing R]

/-- The source equation of the link: `F_hom(v) = b(p, v) · s(y(v))`. -/
def kleinFhom (a b : R) (p v : Fin 5 → R) : R :=
  kleinBilin a b p v * kleinSec a b (kleinStereo a b p v)

/-- The target equation of the link: `G_hom(w) = b(p, R(w)) · s'(w)`. -/
def kleinGhom (a b : R) (p w : Fin 5 → R) : R :=
  kleinBilin a b p (kleinR a b w) * kleinSecDual a b w

end Work.MotK
