import Mathlib
import Submission.Work.MotAS.asW0Defs
import Submission.Work.MotAS.ASRulDefs
import Submission.Work.MotAS.ASTransport
import Submission.Work.MotAS.ASMatrix
import Submission.Work.MotAS.twistFieldAS_eq
import Submission.Work.MotK.TwRuling.sdW_four_ne_zero
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.Cert` §1 — naturality of the explicit coefficient vectors

The coefficient vectors `cPAS`, `cB` of `Submission/Work/MotAS/asW0Defs.lean` are literal matrices
of polynomials with integer coefficients, so they commute with every ring homomorphism.  These two
pointwise naturality statements are what allows the pair-sum identities of `asW0CertB.lean` (stated
over an arbitrary commutative ring `S`) to be compared with the `S`-linear combination
`∑ q, algebraMap F S (cPAS a b g k q) * (κ (pfA q) * κ (pfB q))` appearing in
`Work.MotK.TwRuling.SdWfour.Phi`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.MotAS

open Work.MotK.TwRuling.SdWfour

variable {R : Type*} [CommRing R]

namespace Cert

/-- Naturality of the coefficient vector `cPAS a b g k` of the `k`-th AS Pfaffian. -/
theorem map_cPAS {S : Type*} [CommRing S] (φ : R →+* S) (a b g : R) (k : Fin 5)
    (q : Fin 5 × Fin 3) : cPAS (φ a) (φ b) (φ g) k q = φ (cPAS a b g k q) := by
  obtain ⟨i, s⟩ := q
  fin_cases k <;> fin_cases i <;> fin_cases s <;>
    simp [cPAS, cPASmat, map_sub, map_add, map_mul, map_pow, map_ofNat] <;>
    refl_ring1

/-- Naturality of the coefficient vector `cB a b g` of the quadratic form `asRuleQB a b g · 0`. -/
theorem map_cB {S : Type*} [CommRing S] (φ : R →+* S) (a b g : R) (q : Fin 5 × Fin 3) :
    cB (φ a) (φ b) (φ g) q = φ (cB a b g q) := by
  obtain ⟨i, s⟩ := q
  fin_cases i <;> fin_cases s <;>
    simp [cB, map_sub, map_add, map_mul, map_pow, map_ofNat] <;>
    refl_ring1

end Cert

end Work.MotAS
