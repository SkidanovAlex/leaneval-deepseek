import Submission.Work.ZassenhausSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Tits endomorphism of `GF(2^(2n+1))`

Suzuki 1962 (and BG 5.21, where it is *derived* from the computation of `τ`): the field
automorphism `θ` underlying `Sz(2^(2n+1))` is the one with `θ² = ` Frobenius, i.e.
`θ : x ↦ x ^ 2^(n+1)`.  Here it is realised as `iterateFrobeniusEquiv F 2 (n+1)`, and the
defining property `θ (θ x) = x²` is proved.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

/-- The **Tits endomorphism** `x ↦ x ^ 2 ^ (n+1)` of `GF(2^(2n+1))` (BG Definition 5.5:
`θ` is a Tits endomorphism if `θ²` is the Frobenius). -/
noncomputable def titsTheta (n : ℕ) :
    GaloisField 2 (2 * n + 1) ≃+* GaloisField 2 (2 * n + 1) :=
  iterateFrobeniusEquiv (GaloisField 2 (2 * n + 1)) 2 (n + 1)

/-- The Tits endomorphism is the `(n+1)`-fold Frobenius. -/
theorem titsTheta_apply (n : ℕ) (x : GaloisField 2 (2 * n + 1)) :
    titsTheta n x = x ^ 2 ^ (n + 1) :=
  iterateFrobeniusEquiv_def (GaloisField 2 (2 * n + 1)) 2 (n + 1) x

/-- **`θ²` is the Frobenius** (BG 5.21): `θ (θ x) = x²`. -/
theorem titsTheta_sq_apply (n : ℕ) (x : GaloisField 2 (2 * n + 1)) :
    titsTheta n (titsTheta n x) = x ^ 2 := by
  haveI : Fintype (GaloisField 2 (2 * n + 1)) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 (2 * n + 1)) = 2 ^ (2 * n + 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 (2 * n + 1) (by omega)
  rw [titsTheta_apply, titsTheta_apply, ← pow_mul]
  have hexp : 2 ^ (n + 1) * 2 ^ (n + 1) = 2 ^ (2 * n + 1) * 2 := by ring
  rw [hexp, pow_mul, ← hcard, FiniteField.pow_card]

end Work.ZassenhausSuzuki
