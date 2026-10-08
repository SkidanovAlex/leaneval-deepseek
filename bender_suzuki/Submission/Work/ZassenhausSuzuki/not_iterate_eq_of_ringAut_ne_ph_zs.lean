import Mathlib
import Submission.Work.Higman.Main
import Submission.Work.ZassenhausSuzuki.SzAuto.arith_facts
import Submission.Work.ZassenhausSuzuki.SzAuto.not_iterate_eq_of_ringAut_ne_v2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-- **Order computation** (replacement for the placeholder
`Work.ZassenhausSuzuki.SzAuto.not_iterate_eq_of_ringAut_ne_ph`; note: the conclusion is the
*negation* of "`y ↦ λ·σ y` is a Singer cycle of order `2ⁿ-1`") — for `σ ≠ 1` a field automorphism
of `GF(2ⁿ)` and a unit `λ`, the map `y ↦ λ·σ y` is never a `(2ⁿ-1)`-cycle: it has a shorter period
`m` with `0 < m < 2ⁿ-1`.  (A proof already exists in the workspace as
`SzAuto/not_iterate_eq_of_ringAut_ne_v2.lean`, with `m = (n/gcd(n,s))·(2^gcd(n,s) − 1)` for
`σ = x ↦ x^(2^s)`; do not cite the `unproved` placeholder in `SzAuto/aut_V_action_scalar.lean`, and
check `#print axioms` of your lemma.) -/
theorem not_iterate_eq_of_ringAut_ne_ph_zs {n : ℕ} (hn : 1 ≤ n) (lam : (GaloisField 2 n)ˣ)
    (σ : GaloisField 2 n ≃+* GaloisField 2 n) (hσ : σ ≠ 1) :
    ¬ (∀ x : GaloisField 2 n, ((fun y => (lam : GaloisField 2 n) * σ y)^[2 ^ n - 1]) x = x ∧
       ∀ m : ℕ, 0 < m → m < 2 ^ n - 1 →
         ∃ x : GaloisField 2 n, ((fun y => (lam : GaloisField 2 n) * σ y)^[m]) x ≠ x) :=
  SzAuto.not_iterate_eq_of_ringAut_ne_v2 hn lam σ hσ

end Work.ZassenhausSuzuki
