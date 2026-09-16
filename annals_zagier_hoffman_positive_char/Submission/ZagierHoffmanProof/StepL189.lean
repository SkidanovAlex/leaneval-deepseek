import Submission.ZagierHoffmanProof.StepL166
import Submission.ZagierHoffmanProof.StepL134

set_option autoImplicit false
set_option maxHeartbeats 40000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L189: the generic CASE-1 (k,j) port at an ambient level

`maink_case1_deep_amb`: the `maink_case1_deep` wrapper (StepL134) at the ambient
level.  The config package `maink_config_full` (StepL108) supplies
R0/u/hdepu/hau/hc0/hbhd/hwtA/hhead/hXw/hbndB/hpref and the chain itself is the
ambient splice `maink_case1_splice_amb` (StepL166), whose outputs are
Lambda-admissible and whose recursion hypothesis receives the ambient `ambNu`
descent.  theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The CASE-1 (k, j) splice at an ambient level `Lam >= k`. -/
theorem maink_case1_deep_amb (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (k j : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbigv : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (h1 : kAdmissible (Nat.card F) s (k - 1))
    (Λ : ℕ) (hΛ : k ≤ Λ)
    (rec : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (_hm : weight r' m = w),
      ambNu Λ (Nat.card F) w m < ambNu Λ (Nat.card F) w s → ¬ kAdmissible (Nat.card F) m Λ →
      AdmExpT F w Λ m) :
    AdmExpT F w Λ s := by
  classical
  rcases maink_config_full F k r s hk1 hkr hbigv with
    ⟨R0, u, hdepu, hau, hc0, hbhd, hwtA, hhead, hXw, hbndB, hpref, _⟩
  exact maink_case1_splice_amb F w r s hw k j hk1 hkr hj1 hjk
    hbigv hsj hmid (fun x hx => h1.1 x hx) R0 u hdepu hau hc0 hbhd hwtA hhead hXw
    hbndB hpref Λ hΛ rec

end ZagierHoffmanPositiveChar
