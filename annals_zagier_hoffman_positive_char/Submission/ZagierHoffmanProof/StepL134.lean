import Submission.ZagierHoffmanProof.StepL133
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L134: ★ `maink_case1_kk3` — StepL115 obligation (2) CLOSED (SESSION 259b)

The (k, k−3) CASE-1 splice, obtained purely by INSTANTIATING the generic
StepL133 `maink_case1_splice` at j = k−3:
  • `hmid` from `maink_kk3_hmid` (the two q-entries at k−3, k−2);
  • `hsleq` = the cond1 of the (k−1)-admissibility `h1`;
  • the config from `maink_config_full` (hdepu/hau/hc0/hbhd/hwtA/hhead/hXw/
    hbndB/hpref).
The `rec` is the (β)-form (MainkStep3 + P_full + ¬k-adm) — the SESSION 258x
decision — so NO (k−1)-admissibility of the members and NO Ak1 are needed.
The deeper-j CASE-1 splices are the same instantiation at other j.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ The CASE-1 (k, k−3) splice (StepL115 obligation (2)), in the (β) form. -/
theorem maink_case1_kk3 (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (k : ℕ) (hk1 : 1 ≤ k) (hk4 : 4 ≤ k) (hkr : k ≤ r)
    (hbigv : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsjv : (s ⟨k - 3 - 1, by omega⟩ : ℕ) < Nat.card F)
    (hqmid : (s ⟨k - 3, by omega⟩ : ℕ) = Nat.card F)
    (hqmid1 : (s ⟨k - 2, by omega⟩ : ℕ) = Nat.card F)
    (h1 : kAdmissible (Nat.card F) s (k - 1))
    (rec : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (_hm : weight r' m = w),
      MainkStep3 k (Nat.card F) w s m → ¬ kAdmissible (Nat.card F) m k → AdmExpT F w k m) :
    AdmExpT F w k s := by
  classical
  have hmid := maink_kk3_hmid F r s k hk1 hkr hqmid hqmid1
  rcases maink_config_full F k r s hk1 hkr hbigv with
    ⟨R0, u, hdepu, hau, hc0, hbhd, hwtA, hhead, hXw, hbndB, hpref, _⟩
  exact maink_case1_splice F w r s hw k (k - 3) hk1 hkr (by omega) (by omega)
    hbigv hsjv hmid (fun x hx => h1.1 x hx) R0 u hdepu hau hc0 hbhd hwtA hhead hXw
    hbndB hpref rec

/-- The deeper-j CASE-1 splices: the same instantiation at an arbitrary j with
the q-run hypothesis `hmid` supplied by the caller (StepL115 obligation (3)). -/
theorem maink_case1_deep (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (k j : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbigv : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (h1 : kAdmissible (Nat.card F) s (k - 1))
    (rec : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (_hm : weight r' m = w),
      MainkStep3 k (Nat.card F) w s m → ¬ kAdmissible (Nat.card F) m k → AdmExpT F w k m) :
    AdmExpT F w k s := by
  classical
  rcases maink_config_full F k r s hk1 hkr hbigv with
    ⟨R0, u, hdepu, hau, hc0, hbhd, hwtA, hhead, hXw, hbndB, hpref, _⟩
  exact maink_case1_splice F w r s hw k j hk1 hkr hj1 hjk
    hbigv hsj hmid (fun x hx => h1.1 x hx) R0 u hdepu hau hc0 hbhd hwtA hhead hXw
    hbndB hpref rec

end ZagierHoffmanPositiveChar
