import Submission.ZagierHoffmanProof.StepL134
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L135: ingredients for (a) `maink_g5_zeta_core` (the j = 0 / all-q front
chain) — SESSION 259d

The G5 (j = 0) ζ-identity at symbolic k follows `g5c1_zeta_core` (StepL77, level
2) with the iterate count k−1.  This module supplies the two structural facts
that transcription needs:
  • `maink_g5_depA_u_eq`: the iterated leading member's depth is exactly r
    (the count (k−1) plus `hdepu`);
  • `maink_g5_u_pad0_front`: its first k−1 entries are q (the all-q front) —
    via `BCqIter_cA_pad0_front`;
and records the exact remaining recipe (see the docstring of the second lemma).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ The iterated leading member of the G5 chain has depth exactly r. -/
lemma maink_g5_depA_u_eq (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (R0 : BinaryRel F) (u : R0.ιA) (hdepu : R0.depA u = (r - k) + 1) :
    (RelData.BCqIter F (k - 1) (toData F R0)).depA
        (RelData.iterIdx F (k - 1) (toData F R0) u) = r := by
  have hdep := RelData.BCqIter_depA_at F (k - 1) (toData F R0) u
  rw [hdep]
  have hd : (toData F R0).depA u = (r - k) + 1 := hdepu
  omega

/-- ★ The iterated leading member's first k−1 entries are q (the all-q front).
REMAINING RECIPE for `maink_g5_zeta_core` (mirror `g5c1_zeta_core`, count k−1):
  1. `hz0` := `BCqIter_zeta_zero F (k−1) R0` + `toBinaryRel_zeta_eq` + `simpa`
     (generic in the count — verbatim from the level-2 template);
  2. `hu_zeta : ζ_A F (D.cA u) = ζ_A F s` — via the entrywise u-values lemma
     (the count-(k−1) analogue of `g5c1_u_cA_values`): for m < k−1 the entry is
     `qExp F` from `BCqIter_cA_value`'s `if`-branch (then `= s⟨m⟩` by
     `hallq`), and for m ≥ k−1 it is `(R0.cA u)⟨m−(k−1)⟩`, converted via `hc0`
     to the `bstarBase` entry and then by `bstarBase_head` (= s⟨k−1⟩) /
     `bstarBase_tail` (= the `sTail` entry); the needed `Fin.cast` bridges go
     through `Fin.ext` (cf. StepL126's `hcast`), with the depth equality from
     `maink_g5_depA_u_eq`;
  3. `hfu : f u = ζ_A F s` via `hau` + `completion_coe_one` (verbatim);
  4. the guard/erase bookkeeping `hgu`/`hspl` (verbatim) and the final
     `rw [hspl, hfu] at hz0; simpa [add_assoc] using hz0`. -/
lemma maink_g5_u_pad0_front (r : ℕ) (s : Fin r → ℕ+) (k : ℕ)
    (R0 : BinaryRel F) (u : R0.ιA) :
    ∀ x : ℕ, x < k - 1 →
      pad0 ((RelData.BCqIter F (k - 1) (toData F R0)).cA
        (RelData.iterIdx F (k - 1) (toData F R0) u)) x = Nat.card F := by
  intro x hx
  exact BCqIter_cA_pad0_front F (k - 1) R0 u x hx

end ZagierHoffmanPositiveChar
