import Mathlib
import Submission.Work.IntLib.evArith
import Submission.Work.IntLib.evArithCore

/-!
# Fallback proof of the `hs ≠ []` arithmetic of the `evalPoly` budget

`evArithNeAlt` is the statement requested at `Submission/Work/IntLib/evArithNe.lean`, proved here
(by the author of `chunkEv`) so that the assembly does not have to wait for that copy.  The
arithmetic itself lives in `Submission/Work/IntLib/evArithCore.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.IntLib

open HvdH

/-- The requested `hs ≠ []` arithmetic of the budget, as an alternative to `evArithNe`. -/
theorem evArithNeAlt (KP KCM KR KEP KE KC KA KZ : ℕ) (hs : List ℕ) (b Wl LOl n1 n2 n3 : ℕ)
    (hne : hs ≠ [])
    (hW : Wl ≤ 3 * b + 1) (hLO : LOl ≤ hs.length * (b + 1))
    (hn1 : n1 ≤ KP * (KCM + KR + 1) *
      ((hs.map fun h => h.size).sum + hs.length * (b + 2) + HvdH.isz (b : ℤ) + 100))
    (hn2 : n2 ≤ (10 * KR + 10 * KC + 40 * KA + 50) *
      ((hs.map fun h => h.size).sum + hs.length * (b + 2) + 1))
    (hn3 : n3 ≤ KEP * (KE + 40) *
      (Wl + LOl + (hs.length + 1) * (b + 1) + HvdH.isz (b : ℤ) + 40)) :
    n1 + n2 + n3 + 2 ≤ Work.IntLib.polyK KP KCM KR KEP KE KC KA KZ
      * Work.IntLib.polyBudget hs b := by
  have hL0 : 1 ≤ hs.length := one_le_length_of_ne_nil_alt hne
  have hZ0 : 2 ≤ HvdH.isz (b : ℤ) := two_le_isz_alt b
  have hTS0 : (hs.map fun h => h.size).sum ≤ (hs.map fun h => HvdH.isz (h : ℤ)).sum :=
    sum_size_le_isz_alt hs
  rw [show Work.IntLib.polyK KP KCM KR KEP KE KC KA KZ
      = 1000 * (KP * (KCM + KR + 1) + KEP * (KE + 40) + (KR + KC + KA + KZ + 20) + 1)
        from rfl]
  rw [show Work.IntLib.polyBudget hs b
      = (hs.map fun h => HvdH.isz (h : ℤ)).sum + hs.length * (b + 1) + HvdH.isz (b : ℤ) + 1
        from rfl]
  -- name the four atoms so that the arithmetic lemma applies syntactically
  set S : ℕ := (hs.map fun h => HvdH.isz (h : ℤ)).sum with hSdef
  set T : ℕ := (hs.map fun h => h.size).sum with hTdef
  set L : ℕ := hs.length with hLdef
  set Z : ℕ := HvdH.isz (b : ℤ) with hZdef
  refine arithCoreAlt S T L Z b Wl LOl n1 n2 n3 KP KCM KR KEP KE KC KA KZ
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hTdef, hSdef]; exact hTS0
  · rw [hLdef]; exact hL0
  · rw [hZdef]; exact hZ0
  · exact hW
  · rw [hLdef]; exact hLO
  · rw [hTdef, hLdef, hZdef]; exact hn1
  · rw [hTdef, hLdef]; exact hn2
  · rw [hLdef, hZdef]; exact hn3

end Work.IntLib
