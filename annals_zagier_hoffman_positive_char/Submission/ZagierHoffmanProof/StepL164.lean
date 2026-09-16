import Submission.ZagierHoffmanProof.StepL163
import Submission.ZagierHoffmanProof.StepL128
set_option autoImplicit false
set_option maxHeartbeats 20000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L164: the AMBIENT measure `ambNu` of route (C) and its decrease lemmas

  ambNu (k q w) t := ( (psum t k, w − depth t) , (M0 − initVal q w t, pad0 t (initLen q t)) )
with `M0 = (q+2)^(w+1) − 1`, in lex products (`toLex`).  The first block orders by the
ambient prefix sum `psum t k` and then by DEPTH (`w − depth`, so a strict depth increase
decreases the measure — the case used by the tower step of regime B); the second block is
the `Init`-measure (reversed `initVal`, then the entry at the `Init` length).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The ambient measure of route (C): `((psum-k, w − depth), (M0 − initVal, entry))`. -/
noncomputable def ambNu (k q w : ℕ) {r : ℕ} (s : Fin r → ℕ+) :
    (ℕ ×ₗ ℕ) ×ₗ (ℕ ×ₗ ℕ) :=
  toLex (toLex (psum s k, w - r),
    toLex ((q + 2) ^ (w + 1) - 1 - initVal q w s, pad0 s (initLen q s)))

/-- A strict ambient prefix drop decreases `ambNu`. -/
lemma ambNu_lt_of_psum_lt (k q w : ℕ) {r r' : ℕ} (t : Fin r → ℕ+) (m : Fin r' → ℕ+)
    (h : psum m k < psum t k) : ambNu k q w m < ambNu k q w t := by
  rw [ambNu, ambNu, Prod.Lex.lt_iff]
  left
  rw [Prod.Lex.lt_iff]
  left
  exact h

/-- A strict depth increase (with the ambient prefix sum not increasing) decreases
`ambNu`. -/
lemma ambNu_lt_of_depth_gt (k q w : ℕ) {r r' : ℕ} (t : Fin r → ℕ+) (m : Fin r' → ℕ+)
    (ht : r ≤ w) (hm : r' ≤ w) (h : r < r') (hle : psum m k ≤ psum t k) :
    ambNu k q w m < ambNu k q w t := by
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact ambNu_lt_of_psum_lt k q w t m hlt
  · rw [ambNu, ambNu, Prod.Lex.lt_iff]
    left
    rw [Prod.Lex.lt_iff]
    right
    constructor
    · exact heq
    · show w - r' < w - r
      omega

/-- At equal ambient prefix sum and equal depth, strict `Init`-growth decreases `ambNu`. -/
lemma ambNu_lt_of_initVal (k q w : ℕ) {r r' : ℕ} (t : Fin r → ℕ+) (m : Fin r' → ℕ+)
    (ht : weight r t = w) (hm : weight r' m = w)
    (heq : psum m k = psum t k) (hd : r = r') (hiv : initVal q w t < initVal q w m) :
    ambNu k q w m < ambNu k q w t := by
  have hMu : initVal q w m < (q + 2) ^ (w + 1) := initVal_lt_pow q w m hm
  have hivM1 : initVal q w t < (q + 2) ^ (w + 1) - 1 := by
    have hle : initVal q w m ≤ (q + 2) ^ (w + 1) - 1 := Nat.le_sub_one_of_lt hMu
    omega
  rw [ambNu, ambNu, Prod.Lex.lt_iff]
  right
  constructor
  · apply toLex_inj.mpr
    refine Prod.ext heq ?_
    show w - r' = w - r
    omega
  · show toLex ((q + 2) ^ (w + 1) - 1 - initVal q w m, pad0 m (initLen q m)) <
        toLex ((q + 2) ^ (w + 1) - 1 - initVal q w t, pad0 t (initLen q t))
    rw [Prod.Lex.lt_iff]
    left
    exact Nat.sub_lt_sub_left hivM1 hiv

/-- At equal ambient prefix sum, equal depth and equal `initVal`, a strict drop of the
entry at the `Init` length decreases `ambNu`. -/
lemma ambNu_lt_of_entry (k q w : ℕ) {r r' : ℕ} (t : Fin r → ℕ+) (m : Fin r' → ℕ+)
    (heq : psum m k = psum t k) (hd : r = r')
    (hiv : initVal q w m = initVal q w t)
    (hdrop : pad0 m (initLen q m) < pad0 t (initLen q t)) :
    ambNu k q w m < ambNu k q w t := by
  rw [ambNu, ambNu, Prod.Lex.lt_iff]
  right
  constructor
  · apply toLex_inj.mpr
    refine Prod.ext heq ?_
    show w - r' = w - r
    omega
  · show toLex ((q + 2) ^ (w + 1) - 1 - initVal q w m, pad0 m (initLen q m)) <
        toLex ((q + 2) ^ (w + 1) - 1 - initVal q w t, pad0 t (initLen q t))
    rw [Prod.Lex.lt_iff]
    right
    constructor
    · simp [hiv]
    · exact hdrop

end ZagierHoffmanPositiveChar
