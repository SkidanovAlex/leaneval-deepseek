import Mathlib
import Submission.Work.PTCert.LetterEval

/-!
# `PTCert`: a letter acts on a word as `applyLetter`

Building on `b1Img` (the action of a letter on a single generator), this file proves that the
computable `applyLetter r k w` computes the image of the free-group element of `w` under `b1 r k`:

* `wv_eq_of`, `wv_eq_inv`, `wv_eq_one` — evaluation of the single-letter map `wv`;
* `evalW_flatMap` — `evalW` is compatible with `List.flatMap`;
* `b1_wv` — the per-letter identity;
* `applyLetterSound` (**the main result**):
  `(b1 r k) (evalW w) = evalW (applyLetter r k w)` for `k < NB1 r`.
-/

set_option autoImplicit false

namespace Submission.PTCert

open Submission.FreeGroupAut

theorem wv_eq_of (r c : ℕ) (hcr : c / 2 < r) (hc : c % 2 = 0) :
    wv r c = FreeGroup.of (⟨c / 2, hcr⟩ : Fin r) := by
  unfold wv; rw [dif_pos hcr, if_pos hc]

theorem wv_eq_inv (r c : ℕ) (hcr : c / 2 < r) (hc : c % 2 ≠ 0) :
    wv r c = (FreeGroup.of (⟨c / 2, hcr⟩ : Fin r))⁻¹ := by
  unfold wv; rw [dif_pos hcr, if_neg hc]

theorem wv_eq_one (r c : ℕ) (hcr : ¬ c / 2 < r) : wv r c = 1 := by
  unfold wv; rw [dif_neg hcr]

theorem evalW_single_ge (r i : ℕ) (hi : r ≤ i) : evalW (r := r) [2 * i] = 1 := by
  rw [evalW_cons, evalW_nil, mul_one, wv_eq_one r (2 * i) (by omega)]

theorem evalW_flatMap (r : ℕ) (g : ℕ → List ℕ) (w : List ℕ) :
    evalW (r := r) (w.flatMap g) = (w.map (fun c => evalW (r := r) (g c))).prod := by
  induction w with
  | nil => simp [evalW_nil]
  | cons c w' ih => rw [List.flatMap_cons, evalW_append, ih, List.map_cons, List.prod_cons]

/-- The per-letter identity: a single letter of a word is mapped to the corresponding
`letterImg` (or its inverse word). -/
theorem b1_wv (r k c : ℕ) (hk : k < NB1 r) :
    (b1 r k) (wv r c) = evalW (r := r)
      (bif Nat.beq (c % 2) 0 then letterImg r k (c / 2) else invW (letterImg r k (c / 2))) := by
  rcases Nat.even_or_odd c with he | ho
  · have hc : c % 2 = 0 := Nat.even_iff.mp he
    rw [cond_natbeq, if_pos hc]
    by_cases hcr : c / 2 < r
    · rw [wv_eq_of r c hcr hc]
      exact b1Img r k hk ⟨c / 2, hcr⟩
    · have hge : r ≤ c / 2 := by omega
      rw [wv_eq_one r c hcr, map_one, letterImg_of_ge r k (c / 2) hk hge,
          evalW_single_ge r (c / 2) hge]
  · have hc : c % 2 = 1 := Nat.odd_iff.mp ho
    rw [cond_natbeq, if_neg (by omega : ¬ c % 2 = 0)]
    by_cases hcr : c / 2 < r
    · rw [wv_eq_inv r c hcr (by omega), map_inv, b1Img r k hk ⟨c / 2, hcr⟩, evalW_invW]
    · have hge : r ≤ c / 2 := by omega
      rw [wv_eq_one r c hcr, map_one, letterImg_of_ge r k (c / 2) hk hge, evalW_invW,
          evalW_single_ge r (c / 2) hge]
      rw [inv_one]

/-- **The letter `b1 r k` acts on a word by `applyLetter`.** -/
theorem applyLetterSound (r k : ℕ) (hk : k < NB1 r) (w : List ℕ) :
    (b1 r k) (evalW (r := r) w) = evalW (r := r) (applyLetter r k w) := by
  rw [evalW_eq, map_list_prod, List.map_map]
  simp only [Function.comp_def]
  rw [show (w.map (fun c => (b1 r k) (wv r c)))
        = w.map (fun c => evalW (r := r)
            (bif Nat.beq (c % 2) 0 then letterImg r k (c / 2)
             else invW (letterImg r k (c / 2)))) from by
        apply List.map_congr_left
        intro c _
        exact b1_wv r k c hk]
  unfold applyLetter
  rw [evalW_redW, evalW_flatMap]

end Submission.PTCert
