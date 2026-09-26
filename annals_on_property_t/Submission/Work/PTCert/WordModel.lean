import Mathlib
import Submission.Work.PTCert.Checkers

/-!
# `PTCert` word model: elementary soundness lemmas

The checkers of `Checkers.lean` represent a free-group element by a word `List ℕ`, with
`evalW` the evaluation and `redW`/`invW` the (free) reduction and inverse word.  This file
collects the basic soundness lemmas of the word model:

* `evalW_cons`, `evalW_nil`, `evalW_append` — `evalW` is a monoid homomorphism;
* `evalW_invW` — `invW` computes the inverse;
* `evalW_redW` — `redW` is `evalW`-preserving (free reduction);
* the single-letter evaluations `wv_two_mul`, `wv_two_mul_succ`.

The evaluation map is exposed as `wv` (definitionally equal to the map used in `evalW`) so
that later files can reason about a single letter.
-/

set_option autoImplicit false

namespace Submission.PTCert

/-- Evaluation of a single free-group letter: generator `c/2`, inverted iff `c` is odd;
out-of-range letters are `1`.  Definitionally equal to the map used in `evalW`. -/
def wv (r c : ℕ) : FreeGroup (Fin r) :=
  if h : c / 2 < r then
    (if c % 2 = 0 then FreeGroup.of (⟨c / 2, h⟩ : Fin r)
     else (FreeGroup.of (⟨c / 2, h⟩ : Fin r))⁻¹)
  else 1

theorem evalW_eq (r : ℕ) (w : List ℕ) : evalW (r := r) w = (w.map (wv r)).prod := rfl

theorem evalW_cons (r : ℕ) (c : ℕ) (w : List ℕ) :
    evalW (r := r) (c :: w) = wv r c * evalW (r := r) w := by
  rw [evalW_eq, evalW_eq, List.map_cons, List.prod_cons]

theorem evalW_nil (r : ℕ) : evalW (r := r) [] = 1 := by rw [evalW_eq]; rfl

theorem evalW_append (r : ℕ) (u v : List ℕ) :
    evalW (r := r) (u ++ v) = evalW (r := r) u * evalW (r := r) v := by
  rw [evalW_eq, evalW_eq, evalW_eq, List.map_append, List.prod_append]

theorem xor_one_div_two (c : ℕ) : (c ^^^ 1) / 2 = c / 2 := by
  rcases Nat.even_or_odd c with h | h
  · rw [Nat.xor_one_of_even h]; obtain ⟨m, rfl⟩ := h; omega
  · rw [Nat.xor_one_of_odd h]; obtain ⟨m, hm⟩ := h; omega

/-- Inverting a letter (flipping its exponent bit) inverts its evaluation. -/
theorem wv_xor (r c : ℕ) : wv r (c ^^^ 1) = (wv r c)⁻¹ := by
  unfold wv; rw [xor_one_div_two]
  by_cases hr : c / 2 < r
  · rw [dif_pos hr, dif_pos hr]
    rcases Nat.even_or_odd c with hc | hc
    · have hm : (c ^^^ 1) % 2 = 1 := by rw [Nat.xor_one_of_even hc]; obtain ⟨m, rfl⟩ := hc; omega
      have he : c % 2 = 0 := Nat.even_iff.mp hc
      rw [hm, he]; simp
    · have hm : (c ^^^ 1) % 2 = 0 := by rw [Nat.xor_one_of_odd hc]; obtain ⟨m, hm⟩ := hc; omega
      have ho : c % 2 = 1 := Nat.odd_iff.mp hc
      rw [hm, ho]; simp
  · rw [dif_neg hr, dif_neg hr]; simp

/-- `invW` computes the inverse free-group element. -/
theorem evalW_invW (r : ℕ) (w : List ℕ) :
    evalW (r := r) (invW w) = (evalW (r := r) w)⁻¹ := by
  rw [evalW_eq, evalW_eq]
  unfold invW
  rw [List.map_reverse]
  have hmap : List.map (wv r) (List.map (fun c => c ^^^ 1) w)
      = List.map (fun x => x⁻¹) (List.map (wv r) w) := by
    rw [List.map_map, List.map_map]; congr 1; funext c
    simp [Function.comp_apply, wv_xor]
  rw [hmap]
  exact (List.prod_inv_reverse (List.map (wv r) w)).symm

/-- Evaluation of a single letter as a generator. -/
theorem wv_two_mul (r i : ℕ) (hi : i < r) : wv r (2 * i) = FreeGroup.of (⟨i, hi⟩ : Fin r) := by
  unfold wv
  rw [dif_pos (by omega : 2 * i / 2 < r)]
  have hmod : 2 * i % 2 = 0 := by omega
  rw [hmod]
  simp

/-- Evaluation of a single inverted letter. -/
theorem wv_two_mul_succ (r i : ℕ) (hi : i < r) :
    wv r (2 * i + 1) = (FreeGroup.of (⟨i, hi⟩ : Fin r))⁻¹ := by
  have h : 2 * i + 1 = (2 * i) ^^^ 1 := by
    rw [Nat.xor_one_of_even (show Even (2 * i) from ⟨i, by ring⟩)]
  rw [h, wv_xor, wv_two_mul r i hi]

/-- `evalW` of a reversed cons. -/
theorem evalW_reverse_cons (r : ℕ) (d : ℕ) (t : List ℕ) :
    evalW (r := r) ((d :: t).reverse) = evalW (r := r) t.reverse * wv r d := by
  rw [List.reverse_cons, evalW_append, evalW_cons, evalW_nil, mul_one]

/-- One reduction step preserves the value, as a reversed-accumulator invariant. -/
theorem redStep_sound (r : ℕ) (acc : List ℕ) (c : ℕ) :
    evalW (r := r) ((redStep acc c).reverse) = evalW (r := r) acc.reverse * wv r c := by
  cases acc with
  | nil => simp only [redStep, List.reverse_cons, List.reverse_nil,
      List.nil_append, evalW_cons, evalW_nil, mul_one, one_mul]
  | cons d t =>
    by_cases h : d = c ^^^ 1
    · subst h
      simp only [redStep, Nat.beq_refl, cond_true]
      rw [evalW_reverse_cons, wv_xor, mul_assoc, inv_mul_cancel, mul_one]
    · have hb : Nat.beq d (c ^^^ 1) = false := by
        rw [Bool.eq_false_iff]
        intro hh
        exact h (by rwa [Nat.beq_eq] at hh)
      simp only [redStep, hb, cond_false]
      rw [List.reverse_cons, evalW_append, evalW_cons, evalW_nil, mul_one]

/-- Free reduction `redW` preserves the free-group element. -/
theorem evalW_redW (r : ℕ) (w : List ℕ) : evalW (r := r) (redW w) = evalW (r := r) w := by
  have hgen : ∀ (w acc : List ℕ),
      evalW (r := r) ((w.foldl redStep acc).reverse)
        = evalW (r := r) acc.reverse * evalW (r := r) w := by
    intro w
    induction w with
    | nil => intro acc; rw [List.foldl_nil, evalW_nil, mul_one]
    | cons c w' ih =>
      intro acc
      rw [List.foldl_cons, ih (redStep acc c), redStep_sound, evalW_cons, mul_assoc]
  unfold redW
  rw [hgen w []]
  simp only [List.reverse_nil, evalW_nil, one_mul]

end Submission.PTCert
