import Mathlib
import Submission.Work.IntLib.Defs

/-!
# API for `HvdH.chunks` / `HvdH.evalChunks`

`HvdH.chunks x b N` is the list of the `N` base-`2^b` digits of `x`, least significant first,
and `HvdH.evalChunks hs b = Σ_j hs[j]·2^{b j}` (overlap-add evaluation).  This file collects the
elementary facts about them that the `IntLib` chapter (`chunk`/`evalPoly` words) needs.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-- Recursion step for `evalChunks` on `cons`. -/
theorem evalChunks_cons (h : ℕ) (hs : List ℕ) (b : ℕ) :
    HvdH.evalChunks (h :: hs) b = h + 2^b * HvdH.evalChunks hs b := by
  unfold HvdH.evalChunks
  rw [show (h :: hs).length = hs.length + 1 from rfl, List.range_succ_eq_map, List.map_cons,
      List.sum_cons, List.map_map]
  rw [show (h :: hs).getD 0 0 * 2 ^ (b * 0) = h from by simp]
  rw [show (List.map ((fun j => (h :: hs).getD j 0 * 2 ^ (b * j)) ∘ Nat.succ) (List.range hs.length))
        = List.map (fun j => (hs.getD j 0 * 2 ^ (b * j)) * 2^b) (List.range hs.length) from by
      apply List.map_congr_left
      intro j _
      simp only [Function.comp_apply, List.getD_cons_succ]
      rw [Nat.mul_succ, Nat.pow_add]
      ring]
  rw [List.sum_map_mul_right]
  ring

/-- `evalChunks` is the base-`2^b` `Nat.ofDigits` fold. -/
theorem evalChunks_eq_ofDigits (hs : List ℕ) (b : ℕ) :
    HvdH.evalChunks hs b = Nat.ofDigits (2^b) hs := by
  induction hs with
  | nil => simp [HvdH.evalChunks]
  | cons h t ih =>
    rw [evalChunks_cons, ih, Nat.ofDigits_eq_foldr (2^b) (h :: t), Nat.ofDigits_eq_foldr (2^b) t]
    simp only [List.foldr_cons]
    push_cast
    ring

theorem evalChunks_singleton (c b : ℕ) : HvdH.evalChunks [c] b = c := by
  simp [HvdH.evalChunks]

theorem evalChunks_append (hs ts : List ℕ) (b : ℕ) :
    HvdH.evalChunks (hs ++ ts) b = HvdH.evalChunks hs b + 2^(b * hs.length) * HvdH.evalChunks ts b := by
  rw [evalChunks_eq_ofDigits, evalChunks_eq_ofDigits, evalChunks_eq_ofDigits, Nat.ofDigits_append]
  congr 1
  rw [pow_mul]

theorem chunks_length (x b N : ℕ) : (HvdH.chunks x b N).length = N := by
  simp [HvdH.chunks]

theorem chunks_succ (x b N : ℕ) :
    HvdH.chunks x b (N+1) = HvdH.chunks x b N ++ [x / 2^(b*N) % 2^b] := by
  unfold HvdH.chunks
  rw [List.range_succ, List.map_append, List.map_singleton]

theorem chunks_getD (x b N j : ℕ) (hj : j < N) :
    (HvdH.chunks x b N).getD j 0 = x / 2^(b*j) % 2^b := by
  unfold HvdH.chunks
  have hlen : j < (List.map (fun j => x / 2 ^ (b * j) % 2 ^ b) (List.range N)).length := by
    rw [List.length_map, List.length_range]; exact hj
  rw [List.getD_eq_getElem _ _ hlen, List.getElem_map, List.getElem_range]

/-- Splitting off the lowest digit: `x % 2^(k+m) = x % 2^k + 2^k · (x / 2^k % 2^m)`. -/
theorem mod_pow_digit (x k m : ℕ) :
    x % 2^(k+m) = x % 2^k + 2^k * (x / 2^k % 2^m) := by
  have h := Nat.mod_mul_right_div_self x (2^k) (2^m)
  rw [← h, Nat.pow_add]
  conv_lhs => rw [← Nat.div_add_mod (x % (2^k * 2^m)) (2^k)]
  rw [Nat.mod_mod_of_dvd x (dvd_mul_right (2^k) (2^m))]
  ring

theorem evalChunks_chunks (x b N : ℕ) :
    HvdH.evalChunks (HvdH.chunks x b N) b = x % 2^(b*N) := by
  induction N with
  | zero => simp [HvdH.chunks, HvdH.evalChunks, Nat.mod_one]
  | succ N ih =>
    rw [chunks_succ, evalChunks_append, ih, chunks_length, evalChunks_singleton, Nat.mul_succ,
        mod_pow_digit x (b*N) b]

theorem chunk_mod (x b N j : ℕ) (hj : j < N) :
    x / 2^(b*j) % 2^b = (x % 2^(b*N)) / 2^(b*j) % 2^b := by
  have hd : 2^(b*j) * 2^b ∣ 2^(b*N) := by
    rw [← Nat.pow_add, ← Nat.mul_succ]
    exact Nat.pow_dvd_pow 2 (Nat.mul_le_mul_left b (Nat.succ_le_of_lt hj))
  rw [← Nat.mod_mul_right_div_self x (2^(b*j)) (2^b),
      ← Nat.mod_mul_right_div_self (x % 2^(b*N)) (2^(b*j)) (2^b)]
  congr 1
  rw [Nat.mod_mod_of_dvd x hd]

theorem chunks_mod (x b N : ℕ) :
    HvdH.chunks x b N = HvdH.chunks (x % 2^(b*N)) b N := by
  unfold HvdH.chunks
  apply List.map_congr_left
  intro j hj
  exact chunk_mod x b N j (List.mem_range.mp hj)

/-- `evalChunks` of `N` digits of size `< 2^(3b)` is `< 2^(b*N + 3b)`. -/
theorem evalChunks_lt : ∀ (hs : List ℕ) (b : ℕ), 1 ≤ b → (∀ h ∈ hs, h < 2^(3*b)) →
    HvdH.evalChunks hs b < 2^(b * hs.length + 3 * b) := by
  intro hs
  induction hs using List.reverseRecOn with
  | nil =>
      intro b hb hh
      simp [HvdH.evalChunks]
  | append_singleton l c ih =>
      intro b hb hh
      have h1 := ih b hb (fun h hh' => hh h (List.mem_append.mpr (Or.inl hh')))
      have hc : c < 2^(3*b) := hh c (List.mem_append.mpr (Or.inr (by simp)))
      have h3 : 2^(b*l.length) * c < 2^(b*l.length) * 2^(3*b) :=
        Nat.mul_lt_mul_of_pos_left hc (Nat.two_pow_pos _)
      have h4 : HvdH.evalChunks l b + 2^(b*l.length)*c
          < 2^(b*l.length+3*b) + 2^(b*l.length)*2^(3*b) := Nat.add_lt_add h1 h3
      rw [evalChunks_append, evalChunks_singleton, List.length_append, List.length_singleton]
      refine lt_of_lt_of_le h4 ?_
      have hY : 2^(b*l.length+3*b) = 2^(b*l.length) * 2^(3*b) := by rw [pow_add]
      have hX : 2^(b*(l.length+1)+3*b) = 2^(b*l.length) * 2^(3*b) * 2^b := by
        rw [Nat.mul_succ, add_assoc, pow_add, pow_add]
        ring
      rw [hY, hX]
      have h2b : 2 ≤ 2^b := by
        have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hb
        simpa using this
      calc 2^(b*l.length) * 2^(3*b) + 2^(b*l.length) * 2^(3*b)
          = 2 * (2^(b*l.length) * 2^(3*b)) := by ring
        _ = 2^(b*l.length) * 2^(3*b) * 2 := by ring
        _ ≤ 2^(b*l.length) * 2^(3*b) * 2^b := Nat.mul_le_mul_left _ h2b

/-- The running value of the first `j` digits, divided by `2^(b j)`, stays `≤ 2^(2b+1)`. -/
theorem evalChunks_take_div (hs : List ℕ) (b j : ℕ) (hb : 1 ≤ b)
    (hh : ∀ h ∈ hs, h < 2^(3*b)) (hj : j ≤ hs.length) :
    HvdH.evalChunks (hs.take j) b / 2^(b*j) ≤ 2^(2*b+1) := by
  have h2b : 2 ≤ 2^b := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hb
    simpa using this
  have key : ∀ j, j ≤ hs.length → HvdH.evalChunks (hs.take j) b < 2^(2*b+1) * 2^(b*j) := by
    intro j
    induction j with
    | zero =>
        intro _
        simp [HvdH.evalChunks]
    | succ j ih =>
        intro hj1
        have hjlen : j < hs.length := by omega
        rw [List.take_succ_eq_append_getElem hjlen, evalChunks_append, evalChunks_singleton,
            List.length_take, Nat.min_eq_left (le_of_lt hjlen)]
        have h1 := ih (le_of_lt hjlen)
        have hc : hs[j] < 2^(3*b) := hh _ (List.getElem_mem hjlen)
        have h2 : 2^(b*j) * hs[j] < 2^(b*j) * 2^(3*b) :=
          Nat.mul_lt_mul_of_pos_left hc (Nat.two_pow_pos _)
        have h3 : HvdH.evalChunks (hs.take j) b + 2^(b*j) * hs[j]
            < 2^(2*b+1) * 2^(b*j) + 2^(b*j) * 2^(3*b) := Nat.add_lt_add h1 h2
        refine lt_of_lt_of_le h3 ?_
        have hpow : 2^(2*b+1) ≤ 2^(3*b) :=
          Nat.pow_le_pow_right (by norm_num) (by omega : 2*b+1 ≤ 3*b)
        have h33 : 2^(3*b) + 2^(3*b) = 2^(3*b+1) := by rw [← two_mul, ← pow_succ']
        have h22 : 2^(2*b+1) * 2^b = 2^(3*b+1) := by rw [← pow_add]; congr 1; omega
        have hsum : 2^(2*b+1) + 2^(3*b) ≤ 2^(2*b+1) * 2^b := by
          rw [h22]
          calc 2^(2*b+1) + 2^(3*b) ≤ 2^(3*b) + 2^(3*b) := Nat.add_le_add_right hpow _
            _ = 2^(3*b+1) := h33
        have hbj : 2^(b*(j+1)) = 2^(b*j) * 2^b := by rw [Nat.mul_succ, pow_add]
        rw [hbj]
        calc 2^(2*b+1) * 2^(b*j) + 2^(b*j) * 2^(3*b)
            = 2^(b*j) * (2^(2*b+1) + 2^(3*b)) := by ring
          _ ≤ 2^(b*j) * (2^(2*b+1) * 2^b) := Nat.mul_le_mul_left _ hsum
          _ = 2^(2*b+1) * (2^(b*j) * 2^b) := by ring
  exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact le_of_lt (key j hj))

theorem chunksAPI : (∀ (x b N : ℕ), (HvdH.chunks x b N).length = N) ∧ (∀ (x b N j : ℕ), j < N → (HvdH.chunks x b N).getD j 0 < 2 ^ b) ∧ (∀ (x b N : ℕ), HvdH.evalChunks (HvdH.chunks x b N) b = x % 2 ^ (b * N)) ∧ (∀ (x b N : ℕ), 1 ≤ b → x < 2 ^ (b * N) → HvdH.evalChunks (HvdH.chunks x b N) b = x) ∧ (∀ (x b N : ℕ), HvdH.chunks x b N = HvdH.chunks (x % 2 ^ (b * N)) b N) ∧ (∀ (hs : List ℕ) (b : ℕ), 1 ≤ b → (∀ h ∈ hs, h < 2 ^ (3 * b)) → HvdH.evalChunks hs b < 2 ^ (b * hs.length + 3 * b)) ∧ (∀ (hs : List ℕ) (b j : ℕ), 1 ≤ b → (∀ h ∈ hs, h < 2 ^ (3 * b)) → j ≤ hs.length → HvdH.evalChunks (hs.take j) b / 2 ^ (b * j) ≤ 2 ^ (2 * b + 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x b N
    exact chunks_length x b N
  · intro x b N j hj
    rw [chunks_getD x b N j hj]
    exact Nat.mod_lt _ (Nat.two_pow_pos b)
  · intro x b N
    exact evalChunks_chunks x b N
  · intro x b N _ hx
    rw [evalChunks_chunks, Nat.mod_eq_of_lt hx]
  · intro x b N
    exact chunks_mod x b N
  · exact evalChunks_lt
  · exact evalChunks_take_div

end Work.IntLib
