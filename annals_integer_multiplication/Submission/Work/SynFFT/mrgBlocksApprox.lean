import Mathlib
import Submission.Work.SynFFT.mrgPassDefs
import Submission.Work.SynFFT.lvlAllGetD

/-!
# SynFFT: the interleave ("merge") passes assemble blockwise

`ApproxSL p r t ws u e` says that the list `ws` of `t` coefficient vectors approximates the
array `u` with error `≤ e`.  This module proves that the *interleave* (merge) of scale `s` can be
assembled block by block: if the slice is cut into `t / (2s)` consecutive blocks of `2s`
coefficient vectors and each block `b` is approximated with error `0` by the list `V b`
(at the exact target `mrgN r s (vecFun p r (blkVec s ws b))`), then the concatenation of the
`V b` approximates `mrgN r s u` with the *same* error `e` as `ws` approximated `u`.

The mathematical content is a pure index computation: for `q < t` write `q = b·(2s) + i` with
`i < 2s`; then `mrgN r s u q` reads `u` at position `b·(2s) + (i/2 + (i%2)·s)`, which is exactly
the position inside block `b` that the block word reads.
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH

/-! ## Helper lemmas -/

/-- The sum of the lengths of the first `n` members of a family of lists all of length `m`. -/
private lemma sum_map_length_range {α : Type} (V : ℕ → List α) (m n : ℕ)
    (hV : ∀ b < n, (V b).length = m) :
    ((List.range n).map fun b => (V b).length).sum = n * m := by
  have hm : (List.range n).map (fun b => (V b).length) = List.replicate n m := by
    rw [List.map_congr_left (g := fun _ => m) (fun b hb => hV b (List.mem_range.mp hb))]
    simp
  rw [hm, List.sum_replicate]
  simp

/-- Integer division by `m` when the dividend lies in the `n`-th block of size `m`. -/
private lemma nat_div_eq_of_le_lt {m q n : ℕ} (hm : 0 < m)
    (h1 : n * m ≤ q) (h2 : q < n * m + m) : q / m = n := by
  have h3 : n ≤ q / m := (Nat.le_div_iff_mul_le hm).mpr h1
  have h4 : q / m < n + 1 := by
    rw [Nat.div_lt_iff_lt_mul hm, Nat.succ_mul]; exact h2
  omega

/-- The remainder by `m` when the dividend lies in the `n`-th block of size `m`. -/
private lemma nat_mod_eq_of_le_lt {m q n : ℕ}
    (h1 : n * m ≤ q) (h2 : q < n * m + m) : q % m = q - n * m := by
  have hsub : q - n * m < m := by omega
  have hq : q = n * m + (q - n * m) := by rw [Nat.add_comm, Nat.sub_add_cancel h1]
  conv_lhs => rw [hq]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hsub]

/-- Index of the flattened concatenation of a family of lists of equal length `m`: the `q`-th
entry is the `q % m`-th entry of the `q / m`-th member. -/
private lemma getElem?_flatten_range {α : Type} (V : ℕ → List α) (m : ℕ) :
    ∀ n q, (∀ b < n, (V b).length = m) → q < n * m →
      (((List.range n).map V).flatten)[q]? = (V (q / m))[q % m]? := by
  intro n
  induction n with
  | zero => intro q hV hq; simp at hq
  | succ n ih =>
    intro q hV hq
    rw [Nat.succ_mul] at hq
    have hVn : ∀ b < n, (V b).length = m := fun b hb => hV b (by omega)
    have hlen : ((List.range n).map V).flatten.length = n * m := by
      rw [List.length_flatten, List.map_map, Function.comp_def]
      exact sum_map_length_range V m n hVn
    rw [List.range_succ, List.map_append, List.map_singleton, List.flatten_append,
      List.flatten_singleton, List.getElem?_append, hlen]
    by_cases hlt : q < n * m
    · rw [if_pos hlt]; exact ih q hVn hlt
    · rw [if_neg hlt]
      have hmpos : 0 < m := by
        by_contra h
        have hm0 : m = 0 := by omega
        rw [hm0, Nat.mul_zero, Nat.add_zero] at hq
        omega
      have hle : n * m ≤ q := by omega
      rw [nat_div_eq_of_le_lt hmpos hle hq, nat_mod_eq_of_le_lt hle hq]

/-- `getD` form of `getElem?_flatten_range`. -/
private lemma getD_flatten_range {α : Type} (V : ℕ → List α) (m n q : ℕ) (d : α)
    (hV : ∀ b < n, (V b).length = m) (hq : q < n * m) :
    (((List.range n).map V).flatten).getD q d = (V (q / m)).getD (q % m) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    getElem?_flatten_range V m n q hV hq]

/-- The `j`-th entry of the `b`-th block of `2s` coefficient vectors of `ws` is the
`b·(2s) + j`-th entry of `ws`. -/
private lemma blkVec_getD (s b j : ℕ) (ws : List (List (ℤ × ℤ))) (hj : j < 2 * s) :
    (blkVec s ws b).getD j [] = ws.getD (b * (2 * s) + j) [] := by
  simp only [blkVec, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hj,
    List.getElem?_drop]

/-- The index computation behind `mrgN`: reading `mrgN r s · ` at position
`b·(2s) + i` with `i < 2s` reads position `b·(2s) + (i/2 + (i%2)·s)`. -/
private lemma mrgIdx_eq (s b i : ℕ) (hi : i < 2 * s) :
    (b * (2 * s) + i) / (2 * s) * (2 * s) + ((b * (2 * s) + i) / 2 % s)
      + ((b * (2 * s) + i) % 2) * s = b * (2 * s) + (i / 2 + (i % 2) * s) := by
  have hs2 : 0 < 2 * s := by omega
  have hdiv : (b * (2 * s) + i) / (2 * s) = b := by
    rw [show b * (2 * s) + i = (2 * s) * b + i by ring, Nat.mul_add_div hs2,
      Nat.div_eq_of_lt hi, Nat.add_zero]
  have hdiv2 : (b * (2 * s) + i) / 2 = b * s + i / 2 := by
    rw [show b * (2 * s) + i = 2 * (b * s) + i by ring, Nat.mul_add_div (by norm_num : 0 < 2)]
  have hmod2 : (b * (2 * s) + i) / 2 % s = i / 2 % s := by
    rw [hdiv2, show b * s + i / 2 = i / 2 + s * b by ring, Nat.add_mul_mod_self_left]
  have hmod2b : (b * (2 * s) + i) % 2 = i % 2 := by
    rw [show b * (2 * s) + i = i + (b * s) * 2 by ring, Nat.add_mul_mod_self_right]
  rw [hdiv, hmod2, hmod2b, Nat.mod_eq_of_lt (by omega : i / 2 < s)]
  ring

/-- `mrgN` applied to the exact target function of a list `v` of coefficient vectors: for an
index `i < 2s` inside one block it is the fixed-point value of `v` at the block-internal
position `i/2 + (i%2)·s`. -/
private lemma mrgN_vecFun (p r s : ℕ) (v : List (List (ℤ × ℤ))) (i : ℕ) (hi : i < 2 * s)
    (c : Fin r) :
    mrgN r s (vecFun p r v) i c
      = fxC p ((v.getD (i / 2 + (i % 2) * s) []).getD (c : ℕ) (0, 0)) := by
  have h1 : i / (2 * s) = 0 := Nat.div_eq_of_lt hi
  have h2 : i / 2 % s = i / 2 := Nat.mod_eq_of_lt (by omega)
  simp only [mrgN, vecFun]
  rw [h1, h2]
  simp

/-! ## The main lemma -/

theorem mrgBlocksApprox
    (p r t s : ℕ) (ws : List (List (ℤ × ℤ))) (u : Work.SynFFT.Arr r) (e : ℝ)
    (V : ℕ → List (List (ℤ × ℤ)))
    (hs : 0 < s) (hdiv : 2 * s ∣ t) (hlen : ws.length = t)
    (happ : Work.SynFFT.ApproxSL p r t ws u e)
    (hVlen : ∀ b, b < t / (2 * s) → (V b).length = 2 * s)
    (hVap : ∀ b, b < t / (2 * s) →
       Work.SynFFT.ApproxSL p r (2 * s) (V b)
         (Work.SynFFT.mrgN r s (Work.SynFFT.vecFun p r (Work.SynFFT.blkVec s ws b))) 0) :
    Work.SynFFT.ApproxSL p r t (((List.range (t / (2 * s))).map V).flatten)
      (Work.SynFFT.mrgN r s u) e := by
  have hm2 : 0 < 2 * s := by omega
  have ht : t / (2 * s) * (2 * s) = t := Nat.div_mul_cancel hdiv
  have hlenflat : (((List.range (t / (2 * s))).map V).flatten).length = t := by
    rw [List.length_flatten, List.map_map, Function.comp_def,
      sum_map_length_range V (2 * s) (t / (2 * s)) (fun b hb => hVlen b hb)]
    exact ht
  unfold ApproxSL at happ ⊢
  obtain ⟨-, hwsap⟩ := happ
  refine ⟨hlenflat, ?_⟩
  intro q hq c
  set b := q / (2 * s) with hbdef
  set i := q % (2 * s) with hidef
  have hi : i < 2 * s := Nat.mod_lt _ hm2
  have hqe : b * (2 * s) + i = q := by
    rw [hbdef, hidef, Nat.mul_comm]
    exact Nat.div_add_mod q (2 * s)
  have hb : b < t / (2 * s) := by
    have h : q / (2 * s) < t / (2 * s) := by
      rw [Nat.div_lt_iff_lt_mul hm2, ht]
      exact hq
    show b < t / (2 * s)
    rw [hbdef]
    exact h
  have hVbap := (hVap b hb).2
  have hflat : (((List.range (t / (2 * s))).map V).flatten).getD q [] = (V b).getD i [] := by
    rw [hbdef, hidef]
    exact getD_flatten_range V (2 * s) (t / (2 * s)) q [] (fun b hb => hVlen b hb)
      (by rw [ht]; exact hq)
  have hj : i / 2 + (i % 2) * s < 2 * s := by
    have h1 : i / 2 < s := by omega
    have h2 : (i % 2) * s ≤ s := by
      calc (i % 2) * s ≤ 1 * s := Nat.mul_le_mul_right s (by omega)
        _ = s := one_mul s
    omega
  have hVexact : fxC p (((V b).getD i []).getD (c : ℕ) (0, 0))
      = mrgN r s (vecFun p r (blkVec s ws b)) i c := by
    have h2 := hVbap i hi c
    have hle : ‖fxC p (((V b).getD i []).getD (c : ℕ) (0, 0))
        - mrgN r s (vecFun p r (blkVec s ws b)) i c‖ ≤ 0 := by
      nlinarith [h2, pow_pos (by norm_num : (0:ℝ) < 2) p,
        norm_nonneg (fxC p (((V b).getD i []).getD (c : ℕ) (0, 0))
          - mrgN r s (vecFun p r (blkVec s ws b)) i c)]
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hle (norm_nonneg _)))
  have hblk : mrgN r s (vecFun p r (blkVec s ws b)) i c
      = fxC p ((ws.getD (b * (2 * s) + (i / 2 + (i % 2) * s)) []).getD (c : ℕ) (0, 0)) := by
    rw [mrgN_vecFun p r s (blkVec s ws b) i hi c,
      blkVec_getD s b (i / 2 + (i % 2) * s) ws hj]
  have hidx : q / (2 * s) * (2 * s) + (q / 2 % s) + (q % 2) * s
      = b * (2 * s) + (i / 2 + (i % 2) * s) := by
    rw [← hqe]
    exact mrgIdx_eq s b i hi
  have hu : mrgN r s u q c = u (b * (2 * s) + (i / 2 + (i % 2) * s)) c := by
    simp only [mrgN, hidx]
  have hlt : b * (2 * s) + (i / 2 + (i % 2) * s) < t := by
    have h1 : b + 1 ≤ t / (2 * s) := hb
    have h2 : (b + 1) * (2 * s) ≤ t := by
      calc (b + 1) * (2 * s) ≤ (t / (2 * s)) * (2 * s) := Nat.mul_le_mul_right _ h1
        _ = t := ht
    have h3 : b * (2 * s) + (i / 2 + (i % 2) * s) < (b + 1) * (2 * s) := by
      have : (b + 1) * (2 * s) = b * (2 * s) + 2 * s := by ring
      omega
    omega
  rw [hflat, hVexact, hblk, hu]
  exact hwsap _ hlt c

end Work.SynFFT
