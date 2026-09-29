import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.Kernel.encodeNatBits
import Submission.Work.IntLib.encodeNatBridge

namespace Work.Transform

open HvdH

/-! ## Private encoding-size bookkeeping for `cfxVal` / `cvecVal` -/

private theorem vsz_int' (z : ℤ) : vsz (.int z) = isz z := Work.IntLib.vsz_int z

/-- Encoding size of a `cons` value. -/
private theorem vsz_cons' (a b : Val) : vsz (.cons a b) = vsz a + vsz b + 1 := by
  simp only [vsz, Val.enc, List.length_cons, List.length_append]

/-- Encoding size of a `cons`-chain: one `cons` per element plus the final `nil`. -/
private theorem vsz_ofList' (xs : List Val) : vsz (ofList xs) = (xs.map vsz).sum + xs.length + 1 := by
  induction xs with
  | nil => simp [ofList, vsz, Val.enc]
  | cons x xs ih =>
    have e : ofList (x :: xs) = Val.cons x (ofList xs) := rfl
    rw [e, vsz_cons', ih]
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- The arithmetic slack: for `p ≥ 100`, `n * (2p + 8) + n + 1 ≤ 4 * (n * p^2 + 1)`. -/
private theorem arith_bound {S n p : ℕ} (hp : 100 ≤ p) (h : S ≤ n * (2 * p + 8)) :
    S + n + 1 ≤ 4 * (n * p ^ 2 + 1) := by
  nlinarith [hp, h]

/-- A coordinate of a point of the disc `z ∈ C̃◦` has `natAbs ≤ 2^p`. -/
private theorem natAbs_le_of_inDisc {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) :
    z.1.natAbs ≤ 2 ^ p ∧ z.2.natAbs ≤ 2 ^ p := by
  have key : ∀ w : ℤ, w ^ 2 ≤ 4 ^ p → w.natAbs ≤ 2 ^ p := by
    intro w hw
    have h1 : (w.natAbs : ℤ) ^ 2 ≤ (2 : ℤ) ^ p * 2 ^ p := by
      rw [Int.natAbs_sq]
      calc w ^ 2 ≤ 4 ^ p := hw
        _ = (2 : ℤ) ^ p * 2 ^ p := by rw [show (4 : ℤ) = 2 * 2 by norm_num, mul_pow]
    have h2 : w.natAbs ^ 2 ≤ (2 ^ p) ^ 2 := by
      rw [pow_two (2 ^ p)]
      exact_mod_cast h1
    exact (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).1 h2
  have h' : z.1 ^ 2 + z.2 ^ 2 ≤ 4 ^ p := h
  exact ⟨key z.1 (by nlinarith [sq_nonneg z.2]), key z.2 (by nlinarith [sq_nonneg z.1])⟩

/-- A coordinate of a point of the disc has integer encoding size `≤ p + 3`. -/
private theorem isz_le_of_inDisc {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) :
    isz z.1 ≤ p + 3 ∧ isz z.2 ≤ p + 3 := by
  obtain ⟨h1, h2⟩ := natAbs_le_of_inDisc h
  have key : ∀ w : ℤ, w.natAbs ≤ 2 ^ p → isz w ≤ p + 3 := by
    intro w hw
    have h3 : w.natAbs.size ≤ p + 1 := by
      rw [Nat.size_le]
      exact lt_of_le_of_lt hw (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self p))
    simp only [isz]
    omega
  exact ⟨key z.1 h1, key z.2 h2⟩

theorem inDiscVecSizes {p n : ℕ} {zs : List (ℤ × ℤ)} (h : HvdH.InDiscVec p n zs) (hp : 100 ≤ p) :
    (∀ z ∈ zs, HvdH.vsz (HvdH.cfxVal z) ≤ 2 * p + 8) ∧
    HvdH.vsz (HvdH.cvecVal zs) ≤ 4 * (n * p ^ 2 + 1) := by
  have hlen : zs.length = n := h.1
  have hmem : ∀ z ∈ zs, inDisc p z := h.2
  -- every entry of the vector is a `cfxVal` of size `≤ 2p + 8`
  have hcf : ∀ z ∈ zs, vsz (cfxVal z) ≤ 2 * p + 8 := by
    intro z hz
    obtain ⟨ha, hb⟩ := isz_le_of_inDisc (hmem z hz)
    rw [show cfxVal z = Val.cons (.int z.1) (.int z.2) from rfl, vsz_cons', vsz_int', vsz_int']
    omega
  refine ⟨hcf, ?_⟩
  -- the total size is `Σ vsz + length + 1`
  have hsum : ((zs.map cfxVal).map vsz).sum ≤ zs.length * (2 * p + 8) := by
    calc ((zs.map cfxVal).map vsz).sum
        = (zs.map (fun z => vsz (cfxVal z))).sum := by rw [List.map_map]; rfl
      _ ≤ (zs.map fun _ => 2 * p + 8).sum := List.sum_le_sum hcf
      _ = zs.length * (2 * p + 8) := by
          induction zs with
          | nil => simp
          | cons x xs ih => simp [Nat.succ_mul]; omega
  rw [hlen] at hsum
  rw [show cvecVal zs = ofList (zs.map cfxVal) from rfl, vsz_ofList', List.length_map, hlen]
  exact arith_bound hp hsum

end Work.Transform
