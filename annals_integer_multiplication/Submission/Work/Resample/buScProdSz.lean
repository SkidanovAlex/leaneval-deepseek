import Mathlib
import Submission.Work.Resample.buQWscalDefs

/-!
# `Work.Resample.buScProdSz`: the uniform size bound on the products of the scaling stage

The scaling stage `buQWscal` applies the element map `buScProd (2^p)` to the `zipWith` of the
diagonal weights `D̃'` (`buWd p α s t`) with the work vector `u` (all of whose entries lie in the
disc of radius `2^{p+1}`).  This module proves that **every single value** produced by that
`zipWith` has `vsz ≤ buScB p = 3p + 12`, which is the hypothesis needed by the cost analysis of the
`mapList`/`zipWith` combinator around the scaling stage.

The mathematical content is a two-line estimate: with `8|W| ≤ 3·2^p` and `|a| ≤ 2^{p+1}` we have
`|W·a| < 2^p·2^{p+1}`, hence `|W·a / 2^p| < 2^{p+1}` and `isz (W·a / 2^p) ≤ p+3`; a complex value
is the `cons` of two such integers, so `vsz ≤ 2(p+3) + 1 = 2p + 7 ≤ 3p + 12`.

The formalisation only uses `Work.Fx.vsz_int`, `Work.Fx.vsz_cons` and `Work.Fx.isz_le_of_natAbs_lt`
(the size bookkeeping of `Val`), `Int.natAbs_tdiv` (so that the truncating division by `2^p` is
`|W·a| / 2^p` at the level of `natAbs`) and `buInV_coord` (the disc condition gives a coordinate
bound).  `zipWith` truncates at the minimum of the two lengths, so no hypothesis on `u.length`
is needed: the proof is an induction that steps through the two lists simultaneously.
-/

namespace Work.Resample

open HvdH

/-- One element of the scaling `zipWith`: with `8|W| ≤ 3·2^p` and `|a| ≤ 2^{p+1}`, the truncated
quotient `W·a / 2^p` has at most `p+1` bits, so `isz ≤ p+3`. -/
private theorem isz_tdiv_mul_le {p : ℕ} {W a : ℤ} (hW : 8 * W.natAbs ≤ 3 * 2 ^ p)
    (ha : a.natAbs ≤ 2 ^ (p + 1)) : isz (Int.tdiv (W * a) ((2 : ℤ) ^ p)) ≤ p + 3 := by
  -- `8|W| ≤ 3·2^p < 8·2^p` gives the *strict* bound `|W| < 2^p`
  have hWlt : W.natAbs < 2 ^ p := by
    have h1 : 8 * W.natAbs < 8 * 2 ^ p :=
      lt_of_le_of_lt hW (Nat.mul_lt_mul_of_pos_right (by norm_num) (Nat.two_pow_pos p))
    exact Nat.lt_of_mul_lt_mul_left h1
  have hmul : (W * a).natAbs < 2 ^ p * 2 ^ (p + 1) := by
    rw [Int.natAbs_mul]
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ ha)
      (Nat.mul_lt_mul_of_pos_right hWlt (Nat.two_pow_pos (p + 1)))
  -- truncating division is `natAbs`-wise natural division by `2^p`
  have hnat : (Int.tdiv (W * a) ((2 : ℤ) ^ p)).natAbs = (W * a).natAbs / 2 ^ p := by
    rw [Int.natAbs_tdiv, Int.natAbs_pow]
    norm_num
    rfl
  have hlt : (Int.tdiv (W * a) ((2 : ℤ) ^ p)).natAbs < 2 ^ (p + 1) := by
    rw [hnat]
    exact Nat.div_lt_of_lt_mul hmul
  have := Work.Fx.isz_le_of_natAbs_lt (a := Int.tdiv (W * a) ((2 : ℤ) ^ p)) (n := p + 1) hlt
  omega

/-- The size bound of a single produced value (as a `cons` of two integers). -/
private theorem vsz_buScProd_le {p : ℕ} {W a b : ℤ} (hW : 8 * W.natAbs ≤ 3 * 2 ^ p)
    (ha : a.natAbs ≤ 2 ^ (p + 1)) (hb : b.natAbs ≤ 2 ^ (p + 1)) :
    vsz (buScProd ((2 : ℤ) ^ p) (.int W) (.cons (.int a) (.int b))) ≤ buScB p := by
  rw [buScProd_apply, Work.Fx.vsz_cons, Work.Fx.vsz_int, Work.Fx.vsz_int]
  have h1 := isz_tdiv_mul_le (p := p) hW ha
  have h2 := isz_tdiv_mul_le (p := p) hW hb
  simp only [buScB] at *
  omega

/-- The same bound for a fixed-point pair wrapped in `cfxVal`, the shape in which the pairs of the
`zipWith` occur. -/
private theorem vsz_buScProd_cfxVal_le {p : ℕ} {W : ℤ} {z : ℤ × ℤ}
    (hW : 8 * W.natAbs ≤ 3 * 2 ^ p)
    (hz1 : z.1.natAbs ≤ 2 ^ (p + 1)) (hz2 : z.2.natAbs ≤ 2 ^ (p + 1)) :
    vsz (buScProd ((2 : ℤ) ^ p) (.int W) (cfxVal z)) ≤ buScB p := by
  have h := vsz_buScProd_le (p := p) (a := z.1) (b := z.2) hW hz1 hz2
  simpa [cfxVal] using h

/-- The `zipWith` of a list of weights with a list of fixed-point pairs, under a weight bound and a
coordinate bound: every entry of the result has `vsz ≤ buScB p`.  Since `zipWith` truncates, the
two lists are stepped through simultaneously (both cut at their minimum length). -/
private theorem zipWith_buScProd_le (p : ℕ) :
    ∀ (A : List ℤ) (B : List (ℤ × ℤ)),
      (∀ W ∈ A, 8 * W.natAbs ≤ 3 * 2 ^ p) →
      (∀ z ∈ B, z.1.natAbs ≤ 2 ^ (p + 1) ∧ z.2.natAbs ≤ 2 ^ (p + 1)) →
      ∀ x ∈ List.zipWith (buScProd ((2 : ℤ) ^ p)) (A.map Val.int) (B.map cfxVal),
        vsz x ≤ buScB p := by
  intro A
  induction A with
  | nil => intro B _ _ x hx; simp at hx
  | cons a as ih =>
      intro B hA hB x hx
      cases B with
      | nil => simp at hx
      | cons b bs =>
          simp only [List.map_cons, List.zipWith_cons_cons, List.mem_cons] at hx
          rcases hx with hx | hx
          · subst hx
            obtain ⟨hb1, hb2⟩ := hB b (by simp)
            exact vsz_buScProd_cfxVal_le (p := p) (hA a (by simp)) hb1 hb2
          · exact ih bs (fun W hW => hA W (List.mem_cons_of_mem a hW))
              (fun z hz => hB z (List.mem_cons_of_mem b hz)) x hx

theorem buScProdSz (p α s t : ℕ) (u : List (ℤ × ℤ))
    (hwd : ∀ ℓ : ℤ, 8 * (Work.Resample.buWd p α s t ℓ).natAbs ≤ 3 * 2 ^ p)
    (hVu : Work.Resample.buInV (2 ^ (p + 1)) u) :
    ∀ x ∈ List.zipWith (Work.Resample.buScProd ((2 : ℤ) ^ p))
        ((List.ofFn (fun i : Fin s => Work.Resample.buWd p α s t (i : ℤ))).map HvdH.Val.int)
        (u.map HvdH.cfxVal),
      HvdH.vsz x ≤ Work.Resample.buScB p := by
  refine zipWith_buScProd_le p
    (List.ofFn fun i : Fin s => Work.Resample.buWd p α s t (i : ℤ)) u ?_ ?_
  · intro W hW
    rw [List.mem_ofFn] at hW
    obtain ⟨i, rfl⟩ := hW
    exact hwd (i : ℤ)
  · intro z hz
    exact buInV_coord hVu hz

end Work.Resample
