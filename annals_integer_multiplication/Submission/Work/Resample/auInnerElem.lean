import Mathlib
import Submission.Work.Resample.auKit
import Submission.Work.Resample.auSqPhase
import Submission.Work.Resample.auShufflePhase
import Submission.Work.Resample.auCostSum

/-!
# `Work.Resample.auInnerElem`: the inner element word of the resampling table

Given the weight word `wtProg` (spec `wtSpec`: `[p, α, t, N, auPi p] ↦ int (auWt p α t N)`), this
file builds the word that turns the window

`[cons (int i) (int (auPi p)), int C, int t, int p, int α]`

into

`[int (auWt p α t ((C + t·i)²)), int C, int t, int p, int α]`,

i.e. it splits the labelled window element `cons (int i) (int (auPi p))`, computes
`N = (C + t·i)²` with the schoolbook product (`IntLib.mulS`/`add`), rearranges the stack to the input
window `[p, α, t, N, auPi p]` of the weight word (with a backup copy of `C, t, p, α` underneath),
runs the weight word and finally drops the consumed copies.

The word is the composition of four `Pipe`s: `unconsV` (a `KernelLib` primitive), the square phase
`auSqPhase`, the shuffle `auShufflePhase`, and the weight word itself.  The cost is the sum of the
four, absorbed into a single `K * (p+1)^K` by `auCostSum`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH
open Work.Fx

/-! ## Two `Pipe` adapters -/

/-- `KernelLib.unconsV` as a `Pipe` on a one-value window. -/
theorem Pipe.unconsV {main prog : Cmd} {K : ℕ}
    (h : ∀ m : Cmd, WordR m prog (fun vs => ∃ a b rest, vs = .cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest) (fun _ => K))
    (a b : Val) : Pipe main prog [.cons a b] [a, b] K := by
  intro rest vs hvs s R hR
  have hv : vs = .cons a b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs ⟨a, b, rest, hv⟩ s R hR
  have hh : Val.cons a' b' = Val.cons a b := (List.cons.inj (hvs'.symm.trans hv)).1
  have ht : rest' = rest := (List.cons.inj (hvs'.symm.trans hv)).2
  have h1 : a' = a := (Val.cons.inj hh).1
  have h2 : b' = b := (Val.cons.inj hh).2
  exact ⟨out, s', n, by rw [hout, h1, h2, ht]; rfl, hev, hn, hstk, hoth⟩

/-- A `WordR` whose pre/post are the `∃ rest` forms of a fixed-window transformation is a `Pipe`. -/
theorem Pipe.ofWordR_auInnerElem {main prog : Cmd} {A B : List Val} {c : ℕ}
    (h : WordR main prog (fun vs => ∃ rest, vs = A ++ rest)
      (fun vs out => ∃ rest, vs = A ++ rest ∧ out = B ++ rest) (fun _ => c)) :
    Pipe main prog A B c := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, ⟨rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ := h vs ⟨rest, hvs⟩ s R hR
  have hrest : rest' = rest := List.append_cancel_left (by rw [← hvs', hvs])
  exact ⟨out, s', n, by rw [hout, hrest], hev, hn, hstk, hoth⟩

/-! ## Size helpers -/

/-- `isz p ≤ auSZ p` for the precision exponent itself. -/
theorem isz_self_le {p : ℕ} : isz ((p : ℤ)) ≤ auSZ p := by
  have h1 : p < 2 ^ (p + 1) := by
    calc p < 2 ^ p := Nat.lt_two_pow_self
      _ ≤ 2 ^ (p + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : p.size ≤ p + 1 := Nat.size_le.mpr h1
  simp only [isz, Int.natAbs_natCast, auSZ]
  omega

/-- `isz z ≤ auSZ p` for `0 ≤ z ≤ 2^(4p+8)` (the size of the squared numerator `N`). -/
theorem isz_le_auSZ_of_le {p : ℕ} {z : ℤ} (h0 : 0 ≤ z) (h : z ≤ (2 : ℤ) ^ (4 * p + 8)) :
    isz z ≤ auSZ p := by
  have hA : z.natAbs ≤ 2 ^ (4 * p + 8) := by
    have h' : ((z.natAbs : ℕ) : ℤ) ≤ ((2 ^ (4 * p + 8) : ℕ) : ℤ) := by
      rw [Int.natAbs_of_nonneg h0]
      push_cast
      exact h
    exact_mod_cast h'
  have hB : z.natAbs < 2 ^ (4 * p + 9) :=
    lt_of_le_of_lt hA (Nat.pow_lt_pow_right one_lt_two (by omega))
  have hC : (z.natAbs).size ≤ 4 * p + 9 := Nat.size_le.mpr hB
  simp only [isz, auSZ]
  omega

theorem auInnerElem (hk : HvdH.KernelLib) (hi : HvdH.IntLib) (wtProg : HvdH.Cmd) (Kw : ℕ)
    (wtSpec : ∀ (main : HvdH.Cmd) (p α t : ℕ) (N : ℤ), (0 ≤ N) → (N ≤ (2 : ℤ) ^ (4 * p + 8)) →
      (1 ≤ t) → (t < 2 ^ p) → (α ≤ 2 ^ p) → HvdH.WordR main wtProg
        (fun vs => ∃ rest, vs = [HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ), HvdH.Val.int (t : ℤ),
          HvdH.Val.int N, HvdH.Val.int (Work.Resample.auPi p)] ++ rest)
        (fun vs out => ∃ rest, vs = [HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ), HvdH.Val.int (t : ℤ),
          HvdH.Val.int N, HvdH.Val.int (Work.Resample.auPi p)] ++ rest ∧
          out = HvdH.Val.int (Work.Resample.auWt p α t N) :: rest)
        (fun _ => Kw * (p + 1) ^ Kw)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α t : ℕ) (C : ℤ) (i : ℕ),
      HvdH.isz C ≤ Work.Resample.auSZ p → HvdH.isz ((i : ℕ) : ℤ) ≤ Work.Resample.auSZ p →
      (1 ≤ t) → (t < 2 ^ p) → (α ≤ 2 ^ p) →
      (C + (t : ℤ) * (i : ℤ)) ^ 2 ≤ (2 : ℤ) ^ (4 * p + 8) →
      Work.Resample.Pipe main prog
        [HvdH.Val.cons (HvdH.Val.int (i : ℤ)) (HvdH.Val.int (Work.Resample.auPi p)),
          HvdH.Val.int C, HvdH.Val.int (t : ℤ), HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ)]
        [HvdH.Val.int (Work.Resample.auWt p α t ((C + (t : ℤ) * (i : ℤ)) ^ 2)),
          HvdH.Val.int C, HvdH.Val.int (t : ℤ), HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ)]
        (K * (p + 1) ^ K) := by
  obtain ⟨ucProg, Kuc, hUc⟩ := hk.unconsV
  obtain ⟨sqProg, Ksq, hSq⟩ := auSqPhase hk hi
  obtain ⟨shProg, Ksh, hSh⟩ := auShufflePhase hk
  refine ⟨Cmd.seq ucProg (Cmd.seq sqProg (Cmd.seq shProg wtProg)),
    2 ^ (Kuc + Ksq + Ksh + Kw + Ksq + Ksh + Kw + 20), ?_⟩
  intro main p α t C i hC hI ht htp hα hNsq
  have hp1 : 1 ≤ p := by
    by_contra h
    have h0 : p = 0 := by omega
    rw [h0] at htp
    simp at htp
    omega
  have hPi : isz (auPi p) ≤ auSZ p := isz_auPi_le p
  have hPp : isz ((p : ℤ)) ≤ auSZ p := isz_self_le
  have hT : isz ((t : ℤ)) ≤ auSZ p := isz_le_pow2 (le_of_lt htp)
  have hA : isz ((α : ℤ)) ≤ auSZ p := isz_le_pow2 hα
  have hNsz : isz ((C + (t : ℤ) * (i : ℤ)) ^ 2) ≤ auSZ p :=
    isz_le_auSZ_of_le (sq_nonneg _) hNsq
  have h1 : Pipe main ucProg [.cons (.int (i : ℤ)) (.int (auPi p))]
      [.int (i : ℤ), .int (auPi p)] Kuc := Pipe.unconsV hUc _ _
  have h1' := Pipe.appendTail [.int C, .int (t : ℤ), .int (p : ℤ), .int (α : ℤ)] h1
  have h2 := hSq main p α t C (i : ℤ) hp1 hI hC hT hPp hA hPi
  have h3 := hSh main p ((C + (t : ℤ) * (i : ℤ)) ^ 2) (auPi p) C (t : ℤ) (p : ℤ) (α : ℤ)
    hp1 hNsz hPi hC hT hPp hA
  have h4 : Pipe main wtProg
      [.int (p : ℤ), .int (α : ℤ), .int (t : ℤ), .int ((C + (t : ℤ) * (i : ℤ)) ^ 2),
        .int (auPi p)]
      [.int (auWt p α t ((C + (t : ℤ) * (i : ℤ)) ^ 2))] (Kw * (p + 1) ^ Kw) :=
    Pipe.ofWordR_auInnerElem (wtSpec main p α t ((C + (t : ℤ) * (i : ℤ)) ^ 2) (sq_nonneg _) hNsq ht htp hα)
  have h4' := Pipe.appendTail [.int C, .int (t : ℤ), .int (p : ℤ), .int (α : ℤ)] h4
  refine Pipe.le (Pipe.comp h1' (Pipe.comp h2 (Pipe.comp h3 h4'))) ?_
  exact auCostSum Kuc Ksq Ksh Kw Ksq Ksh Kw p

end Work.Resample
