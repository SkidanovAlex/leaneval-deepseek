import Mathlib
import Submission.Work.Resample.auKit

namespace Work.Resample

open HvdH Computability
open Work.Fx

/-!
# The shuffle phase of the weight word

`auShufflePhase` realises the fixed permutation of the six parameters held in the window
`[N, P, C, T, Q, A]` (top of the value stack first) into the window
`[Q, A, T, N, P, C, T, Q, A]`.

The point is that the last six entries of the target window are again `N, P, C, T, Q, A` in that
order, so nothing has to be deleted: it suffices to *copy* three of the values to the top, namely
`T` (which sits at depth three), then `A` (at depth six), then `Q` (again at depth six).  Three
applications of `KernelLib.pick` with a constant index do the job.

Cost: each `pick k` costs `K·(k+1)·(szl (window.take (k+1)) + 1)`, and in this phase the window
never has more than `8` entries, each of size `≤ auSZ p`; so the total is
`≤ Kp·(114·auSZ p + 18) = Kp·(1140·p + 45618) ≤ K·(p+1)^K` for `K := max Kp 100`.
-/

/-- Cost arithmetic: `(p+1)^K` dominates `1140·p + 45618` as soon as `K ≥ 100` and `p ≥ 1`. -/
theorem lin_le_pow_shuffle (p K : ℕ) (hp : 1 ≤ p) (hK : 100 ≤ K) :
    1140 * p + 45618 ≤ (p + 1) ^ K := by
  have h1 : (p + 1) ^ 100 ≤ (p + 1) ^ K := Nat.pow_le_pow_right (by omega) hK
  have h2 : (2 : ℕ) ^ 99 ≤ (p + 1) ^ 99 := Nat.pow_le_pow_left (by omega) 99
  have h3 : 1140 * p + 45618 ≤ 2 ^ 99 * (p + 1) := by
    have e1 : (1140 : ℕ) ≤ 2 ^ 99 := by norm_num
    have e2 : (45618 : ℕ) ≤ 2 ^ 99 := by norm_num
    nlinarith [e1, e2, hp]
  calc 1140 * p + 45618 ≤ 2 ^ 99 * (p + 1) := h3
    _ ≤ (p + 1) ^ 99 * (p + 1) := Nat.mul_le_mul_right _ h2
    _ = (p + 1) ^ 100 := by rw [← pow_succ]
    _ ≤ (p + 1) ^ K := h1

/-- Copy the value at depth `k` of a window whose entries are all bounded by `auSZ p`.  The cost of
`KernelLib.pick` is bounded by `Kp·(k+1)·(M·auSZ p + 1)` as soon as `k + 1 ≤ M`; this packages the
three `pick` applications of `auShufflePhase`. -/
theorem pipe_pick_le {Kp M k : ℕ} {prog : ℕ → HvdH.Cmd}
    (hpick : ∀ (mm : HvdH.Cmd) (j : ℕ), HvdH.WordR mm (prog j) (fun vs => j < vs.length)
      (fun vs out => out = vs.getD j .nil :: vs)
      (fun vs => Kp * (j + 1) * (((vs.take (j + 1)).map HvdH.vsz).sum + 1)))
    (main : HvdH.Cmd) {p : ℕ} {A : List Val}
    (hAmem : ∀ v ∈ A, vsz v ≤ auSZ p) (hk : k < A.length) (hM : k + 1 ≤ M) :
    Pipe main (prog k) A (A.getD k .nil :: A) (Kp * (k + 1) * (M * auSZ p + 1)) := by
  refine Pipe.le (Pipe.pick main hpick hk) ?_
  have hsz : szl (A.take (k + 1)) ≤ M * auSZ p := by
    refine le_trans (szl_le_of_mem ?_) (Nat.mul_le_mul_right _ ?_)
    · intro v hv
      exact hAmem v (List.mem_of_mem_take hv)
    · rw [List.length_take]
      omega
  exact Nat.mul_le_mul_left _ (by omega)

theorem auShufflePhase (hk : HvdH.KernelLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (N P C T Q A : ℤ),
      (1 ≤ p) →
      HvdH.isz N ≤ Work.Resample.auSZ p → HvdH.isz P ≤ Work.Resample.auSZ p →
      HvdH.isz C ≤ Work.Resample.auSZ p → HvdH.isz T ≤ Work.Resample.auSZ p →
      HvdH.isz Q ≤ Work.Resample.auSZ p → HvdH.isz A ≤ Work.Resample.auSZ p →
      Work.Resample.Pipe main prog
        [HvdH.Val.int N, HvdH.Val.int P, HvdH.Val.int C, HvdH.Val.int T, HvdH.Val.int Q,
          HvdH.Val.int A]
        [HvdH.Val.int Q, HvdH.Val.int A, HvdH.Val.int T, HvdH.Val.int N, HvdH.Val.int P,
          HvdH.Val.int C, HvdH.Val.int T, HvdH.Val.int Q, HvdH.Val.int A]
        (K * (p + 1) ^ K) := by
  obtain ⟨pickprog, Kp, hpick⟩ := hk.pick
  refine ⟨.seq (pickprog 3) (.seq (pickprog 6) (pickprog 6)), max Kp 100, ?_⟩
  intro main p N P C T Q A hp hN hP hC hT hQ hA
  -- size bounds on the individual values
  have szN : vsz (Val.int N) ≤ auSZ p := by rw [vsz_int]; exact hN
  have szP : vsz (Val.int P) ≤ auSZ p := by rw [vsz_int]; exact hP
  have szC : vsz (Val.int C) ≤ auSZ p := by rw [vsz_int]; exact hC
  have szT : vsz (Val.int T) ≤ auSZ p := by rw [vsz_int]; exact hT
  have szQ : vsz (Val.int Q) ≤ auSZ p := by rw [vsz_int]; exact hQ
  have szA : vsz (Val.int A) ≤ auSZ p := by rw [vsz_int]; exact hA
  -- membership predicates for the three successive windows
  have mem0 : ∀ v ∈ ([Val.int N, Val.int P, Val.int C, Val.int T, Val.int Q, Val.int A] :
      List Val), vsz v ≤ auSZ p := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [szN, szP, szC, szT, szQ, szA]
  have mem1 : ∀ v ∈ ([Val.int T, Val.int N, Val.int P, Val.int C, Val.int T, Val.int Q,
      Val.int A] : List Val), vsz v ≤ auSZ p := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [szT, szN, szP, szC, szT, szQ, szA]
  have mem2 : ∀ v ∈ ([Val.int A, Val.int T, Val.int N, Val.int P, Val.int C, Val.int T,
      Val.int Q, Val.int A] : List Val), vsz v ≤ auSZ p := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [szA, szT, szN, szP, szC, szT, szQ, szA]
  -- the three copy steps
  have h1 : Pipe main (pickprog 3)
      ([Val.int N, Val.int P, Val.int C, Val.int T, Val.int Q, Val.int A] : List Val)
      [Val.int T, Val.int N, Val.int P, Val.int C, Val.int T, Val.int Q, Val.int A]
      (Kp * 4 * (4 * auSZ p + 1)) :=
    pipe_pick_le hpick main mem0 (by simp) (by simp)
  have h2 : Pipe main (pickprog 6)
      ([Val.int T, Val.int N, Val.int P, Val.int C, Val.int T, Val.int Q, Val.int A] : List Val)
      [Val.int A, Val.int T, Val.int N, Val.int P, Val.int C, Val.int T, Val.int Q, Val.int A]
      (Kp * 7 * (7 * auSZ p + 1)) :=
    pipe_pick_le hpick main mem1 (by simp) (by simp)
  have h3 : Pipe main (pickprog 6)
      ([Val.int A, Val.int T, Val.int N, Val.int P, Val.int C, Val.int T, Val.int Q,
        Val.int A] : List Val)
      [Val.int Q, Val.int A, Val.int T, Val.int N, Val.int P, Val.int C, Val.int T, Val.int Q,
        Val.int A]
      (Kp * 7 * (7 * auSZ p + 1)) :=
    pipe_pick_le hpick main mem2 (by simp) (by simp)
  have h12 : Pipe main (.seq (pickprog 3) (.seq (pickprog 6) (pickprog 6)))
      ([Val.int N, Val.int P, Val.int C, Val.int T, Val.int Q, Val.int A] : List Val)
      [Val.int Q, Val.int A, Val.int T, Val.int N, Val.int P, Val.int C, Val.int T, Val.int Q,
        Val.int A]
      (Kp * 4 * (4 * auSZ p + 1) + (Kp * 7 * (7 * auSZ p + 1) + Kp * 7 * (7 * auSZ p + 1))) :=
    Pipe.comp h1 (Pipe.comp h2 h3)
  refine Pipe.le h12 ?_
  have hL : Kp * 4 * (4 * auSZ p + 1) + (Kp * 7 * (7 * auSZ p + 1) + Kp * 7 * (7 * auSZ p + 1))
      = Kp * (1140 * p + 45618) := by
    simp only [auSZ]; ring
  rw [hL]
  calc Kp * (1140 * p + 45618) ≤ Kp * (p + 1) ^ max Kp 100 :=
        Nat.mul_le_mul_left _ (lin_le_pow_shuffle p (max Kp 100) hp (le_max_right _ _))
    _ ≤ max Kp 100 * (p + 1) ^ max Kp 100 := Nat.mul_le_mul_right _ (le_max_left _ _)

end Work.Resample
