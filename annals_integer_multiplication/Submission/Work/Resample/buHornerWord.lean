import Mathlib
import Submission.Work.Resample.buHornerKit
import Submission.Work.Resample.buHornerPrePipe
import Submission.Work.Resample.buHornerCostBound

/-!
# The Horner word `Work.Resample.buHornerWord`

A program computing the fixed-point Horner recursion `auH p Z (auNstep p)` (paper Lemma 4.9)
from the value stack `[Z, p]`, in time `K * (p+1)^K`.

The program is a three-phase chain:

* a pre-loop phase (`Work.Resample.buHornerPrePipe`) that pushes the working scale
  `E = 2^{auPrec p}`, the counter `auNstep p` and a second copy of `E`;
* the Horner loop (`Work.Resample.buHornerLoopPipe`): the invariant is
  `[Q, d, E, Z, p] ++ rest` with `Q = auH p Z i` and `d = auNstep p - i`; one round
  performs `Q ↦ E + ⌊⌊Z·Q/E⌋/d⌋` and `d ↦ d - 1`, and pushes `0` when `d - 1 = 0`
  (so the loop stops exactly at `i = auNstep p`);
* a final clean-up phase (`Work.Resample.buHornerFinPipe`) that drops the flag, the counter
  and `E` and leaves `[auH p Z (auNstep p), Z, p] ++ rest`.

The stack shuffling of one loop round is the lemma `buHornerBodyPipe` below; the recursion
arithmetic is `auH_succ_eq` (`buHornerKit`).  Costs are accounted for with the uniform step
bound `buHSB p KS` and absorbed into `K * (p+1)^K` by `buHornerCostBound` and `pow_mul_le`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH

/-! ## Small helpers -/

theorem one_le_buSZ (p : ℕ) : 1 ≤ buSZ p := by simp only [buSZ]; omega

theorem vsz_memHW_le2 {p : ℕ} {a b : ℤ} (ha : isz a ≤ buSZ p) (hb : isz b ≤ buSZ p) :
    ∀ v ∈ ([Val.int a, Val.int b] : List Val), vsz v ≤ buSZ p := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with h | h
  · rw [h]; exact vsz_int_le_buSZ ha
  · rw [h]; exact vsz_int_le_buSZ hb

theorem vsz_memHW_le3 {p : ℕ} {a b c : ℤ} (ha : isz a ≤ buSZ p) (hb : isz b ≤ buSZ p)
    (hc : isz c ≤ buSZ p) :
    ∀ v ∈ ([Val.int a, Val.int b, Val.int c] : List Val), vsz v ≤ buSZ p := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with h | h | h
  · rw [h]; exact vsz_int_le_buSZ ha
  · rw [h]; exact vsz_int_le_buSZ hb
  · rw [h]; exact vsz_int_le_buSZ hc

theorem vsz_memHW_le4 {p : ℕ} {a b c d : ℤ} (ha : isz a ≤ buSZ p) (hb : isz b ≤ buSZ p)
    (hc : isz c ≤ buSZ p) (hd : isz d ≤ buSZ p) :
    ∀ v ∈ ([Val.int a, Val.int b, Val.int c, Val.int d] : List Val), vsz v ≤ buSZ p := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with h | h | h | h
  · rw [h]; exact vsz_int_le_buSZ ha
  · rw [h]; exact vsz_int_le_buSZ hb
  · rw [h]; exact vsz_int_le_buSZ hc
  · rw [h]; exact vsz_int_le_buSZ hd

theorem vsz_memHW_le5 {p : ℕ} {a b c d e : ℤ} (ha : isz a ≤ buSZ p) (hb : isz b ≤ buSZ p)
    (hc : isz c ≤ buSZ p) (hd : isz d ≤ buSZ p) (he : isz e ≤ buSZ p) :
    ∀ v ∈ ([Val.int a, Val.int b, Val.int c, Val.int d, Val.int e] : List Val),
      vsz v ≤ buSZ p := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with h | h | h | h | h
  · rw [h]; exact vsz_int_le_buSZ ha
  · rw [h]; exact vsz_int_le_buSZ hb
  · rw [h]; exact vsz_int_le_buSZ hc
  · rw [h]; exact vsz_int_le_buSZ hd
  · rw [h]; exact vsz_int_le_buSZ he

theorem vsz_memHW_le6 {p : ℕ} {a b c d e f : ℤ} (ha : isz a ≤ buSZ p) (hb : isz b ≤ buSZ p)
    (hc : isz c ≤ buSZ p) (hd : isz d ≤ buSZ p) (he : isz e ≤ buSZ p) (hf : isz f ≤ buSZ p) :
    ∀ v ∈ ([Val.int a, Val.int b, Val.int c, Val.int d, Val.int e, Val.int f] : List Val),
      vsz v ≤ buSZ p := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with h | h | h | h | h | h
  · rw [h]; exact vsz_int_le_buSZ ha
  · rw [h]; exact vsz_int_le_buSZ hb
  · rw [h]; exact vsz_int_le_buSZ hc
  · rw [h]; exact vsz_int_le_buSZ hd
  · rw [h]; exact vsz_int_le_buSZ he
  · rw [h]; exact vsz_int_le_buSZ hf

/-! ## One round of the Horner loop -/

/-- The body of the Horner loop: from `[Q, d, E, Z, p]` it computes
`Q' = E + ⌊⌊Z·Q/E⌋/d⌋`, replaces the counter `d` by `d - 1` and pushes the continuation
flag `if 0 < d - 1 then 1 else 0`. -/
def buHornerBody (pick rollP : ℕ → Cmd) (push : Val → Cmd)
    (mul add sub tdiv lt swap drop : Cmd) : Cmd :=
  .seq (pick 3) (.seq mul (.seq (pick 2) (.seq swap (.seq tdiv (.seq (pick 1) (.seq swap
    (.seq tdiv (.seq (pick 2) (.seq add (.seq (rollP 1) (.seq (push (.int 1)) (.seq swap
    (.seq sub (.seq (pick 0) (.seq (push (.int 0)) (.seq lt (.seq (rollP 2)
    swap)))))))))))))))))

theorem buHornerBodyPipe {main : Cmd} {pick rollP : ℕ → Cmd} {push : Val → Cmd}
    {mul add sub tdiv lt swap drop : Cmd}
    {Kpick Kroll Kpush Kmul Kadd Ksub Ktdiv Klt Kswap Kdrop KS : ℕ}
    (hPick : ∀ m : Cmd, ∀ k : ℕ, WordR m (pick k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => Kpick * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hRoll : ∀ m : Cmd, ∀ k : ℕ, WordR m (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kroll * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hPush : ∀ (m : Cmd) (v : Val), WordR m (push v) (fun _ => True)
      (fun vs out => out = v :: vs) (fun _ => Kpush * (vsz v + 1)))
    (hMul : BinOp main mul (fun _ _ => True) (· * ·) (fun a b => Kmul * isz a * isz b))
    (hAdd : BinOp main add (fun _ _ => True) (· + ·) (fun a b => Kadd * (isz a + isz b)))
    (hSub : BinOp main sub (fun _ _ => True) (· - ·) (fun a b => Ksub * (isz a + isz b)))
    (hTdiv : BinOp main tdiv (fun _ b => b ≠ 0) Int.tdiv (fun a b => Ktdiv * isz a * isz b))
    (hLt : BinOp main lt (fun _ _ => True) (fun a b => if a < b then 1 else 0)
      (fun a b => Klt * (isz a + isz b)))
    (hSwap : ∀ m : Cmd, WordR m swap (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Kswap * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (hDrop : ∀ m : Cmd, WordR m drop (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => Kdrop * (vsz (vs.headD .nil) + 1)))
    (hKpick : Kpick ≤ KS) (hKroll : Kroll ≤ KS) (hKpush : Kpush ≤ KS) (hKmul : Kmul ≤ KS)
    (hKadd : Kadd ≤ KS) (hKsub : Ksub ≤ KS) (hKtdiv : Ktdiv ≤ KS) (hKlt : Klt ≤ KS)
    (hKswap : Kswap ≤ KS) (hKdrop : Kdrop ≤ KS)
    {p : ℕ} {Q d E Z pv : ℤ}
    (hQ : isz Q ≤ buSZ p) (hd : isz d ≤ buSZ p) (hE : isz E ≤ buSZ p) (hZ : isz Z ≤ buSZ p)
    (hpv : isz pv ≤ buSZ p)
    (hv1 : isz (Z * Q) ≤ buSZ p) (hv2 : isz (Int.tdiv (Z * Q) E) ≤ buSZ p)
    (hv3 : isz (Int.tdiv (Int.tdiv (Z * Q) E) d) ≤ buSZ p)
    (hv4 : isz (E + Int.tdiv (Int.tdiv (Z * Q) E) d) ≤ buSZ p)
    (hE0 : E ≠ 0) (hd1 : 1 ≤ d) :
    Pipe main (buHornerBody pick rollP push mul add sub tdiv lt swap drop)
      [.int Q, .int d, .int E, .int Z, .int pv]
      [.int (if (0 : ℤ) < d - 1 then 1 else 0), .int (E + Int.tdiv (Int.tdiv (Z * Q) E) d),
        .int (d - 1), .int E, .int Z, .int pv]
      (19 * buHSB p KS) := by
  have h0 : isz (0 : ℤ) ≤ buSZ p := isz_zero_le_buSZ p
  have h1 : isz (1 : ℤ) ≤ buSZ p := isz_one_le_buSZ p
  have h5 : isz (d - 1) ≤ buSZ p := isz_sub_one_le_buSZ hd1 hd
  have hfl : isz (if (0 : ℤ) < d - 1 then (1 : ℤ) else 0) ≤ buSZ p := isz_flag_le_buSZ
  have hdne : d ≠ 0 := by omega
  have s1 : Pipe main (pick 3) [.int Q, .int d, .int E, .int Z, .int pv]
      [.int Z, .int Q, .int d, .int E, .int Z, .int pv] (buHSB p KS) :=
    Pipe.le (Pipe.pickAt main hPick (A := [.int Q, .int d, .int E, .int Z, .int pv]) (k := 3)
      (by simp) (v := .int Z) (rfl))
      (le_buSB_roll hKpick (by simp) (by simp) (vsz_memHW_le5 hQ hd hE hZ hpv))
  have s2 : Pipe main mul [.int Z, .int Q, .int d, .int E, .int Z, .int pv]
      [.int (Z * Q), .int d, .int E, .int Z, .int pv] (buHSB p KS) :=
    Pipe.le (Pipe.appendTail [.int d, .int E, .int Z, .int pv]
      (Pipe.binOp hMul (a := Z) (b := Q) trivial)) (le_buSB_mul hKmul hZ hQ)
  have s3 : Pipe main (pick 2) [.int (Z * Q), .int d, .int E, .int Z, .int pv]
      [.int E, .int (Z * Q), .int d, .int E, .int Z, .int pv] (buHSB p KS) :=
    Pipe.le (Pipe.pickAt main hPick (A := [.int (Z * Q), .int d, .int E, .int Z, .int pv])
      (k := 2) (by simp) (v := .int E) (rfl))
      (le_buSB_roll hKpick (by simp) (by simp) (vsz_memHW_le5 hv1 hd hE hZ hpv))
  have s4 : Pipe main swap [.int E, .int (Z * Q), .int d, .int E, .int Z, .int pv]
      [.int (Z * Q), .int E, .int d, .int E, .int Z, .int pv] (buHSB p KS) :=
    Pipe.le (Pipe.appendTail [.int d, .int E, .int Z, .int pv]
      (Pipe.swap main hSwap (.int E) (.int (Z * Q))))
      (le_buSB_three hKswap (vsz_int_le_buSZ hE) (vsz_int_le_buSZ hv1) (one_le_buSZ p))
  have s5 : Pipe main tdiv [.int (Z * Q), .int E, .int d, .int E, .int Z, .int pv]
      [.int (Int.tdiv (Z * Q) E), .int d, .int E, .int Z, .int pv] (buHSB p KS) :=
    Pipe.le (Pipe.appendTail [.int d, .int E, .int Z, .int pv]
      (Pipe.binOp hTdiv (a := Z * Q) (b := E) hE0)) (le_buSB_mul hKtdiv hv1 hE)
  have s6 : Pipe main (pick 1) [.int (Int.tdiv (Z * Q) E), .int d, .int E, .int Z, .int pv]
      [.int d, .int (Int.tdiv (Z * Q) E), .int d, .int E, .int Z, .int pv] (buHSB p KS) :=
    Pipe.le (Pipe.pickAt main hPick
      (A := [.int (Int.tdiv (Z * Q) E), .int d, .int E, .int Z, .int pv]) (k := 1) (by simp)
      (v := .int d) (rfl))
      (le_buSB_roll hKpick (by simp) (by simp) (vsz_memHW_le5 hv2 hd hE hZ hpv))
  have s7 : Pipe main swap [.int d, .int (Int.tdiv (Z * Q) E), .int d, .int E, .int Z, .int pv]
      [.int (Int.tdiv (Z * Q) E), .int d, .int d, .int E, .int Z, .int pv] (buHSB p KS) :=
    Pipe.le (Pipe.appendTail [.int d, .int E, .int Z, .int pv]
      (Pipe.swap main hSwap (.int d) (.int (Int.tdiv (Z * Q) E))))
      (le_buSB_three hKswap (vsz_int_le_buSZ hd) (vsz_int_le_buSZ hv2) (one_le_buSZ p))
  have s8 : Pipe main tdiv
      [.int (Int.tdiv (Z * Q) E), .int d, .int d, .int E, .int Z, .int pv]
      [.int (Int.tdiv (Int.tdiv (Z * Q) E) d), .int d, .int E, .int Z, .int pv] (buHSB p KS) :=
    Pipe.le (Pipe.appendTail [.int d, .int E, .int Z, .int pv]
      (Pipe.binOp hTdiv (a := Int.tdiv (Z * Q) E) (b := d) hdne)) (le_buSB_mul hKtdiv hv2 hd)
  have s9 : Pipe main (pick 2)
      [.int (Int.tdiv (Int.tdiv (Z * Q) E) d), .int d, .int E, .int Z, .int pv]
      [.int E, .int (Int.tdiv (Int.tdiv (Z * Q) E) d), .int d, .int E, .int Z, .int pv]
      (buHSB p KS) :=
    Pipe.le (Pipe.pickAt main hPick
      (A := [.int (Int.tdiv (Int.tdiv (Z * Q) E) d), .int d, .int E, .int Z, .int pv])
      (k := 2) (by simp) (v := .int E) (rfl))
      (le_buSB_roll hKpick (by simp) (by simp) (vsz_memHW_le5 hv3 hd hE hZ hpv))
  have s10 : Pipe main add
      [.int E, .int (Int.tdiv (Int.tdiv (Z * Q) E) d), .int d, .int E, .int Z, .int pv]
      [.int (E + Int.tdiv (Int.tdiv (Z * Q) E) d), .int d, .int E, .int Z, .int pv]
      (buHSB p KS) :=
    Pipe.le (Pipe.appendTail [.int d, .int E, .int Z, .int pv]
      (Pipe.binOp hAdd (a := E) (b := Int.tdiv (Int.tdiv (Z * Q) E) d) trivial))
      (le_buSB_two hKadd hE hv3)
  have s11 : Pipe main (rollP 1)
      [.int (E + Int.tdiv (Int.tdiv (Z * Q) E) d), .int d, .int E, .int Z, .int pv]
      [.int d, .int (E + Int.tdiv (Int.tdiv (Z * Q) E) d), .int E, .int Z, .int pv]
      (buHSB p KS) :=
    Pipe.le (Pipe.roll main hRoll
      (A := [.int (E + Int.tdiv (Int.tdiv (Z * Q) E) d), .int d, .int E, .int Z, .int pv])
      (k := 1) (by simp))
      (le_buSB_roll hKroll (by simp) (by simp) (vsz_memHW_le5 hv4 hd hE hZ hpv))
  have s12 : Pipe main (push (.int 1))
      [.int d, .int (E + Int.tdiv (Int.tdiv (Z * Q) E) d), .int E, .int Z, .int pv]
      [.int 1, .int d, .int (E + Int.tdiv (Int.tdiv (Z * Q) E) d), .int E, .int Z, .int pv]
      (buHSB p KS) :=
    Pipe.le (Pipe.pushOnAny
      (T := [.int d, .int (E + Int.tdiv (Int.tdiv (Z * Q) E) d), .int E, .int Z, .int pv])
      (hPush main (.int 1))) (le_buSB_one hKpush (vsz_int_le_buSZ h1))
  have s13 : Pipe main swap
      [.int 1, .int d, .int (E + Int.tdiv (Int.tdiv (Z * Q) E) d), .int E, .int Z, .int pv]
      [.int d, .int 1, .int (E + Int.tdiv (Int.tdiv (Z * Q) E) d), .int E, .int Z, .int pv]
      (buHSB p KS) :=
    Pipe.le (Pipe.appendTail
      [.int (E + Int.tdiv (Int.tdiv (Z * Q) E) d), .int E, .int Z, .int pv]
      (Pipe.swap main hSwap (.int 1) (.int d)))
      (le_buSB_three hKswap (vsz_int_le_buSZ h1) (vsz_int_le_buSZ hd) (one_le_buSZ p))
  have s14 : Pipe main sub
      [.int d, .int 1, .int (E + Int.tdiv (Int.tdiv (Z * Q) E) d), .int E, .int Z, .int pv]
      [.int (d - 1), .int (E + Int.tdiv (Int.tdiv (Z * Q) E) d), .int E, .int Z, .int pv]
      (buHSB p KS) :=
    Pipe.le (Pipe.appendTail
      [.int (E + Int.tdiv (Int.tdiv (Z * Q) E) d), .int E, .int Z, .int pv]
      (Pipe.binOp hSub (a := d) (b := 1) trivial)) (le_buSB_two hKsub hd h1)
  have s15 : Pipe main (pick 0)
      [.int (d - 1), .int (E + Int.tdiv (Int.tdiv (Z * Q) E) d), .int E, .int Z, .int pv]
      [.int (d - 1), .int (d - 1), .int (E + Int.tdiv (Int.tdiv (Z * Q) E) d), .int E,
        .int Z, .int pv] (buHSB p KS) :=
    Pipe.le (Pipe.pickAt main hPick
      (A := [.int (d - 1), .int (E + Int.tdiv (Int.tdiv (Z * Q) E) d), .int E, .int Z,
        .int pv]) (k := 0) (by simp) (v := .int (d - 1)) (rfl))
      (le_buSB_roll hKpick (by simp) (by simp) (vsz_memHW_le5 h5 hv4 hE hZ hpv))
  have s16 : Pipe main (push (.int 0))
      [.int (d - 1), .int (d - 1), .int (E + Int.tdiv (Int.tdiv (Z * Q) E) d), .int E,
        .int Z, .int pv]
      [.int 0, .int (d - 1), .int (d - 1), .int (E + Int.tdiv (Int.tdiv (Z * Q) E) d),
        .int E, .int Z, .int pv] (buHSB p KS) :=
    Pipe.le (Pipe.pushOnAny
      (T := [.int (d - 1), .int (d - 1), .int (E + Int.tdiv (Int.tdiv (Z * Q) E) d),
        .int E, .int Z, .int pv]) (hPush main (.int 0)))
      (le_buSB_one hKpush (vsz_int_le_buSZ h0))
  have s17 : Pipe main lt
      [.int 0, .int (d - 1), .int (d - 1), .int (E + Int.tdiv (Int.tdiv (Z * Q) E) d),
        .int E, .int Z, .int pv]
      [.int (if (0 : ℤ) < d - 1 then 1 else 0), .int (d - 1),
        .int (E + Int.tdiv (Int.tdiv (Z * Q) E) d), .int E, .int Z, .int pv] (buHSB p KS) :=
    Pipe.le (Pipe.appendTail
      [.int (d - 1), .int (E + Int.tdiv (Int.tdiv (Z * Q) E) d), .int E, .int Z, .int pv]
      (Pipe.binOp hLt (a := (0 : ℤ)) (b := d - 1) trivial)) (le_buSB_two hKlt h0 h5)
  have s18 : Pipe main (rollP 2)
      [.int (if (0 : ℤ) < d - 1 then 1 else 0), .int (d - 1),
        .int (E + Int.tdiv (Int.tdiv (Z * Q) E) d), .int E, .int Z, .int pv]
      [.int (E + Int.tdiv (Int.tdiv (Z * Q) E) d),
        .int (if (0 : ℤ) < d - 1 then 1 else 0), .int (d - 1), .int E, .int Z, .int pv]
      (buHSB p KS) :=
    Pipe.le (Pipe.roll main hRoll
      (A := [.int (if (0 : ℤ) < d - 1 then 1 else 0), .int (d - 1),
        .int (E + Int.tdiv (Int.tdiv (Z * Q) E) d), .int E, .int Z, .int pv]) (k := 2)
      (by simp))
      (le_buSB_roll hKroll (by simp) (by simp) (vsz_memHW_le6 hfl h5 hv4 hE hZ hpv))
  have s19 : Pipe main swap
      [.int (E + Int.tdiv (Int.tdiv (Z * Q) E) d),
        .int (if (0 : ℤ) < d - 1 then 1 else 0), .int (d - 1), .int E, .int Z, .int pv]
      [.int (if (0 : ℤ) < d - 1 then 1 else 0),
        .int (E + Int.tdiv (Int.tdiv (Z * Q) E) d), .int (d - 1), .int E, .int Z, .int pv]
      (buHSB p KS) :=
    Pipe.le (Pipe.appendTail [.int (d - 1), .int E, .int Z, .int pv]
      (Pipe.swap main hSwap (.int (E + Int.tdiv (Int.tdiv (Z * Q) E) d))
        (.int (if (0 : ℤ) < d - 1 then 1 else 0))))
      (le_buSB_three hKswap (vsz_int_le_buSZ hv4) (vsz_int_le_buSZ hfl) (one_le_buSZ p))
  have g18 := Pipe.comp s18 s19
  have g17 := Pipe.comp s17 g18
  have g16 := Pipe.comp s16 g17
  have g15 := Pipe.comp s15 g16
  have g14 := Pipe.comp s14 g15
  have g13 := Pipe.comp s13 g14
  have g12 := Pipe.comp s12 g13
  have g11 := Pipe.comp s11 g12
  have g10 := Pipe.comp s10 g11
  have g9 := Pipe.comp s9 g10
  have g8 := Pipe.comp s8 g9
  have g7 := Pipe.comp s7 g8
  have g6 := Pipe.comp s6 g7
  have g5 := Pipe.comp s5 g6
  have g4 := Pipe.comp s4 g5
  have g3 := Pipe.comp s3 g4
  have g2 := Pipe.comp s2 g3
  have g1 := Pipe.comp s1 g2
  exact Pipe.le g1 (by omega)

theorem buSB_le (p KS : ℕ) (hp : 100 ≤ p) : buHSB p KS ≤ 40000000000 * KS * (p + 1) ^ 4 := by
  have h1 : buSZ p + 8 ≤ 200000 * (p + 1) ^ 2 := by
    simp only [buSZ]
    nlinarith
  calc buHSB p KS = KS * (buSZ p + 8) ^ 2 := rfl
    _ ≤ KS * (200000 * (p + 1) ^ 2) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 2)
    _ = 40000000000 * KS * (p + 1) ^ 4 := by ring_nf

/-! ## The Horner loop -/

theorem buHornerLoopPipe (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (body : Cmd) (KSl Kloop : ℕ),
      ∀ (main : Cmd) (p : ℕ), 100 ≤ p → ∀ (Z : ℤ), Z.natAbs ≤ 2 ^ (11 * p + 210) →
        ∀ rest : List Val, WordR main body
          (fun vs => vs = [.int (auEn p), .int ((auNstep p : ℕ) : ℤ), .int (auEn p), .int Z,
              .int (p : ℤ)] ++ rest)
          (fun vs out => vs = [.int (auEn p), .int ((auNstep p : ℕ) : ℤ), .int (auEn p), .int Z,
              .int (p : ℤ)] ++ rest ∧
            out = [.int (auH p Z (auNstep p)), .int 0, .int (auEn p), .int Z,
              .int (p : ℤ)] ++ rest)
          (fun _ => (auNstep p + 1) * (19 * buHSB p KSl + Kloop) + Kloop) := by
  obtain ⟨pickProg, Kpick, hPick⟩ := KL.pick
  obtain ⟨rollProg, Kroll, hRoll⟩ := KL.roll
  obtain ⟨pushProg, Kpush, hPush⟩ := KL.pushVal
  obtain ⟨swapProg, Kswap, hSwap⟩ := KL.swap
  obtain ⟨dropProg, Kdrop, hDrop⟩ := KL.drop
  obtain ⟨comb, Kloop, hLoop⟩ := KL.loop
  obtain ⟨mulProg, Kmul, hMul⟩ := IL.mulS
  obtain ⟨addProg, Kadd, hAdd⟩ := IL.add
  obtain ⟨subProg, Ksub, hSub⟩ := IL.sub
  obtain ⟨tdivProg, Ktdiv, hTdiv⟩ := IL.tdiv
  obtain ⟨ltProg, Klt, hLt⟩ := IL.lt
  set KSl : ℕ := Kpick + Kroll + Kpush + Kmul + Kadd + Ksub + Ktdiv + Klt + Kswap + Kdrop + 1
    with hKSl
  have hKpick : Kpick ≤ KSl := by omega
  have hKroll : Kroll ≤ KSl := by omega
  have hKpush : Kpush ≤ KSl := by omega
  have hKmul : Kmul ≤ KSl := by omega
  have hKadd : Kadd ≤ KSl := by omega
  have hKsub : Ksub ≤ KSl := by omega
  have hKtdiv : Ktdiv ≤ KSl := by omega
  have hKlt : Klt ≤ KSl := by omega
  have hKswap : Kswap ≤ KSl := by omega
  have hKdrop : Kdrop ≤ KSl := by omega
  refine ⟨comb (buHornerBody pickProg rollProg pushProg mulProg addProg subProg tdivProg ltProg
      swapProg dropProg), KSl, Kloop, ?_⟩
  intro main p hp Z hZ rest
  intro vs hvs s R hR
  have hpipe : Pipe main (comb (buHornerBody pickProg rollProg pushProg mulProg addProg subProg
      tdivProg ltProg swapProg dropProg))
      [.int (auEn p), .int ((auNstep p : ℕ) : ℤ), .int (auEn p), .int Z, .int (p : ℤ)]
      [.int (auH p Z (auNstep p)), .int 0, .int (auEn p), .int Z, .int (p : ℤ)]
      ((auNstep p + 1) * (19 * buHSB p KSl + Kloop) + Kloop) := by
    intro rest2 vs2 hvs2 s2 R2 hR2
    let I : ℕ → List Val → Prop := fun i vs => i < auNstep p ∧ ∃ Q : ℤ,
        vs = [.int Q, .int (((auNstep p - i : ℕ) : ℤ)), .int (auEn p), .int Z,
          .int (p : ℤ)] ++ rest2 ∧
        Q = auH p Z i
    let F : List Val → Prop := fun out => ∃ Q : ℤ,
        out = [.int Q, .int 0, .int (auEn p), .int Z, .int (p : ℤ)] ++ rest2 ∧
        Q = auH p Z (auNstep p)
    have hbody : ∀ i vs, I i vs → WordR main (buHornerBody pickProg rollProg pushProg mulProg
        addProg subProg tdivProg ltProg swapProg dropProg) (fun w => w = vs)
        (fun _ out => ∃ vs', (out = .int 0 :: vs' ∧ F vs') ∨
          (out = .int 1 :: vs' ∧ I (i + 1) vs' ∧ i + 1 < auNstep p))
        (fun _ => 19 * buHSB p KSl) := by
      intro i vs hI
      obtain ⟨hiN, Q, hvsI, hQI⟩ := hI
      have hszQ : isz Q ≤ buSZ p := by
        rw [hQI]
        exact isz_auH_le_buSZ p Z i hp hZ (le_of_lt hiN)
      have hszd : isz ((((auNstep p - i : ℕ)) : ℤ)) ≤ buSZ p := isz_Ns_sub_le_buSZ p i
      have hszE : isz (auEn p) ≤ buSZ p := isz_auEn_le_buSZ p
      have hszZ : isz Z ≤ buSZ p := isz_Z_le_buSZ hZ
      have hszp : isz ((p : ℤ)) ≤ buSZ p := isz_p_le_buSZ_HK p
      have hE0 : auEn p ≠ 0 := by rw [auEn]; positivity
      have hd1 : 1 ≤ ((((auNstep p - i : ℕ)) : ℤ)) := by
        have h1 : 1 ≤ auNstep p - i := by omega
        exact_mod_cast h1
      have hv1 : isz (Z * Q) ≤ buSZ p := by
        rw [hQI]
        exact isz_mul_auH_le p hp Z hZ i (le_of_lt hiN)
      have hv2 : isz (Int.tdiv (Z * Q) (auEn p)) ≤ buSZ p := isz_tdiv_le_buSZ hv1
      have hv3 : isz (Int.tdiv (Int.tdiv (Z * Q) (auEn p))
          ((((auNstep p - i : ℕ)) : ℤ))) ≤ buSZ p := isz_tdiv_le_buSZ hv2
      have hv4eq : auEn p + Int.tdiv (Int.tdiv (Z * Q) (auEn p))
          ((((auNstep p - i : ℕ)) : ℤ)) = auH p Z (i + 1) := by
        rw [hQI]
        exact (auH_succ_eq p Z i (le_of_lt hiN)).symm
      have hv4 : isz (auEn p + Int.tdiv (Int.tdiv (Z * Q) (auEn p))
          ((((auNstep p - i : ℕ)) : ℤ))) ≤ buSZ p := by
        rw [hv4eq]
        exact isz_auH_le_buSZ p Z (i + 1) hp hZ (by omega)
      have hpipe2 := buHornerBodyPipe (main := main) (pick := pickProg) (rollP := rollProg)
        (push := pushProg) (mul := mulProg) (add := addProg) (sub := subProg) (tdiv := tdivProg)
        (lt := ltProg) (swap := swapProg) (drop := dropProg) (KS := KSl)
        hPick hRoll hPush (hMul main) (hAdd main) (hSub main) (hTdiv main) (hLt main)
        hSwap hDrop
        hKpick hKroll hKpush hKmul hKadd hKsub hKtdiv hKlt hKswap hKdrop
        (p := p) (Q := Q) (d := (((auNstep p - i : ℕ)) : ℤ)) (E := auEn p) (Z := Z)
        (pv := (p : ℤ)) hszQ hszd hszE hszZ hszp hv1 hv2 hv3 hv4 hE0 hd1
      intro w hw s3 R3 hR3
      have hw' : w = [.int Q, .int ((((auNstep p - i : ℕ)) : ℤ)), .int (auEn p), .int Z,
          .int (p : ℤ)] ++ rest2 := by rw [hw, hvsI]
      obtain ⟨out, s'', n, hout, hev, hn, hstk, hoth⟩ := hpipe2 rest2 w hw' s3 R3 hR3
      by_cases hgt : (1 : ℤ) < (((auNstep p - i : ℕ)) : ℤ)
      · have hfl : (if (0 : ℤ) < ((((auNstep p - i : ℕ)) : ℤ)) - 1 then (1 : ℤ) else 0) = 1 := by
          rw [if_pos]; omega
        have hlt : i + 1 < auNstep p := by
          have hc := Ns_sub_cast p i (le_of_lt hiN)
          have h2 : (i : ℤ) + 1 < (auNstep p : ℤ) := by omega
          omega
        refine ⟨out, s'', n, ⟨[.int (auH p Z (i + 1)),
          .int (((auNstep p - (i + 1) : ℕ)) : ℤ), .int (auEn p), .int Z,
          .int (p : ℤ)] ++ rest2, Or.inr ⟨?_, ?_, hlt⟩⟩, hev, hn, hstk, hoth⟩
        · rw [hout, hfl, hv4eq, Ns_sub_succ_cast p i (le_of_lt hlt)]
          rfl
        · exact ⟨hlt, auH p Z (i + 1), rfl, rfl⟩
      · have hle : (((auNstep p - i : ℕ)) : ℤ) ≤ 1 := by omega
        have heq : ((((auNstep p - i : ℕ)) : ℤ)) - 1 = 0 := by omega
        have hfl : (if (0 : ℤ) < ((((auNstep p - i : ℕ)) : ℤ)) - 1 then (1 : ℤ) else 0) = 0 := by
          rw [if_neg]; omega
        have hieq : i + 1 = auNstep p := by
          have hc := Ns_sub_cast p i (le_of_lt hiN)
          have h2 : (auNstep p : ℤ) - (i : ℤ) = 1 := by omega
          omega
        refine ⟨out, s'', n, ⟨[.int (auH p Z (auNstep p)), .int 0, .int (auEn p), .int Z,
          .int (p : ℤ)] ++ rest2, Or.inl ⟨?_, ?_⟩⟩, hev, hn, hstk, hoth⟩
        · rw [hout, hfl, hv4eq, heq, hieq]
          rfl
        · exact ⟨auH p Z (auNstep p), rfl, rfl⟩
    have hI0 : I 0 vs2 := by
      have h0 : (0 : ℕ) < auNstep p := by simp only [auNstep, auPrec]; omega
      refine ⟨h0, auEn p, ?_, rfl⟩
      rw [hvs2]
      simp
    obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ :=
      hLoop main (buHornerBody pickProg rollProg pushProg mulProg addProg subProg tdivProg
        ltProg swapProg dropProg) I F (19 * buHSB p KSl) (auNstep p) hbody vs2 hI0 s2 R2 hR2
    obtain ⟨Q, hQ1, hQ2⟩ := hout
    exact ⟨out, s', n, by rw [hQ1, hQ2], hev, hn, hstk, hoth⟩
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := hpipe rest vs hvs s R hR
  exact ⟨out, s', n, ⟨hvs, hout⟩, hev, hn, hstk, hoth⟩

/-! ## The clean-up word -/

theorem buHornerCleanPipe (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p : ℕ), 100 ≤ p → ∀ (A : ℤ),
      isz A ≤ buSZ p → ∀ (Z : ℤ), Z.natAbs ≤ 2 ^ (11 * p + 210) →
      ∀ rest : List Val, WordR main prog
        (fun vs => vs = [.int A, .int 0, .int (auEn p), .int Z, .int (p : ℤ)] ++ rest)
        (fun vs out => vs = [.int A, .int 0, .int (auEn p), .int Z, .int (p : ℤ)] ++ rest ∧
          out = [.int A] ++ rest)
        (fun _ => K * (p + 1) ^ K) := by
  obtain ⟨rollProg, Kroll, hRoll⟩ := KL.roll
  obtain ⟨dropProg, Kdrop, hDrop⟩ := KL.drop
  set KS : ℕ := Kroll + Kdrop + 1 with hKS
  have hKroll : Kroll ≤ KS := by omega
  have hKdrop : Kdrop ≤ KS := by omega
  set M : ℕ := 10000000000000 * KS + 1000 with hMdef
  refine ⟨.seq (rollProg 4) (.seq dropProg (.seq (rollProg 3) (.seq dropProg
      (.seq (rollProg 2) (.seq dropProg (.seq (rollProg 1) dropProg)))))), 4 * M + 5 + 1, ?_⟩
  intro main p hp A hA Z hZ rest
  intro vs hvs s R hR
  have hszE : isz (auEn p) ≤ buSZ p := isz_auEn_le_buSZ p
  have hszZ : isz Z ≤ buSZ p := isz_Z_le_buSZ hZ
  have hszp : isz ((p : ℤ)) ≤ buSZ p := isz_p_le_buSZ_HK p
  have hsz0 : isz (0 : ℤ) ≤ buSZ p := isz_zero_le_buSZ p
  have hpipe : Pipe main (.seq (rollProg 4) (.seq dropProg (.seq (rollProg 3) (.seq dropProg
      (.seq (rollProg 2) (.seq dropProg (.seq (rollProg 1) dropProg)))))))
      [.int A, .int 0, .int (auEn p), .int Z, .int (p : ℤ)] [.int A] (8 * buHSB p KS) := by
    have t1 : Pipe main (rollProg 4) [.int A, .int 0, .int (auEn p), .int Z, .int (p : ℤ)]
        [.int (p : ℤ), .int A, .int 0, .int (auEn p), .int Z] (buHSB p KS) :=
      Pipe.le (Pipe.roll main hRoll (A := [.int A, .int 0, .int (auEn p), .int Z, .int (p : ℤ)])
        (k := 4) (by simp))
        (le_buSB_roll hKroll (by simp) (by simp) (vsz_memHW_le5 hA hsz0 hszE hszZ hszp))
    have t2 : Pipe main dropProg [.int (p : ℤ), .int A, .int 0, .int (auEn p), .int Z]
        [.int A, .int 0, .int (auEn p), .int Z] (buHSB p KS) :=
      Pipe.le (Pipe.appendTail [.int A, .int 0, .int (auEn p), .int Z]
        (Pipe.drop main hDrop (.int (p : ℤ)))) (le_buSB_one hKdrop (vsz_int_le_buSZ hszp))
    have t3 : Pipe main (rollProg 3) [.int A, .int 0, .int (auEn p), .int Z]
        [.int Z, .int A, .int 0, .int (auEn p)] (buHSB p KS) :=
      Pipe.le (Pipe.roll main hRoll (A := [.int A, .int 0, .int (auEn p), .int Z]) (k := 3)
        (by simp))
        (le_buSB_roll hKroll (by simp) (by simp) (vsz_memHW_le4 hA hsz0 hszE hszZ))
    have t4 : Pipe main dropProg [.int Z, .int A, .int 0, .int (auEn p)] [.int A, .int 0,
        .int (auEn p)] (buHSB p KS) :=
      Pipe.le (Pipe.appendTail [.int A, .int 0, .int (auEn p)]
        (Pipe.drop main hDrop (.int Z))) (le_buSB_one hKdrop (vsz_int_le_buSZ hszZ))
    have t5 : Pipe main (rollProg 2) [.int A, .int 0, .int (auEn p)] [.int (auEn p), .int A,
        .int 0] (buHSB p KS) :=
      Pipe.le (Pipe.roll main hRoll (A := [.int A, .int 0, .int (auEn p)]) (k := 2) (by simp))
        (le_buSB_roll hKroll (by simp) (by simp) (vsz_memHW_le3 hA hsz0 hszE))
    have t6 : Pipe main dropProg [.int (auEn p), .int A, .int 0] [.int A, .int 0] (buHSB p KS) :=
      Pipe.le (Pipe.appendTail [.int A, .int 0] (Pipe.drop main hDrop (.int (auEn p))))
        (le_buSB_one hKdrop (vsz_int_le_buSZ hszE))
    have t7 : Pipe main (rollProg 1) [.int A, .int 0] [.int 0, .int A] (buHSB p KS) :=
      Pipe.le (Pipe.roll main hRoll (A := [.int A, .int 0]) (k := 1) (by simp))
        (le_buSB_roll hKroll (by simp) (by simp) (vsz_memHW_le2 hA hsz0))
    have t8 : Pipe main dropProg [.int 0, .int A] [.int A] (buHSB p KS) :=
      Pipe.le (Pipe.appendTail [.int A] (Pipe.drop main hDrop (.int 0)))
        (le_buSB_one hKdrop (vsz_int_le_buSZ hsz0))
    have w7 := Pipe.comp t7 t8
    have w6 := Pipe.comp t6 w7
    have w5 := Pipe.comp t5 w6
    have w4 := Pipe.comp t4 w5
    have w3 := Pipe.comp t3 w4
    have w2 := Pipe.comp t2 w3
    have w1 := Pipe.comp t1 w2
    exact Pipe.le w1 (by omega)
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := hpipe rest vs hvs s R hR
  refine ⟨out, s', n, ⟨hvs, hout⟩, hev, ?_, hstk, hoth⟩
  have hb : buHSB p KS ≤ 40000000000 * KS * (p + 1) ^ 4 := buSB_le p KS hp
  have hmid : 320000000000 * KS * (p + 1) ^ 4 ≤ 10000000000000 * KS * (p + 1) ^ 5 := by
    have h101 : 320000000000 ≤ 10000000000000 * (p + 1) := by nlinarith
    calc 320000000000 * KS * (p + 1) ^ 4
        = 320000000000 * (KS * (p + 1) ^ 4) := by ring
      _ ≤ (10000000000000 * (p + 1)) * (KS * (p + 1) ^ 4) := Nat.mul_le_mul_right _ h101
      _ = 10000000000000 * KS * (p + 1) ^ 5 := by ring
  have h1 : n ≤ M * (p + 1) ^ 5 := by
    calc n ≤ 8 * buHSB p KS := hn
      _ ≤ 8 * (40000000000 * KS * (p + 1) ^ 4) := Nat.mul_le_mul_left _ hb
      _ = 320000000000 * KS * (p + 1) ^ 4 := by ring
      _ ≤ 10000000000000 * KS * (p + 1) ^ 5 := hmid
      _ ≤ M * (p + 1) ^ 5 := by rw [hMdef]; exact Nat.mul_le_mul_right _ (by omega)
  calc n ≤ M * (p + 1) ^ 5 := h1
    _ ≤ (4 * M + 5 + 1) * (p + 1) ^ (4 * M + 5) := pow_mul_le M 5 p (by omega) (by omega)
    _ ≤ (4 * M + 5 + 1) * (p + 1) ^ (4 * M + 5 + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))

/-! ## Adapter from a one-phase `WordR` to a `Pipe` -/

theorem pipe_of_wordR' {main prog : Cmd} {A B : List Val} {c : ℕ}
    (h : ∀ rest : List Val, WordR main prog (fun vs => vs = A ++ rest)
      (fun vs out => vs = A ++ rest ∧ out = B ++ rest) (fun _ => c)) :
    Pipe main prog A B c := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, ⟨-, hout⟩, hev, hn, hstk, hoth⟩ := h rest vs hvs s R hR
  exact ⟨out, s', n, hout, hev, hn, hstk, hoth⟩

/-! ## The Horner word -/

theorem buHornerWord (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ), 100 ≤ p → ∀ (Z : ℤ),
      Z.natAbs ≤ 2 ^ (11 * p + 210) →
      ∀ rest : List HvdH.Val, HvdH.WordR main prog
        (fun vs => vs = [HvdH.Val.int Z, HvdH.Val.int (p : ℤ)] ++ rest)
        (fun vs out => vs = [HvdH.Val.int Z, HvdH.Val.int (p : ℤ)] ++ rest ∧
          out = [HvdH.Val.int (Work.Resample.auH p Z (Work.Resample.auNstep p))] ++ rest)
        (fun _ => K * (p + 1) ^ K) := by
  obtain ⟨pre, Kpre, hpre⟩ := buHornerPrePipe KL IL
  obtain ⟨lp, KSl, Kloop, hloop⟩ := buHornerLoopPipe KL IL
  obtain ⟨clean, Kfin, hclean⟩ := buHornerCleanPipe KL IL
  set KS : ℕ := 2 * KSl + Kpre + Kfin + Kloop + 1 with hKS
  set e : ℕ := max 5 (max Kpre Kfin) with he
  set M : ℕ := 10000000000000 * KS + 1000 with hM
  have hKS1 : 1 ≤ KS := by omega
  have hKpre : Kpre ≤ KS := by omega
  have hKfin : Kfin ≤ KS := by omega
  have hKloop : Kloop ≤ KS := by omega
  have he1 : Kpre ≤ e := by omega
  have he2 : Kfin ≤ e := by omega
  have he3 : 5 ≤ e := by omega
  refine ⟨.seq pre (.seq lp clean), 4 * M + e + 1, ?_⟩
  intro main p hp Z hZ rest
  have hP1 : Pipe main pre [.int Z, .int (p : ℤ)]
      [.int (auEn p), .int ((auNstep p : ℕ) : ℤ), .int (auEn p), .int Z, .int (p : ℤ)]
      (Kpre * (p + 1) ^ Kpre) := pipe_of_wordR' (hpre main p hp Z hZ)
  have hP2 : Pipe main lp
      [.int (auEn p), .int ((auNstep p : ℕ) : ℤ), .int (auEn p), .int Z, .int (p : ℤ)]
      [.int (auH p Z (auNstep p)), .int 0, .int (auEn p), .int Z, .int (p : ℤ)]
      ((auNstep p + 1) * (19 * buHSB p KSl + Kloop) + Kloop) :=
    pipe_of_wordR' (hloop main p hp Z hZ)
  have hP3 : Pipe main clean
      [.int (auH p Z (auNstep p)), .int 0, .int (auEn p), .int Z, .int (p : ℤ)]
      [.int (auH p Z (auNstep p))] (Kfin * (p + 1) ^ Kfin) :=
    pipe_of_wordR' (hclean main p hp (auH p Z (auNstep p))
      (isz_auH_le_buSZ p Z (auNstep p) hp hZ le_rfl) Z hZ)
  have hP : Pipe main (.seq pre (.seq lp clean)) [.int Z, .int (p : ℤ)]
      [.int (auH p Z (auNstep p))]
      (Kpre * (p + 1) ^ Kpre + (((auNstep p + 1) * (19 * buHSB p KSl + Kloop) + Kloop)
        + Kfin * (p + 1) ^ Kfin)) := Pipe.comp hP1 (Pipe.comp hP2 hP3)
  intro vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := hP rest vs hvs s R hR
  refine ⟨out, s', n, ⟨hvs, hout⟩, hev, ?_, hstk, hoth⟩
  have hc : 19 * buHSB p KSl ≤ 18 * buHSB p KS := by
    have hmono : buHSB p (2 * KSl) ≤ buHSB p KS := buSB_mono (by omega)
    have hdouble : buHSB p (2 * KSl) = 2 * buHSB p KSl := by simp only [buHSB]; ring
    have h36 : 36 * buHSB p KSl ≤ 18 * buHSB p KS := by
      have h1 := Nat.mul_le_mul_left 18 hmono
      rw [hdouble] at h1
      omega
    omega
  have hn' : n ≤ Kpre * (p + 1) ^ Kpre +
      ((auNstep p + 1) * (19 * buHSB p KSl + Kloop) + Kloop) + Kfin * (p + 1) ^ Kfin := by
    have h := hn
    simp only [Nat.add_assoc] at h ⊢
    exact h
  have hcost := buHornerCostBound p KS Kpre Kfin Kloop (19 * buHSB p KSl) e n hp hKS1 hKpre hKfin
    hKloop he1 he2 he3 hc hn'
  calc n ≤ M * (p + 1) ^ e := hcost
    _ ≤ (4 * M + e + 1) * (p + 1) ^ (4 * M + e) := pow_mul_le M e p (by omega) (by omega)
    _ ≤ (4 * M + e + 1) * (p + 1) ^ (4 * M + e + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))

end Work.Resample
