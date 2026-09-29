import Mathlib
import Submission.Work.Resample.auKDefs

/-!
# `Work.Resample.auKWord`

The word computing the two window centres `auK s t k` and `auK s t (k+1)`
(`auK s t k = ⌊(2ks+t)/(2t)⌋`) from the three integers `k, s, t`.

The program is a chain of 32 library calls: it builds `2t`, `2s`, `2ks`, then
`A0 = 2ks + t` and `A1 = A0 + 2s`, divides each by `2t`, and drops the three inputs.
Every intermediate value has `isz _ ≤ SZ p` (`Work.Resample.auKSizes`), so every step costs at
most `SB p KS = KS·(SZ p + 8)²` for `KS` the maximum of the library constants; the total
`32·SB p KS` is absorbed into `K·(p+1)^K` by `AuPiKit.SB_le` and `AuPiKit.pow_bound`.
-/

set_option autoImplicit false
set_option maxHeartbeats 50000000

namespace Work.Resample

open HvdH
open Work.Fx
open Work.Resample.AuPiKit

theorem auKWord (hk : HvdH.KernelLib) (hi : HvdH.IntLib) : ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p s t k : ℕ), 100 ≤ p → 1 ≤ t → t < 2 ^ p → s < t → k < t →
    Work.Resample.Pipe main prog
      [HvdH.Val.int (k : ℤ), HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)]
      [HvdH.Val.int ((Work.Resample.auK s t k : ℕ) : ℤ),
        HvdH.Val.int ((Work.Resample.auK s t (k + 1) : ℕ) : ℤ)]
      (K * (p + 1) ^ K) := by
  obtain ⟨pickP, Kpick, hpick⟩ := hk.pick
  obtain ⟨rollP, Kroll, hroll⟩ := hk.roll
  obtain ⟨dupP, Kd, hdup⟩ := hk.dup
  obtain ⟨dropP, Kdr, hdrop⟩ := hk.drop
  obtain ⟨pushP, Kpush, hpush⟩ := hk.pushVal
  obtain ⟨mulP, Km, hmul⟩ := hi.mulS
  obtain ⟨tdivP, Kt, htdiv⟩ := hi.tdiv
  obtain ⟨addP, Ka, hadd⟩ := hi.add
  set KS : ℕ := Kpick + Kroll + Kd + Kdr + Kpush + Km + Kt + Ka + 1 with hKSdef
  have hKpick : Kpick ≤ KS := by omega
  have hKroll : Kroll ≤ KS := by omega
  have hKd : Kd ≤ KS := by omega
  have hKdr : Kdr ≤ KS := by omega
  have hKpush : Kpush ≤ KS := by omega
  have hKm : Km ≤ KS := by omega
  have hKt : Kt ≤ KS := by omega
  have hKa : Ka ≤ KS := by omega
  have hKS1 : 1 ≤ KS := by omega
  refine ⟨(Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (pickP 2) (pushP (HvdH.Val.int ((2 : ℤ))))) mulP) (pickP 2)) (pushP (HvdH.Val.int ((2 : ℤ))))) mulP) (pickP 2)) mulP) (pickP 4)) (rollP 1)) addP) dupP) (rollP 2)) (rollP 1)) tdivP) (pickP 3)) (pushP (HvdH.Val.int ((2 : ℤ))))) mulP) (rollP 2)) addP) (pickP 4)) (pushP (HvdH.Val.int ((2 : ℤ))))) mulP) (rollP 1)) tdivP) (rollP 1)) (rollP 2)) dropP) (rollP 2)) dropP) (rollP 2)) dropP), 4 * (32 * 256 * KS) + 1, ?_⟩
  intro main p s t k hp ht htp hst hkt
  have hp100 : 100 ≤ p := hp
  obtain ⟨hzk, hzs, hzt, hzE, hzP, hzA0, hzD, hzA1, hzQ0, hzQ1⟩ :=
    auKSizes p s t k hp ht htp hst hkt
  have hKZ : isz (k : ℤ) ≤ SZ p := hzk
  have hSZ : isz (s : ℤ) ≤ SZ p := hzs
  have hTZ : isz (t : ℤ) ≤ SZ p := hzt
  have h2 : isz (2 : ℤ) ≤ SZ p := AuPiKit.isz_natCast_le (p := p) (n := 2) (by omega)
  have hE : isz ((2 : ℤ) * (s : ℤ)) ≤ SZ p := by simpa only [kE] using hzE
  have hP : isz ((k : ℤ) * ((2 : ℤ) * (s : ℤ))) ≤ SZ p := by simpa only [kP, kE] using hzP
  have hD : isz ((2 : ℤ) * (t : ℤ)) ≤ SZ p := by simpa only [kD] using hzD
  have hA0 : isz ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ≤ SZ p := by simpa only [kA0, kP, kE] using hzA0
  have hA1 : isz (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ≤ SZ p := by simpa only [kA1, kA0, kP, kE] using hzA1
  have hQ0 : isz (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ))) ≤ SZ p := by simpa only [kQ0, kA0, kP, kE, kD] using hzQ0
  have hQ1 : isz (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ))) ≤ SZ p := by simpa only [kQ1, kA1, kA0, kP, kE, kD] using hzQ1
  have hDne : ((2 : ℤ) * (t : ℤ)) ≠ 0 := by
    have ht0 : (0 : ℤ) < (t : ℤ) := by exact_mod_cast ht
    positivity
  have s1 : Pipe main (pickP 2)
      [ (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    have hp := Pipe.pickAt main hpick (A := [ (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 2) (by simp) (v := (HvdH.Val.int ((t : ℤ)))) (by simp)
    exact Pipe.le (hp)
      (AuPiKit.le_SB_roll hKpick hp100 (A := [ (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 2) (by omega) (by simp) (AuPiKit.vsz_mem_le3 (AuPiKit.vsz_int_le hKZ) (AuPiKit.vsz_int_le hSZ) (AuPiKit.vsz_int_le hTZ)))
  have s2 : Pipe main (pushP (HvdH.Val.int ((2 : ℤ))))
      [ (HvdH.Val.int ((t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((2 : ℤ))), (HvdH.Val.int ((t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    exact Pipe.le (Pipe.pushOnAny (T := [ (HvdH.Val.int ((t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (hpush main (HvdH.Val.int ((2 : ℤ)))))
      (AuPiKit.le_SB_one hKpush (AuPiKit.vsz_int_le h2))
  have s3 : Pipe main mulP
      [ (HvdH.Val.int ((2 : ℤ))), (HvdH.Val.int ((t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    exact Pipe.le (Pipe.appendTail [ (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
        (Pipe.binOp (hmul main) (a := (2 : ℤ)) (b := (t : ℤ)) trivial))
      (le_SB_mul hKm h2 hTZ)
  have s4 : Pipe main (pickP 2)
      [ (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    have hp := Pipe.pickAt main hpick (A := [ (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 2) (by simp) (v := (HvdH.Val.int ((s : ℤ)))) (by simp)
    exact Pipe.le (hp)
      (AuPiKit.le_SB_roll hKpick hp100 (A := [ (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 2) (by omega) (by simp) (AuPiKit.vsz_mem_le4 (AuPiKit.vsz_int_le hD) (AuPiKit.vsz_int_le hKZ) (AuPiKit.vsz_int_le hSZ) (AuPiKit.vsz_int_le hTZ)))
  have s5 : Pipe main (pushP (HvdH.Val.int ((2 : ℤ))))
      [ (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((2 : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    exact Pipe.le (Pipe.pushOnAny (T := [ (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (hpush main (HvdH.Val.int ((2 : ℤ)))))
      (AuPiKit.le_SB_one hKpush (AuPiKit.vsz_int_le h2))
  have s6 : Pipe main mulP
      [ (HvdH.Val.int ((2 : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((2 : ℤ) * (s : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    exact Pipe.le (Pipe.appendTail [ (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
        (Pipe.binOp (hmul main) (a := (2 : ℤ)) (b := (s : ℤ)) trivial))
      (le_SB_mul hKm h2 hSZ)
  have s7 : Pipe main (pickP 2)
      [ (HvdH.Val.int ((2 : ℤ) * (s : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((2 : ℤ) * (s : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    have hp := Pipe.pickAt main hpick (A := [ (HvdH.Val.int ((2 : ℤ) * (s : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 2) (by simp) (v := (HvdH.Val.int ((k : ℤ)))) (by simp)
    exact Pipe.le (hp)
      (AuPiKit.le_SB_roll hKpick hp100 (A := [ (HvdH.Val.int ((2 : ℤ) * (s : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 2) (by omega) (by simp) (AuPiKit.vsz_mem_le5 (AuPiKit.vsz_int_le hE) (AuPiKit.vsz_int_le hD) (AuPiKit.vsz_int_le hKZ) (AuPiKit.vsz_int_le hSZ) (AuPiKit.vsz_int_le hTZ)))
  have s8 : Pipe main mulP
      [ (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((2 : ℤ) * (s : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    exact Pipe.le (Pipe.appendTail [ (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
        (Pipe.binOp (hmul main) (a := (k : ℤ)) (b := (2 : ℤ) * (s : ℤ)) trivial))
      (le_SB_mul hKm hKZ hE)
  have s9 : Pipe main (pickP 4)
      [ (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((t : ℤ))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    have hp := Pipe.pickAt main hpick (A := [ (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 4) (by simp) (v := (HvdH.Val.int ((t : ℤ)))) (by simp)
    exact Pipe.le (hp)
      (AuPiKit.le_SB_roll hKpick hp100 (A := [ (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 4) (by omega) (by simp) (AuPiKit.vsz_mem_le5 (AuPiKit.vsz_int_le hP) (AuPiKit.vsz_int_le hD) (AuPiKit.vsz_int_le hKZ) (AuPiKit.vsz_int_le hSZ) (AuPiKit.vsz_int_le hTZ)))
  have s10 : Pipe main (rollP 1)
      [ (HvdH.Val.int ((t : ℤ))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)))), (HvdH.Val.int ((t : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    have hp := Pipe.roll main hroll (A := [ (HvdH.Val.int ((t : ℤ))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 1) (by simp)
    exact Pipe.le ((Pipe.rw hp (by simp)))
      (AuPiKit.le_SB_roll hKroll hp100 (A := [ (HvdH.Val.int ((t : ℤ))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 1) (by omega) (by simp) (AuPiKit.vsz_mem_le_append (AuPiKit.vsz_mem_le4 (AuPiKit.vsz_int_le hTZ) (AuPiKit.vsz_int_le hP) (AuPiKit.vsz_int_le hD) (AuPiKit.vsz_int_le hKZ)) (AuPiKit.vsz_mem_le2 (AuPiKit.vsz_int_le hSZ) (AuPiKit.vsz_int_le hTZ))))
  have s11 : Pipe main addP
      [ (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)))), (HvdH.Val.int ((t : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    exact Pipe.le (Pipe.appendTail [ (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
        (Pipe.binOp (hadd main) (a := (k : ℤ) * ((2 : ℤ) * (s : ℤ))) (b := (t : ℤ)) trivial))
      (AuPiKit.le_SB_two hKa hP hTZ)
  have s12 : Pipe main dupP
      [ (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    exact Pipe.le (Pipe.appendTail [ (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (Pipe.dup main hdup (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)))))
      (AuPiKit.le_SB_one hKd (AuPiKit.vsz_int_le hA0))
  have s13 : Pipe main (rollP 2)
      [ (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    have hp := Pipe.roll main hroll (A := [ (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 2) (by simp)
    exact Pipe.le ((Pipe.rw hp (by simp)))
      (AuPiKit.le_SB_roll hKroll hp100 (A := [ (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 2) (by omega) (by simp) (AuPiKit.vsz_mem_le_append (AuPiKit.vsz_mem_le4 (AuPiKit.vsz_int_le hA0) (AuPiKit.vsz_int_le hA0) (AuPiKit.vsz_int_le hD) (AuPiKit.vsz_int_le hKZ)) (AuPiKit.vsz_mem_le2 (AuPiKit.vsz_int_le hSZ) (AuPiKit.vsz_int_le hTZ))))
  have s14 : Pipe main (rollP 1)
      [ (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    have hp := Pipe.roll main hroll (A := [ (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 1) (by simp)
    exact Pipe.le ((Pipe.rw hp (by simp)))
      (AuPiKit.le_SB_roll hKroll hp100 (A := [ (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 1) (by omega) (by simp) (AuPiKit.vsz_mem_le_append (AuPiKit.vsz_mem_le4 (AuPiKit.vsz_int_le hD) (AuPiKit.vsz_int_le hA0) (AuPiKit.vsz_int_le hA0) (AuPiKit.vsz_int_le hKZ)) (AuPiKit.vsz_mem_le2 (AuPiKit.vsz_int_le hSZ) (AuPiKit.vsz_int_le hTZ))))
  have s15 : Pipe main tdivP
      [ (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    exact Pipe.le (Pipe.appendTail [ (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
        (Pipe.binOp (htdiv main) (a := (k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) (b := (2 : ℤ) * (t : ℤ)) hDne))
      (le_SB_mul hKt hA0 hD)
  have s16 : Pipe main (pickP 3)
      [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    have hp := Pipe.pickAt main hpick (A := [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 3) (by simp) (v := (HvdH.Val.int ((s : ℤ)))) (by simp)
    exact Pipe.le (hp)
      (AuPiKit.le_SB_roll hKpick hp100 (A := [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 3) (by omega) (by simp) (AuPiKit.vsz_mem_le5 (AuPiKit.vsz_int_le hQ0) (AuPiKit.vsz_int_le hA0) (AuPiKit.vsz_int_le hKZ) (AuPiKit.vsz_int_le hSZ) (AuPiKit.vsz_int_le hTZ)))
  have s17 : Pipe main (pushP (HvdH.Val.int ((2 : ℤ))))
      [ (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((2 : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    exact Pipe.le (Pipe.pushOnAny (T := [ (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (hpush main (HvdH.Val.int ((2 : ℤ)))))
      (AuPiKit.le_SB_one hKpush (AuPiKit.vsz_int_le h2))
  have s18 : Pipe main mulP
      [ (HvdH.Val.int ((2 : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((2 : ℤ) * (s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    exact Pipe.le (Pipe.appendTail [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
        (Pipe.binOp (hmul main) (a := (2 : ℤ)) (b := (s : ℤ)) trivial))
      (le_SB_mul hKm h2 hSZ)
  have s19 : Pipe main (rollP 2)
      [ (HvdH.Val.int ((2 : ℤ) * (s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((2 : ℤ) * (s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    have hp := Pipe.roll main hroll (A := [ (HvdH.Val.int ((2 : ℤ) * (s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 2) (by simp)
    exact Pipe.le ((Pipe.rw hp (by simp)))
      (AuPiKit.le_SB_roll hKroll hp100 (A := [ (HvdH.Val.int ((2 : ℤ) * (s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 2) (by omega) (by simp) (AuPiKit.vsz_mem_le_append (AuPiKit.vsz_mem_le4 (AuPiKit.vsz_int_le hE) (AuPiKit.vsz_int_le hQ0) (AuPiKit.vsz_int_le hA0) (AuPiKit.vsz_int_le hKZ)) (AuPiKit.vsz_mem_le2 (AuPiKit.vsz_int_le hSZ) (AuPiKit.vsz_int_le hTZ))))
  have s20 : Pipe main addP
      [ (HvdH.Val.int ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ))), (HvdH.Val.int ((2 : ℤ) * (s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    exact Pipe.le (Pipe.appendTail [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
        (Pipe.binOp (hadd main) (a := (k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) (b := (2 : ℤ) * (s : ℤ)) trivial))
      (AuPiKit.le_SB_two hKa hA0 hE)
  have s21 : Pipe main (pickP 4)
      [ (HvdH.Val.int (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((t : ℤ))), (HvdH.Val.int (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    have hp := Pipe.pickAt main hpick (A := [ (HvdH.Val.int (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 4) (by simp) (v := (HvdH.Val.int ((t : ℤ)))) (by simp)
    exact Pipe.le (hp)
      (AuPiKit.le_SB_roll hKpick hp100 (A := [ (HvdH.Val.int (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 4) (by omega) (by simp) (AuPiKit.vsz_mem_le5 (AuPiKit.vsz_int_le hA1) (AuPiKit.vsz_int_le hQ0) (AuPiKit.vsz_int_le hKZ) (AuPiKit.vsz_int_le hSZ) (AuPiKit.vsz_int_le hTZ)))
  have s22 : Pipe main (pushP (HvdH.Val.int ((2 : ℤ))))
      [ (HvdH.Val.int ((t : ℤ))), (HvdH.Val.int (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((2 : ℤ))), (HvdH.Val.int ((t : ℤ))), (HvdH.Val.int (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    exact Pipe.le (Pipe.pushOnAny (T := [ (HvdH.Val.int ((t : ℤ))), (HvdH.Val.int (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (hpush main (HvdH.Val.int ((2 : ℤ)))))
      (AuPiKit.le_SB_one hKpush (AuPiKit.vsz_int_le h2))
  have s23 : Pipe main mulP
      [ (HvdH.Val.int ((2 : ℤ))), (HvdH.Val.int ((t : ℤ))), (HvdH.Val.int (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    exact Pipe.le (Pipe.appendTail [ (HvdH.Val.int (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
        (Pipe.binOp (hmul main) (a := (2 : ℤ)) (b := (t : ℤ)) trivial))
      (le_SB_mul hKm h2 hTZ)
  have s24 : Pipe main (rollP 1)
      [ (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    have hp := Pipe.roll main hroll (A := [ (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 1) (by simp)
    exact Pipe.le ((Pipe.rw hp (by simp)))
      (AuPiKit.le_SB_roll hKroll hp100 (A := [ (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 1) (by omega) (by simp) (AuPiKit.vsz_mem_le_append (AuPiKit.vsz_mem_le4 (AuPiKit.vsz_int_le hD) (AuPiKit.vsz_int_le hA1) (AuPiKit.vsz_int_le hQ0) (AuPiKit.vsz_int_le hKZ)) (AuPiKit.vsz_mem_le2 (AuPiKit.vsz_int_le hSZ) (AuPiKit.vsz_int_le hTZ))))
  have s25 : Pipe main tdivP
      [ (HvdH.Val.int (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ))), (HvdH.Val.int ((2 : ℤ) * (t : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    exact Pipe.le (Pipe.appendTail [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
        (Pipe.binOp (htdiv main) (a := ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) (b := (2 : ℤ) * (t : ℤ)) hDne))
      (le_SB_mul hKt hA1 hD)
  have s26 : Pipe main (rollP 1)
      [ (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    have hp := Pipe.roll main hroll (A := [ (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 1) (by simp)
    exact Pipe.le ((Pipe.rw hp (by simp)))
      (AuPiKit.le_SB_roll hKroll hp100 (A := [ (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 1) (by omega) (by simp) (AuPiKit.vsz_mem_le5 (AuPiKit.vsz_int_le hQ1) (AuPiKit.vsz_int_le hQ0) (AuPiKit.vsz_int_le hKZ) (AuPiKit.vsz_int_le hSZ) (AuPiKit.vsz_int_le hTZ)))
  have s27 : Pipe main (rollP 2)
      [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    have hp := Pipe.roll main hroll (A := [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 2) (by simp)
    exact Pipe.le ((Pipe.rw hp (by simp)))
      (AuPiKit.le_SB_roll hKroll hp100 (A := [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 2) (by omega) (by simp) (AuPiKit.vsz_mem_le5 (AuPiKit.vsz_int_le hQ0) (AuPiKit.vsz_int_le hQ1) (AuPiKit.vsz_int_le hKZ) (AuPiKit.vsz_int_le hSZ) (AuPiKit.vsz_int_le hTZ)))
  have s28 : Pipe main dropP
      [ (HvdH.Val.int ((k : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    exact Pipe.le (Pipe.appendTail [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ] (Pipe.drop main hdrop (HvdH.Val.int ((k : ℤ)))))
      (AuPiKit.le_SB_one hKdr (AuPiKit.vsz_int_le hKZ))
  have s29 : Pipe main (rollP 2)
      [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    have hp := Pipe.roll main hroll (A := [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 2) (by simp)
    exact Pipe.le ((Pipe.rw hp (by simp)))
      (AuPiKit.le_SB_roll hKroll hp100 (A := [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int ((t : ℤ))) ]) (k := 2) (by omega) (by simp) (AuPiKit.vsz_mem_le4 (AuPiKit.vsz_int_le hQ0) (AuPiKit.vsz_int_le hQ1) (AuPiKit.vsz_int_le hSZ) (AuPiKit.vsz_int_le hTZ)))
  have s30 : Pipe main dropP
      [ (HvdH.Val.int ((s : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((t : ℤ))) ] (SB p KS) := by
    exact Pipe.le (Pipe.appendTail [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((t : ℤ))) ] (Pipe.drop main hdrop (HvdH.Val.int ((s : ℤ)))))
      (AuPiKit.le_SB_one hKdr (AuPiKit.vsz_int_le hSZ))
  have s31 : Pipe main (rollP 2)
      [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((t : ℤ))) ]
      [ (HvdH.Val.int ((t : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))) ] (SB p KS) := by
    have hp := Pipe.roll main hroll (A := [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((t : ℤ))) ]) (k := 2) (by simp)
    exact Pipe.le ((Pipe.rw hp (by simp)))
      (AuPiKit.le_SB_roll hKroll hp100 (A := [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int ((t : ℤ))) ]) (k := 2) (by omega) (by simp) (AuPiKit.vsz_mem_le3 (AuPiKit.vsz_int_le hQ0) (AuPiKit.vsz_int_le hQ1) (AuPiKit.vsz_int_le hTZ)))
  have s32 : Pipe main dropP
      [ (HvdH.Val.int ((t : ℤ))), (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))) ]
      [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))) ] (SB p KS) := by
    exact Pipe.le (Pipe.appendTail [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))) ] (Pipe.drop main hdrop (HvdH.Val.int ((t : ℤ)))))
      (AuPiKit.le_SB_one hKdr (AuPiKit.vsz_int_le hTZ))
  -- the composed word
  have g1 := s1
  have g2 := Pipe.comp g1 s2
  have g3 := Pipe.comp g2 s3
  have g4 := Pipe.comp g3 s4
  have g5 := Pipe.comp g4 s5
  have g6 := Pipe.comp g5 s6
  have g7 := Pipe.comp g6 s7
  have g8 := Pipe.comp g7 s8
  have g9 := Pipe.comp g8 s9
  have g10 := Pipe.comp g9 s10
  have g11 := Pipe.comp g10 s11
  have g12 := Pipe.comp g11 s12
  have g13 := Pipe.comp g12 s13
  have g14 := Pipe.comp g13 s14
  have g15 := Pipe.comp g14 s15
  have g16 := Pipe.comp g15 s16
  have g17 := Pipe.comp g16 s17
  have g18 := Pipe.comp g17 s18
  have g19 := Pipe.comp g18 s19
  have g20 := Pipe.comp g19 s20
  have g21 := Pipe.comp g20 s21
  have g22 := Pipe.comp g21 s22
  have g23 := Pipe.comp g22 s23
  have g24 := Pipe.comp g23 s24
  have g25 := Pipe.comp g24 s25
  have g26 := Pipe.comp g25 s26
  have g27 := Pipe.comp g26 s27
  have g28 := Pipe.comp g27 s28
  have g29 := Pipe.comp g28 s29
  have g30 := Pipe.comp g29 s30
  have g31 := Pipe.comp g30 s31
  have g32 := Pipe.comp g31 s32
  have hfin : Pipe main _ _ _ (32 * SB p KS) := Pipe.le g32 (by omega)
  refine Pipe.le (Pipe.rw hfin ?_) ?_
  · show [ (HvdH.Val.int (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ)))), (HvdH.Val.int (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ)))) ] = [HvdH.Val.int ((auK s t k : ℕ) : ℤ), HvdH.Val.int ((auK s t (k + 1) : ℕ) : ℤ)]
    rw [show (Int.tdiv ((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) ((2 : ℤ) * (t : ℤ))) = kQ0 s t k from rfl, kQ0_eq s t k ht,
        show (Int.tdiv (((k : ℤ) * ((2 : ℤ) * (s : ℤ)) + (t : ℤ)) + (2 : ℤ) * (s : ℤ)) ((2 : ℤ) * (t : ℤ))) = kQ1 s t k from rfl, kQ1_eq s t k ht]
  · have hSB : SB p KS ≤ 256 * KS * (p + 1) ^ 2 := SB_le p KS hp100
    have h1 : 32 * SB p KS ≤ (32 * 256 * KS) * (p + 1) ^ 3 := by
      calc 32 * SB p KS ≤ 32 * (256 * KS * (p + 1) ^ 2) := Nat.mul_le_mul_left 32 hSB
        _ = (32 * 256 * KS) * (p + 1) ^ 2 := by ring
        _ ≤ (32 * 256 * KS) * (p + 1) ^ 3 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : (32 * 256 * KS) * (p + 1) ^ 3 ≤
        (4 * (32 * 256 * KS) + 1) * (p + 1) ^ (4 * (32 * 256 * KS) + 1) :=
      AuPiKit.pow_bound (32 * 256 * KS) p (by omega) (by omega)
    exact le_trans h1 h2

end Work.Resample
