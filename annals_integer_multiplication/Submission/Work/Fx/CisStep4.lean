import Mathlib
import Submission.Work.Fx.CisStep1

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Fx

open HvdH

/-- `cis` word, step 4 (paper Lemma 2.12): the integer `w` returned by the `π` word at precision
`p + 60` occupies the window `[w, Pp, j', k]` (`Pp = p + 60`, `j' = Int.fmod j k`); compute
`R = Int.tdiv (2 * w * j') k`, leaving the window `[R, Pp]`.
Route: `pushVal (Val.int 2)`, `mulS` (`2 * w`), `Work.Fx.Cis.Pipe.roll 2` (bring `j'` to the top),
`swap`, `mulS` (`2 * w * j'`), `Work.Fx.Cis.Pipe.roll 2` (bring `k` to the top), `swap`, `tdiv`
(precondition `k ≠ 0`).  Sizes are `O(Xb p j k)`, and `K` may absorb the constant factor
(`HvdH.isz (2*w) ≤ HvdH.isz w + 4`, `HvdH.isz_mul_le`, `HvdH.isz_tdiv_le`); `Work.Fx.Cis.le_CB_mul`,
`le_CB_roll`, `le_CB_one`, `le_CB_two` bound each word. -/
theorem CisStep4 (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (j : ℤ) (k : ℕ), 100 ≤ p → 1 ≤ k →
      ∀ w : ℤ, HvdH.isz w ≤ Work.Fx.Cis.Xb p j k →
      Work.Fx.Cis.PipeQ main prog
        [HvdH.Val.int w, HvdH.Val.int ((p : ℤ) + 60), HvdH.Val.int (Int.fmod j k),
          HvdH.Val.int (k : ℤ)]
        (fun o => o = [HvdH.Val.int (Int.tdiv (2 * w * Int.fmod j k) k),
          HvdH.Val.int ((p : ℤ) + 60)])
        (K * (Work.Fx.Cis.Xb p j k) ^ 32) := by
  obtain ⟨mulP, Km, hmul⟩ := hi.mulS
  obtain ⟨tdivP, Kt, htdiv⟩ := hi.tdiv
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨swapP, Ks, hswap⟩ := hk.swap
  obtain ⟨pushP, Kpv, hpush⟩ := hk.pushVal
  set KS : ℕ := Km + Kt + Kr + Ks + Kpv + 1 with hKSdef
  have hKm : Km ≤ KS := by rw [hKSdef]; omega
  have hKt : Kt ≤ KS := by rw [hKSdef]; omega
  have hKr : Kr ≤ KS := by rw [hKSdef]; omega
  have hKs : Ks ≤ KS := by rw [hKSdef]; omega
  have hKpv : Kpv ≤ KS := by rw [hKSdef]; omega
  refine ⟨Cmd.seq (pushP (Val.int 2))
    (Cmd.seq mulP (Cmd.seq (rollP 2) (Cmd.seq swapP (Cmd.seq mulP
      (Cmd.seq (rollP 2) (Cmd.seq swapP tdivP)))))),
    8 * KS * 4 ^ 32, ?_⟩
  intro main p j k hp hk1 w hw
  set X : ℕ := 4 * Cis.Xb p j k with hXdef
  have hX168 : 168 ≤ Cis.Xb p j k := Cis.Xb_ge p j k hp
  have hX45 : 45 ≤ X := by rw [hXdef]; omega
  have hX2 : 2 ≤ X := by omega
  have hX3 : 3 ≤ X := by omega
  -- size bounds for the window entries and the intermediate results
  have hwX : isz w ≤ X := by rw [hXdef]; omega
  have hpX : isz ((p : ℤ) + 60) ≤ X := by
    rw [hXdef]; have := Cis.isz_p_add_sixty_le_Xb p j k hp; omega
  have hjX : isz (Int.fmod j (k : ℤ)) ≤ X := by
    rw [hXdef]; have := Cis.isz_fmod_le_Xb p j k hk1; omega
  have hkX : isz ((k : ℤ)) ≤ X := by
    rw [hXdef]; have := Cis.isz_le_Xb_k p j k; omega
  have h2wX : isz (2 * w) ≤ X := by
    rw [hXdef]; have := Cis.isz_two_mul_le w; omega
  have h2wjX : isz (2 * w * Int.fmod j (k : ℤ)) ≤ X := by
    rw [hXdef]
    have h1 := isz_mul_le (2 * w) (Int.fmod j (k : ℤ))
    have h2 := Cis.isz_two_mul_le w
    have h3 := Cis.isz_fmod_le_Xb p j k hk1
    omega
  have hkZ : (k : ℤ) ≠ 0 := by
    have h : 0 < (k : ℤ) := by exact_mod_cast hk1
    omega
  -- membership bounds for the two windows that are scanned by `roll`
  have hmem2 : ∀ v ∈ ([Val.int (2 * w), Val.int ((p : ℤ) + 60),
      Val.int (Int.fmod j (k : ℤ)), Val.int (k : ℤ)] : List Val), vsz v ≤ X :=
    Cis.vsz_mem_le4 (by simpa using h2wX) (by simpa using hpX) (by simpa using hjX)
      (by simpa using hkX)
  have hmem5 : ∀ v ∈ ([Val.int (2 * w * Int.fmod j (k : ℤ)), Val.int ((p : ℤ) + 60),
      Val.int (k : ℤ)] : List Val), vsz v ≤ X :=
    Cis.vsz_mem_le3 (by simpa using h2wjX) (by simpa using hpX) (by simpa using hkX)
  -- step 1: `pushVal 2` -- `[w, Pp, j', k] ↦ [2, w, Pp, j', k]`
  have s1 : Cis.Pipe main (pushP (Val.int 2))
      [Val.int w, Val.int ((p : ℤ) + 60), Val.int (Int.fmod j (k : ℤ)), Val.int (k : ℤ)]
      [Val.int 2, Val.int w, Val.int ((p : ℤ) + 60), Val.int (Int.fmod j (k : ℤ)),
        Val.int (k : ℤ)] (Cis.CB X KS) :=
    Cis.Pipe.le (Cis.Pipe.pushOnAny (hpush main (Val.int 2)))
      (by
        have h := Cis.le_CB_one (K := Kpv) (KS := KS) (X := X) (v := 4) hKpv (by omega) hX2
        simpa [vsz_int_eq, Cis.isz_two] using h)
  -- step 2: `mulS` -- `[2, w, ...] ↦ [2 * w, Pp, j', k]`
  have s2 : Cis.Pipe main mulP
      [Val.int 2, Val.int w, Val.int ((p : ℤ) + 60), Val.int (Int.fmod j (k : ℤ)),
        Val.int (k : ℤ)]
      [Val.int (2 * w), Val.int ((p : ℤ) + 60), Val.int (Int.fmod j (k : ℤ)), Val.int (k : ℤ)]
      (Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.appendTail [Val.int ((p : ℤ) + 60), Val.int (Int.fmod j (k : ℤ)),
          Val.int (k : ℤ)]
        (Cis.Pipe.binOp (prog := mulP) (hmul main) (a := 2) (b := w) trivial))
      (by
        have h := Cis.le_CB_mul (K := Km) (KS := KS) (X := X) (u := 4) (v := isz w) hKm
          (by omega) hwX hX2
        simpa [vsz_int_eq, Cis.isz_two] using h)
  -- step 3: `roll 2` -- `[2 * w, Pp, j', k] ↦ [j', 2 * w, Pp, k]`
  have s3 : Cis.Pipe main (rollP 2)
      [Val.int (2 * w), Val.int ((p : ℤ) + 60), Val.int (Int.fmod j (k : ℤ)), Val.int (k : ℤ)]
      [Val.int (Int.fmod j (k : ℤ)), Val.int (2 * w), Val.int ((p : ℤ) + 60),
        Val.int (k : ℤ)] (Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.rw (Cis.Pipe.roll (prog := rollP) (K := Kr) main hroll
        (A := [Val.int (2 * w), Val.int ((p : ℤ) + 60), Val.int (Int.fmod j (k : ℤ)),
          Val.int (k : ℤ)]) (k := 2) (by simp)) (by simp))
      (Cis.le_CB_roll (K := Kr) (KS := KS) (X := X) (k := 2) hKr (by omega) hmem2 (by simp) hX45)
  -- step 4: `swap` -- `[j', 2 * w, Pp, k] ↦ [2 * w, j', Pp, k]`
  have s4 : Cis.Pipe main swapP
      [Val.int (Int.fmod j (k : ℤ)), Val.int (2 * w), Val.int ((p : ℤ) + 60), Val.int (k : ℤ)]
      [Val.int (2 * w), Val.int (Int.fmod j (k : ℤ)), Val.int ((p : ℤ) + 60),
        Val.int (k : ℤ)] (Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.appendTail [Val.int ((p : ℤ) + 60), Val.int (k : ℤ)]
        (Cis.Pipe.swap (prog := swapP) (K := Ks) main hswap
          (Val.int (Int.fmod j (k : ℤ))) (Val.int (2 * w))))
      (by
        have h := Cis.le_CB_two (K := Ks) (KS := KS) (X := X)
          (u := isz (Int.fmod j (k : ℤ))) (v := isz (2 * w)) hKs hjX h2wX hX3
        simpa [vsz_int_eq] using h)
  -- step 5: `mulS` -- `[2 * w, j', ...] ↦ [2 * w * j', Pp, k]`
  have s5 : Cis.Pipe main mulP
      [Val.int (2 * w), Val.int (Int.fmod j (k : ℤ)), Val.int ((p : ℤ) + 60),
        Val.int (k : ℤ)]
      [Val.int (2 * w * Int.fmod j (k : ℤ)), Val.int ((p : ℤ) + 60), Val.int (k : ℤ)]
      (Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.appendTail [Val.int ((p : ℤ) + 60), Val.int (k : ℤ)]
        (Cis.Pipe.binOp (prog := mulP) (hmul main) (a := 2 * w) (b := Int.fmod j (k : ℤ))
          trivial))
      (by
        have h := Cis.le_CB_mul (K := Km) (KS := KS) (X := X) (u := isz (2 * w))
          (v := isz (Int.fmod j (k : ℤ))) hKm h2wX hjX hX2
        simpa using h)
  -- step 6: `roll 2` -- `[2 * w * j', Pp, k] ↦ [k, 2 * w * j', Pp]`
  have s6 : Cis.Pipe main (rollP 2)
      [Val.int (2 * w * Int.fmod j (k : ℤ)), Val.int ((p : ℤ) + 60), Val.int (k : ℤ)]
      [Val.int (k : ℤ), Val.int (2 * w * Int.fmod j (k : ℤ)), Val.int ((p : ℤ) + 60)]
      (Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.rw (Cis.Pipe.roll (prog := rollP) (K := Kr) main hroll
        (A := [Val.int (2 * w * Int.fmod j (k : ℤ)), Val.int ((p : ℤ) + 60), Val.int (k : ℤ)])
        (k := 2) (by simp)) (by simp))
      (Cis.le_CB_roll (K := Kr) (KS := KS) (X := X) (k := 2) hKr (by omega) hmem5 (by simp)
        hX45)
  -- step 7: `swap` -- `[k, 2 * w * j', Pp] ↦ [2 * w * j', k, Pp]`
  have s7 : Cis.Pipe main swapP
      [Val.int (k : ℤ), Val.int (2 * w * Int.fmod j (k : ℤ)), Val.int ((p : ℤ) + 60)]
      [Val.int (2 * w * Int.fmod j (k : ℤ)), Val.int (k : ℤ), Val.int ((p : ℤ) + 60)]
      (Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.appendTail [Val.int ((p : ℤ) + 60)]
        (Cis.Pipe.swap (prog := swapP) (K := Ks) main hswap (Val.int (k : ℤ))
          (Val.int (2 * w * Int.fmod j (k : ℤ)))))
      (by
        have h := Cis.le_CB_two (K := Ks) (KS := KS) (X := X) (u := isz (k : ℤ))
          (v := isz (2 * w * Int.fmod j (k : ℤ))) hKs hkX h2wjX hX3
        simpa [vsz_int_eq] using h)
  -- step 8: `tdiv` -- `[2 * w * j', k, Pp] ↦ [R, Pp]`
  have s8 : Cis.Pipe main tdivP
      [Val.int (2 * w * Int.fmod j (k : ℤ)), Val.int (k : ℤ), Val.int ((p : ℤ) + 60)]
      [Val.int (Int.tdiv (2 * w * Int.fmod j (k : ℤ)) (k : ℤ)), Val.int ((p : ℤ) + 60)]
      (Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.appendTail [Val.int ((p : ℤ) + 60)]
        (Cis.Pipe.binOp (prog := tdivP) (htdiv main) (a := 2 * w * Int.fmod j (k : ℤ))
          (b := (k : ℤ)) hkZ))
      (by
        have h := Cis.le_CB_mul (K := Kt) (KS := KS) (X := X)
          (u := isz (2 * w * Int.fmod j (k : ℤ))) (v := isz (k : ℤ)) hKt h2wjX hkX hX2
        simpa using h)
  have hcomp : Cis.Pipe main
      (Cmd.seq (pushP (Val.int 2)) (Cmd.seq mulP (Cmd.seq (rollP 2) (Cmd.seq swapP
        (Cmd.seq mulP (Cmd.seq (rollP 2) (Cmd.seq swapP tdivP)))))))
      [Val.int w, Val.int ((p : ℤ) + 60), Val.int (Int.fmod j (k : ℤ)), Val.int (k : ℤ)]
      [Val.int (Int.tdiv (2 * w * Int.fmod j (k : ℤ)) (k : ℤ)), Val.int ((p : ℤ) + 60)]
      (8 * Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.comp s1 (Cis.Pipe.comp s2 (Cis.Pipe.comp s3 (Cis.Pipe.comp s4
        (Cis.Pipe.comp s5 (Cis.Pipe.comp s6 (Cis.Pipe.comp s7 s8)))))))
      (by omega)
  refine Cis.PipeQ.mono (Cis.PipeQ.le (Cis.Pipe.toPipeQ hcomp) ?_) ?_
  · have hcost : 8 * Cis.CB X KS = (8 * KS * 4 ^ 32) * (Cis.Xb p j k) ^ 32 := by
      rw [Cis.CB, Nat.mul_pow]
      ring
    exact le_of_eq hcost
  · intro o ho
    rw [ho]

end Work.Fx
