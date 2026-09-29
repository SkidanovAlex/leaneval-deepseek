import Mathlib
import Submission.Work.Fx.CisKit
import Submission.Work.IntLib.encodeNatBridge

namespace Work.Fx

open HvdH

/-- `vsz` of an integer value is `isz` of the integer. -/
@[simp] theorem vsz_int_eq (z : ℤ) : vsz (Val.int z) = isz z := Work.IntLib.vsz_int z

namespace Cis

/-! ## Window membership bounds at scale `Xb p j k` -/

theorem vsz_int_le_Xb_p (p : ℕ) (j : ℤ) (k : ℕ) : vsz (Val.int (p : ℤ)) ≤ Xb p j k := by
  rw [vsz_int_eq]; exact isz_le_Xb_p p j k

theorem vsz_int_le_Xb_j (p : ℕ) (j : ℤ) (k : ℕ) : vsz (Val.int j) ≤ Xb p j k := by
  rw [vsz_int_eq]; exact isz_le_Xb_j p j k

theorem vsz_int_le_Xb_k (p : ℕ) (j : ℤ) (k : ℕ) : vsz (Val.int (k : ℤ)) ≤ Xb p j k := by
  rw [vsz_int_eq]; exact isz_le_Xb_k p j k

theorem vsz_int_le_Xb_fmod (p : ℕ) (j : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    vsz (Val.int (Int.fmod j (k : ℤ))) ≤ Xb p j k := by
  rw [vsz_int_eq]; exact isz_fmod_le_Xb p j k hk

theorem vsz_int_sixty_le_Xb (p : ℕ) (j : ℤ) (k : ℕ) (hp : 100 ≤ p) :
    vsz (Val.int 60) ≤ Xb p j k := by
  rw [vsz_int_eq, isz_sixty]
  have := Xb_ge p j k hp
  omega

theorem vsz_mem_le2 {X : ℕ} {a b : ℤ} (ha : vsz (Val.int a) ≤ X) (hb : vsz (Val.int b) ≤ X) :
    ∀ v ∈ ([Val.int a, Val.int b] : List Val), vsz v ≤ X := by
  intro v hv
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl <;> assumption

theorem vsz_mem_le3 {X : ℕ} {a b c : ℤ} (ha : vsz (Val.int a) ≤ X) (hb : vsz (Val.int b) ≤ X)
    (hc : vsz (Val.int c) ≤ X) : ∀ v ∈ ([Val.int a, Val.int b, Val.int c] : List Val), vsz v ≤ X := by
  intro v hv
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl <;> assumption

theorem vsz_mem_le4 {X : ℕ} {a b c d : ℤ} (ha : vsz (Val.int a) ≤ X) (hb : vsz (Val.int b) ≤ X)
    (hc : vsz (Val.int c) ≤ X) (hd : vsz (Val.int d) ≤ X) :
    ∀ v ∈ ([Val.int a, Val.int b, Val.int c, Val.int d] : List Val), vsz v ≤ X := by
  intro v hv
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> assumption

end Cis

/-- `cis` word, step 1 (paper Lemma 2.12): from the input window `[p, j, k]` (`100 ≤ p`, `1 ≤ k`)
compute `Pp = p + 60` and `j' = Int.fmod j k`, leaving the window `[Pp, j', k]`.
Route (chain `Work.Fx.Cis.Pipe` windows): `pick 2` (duplicate `k`), `roll 2` (bring `j` to the top),
`fmod` (precondition `0 < k`), `roll 1` (bring `p` to the top), `pushVal (Val.int 60)`,
`add` with `a = 60`, `b = p`.  Every window member has `isz ≤ Work.Fx.Cis.Xb p j k`
(`Work.Fx.Cis.isz_fmod_le_Xb`, `isz_le_Xb_p`, `isz_le_Xb_j`, `isz_le_Xb_k`, `isz_sixty`), so every
single word costs at most `Work.Fx.Cis.CB (Xb p j k) KS` by `le_CB_roll`/`le_CB_mul`/`le_CB_one`/
`le_CB_add`, with `KS` the sum of the library constants. -/
theorem CisStep1 (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (j : ℤ) (k : ℕ), 100 ≤ p → 1 ≤ k →
      Work.Fx.Cis.PipeQ main prog
        [HvdH.Val.int (p : ℤ), HvdH.Val.int j, HvdH.Val.int (k : ℤ)]
        (fun o => o = [HvdH.Val.int ((p : ℤ) + 60), HvdH.Val.int (Int.fmod j k),
          HvdH.Val.int (k : ℤ)])
        (K * (Work.Fx.Cis.Xb p j k) ^ 32) := by
  obtain ⟨pickP, Kp, hpick⟩ := hk.pick
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨pushP, Kpv, hpush⟩ := hk.pushVal
  obtain ⟨fmodP, Kf, hfmod⟩ := hi.fmod
  obtain ⟨addP, Ka, hadd⟩ := hi.add
  refine ⟨Cmd.seq (pickP 2) (Cmd.seq (rollP 2) (Cmd.seq fmodP (Cmd.seq (rollP 1)
    (Cmd.seq (pushP (Val.int 60)) addP)))),
    6 * (Kp + Kr + Kf + Kpv + Ka + 1), ?_⟩
  intro main p j k hp hk1
  set X : ℕ := Cis.Xb p j k with hXdef
  set KS : ℕ := Kp + Kr + Kf + Kpv + Ka + 1 with hKSdef
  have hX : 45 ≤ X := by
    rw [hXdef]; have := Cis.Xb_ge p j k hp; omega
  have hX2 : 2 ≤ X := by omega
  have hKp : Kp ≤ KS := by rw [hKSdef]; omega
  have hKr : Kr ≤ KS := by rw [hKSdef]; omega
  have hKf : Kf ≤ KS := by rw [hKSdef]; omega
  have hKpv : Kpv ≤ KS := by rw [hKSdef]; omega
  have hKa : Ka ≤ KS := by rw [hKSdef]; omega
  -- step 1: `pick 2` -- `[p, j, k] ↦ [k, p, j, k]`
  have hA1 : ∀ v ∈ ([Val.int (p : ℤ), Val.int j, Val.int (k : ℤ)] : List Val), vsz v ≤ X :=
    Cis.vsz_mem_le3 (Cis.vsz_int_le_Xb_p p j k) (Cis.vsz_int_le_Xb_j p j k)
      (Cis.vsz_int_le_Xb_k p j k)
  have s1 : Cis.Pipe main (pickP 2) [Val.int (p : ℤ), Val.int j, Val.int (k : ℤ)]
      [Val.int (k : ℤ), Val.int (p : ℤ), Val.int j, Val.int (k : ℤ)] (Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.rw (Cis.Pipe.pick (prog := pickP) (K := Kp) main hpick
        (A := [Val.int (p : ℤ), Val.int j, Val.int (k : ℤ)]) (k := 2) (by simp)) (by simp))
      (Cis.le_CB_roll (K := Kp) (KS := KS) (X := X) (k := 2) hKp (by omega) hA1 (by simp) hX)
  -- step 2: `roll 2` -- `[k, p, j, k] ↦ [j, k, p, k]`
  have hA2 : ∀ v ∈ ([Val.int (k : ℤ), Val.int (p : ℤ), Val.int j, Val.int (k : ℤ)] : List Val),
      vsz v ≤ X :=
    Cis.vsz_mem_le4 (Cis.vsz_int_le_Xb_k p j k) (Cis.vsz_int_le_Xb_p p j k)
      (Cis.vsz_int_le_Xb_j p j k) (Cis.vsz_int_le_Xb_k p j k)
  have s2 : Cis.Pipe main (rollP 2) [Val.int (k : ℤ), Val.int (p : ℤ), Val.int j, Val.int (k : ℤ)]
      [Val.int j, Val.int (k : ℤ), Val.int (p : ℤ), Val.int (k : ℤ)] (Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.rw (Cis.Pipe.roll (prog := rollP) (K := Kr) main hroll
        (A := [Val.int (k : ℤ), Val.int (p : ℤ), Val.int j, Val.int (k : ℤ)]) (k := 2)
        (by simp)) (by simp))
      (Cis.le_CB_roll (K := Kr) (KS := KS) (X := X) (k := 2) hKr (by omega) hA2 (by simp) hX)
  -- step 3: `fmod` -- `[j, k, p, k] ↦ [j mod k, p, k]`
  have s3 : Cis.Pipe main fmodP
      [Val.int j, Val.int (k : ℤ), Val.int (p : ℤ), Val.int (k : ℤ)]
      [Val.int (Int.fmod j (k : ℤ)), Val.int (p : ℤ), Val.int (k : ℤ)] (Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.appendTail [Val.int (p : ℤ), Val.int (k : ℤ)]
        (Cis.Pipe.binOp (prog := fmodP) (hfmod main) (a := j) (b := (k : ℤ))
          (by exact_mod_cast hk1)))
      (Cis.le_CB_mul (K := Kf) (KS := KS) (X := X) (u := isz j) (v := isz (k : ℤ)) hKf
        (Cis.isz_le_Xb_j p j k) (Cis.isz_le_Xb_k p j k) hX2)
  -- step 4: `roll 1` -- `[j', p, k] ↦ [p, j', k]`
  have hA4 : ∀ v ∈ ([Val.int (Int.fmod j (k : ℤ)), Val.int (p : ℤ), Val.int (k : ℤ)] : List Val),
      vsz v ≤ X :=
    Cis.vsz_mem_le3 (Cis.vsz_int_le_Xb_fmod p j k hk1) (Cis.vsz_int_le_Xb_p p j k)
      (Cis.vsz_int_le_Xb_k p j k)
  have s4 : Cis.Pipe main (rollP 1)
      [Val.int (Int.fmod j (k : ℤ)), Val.int (p : ℤ), Val.int (k : ℤ)]
      [Val.int (p : ℤ), Val.int (Int.fmod j (k : ℤ)), Val.int (k : ℤ)] (Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.rw (Cis.Pipe.roll (prog := rollP) (K := Kr) main hroll
        (A := [Val.int (Int.fmod j (k : ℤ)), Val.int (p : ℤ), Val.int (k : ℤ)]) (k := 1)
        (by simp)) (by simp))
      (Cis.le_CB_roll (K := Kr) (KS := KS) (X := X) (k := 1) hKr (by omega) hA4 (by simp) hX)
  -- step 5: `pushVal 60` -- `[p, j', k] ↦ [60, p, j', k]`
  have s5 : Cis.Pipe main (pushP (Val.int 60))
      [Val.int (p : ℤ), Val.int (Int.fmod j (k : ℤ)), Val.int (k : ℤ)]
      [Val.int 60, Val.int (p : ℤ), Val.int (Int.fmod j (k : ℤ)), Val.int (k : ℤ)]
      (Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.appendTail [Val.int (p : ℤ), Val.int (Int.fmod j (k : ℤ)), Val.int (k : ℤ)]
        (Cis.Pipe.pushVal (prog := pushP) (K := Kpv) hpush (Val.int 60)))
      (by rw [show vsz (Val.int 60) = 8 by rw [vsz_int_eq, Cis.isz_sixty]]
          exact Cis.le_CB_one (K := Kpv) (KS := KS) (X := X) (v := 8) hKpv (by omega) hX2)
  -- step 6: `add` -- `[60, p, j', k] ↦ [60 + p, j', k]`
  have s6 : Cis.Pipe main addP
      [Val.int 60, Val.int (p : ℤ), Val.int (Int.fmod j (k : ℤ)), Val.int (k : ℤ)]
      [Val.int (60 + (p : ℤ)), Val.int (Int.fmod j (k : ℤ)), Val.int (k : ℤ)] (Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.appendTail [Val.int (Int.fmod j (k : ℤ)), Val.int (k : ℤ)]
        (Cis.Pipe.binOp (prog := addP) (hadd main) (a := 60) (b := (p : ℤ)) trivial))
      (by rw [Cis.isz_sixty]
          exact Cis.le_CB_add (K := Ka) (KS := KS) (X := X) (u := 8) (v := isz (p : ℤ)) hKa
            (by omega) (Cis.isz_le_Xb_p p j k) hX2)
  have hcomp : Cis.Pipe main
      (Cmd.seq (pickP 2) (Cmd.seq (rollP 2) (Cmd.seq fmodP (Cmd.seq (rollP 1)
        (Cmd.seq (pushP (Val.int 60)) addP)))))
      [Val.int (p : ℤ), Val.int j, Val.int (k : ℤ)]
      [Val.int (60 + (p : ℤ)), Val.int (Int.fmod j (k : ℤ)), Val.int (k : ℤ)]
      (6 * Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.comp s1 (Cis.Pipe.comp s2 (Cis.Pipe.comp s3 (Cis.Pipe.comp s4
        (Cis.Pipe.comp s5 s6)))))
      (le_of_eq (by ring))
  refine Cis.PipeQ.mono (Cis.PipeQ.le (Cis.Pipe.toPipeQ hcomp) ?_) ?_
  · rw [Cis.CB, hKSdef]
    exact le_of_eq (by ring)
  · intro o ho
    have hc : (60 : ℤ) + (p : ℤ) = (p : ℤ) + 60 := by ring
    rw [ho, hc]

end Work.Fx
