import Mathlib
import Submission.Work.Fx.CisKit

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Fx

open HvdH

namespace Cis

/-- Size bounds for the two members of a two-element window. -/
theorem vsz_mem_pair {X : ℕ} {a b : Val} (ha : vsz a ≤ X) (hb : vsz b ≤ X) :
    ∀ v ∈ ([a, b] : List Val), vsz v ≤ X := by
  intro v hv
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl <;> assumption

/-- `consV` on a fixed two-element window `[a, b]`. -/
theorem Pipe.consV {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => K))
    (a b : Val) : Pipe main prog [a, b] [.cons a b] K := by
  intro rest vs hvs s R hR
  have hv2 : vs = a :: b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv2]; simp) s R hR
  obtain ⟨h1, h2, h3⟩ := cons_inj3 (hvs'.symm.trans hv2)
  exact ⟨out, s', n, by rw [hout, h1, h2, h3]; rfl, hev, hn, hstk, hoth⟩

end Cis

/-- `cis` word, step 6 (paper Lemma 2.12): truncate the pair `(U, V)` returned by the `expc` word
by `2^60` and pack it as a fixed-point complex value; window
`[U, V] → [cfxVal (U / 2^60, V / 2^60)]` (the divisions are `Int.tdiv`, i.e. `hi.shrT` with
`k = 60`, precondition `0 ≤ 60`).
Route: `Work.Fx.Cis.Pipe.roll 1` (bring `V` to the top), `pushVal (Val.int 60)`, `swap`, `shrT`;
then `roll 1`, `pushVal (Val.int 60)`, `swap`, `shrT`; then `consV` (giving
`Val.cons (Val.int U') (Val.int V') = cfxVal (U', V')`).  `M` bounds the sizes of `U` and `V`, so
every window member has size `≤ M + 8` (`HvdH.isz (Int.tdiv U (2^60)) ≤ HvdH.isz U`), and each word
costs `≤ K * M ^ 32` for a suitable constant `K` by the `Work.Fx.Cis.le_CB_*` lemmas. -/
theorem CisStep6 (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (M : ℕ) (U V : ℤ),
      HvdH.isz U ≤ M → HvdH.isz V ≤ M →
      Work.Fx.Cis.PipeQ main prog [HvdH.Val.int U, HvdH.Val.int V]
        (fun o => o = [HvdH.cfxVal (Int.tdiv U (2 ^ 60), Int.tdiv V (2 ^ 60))])
        (K * M ^ 32) := by
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨pushP, Kpv, hpush⟩ := hk.pushVal
  obtain ⟨swapP, Ks, hswap⟩ := hk.swap
  obtain ⟨consP, Kc, hcons⟩ := hk.consV
  obtain ⟨shrP, Kst, hshr⟩ := hi.shrT
  set KS : ℕ := Kr + Kpv + Ks + Kst + Kc + 1 with hKSdef
  have hKr : Kr ≤ KS := by rw [hKSdef]; omega
  have hKpv : Kpv ≤ KS := by rw [hKSdef]; omega
  have hKs : Ks ≤ KS := by rw [hKSdef]; omega
  have hKst : Kst ≤ KS := by rw [hKSdef]; omega
  have hKc : Kc ≤ KS := by rw [hKSdef]; omega
  refine ⟨Cmd.seq (rollP 1) (Cmd.seq (pushP (Val.int 60)) (Cmd.seq swapP (Cmd.seq shrP
    (Cmd.seq (rollP 1) (Cmd.seq (pushP (Val.int 60)) (Cmd.seq swapP (Cmd.seq shrP consP))))))),
    9 * KS * 32 ^ 32, ?_⟩
  intro main M U V hU hV
  set X : ℕ := 32 * M with hXdef
  have hM2 : 2 ≤ M := le_trans (Cis.two_le_isz U) hU
  have hX45 : 45 ≤ X := by rw [hXdef]; omega
  have hX3 : 3 ≤ X := by omega
  have hX2 : 2 ≤ X := by omega
  have hUX : isz U ≤ X := by rw [hXdef]; omega
  have hVX : isz V ≤ X := by rw [hXdef]; omega
  have h60X : isz (60 : ℤ) ≤ X := by rw [Cis.isz_sixty]; omega
  have hUtX : isz (Int.tdiv U (2 ^ 60)) ≤ X :=
    le_trans (Work.Fx.isz_tdiv_le U (2 ^ 60)) hUX
  have hVtX : isz (Int.tdiv V (2 ^ 60)) ≤ X :=
    le_trans (Work.Fx.isz_tdiv_le V (2 ^ 60)) hVX
  -- membership bounds for the two windows that are scanned by `roll`
  have hmem0 : ∀ v ∈ ([Val.int U, Val.int V] : List Val), vsz v ≤ X :=
    Cis.vsz_mem_pair (by rw [vsz_int]; exact hUX) (by rw [vsz_int]; exact hVX)
  have hmem4 : ∀ v ∈ ([Val.int (Int.tdiv V (2 ^ 60)), Val.int U] : List Val), vsz v ≤ X :=
    Cis.vsz_mem_pair (by rw [vsz_int]; exact hVtX) (by rw [vsz_int]; exact hUX)
  -- step 1: `roll 1` -- `[U, V] ↦ [V, U]`
  have s1 : Cis.Pipe main (rollP 1) [Val.int U, Val.int V] [Val.int V, Val.int U]
      (Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.rw (Cis.Pipe.roll (prog := rollP) (K := Kr) main hroll
        (A := [Val.int U, Val.int V]) (k := 1) (by simp)) (by simp))
      (Cis.le_CB_roll (K := Kr) (KS := KS) (X := X) (k := 1) hKr (by omega) hmem0 (by simp) hX45)
  -- step 2: `pushVal 60` -- `[V, U] ↦ [60, V, U]`
  have s2 : Cis.Pipe main (pushP (Val.int 60)) [Val.int V, Val.int U]
      [Val.int 60, Val.int V, Val.int U] (Cis.CB X KS) :=
    Cis.Pipe.le (Cis.Pipe.pushOnAny (hpush main (Val.int 60)))
      (by
        have h := Cis.le_CB_one (K := Kpv) (KS := KS) (X := X) (v := 8) hKpv (by omega) hX2
        simpa [vsz_int, Cis.isz_sixty] using h)
  -- step 3: `swap` -- `[60, V, U] ↦ [V, 60, U]`
  have s3 : Cis.Pipe main swapP [Val.int 60, Val.int V, Val.int U]
      [Val.int V, Val.int 60, Val.int U] (Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.appendTail [Val.int U]
        (Cis.Pipe.swap (prog := swapP) (K := Ks) main hswap (Val.int 60) (Val.int V)))
      (by
        have h := Cis.le_CB_two (K := Ks) (KS := KS) (X := X) (u := 8) (v := isz V) hKs
          h60X hVX hX3
        simpa [vsz_int, Cis.isz_sixty] using h)
  -- step 4: `shrT` -- `[V, 60, U] ↦ [V / 2^60, U]`
  have s4 : Cis.Pipe main shrP [Val.int V, Val.int 60, Val.int U]
      [Val.int (Int.tdiv V (2 ^ 60)), Val.int U] (Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.appendTail [Val.int U]
        (Cis.Pipe.binOp (prog := shrP) (hshr main) (a := V) (b := (60 : ℤ)) (by norm_num)))
      (by
        have h := Cis.le_CB_add (K := Kst) (KS := KS) (X := X) (u := isz V) (v := isz (60 : ℤ))
          hKst hVX h60X hX2
        simpa using h)
  -- step 5: `roll 1` -- `[V / 2^60, U] ↦ [U, V / 2^60]`
  have s5 : Cis.Pipe main (rollP 1) [Val.int (Int.tdiv V (2 ^ 60)), Val.int U]
      [Val.int U, Val.int (Int.tdiv V (2 ^ 60))] (Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.rw (Cis.Pipe.roll (prog := rollP) (K := Kr) main hroll
        (A := [Val.int (Int.tdiv V (2 ^ 60)), Val.int U]) (k := 1) (by simp)) (by simp))
      (Cis.le_CB_roll (K := Kr) (KS := KS) (X := X) (k := 1) hKr (by omega) hmem4 (by simp) hX45)
  -- step 6: `pushVal 60` -- `[U, V / 2^60] ↦ [60, U, V / 2^60]`
  have s6 : Cis.Pipe main (pushP (Val.int 60)) [Val.int U, Val.int (Int.tdiv V (2 ^ 60))]
      [Val.int 60, Val.int U, Val.int (Int.tdiv V (2 ^ 60))] (Cis.CB X KS) :=
    Cis.Pipe.le (Cis.Pipe.pushOnAny (hpush main (Val.int 60)))
      (by
        have h := Cis.le_CB_one (K := Kpv) (KS := KS) (X := X) (v := 8) hKpv (by omega) hX2
        simpa [vsz_int, Cis.isz_sixty] using h)
  -- step 7: `swap` -- `[60, U, V / 2^60] ↦ [U, 60, V / 2^60]`
  have s7 : Cis.Pipe main swapP [Val.int 60, Val.int U, Val.int (Int.tdiv V (2 ^ 60))]
      [Val.int U, Val.int 60, Val.int (Int.tdiv V (2 ^ 60))] (Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.appendTail [Val.int (Int.tdiv V (2 ^ 60))]
        (Cis.Pipe.swap (prog := swapP) (K := Ks) main hswap (Val.int 60) (Val.int U)))
      (by
        have h := Cis.le_CB_two (K := Ks) (KS := KS) (X := X) (u := 8) (v := isz U) hKs
          h60X hUX hX3
        simpa [vsz_int, Cis.isz_sixty] using h)
  -- step 8: `shrT` -- `[U, 60, V / 2^60] ↦ [U / 2^60, V / 2^60]`
  have s8 : Cis.Pipe main shrP [Val.int U, Val.int 60, Val.int (Int.tdiv V (2 ^ 60))]
      [Val.int (Int.tdiv U (2 ^ 60)), Val.int (Int.tdiv V (2 ^ 60))] (Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.appendTail [Val.int (Int.tdiv V (2 ^ 60))]
        (Cis.Pipe.binOp (prog := shrP) (hshr main) (a := U) (b := (60 : ℤ)) (by norm_num)))
      (by
        have h := Cis.le_CB_add (K := Kst) (KS := KS) (X := X) (u := isz U) (v := isz (60 : ℤ))
          hKst hUX h60X hX2
        simpa using h)
  -- step 9: `consV` -- `[U / 2^60, V / 2^60] ↦ [cfxVal (U / 2^60, V / 2^60)]`
  have s9 : Cis.Pipe main consP [Val.int (Int.tdiv U (2 ^ 60)), Val.int (Int.tdiv V (2 ^ 60))]
      [Val.cons (Val.int (Int.tdiv U (2 ^ 60))) (Val.int (Int.tdiv V (2 ^ 60)))]
      (Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.consV (prog := consP) (K := Kc) main hcons (Val.int (Int.tdiv U (2 ^ 60)))
        (Val.int (Int.tdiv V (2 ^ 60))))
      (Cis.le_CB_consV (K := Kc) (KS := KS) (X := X) hKc (by omega))
  have hcomp : Cis.Pipe main
      (Cmd.seq (rollP 1) (Cmd.seq (pushP (Val.int 60)) (Cmd.seq swapP (Cmd.seq shrP
        (Cmd.seq (rollP 1) (Cmd.seq (pushP (Val.int 60))
          (Cmd.seq swapP (Cmd.seq shrP consP))))))))
      [Val.int U, Val.int V]
      [Val.cons (Val.int (Int.tdiv U (2 ^ 60))) (Val.int (Int.tdiv V (2 ^ 60)))]
      (9 * Cis.CB X KS) :=
    Cis.Pipe.le
      (Cis.Pipe.comp s1 (Cis.Pipe.comp s2 (Cis.Pipe.comp s3 (Cis.Pipe.comp s4
        (Cis.Pipe.comp s5 (Cis.Pipe.comp s6 (Cis.Pipe.comp s7 (Cis.Pipe.comp s8 s9))))))))
      (le_of_eq (by ring))
  have hcost : 9 * Cis.CB X KS = (9 * KS * 32 ^ 32) * M ^ 32 := by
    rw [Cis.CB, hXdef, Nat.mul_pow]
    ring
  refine Cis.PipeQ.mono (Cis.PipeQ.le (Cis.Pipe.toPipeQ hcomp) (le_of_eq hcost)) ?_
  intro o ho
  rw [ho]
  rfl

end Work.Fx
