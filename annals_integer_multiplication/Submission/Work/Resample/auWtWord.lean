import Mathlib
import Submission.Work.Resample.auKit2
import Submission.Work.Resample.auRoundP
import Submission.Work.Resample.auPreWord
import Submission.Work.Resample.auPipeC
import Submission.Work.Fx.expRec

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

namespace Work.Resample
open HvdH Work.Fx

theorem pow_bound (M p : ℕ) (hM : 1 ≤ M) (hp : 2 ≤ p + 1) :
    M * (p + 1) ^ 3 ≤ (4 * M + 1) * (p + 1) ^ (4 * M + 1) := by
  have h1 : (p + 1) ^ (4 * M + 1) = (p + 1) ^ 3 * (p + 1) ^ (4 * M - 2) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h1]
  have h2 : M ≤ (p + 1) ^ (4 * M - 2) := by
    have h3 : (2 : ℕ) ^ (4 * M - 2) ≤ (p + 1) ^ (4 * M - 2) :=
      Nat.pow_le_pow_left hp _
    have h4 : M ≤ 2 ^ (4 * M - 2) := by
      have h5 := Nat.lt_two_pow_self (n := 4 * M - 2)
      omega
    exact le_trans h4 h3
  calc M * (p + 1) ^ 3 ≤ (p + 1) ^ (4 * M - 2) * (p + 1) ^ 3 :=
        Nat.mul_le_mul_right _ h2
    _ = (p + 1) ^ 3 * (p + 1) ^ (4 * M - 2) := by ring
    _ ≤ (4 * M + 1) * ((p + 1) ^ 3 * (p + 1) ^ (4 * M - 2)) :=
        Nat.le_mul_of_pos_left _ (by omega)

theorem vsz_mem_single {M : ℕ} {v : Val} (h : vsz v ≤ M) :
    ∀ w ∈ ([v] : List Val), vsz w ≤ M := by
  intro w hw
  rw [List.mem_singleton] at hw
  rw [hw]
  exact h

theorem vsz_mem_append {M : ℕ} {A B : List Val} (hA : ∀ v ∈ A, vsz v ≤ M)
    (hB : ∀ v ∈ B, vsz v ≤ M) : ∀ v ∈ A ++ B, vsz v ≤ M := by
  intro v hv
  rcases List.mem_append.mp hv with h | h
  · exact hA v h
  · exact hB v h

theorem auWtWord (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α t : ℕ) (N : ℤ),
      (0 ≤ N) → (N ≤ (2 : ℤ) ^ (4 * p + 8)) → (1 ≤ t) → (t < 2 ^ p) → (α ≤ 2 ^ p) →
      HvdH.WordR main prog
        (fun vs => ∃ rest, vs = [HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ),
          HvdH.Val.int (t : ℤ), HvdH.Val.int N, HvdH.Val.int (auPi p)] ++ rest)
        (fun vs out => ∃ rest, vs = [HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ),
          HvdH.Val.int (t : ℤ), HvdH.Val.int N, HvdH.Val.int (auPi p)] ++ rest ∧
          out = HvdH.Val.int (auWt p α t N) :: rest)
        (fun _ => K * (p + 1) ^ K) := by
  have hPreW : ∃ (pre : HvdH.Cmd) (KS : ℕ),
      ∀ (main : HvdH.Cmd) (p α t : ℕ) (N : ℤ),
        (1 ≤ p) → (0 ≤ N) → (N ≤ (2 : ℤ) ^ (4 * p + 8)) → (1 ≤ t) → (t < 2 ^ p) →
        (α ≤ 2 ^ p) →
        HvdH.WordR main pre
          (fun vs => ∃ rest, vs = [HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ),
            HvdH.Val.int (t : ℤ), HvdH.Val.int N, HvdH.Val.int (auPi p)] ++ rest)
          (fun vs out => ∃ rest, vs = [HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ),
            HvdH.Val.int (t : ℤ), HvdH.Val.int N, HvdH.Val.int (auPi p)] ++ rest ∧
            out = [HvdH.Val.int (auFlg p α t N), HvdH.Val.int ((auNstep p : ℕ) : ℤ),
              HvdH.Val.int (auEn p), HvdH.Val.int (auZ p α t N), HvdH.Val.int (auEn p),
              HvdH.Val.int (auEn2 p α)] ++ rest)
          (fun _ => 300 * auSB p KS) := auPreWord hk hi
  obtain ⟨pre, KSpre, hPre⟩ := hPreW
  obtain ⟨body, KSrd, hRound⟩ := auRoundWordP hk hi
  obtain ⟨ifzC, Kifz, hIfz⟩ := hk.ifZero
  obtain ⟨loopC, Kloop, hLoop⟩ := hk.loop
  obtain ⟨pushP, Kpush, hPush⟩ := hk.pushVal
  obtain ⟨dropP, Kdrop, hDrop⟩ := hk.drop
  obtain ⟨swapP, Kswap, hSwap⟩ := hk.swap
  obtain ⟨rollP, Kroll, hRoll⟩ := hk.roll
  obtain ⟨pickP, Kpick, hPick⟩ := hk.pick
  obtain ⟨eqP, Keq, hEq⟩ := hi.eq
  obtain ⟨tdivP, Ktdiv, hTdiv⟩ := hi.tdiv
  set KS : ℕ := KSpre + KSrd + Kifz + Kloop + Kpush + Kdrop + Kswap + Kroll + Kpick + Keq
    + Ktdiv + 1 with hKS
  have hKSpre : KSpre ≤ KS := by omega
  have hKSrd : KSrd ≤ KS := by omega
  have hKifz : Kifz ≤ KS := by omega
  have hKloop : Kloop ≤ KS := by omega
  have hKpush : Kpush ≤ KS := by omega
  have hKdrop : Kdrop ≤ KS := by omega
  have hKswap : Kswap ≤ KS := by omega
  have hKroll : Kroll ≤ KS := by omega
  have hKpick : Kpick ≤ KS := by omega
  have hKeq : Keq ≤ KS := by omega
  have hKtdiv : Ktdiv ≤ KS := by omega
  set Cc : ℕ := 5 * 10 ^ 9 * KS + 1 with hCc
  let alphaFlagP : Cmd := .seq (pickP 1) (.seq (pushP (Val.int 0)) eqP)
  let qZeroP : Cmd :=
    .seq dropP (.seq dropP (.seq dropP (.seq dropP (.seq dropP (pushP (Val.int 0))))))
  let qStopP : Cmd :=
    .seq dropP (.seq dropP (.seq dropP (.seq dropP (.seq dropP (pushP (Val.int 0))))))
  let cleanupP : Cmd := .seq (rollP 1) (.seq (rollP 4) (.seq swapP (.seq tdivP (.seq (rollP 3)
      (.seq dropP (.seq (rollP 2) (.seq dropP (.seq (rollP 1) dropP))))))))
  let qLoopP : Cmd := .seq (loopC body) cleanupP
  let qMainP : Cmd := .seq pre (ifzC qLoopP qStopP)
  let prog : Cmd := .seq alphaFlagP (ifzC qMainP qZeroP)
  refine ⟨prog, 4 * Cc + 1, ?_⟩
  intro main p α t N hN0 hN h1t htp hα
  have hNz : N.natAbs ≤ 2 ^ (4 * p + 8) := by
    have h2 : N ≤ ((2 : ℕ) ^ (4 * p + 8) : ℤ) := by
      calc N ≤ (2 : ℤ) ^ (4 * p + 8) := hN
        _ = ((2 : ℕ) ^ (4 * p + 8) : ℤ) := by push_cast; ring
    have h3 : ((N.natAbs : ℕ) : ℤ) ≤ ((2 ^ (4 * p + 8) : ℕ) : ℤ) := by
      rw [Int.natAbs_of_nonneg hN0]
      exact h2
    exact_mod_cast h3
  have hp1 : 1 ≤ p := by
    by_contra hc
    push_neg at hc
    have h0 : p = 0 := by omega
    rw [h0] at htp
    norm_num at htp
    omega

  -- ============ size facts ============
  have hsz_p : isz ((p : ℤ)) ≤ auSZ p := by
    rw [isz, Int.natAbs_natCast]
    have h1 : p.size ≤ p := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p))
    simp only [auSZ]; omega
  have hsz_α : isz ((α : ℤ)) ≤ auSZ p := isz_le_pow2 hα
  have hsz_t : isz ((t : ℤ)) ≤ auSZ p := isz_le_pow2 (le_of_lt htp)
  have hsz_N : isz N ≤ auSZ p := by
    rw [isz]
    have h1 : N.natAbs.size ≤ 4 * p + 9 :=
      Nat.size_le.mpr (lt_of_le_of_lt hNz
        (Nat.pow_lt_pow_right one_lt_two (by omega : 4 * p + 8 < 4 * p + 9)))
    simp only [auSZ]; omega
  have hsz_pi : isz (auPi p) ≤ auSZ p := isz_auPi_le p
  have hsz_zero : isz (0 : ℤ) ≤ auSZ p := isz_const_le p (by norm_num)
  have hsz_one : isz (1 : ℤ) ≤ auSZ p := isz_const_le p (by norm_num)
  have hsz_ten : isz (10 : ℤ) ≤ auSZ p := isz_const_le p (by norm_num)
  have hsz_hundred : isz (100 : ℤ) ≤ auSZ p := isz_const_le p (by norm_num)
  have hsz_E : isz (auEn p) ≤ auSZ p := isz_auEn_le p
  have hsz_E2 : isz (auEn2 p α) ≤ auSZ p := isz_auEn2_le p α hα
  have hsz_Z : isz (auZ p α t N) ≤ auSZ p := isz_auZ_le p α t N hNz
  have hsz_fl : isz (auFlg p α t N) ≤ auSZ p := isz_auFlg_le p α t N
  have hsz_fla : isz (if (0 : ℤ) = (α : ℤ) then 1 else 0) ≤ auSZ p := by
    rw [isz]; split <;> norm_num <;> simp only [auSZ] <;> omega
  have hsz_m : isz (((auNstep p : ℕ) : ℤ)) ≤ auSZ p := isz_auNstep_le p
  have hvsz_p : vsz (Val.int (p : ℤ)) ≤ auSZ p := by rw [vsz_int]; exact hsz_p
  have hvsz_α : vsz (Val.int (α : ℤ)) ≤ auSZ p := by rw [vsz_int]; exact hsz_α
  have hvsz_t : vsz (Val.int (t : ℤ)) ≤ auSZ p := by rw [vsz_int]; exact hsz_t
  have hvsz_N : vsz (Val.int N) ≤ auSZ p := by rw [vsz_int]; exact hsz_N
  have hvsz_pi : vsz (Val.int (auPi p)) ≤ auSZ p := by rw [vsz_int]; exact hsz_pi
  have hvsz_zero : vsz (Val.int (0 : ℤ)) ≤ auSZ p := by rw [vsz_int]; exact hsz_zero
  have hvsz_E : vsz (Val.int (auEn p)) ≤ auSZ p := by rw [vsz_int]; exact hsz_E
  have hvsz_E2 : vsz (Val.int (auEn2 p α)) ≤ auSZ p := by rw [vsz_int]; exact hsz_E2
  have hvsz_Z : vsz (Val.int (auZ p α t N)) ≤ auSZ p := by rw [vsz_int]; exact hsz_Z
  have hvsz_m : vsz (Val.int ((auNstep p : ℕ) : ℤ)) ≤ auSZ p := by rw [vsz_int]; exact hsz_m
  have hvsz_fla : vsz (Val.int (if (0 : ℤ) = (α : ℤ) then 1 else 0)) ≤ auSZ p := by
    rw [vsz_int]; exact hsz_fla
  have hone : 1 ≤ auSZ p := by simp only [auSZ]; omega
  have hsum3 : auSB p KS + (auSB p KS + auSB p KS) ≤ 3 * auSB p KS := by omega
  have hsum6 : auSB p KS + (auSB p KS + (auSB p KS + (auSB p KS + (auSB p KS + auSB p KS))))
      ≤ 6 * auSB p KS := by omega
  have hsum10 : auSB p KS + (auSB p KS + (auSB p KS + (auSB p KS + (auSB p KS
      + (auSB p KS + (auSB p KS + (auSB p KS + (auSB p KS + auSB p KS))))))))
      ≤ 10 * auSB p KS := by omega
  have hsum7 : auSB p KS + (auSB p KS + (auSB p KS + (auSB p KS + (auSB p KS
      + (auSB p KS + auSB p KS))))) ≤ 10 * auSB p KS := by omega
  -- ============ the alpha flag ============
  have hAlpha : Pipe main alphaFlagP
      [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (t : ℤ), Val.int N, Val.int (auPi p)]
      [Val.int (if (0 : ℤ) = (α : ℤ) then (1 : ℤ) else 0), Val.int (p : ℤ), Val.int (α : ℤ),
        Val.int (t : ℤ), Val.int N, Val.int (auPi p)] (3 * auSB p KS) := by
    have s1 := Pipe.le (Pipe.pickAt main hPick
      (A := [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (t : ℤ), Val.int N, Val.int (auPi p)])
      (k := 1) (by simp) (v := Val.int (α : ℤ)) (rfl))
      (au_le_roll hKpick (by simp) (by simp)
        (vsz_mem_append (vsz_mem_single hvsz_p)
          (vsz_mem_append (vsz_mem_single hvsz_α)
            (vsz_mem_append (vsz_mem_single hvsz_t)
              (vsz_mem_append (vsz_mem_single hvsz_N) (vsz_mem_single hvsz_pi))))))
    have s2 := Pipe.le (Pipe.pushOnAny
      (T := [Val.int (α : ℤ), Val.int (p : ℤ), Val.int (α : ℤ), Val.int (t : ℤ), Val.int N,
        Val.int (auPi p)]) (hPush main (Val.int 0))) (au_le_one hKpush hvsz_zero)
    have s3 := Pipe.le (Pipe.appendTail
      [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (t : ℤ), Val.int N, Val.int (auPi p)]
      (Pipe.binOp (hEq main) (a := (0 : ℤ)) (b := (α : ℤ)) trivial))
      (au_le_two hKeq hsz_zero hsz_α)
    exact Pipe.le (Pipe.comp s1 (Pipe.comp s2 s3)) hsum3
  -- ============ the zero branch ============
  have hQZero : Pipe main qZeroP
      [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (t : ℤ), Val.int N, Val.int (auPi p)]
      [Val.int (0 : ℤ)] (6 * auSB p KS) := by
    have s1 := Pipe.le (Pipe.appendTail
      [Val.int (α : ℤ), Val.int (t : ℤ), Val.int N, Val.int (auPi p)]
      (Pipe.drop main hDrop (Val.int (p : ℤ)))) (au_le_one hKdrop hvsz_p)
    have s2 := Pipe.le (Pipe.appendTail
      [Val.int (t : ℤ), Val.int N, Val.int (auPi p)]
      (Pipe.drop main hDrop (Val.int (α : ℤ)))) (au_le_one hKdrop hvsz_α)
    have s3 := Pipe.le (Pipe.appendTail
      [Val.int N, Val.int (auPi p)]
      (Pipe.drop main hDrop (Val.int (t : ℤ)))) (au_le_one hKdrop hvsz_t)
    have s4 := Pipe.le (Pipe.appendTail
      [Val.int (auPi p)]
      (Pipe.drop main hDrop (Val.int N))) (au_le_one hKdrop hvsz_N)
    have s5 := Pipe.le (Pipe.appendTail ([] : List Val)
      (Pipe.drop main hDrop (Val.int (auPi p)))) (au_le_one hKdrop hvsz_pi)
    have s6 := Pipe.le (Pipe.pushOnAny (T := ([] : List Val)) (hPush main (Val.int 0)))
      (au_le_one hKpush hvsz_zero)
    exact Pipe.le (Pipe.comp s1 (Pipe.comp s2 (Pipe.comp s3 (Pipe.comp s4 (Pipe.comp s5 s6))))) hsum6
  -- ============ the pre ============
  have hPreP : Pipe main pre
      [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (t : ℤ), Val.int N, Val.int (auPi p)]
      [Val.int (auFlg p α t N), Val.int ((auNstep p : ℕ) : ℤ), Val.int (auEn p),
        Val.int (auZ p α t N), Val.int (auEn p), Val.int (auEn2 p α)] (300 * auSB p KS) := by
    intro rest vs hvs s R hR
    rw [hvs] at hR
    obtain ⟨out, s', n, ⟨rest', hvs', hout'⟩, hev, hn, hstk, hoth⟩ :=
      hPre main p α t N hp1 hN0 hN h1t htp hα
        ([Val.int (p : ℤ), Val.int (α : ℤ), Val.int (t : ℤ), Val.int N, Val.int (auPi p)] ++ rest)
        ⟨rest, rfl⟩ s R hR
    have hrr : rest' = rest := (List.append_cancel_left hvs').symm
    refine ⟨out, s', n, by rw [hout', hrr], hev,
      le_trans hn (Nat.mul_le_mul_left 300 (auSB_mono hKSpre)), hstk, hoth⟩
  -- ============ the stop branch ============
  have hStopP : Pipe main qStopP
      [Val.int ((auNstep p : ℕ) : ℤ), Val.int (auEn p), Val.int (auZ p α t N),
        Val.int (auEn p), Val.int (auEn2 p α)]
      [Val.int (0 : ℤ)] (6 * auSB p KS) := by
    have s1 := Pipe.le (Pipe.appendTail
      [Val.int (auEn p), Val.int (auZ p α t N), Val.int (auEn p), Val.int (auEn2 p α)]
      (Pipe.drop main hDrop (Val.int ((auNstep p : ℕ) : ℤ)))) (au_le_one hKdrop hvsz_m)
    have s2 := Pipe.le (Pipe.appendTail
      [Val.int (auZ p α t N), Val.int (auEn p), Val.int (auEn2 p α)]
      (Pipe.drop main hDrop (Val.int (auEn p)))) (au_le_one hKdrop hvsz_E)
    have s3 := Pipe.le (Pipe.appendTail
      [Val.int (auEn p), Val.int (auEn2 p α)]
      (Pipe.drop main hDrop (Val.int (auZ p α t N)))) (au_le_one hKdrop hvsz_Z)
    have s4 := Pipe.le (Pipe.appendTail
      [Val.int (auEn2 p α)]
      (Pipe.drop main hDrop (Val.int (auEn p)))) (au_le_one hKdrop hvsz_E)
    have s5 := Pipe.le (Pipe.appendTail ([] : List Val)
      (Pipe.drop main hDrop (Val.int (auEn2 p α)))) (au_le_one hKdrop hvsz_E2)
    have s6 := Pipe.le (Pipe.pushOnAny (T := ([] : List Val)) (hPush main (Val.int 0)))
      (au_le_one hKpush hvsz_zero)
    exact Pipe.le (Pipe.comp s1 (Pipe.comp s2 (Pipe.comp s3 (Pipe.comp s4 (Pipe.comp s5 s6))))) hsum6
  -- ============ the loop ============
  have hLoopG : ∀ Qf : ℕ → ℤ, (∀ i, Qf i = auH p (-(auZ p α t N)) i) →
        (∀ i, i ≤ auNstep p → (Qf i).natAbs ≤ 2 ^ (5 * p + 130)) →
        (auZ p α t N ≤ auBnd p) → Pipe main (loopC body)
          [Val.int ((auNstep p : ℕ) : ℤ), Val.int (auEn p), Val.int (auZ p α t N),
            Val.int (auEn p), Val.int (auEn2 p α)]
          [Val.int (0 : ℤ), Val.int (Qf (auNstep p)), Val.int (auZ p α t N),
            Val.int (auEn p), Val.int (auEn2 p α)]
          ((auNstep p + 1) * (100 * auSB p KS + Kloop) + Kloop) := by
      intro Qf hQf hQs hguard
      have hZg : (auZ p α t N).natAbs ≤ 2 ^ (4 * p + 110) :=
        natAbs_auZ_guard p α t N (auZ_nonneg p α t N hN0) hguard
      have hEg : (auEn p).natAbs ≤ 2 ^ (3 * p + 101) := by
        have h : auEn p = (2 : ℤ) ^ (3 * p + 100) := by
          rw [auEn, show auPrec p = 3 * p + 100 from rfl]
        rw [h]
        have h2 : ((2 : ℤ) ^ (3 * p + 100)).natAbs = 2 ^ (3 * p + 100) := by
          rw [Int.natAbs_pow]
          norm_num
        rw [h2]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hE2g : (auEn2 p α).natAbs ≤ 2 ^ (3 * p + 104) := by
        have h := natAbs_auEn2_le p α hα
        exact le_trans h (Nat.pow_le_pow_right (by norm_num) (by omega))
      intro rest
      let I : ℕ → List Val → Prop := fun i vs => i < auNstep p ∧
        vs = [Val.int ((auNstep p - i : ℕ) : ℤ), Val.int (Qf i),
          Val.int (auZ p α t N), Val.int (auEn p), Val.int (auEn2 p α)] ++ rest
      let F : List Val → Prop := fun vs =>
        vs = [Val.int (0 : ℤ), Val.int (Qf (auNstep p)),
          Val.int (auZ p α t N), Val.int (auEn p), Val.int (auEn2 p α)] ++ rest
      have hbody : ∀ i vs, I i vs → WordR main body (fun w => w = vs)
          (fun _ out => ∃ vs', (out = Val.int 0 :: vs' ∧ F vs') ∨
            (out = Val.int 1 :: vs' ∧ I (i + 1) vs' ∧ i + 1 < auNstep p))
          (fun _ => 100 * auSB p KS) := by
        intro i vs hI
        obtain ⟨hilt, hvs⟩ := hI
        subst hvs
        have hpos : (0 : ℤ) < ((auNstep p - i : ℕ) : ℤ) := by
          have h : 0 < auNstep p - i := Nat.sub_pos_of_lt hilt
          exact_mod_cast h
        have hEpos : (0 : ℤ) < auEn p := auEn_pos p
        have hcntsz : (((auNstep p - i : ℕ) : ℤ)).natAbs ≤ 2 ^ (p + 11) := by
          rw [Int.natAbs_natCast]
          have h1 : auNstep p - i ≤ auNstep p := Nat.sub_le _ _
          have h2 : auNstep p ≤ 2 ^ (p + 11) := by
            have h3 : auNstep p ≤ 206 * 2 ^ p := by
              rw [auNstep, auPrec]
              have h4 : p ≤ 2 ^ p := le_of_lt (Nat.lt_two_pow_self (n := p))
              have h5 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
              have h6 : 6 * p ≤ 6 * 2 ^ p := Nat.mul_le_mul_left 6 h4
              have h7 : 200 ≤ 200 * 2 ^ p := by nlinarith
              have h8 : 2 * (3 * p + 100) = 6 * p + 200 := by ring
              rw [h8]
              linarith
            calc auNstep p ≤ 206 * 2 ^ p := h3
              _ ≤ 256 * 2 ^ p := Nat.mul_le_mul_right _ (by norm_num)
              _ = 2 ^ (p + 8) := by
                  rw [show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_add, Nat.add_comm]
              _ ≤ 2 ^ (p + 11) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have hQg : (Qf i).natAbs ≤ 2 ^ (5 * p + 130) := hQs i (le_of_lt hilt)
        intro w hw s R hR
        rw [hw] at hR
        obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ :=
          (hRound main p ((auNstep p - i : ℕ) : ℤ) (auZ p α t N) (auEn p) (auEn2 p α)
            (Qf i) rest hpos hEpos hcntsz hZg hQg hEg hE2g)
            _ rfl s R hR
        refine ⟨out, s', n, ?_, hev, le_trans hn (Nat.mul_le_mul_left 100 (auSB_mono hKSrd)),
          hstk, hoth⟩
        have hsub1 : ((auNstep p - i : ℕ) : ℤ) - 1 = ((auNstep p - (i + 1) : ℕ) : ℤ) := by
          have h1 : ((auNstep p - i : ℕ) : ℤ) = (auNstep p : ℤ) - (i : ℤ) :=
            Nat.cast_sub (le_of_lt hilt)
          have h2 : ((auNstep p - (i + 1) : ℕ) : ℤ) = (auNstep p : ℤ) - ((i + 1 : ℕ) : ℤ) :=
            Nat.cast_sub (by omega : i + 1 ≤ auNstep p)
          rw [h1, h2]
          push_cast
          ring
        have hQrec : auEn p + Int.tdiv (Int.tdiv (-(auZ p α t N * Qf i))
              (auEn p)) ((auNstep p - i : ℕ) : ℤ) = Qf (i + 1) := by
          rw [hQf i, hQf (i + 1)]
          rw [auH_succ, auEn,
            show ((auNstep p - i : ℕ) : ℤ) = (auNstep p : ℤ) - (i : ℤ) from
              Nat.cast_sub (le_of_lt hilt),
            show (-(auZ p α t N * auH p (-(auZ p α t N)) i) : ℤ)
              = (-(auZ p α t N)) * auH p (-(auZ p α t N)) i by ring]
        rcases lt_or_eq_of_le (show i + 1 ≤ auNstep p by omega) with hlt2 | heq2
        · refine ⟨[Val.int ((auNstep p - (i + 1) : ℕ) : ℤ),
            Val.int (Qf (i + 1)), Val.int (auZ p α t N), Val.int (auEn p),
            Val.int (auEn2 p α)] ++ rest, Or.inr ⟨?_, ?_, hlt2⟩⟩
          · rw [hout, hsub1, hQrec]
            have hp : (0 : ℤ) < ((auNstep p - (i + 1) : ℕ) : ℤ) := by
              have h : 0 < auNstep p - (i + 1) := Nat.sub_pos_of_lt hlt2
              exact_mod_cast h
            split
            · rfl
            · exact absurd hp (by assumption)
          · exact ⟨hlt2, rfl⟩
        · refine ⟨[Val.int (0 : ℤ), Val.int (Qf (auNstep p)),
            Val.int (auZ p α t N), Val.int (auEn p), Val.int (auEn2 p α)] ++ rest,
            Or.inl ⟨?_, rfl⟩⟩
          have hsub0 : ((auNstep p - i : ℕ) : ℤ) - 1 = 0 := by
            have h1 : ((auNstep p - i : ℕ) : ℤ) = (auNstep p : ℤ) - (i : ℤ) :=
              Nat.cast_sub (le_of_lt hilt)
            have h2 : (i : ℤ) = (auNstep p : ℤ) - 1 := by
              have : (i + 1 : ℕ) = auNstep p := by omega
              rw [← this]; push_cast; ring
            rw [h1, h2]; ring
          have hQ0 : auEn p + Int.tdiv (Int.tdiv (-(auZ p α t N * Qf i))
                (auEn p)) ((auNstep p - i : ℕ) : ℤ) = Qf (auNstep p) := by
            rw [hQrec, heq2]
          rw [hout, hsub0, hQ0]
          split
          · exfalso; omega
          · rfl
      have hI0 : I 0 ([Val.int ((auNstep p : ℕ) : ℤ), Val.int (auEn p), Val.int (auZ p α t N),
          Val.int (auEn p), Val.int (auEn2 p α)] ++ rest) := by
        refine ⟨by rw [auNstep, auPrec]; omega, ?_⟩
        rw [hQf 0]
        rfl
      have hloop := hLoop main body I F (100 * auSB p KS) (auNstep p) hbody
      intro vs hvs s R hR
      rw [hvs] at hR
      obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := hloop _ hI0 s R hR
      exact ⟨out, s', n, hout, hev, hn, hstk, hoth⟩
  have hCleanG : ∀ Qv : ℤ, Qv = auH p (-(auZ p α t N)) (auNstep p) →
        Qv.natAbs ≤ 2 ^ (5 * p + 130) →
        (auZ p α t N ≤ auBnd p) → (α ≠ 0) → Pipe main cleanupP
          [Val.int (0 : ℤ), Val.int Qv, Val.int (auZ p α t N), Val.int (auEn p),
            Val.int (auEn2 p α)]
          [Val.int (auWt p α t N)] (10 * auSB p KS) := by
    intro Qv hQv hQm hguard hα0
    have hszQv : isz Qv ≤ auSZ p := by
      rw [isz]
      have h1 : Qv.natAbs.size ≤ 5 * p + 131 :=
        Nat.size_le.mpr (lt_of_le_of_lt hQm
          (Nat.pow_lt_pow_right one_lt_two (by omega : 5 * p + 130 < 5 * p + 131)))
      simp only [auSZ]; omega
    have hvszQv : vsz (Val.int Qv) ≤ auSZ p := by rw [vsz_int]; exact hszQv
    have hszR : isz (Int.tdiv Qv (auEn2 p α)) ≤ auSZ p :=
      le_trans (isz_tdiv_le Qv (auEn2 p α)) hszQv
    have hvszR : vsz (Val.int (Int.tdiv Qv (auEn2 p α))) ≤ auSZ p := by
      rw [vsz_int]; exact hszR
    have hE2ne : auEn2 p α ≠ 0 := auEn2_ne_zero p α hα0
    intro rest
    have hP : WordR main cleanupP
        (fun vs => vs = [Val.int (0 : ℤ), Val.int Qv, Val.int (auZ p α t N),
          Val.int (auEn p), Val.int (auEn2 p α)] ++ rest)
        (fun _ out => out = [Val.int (Int.tdiv Qv (auEn2 p α))] ++ rest)
        (fun _ => 10 * auSB p KS) :=
      auPipeC rollP Kroll dropP Kdrop swapP Kswap tdivP Ktdiv hRoll hDrop hSwap hTdiv
        main KS p Qv (auZ p α t N) (auEn p) (auEn2 p α) rest
        hKroll hKdrop hKswap hKtdiv hszQv hsz_Z hsz_E hsz_E2 hE2ne
    intro vs hvs s R hR
    obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := hP vs hvs s R hR
    refine ⟨out, s', n, ?_, hev, hn, hstk, hoth⟩
    change out = Val.int (auWt p α t N) :: rest
    rw [hout, auWt_eq_of_guard p α t N hguard, ← hQv]
    rfl

  -- ============ the guard branch ============
  have hGuardW : (α ≠ 0) → Pipe main (ifzC qLoopP qStopP)
      [Val.int (auFlg p α t N), Val.int ((auNstep p : ℕ) : ℤ), Val.int (auEn p),
        Val.int (auZ p α t N), Val.int (auEn p), Val.int (auEn2 p α)]
      [Val.int (auWt p α t N)]
      (auSB p KS + ((auNstep p + 1) * (100 * auSB p KS + Kloop) + Kloop + 10 * auSB p KS)) := by
    intro hα0 rest
    have hq1 : (auFlg p α t N = 0 → WordR main qLoopP
        (fun vs => vs = [Val.int ((auNstep p : ℕ) : ℤ), Val.int (auEn p), Val.int (auZ p α t N),
          Val.int (auEn p), Val.int (auEn2 p α)] ++ rest)
        (fun _ out => out = [Val.int (auWt p α t N)] ++ rest)
        (fun _ => (auNstep p + 1) * (100 * auSB p KS + Kloop) + Kloop + 10 * auSB p KS)) := by
      intro hfl
      have hguard : auZ p α t N ≤ auBnd p := (auFlg_eq_zero_iff p α t N).mp hfl
      have hQs : ∀ i, i ≤ auNstep p → ((fun i => auH p (-(auZ p α t N)) i) i).natAbs
          ≤ 2 ^ (5 * p + 130) := by
        intro i hi
        exact auHSize p (auZ p α t N) (auZ_nonneg p α t N hN0) hguard i hi
      have hQm : (auH p (-(auZ p α t N)) (auNstep p)).natAbs ≤ 2 ^ (5 * p + 130) :=
        auHSize p (auZ p α t N) (auZ_nonneg p α t N hN0) hguard (auNstep p) (le_refl _)
      exact Pipe.comp (hLoopG (fun i => auH p (-(auZ p α t N)) i) (fun i => rfl) hQs hguard)
        (hCleanG (auH p (-(auZ p α t N)) (auNstep p)) rfl hQm hguard hα0) rest
    have hq2 : (auFlg p α t N ≠ 0 → WordR main qStopP
        (fun vs => vs = [Val.int ((auNstep p : ℕ) : ℤ), Val.int (auEn p), Val.int (auZ p α t N),
          Val.int (auEn p), Val.int (auEn2 p α)] ++ rest)
        (fun _ out => out = [Val.int (auWt p α t N)] ++ rest) (fun _ => 6 * auSB p KS)) := by
      intro hfl
      have hng : ¬ (auZ p α t N ≤ auBnd p) := fun hc => hfl ((auFlg_eq_zero_iff p α t N).mpr hc)
      have h0 : auWt p α t N = 0 := auWt_eq_zero_of_not_guard p α t N hng
      intro vs hvs s R hR
      obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := hStopP rest vs hvs s R hR
      exact ⟨out, s', n, by rw [hout, h0], hev, hn, hstk, hoth⟩
    have hres := hIfz main qLoopP qStopP (auFlg p α t N)
      ([Val.int ((auNstep p : ℕ) : ℤ), Val.int (auEn p), Val.int (auZ p α t N),
        Val.int (auEn p), Val.int (auEn2 p α)] ++ rest)
      (fun out => out = [Val.int (auWt p α t N)] ++ rest)
      (fun out => out = [Val.int (auWt p α t N)] ++ rest)
      ((auNstep p + 1) * (100 * auSB p KS + Kloop) + Kloop + 10 * auSB p KS)
      (6 * auSB p KS) hq1 hq2
    intro vs hvs s R hR
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hoth⟩ := hres vs hvs s R hR
    refine ⟨out, s', n, ?_, hev, le_trans hn ?_, hstk, hoth⟩
    · by_cases h : auFlg p α t N = 0
      · exact hpost.1 h
      · exact hpost.2 h
    · have h1 : Kifz * (isz (auFlg p α t N) + 1) ≤ auSB p KS := au_le_one hKifz hsz_fl
      have h2 : 6 * auSB p KS ≤ (auNstep p + 1) * (100 * auSB p KS + Kloop) + Kloop
          + 10 * auSB p KS := by nlinarith [auSB p KS]
      have h3 : max ((auNstep p + 1) * (100 * auSB p KS + Kloop) + Kloop + 10 * auSB p KS)
          (6 * auSB p KS) ≤ (auNstep p + 1) * (100 * auSB p KS + Kloop) + Kloop
          + 10 * auSB p KS := max_le le_rfl h2
      exact add_le_add h1 h3
  -- ============ the main branch ============
  have hQMainW : (α ≠ 0) → Pipe main qMainP
      [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (t : ℤ), Val.int N, Val.int (auPi p)]
      [Val.int (auWt p α t N)]
      (300 * auSB p KS + (auSB p KS + ((auNstep p + 1) * (100 * auSB p KS + Kloop)
        + Kloop + 10 * auSB p KS))) := by
    intro hα0
    exact Pipe.comp hPreP (hGuardW hα0)
  -- ============ the outer flag ============
  have hTopW : Pipe main (ifzC qMainP qZeroP)
      [Val.int (if (0 : ℤ) = (α : ℤ) then (1 : ℤ) else 0), Val.int (p : ℤ),
        Val.int (α : ℤ), Val.int (t : ℤ), Val.int N, Val.int (auPi p)]
      [Val.int (auWt p α t N)]
      (auSB p KS + (300 * auSB p KS + (auSB p KS
        + ((auNstep p + 1) * (100 * auSB p KS + Kloop) + Kloop + 10 * auSB p KS)))) := by
    intro rest
    have hq1 : ((if (0 : ℤ) = (α : ℤ) then (1 : ℤ) else 0) = 0 → WordR main qMainP
        (fun vs => vs = [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (t : ℤ), Val.int N,
          Val.int (auPi p)] ++ rest)
        (fun _ out => out = [Val.int (auWt p α t N)] ++ rest)
        (fun _ => 300 * auSB p KS + (auSB p KS + ((auNstep p + 1) * (100 * auSB p KS + Kloop)
          + Kloop + 10 * auSB p KS)))) := by
      intro hfl
      exact hQMainW ((eq_zero_flag α).mp hfl) rest
    have hq2 : ((if (0 : ℤ) = (α : ℤ) then (1 : ℤ) else 0) ≠ 0 → WordR main qZeroP
        (fun vs => vs = [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (t : ℤ), Val.int N,
          Val.int (auPi p)] ++ rest)
        (fun _ out => out = [Val.int (auWt p α t N)] ++ rest) (fun _ => 6 * auSB p KS)) := by
      intro hfl
      have hαz : α = 0 := (eq_zero_flag_ne α).mp hfl
      have h0 : auWt p α t N = 0 := by rw [hαz]; exact auWt_zero p t N
      intro vs hvs s R hR
      obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := hQZero rest vs hvs s R hR
      exact ⟨out, s', n, by rw [hout, h0], hev, hn, hstk, hoth⟩
    have hres := hIfz main qMainP qZeroP (if (0 : ℤ) = (α : ℤ) then (1 : ℤ) else 0)
      ([Val.int (p : ℤ), Val.int (α : ℤ), Val.int (t : ℤ), Val.int N, Val.int (auPi p)] ++ rest)
      (fun out => out = [Val.int (auWt p α t N)] ++ rest)
      (fun out => out = [Val.int (auWt p α t N)] ++ rest)
      (300 * auSB p KS + (auSB p KS + ((auNstep p + 1) * (100 * auSB p KS + Kloop)
        + Kloop + 10 * auSB p KS))) (6 * auSB p KS) hq1 hq2
    intro vs hvs s R hR
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hoth⟩ := hres vs hvs s R hR
    refine ⟨out, s', n, ?_, hev, le_trans hn ?_, hstk, hoth⟩
    · by_cases h : (if (0 : ℤ) = (α : ℤ) then (1 : ℤ) else 0) = 0
      · exact hpost.1 h
      · exact hpost.2 h
    · have h1 : Kifz * (isz ((if (0 : ℤ) = (α : ℤ) then (1 : ℤ) else 0)) + 1) ≤ auSB p KS :=
        au_le_one hKifz hsz_fla
      have h2 : 6 * auSB p KS ≤ 300 * auSB p KS + (auSB p KS + ((auNstep p + 1)
          * (100 * auSB p KS + Kloop) + Kloop + 10 * auSB p KS)) := by
        nlinarith [auSB p KS]
      have h3 : max (300 * auSB p KS + (auSB p KS + ((auNstep p + 1)
            * (100 * auSB p KS + Kloop) + Kloop + 10 * auSB p KS))) (6 * auSB p KS)
          ≤ 300 * auSB p KS + (auSB p KS + ((auNstep p + 1)
            * (100 * auSB p KS + Kloop) + Kloop + 10 * auSB p KS)) := max_le le_rfl h2
      exact add_le_add h1 h3
  -- ============ assemble ============
  have hAll : Pipe main prog
      [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (t : ℤ), Val.int N, Val.int (auPi p)]
      [Val.int (auWt p α t N)] (3 * auSB p KS + (auSB p KS + (300 * auSB p KS + (auSB p KS
        + ((auNstep p + 1) * (100 * auSB p KS + Kloop) + Kloop + 10 * auSB p KS))))) :=
    Pipe.comp hAlpha hTopW
  intro vs hvs s R hR
  obtain ⟨rest0, hvs0⟩ := hvs
  rw [hvs0] at hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := hAll rest0 _ rfl s R hR
  refine ⟨out, s', n, ⟨rest0, hvs0, hout⟩, hev, ?_, hstk, hoth⟩
  refine le_trans hn ?_
  have hSB : auSB p KS ≤ 174724 * KS * (p + 1) ^ 2 := by
    rw [auSB]
    have h1 : auSZ p + 8 ≤ 418 * (p + 1) := by simp only [auSZ]; omega
    calc KS * (auSZ p + 8) ^ 2 ≤ KS * (418 * (p + 1)) ^ 2 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 2)
      _ = 174724 * KS * (p + 1) ^ 2 := by ring
  have hA : KS * (p + 1) ^ 2 ≤ KS * (p + 1) ^ 3 := Nat.mul_le_mul_left _ (by nlinarith)
  have hKL2 : Kloop ≤ KS * (p + 1) ^ 2 := by
    have h1 : KS ≤ KS * (p + 1) ^ 2 := by
      calc KS = KS * 1 := by ring
        _ ≤ KS * (p + 1) ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
    exact le_trans hKloop h1
  have hm : auNstep p + 1 ≤ 201 * (p + 1) := by rw [auNstep, auPrec]; omega
  have hstep : (auNstep p + 1) * (100 * auSB p KS + Kloop) + Kloop
      ≤ 4000000000 * (KS * (p + 1) ^ 3) := by
    have h1 : (auNstep p + 1) * (100 * auSB p KS + Kloop)
        ≤ 201 * (p + 1) * (17472401 * (KS * (p + 1) ^ 2)) := by
      apply Nat.mul_le_mul hm
      calc 100 * auSB p KS + Kloop
            ≤ 100 * (174724 * KS * (p + 1) ^ 2) + KS * (p + 1) ^ 2 :=
            Nat.add_le_add (Nat.mul_le_mul_left 100 hSB) hKL2
        _ = 17472401 * (KS * (p + 1) ^ 2) := by ring
    have h2 : 201 * (p + 1) * (17472401 * (KS * (p + 1) ^ 2)) + KS * (p + 1) ^ 2
        ≤ 4000000000 * (KS * (p + 1) ^ 3) := by
      have h3 : KS * (p + 1) ^ 2 ≤ KS * (p + 1) ^ 3 := hA
      nlinarith
    exact le_trans (Nat.add_le_add h1 hKL2) h2
  have hCc' : Cc = 5 * 10 ^ 9 * KS + 1 := hCc
  have hfin : 3 * auSB p KS + (auSB p KS + (300 * auSB p KS + (auSB p KS
        + ((auNstep p + 1) * (100 * auSB p KS + Kloop) + Kloop + 10 * auSB p KS))))
      ≤ Cc * (p + 1) ^ 3 := by
    have hE : 3 * auSB p KS + (auSB p KS + (300 * auSB p KS + (auSB p KS
        + ((auNstep p + 1) * (100 * auSB p KS + Kloop) + Kloop + 10 * auSB p KS))))
        = 315 * auSB p KS + ((auNstep p + 1) * (100 * auSB p KS + Kloop) + Kloop) := by ring
    rw [hE]
    have hpp : (p + 1) ^ 2 ≤ (p + 1) ^ 3 := by nlinarith
    have hA2 : 174724 * KS * (p + 1) ^ 2 ≤ 174724 * KS * (p + 1) ^ 3 := by
      have h := Nat.mul_le_mul_left (174724 * KS) hpp
      simpa [mul_assoc] using h
    have h315 : 315 * auSB p KS ≤ 315 * (174724 * KS * (p + 1) ^ 2) :=
      Nat.mul_le_mul_left 315 hSB
    have hB : 315 * (174724 * KS * (p + 1) ^ 2) + 4000000000 * (KS * (p + 1) ^ 3)
        ≤ (5 * 10 ^ 9 * KS + 1) * (p + 1) ^ 3 := by
      have hKS1 : 1 ≤ KS := by omega
      have hb : KS * (p + 1) ^ 2 ≤ KS * (p + 1) ^ 3 := hA
      nlinarith
    have hcomb : 315 * auSB p KS + ((auNstep p + 1) * (100 * auSB p KS + Kloop) + Kloop)
        ≤ 315 * (174724 * KS * (p + 1) ^ 2) + 4000000000 * (KS * (p + 1) ^ 3) := by
      have h := hstep
      linarith
    exact le_trans hcomb (by rw [hCc']; exact hB)
  exact le_trans hfin (pow_bound Cc p (by omega) (by omega))

end Work.Resample
