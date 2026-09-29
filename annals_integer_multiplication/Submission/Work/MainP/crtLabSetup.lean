import Mathlib
import Submission.Work.MainP.crtLabDefs
import Submission.Work.MainP.crtLabSetupAux
import Submission.Work.MainP.crtLabSum
import Submission.Work.MainP.crtLabTabW
import Submission.Work.Kernel.Raw
-- import Submission.Work.MainP.crtLabTab

/-!
# `crtLabSetup`: the setup phase of the CRT label-and-sort word

From `int S :: intList ss` (with `S = ss.prod`) the word built here produces

`ofList (drv S) :: acc ss 0`,

i.e. the *driver list* `drv S` (`S` copies of `nil`, consumed one per odometer step by
`Work.MainP.crtLabLoop`) together with the *initial accumulator*
`acc ss 0 = cons (prp 0 (canon ss 0)) nil` — the pair of the current label `vlab ss 0 = 0` and the
initial odometer state `Est ss 0 = canon ss 0`.

The word is the composition of twelve steps, each stated as a `HvdH.WordR` with an *exact* value
stack (the toolkit is `Submission/Work/MainP/crtLabSetupAux.lean`):

1. the place-value table word `crtLabTab`: `intList ss ↦ ofList (canon ss 0)` (`K_tab`),
2. `pushVal (int 0)` and `consV`: the entry `prp 0 (canon ss 0)`,
3. `pushVal nil`, `swap`, `consV`: the accumulator `acc ss 0 = cons (prp 0 (canon ss 0)) nil`,
4. `swap`, `pushVal nil`, `swap`, `replicate`: the driver list `drv S`,
5. `roll 2`, `drop`: remove the `intList ss` that is no longer needed.

The cost is one table pass plus a constant number of linear passes; everything is absorbed into
`K · (vsz (intList ss) · (size S + 1) + (ss.length + 1) · (size S + 1) + S + 1)`.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

/-! ## Elementary facts about the initial accumulator and the sizes involved -/

/-- The initial accumulator, as the literal nested value the setup word builds. -/
theorem acc_zero_cons (ss : List ℕ) :
    acc ss 0 = Val.cons (Val.cons (Val.int 0) (ofList (canon ss 0))) Val.nil := by
  rw [acc_zero]
  simp [prp, vlab_zero, Est_zero]

theorem vsz_nil_val : vsz Val.nil = 1 := by simp [vsz, Val.enc]

theorem vsz_int_zero : vsz (Val.int (0 : ℤ)) = 2 := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, vsz_intNat]
  simp [iszN]

/-- Size of the entry `prp 0 (ofList (canon ss 0))`. -/
theorem vsz_int0_cons (ss : List ℕ) :
    vsz (Val.cons (Val.int 0) (ofList (canon ss 0))) = vsz (ofList (canon ss 0)) + 3 := by
  rw [vsz_cons, vsz_int_zero]; omega

/-- Size of the initial accumulator. -/
theorem vsz_acc_zero_eq (ss : List ℕ) :
    vsz (Val.cons (Val.cons (Val.int 0) (ofList (canon ss 0))) Val.nil)
      = vsz (ofList (canon ss 0)) + 5 := by
  rw [vsz_cons, vsz_int0_cons, vsz_nil_val]

/-- `crtLabSum` controls the size of the first canonical state. -/
theorem vsz_canon_zero_le {ss : List ℕ} {S : ℕ} (hS : S = ss.prod) (hpos : ∀ s ∈ ss, 1 ≤ s) :
    vsz (ofList (canon ss 0)) ≤ (ss.length + 1) * (3 * (S.size + 2) + 4) + 1 := by
  have h := crtLabSum (ss := ss) (S := S) hS hpos 0
  have hsz := h.2.2.2.2.2
  rwa [Est_zero] at hsz

/-- One step of the driver list. -/
theorem drv_succ (S : ℕ) : drv (S + 1) = Val.nil :: drv S := by
  simp [drv, List.replicate_succ]

/-- Size of the driver list. -/
theorem vsz_drv (S : ℕ) : vsz (ofList (drv S)) = 2 * S + 1 := by
  rw [vsz_ofList]
  have h : ((drv S).map vsz).sum = S := by
    induction S with
    | zero => simp [drv]
    | succ n ih =>
        rw [drv_succ, List.map_cons, List.sum_cons, ih, vsz_nil_val]
        omega
  rw [h, drv_length]; ring

/-- Re-bound the (constant) cost of an exact-stack `WordR`. -/
theorem wordR_cost_le (hK : KernelLib) {main p : Cmd} {L M : List Val} {c c' : ℕ}
    (h : WordR main p (fun vs => vs = L) (fun _ out => out = M) (fun _ => c)) (hc : c ≤ c') :
    WordR main p (fun vs => vs = L) (fun _ out => out = M) (fun _ => c') := by
  intro vs hvs s R hR
  cases hvs
  obtain ⟨out, s', n, hq, hev, hn, hstk, hfr⟩ := h L rfl s R hR
  exact ⟨out, s', n, hq, hev, le_trans hn hc, hstk, hfr⟩

/-- `KernelLib.dup` as a step. -/
private theorem step_dup {main p : Cmd} {K0 : ℕ}
    (h : WordR main p (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => K0 * (vsz (vs.headD .nil) + 1)))
    (a : Val) (tl : List Val) (c : ℕ) (hc : K0 * (vsz a + 1) ≤ c) :
    WordR main p (fun vs => vs = a :: tl) (fun _ out => out = a :: a :: tl) (fun _ => c) := by
  refine wordR_lift h (by simp) ?_ ?_
  · intro out hq
    obtain ⟨v, rest, hv, hout⟩ := hq
    simp only [List.cons.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact hout
  · simpa using hc

/-- The setup word, with the place-value table word `tab` as a parameter. -/
theorem crtLabSetup_word (hK : HvdH.KernelLib) (hI : HvdH.IntLib) (hL : HvdH.LayoutLib)
    (tabP : Cmd) (Ktab : ℕ)
    (hTab : ∀ (main : Cmd) (ss : List ℕ) (S : ℕ), (∀ s ∈ ss, 1 ≤ s) → S = ss.prod →
      WordR main tabP
        (fun vs => ∃ rest, vs = Val.int (S : ℤ) :: intList ss :: rest)
        (fun vs out => ∃ rest, vs = Val.int (S : ℤ) :: intList ss :: rest ∧
          out = ofList (canon ss 0) :: rest)
        (fun _ => Ktab * (vsz (intList ss) * (S.size + 1) + (ss.length + 1) * (S.size + 1) + 1))) :
    ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (ss : List ℕ) (S : ℕ),
    (∀ s ∈ ss, 1 ≤ s) → S = ss.prod →
    WordR main prog
      (fun vs => ∃ rest, vs = Val.int (S : ℤ) :: intList ss :: rest)
      (fun vs out => ∃ rest, vs = Val.int (S : ℤ) :: intList ss :: rest ∧
        out = ofList (drv S) :: acc ss 0 :: rest)
      (fun _ => K * (vsz (intList ss) * (S.size + 1) + (ss.length + 1) * (S.size + 1) + S + 1)) := by
  obtain ⟨repP, Krep, hRep⟩ := hL.replicate
  obtain ⟨pushP, Kpush, hPush⟩ := hK.pushVal
  obtain ⟨consP, Kcons, hCons⟩ := hK.consV
  obtain ⟨swapP, Kswap, hSwap⟩ := hK.swap
  obtain ⟨rollP, Kroll, hRoll⟩ := hK.roll
  obtain ⟨dupP, Kdup, hDup⟩ := hK.dup
  set K : ℕ := 200 * (Ktab + Kpush + Kcons + Kswap + Krep + Kroll + Kdup + 1) with hKdef
  let prog : Cmd :=
    .seq dupP (.seq (rollP 2) (.seq swapP (.seq tabP (.seq (pushP (Val.int 0))
      (.seq consP (.seq (pushP Val.nil) (.seq swapP (.seq consP (.seq swapP
        (.seq (pushP Val.nil) (.seq swapP repP)))))))))))
  refine ⟨prog, K, ?_⟩
  intro main ss S hpos hS
  set T : ℕ := vsz (intList ss) * (S.size + 1) + (ss.length + 1) * (S.size + 1) + S + 1 with hT
  -- ## size bounds
  have hT1 : 1 ≤ T := by omega
  have hA_le : vsz (intList ss) ≤ T := by
    rw [hT]
    have h : vsz (intList ss) * 1 ≤ vsz (intList ss) * (S.size + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hS_le : S + 1 ≤ T := by rw [hT]; omega
  have hW_le : S.size + 1 ≤ T := by
    rw [hT]
    have h : 1 * (S.size + 1) ≤ (ss.length + 1) * (S.size + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hSI_le : vsz (Val.int (S : ℤ)) ≤ 3 * T := by
    rw [vsz_intNat]; simp only [iszN]; omega
  have hE_le : vsz (ofList (canon ss 0)) ≤ 14 * T := by
    have h := vsz_canon_zero_le hS hpos
    have h1 : (ss.length + 1) * (3 * (S.size + 2) + 4) + 1 ≤ 14 * T := by
      rw [hT]
      have hA := Nat.le_mul_of_pos_right (vsz (intList ss)) (show 0 < S.size + 1 by omega)
      have hD : 0 < ss.length + 1 := by omega
      have hW : 1 ≤ S.size + 1 := by omega
      nlinarith [hA, hD, hW]
    omega
  have hA0_le : vsz (intList ss) * (S.size + 1) + (ss.length + 1) * (S.size + 1) + 1 ≤ T := by
    rw [hT]; omega
  -- ## the thirteen steps
  have hchain : ∀ tl : List Val, WordR main prog
      (fun vs => vs = Val.int (S : ℤ) :: intList ss :: tl)
      (fun _ out => out = ofList (drv S) ::
        Val.cons (Val.cons (Val.int 0) (ofList (canon ss 0))) Val.nil :: tl)
      (fun _ => K * T) := by
    intro tl
    -- 1. keep a copy of `S`: the table word below consumes it
    have s1 : WordR main dupP
        (fun vs => vs = Val.int (S : ℤ) :: intList ss :: tl)
        (fun _ out => out = Val.int (S : ℤ) :: Val.int (S : ℤ) :: intList ss :: tl)
        (fun _ => Kdup * (4 * T)) :=
      step_dup (hDup main) (Val.int (S : ℤ)) (intList ss :: tl) (Kdup * (4 * T))
        (by
          rw [vsz_intNat]
          simp only [iszN]
          have h := hW_le
          have h1 := hT1
          exact Nat.mul_le_mul_left Kdup (by omega))
    -- 2. move the modulus list to the top
    have s2 : WordR main (rollP 2)
        (fun vs => vs = Val.int (S : ℤ) :: Val.int (S : ℤ) :: intList ss :: tl)
        (fun _ out => out = intList ss :: Val.int (S : ℤ) :: Val.int (S : ℤ) :: tl)
        (fun _ => Kroll * (24 * T)) := by
      refine step_roll (hRoll main) 2
        (Val.int (S : ℤ) :: Val.int (S : ℤ) :: intList ss :: tl) (by simp <;> omega)
        (Kroll * (24 * T)) ?_
      have htake : (Val.int (S : ℤ) :: Val.int (S : ℤ) :: intList ss :: tl).take (2 + 1)
          = [Val.int (S : ℤ), Val.int (S : ℤ), intList ss] := by simp
      rw [htake]
      have hkey : (([Val.int (S : ℤ), Val.int (S : ℤ), intList ss]).map vsz).sum + 1 ≤ 8 * T := by
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        have h1 := hSI_le
        have h2 := hA_le
        have h3 := hT1
        omega
      calc Kroll * (2 + 1) * ((([Val.int (S : ℤ), Val.int (S : ℤ), intList ss]).map vsz).sum + 1)
          = Kroll * ((2 + 1) * ((([Val.int (S : ℤ), Val.int (S : ℤ), intList ss]).map vsz).sum + 1)) := by
            ring
        _ ≤ Kroll * (24 * T) := Nat.mul_le_mul_left Kroll (by omega)
    -- 3. the table word must see `int S :: intList ss`
    have s3 : WordR main swapP
        (fun vs => vs = intList ss :: Val.int (S : ℤ) :: Val.int (S : ℤ) :: tl)
        (fun _ out => out = Val.int (S : ℤ) :: intList ss :: Val.int (S : ℤ) :: tl)
        (fun _ => Kswap * (4 * T)) :=
      step_swap (hSwap main) (intList ss) (Val.int (S : ℤ)) (Val.int (S : ℤ) :: tl)
        (Kswap * (4 * T))
        (by
          rw [vsz_intNat]
          simp only [iszN]
          have h1 := hA_le
          have h2 := hW_le
          have h3 := hT1
          exact Nat.mul_le_mul_left Kswap (by omega))
    -- 4. the place-value table
    have s4 : WordR main tabP
        (fun vs => vs = Val.int (S : ℤ) :: intList ss :: Val.int (S : ℤ) :: tl)
        (fun _ out => out = ofList (canon ss 0) :: Val.int (S : ℤ) :: tl)
        (fun _ => Ktab * T) :=
      wordR_lift (hTab main ss S hpos hS) ⟨Val.int (S : ℤ) :: tl, rfl⟩ (by
        intro out hq
        obtain ⟨r, hr, hout⟩ := hq
        have hr' : r = Val.int (S : ℤ) :: tl := by simpa using hr.symm
        rw [hr'] at hout
        exact hout) (Nat.mul_le_mul_left Ktab hA0_le)
    -- 5. push the label `0`
    have s5 : WordR main (pushP (Val.int 0))
        (fun vs => vs = ofList (canon ss 0) :: Val.int (S : ℤ) :: tl)
        (fun _ out => out = Val.int 0 :: ofList (canon ss 0) :: Val.int (S : ℤ) :: tl)
        (fun _ => Kpush * (4 * T)) :=
      wordR_lift (hPush main (Val.int 0)) trivial (fun _ hq => hq) (by
        rw [vsz_int_zero]
        simpa using Nat.mul_le_mul_left Kpush (show (3 : ℕ) ≤ 4 * T by omega))
    -- 6. the entry `prp 0 (canon ss 0)`
    have s6 : WordR main consP
        (fun vs => vs = Val.int 0 :: ofList (canon ss 0) :: Val.int (S : ℤ) :: tl)
        (fun _ out => out = Val.cons (Val.int 0) (ofList (canon ss 0)) ::
          Val.int (S : ℤ) :: tl)
        (fun _ => Kcons * (4 * T)) :=
      step_consV (hCons main) (Val.int 0) (ofList (canon ss 0))
        (Val.int (S : ℤ) :: tl) (Kcons * (4 * T))
        (Nat.le_mul_of_pos_right Kcons (show 0 < 4 * T by omega))
    -- 7. push `nil` (the history of the accumulator is empty at time 0)
    have s7 : WordR main (pushP Val.nil)
        (fun vs => vs = Val.cons (Val.int 0) (ofList (canon ss 0)) ::
          Val.int (S : ℤ) :: tl)
        (fun _ out => out = Val.nil :: Val.cons (Val.int 0) (ofList (canon ss 0)) ::
          Val.int (S : ℤ) :: tl)
        (fun _ => Kpush * (4 * T)) :=
      wordR_lift (hPush main Val.nil) trivial (fun _ hq => hq) (by
        rw [vsz_nil_val]
        simpa using Nat.mul_le_mul_left Kpush (show (2 : ℕ) ≤ 4 * T by omega))
    -- 8. swap, so that `nil` sits under the entry
    have s8 : WordR main swapP
        (fun vs => vs = Val.nil :: Val.cons (Val.int 0) (ofList (canon ss 0)) ::
          Val.int (S : ℤ) :: tl)
        (fun _ out => out = Val.cons (Val.int 0) (ofList (canon ss 0)) :: Val.nil ::
          Val.int (S : ℤ) :: tl)
        (fun _ => Kswap * (24 * T)) :=
      step_swap (hSwap main) Val.nil (Val.cons (Val.int 0) (ofList (canon ss 0)))
        (Val.int (S : ℤ) :: tl) (Kswap * (24 * T))
        (by
          rw [vsz_nil_val, vsz_int0_cons]
          have h := hE_le
          have h1 := hT1
          exact Nat.mul_le_mul_left Kswap (by omega))
    -- 9. the accumulator `acc ss 0 = cons (prp 0 (canon ss 0)) nil`
    have s9 : WordR main consP
        (fun vs => vs = Val.cons (Val.int 0) (ofList (canon ss 0)) :: Val.nil ::
          Val.int (S : ℤ) :: tl)
        (fun _ out => out = Val.cons (Val.cons (Val.int 0) (ofList (canon ss 0))) Val.nil ::
          Val.int (S : ℤ) :: tl)
        (fun _ => Kcons * (4 * T)) :=
      step_consV (hCons main) (Val.cons (Val.int 0) (ofList (canon ss 0))) Val.nil
        (Val.int (S : ℤ) :: tl) (Kcons * (4 * T))
        (Nat.le_mul_of_pos_right Kcons (show 0 < 4 * T by omega))
    -- 10. move the accumulator below the saved `S`
    have s10 : WordR main swapP
        (fun vs => vs = Val.cons (Val.cons (Val.int 0) (ofList (canon ss 0))) Val.nil ::
          Val.int (S : ℤ) :: tl)
        (fun _ out => out = Val.int (S : ℤ) ::
          Val.cons (Val.cons (Val.int 0) (ofList (canon ss 0))) Val.nil :: tl)
        (fun _ => Kswap * (28 * T)) :=
      step_swap (hSwap main) (Val.cons (Val.cons (Val.int 0) (ofList (canon ss 0))) Val.nil)
        (Val.int (S : ℤ)) tl (Kswap * (28 * T))
        (by
          rw [vsz_acc_zero_eq, vsz_intNat]
          simp only [iszN]
          have h1 := hE_le
          have h2 := hW_le
          have h3 := hT1
          exact Nat.mul_le_mul_left Kswap (by omega))
    -- 11. push the `nil` that the driver list replicates
    have s11 : WordR main (pushP Val.nil)
        (fun vs => vs = Val.int (S : ℤ) ::
          Val.cons (Val.cons (Val.int 0) (ofList (canon ss 0))) Val.nil :: tl)
        (fun _ out => out = Val.nil :: Val.int (S : ℤ) ::
          Val.cons (Val.cons (Val.int 0) (ofList (canon ss 0))) Val.nil :: tl)
        (fun _ => Kpush * (4 * T)) :=
      wordR_lift (hPush main Val.nil) trivial (fun _ hq => hq) (by
        rw [vsz_nil_val]
        simpa using Nat.mul_le_mul_left Kpush (show (2 : ℕ) ≤ 4 * T by omega))
    -- 12. swap, so that `S` is on top and `nil` below it
    have s12 : WordR main swapP
        (fun vs => vs = Val.nil :: Val.int (S : ℤ) ::
          Val.cons (Val.cons (Val.int 0) (ofList (canon ss 0))) Val.nil :: tl)
        (fun _ out => out = Val.int (S : ℤ) :: Val.nil ::
          Val.cons (Val.cons (Val.int 0) (ofList (canon ss 0))) Val.nil :: tl)
        (fun _ => Kswap * (8 * T)) :=
      step_swap (hSwap main) Val.nil (Val.int (S : ℤ))
        (Val.cons (Val.cons (Val.int 0) (ofList (canon ss 0))) Val.nil :: tl)
        (Kswap * (8 * T))
        (by
          rw [vsz_nil_val, vsz_intNat]
          simp only [iszN]
          have h2 := hW_le
          have h3 := hT1
          exact Nat.mul_le_mul_left Kswap (by omega))
    -- 13. the driver list
    have s13 : WordR main repP
        (fun vs => vs = Val.int (S : ℤ) :: Val.nil ::
          Val.cons (Val.cons (Val.int 0) (ofList (canon ss 0))) Val.nil :: tl)
        (fun _ out => out = ofList (drv S) ::
          Val.cons (Val.cons (Val.int 0) (ofList (canon ss 0))) Val.nil :: tl)
        (fun _ => Krep * (8 * T)) :=
      step_replicate (hRep main) S Val.nil
        (Val.cons (Val.cons (Val.int 0) (ofList (canon ss 0))) Val.nil :: tl)
        (Krep * (8 * T))
        (by
          rw [vsz_nil_val, isz_natCast]
          simp only [iszN]
          have h1 := hS_le
          have h2 := hW_le
          exact Nat.mul_le_mul_left Krep (by omega))
    -- ## the chain
    have h12 := wordR_seqC hK s12 s13
    have h11 := wordR_seqC hK s11 h12
    have h10 := wordR_seqC hK s10 h11
    have h9 := wordR_seqC hK s9 h10
    have h8 := wordR_seqC hK s8 h9
    have h7 := wordR_seqC hK s7 h8
    have h6 := wordR_seqC hK s6 h7
    have h5 := wordR_seqC hK s5 h6
    have h4 := wordR_seqC hK s4 h5
    have h3 := wordR_seqC hK s3 h4
    have h2 := wordR_seqC hK s2 h3
    have h1 := wordR_seqC hK s1 h2
    -- ## the cost bound
    have htotal : Kdup * (4 * T) + (Kroll * (24 * T) + (Kswap * (4 * T) +
        (Ktab * T + (Kpush * (4 * T) + (Kcons * (4 * T) + (Kpush * (4 * T) +
        (Kswap * (24 * T) + (Kcons * (4 * T) + (Kswap * (28 * T) + (Kpush * (4 * T) +
        (Kswap * (8 * T) + Krep * (8 * T)))))))))))) =
        (Ktab + (4 * Kdup + (24 * Kroll +
          (64 * Kswap + (12 * Kpush + (8 * Kcons + 8 * Krep)))))) * T := by
      ring
    exact wordR_cost_le hK h1 (by
      rw [htotal]
      exact Nat.mul_le_mul_right T (by rw [hKdef]; omega))
  -- ## assembly
  have hfinal : WordR main prog (fun vs => ∃ tl, vs = Val.int (S : ℤ) :: intList ss :: tl)
      (fun vs out => ∃ tl, vs = Val.int (S : ℤ) :: intList ss :: tl ∧
        out = ofList (drv S) ::
          Val.cons (Val.cons (Val.int 0) (ofList (canon ss 0))) Val.nil :: tl)
      (fun _ => K * T) :=
    wordR_exists_tail (fun tl => Val.int (S : ℤ) :: intList ss :: tl)
      (fun tl => ofList (drv S) ::
        Val.cons (Val.cons (Val.int 0) (ofList (canon ss 0))) Val.nil :: tl) (K * T) hchain
  simpa only [hT, acc_zero_cons] using hfinal

/-- **The setup phase of the CRT label-and-sort word.** -/
theorem crtLabSetup (hK : HvdH.KernelLib) (hI : HvdH.IntLib) (hL : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (ss : List ℕ) (S : ℕ),
    (∀ s ∈ ss, 1 ≤ s) → S = ss.prod →
    HvdH.WordR main prog
      (fun vs => ∃ rest, vs = HvdH.Val.int (S : ℤ) :: HvdH.intList ss :: rest)
      (fun vs out => ∃ rest, vs = HvdH.Val.int (S : ℤ) :: HvdH.intList ss :: rest ∧
        out = HvdH.ofList (Work.MainP.drv S) :: Work.MainP.acc ss 0 :: rest)
      (fun _ => K * (HvdH.vsz (HvdH.intList ss) * (S.size + 1) + (ss.length + 1) * (S.size + 1) + S + 1)) := by
  -- the place-value table word `ofList (canon ss 0)` is `Work.MainP.crtLabTabW`
  obtain ⟨tabP, Ktab, hTab⟩ := crtLabTabW hK hI
  exact crtLabSetup_word hK hI hL tabP Ktab hTab

end Work.MainP
