import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.pbDefs
import Submission.Work.Resample.auLoopDefs
import Submission.Work.Resample.auRoundAux

/-!
# `Work.Resample.auRoundRec`

One round of the streaming-window loop of the resampling word (`Work.Resample.auSetup`): stack `1`
holds the round's record `cons (auSeqFlg g) (cons (int g) (ofList WTS))` (the slide `g` re-encoded so
that a raw glyph test sees it), stack `2` holds the head `e` of the element run, and the window
`ofList W` sits on top of stack `0`.  The word slides the window
(`out = ofList (((W.drop g) ++ [e]).take L)`), pushes the chunk `cons (ofList WTS) (ofList W)` on
stack `3` and keeps or consumes `e` according to `g`.

The proof composes the library words of `KernelLib`/`LayoutLib` with the helper words
`auRoundPop`/`auRoundPush` (moving a value between stack `0` and a non-zero stack) and the
`WordM`-level `ifNil` `auRoundIfNil`; the cost of every step is estimated separately against the
single constant `K` of the statement, which is why one round is linear in
`(L + 1) * (B + 1) + 1`.

Everything is carried out in the `auSeqFlg` vocabulary of `auLoopDefs`.  The private development
below (the `WordM` composition combinators `seqD`/`seqGen`/`wordRdet`, the `auSeqFlg` flag facts and
the proof of the round word itself) is the `auSeqFlg`-spelled rendering of the development recorded
in `Submission/Work/Resample/auRoundWord.lean` (whose flag is the value-level `auFlg` of
`auRoundFlg`).  It is reproduced here rather than obtained by importing that module, because
`auRoundFlg`'s `auFlg` collides with the *unrelated* guard flag `auFlg` of
`Submission/Work/Resample/auKit.lean`: any module that has `auKit` in its import closure -- for
instance `auRecsFWord`, which describes the records of the weight table -- fails to build as soon as
it imports `auRoundWord`.  This file imports only `pbDefs`, `auLoopDefs` and `auRoundAux`, so
`Submission.Work.Resample.auRoundRec` is importable next to `auKit`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.Resample

open HvdH

/-- A state description: the value stack and the value lists on stacks `1,2,3`. -/
private def PreD (V A1 A2 A3 : List Val) : List Val → (Stk → List Val) → Prop :=
  fun vs a => vs = V ∧ a 1 = A1 ∧ a 2 = A2 ∧ a 3 = A3

/-- The postcondition on `(out, b)` for a step described by `(V, A1, A2, A3)` (no dependence on
`vs`). -/
private def PostA (V A1 A2 A3 : List Val) : (Stk → List Val) → List Val → (Stk → List Val) → Prop :=
  fun a out b => out = V ∧ b 1 = A1 ∧ b 2 = A2 ∧ b 3 = A3 ∧ auRoundFr a b

/-- `PostA` in the `WordM` postcondition position. -/
private def PostD (V A1 A2 A3 : List Val) : List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop :=
  fun _ a out b => PostA V A1 A2 A3 a out b

/-- Transferring a `PostA` from one ambient description to another along the frame. -/
private theorem PostA_frame {V A1 A2 A3 : List Val} {a a' : Stk → List Val} {out b : _}
    (hfr : auRoundFr a a') (h : PostA V A1 A2 A3 a' out b) : PostA V A1 A2 A3 a out b := by
  obtain ⟨h1, h2, h3, h4, hfr2⟩ := h
  exact ⟨h1, h2, h3, h4, fun k hk0 hk1 hk2 hk3 => by
    rw [hfr2 k hk0 hk1 hk2 hk3, hfr k hk0 hk1 hk2 hk3]⟩

/-- Composition of two `WordM` steps with determined intermediate descriptions. -/
private theorem seqD {main p q : Cmd} {V1 A1 B1 C1 V2 A2 B2 C2 V3 A3 B3 C3 : List Val}
    {c1 c2 : ℕ}
    (h1 : WordM main p (PreD V1 A1 B1 C1) (PostD V2 A2 B2 C2) (fun _ _ => c1))
    (h2 : WordM main q (PreD V2 A2 B2 C2) (PostD V3 A3 B3 C3) (fun _ _ => c2)) :
    WordM main (.seq p q) (PreD V1 A1 B1 C1) (PostD V3 A3 B3 C3) (fun _ _ => c1 + c2) := by
  refine WordM.conseq (WordM.seq (B := fun _ _ => c2) h1 h2 ?_ ?_) ?_ ?_ ?_
  · intro vs a mid a' h
    obtain ⟨hm, ha1, ha2, ha3, -⟩ := h
    exact ⟨hm, ha1, ha2, ha3⟩
  · intro vs a mid a' _
    exact le_rfl
  · intro vs a hpre; exact hpre
  · rintro vs a out b _ ⟨mid, a', h1p, h2p⟩
    obtain ⟨hm, hb1, hb2, hb3, hfr1⟩ := h1p
    obtain ⟨hm', hb1', hb2', hb3', hfr2⟩ := h2p
    exact ⟨hm', hb1', hb2', hb3', fun k hk0 hk1 hk2 hk3 => by
      rw [hfr2 k hk0 hk1 hk2 hk3, hfr1 k hk0 hk1 hk2 hk3]⟩
  · intro vs a _
    exact le_rfl

/-- Composition of a described step with a step whose postcondition is an arbitrary predicate,
transferring the ambient description along the frame. -/
private theorem seqGen {main p q : Cmd} {V1 A1 B1 C1 V2 A2 B2 C2 : List Val}
    {Post2 : List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop} {c1 c2 : ℕ}
    (h1 : WordM main p (PreD V1 A1 B1 C1) (PostD V2 A2 B2 C2) (fun _ _ => c1))
    (h2 : WordM main q (PreD V2 A2 B2 C2) Post2 (fun _ _ => c2))
    (htr : ∀ (vs : List Val) (a : Stk → List Val) (mid : List Val) (a' : Stk → List Val)
      (out : List Val) (b : Stk → List Val),
      PostD V2 A2 B2 C2 vs a mid a' → Post2 mid a' out b → Post2 vs a out b) :
    WordM main (.seq p q) (PreD V1 A1 B1 C1) Post2 (fun _ _ => c1 + c2) := by
  refine WordM.conseq (WordM.seq (B := fun _ _ => c2) h1 h2 ?_ ?_) ?_ ?_ ?_
  · intro vs a mid a' h
    obtain ⟨hm, ha1, ha2, ha3, -⟩ := h
    exact ⟨hm, ha1, ha2, ha3⟩
  · intro vs a mid a' _; exact le_rfl
  · intro vs a hpre; exact hpre
  · rintro vs a out b _ ⟨mid, a', h1p, h2p⟩
    exact htr vs a mid a' out b h1p h2p
  · intro vs a _; exact le_rfl

/-- A `WordR` word used as a step with prescribed descriptions (it leaves the descriptions of
stacks `1,2,3` untouched). -/
private theorem wordRdet {main p : Cmd} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {C : List Val → ℕ} (h : WordR main p P Q C) {V A1 A2 A3 : List Val} {vs' : List Val} {c : ℕ}
    (h1 : ∀ vs a, PreD V A1 A2 A3 vs a → P vs)
    (h2 : ∀ vs a out, PreD V A1 A2 A3 vs a → Q vs out → out = vs')
    (h3 : ∀ vs a, PreD V A1 A2 A3 vs a → C vs ≤ c) :
    WordM main p (PreD V A1 A2 A3) (PostD vs' A1 A2 A3) (fun _ _ => c) := by
  refine WordM.conseq (WordM.ofWordR h) h1 ?_ h3
  intro vs a out b hpre hpost
  obtain ⟨hQ, hb⟩ := hpost
  have ha1 : a 1 = A1 := hpre.2.1
  have ha2 : a 2 = A2 := hpre.2.2.1
  have ha3 : a 3 = A3 := hpre.2.2.2
  refine ⟨h2 vs a out hpre hQ, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (fun f : Stk → List Val => f 1) hb).trans ha1
  · exact (congrArg (fun f : Stk → List Val => f 2) hb).trans ha2
  · exact (congrArg (fun f : Stk → List Val => f 3) hb).trans ha3
  · intro k _ _ _ _
    exact congrArg (fun f : Stk → List Val => f k) hb

/-- Cost bound: `K * c ≤ SC` when `K ≤ KS` and `c ≤ 1000 N`. -/
private theorem cost_mul {KS N SC K c : ℕ} (hSC : SC = 1000 * KS * N) (hK : K ≤ KS)
    (hc : c ≤ 1000 * N) : K * c ≤ SC := by
  rw [hSC]
  calc K * c ≤ KS * c := Nat.mul_le_mul_right c hK
    _ ≤ KS * (1000 * N) := Nat.mul_le_mul_left KS hc
    _ = 1000 * KS * N := by ring

/-- Cost bound: `K ≤ SC` when `K ≤ KS`. -/
private theorem cost_const {KS N SC K : ℕ} (hSC : SC = 1000 * KS * N) (hN : 1 ≤ N)
    (hK : K ≤ KS) : K ≤ SC := by
  rw [hSC]
  calc K ≤ KS := hK
    _ ≤ KS * (1000 * N) := Nat.le_mul_of_pos_right KS (by omega)
    _ = 1000 * KS * N := by ring

/-- Cost bound: `K * c1 * c2 ≤ SC` when `K ≤ KS`, `c1 ≤ 3` and `c2 ≤ 40 N`. -/
private theorem cost_prod {KS N SC K c1 c2 : ℕ} (hSC : SC = 1000 * KS * N) (hK : K ≤ KS)
    (h1 : c1 ≤ 3) (h2 : c2 ≤ 40 * N) : K * c1 * c2 ≤ SC := by
  rw [hSC]
  have hm : c1 * c2 ≤ 120 * N := by
    have h := Nat.mul_le_mul h1 h2
    omega
  calc K * c1 * c2 = K * (c1 * c2) := by ring
    _ ≤ KS * (120 * N) := Nat.mul_le_mul hK hm
    _ ≤ KS * (1000 * N) := Nat.mul_le_mul_left KS (by omega)
    _ = 1000 * KS * N := by ring

end Work.Resample

namespace Work.Resample

open HvdH

/-! ## The flag value

The record consumed by a round is flagged by `auSeqFlg g` (`nil` for `g = 0`, `cons nil nil` for
`g = 1`), so that a raw glyph test (`peek`/`ite`) can decide which branch to take.  These are the
facts about that flag used below (the `auSeqFlg`-spelled counterparts of the facts proved for `auFlg`
in `Submission/Work/Resample/auRoundFlg.lean`).
-/

/-- The glyph-level flag of a slide `g` is `nil` exactly for `g = 0`. -/
theorem auRound_auSeqFlg_eq_nil_iff (g : ℕ) : auSeqFlg g = .nil ↔ g = 0 := by
  by_cases h : g = 0
  · simp [auSeqFlg, h]
  · simp [auSeqFlg, h]

/-- For `g ≠ 0` the flag `auSeqFlg g` is a `cons`. -/
theorem auRound_auSeqFlg_ne_nil (g : ℕ) (h : g ≠ 0) : auSeqFlg g = .cons .nil .nil := by
  simp [auSeqFlg, h]

/-- The flag `auSeqFlg g` is a `cons` exactly for `g ≠ 0`. -/
theorem auRound_auSeqFlg_ne_nil_iff (g : ℕ) : auSeqFlg g ≠ .nil ↔ g ≠ 0 := by
  rw [ne_eq, auRound_auSeqFlg_eq_nil_iff]

/-- The flag has constant size `≤ 3` (this is what keeps the cost of the branch constant). -/
theorem auRound_vsz_auSeqFlg_le (g : ℕ) : vsz (auSeqFlg g) ≤ 3 := by
  by_cases h : g = 0
  · simp [auSeqFlg, h, vsz, Val.enc]
  · simp [auSeqFlg, h, vsz, Val.enc]


/-- One round of the streaming-window loop (`auRoundWord`): consume the record
`cons (auSeqFlg g) (cons (int g) (ofList WTS))` on top of stack `1`, slide the window `ofList W` on
stack `0` by `g` using the element `e` on top of stack `2` (`e` is consumed iff `g = 1`), and push
the chunk `cons (ofList WTS) (ofList W)` onto stack `3`.  Route: `auRoundPop 1` the record onto
stack `0`, `unconsV`, then `auRoundIfNil` on the flag value (`nil` for `g = 0`, `cons nil nil` for
`g = 1`); the `g = 1` branch uses `KernelLib.pick`/`swap`/`consV` to keep a copy of `W` for the
chunk and `LayoutLib.drop`/`append`/`take` for the slide, then `auRoundPush 3` the chunk.
`auSeqFlg g` is definitionally `auFlg g` (`Submission/Work/Resample/auRoundFlg.lean`), and a nearly
complete proof of this statement (with `auFlg`, same helpers) is in
`Submission/Work/Resample/auRoundWord.lean`, which however does not build.  Sizes:
`vsz (ofList W) ≤ 3 * ((L+1)*(B+1)+1)` and likewise for `WTS` (induction on the list), which is
what makes the stated cost shape work; note `e` is only used when `g = 1`, and for `g = 0`
`(W.drop 0 ++ [e]).take L = W` because `W.length = L`. -/
theorem auRoundRec (hk : HvdH.KernelLib) (hl : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (L g B : ℕ)
      (W WTS P RT ET CT : List HvdH.Val) (e : HvdH.Val),
      g ≤ 1 → W.length = L → WTS.length = L →
      (∀ v ∈ W, HvdH.vsz v ≤ B) → (∀ v ∈ WTS, HvdH.vsz v ≤ B) → HvdH.vsz e ≤ B →
      Work.Resample.WordM main prog
        (fun vs a => vs = HvdH.ofList W :: P ∧
          a 1 = HvdH.Val.cons (Work.Resample.auSeqFlg g)
            (HvdH.Val.cons (.int (g : ℤ)) (HvdH.ofList WTS)) :: RT ∧
          a 2 = e :: ET ∧ a 3 = CT)
        (fun vs a out b => out = HvdH.ofList (((W.drop g) ++ [e]).take L) :: P ∧
          b 1 = RT ∧ b 2 = (if g = 1 then ET else e :: ET) ∧
          b 3 = HvdH.Val.cons (HvdH.ofList WTS) (HvdH.ofList W) :: CT ∧
          (∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → b k = a k))
        (fun _ _ => K * ((L + 1) * (B + 1) + 1)) := by
  obtain ⟨uP, Ku, hu⟩ := hk.unconsV
  obtain ⟨dP, Kd, hd⟩ := hk.drop
  obtain ⟨pP, Kp, hp⟩ := hk.pick
  obtain ⟨rP, Kr, hr⟩ := hk.roll
  obtain ⟨cP, Kc, hc⟩ := hk.consV
  obtain ⟨pvP, Kpv, hpv⟩ := hk.pushVal
  obtain ⟨aP, Ka, ha⟩ := hl.append
  obtain ⟨popP, Kpop, hpop⟩ := auRoundPop 1 (by decide)
  obtain ⟨push3P, Kpush3, hpush3⟩ := auRoundPush 3 (by decide)
  obtain ⟨pop2P, Kpop2, hpop2⟩ := auRoundPop 2 (by decide)
  obtain ⟨ifP, Kif, hif⟩ := auRoundIfNil
  obtain ⟨KS, hKS⟩ :
      ∃ KS : ℕ, KS = Ku + Kd + Kp + Kr + Kc + Kpv + Ka + Kpop + Kpush3 + Kpop2 + Kif + 1 :=
    ⟨_, rfl⟩
  obtain ⟨KK, hKK⟩ : ∃ KK : ℕ, KK = 100000 * KS := ⟨_, rfl⟩
  let inNil : Cmd := Cmd.seq pop2P (Cmd.seq dP (pvP .nil))
  let inCons : Cmd :=
    Cmd.seq uP (Cmd.seq dP (Cmd.seq (pvP .nil) (Cmd.seq pop2P (Cmd.seq cP (Cmd.seq (rP 1) aP)))))
  let bCons : Cmd := Cmd.seq dP (ifP inNil inCons)
  let roundProg : Cmd :=
    Cmd.seq popP (Cmd.seq uP (Cmd.seq (rP 1) (Cmd.seq uP (Cmd.seq dP (Cmd.seq (rP 2)
      (Cmd.seq (rP 1) (Cmd.seq (pP 1) (Cmd.seq (rP 1) (Cmd.seq cP (Cmd.seq push3P
        (Cmd.seq (rP 1) (ifP Cmd.skip bCons))))))))))))
  refine ⟨roundProg, KK, ?_⟩
  intro main L g B W WTS P RT ET CT e hg1 hWlen hWTSlen hWB hWTSB heB
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = (L + 1) * (B + 1) + 1 := ⟨_, rfl⟩
  rw [← hN]
  set W0 : Val := ofList W with hW0
  set T0 : Val := ofList WTS with hT0
  set E : Val := e with hEdef
  set FLG : Val := auSeqFlg g with hFLG
  set TAIL : Val := .cons (.int (g : ℤ)) T0 with hTAIL
  set REC : Val := .cons FLG TAIL with hREC
  set CH : Val := .cons T0 W0 with hCH
  obtain ⟨SC, hSC⟩ : ∃ SC : ℕ, SC = 1000 * KS * N := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by rw [hN]; omega
  have hKS1 : 1 ≤ KS := by rw [hKS]; omega
  have bKu : Ku ≤ KS := by rw [hKS]; omega
  have bKd : Kd ≤ KS := by rw [hKS]; omega
  have bKp : Kp ≤ KS := by rw [hKS]; omega
  have bKr : Kr ≤ KS := by rw [hKS]; omega
  have bKc : Kc ≤ KS := by rw [hKS]; omega
  have bKpv : Kpv ≤ KS := by rw [hKS]; omega
  have bKa : Ka ≤ KS := by rw [hKS]; omega
  have bKpop : Kpop ≤ KS := by rw [hKS]; omega
  have bKpush3 : Kpush3 ≤ KS := by rw [hKS]; omega
  have bKpop2 : Kpop2 ≤ KS := by rw [hKS]; omega
  have bKif : Kif ≤ KS := by rw [hKS]; omega
  have hB1 : 1 ≤ B := le_trans (Work.ConvR.vsz_one_le E) heB
  have hBN : B ≤ N := by
    rw [hN]
    have h : B + 1 ≤ (L + 1) * (B + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have szW0 : vsz W0 ≤ 3 * N := by
    rw [hW0, hN, ← hWlen]
    exact auRound_vsz_ofList_le W B hWB
  have szT0 : vsz T0 ≤ 3 * N := by
    rw [hT0, hN, ← hWTSlen]
    exact auRound_vsz_ofList_le WTS B hWTSB
  have szE : vsz E ≤ N := by rw [hEdef]; exact le_trans heB hBN
  have szFLG : vsz FLG ≤ 3 := by rw [hFLG]; exact auRound_vsz_auSeqFlg_le g
  have szGV : vsz (.int (g : ℤ)) ≤ 3 := by
    rw [Work.ConvR.vsz_int]; exact auRound_isz_le_three g hg1
  have szTAIL : vsz TAIL ≤ 3 * N + 4 := by
    rw [hTAIL, auRound_vsz_cons]
    nlinarith [szGV, szT0, hN1]
  have szREC : vsz REC ≤ 3 * N + 8 := by
    rw [hREC, auRound_vsz_cons]
    nlinarith [szFLG, szTAIL]
  have szCH : vsz CH ≤ 6 * N + 1 := by
    rw [hCH, auRound_vsz_cons]
    nlinarith [szT0, szW0]
  have szWdrop : vsz (ofList (W.drop 1)) ≤ 3 * N := by
    have hlen : (W.drop 1).length ≤ L := by rw [List.length_drop, hWlen]; omega
    have hmem : ∀ v ∈ W.drop 1, vsz v ≤ B := fun v hv => hWB v ((List.drop_sublist 1 W).mem hv)
    have h := auRound_vsz_ofList_le (W.drop 1) B hmem
    rw [hN]
    nlinarith [h, hlen, Nat.zero_le B]
  have szHead : vsz (W.headD .nil) ≤ B := by
    cases W with
    | nil => simpa [auRound_vsz_nil] using hB1
    | cons v vs => exact hWB v (by simp)
  -- ============ step 1: pop the record from stack 1 onto stack 0 ============
  have hS1 : WordM main popP (PreD (W0 :: P) (REC :: RT) (E :: ET) CT)
      (PostD (REC :: W0 :: P) RT (E :: ET) CT) (fun _ _ => SC) := by
    refine WordM.conseq (hpop main REC RT (W0 :: P)) ?_ ?_ ?_
    · rintro vs a ⟨h1, h2, -, -⟩; exact ⟨h1, h2⟩
    · rintro vs a out b ⟨hvs, ha1, ha2, ha3⟩ ⟨hout, hb1, hfr⟩
      exact ⟨by rw [hout, hvs] <;> rfl, hb1,
        by rw [hfr 2 (by decide) (by decide), ha2] <;> rfl,
        by rw [hfr 3 (by decide) (by decide), ha3] <;> rfl,
        fun k hk0 hk1 hk2 hk3 => hfr k hk0 hk1⟩
    · rintro vs a ⟨-, -, -, -⟩
      have hrec : vsz REC + 1 ≤ 1000 * N := by omega
      exact cost_mul hSC bKpop hrec
  -- ============ step 2: split the record ============
  have hS2 : WordM main uP (PreD (REC :: W0 :: P) RT (E :: ET) CT)
      (PostD (FLG :: TAIL :: W0 :: P) RT (E :: ET) CT) (fun _ _ => SC) := by
    refine wordRdet (hu main) ?_ ?_ ?_
    · rintro vs a ⟨hvs, -, -, -⟩
      exact ⟨FLG, TAIL, W0 :: P, by rw [hvs, hREC] <;> rfl⟩
    · rintro vs a out ⟨hvs, -, -, -⟩ ⟨a', b', rest, heq, hout⟩
      have h : Val.cons a' b' :: rest = Val.cons FLG TAIL :: (W0 :: P) := by
        simpa only [hvs, hREC] using heq.symm
      have htail : rest = W0 :: P := by
        simpa only [List.tail_cons] using congrArg List.tail h
      have h1 : Val.cons a' b' = Val.cons FLG TAIL := by
        simpa only [List.headD_cons] using congrArg (fun l => l.headD .nil) h
      cases h1
      rw [hout, htail] <;> rfl
    · rintro vs a ⟨-, -, -, -⟩
      exact cost_const hSC hN1 bKu
  -- ============ step 3: roll 1 ============
  have hS3 : WordM main (rP 1) (PreD (FLG :: TAIL :: W0 :: P) RT (E :: ET) CT)
      (PostD (TAIL :: FLG :: W0 :: P) RT (E :: ET) CT) (fun _ _ => SC) := by
    refine wordRdet (hr main 1) ?_ ?_ ?_
    · rintro vs a ⟨hvs, -, -, -⟩; rw [hvs]; simp
    · rintro vs a out ⟨hvs, -, -, -⟩ hQ
      rw [hQ, hvs] <;> rfl
    · rintro vs a ⟨hvs, -, -, -⟩
      rw [hvs]
      show Kr * 2 * ((vsz FLG + vsz TAIL) + 1) ≤ SC
      have hs : (vsz FLG + vsz TAIL) + 1 ≤ 40 * N := by omega
      exact cost_prod hSC bKr (by omega) hs
  -- ============ step 4: split the tail of the record ============
  have hS4 : WordM main uP (PreD (TAIL :: FLG :: W0 :: P) RT (E :: ET) CT)
      (PostD (.int (g : ℤ) :: T0 :: FLG :: W0 :: P) RT (E :: ET) CT) (fun _ _ => SC) := by
    refine wordRdet (hu main) ?_ ?_ ?_
    · rintro vs a ⟨hvs, -, -, -⟩
      exact ⟨.int (g : ℤ), T0, FLG :: W0 :: P, by rw [hvs, hTAIL] <;> rfl⟩
    · rintro vs a out ⟨hvs, -, -, -⟩ ⟨a', b', rest, heq, hout⟩
      have h : Val.cons a' b' :: rest = Val.cons (.int (g : ℤ)) T0 :: (FLG :: W0 :: P) := by
        simpa only [hvs, hTAIL] using heq.symm
      have htail : rest = FLG :: W0 :: P := by
        simpa only [List.tail_cons] using congrArg List.tail h
      have h1 : Val.cons a' b' = Val.cons (.int (g : ℤ)) T0 := by
        simpa only [List.headD_cons] using congrArg (fun l => l.headD .nil) h
      cases h1
      rw [hout, htail] <;> rfl
    · rintro vs a ⟨-, -, -, -⟩
      exact cost_const hSC hN1 bKu
  -- ============ step 5: drop the slide ============
  have hS5 : WordM main dP (PreD (.int (g : ℤ) :: T0 :: FLG :: W0 :: P) RT (E :: ET) CT)
      (PostD (T0 :: FLG :: W0 :: P) RT (E :: ET) CT) (fun _ _ => SC) := by
    refine wordRdet (hd main) ?_ ?_ ?_
    · rintro vs a ⟨hvs, -, -, -⟩; rw [hvs]; simp
    · rintro vs a out ⟨hvs, -, -, -⟩ ⟨v', rest, heq, hout⟩
      have h : v' :: rest = Val.int (g : ℤ) :: T0 :: FLG :: W0 :: P := by
        simpa only [hvs] using heq.symm
      have htail : rest = T0 :: FLG :: W0 :: P := by
        simpa only [List.tail_cons] using congrArg List.tail h
      rw [hout, htail] <;> rfl
    · rintro vs a ⟨hvs, -, -, -⟩
      rw [hvs]
      show Kd * (vsz (.int (g : ℤ)) + 1) ≤ SC
      exact cost_mul hSC bKd (by omega)
  -- ============ step 6: roll 2 ============
  have hS6 : WordM main (rP 2) (PreD (T0 :: FLG :: W0 :: P) RT (E :: ET) CT)
      (PostD (W0 :: T0 :: FLG :: P) RT (E :: ET) CT) (fun _ _ => SC) := by
    refine wordRdet (hr main 2) ?_ ?_ ?_
    · rintro vs a ⟨hvs, -, -, -⟩; rw [hvs]; simp
    · rintro vs a out ⟨hvs, -, -, -⟩ hQ
      rw [hQ, hvs] <;> rfl
    · rintro vs a ⟨hvs, -, -, -⟩
      rw [hvs]
      show Kr * 3 * ((vsz T0 + (vsz FLG + vsz W0)) + 1) ≤ SC
      have hs : (vsz T0 + (vsz FLG + vsz W0)) + 1 ≤ 40 * N := by omega
      exact cost_prod hSC bKr (by omega) hs
  -- ============ step 7: roll 1 ============
  have hS7 : WordM main (rP 1) (PreD (W0 :: T0 :: FLG :: P) RT (E :: ET) CT)
      (PostD (T0 :: W0 :: FLG :: P) RT (E :: ET) CT) (fun _ _ => SC) := by
    refine wordRdet (hr main 1) ?_ ?_ ?_
    · rintro vs a ⟨hvs, -, -, -⟩; rw [hvs]; simp
    · rintro vs a out ⟨hvs, -, -, -⟩ hQ
      rw [hQ, hvs] <;> rfl
    · rintro vs a ⟨hvs, -, -, -⟩
      rw [hvs]
      show Kr * 2 * ((vsz W0 + vsz T0) + 1) ≤ SC
      have hs : (vsz W0 + vsz T0) + 1 ≤ 40 * N := by omega
      exact cost_prod hSC bKr (by omega) hs
  -- ============ step 8: pick 1 ============
  have hS8 : WordM main (pP 1) (PreD (T0 :: W0 :: FLG :: P) RT (E :: ET) CT)
      (PostD (W0 :: T0 :: W0 :: FLG :: P) RT (E :: ET) CT) (fun _ _ => SC) := by
    refine wordRdet (hp main 1) ?_ ?_ ?_
    · rintro vs a ⟨hvs, -, -, -⟩; rw [hvs]; simp
    · rintro vs a out ⟨hvs, -, -, -⟩ hQ
      rw [hQ, hvs] <;> rfl
    · rintro vs a ⟨hvs, -, -, -⟩
      rw [hvs]
      show Kp * 2 * ((vsz T0 + vsz W0) + 1) ≤ SC
      have hs : (vsz T0 + vsz W0) + 1 ≤ 40 * N := by omega
      exact cost_prod hSC bKp (by omega) hs
  -- ============ step 9: roll 1 ============
  have hS9 : WordM main (rP 1) (PreD (W0 :: T0 :: W0 :: FLG :: P) RT (E :: ET) CT)
      (PostD (T0 :: W0 :: W0 :: FLG :: P) RT (E :: ET) CT) (fun _ _ => SC) := by
    refine wordRdet (hr main 1) ?_ ?_ ?_
    · rintro vs a ⟨hvs, -, -, -⟩; rw [hvs]; simp
    · rintro vs a out ⟨hvs, -, -, -⟩ hQ
      rw [hQ, hvs] <;> rfl
    · rintro vs a ⟨hvs, -, -, -⟩
      rw [hvs]
      show Kr * 2 * ((vsz W0 + vsz T0) + 1) ≤ SC
      have hs : (vsz W0 + vsz T0) + 1 ≤ 40 * N := by omega
      exact cost_prod hSC bKr (by omega) hs
  -- ============ step 10: build the chunk ============
  have hS10 : WordM main cP (PreD (T0 :: W0 :: W0 :: FLG :: P) RT (E :: ET) CT)
      (PostD (CH :: W0 :: FLG :: P) RT (E :: ET) CT) (fun _ _ => SC) := by
    refine wordRdet (hc main) ?_ ?_ ?_
    · rintro vs a ⟨hvs, -, -, -⟩; rw [hvs]; simp
    · rintro vs a out ⟨hvs, -, -, -⟩ ⟨a', b', rest, heq, hout⟩
      have h : T0 :: W0 :: W0 :: FLG :: P = a' :: b' :: rest := by
        simpa only [hvs] using heq
      have h1 : T0 = a' := by
        simpa only [List.headD_cons] using congrArg (fun l => l.headD .nil) h
      have htail : W0 :: W0 :: FLG :: P = b' :: rest := by
        simpa only [List.tail_cons] using congrArg List.tail h
      have h2 : W0 = b' := by
        simpa only [List.headD_cons] using congrArg (fun l => l.headD .nil) htail
      have h3 : W0 :: FLG :: P = rest := by
        simpa only [List.tail_cons] using congrArg List.tail htail
      rw [hout, ← h1, ← h2, ← h3, hCH] <;> rfl
    · rintro vs a ⟨-, -, -, -⟩
      exact cost_const hSC hN1 bKc
  -- ============ step 11: push the chunk on stack 3 ============
  have hS11 : WordM main push3P (PreD (CH :: W0 :: FLG :: P) RT (E :: ET) CT)
      (PostD (W0 :: FLG :: P) RT (E :: ET) (CH :: CT)) (fun _ _ => SC) := by
    refine WordM.conseq (hpush3 main CH (W0 :: FLG :: P) CT) ?_ ?_ ?_
    · rintro vs a ⟨h1, h2, h3, h4⟩; exact ⟨h1, h4⟩
    · rintro vs a out b ⟨hvs, ha1, ha2, ha3⟩ ⟨hout, hb3, hfr⟩
      exact ⟨by rw [hout] <;> rfl, by rw [hfr 1 (by decide) (by decide), ha1] <;> rfl,
        by rw [hfr 2 (by decide) (by decide), ha2] <;> rfl, hb3,
        fun k hk0 hk1 hk2 hk3 => hfr k hk0 hk3⟩
    · rintro vs a ⟨-, -, -, -⟩
      have hsz : vsz CH + 1 ≤ 1000 * N := by omega
      exact cost_mul hSC bKpush3 hsz
  -- ============ step 12: roll 1 ============
  have hS12 : WordM main (rP 1) (PreD (W0 :: FLG :: P) RT (E :: ET) (CH :: CT))
      (PostD (FLG :: W0 :: P) RT (E :: ET) (CH :: CT)) (fun _ _ => SC) := by
    refine wordRdet (hr main 1) ?_ ?_ ?_
    · rintro vs a ⟨hvs, -, -, -⟩; rw [hvs]; simp
    · rintro vs a out ⟨hvs, -, -, -⟩ hQ
      rw [hQ, hvs] <;> rfl
    · rintro vs a ⟨hvs, -, -, -⟩
      rw [hvs]
      show Kr * 2 * ((vsz W0 + vsz FLG) + 1) ≤ SC
      have hs : (vsz W0 + vsz FLG) + 1 ≤ 40 * N := by omega
      exact cost_prod hSC bKr (by omega) hs
  -- ============ the branch bodies ============
  have hInNil : WordM main inNil
      (fun vs a => vs = P ∧ (a 1 = RT ∧ a 2 = E :: ET ∧ a 3 = CH :: CT))
      (PostD (.nil :: P) RT ET (CH :: CT)) (fun _ _ => 4 * SC) := by
    have hA : WordM main pop2P (PreD P RT (E :: ET) (CH :: CT))
        (PostD (E :: P) RT ET (CH :: CT)) (fun _ _ => SC) := by
      refine WordM.conseq (hpop2 main E ET P) ?_ ?_ ?_
      · rintro vs a ⟨h1, -, h3, -⟩; exact ⟨h1, h3⟩
      · rintro vs a out b ⟨hvs, ha1, ha2, ha3⟩ ⟨hout, hb2, hfr⟩
        exact ⟨by rw [hout, hvs] <;> rfl, by rw [hfr 1 (by decide) (by decide), ha1] <;> rfl, hb2,
          by rw [hfr 3 (by decide) (by decide), ha3] <;> rfl,
          fun k hk0 hk1 hk2 hk3 => hfr k hk0 hk2⟩
      · rintro vs a ⟨-, -, -, -⟩
        have hsz : vsz E + 1 ≤ 1000 * N := by omega
        exact cost_mul hSC bKpop2 hsz
    have hB : WordM main dP (PreD (E :: P) RT ET (CH :: CT))
        (PostD P RT ET (CH :: CT)) (fun _ _ => SC) := by
      refine wordRdet (hd main) ?_ ?_ ?_
      · rintro vs a ⟨hvs, -, -, -⟩; rw [hvs]; simp
      · rintro vs a out ⟨hvs, -, -, -⟩ ⟨v', rest, heq, hout⟩
        have h : v' :: rest = E :: (P : List Val) := by
          simpa only [hvs] using heq.symm
        have htail : rest = P := by
          simpa only [List.tail_cons] using congrArg List.tail h
        rw [hout, htail] <;> rfl
      · rintro vs a ⟨hvs, -, -, -⟩
        rw [hvs]
        show Kd * (vsz E + 1) ≤ SC
        exact cost_mul hSC bKd (by omega)
    have hC : WordM main (pvP .nil) (PreD P RT ET (CH :: CT))
        (PostD (.nil :: P) RT ET (CH :: CT)) (fun _ _ => SC) := by
      refine wordRdet (hpv main .nil) ?_ ?_ ?_
      · rintro vs a ⟨hvs, -, -, -⟩; exact trivial
      · rintro vs a out ⟨hvs, -, -, -⟩ hout
        rw [hout, hvs] <;> rfl
      · rintro vs a ⟨-, -, -, -⟩
        have hsz : vsz (.nil : Val) + 1 ≤ 1000 * N := by rw [auRound_vsz_nil]; omega
        exact cost_mul hSC bKpv hsz
    have hAll : WordM main (Cmd.seq pop2P (Cmd.seq dP (pvP .nil))) (PreD P RT (E :: ET) (CH :: CT))
        (PostD (.nil :: P) RT ET (CH :: CT)) (fun _ _ => SC + (SC + SC)) :=
      seqD hA (seqD hB hC)
    exact WordM.mono hAll (fun _ _ => by omega)
  have hInCons : W0 ≠ .nil →
      WordM main inCons (fun vs a => vs = W0 :: P ∧ (a 1 = RT ∧ a 2 = E :: ET ∧ a 3 = CH :: CT))
        (PostD (ofList (W.drop 1 ++ [E]) :: P) RT ET (CH :: CT)) (fun _ _ => 9 * SC) := by
    intro hvne
    have hWne : W ≠ [] := fun hw => hvne (by rw [hW0, hw]; rfl)
    have hWsplit : W0 = .cons (W.headD .nil) (ofList (W.drop 1)) := by
      rw [hW0]; exact auRound_ofList_drop_one W hWne
    have hA : WordM main uP (PreD (W0 :: P) RT (E :: ET) (CH :: CT))
        (PostD (W.headD .nil :: ofList (W.drop 1) :: P) RT (E :: ET) (CH :: CT))
        (fun _ _ => SC) := by
      refine wordRdet (hu main) ?_ ?_ ?_
      · rintro vs a ⟨hvs, -, -, -⟩
        exact ⟨W.headD .nil, ofList (W.drop 1), P, by rw [hvs, hWsplit] <;> rfl⟩
      · rintro vs a out ⟨hvs, -, -, -⟩ ⟨a', b', rest, heq, hout⟩
        have h : Val.cons a' b' :: rest = Val.cons (W.headD .nil) (ofList (W.drop 1)) :: (P : List Val) := by
          simpa only [hvs, hWsplit] using heq.symm
        have htail : rest = P := by
          simpa only [List.tail_cons] using congrArg List.tail h
        have h1 : Val.cons a' b' = Val.cons (W.headD .nil) (ofList (W.drop 1)) := by
          simpa only [List.headD_cons] using congrArg (fun l => l.headD .nil) h
        cases h1
        rw [hout, htail] <;> rfl
      · rintro vs a ⟨-, -, -, -⟩
        exact cost_const hSC hN1 bKu
    have hB : WordM main dP (PreD (W.headD .nil :: ofList (W.drop 1) :: P) RT (E :: ET) (CH :: CT))
        (PostD (ofList (W.drop 1) :: P) RT (E :: ET) (CH :: CT)) (fun _ _ => SC) := by
      refine wordRdet (hd main) ?_ ?_ ?_
      · rintro vs a ⟨hvs, -, -, -⟩; rw [hvs]; simp
      · rintro vs a out ⟨hvs, -, -, -⟩ ⟨v', rest, heq, hout⟩
        have h : v' :: rest = W.headD .nil :: ofList (W.drop 1) :: P := by
          simpa only [hvs] using heq.symm
        have htail : rest = ofList (W.drop 1) :: P := by
          simpa only [List.tail_cons] using congrArg List.tail h
        rw [hout, htail] <;> rfl
      · rintro vs a ⟨hvs, -, -, -⟩
        rw [hvs]
        show Kd * (vsz (W.headD .nil) + 1) ≤ SC
        exact cost_mul hSC bKd (by omega)
    have hC : WordM main (pvP .nil) (PreD (ofList (W.drop 1) :: P) RT (E :: ET) (CH :: CT))
        (PostD (.nil :: ofList (W.drop 1) :: P) RT (E :: ET) (CH :: CT)) (fun _ _ => SC) := by
      refine wordRdet (hpv main .nil) ?_ ?_ ?_
      · rintro vs a ⟨hvs, -, -, -⟩; exact trivial
      · rintro vs a out ⟨hvs, -, -, -⟩ hout
        rw [hout, hvs] <;> rfl
      · rintro vs a ⟨-, -, -, -⟩
        have hsz : vsz (.nil : Val) + 1 ≤ 1000 * N := by rw [auRound_vsz_nil]; omega
        exact cost_mul hSC bKpv hsz
    have hD : WordM main pop2P (PreD (.nil :: ofList (W.drop 1) :: P) RT (E :: ET) (CH :: CT))
        (PostD (E :: .nil :: ofList (W.drop 1) :: P) RT ET (CH :: CT)) (fun _ _ => SC) := by
      refine WordM.conseq (hpop2 main E ET (.nil :: ofList (W.drop 1) :: P)) ?_ ?_ ?_
      · rintro vs a ⟨h1, -, h3, -⟩; exact ⟨h1, h3⟩
      · rintro vs a out b ⟨hvs, ha1, ha2, ha3⟩ ⟨hout, hb2, hfr⟩
        exact ⟨by rw [hout, hvs] <;> rfl, by rw [hfr 1 (by decide) (by decide), ha1] <;> rfl, hb2,
          by rw [hfr 3 (by decide) (by decide), ha3] <;> rfl,
          fun k hk0 hk1 hk2 hk3 => hfr k hk0 hk2⟩
      · rintro vs a ⟨-, -, -, -⟩
        have hsz : vsz E + 1 ≤ 1000 * N := by omega
        exact cost_mul hSC bKpop2 hsz
    have hE : WordM main cP (PreD (E :: .nil :: ofList (W.drop 1) :: P) RT ET (CH :: CT))
        (PostD (.cons E .nil :: ofList (W.drop 1) :: P) RT ET (CH :: CT)) (fun _ _ => SC) := by
      refine wordRdet (hc main) ?_ ?_ ?_
      · rintro vs a ⟨hvs, -, -, -⟩; rw [hvs]; simp
      · rintro vs a out ⟨hvs, -, -, -⟩ ⟨a', b', rest, heq, hout⟩
        have h : E :: .nil :: ofList (W.drop 1) :: P = a' :: b' :: rest := by
          simpa only [hvs] using heq
        have h1 : E = a' := by
          simpa only [List.headD_cons] using congrArg (fun l => l.headD .nil) h
        have htail : .nil :: ofList (W.drop 1) :: P = b' :: rest := by
          simpa only [List.tail_cons] using congrArg List.tail h
        have h2 : (.nil : Val) = b' := by
          simpa only [List.headD_cons] using congrArg (fun l => l.headD .nil) htail
        have h3 : ofList (W.drop 1) :: P = rest := by
          simpa only [List.tail_cons] using congrArg List.tail htail
        rw [hout, ← h1, ← h2, ← h3] <;> rfl
      · rintro vs a ⟨-, -, -, -⟩
        exact cost_const hSC hN1 bKc
    have hF : WordM main (rP 1) (PreD (.cons E .nil :: ofList (W.drop 1) :: P) RT ET (CH :: CT))
        (PostD (ofList (W.drop 1) :: .cons E .nil :: P) RT ET (CH :: CT)) (fun _ _ => SC) := by
      refine wordRdet (hr main 1) ?_ ?_ ?_
      · rintro vs a ⟨hvs, -, -, -⟩; rw [hvs]; simp
      · rintro vs a out ⟨hvs, -, -, -⟩ hQ
        rw [hQ, hvs] <;> rfl
      · rintro vs a ⟨hvs, -, -, -⟩
        rw [hvs]
        show Kr * 2 * ((vsz (.cons E .nil) + vsz (ofList (W.drop 1))) + 1) ≤ SC
        have hs : (vsz (.cons E .nil) + vsz (ofList (W.drop 1))) + 1 ≤ 40 * N := by
          rw [auRound_vsz_cons, auRound_vsz_nil]; omega
        exact cost_prod hSC bKr (by omega) hs
    have hG : WordM main aP (PreD (ofList (W.drop 1) :: .cons E .nil :: P) RT ET (CH :: CT))
        (PostD (ofList (W.drop 1 ++ [E]) :: P) RT ET (CH :: CT)) (fun _ _ => SC) := by
      refine wordRdet (ha main (W.drop 1) [E]) ?_ ?_ ?_
      · rintro vs a ⟨hvs, -, -, -⟩
        exact ⟨P, by rw [hvs] <;> rfl⟩
      · rintro vs a out ⟨hvs, -, -, -⟩ ⟨rest, heq, hout⟩
        have h : ofList (W.drop 1) :: ofList [E] :: rest
            = ofList (W.drop 1) :: Val.cons E .nil :: (P : List Val) := by
          simpa only [hvs] using heq.symm
        have hr : rest = P := by
          simpa only [List.tail_cons] using congrArg List.tail (congrArg List.tail h)
        rw [hout, hr] <;> rfl
      · rintro vs a ⟨-, -, -, -⟩
        have hsz : vsz (ofList (W.drop 1)) + 1 ≤ 1000 * N := by omega
        exact cost_mul hSC bKa hsz
    have hAll : WordM main (Cmd.seq uP (Cmd.seq dP (Cmd.seq (pvP .nil)
        (Cmd.seq pop2P (Cmd.seq cP (Cmd.seq (rP 1) aP))))))
        (PreD (W0 :: P) RT (E :: ET) (CH :: CT))
        (PostD (ofList (W.drop 1 ++ [E]) :: P) RT ET (CH :: CT))
        (fun _ _ => SC + (SC + (SC + (SC + (SC + (SC + SC)))))) :=
      seqD hA (seqD hB (seqD hC (seqD hD (seqD hE (seqD hF hG)))))
    exact WordM.mono hAll (fun _ _ => by omega)
  -- the inner ifNil
  have hInner : WordM main (ifP inNil inCons)
      (PreD (W0 :: P) RT (E :: ET) (CH :: CT))
      (fun _ a out b => (W0 = .nil → PostA (.nil :: P) RT ET (CH :: CT) a out b) ∧
        (W0 ≠ .nil → PostA (ofList (W.drop 1 ++ [E]) :: P) RT ET (CH :: CT) a out b))
      (fun _ _ => 10 * SC) := by
    have hbase := hif main inNil inCons W0 P
      (fun a => a 1 = RT ∧ a 2 = E :: ET ∧ a 3 = CH :: CT)
      (fun a => a 1 = RT ∧ a 2 = E :: ET ∧ a 3 = CH :: CT)
      (PostA (.nil :: P) RT ET (CH :: CT))
      (PostA (ofList (W.drop 1 ++ [E]) :: P) RT ET (CH :: CT))
      (4 * SC) (9 * SC) (fun _ => hInNil) (fun hv => hInCons hv)
    refine WordM.conseq hbase ?_ ?_ ?_
    · rintro vs a ⟨hvs, ha1, ha2, ha3⟩
      exact ⟨hvs, (fun _ => ⟨ha1, ha2, ha3⟩), (fun _ => ⟨ha1, ha2, ha3⟩)⟩
    · rintro vs a out b _ h; exact h
    · rintro vs a ⟨-, -, -, -⟩
      have hmax : max (4 * SC) (9 * SC) = 9 * SC := max_eq_right (by omega)
      rw [hmax]
      have hK : Kif ≤ SC := cost_const hSC hN1 bKif
      omega
  -- the cons branch of the outer ifNil
  have hBCons : WordM main bCons
      (fun vs a => vs = FLG :: W0 :: P ∧ (a 1 = RT ∧ a 2 = E :: ET ∧ a 3 = CH :: CT))
      (fun _ a out b => (W0 = .nil → PostA (.nil :: P) RT ET (CH :: CT) a out b) ∧
        (W0 ≠ .nil → PostA (ofList (W.drop 1 ++ [E]) :: P) RT ET (CH :: CT) a out b))
      (fun _ _ => 12 * SC) := by
    have hD : WordM main dP (PreD (FLG :: W0 :: P) RT (E :: ET) (CH :: CT))
        (PostD (W0 :: P) RT (E :: ET) (CH :: CT)) (fun _ _ => SC) := by
      refine wordRdet (hd main) ?_ ?_ ?_
      · rintro vs a ⟨hvs, -, -, -⟩; rw [hvs]; simp
      · rintro vs a out ⟨hvs, -, -, -⟩ ⟨v', rest, heq, hout⟩
        have h : v' :: rest = FLG :: W0 :: P := by
          simpa only [hvs] using heq.symm
        have htail : rest = W0 :: P := by
          simpa only [List.tail_cons] using congrArg List.tail h
        rw [hout, htail] <;> rfl
      · rintro vs a ⟨hvs, -, -, -⟩
        rw [hvs]
        show Kd * (vsz FLG + 1) ≤ SC
        exact cost_mul hSC bKd (by omega)
    have hpre1 : ∀ vs a mid a', PostD (W0 :: P) RT (E :: ET) (CH :: CT) vs a mid a' →
        PreD (W0 :: P) RT (E :: ET) (CH :: CT) mid a' := by
      intro vs a mid a' h
      obtain ⟨hm, ha1, ha2, ha3, -⟩ := h
      exact ⟨hm, ha1, ha2, ha3⟩
    have hcost1 : ∀ vs a mid a', PostD (W0 :: P) RT (E :: ET) (CH :: CT) vs a mid a' →
        (fun _ _ => 10 * SC) mid a' ≤ (fun _ _ => 10 * SC) vs a := fun _ _ _ _ _ => le_rfl
    have hseq := WordM.seq (B := fun _ _ => 10 * SC) hD hInner hpre1 hcost1
    refine WordM.conseq hseq ?_ ?_ ?_
    · intro vs a hpre; exact hpre
    · rintro vs a out b _ ⟨mid, a', ⟨hm, hb1, hb2, hb3, hfr1⟩, hinner⟩
      obtain ⟨hP1, hP2⟩ := hinner
      exact ⟨fun h1 => by
          obtain ⟨h1', h2', h3', h4', hfr⟩ := hP1 h1
          exact ⟨h1', h2', h3', h4', fun k hk0 hk1 hk2 hk3 => by
            rw [hfr k hk0 hk1 hk2 hk3, hfr1 k hk0 hk1 hk2 hk3]⟩,
        fun h2 => by
          obtain ⟨h1', h2', h3', h4', hfr⟩ := hP2 h2
          exact ⟨h1', h2', h3', h4', fun k hk0 hk1 hk2 hk3 => by
            rw [hfr k hk0 hk1 hk2 hk3, hfr1 k hk0 hk1 hk2 hk3]⟩⟩
    · rintro vs a ⟨-, -, -, -⟩
      omega
  -- the outer ifNil
  have hSkip : WordM main Cmd.skip
      (fun vs a => vs = W0 :: P ∧ (a 1 = RT ∧ a 2 = E :: ET ∧ a 3 = CH :: CT))
      (PostD (W0 :: P) RT (E :: ET) (CH :: CT)) (fun _ _ => SC) := by
    refine wordRdet (Work.Kernel.WordR_skip main) ?_ ?_ ?_
    · rintro vs a ⟨hvs, -, -, -⟩; exact trivial
    · rintro vs a out ⟨hvs, -, -, -⟩ hQ; rw [hQ, hvs]
    · rintro vs a ⟨-, -, -, -⟩
      exact cost_const hSC hN1 (by omega : (1 : ℕ) ≤ KS)
  have hOuter : WordM main (ifP Cmd.skip bCons)
      (PreD (FLG :: W0 :: P) RT (E :: ET) (CH :: CT))
      (fun _ a out b => (FLG = .nil → PostA (W0 :: P) RT (E :: ET) (CH :: CT) a out b) ∧
        (FLG ≠ .nil → (W0 = .nil → PostA (.nil :: P) RT ET (CH :: CT) a out b) ∧
          (W0 ≠ .nil → PostA (ofList (W.drop 1 ++ [E]) :: P) RT ET (CH :: CT) a out b)))
      (fun _ _ => 13 * SC) := by
    have hbase := hif main Cmd.skip bCons FLG (W0 :: P)
      (fun a => a 1 = RT ∧ a 2 = E :: ET ∧ a 3 = CH :: CT)
      (fun a => a 1 = RT ∧ a 2 = E :: ET ∧ a 3 = CH :: CT)
      (PostA (W0 :: P) RT (E :: ET) (CH :: CT))
      (fun a out b => (W0 = .nil → PostA (.nil :: P) RT ET (CH :: CT) a out b) ∧
        (W0 ≠ .nil → PostA (ofList (W.drop 1 ++ [E]) :: P) RT ET (CH :: CT) a out b))
      SC (12 * SC) (fun _ => hSkip) (fun _ => hBCons)
    refine WordM.conseq hbase ?_ ?_ ?_
    · rintro vs a ⟨hvs, ha1, ha2, ha3⟩
      exact ⟨hvs, (fun _ => ⟨ha1, ha2, ha3⟩), (fun _ => ⟨ha1, ha2, ha3⟩)⟩
    · rintro vs a out b _ h; exact h
    · rintro vs a ⟨-, -, -, -⟩
      have hmax : max SC (12 * SC) = 12 * SC := max_eq_right (by omega)
      rw [hmax]
      have hK : Kif ≤ SC := cost_const hSC hN1 bKif
      omega
  -- ============ assemble the whole chain ============
  let OutP : List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop :=
    fun _ a out b => (FLG = .nil → PostA (W0 :: P) RT (E :: ET) (CH :: CT) a out b) ∧
      (FLG ≠ .nil → (W0 = .nil → PostA (.nil :: P) RT ET (CH :: CT) a out b) ∧
        (W0 ≠ .nil → PostA (ofList (W.drop 1 ++ [E]) :: P) RT ET (CH :: CT) a out b))
  have trOut : ∀ (V2 A2 B2 C2 : List Val) (vs : List Val) (a : Stk → List Val)
      (mid : List Val) (a' : Stk → List Val) (out : List Val) (b : Stk → List Val),
      PostD V2 A2 B2 C2 vs a mid a' → OutP vs a' out b → OutP vs a out b := by
    intro V2 A2 B2 C2 vs a mid a' out b h1 h2
    obtain ⟨hm, hb1, hb2, hb3, hfr1⟩ := h1
    exact ⟨fun h => PostA_frame hfr1 (h2.1 h),
      fun h => ⟨fun h2' => PostA_frame hfr1 ((h2.2 h).1 h2'),
        fun h2' => PostA_frame hfr1 ((h2.2 h).2 h2')⟩⟩
  have g12 := seqGen hS12 hOuter (fun vs a mid a' out b h1 h2 => trOut _ _ _ _ vs a mid a' out b h1 h2)
  have g11 := seqGen hS11 g12 (fun vs a mid a' out b h1 h2 => trOut _ _ _ _ vs a mid a' out b h1 h2)
  have g10 := seqGen hS10 g11 (fun vs a mid a' out b h1 h2 => trOut _ _ _ _ vs a mid a' out b h1 h2)
  have g9 := seqGen hS9 g10 (fun vs a mid a' out b h1 h2 => trOut _ _ _ _ vs a mid a' out b h1 h2)
  have g8 := seqGen hS8 g9 (fun vs a mid a' out b h1 h2 => trOut _ _ _ _ vs a mid a' out b h1 h2)
  have g7 := seqGen hS7 g8 (fun vs a mid a' out b h1 h2 => trOut _ _ _ _ vs a mid a' out b h1 h2)
  have g6 := seqGen hS6 g7 (fun vs a mid a' out b h1 h2 => trOut _ _ _ _ vs a mid a' out b h1 h2)
  have g5 := seqGen hS5 g6 (fun vs a mid a' out b h1 h2 => trOut _ _ _ _ vs a mid a' out b h1 h2)
  have g4 := seqGen hS4 g5 (fun vs a mid a' out b h1 h2 => trOut _ _ _ _ vs a mid a' out b h1 h2)
  have g3 := seqGen hS3 g4 (fun vs a mid a' out b h1 h2 => trOut _ _ _ _ vs a mid a' out b h1 h2)
  have g2 := seqGen hS2 g3 (fun vs a mid a' out b h1 h2 => trOut _ _ _ _ vs a mid a' out b h1 h2)
  have g0 := seqGen hS1 g2 (fun vs a mid a' out b h1 h2 => trOut _ _ _ _ vs a mid a' out b h1 h2)
  have hchain : WordM main roundProg (PreD (W0 :: P) (REC :: RT) (E :: ET) CT) OutP (fun _ _ => 25 * SC) :=
    WordM.mono g0 (fun _ _ => by omega)
  -- ============ final conversion ============
  refine WordM.conseq hchain ?_ ?_ ?_
  · rintro vs a ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro vs a out b _ ⟨hnil, hcons⟩
    by_cases hg0 : g = 0
    · have hFLGnil : FLG = .nil := by rw [hFLG, hg0]; rfl
      obtain ⟨hout, hb1, hb2, hb3, hfr⟩ := hnil hFLGnil
      have htake : (W ++ [E]).take L = W := by
        have h1 : L ≤ W.length := by rw [hWlen]
        rw [List.take_append_of_le_length h1]
        conv_lhs => rw [← hWlen]
        rw [List.take_length]
      refine ⟨?_, hb1, ?_, hb3, hfr⟩
      · rw [hout, hW0, hg0, List.drop_zero, htake] <;> rfl
      · rw [hb2, if_neg (by omega : ¬ g = 1)] <;> rfl
    · have hg1' : g = 1 := by omega
      have hFLGne : FLG ≠ .nil := by
        rw [hFLG, auRound_auSeqFlg_ne_nil_iff]
        exact hg0
      obtain ⟨hP1, hP2⟩ := hcons hFLGne
      by_cases hW0nil : W0 = .nil
      · obtain ⟨hout, hb1, hb2, hb3, hfr⟩ := hP1 hW0nil
        have hWnil : W = [] := by
          rw [hW0] at hW0nil
          exact (auRound_ofList_eq_nil_iff W).mp hW0nil
        have hL0 : L = 0 := by rw [← hWlen, hWnil]; rfl
        refine ⟨?_, hb1, ?_, hb3, hfr⟩
        · rw [hout, hg1', hWnil, hL0]
          rfl
        · rw [hb2, if_pos hg1'] <;> rfl
      · obtain ⟨hout, hb1, hb2, hb3, hfr⟩ := hP2 hW0nil
        have hWne' : W ≠ [] := by
          intro hw; exact hW0nil (by rw [hW0, hw]; rfl)
        have htake : (W.drop 1 ++ [E]).take L = W.drop 1 ++ [E] := by
          have h1 : (W.drop 1 ++ [E]).length = L := by
            have hpos : 1 ≤ W.length := by
              cases W with
              | nil => exact absurd rfl hWne'
              | cons v vs => simp
            rw [List.length_append, List.length_drop, List.length_singleton, hWlen]
            omega
          rw [← h1, List.take_length]
        refine ⟨?_, hb1, ?_, hb3, hfr⟩
        · rw [hout, hg1', htake] <;> rfl
        · rw [hb2, if_pos hg1'] <;> rfl
  · intro vs a _
    rw [hKK, hSC]
    nlinarith [Nat.zero_le KS, Nat.zero_le N]

end Work.Resample
