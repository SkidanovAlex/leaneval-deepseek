import Mathlib
import Submission.Work.Resample.pbDefs
import Submission.Work.Resample.auJoinDefs
import Submission.Work.Layout.drainValsEv
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.Kernel.Raw
import Submission.Work.ConvR.basic

/-!
# `Work.Resample.auJoin`: the "join" word of the resampling

`Work.Resample.auJoin` builds the value `ofList CH.reverse` on top of the value stack, out of the
run `CH` of `cons`-values sitting on stack 3 (terminated by the glyph `Glyph.nil`, i.e. the
encoding of `Val.nil`, which is left in place).

The loop is driven by the top glyph of stack 3: a `cons` as long as a value is left, the `nil` of
the terminator at the end.  One iteration moves the top value of stack 3 onto stack 0
(`Work.Layout.mvVal`) and combines it with the accumulator on top of stack 0 (the Kernel word
`consV`), so after `k` iterations the accumulator is `auJoinAux (CH.take k) Val.nil`
(`auJoinAux vs acc` conses the values of `vs` onto `acc`, see `auJoinDefs`).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.Resample

open HvdH
open Work.Layout

/-! ## Elementary facts about the encoding -/

/-- `encs` of a list ending in the terminator `Val.nil`. -/
theorem auJoin_encs_append_nil (CH : List Val) :
    encs (CH ++ [Val.nil]) = encs CH ++ [Glyph.nil] := by
  rw [Work.Kernel.encs_append]
  rfl

/-! ## The cost arithmetic -/

/-- Per-element cost of the join loop against the `vsz` of the element. -/
theorem auJoinTermLe (Kc b : ℕ) : 16 * (b + 1) + (Kc + 2) ≤ (Kc + 18) * (b + 1) := by
  have h : (Kc + 18) * (b + 1) = 16 * (b + 1) + (Kc + 2) * (b + 1) := by ring
  rw [h]
  have h2 : Kc + 2 ≤ (Kc + 2) * (b + 1) := by
    have := Nat.mul_le_mul_left (Kc + 2) (by omega : 1 ≤ b + 1)
    simpa using this
  omega

/-- The total cost of the join loop is linear in the size of the resulting `cons`-chain. -/
theorem auJoinSumLe (Kc : ℕ) (vs : List Val) :
    (vs.map (fun w => 16 * (vsz w + 1) + (Kc + 2))).sum
      ≤ (Kc + 18) * (vsz (ofList vs) + 1) := by
  induction vs with
  | nil => simp [ofList, vsz, Val.enc]
  | cons v vs ih =>
    have hv : vsz (ofList (v :: vs)) + 1 = (vsz v + 1) + (vsz (ofList vs) + 1) := by
      simp only [Work.ConvR.vsz_ofList, List.map_cons, List.sum_cons, List.length_cons]
      ring
    rw [List.map_cons, List.sum_cons, hv]
    conv_rhs => rw [Nat.mul_add]
    exact Nat.add_le_add (auJoinTermLe Kc (vsz v)) ih

/-! ## One iteration -/

theorem auJoinBodyEv {main : Cmd} {t d : Stk}
    (h0t : (0 : Stk) ≠ t) (h0d : (0 : Stk) ≠ d)
    (h3t : (3 : Stk) ≠ t) (h3d : (3 : Stk) ≠ d) (htd : t ≠ d)
    {consV : Cmd} {Kc : ℕ}
    (hconsV : WordR main consV (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = Val.cons a b :: rest)
      (fun _ => Kc))
    {g : Reg → Glyph} {X : Stk → List Glyph} {v acc : Val} {vs P : List Val} {A R : List Glyph}
    (hcons : ∀ w ∈ vs, ∃ a b : Val, w = Val.cons a b)
    (h3 : X 3 = v.enc ++ (encs vs ++ A))
    (h0 : X 0 = encs (acc :: P) ++ R) :
    ∃ s' n, Ev main (auJoinBody consV t d) ⟨g, X⟩ s' n ∧
      n ≤ 16 * (vsz v + 1) + (Kc + 1) ∧
      s'.stk 3 = encs vs ++ A ∧ s'.stk 0 = encs (Val.cons v acc :: P) ++ R ∧
      s'.stk t = X t ∧ s'.stk d = X d ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 3 → k ≠ t → k ≠ d → s'.stk k = X k) ∧
      s'.reg Sk.rH = (if vs = [] then A.headD Glyph.eos else Glyph.cons) := by
  obtain ⟨s₁, n₁, hmv, hn₁, h3₁, h0₁, ht₁, hd₁, hfr₁⟩ :=
    mvVal_ev_full (main := main) (a := 3) (b := 0) (c := t) (d := d)
      (by decide) h3t h3d h0t h0d htd (v := v) (A := encs vs ++ A)
      (B := encs (acc :: P) ++ R) h3 h0
  have h0₁' : s₁.stk 0 = encs (v :: acc :: P) ++ R := by
    rw [h0₁]
    simp only [Work.Kernel.encs_cons, List.append_assoc]
  obtain ⟨out, s₂, n₂, hout, hev₂, hn₂, h0₂, hoth₂⟩ := hconsV (v :: acc :: P) (by simp) s₁ R h0₁'
  obtain ⟨a, b, rest, hvs, houtes⟩ := hout
  injection hvs with ha hvs'
  injection hvs' with hb hrest
  have hout' : out = Val.cons v acc :: P := by rw [houtes, ← ha, ← hb, ← hrest]
  have hn₂' : n₂ ≤ Kc := hn₂
  have hs₂0 : s₂.stk 0 = encs (Val.cons v acc :: P) ++ R := by rw [h0₂, hout']
  have hs₂3 : s₂.stk 3 = encs vs ++ A := by rw [hoth₂ 3 (by decide), h3₁]
  have hs₂t : s₂.stk t = X t := by rw [hoth₂ t (Ne.symm h0t), ht₁]
  have hs₂d : s₂.stk d = X d := by rw [hoth₂ d (Ne.symm h0d), hd₁]
  refine ⟨⟨Function.update s₂.reg Sk.rH ((s₂.stk 3).headD Glyph.eos), s₂.stk⟩, n₁ + (n₂ + 1),
    Ev.seq hmv (Ev.seq ⟨n₂, hev₂, le_rfl⟩ (ev_peek' main 3 Sk.rH s₂.reg s₂.stk)), by omega,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hs₂3
  · exact hs₂0
  · exact hs₂t
  · exact hs₂d
  · intro k hk0 hk3 hkt hkd
    rw [hoth₂ k hk0, hfr₁ k hk3 hk0 hkt hkd]
  · show (Function.update s₂.reg Sk.rH ((s₂.stk 3).headD Glyph.eos)) Sk.rH = _
    rw [Function.update_self, hs₂3, Work.Layout.drainVals_headD_encs hcons]

/-! ## The loop -/

theorem auJoinLoopEv {main : Cmd} {t d : Stk}
    (h0t : (0 : Stk) ≠ t) (h0d : (0 : Stk) ≠ d)
    (h3t : (3 : Stk) ≠ t) (h3d : (3 : Stk) ≠ d) (htd : t ≠ d)
    {consV : Cmd} {Kc : ℕ}
    (hconsV : WordR main consV (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = Val.cons a b :: rest)
      (fun _ => Kc)) :
    ∀ (vs : List Val) (A R : List Glyph) (acc : Val) (P : List Val) (g : Reg → Glyph)
      (X : Stk → List Glyph),
      (∀ w ∈ vs, ∃ a b : Val, w = Val.cons a b) →
      X 3 = encs vs ++ A → X 0 = encs (acc :: P) ++ R →
      g Sk.rH = (if vs = [] then A.headD Glyph.eos else Glyph.cons) →
      ∃ s', loopRuns main Sk.rH Glyph.cons (auJoinBody consV t d) vs.length ⟨g, X⟩ s'
          ((vs.map (fun w => 16 * (vsz w + 1) + (Kc + 2))).sum) ∧
        s'.stk 3 = A ∧ s'.stk 0 = encs (auJoinAux vs acc :: P) ++ R ∧
        s'.stk t = X t ∧ s'.stk d = X d ∧
        (∀ k : Stk, k ≠ 0 → k ≠ 3 → k ≠ t → k ≠ d → s'.stk k = X k) ∧
        s'.reg Sk.rH = A.headD Glyph.eos := by
  intro vs
  induction vs with
  | nil =>
      intro A R acc P g X _ h3 h0 hg
      refine ⟨⟨g, X⟩, loopRuns.zero, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [Work.Kernel.encs_nil, List.nil_append] using h3
      · simpa using h0
      · rfl
      · rfl
      · intro k _ _ _ _; rfl
      · simpa using hg
  | cons v vs ih =>
      intro A R acc P g X hcons h3 h0 hg
      have hv : ∃ a b : Val, v = Val.cons a b := hcons v (List.mem_cons_self ..)
      have hvs : ∀ w ∈ vs, ∃ a b : Val, w = Val.cons a b :=
        fun w hw => hcons w (List.mem_cons_of_mem v hw)
      have hgcons : g Sk.rH = Glyph.cons := by rw [hg]; simp
      have h3' : X 3 = v.enc ++ (encs vs ++ A) := by
        rw [h3, Work.Kernel.encs_cons, List.append_assoc]
      obtain ⟨s₁, n₁, hev₁, hn₁, h3₁, h0₁, ht₁, hd₁, hfr₁, hreg₁⟩ :=
        auJoinBodyEv (main := main) h0t h0d h3t h3d htd hconsV hvs h3' h0
      obtain ⟨s₂, hrun₂, h3₂, h0₂, ht₂, hd₂, hfr₂, hreg₂⟩ :=
        ih A R (Val.cons v acc) P s₁.reg s₁.stk hvs h3₁ h0₁ hreg₁
      have hcat : loopRuns main Sk.rH Glyph.cons (auJoinBody consV t d) (1 + vs.length) ⟨g, X⟩ s₂
          (n₁ + 1 + (vs.map (fun w => 16 * (vsz w + 1) + (Kc + 2))).sum) :=
        loopRuns.concat vs.length (loopRuns.one hgcons hev₁) hrun₂
      have hcost : n₁ + 1 + (vs.map (fun w => 16 * (vsz w + 1) + (Kc + 2))).sum
          ≤ ((v :: vs).map (fun w => 16 * (vsz w + 1) + (Kc + 2))).sum := by
        rw [List.map_cons, List.sum_cons]
        omega
      refine ⟨s₂, ?_, h3₂, ?_, ht₂.trans ht₁, hd₂.trans hd₁, ?_, hreg₂⟩
      · have hlen : 1 + vs.length = (v :: vs).length := by
          simp only [List.length_cons]; omega
        exact loopRuns.mono (by simp only [List.length_cons]; omega)
          (loopRuns.cast hlen hcat) hcost
      · rw [h0₂, auJoinAux_cons]
      · intro k hk0 hk3 hkt hkd
        rw [hfr₂ k hk0 hk3 hkt hkd, hfr₁ k hk0 hk3 hkt hkd]

/-! ## The word -/

theorem auJoin (hk : HvdH.KernelLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (CH P : List HvdH.Val),
      (∀ v ∈ CH, ∃ a b, v = HvdH.Val.cons a b) →
      Work.Resample.WordM main prog
        (fun vs a => vs = P ∧ a 3 = CH ++ [HvdH.Val.nil])
        (fun vs a out b => out = HvdH.ofList CH.reverse :: P ∧ b 3 = [HvdH.Val.nil] ∧
          (∀ k, k ≠ 0 → k ≠ 3 → b k = a k))
        (fun vs a => K * (HvdH.vsz (HvdH.ofList CH) + 1)) := by
  obtain ⟨pushProg, Kpush, hPush⟩ := hk.pushVal
  obtain ⟨consV, Kc, hconsV⟩ := hk.consV
  obtain ⟨t, d, ht0, ht3, hd0, hd3, htd⟩ := auJoinFresh
  refine ⟨Cmd.seq (pushProg Val.nil)
      (Cmd.seq (Cmd.peek 3 Sk.rH) (Cmd.loop Sk.rH Glyph.cons (auJoinBody consV t d))),
    Kc + 2 * Kpush + 21, ?_⟩
  intro main CH P hCH vs a hPre s R Bg h0 hstk
  obtain ⟨hvP, ha3⟩ := hPre
  -- push the empty-chain accumulator `nil` on stack 0
  obtain ⟨w₁, s₁, n₁, hw₁, hev₁, hc₁, h0₁, hk₁⟩ := hPush main Val.nil vs trivial s R h0
  rw [hw₁] at h0₁
  -- stack 3 holds the run `CH` followed by the terminator `Val.nil`
  have h3s : s₁.stk 3 = encs CH ++ (Glyph.nil :: Bg 3) := by
    rw [hk₁ 3 (by decide), hstk 3 (by decide), ha3, auJoin_encs_append_nil, List.append_assoc,
      List.singleton_append]
  -- read the top glyph of stack 3 into the loop register
  have hgg : (Function.update s₁.reg Sk.rH ((s₁.stk 3).headD Glyph.eos)) Sk.rH
      = (if CH = [] then (Glyph.nil :: Bg 3).headD Glyph.eos else Glyph.cons) := by
    rw [Function.update_self, h3s, Work.Layout.drainVals_headD_encs hCH]
  obtain ⟨s₂, hrun, h3₂, h0₂, ht₂, hd₂, hfr₂, hreg₂⟩ :=
    auJoinLoopEv (main := main) (Ne.symm ht0) (Ne.symm hd0) (Ne.symm ht3) (Ne.symm hd3) htd
      (hconsV main) CH (Glyph.nil :: Bg 3) R Val.nil vs
      (Function.update s₁.reg Sk.rH ((s₁.stk 3).headD Glyph.eos)) s₁.stk hCH h3s h0₁ hgg
  have hne : s₂.reg Sk.rH ≠ Glyph.cons := by
    rw [hreg₂]
    exact gnil_ne_cons
  obtain ⟨n₃, hev₃, hn₃⟩ := loopRuns.eval hrun hne
  -- the loop restores the scratch stacks and leaves stack 0 and 3 as `mvVal`/`consV` did
  have hs₂X : ∀ k : Stk, k ≠ 0 → k ≠ 3 → s₂.stk k = s₁.stk k := by
    intro k hk0 hk3
    by_cases hkt : k = t
    · rw [hkt, ht₂]
    · by_cases hkd : k = d
      · rw [hkd, hd₂]
      · rw [hfr₂ k hk0 hk3 hkt hkd]
  refine ⟨auJoinAux CH Val.nil :: P, (fun k => if k = 3 then [Val.nil] else a k), s₂,
    n₁ + (1 + n₃), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [auJoinAux_eq_ofList]
  · simp
  · intro k _ hk3
    change (if k = 3 then [Val.nil] else a k) = a k
    rw [if_neg hk3]
  · exact Eval.seq hev₁ (Eval.seq (Eval.peek 3 Sk.rH s₁) hev₃)
  · have h1 : n₁ ≤ 2 * Kpush := by
      have h : n₁ ≤ Kpush * (1 + 1) := hc₁
      omega
    have hsum := auJoinSumLe Kc CH
    have hstep : 2 * Kpush + 2 + (Kc + 18) * (vsz (ofList CH) + 1)
        ≤ (Kc + 2 * Kpush + 21) * (vsz (ofList CH) + 1) := by
      have h4 : 2 * Kpush + 3 ≤ (2 * Kpush + 3) * (vsz (ofList CH) + 1) := by
        have := Nat.mul_le_mul_left (2 * Kpush + 3) (by omega : 1 ≤ vsz (ofList CH) + 1)
        simpa using this
      have heq : (Kc + 2 * Kpush + 21) * (vsz (ofList CH) + 1)
          = (Kc + 18) * (vsz (ofList CH) + 1)
            + (2 * Kpush + 3) * (vsz (ofList CH) + 1) := by ring
      rw [heq]
      omega
    change n₁ + (1 + n₃) ≤ (Kc + 2 * Kpush + 21) * (vsz (ofList CH) + 1)
    omega
  · rw [h0₂, hvP]
  · intro k hk0
    change s₂.stk k = encs (if k = 3 then [Val.nil] else a k) ++ Bg k
    by_cases hk3 : k = 3
    · rw [hk3, h3₂, if_pos rfl]
      rfl
    · rw [if_neg hk3, hs₂X k hk0 hk3, hk₁ k hk0, hstk k hk0]

end Work.Resample
