import Mathlib
import Submission.Work.Resample.pbDefs
import Submission.Work.Resample.auPeelDefs
import Submission.Work.Kernel.mapListPhaseA
import Submission.Work.Layout.Move

namespace Work.Resample

open HvdH
open Work.Layout

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## One iteration of the peel loop -/

/-- One iteration of `peelBody` when the top glyph of stack 0 is `cons`: the `cons` cell is popped
and the exposed element is moved to stack `T` through the scratch stacks `c`, `d`. -/
theorem peelBody_cons {main : Cmd} {T c d : Stk} (hT : T ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (hcT : c ≠ T) (hdT : d ≠ T) (hcd : c ≠ d) {g : Reg → Glyph} {X : Stk → List Glyph}
    {x : Val} {xs rest : List Val} {R : List Glyph}
    (h0 : X 0 = Glyph.cons :: (x.enc ++ (encs (ofList xs :: rest) ++ R))) :
    ∃ (s' : State) (C : ℕ), Ev main (peelBody T c d) ⟨g, X⟩ s' C ∧ C ≤ 16 * (vsz x + 1) + 4 ∧
      s'.stk 0 = encs (ofList xs :: rest) ++ R ∧ s'.stk T = x.enc ++ X T ∧
      s'.reg rLoopG = Glyph.cons ∧ (∀ k : Stk, k ≠ 0 → k ≠ T → s'.stk k = X k) := by
  have hhead : (X 0).headD Glyph.eos = Glyph.cons := by rw [h0]; rfl
  set sp : State := ⟨Function.update g rA ((X 0).headD Glyph.eos), X⟩ with hsp
  have hpeek : Ev main (.peek 0 rA) ⟨g, X⟩ sp 1 := by rw [hsp]; exact ev_peek' main 0 rA g X
  have hsp_reg : sp.reg rA = Glyph.cons := by rw [hsp]; exact hhead
  have hsp_ne : sp.reg rA ≠ Glyph.nil := by rw [hsp_reg]; exact gcons_ne_nil
  set sq : State := State.tPop sp 0 rA with hsq
  have hpop : Ev main (.pop 0 rA) sp sq 1 := by rw [hsq]; exact ev_pop main 0 rA sp
  have hsq0 : sq.stk 0 = x.enc ++ (encs (ofList xs :: rest) ++ R) := by
    rw [hsq]; simp [State.tPop, hsp, h0]
  have hsqT : sq.stk T = X T := by
    rw [hsq]; simp [State.tPop, hsp, hT]
  have hsqk : ∀ j : Stk, j ≠ 0 → sq.stk j = X j := by
    intro j hj; rw [hsq]; simp [State.tPop, hsp, hj]
  obtain ⟨s₂, n₂, hmv, hn₂, h20, h2T, h2c, h2d, hf₂⟩ :=
    mvVal_ev_full (main := main) (a := 0) (b := T) (c := c) (d := d)
      (Ne.symm hT) (Ne.symm hc0) (Ne.symm hd0) (Ne.symm hcT) (Ne.symm hdT) hcd
      (g := sq.reg) (X := sq.stk) (v := x) (A := encs (ofList xs :: rest) ++ R) (B := X T)
      hsq0 hsqT
  set sr : State := State.tSet s₂ rLoopG Glyph.cons with hsr
  have hset : Ev main (.set rLoopG Glyph.cons) s₂ sr 1 := by
    rw [hsr]; exact ev_set main rLoopG Glyph.cons s₂
  have hs0 : sr.stk 0 = encs (ofList xs :: rest) ++ R := by
    rw [hsr]; simpa [State.tSet, State.updReg] using h20
  have hsT : sr.stk T = x.enc ++ X T := by
    rw [hsr]; simpa [State.tSet, State.updReg] using h2T
  have hsr_reg : sr.reg rLoopG = Glyph.cons := by rw [hsr]; rfl
  have hsr_stk : ∀ k : Stk, sr.stk k = s₂.stk k := by intro k; rw [hsr]; rfl
  have hfr : ∀ k : Stk, k ≠ 0 → k ≠ T → sr.stk k = X k := by
    intro k hk0 hkT
    rw [hsr_stk k]
    rcases eq_or_ne k c with hc | hc
    · rw [hc, h2c, hsqk c hc0]
    · rcases eq_or_ne k d with hd | hd
      · rw [hd, h2d, hsqk d hd0]
      · rw [hf₂ k hk0 hkT hc hd, hsqk k hk0]
  refine ⟨sr, n₂ + 4, ?_, ?_, hs0, hsT, hsr_reg, hfr⟩
  · have hinner : Ev main (.seq (mvVal 0 T c d) (.set rLoopG Glyph.cons)) sq sr (n₂ + 1) :=
      Ev.seq' hmv hset (by omega)
    have hbr : Ev main (.seq (.pop 0 rA) (.seq (mvVal 0 T c d) (.set rLoopG Glyph.cons)))
        sp sr (n₂ + 2) := Ev.seq' hpop hinner (by omega)
    have hite : Ev main (.ite rA Glyph.nil (.seq (.pop 0 rA) (.set rLoopG Glyph.eos))
        (.seq (.pop 0 rA) (.seq (mvVal 0 T c d) (.set rLoopG Glyph.cons)))) sp sr (n₂ + 3) :=
      Ev.iteF hsp_ne hbr
    unfold peelBody
    exact Ev.seq' hpeek hite (by omega)
  · omega

/-- One iteration of `peelBody` when the top glyph of stack 0 is `nil`: pop it and stop. -/
theorem peelBody_nil {main : Cmd} {T c d : Stk} (hT : T ≠ 0) {g : Reg → Glyph}
    {X : Stk → List Glyph} {rest : List Val} {R : List Glyph}
    (h0 : X 0 = Glyph.nil :: (encs rest ++ R)) :
    ∃ (s' : State) (C : ℕ), Ev main (peelBody T c d) ⟨g, X⟩ s' C ∧ C ≤ 4 ∧
      s'.stk 0 = encs rest ++ R ∧ s'.stk T = X T ∧ s'.reg rLoopG = Glyph.eos ∧
      (∀ k : Stk, k ≠ 0 → k ≠ T → s'.stk k = X k) := by
  have hhead : (X 0).headD Glyph.eos = Glyph.nil := by rw [h0]; rfl
  set sp : State := ⟨Function.update g rA ((X 0).headD Glyph.eos), X⟩ with hsp
  have hpeek : Ev main (.peek 0 rA) ⟨g, X⟩ sp 1 := by rw [hsp]; exact ev_peek' main 0 rA g X
  have hsp_reg : sp.reg rA = Glyph.nil := by rw [hsp]; exact hhead
  set sq : State := State.tPop sp 0 rA with hsq
  have hpop : Ev main (.pop 0 rA) sp sq 1 := by rw [hsq]; exact ev_pop main 0 rA sp
  have hsq0 : sq.stk 0 = encs rest ++ R := by
    rw [hsq]; simp [State.tPop, hsp, h0]
  have hsqT : sq.stk T = X T := by
    rw [hsq]; simp [State.tPop, hsp, hT]
  have hsqk : ∀ j : Stk, j ≠ 0 → sq.stk j = X j := by
    intro j hj; rw [hsq]; simp [State.tPop, hsp, hj]
  set sr : State := State.tSet sq rLoopG Glyph.eos with hsr
  have hset : Ev main (.set rLoopG Glyph.eos) sq sr 1 := by
    rw [hsr]; exact ev_set main rLoopG Glyph.eos sq
  have hs0 : sr.stk 0 = encs rest ++ R := by
    rw [hsr]; simpa [State.tSet, State.updReg] using hsq0
  have hsT : sr.stk T = X T := by
    rw [hsr]; simpa [State.tSet, State.updReg] using hsqT
  have hsr_reg : sr.reg rLoopG = Glyph.eos := by rw [hsr]; rfl
  have hsr_stk : ∀ k : Stk, sr.stk k = sq.stk k := by intro k; rw [hsr]; rfl
  have hfr : ∀ k : Stk, k ≠ 0 → k ≠ T → sr.stk k = X k := by
    intro k hk0 hkT; rw [hsr_stk k]; exact hsqk k hk0
  refine ⟨sr, 4, ?_, ?_, hs0, hsT, hsr_reg, hfr⟩
  · have hbr : Ev main (.seq (.pop 0 rA) (.set rLoopG Glyph.eos)) sp sr 2 :=
      Ev.seq' hpop hset (by omega)
    have hite : Ev main (.ite rA Glyph.nil (.seq (.pop 0 rA) (.set rLoopG Glyph.eos))
        (.seq (.pop 0 rA) (.seq (mvVal 0 T c d) (.set rLoopG Glyph.cons)))) sp sr 3 :=
      Ev.iteT hsp_reg hbr
    unfold peelBody
    exact Ev.seq' hpeek hite (by omega)
  · omega

/-! ## The loop -/

set_option maxHeartbeats 3200000 in
/-- The peel loop: from `X 0 = encs (ofList xs :: rest) ++ R` it runs `xs.length + 1` iterations and
leaves `rest` on stack 0 and the elements of `xs` (reversed) on top of `X T`. -/
theorem peelLoop_ev {main : Cmd} {T c d : Stk} (hT : T ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (hcT : c ≠ T) (hdT : d ≠ T) (hcd : c ≠ d) :
    ∀ (xs : List Val) (rest : List Val) (R : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      g rLoopG = Glyph.cons → X 0 = encs (ofList xs :: rest) ++ R →
      ∃ (s' : State) (C : ℕ),
        loopRuns main rLoopG Glyph.cons (peelBody T c d) (xs.length + 1) ⟨g, X⟩ s' C ∧
        C ≤ 16 * ((xs.map vsz).sum + xs.length) + 5 * xs.length + 5 ∧
        s'.stk 0 = encs rest ++ R ∧ s'.stk T = encs xs.reverse ++ X T ∧
        s'.reg rLoopG = Glyph.eos ∧ (∀ k : Stk, k ≠ 0 → k ≠ T → s'.stk k = X k) := by
  intro xs
  induction xs with
  | nil =>
    intro rest R g X hg h0
    have h0' : X 0 = Glyph.nil :: (encs rest ++ R) := by
      rw [h0]; simp [ofList, encs, Val.enc]
    obtain ⟨s₁, C₁, hev₁, hC₁, hs₁0, hs₁T, hs₁r, hfr₁⟩ := peelBody_nil (T := T) hT h0'
    refine ⟨s₁, C₁ + 1, ?_, ?_, hs₁0, ?_, hs₁r, ?_⟩
    · exact loopRuns.one hg hev₁
    · simp only [List.length_nil, List.map_nil, List.sum_nil]
      omega
    · rw [hs₁T]
      simp only [List.reverse_nil, Work.Kernel.encs_nil, List.nil_append]
    · intro k hk0 hkT; exact hfr₁ k hk0 hkT
  | cons x xs ih =>
    intro rest R g X hg h0
    have h0' : X 0 = Glyph.cons :: (x.enc ++ (encs (ofList xs :: rest) ++ R)) := by
      rw [h0, Work.Kernel.mapList_encs_ofList_cons]
      simp only [List.cons_append, List.append_assoc]
    obtain ⟨s₁, C₁, hev₁, hC₁, hs₁0, hs₁T, hs₁r, hfr₁⟩ :=
      peelBody_cons (T := T) (c := c) (d := d) hT hc0 hd0 hcT hdT hcd h0'
    obtain ⟨s₂, C₂, hrun₂, hC₂, hs₂0, hs₂T, hs₂r, hfr₂⟩ :=
      ih rest R s₁.reg s₁.stk hs₁r hs₁0
    have hb₁ : Ev main (peelBody T c d) ⟨g, X⟩ s₁ (16 * (vsz x + 1) + 4) := hev₁.mono hC₁
    refine ⟨s₂, (16 * (vsz x + 1) + 4) + C₂ + 1, ?_, ?_, hs₂0, ?_, hs₂r, ?_⟩
    · refine loopRuns.cast ?_ (loopRuns.succ' hg hb₁ hrun₂ le_rfl)
      simp only [List.length_cons]
    · simp only [List.map_cons, List.sum_cons, List.length_cons] at hC₂ ⊢
      omega
    · rw [hs₂T, hs₁T, Work.Kernel.mapList_encs_reverse_cons, List.append_assoc]
    · intro k hk0 hkT
      rw [hfr₂ k hk0 hkT, hfr₁ k hk0 hkT]

/-! ## The whole program -/

set_option maxHeartbeats 1600000 in
/-- `peelProg`: initialise the loop register and peel the list value on top of stack 0 onto stack
`T`.  Cost `16·|ofList xs| + O(|xs|)`. -/
theorem peelProg_ev {main : Cmd} {T c d : Stk} (hT : T ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (hcT : c ≠ T) (hdT : d ≠ T) (hcd : c ≠ d)
    (xs : List Val) (rest : List Val) (R : List Glyph) (B : List Glyph)
    (g : Reg → Glyph) (X : Stk → List Glyph)
    (h0 : X 0 = encs (ofList xs :: rest) ++ R) (hB : X T = B) :
    ∃ (s' : State) (n : ℕ), Ev main (peelProg T c d) ⟨g, X⟩ s' n ∧
      n ≤ 16 * ((xs.map vsz).sum + xs.length) + 5 * xs.length + 7 ∧
      s'.stk 0 = encs rest ++ R ∧ s'.stk T = encs xs.reverse ++ B ∧
      (∀ k : Stk, k ≠ 0 → k ≠ T → s'.stk k = X k) := by
  set g' : Reg → Glyph := Function.update g rLoopG Glyph.cons with hg'
  have hg'r : g' rLoopG = Glyph.cons := by rw [hg']; simp
  have hset : Ev main (.set rLoopG Glyph.cons) ⟨g, X⟩ ⟨g', X⟩ 1 := by
    rw [hg']; exact ev_set' main rLoopG Glyph.cons g X
  obtain ⟨s₁, C, hrun, hC, hs₁0, hs₁T, hs₁r, hfr⟩ :=
    peelLoop_ev hT hc0 hd0 hcT hdT hcd xs rest R g' X hg'r h0
  obtain ⟨n₁, hev₁, hn₁⟩ := loopRuns.eval' hrun (by rw [hs₁r]; intro h; cases h)
  have hloop : Ev main (.loop rLoopG Glyph.cons (peelBody T c d)) ⟨g', X⟩ s₁ n₁ :=
    ⟨n₁, hev₁, le_rfl⟩
  have hmain : Ev main (peelProg T c d) ⟨g, X⟩ s₁ (n₁ + 1) := by
    unfold peelProg
    exact Ev.seq' hset hloop (by omega)
  refine ⟨s₁, n₁ + 1, hmain, ?_, hs₁0, ?_, hfr⟩
  · have h1 : n₁ ≤ C + 1 := hn₁
    have h2 : C ≤ 16 * ((xs.map vsz).sum + xs.length) + 5 * xs.length + 5 := hC
    omega
  · rw [hs₁T, hB]

/-! ## The target -/

theorem auPeel (T : HvdH.Stk) (hT : T ≠ 0) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (xs : List HvdH.Val) (rest : List HvdH.Val)
      (m : HvdH.Val),
      Work.Resample.WordM main prog
        (fun vs a => vs = HvdH.ofList xs :: rest ∧ a T = [m])
        (fun vs a out b => out = rest ∧ a T = [m] ∧ b T = xs.reverse ++ [m] ∧
          ∀ k, k ≠ 0 → k ≠ T → b k = a k)
        (fun vs a => K * (HvdH.vsz (HvdH.ofList xs) + 1) + K) := by
  obtain ⟨c, d, hcd, hc0, hcT, hd0, hdT⟩ := peelScratch T hT
  refine ⟨peelProg T c d, 64, ?_⟩
  intro main xs rest m vs a hpre s R Bg h0 hk
  obtain ⟨hvs, ha⟩ := hpre
  obtain ⟨g, X⟩ := s
  have h0X : X 0 = encs vs ++ R := h0
  have hkX : ∀ k : Stk, k ≠ 0 → X k = encs (a k) ++ Bg k := hk
  have h0' : X 0 = encs (ofList xs :: rest) ++ R := by rw [h0X, hvs]
  have hB : X T = encs [m] ++ Bg T := by rw [hkX T hT, ha]
  obtain ⟨s', n, ⟨n₀, hev₀, hn₀⟩, hn, hs'0, hs'T, hfr⟩ :=
    peelProg_ev (main := main) hT hc0 hd0 hcT hdT hcd xs rest R (encs [m] ++ Bg T) g X h0' hB
  refine ⟨rest, Function.update a T (xs.reverse ++ [m]), s', n₀,
    ⟨rfl, ha, Function.update_self T (xs.reverse ++ [m]) a, ?_⟩, hev₀, ?_, hs'0, ?_⟩
  · intro k hk0 hkT
    exact Function.update_of_ne hkT (xs.reverse ++ [m]) a
  · change n₀ ≤ 64 * (vsz (ofList xs) + 1) + 64
    have hvz := peelVsz_ofList xs
    have hlen := peelLen_le_sum xs
    have h1 : n₀ ≤ n := hn₀
    have h2 : n ≤ 16 * ((xs.map vsz).sum + xs.length) + 5 * xs.length + 7 := hn
    omega
  · intro k hk0
    by_cases hkT : k = T
    · subst hkT
      rw [Function.update_self, hs'T, Work.Kernel.encs_append, List.append_assoc]
    · rw [Function.update_of_ne hkT, hfr k hk0 hkT, hkX k hk0]

end Work.Resample
