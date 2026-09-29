import Mathlib
import Submission.Work.Layout.enumDefs
import Submission.Work.Layout.Move

set_option autoImplicit false
namespace Work.Layout
open HvdH

/-!
# Deleting the top value of a stack

`dropVal a c d = mvA a c d ; drainMark c`: `mvA` moves the top value of `a` (reversed) onto `c`
above the boundary marker `gMark`, and `drainMark c` pops `c` down to (and including) that marker,
so the value is discarded and every stack is restored.

The helper work is `drainMark`: a `while head c ≠ gMark do pop` loop.
-/

/-! ## The drain loop -/

/-- `drainBody c` with the marker on top: pop it and leave the loop. -/
private theorem drainBody_hit {main : Cmd} {c : Stk} {g : Reg → Glyph} {X : Stk → List Glyph}
    {C : List Glyph} (hc : X c = gMark :: C) :
    ∃ s' n, Ev main (drainBody c) ⟨g, X⟩ s' n ∧ n ≤ 3 ∧ s'.stk c = C ∧
      s'.reg rLoopG = Glyph.eos ∧ (∀ k : Stk, k ≠ c → s'.stk k = X k) := by
  have hhead : (X c).headD Glyph.eos = gMark := by rw [hc]; rfl
  have htail : (X c).tail = C := by rw [hc]; rfl
  have h1 : Ev main (.pop c rA) ⟨g, X⟩
      ⟨Function.update g rA ((X c).headD Glyph.eos), Function.update X c (X c).tail⟩ 1 :=
    ev_pop' main c rA g X
  have h2 : Ev main (.ite rA gMark (.set rLoopG Glyph.eos) (.set rLoopG Glyph.cons))
      ⟨Function.update g rA ((X c).headD Glyph.eos), Function.update X c (X c).tail⟩
      ⟨Function.update (Function.update g rA ((X c).headD Glyph.eos)) rLoopG Glyph.eos,
        Function.update X c (X c).tail⟩ 2 :=
    Ev.iteT (by simp only [Function.update_self]; exact hhead) (ev_set' main rLoopG Glyph.eos _ _)
  have h3 : Ev main (drainBody c) ⟨g, X⟩
      ⟨Function.update (Function.update g rA ((X c).headD Glyph.eos)) rLoopG Glyph.eos,
        Function.update X c (X c).tail⟩ 3 :=
    Ev.seq' h1 h2 (by omega)
  refine ⟨_, _, h3, le_rfl, ?_, ?_, ?_⟩
  · simp [htail]
  · simp [Function.update_of_ne (by decide : rLoopG ≠ rA)]
  · intro k hk
    simp [Function.update_of_ne hk, Function.update_of_ne hk.symm]

/-- `drainBody c` on a non-marker glyph. -/
private theorem drainBody_miss {main : Cmd} {c : Stk} {g : Reg → Glyph} {X : Stk → List Glyph}
    {h : Glyph} {G C : List Glyph} (hh : h ≠ gMark) (hc : X c = h :: (G ++ gMark :: C)) :
    ∃ s' n, Ev main (drainBody c) ⟨g, X⟩ s' n ∧ n ≤ 3 ∧ s'.stk c = G ++ gMark :: C ∧
      s'.reg rLoopG = Glyph.cons ∧ (∀ k : Stk, k ≠ c → s'.stk k = X k) := by
  have hhead : (X c).headD Glyph.eos = h := by rw [hc]; rfl
  have htail : (X c).tail = G ++ gMark :: C := by rw [hc]; rfl
  have h1 : Ev main (.pop c rA) ⟨g, X⟩
      ⟨Function.update g rA ((X c).headD Glyph.eos), Function.update X c (X c).tail⟩ 1 :=
    ev_pop' main c rA g X
  have h2 : Ev main (.ite rA gMark (.set rLoopG Glyph.eos) (.set rLoopG Glyph.cons))
      ⟨Function.update g rA ((X c).headD Glyph.eos), Function.update X c (X c).tail⟩
      ⟨Function.update (Function.update g rA ((X c).headD Glyph.eos)) rLoopG Glyph.cons,
        Function.update X c (X c).tail⟩ 2 :=
    Ev.iteF (by simp only [Function.update_self]; rw [hhead]; exact hh)
      (ev_set' main rLoopG Glyph.cons _ _)
  have h3 : Ev main (drainBody c) ⟨g, X⟩
      ⟨Function.update (Function.update g rA ((X c).headD Glyph.eos)) rLoopG Glyph.cons,
        Function.update X c (X c).tail⟩ 3 :=
    Ev.seq' h1 h2 (by omega)
  refine ⟨_, _, h3, le_rfl, ?_, ?_, ?_⟩
  · simp [htail]
  · simp [Function.update_of_ne (by decide : rLoopG ≠ rA)]
  · intro k hk
    simp [Function.update_of_ne hk, Function.update_of_ne hk.symm]

/-- The `drainMark` loop: consume `G` and then the boundary marker. -/
private theorem drainMark_loop {main : Cmd} {c : Stk} :
    ∀ (G : List Glyph) (C : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      gMark ∉ G → g rLoopG = Glyph.cons → X c = G ++ gMark :: C →
      ∃ s', loopRuns main rLoopG Glyph.cons (drainBody c) (G.length + 1) ⟨g, X⟩ s'
          (4 * (G.length + 1)) ∧ s'.stk c = C ∧ s'.reg rLoopG = Glyph.eos := by
  intro G
  induction G with
  | nil =>
      intro C g X _ hreg hc
      obtain ⟨s', n, hev, hn, hsc, hsr, -⟩ :=
        drainBody_hit (main := main) (c := c) (g := g) (X := X) (C := C) hc
      refine ⟨s', loopRuns.mono (by omega) (loopRuns.one hreg hev) ?_, hsc, hsr⟩
      omega
  | cons h G' ih =>
      intro C g X hmem hreg hc
      have hh : h ≠ gMark := fun hh => hmem (hh ▸ List.mem_cons_self ..)
      have hmem' : gMark ∉ G' := fun hx => hmem (List.mem_cons_of_mem h hx)
      obtain ⟨s₁, n₁, hev₁, hn₁, hc₁, hr₁, hf₁⟩ :=
        drainBody_miss (main := main) (c := c) (g := g) (X := X) (h := h) (G := G') (C := C) hh
          (by rw [hc]; rfl)
      obtain ⟨s₂, hrun₂, hc₂, hr₂⟩ :=
        ih C s₁.reg s₁.stk hmem' hr₁ hc₁
      have hone : loopRuns main rLoopG Glyph.cons (drainBody c) 1 ⟨g, X⟩ s₁ 4 :=
        loopRuns.mono (by omega) (loopRuns.one hreg hev₁) (by omega)
      have hcat := loopRuns.concat (G'.length + 1) hone hrun₂
      refine ⟨s₂, loopRuns.congr ?_ ?_ hcat, hc₂, hr₂⟩
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega

/-- `drainMark c` pops stack `c` down to (and including) the boundary marker `gMark`. -/
private theorem drainMark_ev {main : Cmd} {c : Stk} {G C : List Glyph} {g : Reg → Glyph}
    {X : Stk → List Glyph} (hgM : gMark ∉ G) (hc : X c = G ++ gMark :: C) :
    ∃ s' n, Ev main (drainMark c) ⟨g, X⟩ s' n ∧ n ≤ 4 * (G.length + 1) + 3 ∧ s'.stk c = C ∧
      (∀ k : Stk, k ≠ c → s'.stk k = X k) := by
  have hinit : Ev main (.set rLoopG Glyph.cons) ⟨g, X⟩
      ⟨Function.update g rLoopG Glyph.cons, X⟩ 1 := ev_set' main rLoopG Glyph.cons g X
  obtain ⟨s₁, hrun, hc₁, hr₁⟩ :=
    drainMark_loop (main := main) (c := c) G C (Function.update g rLoopG Glyph.cons) X hgM (by simp) hc
  have hloop : Ev main (.loop rLoopG Glyph.cons (drainBody c))
      ⟨Function.update g rLoopG Glyph.cons, X⟩ s₁ (4 * (G.length + 1) + 1) :=
    loopRuns.eval hrun (by rw [hr₁]; decide)
  have hmain : Ev main (drainMark c) ⟨g, X⟩ s₁ (4 * (G.length + 1) + 2) :=
    Ev.seq' hinit hloop (by omega)
  have htouch : cmdTouches (drainMark c) = {c} := by
    simp only [drainMark, drainBody, seqs, cmdTouches]
    ext k; simp
  refine ⟨s₁, _, hmain, by omega, hc₁, ?_⟩
  intro k hk
  have hfr : s₁.stk k = (⟨g, X⟩ : State).stk k :=
    Ev.frame hmain (S := {c}) (by rw [htouch]) (by simp [hk])
  simpa using hfr

/-! ## `dropVal` -/

theorem dropVal_ev {main : HvdH.Cmd} {a c d : HvdH.Stk} (hac : a ≠ c) (had : a ≠ d) (hcd : c ≠ d)
    {g : HvdH.Reg → HvdH.Glyph} {X : HvdH.Stk → List HvdH.Glyph} {v : HvdH.Val} {A : List HvdH.Glyph}
    (ha : X a = v.enc ++ A) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.dropVal a c d) ⟨g, X⟩ s' n ∧
      n ≤ 16 * (HvdH.vsz v + 1) ∧ s'.stk a = A ∧ s'.stk c = X c ∧ s'.stk d = X d ∧
      (∀ k : HvdH.Stk, k ≠ a → k ≠ c → k ≠ d → s'.stk k = X k) := by
  obtain ⟨s₁, n₁, hE₁, hn₁, ha₁, hc₁, hd₁, hf₁⟩ :=
    mvA_ev (main := main) hac had hcd v A (X c) (X d) g X ha rfl rfl
  obtain ⟨s₂, n₂, hE₂, hn₂, hc₂, hf₂⟩ :=
    drainMark_ev (main := main) (c := c) (G := v.enc.reverse) (C := X c)
      (gMark_not_mem_enc_rev v) hc₁
  have hEv : Ev main (dropVal a c d) ⟨g, X⟩ s₂ (n₁ + n₂) := Ev.seq hE₁ hE₂
  have hlen : (v.enc.reverse).length = vsz v := by simp [vsz]
  refine ⟨s₂, _, hEv, ?_, ?_, ?_, ?_, ?_⟩
  · have h₂ : n₂ ≤ 4 * (vsz v + 1) + 3 := by rw [← hlen]; exact hn₂
    have h₁ : n₁ ≤ 10 * vsz v + 10 := hn₁
    have hv := one_le_vsz v
    omega
  · rw [hf₂ a hac]; exact ha₁
  · exact hc₂
  · rw [hf₂ d hcd.symm]; exact hd₁
  · intro k hka hkc hkd
    rw [hf₂ k hkc]
    exact hf₁ k hka hkc hkd

end Work.Layout
