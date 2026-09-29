import Mathlib
import Submission.Work.IntLib.AddSub.Defs
import Submission.Work.IntLib.AddSub.Basic
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.Basic
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.IntLib.AddSub.SetupChunks

/-!
# `IntLib` / add–sub: `asw_setup` with an abstract sign map

`asw_setup fp` parses the two integer values on top of stack 0 into the scratch stacks of the
add–sub development.  The second sign glyph is passed through the sub-program `fp` before being
stored on `sSgB`; here `fp` is described abstractly by a map `φ` on the two sign glyphs.

The proof splits `asw_setup fp` (see `Submission.Work.IntLib.AddSub.SetupChunks`) into its five
chunks (`Lmark`, `LsignA`, `Lparse sA`, `Lfp fp`, `Lparse sB`), proves a Hoare-style `Ev` spec
for each of them (with an explicit "everything else is untouched" clause), and composes them
with `aswgen_seqs_append`.
-/

set_option autoImplicit false

namespace Work.IntLib.AddSub

open HvdH

/-! ## Generic `Ev` lemmas -/

/-- `Eval` of `.skip` does not move the state. -/
theorem aswgen_Ev_skip {main : Cmd} {s t : State} {C : ℕ} (h : Ev main .skip s t C) : t = s := by
  obtain ⟨n, he, -⟩ := h
  cases he with
  | skip => rfl

/-- Splitting an `Ev` of a sequence into its two halves. -/
theorem aswgen_Ev_seq {main : Cmd} {p q : Cmd} {s u : State} {C : ℕ}
    (h : Ev main (.seq p q) s u C) :
    ∃ (t : State) (C₁ C₂ : ℕ), Ev main p s t C₁ ∧ Ev main q t u C₂ ∧ C₁ + C₂ ≤ C := by
  obtain ⟨n, he, hn⟩ := h
  cases he with
  | seq h₁ h₂ => exact ⟨_, _, _, ⟨_, h₁, le_rfl⟩, ⟨_, h₂, le_rfl⟩, hn⟩

/-- `Ev` of `seqs` is compositional in the concatenation of the command lists. -/
theorem aswgen_seqs_append {main : Cmd} {l₁ l₂ : List Cmd} {s t u : State} {C₁ C₂ : ℕ}
    (h₁ : Ev main (seqs l₁) s t C₁) (h₂ : Ev main (seqs l₂) t u C₂) :
    Ev main (seqs (l₁ ++ l₂)) s u (C₁ + C₂) := by
  have aux : ∀ (l₁ l₂ : List Cmd) (s t u : State) (C₁ C₂ : ℕ),
      Ev main (seqs l₁) s t C₁ → Ev main (seqs l₂) t u C₂ →
      Ev main (seqs (l₁ ++ l₂)) s u (C₁ + C₂) := by
    intro l₁
    induction l₁ with
    | nil =>
        intro l₂ s t u C₁ C₂ h₁ h₂
        have hts : t = s := aswgen_Ev_skip h₁
        rw [hts] at h₂
        exact h₂.mono (by omega)
    | cons c cs ih =>
        intro l₂ s t u C₁ C₂ h₁ h₂
        cases l₂ with
        | nil =>
            have htu : u = t := aswgen_Ev_skip h₂
            subst htu
            rw [List.append_nil]
            exact h₁.mono (by omega)
        | cons d ds =>
            cases cs with
            | nil => exact Ev.seq' h₁ h₂ (by omega)
            | cons e es =>
                have h₁' : Ev main (.seq c (seqs (e :: es))) s t C₁ := h₁
                obtain ⟨t', C₁', C₂', hc, hrest, hle⟩ := aswgen_Ev_seq h₁'
                have hrec : Ev main (seqs ((e :: es) ++ (d :: ds))) t' u (C₂' + C₂) :=
                  ih (d :: ds) t' t u C₂' C₂ hrest h₂
                exact Ev.seq' hc hrec (by omega)
  exact aux l₁ l₂ s t u C₁ C₂ h₁ h₂

/-- `.pop k r` only touches stack `k`. -/
theorem aswgen_pop_touches (k : Stk) (r : Reg) :
    cmdTouches (.pop k r) ⊆ ({k} : Finset Stk) := by
  intro x hx
  exact hx

/-- `asw_drain` only touches its two stacks. -/
theorem aswgen_drain_touches (a b : Stk) (T : Glyph) (r rF : Reg) :
    cmdTouches (asw_drain a b T r rF) ⊆ ({a, b} : Finset Stk) := by
  intro j hj
  simp only [asw_drain, seqs, cmdTouches, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_insert, Finset.notMem_empty] at hj ⊢
  tauto

/-! ## The marker blocks -/

/-- The two commands pushing the marker `gmk k` on stack `k`. -/
abbrev aswgen_markPair (k : Stk) : List Cmd := [.set rA (gmk k), .push k rA]

/-- Pushing one marker. -/
theorem aswgen_markPair_ev {main : Cmd} (k : Stk) (g : Reg → Glyph) (X : Stk → List Glyph) :
    Ev main (seqs [.set rA (gmk k), .push k rA]) ⟨g, X⟩
      ⟨Function.update g rA (gmk k), Function.update X k (gmk k :: X k)⟩ 2 := by
  have h₁ : Ev main (.set rA (gmk k)) ⟨g, X⟩ ⟨Function.update g rA (gmk k), X⟩ 1 :=
    ev_set' main rA (gmk k) g X
  have h₂ : Ev main (.push k rA) ⟨Function.update g rA (gmk k), X⟩
      ⟨Function.update g rA (gmk k), Function.update X k (gmk k :: X k)⟩ 1 := by
    have hp := ev_push' main k rA (Function.update g rA (gmk k)) X
    simpa only [upReg_same] using hp
  simp only [seqs]
  exact Ev.seq h₁ h₂

/-- Pushing the markers of a list of pairwise distinct stacks. -/
theorem aswgen_markAux_ev {main : Cmd} :
    ∀ (ks : List Stk) (g : Reg → Glyph) (X : Stk → List Glyph), ks.Nodup →
      ∃ s' n, Ev main (seqs (ks.flatMap aswgen_markPair)) ⟨g, X⟩ s' n ∧
        n ≤ 2 * ks.length + 1 ∧
        (∀ k, k ∈ ks → s'.stk k = gmk k :: X k) ∧
        (∀ k, k ∉ ks → s'.stk k = X k) := by
  intro ks
  induction ks with
  | nil =>
      intro g X _
      refine ⟨⟨g, X⟩, 1, ?_, ?_, ?_, ?_⟩
      · rw [List.flatMap_nil]
        exact Ev.seqs_nil (main := main) (s := (⟨g, X⟩ : State))
      · simp
      · intro k hk
        exact absurd hk (List.not_mem_nil (a := k))
      · intro k _
        rfl
  | cons k ks ih =>
      intro g X hnodup
      have hk_notin : k ∉ ks := (List.nodup_cons.1 hnodup).1
      have hks : ks.Nodup := (List.nodup_cons.1 hnodup).2
      have hp : Ev main (seqs (aswgen_markPair k)) ⟨g, X⟩
          ⟨Function.update g rA (gmk k), Function.update X k (gmk k :: X k)⟩ 2 :=
        aswgen_markPair_ev k g X
      obtain ⟨s₂, n₂, he₂, hn₂, hmem₂, hnotin₂⟩ :=
        ih (Function.update g rA (gmk k)) (Function.update X k (gmk k :: X k)) hks
      refine ⟨s₂, 2 + n₂, ?_, ?_, ?_, ?_⟩
      · rw [List.flatMap_cons]
        exact aswgen_seqs_append hp he₂
      · have hlen : (k :: ks).length = ks.length + 1 := rfl
        omega
      · intro j hj
        rcases List.mem_cons.1 hj with hjk | hj
        · rw [hjk, hnotin₂ k hk_notin]
          simp only [upStk_same]
        · have hjk : j ≠ k := fun h => hk_notin (h ▸ hj)
          rw [hmem₂ j hj, upStk_ne hjk]
      · intro j hj
        have hjks : j ∉ ks := fun h => hj (List.mem_cons_of_mem k h)
        have hjk : j ≠ k := fun h => hj (List.mem_cons.2 (Or.inl h))
        rw [hnotin₂ j hjks, upStk_ne hjk]

/-- The marker chunk of `asw_setup`. -/
theorem aswgen_Lmark_ev {main : Cmd} (g : Reg → Glyph) (X : Stk → List Glyph) :
    ∃ s' n, Ev main (seqs Lmark) ⟨g, X⟩ s' n ∧ n ≤ 15 ∧ s'.stk 0 = X 0 ∧
      s'.stk sBuf = gmk sBuf :: X sBuf ∧ s'.stk sA = gmk sA :: X sA ∧
      s'.stk sB = gmk sB :: X sB ∧ s'.stk sO1 = gmk sO1 :: X sO1 ∧
      s'.stk sO2 = gmk sO2 :: X sO2 ∧ s'.stk sSgA = gmk sSgA :: X sSgA ∧
      s'.stk sSgB = gmk sSgB :: X sSgB := by
  have hpr : seqs (([sBuf, sA, sB, sO1, sO2, sSgA, sSgB] : List Stk).flatMap aswgen_markPair)
      = seqs Lmark := by
    simp only [aswgen_markPair, List.flatMap_cons, List.flatMap_nil, List.cons_append,
      List.nil_append]
  obtain ⟨s', n, hev, hn, hmem, hnotin⟩ :=
    aswgen_markAux_ev [sBuf, sA, sB, sO1, sO2, sSgA, sSgB] g X
      (show List.Pairwise (· ≠ ·) ([sBuf, sA, sB, sO1, sO2, sSgA, sSgB] : List Stk) from by decide)
  refine ⟨s', n, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpr] at hev; exact hev
  · simpa using hn
  · exact hnotin 0 (by decide)
  · exact hmem sBuf (by decide)
  · exact hmem sA (by decide)
  · exact hmem sB (by decide)
  · exact hmem sO1 (by decide)
  · exact hmem sO2 (by decide)
  · exact hmem sSgA (by decide)
  · exact hmem sSgB (by decide)

/-! ## The sign chunk of the first operand -/

/-- `LsignA`: pop the sign glyph of the first operand onto `sSgA`. -/
theorem aswgen_LsignA_ev {main : Cmd} (g : Reg → Glyph) (X : Stk → List Glyph) {sg : Glyph}
    {A : List Glyph} (h : X 0 = sg :: A) :
    ∃ s' n, Ev main (seqs LsignA) ⟨g, X⟩ s' n ∧ n ≤ 2 ∧ s'.stk 0 = A ∧
      s'.stk sSgA = sg :: X sSgA ∧
      (∀ j : Stk, j ≠ 0 → j ≠ sSgA → s'.stk j = X j) := by
  let X₁ : Stk → List Glyph := Function.update X 0 (X 0).tail
  let X₂ : Stk → List Glyph := Function.update X₁ sSgA
    ((Function.update g rB ((X 0).headD Glyph.eos)) rB :: X₁ sSgA)
  have hg : (Function.update g rB ((X 0).headD Glyph.eos) : Reg → Glyph) rB = sg := by
    simp only [upReg_same, h, List.headD_cons]
  have h₁ : Ev main (.pop 0 rB) ⟨g, X⟩
      ⟨Function.update g rB ((X 0).headD Glyph.eos), X₁⟩ 1 := ev_pop' main 0 rB g X
  have h₂ : Ev main (.push sSgA rB)
      ⟨Function.update g rB ((X 0).headD Glyph.eos), X₁⟩
      ⟨Function.update g rB ((X 0).headD Glyph.eos), X₂⟩ 1 := by
    have hp := ev_push' main sSgA rB (Function.update g rB ((X 0).headD Glyph.eos)) X₁
    simpa only [X₂] using hp
  have hev : Ev main (seqs LsignA) ⟨g, X⟩
      ⟨Function.update g rB ((X 0).headD Glyph.eos), X₂⟩ 2 := by
    simp only [LsignA, seqs]
    exact Ev.seq h₁ h₂
  have hX0 : (⟨Function.update g rB ((X 0).headD Glyph.eos), X₂⟩ : State).stk 0 = A := by
    show X₂ 0 = A
    simp only [X₂, X₁, upStk_ne' (show (0 : Stk) ≠ sSgA by decide), upStk_same, h,
      List.tail_cons]
  have hXS : (⟨Function.update g rB ((X 0).headD Glyph.eos), X₂⟩ : State).stk sSgA =
      sg :: X sSgA := by
    show X₂ sSgA = sg :: X sSgA
    simp only [X₂, upStk_same, hg, X₁, upStk_ne (show (sSgA : Stk) ≠ 0 by decide)]
  refine ⟨⟨Function.update g rB ((X 0).headD Glyph.eos), X₂⟩, 2, hev, le_rfl, hX0, hXS, ?_⟩
  intro j hj0 hjS
  show X₂ j = X j
  simp only [X₂, upStk_ne hjS, X₁, upStk_ne hj0]

/-! ## The `fp` chunk -/

/-- `Lfp fp`: pop the sign of the second operand, apply `fp` to it, push the result on `sSgB`. -/
theorem aswgen_Lfp_ev {main : Cmd} (fp : Cmd) (φ : Glyph → Glyph)
    (hfp : ∀ (g : Reg → Glyph) (X : Stk → List Glyph),
      (g rB = Glyph.pos ∨ g rB = Glyph.neg) →
      ∃ s' n, Ev main fp ⟨g, X⟩ s' n ∧ n ≤ 3 ∧ s'.stk = X ∧ s'.reg rB = φ (g rB))
    (g : Reg → Glyph) (X : Stk → List Glyph) {sg : Glyph} {A : List Glyph}
    (h : X 0 = sg :: A) (hsg : sg = Glyph.pos ∨ sg = Glyph.neg) :
    ∃ s' n, Ev main (seqs (Lfp fp)) ⟨g, X⟩ s' n ∧ n ≤ 5 ∧ s'.stk 0 = A ∧
      s'.stk sSgB = φ sg :: X sSgB ∧
      (∀ j : Stk, j ≠ 0 → j ≠ sSgB → s'.stk j = X j) := by
  let X₁ : Stk → List Glyph := Function.update X 0 (X 0).tail
  have hg₁ : (Function.update g rB ((X 0).headD Glyph.eos) : Reg → Glyph) rB = sg := by
    simp only [upReg_same, h, List.headD_cons]
  have hpop : Ev main (.pop 0 rB) ⟨g, X⟩
      ⟨Function.update g rB ((X 0).headD Glyph.eos), X₁⟩ 1 := ev_pop' main 0 rB g X
  have hsg' : (Function.update g rB ((X 0).headD Glyph.eos) : Reg → Glyph) rB = Glyph.pos ∨
      (Function.update g rB ((X 0).headD Glyph.eos) : Reg → Glyph) rB = Glyph.neg := by
    rw [hg₁]; exact hsg
  obtain ⟨s₂, n₂, he₂, hn₂, h₂stk, h₂reg⟩ :=
    hfp (Function.update g rB ((X 0).headD Glyph.eos)) X₁ hsg'
  have h₂reg' : s₂.reg rB = φ sg := by rw [h₂reg, hg₁]
  let X₂ : Stk → List Glyph := Function.update s₂.stk sSgB (s₂.reg rB :: s₂.stk sSgB)
  have hpush : Ev main (.push sSgB rB) s₂ ⟨s₂.reg, X₂⟩ 1 :=
    ev_push' main sSgB rB s₂.reg s₂.stk
  have hev : Ev main (seqs (Lfp fp)) ⟨g, X⟩ ⟨s₂.reg, X₂⟩ 5 := by
    simp only [Lfp, seqs]
    exact (Ev.seq hpop (Ev.seq he₂ hpush)).mono (by omega)
  have hX0 : (⟨s₂.reg, X₂⟩ : State).stk 0 = A := by
    show X₂ 0 = A
    simp only [X₂, h₂stk, X₁, upStk_ne' (show (0 : Stk) ≠ sSgB by decide), upStk_same, h,
      List.tail_cons]
  have hXS : (⟨s₂.reg, X₂⟩ : State).stk sSgB = φ sg :: X sSgB := by
    show X₂ sSgB = φ sg :: X sSgB
    simp only [X₂, upStk_same, h₂reg', h₂stk, X₁,
      upStk_ne (show (sSgB : Stk) ≠ 0 by decide)]
  refine ⟨⟨s₂.reg, X₂⟩, 5, hev, le_rfl, hX0, hXS, ?_⟩
  intro j hj0 hjS
  show X₂ j = X j
  simp only [X₂, h₂stk, X₁, upStk_ne hjS, upStk_ne hj0]

/-! ## The parse chunk -/

/-- `Lparse k`: move one encoded value off stack 0 onto the scratch stack `k`. -/
theorem aswgen_parse_step {main : Cmd} (k : Stk) (hk0 : k ≠ 0) (hkb : k ≠ sBuf)
    (bits : List Bool) (A B C : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph)
    (h0 : X 0 = bits.map Glyph.bit ++ Glyph.iend :: A)
    (hsb : X sBuf = gmk sBuf :: B) (hk : X k = gmk k :: C) :
    ∃ s' n, Ev main (seqs (Lparse k)) ⟨g, X⟩ s' n ∧ n ≤ 10 * (bits.length + 1) + 5 ∧
      s'.stk 0 = A ∧ s'.stk sBuf = gmk sBuf :: B ∧
      s'.stk k = bits.map Glyph.bit ++ gmk k :: C ∧
      (∀ j : Stk, j ≠ 0 → j ≠ sBuf → j ≠ k → s'.stk j = X j) := by
  have hbits : ∀ h ∈ bits.map Glyph.bit, h ≠ Glyph.iend := by
    intro h hh
    obtain ⟨b, -, hb⟩ := List.mem_map.1 hh
    rw [← hb]
    intro hc
    cases hc
  obtain ⟨s₁, n₁, he₁, hn₁, h₁₀, h₁buf, -⟩ :=
    asw_drain_ev (main := main) 0 sBuf Glyph.iend rT rF (by decide) (by decide)
      (bits.map Glyph.bit) A (gmk sBuf :: B) g X hbits h0 hsb
  have hn₁' : n₁ ≤ 5 * (bits.length + 1) + 2 := by
    simpa only [List.length_map] using hn₁
  have h₁k : s₁.stk k = gmk k :: C := by
    have hf := Ev.frame he₁ (aswgen_drain_touches 0 sBuf Glyph.iend rT rF) (k := k) (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hk0, hkb⟩)
    exact hf.trans hk
  let g₁ : Reg → Glyph := Function.update s₁.reg rT ((s₁.stk 0).headD Glyph.eos)
  let X₂ : Stk → List Glyph := Function.update s₁.stk 0 (s₁.stk 0).tail
  have hpop : Ev main (.pop 0 rT) s₁ ⟨g₁, X₂⟩ 1 := ev_pop' main 0 rT s₁.reg s₁.stk
  have h₂₀ : X₂ 0 = A := by
    simp only [X₂, upStk_same, h₁₀, List.tail_cons]
  have h₂buf : X₂ sBuf = (bits.map Glyph.bit).reverse ++ gmk sBuf :: B := by
    simp only [X₂, upStk_ne (show (sBuf : Stk) ≠ 0 by decide), h₁buf]
  have h₂k : X₂ k = gmk k :: C := by
    simp only [X₂, upStk_ne hk0, h₁k]
  have hbits' : ∀ h ∈ (bits.map Glyph.bit).reverse, h ≠ gmk sBuf := by
    intro h hh
    obtain ⟨b, -, hb⟩ := List.mem_map.1 (List.mem_reverse.1 hh)
    rw [← hb]
    intro hc
    cases hc
  obtain ⟨s₃, n₃, he₃, hn₃, h₃buf, h₃k, -⟩ :=
    asw_drain_ev (main := main) sBuf k (gmk sBuf) rT rF hkb.symm (by decide)
      (bits.map Glyph.bit).reverse B (gmk k :: C) g₁ X₂ hbits' h₂buf h₂k
  have hn₃' : n₃ ≤ 5 * (bits.length + 1) + 2 := by
    simpa only [List.length_reverse, List.length_map] using hn₃
  have h₃₀ : s₃.stk 0 = A := by
    have hf := Ev.frame he₃ (aswgen_drain_touches sBuf k (gmk sBuf) rT rF) (k := (0 : Stk)) (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(by decide : (0 : Stk) ≠ sBuf), fun h => hk0 h.symm⟩)
    exact hf.trans h₂₀
  have h₃fr : ∀ j : Stk, j ≠ 0 → j ≠ sBuf → j ≠ k → s₃.stk j = X j := by
    intro j hj0 hjb hjk
    have hf₃ := Ev.frame he₃ (aswgen_drain_touches sBuf k (gmk sBuf) rT rF) (k := j) (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hjb, hjk⟩)
    have hf₂ := Ev.frame hpop (aswgen_pop_touches 0 rT) (k := j) (by
      simp only [Finset.mem_singleton]
      exact hj0)
    have hf₁ := Ev.frame he₁ (aswgen_drain_touches 0 sBuf Glyph.iend rT rF) (k := j) (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hj0, hjb⟩)
    exact hf₃.trans (hf₂.trans hf₁)
  have h₃k' : s₃.stk k = bits.map Glyph.bit ++ gmk k :: C := by
    rw [h₃k, List.reverse_reverse]
  refine ⟨s₃, n₁ + (1 + n₃), ?_, ?_, h₃₀, h₃buf, h₃k', h₃fr⟩
  · simp only [Lparse, seqs]
    exact Ev.seq he₁ (Ev.seq hpop he₃)
  · omega

/-! ## The main theorem -/

theorem asw_setup_gen_spec {main : HvdH.Cmd} (fp : HvdH.Cmd) (φ : HvdH.Glyph → HvdH.Glyph)
    (hfp : ∀ (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph),
      (g Work.IntLib.AddSub.rB = HvdH.Glyph.pos ∨ g Work.IntLib.AddSub.rB = HvdH.Glyph.neg) →
      ∃ s' n, Work.IntLib.AddSub.Ev main fp ⟨g, X⟩ s' n ∧ n ≤ 3 ∧ s'.stk = X ∧
        s'.reg Work.IntLib.AddSub.rB = φ (g Work.IntLib.AddSub.rB)) :
    ∀ (a b : ℤ) (R : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph)
      (X : HvdH.Stk → List HvdH.Glyph),
      X 0 = (HvdH.Val.int a).enc ++ (HvdH.Val.int b).enc ++ R →
      ∃ s' n, Work.IntLib.AddSub.Ev main (Work.IntLib.AddSub.asw_setup fp) ⟨g, X⟩ s' n ∧
        n ≤ 10 * (HvdH.isz a + HvdH.isz b) + 200 ∧
        s'.stk 0 = R ∧
        s'.stk Work.IntLib.AddSub.sA = (a.natAbs).bits.map HvdH.Glyph.bit ++
          Work.IntLib.AddSub.gmk Work.IntLib.AddSub.sA :: X Work.IntLib.AddSub.sA ∧
        s'.stk Work.IntLib.AddSub.sB = (b.natAbs).bits.map HvdH.Glyph.bit ++
          Work.IntLib.AddSub.gmk Work.IntLib.AddSub.sB :: X Work.IntLib.AddSub.sB ∧
        s'.stk Work.IntLib.AddSub.sSgA = (if a < 0 then HvdH.Glyph.neg else HvdH.Glyph.pos) ::
          Work.IntLib.AddSub.gmk Work.IntLib.AddSub.sSgA :: X Work.IntLib.AddSub.sSgA ∧
        s'.stk Work.IntLib.AddSub.sSgB =
          φ (if b < 0 then HvdH.Glyph.neg else HvdH.Glyph.pos) ::
          Work.IntLib.AddSub.gmk Work.IntLib.AddSub.sSgB :: X Work.IntLib.AddSub.sSgB ∧
        s'.stk Work.IntLib.AddSub.sBuf = Work.IntLib.AddSub.gmk Work.IntLib.AddSub.sBuf ::
          X Work.IntLib.AddSub.sBuf ∧
        s'.stk Work.IntLib.AddSub.sO1 = Work.IntLib.AddSub.gmk Work.IntLib.AddSub.sO1 ::
          X Work.IntLib.AddSub.sO1 ∧
        s'.stk Work.IntLib.AddSub.sO2 = Work.IntLib.AddSub.gmk Work.IntLib.AddSub.sO2 ::
          X Work.IntLib.AddSub.sO2 := by
  intro a b R g X hX
  have hEA : (Val.int a).enc = (if a < 0 then Glyph.neg else Glyph.pos) ::
      ((a.natAbs).bits.map Glyph.bit ++ [Glyph.iend]) := by
    rw [enc_int, encodeNat_eq_bits]
  have hEB : (Val.int b).enc = (if b < 0 then Glyph.neg else Glyph.pos) ::
      ((b.natAbs).bits.map Glyph.bit ++ [Glyph.iend]) := by
    rw [enc_int, encodeNat_eq_bits]
  -- step 1: push the seven markers
  obtain ⟨s₁, n₁, he₁, hn₁, h₁₀, h₁buf, h₁A, h₁B, h₁O1, h₁O2, h₁SA, h₁SB⟩ :=
    aswgen_Lmark_ev (main := main) g X
  -- step 2: sign of the first operand
  have hs₁₀ : s₁.stk 0 = (if a < 0 then Glyph.neg else Glyph.pos) ::
      ((a.natAbs).bits.map Glyph.bit ++ Glyph.iend :: ((Val.int b).enc ++ R)) := by
    rw [h₁₀, hX, hEA]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨s₂, n₂, he₂, hn₂, h₂₀, h₂SA, h₂fr⟩ :=
    aswgen_LsignA_ev (main := main) s₁.reg s₁.stk hs₁₀
  have h₂buf : s₂.stk sBuf = gmk sBuf :: X sBuf := by
    rw [h₂fr sBuf (by decide) (by decide), h₁buf]
  have h₂A : s₂.stk sA = gmk sA :: X sA := by
    rw [h₂fr sA (by decide) (by decide), h₁A]
  -- step 3: parse the magnitude of the first operand onto `sA`
  obtain ⟨s₃, n₃, he₃, hn₃, h₃₀, h₃buf, h₃A, h₃fr⟩ :=
    aswgen_parse_step (main := main) sA (by decide) (by decide) ((a.natAbs).bits)
      ((Val.int b).enc ++ R) (X sBuf) (X sA) s₂.reg s₂.stk h₂₀ h₂buf h₂A
  -- step 4: sign of the second operand through `fp`
  have hs₃₀ : s₃.stk 0 = (if b < 0 then Glyph.neg else Glyph.pos) ::
      ((b.natAbs).bits.map Glyph.bit ++ Glyph.iend :: R) := by
    rw [h₃₀, hEB]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hsgB : (if b < 0 then Glyph.neg else Glyph.pos) = Glyph.pos ∨
      (if b < 0 then Glyph.neg else Glyph.pos) = Glyph.neg := by
    by_cases hb : b < 0
    · right; simp [hb]
    · left; simp [hb]
  obtain ⟨s₄, n₄, he₄, hn₄, h₄₀, h₄SB, h₄fr⟩ :=
    aswgen_Lfp_ev (main := main) fp φ hfp s₃.reg s₃.stk hs₃₀ hsgB
  have h₄buf : s₄.stk sBuf = gmk sBuf :: X sBuf := by
    rw [h₄fr sBuf (by decide) (by decide), h₃buf]
  have h₄B : s₄.stk sB = gmk sB :: X sB := by
    rw [h₄fr sB (by decide) (by decide), h₃fr sB (by decide) (by decide) (by decide),
      h₂fr sB (by decide) (by decide), h₁B]
  -- step 5: parse the magnitude of the second operand onto `sB`
  obtain ⟨s₅, n₅, he₅, hn₅, h₅₀, h₅buf, h₅B, h₅fr⟩ :=
    aswgen_parse_step (main := main) sB (by decide) (by decide) ((b.natAbs).bits) R
      (X sBuf) (X sB) s₄.reg s₄.stk h₄₀ h₄buf h₄B
  -- read off the final state
  have hA₅ : s₅.stk sA = (a.natAbs).bits.map Glyph.bit ++ gmk sA :: X sA :=
    (h₅fr sA (by decide) (by decide) (by decide)).trans
      ((h₄fr sA (by decide) (by decide)).trans h₃A)
  have hSA₅ : s₅.stk sSgA = (if a < 0 then Glyph.neg else Glyph.pos) :: gmk sSgA :: X sSgA :=
    (h₅fr sSgA (by decide) (by decide) (by decide)).trans
      ((h₄fr sSgA (by decide) (by decide)).trans
        ((h₃fr sSgA (by decide) (by decide) (by decide)).trans
          (h₂SA.trans (congrArg (fun L => (if a < 0 then Glyph.neg else Glyph.pos) :: L) h₁SA))))
  have hSB₅ : s₅.stk sSgB = φ (if b < 0 then Glyph.neg else Glyph.pos) ::
      gmk sSgB :: X sSgB :=
    (h₅fr sSgB (by decide) (by decide) (by decide)).trans
      (h₄SB.trans (congrArg (fun L => φ (if b < 0 then Glyph.neg else Glyph.pos) :: L)
        ((h₃fr sSgB (by decide) (by decide) (by decide)).trans
          ((h₂fr sSgB (by decide) (by decide)).trans h₁SB))))
  have hO1₅ : s₅.stk sO1 = gmk sO1 :: X sO1 :=
    (h₅fr sO1 (by decide) (by decide) (by decide)).trans
      ((h₄fr sO1 (by decide) (by decide)).trans
        ((h₃fr sO1 (by decide) (by decide) (by decide)).trans
          ((h₂fr sO1 (by decide) (by decide)).trans h₁O1)))
  have hO2₅ : s₅.stk sO2 = gmk sO2 :: X sO2 :=
    (h₅fr sO2 (by decide) (by decide) (by decide)).trans
      ((h₄fr sO2 (by decide) (by decide)).trans
        ((h₃fr sO2 (by decide) (by decide) (by decide)).trans
          ((h₂fr sO2 (by decide) (by decide)).trans h₁O2)))
  -- glue the five chunks
  have hchain := aswgen_seqs_append
    (l₁ := Lmark) (l₂ := LsignA ++ (Lparse sA ++ (Lfp fp ++ Lparse sB))) he₁
    (aswgen_seqs_append (l₁ := LsignA) (l₂ := Lparse sA ++ (Lfp fp ++ Lparse sB)) he₂
      (aswgen_seqs_append (l₁ := Lparse sA) (l₂ := Lfp fp ++ Lparse sB) he₃
        (aswgen_seqs_append (l₁ := Lfp fp) (l₂ := Lparse sB) he₄ he₅)))
  have hprog : Ev main (asw_setup fp) ⟨g, X⟩ s₅ (n₁ + n₂ + n₃ + n₄ + n₅) := by
    rw [asw_setup_eq]
    exact hchain.mono (by omega)
  have hcost : n₁ + n₂ + n₃ + n₄ + n₅ ≤ 10 * (isz a + isz b) + 200 := by
    have hb₁ : ((a.natAbs).bits).length = a.natAbs.size := Nat.size_eq_bits_len a.natAbs
    have hb₂ : ((b.natAbs).bits).length = b.natAbs.size := Nat.size_eq_bits_len b.natAbs
    rw [isz_eq, isz_eq]
    omega
  exact ⟨s₅, n₁ + n₂ + n₃ + n₄ + n₅, hprog, hcost, h₅₀, hA₅, h₅B, hSA₅, hSB₅, h₅buf,
    hO1₅, hO2₅⟩

end Work.IntLib.AddSub
