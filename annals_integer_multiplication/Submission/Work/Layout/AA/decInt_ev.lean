import Mathlib
import Submission.Work.Layout.AA.Defs
import Submission.Work.Layout.AA.moveTo_ev
import Submission.Work.Layout.AA.copyIntB1_loop
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.encodeNatBridge

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Layout.AA

open HvdH

/-! # `decInt`: decrementing the integer counter on top of a stack -/

/-! ## 1. The bits of `n` and of `n - 1` -/

theorem natBits_decomp (n : ℕ) :
    1 ≤ n → ∃ tz : ℕ, ∃ rest : List Bool,
      n.bits = List.replicate tz false ++ true :: rest ∧
      (rest ≠ [] → rest.getLast? = some true) ∧
      (n - 1).bits = List.replicate tz true ++ (if rest = [] then [] else false :: rest) := by
  suffices h : ∀ k : ℕ, 1 ≤ k → ∃ tz : ℕ, ∃ rest : List Bool,
      k.bits = List.replicate tz false ++ true :: rest ∧
      (rest ≠ [] → rest.getLast? = some true) ∧
      (k - 1).bits = List.replicate tz true ++ (if rest = [] then [] else false :: rest) from h n
  intro k
  refine Nat.strong_induction_on k fun n ih hk => ?_
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hn2 : n = 2 * m := by omega
    have hm1 : 1 ≤ m := by omega
    obtain ⟨tz, rest, h1, h2, h3⟩ := ih m (by omega) hm1
    refine ⟨tz + 1, rest, ?_, h2, ?_⟩
    · simp only [hn2, Nat.bit0_bits m (by omega), h1, List.replicate_succ, List.cons_append]
    · have hsub : n - 1 = 2 * (m - 1) + 1 := by omega
      simp only [hsub, Nat.bit1_bits, h3, List.replicate_succ, List.cons_append]
  · have hn2 : n = 2 * m + 1 := by omega
    refine ⟨0, m.bits, ?_, ?_, ?_⟩
    · simp only [hn2, Nat.bit1_bits, List.replicate_zero, List.nil_append]
    · intro hne
      exact Work.IntLib.bits_getLast?_of_ne_zero (Work.IntLib.bits_ne_nil_iff.mp hne)
    · have hsub : n - 1 = 2 * m := by omega
      rw [hsub]
      by_cases hm0 : m = 0
      · subst hm0
        simp
      · simp only [Nat.bit0_bits m hm0, if_neg (Work.IntLib.bits_ne_nil_iff.mpr hm0),
          List.replicate_zero, List.nil_append, List.cons_append]

theorem enc_decomp (n : ℕ) (hn : 1 ≤ n) :
    ∃ tz : ℕ, ∃ rest : List Bool,
      Computability.encodeNat n = List.replicate tz false ++ true :: rest ∧
      (rest ≠ [] → rest.getLast? = some true) ∧
      Computability.encodeNat (n - 1) =
        List.replicate tz true ++ (if rest = [] then [] else false :: rest) := by
  obtain ⟨tz, rest, h1, h2, h3⟩ := natBits_decomp n hn
  exact ⟨tz, rest, by rw [Work.IntLib.encodeNat_eq_bits]; exact h1, h2,
    by rw [Work.IntLib.encodeNat_eq_bits]; exact h3⟩

/-! ## 2. Register bookkeeping -/

/-- The set of registers a program may *write*. -/
def cmdRegs : HvdH.Cmd → Finset HvdH.Reg
  | .skip => ∅
  | .pop _ r => {r}
  | .peek _ r => {r}
  | .push _ _ => ∅
  | .set r _ => {r}
  | .mov d _ => {d}
  | .seq c₁ c₂ => cmdRegs c₁ ∪ cmdRegs c₂
  | .ite _ _ c₁ c₂ => cmdRegs c₁ ∪ cmdRegs c₂
  | .loop _ _ c => cmdRegs c
  | .self => Finset.univ

theorem eval_reg_frame {main : HvdH.Cmd} {c : HvdH.Cmd} {s s' : HvdH.State} {n : ℕ}
    (hev : HvdH.Eval main c s s' n) {q : HvdH.Reg} (hr : q ∉ cmdRegs c) :
    s'.reg q = s.reg q := by
  induction hev with
  | skip s => rfl
  | pop k r s =>
      simp only [cmdRegs, Finset.mem_singleton] at hr
      exact Function.update_of_ne hr _ _
  | peek k r s =>
      simp only [cmdRegs, Finset.mem_singleton] at hr
      exact Function.update_of_ne hr _ _
  | push k r s => rfl
  | set r c s =>
      simp only [cmdRegs, Finset.mem_singleton] at hr
      exact Function.update_of_ne hr _ _
  | mov d src s =>
      simp only [cmdRegs, Finset.mem_singleton] at hr
      exact Function.update_of_ne hr _ _
  | seq h1 h2 ih1 ih2 =>
      simp only [cmdRegs, Finset.mem_union, not_or] at hr
      rw [ih2 hr.2, ih1 hr.1]
  | iteT hc hb ihb =>
      simp only [cmdRegs, Finset.mem_union, not_or] at hr
      exact ihb hr.1
  | iteF hc hb ihb =>
      simp only [cmdRegs, Finset.mem_union, not_or] at hr
      exact ihb hr.2
  | loopF hc => rfl
  | loopT hc h1 h2 ih1 ih2 =>
      simp only [cmdRegs] at hr
      rw [ih2 hr, ih1 hr]
  | self hb ihb => exact absurd (Finset.mem_univ _) hr

/-- Splitting the `Eval` of a sequenced command. -/
theorem Eval.seq_inv {main : HvdH.Cmd} {p q : HvdH.Cmd} {s s' : HvdH.State} {n : ℕ}
    (h : HvdH.Eval main (.seq p q) s s' n) :
    ∃ (t : HvdH.State) (n₁ n₂ : ℕ),
      HvdH.Eval main p s t n₁ ∧ HvdH.Eval main q t s' n₂ ∧ n₁ + n₂ = n := by
  cases h with
  | seq h₁ h₂ => exact ⟨_, _, _, h₁, h₂, rfl⟩

/-- The registers written by the body of `decInt` (everything after the leading `pop a rs`). -/
theorem cmdRegs_body (a t : HvdH.Stk) (rr rf rk rt : HvdH.Reg) :
    cmdRegs (seqs [.set rf HvdH.Glyph.cons,
      .loop rf HvdH.Glyph.cons (decB1 a t rr rf rk),
      .set rf HvdH.Glyph.cons,
      .loop rf HvdH.Glyph.cons (decB2 a t rr rf),
      .pop t rt, .peek t rr,
      .ite rr (HvdH.Glyph.bit false) (seqs [.pop t rr]) .skip,
      .push t rt,
      moveTo t a rr rf]) = {rr, rf, rk, rt} := by
  ext x
  simp only [seqs, cmdRegs, decB1, decB2, moveTo, moveToBody, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty, or_false, false_or]
  tauto

/-! ## 3. The phase-1 loop (`decB1`) -/

/-- One iteration of the `decB1` loop when the popped glyph is `bit false`. -/
theorem decB1_ev_false (main : HvdH.Cmd) {a t : HvdH.Stk} (hat : a ≠ t) (rr rf rk : HvdH.Reg)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) {C : List HvdH.Glyph}
    (ha : X a = HvdH.Glyph.bit false :: C) :
    ∃ s' n, Ev main (decB1 a t rr rf rk) ⟨g, X⟩ s' n ∧ n ≤ 5 ∧
      s'.stk a = C ∧ s'.stk t = HvdH.Glyph.bit true :: X t ∧ s'.reg rf = HvdH.Glyph.cons ∧
      (∀ j, j ≠ a → j ≠ t → s'.stk j = X j) := by
  have h1 : Ev main (.pop a rr) ⟨g, X⟩
      ⟨Function.update g rr (HvdH.Glyph.bit false), Function.update X a C⟩ 1 := by
    have h := ev_pop' main a rr g X
    rw [ha, List.headD_cons, List.tail_cons] at h
    exact h
  have h2a : Ev main (.set rk (HvdH.Glyph.bit true))
      ⟨Function.update g rr (HvdH.Glyph.bit false), Function.update X a C⟩
      ⟨Function.update (Function.update g rr (HvdH.Glyph.bit false)) rk
          (HvdH.Glyph.bit true), Function.update X a C⟩ 1 :=
    ev_set' main rk (HvdH.Glyph.bit true) _ _
  have h2b : Ev main (.push t rk)
      ⟨Function.update (Function.update g rr (HvdH.Glyph.bit false)) rk
          (HvdH.Glyph.bit true), Function.update X a C⟩
      ⟨Function.update (Function.update g rr (HvdH.Glyph.bit false)) rk (HvdH.Glyph.bit true),
        Function.update (Function.update X a C) t
          (HvdH.Glyph.bit true :: Function.update X a C t)⟩ 1 := by
    have h := ev_push' main t rk
      (Function.update (Function.update g rr (HvdH.Glyph.bit false)) rk (HvdH.Glyph.bit true))
      (Function.update X a C)
    simpa using h
  have h2c : Ev main (.set rf HvdH.Glyph.cons)
      ⟨Function.update (Function.update g rr (HvdH.Glyph.bit false)) rk
          (HvdH.Glyph.bit true),
        Function.update (Function.update X a C) t
          (HvdH.Glyph.bit true :: Function.update X a C t)⟩
      ⟨Function.update (Function.update (Function.update g rr (HvdH.Glyph.bit false)) rk
          (HvdH.Glyph.bit true)) rf HvdH.Glyph.cons,
        Function.update (Function.update X a C) t
          (HvdH.Glyph.bit true :: Function.update X a C t)⟩ 1 :=
    ev_set' main rf HvdH.Glyph.cons _ _
  have h2 : Ev main (seqs [.set rk (HvdH.Glyph.bit true), .push t rk, .set rf HvdH.Glyph.cons])
      ⟨Function.update g rr (HvdH.Glyph.bit false), Function.update X a C⟩
      ⟨Function.update (Function.update (Function.update g rr (HvdH.Glyph.bit false)) rk
          (HvdH.Glyph.bit true)) rf HvdH.Glyph.cons,
        Function.update (Function.update X a C) t
          (HvdH.Glyph.bit true :: Function.update X a C t)⟩ 3 :=
    Ev.seq h2a (Ev.seq h2b h2c)
  have h3 : Ev main (.ite rr (HvdH.Glyph.bit false)
      (seqs [.set rk (HvdH.Glyph.bit true), .push t rk, .set rf HvdH.Glyph.cons])
      (seqs [.set rk (HvdH.Glyph.bit false), .push t rk, .set rf HvdH.Glyph.eos]))
      ⟨Function.update g rr (HvdH.Glyph.bit false), Function.update X a C⟩
      ⟨Function.update (Function.update (Function.update g rr (HvdH.Glyph.bit false)) rk
          (HvdH.Glyph.bit true)) rf HvdH.Glyph.cons,
        Function.update (Function.update X a C) t
          (HvdH.Glyph.bit true :: Function.update X a C t)⟩ 4 :=
    Ev.iteT (by rw [reg_mk, Function.update_self]) h2
  have hbody : decB1 a t rr rf rk = .seq (.pop a rr)
      (.ite rr (HvdH.Glyph.bit false)
        (seqs [.set rk (HvdH.Glyph.bit true), .push t rk, .set rf HvdH.Glyph.cons])
        (seqs [.set rk (HvdH.Glyph.bit false), .push t rk, .set rf HvdH.Glyph.eos])) := rfl
  refine ⟨⟨Function.update (Function.update (Function.update g rr (HvdH.Glyph.bit false)) rk
      (HvdH.Glyph.bit true)) rf HvdH.Glyph.cons,
    Function.update (Function.update X a C) t
      (HvdH.Glyph.bit true :: Function.update X a C t)⟩, 5, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · exact Ev.seq h1 h3
  · rw [stk_mk, Function.update_of_ne hat, Function.update_self]
  · rw [stk_mk, Function.update_self, Function.update_of_ne (Ne.symm hat)]
  · rw [reg_mk, Function.update_self]
  · intro j hja hjt
    rw [stk_mk, Function.update_of_ne hjt, Function.update_of_ne hja]

/-- One iteration of the `decB1` loop when the popped glyph is `bit true`. -/
theorem decB1_ev_true (main : HvdH.Cmd) {a t : HvdH.Stk} (hat : a ≠ t) (rr rf rk : HvdH.Reg)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) {C : List HvdH.Glyph}
    (ha : X a = HvdH.Glyph.bit true :: C) :
    ∃ s' n, Ev main (decB1 a t rr rf rk) ⟨g, X⟩ s' n ∧ n ≤ 5 ∧
      s'.stk a = C ∧ s'.stk t = HvdH.Glyph.bit false :: X t ∧ s'.reg rf = HvdH.Glyph.eos ∧
      (∀ j, j ≠ a → j ≠ t → s'.stk j = X j) := by
  have h1 : Ev main (.pop a rr) ⟨g, X⟩
      ⟨Function.update g rr (HvdH.Glyph.bit true), Function.update X a C⟩ 1 := by
    have h := ev_pop' main a rr g X
    rw [ha, List.headD_cons, List.tail_cons] at h
    exact h
  have h2a : Ev main (.set rk (HvdH.Glyph.bit false))
      ⟨Function.update g rr (HvdH.Glyph.bit true), Function.update X a C⟩
      ⟨Function.update (Function.update g rr (HvdH.Glyph.bit true)) rk
          (HvdH.Glyph.bit false), Function.update X a C⟩ 1 :=
    ev_set' main rk (HvdH.Glyph.bit false) _ _
  have h2b : Ev main (.push t rk)
      ⟨Function.update (Function.update g rr (HvdH.Glyph.bit true)) rk
          (HvdH.Glyph.bit false), Function.update X a C⟩
      ⟨Function.update (Function.update g rr (HvdH.Glyph.bit true)) rk (HvdH.Glyph.bit false),
        Function.update (Function.update X a C) t
          (HvdH.Glyph.bit false :: Function.update X a C t)⟩ 1 := by
    have h := ev_push' main t rk
      (Function.update (Function.update g rr (HvdH.Glyph.bit true)) rk (HvdH.Glyph.bit false))
      (Function.update X a C)
    simpa using h
  have h2c : Ev main (.set rf HvdH.Glyph.eos)
      ⟨Function.update (Function.update g rr (HvdH.Glyph.bit true)) rk
          (HvdH.Glyph.bit false),
        Function.update (Function.update X a C) t
          (HvdH.Glyph.bit false :: Function.update X a C t)⟩
      ⟨Function.update (Function.update (Function.update g rr (HvdH.Glyph.bit true)) rk
          (HvdH.Glyph.bit false)) rf HvdH.Glyph.eos,
        Function.update (Function.update X a C) t
          (HvdH.Glyph.bit false :: Function.update X a C t)⟩ 1 :=
    ev_set' main rf HvdH.Glyph.eos _ _
  have h2 : Ev main (seqs [.set rk (HvdH.Glyph.bit false), .push t rk, .set rf HvdH.Glyph.eos])
      ⟨Function.update g rr (HvdH.Glyph.bit true), Function.update X a C⟩
      ⟨Function.update (Function.update (Function.update g rr (HvdH.Glyph.bit true)) rk
          (HvdH.Glyph.bit false)) rf HvdH.Glyph.eos,
        Function.update (Function.update X a C) t
          (HvdH.Glyph.bit false :: Function.update X a C t)⟩ 3 :=
    Ev.seq h2a (Ev.seq h2b h2c)
  have h3 : Ev main (.ite rr (HvdH.Glyph.bit false)
      (seqs [.set rk (HvdH.Glyph.bit true), .push t rk, .set rf HvdH.Glyph.cons])
      (seqs [.set rk (HvdH.Glyph.bit false), .push t rk, .set rf HvdH.Glyph.eos]))
      ⟨Function.update g rr (HvdH.Glyph.bit true), Function.update X a C⟩
      ⟨Function.update (Function.update (Function.update g rr (HvdH.Glyph.bit true)) rk
          (HvdH.Glyph.bit false)) rf HvdH.Glyph.eos,
        Function.update (Function.update X a C) t
          (HvdH.Glyph.bit false :: Function.update X a C t)⟩ 4 :=
    Ev.iteF (by rw [reg_mk, Function.update_self]; decide) h2
  have hbody : decB1 a t rr rf rk = .seq (.pop a rr)
      (.ite rr (HvdH.Glyph.bit false)
        (seqs [.set rk (HvdH.Glyph.bit true), .push t rk, .set rf HvdH.Glyph.cons])
        (seqs [.set rk (HvdH.Glyph.bit false), .push t rk, .set rf HvdH.Glyph.eos])) := rfl
  refine ⟨⟨Function.update (Function.update (Function.update g rr (HvdH.Glyph.bit true)) rk
      (HvdH.Glyph.bit false)) rf HvdH.Glyph.eos,
    Function.update (Function.update X a C) t
      (HvdH.Glyph.bit false :: Function.update X a C t)⟩, 5, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · exact Ev.seq h1 h3
  · rw [stk_mk, Function.update_of_ne hat, Function.update_self]
  · rw [stk_mk, Function.update_self, Function.update_of_ne (Ne.symm hat)]
  · rw [reg_mk, Function.update_self]
  · intro j hja hjt
    rw [stk_mk, Function.update_of_ne hjt, Function.update_of_ne hja]

/-- Auxiliary list identity for the loop invariant. -/
theorem rep_cons_swap (n : ℕ) (b : HvdH.Glyph) (C : List HvdH.Glyph) :
    List.replicate n b ++ (b :: C) = b :: (List.replicate n b ++ C) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    exact congrArg (fun L => b :: L) ih

/-- The `decB1` loop, `loopRuns` version. -/
theorem decB1_loop (main : HvdH.Cmd) (a t : HvdH.Stk) (rr rf rk : HvdH.Reg) (hat : a ≠ t) :
    ∀ (z : ℕ) (M : List Bool) (A C : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph)
      (X : HvdH.Stk → List HvdH.Glyph),
      g rf = HvdH.Glyph.cons →
      X a = (List.replicate z false ++ true :: M).map HvdH.Glyph.bit ++ HvdH.Glyph.iend :: A →
      X t = C →
      ∃ s', loopRuns main rf HvdH.Glyph.cons (decB1 a t rr rf rk) (z + 1) ⟨g, X⟩ s'
          (6 * (z + 1)) ∧
        s'.reg rf = HvdH.Glyph.eos ∧
        s'.stk a = M.map HvdH.Glyph.bit ++ HvdH.Glyph.iend :: A ∧
        s'.stk t = (HvdH.Glyph.bit false :: List.replicate z (HvdH.Glyph.bit true)) ++ C ∧
        (∀ j, j ≠ a → j ≠ t → s'.stk j = X j) := by
  intro z
  induction z with
  | zero =>
      intro M A C g X hg hX ht
      have hX' : X a = HvdH.Glyph.bit true ::
          (M.map HvdH.Glyph.bit ++ HvdH.Glyph.iend :: A) := by
        simpa using hX
      obtain ⟨s', n, hev, hn, ha', ht', hrf', hfr'⟩ :=
        decB1_ev_true (main := main) hat rr rf rk g X hX'
      refine ⟨s', ?_, hrf', ha', ?_, hfr'⟩
      · exact loopRuns.mono (le_refl 1) (loopRuns.one hg (hev.mono hn)) (by omega)
      · rw [ht']; simp [ht]
  | succ z ih =>
      intro M A C g X hg hX ht
      have hm : (List.replicate (z + 1) false ++ true :: M).map HvdH.Glyph.bit
          = HvdH.Glyph.bit false ::
            (List.replicate z false ++ true :: M).map HvdH.Glyph.bit := by
        rw [List.replicate_succ]
        simp only [List.map_append, List.map_cons, List.cons_append]
      have hX' : X a = HvdH.Glyph.bit false ::
          ((List.replicate z false ++ true :: M).map HvdH.Glyph.bit
            ++ HvdH.Glyph.iend :: A) := by
        rw [hX, hm]
        simp only [List.cons_append]
      obtain ⟨s₁, n₁, hev₁, hn₁, ha₁, ht₁, hr₁, hfr₁⟩ :=
        decB1_ev_false (main := main) hat rr rf rk g X hX'
      obtain ⟨s₂, hrun₂, hr₂, ha₂, ht₂, hfr₂⟩ :=
        ih M A (HvdH.Glyph.bit true :: C) s₁.reg s₁.stk hr₁ ha₁ (by rw [ht₁, ht])
      have hfin : (HvdH.Glyph.bit false :: List.replicate z (HvdH.Glyph.bit true)) ++
            (HvdH.Glyph.bit true :: C)
          = (HvdH.Glyph.bit false :: List.replicate (z + 1) (HvdH.Glyph.bit true)) ++ C := by
        rw [List.replicate_succ]
        exact congrArg (fun L => HvdH.Glyph.bit false :: L)
          (rep_cons_swap z (HvdH.Glyph.bit true) C)
      have hcat := loopRuns.concat (z + 1) (loopRuns.one hg (hev₁.mono hn₁)) hrun₂
      refine ⟨s₂, ?_, hr₂, ha₂, ?_, ?_⟩
      · refine loopRuns.congr (by omega) (by omega) hcat
      · rw [ht₂, hfin]
      · intro j hja hjt
        rw [hfr₂ j hja hjt, hfr₁ j hja hjt]

/-- The phase-1 loop of `decInt`: flip the low zero bits, then the first one. -/
theorem decB1_loopEv (main : HvdH.Cmd) (a t : HvdH.Stk) (rr rf rk : HvdH.Reg) (hat : a ≠ t)
    (z : ℕ) (M : List Bool) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (A C : List HvdH.Glyph) (hg : g rf = HvdH.Glyph.cons)
    (ha : X a = (List.replicate z false ++ true :: M).map HvdH.Glyph.bit
      ++ HvdH.Glyph.iend :: A) (ht : X t = C) :
    ∃ s' n, Ev main (.loop rf HvdH.Glyph.cons (decB1 a t rr rf rk)) ⟨g, X⟩ s' n ∧
      n ≤ 6 * (z + 1) + 1 ∧ s'.reg rf = HvdH.Glyph.eos ∧
      s'.stk a = M.map HvdH.Glyph.bit ++ HvdH.Glyph.iend :: A ∧
      s'.stk t = (HvdH.Glyph.bit false :: List.replicate z (HvdH.Glyph.bit true)) ++ C ∧
      (∀ j, j ≠ a → j ≠ t → s'.stk j = X j) := by
  obtain ⟨s', hrun, hr, ha', ht', hf⟩ := decB1_loop main a t rr rf rk hat z M A C g X hg ha ht
  exact ⟨s', 6 * (z + 1) + 1, loopRuns.eval hrun (by rw [hr]; decide), le_rfl, hr, ha', ht', hf⟩

/-! ## 4. The `iend` / `bit false` gadget -/

/-- `replicate n b ++ [b] = replicate (n+1) b`. -/
theorem replicate_append_singleton (n : ℕ) (b : HvdH.Glyph) :
    List.replicate n b ++ [b] = List.replicate (n + 1) b := by
  rw [rep_cons_swap n b [], List.append_nil, ← List.replicate_succ]

/-- `(replicate n true).reverse.map bit = replicate n (bit true)`. -/
theorem rev_map_replicate_true (n : ℕ) :
    (List.replicate n true).reverse.map HvdH.Glyph.bit =
      List.replicate n (HvdH.Glyph.bit true) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.reverse_cons, List.map_append, List.map_cons, List.map_nil, ih]
    exact replicate_append_singleton n (HvdH.Glyph.bit true)

/-- `(replicate tz true ++ false :: rest).reverse.map bit
= rest.reverse.map bit ++ [bit false] ++ replicate tz (bit true)`. -/
theorem rev_map_replicate_cons (tz : ℕ) (rest : List Bool) :
    (List.replicate tz true ++ (false :: rest)).reverse.map HvdH.Glyph.bit =
      rest.reverse.map HvdH.Glyph.bit ++ [HvdH.Glyph.bit false] ++
        List.replicate tz (HvdH.Glyph.bit true) := by
  rw [List.reverse_append, List.reverse_cons]
  simp only [List.map_append, List.map_cons, List.map_nil, rev_map_replicate_true,
    List.append_assoc]

/-- The gadget `pop t rt ;; peek t rr ;; ite rr (bit false) (pop t rr) skip ;; push t rt`:
it pops the `iend`, drops the following `bit false` exactly when `rest = []`, and pushes the `iend`
back. -/
theorem decIte_gadget (main : HvdH.Cmd) (t : HvdH.Stk) (rr rt : HvdH.Reg) (hrt : rr ≠ rt)
    (tz : ℕ) (rest : List Bool) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (DD : List HvdH.Glyph) (hrest : rest ≠ [] → rest.getLast? = some true)
    (ht : X t = HvdH.Glyph.iend :: rest.reverse.map HvdH.Glyph.bit ++ HvdH.Glyph.bit false ::
        List.replicate tz (HvdH.Glyph.bit true) ++ DD) :
    ∃ s' n, Ev main (seqs [.pop t rt, .peek t rr,
        .ite rr (HvdH.Glyph.bit false) (seqs [.pop t rr]) .skip, .push t rt])
        ⟨g, X⟩ s' n ∧ n ≤ 5 ∧
      s'.stk t = HvdH.Glyph.iend :: ((List.replicate tz true ++
        (if rest = [] then [] else false :: rest)).reverse.map HvdH.Glyph.bit) ++ DD ∧
      (∀ j, j ≠ t → s'.stk j = X j) := by
  rcases eq_or_ne rest [] with hre | hne
  · -- `rest = []`: the `bit false` is dropped
    subst hre
    have ht' : X t = HvdH.Glyph.iend :: (HvdH.Glyph.bit false ::
        (List.replicate tz (HvdH.Glyph.bit true) ++ DD)) := by simpa using ht
    have h1 : Ev main (.pop t rt) ⟨g, X⟩
        ⟨Function.update g rt HvdH.Glyph.iend,
          Function.update X t (HvdH.Glyph.bit false ::
            (List.replicate tz (HvdH.Glyph.bit true) ++ DD))⟩ 1 := by
      have h := ev_pop' main t rt g X
      rw [ht', List.headD_cons, List.tail_cons] at h
      exact h
    have h2 : Ev main (.peek t rr)
        ⟨Function.update g rt HvdH.Glyph.iend,
          Function.update X t (HvdH.Glyph.bit false ::
            (List.replicate tz (HvdH.Glyph.bit true) ++ DD))⟩
        ⟨Function.update (Function.update g rt HvdH.Glyph.iend) rr (HvdH.Glyph.bit false),
          Function.update X t (HvdH.Glyph.bit false ::
            (List.replicate tz (HvdH.Glyph.bit true) ++ DD))⟩ 1 := by
      have h := ev_peek' main t rr (Function.update g rt HvdH.Glyph.iend)
        (Function.update X t (HvdH.Glyph.bit false ::
          (List.replicate tz (HvdH.Glyph.bit true) ++ DD)))
      simpa using h
    have h3 : Ev main (.ite rr (HvdH.Glyph.bit false) (seqs [.pop t rr]) .skip)
        ⟨Function.update (Function.update g rt HvdH.Glyph.iend) rr (HvdH.Glyph.bit false),
          Function.update X t (HvdH.Glyph.bit false ::
            (List.replicate tz (HvdH.Glyph.bit true) ++ DD))⟩
        ⟨Function.update (Function.update (Function.update g rt HvdH.Glyph.iend) rr
            (HvdH.Glyph.bit false)) rr (HvdH.Glyph.bit false),
          Function.update (Function.update X t (HvdH.Glyph.bit false ::
            (List.replicate tz (HvdH.Glyph.bit true) ++ DD))) t
            (List.replicate tz (HvdH.Glyph.bit true) ++ DD)⟩ 2 := by
      refine Ev.iteT (by rw [reg_mk, Function.update_self]) ?_
      have h := ev_pop' main t rr
        (Function.update (Function.update g rt HvdH.Glyph.iend) rr (HvdH.Glyph.bit false))
        (Function.update X t (HvdH.Glyph.bit false ::
          (List.replicate tz (HvdH.Glyph.bit true) ++ DD)))
      simpa [seqs] using h
    have h4 : Ev main (.push t rt)
        ⟨Function.update (Function.update (Function.update g rt HvdH.Glyph.iend) rr
            (HvdH.Glyph.bit false)) rr (HvdH.Glyph.bit false),
          Function.update (Function.update X t (HvdH.Glyph.bit false ::
            (List.replicate tz (HvdH.Glyph.bit true) ++ DD))) t
            (List.replicate tz (HvdH.Glyph.bit true) ++ DD)⟩
        ⟨Function.update (Function.update (Function.update g rt HvdH.Glyph.iend) rr
            (HvdH.Glyph.bit false)) rr (HvdH.Glyph.bit false),
          Function.update (Function.update (Function.update X t (HvdH.Glyph.bit false ::
            (List.replicate tz (HvdH.Glyph.bit true) ++ DD))) t
            (List.replicate tz (HvdH.Glyph.bit true) ++ DD)) t
            (HvdH.Glyph.iend :: (List.replicate tz (HvdH.Glyph.bit true) ++ DD))⟩ 1 := by
      have h := ev_push' main t rt
        (Function.update (Function.update (Function.update g rt HvdH.Glyph.iend) rr
            (HvdH.Glyph.bit false)) rr (HvdH.Glyph.bit false))
        (Function.update (Function.update X t (HvdH.Glyph.bit false ::
            (List.replicate tz (HvdH.Glyph.bit true) ++ DD))) t
            (List.replicate tz (HvdH.Glyph.bit true) ++ DD))
      simpa [Function.update_of_ne (Ne.symm hrt), Function.update_self] using h
    have hbody : Ev main (seqs [.pop t rt, .peek t rr,
        .ite rr (HvdH.Glyph.bit false) (seqs [.pop t rr]) .skip, .push t rt]) ⟨g, X⟩
        ⟨Function.update (Function.update (Function.update g rt HvdH.Glyph.iend) rr
            (HvdH.Glyph.bit false)) rr (HvdH.Glyph.bit false),
          Function.update (Function.update (Function.update X t (HvdH.Glyph.bit false ::
            (List.replicate tz (HvdH.Glyph.bit true) ++ DD))) t
            (List.replicate tz (HvdH.Glyph.bit true) ++ DD)) t
            (HvdH.Glyph.iend :: (List.replicate tz (HvdH.Glyph.bit true) ++ DD))⟩ 5 := by
      have hprog : seqs [.pop t rt, .peek t rr,
          .ite rr (HvdH.Glyph.bit false) (seqs [.pop t rr]) .skip, .push t rt]
          = .seq (.pop t rt) (.seq (.peek t rr)
              (.seq (.ite rr (HvdH.Glyph.bit false) (seqs [.pop t rr]) .skip)
                (.push t rt))) := rfl
      rw [hprog]
      exact Ev.seq h1 (Ev.seq h2 (Ev.seq h3 h4))
    refine ⟨_, 5, hbody, by omega, ?_, ?_⟩
    · simp [rev_map_replicate_true]
    · intro j hj
      simp [hj]
  · -- `rest ≠ []`: the `bit false` stays
    have hlast : rest.getLast? = some true := hrest hne
    obtain ⟨B, hB⟩ : ∃ B, rest.reverse.map HvdH.Glyph.bit = HvdH.Glyph.bit true :: B := by
      have h1 : rest.reverse.head? = some true := by
        rw [List.head?_reverse]; exact hlast
      cases hr : rest.reverse with
      | nil => rw [hr] at h1; exact absurd h1 (by decide)
      | cons x l =>
        have hx : x = true := by
          have h2 : (x :: l).head? = some x := rfl
          rw [hr, h2] at h1
          exact Option.some.inj h1
        subst hx
        exact ⟨l.map HvdH.Glyph.bit, by simp⟩
    have ht' : X t = HvdH.Glyph.iend :: (HvdH.Glyph.bit true ::
        (B ++ (HvdH.Glyph.bit false :: List.replicate tz (HvdH.Glyph.bit true) ++ DD))) := by
      rw [ht, hB]
      simp only [List.cons_append, List.append_assoc]
    have h1 : Ev main (.pop t rt) ⟨g, X⟩
        ⟨Function.update g rt HvdH.Glyph.iend,
          Function.update X t (HvdH.Glyph.bit true ::
            (B ++ (HvdH.Glyph.bit false :: List.replicate tz (HvdH.Glyph.bit true) ++ DD)))⟩ 1 := by
      have h := ev_pop' main t rt g X
      rw [ht', List.headD_cons, List.tail_cons] at h
      exact h
    have h2 : Ev main (.peek t rr)
        ⟨Function.update g rt HvdH.Glyph.iend,
          Function.update X t (HvdH.Glyph.bit true ::
            (B ++ (HvdH.Glyph.bit false :: List.replicate tz (HvdH.Glyph.bit true) ++ DD)))⟩
        ⟨Function.update (Function.update g rt HvdH.Glyph.iend) rr (HvdH.Glyph.bit true),
          Function.update X t (HvdH.Glyph.bit true ::
            (B ++ (HvdH.Glyph.bit false :: List.replicate tz (HvdH.Glyph.bit true) ++ DD)))⟩ 1 := by
      have h := ev_peek' main t rr (Function.update g rt HvdH.Glyph.iend)
        (Function.update X t (HvdH.Glyph.bit true ::
          (B ++ (HvdH.Glyph.bit false :: List.replicate tz (HvdH.Glyph.bit true) ++ DD))))
      simpa using h
    have h3 : Ev main (.ite rr (HvdH.Glyph.bit false) (seqs [.pop t rr]) .skip)
        ⟨Function.update (Function.update g rt HvdH.Glyph.iend) rr (HvdH.Glyph.bit true),
          Function.update X t (HvdH.Glyph.bit true ::
            (B ++ (HvdH.Glyph.bit false :: List.replicate tz (HvdH.Glyph.bit true) ++ DD)))⟩
        ⟨Function.update (Function.update g rt HvdH.Glyph.iend) rr (HvdH.Glyph.bit true),
          Function.update X t (HvdH.Glyph.bit true ::
            (B ++ (HvdH.Glyph.bit false :: List.replicate tz (HvdH.Glyph.bit true) ++ DD)))⟩ 2 := by
      refine Ev.iteF ?_ ?_
      · rw [reg_mk, Function.update_self]; decide
      · exact ev_skip' main _ _
    have h4 : Ev main (.push t rt)
        ⟨Function.update (Function.update g rt HvdH.Glyph.iend) rr (HvdH.Glyph.bit true),
          Function.update X t (HvdH.Glyph.bit true ::
            (B ++ (HvdH.Glyph.bit false :: List.replicate tz (HvdH.Glyph.bit true) ++ DD)))⟩
        ⟨Function.update (Function.update g rt HvdH.Glyph.iend) rr (HvdH.Glyph.bit true),
          Function.update (Function.update X t (HvdH.Glyph.bit true ::
            (B ++ (HvdH.Glyph.bit false :: List.replicate tz (HvdH.Glyph.bit true) ++ DD)))) t
            (HvdH.Glyph.iend :: Function.update X t (HvdH.Glyph.bit true ::
              (B ++ (HvdH.Glyph.bit false :: List.replicate tz (HvdH.Glyph.bit true) ++ DD))) t)⟩ 1 := by
      have h := ev_push' main t rt
        (Function.update (Function.update g rt HvdH.Glyph.iend) rr (HvdH.Glyph.bit true))
        (Function.update X t (HvdH.Glyph.bit true ::
          (B ++ (HvdH.Glyph.bit false :: List.replicate tz (HvdH.Glyph.bit true) ++ DD))))
      simpa [Function.update_of_ne (Ne.symm hrt), Function.update_self] using h
    have hbody : Ev main (seqs [.pop t rt, .peek t rr,
        .ite rr (HvdH.Glyph.bit false) (seqs [.pop t rr]) .skip, .push t rt]) ⟨g, X⟩
        ⟨Function.update (Function.update g rt HvdH.Glyph.iend) rr (HvdH.Glyph.bit true),
          Function.update (Function.update X t (HvdH.Glyph.bit true ::
            (B ++ (HvdH.Glyph.bit false :: List.replicate tz (HvdH.Glyph.bit true) ++ DD)))) t
            (HvdH.Glyph.iend :: Function.update X t (HvdH.Glyph.bit true ::
              (B ++ (HvdH.Glyph.bit false :: List.replicate tz (HvdH.Glyph.bit true) ++ DD))) t)⟩ 5 := by
      have hprog : seqs [.pop t rt, .peek t rr,
          .ite rr (HvdH.Glyph.bit false) (seqs [.pop t rr]) .skip, .push t rt]
          = .seq (.pop t rt) (.seq (.peek t rr)
              (.seq (.ite rr (HvdH.Glyph.bit false) (seqs [.pop t rr]) .skip)
                (.push t rt))) := rfl
      rw [hprog]
      exact Ev.seq h1 (Ev.seq h2 (Ev.seq h3 h4))
    refine ⟨_, 5, hbody, by omega, ?_, ?_⟩
    · rw [if_neg hne, rev_map_replicate_cons, hB]
      simp only [Function.update_self, List.cons_append, List.append_assoc,
        List.nil_append, List.append_nil]
    · intro j hj
      simp [Function.update_of_ne hj]

/-! ## 5. The encoding of a nonnegative integer -/

theorem enc_int_ofNat (m : ℕ) :
    (HvdH.Val.int ((m : ℕ) : ℤ)).enc = HvdH.Glyph.pos ::
      ((Computability.encodeNat m).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend]) := by
  simp [HvdH.Val.enc]

theorem enc_int_ofNat_append (m : ℕ) (A : List HvdH.Glyph) :
    (HvdH.Val.int ((m : ℕ) : ℤ)).enc ++ A = HvdH.Glyph.pos ::
      ((Computability.encodeNat m).map HvdH.Glyph.bit ++ HvdH.Glyph.iend :: A) := by
  rw [enc_int_ofNat m]
  simp only [List.cons_append, List.append_assoc, List.singleton_append,
    List.nil_append]

/-! ## 6. `decInt` -/

theorem decInt_ev (main : HvdH.Cmd) (a t : HvdH.Stk) (rr rf rk rs rt : HvdH.Reg)
    (hat : a ≠ t)
    (h1 : rr ≠ rf) (h2 : rr ≠ rk) (h3 : rr ≠ rs) (h4 : rr ≠ rt) (h5 : rf ≠ rk)
    (h6 : rf ≠ rs) (h7 : rf ≠ rt) (h8 : rk ≠ rs) (h9 : rk ≠ rt) (h10 : rs ≠ rt)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (k : ℕ)
    (A DB : List HvdH.Glyph) (hD : HvdH.Glyph.mk 7 ∉ DB)
    (ha : X a = (HvdH.Val.int (k+1)).enc ++ A) (ht : X t = HvdH.Glyph.mk 7 :: DB) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.decInt a t rr rf rk rs rt) ⟨g, X⟩ s' n ∧
      n ≤ 40 * (HvdH.isz (k+1) + 1) ∧
      s'.stk a = (HvdH.Val.int k).enc ++ A ∧ s'.stk t = HvdH.Glyph.mk 7 :: DB ∧
      (∀ j, j ≠ a → j ≠ t → s'.stk j = X j) := by
  -- 1. the bits of `k+1`
  obtain ⟨tz, rest, hL, hrest, hsub⟩ := enc_decomp (k + 1) (by omega)
  have hk1 : (k + 1) - 1 = k := by omega
  have hT : List.replicate tz true ++ (if rest = [] then [] else false :: rest) =
      Computability.encodeNat k := by rw [← hsub, hk1]
  -- 2. length bookkeeping
  have hSz : tz + rest.length + 1 = (k + 1).size := by
    have hlen : (Computability.encodeNat (k + 1)).length = tz + 1 + rest.length := by
      rw [hL]
      simp only [List.length_append, List.length_replicate, List.length_cons]
      omega
    rw [Work.IntLib.encodeNat_length] at hlen
    omega
  have hisz : HvdH.isz ((k + 1 : ℕ) : ℤ) = (k + 1).size + 2 := by
    rw [HvdH.isz, Int.natAbs_natCast]
  -- 3. the encoding of `k+1` begins with the sign `pos`
  have ha' : X a = HvdH.Glyph.pos :: ((Computability.encodeNat (k+1)).map HvdH.Glyph.bit
      ++ HvdH.Glyph.iend :: A) := by
    rw [ha]
    exact enc_int_ofNat_append (k+1) A
  -- 4. the leading `pop a rs` (reads the sign) and the first `set rf cons`
  have hpop : Ev main (.pop a rs) ⟨g, X⟩
      ⟨Function.update g rs HvdH.Glyph.pos,
        Function.update X a ((Computability.encodeNat (k+1)).map HvdH.Glyph.bit
          ++ HvdH.Glyph.iend :: A)⟩ 1 := by
    have h := ev_pop' main a rs g X
    rw [ha', List.headD_cons, List.tail_cons] at h
    exact h
  have hset1 : Ev main (.set rf HvdH.Glyph.cons)
      ⟨Function.update g rs HvdH.Glyph.pos,
        Function.update X a ((Computability.encodeNat (k+1)).map HvdH.Glyph.bit
          ++ HvdH.Glyph.iend :: A)⟩
      ⟨Function.update (Function.update g rs HvdH.Glyph.pos) rf HvdH.Glyph.cons,
        Function.update X a ((Computability.encodeNat (k+1)).map HvdH.Glyph.bit
          ++ HvdH.Glyph.iend :: A)⟩ 1 :=
    ev_set' main rf HvdH.Glyph.cons _ _
  -- 5. phase 1
  obtain ⟨s2, n2, hloop1, hn2, hr2, ha2, ht2, hf2⟩ :=
    decB1_loopEv main a t rr rf rk hat tz rest
      (Function.update (Function.update g rs HvdH.Glyph.pos) rf HvdH.Glyph.cons)
      (Function.update X a ((Computability.encodeNat (k+1)).map HvdH.Glyph.bit
        ++ HvdH.Glyph.iend :: A))
      A (HvdH.Glyph.mk 7 :: DB)
      (by simp)
      (by rw [Function.update_self, hL])
      (by rw [Function.update_of_ne (Ne.symm hat), ht])
  have hset2 : Ev main (.set rf HvdH.Glyph.cons) s2
      ⟨Function.update s2.reg rf HvdH.Glyph.cons, s2.stk⟩ 1 :=
    ev_set' main rf HvdH.Glyph.cons s2.reg s2.stk
  -- 6. phase 2 (`decB2` is `copyIntB1`)
  have hdecB2 : Work.Layout.decB2 a t rr rf = Work.Layout.copyIntB1 a t rr rf := rfl
  obtain ⟨s4, hrun4, ha4, ht4, hf4, hr4⟩ :=
    copyIntB1_loop main hat rr rf (rest.map HvdH.Glyph.bit) A
      (Function.update s2.reg rf HvdH.Glyph.cons) s2.stk
      (by
        intro hmem
        obtain ⟨b, _, hb⟩ := List.mem_map.mp hmem
        cases b <;> exact absurd hb (by decide))
      (by simp)
      (by simpa using ha2)
  have hloop2ev : Ev main (.loop rf HvdH.Glyph.cons (Work.Layout.decB2 a t rr rf))
      ⟨Function.update s2.reg rf HvdH.Glyph.cons, s2.stk⟩ s4 (5 * (rest.length + 1) + 1) := by
    have h := loopRuns.eval hrun4 (by rw [hr4]; decide)
    rw [← hdecB2] at h
    simpa [List.length_map] using h
  -- 7. the gadget
  obtain ⟨s5, n5, hgadget, hn5, ht5, hf5⟩ :=
    decIte_gadget main t rr rt h4 tz rest s4.reg s4.stk (HvdH.Glyph.mk 7 :: DB) hrest (by
      rw [ht4, ht2, ← List.map_reverse]
      simp only [List.cons_append, List.append_assoc])
  obtain ⟨n5', hev5blk, hn5'⟩ := hgadget
  obtain ⟨sa, m1, m2, hev6, hev789, hm12⟩ := Eval.seq_inv hev5blk
  obtain ⟨sb, m3, m4, hev7, hev89, hm34⟩ := Eval.seq_inv hev789
  obtain ⟨sc, m5, m6, hev8, hev9, hm56⟩ := Eval.seq_inv hev89
  -- 8. `moveTo`
  set D : List HvdH.Glyph := HvdH.Glyph.iend ::
    (List.replicate tz true ++ (if rest = [] then [] else false :: rest)).reverse.map HvdH.Glyph.bit
    with hDdef
  have hDmem : HvdH.Glyph.mk 7 ∉ D := by
    rw [hDdef]
    intro hmem
    rcases List.mem_cons.mp hmem with hmem' | hmem'
    · exact absurd hmem' (by decide)
    · obtain ⟨b, _, hb⟩ := List.mem_map.mp hmem'
      cases b <;> exact absurd hb (by decide)
  have hDlen : D.length ≤ (k + 1).size + 1 := by
    rw [hDdef]
    have hTlen : (List.replicate tz true
        ++ (if rest = [] then [] else false :: rest)).length ≤ tz + rest.length + 1 := by
      by_cases hre : rest = []
      · subst hre
        simp
      · rw [if_neg hre]
        simp only [List.length_append, List.length_replicate, List.length_cons]
        omega
    simp only [List.length_cons, List.length_map, List.length_reverse]
    omega
  obtain ⟨s6, n6, hmove, hn6, ht6, ha6, hf6⟩ :=
    moveTo_ev main t a rr rf h1 (Ne.symm hat) s5.reg s5.stk D DB hDmem
      (by rw [hDdef]; exact ht5)
  -- 9. the register `rs` survives the body
  have hmid : Ev main (seqs [.set rf HvdH.Glyph.cons,
      .loop rf HvdH.Glyph.cons (decB1 a t rr rf rk),
      .set rf HvdH.Glyph.cons,
      .loop rf HvdH.Glyph.cons (decB2 a t rr rf),
      .pop t rt, .peek t rr,
      .ite rr (HvdH.Glyph.bit false) (seqs [.pop t rr]) .skip,
      .push t rt,
      moveTo t a rr rf])
      ⟨Function.update g rs HvdH.Glyph.pos,
        Function.update X a ((Computability.encodeNat (k+1)).map HvdH.Glyph.bit
          ++ HvdH.Glyph.iend :: A)⟩ s6
      (40 * (HvdH.isz ((k+1:ℕ):ℤ) + 1)) := by
    have hprog : seqs [.set rf HvdH.Glyph.cons,
        .loop rf HvdH.Glyph.cons (decB1 a t rr rf rk),
        .set rf HvdH.Glyph.cons,
        .loop rf HvdH.Glyph.cons (decB2 a t rr rf),
        .pop t rt, .peek t rr,
        .ite rr (HvdH.Glyph.bit false) (seqs [.pop t rr]) .skip,
        .push t rt,
        moveTo t a rr rf]
        = .seq (.set rf HvdH.Glyph.cons)
            (.seq (.loop rf HvdH.Glyph.cons (decB1 a t rr rf rk))
              (.seq (.set rf HvdH.Glyph.cons)
                (.seq (.loop rf HvdH.Glyph.cons (decB2 a t rr rf))
                  (.seq (.pop t rt)
                    (.seq (.peek t rr)
                      (.seq (.ite rr (HvdH.Glyph.bit false) (seqs [.pop t rr]) .skip)
                        (.seq (.push t rt) (moveTo t a rr rf)))))))) := rfl
    have hnat : Ev main (seqs [.set rf HvdH.Glyph.cons,
        .loop rf HvdH.Glyph.cons (decB1 a t rr rf rk),
        .set rf HvdH.Glyph.cons,
        .loop rf HvdH.Glyph.cons (decB2 a t rr rf),
        .pop t rt, .peek t rr,
        .ite rr (HvdH.Glyph.bit false) (seqs [.pop t rr]) .skip,
        .push t rt,
        moveTo t a rr rf])
        ⟨Function.update g rs HvdH.Glyph.pos,
          Function.update X a ((Computability.encodeNat (k+1)).map HvdH.Glyph.bit
            ++ HvdH.Glyph.iend :: A)⟩ s6
        (1 + ((6*(tz+1)+1) + (1 + ((5*(rest.length+1)+1)
          + (m1 + (m3 + (m5 + (m6 + (6*D.length+8))))))))) := by
      rw [hprog]
      exact Ev.seq hset1 (Ev.seq (hloop1.mono hn2) (Ev.seq hset2 (Ev.seq hloop2ev
        (Ev.seq ⟨m1, hev6, le_rfl⟩ (Ev.seq ⟨m3, hev7, le_rfl⟩
          (Ev.seq ⟨m5, hev8, le_rfl⟩ (Ev.seq ⟨m6, hev9, le_rfl⟩
            (hmove.mono hn6))))))))
    exact hnat.mono (by omega)
  have hrs_notin : rs ∉ cmdRegs (seqs [.set rf HvdH.Glyph.cons,
      .loop rf HvdH.Glyph.cons (decB1 a t rr rf rk),
      .set rf HvdH.Glyph.cons,
      .loop rf HvdH.Glyph.cons (decB2 a t rr rf),
      .pop t rt, .peek t rr,
      .ite rr (HvdH.Glyph.bit false) (seqs [.pop t rr]) .skip,
      .push t rt,
      moveTo t a rr rf]) := by
    rw [cmdRegs_body]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h3.symm, h6.symm, h8.symm, h10⟩
  have hrs6 : s6.reg rs = HvdH.Glyph.pos := by
    obtain ⟨nm, hevalm, _⟩ := hmid
    have hfr := eval_reg_frame hevalm hrs_notin
    simpa using hfr
  -- 10. the final `push a rs`
  have hpush : Ev main (.push a rs) s6
      ⟨s6.reg, Function.update s6.stk a (s6.reg rs :: s6.stk a)⟩ 1 :=
    ev_push' main a rs s6.reg s6.stk
  -- 11. the whole program
  have hwhole : Ev main (Work.Layout.decInt a t rr rf rk rs rt) ⟨g, X⟩
      ⟨s6.reg, Function.update s6.stk a (s6.reg rs :: s6.stk a)⟩
      (40 * (HvdH.isz ((k+1:ℕ):ℤ) + 1)) := by
    have hprog : Work.Layout.decInt a t rr rf rk rs rt
        = .seq (.pop a rs)
            (.seq (.set rf HvdH.Glyph.cons)
              (.seq (.loop rf HvdH.Glyph.cons (decB1 a t rr rf rk))
                (.seq (.set rf HvdH.Glyph.cons)
                  (.seq (.loop rf HvdH.Glyph.cons (decB2 a t rr rf))
                    (.seq (.pop t rt)
                      (.seq (.peek t rr)
                        (.seq (.ite rr (HvdH.Glyph.bit false) (seqs [.pop t rr]) .skip)
                          (.seq (.push t rt)
                            (.seq (moveTo t a rr rf) (.push a rs)))))))))) := rfl
    have hnat : Ev main (Work.Layout.decInt a t rr rf rk rs rt) ⟨g, X⟩
        ⟨s6.reg, Function.update s6.stk a (s6.reg rs :: s6.stk a)⟩
        (1 + (1 + ((6*(tz+1)+1) + (1 + ((5*(rest.length+1)+1)
          + (m1 + (m3 + (m5 + (m6 + ((6*D.length+8) + 1)))))))))) := by
      rw [hprog]
      exact Ev.seq hpop (Ev.seq hset1 (Ev.seq (hloop1.mono hn2) (Ev.seq hset2
        (Ev.seq hloop2ev (Ev.seq ⟨m1, hev6, le_rfl⟩ (Ev.seq ⟨m3, hev7, le_rfl⟩
          (Ev.seq ⟨m5, hev8, le_rfl⟩ (Ev.seq ⟨m6, hev9, le_rfl⟩
            (Ev.seq (hmove.mono hn6) hpush)))))))))
    exact hnat.mono (by omega)
  -- 12. conclusions
  have hDrev : D.reverse = (List.replicate tz true ++
      (if rest = [] then [] else false :: rest)).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] := by
    rw [hDdef, List.reverse_cons, ← List.map_reverse, List.reverse_reverse]
  have hs5a : s5.stk a = A := by rw [hf5 a hat, ha4]
  have hs6a : s6.stk a = D.reverse ++ A := by rw [ha6, hs5a]
  refine ⟨⟨s6.reg, Function.update s6.stk a (s6.reg rs :: s6.stk a)⟩,
    40 * (HvdH.isz ((k+1:ℕ):ℤ) + 1), hwhole, le_rfl, ?_, ?_, ?_⟩
  · rw [stk_mk, Function.update_self, hrs6, hs6a, hDrev, hT]
    simp [HvdH.Val.enc, List.cons_append, List.singleton_append, List.append_assoc]
  · rw [stk_mk, Function.update_of_ne (Ne.symm hat)]
    exact ht6
  · intro j hja hjt
    rw [stk_mk, Function.update_of_ne hja, hf6 j hjt hja, hf5 j hjt, hf4 j hja hjt,
      hf2 j hja hjt]
    exact Function.update_of_ne hja _ _

end Work.Layout.AA
