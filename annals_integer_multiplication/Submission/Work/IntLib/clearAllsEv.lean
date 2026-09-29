import Mathlib
import Submission.Work.Layout.Base
import Submission.Work.IntLib.Shift.Base

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.IntLib

open HvdH

/-!
# Running `clearAll` on a list of disjoint stacks

`clearAll k r rF` discards everything on stack `k` down to (and including) the frame marker
`Shift.gmk k`.  Here we run these procedures sequentially over a list `l` of pairwise distinct
stacks: since `clearAll k` only ever touches stack `k`, the procedures do not interfere, and the
cost is the sum of the individual costs.

The auxiliary lemma below is the induction statement; the `+ 1` (rather than `+ 10`) slack accounts
for `seqs [] = .skip` costing one step.
-/

/-- Sequential clearing of a list `l` of stacks, with the initial content of each stack `k ∈ l`
written as `regs k ++ gmk k :: Z₀ k`. -/
theorem clearAllsEv_aux (main : Cmd) (r rF : Reg) :
    ∀ (l : List Stk) (X : Stk → List Glyph) (regs Z₀ : Stk → List Glyph) (g : Reg → Glyph),
      l.Nodup →
      (∀ k ∈ l, ∀ h ∈ regs k, h ≠ Shift.gmk k) →
      (∀ k ∈ l, X k = regs k ++ Shift.gmk k :: Z₀ k) →
      ∃ (s' : State) (n : ℕ),
        Work.Layout.Ev main (Work.Layout.seqs (l.map fun k => Shift.clearAll k r rF)) ⟨g, X⟩ s' n ∧
        n ≤ 5 * ((l.map fun k => (regs k).length).sum + l.length) + 4 * l.length + 1 ∧
        (∀ k, k ∈ l → s'.stk k = Z₀ k) ∧ (∀ k, k ∉ l → s'.stk k = X k) := by
  intro l
  induction l with
  | nil =>
      intro X regs Z₀ g _ _ _
      exact ⟨⟨g, X⟩, 1, ⟨1, Eval.skip _, le_rfl⟩, by simp, by simp, fun k _ => rfl⟩
  | cons k ks ih =>
      intro X regs Z₀ g hl hsafe hX
      obtain ⟨hnotin, hks⟩ := List.nodup_cons.mp hl
      have hmem : k ∈ k :: ks := List.mem_cons_self (l := ks)
      have hsafe_k := hsafe k hmem
      have hXk := hX k hmem
      obtain ⟨s1, n1, he1, hn1, hs1k, hs1o⟩ :=
        Shift.clearAll_ev (main := main) k r rF (regs k) (Z₀ k) g X hsafe_k hXk
      have he1' : Work.Layout.Ev main (Shift.clearAll k r rF) ⟨g, X⟩ s1 n1 :=
        ⟨n1, he1, le_rfl⟩
      obtain ⟨s2, n2, he2, hn2, hs2in, hs2out⟩ :=
        ih s1.stk regs Z₀ s1.reg hks
          (fun k' hk' => hsafe k' (List.mem_cons_of_mem k hk'))
          (fun k' hk' => by
            have hne : k' ≠ k := by rintro rfl; exact hnotin hk'
            rw [hs1o k' hne]
            exact hX k' (List.mem_cons_of_mem k hk'))
      have hseq : Work.Layout.Ev main
          (Work.Layout.seqs ((k :: ks).map fun k' => Shift.clearAll k' r rF)) ⟨g, X⟩ s2 (n1 + n2) := by
        rw [List.map_cons]
        exact Work.Layout.Ev.seqs_cons he1' he2
      refine ⟨s2, n1 + n2, hseq, ?_, ?_, ?_⟩
      · simp only [List.length_cons, List.map_cons, List.sum_cons]
        omega
      · intro k' hk'
        rcases List.mem_cons.mp hk' with heq | hk''
        · rw [heq]
          exact (hs2out k hnotin).trans hs1k
        · exact hs2in k' hk''
      · intro k' hk'
        have hk'' : k' ∉ ks := fun h => hk' (List.mem_cons_of_mem k h)
        have hne : k' ≠ k := by rintro rfl; exact hk' (List.mem_cons_self (l := ks))
        exact (hs2out k' hk'').trans (hs1o k' hne)

theorem clearAllsEv (main : HvdH.Cmd) (l : List HvdH.Stk) (r rF : HvdH.Reg)
    (Z Z₀ : HvdH.Stk → List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph)
    (regs : HvdH.Stk → List HvdH.Glyph) (hl : l.Nodup)
    (hsafe : ∀ k ∈ l, ∀ h ∈ regs k, h ≠ Work.IntLib.Shift.gmk k)
    (hZ : ∀ k ∈ l, Z k = regs k ++ Work.IntLib.Shift.gmk k :: Z₀ k) :
    ∃ (s' : HvdH.State) (n : ℕ),
      Work.Layout.Ev main (Work.Layout.seqs (l.map fun k => Work.IntLib.Shift.clearAll k r rF)) ⟨g, Z⟩ s' n ∧
      n ≤ 5 * ((l.map fun k => (regs k).length).sum + l.length) + 4 * l.length + 10 ∧
      (∀ k, k ∈ l → s'.stk k = Z₀ k) ∧ (∀ k, k ∉ l → s'.stk k = Z k) := by
  obtain ⟨s', n, he, hn, h1, h2⟩ := clearAllsEv_aux main r rF l Z regs Z₀ g hl hsafe hZ
  exact ⟨s', n, he, by omega, h1, h2⟩

end Work.IntLib
