import Submission.Work.IntLib.Shift.Base
import Submission.Work.IntLib.encodeNatBridge

/-!
# IntLib: the **exact** cost of `Shift.drain`, and determinism of `HvdH.Eval`

`Shift.drain_ev` (in `Submission/Work/IntLib/Shift/Base.lean`) gives the upper bound

```
Eval main (Shift.drain a b T r rF) ⟨g, X⟩ s' n  →  n ≤ 5 * (G.length + 1) + 2
```

for a run that moves the region `G` above the marker `T` of stack `a` onto stack `b`.  That bound is
**tight**, and this file proves the exact statement: *every* such derivation has cost
`5 * G.length + 7`, and a run of that cost exists.  (The cost is 1 for the initial `set`, then
`5 * L + 6` for the loop: `L + 1` bodies of 4 steps, `L + 1` successful tests and 1 failing test.)

This is used e.g. in `Submission/Work/IntLib/preMainPhase_refute.lean`: the pre-phase of the
`chunk` word performs two `drain`s of the `x`-encoding, so a cost bound that only accounts for one
of them is provably too small.

`Eval.det` (determinism of the operational semantics) is also proved here.  It is already proved in
`Submission/Work/IntLib/SqrtGcd/subLoopEval_refute.lean`, but *that* module cannot be imported
together with `Submission/Work/IntLib/chunkProg.lean`: both trees declare `Work.IntLib.rB`, so Lean
rejects the combination.  Hence the (short) duplication.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Work.IntLib

open HvdH

/-! ## Determinism of `HvdH.Eval` -/

/-- `HvdH.Eval` is deterministic: a command has at most one outcome (state and cost). -/
theorem Eval.det {main : Cmd} : ∀ {c : Cmd} {s s₁ : State} {n₁ : ℕ}, Eval main c s s₁ n₁ →
    ∀ {s₂ : State} {n₂ : ℕ}, Eval main c s s₂ n₂ → s₁ = s₂ ∧ n₁ = n₂ := by
  intro c s s₁ n₁ h
  induction h with
  | skip => intro s₂ n₂ h2; cases h2; exact ⟨rfl, rfl⟩
  | pop k r => intro s₂ n₂ h2; cases h2; exact ⟨rfl, rfl⟩
  | peek k r => intro s₂ n₂ h2; cases h2; exact ⟨rfl, rfl⟩
  | push k r => intro s₂ n₂ h2; cases h2; exact ⟨rfl, rfl⟩
  | set r cc => intro s₂ n₂ h2; cases h2; exact ⟨rfl, rfl⟩
  | mov d sr => intro s₂ n₂ h2; cases h2; exact ⟨rfl, rfl⟩
  | seq h1 h2 ih1 ih2 =>
      intro s₃ n₃ h3
      cases h3 with
      | seq g1 g2 =>
        obtain ⟨e1, d1⟩ := ih1 g1
        rw [← e1] at g2
        obtain ⟨e2, d2⟩ := ih2 g2
        exact ⟨e2, by omega⟩
  | iteT hr h1 ih1 =>
      intro s₂ n₂ h2
      cases h2 with
      | iteT _ g =>
        obtain ⟨e, d⟩ := ih1 g
        rw [e]
        exact ⟨rfl, by omega⟩
      | iteF hne _ => exact absurd hr hne
  | iteF hr h1 ih1 =>
      intro s₂ n₂ h2
      cases h2 with
      | iteT hc _ => exact absurd hc hr
      | iteF _ g =>
        obtain ⟨e, d⟩ := ih1 g
        rw [e]
        exact ⟨rfl, by omega⟩
  | loopF hne =>
      intro s₂ n₂ h2
      cases h2 with
      | loopF _ => exact ⟨rfl, rfl⟩
      | loopT hr _ _ => exact absurd hr hne
  | loopT hr hb htl ihb ihtl =>
      intro s₃ n₃ h3
      cases h3 with
      | loopF hne => exact absurd hr hne
      | loopT _ gb gtl =>
        obtain ⟨e1, d1⟩ := ihb gb
        rw [← e1] at gtl
        obtain ⟨e2, d2⟩ := ihtl gtl
        exact ⟨e2, by omega⟩
  | self h1 ih1 =>
      intro s₂ n₂ h2
      cases h2 with
      | self g =>
        obtain ⟨e, d⟩ := ih1 g
        rw [e]
        exact ⟨rfl, by omega⟩

/-! ## Exact cost of `Shift.drain` -/

/-- exact cost of `Shift.drainBody`, "go" case (the popped glyph is not the marker): 4 steps -/
theorem drainBody_go_exact {main : Cmd} {a b : Stk} {T : Glyph} {r rF : Reg} (hab : a ≠ b)
    {h : Glyph} (hh : h ≠ T) {G A B : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph}
    (ha : X a = h :: G ++ T :: A) (hb : X b = B) :
    ∃ s', Eval main (Shift.drainBody a b T r rF) ⟨g, X⟩ s' 4 ∧ s'.reg rF = Shift.gGo ∧
      s'.stk a = G ++ T :: A ∧ s'.stk b = h :: B ∧
      (∀ k : Stk, k ≠ a → k ≠ b → s'.stk k = X k) := by
  have h1 : Eval main (.pop a r) ⟨g, X⟩
      ⟨Function.update g r h, Function.update X a (G ++ T :: A)⟩ 1 := by
    have h0 := Eval.pop (main := main) a r (⟨g, X⟩ : State)
    simpa [ha] using h0
  have hp : Eval main (.push b r) ⟨Function.update g r h, Function.update X a (G ++ T :: A)⟩
      ⟨Function.update g r h, Function.update (Function.update X a (G ++ T :: A)) b (h :: B)⟩ 1 := by
    have h0 := Eval.push (main := main) b r
      (⟨Function.update g r h, Function.update X a (G ++ T :: A)⟩ : State)
    have hXb : (Function.update X a (G ++ T :: A)) b = B := by
      simp [Function.update_apply, hab, Ne.symm hab, hb]
    simp only [Function.update_self, hXb] at h0
    exact h0
  have hs : Eval main (.set rF Shift.gGo)
      ⟨Function.update g r h, Function.update (Function.update X a (G ++ T :: A)) b (h :: B)⟩
      ⟨Function.update (Function.update g r h) rF Shift.gGo,
        Function.update (Function.update X a (G ++ T :: A)) b (h :: B)⟩ 1 :=
    Eval.set rF Shift.gGo _
  have h23 : Eval main (Shift.seqs [.push b r, .set rF Shift.gGo])
      ⟨Function.update g r h, Function.update X a (G ++ T :: A)⟩
      ⟨Function.update (Function.update g r h) rF Shift.gGo,
        Function.update (Function.update X a (G ++ T :: A)) b (h :: B)⟩ 2 := by
    rw [Shift.seqs_pair]
    exact Eval.seq hp hs
  have hh1 : (Function.update g r h) r ≠ T := by simpa using hh
  have hite : Eval main
      (Shift.seqs [.pop a r,
        .ite r T (Shift.seqs [.push a r, .set rF Shift.gStop])
          (Shift.seqs [.push b r, .set rF Shift.gGo])])
      ⟨g, X⟩
      ⟨Function.update (Function.update g r h) rF Shift.gGo,
        Function.update (Function.update X a (G ++ T :: A)) b (h :: B)⟩ 4 :=
    Eval.seq h1 (Eval.iteF hh1 h23)
  refine ⟨⟨Function.update (Function.update g r h) rF Shift.gGo,
    Function.update (Function.update X a (G ++ T :: A)) b (h :: B)⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Shift.drainBody] using hite
  · exact Function.update_self rF Shift.gGo (Function.update g r h)
  · show (Function.update (Function.update X a (G ++ T :: A)) b (h :: B)) a = G ++ T :: A
    rw [Shift.upStk_ne hab, Shift.upStk_same]
  · show (Function.update (Function.update X a (G ++ T :: A)) b (h :: B)) b = h :: B
    rw [Shift.upStk_same]
  · intro k hk1 hk2
    show (Function.update (Function.update X a (G ++ T :: A)) b (h :: B)) k = X k
    rw [Shift.upStk_ne hk2, Shift.upStk_ne hk1]

/-- exact cost of `Shift.drainBody`, "hit" case (the popped glyph is the marker): 4 steps -/
theorem drainBody_hit_exact {main : Cmd} {a b : Stk} {T : Glyph} {r rF : Reg} (hab : a ≠ b)
    {A B : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph} (ha : X a = T :: A)
    (hb : X b = B) :
    ∃ s', Eval main (Shift.drainBody a b T r rF) ⟨g, X⟩ s' 4 ∧ s'.reg rF = Shift.gStop ∧
      s'.stk a = T :: A ∧ s'.stk b = B ∧
      (∀ k : Stk, k ≠ a → k ≠ b → s'.stk k = X k) := by
  have h1 : Eval main (.pop a r) ⟨g, X⟩
      ⟨Function.update g r T, Function.update X a A⟩ 1 := by
    have h0 := Eval.pop (main := main) a r (⟨g, X⟩ : State)
    simpa [ha] using h0
  have hp : Eval main (.push a r) ⟨Function.update g r T, Function.update X a A⟩
      ⟨Function.update g r T, Function.update X a (T :: A)⟩ 1 := by
    have h0 := Eval.push (main := main) a r (⟨Function.update g r T, Function.update X a A⟩ : State)
    simp only [Function.update_self, Function.update_idem] at h0
    exact h0
  have hs : Eval main (.set rF Shift.gStop)
      ⟨Function.update g r T, Function.update X a (T :: A)⟩
      ⟨Function.update (Function.update g r T) rF Shift.gStop,
        Function.update X a (T :: A)⟩ 1 :=
    Eval.set rF Shift.gStop _
  have h23 : Eval main (Shift.seqs [.push a r, .set rF Shift.gStop])
      ⟨Function.update g r T, Function.update X a A⟩
      ⟨Function.update (Function.update g r T) rF Shift.gStop,
        Function.update X a (T :: A)⟩ 2 := by
    rw [Shift.seqs_pair]
    exact Eval.seq hp hs
  have hreg : (⟨Function.update g r T, Function.update X a A⟩ : State).reg r = T :=
    Function.update_self r T g
  have hite : Eval main
      (Shift.seqs [.pop a r,
        .ite r T (Shift.seqs [.push a r, .set rF Shift.gStop])
          (Shift.seqs [.push b r, .set rF Shift.gGo])])
      ⟨g, X⟩ ⟨Function.update (Function.update g r T) rF Shift.gStop,
        Function.update X a (T :: A)⟩ 4 :=
    Eval.seq h1 (Eval.iteT hreg h23)
  refine ⟨⟨Function.update (Function.update g r T) rF Shift.gStop,
    Function.update X a (T :: A)⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Shift.drainBody] using hite
  · exact Function.update_self rF Shift.gStop (Function.update g r T)
  · show (Function.update X a (T :: A)) a = T :: A
    rw [Shift.upStk_same]
  · show (Function.update X a (T :: A)) b = B
    rw [Shift.upStk_ne' hab]; exact hb
  · intro k hk1 hk2
    show (Function.update X a (T :: A)) k = X k
    rw [Shift.upStk_ne hk1]

/-- exact cost of the `Shift.drain` loop on a region `G` of length `L`: `5 * L + 6` steps -/
theorem drain_loop_exact (main : Cmd) (a b : Stk) (T : Glyph) (r rF : Reg) (hab : a ≠ b)
    (hrF : rF ≠ r) :
    ∀ (G : List Glyph) (A B : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      (∀ h ∈ G, h ≠ T) → g rF = Shift.gGo → X a = G ++ T :: A → X b = B →
      ∃ s', Eval main (.loop rF Shift.gGo (Shift.drainBody a b T r rF)) ⟨g, X⟩ s'
          (5 * G.length + 6) ∧ s'.reg rF ≠ Shift.gGo ∧ s'.stk a = T :: A ∧
        s'.stk b = G.reverse ++ B ∧ (∀ k : Stk, k ≠ a → k ≠ b → s'.stk k = X k) := by
  intro G
  induction G with
  | nil =>
      intro A B g X _ hgo ha hb
      obtain ⟨s1, he1, hre1, ha1, hb1, ho1⟩ :=
        drainBody_hit_exact (main := main) (a := a) (b := b) (T := T) (r := r) (rF := rF)
          (hab := hab) (A := A) (B := B) (g := g) (X := X) ha hb
      have hne : s1.reg rF ≠ Shift.gGo := by rw [hre1]; exact Shift.gStop_ne_gGo
      have hloop : Eval main (.loop rF Shift.gGo (Shift.drainBody a b T r rF)) ⟨g, X⟩ s1
          (4 + 1 + 1) :=
        Eval.loopT hgo he1 (Eval.loopF (main := main) (s := s1) hne)
      refine ⟨s1, ?_, hne, ha1, ?_, ho1⟩
      · simpa using hloop
      · rw [List.reverse_nil, List.nil_append]; exact hb1
  | cons h G' ih =>
      intro A B g X hG hgo ha hb
      have hh : h ≠ T := hG h (List.mem_cons_self ..)
      have hG' : ∀ x ∈ G', x ≠ T := fun x hx => hG x (List.mem_cons_of_mem h hx)
      obtain ⟨s1, he1, hre1, ha1, hb1, ho1⟩ :=
        drainBody_go_exact (main := main) (a := a) (b := b) (T := T) (r := r) (rF := rF)
          (hab := hab) (hh := hh) (G := G') (A := A) (B := B) (g := g) (X := X) ha hb
      obtain ⟨s2, he2, hre2, ha2, hb2, ho2⟩ := ih A (h :: B) s1.reg s1.stk hG' hre1 ha1 hb1
      have hloop : Eval main (.loop rF Shift.gGo (Shift.drainBody a b T r rF)) ⟨g, X⟩ s2
          (4 + (5 * G'.length + 6) + 1) := Eval.loopT hgo he1 he2
      refine ⟨s2, ?_, hre2, ha2, ?_, ?_⟩
      · have harith : 4 + (5 * G'.length + 6) + 1 = 5 * (h :: G').length + 6 := by
          simp only [List.length_cons]; ring
        rw [harith] at hloop; exact hloop
      · rw [hb2, List.reverse_cons, List.append_assoc]; rfl
      · intro k hk1 hk2; rw [ho2 k hk1 hk2, ho1 k hk1 hk2]

/-- The exact cost of `Shift.drain` on a region `G`: `5 * G.length + 7` steps. -/
theorem drain_exact (main : Cmd) (a b : Stk) (T : Glyph) (r rF : Reg) (hab : a ≠ b)
    (hrF : rF ≠ r) :
    ∀ (G A B : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      (∀ h ∈ G, h ≠ T) → X a = G ++ T :: A → X b = B →
      ∃ s', Eval main (Shift.drain a b T r rF) ⟨g, X⟩ s' (5 * G.length + 7) ∧
        s'.reg rF ≠ Shift.gGo ∧ s'.stk a = T :: A ∧ s'.stk b = G.reverse ++ B ∧
        (∀ k : Stk, k ≠ a → k ≠ b → s'.stk k = X k) := by
  intro G A B g X hG ha hb
  have hgo : (Function.update g rF Shift.gGo) rF = Shift.gGo :=
    Function.update_self rF Shift.gGo g
  obtain ⟨s', he, hne, ha', hb', ho'⟩ :=
    drain_loop_exact main a b T r rF hab hrF G A B (Function.update g rF Shift.gGo) X
      hG hgo ha hb
  have hset : Eval main (.set rF Shift.gGo) ⟨g, X⟩ ⟨Function.update g rF Shift.gGo, X⟩ 1 :=
    Eval.set rF Shift.gGo ⟨g, X⟩
  have hcost : (5 : ℕ) * G.length + 7 = 1 + (5 * G.length + 6) := by ring
  refine ⟨s', ?_, hne, ha', hb', ho'⟩
  rw [Shift.drain, Shift.seqs_pair, hcost]
  exact Eval.seq hset he

/-- **The cost of a `Shift.drain` is exactly `5 * L + 7`**: every derivation of a run moving the
region `G` (of length `L`) above the marker `T` from stack `a` onto stack `b` has that cost.  Hence
the bound `5 * (L + 1) + 2` of `Shift.drain_ev` is tight. -/
theorem drain_cost (main : Cmd) (a b : Stk) (T : Glyph) (r rF : Reg) (hab : a ≠ b)
    (hrF : rF ≠ r) {G A B : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph} {s' : State}
    {n : ℕ} (hG : ∀ h ∈ G, h ≠ T) (ha : X a = G ++ T :: A) (hb : X b = B)
    (h : Eval main (Shift.drain a b T r rF) ⟨g, X⟩ s' n) : n = 5 * G.length + 7 :=
  (Eval.det h (drain_exact main a b T r rF hab hrF G A B g X hG ha hb).choose_spec.1).2

/-- specialisation to a region `Val.enc (.int z)` (of length `isz z`): cost `5 * isz z + 7` -/
theorem drain_cost_enc (main : Cmd) (a b : Stk) (T : Glyph) (r rF : Reg) (hab : a ≠ b)
    (hrF : rF ≠ r) (z : ℤ) {A B : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph}
    {s' : State} {n : ℕ} (hG : ∀ h ∈ Val.enc (.int z), h ≠ T)
    (ha : X a = Val.enc (.int z) ++ T :: A) (hb : X b = B)
    (h : Eval main (Shift.drain a b T r rF) ⟨g, X⟩ s' n) : n = 5 * isz z + 7 := by
  rw [drain_cost main a b T r rF hab hrF hG ha hb h, vsz_int z]

end Work.IntLib
