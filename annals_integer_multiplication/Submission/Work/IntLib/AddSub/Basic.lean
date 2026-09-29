import Mathlib
import Submission.Work.IntLib.AddSub.Defs

/-!
# `IntLib` / add–sub: elementary program lemmas

`Ev`-style specifications of the pieces of the programs in
`Submission.Work.IntLib.AddSub.Defs`:

* `asw_drain` — move a marked segment of a stack to another stack, reversing it;
* `asw_clearAt` / `asw_clear` — discard (and pop) a marked segment.
-/

set_option autoImplicit false

namespace Work.IntLib
namespace AddSub

open HvdH

/-! ## The drain body -/

/-- One iteration of the drain body that reads a glyph different from `T`: it is pushed
onto `b` and the flag is set to `gGo` (continue). -/
theorem asw_drain_body_go {main : Cmd} {a b : Stk} {T : Glyph} {r rF : Reg} (hab : a ≠ b)
    {h : Glyph} (hh : h ≠ T) {G A B : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph}
    (ha : X a = h :: G ++ T :: A) (hb : X b = B) :
    ∃ s' n, Ev main (seqs [.pop a r, .ite r T (seqs [.push a r, .set rF gStop])
        (seqs [.push b r, .set rF gGo])]) ⟨g, X⟩ s' n ∧ n ≤ 4 ∧
      s'.stk a = G ++ T :: A ∧ s'.stk b = h :: B ∧ s'.reg rF = gGo := by
  let g1 : Reg → Glyph := Function.update g r ((X a).headD Glyph.eos)
  let X1 : Stk → List Glyph := Function.update X a (X a).tail
  let X2 : Stk → List Glyph := Function.update X1 b (g1 r :: X1 b)
  let g2 : Reg → Glyph := Function.update g1 rF gGo
  have h1 : Ev main (.pop a r) ⟨g, X⟩ ⟨g1, X1⟩ 1 := ev_pop' main a r g X
  have hh' : (⟨g1, X1⟩ : State).reg r ≠ T := by
    show g1 r ≠ T
    simp only [g1, upReg_same]
    rw [ha]; simp [hh]
  have hp : Ev main (.push b r) ⟨g1, X1⟩ ⟨g1, X2⟩ 1 := ev_push' main b r g1 X1
  have hs : Ev main (.set rF gGo) ⟨g1, X2⟩ ⟨g2, X2⟩ 1 := ev_set' main rF gGo g1 X2
  have h2 : Ev main (.ite r T (seqs [.push a r, .set rF gStop]) (seqs [.push b r, .set rF gGo]))
      ⟨g1, X1⟩ ⟨g2, X2⟩ 3 := Ev.iteF hh' (Ev.seq' hp hs (by omega))
  have hmain : Ev main (seqs [.pop a r, .ite r T (seqs [.push a r, .set rF gStop])
        (seqs [.push b r, .set rF gGo])]) ⟨g, X⟩ ⟨g2, X2⟩ 4 := by
    simp only [seqs]
    exact Ev.seq' h1 h2 (by omega)
  refine ⟨⟨g2, X2⟩, _, hmain, by omega, ?_, ?_, ?_⟩
  · simp only [stk_mk]
    have h : X2 a = (X a).tail := by simp only [X2, X1, upStk_ne hab, upStk_same]
    rw [h, ha]; rfl
  · simp only [stk_mk]
    have h1' : X2 b = g1 r :: X1 b := by simp only [X2, upStk_same]
    have h2' : g1 r = (X a).headD Glyph.eos := by simp only [g1, upReg_same]
    have h3' : X1 b = X b := by simp only [X1, upStk_ne hab.symm]
    simp [h1', h2', h3', ha, hb]
  · simp only [reg_mk, g2, g1, upReg_same]

/-- One iteration of the drain body that reads the marker `T`: it is pushed back and the flag
is set to `gStop` (stop). -/
theorem asw_drain_body_hit {main : Cmd} {a b : Stk} {T : Glyph} {r rF : Reg} (hab : a ≠ b)
    {A B : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph}
    (ha : X a = T :: A) (hb : X b = B) :
    ∃ s' n, Ev main (seqs [.pop a r, .ite r T (seqs [.push a r, .set rF gStop])
        (seqs [.push b r, .set rF gGo])]) ⟨g, X⟩ s' n ∧ n ≤ 4 ∧
      s'.stk a = T :: A ∧ s'.stk b = B ∧ s'.reg rF = gStop := by
  let g1 : Reg → Glyph := Function.update g r ((X a).headD Glyph.eos)
  let X1 : Stk → List Glyph := Function.update X a (X a).tail
  let X2 : Stk → List Glyph := Function.update X1 a (g1 r :: X1 a)
  let g2 : Reg → Glyph := Function.update g1 rF gStop
  have h1 : Ev main (.pop a r) ⟨g, X⟩ ⟨g1, X1⟩ 1 := ev_pop' main a r g X
  have hh : (⟨g1, X1⟩ : State).reg r = T := by
    show g1 r = T
    simp only [g1, upReg_same]
    rw [ha]; simp
  have hp : Ev main (.push a r) ⟨g1, X1⟩ ⟨g1, X2⟩ 1 := ev_push' main a r g1 X1
  have hs : Ev main (.set rF gStop) ⟨g1, X2⟩ ⟨g2, X2⟩ 1 := ev_set' main rF gStop g1 X2
  have h2 : Ev main (.ite r T (seqs [.push a r, .set rF gStop]) (seqs [.push b r, .set rF gGo]))
      ⟨g1, X1⟩ ⟨g2, X2⟩ 3 := Ev.iteT hh (Ev.seq' hp hs (by omega))
  have hmain : Ev main (seqs [.pop a r, .ite r T (seqs [.push a r, .set rF gStop])
        (seqs [.push b r, .set rF gGo])]) ⟨g, X⟩ ⟨g2, X2⟩ 4 := by
    simp only [seqs]
    exact Ev.seq' h1 h2 (by omega)
  refine ⟨⟨g2, X2⟩, _, hmain, by omega, ?_, ?_, ?_⟩
  · simp only [stk_mk]
    have h1' : X2 a = g1 r :: X1 a := by simp only [X2, upStk_same]
    have h2' : g1 r = (X a).headD Glyph.eos := by simp only [g1, upReg_same]
    have h3' : X1 a = (X a).tail := by simp only [X1, upStk_same]
    simp [h1', h2', h3', ha]
  · simp only [stk_mk]
    have h1' : X2 b = X1 b := by simp only [X2, upStk_ne hab.symm]
    have h2' : X1 b = X b := by simp only [X1, upStk_ne hab.symm]
    simp only [h1', h2', hb]
  · simp only [reg_mk, g2, g1, upReg_same]

/-! ## The drain loops -/

/-- The drain loop: `G` is the segment above the marker `T` on stack `a`; the loop moves it,
reversed, onto `b` and stops with flag `gStop`, leaving the marker (and `A`) on `a`. -/
theorem asw_drainLoop_ev {main : Cmd} (a b : Stk) (T : Glyph) (r rF : Reg)
    (hab : a ≠ b) (hrF : r ≠ rF) :
    ∀ (G : List Glyph) (A B : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      (∀ h ∈ G, h ≠ T) → g rF = gGo → X a = G ++ T :: A → X b = B →
      ∃ s' n, Ev main (.loop rF gGo (seqs [.pop a r,
          .ite r T (seqs [.push a r, .set rF gStop]) (seqs [.push b r, .set rF gGo])]))
          ⟨g, X⟩ s' n ∧ n ≤ 5 * (G.length + 1) + 1 ∧
        s'.stk a = T :: A ∧ s'.stk b = G.reverse ++ B ∧ s'.reg rF ≠ gGo := by
  intro G
  induction G with
  | nil =>
      intro A B g X _ hreg ha hb
      obtain ⟨s₂, n₂, he₂, hn₂, ha₂, hb₂, hr₂⟩ :=
        asw_drain_body_hit (main := main) (a := a) (b := b) (T := T) (r := r) (rF := rF) hab ha hb
      have hne : s₂.reg rF ≠ gGo := by rw [hr₂]; decide
      have hloop : Ev main (.loop rF gGo (seqs [.pop a r,
          .ite r T (seqs [.push a r, .set rF gStop]) (seqs [.push b r, .set rF gGo])]))
          ⟨g, X⟩ s₂ (n₂ + 1 + 1) := Ev.loopT hreg he₂ (Ev.loopF hne)
      refine ⟨s₂, _, hloop, by omega, ?_, ?_, hne⟩
      · simpa using ha₂
      · simpa using hb₂
  | cons h G' ih =>
      intro A B g X hG hreg ha hb
      have hh : h ≠ T := hG h (List.mem_cons_self ..)
      have hG' : ∀ x ∈ G', x ≠ T := fun x hx => hG x (List.mem_cons_of_mem h hx)
      obtain ⟨s₁, n₁, he₁, hn₁, ha₁, hb₁, hr₁⟩ :=
        asw_drain_body_go (main := main) (a := a) (b := b) (T := T) (r := r) (rF := rF)
          hab hh ha hb
      obtain ⟨s₂, n₂, he₂, hn₂, ha₂, hb₂, hr₂⟩ :=
        ih A (h :: B) s₁.reg s₁.stk hG' hr₁ ha₁ hb₁
      have hloop : Ev main (.loop rF gGo (seqs [.pop a r,
          .ite r T (seqs [.push a r, .set rF gStop]) (seqs [.push b r, .set rF gGo])]))
          ⟨g, X⟩ s₂ (n₁ + n₂ + 1) := Ev.loopT hreg he₁ he₂
      refine ⟨s₂, _, hloop, ?_, ?_, ?_, hr₂⟩
      · have hlen : G'.length + 1 = (h :: G').length := by simp
        omega
      · simpa using ha₂
      · rw [hb₂, List.reverse_cons]; simp [List.append_assoc]

/-- The drain program: move the segment above the marker `T` from `a` to `b`, reversed. -/
theorem asw_drain_ev {main : Cmd} (a b : Stk) (T : Glyph) (r rF : Reg)
    (hab : a ≠ b) (hrF : r ≠ rF) :
    ∀ (G : List Glyph) (A B : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      (∀ h ∈ G, h ≠ T) → X a = G ++ T :: A → X b = B →
      ∃ s' n, Ev main (asw_drain a b T r rF) ⟨g, X⟩ s' n ∧ n ≤ 5 * (G.length + 1) + 2 ∧
        s'.stk a = T :: A ∧ s'.stk b = G.reverse ++ B ∧ s'.reg rF ≠ gGo := by
  intro G A B g X hG ha hb
  let g₁ : Reg → Glyph := Function.update g rF gGo
  have hset : Ev main (.set rF gGo) ⟨g, X⟩ ⟨g₁, X⟩ 1 := ev_set' main rF gGo g X
  obtain ⟨s', n, hev, hn, ha', hb', hr'⟩ :=
    asw_drainLoop_ev (main := main) a b T r rF hab hrF G A B g₁ X hG (by simp [g₁]) ha hb
  have hmain : Ev main (asw_drain a b T r rF) ⟨g, X⟩ s' (1 + n) := by
    unfold asw_drain
    simp only [seqs]
    exact Ev.seq' hset hev (by omega)
  exact ⟨s', _, hmain, by omega, ha', hb', hr'⟩

/-! ## The clearing loops -/

/-- Body of the clearing loop on a non-marker glyph: discard it and continue. -/
theorem asw_clearAt_body_go {main : Cmd} {k : Stk} {M : Glyph} {r rF : Reg}
    {h : Glyph} (hh : h ≠ M) {G A : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph}
    (ha : X k = h :: G ++ M :: A) (hreg : g rF = gGo) :
    ∃ s' n, Ev main (seqs [.pop k r, .ite r M (seqs [.push k r, .set rF gStop]) (.set rF gGo)])
        ⟨g, X⟩ s' n ∧ n ≤ 3 ∧ s'.stk k = G ++ M :: A ∧ s'.reg rF = gGo := by
  let g1 : Reg → Glyph := Function.update g r ((X k).headD Glyph.eos)
  let X1 : Stk → List Glyph := Function.update X k (X k).tail
  have h1 : Ev main (.pop k r) ⟨g, X⟩ ⟨g1, X1⟩ 1 := ev_pop' main k r g X
  have hh' : (⟨g1, X1⟩ : State).reg r ≠ M := by
    show g1 r ≠ M
    simp only [g1, upReg_same]
    rw [ha]; simp [hh]
  have hset : Ev main (.set rF gGo) ⟨g1, X1⟩ ⟨Function.update g1 rF gGo, X1⟩ 1 :=
    ev_set' main rF gGo g1 X1
  have h2 : Ev main (.ite r M (seqs [.push k r, .set rF gStop]) (.set rF gGo)) ⟨g1, X1⟩
      ⟨Function.update g1 rF gGo, X1⟩ 2 := Ev.iteF hh' hset
  have hmain : Ev main (seqs [.pop k r, .ite r M (seqs [.push k r, .set rF gStop])
      (.set rF gGo)]) ⟨g, X⟩ ⟨Function.update g1 rF gGo, X1⟩ 3 := by
    simp only [seqs]
    exact Ev.seq' h1 h2 (by omega)
  refine ⟨⟨Function.update g1 rF gGo, X1⟩, _, hmain, by omega, ?_, ?_⟩
  · simp only [stk_mk]
    have h : X1 k = (X k).tail := by simp only [X1, upStk_same]
    rw [h, ha]; rfl
  · simp only [reg_mk, g1, upReg_same]

/-- Body of the clearing loop on the marker: push it back and stop. -/
theorem asw_clearAt_body_hit {main : Cmd} {k : Stk} {M : Glyph} {r rF : Reg}
    {A : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph} (ha : X k = M :: A) :
    ∃ s' n, Ev main (seqs [.pop k r, .ite r M (seqs [.push k r, .set rF gStop]) (.set rF gGo)])
        ⟨g, X⟩ s' n ∧ n ≤ 4 ∧ s'.stk k = M :: A ∧ s'.reg rF = gStop := by
  let g1 : Reg → Glyph := Function.update g r ((X k).headD Glyph.eos)
  let X1 : Stk → List Glyph := Function.update X k (X k).tail
  let X2 : Stk → List Glyph := Function.update X1 k (g1 r :: X1 k)
  have h1 : Ev main (.pop k r) ⟨g, X⟩ ⟨g1, X1⟩ 1 := ev_pop' main k r g X
  have hh : (⟨g1, X1⟩ : State).reg r = M := by
    show g1 r = M
    simp only [g1, upReg_same]
    rw [ha]; simp
  have hp : Ev main (.push k r) ⟨g1, X1⟩ ⟨g1, X2⟩ 1 := ev_push' main k r g1 X1
  have hs : Ev main (.set rF gStop) ⟨g1, X2⟩ ⟨Function.update g1 rF gStop, X2⟩ 1 :=
    ev_set' main rF gStop g1 X2
  have h2 : Ev main (.ite r M (seqs [.push k r, .set rF gStop]) (.set rF gGo)) ⟨g1, X1⟩
      ⟨Function.update g1 rF gStop, X2⟩ 3 := Ev.iteT hh (Ev.seq' hp hs (by omega))
  have hmain : Ev main (seqs [.pop k r, .ite r M (seqs [.push k r, .set rF gStop])
      (.set rF gGo)]) ⟨g, X⟩ ⟨Function.update g1 rF gStop, X2⟩ 4 := by
    simp only [seqs]
    exact Ev.seq' h1 h2 (by omega)
  refine ⟨⟨Function.update g1 rF gStop, X2⟩, _, hmain, by omega, ?_, ?_⟩
  · simp only [stk_mk]
    have h1' : X2 k = g1 r :: X1 k := by simp only [X2, upStk_same]
    have h2' : g1 r = (X k).headD Glyph.eos := by simp only [g1, upReg_same]
    have h3' : X1 k = (X k).tail := by simp only [X1, upStk_same]
    simp [h1', h2', h3', ha]
  · simp only [reg_mk, g1, upReg_same]

/-- The clearing loop: pop the segment above the marker `M` on stack `k` (discarding it),
leaving the marker in place. -/
theorem asw_clearAtLoop_ev {main : Cmd} (k : Stk) (M : Glyph) (r rF : Reg) (hrF : r ≠ rF) :
    ∀ (G : List Glyph) (A : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      (∀ h ∈ G, h ≠ M) → g rF = gGo → X k = G ++ M :: A →
      ∃ s' n, Ev main (.loop rF gGo (seqs [.pop k r, .ite r M (seqs [.push k r, .set rF gStop])
          (.set rF gGo)])) ⟨g, X⟩ s' n ∧ n ≤ 5 * (G.length + 1) + 1 ∧
        s'.stk k = M :: A ∧ s'.reg rF ≠ gGo := by
  intro G
  induction G with
  | nil =>
      intro A g X _ hreg ha
      obtain ⟨s₂, n₂, he₂, hn₂, ha₂, hr₂⟩ :=
        asw_clearAt_body_hit (main := main) (k := k) (M := M) (r := r) (rF := rF) (g := g) (X := X) ha
      have hne : s₂.reg rF ≠ gGo := by rw [hr₂]; decide
      have hloop : Ev main (.loop rF gGo (seqs [.pop k r, .ite r M (seqs [.push k r, .set rF gStop])
          (.set rF gGo)])) ⟨g, X⟩ s₂ (n₂ + 1 + 1) := Ev.loopT hreg he₂ (Ev.loopF hne)
      exact ⟨s₂, _, hloop, by omega, ha₂, hne⟩
  | cons h G' ih =>
      intro A g X hG hreg ha
      have hh : h ≠ M := hG h (List.mem_cons_self ..)
      have hG' : ∀ x ∈ G', x ≠ M := fun x hx => hG x (List.mem_cons_of_mem h hx)
      obtain ⟨s₁, n₁, he₁, hn₁, ha₁, hr₁⟩ :=
        asw_clearAt_body_go (main := main) (k := k) (M := M) (r := r) (rF := rF)
          (g := g) (X := X) hh ha hreg
      obtain ⟨s₂, n₂, he₂, hn₂, ha₂, hr₂⟩ := ih A s₁.reg s₁.stk hG' hr₁ ha₁
      have hloop : Ev main (.loop rF gGo (seqs [.pop k r, .ite r M (seqs [.push k r, .set rF gStop])
          (.set rF gGo)])) ⟨g, X⟩ s₂ (n₁ + n₂ + 1) := Ev.loopT hreg he₁ he₂
      refine ⟨s₂, _, hloop, ?_, ha₂, hr₂⟩
      · have hlen : G'.length + 1 = (h :: G').length := by simp
        omega

/-- The clearing program: `asw_clearAtLoop` with the flag initialised. -/
theorem asw_clearAt_ev {main : Cmd} (k : Stk) (M : Glyph) (r rF : Reg) (hrF : r ≠ rF) :
    ∀ (G : List Glyph) (A : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      (∀ h ∈ G, h ≠ M) → X k = G ++ M :: A →
      ∃ s' n, Ev main (asw_clearAt k M r rF) ⟨g, X⟩ s' n ∧ n ≤ 5 * (G.length + 1) + 2 ∧
        s'.stk k = M :: A ∧ s'.reg rF ≠ gGo := by
  intro G A g X hG ha
  let g₁ : Reg → Glyph := Function.update g rF gGo
  have hset : Ev main (.set rF gGo) ⟨g, X⟩ ⟨g₁, X⟩ 1 := ev_set' main rF gGo g X
  obtain ⟨s', n, hev, hn, ha', hr'⟩ :=
    asw_clearAtLoop_ev (main := main) k M r rF hrF G A g₁ X hG (by simp [g₁]) ha
  have hmain : Ev main (asw_clearAt k M r rF) ⟨g, X⟩ s' (1 + n) := by
    unfold asw_clearAt
    simp only [seqs]
    exact Ev.seq' hset hev (by omega)
  exact ⟨s', _, hmain, by omega, ha', hr'⟩

/-- `asw_clear` only touches stack `k`. -/
theorem cmdTouches_asw_clear (k : Stk) (M : Glyph) (r rF : Reg) :
    cmdTouches (asw_clear k M r rF) ⊆ {k} := by
  intro j hj
  simp only [asw_clear, asw_clearAt, seqs, cmdTouches, Finset.mem_union, Finset.mem_singleton,
    Finset.notMem_empty] at hj ⊢
  tauto

/-- `asw_clear`: discard the segment above the marker and pop the marker itself. -/
theorem asw_clear_ev {main : Cmd} (k : Stk) (M : Glyph) (r rF : Reg) (hrF : r ≠ rF) :
    ∀ (G : List Glyph) (A : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      (∀ h ∈ G, h ≠ M) → X k = G ++ M :: A →
      ∃ s' n, Ev main (asw_clear k M r rF) ⟨g, X⟩ s' n ∧ n ≤ 5 * (G.length + 1) + 3 ∧
        s'.stk k = A ∧ (∀ j : Stk, j ≠ k → s'.stk j = X j) := by
  intro G A g X hG ha
  obtain ⟨s₁, n₁, he₁, hn₁, ha₁, hr₁⟩ :=
    asw_clearAt_ev (main := main) k M r rF hrF G A g X hG ha
  let g2 : Reg → Glyph := Function.update s₁.reg r ((s₁.stk k).headD Glyph.eos)
  let X2 : Stk → List Glyph := Function.update s₁.stk k (s₁.stk k).tail
  have hpop : Ev main (.pop k r) s₁ ⟨g2, X2⟩ 1 := ev_pop' main k r s₁.reg s₁.stk
  have hmain : Ev main (asw_clear k M r rF) ⟨g, X⟩ ⟨g2, X2⟩ (n₁ + 1) := by
    unfold asw_clear
    simp only [seqs]
    exact Ev.seq' he₁ hpop (by omega)
  refine ⟨⟨g2, X2⟩, _, hmain, by omega, ?_, ?_⟩
  · simp only [stk_mk]
    have h : X2 k = (s₁.stk k).tail := by simp only [X2, upStk_same]
    rw [h, ha₁]; rfl
  · intro j hj
    have hfr := Ev.frame hmain (S := {k}) (cmdTouches_asw_clear k M r rF)
      (by simp only [Finset.mem_singleton]; exact hj)
    simpa using hfr

/-! ## The final cleanup -/

/-- `asw_cleanup` restores all seven scratch stacks to their entry content. -/
theorem asw_cleanup_ev {main : Cmd} :
    ∀ (G1 G3 G4 G5 G6 G8 G9 : List Glyph) (A1 A3 A4 A5 A6 A8 A9 : List Glyph)
      (g : Reg → Glyph) (X : Stk → List Glyph),
      (∀ h ∈ G1, h ≠ gmk sBuf) → (∀ h ∈ G3, h ≠ gmk sA) → (∀ h ∈ G4, h ≠ gmk sB) →
      (∀ h ∈ G5, h ≠ gmk sO1) → (∀ h ∈ G6, h ≠ gmk sO2) → (∀ h ∈ G8, h ≠ gmk sSgA) →
      (∀ h ∈ G9, h ≠ gmk sSgB) →
      X sBuf = G1 ++ gmk sBuf :: A1 → X sA = G3 ++ gmk sA :: A3 →
      X sB = G4 ++ gmk sB :: A4 → X sO1 = G5 ++ gmk sO1 :: A5 →
      X sO2 = G6 ++ gmk sO2 :: A6 → X sSgA = G8 ++ gmk sSgA :: A8 →
      X sSgB = G9 ++ gmk sSgB :: A9 →
      ∃ s' n, Ev main asw_cleanup ⟨g, X⟩ s' n ∧
        n ≤ 5 * (G1.length + G3.length + G4.length + G5.length + G6.length + G8.length
          + G9.length + 7) + 30 ∧
        s'.stk sBuf = A1 ∧ s'.stk sA = A3 ∧ s'.stk sB = A4 ∧ s'.stk sO1 = A5 ∧
        s'.stk sO2 = A6 ∧ s'.stk sSgA = A8 ∧ s'.stk sSgB = A9 := by
  intro G1 G3 G4 G5 G6 G8 G9 A1 A3 A4 A5 A6 A8 A9 g X h1 h3 h4 h5 h6 h8 h9 e1 e3 e4 e5 e6 e8 e9
  obtain ⟨s1, n1, he1, hn1, f1, f1'⟩ :=
    asw_clear_ev (main := main) sBuf (gmk sBuf) rT rF (by decide) G1 A1 g X h1 e1
  obtain ⟨s2, n2, he2, hn2, f2, f2'⟩ :=
    asw_clear_ev (main := main) sA (gmk sA) rT rF (by decide) G3 A3 s1.reg s1.stk h3
      (by rw [f1' sA (by decide)]; exact e3)
  obtain ⟨s3, n3, he3, hn3, f3, f3'⟩ :=
    asw_clear_ev (main := main) sB (gmk sB) rT rF (by decide) G4 A4 s2.reg s2.stk h4
      (by rw [f2' sB (by decide), f1' sB (by decide)]; exact e4)
  obtain ⟨s4, n4, he4, hn4, f4, f4'⟩ :=
    asw_clear_ev (main := main) sO1 (gmk sO1) rT rF (by decide) G5 A5 s3.reg s3.stk h5
      (by rw [f3' sO1 (by decide), f2' sO1 (by decide), f1' sO1 (by decide)]; exact e5)
  obtain ⟨s5, n5, he5, hn5, f5, f5'⟩ :=
    asw_clear_ev (main := main) sO2 (gmk sO2) rT rF (by decide) G6 A6 s4.reg s4.stk h6
      (by rw [f4' sO2 (by decide), f3' sO2 (by decide), f2' sO2 (by decide),
          f1' sO2 (by decide)]; exact e6)
  obtain ⟨s6, n6, he6, hn6, f6, f6'⟩ :=
    asw_clear_ev (main := main) sSgA (gmk sSgA) rT rF (by decide) G8 A8 s5.reg s5.stk h8
      (by rw [f5' sSgA (by decide), f4' sSgA (by decide), f3' sSgA (by decide),
          f2' sSgA (by decide), f1' sSgA (by decide)]; exact e8)
  obtain ⟨s7, n7, he7, hn7, f7, f7'⟩ :=
    asw_clear_ev (main := main) sSgB (gmk sSgB) rT rF (by decide) G9 A9 s6.reg s6.stk h9
      (by rw [f6' sSgB (by decide), f5' sSgB (by decide), f4' sSgB (by decide),
          f3' sSgB (by decide), f2' sSgB (by decide), f1' sSgB (by decide)]; exact e9)
  have hmain : Ev main asw_cleanup ⟨g, X⟩ s7 (n1 + (n2 + (n3 + (n4 + (n5 + (n6 + n7)))))) := by
    unfold asw_cleanup
    simp only [seqs]
    exact Ev.seq he1 (Ev.seq he2 (Ev.seq he3 (Ev.seq he4 (Ev.seq he5 (Ev.seq he6 he7)))))
  refine ⟨s7, _, hmain, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f7' sBuf (by decide), f6' sBuf (by decide), f5' sBuf (by decide), f4' sBuf (by decide),
      f3' sBuf (by decide), f2' sBuf (by decide)]; exact f1
  · rw [f7' sA (by decide), f6' sA (by decide), f5' sA (by decide), f4' sA (by decide),
      f3' sA (by decide)]; exact f2
  · rw [f7' sB (by decide), f6' sB (by decide), f5' sB (by decide), f4' sB (by decide)]; exact f3
  · rw [f7' sO1 (by decide), f6' sO1 (by decide), f5' sO1 (by decide)]; exact f4
  · rw [f7' sO2 (by decide), f6' sO2 (by decide)]; exact f5
  · rw [f7' sSgA (by decide)]; exact f6
  · exact f7

end AddSub
end Work.IntLib
