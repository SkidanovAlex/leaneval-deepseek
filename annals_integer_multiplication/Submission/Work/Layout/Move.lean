import Mathlib
import Submission.Work.Layout.Base

/-!
# Layout area: marker-based value movers

* `mvA a c d` moves the top value of stack `a` to stack `c` *reversed*, using stack `d` as a
  pending-subtree counter (unary: `gPend` marks one pending subtree, `gSent` is a sentinel below it).
* `mvB c b` moves the content of `c` down to the boundary marker `gMark` back onto `b`
  (reversing it again, so a value comes out in normal order).
* `mvVal a b c d = mvA a c d ; mvB c b` moves one value from `a` to `b` in normal order, leaving all
  other stacks (in particular the caller's data below the boundary marker) untouched.

Basic `Ev` facts are stated with the literal states the primitive produces; composite lemmas are
stated in terms of the *facts* they establish about the stacks they touch.
-/

set_option autoImplicit false

namespace Work.Layout

open HvdH
open Computability

/-! ## Markers and registers -/

/-- boundary marker on the buffer stack; never part of a `Val` encoding -/
def gMark : Glyph := .mk 7
/-- sentinel at the bottom of the pending counter -/
def gSent : Glyph := .mk 8
/-- one unit of the pending counter -/
def gPend : Glyph := .mk 9

def rLoopG : Reg := 0
def rA : Reg := 1
def rB : Reg := 2
def rC : Reg := 3
def rD : Reg := 4


@[simp] theorem gcons_ne_nil : Glyph.cons ≠ Glyph.nil := fun h => by cases h
@[simp] theorem gcons_ne_iend : Glyph.cons ≠ Glyph.iend := fun h => by cases h
@[simp] theorem gnil_ne_cons : Glyph.nil ≠ Glyph.cons := fun h => by cases h
@[simp] theorem gnil_ne_iend : Glyph.nil ≠ Glyph.iend := fun h => by cases h
@[simp] theorem giend_ne_cons : Glyph.iend ≠ Glyph.cons := fun h => by cases h
@[simp] theorem giend_ne_nil : Glyph.iend ≠ Glyph.nil := fun h => by cases h

theorem gMark_ne_bit (b : Bool) : gMark ≠ Glyph.bit b := fun h => by cases h
theorem gMark_ne_pos : gMark ≠ Glyph.pos := fun h => by cases h
theorem gMark_ne_neg : gMark ≠ Glyph.neg := fun h => by cases h
theorem gMark_ne_nil : gMark ≠ Glyph.nil := fun h => by cases h
theorem gMark_ne_iend : gMark ≠ Glyph.iend := fun h => by cases h
theorem gMark_ne_cons : gMark ≠ Glyph.cons := fun h => by cases h
theorem gPend_ne_bit (b : Bool) : gPend ≠ Glyph.bit b := fun h => by cases h
@[simp] theorem gPend_ne_pos : gPend ≠ Glyph.pos := fun h => by cases h
@[simp] theorem gPend_ne_neg : gPend ≠ Glyph.neg := fun h => by cases h
@[simp] theorem gPend_ne_nil : gPend ≠ Glyph.nil := fun h => by cases h
@[simp] theorem gPend_ne_iend : gPend ≠ Glyph.iend := fun h => by cases h
@[simp] theorem gPend_ne_cons : gPend ≠ Glyph.cons := fun h => by cases h
@[simp] theorem gSent_ne_gPend : gSent ≠ gPend := fun h => by cases h
@[simp] theorem gSent_ne_cons : gSent ≠ Glyph.cons := fun h => by cases h
@[simp] theorem gSent_ne_nil : gSent ≠ Glyph.nil := fun h => by cases h
@[simp] theorem gSent_ne_iend : gSent ≠ Glyph.iend := fun h => by cases h
theorem gSent_ne_bit (b : Bool) : gSent ≠ Glyph.bit b := fun h => by cases h
@[simp] theorem gSent_ne_pos : gSent ≠ Glyph.pos := fun h => by cases h
@[simp] theorem gSent_ne_neg : gSent ≠ Glyph.neg := fun h => by cases h

/-- `h` is not one of the structural glyphs `cons`, `nil`, `iend`. -/
def NotStruct (h : Glyph) : Prop := h ≠ Glyph.cons ∧ h ≠ Glyph.nil ∧ h ≠ Glyph.iend

theorem notStruct_bit (b : Bool) : NotStruct (Glyph.bit b) := by
  unfold NotStruct; refine ⟨?_, ?_, ?_⟩ <;> (intro h; cases h)
theorem notStruct_pos : NotStruct Glyph.pos := by
  unfold NotStruct; refine ⟨?_, ?_, ?_⟩ <;> (intro h; cases h)
theorem notStruct_neg : NotStruct Glyph.neg := by
  unfold NotStruct; refine ⟨?_, ?_, ?_⟩ <;> (intro h; cases h)

theorem notStruct_sign (z : ℤ) : NotStruct (if z < 0 then Glyph.neg else Glyph.pos) := by
  unfold NotStruct
  by_cases hz : z < 0
  · rw [if_pos hz]; refine ⟨?_, ?_, ?_⟩ <;> (intro h; cases h)
  · rw [if_neg hz]; refine ⟨?_, ?_, ?_⟩ <;> (intro h; cases h)

theorem notStruct_map_bit {bs : List Bool} : ∀ h ∈ bs.map Glyph.bit, NotStruct h := by
  intro h hh
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hh
  exact notStruct_bit b

theorem not_mem_map_bit (x : Glyph) (hx : ∀ b, x ≠ Glyph.bit b) (bs : List Bool) :
    x ∉ bs.map Glyph.bit := by
  intro h
  obtain ⟨b, -, hb⟩ := List.mem_map.mp h
  exact hx b hb.symm

theorem gMark_not_mem_enc (v : Val) : gMark ∉ v.enc := by
  induction v with
  | int z =>
      intro hmem
      simp only [Val.enc] at hmem
      rcases List.mem_cons.mp hmem with h | h
      · by_cases hz : z < 0
        · rw [if_pos hz] at h; exact gMark_ne_neg h
        · rw [if_neg hz] at h; exact gMark_ne_pos h
      · rcases List.mem_append.mp h with h | h
        · exact not_mem_map_bit _ (fun b => gMark_ne_bit b) _ h
        · exact gMark_ne_iend (List.mem_singleton.mp h)
  | nil => intro h; simp only [Val.enc, List.mem_singleton] at h; exact gMark_ne_nil h
  | cons a b iha ihb =>
      intro hmem
      simp only [Val.enc, List.mem_cons] at hmem
      rcases hmem with h | h
      · exact gMark_ne_cons h
      · exact (List.mem_append.mp h).elim iha ihb

theorem gPend_not_mem_enc (v : Val) : gPend ∉ v.enc := by
  induction v with
  | int z =>
      intro hmem
      simp only [Val.enc] at hmem
      rcases List.mem_cons.mp hmem with h | h
      · by_cases hz : z < 0
        · rw [if_pos hz] at h; exact gPend_ne_neg h
        · rw [if_neg hz] at h; exact gPend_ne_pos h
      · rcases List.mem_append.mp h with h | h
        · exact not_mem_map_bit _ (fun b => gPend_ne_bit b) _ h
        · exact gPend_ne_iend (List.mem_singleton.mp h)
  | nil => intro h; simp only [Val.enc, List.mem_singleton] at h; exact gPend_ne_nil h
  | cons a b iha ihb =>
      intro hmem
      simp only [Val.enc, List.mem_cons] at hmem
      rcases hmem with h | h
      · exact gPend_ne_cons h
      · exact (List.mem_append.mp h).elim iha ihb

/-- every value has a nonempty encoding -/
theorem one_le_vsz (v : Val) : 1 ≤ vsz v := by
  cases v with
  | int z => simp [vsz, Val.enc]
  | nil => simp [vsz, Val.enc]
  | cons x y => simp [vsz, Val.enc]

theorem gMark_not_mem_enc_rev (v : Val) : gMark ∉ v.enc.reverse :=
  fun h => gMark_not_mem_enc v (List.mem_reverse.mp h)

theorem gPend_not_mem_enc_rev (v : Val) : gPend ∉ v.enc.reverse :=
  fun h => gPend_not_mem_enc v (List.mem_reverse.mp h)

/-! ## `Function.update` simplification -/

@[simp] theorem stkFn_same (X : Stk → List Glyph) (k : Stk) (l : List Glyph) :
    Function.update X k l k = l := Function.update_self k l X

@[simp] theorem stkFn_ne (X : Stk → List Glyph) {k k' : Stk} (h : k ≠ k') (l : List Glyph) :
    Function.update X k' l k = X k := Function.update_of_ne h l X

@[simp] theorem regUpd_same (g : Reg → Glyph) (r : Reg) (c : Glyph) :
    Function.update g r c r = c := Function.update_self r c g

@[simp] theorem regUpd_ne (g : Reg → Glyph) {r r' : Reg} (h : r ≠ r') (c : Glyph) :
    Function.update g r' c r = g r := Function.update_of_ne h c g

@[simp] theorem headD_cons (a : Glyph) (l : List Glyph) :
    (a :: l).headD Glyph.eos = a := rfl

@[simp] theorem tail_cons (a : Glyph) (l : List Glyph) : (a :: l).tail = l := rfl

/-! ## `mvB`: move the buffer down to its boundary marker onto another stack -/

/-- body of the `mvB` loop -/
def mvBBody (c b : Stk) : Cmd :=
  .seq (seqs [.pop c rA])
    (seqs [.ite rA gMark (.set rLoopG Glyph.eos) (.push b rA)])

/-- move the glyphs above the boundary marker `gMark` from stack `c` to stack `b` (reversing) -/
def mvB (c b : Stk) : Cmd := seqs [.set rLoopG Glyph.cons, .loop rLoopG Glyph.cons (mvBBody c b)]

/-- `mvB` body with the boundary marker on top: stop. -/
theorem mvBBody_hit {main : Cmd} {c b : Stk} {g : Reg → Glyph} {X : Stk → List Glyph}
    {C B : List Glyph} (hbc : b ≠ c) (hc : X c = gMark :: C) (hb : X b = B) :
    ∃ s' n, Ev main (mvBBody c b) ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.stk c = C ∧ s'.stk b = B ∧ s'.reg rLoopG = Glyph.eos := by
  have h1 : Ev main (.pop c rA) ⟨g, X⟩
      ⟨Function.update g rA ((X c).headD Glyph.eos), Function.update X c (X c).tail⟩ 1 :=
    ev_pop' main c rA g X
  have h2 : Ev main (.ite rA gMark (.set rLoopG Glyph.eos) (.push b rA))
      ⟨Function.update g rA ((X c).headD Glyph.eos), Function.update X c (X c).tail⟩
      ⟨Function.update (Function.update g rA ((X c).headD Glyph.eos)) rLoopG Glyph.eos,
        Function.update X c (X c).tail⟩ 2 :=
    Ev.iteT (by simp [hc]) (ev_set' main rLoopG Glyph.eos _ _)
  have h3 : Ev main (mvBBody c b) ⟨g, X⟩
      ⟨Function.update (Function.update g rA ((X c).headD Glyph.eos)) rLoopG Glyph.eos,
        Function.update X c (X c).tail⟩ 3 := by
    unfold mvBBody
    simp only [seqs]
    exact Ev.seq' h1 h2 (by omega)
  refine ⟨_, _, h3, by omega, ?_, ?_, ?_⟩
  · simp [hc]
  · simp [hc, hb, Function.update_of_ne hbc]
  · simp [Function.update_of_ne (by decide : rLoopG ≠ rA)]

/-- `mvB` body on a non-marker glyph: move it to `b`. -/
theorem mvBBody_miss {main : Cmd} {c b : Stk} {g : Reg → Glyph} {X : Stk → List Glyph}
    {h : Glyph} {G C B : List Glyph} (hbc : b ≠ c) (hh : h ≠ gMark)
    (hc : X c = h :: G ++ gMark :: C) (hb : X b = B) (hreg : g rLoopG = Glyph.cons) :
    ∃ s' n, Ev main (mvBBody c b) ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.stk c = G ++ gMark :: C ∧ s'.stk b = h :: B ∧ s'.reg rLoopG = Glyph.cons := by
  have h1 : Ev main (.pop c rA) ⟨g, X⟩
      ⟨Function.update g rA ((X c).headD Glyph.eos), Function.update X c (X c).tail⟩ 1 :=
    ev_pop' main c rA g X
  have h2 : Ev main (.ite rA gMark (.set rLoopG Glyph.eos) (.push b rA))
      ⟨Function.update g rA ((X c).headD Glyph.eos), Function.update X c (X c).tail⟩
      ⟨Function.update g rA ((X c).headD Glyph.eos),
        Function.update (Function.update X c (X c).tail) b
          ((Function.update g rA ((X c).headD Glyph.eos)) rA ::
            Function.update X c (X c).tail b)⟩ 2 :=
    Ev.iteF (by simp [hc, hh]) (ev_push' main b rA _ _)
  have h3 : Ev main (mvBBody c b) ⟨g, X⟩
      ⟨Function.update g rA ((X c).headD Glyph.eos),
        Function.update (Function.update X c (X c).tail) b
          ((Function.update g rA ((X c).headD Glyph.eos)) rA ::
            Function.update X c (X c).tail b)⟩ 3 := by
    unfold mvBBody
    simp only [seqs]
    exact Ev.seq' h1 h2 (by omega)
  refine ⟨_, _, h3, by omega, ?_, ?_, ?_⟩
  · simp [hc, Function.update_of_ne hbc.symm]
  · simp [hc, hb, Function.update_of_ne hbc]
  · simp only [Function.update_of_ne (by decide : rLoopG ≠ rA)] at *
    simpa using hreg

/-- The `mvB` loop: consume `G` then the boundary marker. -/
theorem mvB_loop {main : Cmd} {c b : Stk} (hbc : b ≠ c) :
    ∀ (G : List Glyph) (C B : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      gMark ∉ G → g rLoopG = Glyph.cons → X c = G ++ gMark :: C → X b = B →
      ∃ s', loopRuns main rLoopG Glyph.cons (mvBBody c b) (G.length + 1) ⟨g, X⟩ s'
          (4 * (G.length + 1)) ∧
        s'.stk c = C ∧ s'.stk b = G.reverse ++ B ∧ s'.reg rLoopG = Glyph.eos := by
  intro G
  induction G with
  | nil =>
      intro C B g X _ hreg hc hb
      obtain ⟨s', n, hev, hn, hsc, hsb, hsr⟩ :=
        mvBBody_hit (main := main) (c := c) (b := b) (g := g) (X := X) (C := C) (B := B) hbc hc hb
      refine ⟨s', loopRuns.one hreg (hev.mono hn), ?_, ?_, hsr⟩
      · simpa using hsc
      · simpa using hsb
  | cons h G' ih =>
      intro C B g X hmem hreg hc hb
      have hh : h ≠ gMark := fun hh => hmem (hh ▸ List.mem_cons_self ..)
      have hmem' : gMark ∉ G' := fun hx => hmem (List.mem_cons_of_mem h hx)
      obtain ⟨s₁, n₁, hev₁, hn₁, hc₁, hb₁, hr₁⟩ :=
        mvBBody_miss (main := main) (c := c) (b := b) (g := g) (X := X) (h := h)
          (G := G') (C := C) (B := B) hbc hh hc hb hreg
      obtain ⟨s₂, hrun₂, hc₂, hb₂, hr₂⟩ :=
        ih C (h :: B) s₁.reg s₁.stk hmem' hr₁ hc₁ hb₁
      have hcat := loopRuns.concat (G'.length + 1) (loopRuns.one hreg (hev₁.mono hn₁)) hrun₂
      refine ⟨s₂, loopRuns.congr ?_ ?_ hcat, ?_, ?_, hr₂⟩
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega
      · exact hc₂
      · rw [hb₂]; simp

/-- The stacks `mvB` touches. -/
theorem cmdTouches_mvB (c b : Stk) : cmdTouches (mvB c b) = {c, b} := by
  simp only [mvB, mvBBody, seqs, cmdTouches]
  ext k; simp

/-- `mvB` as a whole. -/
theorem mvB_ev {main : Cmd} {c b : Stk} (hbc : b ≠ c) {G C B : List Glyph}
    {g : Reg → Glyph} {X : Stk → List Glyph}
    (hgM : gMark ∉ G) (hc : X c = G ++ gMark :: C) (hb : X b = B) :
    ∃ s' n, Ev main (mvB c b) ⟨g, X⟩ s' n ∧ n ≤ 4 * (G.length + 1) + 3 ∧
      s'.stk c = C ∧ s'.stk b = G.reverse ++ B ∧
      (∀ k, k ≠ c → k ≠ b → s'.stk k = X k) := by
  have hinit : Ev main (.set rLoopG Glyph.cons) ⟨g, X⟩
      ⟨Function.update g rLoopG Glyph.cons, X⟩ 1 := ev_set' main rLoopG Glyph.cons g X
  obtain ⟨s₁, hrun, hc₁, hb₁, hr₁⟩ :=
    mvB_loop (main := main) hbc G C B (Function.update g rLoopG Glyph.cons) X hgM (by simp) hc hb
  have hloop : Ev main (.loop rLoopG Glyph.cons (mvBBody c b))
      ⟨Function.update g rLoopG Glyph.cons, X⟩ s₁ (4 * (G.length + 1) + 1) :=
    loopRuns.eval hrun (by rw [hr₁]; decide)
  have hmain : Ev main (mvB c b) ⟨g, X⟩ s₁ (4 * (G.length + 1) + 2) := by
    unfold mvB
    simp only [seqs]
    exact Ev.seq' hinit hloop (by omega)
  refine ⟨s₁, _, hmain, by omega, hc₁, hb₁, ?_⟩
  intro k hkc hkb
  have hfr : s₁.stk k = (⟨g, X⟩ : State).stk k :=
    Ev.frame hmain (S := {c, b}) (by rw [cmdTouches_mvB]) (by simp [hkc, hkb])
  simpa using hfr

/-! ## `mvA`: move a value out, reversed, with a pending-subtree counter -/

/-- the common prefix of the `mvA` body: pop the top glyph of `a`, push it on `c` -/
def mvAPrefix (a c : Stk) : Cmd := seqs [.pop a rA, .push c rA]

/-- the pending-counter decrement test -/
def decStep (d : Stk) : Cmd :=
  seqs [.pop d rC, .peek d rD, .ite rD gPend (.set rLoopG Glyph.cons) (.set rLoopG Glyph.eos)]

/-- body of the `mvA` loop -/
def mvABody (a c d : Stk) : Cmd :=
  .seq (mvAPrefix a c)
    (seqs [.ite rA Glyph.cons (seqs [.set rD gPend, .push d rD])
      (.ite rA Glyph.nil (decStep d)
        (.ite rA Glyph.iend (decStep d) (.set rLoopG Glyph.cons)))])

/-- push the constant glyph `cst` on stack `k` (via register `rB`) -/
def pushConst (k : Stk) (cst : Glyph) : Cmd := seqs [.set rB cst, .push k rB]

/-- initialisation of `mvA`: flag, boundary marker on `c`, sentinel and one counter unit on `d` -/
def mvAInit (c d : Stk) : Cmd :=
  .seq (.set rLoopG Glyph.cons) (.seq (pushConst c gMark) (.seq (pushConst d gSent) (pushConst d gPend)))

/-- move the top value of stack `a` to stack `c`, reversed, leaving a boundary marker -/
def mvA (a c d : Stk) : Cmd :=
  .seq (mvAInit c d) (.seq (.loop rLoopG Glyph.cons (mvABody a c d)) (.pop d rC))

/-- move one value from `a` to `b` (normal order), buffering on `c`, counting on `d` -/
def mvVal (a b c d : Stk) : Cmd := .seq (mvA a c d) (mvB c b)

set_option maxHeartbeats 400000 in
theorem mvAPrefix_ev {main : Cmd} {a c : Stk} (hac : a ≠ c) {g : Reg → Glyph}
    {X : Stk → List Glyph} :
    ∃ s' n, Ev main (mvAPrefix a c) ⟨g, X⟩ s' n ∧ n ≤ 2 ∧
      s'.stk a = (X a).tail ∧
      s'.stk c = (X a).headD Glyph.eos :: Function.update X a (X a).tail c ∧
      (∀ k, k ≠ a → k ≠ c → s'.stk k = X k) ∧
      s'.reg rA = (X a).headD Glyph.eos ∧
      (∀ r, r ≠ rA → s'.reg r = g r) := by
  have h1 : Ev main (mvAPrefix a c) ⟨g, X⟩
      ⟨Function.update g rA ((X a).headD Glyph.eos),
        Function.update (Function.update X a (X a).tail) c
          ((Function.update g rA ((X a).headD Glyph.eos)) rA ::
            Function.update X a (X a).tail c)⟩ 2 := by
    unfold mvAPrefix
    simp only [seqs]
    exact Ev.seq' (ev_pop' main a rA g X) (ev_push' main c rA _ _) (show 1 + 1 ≤ 2 by omega)
  refine ⟨_, _, h1, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_of_ne hac, Function.update_of_ne hac.symm]
  · simp
  · intro k hka hkc
    simp [Function.update_of_ne hka, Function.update_of_ne hkc,
      Function.update_of_ne hka.symm, Function.update_of_ne hkc.symm]
  · simp
  · intro r hr
    simp [Function.update_of_ne hr]

set_option maxHeartbeats 800000 in
theorem decStep_last {main : Cmd} {d : Stk} {g : Reg → Glyph} {X : Stk → List Glyph}
    {D : List Glyph} (hd : X d = gPend :: gSent :: D) :
    ∃ s' n, Ev main (decStep d) ⟨g, X⟩ s' n ∧ n ≤ 4 ∧
      s'.stk d = gSent :: D ∧ s'.reg rLoopG = Glyph.eos ∧
      (∀ k, k ≠ d → s'.stk k = X k) := by
  have h1 : Ev main (decStep d) ⟨g, X⟩
      ⟨Function.update (Function.update (Function.update g rC ((X d).headD Glyph.eos)) rD
          ((Function.update X d (X d).tail d).headD Glyph.eos)) rLoopG Glyph.eos,
        Function.update X d (X d).tail⟩ 4 := by
    unfold decStep
    simp only [seqs]
    exact Ev.seq' (ev_pop' main d rC g X)
      (Ev.seq' (ev_peek' main d rD _ _)
        (Ev.iteF (by simp [hd]) (ev_set' main rLoopG Glyph.eos _ _))
        (show 1 + 2 ≤ 3 by omega)) (show 1 + 3 ≤ 4 by omega)
  refine ⟨_, _, h1, by omega, ?_, ?_, ?_⟩
  · simp only [stk_mk, Function.update_self, hd, tail_cons]
  · simp
  · intro k hk
    simp only [stk_mk, Function.update_of_ne hk]

set_option maxHeartbeats 800000 in
theorem decStep_more {main : Cmd} {d : Stk} {g : Reg → Glyph} {X : Stk → List Glyph}
    {D : List Glyph} (hd : X d = gPend :: gPend :: D) :
    ∃ s' n, Ev main (decStep d) ⟨g, X⟩ s' n ∧ n ≤ 4 ∧
      s'.stk d = gPend :: D ∧ s'.reg rLoopG = Glyph.cons ∧
      (∀ k, k ≠ d → s'.stk k = X k) := by
  have h1 : Ev main (decStep d) ⟨g, X⟩
      ⟨Function.update (Function.update (Function.update g rC ((X d).headD Glyph.eos)) rD
          ((Function.update X d (X d).tail d).headD Glyph.eos)) rLoopG Glyph.cons,
        Function.update X d (X d).tail⟩ 4 := by
    unfold decStep
    simp only [seqs]
    exact Ev.seq' (ev_pop' main d rC g X)
      (Ev.seq' (ev_peek' main d rD _ _)
        (Ev.iteT (by simp [hd]) (ev_set' main rLoopG Glyph.cons _ _))
        (show 1 + 2 ≤ 3 by omega)) (show 1 + 3 ≤ 4 by omega)
  refine ⟨_, _, h1, by omega, ?_, ?_, ?_⟩
  · simp only [stk_mk, Function.update_self, hd, tail_cons]
  · simp
  · intro k hk
    simp only [stk_mk, Function.update_of_ne hk]

set_option maxHeartbeats 800000 in
/-- an inert glyph (bits, signs): transfer it and continue -/
theorem mvABody_inert {main : Cmd} {a c d : Stk} (hac : a ≠ c) (had : a ≠ d) (hcd : c ≠ d)
    {g : Reg → Glyph} {X : Stk → List Glyph} {h : Glyph} {A C : List Glyph}
    (hh : NotStruct h) (ha : X a = h :: A) (hc : X c = C) :
    ∃ s' n, Ev main (mvABody a c d) ⟨g, X⟩ s' n ∧ n ≤ 6 ∧
      s'.stk a = A ∧ s'.stk c = h :: C ∧ s'.stk d = X d ∧ s'.reg rLoopG = Glyph.cons := by
  obtain ⟨s₁, n₁, h1, hn₁, ha₁, hc₁, hf₁, hr₁, hreg₁⟩ :=
    mvAPrefix_ev (main := main) hac (g := g) (X := X)
  have hca : s₁.stk a = A := by rw [ha₁, ha]; rfl
  have hcc : s₁.stk c = h :: C := by
    rw [hc₁, ha]
    simp only [headD_cons, Function.update_of_ne hac.symm, hc]
  have hcd₁ : s₁.stk d = X d := hf₁ d had.symm hcd.symm
  have h2 : Ev main (seqs [.ite rA Glyph.cons (seqs [.set rD gPend, .push d rD])
        (.ite rA Glyph.nil (decStep d)
          (.ite rA Glyph.iend (decStep d) (.set rLoopG Glyph.cons)))])
      ⟨s₁.reg, s₁.stk⟩
      ⟨Function.update s₁.reg rLoopG Glyph.cons, s₁.stk⟩ 4 := by
    simp only [seqs]
    refine Ev.iteF (by simp [hr₁, ha, hh.1]) (Ev.iteF (by simp [hr₁, ha, hh.2.1])
      (Ev.iteF (by simp [hr₁, ha, hh.2.2]) ?_))
    simpa using ev_set' main rLoopG Glyph.cons s₁.reg s₁.stk
  have h3 : Ev main (mvABody a c d) ⟨g, X⟩
      ⟨Function.update s₁.reg rLoopG Glyph.cons, s₁.stk⟩ 6 := by
    unfold mvABody
    exact Ev.seq' h1 h2 (by omega)
  refine ⟨_, _, h3, by omega, ?_, ?_, ?_, ?_⟩
  · simp only [stk_mk]; exact hca
  · simp only [stk_mk]; exact hcc
  · simp only [stk_mk]; exact hcd₁
  · simp

set_option maxHeartbeats 800000 in
/-- `cons` glyph: push a pending marker and continue -/
theorem mvABody_cons {main : Cmd} {a c d : Stk} (hac : a ≠ c) (had : a ≠ d) (hcd : c ≠ d)
    {g : Reg → Glyph} {X : Stk → List Glyph} {A C : List Glyph} (hreg : g rLoopG = Glyph.cons)
    (ha : X a = Glyph.cons :: A) (hc : X c = C) :
    ∃ s' n, Ev main (mvABody a c d) ⟨g, X⟩ s' n ∧ n ≤ 5 ∧
      s'.stk a = A ∧ s'.stk c = Glyph.cons :: C ∧ s'.stk d = gPend :: X d ∧
      s'.reg rLoopG = Glyph.cons := by
  obtain ⟨s₁, n₁, h1, hn₁, ha₁, hc₁, hf₁, hr₁, hreg₁⟩ :=
    mvAPrefix_ev (main := main) hac (g := g) (X := X)
  have hca : s₁.stk a = A := by rw [ha₁, ha]; rfl
  have hcc : s₁.stk c = Glyph.cons :: C := by
    rw [hc₁, ha]
    simp only [headD_cons, Function.update_of_ne hac.symm, hc]
  have hcd₁ : s₁.stk d = X d := hf₁ d had.symm hcd.symm
  have h2 : Ev main (seqs [.ite rA Glyph.cons (seqs [.set rD gPend, .push d rD])
        (.ite rA Glyph.nil (decStep d)
          (.ite rA Glyph.iend (decStep d) (.set rLoopG Glyph.cons)))])
      ⟨s₁.reg, s₁.stk⟩
      ⟨Function.update s₁.reg rD gPend, Function.update s₁.stk d (gPend :: s₁.stk d)⟩ 3 := by
    simp only [seqs]
    refine Ev.iteT (by simp [hr₁, ha]) ?_
    exact Ev.seq' (ev_set' main rD gPend s₁.reg s₁.stk) (ev_push' main d rD _ _)
      (show 1 + 1 ≤ 2 by omega)
  have h3 : Ev main (mvABody a c d) ⟨g, X⟩
      ⟨Function.update s₁.reg rD gPend, Function.update s₁.stk d (gPend :: s₁.stk d)⟩ 5 := by
    unfold mvABody
    exact Ev.seq' h1 h2 (by omega)
  refine ⟨_, _, h3, by omega, ?_, ?_, ?_, ?_⟩
  · simp only [stk_mk, Function.update_of_ne had]; exact hca
  · simp only [stk_mk, Function.update_of_ne hcd]; exact hcc
  · simp only [stk_mk, Function.update_self]; rw [hcd₁]
  · simp only [stk_mk, Function.update_of_ne (by decide : rLoopG ≠ rD)]
    rw [hreg₁ rLoopG (by decide : rLoopG ≠ rA)]; exact hreg

set_option maxHeartbeats 800000 in
/-- terminator glyph (`nil`/`iend`) with a single pending marker: stop -/
theorem mvABody_term_last {main : Cmd} {a c d : Stk} (hac : a ≠ c) (had : a ≠ d) (hcd : c ≠ d)
    {g : Reg → Glyph} {X : Stk → List Glyph} {h : Glyph} {A C D : List Glyph}
    (hh : h = Glyph.nil ∨ h = Glyph.iend) (ha : X a = h :: A) (hc : X c = C)
    (hd : X d = gPend :: gSent :: D) :
    ∃ s' n, Ev main (mvABody a c d) ⟨g, X⟩ s' n ∧ n ≤ 9 ∧
      s'.stk a = A ∧ s'.stk c = h :: C ∧ s'.stk d = gSent :: D ∧
      s'.reg rLoopG = Glyph.eos := by
  obtain ⟨s₁, n₁, h1, hn₁, ha₁, hc₁, hf₁, hr₁, hreg₁⟩ :=
    mvAPrefix_ev (main := main) hac (g := g) (X := X)
  have hca : s₁.stk a = A := by rw [ha₁, ha]; rfl
  have hcc : s₁.stk c = h :: C := by
    rw [hc₁, ha]
    simp only [headD_cons, Function.update_of_ne hac.symm, hc]
  have hcd₁ : s₁.stk d = gPend :: gSent :: D := by
    rw [hf₁ d had.symm hcd.symm, hd]
  obtain ⟨s₂, n₂, h2, hn₂, hd₂, hr₂, hf₂⟩ := decStep_last (main := main) (d := d)
    (g := s₁.reg) (X := s₁.stk) (D := D) hcd₁
  have h3 : Ev main (seqs [.ite rA Glyph.cons (seqs [.set rD gPend, .push d rD])
        (.ite rA Glyph.nil (decStep d)
          (.ite rA Glyph.iend (decStep d) (.set rLoopG Glyph.cons)))])
      ⟨s₁.reg, s₁.stk⟩ s₂ (n₂ + 3) := by
    show Ev main (.ite rA Glyph.cons (seqs [.set rD gPend, .push d rD])
        (.ite rA Glyph.nil (decStep d)
          (.ite rA Glyph.iend (decStep d) (.set rLoopG Glyph.cons)))) _ _ _
    have hn : h ≠ Glyph.cons := by rcases hh with rfl | rfl <;> decide
    refine Ev.iteF (by simp [hr₁, ha, hn]) ?_
    rcases hh with rfl | rfl
    · exact Ev.iteT (by simp [hr₁, ha]) (h2.mono (by omega))
    · exact Ev.iteF (by simp [hr₁, ha]) (Ev.iteT (by simp [hr₁, ha]) (h2.mono (by omega)))
  have h4 : Ev main (mvABody a c d) ⟨g, X⟩ s₂ (n₂ + 5) := by
    unfold mvABody
    exact Ev.seq' h1 h3 (by omega)
  refine ⟨_, _, h4.mono (by omega : n₂ + 5 ≤ 9), by omega, ?_, ?_, ?_, ?_⟩
  · rw [hf₂ a had, hca]
  · rw [hf₂ c hcd, hcc]
  · exact hd₂
  · exact hr₂

set_option maxHeartbeats 800000 in
/-- terminator glyph (`nil`/`iend`) with two pending markers: continue -/
theorem mvABody_term_more {main : Cmd} {a c d : Stk} (hac : a ≠ c) (had : a ≠ d) (hcd : c ≠ d)
    {g : Reg → Glyph} {X : Stk → List Glyph} {h : Glyph} {A C D : List Glyph}
    (hh : h = Glyph.nil ∨ h = Glyph.iend) (ha : X a = h :: A) (hc : X c = C)
    (hd : X d = gPend :: gPend :: D) :
    ∃ s' n, Ev main (mvABody a c d) ⟨g, X⟩ s' n ∧ n ≤ 9 ∧
      s'.stk a = A ∧ s'.stk c = h :: C ∧ s'.stk d = gPend :: D ∧
      s'.reg rLoopG = Glyph.cons := by
  obtain ⟨s₁, n₁, h1, hn₁, ha₁, hc₁, hf₁, hr₁, hreg₁⟩ :=
    mvAPrefix_ev (main := main) hac (g := g) (X := X)
  have hca : s₁.stk a = A := by rw [ha₁, ha]; rfl
  have hcc : s₁.stk c = h :: C := by
    rw [hc₁, ha]
    simp only [headD_cons, Function.update_of_ne hac.symm, hc]
  have hcd₁ : s₁.stk d = gPend :: gPend :: D := by
    rw [hf₁ d had.symm hcd.symm, hd]
  obtain ⟨s₂, n₂, h2, hn₂, hd₂, hr₂, hf₂⟩ := decStep_more (main := main) (d := d)
    (g := s₁.reg) (X := s₁.stk) (D := D) hcd₁
  have h3 : Ev main (seqs [.ite rA Glyph.cons (seqs [.set rD gPend, .push d rD])
        (.ite rA Glyph.nil (decStep d)
          (.ite rA Glyph.iend (decStep d) (.set rLoopG Glyph.cons)))])
      ⟨s₁.reg, s₁.stk⟩ s₂ (n₂ + 3) := by
    show Ev main (.ite rA Glyph.cons (seqs [.set rD gPend, .push d rD])
        (.ite rA Glyph.nil (decStep d)
          (.ite rA Glyph.iend (decStep d) (.set rLoopG Glyph.cons)))) _ _ _
    have hn : h ≠ Glyph.cons := by rcases hh with rfl | rfl <;> decide
    refine Ev.iteF (by simp [hr₁, ha, hn]) ?_
    rcases hh with rfl | rfl
    · exact Ev.iteT (by simp [hr₁, ha]) (h2.mono (by omega))
    · exact Ev.iteF (by simp [hr₁, ha]) (Ev.iteT (by simp [hr₁, ha]) (h2.mono (by omega)))
  have h4 : Ev main (mvABody a c d) ⟨g, X⟩ s₂ (n₂ + 5) := by
    unfold mvABody
    exact Ev.seq' h1 h3 (by omega)
  refine ⟨_, _, h4.mono (by omega : n₂ + 5 ≤ 9), by omega, ?_, ?_, ?_, ?_⟩
  · rw [hf₂ a had, hca]
  · rw [hf₂ c hcd, hcc]
  · exact hd₂
  · exact hr₂

/-! ## The `mvA` loop -/

set_option maxHeartbeats 1600000 in
/-- the `mvA` loop on a list of inert glyphs followed by a terminator.  `P` is the list of pending
counter markers (`gPend`s) above the sentinel; the terminator consumes one. -/
theorem mvA_loop_inert {main : Cmd} {a c d : Stk} (hac : a ≠ c) (had : a ≠ d) (hcd : c ≠ d)
    (t : Glyph) (ht : t = Glyph.nil ∨ t = Glyph.iend) :
    ∀ (G : List Glyph) (P : List Glyph) (A C D : List Glyph) (g : Reg → Glyph)
      (X : Stk → List Glyph),
      P ≠ [] → (∀ x ∈ P, x = gPend) → (∀ h ∈ G, NotStruct h) → g rLoopG = Glyph.cons →
      X a = G ++ t :: A → X c = C → X d = P ++ gSent :: D →
      ∃ s', loopRuns main rLoopG Glyph.cons (mvABody a c d) (G.length + 1) ⟨g, X⟩ s'
          (10 * (G.length + 1)) ∧
        s'.stk a = A ∧ s'.stk c = t :: G.reverse ++ C ∧
        s'.stk d = P.tail ++ gSent :: D ∧
        s'.reg rLoopG = (if P.tail = [] then Glyph.eos else Glyph.cons) := by
  intro G
  induction G with
  | nil =>
      intro P A C D g X hP hPg _ hreg ha hc hd
      rw [List.nil_append] at ha
      cases P with
      | nil => exact absurd rfl hP
      | cons p P' =>
        have hp : p = gPend := hPg p (List.mem_cons_self ..)
        subst hp
        rw [List.cons_append] at hd
        cases P' with
        | nil =>
          rw [List.nil_append] at hd
          obtain ⟨s', n, hev, hn, haf, hcf, hdf, hrf⟩ :=
            mvABody_term_last (main := main) hac had hcd ht ha hc hd
          refine ⟨s', loopRuns.one hreg (hev.mono hn), ?_, ?_, ?_, ?_⟩
          · exact haf
          · simpa using hcf
          · simpa using hdf
          · rw [hrf]; simp
        | cons p' P'' =>
          have hp' : p' = gPend := hPg p' (by simp)
          subst hp'
          rw [List.cons_append] at hd
          obtain ⟨s', n, hev, hn, haf, hcf, hdf, hrf⟩ :=
            mvABody_term_more (main := main) hac had hcd ht ha hc hd
          refine ⟨s', loopRuns.one hreg (hev.mono hn), ?_, ?_, ?_, ?_⟩
          · exact haf
          · simpa using hcf
          · simpa using hdf
          · rw [hrf]; simp
  | cons h G' ih =>
      intro P A C D g X hP hPg hG hreg ha hc hd
      have hh : NotStruct h := hG h (List.mem_cons_self ..)
      have hG' : ∀ x ∈ G', NotStruct x := fun x hx => hG x (List.mem_cons_of_mem h hx)
      obtain ⟨s₁, n₁, hev₁, hn₁, ha₁, hc₁, hd₁, hr₁⟩ :=
        mvABody_inert (main := main) hac had hcd (g := g) (X := X) (h := h) (A := G' ++ t :: A)
          (C := C) hh ha hc
      have hd₁' : s₁.stk d = P ++ gSent :: D := by rw [hd₁, hd]
      obtain ⟨s₂, hrun₂, ha₂, hc₂, hd₂, hr₂⟩ :=
        ih P A (h :: C) D s₁.reg s₁.stk hP hPg hG' hr₁ ha₁ hc₁ hd₁'
      have hev₁' : Ev main (mvABody a c d) ⟨g, X⟩ s₁ 6 := hev₁.mono hn₁
      have hcat := loopRuns.concat (G'.length + 1) (loopRuns.one hreg hev₁') hrun₂
      refine ⟨s₂, loopRuns.cast (show 1 + (G'.length + 1) = (h :: G').length + 1 by
          simp only [List.length_cons]; omega)
        (loopRuns.mono (show 1 ≤ 1 + (G'.length + 1) by omega) hcat
          (show 6 + 1 + 10 * (G'.length + 1) ≤ 10 * ((h :: G').length + 1) by
            simp only [List.length_cons]; omega)), ?_, ?_, ?_, hr₂⟩
      · exact ha₂
      · rw [hc₂]
        simp only [List.reverse_cons, List.cons_append, List.append_assoc, List.nil_append]
      · exact hd₂

set_option maxHeartbeats 1600000 in
/-- the `mvA` loop on one value -/
theorem mvA_loop_val {main : Cmd} {a c d : Stk} (hac : a ≠ c) (had : a ≠ d) (hcd : c ≠ d) :
    ∀ (v : Val) (P : List Glyph) (A C D : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      P ≠ [] → (∀ x ∈ P, x = gPend) → g rLoopG = Glyph.cons →
      X a = v.enc ++ A → X c = C → X d = P ++ gSent :: D →
      ∃ s', loopRuns main rLoopG Glyph.cons (mvABody a c d) (vsz v) ⟨g, X⟩ s' (10 * vsz v) ∧
        s'.stk a = A ∧ s'.stk c = v.enc.reverse ++ C ∧
        s'.stk d = P.tail ++ gSent :: D ∧
        s'.reg rLoopG = (if P.tail = [] then Glyph.eos else Glyph.cons) := by
  intro v
  induction v with
  | int z =>
      intro P A C D g X hP hPg hreg ha hc hd
      have hG : ∀ h ∈ [if z < 0 then Glyph.neg else Glyph.pos] ++ (encodeNat z.natAbs).map Glyph.bit,
          NotStruct h := by
        intro h hh
        rcases List.mem_append.mp hh with h' | h'
        · rw [List.mem_singleton] at h'; subst h'; exact notStruct_sign z
        · exact notStruct_map_bit h h'
      have ha' : X a = ([if z < 0 then Glyph.neg else Glyph.pos] ++
            (encodeNat z.natAbs).map Glyph.bit) ++ Glyph.iend :: A := by
        rw [ha]
        simp only [Val.enc, List.cons_append, List.append_assoc, List.nil_append]
      obtain ⟨s', hrun, ha', hc', hd', hr'⟩ :=
        mvA_loop_inert (main := main) hac had hcd Glyph.iend (Or.inr rfl)
          ([if z < 0 then Glyph.neg else Glyph.pos] ++ (encodeNat z.natAbs).map Glyph.bit)
          P A C D g X hP hPg hG hreg ha' hc hd
      have hcnt : ([if z < 0 then Glyph.neg else Glyph.pos] ++
          (encodeNat z.natAbs).map Glyph.bit).length + 1 = vsz (Val.int z) := by
        simp only [vsz, Val.enc, List.length_append, List.length_cons, List.length_map,
          List.length_singleton, List.length_nil]
        omega
      refine ⟨s', loopRuns.congr hcnt (by rw [hcnt]) hrun, ha', ?_, hd', hr'⟩
      · rw [hc']
        simp only [vsz, Val.enc, List.cons_append, List.append_assoc, List.nil_append,
          List.reverse_append, List.reverse_cons, List.append_nil, List.reverse_nil]
  | nil =>
      intro P A C D g X hP hPg hreg ha hc hd
      have ha' : X a = ([] : List Glyph) ++ Glyph.nil :: A := by simpa [Val.enc] using ha
      obtain ⟨s', hrun, ha', hc', hd', hr'⟩ :=
        mvA_loop_inert (main := main) hac had hcd Glyph.nil (Or.inl rfl) [] P A C D g X
          hP hPg (by simp) hreg ha' hc hd
      have hcnt : ([] : List Glyph).length + 1 = vsz (Val.nil) := by simp [vsz, Val.enc]
      refine ⟨s', loopRuns.congr hcnt (by rw [hcnt]) hrun, ha', ?_, hd', hr'⟩
      · rw [hc']; simp [Val.enc]
  | cons x y ihx ihy =>
      intro P A C D g X hP hPg hreg ha hc hd
      have ha1 : X a = Glyph.cons :: (x.enc ++ y.enc ++ A) := by rw [ha]; rfl
      obtain ⟨s₁, n₁, hev₁, hn₁, ha₁, hc₁, hd₁, hr₁⟩ :=
        mvABody_cons (main := main) hac had hcd (g := g) (X := X) (A := x.enc ++ y.enc ++ A)
          (C := C) hreg ha1 hc
      have hd₁' : s₁.stk d = (gPend :: P) ++ gSent :: D := by
        rw [hd₁, hd]
        rfl
      have hP₁ : (gPend :: P) ≠ [] := fun h => List.cons_ne_nil gPend P h
      have hPg₁ : ∀ x ∈ gPend :: P, x = gPend := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact hPg x hx
      have ha₁' : s₁.stk a = x.enc ++ (y.enc ++ A) := by
        rw [ha₁]
        simp only [List.append_assoc]
      obtain ⟨s₂, hrun₂, ha₂, hc₂, hd₂, hr₂⟩ :=
        ihx (gPend :: P) (y.enc ++ A) (Glyph.cons :: C) D s₁.reg s₁.stk hP₁ hPg₁ hr₁ ha₁' hc₁ hd₁'
      have hd₂' : s₂.stk d = P ++ gSent :: D := hd₂
      have hr₂' : s₂.reg rLoopG = Glyph.cons := by
        rw [hr₂, if_neg (by simpa using hP)]
      obtain ⟨s₃, hrun₃, ha₃, hc₃, hd₃, hr₃⟩ :=
        ihy P A (x.enc.reverse ++ Glyph.cons :: C) D s₂.reg s₂.stk hP hPg hr₂' ha₂ hc₂ hd₂'
      have hev₁' : Ev main (mvABody a c d) ⟨g, X⟩ s₁ 5 := hev₁.mono hn₁
      have hcat := loopRuns.concat (vsz x + vsz y)
        (loopRuns.one hreg hev₁') (loopRuns.concat (vsz y) hrun₂ hrun₃)
      refine ⟨s₃, loopRuns.cast (show 1 + (vsz x + vsz y) = vsz (Val.cons x y) by
          simp only [vsz, Val.enc, List.length_cons, List.length_append]; omega)
        (loopRuns.mono (show 1 ≤ 1 + (vsz x + vsz y) by omega) hcat
          (show 5 + 1 + (10 * vsz x + 10 * vsz y) ≤ 10 * vsz (Val.cons x y) by
            simp only [vsz, Val.enc, List.length_cons, List.length_append]; omega)), ?_, ?_, ?_, ?_⟩
      · exact ha₃
      · simpa only [Val.enc, List.reverse_append, List.reverse_cons, List.cons_append,
          List.append_assoc, List.nil_append] using hc₃
      · exact hd₃
      · exact hr₃

set_option maxHeartbeats 400000 in
/-- push a constant glyph with the aid of a register -/
theorem pushConst_ev {main : Cmd} {k : Stk} {cst : Glyph} {g : Reg → Glyph}
    {X : Stk → List Glyph} :
    ∃ s' n, Ev main (pushConst k cst) ⟨g, X⟩ s' n ∧ n ≤ 2 ∧
      s'.stk k = cst :: X k ∧ (∀ k', k' ≠ k → s'.stk k' = X k') ∧ s'.reg rB = cst ∧
      (∀ r, r ≠ rB → s'.reg r = g r) := by
  have h1 : Ev main (pushConst k cst) ⟨g, X⟩
      ⟨Function.update g rB cst, Function.update X k (cst :: X k)⟩ 2 := by
    unfold pushConst
    simp only [seqs]
    exact Ev.seq' (ev_set' main rB cst g X) (ev_push' main k rB _ _)
      (show 1 + 1 ≤ 2 by omega)
  refine ⟨_, _, h1, by omega, ?_, ?_, ?_, ?_⟩
  · simp
  · intro k' hk
    simp [Function.update_of_ne hk]
  · simp
  · intro r hr
    simp [Function.update_of_ne hr]

set_option maxHeartbeats 800000 in
/-- the initialisation of `mvA` -/
theorem mvA_init_ev {main : Cmd} {c d : Stk} (hcd : c ≠ d) {g : Reg → Glyph}
    {X : Stk → List Glyph} :
    ∃ s' n, Ev main (mvAInit c d) ⟨g, X⟩ s' n ∧ n ≤ 8 ∧
      s'.stk c = gMark :: X c ∧ s'.stk d = gPend :: gSent :: X d ∧
      (∀ k, k ≠ c → k ≠ d → s'.stk k = X k) ∧
      s'.reg rLoopG = Glyph.cons ∧ s'.reg rB = gPend := by
  have h0 : Ev main (.set rLoopG Glyph.cons) ⟨g, X⟩
      ⟨Function.update g rLoopG Glyph.cons, X⟩ 1 := ev_set' main rLoopG Glyph.cons g X
  obtain ⟨s₁, n₁, h1, hn₁, hk₁, hf₁, hr₁, hg₁⟩ :=
    pushConst_ev (main := main) (k := c) (cst := gMark) (g := Function.update g rLoopG Glyph.cons) (X := X)
  obtain ⟨s₂, n₂, h2, hn₂, hk₂, hf₂, hr₂, hg₂⟩ :=
    pushConst_ev (main := main) (k := d) (cst := gSent) (g := s₁.reg) (X := s₁.stk)
  obtain ⟨s₃, n₃, h3, hn₃, hk₃, hf₃, hr₃, hg₃⟩ :=
    pushConst_ev (main := main) (k := d) (cst := gPend) (g := s₂.reg) (X := s₂.stk)
  have hmain : Ev main (mvAInit c d) ⟨g, X⟩ s₃ 7 := by
    unfold mvAInit
    exact Ev.seq' h0 (Ev.seq' h1 (Ev.seq' h2 h3 (show n₂ + n₃ ≤ 4 by omega))
      (show n₁ + 4 ≤ 6 by omega)) (show 1 + 6 ≤ 7 by omega)
  refine ⟨s₃, _, hmain, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf₃ c hcd, hf₂ c hcd, hk₁]
  · rw [hk₃, hk₂, hf₁ d hcd.symm]
  · intro k hkc hkd
    rw [hf₃ k hkd, hf₂ k hkd, hf₁ k hkc]
  · rw [hg₃ rLoopG (by decide : rLoopG ≠ rB), hg₂ rLoopG (by decide : rLoopG ≠ rB),
      hg₁ rLoopG (by decide : rLoopG ≠ rB)]
    simp
  · exact hr₃

/-- the stacks `mvA` touches. -/
theorem cmdTouches_mvA (a c d : Stk) : cmdTouches (mvA a c d) = {a, c, d} := by
  simp only [mvA, mvAInit, pushConst, mvABody, mvAPrefix, decStep, seqs, cmdTouches]
  ext k; simp

set_option maxHeartbeats 1600000 in
/-- `mvA` as a whole. -/
theorem mvA_ev {main : Cmd} {a c d : Stk} (hac : a ≠ c) (had : a ≠ d) (hcd : c ≠ d)
    (v : Val) (A C D : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph)
    (ha : X a = v.enc ++ A) (hc : X c = C) (hd : X d = D) :
    ∃ s' n, Ev main (mvA a c d) ⟨g, X⟩ s' n ∧ n ≤ 10 * vsz v + 10 ∧
      s'.stk a = A ∧ s'.stk c = v.enc.reverse ++ gMark :: C ∧ s'.stk d = D ∧
      (∀ k, k ≠ a → k ≠ c → k ≠ d → s'.stk k = X k) := by
  obtain ⟨s₀, n₀, h0, hn₀, hc₀, hd₀, hf₀, hrl₀, hrb₀⟩ :=
    mvA_init_ev (main := main) hcd (g := g) (X := X)
  have ha₀ : s₀.stk a = v.enc ++ A := by rw [hf₀ a hac had]; exact ha
  have hd₀' : s₀.stk d = [gPend] ++ gSent :: D := by rw [hd₀, hd]; simp
  obtain ⟨s₁, hrun, ha₁, hc₁, hd₁, hr₁⟩ :=
    mvA_loop_val (main := main) hac had hcd v [gPend] A (s₀.stk c) D s₀.reg s₀.stk
      (by simp) (by simp) hrl₀ ha₀ rfl hd₀'
  have hd₁' : s₁.stk d = gSent :: D := by rw [hd₁]; rfl
  have hloop : Ev main (.loop rLoopG Glyph.cons (mvABody a c d)) s₀ s₁ (10 * vsz v + 1) :=
    loopRuns.eval hrun (by rw [hr₁]; decide)
  have hpop : Ev main (.pop d rC) s₁
      ⟨Function.update s₁.reg rC ((s₁.stk d).headD Glyph.eos),
        Function.update s₁.stk d (s₁.stk d).tail⟩ 1 :=
    ev_pop' main d rC s₁.reg s₁.stk
  have hmain : Ev main (mvA a c d) ⟨g, X⟩
      ⟨Function.update s₁.reg rC ((s₁.stk d).headD Glyph.eos),
        Function.update s₁.stk d (s₁.stk d).tail⟩ (10 * vsz v + 10) := by
    unfold mvA
    exact Ev.seq' h0 (Ev.seq' hloop hpop
      (show 10 * vsz v + 1 + 1 ≤ 10 * vsz v + 2 by omega))
      (show n₀ + (10 * vsz v + 2) ≤ 10 * vsz v + 10 by omega)
  refine ⟨⟨Function.update s₁.reg rC ((s₁.stk d).headD Glyph.eos),
      Function.update s₁.stk d (s₁.stk d).tail⟩, _, hmain, by omega, ?_, ?_, ?_, ?_⟩
  · simp only [stk_mk, Function.update_of_ne had]; exact ha₁
  · simp only [stk_mk, Function.update_of_ne hcd, hc₁, hc₀, hc]
  · simp only [stk_mk, Function.update_self, hd₁', tail_cons]
  · intro k hka hkc hkd
    have hfr : (⟨Function.update s₁.reg rC ((s₁.stk d).headD Glyph.eos),
        Function.update s₁.stk d (s₁.stk d).tail⟩ : State).stk k = (⟨g, X⟩ : State).stk k :=
      Ev.frame hmain (S := {a, c, d}) (by rw [cmdTouches_mvA]) (by simp [hka, hkc, hkd])
    simpa using hfr

set_option maxHeartbeats 1600000 in
/-- `mvVal` moves one value from stack `a` to stack `b` (normal order), touching only `a`, `b`, `c`,
`d`, leaving everything else alone. -/
theorem mvVal_ev {main : Cmd} {a b c d : Stk} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {g : Reg → Glyph} {X : Stk → List Glyph}
    {v : Val} {A B : List Glyph} (ha : X a = v.enc ++ A) (hb : X b = B) :
    ∃ s' n, Ev main (mvVal a b c d) ⟨g, X⟩ s' n ∧ n ≤ 16 * (vsz v + 1) ∧
      s'.stk a = A ∧ s'.stk b = v.enc ++ B ∧
      (∀ k, k ≠ a → k ≠ b → k ≠ c → k ≠ d → s'.stk k = X k) := by
  obtain ⟨s₁, n₁, h1, hn₁, ha₁, hc₁, hd₁, hf₁⟩ :=
    mvA_ev (main := main) hac had hcd v A (X c) (X d) g X ha rfl rfl
  have hb₁ : s₁.stk b = B := by rw [hf₁ b hab.symm hbc hbd, hb]
  obtain ⟨s₂, n₂, h2, hn₂, hc₂, hb₂, hf₂⟩ :=
    mvB_ev (main := main) hbc (G := v.enc.reverse) (C := X c) (B := B)
      (gMark_not_mem_enc_rev v) hc₁ hb₁
  have hlen : (v.enc.reverse).length = vsz v := by simp [vsz]
  have hn₂' : n₂ ≤ 4 * (vsz v + 1) + 3 := by
    rw [← hlen]; exact hn₂
  have hmain : Ev main (mvVal a b c d) ⟨g, X⟩ s₂ (n₁ + n₂) := by
    unfold mvVal
    exact Ev.seq h1 h2
  have hcost : n₁ + n₂ ≤ 16 * (vsz v + 1) := by
    have h₁ : n₁ ≤ 10 * vsz v + 10 := hn₁
    have h₂ : n₂ ≤ 4 * (vsz v + 1) + 3 := hn₂'
    have hv := one_le_vsz v
    omega
  refine ⟨s₂, _, hmain, hcost, ?_, ?_, ?_⟩
  · rw [hf₂ a hac hab]; exact ha₁
  · rw [hb₂, List.reverse_reverse]
  · intro k hka hkb hkc hkd
    rw [hf₂ k hkc hkb]
    exact hf₁ k hka hkc hkd

end Work.Layout
