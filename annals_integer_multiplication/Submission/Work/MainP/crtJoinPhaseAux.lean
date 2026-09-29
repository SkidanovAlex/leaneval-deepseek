import Mathlib
import Submission.Work.MainP.crtJoinDefs

/-!
# Auxiliary definitions for `joinPhase` (interleaving phase of `crtJoinWord`)

`Work.MainP.joinPhase` walks the two buffers built by `consumeList` (stack 2 = the reversed
`x`-blocks, stack 3 = the reversed `w`-blocks), counted by the unary regions on stacks 6 and 7,
and pushes, for every element pair, `cons cons wᵢ xᵢ` onto stack 0 -- in the reverse of the order in
which the pairs are consumed, because every round *pushes* its output.

The definitions here name the content of the four stacks involved, as functions of the list `Ps` of
the pairs in *consumption order* (the first pair of `Ps` is the first one processed, i.e. the last
element of the list), so that the loop invariant of `joinLoop` is a simple statement about a
*remaining* list:
* `bufGs Ps` / `bufWs Ps`: content of stacks 2 / 3 before the loop;
* `cntGs Ps` / `cntWs Ps`: content of the unary count regions on stacks 6 / 7;
* `outsOf Ps`: what the loop pushes onto stack 0 (accumulated *below* the output of the remaining
  rounds, hence the reversal);
* `jcostL Ps` / `jcost Ps`: the exact cost of the bare loop / of `joinLoop`.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

/-! ## Definitions -/

/-- One round's output: two `cons` glyphs, then the `w`-block, then the `x`-block. -/
def outPair (w x : List Glyph) : List Glyph := [Glyph.cons, Glyph.cons] ++ w ++ x

/-- Output of one processed pair `(x, w)`. -/
def Pm (p : List Glyph × List Glyph) : List Glyph := outPair p.2 p.1

/-- Content of stack 2 before the interleaving loop: the reverse of the `x`-block of each pair, in
consumption order. -/
def bufGs (Ps : List (List Glyph × List Glyph)) : List Glyph :=
  (Ps.map fun p => p.1.reverse).flatten

/-- Content of stack 3 before the interleaving loop. -/
def bufWs (Ps : List (List Glyph × List Glyph)) : List Glyph :=
  (Ps.map fun p => p.2.reverse).flatten

/-- Unary block of one element: one token per glyph, then the separator. -/
def blkCnt (g : List Glyph) : List Glyph := List.replicate g.length jtok ++ [jdelim]

/-- Content of the count region of stack 6: one unary block per pair, in consumption order. -/
def cntGs (Ps : List (List Glyph × List Glyph)) : List Glyph :=
  (Ps.map fun p => blkCnt p.1).flatten

/-- Content of the count region of stack 7. -/
def cntWs (Ps : List (List Glyph × List Glyph)) : List Glyph :=
  (Ps.map fun p => blkCnt p.2).flatten

/-- What the interleaving loop pushes onto stack 0 from `Ps`: the rounds are processed in the order
of `Ps` but pushed, so the output of the first round ends up *at the bottom*. -/
def outsOf (Ps : List (List Glyph × List Glyph)) : List Glyph := (Ps.reverse.map Pm).flatten

/-- Cost of the bare interleaving loop `Cmd.loop 1 jtok joinBody` on `Ps`. -/
def jcostL (Ps : List (List Glyph × List Glyph)) : ℕ :=
  5 * (Ps.map fun p => p.1.length + p.2.length).sum + 10 * Ps.length + 1

/-- Cost of the interleaving loop `joinLoop` (which starts with one `peek`) on `Ps`. -/
def jcost (Ps : List (List Glyph × List Glyph)) : ℕ := jcostL Ps + 1

/-! ## Elementary facts -/

@[simp] theorem outPair_def (w x : List Glyph) : outPair w x = [Glyph.cons, Glyph.cons] ++ w ++ x := rfl

@[simp] theorem Pm_def (p : List Glyph × List Glyph) : Pm p = outPair p.2 p.1 := rfl

@[simp] theorem blkCnt_def (g : List Glyph) : blkCnt g = List.replicate g.length jtok ++ [jdelim] := rfl

@[simp] theorem bufGs_nil : bufGs [] = [] := rfl
@[simp] theorem bufWs_nil : bufWs [] = [] := rfl
@[simp] theorem cntGs_nil : cntGs [] = [] := rfl
@[simp] theorem cntWs_nil : cntWs [] = [] := rfl
@[simp] theorem outsOf_nil : outsOf [] = [] := rfl
@[simp] theorem jcostL_nil : jcostL [] = 1 := by simp [jcostL]
@[simp] theorem jcost_nil : jcost [] = 2 := by simp [jcost]

theorem bufGs_cons (p : List Glyph × List Glyph) (Ps : List (List Glyph × List Glyph)) :
    bufGs (p :: Ps) = p.1.reverse ++ bufGs Ps := by simp [bufGs]

theorem bufWs_cons (p : List Glyph × List Glyph) (Ps : List (List Glyph × List Glyph)) :
    bufWs (p :: Ps) = p.2.reverse ++ bufWs Ps := by simp [bufWs]

theorem cntGs_cons (p : List Glyph × List Glyph) (Ps : List (List Glyph × List Glyph)) :
    cntGs (p :: Ps) = blkCnt p.1 ++ cntGs Ps := by simp [cntGs]

theorem cntWs_cons (p : List Glyph × List Glyph) (Ps : List (List Glyph × List Glyph)) :
    cntWs (p :: Ps) = blkCnt p.2 ++ cntWs Ps := by simp [cntWs]

theorem outsOf_cons (p : List Glyph × List Glyph) (Ps : List (List Glyph × List Glyph)) :
    outsOf (p :: Ps) = outsOf Ps ++ Pm p := by
  simp [outsOf, List.reverse_cons, List.map_append, List.flatten_append]

theorem jcostL_cons (p : List Glyph × List Glyph) (Ps : List (List Glyph × List Glyph)) :
    jcostL (p :: Ps) = 5 * (p.1.length + p.2.length) + jcostL Ps + 10 := by
  simp only [jcostL, List.map_cons, List.sum_cons, List.length_cons]
  ring

theorem jcost_cons (p : List Glyph × List Glyph) (Ps : List (List Glyph × List Glyph)) :
    jcost (p :: Ps) = 5 * (p.1.length + p.2.length) + jcost Ps + 10 := by
  simp only [jcost, jcostL_cons, List.map_cons, List.sum_cons, List.length_cons]
  ring

/-- `headD` of a unary region with at least one token. -/
theorem headD_replicate (n : ℕ) (c : List Glyph) (hn : n ≠ 0) :
    (List.replicate n jtok ++ c).headD Glyph.eos = jtok := by
  cases n with
  | zero => exact absurd rfl hn
  | succ k => rfl

/-- `zipWith outPair` is the function form used by `outGlyphs`. -/
theorem zipWith_outPair_elim (Ws Gs : List (List Glyph)) :
    List.zipWith outPair Ws Gs
      = List.zipWith (fun w g => [Glyph.cons, Glyph.cons] ++ w ++ g) Ws Gs := rfl

/-! ## Component lemmas for the states of a straight-line run -/

theorem tPop_stk_ne (X : State) (k j : Stk) (r : Reg) (h : j ≠ k) :
    (State.tPop X k r).stk j = X.stk j := by
  rw [Work.Kernel.dropValue_tPop_stk]; simp [h]

theorem tPop_stk_tail (X : State) (k : Stk) (r : Reg) :
    (State.tPop X k r).stk k = (X.stk k).tail := by
  rw [Work.Kernel.dropValue_tPop_stk]; simp

theorem tPop_reg_ne (X : State) (k : Stk) (r r' : Reg) (h : r' ≠ r) :
    (State.tPop X k r).reg r' = X.reg r' := by
  rw [Work.Kernel.dropValue_tPop_reg]; simp [h]

theorem tPush_stk_ne (X : State) (k j : Stk) (r : Reg) (h : j ≠ k) :
    (State.tPush X k r).stk j = X.stk j := by
  rw [Work.Kernel.dropValue_compPush_stk]; simp [h]

theorem tPush_stk_self (X : State) (k : Stk) (r : Reg) :
    (State.tPush X k r).stk k = X.reg r :: X.stk k := by
  rw [Work.Kernel.dropValue_compPush_stk]; simp

theorem tPush_reg (X : State) (k : Stk) (r r' : Reg) :
    (State.tPush X k r).reg r' = X.reg r' := Work.Kernel.dropValue_compPush_reg X k r r'

theorem tPeek_stk' (X : State) (k : Stk) (r : Reg) (j : Stk) :
    (State.tPeek X k r).stk j = X.stk j := Work.Kernel.dropValue_tPeek_stk X k r j

theorem tPeek_reg' (X : State) (k : Stk) (r : Reg) :
    (State.tPeek X k r).reg r = (X.stk k).headD Glyph.eos := by
  rw [Work.Kernel.dropValue_tPeek_reg]; simp

theorem tSet_stk' (X : State) (r : Reg) (g : Glyph) (j : Stk) :
    (State.tSet X r g).stk j = X.stk j := Work.Kernel.dropValue_compSet_stk X r g j

theorem tSet_reg_self (X : State) (r : Reg) (g : Glyph) :
    (State.tSet X r g).reg r = g := by
  rw [Work.Kernel.dropValue_compSet_reg]; simp

/-! ## List algebra for the pairs list of `joinPhase` -/

theorem map_fst_lambda {α β γ : Type} (f : α → γ) (l : List (α × β)) :
    l.map (fun p => f p.1) = (l.map Prod.fst).map f := by
  rw [List.map_map]; rfl

theorem map_snd_lambda {α β γ : Type} (f : β → γ) (l : List (α × β)) :
    l.map (fun p => f p.2) = (l.map Prod.snd).map f := by
  rw [List.map_map]; rfl

theorem mem_fst_zip_aux {α β : Type} {p : α × β} :
    ∀ {l₁ : List α} {l₂ : List β}, p ∈ l₁.zip l₂ → p.1 ∈ l₁ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ hp; simp at hp
  | cons a l ih =>
    intro l₂ hp
    cases l₂ with
    | nil => simp at hp
    | cons b l₂ =>
      simp only [List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with h | h
      · subst h; simp
      · exact List.mem_cons_of_mem _ (ih h)

theorem zip_reverse_aux {α β : Type} (l₁ : List α) (l₂ : List β) (h : l₁.length = l₂.length) :
    (l₁.zip l₂).reverse = l₁.reverse.zip l₂.reverse := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all
  | cons a l ih =>
    cases l₂ with
    | nil => simp at h
    | cons b l₂ =>
      have h' : l.length = l₂.length := by simpa using h
      simp only [List.zip_cons_cons, List.reverse_cons]
      rw [List.zip_append (l₁ := l.reverse) (l₂ := l₂.reverse) (r₁ := [a]) (r₂ := [b])
        (by simpa using h'), ih l₂ h']
      simp

theorem bufGs_spairs (Gs Ws : List (List Glyph)) (h : Ws.length = Gs.length) :
    bufGs (Gs.reverse.zip Ws.reverse) = bufReg Gs := by
  have hlen : Gs.reverse.length ≤ Ws.reverse.length := by simpa using h.ge
  have htake : (Gs.reverse.zip Ws.reverse).map Prod.fst = Gs.reverse :=
    List.map_fst_zip hlen
  rw [bufGs, map_fst_lambda, htake, List.map_reverse, bufReg]
  rw [List.flatten_reverse]
  simp [List.map_id]

theorem bufWs_spairs (Gs Ws : List (List Glyph)) (h : Ws.length = Gs.length) :
    bufWs (Gs.reverse.zip Ws.reverse) = bufReg Ws := by
  have hlen : Ws.reverse.length ≤ Gs.reverse.length := by simpa using h.le
  have htake : (Gs.reverse.zip Ws.reverse).map Prod.snd = Ws.reverse :=
    List.map_snd_zip hlen
  rw [bufWs, map_snd_lambda, htake, List.map_reverse, bufReg]
  rw [List.flatten_reverse]
  simp [List.map_id]

theorem cntGs_spairs (Gs Ws : List (List Glyph)) (h : Ws.length = Gs.length) :
    cntGs (Gs.reverse.zip Ws.reverse) = cntReg Gs := by
  have hlen : Gs.reverse.length ≤ Ws.reverse.length := by simpa using h.ge
  have htake : (Gs.reverse.zip Ws.reverse).map Prod.fst = Gs.reverse :=
    List.map_fst_zip hlen
  simp only [cntGs, cntReg]
  rw [map_fst_lambda (f := blkCnt), htake]
  rfl

theorem cntWs_spairs (Gs Ws : List (List Glyph)) (h : Ws.length = Gs.length) :
    cntWs (Gs.reverse.zip Ws.reverse) = cntReg Ws := by
  have hlen : Ws.reverse.length ≤ Gs.reverse.length := by simpa using h.le
  have htake : (Gs.reverse.zip Ws.reverse).map Prod.snd = Ws.reverse :=
    List.map_snd_zip hlen
  simp only [cntWs, cntReg]
  rw [map_snd_lambda (f := blkCnt), htake]
  rfl

theorem map_zip_Pm (Gs Ws : List (List Glyph)) :
    (Gs.zip Ws).map Pm = List.zipWith outPair Ws Gs := by
  induction Gs generalizing Ws with
  | nil => cases Ws <;> simp
  | cons g Gs ih =>
    cases Ws with
    | nil => simp
    | cons w Ws => simp [ih Ws]

theorem outsOf_spairs (Gs Ws : List (List Glyph)) (h : Ws.length = Gs.length) :
    outsOf (Gs.reverse.zip Ws.reverse) = (List.zipWith outPair Ws Gs).flatten := by
  have hlen : (Gs.reverse).length = (Ws.reverse).length := by simpa using h.symm
  rw [outsOf, zip_reverse_aux Gs.reverse Ws.reverse hlen, List.reverse_reverse,
    List.reverse_reverse, map_zip_Pm]

theorem length_spairs (Gs Ws : List (List Glyph)) (h : Ws.length = Gs.length) :
    (Gs.reverse.zip Ws.reverse).length = Gs.length := by
  rw [List.length_zip, List.length_reverse, List.length_reverse]
  exact min_eq_left (by omega)

theorem sum_spairs (Gs Ws : List (List Glyph)) (h : Ws.length = Gs.length) :
    ((Gs.reverse.zip Ws.reverse).map (fun p => p.1.length + p.2.length)).sum
      = (Gs.map List.length).sum + (Ws.map List.length).sum := by
  have hlen : Gs.reverse.length ≤ Ws.reverse.length := by simpa using h.ge
  have hlen' : Ws.reverse.length ≤ Gs.reverse.length := by simpa using h.le
  rw [List.sum_map_add]
  congr 1
  · rw [map_fst_lambda, List.map_fst_zip hlen, List.map_reverse, List.sum_reverse]
  · rw [map_snd_lambda, List.map_snd_zip hlen', List.map_reverse, List.sum_reverse]

theorem mem_spairs (Gs Ws : List (List Glyph)) (_h : Ws.length = Gs.length) :
    ∀ p ∈ Gs.reverse.zip Ws.reverse, p.1 ∈ Gs := by
  intro p hp
  exact List.mem_reverse.mp (mem_fst_zip_aux hp)

end Work.MainP
