import Mathlib
import Submission.Work.IntLib.chunkProg
import Submission.Work.IntLib.dropZeros
import Submission.Work.Layout.Base

/-!
# `dropZerosProg` on the `sS` stack: cost in terms of the actual run of zero bits

The word `Work.IntLib.dropZerosProg k r` pops the *leading* run of `Glyph.bit false` glyphs of
stack `k` (i.e. the trailing run of the push order).  The library lemma `Work.IntLib.dropZeros`
bounds its cost by `3 * l.length + 4` for the whole prefix `l` of the stack; here we need the
sharper bound `3 * (length of the run) + 2`, because the `sS` stack of the `chunk` word carries
*all* the previously closed groups below the group currently being built, and only the trailing
run of zero bits of that group is popped.

Everything is proved from scratch here:

* `sSdz_loopPeel` / `sSdz_dropZerosProg` — the loop/program peel a maximal leading run of
  `bit false` glyphs, with cost `3 * run + 1` / `3 * run + 2`;
* `sSdz_runLe_cons` — the trailing run of `bit false` in `A ++ [cons, pos] ++ bits.map bit` is at
  most `bits.length` (the `pos` glyph blocks the run);
* `sSdz_dropWhile_spec` — a decomposition of the maximal run;
* the main theorem then applies this with the push order `L` of the `chunk` word, whose trailing
  run has length at most `b`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib

open HvdH

/-! ## The test glyph -/

/-- The loop test of `dropZerosProg`, as a Boolean function. -/
abbrev sSdzP : Glyph → Bool := fun g => decide (g = Glyph.bit false)

theorem sSdzP_eq_true {g : Glyph} : sSdzP g = true ↔ g = Glyph.bit false := decide_eq_true_iff

theorem sSdzP_pos : sSdzP Glyph.pos = false := by decide

theorem sSdzP_bit_false : sSdzP (Glyph.bit false) = true := by decide

/-- Nothing is a `bit false` if the head of the list is not. -/
theorem sSdzP_ne_of_ne {g : Glyph} (h : g ≠ Glyph.bit false) : sSdzP g = false := by
  cases hb : sSdzP g with
  | false => rfl
  | true => exact absurd (sSdzP_eq_true.mp hb) h

/-! ## List combinatorics of the trailing run of `bit false` -/

/-- Appending a non-`bit false` glyph at the front right of a list does not change the leading run
of `bit false` of the list. -/
theorem sSdz_takeWhile_append_neg (l k : List Glyph) (a : Glyph) (ha : sSdzP a = false) :
    (l ++ a :: k).takeWhile sSdzP = l.takeWhile sSdzP := by
  induction l with
  | nil =>
      rw [List.nil_append, List.takeWhile_cons_of_neg]
      · rfl
      · rw [ha]; exact Bool.false_ne_true
  | cons b t ih =>
      rw [List.cons_append]
      by_cases hb : sSdzP b = true
      · rw [List.takeWhile_cons_of_pos hb, List.takeWhile_cons_of_pos hb]
        rw [ih]
      · rw [List.takeWhile_cons_of_neg hb, List.takeWhile_cons_of_neg hb]

/-- The length of the trailing run of `bit false` glyphs of `A ++ [cons, pos] ++ bits.map bit` is
at most `bits.length`: the `pos` glyph blocks the run. -/
theorem sSdz_runLe (A : List Glyph) (bits : List Bool) :
    ((A ++ [Glyph.pos] ++ bits.map Glyph.bit).reverse.takeWhile sSdzP).length ≤ bits.length := by
  have hrev : (A ++ [Glyph.pos] ++ bits.map Glyph.bit).reverse
      = (bits.map Glyph.bit).reverse ++ Glyph.pos :: A.reverse := by
    simp [List.append_assoc]
  rw [hrev, sSdz_takeWhile_append_neg _ _ Glyph.pos sSdzP_pos]
  calc ((bits.map Glyph.bit).reverse.takeWhile sSdzP).length
      ≤ ((bits.map Glyph.bit).reverse).length :=
        List.Sublist.length_le (List.takeWhile_sublist sSdzP)
    _ = bits.length := by simp

/-- The group marker `cons`/`pos` blocks the trailing run of zero bits. -/
theorem sSdz_runLe_cons (A : List Glyph) (bits : List Bool) :
    ((A ++ [Glyph.cons, Glyph.pos] ++ bits.map Glyph.bit).reverse.takeWhile sSdzP).length
      ≤ bits.length := by
  have h : A ++ [Glyph.cons, Glyph.pos] ++ bits.map Glyph.bit
      = (A ++ [Glyph.cons]) ++ [Glyph.pos] ++ bits.map Glyph.bit := by
    simp [List.append_assoc]
  rw [h]
  exact sSdz_runLe (A ++ [Glyph.cons]) bits

/-- The maximal leading run of `bit false` of a list, as a decomposition of the list. -/
theorem sSdz_dropWhile_spec (l : List Glyph) :
    l.dropWhile sSdzP = [] ∨
      ∃ a t, l.dropWhile sSdzP = a :: t ∧ a ≠ Glyph.bit false := by
  induction l with
  | nil => exact Or.inl rfl
  | cons b t ih =>
      by_cases hb : sSdzP b = true
      · rw [List.dropWhile_cons_of_pos hb]
        exact ih
      · have hbf : b ≠ Glyph.bit false := fun hcon => hb (hcon ▸ sSdzP_bit_false)
        rw [List.dropWhile_cons_of_neg hb]
        exact Or.inr ⟨b, t, rfl, hbf⟩

/-! ## Peeling a maximal run of `bit false` glyphs -/

/-- The loop of `dropZerosProg`, from a state whose stack `k` holds a maximal run `R` of
`bit false` glyphs followed by `B`: it pops exactly the run, in `3 * R.length + 1` steps (one
failing test included), leaving `B` on the stack and changing no other stack. -/
theorem sSdz_loopPeel (main : Cmd) (k : Stk) (r : Reg) :
    ∀ (R B : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      (∀ x ∈ R, x = Glyph.bit false) →
      (B = [] ∨ ∃ a t, B = a :: t ∧ a ≠ Glyph.bit false) →
      X k = R ++ B →
      g r = (X k).headD Glyph.eos →
      ∃ (s' : State) (n : ℕ),
        Work.Layout.Ev main (.loop r (Glyph.bit false) (.seq (.pop k r) (.peek k r)))
          ⟨g, X⟩ s' n ∧
        n ≤ 3 * R.length + 1 ∧
        s'.stk k = B ∧
        (∀ j : Stk, j ≠ k → s'.stk j = X j) := by
  intro R
  induction R with
  | nil =>
      intro B g X _ hB hX hg
      have hhd : B.headD Glyph.eos ≠ Glyph.bit false := by
        rcases hB with h | ⟨a, t, ha, hat⟩
        · rw [h]; exact (nomatch ·)
        · rw [ha]; exact hat
      have hne : (⟨g, X⟩ : State).reg r ≠ Glyph.bit false := by
        show g r ≠ Glyph.bit false
        rw [hg, hX]
        simpa using hhd
      exact ⟨⟨g, X⟩, 1, Work.Layout.Ev.loopF hne, by simp, by simpa using hX,
        fun j _ => rfl⟩
  | cons hd tl ih =>
      intro B g X hmem hB hX hg
      have hhd : hd = Glyph.bit false := hmem hd (by simp)
      subst hhd
      have hmem' : ∀ x ∈ tl, x = Glyph.bit false :=
        fun x hx => hmem x (List.mem_cons_of_mem _ hx)
      have hX' : X k = Glyph.bit false :: (tl ++ B) := by
        rw [hX, List.cons_append]
      have hr : (⟨g, X⟩ : State).reg r = Glyph.bit false := by
        simpa [hX'] using hg
      have hb1 : Work.Layout.Ev main (.pop k r) ⟨g, X⟩
          ⟨Function.update g r (Glyph.bit false), Function.update X k (tl ++ B)⟩ 1 := by
        simpa [hX'] using Work.Layout.ev_pop' main k r g X
      have hb2 : Work.Layout.Ev main (.peek k r)
          ⟨Function.update g r (Glyph.bit false), Function.update X k (tl ++ B)⟩
          ⟨Function.update (Function.update g r (Glyph.bit false)) r
             (((Function.update X k (tl ++ B)) k).headD Glyph.eos),
           Function.update X k (tl ++ B)⟩ 1 :=
        Work.Layout.ev_peek' main k r _ _
      have hbody : Work.Layout.Ev main (.seq (.pop k r) (.peek k r)) ⟨g, X⟩
          ⟨Function.update (Function.update g r (Glyph.bit false)) r
             (((Function.update X k (tl ++ B)) k).headD Glyph.eos),
           Function.update X k (tl ++ B)⟩ 2 := by
        simpa using Work.Layout.Ev.seq hb1 hb2
      have hX1 : (Function.update X k (tl ++ B)) k = tl ++ B := by simp
      have hg1 : (Function.update (Function.update g r (Glyph.bit false)) r
            (((Function.update X k (tl ++ B)) k).headD Glyph.eos)) r
          = ((Function.update X k (tl ++ B)) k).headD Glyph.eos := by simp
      obtain ⟨s', n', hloop, hn', hstk', hfr⟩ :=
        ih B _ (Function.update X k (tl ++ B)) hmem' hB hX1 hg1
      refine ⟨s', 2 + n' + 1, Work.Layout.Ev.loopT hr hbody hloop, ?_, hstk', ?_⟩
      · rw [List.length_cons]; omega
      · intro j hj
        simpa only [Function.update_of_ne hj] using hfr j hj

/-- `dropZerosProg` on a maximal leading run of `bit false` glyphs: cost `3 * run + 2`, the rest
of the stack is left untouched, no other stack changes. -/
theorem sSdz_dropZerosProg (main : Cmd) (k : Stk) (r : Reg)
    (R B : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph)
    (hmem : ∀ x ∈ R, x = Glyph.bit false)
    (hB : B = [] ∨ ∃ a t, B = a :: t ∧ a ≠ Glyph.bit false)
    (hX : X k = R ++ B) :
    ∃ (s' : State) (n : ℕ),
      Work.Layout.Ev main (dropZerosProg k r) ⟨g, X⟩ s' n ∧
      n ≤ 3 * R.length + 2 ∧
      s'.stk k = B ∧
      (∀ j : Stk, j ≠ k → s'.stk j = X j) := by
  have hpeek : Work.Layout.Ev main (.peek k r) ⟨g, X⟩
      ⟨Function.update g r ((X k).headD Glyph.eos), X⟩ 1 :=
    Work.Layout.ev_peek' main k r g X
  have hg1 : (Function.update g r ((X k).headD Glyph.eos)) r = (X k).headD Glyph.eos := by simp
  obtain ⟨s', n', hloop, hn', hstk, hfr⟩ :=
    sSdz_loopPeel main k r R B _ X hmem hB hX hg1
  refine ⟨s', 1 + n', ?_, by omega, hstk, hfr⟩
  · simpa only [dropZerosProg] using Work.Layout.Ev.seq hpeek hloop

/-! ## The main lemma -/

theorem sSdropZerosProof (main : HvdH.Cmd) (x b N k : ℕ) (hb : 1 ≤ b)
    (Y : HvdH.Stk → List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (hX : X Work.IntLib.sS = (Work.IntLib.outOrder (Work.IntLib.pbits x b N) b k ++
        (if k % b = 0 then [HvdH.Glyph.cons, HvdH.Glyph.pos] else []) ++
        [HvdH.Glyph.bit ((Work.IntLib.pbits x b N).getD k false)]).reverse ++
        Work.IntLib.Shift.gmk Work.IntLib.sS :: Y Work.IntLib.sS) :
    ∃ (s' : HvdH.State) (n : ℕ),
      Work.Layout.Ev main (Work.IntLib.dropZerosProg Work.IntLib.sS Work.IntLib.rD)
        (⟨g, X⟩ : HvdH.State) s' n ∧
      n ≤ 3 * b + 2 ∧
      s'.stk Work.IntLib.sS = (Work.IntLib.stripFalses (Work.IntLib.outOrder (Work.IntLib.pbits x b N) b k ++
        (if k % b = 0 then [HvdH.Glyph.cons, HvdH.Glyph.pos] else []) ++
        [HvdH.Glyph.bit ((Work.IntLib.pbits x b N).getD k false)])).reverse ++
        Work.IntLib.Shift.gmk Work.IntLib.sS :: Y Work.IntLib.sS ∧
      (∀ j : HvdH.Stk, j ≠ Work.IntLib.sS → s'.stk j = X j) := by
  set ps : List Bool := pbits x b N with hps
  set c : Bool := ps.getD k false with hc
  set L : List Glyph := outOrder ps b k ++
    (if k % b = 0 then [Glyph.cons, Glyph.pos] else []) ++ [Glyph.bit c] with hLdef
  set Af : List Glyph := List.flatMap (blk ps b) (List.range (k / b)) with hAf
  set bits : List Bool :=
    (if k % b = 0 then [] else (ps.drop (b * (k / b))).take (k % b)) ++ [c] with hbits
  -- the push order is the accumulated groups followed by the header of the open group
  have hL : L = Af ++ [Glyph.cons, Glyph.pos] ++ bits.map Glyph.bit := by
    rw [hLdef, hAf, hbits]
    unfold Work.IntLib.outOrder
    by_cases h : k % b = 0
    · simp only [if_pos h, List.nil_append, List.append_nil, List.map_cons, List.map_nil,
        List.append_assoc]
    · simp only [if_neg h, Work.IntLib.partBlk, List.map_append, List.map_cons, List.map_nil,
        List.append_nil, List.append_assoc]
  -- the number of zero bits in the open group is at most `b`
  have hbitslen : bits.length ≤ b := by
    rw [hbits]
    by_cases h : k % b = 0
    · rw [if_pos h, List.nil_append, List.length_singleton]
      omega
    · rw [if_neg h, List.length_append, List.length_singleton]
      have h1 : ((ps.drop (b * (k / b))).take (k % b)).length ≤ k % b :=
        List.length_take_le _ _
      have h2 : k % b < b := Nat.mod_lt k (by omega)
      omega
  -- hence the trailing run of zero bits of the push order is at most `b`
  have hrun : (L.reverse.takeWhile sSdzP).length ≤ b := by
    rw [hL]
    exact le_trans (sSdz_runLe_cons Af bits) hbitslen
  have hmem : ∀ x ∈ L.reverse.takeWhile sSdzP, x = Glyph.bit false := by
    intro x hx
    have h1 : sSdzP x = true := List.mem_takeWhile_imp hx
    exact sSdzP_eq_true.mp h1
  have hrest : (L.reverse.dropWhile sSdzP ++ Shift.gmk sS :: Y sS) = [] ∨
      ∃ a t, (L.reverse.dropWhile sSdzP ++ Shift.gmk sS :: Y sS) = a :: t ∧
        a ≠ Glyph.bit false := by
    right
    rcases sSdz_dropWhile_spec L.reverse with h | ⟨a, t, ha, hat⟩
    · refine ⟨Shift.gmk sS, Y sS, ?_, ?_⟩
      · rw [h]; rfl
      · intro hcon; cases hcon
    · exact ⟨a, t ++ Shift.gmk sS :: Y sS, by rw [ha]; rfl, hat⟩
  have hXapp : X sS =
      L.reverse.takeWhile sSdzP ++ (L.reverse.dropWhile sSdzP ++ Shift.gmk sS :: Y sS) := by
    have htk := List.takeWhile_append_dropWhile (p := sSdzP) (l := L.reverse)
    calc X sS = L.reverse ++ Shift.gmk sS :: Y sS := hX
      _ = (L.reverse.takeWhile sSdzP ++ L.reverse.dropWhile sSdzP) ++
            Shift.gmk sS :: Y sS := by rw [htk]
      _ = L.reverse.takeWhile sSdzP ++
            (L.reverse.dropWhile sSdzP ++ Shift.gmk sS :: Y sS) := List.append_assoc _ _ _
  obtain ⟨s', n', hev, hn', hstk, hfr⟩ :=
    sSdz_dropZerosProg main sS rD (L.reverse.takeWhile sSdzP)
      (L.reverse.dropWhile sSdzP ++ Shift.gmk sS :: Y sS) g X hmem hrest hXapp
  have hstrip : (Work.IntLib.stripFalses L).reverse = L.reverse.dropWhile sSdzP := by
    rw [Work.IntLib.stripFalses, List.reverse_reverse]
  refine ⟨s', n', hev, by omega, ?_, hfr⟩
  rw [hstk, hstrip]

end Work.IntLib
