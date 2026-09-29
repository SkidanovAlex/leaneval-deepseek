import Mathlib
import Submission.Work.Layout.SortDefs
import Submission.Work.Layout.mvVal_ev_full

set_option autoImplicit false

namespace Work.Layout

open HvdH

/-! ## The assembly loop of `Sk.assemble`

`Sk.assemble` turns the single run (a `cons`-chain of values) on stack `X` back into a value on
stack 0: it drains the run onto the buffer `Z` (a `gMark` first, so the marker ends up below the
values) and then moves the values one at a time onto stack 0, pushing a `cons` glyph above each.
This file proves the loop that performs the second half.
-/

/-- The top glyph of a `cons`-value's encoding, above anything else. -/
theorem asmLHeadD_enc_cons (a b : Val) (C : List Glyph) :
    ((Val.cons a b).enc ++ C).headD Glyph.eos = Glyph.cons := rfl

/-- The top glyph below a `gMark`. -/
theorem headD_gMark (C : List Glyph) : (gMark :: C).headD Glyph.eos = gMark := rfl

/-- `encs` of the empty list. -/
@[simp] theorem asm_encs_nil : encs ([] : List Val) = [] := rfl

/-- `encs` of a cons-pair, with an arbitrary tail appended. -/
theorem asm_encs_cons (v : Val) (vs : List Val) (C : List Glyph) :
    encs (v :: vs) ++ C = v.enc ++ (encs vs ++ C) := by
  simp [HvdH.encs, List.map_cons, List.flatten_cons, List.append_assoc]

/-- The `cons`-chain built by an extra iteration at the bottom: appending `f v` to the flattened
`cons`-chain of `rest.reverse` gives the `cons`-chain of `(v :: rest).reverse`, minus the final
`nil` that the caller's `A` accounts for. -/
theorem asm_flat_rev_cons (v : Val) (rest : List Val) (A : List Glyph) :
    (rest.reverse.map (fun v => Glyph.cons :: v.enc)).flatten ++
      ((fun v => Glyph.cons :: v.enc) v ++ A) =
    ((v :: rest).reverse.map (fun v => Glyph.cons :: v.enc)).flatten ++ A := by
  simp [List.reverse_cons, List.map_append, List.flatten_append, List.append_assoc]

/-- One iteration of the assembly loop: `Sk.asmBody Z t d` moves the top value `v` of `Z` onto
stack 0 (via the scratches `t`, `d`), pushes a `cons` glyph above it, and reads the new top glyph of
`Z` into `Sk.rH`. -/
theorem asmBody_ev {main : Cmd} {Z t d : Stk}
    (hZ0 : Z ≠ 0) (hZt : Z ≠ t) (hZd : Z ≠ d) (h0t : (0 : Stk) ≠ t) (h0d : (0 : Stk) ≠ d)
    (htd : t ≠ d) {g : Reg → Glyph} {X : Stk → List Glyph} {v : Val} {Zr A : List Glyph}
    (hZ : X Z = v.enc ++ Zr) (h0 : X 0 = A) :
    ∃ s' n, Ev main (Sk.asmBody Z t d) ⟨g, X⟩ s' n ∧ n ≤ 16 * (vsz v + 1) + 3 ∧
      s'.stk Z = Zr ∧ s'.stk 0 = Glyph.cons :: (v.enc ++ A) ∧
      s'.stk t = X t ∧ s'.stk d = X d ∧
      (∀ k : Stk, k ≠ Z → k ≠ 0 → k ≠ t → k ≠ d → s'.stk k = X k) ∧
      s'.reg Sk.rH = Zr.headD Glyph.eos := by
  obtain ⟨s₁, n₁, hmv, hn₁, hZ₁, h0₁, ht₁, hd₁, hf₁⟩ :=
    mvVal_ev_full (main := main) hZ0 hZt hZd h0t h0d htd hZ h0
  obtain ⟨s₂, n₂, hpc, hn₂, h0₂, hf₂, -, -⟩ :=
    pushConst_ev (main := main) (k := (0 : Stk)) (cst := Glyph.cons) (g := s₁.reg) (X := s₁.stk)
  have hpk : Ev main (.peek Z Sk.rH) ⟨s₂.reg, s₂.stk⟩
      ⟨Function.update s₂.reg Sk.rH ((s₂.stk Z).headD Glyph.eos), s₂.stk⟩ 1 :=
    ev_peek' main Z Sk.rH s₂.reg s₂.stk
  have hZ₂ : s₂.stk Z = s₁.stk Z := hf₂ Z hZ0
  refine ⟨⟨Function.update s₂.reg Sk.rH ((s₂.stk Z).headD Glyph.eos), s₂.stk⟩,
    n₁ + n₂ + 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Sk.asmBody
    exact Ev.seq' hmv (Ev.seq hpc hpk) (by omega)
  · omega
  · have : (⟨Function.update s₂.reg Sk.rH ((s₂.stk Z).headD Glyph.eos), s₂.stk⟩
        : State).stk Z = s₂.stk Z := rfl
    rw [this, hZ₂, hZ₁]
  · have : (⟨Function.update s₂.reg Sk.rH ((s₂.stk Z).headD Glyph.eos), s₂.stk⟩
        : State).stk 0 = s₂.stk 0 := rfl
    rw [this, h0₂, h0₁]
  · have : (⟨Function.update s₂.reg Sk.rH ((s₂.stk Z).headD Glyph.eos), s₂.stk⟩
        : State).stk t = s₂.stk t := rfl
    rw [this, hf₂ t h0t.symm, ht₁]
  · have : (⟨Function.update s₂.reg Sk.rH ((s₂.stk Z).headD Glyph.eos), s₂.stk⟩
        : State).stk d = s₂.stk d := rfl
    rw [this, hf₂ d h0d.symm, hd₁]
  · intro k hkZ hk0 hkt hkd
    have h1 : (⟨Function.update s₂.reg Sk.rH ((s₂.stk Z).headD Glyph.eos), s₂.stk⟩
        : State).stk k = s₂.stk k := rfl
    rw [h1, hf₂ k hk0, hf₁ k hkZ hk0 hkt hkd]
  · have : (⟨Function.update s₂.reg Sk.rH ((s₂.stk Z).headD Glyph.eos), s₂.stk⟩
        : State).reg Sk.rH = (s₂.stk Z).headD Glyph.eos := by
      simp only [Function.update_self]
    rw [this, hZ₂, hZ₁]

/-- The assembly loop, run `vals.length` times: every value of `vals` is moved onto stack 0 (in
turn) with a `cons` glyph above it, so that the output is the flattened `cons`-chain of
`vals.reverse` (without its terminating `nil`) sitting above `A`. -/
theorem asmLoop_loopRuns {main : Cmd} {Z t d : Stk}
    (hZ0 : Z ≠ 0) (hZt : Z ≠ t) (hZd : Z ≠ d) (ht0 : t ≠ 0) (hd0 : d ≠ 0) (htd : t ≠ d) :
    ∀ (vals : List Val) (g : Reg → Glyph) (X : Stk → List Glyph) (A B : List Glyph),
      (∀ v ∈ vals, ∃ a b : Val, v = Val.cons a b) →
      X Z = encs vals ++ gMark :: B → X 0 = A → g Sk.rH = (X Z).headD Glyph.eos →
      ∃ s' C, loopRuns main Sk.rH Glyph.cons (Sk.asmBody Z t d) vals.length ⟨g, X⟩ s' C ∧
        C ≤ 16 * (vals.map vsz).sum + 20 * vals.length ∧
        s'.stk Z = gMark :: B ∧
        s'.stk 0 = (vals.reverse.map (fun v => Glyph.cons :: v.enc)).flatten ++ A ∧
        s'.stk t = X t ∧ s'.stk d = X d ∧
        (∀ k : Stk, k ≠ Z → k ≠ 0 → k ≠ t → k ≠ d → s'.stk k = X k) ∧
        s'.reg Sk.rH = gMark := by
  intro vals
  induction vals with
  | nil =>
      intro g X A B hcons hZ h0 hrh
      have hZ' : X Z = gMark :: B := by simpa using hZ
      have hrh' : g Sk.rH = gMark := by rw [hrh, hZ']; exact headD_gMark B
      refine ⟨⟨g, X⟩, 0, loopRuns.zero, by simp, hZ', ?_, rfl, rfl,
        (fun k _ _ _ _ => rfl), hrh'⟩
      · simpa using h0
  | cons v rest ih =>
      intro g X A B hcons hZ h0 hrh
      obtain ⟨a, b, rfl⟩ := hcons v (by simp)
      have hcons' : ∀ u ∈ rest, ∃ a b : Val, u = Val.cons a b :=
        fun u hu => hcons u (List.mem_cons_of_mem _ hu)
      have hZ1 : X Z = (Val.cons a b).enc ++ (encs rest ++ gMark :: B) := by
        rw [hZ, asm_encs_cons]
      have hrh1 : g Sk.rH = Glyph.cons := by
        rw [hrh, hZ1]
        exact asmLHeadD_enc_cons a b (encs rest ++ gMark :: B)
      obtain ⟨s₁, n₁, hev₁, hn₁, hZs₁, h0s₁, hts₁, hds₁, hfs₁, hrhs₁⟩ :=
        asmBody_ev (main := main) hZ0 hZt hZd ht0.symm hd0.symm htd hZ1 h0
      have hone : loopRuns main Sk.rH Glyph.cons (Sk.asmBody Z t d) 1 ⟨g, X⟩ s₁ (n₁ + 1) :=
        loopRuns.one hrh1 hev₁
      have hZ2 : s₁.stk Z = encs rest ++ gMark :: B := hZs₁
      have h0s₁' : s₁.stk 0 = (Glyph.cons :: (Val.cons a b).enc) ++ A := by
        rw [h0s₁, List.cons_append]
      have hrhs₁' : s₁.reg Sk.rH = (s₁.stk Z).headD Glyph.eos := by rw [hZ2]; exact hrhs₁
      obtain ⟨s', C, hrun, hC, hZs, h0s, hts, hds, hfs, hrHs⟩ :=
        ih s₁.reg s₁.stk ((Glyph.cons :: (Val.cons a b).enc) ++ A) B hcons' hZ2 h0s₁' hrhs₁'
      have hcat : loopRuns main Sk.rH Glyph.cons (Sk.asmBody Z t d) (1 + rest.length)
          ⟨g, X⟩ s' ((n₁ + 1) + C) := loopRuns.concat rest.length hone hrun
      have hcast : loopRuns main Sk.rH Glyph.cons (Sk.asmBody Z t d)
          (Val.cons a b :: rest).length ⟨g, X⟩ s' ((n₁ + 1) + C) :=
        loopRuns.cast (show 1 + rest.length = (Val.cons a b :: rest).length by
            simp only [List.length_cons]; omega) hcat
      refine ⟨s', (n₁ + 1) + C, hcast, ?_, hZs, ?_, ?_, ?_, ?_, hrHs⟩
      · have h1 : n₁ ≤ 16 * (vsz (Val.cons a b) + 1) + 3 := hn₁
        have h2 : C ≤ 16 * (rest.map vsz).sum + 20 * rest.length := hC
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
      · rw [h0s]
        exact asm_flat_rev_cons (Val.cons a b) rest A
      · rw [hts, hts₁]
      · rw [hds, hds₁]
      · intro k hkZ hk0 hkt hkd
        rw [hfs k hkZ hk0 hkt hkd, hfs₁ k hkZ hk0 hkt hkd]

/-- `Work.Layout.Sk.asmBody Z t d = mvVal Z 0 t d ;; pushConst 0 HvdH.Glyph.cons ;; peek Z rH`
(see `Submission/Work/Layout/SortDefs.lean`): move the top value of `Z` onto stack 0 and push a
`cons` glyph above it, then read the new top glyph of `Z` into the loop register `rH`.

Here `Z` holds the values `vals` (all of them `cons`-values) above a `gMark` terminator:
`X Z = HvdH.encs vals ++ Work.Layout.gMark :: B`, stack 0 holds `A`, and the loop register holds the
top glyph of `Z`.  The loop therefore runs `vals.length` times, consuming `gMark` as its exit
condition, and the values are moved in the order they sit on `Z`, so the output on stack 0 is built
bottom-up: `(vals.reverse.map (fun v => HvdH.Glyph.cons :: v.enc)).flatten ++ A` (the `cons`-chain
`ofList vals.reverse` without its terminating `nil`, sitting above `A`). -/
theorem asmLoopEv {main : HvdH.Cmd} {Z t d : HvdH.Stk}
    (hZ0 : Z ≠ 0) (hZt : Z ≠ t) (hZd : Z ≠ d) (ht0 : t ≠ 0) (hd0 : d ≠ 0) (htd : t ≠ d)
    {g : HvdH.Reg → HvdH.Glyph} {X : HvdH.Stk → List HvdH.Glyph} {vals : List HvdH.Val}
    {A B : List HvdH.Glyph}
    (hcons : ∀ v ∈ vals, ∃ a b : HvdH.Val, v = HvdH.Val.cons a b)
    (hZ : X Z = HvdH.encs vals ++ Work.Layout.gMark :: B) (h0 : X 0 = A)
    (hrh : g Work.Layout.Sk.rH = (X Z).headD HvdH.Glyph.eos) :
    ∃ s' n, Work.Layout.Ev main
        (HvdH.Cmd.loop Work.Layout.Sk.rH HvdH.Glyph.cons (Work.Layout.Sk.asmBody Z t d))
        ⟨g, X⟩ s' n ∧
      n ≤ 20 * ((vals.map HvdH.vsz).sum + vals.length + 1) ∧
      s'.stk Z = Work.Layout.gMark :: B ∧
      s'.stk 0 = (vals.reverse.map (fun v => HvdH.Glyph.cons :: v.enc)).flatten ++ A ∧
      s'.stk t = X t ∧ s'.stk d = X d ∧
      (∀ k : HvdH.Stk, k ≠ Z → k ≠ 0 → k ≠ t → k ≠ d → s'.stk k = X k) := by
  obtain ⟨s', C, hrun, hC, hZs, h0s, hts, hds, hfs, hrHs⟩ :=
    asmLoop_loopRuns (main := main) hZ0 hZt hZd ht0 hd0 htd vals g X A B hcons hZ h0 hrh
  obtain ⟨n, hev, hle⟩ := loopRuns.eval' hrun (by rw [hrHs]; exact gMark_ne_cons)
  refine ⟨s', C + 1, ⟨n, hev, hle⟩, ?_, hZs, h0s, hts, hds, hfs⟩
  have h1 : C ≤ 16 * (vals.map HvdH.vsz).sum + 20 * vals.length := hC
  omega

end Work.Layout
