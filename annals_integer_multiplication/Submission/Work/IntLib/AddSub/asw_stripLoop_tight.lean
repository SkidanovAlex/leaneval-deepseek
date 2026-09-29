import Mathlib
import Submission.Work.IntLib.AddSub.Defs
import Submission.Work.IntLib.AddSub.Basic
import Submission.Work.IntLib.mulSArith

/-!
# `IntLib` / add–sub: the tight specification of the leading-zero stripper

`asw_stripLoop out` pops the maximal prefix of `Glyph.bit false` glyphs of stack `out` (i.e. of
the *high-order* zero bits of the magnitude stored most-significant-bit-first above the frame
marker `gmk out`) and pushes the first non-`false` glyph back.

The statement proved here is the *tight* one: the stack content after the run is exactly the
canonical form `MulS.stripHigh em` of the input bit list, and the cost is `4 * k + 7` where `k` is
the number of glyphs actually stripped — not `O(em.length)`.  This is what makes the cost of the
surrounding word (`asw_finish`, `asw_same`, …) depend on the *output* length only.

The proof splits into two independent halves:

* `stripHigh_stack_decomp` — pure list bookkeeping: the glyph stack `(em.map bit).reverse` splits
  as `replicate k (bit false) ++ ((stripHigh em).map bit).reverse`, where `k = em.length -
  (stripHigh em).length`, and the remainder is nonempty with a non-`false` head;
* `asw_stripLoopLoop_ev` — the `Ev` unrolling of the loop, cost `4 * |Z| + 6` for a run `Z` of
  `false` bits (plus one step for the initial flag set).
-/

set_option autoImplicit false

namespace Work.IntLib.AddSub

open HvdH

/-! ## List bookkeeping -/

/-- `stripHigh l` is obtained from `l` by deleting its trailing (high-order) `false`s. -/
theorem stripHigh_decomp (l : List Bool) :
    l = Work.IntLib.MulS.stripHigh l ++
      List.replicate (l.length - (Work.IntLib.MulS.stripHigh l).length) false := by
  induction l using List.reverseRecOn with
  | nil => simp [Work.IntLib.MulS.stripHigh]
  | append_singleton xs b ih =>
    have hle : (Work.IntLib.MulS.stripHigh xs).length ≤ xs.length := by
      have h := congrArg List.length ih
      simp at h
      omega
    cases b
    · have hs : Work.IntLib.MulS.stripHigh (xs ++ [false]) = Work.IntLib.MulS.stripHigh xs := by
        unfold Work.IntLib.MulS.stripHigh
        rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
        rw [List.dropWhile_cons_of_pos (p := fun b => !b) (a := false) (l := xs.reverse) (by simp)]
      have hlen : xs.length + 1 - (Work.IntLib.MulS.stripHigh xs).length
          = (xs.length - (Work.IntLib.MulS.stripHigh xs).length) + 1 := by omega
      rw [hs, List.length_append, List.length_singleton, hlen]
      rw [List.replicate_succ', ← List.append_assoc, ← ih]
    · have hs : Work.IntLib.MulS.stripHigh (xs ++ [true]) = xs ++ [true] := by
        unfold Work.IntLib.MulS.stripHigh
        rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
        rw [List.dropWhile_cons_of_neg (p := fun b => !b) (a := true) (l := xs.reverse) (by simp)]
        simp
      rw [hs]
      simp

/-- The stack content of the reversed bit image splits into a run of `bit false` glyphs followed
by the canonical form, and the remainder is a nonempty list with a non-`false` head. -/
theorem stripHigh_stack_decomp (em : List Bool) (M : HvdH.Glyph) (C : List HvdH.Glyph)
    (hM : M ≠ HvdH.Glyph.bit false) :
    ∃ (k : ℕ) (rest : List HvdH.Glyph),
      (em.map HvdH.Glyph.bit).reverse ++ M :: C =
        List.replicate k (HvdH.Glyph.bit false) ++ rest ∧
      rest = ((Work.IntLib.MulS.stripHigh em).map HvdH.Glyph.bit).reverse ++ M :: C ∧
      em.length = (Work.IntLib.MulS.stripHigh em).length + k ∧
      rest ≠ [] ∧ rest.head? ≠ some (HvdH.Glyph.bit false) := by
  set k : ℕ := em.length - (Work.IntLib.MulS.stripHigh em).length with hk
  set rest : List Glyph :=
    ((Work.IntLib.MulS.stripHigh em).map Glyph.bit).reverse ++ M :: C with hr
  have hdec : em = Work.IntLib.MulS.stripHigh em ++ List.replicate k false := by
    have h := stripHigh_decomp em
    rw [← hk] at h
    exact h
  have hmap : em.map Glyph.bit =
      (Work.IntLib.MulS.stripHigh em).map Glyph.bit ++
        List.replicate k (Glyph.bit false) := by
    conv_lhs => rw [hdec]
    rw [List.map_append, List.map_replicate]
  have hrev : (em.map Glyph.bit).reverse =
      List.replicate k (Glyph.bit false) ++
        ((Work.IntLib.MulS.stripHigh em).map Glyph.bit).reverse := by
    rw [hmap, List.reverse_append, List.reverse_replicate]
  have hlen : em.length = (Work.IntLib.MulS.stripHigh em).length + k := by
    conv_lhs => rw [hdec]
    rw [List.length_append, List.length_replicate]
  have hs' : Work.IntLib.MulS.stripHigh em = [] ∨
      (Work.IntLib.MulS.stripHigh em).getLast? = some true :=
    Work.IntLib.MulS.isBits_stripHigh em
  refine ⟨k, rest, ?_, hr, hlen, ?_, ?_⟩
  · rw [hrev, List.append_assoc]
  · rw [hr]; simp
  · rw [hr, List.head?_append]
    rcases hs' with hs0 | hsl
    · rw [hs0]
      simp [hM]
    · have hgl : (((Work.IntLib.MulS.stripHigh em).map Glyph.bit).reverse).head? =
          some (Glyph.bit true) := by
        rw [List.head?_reverse, List.getLast?_map, hsl]
        rfl
      rw [hgl]
      simp

/-! ## The loop -/

/-- The body of the loop of `asw_stripLoop`. -/
abbrev asw_stripLoopBody (out : Stk) : Cmd :=
  seqs [.pop out rT, .ite rT (.bit false) (.set rF gGo) (seqs [.push out rT, .set rF gStop])]

theorem asw_stripLoop_eq (out : Stk) :
    asw_stripLoop out = seqs [.set rF gGo, .loop rF gGo (asw_stripLoopBody out)] := rfl

/-- One iteration of the body on a `false` bit: the glyph is discarded and the flag is reset to
`gGo`; cost `3`. -/
theorem asw_stripLoopBody_go {main : Cmd} {out : Stk} {G : List Glyph}
    {g : Reg → Glyph} {X : Stk → List Glyph} (hX : X out = Glyph.bit false :: G) :
    ∃ s' n, Ev main (asw_stripLoopBody out) ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.stk out = G ∧ s'.reg rF = gGo := by
  let g1 : Reg → Glyph := Function.update g rT ((X out).headD Glyph.eos)
  let X1 : Stk → List Glyph := Function.update X out (X out).tail
  have h1 : Ev main (.pop out rT) ⟨g, X⟩ ⟨g1, X1⟩ 1 := ev_pop' main out rT g X
  have hgd : (X out).headD Glyph.eos = Glyph.bit false := by rw [hX]; rfl
  have hg1 : (⟨g1, X1⟩ : State).reg rT = Glyph.bit false := by
    show g1 rT = Glyph.bit false
    rw [show g1 rT = (X out).headD Glyph.eos from rfl, hgd]
  have h2 : Ev main (.ite rT (.bit false) (.set rF gGo)
      (seqs [.push out rT, .set rF gStop])) ⟨g1, X1⟩
      ⟨Function.update g1 rF gGo, X1⟩ 2 :=
    Ev.iteT hg1 (ev_set' main rF gGo g1 X1)
  have hmain : Ev main (asw_stripLoopBody out) ⟨g, X⟩ ⟨Function.update g1 rF gGo, X1⟩ 3 := by
    unfold asw_stripLoopBody
    simp only [seqs]
    exact Ev.seq' h1 h2 (by omega)
  refine ⟨_, _, hmain, by omega, ?_, ?_⟩
  · show X1 out = G
    show (Function.update X out (X out).tail) out = G
    rw [Function.update_self, hX]
    rfl
  · show (Function.update g1 rF gGo) rF = gGo
    rw [Function.update_self]

/-- One iteration of the body on a glyph which is not a `false` bit: it is pushed back and the
flag is set to `gStop`; cost `4`. -/
theorem asw_stripLoopBody_hit {main : Cmd} {out : Stk} (h : Glyph) (tl : List Glyph)
    (hh : h ≠ Glyph.bit false) {g : Reg → Glyph} {X : Stk → List Glyph}
    (hX : X out = h :: tl) :
    ∃ s' n, Ev main (asw_stripLoopBody out) ⟨g, X⟩ s' n ∧ n ≤ 4 ∧
      s'.stk out = h :: tl ∧ s'.reg rF = gStop := by
  let g1 : Reg → Glyph := Function.update g rT ((X out).headD Glyph.eos)
  let X1 : Stk → List Glyph := Function.update X out (X out).tail
  let X2 : Stk → List Glyph := Function.update X1 out (g1 rT :: X1 out)
  have h1 : Ev main (.pop out rT) ⟨g, X⟩ ⟨g1, X1⟩ 1 := ev_pop' main out rT g X
  have hgd : (X out).headD Glyph.eos = h := by rw [hX]; rfl
  have hg1 : (⟨g1, X1⟩ : State).reg rT ≠ Glyph.bit false := by
    show g1 rT ≠ Glyph.bit false
    rw [show g1 rT = (X out).headD Glyph.eos from rfl, hgd]
    exact hh
  have hp : Ev main (.push out rT) ⟨g1, X1⟩ ⟨g1, X2⟩ 1 := ev_push' main out rT g1 X1
  have hs : Ev main (.set rF gStop) ⟨g1, X2⟩ ⟨Function.update g1 rF gStop, X2⟩ 1 :=
    ev_set' main rF gStop g1 X2
  have h2 : Ev main (.ite rT (.bit false) (.set rF gGo) (seqs [.push out rT, .set rF gStop]))
      ⟨g1, X1⟩ ⟨Function.update g1 rF gStop, X2⟩ 3 :=
    Ev.iteF hg1 (Ev.seq' hp hs (by omega))
  have hmain : Ev main (asw_stripLoopBody out) ⟨g, X⟩ ⟨Function.update g1 rF gStop, X2⟩ 4 := by
    unfold asw_stripLoopBody
    simp only [seqs]
    exact Ev.seq' h1 h2 (by omega)
  refine ⟨_, _, hmain, by omega, ?_, ?_⟩
  · show X2 out = h :: tl
    show (Function.update X1 out (g1 rT :: X1 out)) out = h :: tl
    rw [Function.update_self]
    have hg1' : g1 rT = h := by
      rw [show g1 rT = (X out).headD Glyph.eos from rfl, hgd]
    have hX1 : X1 out = tl := by
      show (Function.update X out (X out).tail) out = tl
      rw [Function.update_self, hX]
      rfl
    rw [hg1', hX1]
  · show (Function.update g1 rF gStop) rF = gStop
    rw [Function.update_self]

/-- The loop of `asw_stripLoop`: a run `Z` of `bit false` glyphs is popped, the glyph `rest.head`
is pushed back and the flag set to `gStop`.  Cost `≤ 4 * |Z| + 6`. -/
theorem asw_stripLoopLoop_ev {main : Cmd} (out : Stk) :
    ∀ (Z rest : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      (∀ z ∈ Z, z = Glyph.bit false) → rest ≠ [] →
      rest.head? ≠ some (Glyph.bit false) → g rF = gGo → X out = Z ++ rest →
      ∃ s' n, Ev main (.loop rF gGo (asw_stripLoopBody out)) ⟨g, X⟩ s' n ∧
        n ≤ 4 * Z.length + 6 ∧ s'.stk out = rest ∧ s'.reg rF = gStop := by
  intro Z
  induction Z with
  | nil =>
      intro rest g X hZ hne hhead hreg hX
      obtain ⟨h, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
      have hh : h ≠ Glyph.bit false := by
        intro hc
        exact hhead (by simp [hc])
      obtain ⟨s₁, n₁, hbody, hn₁, hstk₁, hreg₁⟩ :=
        asw_stripLoopBody_hit h tl hh (by simpa using hX)
      have hne₁ : s₁.reg rF ≠ gGo := by rw [hreg₁]; decide
      refine ⟨s₁, _, Ev.loopT hreg hbody (Ev.loopF hne₁), ?_, hstk₁, hreg₁⟩
      simp only [List.length_nil]
      omega
  | cons z Zs ih =>
      intro rest g X hZ hne hhead hreg hX
      have hz : z = Glyph.bit false := hZ z (List.mem_cons_self ..)
      have hZ' : ∀ w ∈ Zs, w = Glyph.bit false := fun w hw => hZ w (List.mem_cons_of_mem z hw)
      have hX'' : X out = Glyph.bit false :: (Zs ++ rest) := by
        rw [hX, List.cons_append, hz]
      obtain ⟨s₁, n₁, hbody, hn₁, hstk₁, hreg₁⟩ :=
        asw_stripLoopBody_go (out := out) (G := Zs ++ rest) hX''
      obtain ⟨s₂, n₂, hloop, hn₂, hstk₂, hreg₂⟩ :=
        ih rest s₁.reg s₁.stk hZ' hne hhead hreg₁ hstk₁
      refine ⟨s₂, _, Ev.loopT hreg hbody hloop, ?_, hstk₂, hreg₂⟩
      simp only [List.length_cons]
      omega

/-- The whole program `asw_stripLoop`: cost `≤ 4 * |Z| + 7`. -/
theorem asw_stripLoop_prog {main : Cmd} (out : Stk) :
    ∀ (Z rest : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      (∀ z ∈ Z, z = Glyph.bit false) → rest ≠ [] →
      rest.head? ≠ some (Glyph.bit false) → X out = Z ++ rest →
      ∃ s' n, Ev main (asw_stripLoop out) ⟨g, X⟩ s' n ∧ n ≤ 4 * Z.length + 7 ∧
        s'.stk out = rest ∧ s'.reg rF ≠ gGo := by
  intro Z rest g X hZ hne hhead hX
  let g₁ : Reg → Glyph := Function.update g rF gGo
  have hset : Ev main (.set rF gGo) ⟨g, X⟩ ⟨g₁, X⟩ 1 := ev_set' main rF gGo g X
  have hg₁ : g₁ rF = gGo := by simp [g₁]
  obtain ⟨s', n, hloop, hn, hstk, hreg⟩ :=
    asw_stripLoopLoop_ev (main := main) out Z rest g₁ X hZ hne hhead hg₁ hX
  have hmain : Ev main (asw_stripLoop out) ⟨g, X⟩ s' (1 + n) := by
    rw [asw_stripLoop_eq]
    simp only [seqs]
    exact Ev.seq hset hloop
  refine ⟨s', _, hmain, ?_, hstk, ?_⟩
  · omega
  · rw [hreg]; decide

/-! ## The tight specification -/

theorem asw_stripLoop_tight {main : HvdH.Cmd} (out : HvdH.Stk) :
    ∀ (em : List Bool) (C : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph)
      (X : HvdH.Stk → List HvdH.Glyph),
      X out = (em.map HvdH.Glyph.bit).reverse ++ Work.IntLib.AddSub.gmk out :: C →
      ∃ k s' n, Work.IntLib.AddSub.Ev main (Work.IntLib.AddSub.asw_stripLoop out) ⟨g, X⟩ s' n ∧
        n ≤ 4 * k + 7 ∧
        em.length = (Work.IntLib.MulS.stripHigh em).length + k ∧
        s'.stk out = ((Work.IntLib.MulS.stripHigh em).map HvdH.Glyph.bit).reverse ++
          Work.IntLib.AddSub.gmk out :: C ∧
        s'.reg Work.IntLib.AddSub.rF ≠ Work.IntLib.AddSub.gGo := by
  intro em C g X hX
  have hM : gmk out ≠ Glyph.bit false := by simp [gmk]
  obtain ⟨k, rest, hdec, hrest, hlen, hne, hhead⟩ :=
    stripHigh_stack_decomp em (gmk out) C hM
  obtain ⟨h, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hh : h ≠ Glyph.bit false := by
    intro hc
    exact hhead (by simp [hc])
  have hZ : ∀ z ∈ List.replicate k (Glyph.bit false), z = Glyph.bit false :=
    fun z hz => List.eq_of_mem_replicate hz
  have hX' : X out = List.replicate k (Glyph.bit false) ++ h :: tl := hX.trans hdec
  obtain ⟨s', n, hev, hn, hstk, hreg⟩ :=
    asw_stripLoop_prog (main := main) out (List.replicate k (Glyph.bit false)) (h :: tl)
      g X hZ (List.cons_ne_nil h tl) (by simpa using hhead) hX'
  refine ⟨k, s', n, hev, ?_, hlen, ?_, hreg⟩
  · have : (List.replicate k (Glyph.bit false)).length = k := List.length_replicate ..
    omega
  · rw [hstk, hrest]

end Work.IntLib.AddSub
