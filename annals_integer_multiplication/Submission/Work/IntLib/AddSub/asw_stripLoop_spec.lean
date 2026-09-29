import Mathlib
import Submission.Work.IntLib.AddSub.Defs
import Submission.Work.IntLib.AddSub.Basic
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.Basic
import Submission.Work.IntLib.mulSArith

/-!
# `IntLib` / add–sub: the leading-zero stripper `asw_stripLoop`

`asw_stripLoop out` pops the maximal prefix of `Glyph.bit false` glyphs of stack `out` and pushes
back the first glyph which is not a `false` bit.  It is used by `asw_finish`, where `out` holds a
magnitude most-significant-digit first, so that the short-circuit is exactly the removal of the
high-order zero bits.

`asw_stripLoop_spec` states that on a stack whose content above the frame marker `gmk out` is the
reversed bit image of a bit list `em`, the program ends with the reversed bit image of a *canonical*
bit list `em'` (no high-order zeros) representing the same number, in at most `5 * (em.length + 1) + 3`
steps, and leaves the frame register `rF` different from `gGo`.
-/

set_option autoImplicit false

namespace Work.IntLib
namespace AddSub

open HvdH

/-! ## Auxiliary list lemmas -/

/-- `dropWhile` stops at an element which does not satisfy the predicate. -/
theorem dropWhile_cons_p {α : Type*} {p : α → Bool} :
    ∀ {l : List α} {a : α} {t : List α}, l.dropWhile p = a :: t → p a = false := by
  intro l
  induction l with
  | nil => intro a t h; simp at h
  | cons b bs ih =>
    intro a t h
    rw [List.dropWhile_cons] at h
    by_cases hb : p b = true
    · rw [ite_eq_left hb] at h
      exact ih h
    · rw [ite_eq_right hb] at h
      simp only [List.cons.injEq] at h
      rw [← h.1]
      cases hpb : p b
      · rfl
      · exact absurd hpb hb

/-- Stack order: dropping the leading `bit false` glyphs of the reversed bit image of a bit list
is the same as stripping the high-order zero bits of the list. -/
theorem stripHigh_map_bit_reverse (em : List Bool) :
    ((Work.IntLib.MulS.stripHigh em).map HvdH.Glyph.bit).reverse =
      ((em.map HvdH.Glyph.bit).reverse).dropWhile (fun gg => gg = HvdH.Glyph.bit false) := by
  rw [← List.map_reverse]
  conv_rhs => rw [← List.map_reverse, List.dropWhile_map]
  simp only [Work.IntLib.MulS.stripHigh, List.reverse_reverse]
  have hp : ((fun gg => decide (gg = Glyph.bit false)) ∘ Glyph.bit) = (fun b : Bool => !b) := by
    funext b; cases b <;> rfl
  rw [hp]

/-! ## The loop -/

/-- The loop of `asw_stripLoop`: from a state whose stack `out` holds `Z ++ M :: A`, where every
glyph of `Z` is a `false` bit and `M` is not, and whose flag register `rF` holds `gGo`, the loop
pops the whole run `Z`, pushes `M` back and stops.  Cost `≤ 4 * Z.length + 6`, and afterwards the
flag is no longer `gGo`. -/
theorem asw_stripLoopLoop_spec {main : HvdH.Cmd} (out : HvdH.Stk) :
    ∀ (Z : List HvdH.Glyph) (M : HvdH.Glyph) (A : List HvdH.Glyph)
      (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph),
      (∀ x ∈ Z, x = HvdH.Glyph.bit false) → M ≠ HvdH.Glyph.bit false →
      g Work.IntLib.AddSub.rF = Work.IntLib.AddSub.gGo →
      X out = Z ++ M :: A →
      ∃ s' n, Work.IntLib.AddSub.Ev main
        (.loop Work.IntLib.AddSub.rF Work.IntLib.AddSub.gGo
          (Work.IntLib.AddSub.seqs [.pop out Work.IntLib.AddSub.rT,
            .ite Work.IntLib.AddSub.rT (HvdH.Glyph.bit false)
              (.set Work.IntLib.AddSub.rF Work.IntLib.AddSub.gGo)
              (Work.IntLib.AddSub.seqs [.push out Work.IntLib.AddSub.rT,
                .set Work.IntLib.AddSub.rF Work.IntLib.AddSub.gStop])]))
        ⟨g, X⟩ s' n ∧
        n ≤ 4 * Z.length + 6 ∧
        s'.stk out = M :: A ∧ s'.reg Work.IntLib.AddSub.rF ≠ Work.IntLib.AddSub.gGo := by
  intro Z
  induction Z with
  | nil =>
      intro M A g X _ hM hg hX
      let g1 : Reg → Glyph := Function.update g rT ((X out).headD Glyph.eos)
      let X1 : Stk → List Glyph := Function.update X out (X out).tail
      let X2 : Stk → List Glyph := Function.update X1 out (g1 rT :: X1 out)
      let g2 : Reg → Glyph := Function.update g1 rF gStop
      have h1 : Ev main (.pop out rT) ⟨g, X⟩ ⟨g1, X1⟩ 1 := ev_pop' main out rT g X
      have hg1x : g1 rT = M := by
        show (Function.update g rT ((X out).headD Glyph.eos)) rT = M
        rw [Function.update_self, hX]; rfl
      have hne : (⟨g1, X1⟩ : State).reg rT ≠ Glyph.bit false := by
        show g1 rT ≠ Glyph.bit false
        rw [hg1x]; exact hM
      have hp : Ev main (.push out rT) ⟨g1, X1⟩ ⟨g1, X2⟩ 1 := ev_push' main out rT g1 X1
      have hs : Ev main (.set rF gStop) ⟨g1, X2⟩ ⟨g2, X2⟩ 1 := ev_set' main rF gStop g1 X2
      have h2 : Ev main (.ite rT (Glyph.bit false) (.set rF gGo)
          (seqs [.push out rT, .set rF gStop])) ⟨g1, X1⟩ ⟨g2, X2⟩ 3 :=
        Ev.iteF hne (Ev.seq' hp hs (by omega))
      have hbody : Ev main (seqs [.pop out rT, .ite rT (Glyph.bit false) (.set rF gGo)
          (seqs [.push out rT, .set rF gStop])]) ⟨g, X⟩ ⟨g2, X2⟩ 4 := by
        simp only [seqs]
        exact Ev.seq' h1 h2 (by omega)
      have hreg2 : (⟨g2, X2⟩ : State).reg rF ≠ gGo := by
        show g2 rF ≠ gGo
        have hgs : g2 rF = gStop := by
          show (Function.update g1 rF gStop) rF = gStop
          rw [Function.update_self]
        rw [hgs]; decide
      have hloop : Ev main (.loop rF gGo (seqs [.pop out rT, .ite rT (Glyph.bit false)
          (.set rF gGo) (seqs [.push out rT, .set rF gStop])])) ⟨g, X⟩ ⟨g2, X2⟩ (4 + 1 + 1) :=
        Ev.loopT hg hbody (Ev.loopF hreg2)
      refine ⟨⟨g2, X2⟩, 4 + 1 + 1, hloop, by omega, ?_, hreg2⟩
      show X2 out = M :: A
      have hX1 : X1 out = A := by
        show (Function.update X out (X out).tail) out = A
        rw [Function.update_self, hX]; rfl
      show (Function.update X1 out (g1 rT :: X1 out)) out = M :: A
      rw [Function.update_self, hX1, hg1x]
  | cons h Z' ih =>
      intro M A g X hZ hM hg hX
      have hh : h = Glyph.bit false := hZ h (List.mem_cons_self ..)
      subst hh
      let g1 : Reg → Glyph := Function.update g rT ((X out).headD Glyph.eos)
      let X1 : Stk → List Glyph := Function.update X out (X out).tail
      let g2 : Reg → Glyph := Function.update g1 rF gGo
      have h1 : Ev main (.pop out rT) ⟨g, X⟩ ⟨g1, X1⟩ 1 := ev_pop' main out rT g X
      have hg1x : g1 rT = Glyph.bit false := by
        show (Function.update g rT ((X out).headD Glyph.eos)) rT = Glyph.bit false
        rw [Function.update_self, hX]; rfl
      have heq : (⟨g1, X1⟩ : State).reg rT = Glyph.bit false := by
        show g1 rT = Glyph.bit false
        exact hg1x
      have hs : Ev main (.set rF gGo) ⟨g1, X1⟩ ⟨g2, X1⟩ 1 := ev_set' main rF gGo g1 X1
      have h2 : Ev main (.ite rT (Glyph.bit false) (.set rF gGo)
          (seqs [.push out rT, .set rF gStop])) ⟨g1, X1⟩ ⟨g2, X1⟩ 2 := Ev.iteT heq hs
      have hbody : Ev main (seqs [.pop out rT, .ite rT (Glyph.bit false) (.set rF gGo)
          (seqs [.push out rT, .set rF gStop])]) ⟨g, X⟩ ⟨g2, X1⟩ 3 := by
        simp only [seqs]
        exact Ev.seq' h1 h2 (by omega)
      have hX1 : X1 out = Z' ++ M :: A := by
        show (Function.update X out (X out).tail) out = Z' ++ M :: A
        rw [Function.update_self, hX]; rfl
      have hg2 : g2 rF = gGo := by
        show (Function.update g1 rF gGo) rF = gGo
        rw [Function.update_self]
      obtain ⟨s₂, n₂, hloop₂, hn₂, hstk₂, hreg₂⟩ :=
        ih M A g2 X1 (fun x hx => hZ x (List.mem_cons_of_mem (Glyph.bit false) hx)) hM hg2 hX1
      have hloop : Ev main (.loop rF gGo (seqs [.pop out rT, .ite rT (Glyph.bit false)
          (.set rF gGo) (seqs [.push out rT, .set rF gStop])])) ⟨g, X⟩ s₂ (3 + n₂ + 1) :=
        Ev.loopT hg hbody hloop₂
      refine ⟨s₂, 3 + n₂ + 1, hloop, ?_, hstk₂, hreg₂⟩
      have hlen : (Glyph.bit false :: Z').length = Z'.length + 1 := List.length_cons
      omega

/-! ## The program -/

theorem asw_stripLoop_spec {main : HvdH.Cmd} (out : HvdH.Stk) :
    ∀ (em : List Bool) (C : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph)
      (X : HvdH.Stk → List HvdH.Glyph),
      X out = (em.map HvdH.Glyph.bit).reverse ++ Work.IntLib.AddSub.gmk out :: C →
      ∃ s' n, Work.IntLib.AddSub.Ev main (Work.IntLib.AddSub.asw_stripLoop out) ⟨g, X⟩ s' n ∧
        n ≤ 5 * (em.length + 1) + 3 ∧
        s'.reg Work.IntLib.AddSub.rF ≠ Work.IntLib.AddSub.gGo ∧
        ∃ em' : List Bool,
          s'.stk out = (em'.map HvdH.Glyph.bit).reverse ++ Work.IntLib.AddSub.gmk out :: C ∧
          Work.IntLib.ofBits em' = Work.IntLib.ofBits em ∧ Work.IntLib.IsBits em' := by
  intro em C g X hX
  set p : Glyph → Bool := fun gg => gg = Glyph.bit false with hp
  set l : List Glyph := (em.map Glyph.bit).reverse with hl
  have hlen : l.length = em.length := by rw [hl]; simp
  have hZ : ∀ x ∈ l.takeWhile p, x = Glyph.bit false := by
    intro x hx
    have h := List.mem_takeWhile_imp (p := p) hx
    simpa [hp] using h
  have hXsplit : X out = l.takeWhile p ++ (l.dropWhile p ++ gmk out :: C) := by
    calc X out = l ++ gmk out :: C := hX
      _ = (l.takeWhile p ++ l.dropWhile p) ++ gmk out :: C := by
            rw [List.takeWhile_append_dropWhile]
      _ = l.takeWhile p ++ (l.dropWhile p ++ gmk out :: C) := List.append_assoc ..
  have hleft : ((Work.IntLib.MulS.stripHigh em).map Glyph.bit).reverse = l.dropWhile p := by
    rw [stripHigh_map_bit_reverse em, hl]
  have hZlen : (l.takeWhile p).length ≤ em.length := by
    rw [← hlen]
    exact List.Sublist.length_le (List.takeWhile_sublist p)
  let g₁ : Reg → Glyph := Function.update g rF gGo
  have hg₁ : g₁ rF = gGo := by simp [g₁]
  have hset : Ev main (.set rF gGo) ⟨g, X⟩ ⟨g₁, X⟩ 1 := ev_set' main rF gGo g X
  have hM : gmk out ≠ Glyph.bit false := by simp [gmk]
  rcases hdrop : l.dropWhile p with _ | ⟨m, ms⟩
  · have hX' : X out = l.takeWhile p ++ gmk out :: C := by
      rw [hXsplit, hdrop, List.nil_append]
    obtain ⟨s', n, hev, hn, hstk, hreg⟩ :=
      asw_stripLoopLoop_spec (main := main) out (l.takeWhile p) (gmk out) C g₁ X hZ hM hg₁ hX'
    refine ⟨s', n + 1, ?_, ?_, hreg, Work.IntLib.MulS.stripHigh em, ?_,
      Work.IntLib.MulS.ofBits_stripHigh em, Work.IntLib.MulS.isBits_stripHigh em⟩
    · unfold asw_stripLoop
      simp only [seqs]
      exact Ev.seq' hset hev (by omega)
    · have := hn; omega
    · rw [hstk, hleft, hdrop]; simp
  · have hm : m ≠ Glyph.bit false := by
      have h1 : p m = false := dropWhile_cons_p (p := p) hdrop
      intro hcon
      rw [hcon] at h1
      simp [hp] at h1
    have hX' : X out = l.takeWhile p ++ m :: (ms ++ gmk out :: C) := by
      rw [hXsplit, hdrop, List.cons_append]
    obtain ⟨s', n, hev, hn, hstk, hreg⟩ :=
      asw_stripLoopLoop_spec (main := main) out (l.takeWhile p) m (ms ++ gmk out :: C) g₁ X hZ hm
        hg₁ hX'
    refine ⟨s', n + 1, ?_, ?_, hreg, Work.IntLib.MulS.stripHigh em, ?_,
      Work.IntLib.MulS.ofBits_stripHigh em, Work.IntLib.MulS.isBits_stripHigh em⟩
    · unfold asw_stripLoop
      simp only [seqs]
      exact Ev.seq' hset hev (by omega)
    · have := hn; omega
    · rw [hstk, hleft, hdrop]
      simp only [List.cons_append]

end AddSub
end Work.IntLib
