import Mathlib
import Submission.Work.Layout.MergeDefs

/-!
# `readFlag`: consuming the flag value at the top of a stack

`Sk.readFlag f r` pops the flag value at the top of `f` (a `Val.int 0` or a `Val.int 1`) and
leaves `Sk.rJ` set to `Glyph.iend`, with `Glyph.bit true` in register `r` iff the flag was `1`;
the flag's own glyphs are removed from `f`.

The statement below mentions `rJ`, which is `Work.Layout.Sk.rJ` — the register that `readFlag`
pops into.  It is brought into scope by `open Work.Layout.Sk`.
-/

namespace Work.Layout

open HvdH Work.Layout
open Work.Layout.Sk

theorem merge_readFlag {main : Cmd} {f : Stk} {r : Reg} (hrJ : r ≠ rJ) {g : Reg → Glyph} {X : Stk → List Glyph} {b : Bool} {G : List Glyph} (hf : X f = (Val.int (if b then (1 : ℤ) else 0)).enc ++ G) : ∃ s' n, Ev main (Sk.readFlag f r) ⟨g, X⟩ s' n ∧ n ≤ 6 ∧ s'.stk f = G ∧ s'.reg r = (if b then Glyph.bit true else Glyph.iend) ∧ (∀ k' : Stk, k' ≠ f → s'.stk k' = X k') := by
  cases b with
  | false =>
      -- the flag is `int 0`, encoded `pos, iend`
      have hf' : X f = Glyph.pos :: (Glyph.iend :: G) := by rw [hf]; rfl
      refine ⟨⟨Function.update (Function.update (Function.update g r Glyph.pos) r Glyph.iend) rJ Glyph.iend,
               Function.update (Function.update X f (Glyph.iend :: G)) f G⟩, 6, ?_, by omega, ?_, ?_, ?_⟩
      · -- `pop f r` then `peek f r` (reads `iend`) then the `else` branch `pop f rJ`
        have h1 : (X f).headD Glyph.eos = Glyph.pos := by rw [hf', List.headD_cons]
        have h2 : (X f).tail = Glyph.iend :: G := by rw [hf', List.tail_cons]
        have e1 : Ev main (.pop f r) ⟨g, X⟩
            ⟨Function.update g r Glyph.pos, Function.update X f (Glyph.iend :: G)⟩ 1 := by
          have hp := ev_pop' main f r g X
          rw [h1, h2] at hp
          exact hp
        have hd : ((Function.update X f (Glyph.iend :: G)) f).headD Glyph.eos = Glyph.iend := by simp
        have e2 : Ev main (.peek f r)
            ⟨Function.update g r Glyph.pos, Function.update X f (Glyph.iend :: G)⟩
            ⟨Function.update (Function.update g r Glyph.pos) r Glyph.iend,
              Function.update X f (Glyph.iend :: G)⟩ 1 := by
          have hp := ev_peek' main f r (Function.update g r Glyph.pos)
            (Function.update X f (Glyph.iend :: G))
          rw [hd] at hp
          exact hp
        have hne : (Function.update (Function.update g r Glyph.pos) r Glyph.iend) r ≠ Glyph.bit true := by
          rw [Function.update_self]
          decide
        have e3 : Ev main (.ite r (Glyph.bit true) (.seq (.pop f rJ) (.pop f rJ)) (.pop f rJ))
            ⟨Function.update (Function.update g r Glyph.pos) r Glyph.iend,
              Function.update X f (Glyph.iend :: G)⟩
            ⟨Function.update (Function.update (Function.update g r Glyph.pos) r Glyph.iend) rJ Glyph.iend,
              Function.update (Function.update X f (Glyph.iend :: G)) f G⟩ 2 := by
          have h4 : ((Function.update X f (Glyph.iend :: G)) f).headD Glyph.eos = Glyph.iend := by simp
          have h5 : ((Function.update X f (Glyph.iend :: G)) f).tail = G := by simp
          have hp := ev_pop' main f rJ (Function.update (Function.update g r Glyph.pos) r Glyph.iend)
            (Function.update X f (Glyph.iend :: G))
          rw [h4, h5] at hp
          exact Ev.iteF hne hp
        have e23 : Ev main (.seq (.peek f r) (.ite r (Glyph.bit true) (.seq (.pop f rJ) (.pop f rJ)) (.pop f rJ)))
            ⟨Function.update g r Glyph.pos, Function.update X f (Glyph.iend :: G)⟩
            ⟨Function.update (Function.update (Function.update g r Glyph.pos) r Glyph.iend) rJ Glyph.iend,
              Function.update (Function.update X f (Glyph.iend :: G)) f G⟩ 3 :=
          Ev.seq' e2 e3 (by omega)
        unfold Sk.readFlag
        exact (Ev.seq' (C := 4) e1 e23 (by omega)).mono (by omega)
      · simp only [Function.update_self]
      · simp [Function.update_of_ne hrJ]
      · intro k' hk
        simp only [Function.update_of_ne hk]
  | true =>
      -- the flag is `int 1`, encoded `pos, bit true, iend`
      have hf' : X f = Glyph.pos :: (Glyph.bit true :: (Glyph.iend :: G)) := by rw [hf]; rfl
      refine ⟨⟨Function.update (Function.update (Function.update (Function.update g r Glyph.pos) r (Glyph.bit true)) rJ (Glyph.bit true)) rJ Glyph.iend,
               Function.update (Function.update (Function.update X f (Glyph.bit true :: Glyph.iend :: G)) f (Glyph.iend :: G)) f G⟩, 6, ?_, by omega, ?_, ?_, ?_⟩
      · -- `pop f r`, `peek f r` (reads `bit true`), then the `then` branch `pop f rJ; pop f rJ`
        have h1 : (X f).headD Glyph.eos = Glyph.pos := by rw [hf', List.headD_cons]
        have h2 : (X f).tail = Glyph.bit true :: Glyph.iend :: G := by rw [hf', List.tail_cons]
        have e1 : Ev main (.pop f r) ⟨g, X⟩
            ⟨Function.update g r Glyph.pos, Function.update X f (Glyph.bit true :: Glyph.iend :: G)⟩ 1 := by
          have hp := ev_pop' main f r g X
          rw [h1, h2] at hp
          exact hp
        have hd : ((Function.update X f (Glyph.bit true :: Glyph.iend :: G)) f).headD Glyph.eos = Glyph.bit true := by simp
        have e2 : Ev main (.peek f r)
            ⟨Function.update g r Glyph.pos, Function.update X f (Glyph.bit true :: Glyph.iend :: G)⟩
            ⟨Function.update (Function.update g r Glyph.pos) r (Glyph.bit true),
              Function.update X f (Glyph.bit true :: Glyph.iend :: G)⟩ 1 := by
          have hp := ev_peek' main f r (Function.update g r Glyph.pos)
            (Function.update X f (Glyph.bit true :: Glyph.iend :: G))
          rw [hd] at hp
          exact hp
        have hreg : (Function.update (Function.update g r Glyph.pos) r (Glyph.bit true)) r = Glyph.bit true :=
          Function.update_self ..
        have hp1 : Ev main (.pop f rJ)
            ⟨Function.update (Function.update g r Glyph.pos) r (Glyph.bit true),
              Function.update X f (Glyph.bit true :: Glyph.iend :: G)⟩
            ⟨Function.update (Function.update (Function.update g r Glyph.pos) r (Glyph.bit true)) rJ (Glyph.bit true),
              Function.update (Function.update X f (Glyph.bit true :: Glyph.iend :: G)) f (Glyph.iend :: G)⟩ 1 := by
          have ha : ((Function.update X f (Glyph.bit true :: Glyph.iend :: G)) f).headD Glyph.eos = Glyph.bit true := by simp
          have hb : ((Function.update X f (Glyph.bit true :: Glyph.iend :: G)) f).tail = Glyph.iend :: G := by simp
          have hp := ev_pop' main f rJ (Function.update (Function.update g r Glyph.pos) r (Glyph.bit true))
            (Function.update X f (Glyph.bit true :: Glyph.iend :: G))
          rw [ha, hb] at hp
          exact hp
        have hp2 : Ev main (.pop f rJ)
            ⟨Function.update (Function.update (Function.update g r Glyph.pos) r (Glyph.bit true)) rJ (Glyph.bit true),
              Function.update (Function.update X f (Glyph.bit true :: Glyph.iend :: G)) f (Glyph.iend :: G)⟩
            ⟨Function.update (Function.update (Function.update (Function.update g r Glyph.pos) r (Glyph.bit true)) rJ (Glyph.bit true)) rJ Glyph.iend,
              Function.update (Function.update (Function.update X f (Glyph.bit true :: Glyph.iend :: G)) f (Glyph.iend :: G)) f G⟩ 1 := by
          have ha : ((Function.update (Function.update X f (Glyph.bit true :: Glyph.iend :: G)) f (Glyph.iend :: G)) f).headD Glyph.eos = Glyph.iend := by simp
          have hb : ((Function.update (Function.update X f (Glyph.bit true :: Glyph.iend :: G)) f (Glyph.iend :: G)) f).tail = G := by simp
          have hp := ev_pop' main f rJ
            (Function.update (Function.update (Function.update g r Glyph.pos) r (Glyph.bit true)) rJ (Glyph.bit true))
            (Function.update (Function.update X f (Glyph.bit true :: Glyph.iend :: G)) f (Glyph.iend :: G))
          rw [ha, hb] at hp
          exact hp
        have e3 : Ev main (.ite r (Glyph.bit true) (.seq (.pop f rJ) (.pop f rJ)) (.pop f rJ))
            ⟨Function.update (Function.update g r Glyph.pos) r (Glyph.bit true),
              Function.update X f (Glyph.bit true :: Glyph.iend :: G)⟩
            ⟨Function.update (Function.update (Function.update (Function.update g r Glyph.pos) r (Glyph.bit true)) rJ (Glyph.bit true)) rJ Glyph.iend,
              Function.update (Function.update (Function.update X f (Glyph.bit true :: Glyph.iend :: G)) f (Glyph.iend :: G)) f G⟩ 3 :=
          Ev.iteT hreg (Ev.seq' (C := 2) hp1 hp2 (by omega))
        have e23 : Ev main (.seq (.peek f r) (.ite r (Glyph.bit true) (.seq (.pop f rJ) (.pop f rJ)) (.pop f rJ)))
            ⟨Function.update g r Glyph.pos, Function.update X f (Glyph.bit true :: Glyph.iend :: G)⟩
            ⟨Function.update (Function.update (Function.update (Function.update g r Glyph.pos) r (Glyph.bit true)) rJ (Glyph.bit true)) rJ Glyph.iend,
              Function.update (Function.update (Function.update X f (Glyph.bit true :: Glyph.iend :: G)) f (Glyph.iend :: G)) f G⟩ 4 :=
          Ev.seq' e2 e3 (by omega)
        unfold Sk.readFlag
        exact (Ev.seq' (C := 5) e1 e23 (by omega)).mono (by omega)
      · simp only [Function.update_self]
      · simp [Function.update_of_ne hrJ]
      · intro k' hk
        simp only [Function.update_of_ne hk]

end Work.Layout
