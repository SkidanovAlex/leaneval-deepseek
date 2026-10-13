import Mathlib
import Submission.Work.WilE9.Defs
import Submission.Work.WilG0.Defs

namespace Work.WilE9.Glue

open WilkiesDesign WilkiesDesign.E

/-
  `m` iterated projections of a `Gen`-set.  Do NOT prove this by instantiating the generic
  `SOMin` version `Work.WilG0.projLastIter_mem` at `WilkiesDesign.E.genSOMin`: the `comps`
  field of `genSOMin` is the `sorry`ed `E8_comps`, so that would depend on `sorryAx`.  The
  proof is a copy of the induction in `Submission/Work/WilG0/projLastIter_mem.lean` with
  `S.Ω` replaced by `Gen` (using only `Gen.proj`, `Gen.mono_F`, `Gen.mono_D`).
-/
theorem projLastIter_mem {n m F D : ℕ} {X : Set (Fin (n + m) → ℝ)}
    (h : WilkiesDesign.E.Gen F D (n + m) X) :
    WilkiesDesign.E.Gen (F + m) D n (Work.WilG0.projLastIter n m X) := by
  -- Iterating the projection axiom `m` times: dimension `n+m → n`, format `F → F+m`.
  have key : ∀ m (F D : ℕ) (X : Set (Fin (n + m) → ℝ)),
      WilkiesDesign.E.Gen F D (n + m) X →
      WilkiesDesign.E.Gen (F + m) D n (Work.WilG0.projLastIter n m X) := by
    intro m
    induction m with
    | zero =>
      intro F D X hX
      simpa [Work.WilG0.projLastIter] using hX
    | succ m ih =>
      intro F D X hX
      have hX' : WilkiesDesign.E.Gen (F + 1) D (n + m) (projLast X) :=
        WilkiesDesign.E.Gen.proj hX
      have hres : WilkiesDesign.E.Gen ((F + 1) + m) D n
          (Work.WilG0.projLastIter n m (projLast X)) := ih (F + 1) D (projLast X) hX'
      have heq : (F + 1) + m = F + (m + 1) := by omega
      exact heq ▸ hres
  exact key m F D X h

end Work.WilE9.Glue
