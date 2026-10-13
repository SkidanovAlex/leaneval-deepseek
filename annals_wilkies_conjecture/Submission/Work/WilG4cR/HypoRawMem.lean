/-
  WilG4cR / `HypoRawMem` — a **clean** copy of `Work.WilkG4c.CritAux.hypoRaw_mem` (module
  `Submission/Work/WilG4c/CritAux/hypoRaw_mem.lean`).  The original proof reduces `HypoRaw` to
  `HypoBuild` through the two `sorry`-stubs `hypoRaw_eq_hypoRawE` / `hypoBuild_eq_hypoRawE`, hence
  carries `sorryAx`; here the reduction is the proved `Work.WilG4cR.HypoRaw_eq_HypoBuild`, and the
  `Ω`-bookkeeping `HypoBuild_mem` (proved, `sorry`-free) does the rest.

  `HypoRaw p n X` is the *ball-condensation* of `X`: the set of is `u` such that some fibre ball
  around `u` lies in `X`.  This is the operator that turns the pointwise `ε`-`δ` criterion
  `UVFix` into the localised one `LocCritFix`, and it is what `CritFixMem` consumes.
-/
import Mathlib
import Submission.Work.WilG4c.CritAux
import Submission.Work.WilG4c.CritAux.HypoDefs
import Submission.Work.WilG4c.CritAux.hypoRaw_mem
import Submission.Work.WilG4cR.HypoRaw_eq_HypoBuild
import Submission.Work.WilG4a.liftNM_mem

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4cR

open WilkiesDesign

theorem hypoRaw_mem (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (F D : ℕ) (X : Set (Fin (p + (n + 1)) → ℝ)),
      X ∈ S.Ω F D (p + (n + 1)) →
      Work.WilkG4c.HypoRaw p n X ∈ S.Ω (F + a) (b.eval D) (p + (n + 1)) := by
  refine ⟨3 * Work.WilkG4c.hypoM p n + 3 * Work.WilkG4c.hypoN p n + (n + 1) + 12,
    Polynomial.X + Polynomial.C 9, ?_⟩
  intro F D X hX
  have hbuild := Work.WilG4c.CritAux.HypoBuild_mem S p n F D X hX
  have hraw : Work.WilkG4c.HypoRaw p n X ∈
      S.Ω (F + (3 * Work.WilkG4c.hypoM p n + 3 * Work.WilkG4c.hypoN p n + (n + 1) + 12))
        (D + 9) (p + (n + 1)) := by
    rw [Work.WilG4cR.HypoRaw_eq_HypoBuild p n X]
    exact hbuild
  refine Work.WilG4a.mem_mono hraw le_rfl ?_
  simp [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

end Work.WilG4cR
