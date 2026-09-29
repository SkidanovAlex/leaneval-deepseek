import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.IvMSpec
import Submission.Work.CNum.NrmSpec

/-!
# `Work.CNum.CpxSound` — soundness of the complex-interval layer `Cpx`

`Cpx` (in `Fx`) is a pair of `Iv`s, i.e. a rectangle in `ℂ`, with membership
`Cpx.Mem I z ↔ I.re.Mem z.re ∧ I.im.Mem z.im`.  This module proves that the operations
`add`, `neg`, `sub`, `mul`, `mulr`, `pt` are sound, using the real interval lemmas of
`Work.ANum.Ivl` (`mem_add`, `mem_neg`, `mem_sub`, `mem_sq`) and the four-corner multiplication
soundness `IvMSpec`.
-/

namespace Work.CNum

open Work.ANum

theorem mem_add {I J : Cpx} {z w : ℂ} (hz : I.Mem z) (hw : J.Mem w) :
    (Cpx.add I J).Mem (z + w) := by
  refine ⟨?_, ?_⟩
  · simpa [Cpx.add, Cpx.Mem, Complex.add_re] using Iv.mem_add hz.1 hw.1
  · simpa [Cpx.add, Cpx.Mem, Complex.add_im] using Iv.mem_add hz.2 hw.2

theorem mem_neg {I : Cpx} {z : ℂ} (hz : I.Mem z) : (Cpx.neg I).Mem (-z) := by
  refine ⟨?_, ?_⟩
  · simpa [Cpx.neg, Cpx.Mem, Complex.neg_re] using Iv.mem_neg hz.1
  · simpa [Cpx.neg, Cpx.Mem, Complex.neg_im] using Iv.mem_neg hz.2

theorem mem_sub {I J : Cpx} {z w : ℂ} (hz : I.Mem z) (hw : J.Mem w) :
    (Cpx.sub I J).Mem (z - w) := by
  refine ⟨?_, ?_⟩
  · simpa [Cpx.sub, Cpx.Mem, Complex.sub_re] using Iv.mem_sub hz.1 hw.1
  · simpa [Cpx.sub, Cpx.Mem, Complex.sub_im] using Iv.mem_sub hz.2 hw.2

theorem mem_mul {I J : Cpx} {z w : ℂ} (hz : I.Mem z) (hw : J.Mem w) :
    (Cpx.mul I J).Mem (z * w) := by
  refine ⟨?_, ?_⟩
  · simpa [Cpx.mul, Cpx.Mem, Complex.mul_re] using
      Iv.mem_sub (IvMSpec hz.1 hw.1) (IvMSpec hz.2 hw.2)
  · simpa [Cpx.mul, Cpx.Mem, Complex.mul_im] using
      Iv.mem_add (IvMSpec hz.1 hw.2) (IvMSpec hz.2 hw.1)

theorem mem_mulr {I : Cpx} {r : Iv} {z : ℂ} {s : ℝ} (hz : I.Mem z) (hr : r.Mem s) :
    (Cpx.mulr I r).Mem (z * (s : ℂ)) := by
  refine ⟨?_, ?_⟩
  · simpa [Cpx.mulr, Cpx.Mem, Complex.mul_re] using IvMSpec hz.1 hr
  · simpa [Cpx.mulr, Cpx.Mem, Complex.mul_im] using IvMSpec hz.2 hr

end Work.CNum
