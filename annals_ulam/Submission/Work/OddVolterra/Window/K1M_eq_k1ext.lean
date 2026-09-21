import Mathlib
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.Window.fed_faaDiBruno_recursion
import Submission.Work.OddVolterra.Window.KvecDefs

/-!
# The manifest denominator `K1M` is the diagonal extension `k1ext`

`KernelExt.K1M n h a σ t = J1M n h a σ t / Kden h a σ t` is the manifest (polynomial) form of the
first Abel kernel, the quotient of the Bell numerator `J1M = Rnu (n+1/2) h 1 (n+1)` by the square
root of the radicand `krad h σ t a`; `Work.OddVolterra.k1ext n h σ t a` is the diagonal extension
of `K1` written with the Faà-di-Bruno polynomial evaluated at the jet of the radicand.

The two agree for **every** `a σ t`, with no order condition between `a` and `σ`:

* `Work.Window.fed_faaDiBruno_recursion` (part 2) identifies `J1M n h a σ t` with
  `faaDiBrunoJ (n+1) ((n:ℝ)+1/2) 0` applied to the `a`-jet of `Zrad h (·,σ,t)`, for all `a σ t`;
* `Work.OddVolterra.Window.kjet_eq_Zrad` rewrites that jet as the `kjet` jet used by `k1ext`;
* the Faà-di-Bruno polynomial is *independent of its third (base point) argument*, which is a
  dummy in `Commons.Geometry.Ulam.faaDiBrunoJ`, so the two slots agree as well.
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

theorem K1M_eq_k1ext (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (a σ t : ℝ) :
    Work.OddVolterra.KernelExt.K1M n h a σ t = Work.OddVolterra.k1ext n h σ t a := by
  have h1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have hJ := (Work.Window.fed_faaDiBruno_recursion 0 (0 : ℝ) (fun _ : Fin 2 => (0 : ℝ))).2
    n h hh a σ t
  have hjet : (fun i : Fin (n + 2) => Work.OddVolterra.kjet h σ t a i.1)
      = fun i : Fin (n + 2) =>
          iteratedDeriv i.1 (fun x : ℝ => Work.OddVolterra.KernelExt.Zrad h (x, σ, t)) a := by
    funext i
    exact Work.OddVolterra.Window.kjet_eq_Zrad h1 σ t a i.1
  rw [Work.OddVolterra.KernelExt.K1M, Work.OddVolterra.k1ext, hJ, hjet,
    Work.OddVolterra.Kden_eq_sqrt_krad]
  congr 1

end Work.OddVolterra.Window
