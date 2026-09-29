import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Lyap.lyap_nonneg
import Submission.Work.TMC7Core.LDT
import Submission.Work.TMC7Core.Scale.hasLEBound_Icc
import Submission.Work.TMC7Core.Scale.exists_approx_seq
import Submission.Work.TMC7Core.Scale.spectral_continuity

/-!
# TMC7Core: assembly of `P_BJ`

The lower half of the Bourgain--Jitomirskaya formula, `max 0 (log |lam|) ≤ lyap`, is Herman's
bound (`P_LEBasics.1`) plus `0 ≤ lyap`.

The upper half is assembled here from the three analytic inputs of the BJ route (all proved in
sibling files, modulo their own `Prop`-hypotheses):

* `hLDT` — the large deviation theorem with uniform constants (`Fourier/large_deviation`);
* `hCont` — continuity of `lyap` in `(α, E)` at points where `lyap > 0`, in the quantitative
  form produced by the scale chain (`Scale/lyap_continuous_pos`, from `prop9_final`);
* `hRat` — the rational (Floquet + Chambers) upper bound (`Solutions/rat_bound`).

The argument: if `L := lyap α₀ lam E > max 0 (log|λ|)`, take `κ = min (L/400) (1/100)` and the
LDT constants `(c,C,r)` at `(lam,E)`, replace `c` by `min c 1`, get the uniform energy bound
`C₀` from `hasLEBound_Icc`, and apply `hCont` with `ε = (L - M)/2` to get a neighbourhood on
which `lyap > (L+M)/2`.  Take a good rational approximant `a n / q n` of `α₀` (`q n → ∞`,
coprime, `|α₀ - a n/q n| < 1/q n²`) inside that neighbourhood, and `E' ∈ amoSpec (a n/q n) lam`
with `|E' - E|` small (`spectral_continuity`).  Then `hRat` bounds `lyap (a n/q n) lam E'` by
`M + log 6 / q n`, while continuity gives `lyap (a n/q n) lam E' > (L+M)/2`; choosing `q n`
large makes `M + log 6/q n < (L+M)/2`, a contradiction.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core

/-- Herman's bound plus `lyap ≥ 0`: the lower half of `P_BJ`. -/
theorem max_log_le_lyap (h4 : P_LEBasics) (α lam : ℝ) (E : ℂ) :
    max 0 (Real.log |lam|) ≤ lyap α lam E :=
  max_le (Work.TMC7Core.Lyap.lyap_nonneg α lam E) (h4.1 α lam E)

/-- `Icc (E-r) (E+r) ⊆ Icc (-(|E|+r)) (|E|+r)` for `r ≥ 0`. -/
theorem Icc_subset_Icc_abs {E r : ℝ} (hr : 0 ≤ r) :
    Set.Icc (E - r) (E + r) ⊆ Set.Icc (-(|E| + r)) (|E| + r) := by
  intro x hx
  have h1 : E - r ≤ x := hx.1
  have h2 : x ≤ E + r := hx.2
  have h3 : -( |E| + r) ≤ E - r := by linarith [neg_abs_le E]
  have h4 : E + r ≤ |E| + r := by linarith [le_abs_self E]
  exact ⟨by linarith, by linarith⟩

end Work.TMC7Core
