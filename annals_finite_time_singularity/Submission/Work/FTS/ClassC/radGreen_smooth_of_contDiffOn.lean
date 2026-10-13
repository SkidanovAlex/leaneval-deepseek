/-
# `radGreen_smooth_of_contDiffOn` — smoothness of the radial Green's function

`Work.FTS.PhiStar.Radial.radGreen α m c` is the Green's function of the mode-`m` radial Euler
equation, in the explicit form

```
radGreen α m c z = K·( z^{s⁻}·∫₀^z c(t) t^{q-1} dt + z^{s⁺}·∫_{Ioi z} c(t) t^{-p-1} dt )
```
with `K = 1/(α(4m+5))`, `s⁻ = -q`, `s⁺ = p`, `q = (2m+5)/α`, `p = 2m/α`.

If the source `c` is `C^∞` on `(0,∞)` and the three integrability conditions

* `c·t^{q-1} ∈ L¹(0,1)`,   * `c·t^{-p-1} ∈ L¹(0,1)`,   * `c·t^{-p-1} ∈ L¹(1,∞)`

hold, then `radGreen α m c` is `C^n` on `(0,∞)` for every `n`.  None of the three is needed to
identify the derivatives (which only uses the fundamental theorem of calculus, hence local
integrability, available from the continuity of `c` together with the integrability at `0`); they
enter because the `0..z` interval integral must be differentiable, which uses that the integrand
is integrable near the lower limit `0`.

The scaffolding `rgiK`, `rgiSn`, `rgiSp`, `rgiF1`, `rgiF2`, `rgiA`, `rgiB` and the two
fundamental-theorem-of-calculus lemmas `rgiA_hasDerivAt`, `rgiB_hasDerivAt` (for the interval
integral and for the tail integral respectively) are the ones already proved in
`Submission/Work/FTS/PhiStar/Series/radGreenI_differentiableAt.lean`.  The only remaining step is
the general lemma `contDiffOn_of_hasDerivAt_of_contDiffOn` below: on an **open** set, a function
whose pointwise derivative is `C^∞` is itself `C^∞` (this is just the `n+1`-characterisation of
`ContDiffOn` by `deriv`, iterated — no induction is needed).
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Radial.radGreen_solves
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.Series.radGreenI_differentiableAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open MeasureTheory Set Filter

/-- **`C^∞` from the derivative.**  On an open set `s`, if `f` has pointwise derivative `f'` and
`f'` is `C^n` on `s` for every `n`, then so is `f`. -/
theorem contDiffOn_of_hasDerivAt_of_contDiffOn {f f' : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hder : ∀ x ∈ s, HasDerivAt f (f' x) x) (hf' : ∀ n : ℕ, ContDiffOn ℝ n f' s) :
    ∀ n : ℕ, ContDiffOn ℝ n f s := by
  intro n
  cases n with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun x hx => (hder x hx).continuousAt.continuousWithinAt
  | succ n =>
    rw [Nat.cast_add_one, contDiffOn_succ_iff_deriv_of_isOpen hs]
    refine ⟨fun x hx => (hder x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · intro h
      exact absurd h (by simp)
    · exact (contDiffOn_congr (fun x hx => (hder x hx).deriv)).mpr (hf' n)

/-- The power function `z ↦ z ^ p` is `C^n` on `(0,∞)` for every real exponent `p`. -/
theorem contDiffOn_rpow_Ioi (p : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun z : ℝ => z ^ p) (Set.Ioi 0) :=
  (isOpen_Ioi.contDiffOn_iff).mpr (by
    intro a ha
    exact Real.contDiffAt_rpow_const_of_ne (ne_of_gt ha))

/-- `rgiF1 α m c = fun t => c t * t^((2m+5)/α - 1)` is `C^n` on `(0,∞)`. -/
theorem contDiffOn_rgiF1 {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hc : ∀ n : ℕ, ContDiffOn ℝ n c (Set.Ioi 0)) :
    ∀ n : ℕ, ContDiffOn ℝ n (Work.FTS.PhiStar.Series.rgiF1 α m c) (Set.Ioi 0) := by
  intro n
  have h := (hc n).mul (contDiffOn_rpow_Ioi ((2 * (m : ℝ) + 5) / α - 1) n)
  exact h.congr (fun t _ => rfl)

/-- `rgiF2 α m c = fun t => c t * t^(-(2m/α) - 1)` is `C^n` on `(0,∞)`. -/
theorem contDiffOn_rgiF2 {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hc : ∀ n : ℕ, ContDiffOn ℝ n c (Set.Ioi 0)) :
    ∀ n : ℕ, ContDiffOn ℝ n (Work.FTS.PhiStar.Series.rgiF2 α m c) (Set.Ioi 0) := by
  intro n
  have h := (hc n).mul (contDiffOn_rpow_Ioi (-(2 * (m : ℝ) / α) - 1) n)
  exact h.congr (fun t _ => rfl)

/-- The interval integral `rgiA α m c z = ∫₀^z c t t^((2m+5)/α-1) dt` is `C^n` on `(0,∞)`. -/
theorem contDiffOn_rgiA {α : ℝ} (m : ℕ) {c : ℝ → ℝ}
    (hc : ∀ n : ℕ, ContDiffOn ℝ n c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1)) :
    ∀ n : ℕ, ContDiffOn ℝ n (Work.FTS.PhiStar.Series.rgiA α m c) (Set.Ioi 0) :=
  contDiffOn_of_hasDerivAt_of_contDiffOn isOpen_Ioi
    (Work.FTS.PhiStar.Series.rgiA_hasDerivAt (α := α) (m := m) (c := c)
      (hc 0).continuousOn h0)
    (contDiffOn_rgiF1 (α := α) (m := m) (c := c) hc)

/-- The tail integral `rgiB α m c z = ∫_{Ioi z} c t t^(-(2m/α)-1) dt` is `C^n` on `(0,∞)`. -/
theorem contDiffOn_rgiB {α : ℝ} (m : ℕ) {c : ℝ → ℝ}
    (hc : ∀ n : ℕ, ContDiffOn ℝ n c (Set.Ioi 0))
    (hinf : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    ∀ n : ℕ, ContDiffOn ℝ n (Work.FTS.PhiStar.Series.rgiB α m c) (Set.Ioi 0) :=
  contDiffOn_of_hasDerivAt_of_contDiffOn isOpen_Ioi
    (Work.FTS.PhiStar.Series.rgiB_hasDerivAt (α := α) (m := m) (c := c)
      (hc 0).continuousOn hinf)
    (fun n => (contDiffOn_rgiF2 (α := α) (m := m) (c := c) hc n).neg)

/-- The explicit Green's function written with the `rgi`-scaffolding (definitional). -/
theorem radGreen_eq_rgi (α : ℝ) (m : ℕ) (c : ℝ → ℝ) :
    (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z)
      = fun z => Work.FTS.PhiStar.Series.rgiK α m *
          (z ^ (Work.FTS.PhiStar.Series.rgiSn α m) * Work.FTS.PhiStar.Series.rgiA α m c z
            + z ^ (Work.FTS.PhiStar.Series.rgiSp α m) * Work.FTS.PhiStar.Series.rgiB α m c z) := by
  funext z
  rfl

theorem radGreen_smooth_of_contDiffOn {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ∀ n : ℕ, ContDiffOn ℝ n c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1))
    (h0' : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    ∀ n : ℕ, ContDiffOn ℝ n (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z) (Set.Ioi 0) := by
  intro n
  have hA : ContDiffOn ℝ n (Work.FTS.PhiStar.Series.rgiA α m c) (Set.Ioi 0) :=
    contDiffOn_rgiA (α := α) m hc h0 n
  have hB : ContDiffOn ℝ n (Work.FTS.PhiStar.Series.rgiB α m c) (Set.Ioi 0) :=
    contDiffOn_rgiB (α := α) m hc hinf n
  have hmain : ContDiffOn ℝ n (fun z => Work.FTS.PhiStar.Series.rgiK α m •
      (z ^ (Work.FTS.PhiStar.Series.rgiSn α m) * Work.FTS.PhiStar.Series.rgiA α m c z
        + z ^ (Work.FTS.PhiStar.Series.rgiSp α m) * Work.FTS.PhiStar.Series.rgiB α m c z))
      (Set.Ioi 0) :=
    ContDiffOn.const_smul (Work.FTS.PhiStar.Series.rgiK α m)
      (((contDiffOn_rpow_Ioi (Work.FTS.PhiStar.Series.rgiSn α m) n).mul hA).add
        ((contDiffOn_rpow_Ioi (Work.FTS.PhiStar.Series.rgiSp α m) n).mul hB))
  rw [radGreen_eq_rgi]
  simpa only [smul_eq_mul] using hmain

end Work.FTS.ClassC
