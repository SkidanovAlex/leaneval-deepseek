/-
# `Work.FTS.PhiStar.FlatWAux.RadGreenExpansionPhiAj`

The `J`-fold `1/λ_m`-expansion of the mode-`m` radial Green function at the source `φ = phiA α`:

`radGreen α m φ = Σ_{j<J} (α^j/λ_m^{j+1})·(𝒜^j φ) + (α^J/λ_m^J)·radGreen α m (𝒜^J φ)`,

`𝒜 = αz²∂² + (5+α)z∂`, `λ_m = 2m(2m+5)`, `J = 8`.

The expansion itself is the purely algebraic `FlatWAux.radGreen_expansion`, whose input is the
one-step resolvent identity `λ_m·radGreen α m c = c + α·radGreen α m (𝒜 c)` at every level
`c = 𝒜^j φ`, `j ≤ J`.  That identity is the existing `FlatWAux.radGreen_step`, but its hypothesis
list contains, besides the hypotheses of the ODE `radGreen_solves`, the extra integrability
condition

`IntegrableOn (fun t => c t · t^{-2m/α-1}) (Ioo 0 1)`

— which its proof never uses (`Radial/radGreenIntended.lean`'s `radGreenI_solves` binds it and
never refers to it, and `RadGreenSupport/radGreen_ode_weak.lean` records the ODE without it) and
which is **false** for the sources of this expansion: `𝒜^j φ` vanishes only to first order at
`z = 0` (`Ajit α j (phiA α) = phiAj (j+1) α = P(z)/(1+z)^{2j+2}` with `P(0) = 0`, `P'(0) ≠ 0`),
so `c t · t^{-2m/α-1} ∼ C·t^{-2m/α}` is not integrable near `0` for `m ≥ 1`.

Here the one-step identity is therefore re-derived from the *weak* ODE
`RadGreenSupport.radGreen_ode_weak` (same statement, hypotheses `hc`, `h0`, `hinf` only),
together with the already proved commutator identity `RadGreenActA`; the resulting
`radGreen_step_weak` has exactly the hypothesis list that the sources `𝒜^j φ` satisfy.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.FlatWAux.Expansion
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.RadGreenActA
import Submission.Work.FTS.PhiStar.Radial.radGreen_solves
import Submission.Work.FTS.PhiStar.FlatWAux.PhiAjFlatDecayU
import Submission.Work.FTS.PhiStar.PhiAjFlatDecay
import Submission.Work.FTS.PhiStar.phiAj_smooth2
import Submission.Work.FTS.VocabO

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

open scoped ContDiff

set_option autoImplicit false

/-! ## 1. `𝒜^j φ` is `C^∞` at every `z > 0` -/

/-- **`𝒜^j φ` is `C^∞` at every `z > 0`.**  Induction on `j`: `φ` is the explicit rational
function `4αz²(z−2)/(1+z)⁴ + 2(5+α)z(1−z)/(1+z)³` (`contDiffAt_phiA`), and the step is a sum of
products of the smooth `z²`, `z` with the first and second iterated derivatives of a `C^∞`
function. -/
theorem contDiffAt_Ajit_phiA_infty (α : ℝ) (j : ℕ) {z : ℝ} (hz : 0 < z) :
    ContDiffAt ℝ ∞ (Ajit α j (Work.FTS.VocabO.phiA α)) z := by
  induction j with
  | zero => simpa only [Ajit_zero] using Work.FTS.PhiStar.contDiffAt_phiA α hz
  | succ j ih =>
      rw [Ajit_succ]
      exact (((contDiffAt_const (c := α)).mul (contDiffAt_id.pow 2)).mul
          (Work.FTS.PhiStar.contDiffAt_infty_iteratedDeriv 2 ih)).add
        (((contDiffAt_const (c := (5 + α))).mul contDiffAt_id).mul
          (Work.FTS.PhiStar.contDiffAt_infty_deriv ih))

/-- The `ContDiffOn` form of `contDiffAt_Ajit_phiA_infty` at order `2`. -/
theorem contDiffOn_Ajit_phiA_two (α : ℝ) (j : ℕ) :
    ContDiffOn ℝ 2 (Ajit α j (Work.FTS.VocabO.phiA α)) (Set.Ioi 0) :=
  fun z hz =>
    ((contDiffAt_Ajit_phiA_infty α j hz).of_le (by simp : ((2 : ℕ∞ω)) ≤ ∞)).contDiffWithinAt

/-! ## 2. The one-step resolvent identity without the redundant integrability hypothesis -/

/-- **The mode-`m` resolvent identity** `λ_m·R = c + A R` under the *weak* hypothesis set of
`RadGreenSupport.radGreen_ode_weak`: no integrability of `c t·t^{-2m/α-1}` on `(0,1)`. -/
theorem radGreen_resolvent_weak {α : ℝ} (m : ℕ) {c : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hα : 0 < α) (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    Work.FTS.PhiStar.Radial.lamR m * Work.FTS.PhiStar.Radial.radGreen α m c z
      = c z + (α ^ 2 * z ^ 2 *
            deriv (deriv (Work.FTS.PhiStar.Radial.radGreen α m c)) z
          + α * (5 + α) * z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z) := by
  have h := Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak hα m hc h0 hinf z hz
  linarith [h]

/-- **The one-step resolvent identity** `R_m c = c/λ_m + (α/λ_m)·R_m(𝒜c)` in the form needed by
the `1/λ_m`-expansion; compared with `radGreen_step` the hypothesis
`IntegrableOn (fun t => c t·t^{-2m/α-1}) (Ioo 0 1)` is dropped (it is unused, and it fails for
`c = 𝒜^j φ`). -/
theorem radGreen_step_weak {α : ℝ} (m : ℕ) (hα : 0 < α) (hα5 : α ≤ 1 / 5) (hm : 1 ≤ m)
    {c : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A) (hc : ContDiffOn ℝ 2 c (Set.Ioi 0))
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ t : ℝ, 0 < t →
      |iteratedDeriv k c t| ≤ A / (1 + t ^ (k + 1)))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z → Work.FTS.PhiStar.Radial.radGreen α m c z
      = c z / Work.FTS.PhiStar.Radial.lamR m
        + (α / Work.FTS.PhiStar.Radial.lamR m)
            * Work.FTS.PhiStar.Radial.radGreen α m (Ajit α 1 c) z := by
  intro z hz
  have hres := radGreen_resolvent_weak m hz hα hc.continuousOn h0 hinf
  have hact := RadGreenActA (α := α) m hα hα5 hm hA hc hb z hz
  have hstep : Work.FTS.PhiStar.Radial.radGreen α m (Ajit α 1 c) z
      = α * z ^ 2 * iteratedDeriv 2 (Work.FTS.PhiStar.Radial.radGreen α m c) z
        + (5 + α) * z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z := by
    rw [Ajit_succ]
    exact hact
  have hite : iteratedDeriv 2 (Work.FTS.PhiStar.Radial.radGreen α m c) z
      = deriv (deriv (Work.FTS.PhiStar.Radial.radGreen α m c)) z := by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have hkey : Work.FTS.PhiStar.Radial.lamR m
      * Work.FTS.PhiStar.Radial.radGreen α m c z
      = c z + α * Work.FTS.PhiStar.Radial.radGreen α m (Ajit α 1 c) z := by
    rw [hres, hstep, hite]
    ring
  have hne := lamR_ne_zero hm
  field_simp
  linarith [hkey]

/-! ## 3. The expansion -/

theorem RadGreenExpansionPhiAj : ∀ (α : ℝ), 0 < α → α ≤ 1 / 5 → ∀ (m : ℕ), 1 ≤ m → ∀ z : ℝ, 0 < z →
    Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z
      = (∑ j ∈ Finset.range Work.FTS.PhiStar.FlatWAux.J,
          (α ^ j / (Work.FTS.PhiStar.Radial.lamR m) ^ (j + 1))
            * Work.FTS.PhiStar.FlatWAux.Ajit α j (Work.FTS.VocabO.phiA α) z)
        + (α ^ Work.FTS.PhiStar.FlatWAux.J
            / (Work.FTS.PhiStar.Radial.lamR m) ^ Work.FTS.PhiStar.FlatWAux.J)
            * Work.FTS.PhiStar.Radial.radGreen α m
                (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                  (Work.FTS.VocabO.phiA α)) z := by
  intro α hα hα5 m hm z hz
  obtain ⟨A, hApos, hA⟩ := PhiAjFlatDecayU
  refine radGreen_expansion (z := z) m (Work.FTS.VocabO.phiA α) J (lamR_ne_zero hm) ?_
  intro j hj
  have hj8 : j ≤ 8 := hj
  have hj9 : j + 1 ≤ 9 := by omega
  have hsmooth : ContDiffOn ℝ 2 (Ajit α j (Work.FTS.VocabO.phiA α)) (Set.Ioi 0) :=
    contDiffOn_Ajit_phiA_two α j
  have hb : ∀ k : ℕ, k ≤ 2 → ∀ t : ℝ, 0 < t →
      |iteratedDeriv k (Ajit α j (Work.FTS.VocabO.phiA α)) t| ≤ A / (1 + t ^ (k + 1)) := by
    intro k hk t ht
    have hk14 : k ≤ 14 := by omega
    simpa only [Ajit_phiA α j] using (hA α hα hα5 (j + 1) hj9).1 k hk14 t ht
  obtain ⟨h0, hinf⟩ :=
    Work.FTS.PhiStar.RadGreenSupport.src_integrable hα m hApos.le hsmooth hb
  have hstep := radGreen_step_weak (α := α) m hα hα5 hm hApos.le hsmooth hb h0 hinf z hz
  simpa only [Ajit_succ, Ajit_zero] using hstep

end Work.FTS.PhiStar.FlatWAux
