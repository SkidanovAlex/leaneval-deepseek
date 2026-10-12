import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.JointLim
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Layer 2 — the diagonal limit from continuity of the liminf function.

Write `x̲ ρ := diagLiminf v ρ` and `x̄ ρ := diagLimsup v ρ`.  With the upper
side (`diagLimsup_le_diagLiminf_of_lt`: `x̄ ρ ≤ x̲ ρ'` for every `ρ' > ρ`) the
diagonal limit at `ρ` exists as soon as `x̲` has no upward jump at `ρ`
(one-sided epsilon form `diagLiminf_right_lc`).  Combining that with the
window sandwich (`JointLim`) gives the thermodynamic-limit convergence
(`hconv`) of `e_ge_of_eventually_box_ge` under the single classical
hypothesis that the liminf function `ρ ↦ diagLiminf v ρ` is continuous on
`(0,ρ₀)` — continuity that is classically derived from convexity of the
canonical energy density (grand-canonical Legendre duality), the remaining
Layer-2 milestone.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Boundedness side conditions for the general liminf/limsup theorems -/

/-- `IsBoundedUnder (· ≤ ·)` from an eventual upper bound. -/
lemma isBoundedUnder_le_of_eventually_le {u : ℝ → ℝ} {B : ℝ}
    (hB : ∀ᶠ L : ℝ in atTop, u L ≤ B) : atTop.IsBoundedUnder (· ≤ ·) u := by
  refine ⟨B, ?_⟩
  simpa [Filter.eventually_map] using hB

/-- `IsBoundedUnder (· ≥ ·)` from an eventual lower bound. -/
lemma isBoundedUnder_ge_of_eventually_ge {u : ℝ → ℝ} {b : ℝ}
    (hb : ∀ᶠ L : ℝ in atTop, b ≤ u L) : atTop.IsBoundedUnder (· ≥ ·) u := by
  refine ⟨b, ?_⟩
  simpa [Filter.eventually_map] using hb

/-- `IsBoundedUnder (· ≤ ·)` for the diagonal (upper bound at nonnegative density). -/
lemma diag_isBoundedUnder_le {v : ℝ³ → ℝ} {ρ : ℝ} (hv1 : MemLp v 1) (hρ : 0 ≤ ρ) :
    atTop.IsBoundedUnder (· ≤ ·) (fun L : ℝ => diag v ρ L) := by
  rcases diag_eventually_bdd_above hv1 hρ with ⟨B, hB⟩
  exact isBoundedUnder_le_of_eventually_le hB

/-- `IsBoundedUnder (· ≥ ·)` for the diagonal (lower bound `0`). -/
lemma diag_isBoundedUnder_ge {v : ℝ³ → ℝ} {ρ : ℝ} (hv : 0 ≤ v) :
    atTop.IsBoundedUnder (· ≥ ·) (fun L : ℝ => diag v ρ L) :=
  isBoundedUnder_ge_of_eventually_ge (diag_eventually_nonneg hv)

/-! ## The diagonal limit at a single density -/

/-- If the liminf and limsup of the diagonal agree, the diagonal converges to
their common value. -/
lemma diag_tendsto_of_liminf_eq_limsup {v : ℝ³ → ℝ} {ρ : ℝ} (hv : 0 ≤ v)
    (hv1 : MemLp v 1) (hρ : 0 ≤ ρ) (heq : diagLiminf v ρ = diagLimsup v ρ) :
    Tendsto (fun L : ℝ => diag v ρ L) atTop (𝓝 (diagLiminf v ρ)) := by
  have hinf : diagLiminf v ρ ≤ Filter.liminf (fun L : ℝ => diag v ρ L) atTop := le_rfl
  have hsup : Filter.limsup (fun L : ℝ => diag v ρ L) atTop ≤ diagLiminf v ρ := by
    exact heq.symm.le
  exact tendsto_of_le_liminf_of_limsup_le hinf hsup
    (diag_isBoundedUnder_le (v := v) (ρ := ρ) hv1 hρ)
    (diag_isBoundedUnder_ge (v := v) (ρ := ρ) hv)

/-- One-sided (right) local continuity of the liminf function at `ρ`, in the
weak epsilon form needed to close the upper side: arbitrarily close densities
`ρ' > ρ` have `x̲ ρ'` at most `x̲ ρ + ε`. -/
def diagLiminf_right_lc (v : ℝ³ → ℝ) (ρ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ ρ' : ℝ, ρ < ρ' ∧ diagLiminf v ρ' < diagLiminf v ρ + ε

/-- Continuity of the liminf function at `ρ` implies the one-sided form. -/
lemma diagLiminf_right_lc_of_continuousAt {v : ℝ³ → ℝ} {ρ : ℝ}
    (hcont : ContinuousAt (diagLiminf v) ρ) : diagLiminf_right_lc v ρ := by
  intro ε hε
  rcases Metric.continuousAt_iff.mp hcont ε hε with ⟨δ, hδ, hδ'⟩
  refine ⟨ρ + δ / 2, by linarith, ?_⟩
  -- |x̲(ρ+δ/2) − x̲ρ| < ε ⟹ x̲(ρ+δ/2) < x̲ρ + ε
  have harg : dist (ρ + δ / 2) ρ < δ := by
    rw [Real.dist_eq]
    rw [show (ρ + δ / 2) - ρ = δ / 2 by ring, abs_of_pos (by positivity : 0 < δ / 2)]
    linarith
  have hd := hδ' harg
  change |diagLiminf v (ρ + δ / 2) - diagLiminf v ρ| < ε at hd
  rw [abs_lt] at hd
  nlinarith

/-- Closing the upper side at `ρ`: if the liminf function has no upward jump
at `ρ` then the limsup of the diagonal is `≤` its liminf. -/
lemma diagLimsup_le_diagLiminf_of_right_lc {v : ℝ³ → ℝ} {ρ : ℝ} (hv : 0 ≤ v)
    (hv1 : MemLp v 1) {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hρ : 0 ≤ ρ) (hrc : diagLiminf_right_lc v ρ) :
    diagLimsup v ρ ≤ diagLiminf v ρ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  rcases hrc ε hε with ⟨ρ', hρρ', hbd⟩
  have hup := diagLimsup_le_diagLiminf_of_lt (v := v) (ρ := ρ) (ρ' := ρ') hv hv1 hR hsupp hρ hρρ'
  -- x̄ρ ≤ x̲ρ' < x̲ρ + ε
  have : diagLimsup v ρ ≤ diagLiminf v ρ + ε := le_of_lt (lt_of_le_of_lt hup hbd)
  simpa [diagLiminf] using this

/-- The diagonal limit at `ρ` exists (equal to the liminf) under the one-sided
epsilon condition on the liminf function. -/
lemma diag_tendsto_of_right_lc {v : ℝ³ → ℝ} {ρ : ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) (hρ : 0 ≤ ρ)
    (hrc : diagLiminf_right_lc v ρ) :
    Tendsto (fun L : ℝ => diag v ρ L) atTop (𝓝 (diagLiminf v ρ)) := by
  apply diag_tendsto_of_liminf_eq_limsup hv hv1 hρ
  apply le_antisymm
  · exact diagLiminf_le_diagLimsup hv hv1 hρ
  · exact diagLimsup_le_diagLiminf_of_right_lc hv hv1 hR hsupp hρ hrc

/-! ## The thermodynamic limit from continuity of the liminf function -/

/-- On `(0,ρ₀)`, continuity of `x̲ := diagLiminf v` gives the diagonal limit at
every point of the interval. -/
lemma diag_tendsto_of_continuous_on {v : ℝ³ → ℝ} {ρ : ℝ} (hv : 0 ≤ v)
    (hv1 : MemLp v 1) {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R)
    {ρ₀ : ℝ} (hρ : 0 < ρ) (hρ₀ : ρ < ρ₀)
    (hcont : ∀ ρ' : ℝ, 0 < ρ' → ρ' < ρ₀ → ContinuousAt (diagLiminf v) ρ') :
    Tendsto (fun L : ℝ => diag v ρ L) atTop (𝓝 (diagLiminf v ρ)) := by
  exact diag_tendsto_of_right_lc (v := v) (ρ := ρ) hv hv1 hR hsupp (le_of_lt hρ)
    (diagLiminf_right_lc_of_continuousAt (hcont ρ hρ hρ₀))

/-- The `hconv` convergence of the box densities along the joint filter, at
every density of `(0,ρ₀)`, under continuity of the liminf function there. -/
lemma tendsto_boxDensity_of_liminf_continuous_on {v : ℝ³ → ℝ} {ρ : ℝ} (hv : 0 ≤ v)
    (hv1 : MemLp v 1) {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R)
    {ρ₀ : ℝ} (hρ : 0 < ρ) (hρ₀ : ρ < ρ₀)
    (hcont : ∀ ρ' : ℝ, 0 < ρ' → ρ' < ρ₀ → ContinuousAt (diagLiminf v) ρ') :
    Tendsto (boxDensity v) (jointFilter ρ) (𝓝 (diagLiminf v ρ)) := by
  exact tendsto_boxDensity_of_diag_limits_on (v := v) (ρ := ρ) (ρ₀ := ρ₀) (x := diagLiminf v)
    hv hv1 hρ hρ₀ (hcont ρ hρ hρ₀)
    (fun ρ' hρ' hρ'₀ =>
      diag_tendsto_of_right_lc (v := v) (ρ := ρ') hv hv1 hR hsupp (le_of_lt hρ')
        (diagLiminf_right_lc_of_continuousAt (hcont ρ' hρ' hρ'₀)))

/-- Eventual form of `hconv`: continuity of the liminf function on `(0,ρ₀)`
gives convergence of the box densities along the joint filter at every small
density. -/
lemma eventually_hconv_of_liminf_continuous {v : ℝ³ → ℝ} (hv : 0 ≤ v)
    (hv1 : MemLp v 1) {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hcont : ∀ ρ' : ℝ, 0 < ρ' → ρ' < ρ₀ → ContinuousAt (diagLiminf v) ρ') :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ x : ℝ, Tendsto (boxDensity v) (jointFilter ρ) (𝓝 x) := by
  have hlt : ∀ᶠ ρ : ℝ in 𝓝[>] (0 : ℝ), ρ < ρ₀ := by
    have hio : ∀ᶠ y : ℝ in 𝓝 (0 : ℝ), y < ρ₀ := isOpen_Iio.mem_nhds hρ₀
    exact hio.filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hlt] with ρ hρpos hρlt
  refine ⟨diagLiminf v ρ, ?_⟩
  exact tendsto_boxDensity_of_liminf_continuous_on (v := v) (ρ := ρ) hv hv1 hR hsupp
    hρpos hρlt hcont

end BoseGases

end Submission
