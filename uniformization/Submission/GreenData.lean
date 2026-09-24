import ChallengeDeps
import Submission.Holomorphic

/-!
# Green-function data: from the classical construction to the endgame hypotheses

The classical construction of the uniformization of a *hyperbolic* Riemann surface `X` produces

* a positive harmonic function `E : X → ℝ`, harmonic off a point `z₀`, with a logarithmic pole at
  `z₀` and `E → 0` at infinity, and
* a holomorphic function `Φ : X → ℂ` whose modulus is `exp (-E)` (explicitly `Φ = exp (-(G + iG*))`
  where `G*` is the harmonic conjugate of the Green function `G`).

The purpose of this module is to record, in the exact form consumed by the endgame interface
(`Submission.uniformization_of_proper_single_zero_disc`, in the *corrected* version where the
properness hypothesis is only required for compact subsets of the disc), the elementary
consequences of that data:

* `Φ z₀ = 0` (`Submission.phi_zero_of_logPole`);
* the zero is simple, i.e. the chart derivative at `z₀` does not vanish
  (`Submission.phi_deriv_ne_zero_of_logPole`);
* `Φ` maps `X` into the open unit disc (`Submission.phi_mem_ball`);
* `Φ ⁻¹' {0} = {z₀}` (`Submission.phi_preimage_zero`);
* `Φ` is *proper into the disc*: the preimage of every compact subset of the disc is compact
  (`Submission.isCompact_preimage_of_green`), which is exactly the hypothesis needed by the
  corrected endgame.

Note the *absence* of a boundedness/topological hypothesis on `X`: none of the statements below
uses compactness of `X` or of its exhaustion.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The logarithmic-pole hypothesis**: near `z₀`, in the preferred chart at `z₀`, the function
`Φ` looks like `w ↦ (w - w₀) * H w` with `H` analytic at `w₀` and `H w₀ ≠ 0`.  This is exactly the
statement that `Φ` has a simple zero at `z₀` of multiplicity one (and it implies in particular
that `Φ` vanishes there). -/
def HasLogPoleAt (z₀ : X) (Φ : X → ℂ) : Prop :=
  ∃ H : ℂ → ℂ, AnalyticAt ℂ H ((chartAt ℂ z₀) z₀) ∧ H ((chartAt ℂ z₀) z₀) ≠ 0 ∧
    (Φ ∘ (chartAt ℂ z₀).symm) =ᶠ[𝓝 ((chartAt ℂ z₀) z₀)]
      (fun w : ℂ => (w - (chartAt ℂ z₀) z₀) * H w)

/-- **The pole forces `Φ z₀ = 0`.** -/
theorem phi_zero_of_logPole {z₀ : X} {Φ : X → ℂ} (hΦ : HolomorphicOnX Φ univ)
    (hpole : HasLogPoleAt z₀ Φ) : Φ z₀ = 0 := by
  obtain ⟨H, hHana, _, hev⟩ := hpole
  set c := chartAt ℂ z₀ with hc
  set a : ℂ := c z₀ with ha
  have hsrc : z₀ ∈ c.source := mem_chart_source ℂ z₀
  have hsymm_a : c.symm a = z₀ := c.left_inv hsrc
  have htend_c : Tendsto c.symm (𝓝 a) (𝓝 z₀) := c.tendsto_symm hsrc
  have htend1 : Tendsto (Φ ∘ c.symm) (𝓝 a) (𝓝 (Φ z₀)) :=
    ((hΦ z₀ (mem_univ z₀)).continuousAt).tendsto.comp htend_c
  have htend2 : Tendsto (Φ ∘ c.symm) (𝓝 a) (𝓝 0) := by
    have hmul : Tendsto (fun w : ℂ => (w - a) * H w) (𝓝 a) (𝓝 ((a - a) * H a)) :=
      ((tendsto_id.sub tendsto_const_nhds).mul hHana.continuousAt)
    have h0 : ((a - a) * H a) = 0 := by simp
    rw [h0] at hmul
    exact hmul.congr' hev.symm
  exact tendsto_nhds_unique htend1 htend2

/-- **The zero at `z₀` is simple**: the derivative of `Φ` in the preferred chart at `z₀` does not
vanish. -/
theorem phi_deriv_ne_zero_of_logPole {z₀ : X} {Φ : X → ℂ} (hpole : HasLogPoleAt z₀ Φ) :
    deriv (Φ ∘ (chartAt ℂ z₀).symm) ((chartAt ℂ z₀) z₀) ≠ 0 := by
  obtain ⟨H, hHana, hHne, hev⟩ := hpole
  set c := chartAt ℂ z₀ with hc
  set a : ℂ := c z₀ with ha
  have hev' : (Φ ∘ c.symm) =ᶠ[𝓝 a] (fun w : ℂ => (w - a) * H w) := hev
  have hderiv : deriv (Φ ∘ c.symm) a = deriv (fun w : ℂ => (w - a) * H w) a := hev'.deriv_eq
  rw [hderiv]
  have hf : HasDerivAt (fun w : ℂ => w - a) 1 a := by
    simpa using (hasDerivAt_id a).sub_const a
  have hg : HasDerivAt H (deriv H a) a := hHana.differentiableAt.hasDerivAt
  have hprod := hf.mul hg
  have hval : deriv (fun w : ℂ => (w - a) * H w) a = H a := by
    have hd : deriv (fun w : ℂ => (w - a) * H w) a = deriv ((fun w : ℂ => w - a) * H) a := rfl
    rw [hd, hprod.deriv]
    simp
  rw [hval]
  exact hHne

/-- `Φ` maps `X` into the open unit disc, as soon as `E > 0` off `z₀` and `Φ z₀ = 0`. -/
theorem phi_mem_ball {z₀ : X} {E : X → ℝ} {Φ : X → ℂ}
    (hpos : ∀ x, x ≠ z₀ → 0 < E x) (hmod : ∀ x, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x)))
    (hzero : Φ z₀ = 0) (x : X) : Φ x ∈ Metric.ball (0 : ℂ) 1 := by
  rw [Metric.mem_ball, dist_eq_norm, sub_zero]
  rcases eq_or_ne x z₀ with rfl | hx
  · rw [hzero, norm_zero]; norm_num
  · rw [hmod x hx, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith [hpos x hx])

/-- `Φ ⁻¹' {0} = {z₀}`. -/
theorem phi_preimage_zero {z₀ : X} {E : X → ℝ} {Φ : X → ℂ}
    (hpos : ∀ x, x ≠ z₀ → 0 < E x) (hmod : ∀ x, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x)))
    (hzero : Φ z₀ = 0) : Φ ⁻¹' {0} = {z₀} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hx
    by_contra hne
    have h1 : ‖Φ x‖ = Real.exp (-(E x)) := hmod x hne
    rw [hx, norm_zero] at h1
    have h2 := Real.exp_pos (-(E x))
    linarith
  · intro hx
    rw [hx]
    exact hzero

/-- **Properness into the disc.**  If `E` is positive off `z₀`, `‖Φ x‖ = exp (-E x)` there, and the
superlevel sets `{E ≥ ε}` (`ε > 0`) are compact, then the preimage of every compact subset of the
open unit disc is compact.  This is the corrected (satisfiable) properness hypothesis for the
hyperbolic endgame. -/
theorem isCompact_preimage_of_green {z₀ : X} {E : X → ℝ} {Φ : X → ℂ}
    (hpos : ∀ x, x ≠ z₀ → 0 < E x) (hmod : ∀ x, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x)))
    (hzero : Φ z₀ = 0)
    (hinf : ∀ ε : ℝ, 0 < ε → IsCompact {x : X | ε ≤ E x})
    (hcont : Continuous Φ) {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ Metric.ball (0 : ℂ) 1) :
    IsCompact (Φ ⁻¹' K) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨w₀, hw₀K, hw₀max⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
  set r : ℝ := ‖w₀‖ with hr
  have hw₀lt : r < 1 := by
    have h := hKsub hw₀K
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h
    exact h
  have hrle : 0 ≤ r := norm_nonneg w₀
  have hpre0 : Φ ⁻¹' {0} = {z₀} := phi_preimage_zero hpos hmod hzero
  have hclosed : IsClosed (Φ ⁻¹' K) := hK.isClosed.preimage hcont
  rcases eq_or_ne r 0 with hr0 | hrne
  · have hKsub' : K ⊆ {0} := by
      intro z hz
      have h1 : ‖z‖ ≤ r := hw₀max hz
      rw [hr0] at h1
      simp only [Set.mem_singleton_iff]
      exact norm_eq_zero.mp (le_antisymm h1 (norm_nonneg z))
    have hpre : Φ ⁻¹' K ⊆ {z₀} := by
      intro x hx
      have h2 : Φ x = 0 := hKsub' hx
      have hx0 : x ∈ Φ ⁻¹' {0} := by simpa using h2
      rw [hpre0] at hx0
      exact hx0
    exact IsCompact.of_isClosed_subset isCompact_singleton hclosed hpre
  · have hrpos : 0 < r := lt_of_le_of_ne hrle (Ne.symm hrne)
    have hlog : Real.log r < 0 := Real.log_neg hrpos hw₀lt
    have hcomp : IsCompact ({x : X | -Real.log r ≤ E x} ∪ {z₀} : Set X) :=
      IsCompact.union (hinf (-Real.log r) (by rw [neg_pos]; exact hlog)) isCompact_singleton
    have hsub : Φ ⁻¹' K ⊆ ({x : X | -Real.log r ≤ E x} ∪ {z₀} : Set X) := by
      intro x hx
      rcases eq_or_ne x z₀ with rfl | hxne
      · exact Or.inr rfl
      · refine Or.inl ?_
        have h1 : ‖Φ x‖ ≤ r := hw₀max hx
        rw [hmod x hxne, ← Real.exp_log hrpos] at h1
        have h2 : -(E x) ≤ Real.log r := Real.exp_le_exp.mp h1
        show -Real.log r ≤ E x
        linarith
    exact IsCompact.of_isClosed_subset hcomp hclosed hsub

end Submission
