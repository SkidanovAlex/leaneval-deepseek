import Mathlib
import Submission.Lib.Unif2.Work.Drive.PhaseCover
import Submission.Lib.Unif2.Work.Analysis.RiemannSurface.isEvenlyCovered_logProj

/-!
# The bridge from the conjugate étale space and the log cover to the phase cover

Let `X` be a connected Riemann surface, `z₀ : X`, `E : X → ℝ` harmonic off `z₀` and `Θ : X → ℂ`
continuous and nonvanishing off `z₀`.  Write `U := X ∖ {z₀}` for the punctured surface.

Three covering spaces of `U` are relevant:

* the *conjugate étale space* `U × ℝ` of `E|_U` (`Submission.conjTopology`), whose coordinate `t`
  at `u` is the value of a local harmonic conjugate of `E`;
* the *logarithmic étale space* `{p : U × ℂ // exp p.2 = Θ p.1.1}` of `Θ|_U`, whose coordinate `w`
  at `u` satisfies `exp w = Θ u`;
* the *phase cover* `X × ℝ` (`Work.Drive.phaseTopology`), whose coordinate `lam` at `x` is the
  value of a local branch of the multivalued function `E* + arg Θ`.

The *bridge* is the map

  `(u, t), (u, w) ↦ (u, t + Im w)`

from the fibre product of the first two covers into the phase cover.  It is continuous, and it is
what makes the monodromy of the phase cover computable from the conjugate period and the winding
number: the two covering-theoretic inputs are transported into the third.

This module only fixes the vocabulary; the continuity of the bridge is
`Work.Drive.continuous_phaseBridge`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Filter Set Classical

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The punctured surface, as a type. -/
abbrev Punct (z₀ : X) : Type _ := ↥(Work.Modulus.puncturedOpens z₀)

/-- The logarithmic étale space of `Θ|_U` over the punctured surface. -/
abbrev LogSp {z₀ : X} (Θ : X → ℂ) : Type _ :=
  ↥(Work.SimplyConnected.ABS.logSpace (fun u : Punct z₀ => Θ u.1))

/-- The fibre product of the conjugate étale space and the log cover, over the punctured
surface. -/
def phaseFiberProd (z₀ : X) (Θ : X → ℂ) : Set ((Punct z₀ × ℝ) × LogSp (z₀ := z₀) Θ) :=
  {p | p.1.1 = p.2.1.1}

/-- The topology of the fibre product: the subspace topology of the product of the *conjugate étale
topology* (`Work.Modulus.greenConjTopology z₀ E`) on the first factor with the (subspace) topology of
the logarithmic étale space on the second. -/
def phaseFiberProdTopology (z₀ : X) (E : X → ℝ) (Θ : X → ℂ) :
    TopologicalSpace ↥(phaseFiberProd z₀ Θ) :=
  letI : TopologicalSpace (Punct z₀ × ℝ) := Work.Modulus.greenConjTopology z₀ E
  (inferInstance : TopologicalSpace ((Punct z₀ × ℝ) × LogSp (z₀ := z₀) Θ)).induced Subtype.val

/-- **The bridge** from the fibre product to the phase cover: the phase coordinate is the sum of the
conjugate coordinate and the imaginary part of the logarithmic coordinate. -/
def phaseBridge (z₀ : X) (Θ : X → ℂ) : ↥(phaseFiberProd z₀ Θ) → X × ℝ :=
  fun p => (p.1.1.1.1, p.1.1.2 + (p.1.2.1.2).im)

/-- Holomorphy off the pole restricts to the punctured surface. -/
theorem holomorphicOnX_punctured_of_holomorphicOnX {z₀ : X} {W : Set X} {F : X → ℂ}
    (hF : Submission.HolomorphicOnX F W) :
    Submission.HolomorphicOnX (fun u : Punct z₀ => F u.1) {u : Punct z₀ | u.1 ∈ W} := by
  intro u hu
  rw [Submission.HolomorphicOnXAt]
  have heq : (F ∘ (chartAt ℂ u.1).symm) =ᶠ[𝓝 ((chartAt ℂ u) u)]
      ((fun v : Punct z₀ => F v.1) ∘ (chartAt ℂ u).symm) := by
    filter_upwards [(chartAt ℂ u).open_target.mem_nhds
      (Work.Modulus.opensChartAt_mem_target (Work.Modulus.puncturedOpens z₀) u)] with z hz
    simp only [Function.comp_apply]
    rw [Work.Modulus.opensChartAt_symm_eqOn (Work.Modulus.puncturedOpens z₀) u hz]
  have h' : AnalyticAt ℂ (F ∘ (chartAt ℂ u.1).symm) ((chartAt ℂ u) u) := by
    rw [Work.Modulus.opensChartAt_apply (Work.Modulus.puncturedOpens z₀) u]
    exact hF u.1 hu
  exact h'.congr heq

/-- An integer multiple of `2πi` of norm less than `π` vanishes. -/
theorem int_eq_zero_of_norm_two_pi_I_lt' {k : ℤ}
    (h : ‖(k : ℂ) * (2 * Real.pi * Complex.I)‖ < Real.pi) : k = 0 := by
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h4 : (k : ℂ) * (2 * Real.pi * Complex.I)
      = (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h4] at h
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
  rw [abs_mul, abs_of_pos hpos] at h
  have h5 : |(k : ℝ)| < 1 := by nlinarith [Real.pi_pos, h]
  have h6 : ((|k| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; exact h5
  have h7 : |k| < 1 := by exact_mod_cast h6
  exact Int.abs_lt_one_iff.mp h7

/-- **The sheets of the log cover are open.**  If `w` is a continuous logarithm of `Θ` on the open
set `W`, then the set of points of the log cover whose coordinate is `w` and whose projection lies
in `W` is open: the fibre of the log cover over `u` is `w u + 2πiℤ`, and the ball of radius `π`
around `w u` meets it only in `w u`. -/
theorem isOpen_logSheet {z₀ : X} {Θ : X → ℂ} {W : Set X} {w : X → ℂ}
    (hW : IsOpen W) (hw : ContinuousOn w W) (hwe : ∀ x ∈ W, Complex.exp (w x) = Θ x) :
    IsOpen {l : LogSp (z₀ := z₀) Θ | l.1.1.1 ∈ W ∧ l.1.2 = w l.1.1.1} := by
  rw [isOpen_iff_mem_nhds]
  rintro l ⟨hlW, hlw⟩
  have hcont : ContinuousAt w l.1.1.1 := hw.continuousAt (hW.mem_nhds hlW)
  have hε : ∀ᶠ y in 𝓝 l.1.1.1, dist (w y) (w l.1.1.1) < Real.pi / 4 := by
    have hb : Metric.ball (w l.1.1.1) (Real.pi / 4) ∈ 𝓝 (w l.1.1.1) :=
      Metric.ball_mem_nhds _ (by positivity)
    filter_upwards [hcont hb] with y hy
    exact hy
  have hmem : {y : X | dist (w y) (w l.1.1.1) < Real.pi / 4} ∩ W ∈ 𝓝 l.1.1.1 :=
    Filter.inter_mem hε (hW.mem_nhds hlW)
  obtain ⟨V, hVsub, hVopen, hlV⟩ := mem_nhds_iff.mp hmem
  have hVsub₁ : ∀ y ∈ V, dist (w y) (w l.1.1.1) < Real.pi / 4 := fun y hy => (hVsub hy).1
  have hVsub₂ : ∀ y ∈ V, y ∈ W := fun y hy => (hVsub hy).2
  have hVp : IsOpen {u : Punct z₀ | u.1 ∈ V} := hVopen.preimage continuous_subtype_val
  have hO : IsOpen ((Subtype.val : ↥(Work.SimplyConnected.ABS.logSpace
      (fun u : Punct z₀ => Θ u.1)) → (Punct z₀ × ℂ)) ⁻¹'
      ({u : Punct z₀ | u.1 ∈ V} ×ˢ (Metric.ball l.1.2 (Real.pi / 4)))) :=
    (hVp.prod Metric.isOpen_ball).preimage continuous_subtype_val
  refine Filter.mem_of_superset (hO.mem_nhds ⟨hlV, ?_⟩) ?_
  · show l.1.2 ∈ Metric.ball l.1.2 (Real.pi / 4)
    exact Metric.mem_ball_self (by positivity)
  · intro l' hl'
    obtain ⟨hl'V, hl'ball⟩ := hl'
    have hl'W : l'.1.1.1 ∈ W := hVsub₂ _ hl'V
    rw [Metric.mem_ball, dist_eq_norm] at hl'ball
    have h1 : ‖l'.1.2 - w l'.1.1.1‖ < Real.pi / 2 := by
      have hsplit : l'.1.2 - w l'.1.1.1
          = (l'.1.2 - l.1.2) + (w l.1.1.1 - w l'.1.1.1) := by rw [hlw]; ring
      rw [hsplit]
      have h2 : ‖w l.1.1.1 - w l'.1.1.1‖ < Real.pi / 4 := by
        rw [← dist_eq_norm, dist_comm]; exact hVsub₁ _ hl'V
      calc ‖(l'.1.2 - l.1.2) + (w l.1.1.1 - w l'.1.1.1)‖
          ≤ ‖l'.1.2 - l.1.2‖ + ‖w l.1.1.1 - w l'.1.1.1‖ := norm_add_le _ _
        _ < Real.pi / 4 + Real.pi / 4 := by linarith
        _ = Real.pi / 2 := by ring
    have h3 : Complex.exp (w l'.1.1.1) = (fun u : Punct z₀ => Θ u.1) l'.1.1 := hwe _ hl'W
    have hexp : Complex.exp (l'.1.2 - w l'.1.1.1) = 1 := by
      rw [Complex.exp_sub, l'.2, h3]
      exact div_self (by rw [← h3]; exact Complex.exp_ne_zero _)
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
    have hn0 : n = 0 := by
      refine int_eq_zero_of_norm_two_pi_I_lt' ?_
      rw [← hn]
      exact lt_trans h1 (by linarith [Real.pi_pos])
    refine ⟨hl'W, ?_⟩
    have hzero : l'.1.2 - w l'.1.1.1 = 0 := by rw [hn, hn0]; simp
    exact sub_eq_zero.mp hzero

end Work.Drive
