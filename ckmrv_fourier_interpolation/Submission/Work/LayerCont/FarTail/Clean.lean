/-
# Far-side cleanliness of the contour and non-degeneracy of the pole

Two geometric inputs for the far side (`1 < Re τ`) of the CKMRV layer, both about the *quadrature*
of the two side conditions under which the contour may be deformed:

* `clean_axis_of_web_re_gt_one` — the far-side twin of `Work.LayerCont.clean_axis_of_web_re_lt_one`:
  from the local web classification of the `SL(2,ℤ)`-orbit of the imaginary axis near `1 + i s₀`,
  a point `τ` of the ball with `1 < τ.re` is *not* `SL(2,ℤ)`-equivalent to any `i t`.  (The web
  forces every orbit point of the imaginary axis in the ball to have real part exactly `1`.)

* `jprime_ne_zero_far` — the pole `z = τ - 1` (`Work.Asymptotics.tauSubOne`) of the far-side
  detour is non-degenerate for `τ` in a ball around `1 + i s₀` with `s₀ > 1`: the translate
  `T⁻¹τ = τ - 1` never hits an elliptic point, because those have imaginary part `≤ 1 < s₀`.
-/
import Mathlib
import Submission.Work.LayerCont.FarTail.Defs
import Submission.Work.LayerCont.WindowChart
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.exists_jprime_lower_near_imagAxis

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.LayerCont.FarTail

/-- **Cleanliness of the contour for `1 < τ.re`**, from the web classification: any
`SL(2,ℤ)`-translate of `i t` in the web ball around `1 + i s₀` has real part exactly `1`, so it
cannot equal a `τ` with `1 < τ.re`. -/
theorem clean_axis_of_web_re_gt_one {s₀ ε rw₀ : ℝ} (hs₀ : 0 < s₀) (hεw : ε ≤ rw₀)
    (hweb : ∀ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (t : ℝ) (ht : 0 < t),
      dist (σ • Work.Kernels.imagAxis t ht) (Work.Asymptotics.onePlusI s₀ hs₀) < rw₀ →
      (σ • Work.Kernels.imagAxis t ht).re = 1 ∧
        ((σ • Work.Kernels.imagAxis t ht).im = t ∨
          (σ • Work.Kernels.imagAxis t ht).im = t⁻¹)) :
    ∀ (t : ℝ) (ht : 0 < t), ∀ τ : UpperHalfPlane,
      dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
  intro t ht τ hτ hτre hjeq
  obtain ⟨σ, hσ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
  have hd : dist (σ • Work.Kernels.imagAxis t ht) (Work.Asymptotics.onePlusI s₀ hs₀) < rw₀ := by
    rw [hσ]
    exact lt_of_lt_of_le hτ hεw
  obtain ⟨hre, -⟩ := hweb σ t ht hd
  rw [hσ] at hre
  linarith

/-- **The far-side web cleanliness specialised to the whole positive axis.** -/
theorem farClean_of_web {s₀ ε rw₀ : ℝ} (hs₀ : 0 < s₀) (hεw : ε ≤ rw₀)
    (hweb : ∀ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (t : ℝ) (ht : 0 < t),
      dist (σ • Work.Kernels.imagAxis t ht) (Work.Asymptotics.onePlusI s₀ hs₀) < rw₀ →
      (σ • Work.Kernels.imagAxis t ht).re = 1 ∧
        ((σ • Work.Kernels.imagAxis t ht).im = t ∨
          (σ • Work.Kernels.imagAxis t ht).im = t⁻¹)) :
    ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      ∀ (t : ℝ) (ht : 0 < t),
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) :=
  fun τ hτ hre t ht =>
    clean_axis_of_web_re_gt_one hs₀ hεw hweb t ht τ hτ hre

/-- **Non-vanishing of `j'` on a far-side ball.**  For `s₀ > 1` there is a ball around
`1 + i s₀` on which `jprime` never vanishes.

Route: `jprime` is invariant under `T` (`Work.Residues.jprime_vadd_one`), so on a neighbourhood of
`1 + i s₀` it is the translate of `jprime` on a neighbourhood of `i s₀`, where
`Work.Asymptotics.exists_jprime_lower_near_imagAxis` (valid for `s₀ ≠ 1`) gives the uniform
lower bound. -/
theorem jprime_ne_zero_far {s₀ : ℝ} (hs₀ : 0 < s₀) (hs₀1 : 1 < s₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ τ : UpperHalfPlane,
      dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → Work.Residues.jprime τ ≠ 0 := by
  obtain ⟨η, c, hη, hc, hb⟩ :=
    Work.Asymptotics.exists_jprime_lower_near_imagAxis (s₀ := s₀) hs₀ (ne_of_gt hs₀1)
  refine ⟨min 1 (η / (7 * s₀)), lt_min one_pos (div_pos hη (by positivity)), ?_⟩
  intro τ hτ
  have hεpos : 0 < min 1 (η / (7 * s₀)) := lt_min one_pos (div_pos hη (by positivity))
  have hε1 : min 1 (η / (7 * s₀)) ≤ 1 := min_le_left _ _
  have hε2 : min 1 (η / (7 * s₀)) ≤ η / (7 * s₀) := min_le_right _ _
  obtain ⟨h1, h2⟩ := Work.Asymptotics.abs_re_im_sub_lt hs₀ hεpos hε1 hτ
  -- the Euclidean distance to the centre, controlled by the hyperbolic one
  have hnorm : ‖(τ : ℂ) - ((1 : ℂ) + (s₀ : ℂ) * Complex.I)‖ < η := by
    have h3 := Complex.norm_le_abs_re_add_abs_im ((τ : ℂ) - ((1 : ℂ) + (s₀ : ℂ) * Complex.I))
    have hre : ((τ : ℂ) - ((1 : ℂ) + (s₀ : ℂ) * Complex.I)).re = τ.re - 1 := by simp
    have him : ((τ : ℂ) - ((1 : ℂ) + (s₀ : ℂ) * Complex.I)).im = τ.im - s₀ := by simp
    rw [hre, him] at h3
    have h6 : min 1 (η / (7 * s₀)) * (7 * s₀) ≤ η :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < 7 * s₀)).mp hε2
    nlinarith [h3, h1, h2, h6, hη, hs₀, hεpos]
  have hζ : ‖((Work.Asymptotics.tauSubOne τ : UpperHalfPlane) : ℂ)
      - Complex.I * (s₀ : ℂ)‖ < η := by
    rw [Work.Asymptotics.tauSubOne_coe]
    convert hnorm using 2
    ring
  have hb' := hb (Work.Asymptotics.tauSubOne τ) hζ
  have hj : Work.Residues.jprime (Work.Asymptotics.tauSubOne τ) = Work.Residues.jprime τ :=
    Work.Residues.jprime_vadd_neg_one τ
  rw [hj] at hb'
  intro h0
  rw [h0, norm_zero] at hb'
  linarith


/-- **`j'` does not vanish on a small ball around a point where it does not vanish.**  `j'` is
holomorphic (`Work.Residues.mdifferentiable_jprime`-style regularity is not needed: continuity
suffices), so the set `{j' ≠ 0}` is open.  This is the hypothesis-free companion of
`jprime_ne_zero_far` for points `c` at which `j'` is known not to vanish — e.g. the centres
`1 + i s₀` for `s₀ < 1`, where the elliptic orbit can pass through the centre. -/
theorem jprime_ne_zero_near (c : UpperHalfPlane) (hc : Work.Residues.jprime c ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ τ : UpperHalfPlane, dist τ c < ε → Work.Residues.jprime τ ≠ 0 := by
  have hcont : Continuous fun τ : UpperHalfPlane => Work.Residues.jprime τ := by
    have hE4 : Continuous fun τ : UpperHalfPlane => Work.Kernels.E4Fun τ :=
      (ModularFormClass.holo ModularForm.E₄).continuous
    have hE6 : Continuous fun τ : UpperHalfPlane => Work.Kernels.E6Fun τ :=
      (ModularFormClass.holo ModularForm.E₆).continuous
    have hD : Continuous fun τ : UpperHalfPlane => Work.Kernels.DeltaFun τ :=
      (ModularFormClass.holo (CuspForm.discriminant :
        CuspForm (Matrix.SpecialLinearGroup.mapGL ℝ).range 12)).continuous
    have h : (fun τ : UpperHalfPlane => Work.Residues.jprime τ)
        = fun τ : UpperHalfPlane => -(2 * (Real.pi : ℂ) * Complex.I)
            * Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ
            / Work.Kernels.DeltaFun τ := rfl
    rw [h]
    exact ((continuous_const.mul (hE4.pow 2)).mul hE6).div hD
      (fun τ => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
  have hnhds : {τ : UpperHalfPlane | Work.Residues.jprime τ ≠ 0} ∈ 𝓝 c :=
    (isOpen_ne_fun hcont continuous_const).mem_nhds hc
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  exact ⟨ε, hε, fun τ hτ => hball (by simpa using hτ)⟩

end Work.LayerCont.FarTail
