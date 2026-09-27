import Mathlib
import Submission.Work.Drive.rot90
import Submission.Work.Drive.UmlaufSetup
import Submission.Work.Drive.curve_deriv_ne_zero
import Submission.Work.Drive.curve_periodic
import Submission.Work.Drive.deriv_curve_periodic

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold

/-- The linear functional `p ↦ ⟪p, e⟫` of the Euclidean plane `ℝ × ℝ`. -/
noncomputable def eucLinFun (e : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  e.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + e.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

lemma eucLinFun_apply (e p : ℝ × ℝ) : eucLinFun e p = p.1 * e.1 + p.2 * e.2 := by
  simp [eucLinFun]
  ring

lemma eucLinFun_eq_eucDot (e p : ℝ × ℝ) : eucLinFun e p = Submission.Geometry.eucDot p e := by
  rw [eucLinFun_apply]
  rfl

/-- The derivative of `s ↦ ⟪curve γ s, e⟫` is `s ↦ ⟪curve γ' s, e⟫`: a linear functional
composed with a differentiable curve. -/
lemma deriv_eucDot_curve_const {γ : Circle → ℝ × ℝ} (hC1 : ContDiff ℝ 1 (curve γ))
    (e : ℝ × ℝ) (s : ℝ) :
    deriv (fun u => Submission.Geometry.eucDot (curve γ u) e) s =
      Submission.Geometry.eucDot (deriv (curve γ) s) e := by
  have hd : DifferentiableAt ℝ (curve γ) s :=
    (hC1.differentiable (by simp)).differentiableAt
  have h : HasDerivAt ((eucLinFun e) ∘ curve γ) ((eucLinFun e) (deriv (curve γ) s)) s :=
    (ContinuousLinearMap.hasFDerivAt (eucLinFun e)).comp_hasDerivAt s hd.hasDerivAt
  have hfun : (fun u => Submission.Geometry.eucDot (curve γ u) e) = (eucLinFun e) ∘ curve γ :=
    funext fun u => (eucLinFun_eq_eucDot e (curve γ u)).symm
  rw [hfun, h.deriv]
  exact eucLinFun_eq_eucDot e (deriv (curve γ) s)

/-- **Local monotonicity.**  At every parameter `t`, the curve is strictly monotone for the
linear functional `⟪·, curve γ' t⟫` on a neighbourhood of `t`.

Indeed the function `φ s = ⟪curve γ s, curve γ' t⟫` has `φ' t = ⟪curve γ' t, curve γ' t⟫ > 0`
(`curve γ' t ≠ 0`), and `φ'` is continuous, so `φ' > 0` on a neighbourhood of `t`; on that
neighbourhood `φ` is strictly increasing by the mean value theorem. -/
lemma exists_local_monotone_curve {γ : Circle → ℝ × ℝ} (hC1 : ContDiff ℝ 1 (curve γ))
    (hne : ∀ t, deriv (curve γ) t ≠ 0) (t : ℝ) :
    ∃ δ > 0, ∀ s₁ s₂ : ℝ, t - δ < s₁ → s₁ < s₂ → s₂ < t + δ →
      Submission.Geometry.eucDot (curve γ s₁) (deriv (curve γ) t) <
        Submission.Geometry.eucDot (curve γ s₂) (deriv (curve γ) t) := by
  have hcont : Continuous (deriv (curve γ)) := hC1.continuous_deriv (by simp)
  have hcontcurve : Continuous (curve γ) := hC1.continuous
  set φ : ℝ → ℝ := fun u => Submission.Geometry.eucDot (curve γ u) (deriv (curve γ) t) with hφ
  have hderivφ : ∀ s, deriv φ s =
      Submission.Geometry.eucDot (deriv (curve γ) s) (deriv (curve γ) t) :=
    fun s => deriv_eucDot_curve_const hC1 (deriv (curve γ) t) s
  have hdcont : Continuous (deriv φ) := by
    rw [funext hderivφ]
    have hfun : (fun s => Submission.Geometry.eucDot (deriv (curve γ) s) (deriv (curve γ) t))
        = (eucLinFun (deriv (curve γ) t)) ∘ (deriv (curve γ)) :=
      funext fun s => (eucLinFun_eq_eucDot (deriv (curve γ) t) (deriv (curve γ) s)).symm
    rw [hfun]
    exact (eucLinFun (deriv (curve γ) t)).continuous.comp hcont
  have hφcont : Continuous φ := by
    have hfun : φ = (eucLinFun (deriv (curve γ) t)) ∘ (curve γ) :=
      funext fun u => (eucLinFun_eq_eucDot (deriv (curve γ) t) (curve γ u)).symm
    rw [hfun]
    exact (eucLinFun (deriv (curve γ) t)).continuous.comp hcontcurve
  have hpost : 0 < deriv φ t := by
    rw [hderivφ t]
    rw [Submission.Geometry.eucDot_self]
    rcases eq_or_ne (deriv (curve γ) t).1 0 with h1 | h1
    · have h2 : (deriv (curve γ) t).2 ≠ 0 := by
        intro h2
        exact hne t (by ext <;> simp [h1, h2])
      nlinarith [sq_pos_of_ne_zero h2, sq_nonneg (deriv (curve γ) t).1]
    · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg (deriv (curve γ) t).2]
  have hopen : IsOpen {s : ℝ | 0 < deriv φ s} := isOpen_lt continuous_const hdcont
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hpost)
  refine ⟨δ, hδpos, ?_⟩
  have hmono : StrictMonoOn φ (Set.Ioo (t - δ) (t + δ)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) hφcont.continuousOn ?_
    intro x hx
    rw [interior_Ioo] at hx
    exact hδsub (by rw [Real.ball_eq_Ioo]; exact hx)
  intro s₁ s₂ h1 h2 h3
  have hs1 : s₁ ∈ Set.Ioo (t - δ) (t + δ) := ⟨h1, by linarith⟩
  have hs2 : s₂ ∈ Set.Ioo (t - δ) (t + δ) := ⟨by linarith, h3⟩
  exact hmono hs1 hs2 h2

/-- **Uniform local monotonicity on a compact parameter interval.**

The family of neighbourhoods produced by `exists_local_monotone_curve` covers the compact interval
`[0, M]`; a Lebesgue number `L` of this open cover makes every parameter interval of length
`≤ L/2` inside one of them, on which the corresponding linear functional is strictly monotone. -/
theorem exists_uniform_local_monotone_curve_compact {γ : Circle → ℝ × ℝ} (hC1 : ContDiff ℝ 1 (curve γ))
    (hne : ∀ t, deriv (curve γ) t ≠ 0) {M : ℝ} (_hM : 0 < M) :
    ∃ ε > 0, ∀ a d : ℝ, 0 ≤ a → a < d → d ≤ M → d - a ≤ ε →
      ∃ e : ℝ × ℝ, e ≠ 0 ∧ ∀ s₁ s₂ : ℝ, a ≤ s₁ → s₁ < s₂ → s₂ ≤ d →
        Submission.Geometry.eucDot (curve γ s₁) e < Submission.Geometry.eucDot (curve γ s₂) e := by
  classical
  have hloc : ∀ t : ℝ, ∃ δ > 0, ∀ s₁ s₂ : ℝ, t - δ < s₁ → s₁ < s₂ → s₂ < t + δ →
      Submission.Geometry.eucDot (curve γ s₁) (deriv (curve γ) t) <
        Submission.Geometry.eucDot (curve γ s₂) (deriv (curve γ) t) :=
    fun t => exists_local_monotone_curve hC1 hne t
  choose δ hδpos hδmono using hloc
  have hcover : Set.Icc (0 : ℝ) M ⊆ ⋃ t : ℝ, Set.Ioo (t - δ t) (t + δ t) := by
    intro u _
    exact Set.mem_iUnion.mpr ⟨u, ⟨by linarith [hδpos u], by linarith [hδpos u]⟩⟩
  obtain ⟨L, hLpos, hL⟩ :=
    lebesgue_number_lemma_of_metric isCompact_Icc (fun _ => isOpen_Ioo) hcover
  refine ⟨L / 2, by linarith, ?_⟩
  intro a d ha had hdM hℓ
  obtain ⟨i, hi⟩ := hL a ⟨ha, le_trans (le_of_lt had) hdM⟩
  refine ⟨deriv (curve γ) i, hne i, ?_⟩
  intro s₁ s₂ hs1 hs12 hs2
  have hm1 : s₁ ∈ Metric.ball a L := by
    rw [Real.ball_eq_Ioo]
    constructor <;> linarith
  have hm2 : s₂ ∈ Metric.ball a L := by
    rw [Real.ball_eq_Ioo]
    constructor <;> linarith
  exact hδmono i s₁ s₂ (hi hm1).1 hs12 (hi hm2).2

/-- **Uniform local monotonicity of a smooth embedded closed plane curve.**

For `γ : Circle → ℝ × ℝ` a smooth Jordan curve, parametrised as `curve γ t = γ (Circle.exp t)`, there
is a uniform `ε₀ > 0` such that, whenever four parameters satisfy `a < b < c < d` with `d - a ≤ ε₀`,
the whole parameter arc `[a,d]` lies in a region on which `curve γ` is strictly monotone for some
nonzero linear functional `e`: `s ↦ eucDot (curve γ s) e` is strictly increasing on `[a,d]`.

Proof sketch.  `curve γ` is `C¹` (it is `hγ.contMDiff.comp contMDiff_circleExp`, with derivative
`deriv (curve γ) t ≠ 0` by `Work.Drive.curve_deriv_ne_zero`) and `deriv (curve γ)` is `2π`-periodic
(`Work.Drive.deriv_curve_periodic`).  At each `t`, the derivative of `s ↦ eucDot (curve γ s) (deriv (curve γ) t)`
at `t` equals `eucDot (deriv (curve γ) t) (deriv (curve γ) t) = eucNorm (deriv (curve γ) t)² > 0`, so
that function is strictly increasing on a neighbourhood `(t-δ t, t+δ t)` of `t`; the family of these
intervals covers the parameter line periodically, so on the compact interval `[0, 4π]` a Lebesgue
number `L > 0` of the open cover `{(t-δ t, t+δ t)}` exists, and `ε₀ := min L (2π) / 2` works after
reducing `a` modulo `2π` (the hypotheses are `2π`-periodic). -/
theorem exists_uniform_local_monotone (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ a b c d : ℝ, a < b → b < c → c < d → d - a ≤ ε₀ →
      ∃ e : ℝ × ℝ, e ≠ 0 ∧ ∀ s₁ s₂ : ℝ, a ≤ s₁ → s₁ < s₂ → s₂ ≤ d →
        Submission.Geometry.eucDot (curve γ s₁) e < Submission.Geometry.eucDot (curve γ s₂) e := by
  have hC1 : ContDiff ℝ 1 (curve γ) :=
    (hγ.contMDiff.comp contMDiff_circleExp).contDiff.of_le (by simp)
  have hne : ∀ t, deriv (curve γ) t ≠ 0 := curve_deriv_ne_zero γ hγ
  have hper : Function.Periodic (curve γ) (2 * Real.pi) := curve_periodic γ
  obtain ⟨ε, hεpos, hε⟩ :=
    exists_uniform_local_monotone_curve_compact hC1 hne (M := 4 * Real.pi) (by positivity)
  refine ⟨min ε Real.pi, lt_min hεpos Real.pi_pos, ?_⟩
  intro a b c d hab hbc hcd hda
  have had : a < d := lt_trans hab (lt_trans hbc hcd)
  have hℓε : d - a ≤ ε := le_trans hda (min_le_left _ _)
  have hℓπ : d - a ≤ Real.pi := le_trans hda (min_le_right _ _)
  set k : ℤ := ⌊a / (2 * Real.pi)⌋ with hk
  set a₀ : ℝ := a - (k : ℝ) * (2 * Real.pi) with ha₀
  have hk_le : (k : ℝ) * (2 * Real.pi) ≤ a := by
    have h1 : (k : ℝ) ≤ a / (2 * Real.pi) := by rw [hk]; exact Int.floor_le _
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mp h1
  have hk_gt : a < (k : ℝ) * (2 * Real.pi) + 2 * Real.pi := by
    have h1 : a / (2 * Real.pi) < (k : ℝ) + 1 := by rw [hk]; exact Int.lt_floor_add_one _
    have h2 : a < ((k : ℝ) + 1) * (2 * Real.pi) :=
      (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mp h1
    linarith
  have ha₀_nonneg : 0 ≤ a₀ := by rw [ha₀]; linarith
  have ha₀_lt : a₀ < 2 * Real.pi := by rw [ha₀]; linarith
  have hd₀ : a₀ + (d - a) < 4 * Real.pi := by linarith [ha₀_lt, hℓπ, Real.pi_pos]
  obtain ⟨e, he, hmono⟩ := hε a₀ (a₀ + (d - a)) ha₀_nonneg (by linarith)
    (le_of_lt hd₀) (by linarith)
  refine ⟨e, he, ?_⟩
  have hper_sub : ∀ x : ℝ, curve γ (x - (k : ℝ) * (2 * Real.pi)) = curve γ x := by
    intro x
    have h := (hper.int_mul k) (x - (k : ℝ) * (2 * Real.pi))
    have hx : x - (k : ℝ) * (2 * Real.pi) + (k : ℝ) * (2 * Real.pi) = x := by ring
    rw [hx] at h
    exact h.symm
  intro s₁ s₂ hs1 hs12 hs2
  have hm1 : a₀ ≤ s₁ - (k : ℝ) * (2 * Real.pi) := by rw [ha₀]; linarith
  have hm3 : s₂ - (k : ℝ) * (2 * Real.pi) ≤ a₀ + (d - a) := by rw [ha₀]; linarith
  have hm2 : s₁ - (k : ℝ) * (2 * Real.pi) < s₂ - (k : ℝ) * (2 * Real.pi) := by linarith
  have h := hmono _ _ hm1 hm2 hm3
  rwa [hper_sub s₁, hper_sub s₂] at h

end Work.Drive
