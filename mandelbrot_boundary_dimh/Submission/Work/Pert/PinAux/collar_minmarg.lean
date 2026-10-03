import Mathlib
import Submission.Work.Pert.PinAux.CollarDefs

set_option linter.unusedVariables false

namespace Work.Pert.PinAux

open MandelDim Complex Metric

noncomputable section

/-!
# `Work.Pert.PinAux.collar_minmarg`

A ball contained in the gate `Qm Ξ α` cannot have radius exceeding `minmarg Ξ α z`.

The two margins `margA Ξ α z`, `margB Ξ α z` are `√2` times the *signed* distances of `z` to the
two boundary cones of the gate.  Hence the distance from `z` to the complement of the gate is at
most `min (margA Ξ α z) (margB Ξ α z) = minmarg Ξ α z`: for either cone the *apex* lies in the
cone (so outside the gate) and is at distance at most the corresponding margin, since the margin
is the `l¹`-norm of the apex-displacement while the distance is its `l²`-norm.
-/

/-- The `A`-margin is the `l¹`-norm of the displacement from the `A`-apex `Ξ - 1/α`. -/
lemma margA_eq_apex (Ξ : ℝ) (α w : ℂ) :
    margA Ξ α w = (w - ((Ξ : ℂ) - 1 / α)).re + |(w - ((Ξ : ℂ) - 1 / α)).im| := by
  simp only [margA, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  ring_nf

/-- The `B`-margin is the `l¹`-norm of the displacement from the `B`-apex `-Ξ`. -/
lemma margB_eq_apexB (Ξ : ℝ) (α w : ℂ) :
    margB Ξ α w = |(w + (Ξ : ℂ)).im| - (w + (Ξ : ℂ)).re := by
  simp only [margB, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
  ring_nf

/-- Moving by `u` from the `A`-apex, the `A`-margin equals the `l¹`-norm of `u`. -/
lemma margA_add_apex (Ξ : ℝ) (α u : ℂ) :
    margA Ξ α (((Ξ : ℂ) - 1 / α) + u) = u.re + |u.im| := by
  simp only [margA, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring_nf

/-- Moving by `-u` from the `B`-apex `-Ξ`, the `B`-margin equals the `l¹`-norm of `u`. -/
lemma margB_sub_apexB (Ξ : ℝ) (α u : ℂ) :
    margB Ξ α ((-(Ξ : ℂ)) - u) = u.re + |u.im| := by
  have h1 : ((-(Ξ : ℂ)) - u).im = -u.im := by simp
  have h2 : ((-(Ξ : ℂ)) - u).re = -Ξ - u.re := by simp
  rw [margB, h1, h2, abs_neg]
  ring

/-- The displacement from the `B`-apex, reflected in the origin, has `l¹`-norm equal to the
`B`-margin. -/
lemma margB_eq_neg_add (Ξ : ℝ) (α w : ℂ) :
    margB Ξ α w = (-(w + (Ξ : ℂ))).re + |(-(w + (Ξ : ℂ))).im| := by
  rw [margB_eq_apexB]
  simp only [Complex.neg_re, Complex.neg_im]
  rw [abs_neg]
  ring

/-- The `l²`-norm of `(c/2) • (1 + I)` is at most `c`. -/
lemma norm_half_mul_one_add_I_le (c : ℝ) (hc : 0 ≤ c) :
    ‖((c / 2 : ℝ) : ℂ) * (1 + Complex.I)‖ ≤ c := by
  rw [norm_mul]
  have h1 : ‖((c / 2 : ℝ) : ℂ)‖ = c / 2 := Complex.norm_of_nonneg (by linarith)
  rw [h1]
  have h2 : ‖(1 : ℂ) + Complex.I‖ ≤ 2 := by
    calc ‖(1 : ℂ) + Complex.I‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I‖ := norm_add_le _ _
      _ = 2 := by simp [Complex.norm_I]; norm_num
  nlinarith [norm_nonneg ((1 : ℂ) + Complex.I), hc]

/-- The `l²`-norm of `(c/2) • (1 - I)` is at most `c`. -/
lemma norm_half_mul_one_sub_I_le (c : ℝ) (hc : 0 ≤ c) :
    ‖((c / 2 : ℝ) : ℂ) * (1 - Complex.I)‖ ≤ c := by
  rw [norm_mul]
  have h1 : ‖((c / 2 : ℝ) : ℂ)‖ = c / 2 := Complex.norm_of_nonneg (by linarith)
  rw [h1]
  have h2 : ‖(1 : ℂ) - Complex.I‖ ≤ 2 := by
    calc ‖(1 : ℂ) - Complex.I‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I‖ := norm_sub_le _ _
      _ = 2 := by simp [Complex.norm_I]; norm_num
  nlinarith [norm_nonneg ((1 : ℂ) - Complex.I), hc]

/-- **Geometry of the left cone.**  If `0 ≤ p.re + |p.im|`, then the closed left cone
`{v | v.re + |v.im| ≤ 0}` meets the closed ball of radius `p.re + |p.im|` about `p`.

Either `p.re ≥ 0`, when the apex `0` itself is within distance `‖p‖ ≤ p.re + |p.im|`; or `p.re < 0`,
when the perpendicular foot on the appropriate boundary ray is within distance
`(p.re + |p.im|) / √2 ≤ p.re + |p.im|`. -/
lemma exists_leftCone_dist_le (p : ℂ) (hp : 0 ≤ p.re + |p.im|) :
    ∃ u : ℂ, u.re + |u.im| ≤ 0 ∧ ‖p - u‖ ≤ p.re + |p.im| := by
  by_cases hre : 0 ≤ p.re
  · refine ⟨0, by simp, ?_⟩
    have hsq : ‖p‖ ^ 2 ≤ (p.re + |p.im|) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [abs_nonneg p.im, hre, sq_abs p.im]
    have h3 := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (norm_nonneg p), Real.sqrt_sq hp] at h3
    simpa using h3
  · by_cases him : 0 ≤ p.im
    · have hp' : 0 ≤ p.re + p.im := by rw [← abs_of_nonneg him]; exact hp
      refine ⟨Complex.mk ((p.re - p.im) / 2) ((p.im - p.re) / 2), ?_, ?_⟩
      · change (p.re - p.im) / 2 + |(p.im - p.re) / 2| ≤ 0
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (p.im - p.re) / 2)]
        linarith
      · have heq : p - Complex.mk ((p.re - p.im) / 2) ((p.im - p.re) / 2)
            = (((p.re + p.im) / 2 : ℝ) : ℂ) * (1 + Complex.I) := by
          apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
        rw [heq, abs_of_nonneg him]
        exact norm_half_mul_one_add_I_le (p.re + p.im) hp'
    · have him' : p.im < 0 := not_le.mp him
      have hp' : 0 ≤ p.re - p.im := by
        have hp2 := hp
        rw [abs_of_nonpos him'.le] at hp2
        linarith
      refine ⟨Complex.mk ((p.re + p.im) / 2) ((p.re + p.im) / 2), ?_, ?_⟩
      · change (p.re + p.im) / 2 + |(p.re + p.im) / 2| ≤ 0
        rw [abs_of_nonpos (by linarith : (p.re + p.im) / 2 ≤ 0)]
        linarith
      · have heq : p - Complex.mk ((p.re + p.im) / 2) ((p.re + p.im) / 2)
            = (((p.re - p.im) / 2 : ℝ) : ℂ) * (1 - Complex.I) := by
          apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
        rw [heq]
        have hrw : p.re + |p.im| = p.re - p.im := by
          rw [abs_of_nonpos him'.le]; ring
        rw [hrw]
        exact norm_half_mul_one_sub_I_le (p.re - p.im) hp'

/-- The `A`-apex is a point of the complement of the gate at distance at most `margA Ξ α z`. -/
lemma exists_compl_dist_le_margA {Ξ : ℝ} {α : ℂ} {z : ℂ} (hz : z ∈ Qm Ξ α) :
    ∃ u : ℂ, u ∉ Qm Ξ α ∧ dist z u ≤ margA Ξ α z := by
  have hzA : 0 < margA Ξ α z := ((mem_Qm_iff_marg Ξ α z).mp hz).1
  obtain ⟨u₀, hu₀c, hu₀d⟩ :=
    exists_leftCone_dist_le (z - ((Ξ : ℂ) - 1 / α)) (by rw [← margA_eq_apex]; linarith)
  refine ⟨((Ξ : ℂ) - 1 / α) + u₀, ?_, ?_⟩
  · intro hmem
    have hpos : 0 < margA Ξ α (((Ξ : ℂ) - 1 / α) + u₀) := ((mem_Qm_iff_marg _ _ _).mp hmem).1
    rw [margA_add_apex] at hpos
    linarith
  · rw [dist_eq_norm]
    have hring : z - (((Ξ : ℂ) - 1 / α) + u₀) = (z - ((Ξ : ℂ) - 1 / α)) - u₀ := by ring
    rw [hring, margA_eq_apex]
    exact hu₀d

/-- The `B`-apex is a point of the complement of the gate at distance at most `margB Ξ α z`. -/
lemma exists_compl_dist_le_margB {Ξ : ℝ} {α : ℂ} {z : ℂ} (hz : z ∈ Qm Ξ α) :
    ∃ u : ℂ, u ∉ Qm Ξ α ∧ dist z u ≤ margB Ξ α z := by
  have hzB : 0 < margB Ξ α z := ((mem_Qm_iff_marg Ξ α z).mp hz).2
  obtain ⟨u₀, hu₀c, hu₀d⟩ :=
    exists_leftCone_dist_le (-(z + (Ξ : ℂ))) (by rw [← margB_eq_neg_add]; linarith)
  refine ⟨(-(Ξ : ℂ)) - u₀, ?_, ?_⟩
  · intro hmem
    have hpos : 0 < margB Ξ α ((-(Ξ : ℂ)) - u₀) := ((mem_Qm_iff_marg _ _ _).mp hmem).2
    rw [margB_sub_apexB] at hpos
    linarith
  · rw [dist_eq_norm]
    have hring : z - ((-(Ξ : ℂ)) - u₀) = -(-(z + (Ξ : ℂ)) - u₀) := by ring
    rw [hring, norm_neg, margB_eq_neg_add]
    exact hu₀d

/-- The distance from a point of the gate to the complement is at most `minmarg`. -/
lemma infDist_le_minmarg {Ξ : ℝ} {α : ℂ} {z : ℂ} (hz : z ∈ Qm Ξ α) :
    Metric.infDist z ((Qm Ξ α)ᶜ) ≤ minmarg Ξ α z := by
  rw [minmarg]
  apply le_min
  · obtain ⟨u, hu, hd⟩ := exists_compl_dist_le_margA hz
    exact le_trans (Metric.infDist_le_dist_of_mem (by simpa using hu)) hd
  · obtain ⟨u, hu, hd⟩ := exists_compl_dist_le_margB hz
    exact le_trans (Metric.infDist_le_dist_of_mem (by simpa using hu)) hd

theorem collar_minmarg {Ξ : ℝ} {α : ℂ} {R₁ : ℝ} {z : ℂ} (hR₁ : 0 < R₁)
    (hz : z ∈ Work.Pert.Qm Ξ α) (hball : Metric.ball z R₁ ⊆ Work.Pert.Qm Ξ α) :
    R₁ ≤ Work.Pert.PinAux.minmarg Ξ α z := by
  have hcomp : ((Qm Ξ α)ᶜ).Nonempty := by
    obtain ⟨u, hu, _⟩ := exists_compl_dist_le_margA hz
    exact ⟨u, by simpa using hu⟩
  have hle : R₁ ≤ Metric.infDist z ((Qm Ξ α)ᶜ) := by
    rw [Metric.le_infDist hcomp]
    intro y hy
    have hyc : y ∉ Qm Ξ α := by simpa using hy
    by_contra hlt
    have hlt' : dist z y < R₁ := not_le.mp hlt
    exact hyc (hball (Metric.mem_ball.mpr (by rwa [dist_comm] at hlt')))
  exact le_trans hle (infDist_le_minmarg hz)

end

end Work.Pert.PinAux
