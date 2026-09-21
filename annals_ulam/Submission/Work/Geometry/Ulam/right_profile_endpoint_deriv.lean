import Mathlib
import Submission.Work.Geometry.Ulam.radial_profile_reconstruction
import Submission.Work.Geometry.Ulam.right_profile_concave
import Submission.Work.Geometry.Ulam.continuous_invFunOn

namespace Commons.Geometry.Ulam

open Set Filter
open scoped Topology ContDiff

noncomputable section

set_option maxHeartbeats 4000000

lemma rightProfile_hasDerivAt
    (R : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α) :
    ∀ t ∈ Set.Ioo 0 (R 0),
      HasDerivAt (rightProfile R) (deriv (rightProfile R) t) t := by
  intro t ht
  let α := rightAlpha R t
  have ht_mem : t ∈ Set.Icc 0 (R 0) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hα_spec := rightAlpha_spec R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound ht_mem
  have hα_mem : α ∈ Set.Icc 0 (Real.pi / 2) := hα_spec.1
  have hαeq : R α * Real.cos α = t := hα_spec.2
  have hα_pos : 0 < α := by
    by_contra h
    have hα0 : α = 0 := le_antisymm (le_of_not_gt h) hα_mem.1
    have : t = R 0 := by
      rw [← hαeq, hα0]
      simp [Real.cos_zero, mul_one]
    linarith [ht.2]
  have hα_lt_pi_div_two : α < Real.pi / 2 := by
    by_contra h
    have hαpi : α = Real.pi / 2 := le_antisymm hα_mem.2 (le_of_not_gt h)
    have : t = 0 := by
      rw [← hαeq, hαpi]
      simp [Real.cos_pi_div_two]
    linarith [ht.1]
  have hR_diff : DifferentiableAt ℝ R α :=
    (hR_cont.differentiableOn (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0) α hα_mem).differentiableAt
      (Icc_mem_nhds hα_pos hα_lt_pi_div_two)
  have hf_deriv : HasDerivAt (fun α => R α * Real.cos α)
      (deriv R α * Real.cos α - R α * Real.sin α) α := by
    have h := hR_diff.hasDerivAt.mul (Real.hasDerivAt_cos α)
    change HasDerivAt (R * Real.cos) (deriv R α * Real.cos α - R α * Real.sin α) α
    simpa [mul_neg, sub_eq_add_neg] using h
  have hf'_ne : deriv R α * Real.cos α - R α * Real.sin α ≠ 0 := by
    exact ne_of_lt (rightArc_deriv_neg R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
      ⟨hα_pos, hα_lt_pi_div_two⟩)
  have hg_cont : ContinuousAt (rightAlpha R) t :=
    rightAlpha_continuousAt R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound ht
  have hfg : ∀ᶠ y in 𝓝 t, (fun α => R α * Real.cos α) (rightAlpha R y) = y := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with y hy
    exact (rightAlpha_spec R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound hy).2
  have hg_deriv : HasDerivAt (rightAlpha R)
      ((deriv R α * Real.cos α - R α * Real.sin α)⁻¹) t :=
    HasDerivAt.of_local_left_inverse hg_cont hf_deriv hf'_ne hfg
  have hR_chain : HasDerivAt (fun t => R (rightAlpha R t))
      (deriv R α * (deriv R α * Real.cos α - R α * Real.sin α)⁻¹) t :=
    hR_diff.hasDerivAt.comp t hg_deriv
  have hsin_chain : HasDerivAt (fun t => Real.sin (rightAlpha R t))
      (Real.cos α * (deriv R α * Real.cos α - R α * Real.sin α)⁻¹) t := by
    change HasDerivAt (Real.sin ∘ rightAlpha R)
      (Real.cos α * (deriv R α * Real.cos α - R α * Real.sin α)⁻¹) t
    simpa using (Real.hasDerivAt_sin α).comp t hg_deriv
  have hprod := hR_chain.mul hsin_chain
  have hprod' : HasDerivAt (fun t => R (rightAlpha R t) * Real.sin (rightAlpha R t))
      (deriv R α * (deriv R α * Real.cos α - R α * Real.sin α)⁻¹ * Real.sin α +
        R α * (Real.cos α * (deriv R α * Real.cos α - R α * Real.sin α)⁻¹)) t := by
    change HasDerivAt ((fun t => R (rightAlpha R t)) * fun t => Real.sin (rightAlpha R t))
      (deriv R α * (deriv R α * Real.cos α - R α * Real.sin α)⁻¹ * Real.sin α +
        R α * (Real.cos α * (deriv R α * Real.cos α - R α * Real.sin α)⁻¹)) t
    exact hprod
  have hmain : HasDerivAt (rightProfile R)
      ((deriv R α * Real.sin α + R α * Real.cos α) /
        (deriv R α * Real.cos α - R α * Real.sin α)) t := by
    convert hprod' using 1
    · ext t; rfl
    · rw [div_eq_mul_inv]; ring
  have hderiv := rightProfile_deriv R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound t ht
  simpa [hderiv, α] using hmain


/-- The right-branch profile is differentiable on `(0, R 0)`. -/
lemma rightProfile_differentiableOn
    (R : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α) :
    DifferentiableOn ℝ (rightProfile R) (Set.Ioo 0 (R 0)) := by
  intro t ht
  exact (rightProfile_hasDerivAt R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound t ht).differentiableAt.differentiableWithinAt

/-- The right-branch profile is continuous within `(0, R 0)` at `0`. -/
lemma rightProfile_continuousWithinAt_zero
    (R : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α) :
    ContinuousWithinAt (rightProfile R) (Set.Ioo 0 (R 0)) 0 := by
  have hcont := rightProfile_continuousOn R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (R 0) :=
    ⟨le_rfl, le_of_lt (hR_pos 0 ⟨le_rfl, by linarith [Real.pi_pos]⟩)⟩
  exact (hcont.continuousWithinAt h0).mono (by intro x hx; exact Set.Ioo_subset_Icc_self hx)

end

end Commons.Geometry.Ulam

namespace Commons.Geometry.Ulam

open Set Filter
open scoped Topology ContDiff

noncomputable section

/-- The derivative of the right-branch profile tends to the endpoint value as
`t → 0⁺`. -/
lemma rightProfile_deriv_tendsto_zero
    (R : ℝ → ℝ) {η δ : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hδ : 0 < δ)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_nhds : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 + δ)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α) :
    Tendsto (fun t => deriv (rightProfile R) t) (𝓝[>] 0)
      (𝓝 (- deriv R (Real.pi / 2) / R (Real.pi / 2))) := by
  have hα_tendsto : Tendsto (rightAlpha R) (𝓝[>] 0) (𝓝 (Real.pi / 2)) := by
    have hcont := rightAlpha_continuousOn R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
    have hR0pos : 0 < R 0 := hR_pos 0 ⟨le_rfl, by linarith [Real.pi_pos]⟩
    have h0 : (0 : ℝ) ∈ Set.Icc 0 (R 0) := ⟨le_rfl, le_of_lt hR0pos⟩
    have hIio_mem : Set.Iio (R 0) ∈ 𝓝[>] (0 : ℝ) := by
      rw [mem_nhdsWithin]
      exact ⟨Set.Iio (R 0), isOpen_Iio, by simpa using hR0pos,
        by intro x hx; exact hx.1⟩
    have hnhds : 𝓝[Set.Ioo 0 (R 0)] (0 : ℝ) = 𝓝[>] 0 := by
      rw [show Set.Ioo 0 (R 0) = Set.Iio (R 0) ∩ Set.Ioi 0 by ext; simp [and_comm]]
      exact nhdsWithin_inter_of_mem hIio_mem
    have hmono : 𝓝[Set.Ioo 0 (R 0)] (0 : ℝ) ≤ 𝓝[Set.Icc 0 (R 0)] (0 : ℝ) :=
      nhdsWithin_mono _ (by intro x hx; exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
    have hlim := (hcont.continuousWithinAt h0).tendsto.mono_left (hnhds ▸ hmono)
    have hzero : rightAlpha R 0 = Real.pi / 2 :=
      rightAlpha_zero R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
    simpa [hzero] using hlim
  have hR0pos : 0 < R 0 := hR_pos 0 ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hnhds : 𝓝[Set.Ioo 0 (R 0)] (0 : ℝ) = 𝓝[>] 0 := by
    have hIio_mem : Set.Iio (R 0) ∈ 𝓝[>] (0 : ℝ) := by
      rw [mem_nhdsWithin]
      exact ⟨Set.Iio (R 0), isOpen_Iio, by simpa using hR0pos,
        by intro x hx; exact hx.1⟩
    rw [show Set.Ioo 0 (R 0) = Set.Iio (R 0) ∩ Set.Ioi 0 by ext; simp [and_comm]]
    exact nhdsWithin_inter_of_mem hIio_mem
  have hR_cont_at : ContinuousAt R (Real.pi / 2) :=
    hR_nhds.continuousOn.continuousAt (Ioo_mem_nhds (by linarith) (by linarith))
  have hderiv_cont : ContinuousAt (deriv R) (Real.pi / 2) := by
    have hcont := ContDiffOn.continuousOn_derivWithin hR_nhds
      (uniqueDiffOn_Ioo (Real.pi / 2 - δ) (Real.pi / 2 + δ)) (by simp)
    have hmem : Real.pi / 2 ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 + δ) :=
      ⟨by linarith, by linarith⟩
    have hcont_at := hcont.continuousWithinAt hmem
    have heq : derivWithin R (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 + δ)) =ᶠ[𝓝 (Real.pi / 2)] deriv R := by
      filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with x hx
      exact derivWithin_of_mem_nhds (Ioo_mem_nhds hx.1 hx.2)
    have hx : deriv R (Real.pi / 2) = derivWithin R (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 + δ)) (Real.pi / 2) := by
      rw [derivWithin_of_mem_nhds (Ioo_mem_nhds hmem.1 hmem.2)]
    have hcont_at' : ContinuousWithinAt (deriv R) (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 + δ)) (Real.pi / 2) :=
      hcont_at.congr_of_eventuallyEq (heq.symm.filter_mono nhdsWithin_le_nhds) hx
    exact hcont_at'.continuousAt (Ioo_mem_nhds hmem.1 hmem.2)
  have hderiv_alpha : Tendsto (fun t => deriv R (rightAlpha R t)) (𝓝[>] 0) (𝓝 (deriv R (Real.pi / 2))) :=
    Filter.Tendsto.comp hderiv_cont.tendsto hα_tendsto
  have hR_alpha : Tendsto (fun t => R (rightAlpha R t)) (𝓝[>] 0) (𝓝 (R (Real.pi / 2))) :=
    Filter.Tendsto.comp hR_cont_at.tendsto hα_tendsto
  have hsin_alpha : Tendsto (fun t => Real.sin (rightAlpha R t)) (𝓝[>] 0) (𝓝 (Real.sin (Real.pi / 2))) :=
    (Real.continuous_sin.tendsto (Real.pi / 2)).comp hα_tendsto
  have hcos_alpha : Tendsto (fun t => Real.cos (rightAlpha R t)) (𝓝[>] 0) (𝓝 (Real.cos (Real.pi / 2))) :=
    (Real.continuous_cos.tendsto (Real.pi / 2)).comp hα_tendsto
  have hnum_tendsto : Tendsto (fun t => deriv R (rightAlpha R t) * Real.sin (rightAlpha R t) +
      R (rightAlpha R t) * Real.cos (rightAlpha R t)) (𝓝[>] 0)
      (𝓝 (deriv R (Real.pi / 2) * Real.sin (Real.pi / 2) +
        R (Real.pi / 2) * Real.cos (Real.pi / 2))) :=
    Filter.Tendsto.add (Filter.Tendsto.mul hderiv_alpha hsin_alpha)
      (Filter.Tendsto.mul hR_alpha hcos_alpha)
  have hden_tendsto : Tendsto (fun t => deriv R (rightAlpha R t) * Real.cos (rightAlpha R t) -
      R (rightAlpha R t) * Real.sin (rightAlpha R t)) (𝓝[>] 0)
      (𝓝 (deriv R (Real.pi / 2) * Real.cos (Real.pi / 2) -
        R (Real.pi / 2) * Real.sin (Real.pi / 2))) :=
    Filter.Tendsto.sub (Filter.Tendsto.mul hderiv_alpha hcos_alpha)
      (Filter.Tendsto.mul hR_alpha hsin_alpha)
  have hden_ne : deriv R (Real.pi / 2) * Real.cos (Real.pi / 2) -
      R (Real.pi / 2) * Real.sin (Real.pi / 2) ≠ 0 := by
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two, ne_of_gt (hR_pos (Real.pi / 2) ⟨by linarith [Real.pi_pos], le_refl _⟩)]
  have hquot_tendsto := hnum_tendsto.div hden_tendsto hden_ne
  have hRpi_pos : 0 < R (Real.pi / 2) := hR_pos (Real.pi / 2) ⟨by linarith [Real.pi_pos], le_rfl⟩
  have hquot_eq : (deriv R (Real.pi / 2) * Real.sin (Real.pi / 2) +
        R (Real.pi / 2) * Real.cos (Real.pi / 2)) /
      (deriv R (Real.pi / 2) * Real.cos (Real.pi / 2) -
        R (Real.pi / 2) * Real.sin (Real.pi / 2)) =
      - deriv R (Real.pi / 2) / R (Real.pi / 2) := by
    have hnum : deriv R (Real.pi / 2) * Real.sin (Real.pi / 2) +
        R (Real.pi / 2) * Real.cos (Real.pi / 2) = deriv R (Real.pi / 2) := by
      simp [Real.sin_pi_div_two, Real.cos_pi_div_two]
    have hden : deriv R (Real.pi / 2) * Real.cos (Real.pi / 2) -
        R (Real.pi / 2) * Real.sin (Real.pi / 2) = -R (Real.pi / 2) := by
      simp [Real.sin_pi_div_two, Real.cos_pi_div_two]
    rw [hnum, hden]
    field_simp [ne_of_gt hRpi_pos]
  rw [hquot_eq] at hquot_tendsto
  refine hquot_tendsto.congr' ?_
  filter_upwards [(hnhds ▸ self_mem_nhdsWithin : Set.Ioo 0 (R 0) ∈ 𝓝[>] (0 : ℝ))] with t ht
  have ht' : t ∈ Set.Ioo 0 (R 0) := ht
  have h := rightProfile_deriv R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound t ht'
  simpa [h] using h.symm

end

end Commons.Geometry.Ulam

namespace Commons.Geometry.Ulam

open Set Filter
open scoped Topology ContDiff

noncomputable section

/-- The right-branch profile has the one-sided derivative
`- deriv R (π/2) / R (π/2)` at `0`. -/
lemma rightProfile_hasDerivWithinAt_zero
    (R : ℝ → ℝ) {η δ : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hδ : 0 < δ)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_nhds : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 + δ)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α) :
    HasDerivWithinAt (rightProfile R) (- deriv R (Real.pi / 2) / R (Real.pi / 2))
      (Set.Ici 0) 0 := by
  have hs : Set.Ioo 0 (R 0) ∈ 𝓝[>] (0 : ℝ) := by
    have hR0pos : 0 < R 0 := hR_pos 0 ⟨le_rfl, by linarith [Real.pi_pos]⟩
    have hIio_mem : Set.Iio (R 0) ∈ 𝓝[>] (0 : ℝ) := by
      rw [mem_nhdsWithin]
      exact ⟨Set.Iio (R 0), isOpen_Iio, by simpa using hR0pos,
        by intro x hx; exact hx.1⟩
    rw [show Set.Ioo 0 (R 0) = Set.Iio (R 0) ∩ Set.Ioi 0 by ext; simp [and_comm]]
    exact Filter.inter_mem hIio_mem self_mem_nhdsWithin
  refine hasDerivWithinAt_Ici_of_tendsto_deriv
    (f := rightProfile R) (s := Set.Ioo 0 (R 0)) (a := 0)
    (e := - deriv R (Real.pi / 2) / R (Real.pi / 2)) ?_ ?_ ?_ ?_
  · exact rightProfile_differentiableOn R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
  · exact rightProfile_continuousWithinAt_zero R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
  · exact hs
  · exact rightProfile_deriv_tendsto_zero R hη hηsmall hδ hR_cont hR_nhds hR_pos hR_lower hR_deriv_bound

set_option maxHeartbeats 4000000 in
/-- The endpoint formula for the right branch, in `derivWithin` form. -/
lemma rightProfile_derivWithin_zero
    (R : ℝ → ℝ) {η δ : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hδ : 0 < δ)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_nhds : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 + δ)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α) :
    derivWithin (rightProfile R) (Set.Icc 0 (R 0)) 0 =
      - deriv R (Real.pi / 2) / R (Real.pi / 2) := by
  have h := rightProfile_hasDerivWithinAt_zero R hη hηsmall hδ hR_cont hR_nhds hR_pos hR_lower
    hR_deriv_bound
  have hmem : Set.Ici 0 ∈ 𝓝[Set.Icc 0 (R 0)] 0 := by
    rw [mem_nhdsWithin]
    exact ⟨Set.univ, isOpen_univ, trivial, by intro x hx; exact hx.2.1⟩
  have h' : HasDerivWithinAt (rightProfile R) (- deriv R (Real.pi / 2) / R (Real.pi / 2))
      (Set.Icc 0 (R 0)) 0 :=
    h.mono_of_mem_nhdsWithin hmem
  have hR0pos : 0 < R 0 := hR_pos 0 ⟨le_rfl, by linarith [Real.pi_pos]⟩
  exact h'.derivWithin ((uniqueDiffOn_Icc hR0pos).uniqueDiffWithinAt ⟨le_rfl, le_of_lt hR0pos⟩)

end

end Commons.Geometry.Ulam
