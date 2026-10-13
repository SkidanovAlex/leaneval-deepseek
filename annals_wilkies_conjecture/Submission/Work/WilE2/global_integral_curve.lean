import Mathlib
import Submission.Work.WilE2.Setup
import Submission.Work.WilE2.exists_smooth_cutoff_infty
import Submission.Work.WilE2.local_invariance
import Submission.Work.WilE2.global_integralCurve_of_uniform_local

namespace Work.WilE2

open Filter Metric
open scoped Topology

theorem global_integral_curve {m : ℕ} (V : (Fin m → ℝ) → (Fin (m - 1) → ℝ)) (X : (Fin m → ℝ) → (Fin m → ℝ)) (hV : ContDiff ℝ 1 V) (hX : ContDiff ℝ 1 X) (hC : IsCompact {z | V z = 0}) (hgrad : ∀ z, V z = 0 → LinearIndependent ℝ (fun i => fderiv ℝ (fun w => V w i) z)) (hX0 : ∀ z, V z = 0 → X z ≠ 0) (htan : ∀ z, V z = 0 → ∀ i, fderiv ℝ (fun w => V w i) z (X z) = 0) : ∀ z, V z = 0 → ∃ γ : ℝ → Fin m → ℝ, γ 0 = z ∧ (∀ t, HasDerivAt γ (X (γ t)) t) ∧ (∀ t, V (γ t) = 0) := by
  classical
  obtain ⟨U, χ, hUopen, hUM, hχsm, hχcs, hχ1, hχnn, hχle⟩ :=
    exists_smooth_cutoff_infty {z | V z = 0} hC
  have hχ1c : ContDiff ℝ 1 χ := (contDiff_infty.mp hχsm) 1
  -- the vector field, cut off to a neighbourhood of the level set
  set V' : (Fin m → ℝ) → (Fin m → ℝ) := fun z => χ z • X z with hV'
  have hcd : ContDiff ℝ 1 V' := by rw [hV']; exact hχ1c.smul hX
  have hcs : HasCompactSupport V' := by rw [hV']; exact hχcs.smul_right
  obtain ⟨K, hLip⟩ := hcd.lipschitzWith_of_hasCompactSupport hcs one_ne_zero
  obtain ⟨C, hCb⟩ := hcs.exists_bound_of_continuousOn hcd.continuous.continuousOn
  have hbound : ∀ x, ‖V' x‖ ≤ max C 0 := by
    intro x
    by_cases hx : x ∈ tsupport V'
    · exact le_trans (hCb x hx) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
      exact le_max_right C 0
  -- an explicit bound on the norm of `V'`
  let L : NNReal := ⌈max C 0⌉₊
  have hL : ∀ x : Fin m → ℝ, ‖V' x‖ ≤ (L : ℝ) :=
    fun x => le_trans (hbound x) (Nat.le_ceil (max C 0))
  -- a uniform time step, from Picard–Lindelöf with uniform constants
  let ε : ℝ := 1 / ((L : ℝ) + 1)
  have hε : 0 < ε := by
    have : (0 : ℝ) ≤ L := L.coe_nonneg
    positivity
  have hmem : (0 : ℝ) ∈ Set.Icc (-ε) ε := by
    rw [Set.mem_Icc]
    exact ⟨neg_nonpos.mpr hε.le, hε.le⟩
  have hpl : ∀ x₀ : Fin m → ℝ,
      IsPicardLindelof (fun _ : ℝ => V') (tmin := -ε) (tmax := ε) ⟨0, hmem⟩ x₀ 1 0 L K := by
    intro x₀
    refine IsPicardLindelof.of_time_independent ?_ ?_ ?_
    · intro x _
      exact hL x
    · exact hLip.lipschitzOnWith
    · have hmax : max (ε - 0) (0 - -ε) = ε := by simp [max_self]
      rw [hmax]
      show (L : ℝ) * (1 / ((L : ℝ) + 1)) ≤ 1 - 0
      rw [sub_zero, mul_one_div, div_le_one (by positivity)]
      linarith [NNReal.coe_nonneg L]
  have hunif : ∃ δ > 0, ∀ x : Fin m → ℝ, ∃ γ : ℝ → Fin m → ℝ,
      γ 0 = x ∧ ∀ t ∈ Set.Ioo (-δ) δ, HasDerivAt γ (V' (γ t)) t := by
    refine ⟨ε, hε, fun x₀ => ?_⟩
    obtain ⟨α, hα0, hα⟩ := IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ (hpl x₀)
    exact ⟨α, hα0, fun t ht =>
      (hα t (Set.Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩
  obtain ⟨δ, hδ, hloc⟩ := hunif
  intro z hz
  obtain ⟨γ, hγ0, hγd⟩ := global_integralCurve_of_uniform_local V' K hLip δ hδ hloc z
  -- the trajectory stays on the level set, by connectedness of `ℝ`
  have hγcont : Continuous γ := continuous_iff_continuousAt.mpr fun t => (hγd t).continuousAt
  have hclosed : IsClosed {t : ℝ | V (γ t) = 0} :=
    isClosed_eq (hV.continuous.comp hγcont) continuous_const
  have hopen : IsOpen {t : ℝ | V (γ t) = 0} := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have hode : ∀ᶠ s in nhds t, HasDerivAt γ (X (γ s)) s := by
      have h1 : ∀ᶠ s in nhds t, γ s ∈ U :=
        hγcont.continuousAt.preimage_mem_nhds (hUopen.mem_nhds (hUM ht))
      filter_upwards [h1] with s hsU
      have hs := hγd s
      rw [hV'] at hs
      simp only at hs
      rw [hχ1 (γ s) hsU, one_smul] at hs
      exact hs
    exact local_invariance V X hV hX hgrad htan γ t ht hode
  have hclopen : IsClopen {t : ℝ | V (γ t) = 0} := ⟨hclosed, hopen⟩
  have hne : ({t : ℝ | V (γ t) = 0}).Nonempty := ⟨0, by simp [hγ0, hz]⟩
  have hAll : ∀ t : ℝ, V (γ t) = 0 := by
    have huniv : {t : ℝ | V (γ t) = 0} = Set.univ := by
      rcases isClopen_iff.mp hclopen with h | h
      · exact absurd hne (by rw [h]; exact Set.not_nonempty_empty)
      · exact h
    intro t
    have := congrArg (fun s : Set ℝ => t ∈ s) huniv
    simpa using this
  refine ⟨γ, hγ0, fun t => ?_, hAll⟩
  have htU : γ t ∈ U := hUM (hAll t)
  have ht := hγd t
  rw [hV'] at ht
  simp only at ht
  rwa [hχ1 (γ t) htU, one_smul] at ht

end Work.WilE2
