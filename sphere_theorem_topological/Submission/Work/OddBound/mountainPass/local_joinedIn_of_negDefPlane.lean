import Mathlib
import Submission.Work.OddBound.mountainPass.taylor2_bound

set_option maxHeartbeats 1000000

namespace Work.OddBound.mountainPass

open Set Metric

/-- For a `C²` function, the quadratic form of the Hessian at `y` is close to that at `z` for `y`
near `z`. -/
private lemma exists_hessian_apply_close {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (z Δ : E) {ω : ℝ} (hω : 0 < ω) :
    ∃ ρ > 0, ∀ y : E, dist y z < ρ →
      |(fderiv ℝ (fderiv ℝ f) y) Δ Δ - (fderiv ℝ (fderiv ℝ f) z) Δ Δ| ≤ ω := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h2 : Continuous fun p : E × E => (fderiv ℝ (fderiv ℝ f) p.1) p.2 :=
    h1.continuous_fderiv_apply (by norm_num)
  have h3 : Continuous fun y : E => (fderiv ℝ (fderiv ℝ f) y) Δ :=
    h2.comp (continuous_id.prodMk continuous_const)
  have h4 : Continuous fun y : E => (fderiv ℝ (fderiv ℝ f) y) Δ Δ :=
    h3.clm_apply continuous_const
  rcases Metric.continuousAt_iff.mp h4.continuousAt ω hω with ⟨ρ, hρ, hρ'⟩
  exact ⟨ρ, hρ, fun y hy => le_of_lt (hρ' hy)⟩


/-- If the second derivative is nonpositive along a segment and the first derivative at the initial
point is nonpositive, then `f` does not increase along the segment. -/
private lemma slide_le_of_second_deriv_nonpos {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ 2 f) {x Δ : E}
    (h0 : fderiv ℝ f x Δ ≤ 0)
    (h2 : ∀ u ∈ Set.Icc (0 : ℝ) 1, (fderiv ℝ (fderiv ℝ f) (x + u • Δ)) Δ Δ ≤ 0) :
    ∀ u ∈ Set.Icc (0 : ℝ) 1, f (x + u • Δ) ≤ f x := by
  have hlin : ∀ u : ℝ, HasDerivAt (fun t : ℝ => x + t • Δ) Δ u := by
    intro u
    simpa using ((hasDerivAt_id u).smul_const Δ).const_add x
  have hdφ : ∀ u : ℝ, HasDerivAt (fun t : ℝ => f (x + t • Δ))
      ((fderiv ℝ f (x + u • Δ)) Δ) u := by
    intro u
    exact ((hf.differentiable (by norm_num)).differentiableAt).hasFDerivAt.comp_hasDerivAt u
      (hlin u)
  have hdψ : ∀ u : ℝ, HasDerivAt (fun t : ℝ => (fderiv ℝ f (x + t • Δ)) Δ)
      ((fderiv ℝ (fderiv ℝ f) (x + u • Δ)) Δ Δ) u := by
    intro u
    have hc1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
    have hg : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (x + u • Δ)) (x + u • Δ) :=
      ((hc1.differentiable (by norm_num)).differentiableAt).hasFDerivAt
    have hcomp : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • Δ))
        ((fderiv ℝ (fderiv ℝ f) (x + u • Δ)) Δ) u := hg.comp_hasDerivAt u (hlin u)
    have hcc := hcomp.clm_apply (hasDerivAt_const (𝕜 := ℝ) u (Δ : E))
    simpa using hcc
  have hAntiψ : AntitoneOn (fun t : ℝ => (fderiv ℝ f (x + t • Δ)) Δ) (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) ?_ ?_ ?_
    · intro u _
      exact (hdψ u).continuousAt.continuousWithinAt
    · intro u _
      exact (hdψ u).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      rw [(hdψ u).deriv]
      exact h2 u ⟨hu.1.le, hu.2.le⟩
  have hAntiφ : AntitoneOn (fun t : ℝ => f (x + t • Δ)) (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) ?_ ?_ ?_
    · intro u _
      exact (hdφ u).continuousAt.continuousWithinAt
    · intro u _
      exact (hdφ u).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      rw [(hdφ u).deriv]
      have hle : (fderiv ℝ f (x + u • Δ)) Δ ≤ (fderiv ℝ f x) Δ := by
        simpa using hAntiψ (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
          ⟨hu.1.le, hu.2.le⟩ hu.1.le
      linarith
  intro u hu
  have hh := hAntiφ (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1) hu hu.1
  simpa using hh

/-- The quadratic form of a continuous bilinear form scales quadratically. -/
private lemma clm_smul_smul_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E →L[ℝ] (E →L[ℝ] ℝ)) (p : E) (c : ℝ) :
    H (c • p) (c • p) = c ^ 2 * H p p := by
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

theorem local_joinedIn_of_negDefPlane
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {Λ : ℝ} {z : E} (hz : f z = Λ)
    (hcz : fderiv ℝ f z = 0)
    (hbad : ∃ v w : E, ∀ c d : ℝ, (c, d) ≠ 0 →
      (fderiv ℝ (fderiv ℝ f) z) (c • v + d • w) (c • v + d • w) < 0) :
    ∃ ρ > 0, ∀ x y : E, dist x z < ρ → dist y z < ρ → f x < Λ → f y < Λ →
      JoinedIn {w : E | f w < Λ} x y := by
  classical
  set Hz : E →L[ℝ] (E →L[ℝ] ℝ) := fderiv ℝ (fderiv ℝ f) z with hHz
  obtain ⟨v, w, hvw⟩ := hbad
  -- ## Step 1: the two-plane on which the Hessian is negative definite
  set P : Submodule ℝ E := Submodule.span ℝ (Set.range ![v, w]) with hP
  have hrange : Set.range ![v, w] = ({v, w} : Set E) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      simp only [mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  have hmemP : ∀ p : E, p ∈ P ↔ ∃ c d : ℝ, c • v + d • w = p := by
    intro p
    rw [hP, hrange, Submodule.mem_span_pair]
  have hw0 : w ≠ 0 := by
    intro h0
    have h := hvw 0 1 (by simp)
    rw [zero_smul, one_smul, h0] at h
    simpa using h
  have hw_not_mem : ∀ a : ℝ, a • w ≠ v := by
    intro a ha
    have h := hvw 1 (-a) (by simp)
    rw [one_smul, neg_smul, ha] at h
    simpa using h
  have hlin : LinearIndependent ℝ ![v, w] := by
    rw [linearIndependent_fin2]
    exact ⟨by simpa using hw0, by simpa using hw_not_mem⟩
  have hfinrank : Module.finrank ℝ ↥P = 2 := by
    rw [hP]
    simpa using finrank_span_eq_card hlin
  have hrank : 1 < Module.rank ℝ ↥P := by
    rw [← Module.finrank_eq_rank' ℝ ↥P, hfinrank]
    norm_num
  -- ## Step 2: the negative definiteness constant `μ`
  have hwP : w ∈ P := (hmemP w).mpr ⟨0, 1, by simp⟩
  have hne_sphere : (Metric.sphere (0 : ↥P) 1).Nonempty :=
    ⟨⟨‖w‖⁻¹ • w, P.smul_mem _ hwP⟩, by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)]⟩
  have hex : ∃ u₀ ∈ Metric.sphere (0 : ↥P) 1,
      ∀ u ∈ Metric.sphere (0 : ↥P) 1, Hz (u : E) (u : E) ≤ Hz (u₀ : E) (u₀ : E) :=
    (isCompact_sphere (0 : ↥P) 1).exists_isMaxOn hne_sphere
      ((Hz.continuous.comp continuous_subtype_val).clm_apply continuous_subtype_val).continuousOn
  obtain ⟨u₀, hu₀mem, hu₀max⟩ := hex
  have hu₀norm : ‖(u₀ : E)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hu₀mem
  have hu₀ne : (u₀ : E) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu₀norm
    exact one_ne_zero hu₀norm.symm
  have hnegP : ∀ p ∈ P, p ≠ 0 → Hz p p < 0 := by
    intro p hp hp0
    obtain ⟨c, d, hcd⟩ := (hmemP p).mp hp
    have hne : (c, d) ≠ 0 := by
      intro h
      apply hp0
      have hc : c = 0 := congrArg Prod.fst h
      have hd : d = 0 := congrArg Prod.snd h
      rw [← hcd, hc, hd]
      simp
    have h := hvw c d hne
    rwa [hcd] at h
  have hneg_u₀ : Hz (u₀ : E) (u₀ : E) < 0 := hnegP _ u₀.2 hu₀ne
  set μ : ℝ := -(Hz (u₀ : E) (u₀ : E)) with hμdef
  have hμpos : 0 < μ := by rw [hμdef]; linarith
  have hμu₀ : Hz (u₀ : E) (u₀ : E) = -μ := by rw [hμdef]; ring
  have hneg : ∀ p ∈ P, Hz p p ≤ -μ * ‖p‖ ^ 2 := by
    intro p hp
    rcases eq_or_ne p 0 with rfl | hp0
    · simp [hμdef]
    · have hpd : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp0
      have hmem : (‖p‖⁻¹ • p) ∈ P := P.smul_mem _ hp
      have hu : ‖(⟨‖p‖⁻¹ • p, hmem⟩ : ↥P)‖ = 1 := by
        simp [norm_smul, inv_mul_cancel₀ hpd]
      have hmax : Hz (‖p‖⁻¹ • p) (‖p‖⁻¹ • p) ≤ Hz (u₀ : E) (u₀ : E) :=
        hu₀max ⟨‖p‖⁻¹ • p, hmem⟩ (by
          rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hu)
      have hmax' : Hz (‖p‖⁻¹ • p) (‖p‖⁻¹ • p) ≤ -μ := by
        rw [hμu₀] at hmax
        exact hmax
      have hrepr : p = ‖p‖ • (‖p‖⁻¹ • p) := by
        rw [smul_smul, mul_inv_cancel₀ hpd, one_smul]
      have hrepr2 : Hz p p = Hz (‖p‖ • (‖p‖⁻¹ • p)) (‖p‖ • (‖p‖⁻¹ • p)) := by
        conv_lhs => rw [hrepr]
      rw [hrepr2, clm_smul_smul_smul]
      have h1 : ‖p‖ ^ 2 * Hz (‖p‖⁻¹ • p) (‖p‖⁻¹ • p) ≤ ‖p‖ ^ 2 * (-μ) :=
        mul_le_mul_of_nonneg_left hmax' (sq_nonneg _)
      have h2 : ‖p‖ ^ 2 * (-μ) = -μ * ‖p‖ ^ 2 := by ring
      linarith [h1, h2]
  -- ## Step 3: constants
  have hμ16pos : 0 < μ / 16 := by linarith
  set A : ℝ := ‖Hz‖ with hAdef
  have hAnonneg : 0 ≤ A := by rw [hAdef]; positivity
  obtain ⟨ρ_tay, hρ_tay, htay⟩ := taylor2_bound hf z (μ / 16) hμ16pos
  rw [← hHz] at htay
  obtain ⟨ρ_pert, hρ_pert, hpert⟩ :=
    exists_hessian_apply_close hf z (u₀ : E) (ω := μ / 16) hμ16pos
  set ρ₀ : ℝ := min ρ_tay ρ_pert with hρ₀def
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀def]; exact lt_min hρ_tay hρ_pert
  have hρ₀_tay : ρ₀ ≤ ρ_tay := by rw [hρ₀def]; exact min_le_left _ _
  have hρ₀_pert : ρ₀ ≤ ρ_pert := by rw [hρ₀def]; exact min_le_right _ _
  set R₀ : ℝ := ρ₀ / 2 with hR₀def
  have hR₀pos : 0 < R₀ := by rw [hR₀def]; linarith
  set ρ₁ : ℝ := min (ρ₀ / 8) (μ * R₀ / (64 * (A + 1))) with hρ₁def
  have hA1pos : 0 < A + 1 := by linarith
  have hρ₁pos : 0 < ρ₁ := by
    rw [hρ₁def]
    exact lt_min (by linarith) (div_pos (mul_pos hμpos hR₀pos) (by linarith))
  have hρ₁_nonneg : 0 ≤ ρ₁ := hρ₁pos.le
  have hρ₁_le_ρ₀8 : ρ₁ ≤ ρ₀ / 8 := by rw [hρ₁def]; exact min_le_left _ _
  have hρ₁_le_μR : ρ₁ ≤ μ * R₀ / (64 * (A + 1)) := by rw [hρ₁def]; exact min_le_right _ _
  have hρ₁_le_R₀4 : ρ₁ ≤ R₀ / 4 := by
    have h : ρ₀ / 8 = R₀ / 4 := by rw [hR₀def]; ring
    linarith
  have hR₀ρ₁ : R₀ + ρ₁ ≤ ρ₀ := by
    have h : ρ₀ / 2 = R₀ := by rw [hR₀def]
    linarith
  -- scalar consequence of the definition of `ρ₁`
  have hAρ₁ : A * ρ₁ ≤ μ * R₀ / 64 := by
    have h1 : A * ρ₁ ≤ A * (μ * R₀ / (64 * (A + 1))) :=
      mul_le_mul_of_nonneg_left hρ₁_le_μR hAnonneg
    have h2 : A * (μ * R₀ / (64 * (A + 1))) = (A / (A + 1)) * (μ * R₀ / 64) := by
      field_simp
    rw [h2] at h1
    have h3 : A / (A + 1) ≤ 1 := (div_le_one hA1pos).2 (by linarith)
    calc A * ρ₁ ≤ (A / (A + 1)) * (μ * R₀ / 64) := h1
      _ ≤ 1 * (μ * R₀ / 64) := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = μ * R₀ / 64 := one_mul _
  have hAρ₁' : A * R₀ * ρ₁ ≤ μ * R₀ ^ 2 / 64 := by
    calc A * R₀ * ρ₁ = (A * ρ₁) * R₀ := by ring
      _ ≤ (μ * R₀ / 64) * R₀ := mul_le_mul_of_nonneg_right hAρ₁ hR₀pos.le
      _ = μ * R₀ ^ 2 / 64 := by ring
  -- ## Step 4: the sublevel cylinder
  have hmargin : ∀ p ∈ P, ∀ q ∈ Pᗮ, ‖p‖ = R₀ → ‖q‖ ≤ ρ₁ → f (z + p + q) < Λ := by
    intro p hp q hq hpR hqρ
    have hball2 : ‖p + q‖ ≤ R₀ + ρ₁ := by
      calc ‖p + q‖ ≤ ‖p‖ + ‖q‖ := norm_add_le _ _
        _ ≤ R₀ + ρ₁ := by linarith
    have ht := htay (p + q) (le_trans hball2 hR₀ρ₁ |>.trans hρ₀_tay)
    rw [hz, hcz] at ht
    simp only [zero_apply, sub_zero] at ht
    have hup : f (z + (p + q)) ≤ Λ + (1 / 2) * (Hz (p + q) (p + q)) + (μ / 16) * ‖p + q‖ ^ 2 := by
      have h1 : f (z + (p + q)) - Λ - (1 / 2) * (Hz (p + q) (p + q)) ≤ (μ / 16) * ‖p + q‖ ^ 2 :=
        le_trans (le_abs_self _) ht
      linarith
    have hquad : Hz (p + q) (p + q) ≤ -μ * R₀ ^ 2 + 2 * A * R₀ * ρ₁ + A * ρ₁ ^ 2 := by
      have hexp : Hz (p + q) (p + q) = Hz p p + Hz p q + Hz q p + Hz q q := by
        simp only [map_add, add_apply]
        ring
      have h1 : Hz p p ≤ -μ * R₀ ^ 2 := by
        have := hneg p hp
        rw [hpR] at this
        simpa using this
      have h2 : Hz p q ≤ A * R₀ * ρ₁ := by
        have ha : ‖Hz p q‖ ≤ (A * R₀) * ρ₁ := by
          calc ‖Hz p q‖ ≤ ‖Hz p‖ * ‖q‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ (A * R₀) * ρ₁ := by
                refine mul_le_mul ?_ hqρ (norm_nonneg q) ?_
                · calc ‖Hz p‖ ≤ ‖Hz‖ * ‖p‖ := ContinuousLinearMap.le_opNorm _ _
                    _ = A * R₀ := by rw [← hAdef, hpR]
                · positivity
        calc Hz p q ≤ ‖Hz p q‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
          _ ≤ A * R₀ * ρ₁ := ha
      have h3 : Hz q p ≤ A * R₀ * ρ₁ := by
        have ha : ‖Hz q p‖ ≤ (A * R₀) * ρ₁ := by
          calc ‖Hz q p‖ ≤ ‖Hz q‖ * ‖p‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ (A * ρ₁) * R₀ := by
                refine mul_le_mul ?_ hpR.le (norm_nonneg p) ?_
                · calc ‖Hz q‖ ≤ ‖Hz‖ * ‖q‖ := ContinuousLinearMap.le_opNorm _ _
                    _ ≤ A * ρ₁ := by
                        rw [← hAdef]
                        exact mul_le_mul_of_nonneg_left hqρ (norm_nonneg Hz)
                · positivity
            _ = (A * R₀) * ρ₁ := by ring
        calc Hz q p ≤ ‖Hz q p‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
          _ ≤ A * R₀ * ρ₁ := ha
      have h4 : Hz q q ≤ A * ρ₁ ^ 2 := by
        have ha : ‖Hz q q‖ ≤ A * ρ₁ ^ 2 := by
          calc ‖Hz q q‖ ≤ ‖Hz q‖ * ‖q‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ (A * ρ₁) * ρ₁ := by
                refine mul_le_mul ?_ hqρ (norm_nonneg q) ?_
                · calc ‖Hz q‖ ≤ ‖Hz‖ * ‖q‖ := ContinuousLinearMap.le_opNorm _ _
                    _ ≤ A * ρ₁ := by
                        rw [← hAdef]
                        exact mul_le_mul_of_nonneg_left hqρ (norm_nonneg Hz)
                · positivity
            _ = A * ρ₁ ^ 2 := by ring
        calc Hz q q ≤ ‖Hz q q‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
          _ ≤ A * ρ₁ ^ 2 := ha
      linarith
    have hρ2 : (R₀ + ρ₁) ^ 2 ≤ 25 * R₀ ^ 2 / 16 := by
      nlinarith [hρ₁_le_R₀4, hR₀pos, hρ₁_nonneg]
    have hε2 : (μ / 16) * ‖p + q‖ ^ 2 ≤ (μ / 16) * (25 * R₀ ^ 2 / 16) := by
      have h1 : ‖p + q‖ ^ 2 ≤ (R₀ + ρ₁) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hball2 2
      exact (mul_le_mul_of_nonneg_left (le_trans h1 hρ2) hμ16pos.le)
    have hkey : (1 / 2) * (-μ * R₀ ^ 2 + 2 * A * R₀ * ρ₁ + A * ρ₁ ^ 2)
        + (μ / 16) * (25 * R₀ ^ 2 / 16) < 0 := by
      have hpos : 0 < μ * R₀ ^ 2 := mul_pos hμpos (pow_pos hR₀pos 2)
      nlinarith [hAρ₁', hAρ₁, hρ₁_le_R₀4, hρ₁_nonneg, hAnonneg, hpos]
    have hmain : (1 / 2) * (Hz (p + q) (p + q)) + (μ / 16) * ‖p + q‖ ^ 2 < 0 := by
      linarith [hquad, hkey, hε2]
    have hfin : f (z + (p + q)) < Λ := by linarith
    simpa [add_assoc] using hfin
  set S : Set E := {w : E | f w < Λ} with hS
  -- ## Step 5: the local path
  have hlocal : ∀ x : E, dist x z < ρ₁ → f x < Λ → JoinedIn S x (z + R₀ • (u₀ : E)) := by
    intro x hxdist hfx
    obtain ⟨p, hpP, q, hqQ, hpq⟩ := Submodule.exists_add_mem_mem_orthogonal (K := P) (x - z)
    have hxdecomp : x = z + (p + q) := by
      rw [← hpq]
      abel
    have hinner0 : inner ℝ p q = 0 := (Submodule.mem_orthogonal P q).mp hqQ p hpP
    have hdist' : ‖x - z‖ < ρ₁ := by rwa [dist_eq_norm] at hxdist
    have hpnorm : ‖p‖ ≤ ‖x - z‖ := by
      have h : ‖p‖ * ‖p‖ ≤ ‖x - z‖ * ‖x - z‖ := by
        rw [hpq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p q hinner0]
        nlinarith [mul_self_nonneg ‖q‖]
      exact (mul_self_le_mul_self_iff (norm_nonneg p) (norm_nonneg (x - z))).mpr h
    have hqnorm : ‖q‖ ≤ ‖x - z‖ := by
      have h : ‖q‖ * ‖q‖ ≤ ‖x - z‖ * ‖x - z‖ := by
        rw [hpq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p q hinner0]
        nlinarith [mul_self_nonneg ‖p‖]
      exact (mul_self_le_mul_self_iff (norm_nonneg q) (norm_nonneg (x - z))).mpr h
    have hpn : ‖p‖ < ρ₁ := lt_of_le_of_lt hpnorm hdist'
    have hqn : ‖q‖ < ρ₁ := lt_of_le_of_lt hqnorm hdist'
    -- a direction in `P` with nonpositive derivative
    have he₀P : (u₀ : E) ∈ P := u₀.2
    obtain ⟨Δ, hΔP, hΔn, hΔderiv, hΔcases⟩ :
        ∃ Δ ∈ P, ‖Δ‖ = 1 ∧ fderiv ℝ f x Δ ≤ 0 ∧ (Δ = (u₀ : E) ∨ Δ = -(u₀ : E)) := by
      by_cases hpos : 0 < (fderiv ℝ f x) (u₀ : E)
      · refine ⟨-(u₀ : E), P.neg_mem he₀P, by simp [hu₀norm], ?_, Or.inr rfl⟩
        rw [map_neg, neg_nonpos]
        exact hpos.le
      · exact ⟨(u₀ : E), he₀P, hu₀norm, le_of_not_gt hpos, Or.inl rfl⟩
    have hΔbound : ∀ y : E, dist y z < ρ_pert →
        (fderiv ℝ (fderiv ℝ f) y) Δ Δ ≤ Hz Δ Δ + μ / 16 := by
      intro y hy
      have hyy := hpert y hy
      rcases hΔcases with hΔeq | hΔeq
      · rw [hΔeq]
        linarith [le_abs_self ((fderiv ℝ (fderiv ℝ f) y) (u₀ : E) (u₀ : E)
          - Hz (u₀ : E) (u₀ : E)), hyy]
      · have hsign : ∀ H : E →L[ℝ] (E →L[ℝ] ℝ),
            H (-(u₀ : E)) (-(u₀ : E)) = H (u₀ : E) (u₀ : E) := by
          intro H
          have h := clm_smul_smul_smul H (u₀ : E) (-1 : ℝ)
          simpa using h
        rw [hΔeq, hsign, hsign]
        linarith [le_abs_self ((fderiv ℝ (fderiv ℝ f) y) (u₀ : E) (u₀ : E)
          - Hz (u₀ : E) (u₀ : E)), hyy]
    -- the slide length
    have hIVT : ∃ t₁ ∈ Icc (0 : ℝ) (R₀ + ρ₁), ‖p + t₁ • Δ‖ = R₀ := by
      have hcont : ContinuousOn (fun t : ℝ => ‖p + t • Δ‖) (Icc 0 (R₀ + ρ₁)) := by fun_prop
      have hle1 : ‖p + (0 : ℝ) • Δ‖ ≤ R₀ := by
        have h : ‖p‖ ≤ R₀ := by linarith [hρ₁_le_R₀4]
        simpa using h
      have hle2 : R₀ ≤ ‖p + (R₀ + ρ₁) • Δ‖ := by
        have h1 : ‖(R₀ + ρ₁) • Δ‖ ≤ ‖p + (R₀ + ρ₁) • Δ‖ + ‖p‖ := by
          simpa [add_sub_cancel_left] using norm_sub_le (p + (R₀ + ρ₁) • Δ) p
        have h2 : ‖(R₀ + ρ₁) • Δ‖ = R₀ + ρ₁ := by
          rw [norm_smul, hΔn, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      exact (intermediate_value_Icc (by linarith) hcont) ⟨hle1, hle2⟩
    obtain ⟨t₁, ht₁mem, ht₁eq⟩ := hIVT
    have ht₁nonneg : 0 ≤ t₁ := ht₁mem.1
    have ht₁le : t₁ ≤ R₀ + ρ₁ := ht₁mem.2
    have hp'P : p + t₁ • Δ ∈ P := P.add_mem hpP (P.smul_mem _ hΔP)
    -- the slide
    have hslide : JoinedIn S x (z + (p + t₁ • Δ) + q) := by
      have h0 : fderiv ℝ f x (t₁ • Δ) ≤ 0 := by
        rw [map_smul, smul_eq_mul]
        exact mul_nonpos_of_nonneg_of_nonpos ht₁nonneg hΔderiv
      have h2 : ∀ u ∈ Icc (0 : ℝ) 1,
          (fderiv ℝ (fderiv ℝ f) (x + u • (t₁ • Δ))) (t₁ • Δ) (t₁ • Δ) ≤ 0 := by
        intro u hu
        have hdist : dist (x + u • (t₁ • Δ)) z < ρ_pert := by
          rw [dist_eq_norm]
          have hrepr : x + u • (t₁ • Δ) - z = (p + u • (t₁ • Δ)) + q := by
            rw [hxdecomp]
            abel
          rw [hrepr]
          have htu : ‖u • (t₁ • Δ)‖ = u * t₁ := by
            rw [norm_smul, norm_smul, hΔn, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg hu.1, abs_of_nonneg ht₁nonneg]
          calc ‖(p + u • (t₁ • Δ)) + q‖ ≤ ‖p + u • (t₁ • Δ)‖ + ‖q‖ := norm_add_le _ _
            _ ≤ (‖p‖ + ‖u • (t₁ • Δ)‖) + ‖q‖ := by
                have := norm_add_le p (u • (t₁ • Δ))
                linarith
            _ < (ρ₁ + (R₀ + ρ₁)) + ρ₁ := by
                rw [htu]
                have h1 : u * t₁ ≤ R₀ + ρ₁ := by
                  nlinarith [hu.1, hu.2, ht₁nonneg, ht₁le]
                linarith [hpn, hqn, h1]
            _ ≤ ρ₀ := by linarith
            _ ≤ ρ_pert := hρ₀_pert
        have hbound := hΔbound (x + u • (t₁ • Δ)) hdist
        have hHzΔ : Hz Δ Δ ≤ -μ := by
          have := hneg Δ hΔP
          rw [hΔn] at this
          simpa using this
        have hneg2 : (fderiv ℝ (fderiv ℝ f) (x + u • (t₁ • Δ))) Δ Δ ≤ 0 := by
          linarith [hbound, hHzΔ, hμpos]
        rw [clm_smul_smul_smul]
        exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t₁) hneg2
      have hle := slide_le_of_second_deriv_nonpos hf h0 h2
      refine JoinedIn.ofLine (f := fun t : ℝ => z + (p + (t * t₁) • Δ) + q) ?_ ?_ ?_ ?_
      · fun_prop
      · show z + (p + (0 * t₁) • Δ) + q = x
        rw [hxdecomp]
        simp only [zero_mul, zero_smul, add_zero, add_assoc]
      · show z + (p + (1 * t₁) • Δ) + q = z + (p + t₁ • Δ) + q
        simp
      · rintro y ⟨t, ht, rfl⟩
        show f (z + (p + (t * t₁) • Δ) + q) < Λ
        have hstep : z + (p + (t * t₁) • Δ) + q = x + t • (t₁ • Δ) := by
          rw [hxdecomp]
          simp only [smul_smul]
          abel
        rw [hstep]
        exact lt_of_le_of_lt (hle t ht) hfx
    -- shrink the `Pᗮ`-component to zero
    have hshrink : JoinedIn S (z + (p + t₁ • Δ) + q) (z + (p + t₁ • Δ)) := by
      have hp'norm : ‖p + t₁ • Δ‖ = R₀ := ht₁eq
      refine JoinedIn.ofLine (f := fun t : ℝ => z + (p + t₁ • Δ) + ((1 : ℝ) - t) • q) ?_ ?_ ?_ ?_
      · fun_prop
      · show z + (p + t₁ • Δ) + ((1 : ℝ) - 0) • q = z + (p + t₁ • Δ) + q
        simp
      · show z + (p + t₁ • Δ) + ((1 : ℝ) - 1) • q = z + (p + t₁ • Δ)
        simp
      · rintro y ⟨t, ht, rfl⟩
        have hq' : ((1 : ℝ) - t) • q ∈ Pᗮ := Pᗮ.smul_mem _ hqQ
        have hqn' : ‖((1 : ℝ) - t) • q‖ ≤ ρ₁ := by
          rw [norm_smul, Real.norm_eq_abs]
          calc |(1 : ℝ) - t| * ‖q‖ ≤ 1 * ρ₁ := by
                refine mul_le_mul ?_ hqn.le (norm_nonneg q) (by norm_num)
                rw [abs_le]
                constructor <;> linarith [ht.1, ht.2]
            _ = ρ₁ := one_mul _
        exact hmargin (p + t₁ • Δ) hp'P (((1 : ℝ) - t) • q) hq' hp'norm hqn'
    -- rotate in `P` to the reference direction
    have hrot : JoinedIn S (z + (p + t₁ • Δ)) (z + R₀ • (u₀ : E)) := by
      have hpc : IsPathConnected (Metric.sphere (0 : ↥P) R₀) :=
        isPathConnected_sphere hrank 0 hR₀pos.le
      have hmem1 : (⟨p + t₁ • Δ, hp'P⟩ : ↥P) ∈ Metric.sphere (0 : ↥P) R₀ := by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
        exact ht₁eq
      have hmem2 : (⟨R₀ • (u₀ : E), P.smul_mem _ u₀.2⟩ : ↥P) ∈ Metric.sphere (0 : ↥P) R₀ := by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
        simp [norm_smul, hu₀norm, abs_of_pos hR₀pos]
      have hj := hpc.joinedIn ⟨p + t₁ • Δ, hp'P⟩ hmem1
        ⟨R₀ • (u₀ : E), P.smul_mem _ u₀.2⟩ hmem2
      have hmap := hj.map (f := fun u : ↥P => z + (u : E)) (by fun_prop)
      refine hmap.mono ?_
      rintro w ⟨u, hu, rfl⟩
      have hunorm : ‖(u : E)‖ = R₀ := by
        have h := hu
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
        exact h
      rw [hS]
      simpa using hmargin (u : E) u.2 0 (Submodule.zero_mem _) hunorm (by simp [hρ₁_nonneg])
    exact hslide.trans (hshrink.trans hrot)
  refine ⟨ρ₁, hρ₁pos, fun x y hx hy hfx hfy => ?_⟩
  exact (hlocal x hx hfx).trans (hlocal y hy hfy).symm

end Work.OddBound.mountainPass
