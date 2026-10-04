import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

namespace Work.OddBound.mountainPass.port

open Set Metric
open scoped Topology

/-- **Second-order Taylor estimate with an explicit small constant.**
For a `C²` function `f` on a real normed space and `ε > 0` there is `ρ > 0` such that for all `h`
with `‖h‖ ≤ ρ`,
`|f (z+h) - f z - f'(z) h - ½ f''(z)(h,h)| ≤ ε * ‖h‖²`. -/
theorem taylor2_bound_ns {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (z : E) :
    ∀ ε > 0, ∃ ρ > 0, ∀ h : E, ‖h‖ ≤ ρ →
      |f (z + h) - f z - (fderiv ℝ f z) h - (1 / 2) * ((fderiv ℝ (fderiv ℝ f) z) h h)|
        ≤ ε * ‖h‖ ^ 2 := by
  intro ε hε
  have hf' : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have hg : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((hf'.differentiable (by norm_num)).differentiableAt).hasFDerivAt
  have hlittle := hg.isLittleO
  rw [Asymptotics.isLittleO_iff] at hlittle
  have hev : ∀ᶠ x' in 𝓝 z, ‖fderiv ℝ f x' - fderiv ℝ f z -
      (fderiv ℝ (fderiv ℝ f) z) (x' - z)‖ ≤ ε * ‖x' - z‖ := hlittle hε
  obtain ⟨ρ₀, hρ₀, hbound₀⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ρ₀ / 2, by positivity, fun h hh => ?_⟩
  have hlt : ‖h‖ < ρ₀ := lt_of_le_of_lt hh (by linarith)
  set H2 := fderiv ℝ (fderiv ℝ f) z with hH2
  set φ : ℝ → ℝ := fun t => f (z + t • h) - t * ((fderiv ℝ f z) h) - (t ^ 2 / 2) * (H2 h h)
    with hφ
  have hφderiv : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt φ
      ((fderiv ℝ f (z + x • h) - fderiv ℝ f z - H2 (x • h)) h) (Set.Icc (0 : ℝ) 1) x := by
    intro x hx
    have h1 : HasDerivAt (fun t : ℝ => z + t • h) h x := by
      simpa using ((hasDerivAt_id x).smul_const h).const_add z
    have h2 : HasDerivAt (fun t : ℝ => f (z + t • h)) ((fderiv ℝ f (z + x • h)) h) x :=
      (((hf.differentiable (by norm_num)).differentiableAt).hasFDerivAt).comp_hasDerivAt x h1
    have h3 : HasDerivAt (fun t : ℝ => t * ((fderiv ℝ f z) h)) ((fderiv ℝ f z) h) x := by
      simpa using (hasDerivAt_id x).mul_const ((fderiv ℝ f z) h)
    have h4 : HasDerivAt (fun t : ℝ => (t ^ 2 / 2) * (H2 h h)) (x * (H2 h h)) x := by
      have h5 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) x x := by
        simpa using (hasDerivAt_pow 2 x).div_const 2
      exact h5.mul_const (H2 h h)
    have h6 : HasDerivAt φ
        ((fderiv ℝ f (z + x • h)) h - (fderiv ℝ f z) h - x * (H2 h h)) x :=
      (h2.sub h3).sub h4
    have h7 : HasDerivAt φ ((fderiv ℝ f (z + x • h) - fderiv ℝ f z - H2 (x • h)) h) x := by
      convert h6 using 2
      simp only [sub_apply, map_smul, smul_apply, smul_eq_mul]
    exact h7.hasDerivWithinAt
  have hbound' : ∀ x ∈ Set.Ico (0 : ℝ) 1,
      ‖(fderiv ℝ f (z + x • h) - fderiv ℝ f z - H2 (x • h)) h‖ ≤ ε * ‖h‖ ^ 2 := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hx1 : x ≤ 1 := hx.2.le
    have hxh : ‖x • h‖ ≤ ‖h‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hx0]
      calc x * ‖h‖ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right hx1 (norm_nonneg h)
        _ = ‖h‖ := one_mul _
    have hxlt : ‖x • h‖ < ρ₀ := lt_of_le_of_lt hxh hlt
    have hL := hbound₀ (y := z + x • h) (by rw [dist_eq_norm]; simpa using hxlt)
    have hL2 : ‖fderiv ℝ f (z + x • h) - fderiv ℝ f z - H2 (x • h)‖ ≤ ε * ‖x • h‖ := by
      simpa [H2, add_sub_cancel_left] using hL
    calc ‖(fderiv ℝ f (z + x • h) - fderiv ℝ f z - H2 (x • h)) h‖
        ≤ ‖fderiv ℝ f (z + x • h) - fderiv ℝ f z - H2 (x • h)‖ * ‖h‖ :=
          ContinuousLinearMap.le_opNorm _ h
      _ ≤ (ε * ‖x • h‖) * ‖h‖ := by
          exact mul_le_mul_of_nonneg_right hL2 (norm_nonneg h)
      _ ≤ (ε * ‖h‖) * ‖h‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxh hε.le) (norm_nonneg h)
      _ = ε * ‖h‖ ^ 2 := by ring
  have hmain : ‖φ 1 - φ 0‖ ≤ ε * ‖h‖ ^ 2 :=
    norm_image_sub_le_of_norm_deriv_le_segment_01' hφderiv hbound'
  have hgoal : φ 1 - φ 0 = f (z + h) - f z - (fderiv ℝ f z) h - (1 / 2) * (H2 h h) := by
    rw [hφ]
    norm_num
    ring
  rw [hgoal] at hmain
  rwa [Real.norm_eq_abs] at hmain

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

/-- Every finite-dimensional real subspace of a normed space is the range of a *continuous* linear
projection. -/
theorem exists_cLprojection_onto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (P : Submodule ℝ E) :
    ∃ π : E →L[ℝ] E, (∀ p ∈ P, π p = p) ∧ (∀ v : E, π v ∈ P) := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (p := P) (LinearMap.id : ↥P →ₗ[ℝ] ↥P)
  refine ⟨(Submodule.subtypeL P).comp (g.toContinuousLinearMap), ?_, ?_⟩
  · intro p hp
    have h1 : g (P.subtype ⟨p, hp⟩) = ⟨p, hp⟩ := LinearMap.congr_fun hg ⟨p, hp⟩
    have h2 : (g.toContinuousLinearMap : E →L[ℝ] ↥P) p = ⟨p, hp⟩ := h1
    simp [h2]
  · intro v
    exact (g.toContinuousLinearMap v).2

/-- **Local path connectedness of the sublevel set at a critical point whose Hessian is negative
definite on a two-plane.**  The connecting paths are found inside a prescribed ball around `z`. -/
theorem local_joinedIn_ball_of_negDefPlane
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {Λ : ℝ} {z : E} (hz : F z = Λ)
    (hcz : fderiv ℝ F z = 0)
    (hbad : ∃ v w : E, ∀ c d : ℝ, (c, d) ≠ 0 →
      (fderiv ℝ (fderiv ℝ F) z) (c • v + d • w) (c • v + d • w) < 0) :
    ∀ σ > 0, ∃ ρ > 0, ∀ x y : E, dist x z < ρ → dist y z < ρ → F x < Λ → F y < Λ →
      JoinedIn ({w : E | F w < Λ} ∩ Metric.ball z σ) x y := by
  classical
  intro σ hσ
  set Hz : E →L[ℝ] (E →L[ℝ] ℝ) := fderiv ℝ (fderiv ℝ F) z with hHz
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
  obtain ⟨ρ_tay, hρ_tay, htay⟩ := taylor2_bound_ns hF z (μ / 16) hμ16pos
  rw [← hHz] at htay
  obtain ⟨ρ_pert, hρ_pert, hpert⟩ :=
    exists_hessian_apply_close hF z (u₀ : E) (ω := μ / 16) hμ16pos
  -- a continuous linear projection onto the bad plane, and its operator-norm bound
  obtain ⟨π, hπid, hπmem⟩ := exists_cLprojection_onto (E := E) P
  set K : ℝ := max 1 (‖π‖ + 1) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKπ : ‖π‖ + 1 ≤ K := le_max_right _ _
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK1
  -- the ball constraint enters through `ρ₀ ≤ σ`
  set ρ₀ : ℝ := min (min ρ_tay ρ_pert) σ with hρ₀def
  have hρ₀pos : 0 < ρ₀ := by
    rw [hρ₀def]
    exact lt_min (lt_min hρ_tay hρ_pert) hσ
  have hρ₀_tay : ρ₀ ≤ ρ_tay := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρ₀_pert : ρ₀ ≤ ρ_pert := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρ₀_σ : ρ₀ ≤ σ := min_le_right _ _
  set R₀ : ℝ := ρ₀ / 2 with hR₀def
  have hR₀pos : 0 < R₀ := by rw [hR₀def]; linarith
  set ρ₁ : ℝ := min (ρ₀ / (16 * K)) (μ * R₀ / (64 * K * (A + 1))) with hρ₁def
  have hA1pos : 0 < A + 1 := by linarith
  have hρ₁pos : 0 < ρ₁ := by
    rw [hρ₁def]
    exact lt_min (div_pos hρ₀pos (by positivity))
      (div_pos (mul_pos hμpos hR₀pos) (by positivity))
  have hρ₁nonneg : 0 ≤ ρ₁ := hρ₁pos.le
  have hKρ₁_le : K * ρ₁ ≤ ρ₀ / 16 := by
    have h1 : K * ρ₁ ≤ K * (ρ₀ / (16 * K)) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hKpos.le
    have h2 : K * (ρ₀ / (16 * K)) = ρ₀ / 16 := by field_simp
    linarith [h1, h2]
  have hKρ₁_nonneg : 0 ≤ K * ρ₁ := mul_nonneg hKpos.le hρ₁nonneg
  have hKρ₁_le_R₀4 : K * ρ₁ ≤ R₀ / 4 := by
    have h2 : ρ₀ / 16 = R₀ / 8 := by rw [hR₀def]; ring
    linarith [hKρ₁_le, h2]
  have hR₀q : R₀ + K * ρ₁ ≤ ρ₀ := by
    rw [hR₀def] at *
    linarith [hKρ₁_le]
  have hAρq : A * (K * ρ₁) ≤ μ * R₀ / 64 := by
    have h1 : K * ρ₁ ≤ μ * R₀ / (64 * (A + 1)) := by
      have h2 : K * ρ₁ ≤ K * (μ * R₀ / (64 * K * (A + 1))) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hKpos.le
      have h3 : K * (μ * R₀ / (64 * K * (A + 1))) = μ * R₀ / (64 * (A + 1)) := by
        field_simp
      linarith [h2, h3]
    have h4 : A * (K * ρ₁) ≤ A * (μ * R₀ / (64 * (A + 1))) :=
      mul_le_mul_of_nonneg_left h1 hAnonneg
    have h5 : A * (μ * R₀ / (64 * (A + 1))) = (A / (A + 1)) * (μ * R₀ / 64) := by
      field_simp
    have h6 : A / (A + 1) ≤ 1 := (div_le_one hA1pos).2 (by linarith)
    have h7 : (A / (A + 1)) * (μ * R₀ / 64) ≤ 1 * (μ * R₀ / 64) :=
      mul_le_mul_of_nonneg_right h6 (by positivity)
    calc A * (K * ρ₁) ≤ A * (μ * R₀ / (64 * (A + 1))) := h4
      _ = (A / (A + 1)) * (μ * R₀ / 64) := h5
      _ ≤ 1 * (μ * R₀ / 64) := h7
      _ = μ * R₀ / 64 := one_mul _
  have hAρq' : A * R₀ * (K * ρ₁) ≤ μ * R₀ ^ 2 / 64 := by
    calc A * R₀ * (K * ρ₁) = (A * (K * ρ₁)) * R₀ := by ring
      _ ≤ (μ * R₀ / 64) * R₀ := mul_le_mul_of_nonneg_right hAρq hR₀pos.le
      _ = μ * R₀ ^ 2 / 64 := by ring
  -- ## Step 4: the sublevel cylinder
  have hmargin : ∀ p ∈ P, ∀ q : E, ‖p‖ = R₀ → ‖q‖ ≤ K * ρ₁ → F (z + p + q) < Λ := by
    intro p hp q hpR hqρ
    have hball2 : ‖p + q‖ ≤ R₀ + K * ρ₁ := by
      calc ‖p + q‖ ≤ ‖p‖ + ‖q‖ := norm_add_le _ _
        _ ≤ R₀ + K * ρ₁ := by linarith
    have ht := htay (p + q) (le_trans hball2 (le_trans hR₀q hρ₀_tay))
    rw [hz, hcz] at ht
    simp only [zero_apply, sub_zero] at ht
    have hup : F (z + (p + q)) ≤ Λ + (1 / 2) * (Hz (p + q) (p + q)) + (μ / 16) * ‖p + q‖ ^ 2 := by
      have h1 : F (z + (p + q)) - Λ - (1 / 2) * (Hz (p + q) (p + q)) ≤ (μ / 16) * ‖p + q‖ ^ 2 :=
        le_trans (le_abs_self _) ht
      linarith
    have hquad : Hz (p + q) (p + q) ≤ -μ * R₀ ^ 2 + 2 * A * R₀ * (K * ρ₁) + A * (K * ρ₁) ^ 2 := by
      have hexp : Hz (p + q) (p + q) = Hz p p + Hz p q + Hz q p + Hz q q := by
        simp only [map_add, add_apply]
        ring
      have h1 : Hz p p ≤ -μ * R₀ ^ 2 := by
        have := hneg p hp
        rw [hpR] at this
        simpa using this
      have h2 : Hz p q ≤ A * R₀ * (K * ρ₁) := by
        have ha : ‖Hz p q‖ ≤ (A * R₀) * (K * ρ₁) := by
          calc ‖Hz p q‖ ≤ ‖Hz p‖ * ‖q‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ (A * R₀) * (K * ρ₁) := by
                refine mul_le_mul ?_ hqρ (norm_nonneg q) ?_
                · calc ‖Hz p‖ ≤ ‖Hz‖ * ‖p‖ := ContinuousLinearMap.le_opNorm _ _
                    _ = A * R₀ := by rw [← hAdef, hpR]
                · positivity
        calc Hz p q ≤ ‖Hz p q‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
          _ ≤ A * R₀ * (K * ρ₁) := ha
      have h3 : Hz q p ≤ A * R₀ * (K * ρ₁) := by
        have ha : ‖Hz q p‖ ≤ (A * R₀) * (K * ρ₁) := by
          calc ‖Hz q p‖ ≤ ‖Hz q‖ * ‖p‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ (A * (K * ρ₁)) * R₀ := by
                refine mul_le_mul ?_ hpR.le (norm_nonneg p) ?_
                · calc ‖Hz q‖ ≤ ‖Hz‖ * ‖q‖ := ContinuousLinearMap.le_opNorm _ _
                    _ ≤ A * (K * ρ₁) := by
                        rw [← hAdef]
                        exact mul_le_mul_of_nonneg_left hqρ (norm_nonneg Hz)
                · positivity
            _ = (A * R₀) * (K * ρ₁) := by ring
        calc Hz q p ≤ ‖Hz q p‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
          _ ≤ A * R₀ * (K * ρ₁) := ha
      have h4 : Hz q q ≤ A * (K * ρ₁) ^ 2 := by
        have ha : ‖Hz q q‖ ≤ A * (K * ρ₁) ^ 2 := by
          calc ‖Hz q q‖ ≤ ‖Hz q‖ * ‖q‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ (A * (K * ρ₁)) * (K * ρ₁) := by
                refine mul_le_mul ?_ hqρ (norm_nonneg q) ?_
                · calc ‖Hz q‖ ≤ ‖Hz‖ * ‖q‖ := ContinuousLinearMap.le_opNorm _ _
                    _ ≤ A * (K * ρ₁) := by
                        rw [← hAdef]
                        exact mul_le_mul_of_nonneg_left hqρ (norm_nonneg Hz)
                · positivity
            _ = A * (K * ρ₁) ^ 2 := by ring
        calc Hz q q ≤ ‖Hz q q‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
          _ ≤ A * (K * ρ₁) ^ 2 := ha
      linarith
    have hρ2 : (R₀ + K * ρ₁) ^ 2 ≤ 25 * R₀ ^ 2 / 16 := by
      nlinarith [hKρ₁_le_R₀4, hR₀pos, hKρ₁_nonneg]
    have hε2 : (μ / 16) * ‖p + q‖ ^ 2 ≤ (μ / 16) * (25 * R₀ ^ 2 / 16) := by
      have h1 : ‖p + q‖ ^ 2 ≤ (R₀ + K * ρ₁) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hball2 2
      exact (mul_le_mul_of_nonneg_left (le_trans h1 hρ2) hμ16pos.le)
    have hkey : (1 / 2) * (-μ * R₀ ^ 2 + 2 * A * R₀ * (K * ρ₁) + A * (K * ρ₁) ^ 2)
        + (μ / 16) * (25 * R₀ ^ 2 / 16) < 0 := by
      have hpos : 0 < μ * R₀ ^ 2 := mul_pos hμpos (pow_pos hR₀pos 2)
      nlinarith [hAρq', hAρq, hKρ₁_le_R₀4, hKρ₁_nonneg, hAnonneg, hpos]
    have hmain : (1 / 2) * (Hz (p + q) (p + q)) + (μ / 16) * ‖p + q‖ ^ 2 < 0 := by
      linarith [hquad, hkey, hε2]
    have hfin : F (z + (p + q)) < Λ := by linarith
    simpa [add_assoc] using hfin
  set S : Set E := {w : E | F w < Λ} with hS
  -- ## Step 5: the local path
  have hlocal : ∀ x : E, dist x z < ρ₁ → F x < Λ →
      JoinedIn (S ∩ Metric.ball z σ) x (z + R₀ • (u₀ : E)) := by
    intro x hxdist hFx
    set p : E := π (x - z) with hpdef
    set q : E := x - z - π (x - z) with hqdef
    have hpP : p ∈ P := hπmem _
    have hxdecomp : x = z + (p + q) := by
      rw [hpdef, hqdef]
      abel
    have hdist' : ‖x - z‖ < ρ₁ := by rwa [dist_eq_norm] at hxdist
    have hpnorm : ‖p‖ ≤ K * ‖x - z‖ := by
      rw [hpdef]
      calc ‖π (x - z)‖ ≤ ‖π‖ * ‖x - z‖ := π.le_opNorm _
        _ ≤ K * ‖x - z‖ := by nlinarith [hKπ, norm_nonneg (x - z)]
    have hqnorm : ‖q‖ ≤ K * ‖x - z‖ := by
      rw [hqdef]
      calc ‖x - z - π (x - z)‖ ≤ ‖x - z‖ + ‖π (x - z)‖ := norm_sub_le _ _
        _ ≤ ‖x - z‖ + ‖π‖ * ‖x - z‖ := by nlinarith [π.le_opNorm (x - z)]
        _ = (1 + ‖π‖) * ‖x - z‖ := by ring
        _ ≤ K * ‖x - z‖ := by nlinarith [hKπ, norm_nonneg (x - z)]
    have hpn : ‖p‖ < K * ρ₁ := lt_of_le_of_lt hpnorm (by nlinarith [hdist', hKpos])
    have hqn : ‖q‖ < K * ρ₁ := lt_of_le_of_lt hqnorm (by nlinarith [hdist', hKpos])
    have hpnR : ‖p‖ ≤ R₀ := by linarith [hpn.le, hKρ₁_le_R₀4, hR₀pos.le]
    -- a direction in `P` with nonpositive derivative
    have he₀P : (u₀ : E) ∈ P := u₀.2
    obtain ⟨Δ, hΔP, hΔn, hΔderiv, hΔcases⟩ :
        ∃ Δ ∈ P, ‖Δ‖ = 1 ∧ fderiv ℝ F x Δ ≤ 0 ∧ (Δ = (u₀ : E) ∨ Δ = -(u₀ : E)) := by
      by_cases hpos : 0 < (fderiv ℝ F x) (u₀ : E)
      · refine ⟨-(u₀ : E), P.neg_mem he₀P, by simp [hu₀norm], ?_, Or.inr rfl⟩
        rw [map_neg, neg_nonpos]
        exact hpos.le
      · exact ⟨(u₀ : E), he₀P, hu₀norm, le_of_not_gt hpos, Or.inl rfl⟩
    have hΔbound : ∀ y : E, dist y z < ρ_pert →
        (fderiv ℝ (fderiv ℝ F) y) Δ Δ ≤ Hz Δ Δ + μ / 16 := by
      intro y hy
      have hyy := hpert y hy
      rcases hΔcases with hΔeq | hΔeq
      · rw [hΔeq]
        linarith [le_abs_self ((fderiv ℝ (fderiv ℝ F) y) (u₀ : E) (u₀ : E)
          - Hz (u₀ : E) (u₀ : E)), hyy]
      · have hsign : ∀ H : E →L[ℝ] (E →L[ℝ] ℝ),
            H (-(u₀ : E)) (-(u₀ : E)) = H (u₀ : E) (u₀ : E) := by
          intro H
          have h := clm_smul_smul_smul H (u₀ : E) (-1 : ℝ)
          simpa using h
        rw [hΔeq, hsign, hsign]
        linarith [le_abs_self ((fderiv ℝ (fderiv ℝ F) y) (u₀ : E) (u₀ : E)
          - Hz (u₀ : E) (u₀ : E)), hyy]
    -- the slide length
    have hIVT : ∃ t₁ ∈ Icc (0 : ℝ) (R₀ + K * ρ₁), ‖p + t₁ • Δ‖ = R₀ := by
      have hcont : ContinuousOn (fun t : ℝ => ‖p + t • Δ‖) (Icc 0 (R₀ + K * ρ₁)) := by fun_prop
      have hle1 : ‖p + (0 : ℝ) • Δ‖ ≤ R₀ := by
        simpa using hpnR
      have hle2 : R₀ ≤ ‖p + (R₀ + K * ρ₁) • Δ‖ := by
        have h1 : ‖(R₀ + K * ρ₁) • Δ‖ ≤ ‖p + (R₀ + K * ρ₁) • Δ‖ + ‖p‖ := by
          simpa [add_sub_cancel_left] using norm_sub_le (p + (R₀ + K * ρ₁) • Δ) p
        have h2 : ‖(R₀ + K * ρ₁) • Δ‖ = R₀ + K * ρ₁ := by
          rw [norm_smul, hΔn, mul_one, Real.norm_eq_abs,
            abs_of_pos (by linarith [hR₀pos, hKρ₁_nonneg])]
        linarith [h1, h2, hpn.le]
      exact (intermediate_value_Icc (by linarith [hKρ₁_nonneg]) hcont) ⟨hle1, hle2⟩
    obtain ⟨t₁, ht₁mem, ht₁eq⟩ := hIVT
    have ht₁nonneg : 0 ≤ t₁ := ht₁mem.1
    have ht₁le : t₁ ≤ R₀ + K * ρ₁ := ht₁mem.2
    have hp'P : p + t₁ • Δ ∈ P := P.add_mem hpP (P.smul_mem _ hΔP)
    -- the slide
    have hslide : JoinedIn (S ∩ Metric.ball z σ) x (z + (p + t₁ • Δ) + q) := by
      have h0 : fderiv ℝ F x (t₁ • Δ) ≤ 0 := by
        rw [map_smul, smul_eq_mul]
        exact mul_nonpos_of_nonneg_of_nonpos ht₁nonneg hΔderiv
      have h2 : ∀ u ∈ Icc (0 : ℝ) 1,
          (fderiv ℝ (fderiv ℝ F) (x + u • (t₁ • Δ))) (t₁ • Δ) (t₁ • Δ) ≤ 0 := by
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
            _ < (K * ρ₁ + (R₀ + K * ρ₁)) + K * ρ₁ := by
                rw [htu]
                have h1 : u * t₁ ≤ R₀ + K * ρ₁ := by nlinarith [hu.1, hu.2, ht₁nonneg, ht₁le]
                linarith [hpn, hqn]
            _ ≤ ρ₀ := by linarith [hKρ₁_le, hR₀def]
            _ ≤ ρ_pert := hρ₀_pert
        have hbound := hΔbound (x + u • (t₁ • Δ)) hdist
        have hHzΔ : Hz Δ Δ ≤ -μ := by
          have := hneg Δ hΔP
          rw [hΔn] at this
          simpa using this
        have hneg2 : (fderiv ℝ (fderiv ℝ F) (x + u • (t₁ • Δ))) Δ Δ ≤ 0 := by
          linarith [hbound, hHzΔ, hμpos]
        rw [clm_smul_smul_smul]
        exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t₁) hneg2
      have hle := slide_le_of_second_deriv_nonpos hF h0 h2
      refine JoinedIn.ofLine (f := fun t : ℝ => z + (p + (t * t₁) • Δ) + q) ?_ ?_ ?_ ?_
      · fun_prop
      · show z + (p + (0 * t₁) • Δ) + q = x
        rw [hxdecomp]
        simp only [zero_mul, zero_smul, add_zero, add_assoc]
      · show z + (p + (1 * t₁) • Δ) + q = z + (p + t₁ • Δ) + q
        simp
      · rintro y ⟨t, ht, rfl⟩
        constructor
        · show F (z + (p + (t * t₁) • Δ) + q) < Λ
          have hstep : z + (p + (t * t₁) • Δ) + q = x + t • (t₁ • Δ) := by
            rw [hxdecomp]
            simp only [smul_smul]
            abel
          rw [hstep]
          exact lt_of_le_of_lt (hle t ht) hFx
        · show z + (p + (t * t₁) • Δ) + q ∈ Metric.ball z σ
          rw [Metric.mem_ball, dist_eq_norm]
          have hstep : z + (p + (t * t₁) • Δ) + q - z = (p + (t * t₁) • Δ) + q := by abel
          rw [hstep]
          have ht1 : |t| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [ht.1], ht.2⟩
          have hnormt : ‖(t * t₁) • Δ‖ = |t * t₁| := by rw [norm_smul, hΔn, mul_one, Real.norm_eq_abs]
          have h1 : |t * t₁| ≤ R₀ + K * ρ₁ := by
            rw [abs_mul]
            calc |t| * |t₁| ≤ 1 * t₁ := by
                  refine mul_le_mul ht1 ?_ (abs_nonneg t₁) (by norm_num)
                  rw [abs_of_nonneg ht₁nonneg]
              _ = t₁ := one_mul _
              _ ≤ R₀ + K * ρ₁ := by linarith [hKρ₁_nonneg]
          calc ‖(p + (t * t₁) • Δ) + q‖ ≤ ‖p + (t * t₁) • Δ‖ + ‖q‖ := norm_add_le _ _
            _ ≤ (‖p‖ + ‖(t * t₁) • Δ‖) + ‖q‖ := by
                have := norm_add_le p ((t * t₁) • Δ)
                linarith
            _ < (K * ρ₁ + (R₀ + K * ρ₁)) + K * ρ₁ := by
                rw [hnormt]
                linarith [h1, hpn, hqn]
            _ < σ := by linarith [hKρ₁_le, hR₀def, hρ₀_σ]
    -- shrink the off-plane component to zero
    have hshrink : JoinedIn (S ∩ Metric.ball z σ)
        (z + (p + t₁ • Δ) + q) (z + (p + t₁ • Δ)) := by
      refine JoinedIn.ofLine (f := fun t : ℝ => z + (p + t₁ • Δ) + ((1 : ℝ) - t) • q) ?_ ?_ ?_ ?_
      · fun_prop
      · show z + (p + t₁ • Δ) + ((1 : ℝ) - 0) • q = z + (p + t₁ • Δ) + q
        simp
      · show z + (p + t₁ • Δ) + ((1 : ℝ) - 1) • q = z + (p + t₁ • Δ)
        simp
      · rintro y ⟨t, ht, rfl⟩
        have hq' : ‖((1 : ℝ) - t) • q‖ ≤ K * ρ₁ := by
          rw [norm_smul, Real.norm_eq_abs]
          calc |(1 : ℝ) - t| * ‖q‖ ≤ 1 * (K * ρ₁) := by
                refine mul_le_mul ?_ hqn.le (norm_nonneg q) (by norm_num)
                rw [abs_le]
                constructor <;> linarith [ht.1, ht.2]
            _ = K * ρ₁ := one_mul _
        refine ⟨hmargin (p + t₁ • Δ) hp'P (((1 : ℝ) - t) • q) ht₁eq hq', ?_⟩
        rw [Metric.mem_ball, dist_eq_norm]
        have hstep : z + (p + t₁ • Δ) + ((1 : ℝ) - t) • q - z
            = (p + t₁ • Δ) + ((1 : ℝ) - t) • q := by abel
        rw [hstep]
        calc ‖(p + t₁ • Δ) + ((1 : ℝ) - t) • q‖
            ≤ ‖p + t₁ • Δ‖ + ‖((1 : ℝ) - t) • q‖ := norm_add_le _ _
          _ ≤ R₀ + K * ρ₁ := by rw [ht₁eq]; linarith
          _ < σ := by linarith [hKρ₁_le, hR₀def, hρ₀_σ]
    -- rotate in `P` to the reference direction
    have hrot : JoinedIn (S ∩ Metric.ball z σ) (z + (p + t₁ • Δ)) (z + R₀ • (u₀ : E)) := by
      have hpc : IsPathConnected (Metric.sphere (0 : ↥P) R₀) :=
        isPathConnected_sphere (E := ↥P) hrank 0 hR₀pos.le
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
      refine ⟨?_, ?_⟩
      · rw [hS]
        simpa using hmargin (u : E) u.2 0 hunorm (by simpa using hKρ₁_nonneg)
      · rw [Metric.mem_ball, dist_eq_norm]
        have hstep : z + (u : E) - z = (u : E) := by abel
        rw [hstep, hunorm]
        linarith [hR₀def, hρ₀_σ]
    exact hslide.trans (hshrink.trans hrot)
  refine ⟨ρ₁, hρ₁pos, fun x y hx hy hFx hFy => ?_⟩
  exact (hlocal x hx hFx).trans (hlocal y hy hFy).symm

end Work.OddBound.mountainPass.port
