import Mathlib
import Submission.Work.ThomBordism.weighted_taylor_two

/-!
# The image of a small ball under a `C²` map with invertible derivative at `0` is convex

This file proves `Work.ThomBordism.exists_convex_image_ball`: for a finite-dimensional real
inner product space `E`, a finite family of maps `τ i : E → E` which are `C²` at `0`, fix `0` and
have injective derivative at `0`, there is a common `ε > 0` such that every `τ i '' ball 0 ε` is
convex.

The proof is a quantitative inverse function theorem argument.  Around `0` the map `τ i`
approximates the invertible linear map `A = D(τ i)(0)`; on a small ball it is a bi-Lipschitz
homeomorphism onto its image (the `ApproximatesLinearOn` machinery of Mathlib), and the
second-order Taylor estimate `weighted_taylor_two` says that
`a • f x + b • f y` differs from `f (a • x + b • y)` by at most `M a b ‖x - y‖²`.  Combining the
two, for `a, b ≥ 0`, `a + b = 1` the point `a • f x + b • f y` is `f z` for some `z` with
`‖z‖ < ε` as soon as `x, y ∈ ball 0 ε` and `ε` is small enough, because on the ball
`‖a • x + b • y‖² ≤ ε² - a b ‖x - y‖²` while the inverse map distorts distances only by a fixed
factor.  This is where the inner product structure is used.
-/

namespace Work.ThomBordism

open Set Metric Filter

open scoped NNReal

set_option maxHeartbeats 4000000

/-- From `ContDiffAt ℝ 2 f 0` we extract a radius `ρ` around `0` and a bound `M` for the second
derivative on that ball: on `closedBall 0 ρ` both `f` and `fderiv ℝ f` are differentiable, with
`fderiv ℝ (fderiv ℝ f)` bounded by `M`. -/
lemma contDiffAt_two_local_data
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → E)
    (h : ContDiffAt ℝ 2 f 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ M : ℝ, ∀ w : E, ‖w‖ ≤ ρ →
      HasFDerivAt f (fderiv ℝ f w) w ∧
      HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) w) w ∧
      ‖fderiv ℝ (fderiv ℝ f) w‖ ≤ M := by
  obtain ⟨u, hu_nhds, hu⟩ := h.contDiffOn (m := 2) le_rfl (fun hc => by norm_num at hc)
  obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp hu_nhds
  have hOn : ContDiffOn ℝ 2 f (ball 0 r) := hu.mono hrsub
  have hder1 : ContDiffOn ℝ 1 (fderiv ℝ f) (ball 0 r) :=
    hOn.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hcont : ContinuousOn (fderiv ℝ (fderiv ℝ f)) (ball 0 r) :=
    hder1.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  have hdiffOn : DifferentiableOn ℝ f (ball 0 r) := hOn.differentiableOn (by norm_num)
  have hdiffOn2 : DifferentiableOn ℝ (fderiv ℝ f) (ball 0 r) :=
    hder1.differentiableOn (by norm_num)
  have h0ball : (0 : E) ∈ ball 0 r := mem_ball_self hrpos
  have htend : Tendsto (fun w : E => ‖fderiv ℝ (fderiv ℝ f) w‖) (nhds 0)
      (nhds ‖fderiv ℝ (fderiv ℝ f) 0‖) :=
    (hcont.continuousAt (isOpen_ball.mem_nhds h0ball)).norm
  have hev : ∀ᶠ w in nhds (0 : E),
      ‖fderiv ℝ (fderiv ℝ f) w‖ < ‖fderiv ℝ (fderiv ℝ f) 0‖ + 1 :=
    htend.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨r₂, hr₂pos, hr₂sub⟩ := Metric.mem_nhds_iff.mp hev
  have hminpos : (0 : ℝ) < min r (r₂ / 2) := lt_min hrpos (by linarith)
  refine ⟨min r (r₂ / 2) / 2, by linarith, ‖fderiv ℝ (fderiv ℝ f) 0‖ + 1, fun w hw => ?_⟩
  have hwlt : ‖w‖ < min r (r₂ / 2) := by linarith
  have hwr : w ∈ ball 0 r := by
    rw [mem_ball_zero_iff]
    exact lt_of_lt_of_le hwlt (min_le_left _ _)
  have hw2 : ‖w‖ < r₂ :=
    lt_of_lt_of_le hwlt (le_trans (min_le_right _ _) (by linarith))
  exact ⟨(hdiffOn.differentiableAt (isOpen_ball.mem_nhds hwr)).hasFDerivAt,
    (hdiffOn2.differentiableAt (isOpen_ball.mem_nhds hwr)).hasFDerivAt,
    le_of_lt (hr₂sub (mem_ball_zero_iff.mpr hw2))⟩

theorem convex_image_ball_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → E) (hτ : ContDiffAt ℝ 2 f 0) (h0 : f 0 = 0)
    (hinv : Function.Injective (fderiv ℝ f 0)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → Convex ℝ (f '' Metric.ball 0 ε) := by
  by_cases hsub : Subsingleton E
  · refine ⟨1, one_pos, fun ε hεpos _ => ?_⟩
    have himg : f '' Metric.ball 0 ε = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro y
      exact ⟨0, mem_ball_self hεpos, by rw [h0]; exact hsub.allEq 0 y⟩
    rw [himg]; exact convex_univ
  · have hsurj : Function.Surjective (fderiv ℝ f 0 : E → E) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ) (V := E) (V₂ := E)
        rfl).mp hinv
    set Ae : E ≃L[ℝ] E :=
      (LinearEquiv.ofBijective (fderiv ℝ f 0).toLinearMap ⟨hinv, hsurj⟩).toContinuousLinearEquiv
      with hAe
    have hAe_coe : (Ae : E →L[ℝ] E) = fderiv ℝ f 0 := by rw [hAe]; ext v; rfl
    have hstrict : HasStrictFDerivAt f (Ae : E →L[ℝ] E) 0 := by
      rw [hAe_coe]
      exact hτ.hasStrictFDerivAt (by norm_num)
    obtain ⟨s, h0s, hsopen, happ⟩ := hstrict.approximates_deriv_on_open_nhds
    set N : ℝ := ‖(Ae.symm : E →L[ℝ] E)‖ with hNdef
    have hNnnpos : 0 < ‖(Ae.symm : E →L[ℝ] E)‖₊ := by
      rcases ContinuousLinearEquiv.subsingleton_or_nnnorm_symm_pos Ae with h | h
      · exact absurd h hsub
      · exact h
    have hNpos : 0 < N := by
      have h : (0 : ℝ) < (‖(Ae.symm : E →L[ℝ] E)‖₊ : ℝ) := hNnnpos
      rw [coe_nnnorm, ← hNdef] at h
      exact h
    have hc₀ : (‖(Ae.symm : E →L[ℝ] E)‖₊⁻¹ / 2) < ‖(Ae.symm : E →L[ℝ] E)‖₊⁻¹ :=
      NNReal.half_lt_self (ne_of_gt (inv_pos.mpr hNnnpos))
    have hc : Subsingleton E ∨
        (‖(Ae.symm : E →L[ℝ] E)‖₊⁻¹ / 2) < ‖(Ae.symm : E →L[ℝ] E)‖₊⁻¹ := Or.inr hc₀
    set cR : ℝ := ((‖(Ae.symm : E →L[ℝ] E)‖₊⁻¹ / 2 : ℝ≥0) : ℝ) with hcRdef
    have hcRval : cR = N⁻¹ / 2 := by
      rw [hcRdef, NNReal.coe_div, NNReal.coe_inv, coe_nnnorm, ← hNdef]
      norm_num
    have hcRpos : 0 < cR := by rw [hcRval]; exact div_pos (inv_pos.mpr hNpos) two_pos
    have hKpos : 0 < N⁻¹ - cR := by rw [hcRval]; linarith [inv_pos.mpr hNpos]
    have hKval : N⁻¹ - cR = N⁻¹ / 2 := by rw [hcRval]; ring
    set L : ℝ := ‖(Ae : E →L[ℝ] E)‖ with hLdef
    have hLpos : 0 < L + cR := by rw [hLdef]; linarith [norm_nonneg (Ae : E →L[ℝ] E), hcRpos]
    have happR : ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y - Ae (x - y)‖ ≤ cR * ‖x - y‖ := by
      intro x hx y hy
      simpa [hcRdef] using happ x hx y hy
    obtain ⟨s₁, hs₁pos, hs₁sub⟩ := Metric.mem_nhds_iff.mp (hsopen.mem_nhds h0s)
    have hs₁closed : Metric.closedBall 0 (s₁ / 2) ⊆ s := by
      intro x hx
      refine hs₁sub ?_
      rw [mem_closedBall_zero_iff] at hx
      rw [mem_ball_zero_iff]
      linarith
    set δ : ℝ := (N⁻¹ - cR) * (s₁ / 2) with hδdef
    have hδsub : Metric.closedBall 0 δ ⊆ f '' s := by
      have hh := ApproximatesLinearOn.closedBall_subset_target (f := f) (f' := Ae)
        (c := ‖(Ae.symm : E →L[ℝ] E)‖₊⁻¹ / 2) (s := s) happ hc hsopen
        (ε := s₁ / 2) (b := 0) (by linarith) hs₁closed
      have hcoe : (↑(‖(Ae.symm : E →L[ℝ] E)‖₊⁻¹) : ℝ) = N⁻¹ := by
        rw [NNReal.coe_inv, coe_nnnorm, ← hNdef]
      have hcRval2 : (↑(‖(Ae.symm : E →L[ℝ] E)‖₊⁻¹ / 2 : ℝ≥0) : ℝ) = N⁻¹ / 2 := by
        rw [NNReal.coe_div, NNReal.coe_inv, coe_nnnorm, ← hNdef]
        norm_num
      have hconst : (↑(‖(Ae.symm : E →L[ℝ] E)‖₊⁻¹) : ℝ)
          - (↑(‖(Ae.symm : E →L[ℝ] E)‖₊⁻¹ / 2 : ℝ≥0) : ℝ) = N⁻¹ - cR := by
        rw [hcoe, hcRval2, hcRval]
      rw [hconst, h0, ApproximatesLinearOn.toOpenPartialHomeomorph_target] at hh
      rw [hδdef]
      exact hh
    have hδpos : 0 < δ := by rw [hδdef]; exact mul_pos hKpos (by linarith)
    obtain ⟨ρT, hρTpos, M, hM⟩ := contDiffAt_two_local_data f hτ
    have hMnn : 0 ≤ M := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ f) 0))
      ((hM 0 (by simpa using hρTpos.le)).2.2)
    set M' : ℝ := M + 1 with hM'def
    have hM'pos : 0 < M' := by rw [hM'def]; linarith
    have hMtay1 : ∀ w, ‖w‖ ≤ ρT → HasFDerivAt f (fderiv ℝ f w) w := fun w hw => (hM w hw).1
    have hMtay2 : ∀ w, ‖w‖ ≤ ρT →
        HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) w) w := fun w hw => (hM w hw).2.1
    have hMtay3 : ∀ w, ‖w‖ ≤ ρT → ‖fderiv ℝ (fderiv ℝ f) w‖ ≤ M' := by
      intro w hw
      have := (hM w hw).2.2
      rw [hM'def]; linarith
    have hfbound : ∀ x ∈ s, ‖f x‖ ≤ (L + cR) * ‖x‖ := by
      intro x hx
      have h1 : ‖f x - Ae x‖ ≤ cR * ‖x‖ := by
        have h2 := happR x hx 0 h0s
        simpa [h0] using h2
      calc ‖f x‖ = ‖(f x - Ae x) + Ae x‖ := by congr 1; abel
        _ ≤ ‖f x - Ae x‖ + ‖Ae x‖ := norm_add_le _ _
        _ ≤ cR * ‖x‖ + L * ‖x‖ := by
              rw [hLdef]
              exact add_le_add h1 (by simpa using (Ae : E →L[ℝ] E).le_opNorm x)
        _ = (L + cR) * ‖x‖ := by ring
    have hanti : ∀ x ∈ s, ∀ y ∈ s, ‖x - y‖ ≤ (N⁻¹ - cR)⁻¹ * ‖f x - f y‖ := by
      intro x hx y hy
      have hle : ‖x - y‖ / N ≤ ‖Ae (x - y)‖ := by
        have h2 := (Ae.symm : E →L[ℝ] E).le_opNorm (Ae (x - y))
        have h3 : (Ae.symm : E →L[ℝ] E) (Ae (x - y)) = x - y := by simp
        rw [h3, ← hNdef] at h2
        rw [div_le_iff₀ hNpos]
        simpa [mul_comm] using h2
      have hkey : (N⁻¹ - cR) * ‖x - y‖ ≤ ‖f x - f y‖ := by
        have h4 := happR x hx y hy
        have h6 := norm_sub_le (f x - f y) (f x - f y - Ae (x - y))
        have h7 : (f x - f y) - (f x - f y - Ae (x - y)) = Ae (x - y) := by abel
        rw [h7] at h6
        have h8 : (N⁻¹ - cR) * ‖x - y‖ = ‖x - y‖ / N - cR * ‖x - y‖ := by
          rw [div_eq_inv_mul]; ring
        rw [h8]
        linarith
      rw [le_inv_mul_iff₀ hKpos]
      exact hkey
    set E₀ : ℝ := min (min ρT (s₁ / 2)) (min (δ / (L + cR)) (1 / (8 * N * M'))) with hE0def
    have hE0pos : 0 < E₀ := by
      rw [hE0def]
      refine lt_min (lt_min hρTpos (by linarith))
        (lt_min (div_pos hδpos hLpos) (div_pos one_pos (by positivity)))
    refine ⟨E₀, hE0pos, fun ε hεpos hεle => ?_⟩
    have hε_s₁ : ε ≤ s₁ / 2 :=
      le_trans hεle (by rw [hE0def]; exact le_trans (min_le_left _ _) (min_le_right _ _))
    have hε_ρT : ε ≤ ρT :=
      le_trans hεle (by rw [hE0def]; exact le_trans (min_le_left _ _) (min_le_left _ _))
    have hε_δ : (L + cR) * ε ≤ δ := by
      have h1 : ε ≤ δ / (L + cR) :=
        le_trans hεle (by rw [hE0def]; exact le_trans (min_le_right _ _) (min_le_left _ _))
      have h2 := (le_div_iff₀ hLpos).mp h1
      simpa [mul_comm] using h2
    have hε_M : 2 * ε * M' < N⁻¹ - cR := by
      have h1 : ε ≤ 1 / (8 * N * M') :=
        le_trans hεle (by rw [hE0def]; exact le_trans (min_le_right _ _) (min_le_right _ _))
      have h8 : (0 : ℝ) < 8 * N * M' := by positivity
      have h2 : ε * (8 * N * M') ≤ 1 := (le_div_iff₀ h8).mp h1
      have h5 : N⁻¹ / 2 = 1 / (2 * N) := by rw [inv_eq_one_div]; ring
      rw [hKval, h5, lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * N)]
      nlinarith [h2]
    rw [convex_iff_add_mem]
    intro x hx y hy a b ha hb hab
    rw [Set.mem_image] at hx hy ⊢
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    rw [mem_ball_zero_iff] at hx' hy'
    have hx's : x' ∈ s := hs₁closed (by rw [mem_closedBall_zero_iff]; linarith [lt_of_lt_of_le hx' hε_s₁])
    have hy's : y' ∈ s := hs₁closed (by rw [mem_closedBall_zero_iff]; linarith [lt_of_lt_of_le hy' hε_s₁])
    set m : E := a • x' + b • y' with hmdef
    set p : E := a • f x' + b • f y' with hpdef
    have hmnorm : ‖m‖ ≤ a * ‖x'‖ + b * ‖y'‖ := by
      rw [hmdef]
      calc ‖a • x' + b • y'‖ ≤ ‖a • x'‖ + ‖b • y'‖ := norm_add_le _ _
        _ = a * ‖x'‖ + b * ‖y'‖ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    have hms : m ∈ s := hs₁closed (by
      rw [mem_closedBall_zero_iff]
      calc ‖m‖ ≤ a * ‖x'‖ + b * ‖y'‖ := hmnorm
        _ ≤ s₁ / 2 := by
              have h1 : a * ‖x'‖ ≤ a * (s₁ / 2) :=
                mul_le_mul_of_nonneg_left (le_of_lt (lt_of_lt_of_le hx' hε_s₁)) ha
              have h2 : b * ‖y'‖ ≤ b * (s₁ / 2) :=
                mul_le_mul_of_nonneg_left (le_of_lt (lt_of_lt_of_le hy' hε_s₁)) hb
              have h3 : a * (s₁ / 2) + b * (s₁ / 2) = s₁ / 2 := by
                rw [← add_mul, hab, one_mul]
              linarith)
    have hm_lt : ‖m‖ < ε := by
      by_cases hz0 : a * b * ‖x' - y'‖ ^ 2 = 0
      · rcases mul_eq_zero.mp hz0 with h | h
        · rcases mul_eq_zero.mp h with ha0 | hb0
          · have hm' : m = y' := by
              rw [hmdef, ha0, zero_smul, zero_add, show b = 1 by linarith, one_smul]
            rw [hm']; exact hy'
          · have hm' : m = x' := by
              rw [hmdef, hb0, zero_smul, add_zero, show a = 1 by linarith, one_smul]
            rw [hm']; exact hx'
        · have hxy : x' = y' := by
            have h3 : ‖x' - y'‖ = 0 := by nlinarith [norm_nonneg (x' - y')]
            exact sub_eq_zero.mp (norm_eq_zero.mp h3)
          have hm' : m = x' := by rw [hmdef, hxy, ← add_smul, hab, one_smul]
          rw [hm']; exact hx'
      · have hlt : a * ‖x'‖ + b * ‖y'‖ < ε := by
          have habε : a * ε + b * ε = ε := by rw [← add_mul, hab, one_mul]
          rcases eq_or_lt_of_le ha with ha0 | hapos
          · have hb1 : b = 1 := by linarith
            rw [← ha0, zero_mul, zero_add, hb1, one_mul]
            exact hy'
          · have h1 : a * ‖x'‖ < a * ε := mul_lt_mul_of_pos_left hx' hapos
            have h2 : b * ‖y'‖ ≤ b * ε := mul_le_mul_of_nonneg_left (le_of_lt hy') hb
            linarith
        exact lt_of_le_of_lt hmnorm hlt
    have hpδ : p ∈ Metric.closedBall 0 δ := by
      rw [mem_closedBall_zero_iff, hpdef]
      calc ‖a • f x' + b • f y'‖ ≤ ‖a • f x'‖ + ‖b • f y'‖ := norm_add_le _ _
        _ = a * ‖f x'‖ + b * ‖f y'‖ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
        _ ≤ a * ((L + cR) * ‖x'‖) + b * ((L + cR) * ‖y'‖) :=
              add_le_add (mul_le_mul_of_nonneg_left (hfbound x' hx's) ha)
                (mul_le_mul_of_nonneg_left (hfbound y' hy's) hb)
        _ ≤ (L + cR) * ε := by
              have h1 : a * ((L + cR) * ‖x'‖) ≤ a * ((L + cR) * ε) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left (le_of_lt hx') (le_of_lt hLpos)) ha
              have h2 : b * ((L + cR) * ‖y'‖) ≤ b * ((L + cR) * ε) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left (le_of_lt hy') (le_of_lt hLpos)) hb
              have h3 : a * ((L + cR) * ε) + b * ((L + cR) * ε) = (L + cR) * ε := by
                rw [← add_mul, hab, one_mul]
              linarith
        _ ≤ δ := hε_δ
    obtain ⟨z, hzs, hfz⟩ := hδsub hpδ
    have hzm : ‖z - m‖ ≤ (N⁻¹ - cR)⁻¹ * ‖p - f m‖ := by
      have h := hanti z hzs m hms
      rwa [hfz] at h
    have hpt : ‖p - f m‖ ≤ M' * (a * b) * ‖x' - y'‖ ^ 2 := by
      have h := weighted_taylor_two hMtay1 hMtay2 hMtay3 (x := x') (y := y')
        (le_of_lt (lt_of_lt_of_le hx' hε_ρT)) (le_of_lt (lt_of_lt_of_le hy' hε_ρT)) ha hb hab
      simpa [hpdef, hmdef] using h
    refine ⟨z, ?_, ?_⟩
    · rw [mem_ball_zero_iff]
      have hz0imp : a * b * ‖x' - y'‖ ^ 2 = 0 → ‖z‖ = ‖m‖ := by
        intro hz0
        have hpm : p = f m := by
          have h := hpt
          rw [show M' * (a * b) * ‖x' - y'‖ ^ 2 = M' * (a * b * ‖x' - y'‖ ^ 2) by ring] at h
          rw [hz0, mul_zero] at h
          exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
        have hzm0 : ‖z - m‖ = 0 := by
          have h := hzm
          rw [hpm, sub_self, norm_zero, mul_zero] at h
          exact le_antisymm h (norm_nonneg _)
        have hzeq : z = m := sub_eq_zero.mp (norm_eq_zero.mp hzm0)
        rw [hzeq]
      by_cases hz0 : a * b * ‖x' - y'‖ ^ 2 = 0
      · rw [hz0imp hz0]
        exact hm_lt
      · have hs_pos : 0 < a * b * ‖x' - y'‖ ^ 2 :=
          lt_of_le_of_ne (by positivity) (Ne.symm hz0)
        have hpar : ‖m‖ ^ 2 ≤ ε ^ 2 - a * b * ‖x' - y'‖ ^ 2 := by
          have hexp : ‖m‖ ^ 2 = a * ‖x'‖ ^ 2 + b * ‖y'‖ ^ 2 - a * b * ‖x' - y'‖ ^ 2 := by
            rw [hmdef, norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul,
              Real.norm_of_nonneg ha, Real.norm_of_nonneg hb,
              real_inner_smul_left, real_inner_smul_right]
            linear_combination (a * ‖x'‖ ^ 2 + b * ‖y'‖ ^ 2) * hab
          rw [hexp]
          have h3 : a * ‖x'‖ ^ 2 ≤ a * ε ^ 2 :=
            mul_le_mul_of_nonneg_left (by nlinarith [hx', norm_nonneg x', hεpos]) ha
          have h4 : b * ‖y'‖ ^ 2 ≤ b * ε ^ 2 :=
            mul_le_mul_of_nonneg_left (by nlinarith [hy', norm_nonneg y', hεpos]) hb
          nlinarith [h3, h4, hab]
        have hmlt : ‖m‖ < ε := by
          have h1 : ‖m‖ ^ 2 < ε ^ 2 := by linarith [hpar, hs_pos]
          have h2 := sq_lt_sq.mp h1
          rwa [abs_of_nonneg (norm_nonneg m), abs_of_nonneg (le_of_lt hεpos)] at h2
        have hmle : ‖m‖ ≤ ε - (a * b * ‖x' - y'‖ ^ 2) / (2 * ε) := by
          have h1 : a * b * ‖x' - y'‖ ^ 2 ≤ (ε - ‖m‖) * (ε + ‖m‖) := by nlinarith [hpar]
          have h2 : ε + ‖m‖ ≤ 2 * ε := by linarith
          have h3 : 0 ≤ ε - ‖m‖ := by linarith
          have h4 : a * b * ‖x' - y'‖ ^ 2 ≤ (ε - ‖m‖) * (2 * ε) :=
            le_trans h1 (mul_le_mul_of_nonneg_left h2 h3)
          have h5 : (a * b * ‖x' - y'‖ ^ 2) / (2 * ε) ≤ ε - ‖m‖ := by
            rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * ε)]
            exact h4
          linarith
        have hKinv : (N⁻¹ - cR)⁻¹ * M' < 1 / (2 * ε) := by
          have h2e : (0 : ℝ) < 2 * ε := by linarith
          have h1 : (N⁻¹ - cR)⁻¹ * M' = M' / (N⁻¹ - cR) := by rw [div_eq_inv_mul]
          rw [h1, div_lt_div_iff₀ hKpos h2e]
          linarith [hε_M]
        have hfinal : (N⁻¹ - cR)⁻¹ * (M' * (a * b * ‖x' - y'‖ ^ 2))
            < (a * b * ‖x' - y'‖ ^ 2) / (2 * ε) := by
          have h := mul_lt_mul_of_pos_left hKinv hs_pos
          calc (N⁻¹ - cR)⁻¹ * (M' * (a * b * ‖x' - y'‖ ^ 2))
              = (a * b * ‖x' - y'‖ ^ 2) * ((N⁻¹ - cR)⁻¹ * M') := by ring
            _ < (a * b * ‖x' - y'‖ ^ 2) * (1 / (2 * ε)) := h
            _ = (a * b * ‖x' - y'‖ ^ 2) / (2 * ε) := by rw [mul_one_div]
        have hbound : ‖z - m‖ ≤ (N⁻¹ - cR)⁻¹ * (M' * (a * b * ‖x' - y'‖ ^ 2)) := by
          calc ‖z - m‖ ≤ (N⁻¹ - cR)⁻¹ * ‖p - f m‖ := hzm
            _ ≤ (N⁻¹ - cR)⁻¹ * (M' * (a * b * ‖x' - y'‖ ^ 2)) := by
                  have hinner : ‖p - f m‖ ≤ M' * (a * b * ‖x' - y'‖ ^ 2) := by
                    calc ‖p - f m‖ ≤ M' * (a * b) * ‖x' - y'‖ ^ 2 := hpt
                      _ = M' * (a * b * ‖x' - y'‖ ^ 2) := by ring
                  exact mul_le_mul_of_nonneg_left hinner (inv_nonneg.mpr hKpos.le)
        have htri : ‖z‖ ≤ ‖m‖ + ‖z - m‖ := by
          have h := norm_add_le m (z - m)
          rwa [show m + (z - m) = z by abel] at h
        linarith
    · rw [hfz, hpdef]

theorem exists_convex_image_ball
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (τ : ι → E → E)
    (hτ : ∀ i, ContDiffAt ℝ 2 (τ i) 0)
    (h0 : ∀ i, τ i 0 = 0)
    (hinv : ∀ i, Function.Injective (fderiv ℝ (τ i) 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, Convex ℝ (τ i '' Metric.ball 0 ε) := by
  by_cases hne : Nonempty ι
  · have hnonemp : (Finset.univ : Finset ι).Nonempty :=
      hne.elim (fun i => ⟨i, Finset.mem_univ i⟩)
    choose e hepos heconv using
      fun i => convex_image_ball_of_contDiffAt (τ i) (hτ i) (h0 i) (hinv i)
    set ε₀ : ℝ := Finset.univ.inf' hnonemp e with hεdef
    have hεpos : 0 < ε₀ := by
      rw [hεdef]
      exact (Finset.lt_inf'_iff hnonemp).mpr (fun i _ => hepos i)
    refine ⟨ε₀, hεpos, fun i => ?_⟩
    exact heconv i ε₀ hεpos (by rw [hεdef]; exact Finset.inf'_le e (Finset.mem_univ i))
  · exact ⟨1, one_pos, fun i => absurd ⟨i⟩ hne⟩

end Work.ThomBordism
