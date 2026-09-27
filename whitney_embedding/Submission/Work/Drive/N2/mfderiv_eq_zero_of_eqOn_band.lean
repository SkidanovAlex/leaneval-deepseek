import Mathlib

/-!
# Vanishing derivative at a regular point of a band

Let `M` be a smooth `n`-manifold, `f R : M → ℝ` smooth, `a < b` and `x : M` with
`f x ∈ [a,b]` a *regular* point of `f` (`mfderiv f x ≠ 0`).  If `R` vanishes on the whole
"band" `f ⁻¹' [a,b]`, then `mfderiv R x = 0`.

This is the elementary regularity statement behind cutting off along a regular level of a
function: on the band the function `R` is constant `0`, and since `x` is a regular point the band
is a genuine (locally closed) half-space/slab near `x`, so no first-order information of `R`
survives at `x`.

The proof has three layers.

* `deriv_eq_zero_of_eqOn_Icc`: a one-dimensional lemma.  If `φ : ℝ → ℝ` is differentiable at `0`
  and equals `φ 0` on `[α,β] ∋ 0` with `α < β`, then `deriv φ 0 = 0`.  (The interval may have `0`
  as an endpoint; differentiability at `0` upgrades "the one-sided difference quotients tend to
  `0`" to "the derivative is `0`".)

* `fderiv_eq_zero_of_eventually_eqOn_band`: the Euclidean core.  For `F G : E → ℝ` on a real
  normed space with `F x ∈ [a,b]`, `fderiv F x ≠ 0` and `G = 0` on the band near `x`, one has
  `fderiv G x = 0`.  The argument is by lines: for every direction `u` with `(fderiv F x) u ≠ 0`
  the straight line `t ↦ x + t • u` meets the band on one side of `0`, so `G` vanishes on a
  one-sided interval and hence `(fderiv G x) u = 0`; since the zero set of a nonzero continuous
  linear functional is nowhere dense, `fderiv G x` vanishes on a spanning set of directions.

* `mfderiv_eq_zero_of_eqOn_band`: the manifold statement, obtained by writing `f` and `R` in the
  chart at `x` (`mfderiv_chartRep_eq`) and applying the Euclidean core.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Filter Set

/-! ## One-dimensional one-sided lemma -/

/-- If `φ : ℝ → ℝ` is differentiable at `0` and agrees with its value at `0` on an interval
`[α,β]` containing `0` (with `α < β`), then `deriv φ 0 = 0`.  Only the one-sided information at
the endpoint `0` is used. -/
lemma deriv_eq_zero_of_eqOn_Icc {φ : ℝ → ℝ} {α β : ℝ} (hαβ : α < β)
    (h0 : (0 : ℝ) ∈ Set.Icc α β) (h : ∀ s ∈ Set.Icc α β, φ s = φ 0)
    (hφ : DifferentiableAt ℝ φ 0) : deriv φ 0 = 0 := by
  have hS : UniqueDiffWithinAt ℝ (Set.Icc α β) 0 := (uniqueDiffOn_Icc hαβ) 0 h0
  rw [← hφ.derivWithin hS]
  rw [← derivWithin_congr (f₁ := Function.const ℝ (φ 0)) (fun s hs => (h s hs).symm) rfl]
  simp [derivWithin_const]

/-! ## The band mechanism along a line -/

/-- Right-sided version: if `ξ` is differentiable at `0` with positive derivative and
`a ≤ ξ 0 < b`, then `ξ` takes its values in `[a,b]` for `t` just to the right of `0`. -/
lemma eventually_Icc_nhdsGT {ξ : ℝ → ℝ} {a b c : ℝ} (hξ : HasDerivAt ξ c 0)
    (hc : 0 < c) (ha : a ≤ ξ 0) (hb : ξ 0 < b) :
    ∀ᶠ t in 𝓝[>] 0, ξ t ∈ Set.Icc a b := by
  have hsl : Tendsto (fun t : ℝ => t⁻¹ * (ξ t - ξ 0)) (𝓝[>] 0) (𝓝 c) := by
    simpa [zero_add, smul_eq_mul] using hξ.tendsto_slope_zero_right
  have hlow : ∀ᶠ t in 𝓝[>] 0, a ≤ ξ t := by
    have h1 : ∀ᶠ t in 𝓝[>] 0, 0 < t⁻¹ * (ξ t - ξ 0) :=
      hsl.eventually (isOpen_Ioi.mem_nhds hc)
    filter_upwards [h1, self_mem_nhdsWithin] with t h1 ht
    have htinv : 0 < t⁻¹ := inv_pos.mpr ht
    have hX : 0 < ξ t - ξ 0 := (mul_pos_iff_of_pos_left htinv).mp h1
    linarith
  have hupp : ∀ᶠ t in 𝓝[>] 0, ξ t ≤ b := by
    have h2 : ∀ᶠ t in 𝓝[>] 0, t⁻¹ * (ξ t - ξ 0) < 2 * c :=
      hsl.eventually (eventually_lt_nhds (by linarith))
    have hK : (0:ℝ) < (b - ξ 0) / (2 * c) := by
      have h1 : (0:ℝ) < b - ξ 0 := by linarith
      have h2 : (0:ℝ) < 2 * c := by linarith
      exact div_pos h1 h2
    have h3 : ∀ᶠ t in 𝓝[>] 0, t < (b - ξ 0) / (2 * c) :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hK)
    filter_upwards [h2, h3, self_mem_nhdsWithin] with t h2 h3 ht
    have hne : t ≠ 0 := ne_of_gt ht
    have hX1 : ξ t - ξ 0 < 2 * c * t := by
      have h := mul_lt_mul_of_pos_left h2 ht
      rwa [mul_inv_cancel_left₀ hne, mul_comm] at h
    have hX2 : 2 * c * t < b - ξ 0 := by
      have h : t * (2 * c) < b - ξ 0 := by
        have h := mul_lt_mul_of_pos_right h3 (by linarith : (0:ℝ) < 2 * c)
        rwa [div_mul_cancel₀ _ (by linarith : (2:ℝ) * c ≠ 0)] at h
      rw [mul_comm (2 * c) t]
      exact h
    linarith
  filter_upwards [hlow, hupp] with t h1 h2
  exact ⟨h1, h2⟩

/-- Left-sided version: if `ξ` is differentiable at `0` with positive derivative and
`a < ξ 0 ≤ b`, then `ξ` takes its values in `[a,b]` for `t` just to the left of `0`. -/
lemma eventually_Icc_nhdsLT {ξ : ℝ → ℝ} {a b c : ℝ} (hξ : HasDerivAt ξ c 0)
    (hc : 0 < c) (ha : a < ξ 0) (hb : ξ 0 ≤ b) :
    ∀ᶠ t in 𝓝[<] 0, ξ t ∈ Set.Icc a b := by
  have hsl : Tendsto (fun t : ℝ => t⁻¹ * (ξ t - ξ 0)) (𝓝[<] 0) (𝓝 c) := by
    simpa [zero_add, smul_eq_mul] using hξ.tendsto_slope_zero_left
  have hnear : ∀ᶠ t in 𝓝[<] 0, a < ξ t :=
    ((hξ.continuousAt.eventually (isOpen_Ioi.mem_nhds ha)).filter_mono nhdsWithin_le_nhds)
  have hupper : ∀ᶠ t in 𝓝[<] 0, ξ t ≤ b := by
    have h1 : ∀ᶠ t in 𝓝[<] 0, 0 < t⁻¹ * (ξ t - ξ 0) :=
      hsl.eventually (isOpen_Ioi.mem_nhds hc)
    filter_upwards [h1, self_mem_nhdsWithin] with t h1 ht
    have htinv : t⁻¹ < 0 := by
      have : 0 < -t := neg_pos.mpr ht
      simpa using (inv_pos.mpr this : 0 < (-t)⁻¹)
    have hX : ξ t - ξ 0 < 0 := by
      rcases (mul_pos_iff.mp h1) with ⟨h,_⟩ | ⟨_,h⟩
      · exact absurd h (not_lt.mpr (le_of_lt htinv))
      · exact h
    linarith
  filter_upwards [hnear, hupper] with t h1 h2
  exact ⟨le_of_lt h1, h2⟩

/-- A right-neighbourhood condition upgrades to membership on a genuine interval `[0,δ]`. -/
lemma exists_Icc_right_of_eventually {p : ℝ → Prop} (h : ∀ᶠ t in 𝓝[>] 0, p t) (h0 : p 0) :
    ∃ δ > 0, ∀ t ∈ Set.Icc 0 δ, p t := by
  rw [eventually_nhdsWithin_iff] at h
  obtain ⟨ε, hε, hεp⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨ε / 2, by linarith, fun t ht => ?_⟩
  rcases lt_or_eq_of_le ht.1 with ht0 | hteq
  · refine hεp ?_ ht0
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos ht0]
    linarith [ht.2]
  · subst hteq; exact h0

/-- A left-neighbourhood condition upgrades to membership on a genuine interval `[-δ,0]`. -/
lemma exists_Icc_left_of_eventually {p : ℝ → Prop} (h : ∀ᶠ t in 𝓝[<] 0, p t) (h0 : p 0) :
    ∃ δ > 0, ∀ t ∈ Set.Icc (-δ) 0, p t := by
  rw [eventually_nhdsWithin_iff] at h
  obtain ⟨ε, hε, hεp⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨ε / 2, by linarith, fun t ht => ?_⟩
  rcases lt_or_eq_of_le ht.2 with ht0 | hteq
  · refine hεp ?_ ht0
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_neg ht0]
    linarith [ht.1]
  · subst hteq; exact h0

/-! ## The Euclidean core -/

/-- **Euclidean core.**  Let `F G : E → ℝ` be differentiable at `x`, with `F x ∈ [a,b]`,
`fderiv F x ≠ 0`, and `G = 0` on the band `F ⁻¹' [a,b]` near `x`.  Then `fderiv G x = 0`. -/
theorem fderiv_eq_zero_of_eventually_eqOn_band {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : E → ℝ) {a b : ℝ} (hab : a < b) {x : E}
    (hF : HasFDerivAt F (fderiv ℝ F x) x) (hG : HasFDerivAt G (fderiv ℝ G x) x)
    (hx : F x ∈ Set.Icc a b) (hreg : fderiv ℝ F x ≠ 0)
    (hG0 : ∀ᶠ z in 𝓝 x, F z ∈ Set.Icc a b → G z = 0) :
    fderiv ℝ G x = 0 := by
  -- the one-dimensional mechanism applied to a straight line through `x`
  have key_pos : ∀ u : E, 0 < (fderiv ℝ F x) u → (fderiv ℝ G x) u = 0 := by
    intro u hu
    have hline : HasDerivAt (fun t : ℝ => x + t • u) u 0 := by
      have h := ((hasDerivAt_id (0:ℝ)).smul_const u).const_add x
      simpa using h
    have hxline : (fun t : ℝ => x + t • u) 0 = x := by simp
    have hF' : HasFDerivAt F (fderiv ℝ F x) ((fun t : ℝ => x + t • u) 0) := by
      rw [hxline]; exact hF
    have hG' : HasFDerivAt G (fderiv ℝ G x) ((fun t : ℝ => x + t • u) 0) := by
      rw [hxline]; exact hG
    have hξ : HasDerivAt (fun t : ℝ => F (x + t • u)) ((fderiv ℝ F x) u) 0 :=
      hF'.comp_hasDerivAt 0 hline
    have hρ : HasDerivAt (fun t : ℝ => G (x + t • u)) ((fderiv ℝ G x) u) 0 :=
      hG'.comp_hasDerivAt 0 hline
    obtain ⟨N, hN, hNG⟩ := Filter.eventually_iff_exists_mem.mp hG0
    obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.mp hN
    -- shrink any one-sided length so that the corresponding points stay in `N`
    have hshrink : ∀ δ₀ : ℝ, 0 < δ₀ → ∃ δ > 0, δ ≤ δ₀ ∧ δ * ‖u‖ < ε := by
      intro δ₀ hδ₀
      refine ⟨min δ₀ (ε / (‖u‖ + 1)), lt_min hδ₀ (by positivity), min_le_left _ _, ?_⟩
      calc min δ₀ (ε / (‖u‖ + 1)) * ‖u‖ ≤ (ε / (‖u‖ + 1)) * ‖u‖ :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
        _ < ε := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0:ℝ) < ‖u‖ + 1)]
            nlinarith [norm_nonneg u, hε]
    rcases lt_or_eq_of_le hx.2 with hb | hb
    · -- `F x < b`: the band is entered going to the right
      obtain ⟨δ₀, hδ₀, hδP⟩ := exists_Icc_right_of_eventually
          (eventually_Icc_nhdsGT hξ hu (by simpa using hx.1) (by simpa using hb))
          (by simpa using hx)
      obtain ⟨δ, hδ, hδle, hδn⟩ := hshrink δ₀ hδ₀
      have hzero : ∀ s ∈ Set.Icc (0:ℝ) δ, G (x + s • u) = 0 := by
        intro s hs
        have hband : F (x + s • u) ∈ Set.Icc a b := hδP s ⟨hs.1, le_trans hs.2 hδle⟩
        have hdist : x + s • u ∈ Metric.ball x ε := by
          rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg hs.1]
          exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hs.2 (norm_nonneg u)) hδn
        exact hNG _ (hεN hdist) hband
      have hmem : ∀ s ∈ Set.Icc (0:ℝ) δ, (fun t : ℝ => G (x + t • u)) s
          = (fun t : ℝ => G (x + t • u)) 0 := by
        intro s hs
        show G (x + s • u) = G (x + 0 • u)
        rw [hzero s hs, hzero 0 ⟨le_refl 0, hδ.le⟩]
      have hder := deriv_eq_zero_of_eqOn_Icc (φ := fun t : ℝ => G (x + t • u))
          hδ ⟨le_refl 0, hδ.le⟩ hmem hρ.differentiableAt
      rw [← hρ.deriv]; exact hder
    · -- `F x = b`: the band is entered going to the left
      have ha' : a < F (x + (0:ℝ) • u) := by simpa [hb] using hab
      have hb' : F (x + (0:ℝ) • u) ≤ b := by simp [hb]
      obtain ⟨δ₀, hδ₀, hδP⟩ := exists_Icc_left_of_eventually
          (eventually_Icc_nhdsLT hξ hu ha' hb') (by simpa using hx)
      obtain ⟨δ, hδ, hδle, hδn⟩ := hshrink δ₀ hδ₀
      have hzero : ∀ s ∈ Set.Icc (-δ) 0, G (x + s • u) = 0 := by
        intro s hs
        have hband : F (x + s • u) ∈ Set.Icc a b :=
          hδP s ⟨le_trans (neg_le_neg hδle) hs.1, hs.2⟩
        have hdist : x + s • u ∈ Metric.ball x ε := by
          rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_nonpos hs.2]
          have hle : -s ≤ δ := by linarith [hs.1]
          exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle (norm_nonneg u)) hδn
        exact hNG _ (hεN hdist) hband
      have hmem : ∀ s ∈ Set.Icc (-δ) 0, (fun t : ℝ => G (x + t • u)) s
          = (fun t : ℝ => G (x + t • u)) 0 := by
        intro s hs
        show G (x + s • u) = G (x + 0 • u)
        rw [hzero s hs, hzero 0 ⟨by linarith [hδ], le_refl 0⟩]
      have hder := deriv_eq_zero_of_eqOn_Icc (φ := fun t : ℝ => G (x + t • u))
          (by linarith [hδ]) ⟨by linarith [hδ], le_refl 0⟩ hmem hρ.differentiableAt
      rw [← hρ.deriv]; exact hder
  -- directions with nonzero `F`-derivative satisfy the claim
  have key : ∀ u : E, (fderiv ℝ F x) u ≠ 0 → (fderiv ℝ G x) u = 0 := by
    intro u hu
    rcases lt_or_gt_of_ne hu with hlt | hgt
    · have h := key_pos (-u) (by rw [map_neg]; exact neg_pos.mpr hlt)
      rw [map_neg] at h
      exact neg_eq_zero.mp h
    · exact key_pos u hgt
  -- the set of such directions spans `E`
  apply ContinuousLinearMap.ext
  intro u
  show (fderiv ℝ G x) u = (0:ℝ)
  by_cases hu : (fderiv ℝ F x) u = 0
  · obtain ⟨w, hw⟩ : ∃ w : E, (fderiv ℝ F x) w ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hreg (ContinuousLinearMap.ext h)
    have h1 : (fderiv ℝ G x) (u + w) = 0 := by
      apply key
      rw [map_add, hu, zero_add]
      exact hw
    have h2 : (fderiv ℝ G x) (u + (2:ℝ) • w) = 0 := by
      apply key
      rw [map_add, map_smul, hu, zero_add]
      simpa [smul_eq_mul] using mul_ne_zero two_ne_zero hw
    rw [map_add] at h1
    rw [map_add, map_smul] at h2
    have h2' : (fderiv ℝ G x) u + 2 * (fderiv ℝ G x) w = 0 := by
      simpa [smul_eq_mul] using h2
    have hB : (fderiv ℝ G x) w = 0 := by linarith [h1, h2']
    linarith [h1, hB]
  · exact key u hu

/-! ## From the chart representation to the manifold statement -/

/-- The manifold derivative of `g : M → ℝ` at a point of a chart source factors through the
derivative of the chart, the remaining factor being the Fréchet derivative of the chart
representation of `g`. -/
theorem mfderiv_chartRep_eq {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : M → ℝ) (hg : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ g) (p x : M)
    (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    mfderiv (𝓡 n) 𝓘(ℝ,ℝ) g x =
      (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
        g ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y))
        ((chartAt (EuclideanSpace ℝ (Fin n)) p) x)) ∘L
      mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) x := by
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) x :=
    mdifferentiableAt_atlas (chart_mem_atlas _ _) hx
  have hcs : MDifferentiableAt (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
      ((chartAt (EuclideanSpace ℝ (Fin n)) p) x) :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas _ _)
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).map_source hx)
  have hgmd : MDifferentiableAt (𝓡 n) 𝓘(ℝ,ℝ) g x := (hg x).mdifferentiableAt (by simp)
  have hgr : MDifferentiableAt (𝓡 n) 𝓘(ℝ,ℝ)
      (fun y : EuclideanSpace ℝ (Fin n) => g ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y))
      ((chartAt (EuclideanSpace ℝ (Fin n)) p) x) :=
    MDifferentiableAt.comp_of_eq ((chartAt (EuclideanSpace ℝ (Fin n)) p) x) hgmd hcs
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).left_inv hx)
  have hcomp := mfderiv_comp x hgr hc
  have heq : mfderiv (𝓡 n) 𝓘(ℝ,ℝ)
      ((fun y : EuclideanSpace ℝ (Fin n) => g ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y))
        ∘ (chartAt (EuclideanSpace ℝ (Fin n)) p)) x = mfderiv (𝓡 n) 𝓘(ℝ,ℝ) g x := by
    apply Filter.EventuallyEq.mfderiv_eq
    filter_upwards [(chartAt (EuclideanSpace ℝ (Fin n)) p).open_source.mem_nhds hx] with y hy
    simp only [Function.comp_apply]
    rw [OpenPartialHomeomorph.left_inv _ hy]
  rw [← heq, hcomp, mfderiv_eq_fderiv]
  rfl

/-! ## The target statement -/

theorem mfderiv_eq_zero_of_eqOn_band {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f R : M → ℝ) {a b : ℝ} (hab : a < b) {x : M}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hR : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ R)
    (hx : f x ∈ Set.Icc a b) (hreg : mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0)
    (hR0 : ∀ z : M, f z ∈ Set.Icc a b → R z = 0) :
    mfderiv (𝓡 n) 𝓘(ℝ, ℝ) R x = 0 := by
  have hφsrc : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := mem_chart_source _ x
  -- the chart representations of `f` and `R`
  let F : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => f ((chartAt (EuclideanSpace ℝ (Fin n)) x).symm y)
  let G : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => R ((chartAt (EuclideanSpace ℝ (Fin n)) x).symm y)
  have hx' : F ((chartAt (EuclideanSpace ℝ (Fin n)) x) x) ∈ Set.Icc a b := by
    simpa [F, (chartAt (EuclideanSpace ℝ (Fin n)) x).left_inv hφsrc] using hx
  have hFdiff : MDifferentiableAt (𝓡 n) 𝓘(ℝ,ℝ) F
      ((chartAt (EuclideanSpace ℝ (Fin n)) x) x) :=
    MDifferentiableAt.comp_of_eq ((chartAt (EuclideanSpace ℝ (Fin n)) x) x)
      ((hf x).mdifferentiableAt (by simp))
      (mdifferentiableAt_atlas_symm (chart_mem_atlas _ _)
        ((chartAt (EuclideanSpace ℝ (Fin n)) x).map_source hφsrc))
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).left_inv hφsrc)
  have hGdiff : MDifferentiableAt (𝓡 n) 𝓘(ℝ,ℝ) G
      ((chartAt (EuclideanSpace ℝ (Fin n)) x) x) :=
    MDifferentiableAt.comp_of_eq ((chartAt (EuclideanSpace ℝ (Fin n)) x) x)
      ((hR x).mdifferentiableAt (by simp))
      (mdifferentiableAt_atlas_symm (chart_mem_atlas _ _)
        ((chartAt (EuclideanSpace ℝ (Fin n)) x).map_source hφsrc))
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).left_inv hφsrc)
  have hG0 : ∀ z, F z ∈ Set.Icc a b → G z = 0 :=
    fun z hz => hR0 ((chartAt (EuclideanSpace ℝ (Fin n)) x).symm z) hz
  have hFdec := mfderiv_chartRep_eq f hf x x hφsrc
  have hRdec := mfderiv_chartRep_eq R hR x x hφsrc
  -- regularity is inherited by the chart representation
  have hreg' : fderiv ℝ F ((chartAt (EuclideanSpace ℝ (Fin n)) x) x) ≠ 0 := by
    intro h0
    apply hreg
    rw [hFdec]
    apply ContinuousLinearMap.ext
    intro v
    show (fderiv ℝ F ((chartAt (EuclideanSpace ℝ (Fin n)) x) x))
        ((mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) x) x) v) = 0
    rw [h0]
    rfl
  have hcore := fderiv_eq_zero_of_eventually_eqOn_band F G hab
      hFdiff.differentiableAt.hasFDerivAt hGdiff.differentiableAt.hasFDerivAt hx' hreg'
      (Filter.Eventually.of_forall hG0)
  rw [hRdec]
  apply ContinuousLinearMap.ext
  intro v
  show (fderiv ℝ G ((chartAt (EuclideanSpace ℝ (Fin n)) x) x))
      ((mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) x) x) v) = 0
  rw [hcore]
  rfl

end Work.Drive.N2
