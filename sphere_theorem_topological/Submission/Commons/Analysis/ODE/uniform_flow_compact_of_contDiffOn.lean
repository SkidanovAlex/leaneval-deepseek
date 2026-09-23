import Mathlib
import Submission.Commons.Analysis.ContinuousMap.exists_contDiffOn_nemitskii
import Submission.Commons.Analysis.ODE.contDiffAt_solutionMap
import Submission.Commons.Analysis.ODE.eqOn_of_hasDerivAt_of_locallyLipschitz

open scoped ContDiff Topology
open Set Filter Metric MeasureTheory

noncomputable section

namespace Commons.Analysis.ODE

/-! ## Auxiliary continuous linear maps on `C(Icc (-a) a, E)`

These are the tools used to set up the fixed-point equation `Ψ = 0` whose implicit solution is the
local flow. -/

/-- Clamping a real number into `Icc (-a) a`. -/
private def clampI (a : ℝ) (ha : 0 ≤ a) : ℝ → Icc (-a) a :=
  Set.projIcc (-a) a (by linarith)

private lemma clampI_continuous (a : ℝ) (ha : 0 ≤ a) : Continuous (clampI a ha) :=
  continuous_projIcc

private lemma clampI_coe_of_mem (a : ℝ) (ha : 0 ≤ a) {s : ℝ} (hs : s ∈ Icc (-a) a) :
    ((clampI a ha s : Icc (-a) a) : ℝ) = s := by
  rw [clampI, Set.projIcc_of_mem _ hs]

/-- The constant map as a continuous linear map. -/
private def constCM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℝ) :
    E →L[ℝ] C(Icc (-a) a, E) :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun _ => x, continuous_const⟩
      map_add' := by intro x y; ext s; rfl
      map_smul' := by intro c x; ext s; rfl }
    1 (by
      intro x
      rw [one_mul]
      refine (ContinuousMap.norm_le _ (norm_nonneg x)).2 (fun s => ?_)
      exact le_rfl)

private lemma constCM_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℝ)
    (x : E) (s : Icc (-a) a) : constCM (E := E) a x s = x := rfl

/-- The primitive operator `w ↦ (σ ↦ ∫_0^σ w)` as a continuous linear map. -/
private def intMapCLM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (ha : 0 ≤ a) : C(Icc (-a) a, E) →L[ℝ] C(Icc (-a) a, E) :=
  LinearMap.mkContinuous
    { toFun := fun w => ⟨fun σ => ∫ s in (0:ℝ)..(σ:ℝ), w (clampI a ha s), by
          exact (intervalIntegral.continuous_primitive
            (fun u v => ((w.continuous.comp (clampI_continuous a ha)).intervalIntegrable u v))
            0).comp continuous_subtype_val⟩
      map_add' := by
        intro w₁ w₂
        ext σ
        rw [ContinuousMap.add_apply]
        have h : (fun s : ℝ => (w₁ + w₂) (clampI a ha s))
            = (fun s : ℝ => w₁ (clampI a ha s) + w₂ (clampI a ha s)) := by
          funext s
          rw [ContinuousMap.add_apply]
        show (∫ s in (0:ℝ)..(σ:ℝ), (w₁ + w₂) (clampI a ha s))
            = (∫ s in (0:ℝ)..(σ:ℝ), w₁ (clampI a ha s))
              + (∫ s in (0:ℝ)..(σ:ℝ), w₂ (clampI a ha s))
        rw [h, intervalIntegral.integral_add]
        · exact (w₁.continuous.comp (clampI_continuous a ha)).intervalIntegrable _ _
        · exact (w₂.continuous.comp (clampI_continuous a ha)).intervalIntegrable _ _
      map_smul' := by
        intro c w
        ext σ
        show (∫ s in (0:ℝ)..(σ:ℝ), (c • w) (clampI a ha s))
            = c • (∫ s in (0:ℝ)..(σ:ℝ), w (clampI a ha s))
        rw [show (fun s => (c • w) (clampI a ha s)) = (fun s => c • w (clampI a ha s)) from rfl]
        rw [intervalIntegral.integral_smul] }
    a (by
      intro w
      refine (ContinuousMap.norm_le _ (mul_nonneg ha (norm_nonneg w))).2 (fun σ => ?_)
      show ‖∫ s in (0:ℝ)..((σ : Icc (-a) a) : ℝ), w (clampI a ha s)‖ ≤ a * ‖w‖
      calc ‖∫ s in (0:ℝ)..((σ : Icc (-a) a) : ℝ), w (clampI a ha s)‖
          ≤ ‖w‖ * |((σ : Icc (-a) a) : ℝ) - 0| := by
            apply intervalIntegral.norm_integral_le_of_norm_le_const
            intro s hs
            exact ContinuousMap.norm_coe_le_norm w (clampI a ha s)
        _ = ‖w‖ * |((σ : Icc (-a) a) : ℝ)| := by rw [sub_zero]
        _ ≤ ‖w‖ * a := by
            gcongr
            exact abs_le.mpr ⟨σ.2.1, σ.2.2⟩
        _ = a * ‖w‖ := mul_comm _ _)

private lemma intMapCLM_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (ha : 0 ≤ a) (w : C(Icc (-a) a, E)) (σ : Icc (-a) a) :
    intMapCLM a ha w σ = ∫ s in (0:ℝ)..(σ:ℝ), w (clampI a ha s) := rfl

private lemma norm_intMapCLM_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (ha : 0 ≤ a) : ‖intMapCLM (E := E) a ha‖ ≤ a := by
  refine ContinuousLinearMap.opNorm_le_bound _ ha (fun w => ?_)
  exact (ContinuousMap.norm_le _ (mul_nonneg ha (norm_nonneg w))).2 (fun σ => by
    show ‖∫ s in (0:ℝ)..((σ : Icc (-a) a) : ℝ), w (clampI a ha s)‖ ≤ a * ‖w‖
    calc ‖∫ s in (0:ℝ)..((σ : Icc (-a) a) : ℝ), w (clampI a ha s)‖
        ≤ ‖w‖ * |((σ : Icc (-a) a) : ℝ) - 0| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro s hs
          exact ContinuousMap.norm_coe_le_norm w (clampI a ha s)
      _ = ‖w‖ * |((σ : Icc (-a) a) : ℝ)| := by rw [sub_zero]
      _ ≤ ‖w‖ * a := by
          gcongr
          exact abs_le.mpr ⟨σ.2.1, σ.2.2⟩
      _ = a * ‖w‖ := mul_comm _ _)

/-- The set of continuous maps with image in an open set is a neighbourhood of any of its members. -/
private lemma nhds_image_subset_of_isCompact {K E : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] {W : Set E} (hW : IsOpen W) {g₀ : C(K, E)} (hg₀ : ∀ s, g₀ s ∈ W) :
    {g : C(K, E) | ∀ s, g s ∈ W} ∈ 𝓝 g₀ := by
  obtain ⟨δ, hδ, hδW⟩ := (isCompact_range g₀.continuous).exists_cthickening_subset_open hW
    (fun x ⟨s, hs⟩ => hs ▸ hg₀ s)
  refine Metric.mem_nhds_iff.mpr ⟨δ, hδ, fun g hg s => hδW ?_⟩
  rw [Metric.mem_cthickening_iff]
  refine le_trans (infEDist_le_edist_of_mem (⟨s, rfl⟩ : g₀ s ∈ Set.range g₀)) ?_
  rw [edist_dist]
  exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff hδ).mpr (by
    calc dist (g s) (g₀ s) ≤ dist g g₀ := ContinuousMap.dist_apply_le_dist s
      _ < δ := Metric.mem_ball.mp hg))

/-- **Localized Nemytskii (composition) operator smoothness, special case `M = E`.**  If `F : E → E`
is `C^∞` on an open set `W`, then the composition operator `g ↦ F ∘ g` on `C(K, E)` is `C^∞` on the
open set of those `g` whose image lies in `W`. -/
private theorem nemitskii_local {K E : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {W : Set E} (hW : IsOpen W) {F : E → E}
    (hF : ContDiffOn ℝ ∞ F W) :
    ∃ Φ : C(K, E) → C(K, E),
      (∀ g, (∀ s : K, g s ∈ W) → ∀ s : K, Φ g s = F (g s)) ∧
      ContDiffOn ℝ ∞ Φ {g : C(K, E) | ∀ s : K, g s ∈ W} :=
  Commons.Analysis.ContinuousMap.exists_contDiffOn_nemitskii hW hF

/-! ## Uniform Lipschitz and boundedness data on a compact subset

Pointwise local Lipschitzness of a `C^∞` (even `C^1`) function plus compactness gives a *uniform*
radius, a uniform Lipschitz constant and a uniform norm bound on the balls of that radius around
the points of the compact set. -/

private lemma exists_uniform_lipschitz_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → E} {W : Set E} (hW : IsOpen W) (hFW : ContDiffOn ℝ ∞ F W)
    {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty) (hKW : K ⊆ W) :
    ∃ r : ℝ, 0 < r ∧ ∃ L : NNReal, ∃ M : ℝ, 0 ≤ M ∧
      ∀ p ∈ K, closedBall p r ⊆ W ∧ LipschitzOnWith L F (closedBall p r) ∧
        (∀ y ∈ closedBall p r, ‖F y‖ ≤ M) := by
  classical
  have hloc : ∀ x : K, ∃ (Lx : NNReal) (τx : Set E) (ax : ℝ) (Mx : ℝ),
      0 < ax ∧ τx ∈ 𝓝 (x : E) ∧ LipschitzOnWith Lx F τx ∧
      (ball (x : E) ax ⊆ τx ∩ W) ∧ 0 ≤ Mx ∧ (∀ y ∈ ball (x : E) ax, ‖F y‖ ≤ Mx) := by
    intro x
    have hxW : (x : E) ∈ W := hKW x.2
    have hcd : ContDiffAt ℝ ∞ F (x : E) := hFW.contDiffAt (hW.mem_nhds hxW)
    obtain ⟨Lx, τx, hτx, hLipx⟩ :=
      (hcd.of_le (by norm_num : ((1 : ℕ∞ω)) ≤ ∞)).exists_lipschitzOnWith
    obtain ⟨b₁, hb₁, hb₁sub⟩ := Metric.mem_nhds_iff.mp hτx
    obtain ⟨b₂, hb₂, hb₂sub⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hxW)
    have hcont : ContinuousAt F (x : E) := hcd.continuousAt
    obtain ⟨b₃, hb₃, hb₃sub⟩ :=
      Metric.mem_nhds_iff.mp (hcont.preimage_mem_nhds (Metric.ball_mem_nhds (F (x : E)) one_pos))
    refine ⟨Lx, τx, min b₁ (min b₂ b₃) / 2, ‖F (x : E)‖ + 1, by positivity, hτx, hLipx, ?_,
      by positivity, ?_⟩
    · intro y hy
      rw [Metric.mem_ball] at hy
      have h1 : dist y (x : E) < b₁ := by
        have := min_le_left b₁ (min b₂ b₃); linarith
      have h2 : dist y (x : E) < b₂ := by
        have := le_trans (min_le_right b₁ (min b₂ b₃)) (min_le_left b₂ b₃); linarith
      exact ⟨hb₁sub (Metric.mem_ball.mpr h1), hb₂sub (Metric.mem_ball.mpr h2)⟩
    · intro y hy
      rw [Metric.mem_ball] at hy
      have h3 : dist y (x : E) < b₃ := by
        have := le_trans (min_le_right b₁ (min b₂ b₃)) (min_le_right b₂ b₃); linarith
      have hd : ‖F y - F (x : E)‖ < 1 := by
        have h := hb₃sub (Metric.mem_ball.mpr h3)
        simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at h
        exact h
      have htri : ‖F y‖ ≤ ‖F y - F (x : E)‖ + ‖F (x : E)‖ := by
        calc ‖F y‖ = ‖(F y - F (x : E)) + F (x : E)‖ := by rw [sub_add_cancel]
          _ ≤ ‖F y - F (x : E)‖ + ‖F (x : E)‖ := norm_add_le _ _
      have hd' : ‖F y - F (x : E)‖ ≤ 1 := le_of_lt hd
      linarith
  choose Lx τx ax Mx hax hτx hLipx hballsub hMxnn hMxbd using hloc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => ball (x : E) (ax x / 2))
      (fun x => isOpen_ball)
      (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, by
        simp only [Metric.mem_ball, dist_self]; exact half_pos (hax ⟨y, hy⟩)⟩)
  have htne : t.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    obtain ⟨y, hy⟩ := hKne
    have hmem := ht hy
    rw [hcon] at hmem
    simpa using hmem
  obtain ⟨x₀, hx₀t⟩ := htne
  have hAne : (t.image (fun x : K => ax x / 2)).Nonempty :=
    Finset.image_nonempty.mpr ⟨x₀, hx₀t⟩
  have hLne : (t.image Lx).Nonempty := Finset.image_nonempty.mpr ⟨x₀, hx₀t⟩
  have hMne : (t.image Mx).Nonempty := Finset.image_nonempty.mpr ⟨x₀, hx₀t⟩
  refine ⟨(t.image (fun x : K => ax x / 2)).min' hAne, ?_,
    (t.image Lx).max' hLne, (t.image Mx).max' hMne, ?_, fun p hp => ?_⟩
  · rw [Finset.lt_min'_iff]
    rintro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact half_pos (hax x)
  · have hle : Mx x₀ ≤ (t.image Mx).max' hMne :=
      Finset.le_max' _ _ (Finset.mem_image.mpr ⟨x₀, hx₀t, rfl⟩)
    exact le_trans (hMxnn x₀) hle
  · have hpcover : p ∈ ⋃ x ∈ t, ball (x : E) (ax x / 2) := ht hp
    simp only [mem_iUnion, exists_prop] at hpcover
    obtain ⟨x, hxt, hxball⟩ := hpcover
    rw [Metric.mem_ball] at hxball
    have hsub : closedBall p ((t.image (fun y : K => ax y / 2)).min' hAne) ⊆ ball (x : E) (ax x) := by
      intro y hy
      rw [Metric.mem_closedBall] at hy
      rw [Metric.mem_ball]
      have hle : (t.image (fun y : K => ax y / 2)).min' hAne ≤ ax x / 2 :=
        Finset.min'_le _ _ (Finset.mem_image.mpr ⟨x, hxt, rfl⟩)
      have h1 : dist y p ≤ ax x / 2 := le_trans hy hle
      have h2 : dist p (x : E) ≤ ax x / 2 := le_of_lt hxball
      have h3 : dist y (x : E) ≤ dist y p + dist p (x : E) := dist_triangle _ _ _
      linarith
    have hLx : Lx x ≤ (t.image Lx).max' hLne :=
      Finset.le_max' _ _ (Finset.mem_image.mpr ⟨x, hxt, rfl⟩)
    have hMx : Mx x ≤ (t.image Mx).max' hMne :=
      Finset.le_max' _ _ (Finset.mem_image.mpr ⟨x, hxt, rfl⟩)
    have hsubτ : closedBall p ((t.image (fun y : K => ax y / 2)).min' hAne) ⊆ τx x :=
      fun y hy => (hballsub x (hsub hy)).1
    refine ⟨fun y hy => (hballsub x (hsub hy)).2, ?_, ?_⟩
    · exact ((hLipx x).mono hsubτ).weaken hLx
    · intro y hy
      exact le_trans (hMxbd x y (hsub hy)) hMx

/-! ## Picard–Lindelöf with a bound on the trajectory

Mathlib's public existence theorems for `IsPicardLindelof` do not record that the trajectory stays
inside the closed ball on which the field was assumed Lipschitz; we extract that fact from the
internal `FunSpace` fixed-point construction. -/

private theorem exists_hasDerivWithinAt_mem_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : NNReal}
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → E, α t₀ = x ∧
      (∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t) ∧
      (∀ t : ℝ, α t ∈ closedBall x₀ a) := by
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, ?_, ?_, fun t => α.compProj_mem_closedBall hf.mul_max_le⟩
  · rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · intro t ht
    apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
      α.continuous_compProj.continuousOn
      (fun _ _ => α.compProj_mem_closedBall hf.mul_max_le) x ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

/-- **Uniform short-time existence for a uniformly Lipschitz field on a compact set.**  There is a
time `ρ > 0` and a radius `r > 0` such that around every point `p` of the compact set `K` the field
`F` is Lipschitz (with constant `L`) and bounded (by `M`) on `closedBall p r`, and the trajectory
through `p` exists for `|t| < 2ρ` while staying within `closedBall p (r/2)`. -/
private theorem exists_uniform_trajectory
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E} {W : Set E} (hW : IsOpen W) (hFW : ContDiffOn ℝ ∞ F W)
    {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty) (hKW : K ⊆ W) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ r : ℝ, 0 < r ∧ ∃ L : NNReal, ∃ M : ℝ, 0 ≤ M ∧
      (L : ℝ) * ρ < 1 / 2 ∧
      (∀ p ∈ K, closedBall p r ⊆ W ∧ LipschitzOnWith L F (closedBall p r) ∧
        (∀ y ∈ closedBall p r, ‖F y‖ ≤ M) ∧
        ∃ β : ℝ → E, β 0 = p ∧
          (∀ t : ℝ, |t| < 2 * ρ → HasDerivAt β (F (β t)) t) ∧
          (∀ t : ℝ, |t| ≤ ρ → β t ∈ closedBall p (r / 2))) := by
  obtain ⟨r₀, hr₀, L, M, hMnn, hdata⟩ := exists_uniform_lipschitz_bounded hW hFW hK hKne hKW
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  set ρ : ℝ := min (r₀ / (4 * (M + 1))) (1 / (4 * ((L : ℝ) + 1))) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]; exact lt_min (by positivity) (by positivity)
  have hρ_le1 : ρ ≤ r₀ / (4 * (M + 1)) := by rw [hρdef]; exact min_le_left _ _
  have hρ_le2 : ρ ≤ 1 / (4 * ((L : ℝ) + 1)) := by rw [hρdef]; exact min_le_right _ _
  have hLρ : (L : ℝ) * ρ < 1 / 2 := by
    have hden : (0 : ℝ) < 4 * ((L : ℝ) + 1) := by positivity
    have h1 : ρ * (4 * ((L : ℝ) + 1)) ≤ 1 := by
      have h2 := hρ_le2
      rw [le_div_iff₀ hden] at h2
      linarith
    nlinarith [h1, hLnn]
  have hρin_le : M * (2 * ρ) ≤ r₀ / 2 := by
    have hden : (0 : ℝ) < 4 * (M + 1) := by positivity
    have h1 : ρ * (4 * (M + 1)) ≤ r₀ := by
      have h2 := hρ_le1
      rw [le_div_iff₀ hden] at h2
      linarith
    nlinarith [h1, hMnn, hρpos]
  refine ⟨ρ, hρpos, r₀, hr₀, L, M, hMnn, hLρ, fun p hp => ?_⟩
  obtain ⟨hbW, hbLip, hbBd⟩ := hdata p hp
  have hsub : closedBall p (r₀ / 2) ⊆ closedBall p r₀ :=
    closedBall_subset_closedBall (by linarith)
  have hr2 : (0 : ℝ) < r₀ / 2 := by linarith
  -- Picard–Lindelöf with the uniform constants
  set a : NNReal := ⟨r₀ / 2, hr2.le⟩ with hadef
  set Lb : NNReal := ⟨M, hMnn⟩ with hLbdef
  set ρin : ℝ := 2 * ρ with hρindef
  have hρinpos : 0 < ρin := by rw [hρindef]; linarith
  have h0mem : (0 : ℝ) ∈ Icc (-ρin) ρin :=
    ⟨by linarith [hρinpos.le], by linarith [hρinpos.le]⟩
  have hpl : IsPicardLindelof (fun (_ : ℝ) (y : E) => F y) ⟨0, h0mem⟩ p a 0 Lb L := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      exact hbLip.mono hsub
    · intro x hx
      exact continuousOn_const
    · intro t ht x hx
      exact hbBd x (hsub hx)
    · have hmax : max (ρin - (0:ℝ)) ((0:ℝ) - (-ρin)) = ρin := by
        rw [sub_zero, zero_sub, neg_neg, max_self]
      have hLb : (Lb : ℝ) = M := rfl
      have ha : (a : ℝ) = r₀ / 2 := rfl
      rw [hLb, ha, hmax]
      simp only [NNReal.coe_zero, sub_zero]
      exact hρin_le
  obtain ⟨α, hα0, hαode, hαmem⟩ :=
    exists_hasDerivWithinAt_mem_closedBall hpl (mem_closedBall_self (le_refl (0 : NNReal)))
  refine ⟨hbW, hbLip, hbBd, α, hα0, ?_, ?_⟩
  · intro t ht
    have htI : t ∈ Ioo (-ρin) ρin := by
      rw [abs_lt] at ht; exact ⟨ht.1, ht.2⟩
    exact (hαode t ⟨le_of_lt htI.1, le_of_lt htI.2⟩).hasDerivAt
      (Icc_mem_nhds htI.1 htI.2)
  · intro t ht
    exact hαmem t

/-- A `C^∞` function on an open set is locally Lipschitz at every point of that set. -/
private lemma locallyLipschitz_of_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → E} {W : Set E} (hW : IsOpen W) (hFW : ContDiffOn ℝ ∞ F W)
    {x : E} (hx : x ∈ W) :
    ∃ K : NNReal, ∃ U ∈ 𝓝 x, LipschitzOnWith K F U :=
  ((hFW.contDiffAt (hW.mem_nhds hx)).of_le (by norm_num : ((1 : ℕ∞ω)) ≤ ∞)).exists_lipschitzOnWith

/-- **Two-sided uniqueness for `x' = F x` with a locally Lipschitz field.**  Two solutions on
`Icc (-c) c` with the same value at `0` agree everywhere, provided `F` is locally Lipschitz at every
point of one of the trajectories. -/
private theorem eqOn_flow_of_hasDerivAt_of_locallyLipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E} {u v : ℝ → E} {c : ℝ} (hc : 0 < c)
    (hu : ∀ t ∈ Icc (-c) c, HasDerivAt u (F (u t)) t)
    (hv : ∀ t ∈ Icc (-c) c, HasDerivAt v (F (v t)) t)
    (hloc : ∀ t ∈ Icc (-c) c, ∃ K : NNReal, ∃ U ∈ 𝓝 (u t), LipschitzOnWith K F U)
    (h0 : u 0 = v 0) : EqOn u v (Icc (-c) c) := by
  have hpos : EqOn u v (Icc 0 c) :=
    eqOn_of_hasDerivAt_of_locallyLipschitz (f := F) (u := u) (v := v) (a := 0) (b := c) hc.le
      (fun t ht => hu t ⟨by linarith [ht.1], ht.2⟩)
      (fun t ht => hv t ⟨by linarith [ht.1], ht.2⟩)
      (fun t ht => hloc t ⟨by linarith [ht.1], ht.2⟩) h0
  have hneg : EqOn (fun s => u (-s)) (fun s => v (-s)) (Icc 0 c) :=
    eqOn_of_hasDerivAt_of_locallyLipschitz (f := fun y => -F y) (u := fun s => u (-s))
      (v := fun s => v (-s)) (a := 0) (b := c) hc.le
      (fun t ht => by
        have ht' : -t ∈ Icc (-c) c := ⟨by linarith [ht.2], by linarith [ht.1]⟩
        have h := (hu (-t) ht').scomp t (hasDerivAt_neg t)
        simpa [Function.comp_def, neg_one_smul] using h)
      (fun t ht => by
        have ht' : -t ∈ Icc (-c) c := ⟨by linarith [ht.2], by linarith [ht.1]⟩
        have h := (hv (-t) ht').scomp t (hasDerivAt_neg t)
        simpa [Function.comp_def, neg_one_smul] using h)
      (fun t ht => by
        have ht' : -t ∈ Icc (-c) c := ⟨by linarith [ht.2], by linarith [ht.1]⟩
        obtain ⟨K, U, hU, hLip⟩ := hloc (-t) ht'
        exact ⟨K, U, hU, hLip.neg⟩)
      (by simpa [Function.comp_def] using h0)
  intro t ht
  rcases le_or_gt 0 t with h | h
  · exact hpos ⟨h, ht.2⟩
  · have hmem : -t ∈ Icc (0 : ℝ) c := ⟨by linarith, by linarith [ht.1]⟩
    have h1 : u (-(-t)) = v (-(-t)) := hneg hmem
    simpa using h1

/-- **Smooth dependence on the initial condition with prescribed data.**  Given a solution `β`
through `p` of `ẋ = F x` on the (slightly larger) interval `|t| < ρ_in`, lying in `closedBall p (r/2)`
for `|t| ≤ s`, where `F` is `L`-Lipschitz on `closedBall p r ⊆ W` and `L s < 1/2`, there is a local
flow `u` on a neighbourhood `O` of `p`, solving the ODE with trajectories in `W`, and `q ↦ u q t` is
`C^∞` at `p` for `|t| ≤ s/2`. -/
private theorem local_flow_of_trajectory
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E} {W : Set E} (hW : IsOpen W) (hFW : ContDiffOn ℝ ∞ F W)
    {p : E} {r : ℝ} (hr : 0 < r) (hballW : closedBall p r ⊆ W)
    {L : NNReal} (hLip : LipschitzOnWith L F (closedBall p r))
    {ρ_in s : ℝ} (hρ_in : 0 < ρ_in) (hs : 0 < s) (hs_lt : s < ρ_in)
    (hLs : (L : ℝ) * s < 1 / 2)
    {β : ℝ → E} (hβ0 : β 0 = p)
    (hβode : ∀ t : ℝ, |t| < ρ_in → HasDerivAt β (F (β t)) t)
    (hβbd : ∀ t : ℝ, |t| ≤ s → β t ∈ closedBall p (r / 2)) :
    ∃ O : Set E, O ∈ 𝓝 p ∧ ∃ u : E → ℝ → E,
      (∀ q ∈ O, u q 0 = q) ∧
      (∀ q ∈ O, ∀ t : ℝ, |t| ≤ s / 2 → HasDerivAt (u q) (F (u q t)) t) ∧
      (∀ q ∈ O, ∀ t : ℝ, |t| ≤ s / 2 → u q t ∈ W) ∧
      (∀ t : ℝ, |t| ≤ s / 2 → ContDiffAt ℝ ∞ (fun q : E => u q t) p) := by
  classical
  have hsnn : (0 : ℝ) ≤ s := le_of_lt hs
  haveI : CompactSpace (Icc (-s) s) := isCompact_iff_compactSpace.mp isCompact_Icc
  -- (1) the base trajectory as an element of `C(Icc (-s) s, E)`
  have hb_ode : ∀ t : Icc (-s) s, HasDerivAt β (F (β t)) (t : ℝ) := fun t =>
    hβode t (by rw [abs_lt]; exact ⟨by linarith [t.2.1, hs_lt], by linarith [t.2.2, hs_lt]⟩)
  have hβcontI : ContinuousOn β (Icc (-s) s) := fun t ht =>
    (hb_ode ⟨t, ht⟩).continuousAt.continuousWithinAt
  let y₀ : C(Icc (-s) s, E) := ⟨fun t => β t, hβcontI.domRestrict⟩
  have hy₀_apply : ∀ t : Icc (-s) s, y₀ t = β t := fun t => rfl
  have hβmem : ∀ t : Icc (-s) s, β t ∈ closedBall p (r / 2) := fun t =>
    hβbd t (abs_le.mpr ⟨t.2.1, t.2.2⟩)
  have hy₀W : ∀ t : Icc (-s) s, y₀ t ∈ W := fun t =>
    hballW (closedBall_subset_closedBall (by linarith) (hβmem t))
  -- (2) the Nemytskii operator
  obtain ⟨Φ, hΦ_agree, hΦ_smooth⟩ := nemitskii_local hW hFW (K := Icc (-s) s)
  have hU_nhds : {g : C(Icc (-s) s, E) | ∀ σ, g σ ∈ W} ∈ 𝓝 y₀ :=
    nhds_image_subset_of_isCompact hW hy₀W
  have hΦ_cd : ContDiffAt ℝ ∞ Φ y₀ := hΦ_smooth.contDiffAt hU_nhds
  -- (3) the equation `Ψ = 0`
  let Ψ : E × C(Icc (-s) s, E) → C(Icc (-s) s, E) :=
    fun z => z.2 - constCM s z.1 - intMapCLM s hsnn (Φ z.2)
  have hbase : Ψ (p, y₀) = 0 := by
    ext t
    show (y₀ t - p - ∫ σ in (0:ℝ)..((t : Icc (-s) s) : ℝ),
        Φ y₀ (clampI s hsnn σ)) = 0
    have hInt : (∫ σ in (0:ℝ)..((t : Icc (-s) s) : ℝ),
          Φ y₀ (clampI s hsnn σ)) = ∫ σ in (0:ℝ)..((t : Icc (-s) s) : ℝ), F (β σ) := by
      apply intervalIntegral.integral_congr
      intro σ hσ
      rw [uIcc] at hσ
      have hσ' : σ ∈ Icc (-s) s :=
        ⟨le_trans (le_min (neg_nonpos.mpr hsnn) t.2.1) hσ.1,
         le_trans hσ.2 (max_le hsnn t.2.2)⟩
      have hc : (clampI s hsnn σ : Icc (-s) s) = ⟨σ, hσ'⟩ :=
        Subtype.ext (clampI_coe_of_mem s hsnn hσ')
      show (Φ y₀) (clampI s hsnn σ) = F (β σ)
      rw [hc]
      exact hΦ_agree y₀ hy₀W ⟨σ, hσ'⟩
    have hFTC : (∫ σ in (0:ℝ)..((t : Icc (-s) s) : ℝ), F (β σ)) = y₀ t - p := by
      have hsub : ∀ x ∈ uIcc (0:ℝ) ((t : Icc (-s) s) : ℝ), x ∈ Icc (-s) s := by
        intro x hx
        rw [uIcc] at hx
        exact ⟨le_trans (le_min (neg_nonpos.mpr hsnn) t.2.1) hx.1,
               le_trans hx.2 (max_le hsnn t.2.2)⟩
      have hderiv : ∀ x ∈ uIcc (0:ℝ) ((t : Icc (-s) s) : ℝ),
          HasDerivAt β (F (β x)) x := by
        intro x hx
        refine hβode x ?_
        rw [abs_lt]
        obtain ⟨h1, h2⟩ := hsub x hx
        exact ⟨by linarith [h1, hs_lt], by linarith [h2, hs_lt]⟩
      have hint : IntervalIntegrable (fun σ => F (β σ)) volume (0:ℝ)
          ((t : Icc (-s) s) : ℝ) := by
        have hcontβ : ContinuousOn β (uIcc (0:ℝ) ((t : Icc (-s) s) : ℝ)) := fun x hx =>
          (hderiv x hx).continuousAt.continuousWithinAt
        have himg : ∀ y ∈ β '' (uIcc (0:ℝ) ((t : Icc (-s) s) : ℝ)), ContinuousAt F y := by
          rintro y ⟨x, hx, rfl⟩
          exact hFW.continuousOn.continuousAt (hW.mem_nhds (hy₀W ⟨x, hsub x hx⟩))
        exact ContinuousOn.intervalIntegrable
          (ContinuousOn.comp (fun y hy => (himg y hy).continuousWithinAt) hcontβ
            (mapsTo_image _ _))
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, hβ0]
      rfl
    rw [hInt, hFTC, sub_self]
  -- (4) smoothness of `Ψ`
  have hΨ_cd : ContDiffAt ℝ ∞ Ψ (p, y₀) := by
    have h1 : ContDiffAt ℝ ∞ (fun z : E × C(Icc (-s) s, E) => z.2) (p, y₀) := contDiffAt_snd
    have h2 : ContDiffAt ℝ ∞ (fun z : E × C(Icc (-s) s, E) => constCM s z.1) (p, y₀) :=
      ((constCM (E := E) s).contDiff.contDiffAt).comp (p, y₀) contDiffAt_fst
    have h3 : ContDiffAt ℝ ∞ (fun z : E × C(Icc (-s) s, E) => Φ z.2) (p, y₀) :=
      hΦ_cd.comp (p, y₀) contDiffAt_snd
    have hclm : ContDiffAt ℝ ∞ (⇑(intMapCLM s hsnn)) (Φ y₀) :=
      (intMapCLM s hsnn).contDiff.contDiffAt (x := Φ y₀)
    have h4 : ContDiffAt ℝ ∞
        (fun z : E × C(Icc (-s) s, E) => intMapCLM s hsnn (Φ z.2)) (p, y₀) :=
      hclm.comp (p, y₀) h3
    exact (h1.sub h2).sub h4
  -- (5) the Lipschitz estimate for `Φ`
  have hΦ_lip : LipschitzOnWith L Φ (ball y₀ (r / 4)) := by
    refine LipschitzOnWith.of_dist_le_mul (fun y hy y' hy' => ?_)
    have hkey : ∀ (y : C(Icc (-s) s, E)), dist y y₀ < r / 4 →
        ∀ σ : Icc (-s) s, ‖y σ - p‖ ≤ r ∧ y σ ∈ W := by
      intro y hy σ
      have h1 : ‖y σ - y₀ σ‖ ≤ dist y y₀ := by
        rw [← dist_eq_norm]
        exact ContinuousMap.dist_apply_le_dist (f := y) (g := y₀) σ
      have h2 : ‖y₀ σ - p‖ ≤ r / 2 := by
        rw [hy₀_apply, ← dist_eq_norm]
        exact hβmem σ
      have h3 : ‖y σ - p‖ < r := by
        have htr : ‖y σ - p‖ ≤ ‖y σ - y₀ σ‖ + ‖y₀ σ - p‖ := by
          calc ‖y σ - p‖ = ‖(y σ - y₀ σ) + (y₀ σ - p)‖ := by
                rw [show y σ - p = (y σ - y₀ σ) + (y₀ σ - p) from by abel]
            _ ≤ _ := norm_add_le _ _
        calc ‖y σ - p‖ ≤ ‖y σ - y₀ σ‖ + ‖y₀ σ - p‖ := htr
          _ ≤ dist y y₀ + r / 2 := by linarith
          _ < r / 4 + r / 2 := by linarith
          _ < r := by linarith
      exact ⟨le_of_lt h3, hballW (by rw [Metric.mem_closedBall, dist_eq_norm]; exact le_of_lt h3)⟩
    have hyB := hkey y (Metric.mem_ball.mp hy)
    have hy'B := hkey y' (Metric.mem_ball.mp hy')
    rw [dist_eq_norm]
    refine (ContinuousMap.norm_le _ (by positivity)).2 (fun σ => ?_)
    rw [ContinuousMap.sub_apply, hΦ_agree y (fun σ => (hyB σ).2) σ,
      hΦ_agree y' (fun σ => (hy'B σ).2) σ]
    calc ‖F (y σ) - F (y' σ)‖
        ≤ (L : ℝ) * ‖y σ - y' σ‖ := by
          have h := hLip.dist_le_mul (y σ)
            (by rw [Metric.mem_closedBall, dist_eq_norm]; exact (hyB σ).1) (y' σ)
            (by rw [Metric.mem_closedBall, dist_eq_norm]; exact (hy'B σ).1)
          rwa [dist_eq_norm, dist_eq_norm] at h
      _ ≤ (L : ℝ) * dist y y' := by
          gcongr
          rw [dist_eq_norm]
          exact ContinuousMap.norm_coe_le_norm (y - y') σ
  have hΦ_diff : DifferentiableAt ℝ Φ y₀ := hΦ_cd.differentiableAt (by norm_num)
  have hfdΦ : ‖fderiv ℝ Φ y₀‖ ≤ (L : ℝ) :=
    norm_fderiv_le_of_lipschitzOn ℝ (Metric.ball_mem_nhds y₀ (by positivity)) hΦ_lip
  set M : C(Icc (-s) s, E) →L[ℝ] C(Icc (-s) s, E) :=
    (intMapCLM s hsnn).comp (fderiv ℝ Φ y₀) with hM
  have hL_norm : ‖M‖ < 1 / 2 := by
    rw [hM]
    have h1 : ‖(intMapCLM s hsnn).comp (fderiv ℝ Φ y₀)‖ ≤ s * (L : ℝ) := by
      refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
      exact mul_le_mul (norm_intMapCLM_le s hsnn) hfdΦ (norm_nonneg _) hsnn
    have h2 : s * (L : ℝ) < 1 / 2 := by rw [mul_comm]; exact hLs
    linarith
  have hL_has : HasFDerivAt (fun y : C(Icc (-s) s, E) =>
      intMapCLM s hsnn (Φ y)) M y₀ := by
    rw [hM]
    exact (intMapCLM s hsnn).hasFDerivAt.comp y₀ hΦ_diff.hasFDerivAt
  -- (6) the derivative of `Ψ` and invertibility
  have hΨ_has : HasFDerivAt Ψ
      (ContinuousLinearMap.snd ℝ E (C(Icc (-s) s, E))
        - (constCM (E := E) s).comp (ContinuousLinearMap.fst ℝ E (C(Icc (-s) s, E)))
        - M.comp (ContinuousLinearMap.snd ℝ E (C(Icc (-s) s, E)))) (p, y₀) := by
    have h1 : HasFDerivAt (fun z : E × C(Icc (-s) s, E) => z.2)
        (ContinuousLinearMap.snd ℝ E (C(Icc (-s) s, E))) (p, y₀) := hasFDerivAt_snd
    have h2 : HasFDerivAt (fun z : E × C(Icc (-s) s, E) => constCM s z.1)
        ((constCM (E := E) s).comp
          (ContinuousLinearMap.fst ℝ E (C(Icc (-s) s, E)))) (p, y₀) :=
      ((constCM s).hasFDerivAt (x := p)).comp (p, y₀) (hasFDerivAt_fst (p := (p, y₀)))
    have h3 : HasFDerivAt (fun z : E × C(Icc (-s) s, E) =>
        intMapCLM s hsnn (Φ z.2))
        (M.comp (ContinuousLinearMap.snd ℝ E (C(Icc (-s) s, E)))) (p, y₀) := by
      have hinner : HasFDerivAt (fun z : E × C(Icc (-s) s, E) => Φ z.2)
          ((fderiv ℝ Φ y₀) ∘SL
            (ContinuousLinearMap.snd ℝ E (C(Icc (-s) s, E)))) (p, y₀) :=
        hΦ_diff.hasFDerivAt.comp (p, y₀)
          (hasFDerivAt_snd (𝕜 := ℝ) (p := (p, y₀)))
      rw [hM, ContinuousLinearMap.comp_assoc]
      exact ((intMapCLM s hsnn).hasFDerivAt (x := Φ y₀)).comp (p, y₀) hinner
    exact (h1.sub h2).sub h3
  have hD_key : (ContinuousLinearMap.snd ℝ E (C(Icc (-s) s, E))
        - (constCM (E := E) s).comp (ContinuousLinearMap.fst ℝ E (C(Icc (-s) s, E)))
        - M.comp (ContinuousLinearMap.snd ℝ E (C(Icc (-s) s, E))))
      ∘SL ContinuousLinearMap.inr ℝ E (C(Icc (-s) s, E)) = 1 - M := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.inr_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.coe_comp', Function.comp_apply, Prod.fst_zero, Prod.snd_zero,
      ContinuousMap.sub_apply, ContinuousMap.one_apply]
    simp
  have hif : (fderiv ℝ Ψ (p, y₀) ∘SL
      ContinuousLinearMap.inr ℝ E (C(Icc (-s) s, E))).IsInvertible := by
    rw [hΨ_has.fderiv, hD_key]
    exact SmoothDep.isInvertible_one_sub M (lt_trans hL_norm (by norm_num))
  -- (7) the implicit function
  let ψ : E → C(Icc (-s) s, E) :=
    hΨ_cd.implicitFunction (by norm_num : (∞ : ℕ∞ω) ≠ 0) hif
  have hψ_cd : ContDiffAt ℝ ∞ ψ p :=
    hΨ_cd.contDiffAt_implicitFunction (by norm_num) hif
  have hψ_apply : ψ p = y₀ := hΨ_cd.implicitFunction_apply_self (by norm_num) hif
  have hψ_eq : ∀ᶠ q in 𝓝 p, Ψ (q, ψ q) = Ψ (p, y₀) :=
    hΨ_cd.eventually_apply_implicitFunction (by norm_num) hif
  have hψ_cont : ContinuousAt ψ p := hψ_cd.continuousAt
  -- (8) the trajectory stays in `W`
  have hvalW : ∀ (q : E), ψ q ∈ ball y₀ (r / 4) → ∀ σ : Icc (-s) s, ψ q σ ∈ W := by
    intro q hq σ
    apply hballW
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 : ‖ψ q σ - y₀ σ‖ ≤ dist (ψ q) y₀ := by
      rw [← dist_eq_norm]
      exact ContinuousMap.dist_apply_le_dist (f := ψ q) (g := y₀) σ
    have h2 : ‖y₀ σ - p‖ ≤ r / 2 := by
      rw [hy₀_apply, ← dist_eq_norm]
      exact hβmem σ
    have h3 : ‖ψ q σ - p‖ < r := by
      have htr : ‖ψ q σ - p‖ ≤ ‖ψ q σ - y₀ σ‖ + ‖y₀ σ - p‖ := by
        calc ‖ψ q σ - p‖ = ‖(ψ q σ - y₀ σ) + (y₀ σ - p)‖ := by
              rw [show ψ q σ - p = (ψ q σ - y₀ σ) + (y₀ σ - p) from by abel]
          _ ≤ _ := norm_add_le _ _
      calc ‖ψ q σ - p‖ ≤ ‖ψ q σ - y₀ σ‖ + ‖y₀ σ - p‖ := htr
        _ ≤ dist (ψ q) y₀ + r / 2 := by linarith
        _ < r / 4 + r / 2 := by linarith [Metric.mem_ball.mp hq]
        _ < r := by linarith
    exact le_of_lt h3
  -- (9) the final assembly
  let u : E → ℝ → E := fun q t => ψ q (clampI s hsnn t)
  refine ⟨{q | Ψ (q, ψ q) = 0 ∧ ψ q ∈ ball y₀ (r / 4)}, ?_, u, ?_, ?_, ?_, ?_⟩
  · refine Filter.inter_mem ?_ ?_
    · filter_upwards [hψ_eq] with q hq
      rwa [hbase] at hq
    · have hb : ball y₀ (r / 4) ∈ 𝓝 (ψ p) := by
        rw [hψ_apply]; exact Metric.ball_mem_nhds _ (by positivity)
      exact hψ_cont.preimage_mem_nhds hb
  · intro q hq
    have h2 := congrArg (fun w : C(Icc (-s) s, E) => w (clampI s hsnn 0)) hq.1
    simp only [ContinuousMap.zero_apply, Ψ, ContinuousMap.sub_apply, constCM_apply,
      intMapCLM_apply] at h2
    have hc0 : ((clampI s hsnn 0 : Icc (-s) s) : ℝ) = 0 :=
      clampI_coe_of_mem s hsnn (by constructor <;> linarith)
    rw [hc0, intervalIntegral.integral_same] at h2
    change ψ q (clampI s hsnn 0) = q
    exact sub_eq_zero.mp (sub_eq_zero.mp h2)
  · intro q hq t ht
    have hval := hvalW q hq.2
    have htIoo : t ∈ Ioo (-s) s := by
      rw [mem_Ioo]
      constructor <;> linarith [abs_le.mp ht]
    have hint_eq : ∀ σ : Icc (-s) s,
        ψ q σ = q + ∫ v in (0:ℝ)..(σ:ℝ), F (ψ q (clampI s hsnn v)) := by
      intro σ
      have h2 := congrArg (fun w : C(Icc (-s) s, E) => w σ) hq.1
      simp only [ContinuousMap.zero_apply, Ψ, ContinuousMap.sub_apply, constCM_apply,
        intMapCLM_apply] at h2
      have hcongr : (∫ v in (0:ℝ)..(σ:ℝ), Φ (ψ q) (clampI s hsnn v))
          = ∫ v in (0:ℝ)..(σ:ℝ), F (ψ q (clampI s hsnn v)) := by
        apply intervalIntegral.integral_congr
        intro v hv
        exact hΦ_agree (ψ q) hval (clampI s hsnn v)
      have h3 : ψ q σ - q = ∫ v in (0:ℝ)..(σ:ℝ), F (ψ q (clampI s hsnn v)) := by
        have h4 : ψ q σ - q - (∫ v in (0:ℝ)..(σ:ℝ), F (ψ q (clampI s hsnn v))) = 0 := by
          simpa [hcongr] using h2
        exact sub_eq_zero.mp h4
      rw [sub_eq_iff_eq_add, add_comm] at h3
      exact h3
    have hcont_g : Continuous fun v : ℝ => F (ψ q (clampI s hsnn v)) := by
      rw [continuous_iff_continuousAt]
      intro v
      have h1 : ContinuousAt (fun v : ℝ => ψ q (clampI s hsnn v)) v :=
        (ψ q).continuous.continuousAt.comp (clampI_continuous s hsnn).continuousAt
      exact ContinuousAt.comp (f := fun v : ℝ => ψ q (clampI s hsnn v)) (x := v)
        (hFW.continuousOn.continuousAt (hW.mem_nhds (hval (clampI s hsnn v)))) h1
    have hderiv : HasDerivAt
        (fun σ : ℝ => q + ∫ v in (0:ℝ)..σ, F (ψ q (clampI s hsnn v)))
        (F (ψ q (clampI s hsnn t))) t :=
      (intervalIntegral.integral_hasDerivAt_right (hcont_g.intervalIntegrable 0 t)
        (hcont_g.stronglyMeasurableAtFilter volume (𝓝 t)) hcont_g.continuousAt).const_add q
    have hev : (fun σ : ℝ => ψ q (clampI s hsnn σ)) =ᶠ[𝓝 t]
        (fun σ => q + ∫ v in (0:ℝ)..σ, F (ψ q (clampI s hsnn v))) := by
      filter_upwards [isOpen_Ioo.mem_nhds htIoo] with σ hσ
      have hσI : σ ∈ Icc (-s) s := ⟨le_of_lt hσ.1, le_of_lt hσ.2⟩
      have hc : (clampI s hsnn σ : Icc (-s) s) = ⟨σ, hσI⟩ :=
        Subtype.ext (clampI_coe_of_mem s hsnn hσI)
      rw [hc, hint_eq ⟨σ, hσI⟩]
    change HasDerivAt (fun σ : ℝ => ψ q (clampI s hsnn σ))
      (F (ψ q (clampI s hsnn t))) t
    exact hderiv.congr_of_eventuallyEq hev
  · intro q hq t ht
    have htI : t ∈ Icc (-s) s := by
      rw [abs_le] at ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hc : (clampI s hsnn t : Icc (-s) s) = ⟨t, htI⟩ :=
      Subtype.ext (clampI_coe_of_mem s hsnn htI)
    change ψ q (clampI s hsnn t) ∈ W
    rw [hc]
    exact hvalW q hq.2 ⟨t, htI⟩
  · intro t ht
    have htI : t ∈ Icc (-s) s := by
      rw [abs_le] at ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have heq : (fun q : E => u q t) = (fun q => ψ q ⟨t, htI⟩) := by
      funext q
      change ψ q (clampI s hsnn t) = ψ q ⟨t, htI⟩
      rw [show (clampI s hsnn t : Icc (-s) s) = ⟨t, htI⟩ from
        Subtype.ext (clampI_coe_of_mem s hsnn htI)]
    rw [heq]
    exact ((ContinuousMap.evalCLM ℝ ⟨t, htI⟩).contDiff.contDiffAt).comp p hψ_cd

/-- **Uniform local flow of a `C^∞` field on an open set (the correct hypothesis).**

If `F : E → E` is `C^∞` on an open set `W ⊆ E` and `K ⊆ W` is compact, then there are `ρ > 0` and a
family `α` solving `∂_t α p t = F (α p t)`, `α p 0 = p` for `p ∈ K`, `|t| ≤ ρ`, whose dependence on
the initial point is smooth at every `p ∈ K`. -/
theorem uniform_flow_compact_of_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E} {W : Set E} (hW : IsOpen W) (hFW : ContDiffOn ℝ ∞ F W)
    {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ α : E → ℝ → E,
      (∀ p ∈ K, α p 0 = p) ∧
      (∀ p ∈ K, ∀ t : ℝ, |t| ≤ ρ → HasDerivAt (α p) (F (α p t)) t) ∧
      (∀ p ∈ K, ∀ t : ℝ, |t| ≤ ρ →
        ContDiffAt ℝ ∞ (fun q : E => α q t) p) := by
  classical
  rcases Set.eq_empty_or_nonempty K with hKemp | hKne
  · subst hKemp
    exact ⟨1, one_pos, fun p _ => p, by simp, by simp, by simp⟩
  · obtain ⟨ρ, hρpos, r, hrpos, L, M, hMnn, hLρ, hdata⟩ :=
      exists_uniform_trajectory hW hFW hK hKne hKW
    have hdata' : ∀ p : K, closedBall (p : E) r ⊆ W ∧
        LipschitzOnWith L F (closedBall (p : E) r) ∧
        (∀ y ∈ closedBall (p : E) r, ‖F y‖ ≤ M) ∧
        ∃ β : ℝ → E, β 0 = (p : E) ∧
          (∀ t : ℝ, |t| < 2 * ρ → HasDerivAt β (F (β t)) t) ∧
          (∀ t : ℝ, |t| ≤ ρ → β t ∈ closedBall (p : E) (r / 2)) := fun p => hdata p p.2
    choose hbW hbLip hbBd fβ hβ0 hβode hβbd using hdata'
    have hflow : ∀ p : K, ∃ O : Set E, O ∈ 𝓝 (p : E) ∧ ∃ u : E → ℝ → E,
        (∀ q ∈ O, u q 0 = q) ∧
        (∀ q ∈ O, ∀ t : ℝ, |t| ≤ ρ / 2 → HasDerivAt (u q) (F (u q t)) t) ∧
        (∀ q ∈ O, ∀ t : ℝ, |t| ≤ ρ / 2 → u q t ∈ W) ∧
        (∀ t : ℝ, |t| ≤ ρ / 2 → ContDiffAt ℝ ∞ (fun q : E => u q t) (p : E)) := by
      intro p
      have h2ρ : 0 < 2 * ρ := by linarith
      have hρ2ρ : ρ < 2 * ρ := by linarith
      exact local_flow_of_trajectory (ρ_in := 2 * ρ) (s := ρ) hW hFW hrpos (hbW p) (hbLip p)
        h2ρ hρpos hρ2ρ hLρ (hβ0 p) (hβode p) (hβbd p)
    choose Of hOfmem uf huf0 hufode hufW hufsmooth using hflow
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun p : K => interior (Of p))
        (fun p => isOpen_interior)
        (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩,
          mem_interior_iff_mem_nhds.mpr (hOfmem ⟨y, hy⟩)⟩)
    have htne : t.Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      obtain ⟨y, hy⟩ := hKne
      have hmem := ht hy
      rw [hcon] at hmem
      simp at hmem
    obtain ⟨p₀, hp₀t⟩ := htne
    let idx : E → K := fun q => if h : ∃ p ∈ t, q ∈ interior (Of p) then h.choose else p₀
    have hidx_spec : ∀ q (h : ∃ p ∈ t, q ∈ interior (Of p)),
        idx q ∈ t ∧ q ∈ interior (Of (idx q)) := by
      intro q h
      have hh : idx q = h.choose := dif_pos h
      rw [hh]
      exact h.choose_spec
    have hidx_of_mem : ∀ q, q ∈ ⋃ p ∈ t, interior (Of p) →
        idx q ∈ t ∧ q ∈ interior (Of (idx q)) := by
      intro q hq
      exact hidx_spec q (by simpa only [mem_iUnion, exists_prop] using hq)
    let α : E → ℝ → E := fun q t => uf (idx q) q t
    refine ⟨ρ / 2, by linarith, α, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨hidxt, hidxp⟩ := hidx_of_mem p (ht hp)
      exact huf0 (idx p) p (interior_subset hidxp)
    · intro p hp T hT
      obtain ⟨hidxt, hidxp⟩ := hidx_of_mem p (ht hp)
      exact hufode (idx p) p (interior_subset hidxp) T hT
    · intro p hp T hT
      obtain ⟨hidxt, hidxp⟩ := hidx_of_mem p (ht hp)
      have hN : interior (Of (idx p)) ∩ Of ⟨p, hp⟩ ∈ 𝓝 p :=
        Filter.inter_mem (isOpen_interior.mem_nhds hidxp) (hOfmem ⟨p, hp⟩)
      have hev : (fun q : E => α q T) =ᶠ[𝓝 p] (fun q => uf ⟨p, hp⟩ q T) := by
        filter_upwards [hN] with q hq
        obtain ⟨hqint, hqofp⟩ := hq
        have hex : ∃ p' ∈ t, q ∈ interior (Of p') := ⟨idx p, hidxt, hqint⟩
        obtain ⟨hidxqt, hidxqint⟩ := hidx_spec q hex
        have hU1 : q ∈ Of (idx q) := interior_subset hidxqint
        have hTsub : ∀ τ ∈ Icc (-(ρ / 2)) (ρ / 2), |τ| ≤ ρ / 2 := fun τ hτ =>
          by rw [abs_le]; exact ⟨hτ.1, hτ.2⟩
        have hTI : T ∈ Icc (-(ρ / 2)) (ρ / 2) :=
          ⟨by linarith [abs_le.mp hT], by linarith [abs_le.mp hT]⟩
        have hI := eqOn_flow_of_hasDerivAt_of_locallyLipschitz (F := F) (c := ρ / 2)
          (u := uf (idx q) q) (v := uf ⟨p, hp⟩ q) (by linarith)
          (fun τ hτ => hufode (idx q) q hU1 τ (hTsub τ hτ))
          (fun τ hτ => hufode ⟨p, hp⟩ q hqofp τ (hTsub τ hτ))
          (fun τ hτ => locallyLipschitz_of_contDiffOn hW hFW
            (hufW (idx q) q hU1 τ (hTsub τ hτ)))
          (by rw [huf0 (idx q) q hU1, huf0 ⟨p, hp⟩ q hqofp])
        show uf (idx q) q T = uf ⟨p, hp⟩ q T
        exact hI hTI
      exact (hufsmooth ⟨p, hp⟩ T hT).congr_of_eventuallyEq hev

end Commons.Analysis.ODE
