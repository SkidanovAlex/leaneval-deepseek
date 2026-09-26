/-
# Holomorphy of the corrected left detour (clash-free copy)

This is a verbatim copy of the proof of `Work.Asymptotics.detourLeftC_mdifferentiableOn`
(module `Submission.Work.Asymptotics.detourLeftC_mdifferentiableOn`), with two differences:

* it does **not** import `Submission.Work.Asymptotics.clean_at_corner` nor
  `Submission.Work.Asymptotics.detourRight_mdifferentiableOn` (both of which transitively bring in
  `clean_at_corner`, which declares the public name `Work.Asymptotics.mdifferentiable_jInvariantFun`
  also declared by `Submission.Work.Asymptotics.Kfun_principal_part_z_lip`; a module containing both
  cannot build).  The imports are `Mathlib`, `Submission.Work.Asymptotics.contourLeftDefs` and
  `Submission.Work.Asymptotics.detourLeft_mdifferentiableOn`, the latter supplying the parametric
  engine `mdifferentiableOn_paramIntegral_Kfun` together with the continuity facts
  `continuous_jInvariantFun'` (via `continuousOn_Kfun_clean`) and `jInvariantFun_imagAxis_ne`;
* the lemmas taken from `clean_at_corner` are inlined under fresh (private) names:
  `analyticOnNhd_jInvariantFun_comp` (used once), `not_const_jInvariantFun_comp` (used once) and
  the rectangle-corner argument `clean_at_corner` (used twice, here in the generalised form for an
  arbitrary rectangle that the C-file uses).  Everything else added here is private, so no name in
  it can clash with the surrounding development.

The target `Work.Asymptotics.detourLeftC_mdifferentiableOn_MR` has exactly the requested statement.
-/
import Mathlib
import Submission.Work.Asymptotics.contourLeftDefs
import Submission.Work.Asymptotics.detourLeft_mdifferentiableOn

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

noncomputable section

open UpperHalfPlane Filter Topology MeasureTheory
open scoped Topology Manifold

namespace Work.Asymptotics

/-! ## Inlined inputs replacing the `clean_at_corner` import

`Work.Asymptotics.clean_at_corner` is not imported here (see the module docstring).  The analytic
input it supplies -- `j` is holomorphic and non-constant, hence the lift `w ↦ j(ofComplex w)` is
open -- is restated below, together with the continuity of the horizontal edge parametrisation
which lives in `detourRight_mdifferentiableOn`. -/

/-- The modular `j`-invariant, viewed as a function of `ℍ`, is holomorphic. -/
private lemma detourLeftCMR_mdifferentiable_jInvariantFun :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Work.Kernels.jInvariantFun) :=
  ((ModularFormClass.holo ModularForm.E₄).pow 3).div
    (CuspFormClass.holo CuspForm.discriminant)
    (fun z => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z)

/-- The lift `w ↦ j(ofComplex w)` is analytic on the upper half plane. -/
private lemma detourLeftCMR_analyticOnNhd_jInvariantFun_comp :
    AnalyticOnNhd ℂ (fun w : ℂ => Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im} :=
  (UpperHalfPlane.mdifferentiable_iff.mp detourLeftCMR_mdifferentiable_jInvariantFun).analyticOnNhd
    UpperHalfPlane.isOpen_upperHalfPlaneSet

/-- The lift `w ↦ j(ofComplex w)` is not constant on the upper half plane: `j` is unbounded
along the imaginary axis. -/
private lemma detourLeftCMR_not_const_jInvariantFun_comp :
    ¬ (∃ c : ℂ, ∀ w : ℂ, 0 < w.im →
      Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w) = c) := by
  rintro ⟨c, hc⟩
  obtain ⟨t, ht, hne⟩ := Work.Asymptotics.jInvariantFun_imagAxis_ne c
  refine hne (hc ((t : ℂ) * Complex.I) ?_)
  rw [Complex.mul_im]
  simp [ht]

/-- For `v > 0` the parametrisation `u ↦ u + i v` of a horizontal edge is continuous. -/
private lemma detourLeftCMR_continuous_ofReImT_const (v : ℝ) (hv : 0 < v) :
    Continuous (fun u : ℝ => ofReImT u v) := by
  rw [UpperHalfPlane.isEmbedding_coe.continuous_iff]
  change Continuous fun u : ℝ => ((ofReImT u v : UpperHalfPlane) : ℂ)
  have h_eq : (fun u : ℝ => ((ofReImT u v : UpperHalfPlane) : ℂ)) =
      fun u : ℝ => (u : ℂ) + (v : ℂ) * Complex.I := by
    funext u
    rw [ofReImT_eq u v hv]
  rw [h_eq]
  fun_prop


/-- Continuity of the phase weight `u ↦ phaseWeight r u`. -/
private lemma detourLeftCMR_continuous_phaseWeight (r : ℝ) :
    Continuous (fun u : ℝ => phaseWeight r u) := by
  simp only [phaseWeight]
  fun_prop

/-- Continuity of the gaussian weight `v ↦ gaussWeight r v`. -/
private lemma detourLeftCMR_continuous_gaussWeight (r : ℝ) :
    Continuous (fun v : ℝ => gaussWeight r v) := by
  simp only [gaussWeight]
  fun_prop

/-! ## Cleanliness at the corners of a general rectangle

For an arbitrary rectangle `[u₁,u₂] × [v₁,v₂]` with `v₁ > 0` and an arbitrary ball
`B(τ₀,ε)`, the *open* side cleanliness hypothesis implies cleanliness at the four corners.
This is the generalisation of `Work.Asymptotics.clean_at_corner` (right detour) and of the
private `clean_at_corner_left` of the left-detour file. -/

/-- **The four corners of a rectangle are clean.**  If `hclean` holds on the three open sides of
the rectangle `[u₁,u₂] × [v₁,v₂]`, then for every `τ` in the ball the `j`-invariant of `τ`
differs from that of every corner point `u₀ + i v₀` with `u₀ ∈ {u₁,u₂}`, `v₀ ∈ {v₁,v₂}`. -/
private theorem detourLeftCMR_corner_gen {τ₀ : UpperHalfPlane} {ε u₁ u₂ v₁ v₂ : ℝ}
    (hu : u₁ < u₂) (hv : v₁ < v₂) (hv₁ : 0 < v₁) (hε : 0 < ε)
    (hclean : ∀ (u v : ℝ), 0 < v →
      ((u₁ < u ∧ u < u₂ ∧ (v = v₁ ∨ v = v₂)) ∨ (u = u₁ ∧ v₁ < v ∧ v < v₂)) →
      ∀ τ : UpperHalfPlane, dist τ τ₀ < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (ofReImT u v))
    {u₀ v₀ : ℝ} (hu₀ : u₀ = u₁ ∨ u₀ = u₂) (hv₀ : v₀ = v₁ ∨ v₀ = v₂) :
    ∀ τ : UpperHalfPlane, dist τ τ₀ < ε →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (ofReImT u₀ v₀) := by
  have hv₀pos : 0 < v₀ := by rcases hv₀ with h | h <;> linarith
  intro τ₁ hτ₁ heq
  -- ## The open mapping input
  have hopen : ∀ s ⊆ {w : ℂ | 0 < w.im}, IsOpen s →
      IsOpen ((fun w : ℂ => Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w)) '' s) :=
    (detourLeftCMR_analyticOnNhd_jInvariantFun_comp.is_constant_or_isOpen
      (convex_halfSpace_im_gt 0).isPreconnected).resolve_left
        detourLeftCMR_not_const_jInvariantFun_comp
  -- ## The Euclidean ball `D` around `τ₁` on which the whole ball condition holds
  have hΦcont : Continuous fun w : {w : ℂ // 0 < w.im} =>
      (⟨w.1, w.2⟩ : UpperHalfPlane) :=
    Continuous.upperHalfPlaneMk continuous_subtype_val (fun w => w.2)
  have hψcont : Continuous fun w : {w : ℂ // 0 < w.im} =>
      dist (⟨w.1, w.2⟩ : UpperHalfPlane) τ₀ :=
    hΦcont.dist continuous_const
  have hψ₀ : dist (⟨(τ₁ : ℂ), τ₁.im_pos⟩ : UpperHalfPlane) τ₀ < ε := hτ₁
  have hOpen : IsOpen {w : {w : ℂ // 0 < w.im} |
      dist (⟨w.1, w.2⟩ : UpperHalfPlane) τ₀ < ε} :=
    isOpen_lt hψcont continuous_const
  have hψmem : (⟨(τ₁ : ℂ), τ₁.im_pos⟩ : {w : ℂ // 0 < w.im}) ∈
      {w : {w : ℂ // 0 < w.im} |
        dist (⟨w.1, w.2⟩ : UpperHalfPlane) τ₀ < ε} := hψ₀
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.mem_nhds_iff.1 (hOpen.mem_nhds hψmem)
  set δ : ℝ := min δ₁ τ₁.im / 2 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact div_pos (lt_min hδ₁pos τ₁.im_pos) two_pos
  have hδle₁ : δ ≤ δ₁ := by
    rw [hδdef]; have := min_le_left δ₁ τ₁.im; linarith
  have hδltim : δ < τ₁.im := by
    rw [hδdef]; have := min_le_right δ₁ τ₁.im; linarith
  set D : Set ℂ := Metric.ball (τ₁ : ℂ) δ with hDdef
  have hδltim' : δ < (τ₁ : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact hδltim
  have hDsub : D ⊆ {w : ℂ | 0 < w.im} := by
    intro w hw
    have h1 : ‖w - (τ₁ : ℂ)‖ < δ := by simpa [hDdef, Metric.mem_ball, dist_eq_norm] using hw
    have h2 : |(w - (τ₁ : ℂ)).im| ≤ ‖w - (τ₁ : ℂ)‖ := Complex.abs_im_le_norm _
    have h5 : |(w - (τ₁ : ℂ)).im| < δ := lt_of_le_of_lt h2 h1
    have h6 : -δ < w.im - (τ₁ : ℂ).im := by
      have h := (abs_lt.mp h5).1
      have h3 : (w - (τ₁ : ℂ)).im = w.im - (τ₁ : ℂ).im := by simp
      rwa [h3] at h
    have h8 : 0 < (τ₁ : ℂ).im - δ := by linarith
    show 0 < w.im
    linarith
  -- the image of `D` is a neighbourhood of `j τ₁`
  have hGD : ((fun w : ℂ => Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w)) '' D)
      ∈ 𝓝 (Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (τ₁ : ℂ))) := by
    refine (hopen D hDsub Metric.isOpen_ball).mem_nhds ⟨(τ₁ : ℂ), ?_, rfl⟩
    simp [hDdef, Metric.mem_ball, hδpos]
  obtain ⟨η, hηpos, hη⟩ := Metric.mem_nhds_iff.1 hGD
  -- ## The adjacent edge meets the preimage of `ball (j τ₁) η`
  have hofReImT_cont : Continuous (fun t : ℝ => ofReImT t v₀) :=
    detourLeftCMR_continuous_ofReImT_const v₀ hv₀pos
  have hφcont : Continuous fun t : ℝ =>
      Work.Kernels.jInvariantFun (ofReImT t v₀) :=
    continuous_jInvariantFun'.comp hofReImT_cont
  have hu₀cl : u₀ ∈ closure (Set.Ioo u₁ u₂) := by
    rw [closure_Ioo (ne_of_lt hu)]
    rw [Set.mem_Icc]
    rcases hu₀ with h | h <;> rw [h] <;> constructor <;> linarith
  have hpre : ((fun t : ℝ => Work.Kernels.jInvariantFun (ofReImT t v₀)) ⁻¹'
      Metric.ball (Work.Kernels.jInvariantFun (ofReImT u₀ v₀)) η) ∈ 𝓝 u₀ :=
    hφcont.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hηpos)
  obtain ⟨t, htball, htIoo⟩ := (mem_closure_iff_nhds.1 hu₀cl) _ hpre
  rw [Set.mem_Ioo] at htIoo
  -- ## The contradiction
  have hτ₁c : UpperHalfPlane.ofComplex (τ₁ : ℂ) = τ₁ :=
    (UpperHalfPlane.ofComplex_apply_of_im_pos τ₁.im_pos).trans (UpperHalfPlane.ext rfl)
  have hzmem : Work.Kernels.jInvariantFun (ofReImT t v₀) ∈
      ((fun w : ℂ => Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w)) '' D) := by
    refine hη ?_
    rw [hτ₁c, heq]
    exact htball
  obtain ⟨w, hwD, hwG⟩ := hzmem
  have hwpos : 0 < w.im := hDsub hwD
  have hwball : (⟨w, hwpos⟩ : {w : ℂ // 0 < w.im}) ∈ Metric.ball
      (⟨(τ₁ : ℂ), τ₁.im_pos⟩ : {w : ℂ // 0 < w.im}) δ₁ := by
    have h1 : ‖w - (τ₁ : ℂ)‖ < δ := by simpa [hDdef, Metric.mem_ball, dist_eq_norm] using hwD
    rw [Metric.mem_ball]
    show dist (⟨w, hwpos⟩ : {w : ℂ // 0 < w.im}) ⟨(τ₁ : ℂ), τ₁.im_pos⟩ < δ₁
    rw [Subtype.dist_eq]
    rw [dist_eq_norm]
    exact lt_of_lt_of_le h1 hδle₁
  have hwG' : Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w)
      = Work.Kernels.jInvariantFun (ofReImT t v₀) := hwG
  have hjw : Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w)
      = Work.Kernels.jInvariantFun (⟨w, hwpos⟩ : UpperHalfPlane) := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hwpos]
  exact (hclean t v₀ hv₀pos (Or.inl ⟨htIoo.1, htIoo.2, hv₀⟩) ⟨w, hwpos⟩ (hδ₁ hwball))
    (by rw [← hjw, hwG'])

/-- **The closed sides of a rectangle are clean.**  The open-side cleanliness hypothesis implies
cleanliness on the closed three sides (the four corners included). -/
private theorem detourLeftCMR_closedEdge_gen {τ₀ : UpperHalfPlane} {ε u₁ u₂ v₁ v₂ : ℝ}
    (hu : u₁ < u₂) (hv : v₁ < v₂) (hv₁ : 0 < v₁) (hε : 0 < ε)
    (hclean : ∀ (u v : ℝ), 0 < v →
      ((u₁ < u ∧ u < u₂ ∧ (v = v₁ ∨ v = v₂)) ∨ (u = u₁ ∧ v₁ < v ∧ v < v₂)) →
      ∀ τ : UpperHalfPlane, dist τ τ₀ < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (ofReImT u v)) :
    ∀ (τ : UpperHalfPlane), dist τ τ₀ < ε →
      ∀ (u v : ℝ), 0 < v →
        ((u₁ ≤ u ∧ u ≤ u₂ ∧ (v = v₁ ∨ v = v₂)) ∨ (u = u₁ ∧ v₁ ≤ v ∧ v ≤ v₂)) →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (ofReImT u v) := by
  intro τ hτ u v hv0 hdisj
  rcases hdisj with ⟨hu1', hu2', hv'⟩ | ⟨hu_eq, hva, hvb⟩
  · by_cases huc : u₁ < u ∧ u < u₂
    · exact hclean u v hv0 (Or.inl ⟨huc.1, huc.2, hv'⟩) τ hτ
    · have hu'' : u = u₁ ∨ u = u₂ := by
        rcases lt_or_eq_of_le hu1' with h | h
        · exact Or.inr (le_antisymm hu2' (le_of_not_gt fun hlt => huc ⟨h, hlt⟩))
        · exact Or.inl h.symm
      exact detourLeftCMR_corner_gen (u₁ := u₁) (u₂ := u₂) (v₁ := v₁) (v₂ := v₂)
        (u₀ := u) (v₀ := v) hu hv hv₁ hε hclean hu'' hv' τ hτ
  · by_cases hvc : v₁ < v ∧ v < v₂
    · exact hclean u v hv0 (Or.inr ⟨hu_eq, hvc.1, hvc.2⟩) τ hτ
    · have hv'' : v = v₁ ∨ v = v₂ := by
        rcases lt_or_eq_of_le hva with h | h
        · exact Or.inr (le_antisymm hvb (le_of_not_gt fun hlt => hvc ⟨h, hlt⟩))
        · exact Or.inl h.symm
      exact detourLeftCMR_corner_gen (u₁ := u₁) (u₂ := u₂) (v₁ := v₁) (v₂ := v₂)
        (u₀ := u) (v₀ := v) hu hv hv₁ hε hclean (Or.inl hu_eq) hv'' τ hτ

/-! ## Continuity helpers for the clamped contour parametrisations -/

/-- `v ↦ ofReImT a (max v c)` is continuous for `c > 0` (the parametrisation of a vertical
edge, extended to all of `ℝ` by clamping so that it never leaves the upper half plane). -/
private lemma continuous_ofReImT_fst_max (a c : ℝ) (hc : 0 < c) :
    Continuous (fun v : ℝ => ofReImT a (max v c)) := by
  rw [UpperHalfPlane.isEmbedding_coe.continuous_iff]
  have h_eq : (fun v : ℝ => ((ofReImT a (max v c) : UpperHalfPlane) : ℂ))
      = fun v : ℝ => (a : ℂ) + ((max v c : ℝ) : ℂ) * Complex.I := by
    funext v
    exact ofReImT_coe a (max v c) (lt_of_lt_of_le hc (le_max_right _ _))
  rw [show (UpperHalfPlane.coe ∘ fun v : ℝ => ofReImT a (max v c))
      = fun v : ℝ => ((ofReImT a (max v c) : UpperHalfPlane) : ℂ) from rfl, h_eq]
  fun_prop

/-- The clamping is invisible in the range of the parameter. -/
private lemma ofReImT_max_eq (a c v : ℝ) (hv : c ≤ v) : ofReImT a (max v c) = ofReImT a v := by
  rw [max_eq_left hv]

/-! ## Local boundedness of `Kfun` along a clean compact contour -/

/-- **`Kfun` is locally uniformly bounded along a clean compact contour.**  Given cleanliness on
the closed contour, compactness of the contour together with the joint continuity of `Kfun` off
the coincidence divisor gives a bound in a neighbourhood of every point of the ball. -/
private lemma localBound_Kfun_on_clean_compact (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {τ₀ : UpperHalfPlane} {ε : ℝ} (hε : 0 < ε)
    {S : Set UpperHalfPlane} (hS : IsCompact S)
    (hcleanS : ∀ z ∈ S, ∀ τ : UpperHalfPlane, dist τ τ₀ < ε →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    ∀ τ₁ : UpperHalfPlane, dist τ₁ τ₀ < ε → ∃ M r : ℝ, 0 < r ∧
      ∀ z ∈ S, ∀ τ : UpperHalfPlane, dist τ τ₁ < r →
        ‖Work.Kernels.Kfun ℓ d τ z‖ ≤ M := by
  intro τ₁ hτ₁
  set r : ℝ := (ε - dist τ₁ τ₀) / 2 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hsub : (Metric.closedBall τ₁ r ×ˢ S) ⊆
      {p : UpperHalfPlane × UpperHalfPlane |
        Work.Kernels.jInvariantFun p.1 ≠ Work.Kernels.jInvariantFun p.2} := by
    rintro ⟨τ, z⟩ ⟨hτ, hz⟩
    have h2 : dist τ τ₁ ≤ r := Metric.mem_closedBall.mp hτ
    have hlt : dist τ τ₀ < ε := by
      calc dist τ τ₀ ≤ dist τ τ₁ + dist τ₁ τ₀ := dist_triangle _ _ _
        _ ≤ r + dist τ₁ τ₀ := by linarith
        _ < ε := by rw [hrdef]; linarith
    exact hcleanS z hz τ hlt
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
    ((isCompact_closedBall τ₁ r).prod hS) ((continuousOn_Kfun_clean ℓ d hd).mono hsub)
  exact ⟨M, r, hrpos, fun z hz τ hτ =>
    hM (τ, z) ⟨Metric.mem_closedBall.mpr (le_of_lt hτ), hz⟩⟩

/-! ## The three single-edge integrals as named functions -/

/-- The integral along a horizontal edge at height `h` (from `u = -ξ` to `u = 0`). -/
private def edgeHCTerm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r h ξ : ℝ) :
    UpperHalfPlane → ℂ :=
  fun τ => ∫ u in Set.Ioo (0 : ℝ) ξ, edgeH ℓ d r τ (-u) h

/-- The integral along the vertical edge `u = -ξ` (from `v = c-A` to `v = c+A`). -/
private def edgeVCTerm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r c A ξ : ℝ) :
    UpperHalfPlane → ℂ :=
  fun τ => ∫ v in Set.Ioo (c - A) (c + A), edgeV ℓ d r τ (-ξ) v

/-- The horizontal-edge integrand of the engine agrees with `edgeH`. -/
private lemma edgeHC_eq_Kfun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r h ξ : ℝ) :
    (fun τ : UpperHalfPlane => ∫ u in Set.Ioo (0 : ℝ) ξ, edgeH ℓ d r τ (-u) h)
      = fun τ : UpperHalfPlane => ∫ u in Set.Ioo (0 : ℝ) ξ,
          Work.Kernels.Kfun ℓ d τ (ofReImT (-u) h)
            * ((phaseWeight r (-u) * gaussWeight r h) / Complex.I) := by
  funext τ
  refine setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
  simp only [edgeH]
  ring

/-- The vertical-edge integrand of the engine agrees with `edgeV`. -/
private lemma edgeVC_eq_Kfun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r c A ξ : ℝ) :
    (fun τ : UpperHalfPlane => ∫ v in Set.Ioo (c - A) (c + A),
        Work.Kernels.Kfun ℓ d τ (ofReImT (-ξ) (max v (c - A)))
          * (phaseWeight r (-ξ) * gaussWeight r v))
      = fun τ : UpperHalfPlane => ∫ v in Set.Ioo (c - A) (c + A), edgeV ℓ d r τ (-ξ) v := by
  funext τ
  refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
  simp only [edgeV]
  rw [ofReImT_max_eq (-ξ) (c - A) v (le_of_lt hv.1)]

/-- `detourLeftC` is the corrected combination of the three single-edge integrals. -/
private lemma detourLeftC_eq_terms (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r c A ξ : ℝ) :
    (fun τ : UpperHalfPlane => detourLeftC ℓ d r c A ξ τ)
      = - edgeHCTerm ℓ d r (c - A) ξ + edgeVCTerm ℓ d r c A ξ + edgeHCTerm ℓ d r (c + A) ξ := by
  funext τ
  simp only [detourLeftC, edgeHCTerm, edgeVCTerm, Pi.neg_apply, Pi.add_apply]

/-! ## The target -/

theorem detourLeftC_mdifferentiableOn_MR (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {r c A ξ ε t₀ : ℝ} (ht₀ : 0 < t₀) (hA : 0 < A) (hξ : 0 < ξ)
    (hcA : 0 < c - A) (hε : 0 < ε)
    (hclean : ∀ (u v : ℝ), 0 < v →
      ((-ξ < u ∧ u < 0 ∧ (v = c - A ∨ v = c + A)) ∨ (u = -ξ ∧ c - A < v ∧ v < c + A)) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε →
        Work.Kernels.jInvariantFun τ
          ≠ Work.Kernels.jInvariantFun (Work.Asymptotics.ofReImT u v)) :
    MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ => Work.Asymptotics.detourLeftC ℓ d r c A ξ τ)
      (Metric.ball (Work.Asymptotics.onePlusI t₀ ht₀) ε) := by
  -- closed-side cleanliness, obtained from the open-side hypothesis
  have hcl : ∀ (u v : ℝ), 0 < v →
      ((-ξ ≤ u ∧ u ≤ 0 ∧ (v = c - A ∨ v = c + A))
        ∨ (u = -ξ ∧ c - A ≤ v ∧ v ≤ c + A)) →
      ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (ofReImT u v) :=
    fun u v hv hdisj τ hτ =>
      detourLeftCMR_closedEdge_gen (τ₀ := onePlusI t₀ ht₀)
        (u₁ := -ξ) (u₂ := 0) (v₁ := c - A) (v₂ := c + A)
        (by linarith : (-ξ : ℝ) < 0) (by linarith : c - A < c + A) hcA hε hclean
        τ hτ u v hv hdisj
  have hcA₂ : 0 < c + A := by linarith
  have hlt : c - A ≤ c + A := by linarith
  -- ## The three edge terms
  have hterm1 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (edgeHCTerm ℓ d r (c - A) ξ) (Metric.ball (onePlusI t₀ ht₀) ε) := by
    change MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ => ∫ u in Set.Ioo (0 : ℝ) ξ, edgeH ℓ d r τ (-u) (c - A))
      (Metric.ball (onePlusI t₀ ht₀) ε)
    have hZ : Continuous (fun u : ℝ => ofReImT (-u) (c - A)) :=
      (detourLeftCMR_continuous_ofReImT_const (c - A) hcA).comp continuous_neg
    have hκ : Continuous (fun u : ℝ =>
        (phaseWeight r (-u) * gaussWeight r (c - A)) / Complex.I) :=
      Continuous.div_const (Continuous.mul ((detourLeftCMR_continuous_phaseWeight r).comp continuous_neg)
        continuous_const) _
    have hS : IsCompact ((fun u : ℝ => ofReImT (-u) (c - A)) '' Set.Icc (0 : ℝ) ξ) :=
      isCompact_Icc.image (hZ)
    have hcleanS : ∀ z ∈ ((fun u : ℝ => ofReImT (-u) (c - A)) '' Set.Icc (0 : ℝ) ξ),
        ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
          Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
      rintro z ⟨u, hu, rfl⟩ τ hτ
      exact hcl (-u) (c - A) hcA
        (Or.inl ⟨by linarith [hu.2], by linarith [hu.1], Or.inl rfl⟩) τ hτ
    have hb := localBound_Kfun_on_clean_compact ℓ d hd hε hS hcleanS
    have h := mdifferentiableOn_paramIntegral_Kfun ℓ d hd (a := 0) (b := ξ) hξ.le hZ hκ hε
      (fun u hu τ hτ => by
        obtain ⟨hu1, hu2⟩ := hu
        exact hcl (-u) (c - A) hcA
          (Or.inl ⟨by linarith, by linarith, Or.inl rfl⟩) τ hτ)
      (fun τ₁ hτ₁ => by
        obtain ⟨M, rr, hrr, hM⟩ := hb τ₁ hτ₁
        exact ⟨M, rr, hrr, fun u hu τ hτ => hM (ofReImT (-u) (c - A)) ⟨u, hu, rfl⟩ τ hτ⟩)
    rw [← edgeHC_eq_Kfun ℓ d r (c - A) ξ] at h
    exact h
  have hterm2 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (edgeVCTerm ℓ d r c A ξ) (Metric.ball (onePlusI t₀ ht₀) ε) := by
    change MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ => ∫ v in Set.Ioo (c - A) (c + A), edgeV ℓ d r τ (-ξ) v)
      (Metric.ball (onePlusI t₀ ht₀) ε)
    have hZ : Continuous (fun v : ℝ => ofReImT (-ξ) (max v (c - A))) :=
      continuous_ofReImT_fst_max (-ξ) (c - A) hcA
    have hκ : Continuous (fun v : ℝ => phaseWeight r (-ξ) * gaussWeight r v) :=
      Continuous.mul continuous_const (detourLeftCMR_continuous_gaussWeight r)
    have hS : IsCompact ((fun v : ℝ => ofReImT (-ξ) v) '' Set.Icc (c - A) (c + A)) := by
      have hcont : ContinuousOn (fun v : ℝ => ofReImT (-ξ) v) (Set.Icc (c - A) (c + A)) :=
        (continuous_ofReImT_fst_max (-ξ) (c - A) hcA).continuousOn.congr
          (fun v hv => (ofReImT_max_eq (-ξ) (c - A) v hv.1).symm)
      exact isCompact_Icc.image_of_continuousOn hcont
    have hcleanS : ∀ z ∈ ((fun v : ℝ => ofReImT (-ξ) v) '' Set.Icc (c - A) (c + A)),
        ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
          Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
      rintro z ⟨v, hv, rfl⟩ τ hτ
      exact hcl (-ξ) v (lt_of_lt_of_le hcA hv.1) (Or.inr ⟨rfl, hv.1, hv.2⟩) τ hτ
    have hb := localBound_Kfun_on_clean_compact ℓ d hd hε hS hcleanS
    have h := mdifferentiableOn_paramIntegral_Kfun ℓ d hd (a := c - A) (b := c + A) hlt hZ hκ hε
      (fun v hv τ hτ => by
        rw [ofReImT_max_eq (-ξ) (c - A) v hv.1]
        exact hcl (-ξ) v (lt_of_lt_of_le hcA hv.1) (Or.inr ⟨rfl, hv.1, hv.2⟩) τ hτ)
      (fun τ₁ hτ₁ => by
        obtain ⟨M, rr, hrr, hM⟩ := hb τ₁ hτ₁
        exact ⟨M, rr, hrr, fun v hv τ hτ => by
          rw [ofReImT_max_eq (-ξ) (c - A) v hv.1]
          exact hM (ofReImT (-ξ) v) ⟨v, hv, rfl⟩ τ hτ⟩)
    rw [edgeVC_eq_Kfun ℓ d r c A ξ] at h
    exact h
  have hterm3 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (edgeHCTerm ℓ d r (c + A) ξ) (Metric.ball (onePlusI t₀ ht₀) ε) := by
    change MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ => ∫ u in Set.Ioo (0 : ℝ) ξ, edgeH ℓ d r τ (-u) (c + A))
      (Metric.ball (onePlusI t₀ ht₀) ε)
    have hZ : Continuous (fun u : ℝ => ofReImT (-u) (c + A)) :=
      (detourLeftCMR_continuous_ofReImT_const (c + A) hcA₂).comp continuous_neg
    have hκ : Continuous (fun u : ℝ =>
        (phaseWeight r (-u) * gaussWeight r (c + A)) / Complex.I) :=
      Continuous.div_const (Continuous.mul ((detourLeftCMR_continuous_phaseWeight r).comp continuous_neg)
        continuous_const) _
    have hS : IsCompact ((fun u : ℝ => ofReImT (-u) (c + A)) '' Set.Icc (0 : ℝ) ξ) :=
      isCompact_Icc.image hZ
    have hcleanS : ∀ z ∈ ((fun u : ℝ => ofReImT (-u) (c + A)) '' Set.Icc (0 : ℝ) ξ),
        ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
          Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
      rintro z ⟨u, hu, rfl⟩ τ hτ
      exact hcl (-u) (c + A) hcA₂
        (Or.inl ⟨by linarith [hu.2], by linarith [hu.1], Or.inr rfl⟩) τ hτ
    have hb := localBound_Kfun_on_clean_compact ℓ d hd hε hS hcleanS
    have h := mdifferentiableOn_paramIntegral_Kfun ℓ d hd (a := 0) (b := ξ) hξ.le hZ hκ hε
      (fun u hu τ hτ => by
        obtain ⟨hu1, hu2⟩ := hu
        exact hcl (-u) (c + A) hcA₂
          (Or.inl ⟨by linarith, by linarith, Or.inr rfl⟩) τ hτ)
      (fun τ₁ hτ₁ => by
        obtain ⟨M, rr, hrr, hM⟩ := hb τ₁ hτ₁
        exact ⟨M, rr, hrr, fun u hu τ hτ => hM (ofReImT (-u) (c + A)) ⟨u, hu, rfl⟩ τ hτ⟩)
    rw [← edgeHC_eq_Kfun ℓ d r (c + A) ξ] at h
    exact h
  -- ## Assembly
  have hsum : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (- edgeHCTerm ℓ d r (c - A) ξ + edgeVCTerm ℓ d r c A ξ + edgeHCTerm ℓ d r (c + A) ξ)
      (Metric.ball (onePlusI t₀ ht₀) ε) :=
    (hterm1.neg.add hterm2).add hterm3
  rw [detourLeftC_eq_terms ℓ d r c A ξ]
  exact hsum

end Work.Asymptotics
