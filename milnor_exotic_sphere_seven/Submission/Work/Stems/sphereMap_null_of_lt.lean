import Mathlib
import Submission.Work.Stems.sphereMissesPoint

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.Stems.sphereMap_null_of_lt`

A continuous map of spheres `S^j → Sⁿ` with `j < n` is null-homotopic relative to any base point at
which it takes the value of the constant map.

The proof is the classical "general position" argument: approximate `f` by a smooth map `g` (keeping
the value at the base point), a smooth map `S^j → Sⁿ` with `j < n` is never surjective (a
measure-theoretic Sard argument, `exists_sphereMap_ne_of_contMDiff` below), and a map missing a point
is null-homotopic (`Work.Stems.homotopicRel_const_of_misses'`).
-/

open scoped Manifold ContDiff
open Metric MeasureTheory
open scoped Topology

namespace Work.Stems

noncomputable section

/-! ## General position: a smooth map `S^j → Sⁿ` with `j < n` is not surjective -/

/-- **A smooth map `S^j → Sⁿ` with `j < n` misses a point.**

This is the geometric core of the general-position argument.  Writing `Sⁱ` for
`Work.Stems.sphere i`: the stereographic chart at a point `w₀` parametrises `S^j` minus one point by
`EuclideanSpace ℝ (Fin j)`, giving a smooth `γ : ℝ^j → ℝⁿ⁺¹`.  The "cone" map
`Γ : ℝ^j × ℝ → ℝⁿ⁺¹`, `Γ (u,s) = s • γ u` then has image `ℝ·γ(ℝ^j)`; if `g` were surjective this
would be all of `ℝⁿ⁺¹`.  Composing `Γ` with a linear surjection `π : ℝⁿ⁺¹ → ℝ^j × ℝ` (which exists
since `j < n`) gives a map `Ξ : ℝⁿ⁺¹ → ℝⁿ⁺¹` whose differential has rank `≤ j+1 < n+1` (it factors
through `ℝ^j × ℝ`), hence determinant zero; Sard's lemma then forces `volume (range Ξ) = 0`,
contradicting `range Ξ = univ`. -/
theorem exists_sphereMap_ne_of_contMDiff {j n : ℕ} (hjn : j < n)
    (g : C(sphere j, sphere n)) (hg : ContMDiff (𝓡 j) (𝓡 n) ∞ g) :
    ∃ y : sphere n, ∀ x : sphere j, g x ≠ y := by
  haveI hFj : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (j+1))) = j + 1) := ⟨by simp⟩
  haveI hFn : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n + 1) := ⟨by simp⟩
  by_contra hcon
  push_neg at hcon
  -- a base point of `S^j`, and the point it will be convenient to omit
  let w₀ : sphere j :=
    ⟨EuclideanSpace.basisFun (Fin (j+1)) ℝ ⟨0, by omega⟩, by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      exact OrthonormalBasis.norm_eq_one _ _⟩
  let p : sphere j := -w₀
  have hchart : chartAt (EuclideanSpace ℝ (Fin j)) w₀ = stereographic' j (-w₀) := rfl
  -- the chart inverse, a parametrisation of `S^j ∖ {p}`
  let σ : EuclideanSpace ℝ (Fin j) → sphere j :=
    fun u => (chartAt (EuclideanSpace ℝ (Fin j)) w₀).symm u
  have hσcont : ContMDiff (𝓡 j) (𝓡 j) ∞ σ := by
    have h : ContMDiffOn (𝓡 j) (𝓡 j) ∞ (fun u => (chartAt (EuclideanSpace ℝ (Fin j)) w₀).symm u)
        (chartAt (EuclideanSpace ℝ (Fin j)) w₀).target :=
      contMDiffOn_chart_symm (I := 𝓡 j) (x := w₀)
    rw [show (chartAt (EuclideanSpace ℝ (Fin j)) w₀).target = Set.univ from by
      rw [hchart, stereographic'_target]] at h
    exact contMDiffOn_univ.mp h
  have hσrange : ∀ y : sphere j, y ≠ p → ∃ u : EuclideanSpace ℝ (Fin j), σ u = y := by
    intro y hy
    refine ⟨chartAt (EuclideanSpace ℝ (Fin j)) w₀ y, ?_⟩
    have hmem : y ∈ (chartAt (EuclideanSpace ℝ (Fin j)) w₀).source := by
      rw [hchart, stereographic'_source]
      simpa [p] using hy
    exact (chartAt (EuclideanSpace ℝ (Fin j)) w₀).left_inv hmem
  -- the smooth map `γ = g ∘ σ`
  let γ : EuclideanSpace ℝ (Fin j) → EuclideanSpace ℝ (Fin (n+1)) :=
    fun u => (g (σ u) : EuclideanSpace ℝ (Fin (n+1)))
  have hgcoe : ContMDiff (𝓡 j) (𝓘(ℝ, EuclideanSpace ℝ (Fin (n+1)))) ∞
      (fun x : sphere j => (g x : EuclideanSpace ℝ (Fin (n+1)))) :=
    (contMDiff_coe_sphere (n := n) (m := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp hg
  have hγmd : ContMDiff (𝓡 j) (𝓘(ℝ, EuclideanSpace ℝ (Fin (n+1)))) ∞ γ := hgcoe.comp hσcont
  have hγ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ := by
    have h1 : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin j)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n+1)))) ∞ γ Set.univ :=
      contMDiffOn_univ.mpr hγmd
    exact contDiffOn_univ.mp (contMDiffOn_iff_contDiffOn.mp h1)
  have hγrange : ∀ y : sphere n, y ≠ g p → ∃ u : EuclideanSpace ℝ (Fin j), γ u = y := by
    intro y hy
    obtain ⟨x, hx⟩ := hcon y
    have hxne : x ≠ p := by intro h; exact hy (by rw [← hx, h])
    obtain ⟨u, hu⟩ := hσrange x hxne
    refine ⟨u, ?_⟩
    show (g (σ u) : EuclideanSpace ℝ (Fin (n+1))) = (y : EuclideanSpace ℝ (Fin (n+1)))
    rw [hu, hx]
  -- the cone over `γ`
  let Γ : EuclideanSpace ℝ (Fin j) × ℝ → EuclideanSpace ℝ (Fin (n+1)) := fun q => q.2 • γ q.1
  have hΓ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Γ :=
    contDiff_snd.smul (hγ.comp contDiff_fst)
  -- a linear surjection onto the first `j+1` coordinates
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) =
      Module.finrank ℝ ((EuclideanSpace ℝ (Fin j) × ℝ) × EuclideanSpace ℝ (Fin (n-j))) := by
    simp only [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self]
    omega
  let e : EuclideanSpace ℝ (Fin (n+1)) ≃L[ℝ]
      ((EuclideanSpace ℝ (Fin j) × ℝ) × EuclideanSpace ℝ (Fin (n-j))) :=
    Classical.choice (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq hdim)
  let π : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] (EuclideanSpace ℝ (Fin j) × ℝ) :=
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin j) × ℝ) (EuclideanSpace ℝ (Fin (n-j)))).comp
      (e : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] _)
  let Ξ : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) := fun w => Γ (π w)
  have hΞ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ξ := hΓ.comp π.contDiff
  -- ## the differential of `Ξ` has determinant zero
  have hdet : ∀ w, (fderiv ℝ Ξ w).det = 0 := by
    intro w
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot]
    intro hbot
    have hne : ((0 : EuclideanSpace ℝ (Fin j) × ℝ),
        EuclideanSpace.single (⟨0, by omega⟩ : Fin (n-j)) (1:ℝ)) ≠ 0 := by
      intro h
      have h2 := congrArg (fun q => q.2) h
      simp only [Prod.snd_zero] at h2
      have h3 : ‖EuclideanSpace.single (⟨0, by omega⟩ : Fin (n-j)) (1:ℝ)‖ = 1 := by
        rw [show EuclideanSpace.single (⟨0, by omega⟩ : Fin (n-j)) (1:ℝ)
          = PiLp.single 2 (⟨0, by omega⟩ : Fin (n-j)) (1:ℝ) from rfl]
        rw [PiLp.norm_single]; norm_num
      rw [h2, norm_zero] at h3
      norm_num at h3
    have hv0 : e.symm ((0 : EuclideanSpace ℝ (Fin j) × ℝ),
        EuclideanSpace.single (⟨0, by omega⟩ : Fin (n-j)) (1:ℝ)) ≠ 0 := by
      intro h
      exact hne (by rw [← e.symm.injective.eq_iff, h, map_zero])
    have hker : (fderiv ℝ Ξ w) (e.symm ((0 : EuclideanSpace ℝ (Fin j) × ℝ),
        EuclideanSpace.single (⟨0, by omega⟩ : Fin (n-j)) (1:ℝ))) = 0 := by
      have hfd : fderiv ℝ Ξ w = (fderiv ℝ Γ (π w)).comp π := by
        show fderiv ℝ (fun w => Γ (π w)) w = _
        exact (((hΓ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp w
          π.hasFDerivAt).fderiv
      rw [hfd, ContinuousLinearMap.comp_apply]
      have hπ0 : π (e.symm ((0 : EuclideanSpace ℝ (Fin j) × ℝ),
          EuclideanSpace.single (⟨0, by omega⟩ : Fin (n-j)) (1:ℝ))) = 0 := by simp [π]
      rw [hπ0, map_zero]
    have hmem : e.symm ((0 : EuclideanSpace ℝ (Fin j) × ℝ),
        EuclideanSpace.single (⟨0, by omega⟩ : Fin (n-j)) (1:ℝ)) ∈
        LinearMap.ker (fderiv ℝ Ξ w : EuclideanSpace ℝ (Fin (n+1)) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin (n+1))) := by
      rw [LinearMap.mem_ker]; exact hker
    rw [hbot] at hmem
    exact hv0 hmem
  -- ## Sard: the image of `Ξ` has measure zero
  have hsard : volume (Ξ '' Set.univ) = 0 := by
    refine MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume)
      (s := Set.univ) (f := Ξ) (f' := fun w => fderiv ℝ Ξ w) ?_ ?_
    · intro w _
      exact ((hΞ.differentiable (by simp)).differentiableAt).hasFDerivAt.hasFDerivWithinAt
    · intro w _; exact hdet w
  -- ## if `g` were surjective the image would be everything
  have himage : ∀ z : EuclideanSpace ℝ (Fin (n+1)), ∃ w, Ξ w = z := by
    intro z
    by_cases hz : z = 0
    · subst hz
      refine ⟨e.symm ((0, 0), 0), ?_⟩
      simp [Ξ, Γ, π]
    · let ζ : sphere n := ⟨(‖z‖)⁻¹ • z, by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_nonneg (norm_nonneg z)]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)⟩
      have hζz : (‖z‖) • (ζ : EuclideanSpace ℝ (Fin (n+1))) = z := by
        show (‖z‖) • ((‖z‖)⁻¹ • z) = z
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
      by_cases hcase : ζ = g p
      · have hneζ : (-ζ : sphere n) ≠ g p := by
          intro h
          have h2 : (-ζ : sphere n) = ζ := by rw [h, hcase]
          have h4 : -(ζ : EuclideanSpace ℝ (Fin (n+1))) = (ζ : EuclideanSpace ℝ (Fin (n+1))) :=
            congrArg (fun t : sphere n => (t : EuclideanSpace ℝ (Fin (n+1)))) h2
          have h6 : (ζ : EuclideanSpace ℝ (Fin (n+1))) + (ζ : EuclideanSpace ℝ (Fin (n+1))) = 0 := by
            have h6' := neg_add_cancel (ζ : EuclideanSpace ℝ (Fin (n+1)))
            rw [h4] at h6'
            exact h6'
          have h7 : (ζ : EuclideanSpace ℝ (Fin (n+1))) = 0 := by
            have h8 : (2:ℝ) • (ζ : EuclideanSpace ℝ (Fin (n+1))) = 0 := by rw [two_smul]; exact h6
            exact (smul_eq_zero.mp h8).resolve_left (by norm_num)
          have h5 : ‖(ζ : EuclideanSpace ℝ (Fin (n+1)))‖ = 1 := norm_eq_of_mem_sphere ζ
          rw [h7, norm_zero] at h5
          norm_num at h5
        obtain ⟨u, hu⟩ := hγrange (-ζ) hneζ
        refine ⟨e.symm (((u, -‖z‖)), (0 : EuclideanSpace ℝ (Fin (n-j)))), ?_⟩
        show Γ (π (e.symm (((u, -‖z‖)), 0))) = z
        rw [show π (e.symm ((((u, -‖z‖), 0) : (EuclideanSpace ℝ (Fin j) × ℝ) ×
            EuclideanSpace ℝ (Fin (n-j))))) = ((u, -‖z‖) : EuclideanSpace ℝ (Fin j) × ℝ) from by
          simp [π]]
        show (-‖z‖) • γ u = z
        rw [hu]
        rw [show ((-ζ : sphere n) : EuclideanSpace ℝ (Fin (n+1))) =
          -(ζ : EuclideanSpace ℝ (Fin (n+1))) from rfl, smul_neg, neg_smul, neg_neg, hζz]
      · obtain ⟨u, hu⟩ := hγrange ζ hcase
        refine ⟨e.symm (((u, ‖z‖)), (0 : EuclideanSpace ℝ (Fin (n-j)))), ?_⟩
        show Γ (π (e.symm (((u, ‖z‖)), 0))) = z
        rw [show π (e.symm ((((u, ‖z‖), 0) : (EuclideanSpace ℝ (Fin j) × ℝ) ×
            EuclideanSpace ℝ (Fin (n-j))))) = ((u, ‖z‖) : EuclideanSpace ℝ (Fin j) × ℝ) from by
          simp [π]]
        show (‖z‖) • γ u = z
        rw [hu, hζz]
  -- ## contradiction: `ℝⁿ⁺¹` has measure zero
  have hrange : Set.range Ξ = Set.univ :=
    Set.eq_univ_of_forall (fun z => Set.mem_range.mpr (himage z))
  have hzero : volume (Set.range Ξ) = 0 := by
    rw [← Set.image_univ]; exact hsard
  rw [hrange] at hzero
  have hpos : 0 < volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n+1))) 1) :=
    measure_ball_pos volume 0 one_pos
  have hle : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n+1))) 1)
      ≤ volume (Set.univ : Set (EuclideanSpace ℝ (Fin (n+1)))) := measure_mono (Set.subset_univ _)
  rw [hzero] at hle
  exact absurd hle (not_le.mpr hpos)


/-! ## Maps at distance `< 1` are homotopic relative to a set on which they agree -/

open scoped unitInterval in
/-- Two maps `X → Sⁿ` that are pointwise at distance `< 1` and agree on a set `S` are homotopic
relative to `S`: the straight-line homotopy in the ambient `ℝⁿ⁺¹` never passes through the origin
and is radially projected back to the sphere. -/
theorem closeMaps_homotopicRel_aux {X : Type*} [TopologicalSpace X] (n : ℕ)
    (f g : C(X, sphere n)) (S : Set X) (hdist : ∀ x, dist (f x) (g x) < 1)
    (hS : ∀ x ∈ S, f x = g x) : ContinuousMap.HomotopicRel f g S := by
  have hdist' : ∀ x, ‖(f x : EuclideanSpace ℝ (Fin (n+1))) - (g x : EuclideanSpace ℝ (Fin (n+1)))‖ < 1 := by
    intro x
    have h := hdist x
    rw [Subtype.dist_eq, dist_eq_norm] at h
    exact h
  have hfx : ∀ x : X, ‖(f x : EuclideanSpace ℝ (Fin (n+1)))‖ = 1 := fun x => norm_eq_of_mem_sphere (f x)
  have hgx : ∀ x : X, ‖(g x : EuclideanSpace ℝ (Fin (n+1)))‖ = 1 := fun x => norm_eq_of_mem_sphere (g x)
  have hne : ∀ (x : X) (t : I),
      (1 - (t : ℝ)) • (f x : EuclideanSpace ℝ (Fin (n+1)))
        + (t : ℝ) • (g x : EuclideanSpace ℝ (Fin (n+1))) ≠ 0 := by
    intro x t hzero
    have h1 : ‖(1 - (t : ℝ)) • (f x : EuclideanSpace ℝ (Fin (n+1)))‖
        = ‖(t : ℝ) • (g x : EuclideanSpace ℝ (Fin (n+1)))‖ := by
      have h : (1 - (t : ℝ)) • (f x : EuclideanSpace ℝ (Fin (n+1)))
          = -((t : ℝ) • (g x : EuclideanSpace ℝ (Fin (n+1)))) := by
        rw [eq_neg_iff_add_eq_zero]
        exact hzero
      rw [h, norm_neg]
    rw [norm_smul, norm_smul, hfx x, hgx x, mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs] at h1
    have ht : (t : ℝ) = 1 / 2 := by
      rcases abs_eq_abs.mp h1 with h | h
      · linarith
      · linarith
    have hfg : (f x : EuclideanSpace ℝ (Fin (n+1))) = -(g x : EuclideanSpace ℝ (Fin (n+1))) := by
      have h := hzero
      rw [ht] at h
      norm_num at h
      have h2 : (f x : EuclideanSpace ℝ (Fin (n+1))) + (g x : EuclideanSpace ℝ (Fin (n+1))) = 0 := by
        have h4 : (1/2 : ℝ) • ((f x : EuclideanSpace ℝ (Fin (n+1)))
            + (g x : EuclideanSpace ℝ (Fin (n+1)))) = 0 := by
          rw [smul_add]; exact h
        exact (smul_eq_zero.mp h4).resolve_left (by norm_num)
      exact eq_neg_iff_add_eq_zero.mpr h2
    have h2 : ‖(f x : EuclideanSpace ℝ (Fin (n+1))) - (g x : EuclideanSpace ℝ (Fin (n+1)))‖ = 2 := by
      have h3 : (f x : EuclideanSpace ℝ (Fin (n+1))) - (g x : EuclideanSpace ℝ (Fin (n+1)))
          = (-2 : ℝ) • (g x : EuclideanSpace ℝ (Fin (n+1))) := by rw [hfg]; module
      rw [h3, norm_smul, Real.norm_eq_abs, hgx x]
      norm_num
    linarith [hdist' x]
  let F : I × X → EuclideanSpace ℝ (Fin (n+1)) := fun y =>
    (1 - (y.1 : ℝ)) • (f y.2 : EuclideanSpace ℝ (Fin (n+1)))
      + (y.1 : ℝ) • (g y.2 : EuclideanSpace ℝ (Fin (n+1)))
  have hFcont : Continuous F := by
    unfold F
    apply Continuous.add
    · exact ((continuous_const : Continuous fun _ : I × X => (1 : ℝ)).sub
        (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp (f.continuous.comp continuous_snd))
    · exact (continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (g.continuous.comp continuous_snd))
  let G : I × X → sphere n := fun y =>
    ⟨(‖F y‖)⁻¹ • F y, by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg (F y))]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hne y.2 y.1))⟩
  have hGcont : Continuous G := by
    apply Continuous.subtype_mk
    exact (((continuous_norm.comp hFcont).inv₀
      (fun y => norm_ne_zero_iff.mpr (hne y.2 y.1))).smul hFcont)
  refine ⟨{ toHomotopy := ⟨⟨G, hGcont⟩, ?_, ?_⟩, prop' := ?_ }⟩
  · intro x
    apply Subtype.ext
    show (‖F (0, x)‖)⁻¹ • F (0, x) = (f x : EuclideanSpace ℝ (Fin (n+1)))
    have hF0 : F (0, x) = (f x : EuclideanSpace ℝ (Fin (n+1))) := by
      unfold F
      simp
    rw [hF0, hfx x]
    simp
  · intro x
    apply Subtype.ext
    show (‖F (1, x)‖)⁻¹ • F (1, x) = (g x : EuclideanSpace ℝ (Fin (n+1)))
    have hF1 : F (1, x) = (g x : EuclideanSpace ℝ (Fin (n+1))) := by
      unfold F
      simp
    rw [hF1, hgx x]
    simp
  · intro t x hx
    apply Subtype.ext
    show (‖F (t, x)‖)⁻¹ • F (t, x) = (f x : EuclideanSpace ℝ (Fin (n+1)))
    have hfx0 : F (t, x) = (f x : EuclideanSpace ℝ (Fin (n+1))) := by
      unfold F
      rw [hS x hx]
      module
    rw [hfx0, hfx x]
    simp


/-! ## Smooth approximation of a map of spheres, fixing the value at one point -/

/-- The coordinate functions of `S^j` are smooth. -/
private lemma contMDiff_sphereCoord (j : ℕ) (i : Fin (j+1)) :
    ContMDiff (𝓡 j) (modelWithCornersSelf ℝ ℝ) ∞
      (fun x : sphere j => (x : EuclideanSpace ℝ (Fin (j+1))) i) := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (j+1))) = j + 1) := ⟨by simp⟩
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).contMDiff.comp
    (contMDiff_coe_sphere (n := j) (m := ((⊤ : ℕ∞) : WithTop ℕ∞)))

/-- The subalgebra of smooth real-valued functions on `S^j`. -/
private def sphereSmoothSubalgebra (j : ℕ) : Subalgebra ℝ C(sphere j, ℝ) where
  carrier := {g : C(sphere j, ℝ) | ContMDiff (𝓡 j) (modelWithCornersSelf ℝ ℝ) ∞ (⇑g)}
  mul_mem' := by intro a b ha hb; exact ha.mul hb
  one_mem' := by
    show ContMDiff (𝓡 j) (modelWithCornersSelf ℝ ℝ) ∞ (fun _ : sphere j => (1 : ℝ))
    exact contMDiff_const
  add_mem' := by intro a b ha hb; exact ha.add hb
  zero_mem' := by
    show ContMDiff (𝓡 j) (modelWithCornersSelf ℝ ℝ) ∞ (fun _ : sphere j => (0 : ℝ))
    exact contMDiff_const
  algebraMap_mem' := by
    intro r
    show ContMDiff (𝓡 j) (modelWithCornersSelf ℝ ℝ) ∞ (fun _ : sphere j => r)
    exact contMDiff_const

/-- The smooth functions separate the points of `S^j`. -/
private lemma sphereSmoothSubalgebra_separatesPoints (j : ℕ) :
    (sphereSmoothSubalgebra j).SeparatesPoints := by
  intro x y hxy
  by_contra h
  push Not at h
  refine hxy (Subtype.ext (by
    ext i
    have hi := h (fun z : sphere j => (z : EuclideanSpace ℝ (Fin (j+1))) i)
      ⟨⟨fun z : sphere j => (z : EuclideanSpace ℝ (Fin (j+1))) i,
          (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp continuous_subtype_val⟩,
        contMDiff_sphereCoord j i, rfl⟩
    exact hi))

/-- **Stone–Weierstrass, coordinate by coordinate**: every coordinate function of a continuous map
`S^j → Sⁿ` is uniformly approximated by a smooth function on `S^j`. -/
private lemma exists_smooth_close_coord (j n : ℕ) (f : C(sphere j, sphere n)) (i : Fin (n+1))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ φ : C(sphere j, ℝ), ContMDiff (𝓡 j) (modelWithCornersSelf ℝ ℝ) ∞ (⇑φ) ∧
      ∀ x, |φ x - (f x : EuclideanSpace ℝ (Fin (n+1))) i| < δ := by
  have hcont : Continuous (fun x : sphere j => (f x : EuclideanSpace ℝ (Fin (n+1))) i) := by
    fun_prop
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
    (A := sphereSmoothSubalgebra j) (sphereSmoothSubalgebra_separatesPoints j)
    (fun x : sphere j => (f x : EuclideanSpace ℝ (Fin (n+1))) i) hcont δ hδ
  exact ⟨g, g.2, fun x => by simpa [Real.norm_eq_abs] using hg x⟩

/-- A coordinate bound controls the Euclidean norm: if all coordinates of `v` are smaller than `δ`
in absolute value, then `‖v‖ < √(n+1) · δ`. -/
private lemma euclid_norm_lt (n : ℕ) (v : EuclideanSpace ℝ (Fin (n+1))) (δ : ℝ) (hδ : 0 < δ)
    (h : ∀ i, |v i| < δ) : ‖v‖ < Real.sqrt (n + 1) * δ := by
  have hterm : ∀ i : Fin (n + 1), ‖v i‖ ^ 2 < δ ^ 2 := by
    intro i
    have h1 : |‖v i‖| < |δ| := by
      rw [abs_of_nonneg (norm_nonneg _), abs_of_pos hδ, Real.norm_eq_abs]
      exact h i
    exact (sq_lt_sq).mpr h1
  have hsq : ‖v‖ ^ 2 < (n + 1 : ℝ) * δ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖v.ofLp i‖ ^ 2 < ∑ _i : Fin (n + 1), δ ^ 2 :=
          Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) (fun i _ => hterm i)
      _ = (n + 1 : ℝ) * δ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  have h1 : ‖v‖ < Real.sqrt ((n + 1 : ℝ) * δ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg v)]
    exact Real.sqrt_lt_sqrt (by positivity) hsq
  calc ‖v‖ < Real.sqrt ((n + 1 : ℝ) * δ ^ 2) := h1
    _ = Real.sqrt (n + 1) * δ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (le_of_lt hδ)]

/-- **Uniform approximation of a map of spheres by a smooth one, keeping the value at a prescribed
point.** -/
theorem exists_contMDiff_dist_lt_fixing_aux (j n : ℕ) (f : C(sphere j, sphere n)) (b : sphere j)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : C(sphere j, sphere n), ContMDiff (𝓡 j) (𝓡 n) ∞ (⇑g) ∧ g b = f b ∧
      ∀ x, dist (f x) (g x) < ε := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n + 1) := ⟨by simp⟩
  obtain ⟨δ, hδ, hδle, hδsm⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε / (8 * ((n : ℝ) + 1)) ∧
      δ ≤ 1 / (8 * ((n : ℝ) + 1)) :=
    ⟨min (ε / (8 * ((n : ℝ) + 1))) (1 / (8 * ((n : ℝ) + 1))), lt_min (by positivity) (by positivity),
      min_le_left _ _, min_le_right _ _⟩
  have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have hsqrt_le : Real.sqrt ((n:ℝ) + 1) ≤ (n:ℝ) + 1 := by
    have h1 : (1:ℝ) ≤ Real.sqrt ((n:ℝ) + 1) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      linarith
    nlinarith [Real.sq_sqrt hn1.le, Real.sqrt_nonneg ((n:ℝ) + 1), h1]
  have hquarter : Real.sqrt ((n:ℝ) + 1) * δ ≤ 1 / 4 := by
    have h := mul_le_mul hsqrt_le hδsm (le_of_lt hδ) (by positivity)
    have h2 : ((n:ℝ) + 1) * (1 / (8 * ((n:ℝ) + 1))) = 1 / 8 := by field_simp
    linarith
  have hmain : 4 * (Real.sqrt ((n:ℝ) + 1) * δ) ≤ ε := by
    have h1 : Real.sqrt ((n:ℝ) + 1) * δ ≤ ε / 8 := by
      have h := mul_le_mul hsqrt_le hδle (le_of_lt hδ) (by positivity)
      have h2 : ((n:ℝ) + 1) * (ε / (8 * ((n:ℝ) + 1))) = ε / 8 := by field_simp
      linarith
    linarith [h1, hε]
  choose Φ hΦsm hΦclose using fun i : Fin (n+1) => exists_smooth_close_coord j n f i δ hδ
  -- the ambient map
  let Gfun : sphere j → EuclideanSpace ℝ (Fin (n+1)) :=
    fun x => (EuclideanSpace.equiv (Fin (n+1)) ℝ).symm (fun i => Φ i x)
  have hGcont : Continuous Gfun :=
    ((EuclideanSpace.equiv (Fin (n+1)) ℝ).symm.continuous).comp
      (continuous_pi fun i => (Φ i).continuous)
  let G : C(sphere j, EuclideanSpace ℝ (Fin (n+1))) := ⟨Gfun, hGcont⟩
  have hGsm : ContMDiff (𝓡 j) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n+1)))) ∞ Gfun := by
    have h1 : ContMDiff (𝓡 j) (modelWithCornersSelf ℝ ((Fin (n+1)) → ℝ)) ∞
        (fun x => (fun i => Φ i x)) := by
      rw [contMDiff_pi_space]
      exact fun i => hΦsm i
    exact (((EuclideanSpace.equiv (Fin (n+1)) ℝ).symm :
      ((Fin (n+1)) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))).contMDiff).comp h1
  have hGclose : ∀ x, ‖(G x : EuclideanSpace ℝ (Fin (n+1))) - (f x : EuclideanSpace ℝ (Fin (n+1)))‖
      < Real.sqrt ((n:ℝ)+1) * δ := by
    intro x
    apply euclid_norm_lt n _ δ hδ
    intro i
    have hdiff : ((G x : EuclideanSpace ℝ (Fin (n+1))) - (f x : EuclideanSpace ℝ (Fin (n+1)))) i
        = Φ i x - (f x : EuclideanSpace ℝ (Fin (n+1))) i := by
      simp [G, Gfun]
    rw [hdiff]
    exact hΦclose i x
  -- pin the value at `b`
  let G'fun : sphere j → EuclideanSpace ℝ (Fin (n+1)) :=
    (fun x : sphere j => (G x : EuclideanSpace ℝ (Fin (n+1))) - (G b : EuclideanSpace ℝ (Fin (n+1))))
      + (fun _ : sphere j => (f b : EuclideanSpace ℝ (Fin (n+1))))
  have hG'fun_cont : Continuous G'fun := by
    apply Continuous.add
    · exact hGcont.sub continuous_const
    · exact continuous_const
  let G' : C(sphere j, EuclideanSpace ℝ (Fin (n+1))) := ⟨G'fun, hG'fun_cont⟩
  have hG'sm : ContMDiff (𝓡 j) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n+1)))) ∞ G'fun := by
    have h2 : ContMDiff (𝓡 j) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n+1)))) ∞
        (fun x : sphere j =>
          (G x : EuclideanSpace ℝ (Fin (n+1))) - (G b : EuclideanSpace ℝ (Fin (n+1)))) :=
      hGsm.sub contMDiff_const
    have h3 := h2.add (contMDiff_const :
      ContMDiff (𝓡 j) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n+1)))) ∞
        (fun _ : sphere j => (f b : EuclideanSpace ℝ (Fin (n+1)))))
    simpa only [G'fun] using h3
  have hG'b : (G' b : EuclideanSpace ℝ (Fin (n+1))) = (f b : EuclideanSpace ℝ (Fin (n+1))) := by
    show G'fun b = (f b : EuclideanSpace ℝ (Fin (n+1)))
    simp [G'fun]
  have hG'close : ∀ x, ‖(G' x : EuclideanSpace ℝ (Fin (n+1))) - (f x : EuclideanSpace ℝ (Fin (n+1)))‖
      < 2 * (Real.sqrt ((n:ℝ)+1) * δ) := by
    intro x
    have h1 : ‖(G' x : EuclideanSpace ℝ (Fin (n+1))) - (G x : EuclideanSpace ℝ (Fin (n+1)))‖
        < Real.sqrt ((n:ℝ)+1) * δ := by
      have heq : (G' x : EuclideanSpace ℝ (Fin (n+1))) - (G x : EuclideanSpace ℝ (Fin (n+1)))
          = -((G b : EuclideanSpace ℝ (Fin (n+1))) - (f b : EuclideanSpace ℝ (Fin (n+1)))) := by
        show G'fun x - (G x : EuclideanSpace ℝ (Fin (n+1))) = _
        simp only [G'fun, Pi.add_apply]
        abel_nf
      rw [heq, norm_neg]
      simpa using hGclose b
    calc ‖(G' x : EuclideanSpace ℝ (Fin (n+1))) - (f x : EuclideanSpace ℝ (Fin (n+1)))‖
        ≤ ‖(G' x : EuclideanSpace ℝ (Fin (n+1))) - (G x : EuclideanSpace ℝ (Fin (n+1)))‖
          + ‖(G x : EuclideanSpace ℝ (Fin (n+1))) - (f x : EuclideanSpace ℝ (Fin (n+1)))‖ := by
          rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
          exact dist_triangle _ _ _
      _ < Real.sqrt ((n:ℝ)+1) * δ + Real.sqrt ((n:ℝ)+1) * δ := add_lt_add h1 (hGclose x)
      _ = 2 * (Real.sqrt ((n:ℝ)+1) * δ) := by ring
  -- continuity of the coerced map
  have hG'coec : Continuous fun x => (G' x : EuclideanSpace ℝ (Fin (n+1))) :=
    hG'fun_cont.congr (fun x => by simp [G'])
  -- the values stay away from the origin
  have hne : ∀ x, (G' x : EuclideanSpace ℝ (Fin (n+1))) ≠ 0 := by
    intro x h0
    have hc : ‖(f x : EuclideanSpace ℝ (Fin (n+1)))‖ < 2 * (Real.sqrt ((n:ℝ)+1) * δ) := by
      have h := hG'close x
      rw [h0, zero_sub, norm_neg] at h
      exact h
    have hf : ‖(f x : EuclideanSpace ℝ (Fin (n+1)))‖ = 1 := norm_eq_of_mem_sphere (f x)
    have hq : 2 * (Real.sqrt ((n:ℝ)+1) * δ) ≤ 1 / 2 := by linarith [hquarter]
    linarith
  have hnorm1 : ∀ x, ‖(‖(G' x : EuclideanSpace ℝ (Fin (n+1)))‖)⁻¹ •
      (G' x : EuclideanSpace ℝ (Fin (n+1)))‖ = 1 := by
    intro x
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hne x))
  have hmem1 : ∀ x, (‖(G' x : EuclideanSpace ℝ (Fin (n+1)))‖)⁻¹ •
      (G' x : EuclideanSpace ℝ (Fin (n+1))) ∈
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 := by
    intro x
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    exact hnorm1 x
  -- smoothness of the normalised map
  have hnorm_sm : ContMDiff (𝓡 j) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n+1)))) ∞
      (fun x => (‖(G' x : EuclideanSpace ℝ (Fin (n+1)))‖)⁻¹ •
        (G' x : EuclideanSpace ℝ (Fin (n+1)))) := by
    have hUdiff : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun v : EuclideanSpace ℝ (Fin (n+1)) => (‖v‖)⁻¹ • v) {v | v ≠ 0} := by
      have hnorm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun v : EuclideanSpace ℝ (Fin (n+1)) => ‖v‖) {v | v ≠ 0} :=
        ContDiffOn.norm ℝ contDiffOn_id (fun v hv => hv)
      have hinv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun v : EuclideanSpace ℝ (Fin (n+1)) => (‖v‖)⁻¹) {v | v ≠ 0} :=
        hnorm.inv (fun v hv => by positivity)
      exact hinv.smul contDiffOn_id
    have hU : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n+1))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n+1)))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun v : EuclideanSpace ℝ (Fin (n+1)) => (‖v‖)⁻¹ • v) {v | v ≠ 0} :=
      contMDiffOn_iff_contDiffOn.mpr hUdiff
    have hG'smOn : ContMDiffOn (𝓡 j) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n+1))))
        ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (G' x : EuclideanSpace ℝ (Fin (n+1)))) Set.univ :=
      hG'sm.contMDiffOn.congr (fun x _ => by simp [G'])
    have hcomp := ContMDiffOn.comp hU hG'smOn (fun x _ => hne x)
    exact contMDiffOn_univ.mp hcomp
  refine ⟨⟨fun x => ⟨(‖(G' x : EuclideanSpace ℝ (Fin (n+1)))‖)⁻¹ •
      (G' x : EuclideanSpace ℝ (Fin (n+1))), hmem1 x⟩, ?_⟩, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk (((continuous_norm.comp hG'coec).inv₀
      (fun x => norm_ne_zero_iff.mpr (hne x))).smul hG'coec) hmem1
  · exact ContMDiff.codRestrict_sphere hnorm_sm hmem1
  · apply Subtype.ext
    show (‖(G' b : EuclideanSpace ℝ (Fin (n+1)))‖)⁻¹ • (G' b : EuclideanSpace ℝ (Fin (n+1)))
      = (f b : EuclideanSpace ℝ (Fin (n+1)))
    rw [hG'b, norm_eq_of_mem_sphere (f b)]
    simp
  · intro x
    have hkey : ‖(f x : EuclideanSpace ℝ (Fin (n+1))) -
        (‖(G' x : EuclideanSpace ℝ (Fin (n+1)))‖)⁻¹ • (G' x : EuclideanSpace ℝ (Fin (n+1)))‖
        ≤ 2 * ‖(G' x : EuclideanSpace ℝ (Fin (n+1))) - (f x : EuclideanSpace ℝ (Fin (n+1)))‖ := by
      have hnorm' : ‖(G' x : EuclideanSpace ℝ (Fin (n+1))) -
          (‖(G' x : EuclideanSpace ℝ (Fin (n+1)))‖)⁻¹ • (G' x : EuclideanSpace ℝ (Fin (n+1)))‖
          = |‖(G' x : EuclideanSpace ℝ (Fin (n+1)))‖ - 1| := by
        have hr : (0:ℝ) < ‖(G' x : EuclideanSpace ℝ (Fin (n+1)))‖ :=
          norm_pos_iff.mpr (hne x)
        have h1 : (G' x : EuclideanSpace ℝ (Fin (n+1))) -
            (‖(G' x : EuclideanSpace ℝ (Fin (n+1)))‖)⁻¹ • (G' x : EuclideanSpace ℝ (Fin (n+1)))
            = (1 - (‖(G' x : EuclideanSpace ℝ (Fin (n+1)))‖)⁻¹) •
              (G' x : EuclideanSpace ℝ (Fin (n+1))) := by
          rw [sub_smul, one_smul]
        have h2 : (1 - (‖(G' x : EuclideanSpace ℝ (Fin (n+1)))‖)⁻¹)
            = (‖(G' x : EuclideanSpace ℝ (Fin (n+1)))‖ - 1) /
                ‖(G' x : EuclideanSpace ℝ (Fin (n+1)))‖ := by
          field_simp
        rw [h1, h2, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hr]
        field_simp
      have hle : |‖(G' x : EuclideanSpace ℝ (Fin (n+1)))‖ - 1|
          ≤ ‖(G' x : EuclideanSpace ℝ (Fin (n+1))) - (f x : EuclideanSpace ℝ (Fin (n+1)))‖ := by
        have h := abs_norm_sub_norm_le (G' x : EuclideanSpace ℝ (Fin (n+1)))
          (f x : EuclideanSpace ℝ (Fin (n+1)))
        rwa [norm_eq_of_mem_sphere (f x)] at h
      have hsplit : (f x : EuclideanSpace ℝ (Fin (n+1))) -
          (‖(G' x : EuclideanSpace ℝ (Fin (n+1)))‖)⁻¹ • (G' x : EuclideanSpace ℝ (Fin (n+1)))
          = ((f x : EuclideanSpace ℝ (Fin (n+1))) - (G' x : EuclideanSpace ℝ (Fin (n+1))))
            + ((G' x : EuclideanSpace ℝ (Fin (n+1))) -
              (‖(G' x : EuclideanSpace ℝ (Fin (n+1)))‖)⁻¹ •
                (G' x : EuclideanSpace ℝ (Fin (n+1)))) := by
        rw [sub_add_sub_cancel]
      calc ‖(f x : EuclideanSpace ℝ (Fin (n+1))) -
            (‖(G' x : EuclideanSpace ℝ (Fin (n+1)))‖)⁻¹ • (G' x : EuclideanSpace ℝ (Fin (n+1)))‖
          = ‖((f x : EuclideanSpace ℝ (Fin (n+1))) - (G' x : EuclideanSpace ℝ (Fin (n+1))))
              + ((G' x : EuclideanSpace ℝ (Fin (n+1))) -
                (‖(G' x : EuclideanSpace ℝ (Fin (n+1)))‖)⁻¹ •
                  (G' x : EuclideanSpace ℝ (Fin (n+1))))‖ := by rw [hsplit]
        _ ≤ ‖(f x : EuclideanSpace ℝ (Fin (n+1))) - (G' x : EuclideanSpace ℝ (Fin (n+1)))‖
              + ‖(G' x : EuclideanSpace ℝ (Fin (n+1))) -
                (‖(G' x : EuclideanSpace ℝ (Fin (n+1)))‖)⁻¹ •
                  (G' x : EuclideanSpace ℝ (Fin (n+1)))‖ := norm_add_le _ _
        _ = ‖(G' x : EuclideanSpace ℝ (Fin (n+1))) - (f x : EuclideanSpace ℝ (Fin (n+1)))‖
              + |‖(G' x : EuclideanSpace ℝ (Fin (n+1)))‖ - 1| := by
            rw [norm_sub_rev (f x : EuclideanSpace ℝ (Fin (n+1)))
              (G' x : EuclideanSpace ℝ (Fin (n+1))), hnorm']
        _ ≤ ‖(G' x : EuclideanSpace ℝ (Fin (n+1))) - (f x : EuclideanSpace ℝ (Fin (n+1)))‖
              + ‖(G' x : EuclideanSpace ℝ (Fin (n+1))) - (f x : EuclideanSpace ℝ (Fin (n+1)))‖ :=
            add_le_add le_rfl hle
        _ = 2 * ‖(G' x : EuclideanSpace ℝ (Fin (n+1))) - (f x : EuclideanSpace ℝ (Fin (n+1)))‖ := by
            ring
    have hlt : dist (f x)
        ((⟨(‖(G' x : EuclideanSpace ℝ (Fin (n+1)))‖)⁻¹ • (G' x : EuclideanSpace ℝ (Fin (n+1))),
          hmem1 x⟩ : sphere n)) < ε := by
      rw [Subtype.dist_eq, dist_eq_norm]
      calc ‖(f x : EuclideanSpace ℝ (Fin (n+1))) -
            (‖(G' x : EuclideanSpace ℝ (Fin (n+1)))‖)⁻¹ • (G' x : EuclideanSpace ℝ (Fin (n+1)))‖
          ≤ 2 * ‖(G' x : EuclideanSpace ℝ (Fin (n+1))) - (f x : EuclideanSpace ℝ (Fin (n+1)))‖ := hkey
        _ < 2 * (2 * (Real.sqrt ((n:ℝ)+1) * δ)) := by linarith [hG'close x]
        _ = 4 * (Real.sqrt ((n:ℝ)+1) * δ) := by ring
        _ ≤ ε := hmain
    exact hlt


/-! ## The geometric input: based maps `S^j → Sⁿ` with `j < n` are null -/

/-- **A continuous map `S^j → Sⁿ` with `j < n` is null-homotopic relative to a base point at which
it takes the value of the constant map.**  (Note that no hypothesis `1 ≤ j` is needed: for `j = 0`
the statement is the path-connectedness of `Sⁿ`, which the same argument supplies.) -/
theorem sphereMap_null_of_lt (j n : ℕ) (hjn : j < n) (b : Work.Stems.sphere j) (x₀ : Work.Stems.sphere n)
    (f : C(Work.Stems.sphere j, Work.Stems.sphere n)) (hb : f b = x₀) :
    ContinuousMap.HomotopicRel f (ContinuousMap.const _ x₀) {b} := by
  -- a smooth approximation keeping the value at the base point
  obtain ⟨g, hgsm, hgb, hgdist⟩ := exists_contMDiff_dist_lt_fixing_aux j n f b 1 one_pos
  have hgb' : g b = x₀ := by rw [hgb, hb]
  -- a point missed by the smooth approximation
  obtain ⟨y, hy⟩ := exists_sphereMap_ne_of_contMDiff hjn g hgsm
  -- `f` and `g` are homotopic relative to the base point
  have h1 : ContinuousMap.HomotopicRel f g {b} :=
    closeMaps_homotopicRel_aux n f g {b} hgdist (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hgb.symm)
  -- a map missing a point is based-null
  have h2 : ContinuousMap.HomotopicRel g (ContinuousMap.const _ x₀) {b} :=
    homotopicRel_const_of_misses' (X := sphere j) n g hy hgb'
  exact h1.trans h2

end

end Work.Stems
