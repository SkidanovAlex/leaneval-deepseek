import Mathlib
import Submission.Work.Drive.Mono.FiberModel.Defs

/-!
# A coordinate on the fibres of the level's pair of functionals

For `v ≠ 0`, `ℓ v = 0` and `ℓ ≠ 0` the two linear functionals `⟪v,·⟫` and `ℓ` are linearly
independent, so the pair `π = (⟪v,·⟫, ℓ) : ℝ³ → ℝ × ℝ` is surjective with one-dimensional fibres
(lines).  A third linear functional `ζ` with `ker π ∩ ker ζ = {0}` therefore exists: it is a
linear coordinate on the fibres, and `(π, ζ) : ℝ³ → ℝ² × ℝ` is a linear isomorphism.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Mono.FiberModel

noncomputable section

/-- **A functional transverse to the fibres of `π = (⟪v,·⟫, ℓ)`.**

If `v ≠ 0`, `ℓ v = 0` and `ℓ ≠ 0`, then there is a linear functional `ζ` with
`⟪v,y⟫ = 0 → ℓ y = 0 → ζ y = 0 → y = 0`, i.e. `(⟪v,·⟫, ℓ, ζ)` is a linear coordinate system. -/
theorem exists_fibreCoord {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓne : ℓ ≠ 0) : ∃ ζ : R3 →L[ℝ] ℝ, HasTrivKernel v ℓ ζ := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : R3, ℓ w ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓne (ContinuousLinearMap.ext fun y => by simpa using h y)
  have hv2 : ‖v‖ ^ 2 ≠ 0 := by
    have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    positivity
  -- the pair of functionals, as a linear map
  set F : R3 →ₗ[ℝ] (ℝ × ℝ) :=
    ((innerSL ℝ v : R3 →L[ℝ] ℝ) : R3 →ₗ[ℝ] ℝ).prod (ℓ : R3 →ₗ[ℝ] ℝ) with hFdef
  have hF : ∀ y : R3, F y = (inner ℝ v y, ℓ y) := fun y => rfl
  -- the image contains the two standard basis vectors, hence is everything
  have hgen : F.range = ⊤ := by
    have h1 : ((1 : ℝ), (0 : ℝ)) ∈ F.range := by
      refine ⟨(‖v‖ ^ 2)⁻¹ • v, ?_⟩
      rw [hF]
      simp only [inner_smul_right, real_inner_self_eq_norm_sq, map_smul, smul_eq_mul, hℓv,
        mul_zero]
      rw [inv_mul_cancel₀ hv2]
    have h2 : ((0 : ℝ), (1 : ℝ)) ∈ F.range := by
      refine ⟨(ℓ w)⁻¹ • (w - (inner ℝ v w) • ((‖v‖ ^ 2)⁻¹ • v)), ?_⟩
      rw [hF]
      simp only [map_sub, map_smul, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
        smul_eq_mul, hℓv, mul_zero, sub_zero]
      refine Prod.ext ?_ ?_
      · field_simp
        ring
      · field_simp
    rw [Submodule.eq_top_iff']
    intro X
    have : X = X.1 • ((1 : ℝ), (0 : ℝ)) + X.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)
  have hfin : Module.finrank ℝ F.range = 2 := by
    have h2 : Module.finrank ℝ (ℝ × ℝ) = 2 := by
      simp [Module.finrank_prod, Module.finrank_self]
    rw [hgen]
    exact (Submodule.topEquiv (R := ℝ) (M := ℝ × ℝ)).finrank_eq.trans h2
  have hker : Module.finrank ℝ F.ker = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker F
    rw [hfin, finrank_euclideanSpace_fin] at h
    omega
  have hne : F.ker ≠ ⊥ := by
    intro h
    have h0 : Module.finrank ℝ F.ker = 0 := (Submodule.finrank_eq_zero).mpr h
    omega
  obtain ⟨n, hnker, hnne⟩ := (Submodule.ne_bot_iff F.ker).mp hne
  have hn0 : ‖n‖ ≠ 0 := by rwa [norm_ne_zero_iff]
  obtain ⟨ζ, -, hζn⟩ := exists_dual_vector ℝ n hn0
  refine ⟨ζ, ?_⟩
  intro y hy1 hy2 hy3
  have hyker : y ∈ F.ker := by
    rw [LinearMap.mem_ker, hF]
    exact Prod.ext hy1 hy2
  have hspan : Submodule.span ℝ ({n} : Set R3) = F.ker := by
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · rw [Submodule.span_le]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hnker
    · rw [finrank_span_singleton hnne, hker]
  have hymem : y ∈ Submodule.span ℝ ({n} : Set R3) := by
    rw [hspan]
    exact hyker
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hymem
  have hcz : c * ‖n‖ = 0 := by
    have h1 : ζ (c • n) = c • ζ n := map_smul ζ c n
    rw [hc, hy3, hζn] at h1
    simpa using h1.symm
  rcases mul_eq_zero.mp hcz with h | h
  · rw [← hc, h, zero_smul]
  · exact absurd h hn0

end

end Work.Drive.Mono.FiberModel
