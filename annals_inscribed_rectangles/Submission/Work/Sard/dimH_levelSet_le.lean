import Mathlib
import Submission.Work.Projection.dimH_image_le_of_contDiffOn
import Submission.Work.Sard.submersion_param

namespace Work.Sard

/-- **Dimension of a level set.**  If `fderiv ℝ u x₀ ≠ 0` for a smooth scalar function on a
finite-dimensional real normed space, then the level set `{u = u x₀}` has, locally at `x₀`, Hausdorff
dimension at most `finrank ℝ E - 1`.

Proof sketch: `K := ker (fderiv ℝ u x₀)` has codimension one.  Using `Sard/submersion_param` instantiated
with `G := ℝ` (or the same argument inline: the map `x ↦ (u x, π x)`, where `π` projects onto `K` along a
complement of `K`, has invertible derivative at `x₀`, so its inverse function — `ContDiffAt.localInverse`
— parametrises the level sets of `u` near `x₀`), one gets a `C¹` map `ψ : K → E` and `t ∈ nhds x₀` with
`{u = u x₀} ∩ t ⊆ ψ '' s` for some bounded `s ⊆ K`.  Then
`dimH ({u = u x₀} ∩ t) ≤ dimH (ψ '' s) ≤ dimH K = finrank ℝ K = finrank ℝ E - 1`, using `dimH_mono`, the
workspace result `Submission.Work.Projection.dimH_image_le_of_contDiffOn` (proved, sorry-free:
`dimH (g '' s) ≤ finrank ℝ E` for a `C¹` map `g` on an open set containing `s`) and
`Real.dimH_univ_eq_finrank`. -/
theorem dimH_levelSet_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (u : E → ℝ) (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (x₀ : E)
    (hx : fderiv ℝ u x₀ ≠ 0) :
    ∃ t ∈ nhds x₀, dimH ({y : E | u y = u x₀} ∩ t) ≤ ((Module.finrank ℝ E : ℕ) : ENNReal) - 1 := by
  classical
  -- `fderiv ℝ u x₀ : E →L[ℝ] ℝ` is nonzero, hence surjective.
  have hsurj : Function.Surjective (fderiv ℝ u x₀) := by
    intro c
    have hv : ∃ v : E, fderiv ℝ u x₀ v ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hx (ContinuousLinearMap.ext h)
    obtain ⟨v, hv⟩ := hv
    refine ⟨(c / (fderiv ℝ u x₀ v)) • v, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]
  -- A complement of `ker (fderiv ℝ u x₀)`.
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (fderiv ℝ u x₀).ker
  obtain ⟨Φ, -, hΦdiff, -, hΦleft⟩ := submersion_param u hu x₀ hsurj C hC
  -- The projection onto the kernel along `C`.
  let π : E →ₗ[ℝ] (fderiv ℝ u x₀).ker := (fderiv ℝ u x₀).ker.projectionOnto C hC
  have hΦleft' : ∀ᶠ x in nhds x₀, Φ (u x, π x) = x := hΦleft
  have hπcont : Continuous fun x : E => π x := LinearMap.continuous_of_finiteDimensional π
  -- `Φ` is `C¹` on some neighbourhood of the base point.
  obtain ⟨s, hs_mem, hs_on⟩ := hΦdiff.contDiffOn (m := 1) (by norm_num) (by simp)
  obtain ⟨u₁, hu₁, V₀, hV₀, hbox⟩ := mem_nhds_prod_iff.mp hs_mem
  -- Shrink the second factor to an open set.
  let V : Set (fderiv ℝ u x₀).ker := interior V₀
  have hVopen : IsOpen V := isOpen_interior
  have hVmem : V ∈ nhds (π x₀) :=
    IsOpen.mem_nhds hVopen ((mem_interior_iff_mem_nhds).mpr hV₀)
  -- The parametrisation of the level set by the kernel.
  let ψ : (fderiv ℝ u x₀).ker → E := fun k => Φ (u x₀, k)
  have hψ : ContDiffOn ℝ 1 ψ V := by
    have hg : ContDiffOn ℝ 1 (fun k : (fderiv ℝ u x₀).ker => (u x₀, k)) V :=
      (contDiff_const.prodMk contDiff_id).contDiffOn
    have hmaps : Set.MapsTo (fun k : (fderiv ℝ u x₀).ker => (u x₀, k)) V s := by
      intro k hk
      have h1 : u x₀ ∈ u₁ := mem_of_mem_nhds hu₁
      have h2 : k ∈ V₀ := interior_subset hk
      exact hbox (by rw [Set.mem_prod]; exact ⟨h1, h2⟩)
    exact hs_on.comp hg hmaps
  -- The neighbourhood `t` of `x₀`.
  have ht_mem : {x : E | Φ (u x, π x) = x} ∩ π ⁻¹' V ∈ nhds x₀ :=
    Filter.inter_mem hΦleft' (hπcont.continuousAt.preimage_mem_nhds hVmem)
  refine ⟨{x : E | Φ (u x, π x) = x} ∩ π ⁻¹' V, ht_mem, ?_⟩
  have hsub : {y : E | u y = u x₀} ∩ ({x : E | Φ (u x, π x) = x} ∩ π ⁻¹' V)
      ⊆ ψ '' (π '' ({x : E | Φ (u x, π x) = x} ∩ π ⁻¹' V)) := by
    rintro y ⟨hyu, hy1, hyV⟩
    refine ⟨π y, ⟨y, ⟨hy1, hyV⟩, rfl⟩, ?_⟩
    show Φ (u x₀, π y) = y
    rw [← hyu]
    exact hy1
  have hmem : π '' ({x : E | Φ (u x, π x) = x} ∩ π ⁻¹' V) ⊆ V := by
    rintro k ⟨x, ⟨-, hxV⟩, rfl⟩
    exact hxV
  have hdim : dimH (ψ '' (π '' ({x : E | Φ (u x, π x) = x} ∩ π ⁻¹' V)))
      ≤ (Module.finrank ℝ (fderiv ℝ u x₀).ker : ENNReal) :=
    Work.Projection.dimH_image_le_of_contDiffOn hVopen hψ hmem
  have hfin : (Module.finrank ℝ (fderiv ℝ u x₀).ker : ENNReal)
      ≤ ((Module.finrank ℝ E : ℕ) : ENNReal) - 1 := by
    have hker : Module.finrank ℝ (fderiv ℝ u x₀).ker + 1 = Module.finrank ℝ E := by
      have h := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ u x₀ : E →ₗ[ℝ] ℝ)
      have hrange : Module.finrank ℝ ↥(LinearMap.range (fderiv ℝ u x₀ : E →ₗ[ℝ] ℝ)) = 1 := by
        rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
      omega
    have heq : ((Module.finrank ℝ E : ℕ) : ENNReal)
        = ((Module.finrank ℝ (fderiv ℝ u x₀).ker : ℕ) : ENNReal) + 1 := by
      rw [← hker, Nat.cast_add, Nat.cast_one]
    have hsub2 := ENNReal.sub_eq_of_eq_add (a := ((Module.finrank ℝ E : ℕ) : ENNReal))
      (b := 1) (c := ((Module.finrank ℝ (fderiv ℝ u x₀).ker : ℕ) : ENNReal)) (by simp) heq
    rw [hsub2]
  calc dimH ({y : E | u y = u x₀} ∩ ({x : E | Φ (u x, π x) = x} ∩ π ⁻¹' V))
      ≤ dimH (ψ '' (π '' ({x : E | Φ (u x, π x) = x} ∩ π ⁻¹' V))) := dimH_mono hsub
    _ ≤ (Module.finrank ℝ (fderiv ℝ u x₀).ker : ENNReal) := hdim
    _ ≤ ((Module.finrank ℝ E : ℕ) : ENNReal) - 1 := hfin

end Work.Sard
