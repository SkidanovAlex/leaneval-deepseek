import Mathlib
import Submission.Work.Noncompact.CompressionTube.isLocalDiffeomorph_of_immersion
import Submission.Work.Noncompact.CompressionTube.Notation

/-!
# Normalising one of two affine straightenings (step 1 of the spread)

Two blocks used by the gluing step of the arc-straightening argument:

* `exists_linearEquiv_map_ne_zero` — a continuous linear equivalence carrying one nonzero vector
  to another, built from a transvection `id + ξ ⊗ (u₁ - u₂)` (two cases, orthogonal or not);
* `normalizeChart` — given two charts `c₁`, `c₂` of the maximal atlas that straighten an immersed
  curve affinely on two intervals, the second chart can be composed with an *affine* model
  diffeomorphism so that the new chart `c₂'` agrees with `c₁` on the overlap, with the same affine
  parametrisation in `t`.
-/

noncomputable section

open Set Topology Filter
open scoped Topology

namespace Work.Routing

variable {n : ℕ}

/-- The transvection `id + ξ ⊗ (u₁ - u₂)` sends `u₂` to `u₁` when `ξ u₂ = 1`. -/
theorem transvection_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u₁ u₂ : E} {ξ : E →L[ℝ] ℝ} (hξ₂ : ξ u₂ = 1) :
    (ContinuousLinearMap.id ℝ E + ξ.smulRight (u₁ - u₂)) u₂ = u₁ := by
  simp only [add_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    hξ₂, one_smul]
  abel

/-- The same transvection is injective as soon as `ξ u₁ ≠ 0`. -/
theorem transvection_injective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u₁ u₂ : E} {ξ : E →L[ℝ] ℝ} (hξ₂ : ξ u₂ = 1) (hξ₁ : ξ u₁ ≠ 0) :
    Function.Injective (ContinuousLinearMap.id ℝ E + ξ.smulRight (u₁ - u₂)) := by
  intro x y hxy
  have h : x - y + ξ (x - y) • (u₁ - u₂) = 0 := by
    have h0 : (ContinuousLinearMap.id ℝ E + ξ.smulRight (u₁ - u₂)) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    simpa only [add_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply] using h0
  have h1 : x - y = -(ξ (x - y)) • (u₁ - u₂) := by
    conv_lhs => rw [eq_neg_of_add_eq_zero_left h]
    rw [neg_smul]
  have h2 : ξ (x - y) = -(ξ (x - y)) * (ξ u₁ - ξ u₂) := by
    conv_lhs => rw [h1]
    simp only [map_smul, smul_eq_mul, map_sub]
  rw [hξ₂] at h2
  have h3 : ξ (x - y) * ξ u₁ = 0 := by linarith [h2]
  have h4 : ξ (x - y) = 0 := by
    rcases mul_eq_zero.mp h3 with h5 | h5
    · exact h5
    · exact absurd h5 hξ₁
  rw [h4] at h1
  have h5 : x - y = 0 := by simpa using h1
  exact sub_eq_zero.mp h5

/-- **A continuous linear equivalence carrying one nonzero vector to another.** -/
theorem exists_linearEquiv_map_ne_zero {u₁ u₂ : EuclideanSpace ℝ (Fin n)}
    (h₁ : u₁ ≠ 0) (h₂ : u₂ ≠ 0) :
    ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n), L u₂ = u₁ := by
  classical
  have hnn : 0 < inner ℝ u₂ u₂ := by rw [real_inner_self_eq_norm_sq]; positivity
  have hnne : inner ℝ u₂ u₂ ≠ 0 := ne_of_gt hnn
  have hself : inner ℝ u₁ u₁ ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]
    exact ne_of_gt (by positivity)
  by_cases hcase : inner ℝ u₂ u₁ = 0
  · -- orthogonal case: `ξ = ⟨u₁ + u₂, ·⟩ / ⟨u₂, u₂⟩`
    set ξ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
      (inner ℝ u₂ u₂)⁻¹ • innerSL ℝ (u₁ + u₂) with hξdef
    have hξapp : ∀ z, ξ z = inner ℝ (u₁ + u₂) z / inner ℝ u₂ u₂ := by
      intro z
      simp only [hξdef, smul_apply, smul_eq_mul, innerSL_apply_apply, div_eq_inv_mul]
    have hξ₂ : ξ u₂ = 1 := by
      rw [hξapp]
      have h : inner ℝ (u₁ + u₂) u₂ = inner ℝ u₂ u₂ := by
        rw [inner_add_left, (real_inner_comm u₁ u₂).symm, hcase, zero_add]
      rw [h, div_self hnne]
    have hξ₁ : ξ u₁ ≠ 0 := by
      rw [hξapp]
      have h : inner ℝ (u₁ + u₂) u₁ = inner ℝ u₁ u₁ := by
        rw [inner_add_left, hcase, add_zero]
      rw [h]
      exact div_ne_zero hself hnne
    obtain ⟨L, hL⟩ := Work.Noncompact.CompressionTube.exists_continuousLinearEquiv_of_injective
      (rfl : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))
      (ContinuousLinearMap.id ℝ _ + ξ.smulRight (u₁ - u₂))
      (transvection_injective hξ₂ hξ₁)
    exact ⟨L, (congrArg (fun f : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)
      => f u₂) hL).trans (transvection_apply hξ₂)⟩
  · -- non-orthogonal case: `ξ = ⟨u₂, ·⟩ / ⟨u₂, u₂⟩`
    set ξ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
      (inner ℝ u₂ u₂)⁻¹ • innerSL ℝ u₂ with hξdef
    have hξapp : ∀ z, ξ z = inner ℝ u₂ z / inner ℝ u₂ u₂ := by
      intro z
      simp only [hξdef, smul_apply, smul_eq_mul, innerSL_apply_apply, div_eq_inv_mul]
    have hξ₂ : ξ u₂ = 1 := by rw [hξapp]; exact div_self hnne
    have hξ₁ : ξ u₁ ≠ 0 := by
      rw [hξapp]
      exact div_ne_zero hcase hnne
    obtain ⟨L, hL⟩ := Work.Noncompact.CompressionTube.exists_continuousLinearEquiv_of_injective
      (rfl : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))
      (ContinuousLinearMap.id ℝ _ + ξ.smulRight (u₁ - u₂))
      (transvection_injective hξ₂ hξ₁)
    exact ⟨L, (congrArg (fun f : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)
      => f u₂) hL).trans (transvection_apply hξ₂)⟩

/-- The affine map `Φ x = o + L (x - p₂)` and its inverse `Ψ y = p₂ + L.symm (y - o)` are
mutually inverse. -/
theorem affine_Phi_Psi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E ≃L[ℝ] E) (p₂ o : E) :
    (∀ y : E, o + L (p₂ + L.symm (y - o) - p₂) = y) ∧
    (∀ x : E, p₂ + L.symm (o + L (x - p₂) - o) = x) := by
  constructor
  · intro y
    rw [show p₂ + L.symm (y - o) - p₂ = L.symm (y - o) from by abel,
      L.apply_symm_apply]
    abel
  · intro x
    rw [show o + L (x - p₂) - o = L (x - p₂) from by abel, L.symm_apply_apply]
    abel

/-- Continuity of the normalising map. -/
theorem affine_Phi_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E ≃L[ℝ] E) (p₂ o : E) :
    Continuous fun x : E => o + L (x - p₂) := by fun_prop

/-- Continuity of the inverse of the normalising map. -/
theorem affine_Psi_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E ≃L[ℝ] E) (p₂ o : E) :
    Continuous fun y : E => p₂ + L.symm (y - o) := by fun_prop

/-- The normalising map is injective. -/
theorem affine_Phi_injective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E ≃L[ℝ] E) (p₂ o : E) :
    Function.Injective fun x : E => o + L (x - p₂) := by
  intro x y hxy
  have h : L (x - p₂) = L (y - p₂) := add_left_cancel hxy
  have h' : x - p₂ = y - p₂ := L.injective h
  have h2 : x - p₂ + p₂ = y - p₂ + p₂ := by rw [h']
  simpa using h2

/-- The image of a set under the normalising map is the preimage under its inverse. -/
theorem affine_Phi_image_eq_preimage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E ≃L[ℝ] E) (p₂ o : E) (t : Set E) :
    (fun x : E => o + L (x - p₂)) '' t
      = (fun y : E => p₂ + L.symm (y - o)) ⁻¹' t := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [Set.mem_preimage]
    rw [show p₂ + L.symm ((o + L (x - p₂)) - o) = x from by
      rw [show o + L (x - p₂) - o = L (x - p₂) from by abel, L.symm_apply_apply]
      abel]
    exact hx
  · intro hy
    refine ⟨p₂ + L.symm (y - o), hy, ?_⟩
    show o + L (p₂ + L.symm (y - o) - p₂) = y
    rw [show p₂ + L.symm (y - o) - p₂ = L.symm (y - o) from by abel, L.apply_symm_apply]
    abel

/-- **The transpose of `c₂` by the normalising affine map.** -/
def normalizeChart {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (p₂ o : EuclideanSpace ℝ (Fin n)) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) where
  toFun x := o + L (c₂ x - p₂)
  invFun y := c₂.symm (p₂ + L.symm (y - o))
  source := c₂.source
  target := (fun x : EuclideanSpace ℝ (Fin n) => o + L (x - p₂)) '' c₂.target
  map_source' x hx := ⟨c₂ x, c₂.map_source hx, rfl⟩
  map_target' y hy := by
    obtain ⟨z, hz, hzy⟩ := hy
    have hΨ : p₂ + L.symm (y - o) = z := by
      rw [← hzy]
      exact (affine_Phi_Psi L p₂ o).2 z
    rw [hΨ]
    exact c₂.map_target hz
  left_inv' x hx := by
    show c₂.symm (p₂ + L.symm (o + L (c₂ x - p₂) - o)) = x
    rw [(affine_Phi_Psi L p₂ o).2 (c₂ x)]
    exact c₂.left_inv hx
  right_inv' y hy := by
    obtain ⟨z, hz, hzy⟩ := hy
    have hΨ : p₂ + L.symm (y - o) = z := by
      rw [← hzy]
      exact (affine_Phi_Psi L p₂ o).2 z
    have hmem : p₂ + L.symm (y - o) ∈ c₂.target := by rw [hΨ]; exact hz
    show o + L (c₂ (c₂.symm (p₂ + L.symm (y - o))) - p₂) = y
    rw [c₂.right_inv hmem]
    exact (affine_Phi_Psi L p₂ o).1 y
  open_source := c₂.open_source
  open_target := by
    rw [affine_Phi_image_eq_preimage L p₂ o]
    exact c₂.open_target.preimage (affine_Psi_continuous L p₂ o)
  continuousOn_toFun := (affine_Phi_continuous L p₂ o).continuousOn.comp c₂.continuousOn_toFun
    (fun _ _ => Set.mem_univ _)
  continuousOn_invFun := c₂.continuousOn_invFun.comp (affine_Psi_continuous L p₂ o).continuousOn
    (fun y hy => by
      obtain ⟨z, hz, hzy⟩ := hy
      have hΨ : p₂ + L.symm (y - o) = z := by
        rw [← hzy]
        exact (affine_Phi_Psi L p₂ o).2 z
      rw [hΨ]
      exact hz)

/-- The normalised chart is smooth in the structural sense, hence in the maximal atlas. -/
theorem normalizeChart_smooth {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M] [T2Space M] [SecondCountableTopology M]
    {c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc₂ : c₂ ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (p₂ o : EuclideanSpace ℝ (Fin n)) :
    normalizeChart c₂ L p₂ o ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M := by
  rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
  constructor
  · -- smoothness of `Φ ∘ c₂` on `c₂.source`
    have hΦ : ContMDiffOn (Work.Noncompact.CompressionTube.MC n)
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder
        (fun x : EuclideanSpace ℝ (Fin n) => o + L (x - p₂)) Set.univ := by
      rw [contMDiffOn_univ]
      exact contMDiff_iff_contDiff.mpr (by fun_prop)
    exact hΦ.comp (contMDiffOn_of_mem_maximalAtlas hc₂) (fun _ _ => Set.mem_univ _)
  · -- smoothness of the inverse
    have hΨ : ContMDiffOn (Work.Noncompact.CompressionTube.MC n)
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder
        (fun y : EuclideanSpace ℝ (Fin n) => p₂ + L.symm (y - o)) Set.univ := by
      rw [contMDiffOn_univ]
      exact contMDiff_iff_contDiff.mpr (by fun_prop)
    exact (contMDiffOn_symm_of_mem_maximalAtlas hc₂).comp (hΨ.mono (Set.subset_univ _))
      (fun y hy => by
        obtain ⟨z, hz, hzy⟩ := hy
        have hΨz : p₂ + L.symm (y - o) = z := by
          rw [← hzy]
          exact (affine_Phi_Psi L p₂ o).2 z
        show p₂ + L.symm (y - o) ∈ c₂.target
        rw [hΨz]
        exact hz)

/-- **The overlap identity.**  With `o = c₁ (γ a₁) + (a₂ - a₁) • u₁` and `L u₂ = u₁`, the
normalised chart `normalizeChart c₂ L (c₂ (γ a₂)) o` reproduces the *first* chart's affine
parametrisation along the curve wherever the second chart does. -/
theorem normalizeChart_overlap {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {γ : ℝ → M} {c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {u₁ u₂ : EuclideanSpace ℝ (Fin n)} {a₁ a₂ b₂ : ℝ}
    {c₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (hL : L u₂ = u₁)
    (h₂ : ∀ t : ℝ, t ∈ Set.Icc a₂ b₂ →
      γ t ∈ c₂.source ∧ c₂ (γ t) = c₂ (γ a₂) + (t - a₂) • u₂) :
    ∀ t : ℝ, t ∈ Set.Icc a₂ b₂ →
      normalizeChart c₂ L (c₂ (γ a₂)) (c₁ (γ a₁) + (a₂ - a₁) • u₁) (γ t)
        = c₁ (γ a₁) + (t - a₁) • u₁ := by
  intro t ht
  have hc := (h₂ t ht).2
  show c₁ (γ a₁) + (a₂ - a₁) • u₁ + L (c₂ (γ t) - (c₂ (γ a₂))) = c₁ (γ a₁) + (t - a₁) • u₁
  rw [hc]
  have hsub : c₂ (γ a₂) + (t - a₂) • u₂ - c₂ (γ a₂) = (t - a₂) • u₂ := by abel
  rw [hsub, map_smul, hL]
  module

/-- **Step 2: the transition `F̃ = c₂' ∘ c₁.symm` fixes the axis pointwise on the overlap.**

Here `c₂'` is the normalised second chart (so that on the overlap it agrees with `c₁`'s affine
parametrisation), `p₁ = c₁ (γ a₁)` is the base point of the `c₁`-axis, and the parameter ranges of
the two affine straightenings overlap on `Icc (max a₁ a₂) (min b₁ b₂)`.  Then the transition
`c₂' ∘ c₁.symm` fixes every axis point `p₁ + (t - a₁) • u₁` of the overlap.  This is exactly the
hypothesis the isotopy of step 3 consumes (it is what makes the straightening survive the gluing).-/
theorem transition_fixes_overlap_axis {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {γ : ℝ → M} {c₁ c₂' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {u₁ : EuclideanSpace ℝ (Fin n)} {a₁ b₁ a₂ b₂ : ℝ} {p₁ : EuclideanSpace ℝ (Fin n)}
    (h₁ : ∀ t : ℝ, t ∈ Set.Icc a₁ b₁ → γ t ∈ c₁.source ∧ c₁ (γ t) = p₁ + (t - a₁) • u₁)
    (hov : ∀ t : ℝ, t ∈ Set.Icc (max a₁ a₂) (min b₁ b₂) →
      c₂' (γ t) = p₁ + (t - a₁) • u₁) :
    ∀ t : ℝ, t ∈ Set.Icc (max a₁ a₂) (min b₁ b₂) →
      c₂' (c₁.symm (p₁ + (t - a₁) • u₁)) = p₁ + (t - a₁) • u₁ := by
  intro t ht
  have hmem : t ∈ Set.Icc a₁ b₁ :=
    ⟨le_trans (le_max_left _ _) ht.1, le_trans ht.2 (min_le_left _ _)⟩
  have hsrc : γ t ∈ c₁.source := (h₁ t hmem).1
  have hval : p₁ + (t - a₁) • u₁ = c₁ (γ t) := (h₁ t hmem).2.symm
  calc c₂' (c₁.symm (p₁ + (t - a₁) • u₁))
      = c₂' (c₁.symm (c₁ (γ t))) := by rw [hval]
    _ = c₂' (γ t) := by rw [c₁.left_inv hsrc]
    _ = p₁ + (t - a₁) • u₁ := hov t ht

end Work.Routing
