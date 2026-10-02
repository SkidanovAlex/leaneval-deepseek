import Mathlib
import Submission.Work.Whitney.Basic
import Submission.Work.Thom.chernClass_homeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The Whitney sum with a rank-`0` bundle

`Work.Whitney.whitneySum Z W` is the direct sum of two complex gluing-data bundles, glued along the
explicit splitting `Work.Whitney.sumFibreC m₀ m₁`.  When the second summand has rank `0` — i.e. its
model fibre is the one-point space `EuclideanSpace ℂ (Fin 0)` — the direct sum is the first summand:
the transition functions of the second factor are all the identity (there is no other endomorphism
of the zero space), so the sum is isomorphic, through the gauge `fst ∘ e⁻¹`, to `Z` itself.

This module makes that precise:

* `Work.Whitney.nonempty_bundleIso_sumCore_of_subsingleton` — for an arbitrary field of scalars, an
  arbitrary splitting `e : F₁ × F₂ ≃L F` and a bundle `Z₂` whose model fibre is a *subsingleton*
  (in particular, of rank `0`), the direct sum `sumCore e Z₁ Z₂` is isomorphic to `Z₁`.  The gauge
  is `τ = fst ∘ e⁻¹ : F → F₁` with inverse `τ⁻¹ = e ∘ inl : F₁ → F`; the only use of the
  subsingleton hypothesis is `inl (fst w) = w` for `w : F₁ × F₂`.
* `Work.Whitney.chernClass_whitneySum_rank_zero` — consequently adding a rank-`0` bundle to a
  complex bundle leaves every Chern class unchanged.
-/

namespace Work.Whitney

open scoped ContinuousLinearMap

noncomputable section

/-! ## The general isomorphism -/

/-- **A direct sum with a rank-`0` (subsingleton-fibre) summand is the other summand.**  For a
splitting `e : F₁ × F₂ ≃L[𝕜] F` and a bundle `Z₂` whose model fibre `F₂` is a subsingleton,
`Work.Whitney.sumCore e Z₁ Z₂` is isomorphic to `Z₁` through the constant gauge
`τ = fst ∘ e⁻¹ : F → F₁` and its inverse `τ⁻¹ = e ∘ inl : F₁ → F`. -/
theorem nonempty_bundleIso_sumCore_of_subsingleton {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {B : Type} [TopologicalSpace B]
    {F₁ F₂ F : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [Subsingleton F₂]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {ι₁ ι₂ : Type*} (e : (F₁ × F₂) ≃L[𝕜] F)
    (Z₁ : VectorBundleCore 𝕜 B F₁ ι₁) (Z₂ : VectorBundleCore 𝕜 B F₂ ι₂) :
    Nonempty (Work.Thom.BundleIso (sumCore e Z₁ Z₂) Z₁) := by
  classical
  set τ : F →L[𝕜] F₁ :=
    (ContinuousLinearMap.fst 𝕜 F₁ F₂).comp (e.symm : F →L[𝕜] (F₁ × F₂)) with hτ
  set τinv : F₁ →L[𝕜] F :=
    (e : (F₁ × F₂) →L[𝕜] F).comp (ContinuousLinearMap.inl 𝕜 F₁ F₂) with hτinv
  have hinlfst_apply : ∀ w : F₁ × F₂,
      (ContinuousLinearMap.inl 𝕜 F₁ F₂) ((ContinuousLinearMap.fst 𝕜 F₁ F₂) w) = w := by
    rintro ⟨u, z⟩
    simp [Subsingleton.elim z 0]
  have hfstinl_apply : ∀ u : F₁,
      (ContinuousLinearMap.fst 𝕜 F₁ F₂) ((ContinuousLinearMap.inl 𝕜 F₁ F₂) u) = u := by
    intro u; rfl
  have hτinvτ : τinv.comp τ = ContinuousLinearMap.id 𝕜 F := by
    rw [hτ, hτinv]
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [hinlfst_apply (e.symm v), ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have hττinv : τ.comp τinv = ContinuousLinearMap.id 𝕜 F₁ := by
    rw [hτ, hτinv]
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [ContinuousLinearEquiv.symm_apply_apply, hfstinl_apply]
    rfl
  have hptF : ∀ y : F, τinv (τ y) = y := by
    intro y
    have hh := congrFun (congrArg DFunLike.coe hτinvτ) y
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hh
    exact hh
  have hptG : ∀ z : F₁, τ (τinv z) = z := by
    intro z
    have hh := congrFun (congrArg DFunLike.coe hττinv) z
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hh
    exact hh
  have hτX : ∀ (p : ι₁) (q : ι₂) (i : ι₁) (b : B),
      τ.comp ((sumCore e Z₁ Z₂).coordChange (p, q) ((sumCore e Z₁ Z₂).indexAt b) b)
        = (Z₁.coordChange p (Z₁.indexAt b) b).comp τ := by
    intro p q i b
    rw [hτ]
    rw [sumCore_coordChange, sumCore_indexAt]
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_prodMap']
    simp
  have hτinvX : ∀ (p : ι₁) (q : ι₂) (i : ι₁) (b : B),
      ((sumCore e Z₁ Z₂).coordChange ((sumCore e Z₁ Z₂).indexAt b) (p, q) b).comp τinv
        = τinv.comp (Z₁.coordChange (Z₁.indexAt b) p b) := by
    intro p q i b
    rw [hτinv]
    rw [sumCore_coordChange, sumCore_indexAt]
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_prodMap',
      ContinuousLinearMap.inl_apply]
    simp
  have hpoint1 : ∀ (p : ι₁) (q : ι₂) (i₂ : ι₁) (b : B)
      (_hb : b ∈ (sumCore e Z₁ Z₂).baseSet (p, q) ∩ Z₁.baseSet i₂),
      (Z₁.coordChange (Z₁.indexAt b) i₂ b).comp (τ.comp
          ((sumCore e Z₁ Z₂).coordChange (p, q) ((sumCore e Z₁ Z₂).indexAt b) b))
        = (Z₁.coordChange p i₂ b).comp τ := by
    intro p q i₂ b hb
    rw [hτX p q i₂ b]
    have hcyc := Z₁.coordChange_linear_comp p (Z₁.indexAt b) i₂ b
      ⟨⟨hb.1.1, Z₁.mem_baseSet_at b⟩, hb.2⟩
    rw [← ContinuousLinearMap.comp_assoc, hcyc]
  have hpoint2 : ∀ (p : ι₁) (q : ι₂) (i₁ : ι₁) (b : B)
      (_hb : b ∈ Z₁.baseSet i₁ ∩ (sumCore e Z₁ Z₂).baseSet (p, q)),
      ((sumCore e Z₁ Z₂).coordChange ((sumCore e Z₁ Z₂).indexAt b) (p, q) b).comp (τinv.comp
          (Z₁.coordChange i₁ (Z₁.indexAt b) b))
        = τinv.comp (Z₁.coordChange i₁ p b) := by
    intro p q i₁ b hb
    rw [← ContinuousLinearMap.comp_assoc, hτinvX p q i₁ b]
    have hcyc := Z₁.coordChange_linear_comp i₁ (Z₁.indexAt b) p b
      ⟨⟨hb.1, Z₁.mem_baseSet_at b⟩, hb.2.1⟩
    rw [ContinuousLinearMap.comp_assoc, hcyc]
  have hT : ∀ (i₁ : ι₁ × ι₂) (i₂ : ι₁), ContinuousOn (fun b : B =>
      (Z₁.coordChange (Z₁.indexAt b) i₂ b).comp (τ.comp
        ((sumCore e Z₁ Z₂).coordChange i₁ ((sumCore e Z₁ Z₂).indexAt b) b)))
      ((sumCore e Z₁ Z₂).baseSet i₁ ∩ Z₁.baseSet i₂) := by
    rintro ⟨p, q⟩ i₂
    refine ContinuousOn.congr
      (((Z₁.continuousOn_coordChange p i₂).clm_comp continuousOn_const).mono
        (fun b hb => ⟨hb.1.1, hb.2⟩)) (fun b hb => hpoint1 p q i₂ b hb)
  have hT2 : ∀ (i₁ : ι₁) (i₂ : ι₁ × ι₂), ContinuousOn (fun b : B =>
      ((sumCore e Z₁ Z₂).coordChange ((sumCore e Z₁ Z₂).indexAt b) i₂ b).comp (τinv.comp
        (Z₁.coordChange i₁ (Z₁.indexAt b) b)))
      (Z₁.baseSet i₁ ∩ (sumCore e Z₁ Z₂).baseSet i₂) := by
    rintro i₁ ⟨p, q⟩
    refine ContinuousOn.congr
      ((continuousOn_const.clm_comp (Z₁.continuousOn_coordChange i₁ p)).mono
        (fun b hb => ⟨hb.1, hb.2.1⟩)) (fun b hb => hpoint2 p q i₁ b hb)
  refine ⟨{ hom := fun _ => τ.toLinearMap
            inv := fun _ => τinv.toLinearMap
            left_inv := fun b x => ?_
            right_inv := fun b y => ?_
            continuous_hom := ?_
            continuous_inv := ?_ }⟩
  · exact hptF x
  · exact hptG y
  · exact Work.Thom.continuous_totalSpaceMap_clm_gen
      (sumCore e Z₁ Z₂) Z₁ (ContinuousMap.id B) (fun _ => τ) hT
  · exact Work.Thom.continuous_totalSpaceMap_clm_gen
      Z₁ (sumCore e Z₁ Z₂) (ContinuousMap.id B) (fun _ => τinv) hT2

/-! ## The Chern classes -/

/-- **The Chern classes do not see a rank-`0` summand**: for a complex bundle `Z` of rank `m` and
any complex bundle `W` of rank `0`, `c_k(Z ⊕ W) = c_k(Z)`. -/
theorem chernClass_whitneySum_rank_zero {Y : Type} [TopologicalSpace Y]
    {ι ι₀ : Type} [Fintype ι] [Fintype ι₀] {m : ℕ}
    (Z : VectorBundleCore ℂ Y (EuclideanSpace ℂ (Fin m)) ι)
    (W : VectorBundleCore ℂ Y (EuclideanSpace ℂ (Fin 0)) ι₀) (k : ℕ) :
    Work.Thom.chernClass (m + 0) k (Work.Whitney.whitneySum Z W)
      = Work.Thom.chernClass m k Z := by
  obtain ⟨e⟩ := nonempty_bundleIso_sumCore_of_subsingleton
    (𝕜 := ℂ) (B := Y) (F₁ := EuclideanSpace ℂ (Fin m))
    (F₂ := EuclideanSpace ℂ (Fin 0)) (F := EuclideanSpace ℂ (Fin (m + 0)))
    (sumFibreC m 0) Z W
  exact Work.Thom.chernClass_BundleIso (whitneySum Z W) Z e

end

end Work.Whitney
