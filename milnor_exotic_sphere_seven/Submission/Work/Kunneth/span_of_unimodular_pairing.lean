import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Spanning from a unimodular pairing matrix

If `M` is a free `ℤ`-module of rank `3` and `x₀ x₁ x₂ ∈ M`, `β₀ β₁ β₂ : M →ₗ[ℤ] ℤ` are such that
the matrix `(βᵢ xⱼ)` has unit determinant, then `x₀ x₁ x₂` span `M`.

This is the linear algebra behind the spanning statement of item 4 of the Künneth subproject,
`H⁴(ℂP² × ℂP²; ℤ) = ℤ⟨a², ab, b²⟩`: the functionals `βᵢ` are the intersection products
`βᵢ(x) = ⟨xᵢ ⌣ x, c⟩` against the fundamental class, and the unimodularity of the matrix
`⟨xᵢ ⌣ xⱼ, c⟩` (the middle intersection form of `ℂP² × ℂP²`) is what an index-one subgroup
amounts to.

The rank-`2` analogue (used by the `Work.Projective` chapter) is
`Work.Projective.span_pair_eq_top_of_pairing`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace Work.Kunneth

noncomputable section

open scoped BigOperators

/-- **Rank-`3` spanning from a unimodular pairing**, over `Fin 3 → ℤ`. -/
lemma span_triple_eq_top_fin3 (x : Fin 3 → (Fin 3 → ℤ))
    (α : Fin 3 → ((Fin 3 → ℤ) →ₗ[ℤ] ℤ))
    (hunit : IsUnit (Matrix.det (Matrix.of (fun i j => α j (x i))))) :
    Submodule.span ℤ (Set.range x) = ⊤ := by
  classical
  -- the transpose of the pairing matrix: `N j k = α j (x k)`
  set N : Matrix (Fin 3) (Fin 3) ℤ := (Matrix.of (fun i j => α j (x i))).transpose with hN
  have hNapply : ∀ j k, N j k = α j (x k) := by
    intro j k
    rw [hN]
    rfl
  have hdetN : IsUnit N.det := by
    rw [hN, Matrix.det_transpose]
    exact hunit
  -- the adjugate gives an inverse of `N` over `ℤ`
  obtain ⟨u, hu⟩ := hdetN
  set A' : Matrix (Fin 3) (Fin 3) ℤ := ((u⁻¹ : ℤˣ) : ℤ) • N.adjugate with hA'
  have hA'N : A' * N = 1 := by
    have hcoe : ((u⁻¹ : ℤˣ) : ℤ) * N.det = 1 := by
      rw [← hu]; exact Units.inv_mul u
    rw [hA', Matrix.smul_mul, Matrix.adjugate_mul]
    rw [show ((u⁻¹ : ℤˣ) : ℤ) • (N.det • (1 : Matrix (Fin 3) (Fin 3) ℤ))
        = (((u⁻¹ : ℤˣ) : ℤ) * N.det) • (1 : Matrix (Fin 3) (Fin 3) ℤ) from
      (smul_assoc ((u⁻¹ : ℤˣ) : ℤ) N.det (1 : Matrix (Fin 3) (Fin 3) ℤ)).symm]
    rw [hcoe, one_smul]
  -- the rows of the inverse, as functionals
  set β : Fin 3 → ((Fin 3 → ℤ) →ₗ[ℤ] ℤ) := fun i => ∑ j, A' i j • α j with hβ
  have hβ_apply : ∀ i w, β i w = ∑ j, A' i j * α j w := by
    intro i w
    rw [hβ]
    change (∑ j, A' i j • α j) w = ∑ j, A' i j * α j w
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  -- the two endomorphisms of `Fin 3 → ℤ`
  let F : (Fin 3 → ℤ) →ₗ[ℤ] (Fin 3 → ℤ) := ∑ i, (LinearMap.proj (R := ℤ)
    (φ := fun _ : Fin 3 => ℤ) i).smulRight (x i)
  let G : (Fin 3 → ℤ) →ₗ[ℤ] (Fin 3 → ℤ) := ∑ i, (β i).smulRight (Pi.single i (1 : ℤ))
  have hF : ∀ v : Fin 3 → ℤ, F v = ∑ i, v i • x i := by
    intro v
    change (∑ i, (LinearMap.proj (R := ℤ) (φ := fun _ : Fin 3 => ℤ) i).smulRight (x i)) v
      = ∑ i, v i • x i
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
      LinearMap.smulRight_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
      LinearMap.proj_apply, LinearMap.proj_apply]
  have hG : ∀ w : Fin 3 → ℤ, G w = ∑ i, β i w • Pi.single i (1 : ℤ) := by
    intro w
    change (∑ i, (β i).smulRight (Pi.single i (1 : ℤ))) w = _
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
      LinearMap.smulRight_apply, LinearMap.smulRight_apply]
  have hsum : ∀ v : Fin 3 → ℤ, (∑ i, v i • Pi.single i (1 : ℤ)) = v := by
    intro v
    simpa [Pi.basisFun_repr, Pi.basisFun_apply] using
      Module.Basis.sum_repr (Pi.basisFun ℤ (Fin 3)) v
  have hFsingle : ∀ i : Fin 3, F (Pi.single i (1 : ℤ)) = x i := by
    intro i
    rw [hF]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, one_smul]
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk, zero_smul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hentry : ∀ a b : Fin 3, ∑ j, A' a j * N j b = if a = b then 1 else 0 := by
    intro a b
    have h := congrFun (congrFun hA'N a) b
    rwa [Matrix.mul_apply, Matrix.one_apply] at h
  have hcomp : G.comp F = 1 := by
    apply LinearMap.ext
    intro v
    rw [LinearMap.comp_apply, Module.End.one_apply, hF v, hG]
    have hkey : ∀ i, β i (∑ k, v k • x k) = v i := by
      intro i
      rw [hβ_apply i]
      have h1 : ∀ j, α j (∑ k, v k • x k) = ∑ k, v k * N j k := by
        intro j
        rw [map_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [map_smul, smul_eq_mul]
        rw [hNapply j k]
      rw [Finset.sum_congr rfl (fun j _ => by rw [h1 j])]
      calc ∑ j, A' i j * (∑ k, v k * N j k)
          = ∑ j, ∑ k, A' i j * (v k * N j k) := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [Finset.mul_sum]
        _ = ∑ k, ∑ j, A' i j * (v k * N j k) := Finset.sum_comm
        _ = ∑ k, (∑ j, A' i j * N j k) * v k := by
              refine Finset.sum_congr rfl (fun k _ => ?_)
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl (fun j _ => by ring)
        _ = ∑ k, (if i = k then (1 : ℤ) else 0) * v k := by
              exact Finset.sum_congr rfl (fun k _ => by rw [hentry i k])
        _ = v i := by
              rw [Finset.sum_eq_single i]
              · rw [if_pos rfl, one_mul]
              · intro k _ hk
                rw [if_neg (Ne.symm hk), zero_mul]
              · intro hi
                exact absurd (Finset.mem_univ i) hi
    rw [Finset.sum_congr rfl (fun i _ => by rw [hkey i])]
    exact hsum v
  have hdet : IsUnit (LinearMap.det F) := by
    have h : LinearMap.det G * LinearMap.det F = 1 := by
      have hh := congrArg LinearMap.det hcomp
      rwa [LinearMap.det_comp, LinearMap.det.map_one] at hh
    exact isUnit_iff_exists.mpr ⟨LinearMap.det G, by rw [mul_comm]; exact h, h⟩
  have hunitF : IsUnit F := (LinearMap.isUnit_iff_isUnit_det F).mpr hdet
  have hrange : F.range = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    exact ⟨(↑(hunitF.unit⁻¹) : (Fin 3 → ℤ) →ₗ[ℤ] (Fin 3 → ℤ)) y, by
      have h2 : F * ↑hunitF.unit⁻¹ = 1 := IsUnit.mul_val_inv hunitF
      have h4 := congrArg (fun f : (Fin 3 → ℤ) →ₗ[ℤ] (Fin 3 → ℤ) => f y) h2
      rw [Module.End.mul_apply, Module.End.one_apply] at h4
      exact h4⟩
  -- `F.range` is contained in the span of the `x i`
  have hle : F.range ≤ Submodule.span ℤ (Set.range x) := by
    rintro y ⟨v, rfl⟩
    rw [hF v]
    exact Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  rw [Submodule.eq_top_iff']
  intro y
  exact hle (by rw [hrange]; exact Submodule.mem_top)

/-- **Spanning from a unimodular pairing matrix** (rank `3`).  If `M` is a free `ℤ`-module of rank
`3`, `x₀ x₁ x₂ ∈ M` and `β₀ β₁ β₂ : M →ₗ[ℤ] ℤ` pair with them in a matrix of unit determinant,
then `x₀ x₁ x₂` span `M`. -/
theorem span_of_unimodular_pairing {M : Type*} [AddCommGroup M] [Module ℤ M]
    (b : Module.Basis (Fin 3) ℤ M) (x : Fin 3 → M) (β : Fin 3 → M →ₗ[ℤ] ℤ)
    (hunit : IsUnit (Matrix.det (Matrix.of (fun i j => β i (x j))))) :
    Submodule.span ℤ (Set.range x) = ⊤ := by
  classical
  set e : M ≃ₗ[ℤ] (Fin 3 → ℤ) := b.equivFun with he
  set x' : Fin 3 → (Fin 3 → ℤ) := fun i => e (x i) with hx'
  set α : Fin 3 → ((Fin 3 → ℤ) →ₗ[ℤ] ℤ) := fun j => (β j).comp (e.symm : (Fin 3 → ℤ) →ₗ[ℤ] M)
    with hα
  have hαx : ∀ i j, α j (x' i) = β j (x i) := by
    intro i j
    rw [hα, hx']
    change β j (e.symm (e (x i))) = β j (x i)
    rw [LinearEquiv.symm_apply_apply]
  have hunit' : IsUnit (Matrix.det (Matrix.of (fun i j => α j (x' i)))) := by
    rw [show (Matrix.of (fun i j => α j (x' i))) =
        (Matrix.of (fun i j => β i (x j))).transpose from by
      ext i j
      simp only [Matrix.of_apply, Matrix.transpose_apply, hαx i j]]
    rw [Matrix.det_transpose]
    exact hunit
  have hspan' := span_triple_eq_top_fin3 x' α hunit'
  have himg : (e.symm : (Fin 3 → ℤ) →ₗ[ℤ] M) '' Set.range x' = Set.range x := by
    rw [← Set.range_comp]
    congr 1
    funext i
    rw [hx']
    exact e.symm_apply_apply (x i)
  rw [← himg, ← Submodule.map_span (e.symm : (Fin 3 → ℤ) →ₗ[ℤ] M) (Set.range x'), hspan',
    Submodule.map_top, LinearMap.range_eq_top]
  exact e.symm.surjective

end

end Work.Kunneth
