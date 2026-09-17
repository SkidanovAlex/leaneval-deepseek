import Mathlib.Algebra.Module.ZLattice.Covolume

namespace Commons.Lattice.Packing

open MeasureTheory Module

lemma euclidean_basisFun_equivFun_apply {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis).equivFun x i = x i := by
  rw [Basis.equivFun_apply]
  exact PiLp.basisFun_repr 2 ℝ (Fin d) x i

theorem exists_ellipsoid_of_lattice {d : ℕ} (hd : 0 < d)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hmin : ∀ v : Λ, v ≠ 0 → 1 ≤ ‖(v : EuclideanSpace ℝ (Fin d))‖) :
    ∃ φ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d),
      {v ∈ φ '' Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 |
          ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} ∧
      |LinearMap.det φ| * ZLattice.covolume Λ = 1 := by
  classical
  have hfin : finrank ℤ Λ = d := by
    rw [ZLattice.rank ℝ Λ, finrank_euclideanSpace_fin]
  let b : Basis (Fin d) ℤ Λ := (Free.chooseBasis ℤ Λ).reindex
    (Fintype.equivOfCardEq (by rw [Fintype.card_fin, ← finrank_eq_card_chooseBasisIndex, hfin]))
  let b₀ : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) := b.ofZLatticeBasis ℝ Λ
  let β : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  let φe : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) := b₀.equivFun.trans β.equivFun.symm
  let Φ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) := φe
  let Ψ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) := φe.symm
  have hβ_apply : ∀ (x : EuclideanSpace ℝ (Fin d)) (i : Fin d), β.equivFun x i = x i := by
    intro x i
    exact euclidean_basisFun_equivFun_apply x i
  have hφe : ∀ y, φe y = β.equivFun.symm (b₀.equivFun y) := by
    intro y; rfl
  have hsymm : ∀ z, Ψ z = b₀.equivFun.symm (β.equivFun z) := by
    intro z; rfl
  have hΦ : ∀ y, Φ y = φe y := fun y => rfl
  refine ⟨Φ, ?_, ?_⟩
  · ext v
    simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hint⟩
      have hy1 : ‖y‖ < 1 := by rw [Metric.mem_ball, dist_zero_right] at hy; exact hy
      have hcoord : b₀.equivFun y = β.equivFun (φe y) := by
        rw [hφe y, LinearEquiv.apply_symm_apply]
      have hyL : y ∈ Λ := by
        have hmem : y ∈ Submodule.span ℤ (Set.range b₀) := by
          rw [← Basis.sum_repr b₀ y]
          apply Submodule.sum_mem
          intro i _
          obtain ⟨k, hk⟩ := hint i
          have hki : b₀.repr y i = (k : ℝ) := by
            have h1 : b₀.repr y i = (φe y) i := by
              rw [← congr_fun (Basis.equivFun_apply b₀ y) i, hcoord]
              exact hβ_apply (φe y) i
            rw [h1]; exact hk.symm
          rw [hki, Int.cast_smul_eq_zsmul]
          exact Submodule.smul_mem _ k (Submodule.subset_span (Set.mem_range_self i))
        rwa [show Submodule.span ℤ (Set.range b₀) = Λ from
          Basis.ofZLatticeBasis_span ℝ Λ b] at hmem
      have hy0 : y = 0 := by
        by_contra hne
        have h1 : 1 ≤ ‖y‖ := by simpa using hmin ⟨y, hyL⟩ (by simpa using hne)
        linarith
      show Φ y = 0
      rw [hy0, map_zero]
    · rintro rfl
      exact ⟨⟨0, by simp [Metric.mem_ball], by simp⟩, fun i => ⟨0, by simp⟩⟩
  · have hdet : LinearMap.det Ψ = β.det (Subtype.val ∘ (b : Fin d → Λ)) := by
      have hkey := Basis.det_comp β Ψ ⇑β
      rw [Basis.det_self, mul_one] at hkey
      rw [← hkey]
      congr 1
      funext i
      simp only [Function.comp_apply]
      rw [hsymm]
      rw [show β.equivFun (β i) = b₀.equivFun (b₀ i) from by
        rw [Basis.equivFun_apply, Basis.equivFun_apply, Basis.repr_self, Basis.repr_self]]
      rw [LinearEquiv.symm_apply_apply]
      exact Basis.ofZLatticeBasis_apply ℝ Λ b i
    have hvolβ : volume.real (ZSpan.fundamentalDomain β) = 1 := by
      have hβcoe : (⇑β : Fin d → EuclideanSpace ℝ (Fin d)) = ⇑(EuclideanSpace.basisFun (Fin d) ℝ) :=
        OrthonormalBasis.coe_toBasis _
      have h1 : volume (ZSpan.fundamentalDomain β) = 1 := by
        rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped β volume)]
        rw [show parallelepiped (⇑β) = parallelepiped (⇑(EuclideanSpace.basisFun (Fin d) ℝ)) from
          congrArg _ hβcoe]
        exact OrthonormalBasis.volume_parallelepiped (EuclideanSpace.basisFun (Fin d) ℝ)
      rw [measureReal_def, h1, ENNReal.toReal_one]
    have hcov : ZLattice.covolume Λ = |LinearMap.det Ψ| := by
      rw [ZLattice.covolume_eq_det_mul_measureReal Λ volume b β]
      rw [← hdet, hvolβ, mul_one]
    have hprod : LinearMap.det Φ * LinearMap.det Ψ = 1 := by
      have h := LinearMap.det_comp Φ Ψ
      have hcomp : Φ ∘ₗ Ψ = 1 := by
        apply LinearMap.ext
        intro x
        show Φ (Ψ x) = x
        rw [hΦ, hsymm, hφe, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
      rw [hcomp] at h
      simpa using h.symm
    rw [hcov, ← abs_mul, hprod, abs_one]

end Commons.Lattice.Packing