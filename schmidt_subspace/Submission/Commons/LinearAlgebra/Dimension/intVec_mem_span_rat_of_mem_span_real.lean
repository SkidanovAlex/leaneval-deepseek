import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

namespace Commons.LinearAlgebra.Dimension

open TensorProduct

/-- A vector lies in a submodule `p` if and only if its image under `m ↦ 1 ⊗ₜ m` in the base
change along a faithfully flat algebra lies in the base change of `p`. -/
lemma mem_of_one_tmul_mem_baseChange {R A M : Type*} [CommRing R] [Ring A] [Algebra R A]
    [Module.FaithfullyFlat R A] [AddCommGroup M] [Module R M] (p : Submodule R M) (m : M) :
    m ∈ p ↔ (1 : A) ⊗ₜ[R] m ∈ p.baseChange A := by
  rw [← Submodule.span_singleton_le_iff_mem m p,
    ← Submodule.baseChange_le_iff (A := A) (p := Submodule.span R {m}) (q := p),
    Submodule.baseChange_span, Set.image_singleton,
    Submodule.span_singleton_le_iff_mem (TensorProduct.mk R A M 1 m) (p.baseChange A),
    TensorProduct.mk_apply]

theorem intVec_mem_span_rat_of_mem_span_real {N : ℕ} {ι : Type*} [Fintype ι]
    (x : ι → Fin N → ℤ) (y : Fin N → ℤ)
    (h : (fun k => (y k : ℝ)) ∈
      Submodule.span ℝ (Set.range (fun i => fun k => (x i k : ℝ)))) :
    (fun k => (y k : ℚ)) ∈
      Submodule.span ℚ (Set.range (fun i => fun k => (x i k : ℚ))) := by
  set xq : ι → (Fin N → ℚ) := (fun i k => (x i k : ℚ)) with hxq
  set yq : Fin N → ℚ := (fun k => (y k : ℚ)) with hyq
  set xr : ι → (Fin N → ℝ) := (fun i k => (x i k : ℝ)) with hxr
  set yr : Fin N → ℝ := (fun k => (y k : ℝ)) with hyr
  set w : ι → (ℝ ⊗[ℚ] (Fin N → ℚ)) := (fun i => (1 : ℝ) ⊗ₜ[ℚ] xq i) with hw
  -- the linear equivalence identifying the base change with the real vector space
  let e : (ℝ ⊗[ℚ] (Fin N → ℚ)) ≃ₗ[ℝ] (Fin N → ℝ) :=
    TensorProduct.piScalarRight ℚ ℝ ℝ (Fin N)
  have he_w : ∀ i, e (w i) = xr i := by
    intro i
    show TensorProduct.piScalarRight ℚ ℝ ℝ (Fin N) ((1 : ℝ) ⊗ₜ[ℚ] xq i) = xr i
    rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    ext k
    simp [xq, xr, Algebra.smul_def]
  have he_y : e ((1 : ℝ) ⊗ₜ[ℚ] yq) = yr := by
    show TensorProduct.piScalarRight ℚ ℝ ℝ (Fin N) ((1 : ℝ) ⊗ₜ[ℚ] yq) = yr
    rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    ext k
    simp [yq, yr, Algebra.smul_def]
  have hfun_base : (fun i => TensorProduct.mk ℚ ℝ (Fin N → ℚ) (1 : ℝ) (xq i)) = w := by
    funext i
    rw [TensorProduct.mk_apply, hw]
  have hbase : (Submodule.span ℚ (Set.range xq)).baseChange ℝ
      = Submodule.span ℝ (Set.range w) := by
    rw [Submodule.baseChange_span, ← Set.range_comp', hfun_base]
  -- the image of `Set.range w` under `e` is `Set.range xr`
  have hmap_img : (e : (ℝ ⊗[ℚ] (Fin N → ℚ)) →ₗ[ℝ] (Fin N → ℝ)) '' Set.range w
      = Set.range xr := by
    ext z
    constructor
    · rintro ⟨a, ⟨i, rfl⟩, h⟩
      exact ⟨i, by rw [← h]; exact (he_w i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨w i, ⟨i, rfl⟩, he_w i⟩
  have hmap : (Submodule.span ℝ (Set.range w)).map
        (e : (ℝ ⊗[ℚ] (Fin N → ℚ)) →ₗ[ℝ] (Fin N → ℝ))
      = Submodule.span ℝ (Set.range xr) := by
    rw [Submodule.map_span, hmap_img]
  have hmem : (1 : ℝ) ⊗ₜ[ℚ] yq ∈ (Submodule.span ℚ (Set.range xq)).baseChange ℝ := by
    rw [hbase]
    have hr : yr ∈ Submodule.span ℝ (Set.range xr) := h
    have hsy : e.symm yr = (1 : ℝ) ⊗ₜ[ℚ] yq := by
      rw [← he_y, LinearEquiv.symm_apply_apply]
    have h2 : yr ∈ (Submodule.span ℝ (Set.range w)).map
        (e : (ℝ ⊗[ℚ] (Fin N → ℚ)) →ₗ[ℝ] (Fin N → ℝ)) := by
      rw [hmap]; exact hr
    have h3 : e.symm yr ∈ Submodule.span ℝ (Set.range w) :=
      (Submodule.mem_map_equiv (p := Submodule.span ℝ (Set.range w)) (e := e)).mp h2
    rwa [hsy] at h3
  exact (mem_of_one_tmul_mem_baseChange (Submodule.span ℚ (Set.range xq)) yq).mpr hmem

end Commons.LinearAlgebra.Dimension