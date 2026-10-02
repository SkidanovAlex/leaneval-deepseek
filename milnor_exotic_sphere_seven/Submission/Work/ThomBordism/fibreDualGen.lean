import Mathlib
import Submission.Work.ThomBordism.orientedFibreGen
import Submission.Work.ThomBordism.relKronH_surjective
import Submission.Work.Cohomology.relChains_free

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A dual generator of the fibre homology of the normal bundle

Let `V` be a closed oriented `8`-manifold, `E` an embedding datum of `V` into `ℝ^{8+k}` and `x ∈ V`
a point.  The fibre of the normal bundle over `x` is a `k`-disc, and the pair
`(nfSet E x, nfPunct E x)` is a pair of the form `(D^k, D^k ∖ 0)`; its relative cohomology in
degree `k` and its relative homology in degree `k` are both free of rank one, and the relative
Kronecker pairing (`Work.Tubular.relKronH`) between them is a perfect pairing.

This file proves the elementary consequence needed for the last mile of the Thom chapter: **if `y`
generates the relative cohomology `H^k(nfSet, nfPunct)` and `H_k(nfSet, nfPunct) ≅ ℤ` is exhibited
by a linear equivalence `eM`, then there is a *generator* `z` of the relative homology with
`relKronH y z = 1`.**

The argument is purely algebraic and uses only the surjectivity of the relative Kronecker pairing
(`Work.ThomBordism.relKronH_surjective`, the surjectivity half of the universal coefficient theorem
— it applies because the relative chains are degreewise free, `Work.Cohomology.relChains_free`):

* `relKronH X A k` is surjective, so it carries the generator `y` of `H^k(X,A;ℤ)` to a generator
  `φ := relKronH y` of its image `H_k(X,A;ℤ) →ₗ[ℤ] ℤ` (a surjective linear map sends a generator to
  a generator).
* Hence `eM.toLinearMap = c • φ` for some `c ∈ ℤ`, and evaluating at `eM.symm 1` shows `c * φ (eM.symm 1) = 1`,
  so `c = ±1` and `c` is invertible.
* The class `z := eM.symm c` is a generator (`c = ±1` generates `ℤ` and `eM` is an equivalence), and
  `c * φ z = eM z = c`, so `φ z = 1`.
-/

namespace Work.ThomBordism

/-- **A dual generator of the fibre homology.**  If `y` generates the relative cohomology
`H^k(nfSet, nfPunct)` of the fibre pair of the normal bundle at `x`, and the relative homology in
degree `k` is identified with `ℤ` by `eM`, then there is a generator `z` of the relative homology
pairing to `1` against `y`. -/
theorem fibreDualGen {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt)
    (eM : ↥((Work.Cohomology.relChains (TopCat.of ↥(Work.ThomBordism.nfSet E x))
      (Work.ThomBordism.nfPunct E x)).homology k) ≃ₗ[ℤ] ℤ)
    (y : Work.Thom.RelCoh ℤ k ↥(Work.ThomBordism.nfSet E x) (Work.ThomBordism.nfPunct E x))
    (hy : Submodule.span ℤ ({y} : Set _) = ⊤) :
    ∃ z : ↥((Work.Cohomology.relChains (TopCat.of ↥(Work.ThomBordism.nfSet E x))
        (Work.ThomBordism.nfPunct E x)).homology k),
      Submodule.span ℤ ({z} : Set _) = ⊤ ∧
      Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
        (Work.ThomBordism.nfPunct E x) k y z = 1 := by
  -- the relative chains are degreewise free, so the Kronecker pairing is surjective
  have hfree : ∀ m, Module.Free ℤ ↥((Work.Cohomology.relChains
      (TopCat.of ↥(nfSet E x)) (nfPunct E x)).X m) :=
    fun m => Work.Cohomology.relChains_free (TopCat.of ↥(nfSet E x)) (nfPunct E x) m
  have hsurj : Function.Surjective
      (Work.Tubular.relKronH (TopCat.of ↥(nfSet E x)) (nfPunct E x) k) :=
    relKronH_surjective (TopCat.of ↥(nfSet E x)) (nfPunct E x) k hfree
  -- the surjective pairing sends the generator `y` to a generator `φ = relKronH y`
  have hspanφ : Submodule.span ℤ
      ({(Work.Tubular.relKronH (TopCat.of ↥(nfSet E x)) (nfPunct E x) k) y} : Set _) = ⊤ := by
    rw [← Set.image_singleton, ← Submodule.map_span, hy, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hsurj
  -- hence `eM` is a multiple `c` of `φ`
  have hmem : eM.toLinearMap ∈ Submodule.span ℤ
      ({(Work.Tubular.relKronH (TopCat.of ↥(nfSet E x)) (nfPunct E x) k) y} : Set _) := by
    rw [hspanφ]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  -- the multiplier is a unit: evaluate at `eM.symm 1`
  have hc1 : c * Work.Tubular.relKronH (TopCat.of ↥(nfSet E x)) (nfPunct E x) k y
      (eM.symm 1) = 1 := by
    have h := LinearMap.congr_fun hc (eM.symm 1)
    simp only [LinearMap.smul_apply, smul_eq_mul, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply] at h
    exact h
  have hcu : c = 1 ∨ c = -1 :=
    Int.isUnit_iff.mp (isUnit_iff_exists_inv.mpr
      ⟨Work.Tubular.relKronH (TopCat.of ↥(nfSet E x)) (nfPunct E x) k y (eM.symm 1), hc1⟩)
  have hcne : c ≠ 0 := by rcases hcu with h | h <;> rw [h] <;> norm_num
  have hcsq : c * c = 1 := by rcases hcu with h | h <;> rw [h] <;> norm_num
  have hcz : c * Work.Tubular.relKronH (TopCat.of ↥(nfSet E x)) (nfPunct E x) k y
      (eM.symm c) = c := by
    have h := LinearMap.congr_fun hc (eM.symm c)
    simp only [LinearMap.smul_apply, smul_eq_mul, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply] at h
    exact h
  refine ⟨eM.symm c, ?_, ?_⟩
  · -- `eM.symm c` is a generator because `c = ±1` generates `ℤ` and `eM` is an equivalence
    refine Submodule.eq_top_iff'.mpr (fun w => ?_)
    refine Submodule.mem_span_singleton.mpr ⟨eM w * c, ?_⟩
    apply eM.injective
    rw [LinearEquiv.map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_assoc, hcsq, mul_one]
  · -- and it pairs to `1` against `y`
    exact Int.eq_of_mul_eq_mul_left hcne (by rw [hcz, mul_one])

end Work.ThomBordism
