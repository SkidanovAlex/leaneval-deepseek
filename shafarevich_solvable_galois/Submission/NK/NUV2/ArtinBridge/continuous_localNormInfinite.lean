import Mathlib
import Submission.NK.GlobalCFT.Place
import Submission.NK.NUV2.ArtinBridge.continuous_algebraNorm
import Submission.NK.GlobalCFT.Norm.globalCFT_localAbs_localNormInfinite
import Submission.NK.GlobalCFT.Inclusion.globalCFT_prod_smul_eq_inclusion_normIdeleHom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option autoImplicit false

/-!
# Continuity of the archimedean local norm `N_{L_w/K_v}` on local units

For a finite extension of number fields `L / K`, an infinite place `w` of `L` lying over the
infinite place `v` of `K`, the local norm

`N_{L_w/K_v} : L_wˣ → K_vˣ`   (`NK.GlobalCFT.Place.localNormInfinite`)

is continuous.  Unfolding the definition, `localNormInfinite w v` is `Units.map (Algebra.norm
K_v)` for the `K_v`-algebra structure on `L_w` induced by the completion map
`NumberField.LiesOver.completionMap : K_v →+* L_w`, so it suffices to know that

* `K_v` is a complete *nontrivially* normed field — the norm on the completion of a number field
  at an infinite place is nontrivial because `v 2 = 2`;
* `L_w` is finite dimensional over `K_v` — here `L_w/K_v` is `ℝ/ℝ`, `ℂ/ℂ` or `ℂ/ℝ`, so that
  `L_w` is a quotient of the finite dimensional `K_v`-vector space `K_v ⊗[K] L`, via density of
  `L ⊆ L_w` and closedness of finite dimensional subspaces of a space over a complete field;
* the algebra norm of a finite-dimensional normed algebra over a complete nontrivially normed
  field is continuous (`NK.NUV2.ArtinBridge.continuous_algebraNorm`);
* `Units.map` of a continuous monoid homomorphism is continuous on the groups of units
  (`Continuous.units_map`).
-/

open scoped NumberField.LiesOver TensorProduct

namespace NK.NUV2.ArtinBridge

/-- The norm on the completion of a number field at an infinite place is nontrivial: `v 2 = 2`,
so the image of `2` in the completion has norm `2 > 1`. -/
theorem exists_one_lt_norm_completionInfinite {K : Type} [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) :
    ∃ x : v.Completion, 1 < ‖x‖ := by
  refine ⟨((((2 : ℕ) : K)) : v.Completion), ?_⟩
  have h : ‖(((((2 : ℕ)) : K)) : v.Completion)‖ = v (((2 : ℕ)) : K) := by
    rw [show (((((2 : ℕ)) : K)) : v.Completion) =
        (↑(WithAbs.toAbs v.1 (((2 : ℕ)) : K)) : v.Completion) from rfl]
    rw [NumberField.InfinitePlace.Completion.norm_coe]
    simp only [WithAbs.equiv_apply]
  rw [h, NumberField.InfinitePlace.map_natCast]
  norm_num

/-- **The archimedean local extension is finite dimensional.**  `L_w` is a quotient of the finite
dimensional `K_v`-vector space `K_v ⊗[K] L`: the canonical map `x ⊗ l ↦ x · l` has dense range
(`L` is dense in `L_w`) and closed range (it is finite dimensional over the complete field
`K_v`). -/
theorem module_finite_completionInfinite {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (w : NumberField.InfinitePlace L)
    (v : NumberField.InfinitePlace K) [w.LiesOver v] :
    Module.Finite v.Completion w.Completion := by
  classical
  -- `K_v` is a complete nontrivially normed field
  letI hnt : NontriviallyNormedField v.Completion :=
    { (inferInstance : NormedField v.Completion) with
        non_trivial := exists_one_lt_norm_completionInfinite v }
  -- the tower `K → L → L_w` is compatible
  haveI hST : IsScalarTower K L w.Completion := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- the finite dimensional `K_v`-vector space `K_v ⊗[K] L`
  haveI hfin : Module.Finite v.Completion (v.Completion ⊗[K] L) :=
    Module.Finite.base_change K v.Completion L
  -- the canonical `K_v`-linear map `K_v ⊗[K] L →ₗ L_w`, `x ⊗ l ↦ x · l`
  let Φ : v.Completion ⊗[K] L →ₗ[v.Completion] w.Completion :=
    (Algebra.TensorProduct.lift (Algebra.algHom v.Completion v.Completion w.Completion)
      (Algebra.algHom K L w.Completion) fun _ _ => mul_comm ..).toLinearMap
  have hΦ : ∀ l : L, Φ (1 ⊗ₜ[K] l) = algebraMap L w.Completion l := by
    intro l
    change (Algebra.TensorProduct.lift (Algebra.algHom v.Completion v.Completion w.Completion)
      (Algebra.algHom K L w.Completion) (fun _ _ => mul_comm ..)) (1 ⊗ₜ[K] l)
        = algebraMap L w.Completion l
    change (Algebra.algHom v.Completion v.Completion w.Completion) 1 *
        (Algebra.algHom K L w.Completion) l = algebraMap L w.Completion l
    simp [Algebra.algHom]
  -- the image of `L` in `L_w` is dense
  have hd : DenseRange (algebraMap L w.Completion) := by
    have h1 : DenseRange (((↑) : L → w.Completion)) := by
      refine (NumberField.InfinitePlace.Completion.denseRange_coe w).mono ?_
      rintro y ⟨x, rfl⟩
      exact ⟨WithAbs.ofAbs x, by simp⟩
    exact h1.mono (by
      rintro y ⟨l, rfl⟩
      exact ⟨l, (NumberField.InfinitePlace.Completion.algebraMap_apply (v := w) l).symm⟩)
  -- so the range of `Φ` is dense
  have hdense : DenseRange Φ :=
    hd.mono (by rintro y ⟨l, rfl⟩; exact ⟨1 ⊗ₜ[K] l, hΦ l⟩)
  -- and closed, since it is finite dimensional over the complete field `K_v`
  have hclosed : IsClosed (Set.range ⇑Φ) := by
    rw [← LinearMap.coe_range (f := Φ)]
    exact Submodule.closed_of_finiteDimensional (𝕜 := v.Completion) (E := w.Completion) Φ.range
  -- hence `Φ` is surjective and `L_w` is a finite `K_v`-module
  refine Module.Finite.of_surjective Φ ?_
  rw [← Set.range_eq_univ]
  rw [← hclosed.closure_eq]
  exact hdense.closure_range

/-- **Continuity of the local norm at an infinite place.** -/
theorem continuous_localNormInfinite {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (w : NumberField.InfinitePlace L)
    (v : NumberField.InfinitePlace K) [w.LiesOver v] :
    Continuous (NK.GlobalCFT.Place.localNormInfinite w v) := by
  classical
  letI hnt : NontriviallyNormedField v.Completion :=
    { (inferInstance : NormedField v.Completion) with
        non_trivial := exists_one_lt_norm_completionInfinite v }
  haveI hfin : FiniteDimensional v.Completion w.Completion :=
    module_finite_completionInfinite (K := K) (L := L) w v
  have key : Continuous
      (Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion)) :=
    (continuous_algebraNorm (𝕜 := v.Completion)
      (A := w.Completion)).units_map (Algebra.norm v.Completion)
  rw [show NK.GlobalCFT.Place.localNormInfinite w v =
      Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) from rfl]
  exact key

end NK.NUV2.ArtinBridge
