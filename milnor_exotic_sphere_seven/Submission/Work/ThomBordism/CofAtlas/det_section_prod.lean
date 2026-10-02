import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The determinant identity behind the sign of a coframed level-set atlas

This file proves `Work.ThomBordism.CofAtlas.det_section_prod`, the abstract linear-algebra
identity used in `Work.ThomBordism.levelSet_positiveAtlas_of_coframing` to compute the sign of
the determinant of the differential of a chart transition of the coframed level set `W = v⁻¹(0)`.

Setting: `β ∘ J = id`, `range J = ker q` (so `β.prod q : X ≅ V × W`), `q' = g ∘ q`.  Then

  `det (β'∘J) · det (σ∘(β.prod q)) · det g = det (σ∘(β'.prod q'))`

for an *arbitrary* linear map `β' : X → V` and any linear isomorphism `σ : V × W ≅ X`.

The mathematical content is the factorisation `β'.prod q' = (β'.prod q') ∘ (β.prod q)⁻¹ ∘ (β.prod q)`
together with the observation that, in the splitting `V × W` given by `(β, q)`, the middle factor
`(β'.prod q') ∘ (β.prod q)⁻¹` has the block-triangular shape `(v, w) ↦ (β'J v + β'(⋯w), g w)`, whose
determinant is `det (β'J) · det g`.
-/

namespace Work.ThomBordism.CofAtlas

/-- Determinant of a block-triangular endomorphism of a product: for linear maps
`f : M → M`, `k : N → M`, `g : N → N`, the determinant of `(v, w) ↦ (f v + k w, g w)` is
`det f * det g`. -/
theorem det_prod_block {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Free R M] [Module.Free R N] [Module.Finite R M]
    [Module.Finite R N] (f : M →ₗ[R] M) (k : N →ₗ[R] M) (g : N →ₗ[R] N) :
    LinearMap.det ((f.comp (LinearMap.fst R M N) + k.comp (LinearMap.snd R M N)).prod
      (g.comp (LinearMap.snd R M N))) = LinearMap.det f * LinearMap.det g := by
  let b := Module.Free.chooseBasis R M
  let c := Module.Free.chooseBasis R N
  have hmat : (LinearMap.toMatrix (b.prod c) (b.prod c))
      ((f.comp (LinearMap.fst R M N) + k.comp (LinearMap.snd R M N)).prod
        (g.comp (LinearMap.snd R M N)))
      = Matrix.fromBlocks (LinearMap.toMatrix b b f) (LinearMap.toMatrix c b k) 0
          (LinearMap.toMatrix c c g) := by
    ext (i | i) (j | j) <;>
      simp only [LinearMap.toMatrix_apply, LinearMap.prod_apply, Function.prod_apply,
        LinearMap.comp_apply, LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply,
        map_zero,
        Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
        Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inl_snd,
        Module.Basis.prod_apply_inr_fst, Module.Basis.prod_apply_inr_snd,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Finsupp.zero_apply, Matrix.zero_apply,
        zero_add, add_zero]
  rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix c,
    ← LinearMap.det_toMatrix (b.prod c), hmat, Matrix.det_fromBlocks_zero₂₁]

set_option maxHeartbeats 1600000 in
/-- The determinant identity, in the natural generality of a field. -/
theorem det_section_prod_gen {K : Type*} [Field K] {V W X : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X]
    [FiniteDimensional K V] [FiniteDimensional K W] [FiniteDimensional K X]
    (σ : (V × W) ≃ₗ[K] X) (β β' : X →ₗ[K] V) (q q' : X →ₗ[K] W) (g : W ≃ₗ[K] W)
    (J : V →ₗ[K] X)
    (hJ : β.comp J = LinearMap.id)
    (himJ : LinearMap.range J = LinearMap.ker q)
    (hq' : q' = g.toLinearMap.comp q) :
    LinearMap.det (β'.comp J) * LinearMap.det (σ.toLinearMap.comp (β.prod q)) *
      LinearMap.det g.toLinearMap =
    LinearMap.det (σ.toLinearMap.comp (β'.prod q')) := by
  have hβJ : ∀ v, β (J v) = v := fun v => by
    simpa using (LinearMap.ext_iff.mp hJ v)
  have hJker : ∀ v, q (J v) = 0 := fun v => by
    have h : J v ∈ LinearMap.ker q := by
      rw [← himJ]; exact LinearMap.mem_range_self J v
    simpa [LinearMap.mem_ker] using h
  -- `β.prod q` is injective, purely from `β ∘ J = id` and `range J = ker q`.
  have hinj : Function.Injective (β.prod q) := by
    intro x y hxy
    have hx : β x = β y := by
      have h := congrArg Prod.fst hxy
      simpa [LinearMap.prod_apply, Function.prod_apply] using h
    have hqx : q x = q y := by
      have h := congrArg Prod.snd hxy
      simpa [LinearMap.prod_apply, Function.prod_apply] using h
    have hker : x - y ∈ LinearMap.ker q := by
      rw [LinearMap.mem_ker, map_sub, hqx, sub_self]
    rw [← himJ] at hker
    obtain ⟨v, hv⟩ := hker
    have hv0 : v = 0 := by
      have h1 : v = β (x - y) := by rw [← hv, hβJ]
      have h2 : β (x - y) = 0 := by rw [map_sub, hx, sub_self]
      rw [h1, h2]
    rw [hv0, map_zero] at hv
    exact sub_eq_zero.mp hv.symm
  -- the dimensions agree because `σ : V × W ≃ X` exists, so `β.prod q` is onto as well.
  have hfin : Module.finrank K X = Module.finrank K (V × W) := by
    rw [(LinearEquiv.finrank_eq σ).symm, Module.finrank_prod]
  have hsurj : Function.Surjective (β.prod q) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj
  let E : X ≃ₗ[K] (V × W) := LinearEquiv.ofBijective (β.prod q) ⟨hinj, hsurj⟩
  have hEeq : (E : X →ₗ[K] V × W) = β.prod q :=
    LinearMap.ext fun x => by simp [E, LinearEquiv.ofBijective]
  let C : (V × W) →ₗ[K] X := E.symm
  have hCE : ∀ z : V × W, (E : X →ₗ[K] V × W) (C z) = z := fun z => E.apply_symm_apply z
  have hCβ : ∀ z : V × W, β (C z) = z.1 := fun z => by
    have h : (β.prod q) (C z) = z := by simpa [← hEeq] using hCE z
    simpa [LinearMap.prod_apply, Function.prod_apply] using congrArg Prod.fst h
  have hCq : ∀ z : V × W, q (C z) = z.2 := fun z => by
    have h : (β.prod q) (C z) = z := by simpa [← hEeq] using hCE z
    simpa [LinearMap.prod_apply, Function.prod_apply] using congrArg Prod.snd h
  have hEJ : ∀ v : V, E (J v) = (v, 0) := fun v => by
    change (E : X →ₗ[K] V × W) (J v) = (v, 0)
    rw [hEeq]
    simp [LinearMap.prod_apply, Function.prod_apply, hβJ v, hJker v]
  have hCJ : ∀ v : V, C (v, 0) = J v := fun v => by
    have h := E.symm_apply_apply (J v)
    rw [hEJ v] at h
    exact h
  have hCsplit : ∀ z : V × W, C z = J z.1 + C (LinearMap.inr K V W z.2) := by
    intro z
    have hz : z = LinearMap.inl K V W z.1 + LinearMap.inr K V W z.2 := by
      ext <;> simp [LinearMap.inl_apply, LinearMap.inr_apply]
    calc C z = C (LinearMap.inl K V W z.1 + LinearMap.inr K V W z.2) := by rw [← hz]
      _ = C (LinearMap.inl K V W z.1) + C (LinearMap.inr K V W z.2) := map_add C _ _
      _ = C (z.1, 0) + C (LinearMap.inr K V W z.2) := by rw [LinearMap.inl_apply]
      _ = J z.1 + C (LinearMap.inr K V W z.2) := by rw [hCJ]
  set P : (V × W) →ₗ[K] (V × W) :=
    ((β'.comp J).comp (LinearMap.fst K V W) +
      (β'.comp (C.comp (LinearMap.inr K V W))).comp (LinearMap.snd K V W)).prod
      (g.toLinearMap.comp (LinearMap.snd K V W)) with hPdef
  have hPdet : LinearMap.det P = LinearMap.det (β'.comp J) * LinearMap.det g.toLinearMap := by
    rw [hPdef]
    exact det_prod_block (β'.comp J) (β'.comp (C.comp (LinearMap.inr K V W))) g.toLinearMap
  have hPeq : P = (β'.prod q').comp C := by
    rw [hPdef]
    refine LinearMap.ext fun z => ?_
    refine Prod.ext ?_ ?_
    · simp only [LinearMap.comp_apply, LinearMap.prod_apply, Function.prod_apply,
        LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply]
      simp only [hCsplit z, map_add]
    · simp only [LinearMap.comp_apply, LinearMap.prod_apply, Function.prod_apply,
        LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply]
      rw [hq', LinearMap.comp_apply, hCq z]
  have hcomp1 : (σ.toLinearMap.comp E.toLinearMap) ∘ₗ (C.comp (β'.prod q')) =
      σ.toLinearMap.comp (β'.prod q') := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply]
    rw [hCE]
  have hconj : E.toLinearMap ∘ₗ (C.comp (β'.prod q')) ∘ₗ E.symm.toLinearMap =
      (β'.prod q').comp C := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply]
    rw [hCE]
  have h1 : LinearMap.det (σ.toLinearMap.comp (β'.prod q')) =
      LinearMap.det (σ.toLinearMap.comp E.toLinearMap) *
        LinearMap.det (C.comp (β'.prod q')) := by
    rw [← hcomp1, LinearMap.det_comp]
  have h2 : LinearMap.det (C.comp (β'.prod q')) =
      LinearMap.det (β'.comp J) * LinearMap.det g.toLinearMap := by
    have hconj' : LinearMap.det (C.comp (β'.prod q')) =
        LinearMap.det ((β'.prod q').comp C) := by
      rw [← hconj, LinearMap.det_conj]
    rw [hconj', ← hPeq, hPdet]
  have h3 : LinearMap.det (σ.toLinearMap.comp E.toLinearMap) =
      LinearMap.det (σ.toLinearMap.comp (β.prod q)) := by rw [hEeq]
  rw [h1, h2, h3]
  ring

/-- **The determinant identity for the coframed level-set atlas.**
For `β ∘ J = id`, `range J = ker q` and `q' = g ∘ q` (with `σ : ℝ⁹ × ℝᵏ ≅ ℝ⁹⁺ᵏ` an arbitrary
linear isomorphism and `β' : ℝ⁹⁺ᵏ → ℝ⁹` an arbitrary linear map),
`det (β'∘J) · det (σ∘(β.prod q)) · det g = det (σ∘(β'.prod q'))`. -/
theorem det_section_prod {k : ℕ}
    (σ : (EuclideanSpace ℝ (Fin 9) × EuclideanSpace ℝ (Fin k)) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (9 + k)))
    (β β' : EuclideanSpace ℝ (Fin (9 + k)) →ₗ[ℝ] EuclideanSpace ℝ (Fin 9))
    (q q' : EuclideanSpace ℝ (Fin (9 + k)) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
    (g : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin k))
    (J : EuclideanSpace ℝ (Fin 9) →ₗ[ℝ] EuclideanSpace ℝ (Fin (9 + k)))
    (hJ : β.comp J = LinearMap.id)
    (himJ : LinearMap.range J = LinearMap.ker q)
    (hq' : q' = g.toLinearMap.comp q) :
    LinearMap.det (β'.comp J) * LinearMap.det (σ.toLinearMap.comp (β.prod q)) *
      LinearMap.det g.toLinearMap =
    LinearMap.det (σ.toLinearMap.comp (β'.prod q')) := by
  exact det_section_prod_gen σ β β' q q' g J hJ himJ hq'

end Work.ThomBordism.CofAtlas
