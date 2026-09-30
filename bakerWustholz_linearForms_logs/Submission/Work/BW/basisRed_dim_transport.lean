import Mathlib
import Submission.Work.BW.basisRed_defs
import Submission.Work.BW.minkowski_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Dimension transport along the lattice isomorphism given by `A`

This file proves `Work.BW.basisRed_dim_transport`: for an integer matrix `A` with `det A ≠ 0`
the dimension of the real span of the integer vectors `v ∈ ℤⁿ` with `wNorm A c v ≤ t` equals
the dimension of the real span of the lattice points `x ∈ A ℤⁿ` with `wl1 c x ≤ t`.

The point is that the map `v ↦ A v` identifies `ℤⁿ` with the lattice `A ℤⁿ ⊆ ℝⁿ`, sends the
weighted norm `wNorm A c` to `wl1 c`, and is an injective `ℝ`-linear endomorphism of `ℝⁿ`
(because `det A ≠ 0`); an injective linear map preserves the dimension of the span of a set.
-/

namespace Work.BW

open Matrix

variable {n : ℕ}

/-- The `ℝ`-linear endomorphism of `ℝⁿ` attached to an integer matrix `A` (entries cast to
`ℝ`): the map `x ↦ (A.map (Int.castRingHom ℝ)) *ᵥ x`. -/
noncomputable def linOf (A : Matrix (Fin n) (Fin n) ℤ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  (A.map (Int.castRingHom ℝ)).mulVecLin

lemma linOf_apply (A : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℝ) :
    linOf A x = (A.map (Int.castRingHom ℝ)).mulVec x := by
  rw [linOf, Matrix.coe_mulVecLin]

/-- The image of an integer vector under `A` expressed in the columns of `A`. -/
lemma linOf_toR (A : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) :
    linOf A (fun i => (v i : ℝ)) = ∑ j, (v j) • (fun i => (A i j : ℝ)) := by
  rw [linOf, Matrix.coe_mulVecLin]
  ext i
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.map_apply, ← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul]
  rw [show (Int.castRingHom ℝ) (A i j) = ((A i j : ℤ) : ℝ) from rfl, mul_comm]

/-- The determinant of `A` cast to `ℝ` is nonzero when `det A ≠ 0` in `ℤ`. -/
lemma det_cast_ne_zero (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det ≠ 0) :
    (A.map (Int.castRingHom ℝ)).det ≠ 0 := by
  have h := RingHom.map_det (Int.castRingHom ℝ) A
  rw [show RingHom.mapMatrix (Int.castRingHom ℝ) A = A.map (Int.castRingHom ℝ) from rfl] at h
  rw [← h]
  change ((A.det : ℤ) : ℝ) ≠ 0
  exact_mod_cast hA

/-- `linOf A` is injective when `det A ≠ 0`. -/
lemma linOf_injective (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det ≠ 0) :
    Function.Injective (linOf A) := by
  rw [linOf, Matrix.coe_mulVecLin]
  exact Matrix.mulVec_injective_of_det_ne_zero (det_cast_ne_zero A hA)

/-- The image of an integer vector lies in the lattice `A ℤⁿ`. -/
lemma linOf_toR_mem_latOf (A : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) :
    linOf A (fun i => (v i : ℝ)) ∈ latOf A := by
  rw [latOf, linOf_toR]
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- Membership in the lattice `A ℤⁿ` is exactly being the image of an integer vector. -/
lemma latOf_mem_iff (A : Matrix (Fin n) (Fin n) ℤ) (y : Fin n → ℝ) :
    y ∈ latOf A ↔ ∃ v : Fin n → ℤ, linOf A (fun i => (v i : ℝ)) = y := by
  constructor
  · intro hy
    rw [latOf] at hy
    rw [Submodule.mem_span_range_iff_exists_fun ℤ] at hy
    obtain ⟨c, hc⟩ := hy
    refine ⟨c, ?_⟩
    rw [linOf_toR, hc]
  · rintro ⟨v, rfl⟩
    exact linOf_toR_mem_latOf A v

/-- `wNorm A c` on an integer vector is `wl1 c` of its image under `A`. -/
lemma wNorm_toR_eq_wl1 (A : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → ℝ) (v : Fin n → ℤ) :
    wNorm A c (fun i => (v i : ℝ)) = wl1 c (linOf A (fun i => (v i : ℝ))) := by
  rw [wNorm, wl1, linOf_apply]

/-- An injective linear map preserves the `finrank` of the image of a submodule. -/
lemma finrank_map_eq_of_injective {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (f : V →ₗ[ℝ] W) (hf : Function.Injective f)
    (p : Submodule ℝ V) :
    Module.finrank ℝ (Submodule.map f p) = Module.finrank ℝ p := by
  have h1 : Submodule.map f p = LinearMap.range (f.comp p.subtype) := by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.comp_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨⟨x, hx⟩, hxy⟩; exact ⟨x, hx, hxy⟩
  rw [h1]
  exact LinearMap.finrank_range_of_inj (hf.comp p.subtype_injective)

theorem basisRed_dim_transport {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det ≠ 0)
    (c : Fin n → ℝ) (t : ℝ) :
    Module.finrank ℝ (Submodule.span ℝ {x : Fin n → ℝ |
        (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ Work.BW.wNorm A c x ≤ t})
      = Module.finrank ℝ (Submodule.span ℝ
          ({x : Fin n → ℝ | Work.BW.wl1 c x ≤ t} ∩ (Work.BW.latOf A : Set (Fin n → ℝ)))) := by
  classical
  set S₁ : Set (Fin n → ℝ) :=
    {x : Fin n → ℝ | (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ wNorm A c x ≤ t} with hS₁
  set S₂ : Set (Fin n → ℝ) :=
    {x : Fin n → ℝ | wl1 c x ≤ t} ∩ (latOf A : Set (Fin n → ℝ)) with hS₂
  have hset : S₂ = linOf A '' S₁ := by
    ext y
    constructor
    · intro hy
      rw [hS₂] at hy
      obtain ⟨hy1, hy2⟩ := hy
      obtain ⟨v, hv⟩ := (latOf_mem_iff A y).mp hy2
      refine ⟨fun i => (v i : ℝ), ?_, hv⟩
      rw [hS₁]
      refine ⟨⟨v, rfl⟩, ?_⟩
      rw [wNorm_toR_eq_wl1, hv]
      exact hy1
    · rintro ⟨x, hx, rfl⟩
      rw [hS₁] at hx
      obtain ⟨⟨v, hvx⟩, hwx⟩ := hx
      rw [hS₂]
      refine ⟨?_, ?_⟩
      · change wl1 c (linOf A x) ≤ t
        rw [hvx, ← wNorm_toR_eq_wl1 A c v, ← hvx]
        exact hwx
      · rw [hvx]
        exact linOf_toR_mem_latOf A v
  have hspan : Submodule.span ℝ S₂ = Submodule.map (linOf A) (Submodule.span ℝ S₁) := by
    rw [hset, Submodule.span_image]
  rw [hspan]
  exact (finrank_map_eq_of_injective (linOf A) (linOf_injective A hA) (Submodule.span ℝ S₁)).symm

end Work.BW
