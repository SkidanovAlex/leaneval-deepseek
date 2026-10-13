import Mathlib
import Submission.Work.DSEQ0.sum_Icc_mul_add_succ

/-!
# Euler–Poincaré for a bounded complex of finite-dimensional vector spaces

This file proves `Work.DSEQ0.eulerChar_eq_homology_finrank`: for a cochain complex `C` of
`K`-vector spaces which is finite dimensional in every degree and concentrated in a window
`[lo, hi]`, the alternating sum of the dimensions of the terms equals the alternating sum of
the dimensions of the homology groups.

The mathematical content is the classical telescoping argument:

* for every degree `i`, `dim (X i) = dim (ker d ⁱ) + dim (im d ⁱ)` (rank–nullity);
* `dim (ker d ⁱ) = dim (H ⁱ) + dim (im d ⁱ⁻¹)` (the concrete description of the homology of
  a short complex of modules as `ker g ⧸ im f`);
* hence `dim (X i) = dim (H ⁱ) + β i + β (i+1)`, where `β j` is the dimension of the boundaries
  in degree `j` (image of `d (j-1) j`);
* the two boundary contributions telescope over the window, since `β lo = 0` and `β (hi+1) = 0`
  by boundedness.

The only non-trivial formal point is the identification of `β (i+1)` (which is the dimension of
the image of `d ((i+1)-1) (i+1)`) with the dimension of the image of `d i (i+1)`; since integer
arithmetic is not definitional, this is an instance of `Mathlib`'s `HomologicalComplex.XIsoOfEq`
transport.
-/

open CategoryTheory Limits

namespace Work.DSEQ0

universe u

variable {K : Type u} [Field K]

/-- The dimension of the image is unchanged by `codRestrict` to a submodule containing it. -/
lemma finrank_range_codRestrict {M N : Type u} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [Module.Finite K M]
    (f : M →ₗ[K] N) (p : Submodule K N) (h : ∀ x, f x ∈ p) :
    Module.finrank K ↥(LinearMap.range (f.codRestrict p h)) = Module.finrank K ↥(LinearMap.range f) := by
  have hker : LinearMap.ker (f.codRestrict p h) = LinearMap.ker f := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    constructor
    · intro hx
      have := congrArg (fun y : ↥p => (y : N)) hx
      simpa [LinearMap.codRestrict_apply] using this
    · intro hx
      exact Subtype.ext (by simpa [LinearMap.codRestrict_apply] using hx)
  have h1 := LinearMap.finrank_range_add_finrank_ker (f.codRestrict p h)
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  rw [hker, ← h2] at h1
  exact Nat.add_right_cancel h1

/-- Rank–nullity for the homology of a short complex of finite dimensional vector spaces:
`dim H + dim (im f) = dim (ker g)`. -/
lemma finrank_homology_shortComplex (S : ShortComplex (ModuleCat.{u} K))
    [Module.Finite K ↥(S.X₁)] [Module.Finite K ↥(S.X₂)] :
    Module.finrank K ↥(S.homology) + Module.finrank K ↥(LinearMap.range S.f.hom)
      = Module.finrank K ↥(LinearMap.ker S.g.hom) := by
  have hfin : Module.finrank K ↥(S.homology) = Module.finrank K ↥(S.moduleCatLeftHomologyData.H) :=
    LinearEquiv.finrank_eq (ShortComplex.moduleCatHomologyIso S).toLinearEquiv
  have hH : Module.finrank K ↥(S.moduleCatLeftHomologyData.H)
      = Module.finrank K ((↥(S.g.hom.ker)) ⧸ S.moduleCatToCycles.range) := by
    rw [ShortComplex.moduleCatLeftHomologyData_H]
  have hq : Module.finrank K ((↥(S.g.hom.ker)) ⧸ S.moduleCatToCycles.range)
      + Module.finrank K ↥(S.moduleCatToCycles.range)
      = Module.finrank K ↥(S.g.hom.ker) :=
    Submodule.finrank_quotient_add_finrank (S.moduleCatToCycles.range)
  have hrange : Module.finrank K ↥(S.moduleCatToCycles.range)
      = Module.finrank K ↥(LinearMap.range S.f.hom) :=
    finrank_range_codRestrict S.f.hom (LinearMap.ker S.g.hom) S.moduleCat_zero_apply
  rw [← hH, ← hfin, hrange] at hq
  exact hq

/-- **Rank–nullity for the homology of a cochain complex.** In degree `i`,
`dim Hⁱ + dim (im d ⁱ⁻¹) = dim (ker d ⁱ)`. -/
lemma finrank_homology_add (C : CochainComplex (ModuleCat.{u} K) ℤ)
    [∀ i : ℤ, Module.Finite K ↥(C.X i)] (i : ℤ) :
    Module.finrank K ↥(C.homology i)
      + Module.finrank K ↥(LinearMap.range ((C.d (i - 1) i).hom))
      = Module.finrank K ↥(LinearMap.ker ((C.d i (i + 1)).hom)) := by
  set S : ShortComplex (ModuleCat.{u} K) := C.sc' (i - 1) i (i + 1) with hS
  have hS1 : Module.Finite K ↥(S.X₁) := by
    change Module.Finite K ↥(C.X (i - 1)); infer_instance
  have hS2 : Module.Finite K ↥(S.X₂) := by
    change Module.Finite K ↥(C.X i); infer_instance
  have hf : S.f.hom = (C.d (i - 1) i).hom := rfl
  have hg : S.g.hom = (C.d i (i + 1)).hom := rfl
  have hkey := @finrank_homology_shortComplex K _ S hS1 hS2
  have e1 : C.homology i ≅ S.homology :=
    HomologicalComplex.homologyIsoSc' C (i - 1) i (i + 1) (by simp) (by simp)
  have hfin : Module.finrank K ↥(C.homology i) = Module.finrank K ↥(S.homology) :=
    LinearEquiv.finrank_eq e1.toLinearEquiv
  rw [hf, hg] at hkey
  rw [← hfin] at hkey
  exact hkey

/-- The image of `d ⁱ` and of `d ⁽ⁱ⁺¹⁾⁻¹` have the same dimension (the two descriptions of the
same morphism, which differ only by the (non definitional) integer identity `(i+1)-1 = i`). -/
lemma range_d_shift (C : CochainComplex (ModuleCat.{u} K) ℤ) (i : ℤ) :
    LinearMap.range ((C.d i (i+1)).hom) = LinearMap.range ((C.d ((i+1)-1) (i+1)).hom) := by
  have h : i = (i+1)-1 := by ring
  have hcomp := HomologicalComplex.XIsoOfEq_hom_comp_d C h (i+1)
  have hhom : (C.d i (i+1)).hom = ((C.d ((i+1)-1) (i+1)).hom).comp ((C.XIsoOfEq h).hom).hom := by
    rw [← hcomp]
    rfl
  rw [hhom, LinearMap.range_comp]
  have he : LinearMap.range (((C.XIsoOfEq h).hom).hom) = ⊤ := by
    rw [show ((C.XIsoOfEq h).hom).hom
      = ((C.XIsoOfEq h).toLinearEquiv : ↥(C.X i) →ₗ[K] ↥(C.X ((i+1)-1))) from rfl]
    exact LinearMap.range_eq_top.mpr (C.XIsoOfEq h).toLinearEquiv.surjective
  rw [he, Submodule.map_top]

/-- The dimension of the boundaries in degree `j`, i.e. of the image of `d (j-1) j`. -/
noncomputable def bndDim (C : CochainComplex (ModuleCat.{u} K) ℤ) (j : ℤ) : ℕ :=
  Module.finrank K ↥(LinearMap.range ((C.d (j-1) j).hom))

/-- The fundamental degreewise identity `dim (X i) = dim (Hⁱ) + β i + β (i+1)`. -/
lemma finrank_X_eq (C : CochainComplex (ModuleCat.{u} K) ℤ)
    [∀ i : ℤ, Module.Finite K ↥(C.X i)] (i : ℤ) :
    (Module.finrank K ↥(C.X i) : ℤ)
      = (Module.finrank K ↥(C.homology i) : ℤ)
        + (bndDim C i : ℤ) + (bndDim C (i+1) : ℤ) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker ((C.d i (i+1)).hom)
  have h2 := finrank_homology_add C i
  have hb : bndDim C i = Module.finrank K ↥(LinearMap.range ((C.d (i-1) i).hom)) := rfl
  have h3 : bndDim C (i+1) = Module.finrank K ↥(LinearMap.range ((C.d i (i+1)).hom)) := by
    simp only [bndDim]
    rw [range_d_shift]
  have key : Module.finrank K ↥(C.X i)
      = Module.finrank K ↥(C.homology i) + bndDim C i + bndDim C (i+1) := by
    rw [hb, h3, h2]
    omega
  rw [key]
  push_cast
  ring

/-- Below the window there are no boundaries. -/
lemma bndDim_lo (C : CochainComplex (ModuleCat.{u} K) ℤ) (lo hi : ℤ)
    (hbdd : ∀ i : ℤ, i < lo ∨ hi < i → IsZero (C.X i)) : bndDim C lo = 0 := by
  have hsub : Subsingleton ↥(C.X (lo-1)) :=
    (ModuleCat.isZero_iff_subsingleton).mp (hbdd (lo-1) (Or.inl (by omega)))
  have hf : (C.d (lo-1) lo).hom = 0 := by
    ext x
    have hx : x = 0 := @Subsingleton.elim _ hsub x 0
    rw [hx, map_zero, LinearMap.zero_apply]
  simp only [bndDim]
  rw [hf, LinearMap.range_zero]
  exact Module.finrank_zero_of_subsingleton

/-- Above the window there are no boundaries. -/
lemma bndDim_hi (C : CochainComplex (ModuleCat.{u} K) ℤ) (lo hi : ℤ)
    (hbdd : ∀ i : ℤ, i < lo ∨ hi < i → IsZero (C.X i)) : bndDim C (hi+1) = 0 := by
  have hsub : Subsingleton ↥(C.X (hi+1)) :=
    (ModuleCat.isZero_iff_subsingleton).mp (hbdd (hi+1) (Or.inr (by omega)))
  have h3 : bndDim C (hi+1) = Module.finrank K ↥(LinearMap.range ((C.d hi (hi+1)).hom)) := by
    simp only [bndDim]
    rw [range_d_shift]
  rw [h3]
  exact Module.finrank_zero_of_subsingleton

theorem eulerChar_eq_homology_finrank (K : Type u) [Field K]
    (C : CochainComplex (ModuleCat.{u} K) ℤ) (lo hi : ℤ)
    [∀ i : ℤ, Module.Finite K ↥(C.X i)]
    (hbdd : ∀ i : ℤ, i < lo ∨ hi < i → CategoryTheory.Limits.IsZero (C.X i)) :
    (∑ i ∈ Finset.Icc lo hi, (-1 : ℤ) ^ i.natAbs * (Module.finrank K ↥(C.X i) : ℤ)) =
      ∑ i ∈ Finset.Icc lo hi, (-1 : ℤ) ^ i.natAbs * (Module.finrank K ↥(C.homology i) : ℤ) := by
  by_cases hle : lo ≤ hi
  · -- the sign changes by `-1` when the degree is raised by one
    have hs : ∀ m : ℤ, (-1 : ℤ) ^ (m+1).natAbs = - ((-1 : ℤ) ^ m.natAbs) := by
      intro m
      rw [← Int.coe_negOnePow, ← Int.coe_negOnePow, Int.negOnePow_succ]
      simp
    have hlo : bndDim C lo = 0 := bndDim_lo C lo hi hbdd
    have hhi : bndDim C (hi+1) = 0 := bndDim_hi C lo hi hbdd
    -- the degreewise identity, multiplied by the sign
    have hterm : ∀ i ∈ Finset.Icc lo hi,
        (-1 : ℤ) ^ i.natAbs * (Module.finrank K ↥(C.X i) : ℤ)
          = (-1 : ℤ) ^ i.natAbs * (Module.finrank K ↥(C.homology i) : ℤ)
            + (-1 : ℤ) ^ i.natAbs * ((bndDim C i : ℤ) + (bndDim C (i+1) : ℤ)) := by
      intro i _
      rw [finrank_X_eq C i]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    -- the boundary terms telescope and the two end terms vanish
    rw [sum_Icc_mul_add_succ ℤ (fun m : ℤ => (-1 : ℤ) ^ m.natAbs) hs
      (fun j : ℤ => (bndDim C j : ℤ)) lo hi hle]
    rw [hlo, hhi]
    simp
  · -- an empty window: both sides vanish
    rw [Finset.Icc_eq_empty hle]
    simp

end Work.DSEQ0
