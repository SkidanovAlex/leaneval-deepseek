import Mathlib
import Submission.Work.Pi6.EFACTS.tuctDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 1200000

/-!
# The coefficient connecting isomorphism `H^{n-1}(C; ℚ/ℤ) ≅ Hⁿ(C; ℤ)`

For a chain complex `C` of **free** `ℤ`-modules whose `ℚ`-cohomology vanishes in degrees `n - 1`
and `n`, the connecting homomorphism of the long exact sequence of the coefficient sequence
`0 → ℤ → ℚ → ℚ/ℤ → 0` is an isomorphism

`H^{n-1}(C; ℚ/ℤ) ≅ Hⁿ(C; ℤ)`

(the neighbouring terms `H^{n-1}(C;ℚ)` and `Hⁿ(C;ℚ)` are killed by the hypotheses, so the
connecting map `δ : H^{n-1}(C;ℚ/ℤ) → Hⁿ(C;ℤ)` is both injective and surjective).

## Route

* `homComplexMap` (from `tuctDefs`) is the postcomposition with a map of coefficient groups, so
  `homComplexMap intToRat C ≫ homComplexMap ratToQZ C = 0` and we get a short complex `S` of
  cochain complexes `0 → Hom(C,ℤ) → Hom(C,ℚ) → Hom(C,ℚ/ℤ) → 0`;
* `S` is short exact: degreewise the sequence of `ℤ`-modules
  `0 → Hom(M,ℤ) → Hom(M,ℚ) → Hom(M,ℚ/ℤ) → 0` is exact — injectivity of `ℤ → ℚ`, exactness of the
  coefficient sequence `ker(ℚ → ℚ/ℤ) = range(ℤ → ℚ)`, and surjectivity of `Hom(M,ℚ) → Hom(M,ℚ/ℤ)`
  because `M` is free, hence projective, so maps lift along the surjection `ℚ ↠ ℚ/ℤ`;
* `ShortComplex.ShortExact.δIso` turns the connecting map into an isomorphism as soon as the two
  neighbouring homology objects of the middle complex vanish.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.EFACTS

noncomputable section

attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

/-! ## Elementary facts about the coefficient sequence `0 → ℤ → ℚ → ℚ/ℤ → 0` -/

/-- The underlying function of `intToRat`. -/
lemma coeffConn_intToRat_apply (z : ℤ) : intToRat z = (z : ℚ) := rfl

/-- The underlying function of `ratToQZ`. -/
lemma coeffConn_ratToQZ_apply (q : ℚ) : ratToQZ q = (q : AddCircle (1 : ℚ)) := rfl

/-- An integer has vanishing class in `ℚ/ℤ`. -/
lemma coeffConn_cast_addCircle_zero (z : ℤ) : ((z : ℚ) : AddCircle (1 : ℚ)) = 0 := by
  rw [← zsmul_one z, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]

lemma coeffConn_intToRat_injective : Function.Injective intToRat :=
  fun a b h => Int.cast_injective (show ((a : ℚ) = (b : ℚ)) from h)

lemma coeffConn_ratToQZ_surjective : Function.Surjective ratToQZ := by
  intro x
  obtain ⟨q, hq⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℚ)) x
  exact ⟨q, hq⟩

/-- A rational number whose class in `ℚ/ℤ` vanishes is an integer. -/
lemma coeffConn_mem_range_intToRat_iff (q : ℚ) :
    q ∈ LinearMap.range intToRat ↔ ∃ n : ℤ, (n : ℚ) = q := by
  rw [LinearMap.mem_range]
  simp only [coeffConn_intToRat_apply]

lemma coeffConn_ker_ratToQZ : LinearMap.ker ratToQZ = LinearMap.range intToRat := by
  ext q
  rw [LinearMap.mem_ker, coeffConn_mem_range_intToRat_iff]
  constructor
  · intro h
    have h1 : (q : AddCircle (1 : ℚ)) = 0 := h
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff] at h1
    obtain ⟨k, hk⟩ := h1
    exact ⟨k, by rw [← hk, zsmul_one]⟩
  · rintro ⟨k, hk⟩
    calc ratToQZ q = ((k : ℚ) : AddCircle (1 : ℚ)) := by
          rw [← hk, coeffConn_ratToQZ_apply]
      _ = 0 := coeffConn_cast_addCircle_zero k

/-- The coefficient sequence is a complex: `ℤ → ℚ → ℚ/ℤ` has zero composite. -/
lemma coeffConn_ratToQZ_comp_intToRat : ratToQZ.comp intToRat = 0 := by
  refine LinearMap.ext fun z => ?_
  rw [LinearMap.comp_apply, LinearMap.zero_apply, coeffConn_ratToQZ_apply,
    coeffConn_intToRat_apply]
  exact coeffConn_cast_addCircle_zero z

/-! ## The underlying function of `homComplexMap` in each degree -/

lemma coeffConn_homComplexMap_f_apply {G G' : Type} [AddCommGroup G] [Module ℤ G]
    [AddCommGroup G'] [Module ℤ G'] (φ : G →ₗ[ℤ] G') (C : ChainComplex (ModuleCat ℤ) ℕ)
    (k : ℕ) (f : ↥(C.X k) →ₗ[ℤ] G) :
    (((homComplexMap φ C).f k).hom) f = φ.comp f := rfl

/-- The composite `Hom(M,ℤ) → Hom(M,ℚ) → Hom(M,ℚ/ℤ)` is zero. -/
lemma coeffConn_postcomp_zero (C : ChainComplex (ModuleCat ℤ) ℕ) (k : ℕ)
    (f : ↥(C.X k) →ₗ[ℤ] ℤ) : ratToQZ.comp (intToRat.comp f) = 0 := by
  refine LinearMap.ext fun m => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.zero_apply]
  exact coeffConn_cast_addCircle_zero (f m)

/-- `homComplexMap intToRat C ≫ homComplexMap ratToQZ C = 0`. -/
lemma coeffConn_homComplexMap_comp_zero (C : ChainComplex (ModuleCat ℤ) ℕ) :
    homComplexMap intToRat C ≫ homComplexMap ratToQZ C = 0 := by
  refine HomologicalComplex.hom_ext _ _ (fun k => ?_)
  apply ModuleCat.hom_ext
  ext f
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f, ModuleCat.hom_comp,
    ModuleCat.hom_zero, LinearMap.comp_apply, LinearMap.zero_apply]
  change ratToQZ.comp (intToRat.comp f) = 0
  exact coeffConn_postcomp_zero C k f

/-! ## The degreewise short exactness

For a free `ℤ`-module `M` the sequence `0 → Hom(M,ℤ) → Hom(M,ℚ) → Hom(M,ℚ/ℤ) → 0` is exact. -/

theorem coeffConn_postcomp_exact (C : ChainComplex (ModuleCat ℤ) ℕ) (k : ℕ) :
    Function.Exact (fun f : ↥(C.X k) →ₗ[ℤ] ℤ => intToRat.comp f)
      (fun f : ↥(C.X k) →ₗ[ℤ] ℚ => ratToQZ.comp f) := by
  have hInj : Function.Injective intToRat := coeffConn_intToRat_injective
  let e : ℤ ≃ₗ[ℤ] LinearMap.range intToRat :=
    LinearEquiv.ofBijective intToRat.rangeRestrict
      ⟨fun a b h => hInj (by
          have h' := congrArg (fun y : ↥(LinearMap.range intToRat) => (y : ℚ)) h
          simpa [LinearMap.codRestrict_apply] using h'),
       LinearMap.surjective_rangeRestrict intToRat⟩
  have he : ∀ z : ℤ, ((e z : ↥(LinearMap.range intToRat)) : ℚ) = (z : ℚ) := by
    intro z
    have h2 : e z = intToRat.rangeRestrict z := rfl
    rw [h2]
    simp only [LinearMap.codRestrict_apply]
    exact coeffConn_intToRat_apply z
  intro x
  constructor
  · intro hx
    have hle : ∀ m : ↥(C.X k), x m ∈ LinearMap.range intToRat := by
      intro m
      rw [← coeffConn_ker_ratToQZ]
      exact LinearMap.mem_ker.mpr (by simpa using LinearMap.congr_fun hx m)
    refine ⟨e.symm.comp (x.codRestrict _ hle), ?_⟩
    refine LinearMap.ext fun m => ?_
    rw [LinearMap.comp_apply]
    change ((e.symm (x.codRestrict _ hle m) : ℤ) : ℚ) = x m
    have h1 : ((e.symm (x.codRestrict _ hle m) : ℤ) : ℚ) =
        ((x.codRestrict _ hle m : ↥(LinearMap.range intToRat)) : ℚ) := by
      rw [← he (e.symm (x.codRestrict _ hle m)), LinearEquiv.apply_symm_apply]
    rw [h1, LinearMap.codRestrict_apply]
  · rintro ⟨y, rfl⟩
    refine LinearMap.ext fun m => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.zero_apply]
    exact coeffConn_cast_addCircle_zero (y m)

/-! ## The connecting isomorphism -/

theorem coeffConnectingIso (C : ChainComplex (ModuleCat ℤ) ℕ)
    (hfree : ∀ k : ℕ, Module.Free ℤ ↥(C.X k)) (n : ℕ) (hn : 1 ≤ n)
    (h1 : CategoryTheory.Limits.IsZero ((Work.Pi6.EFACTS.homComplex ℚ C).homology (n - 1)))
    (h2 : CategoryTheory.Limits.IsZero ((Work.Pi6.EFACTS.homComplex ℚ C).homology n)) :
    Nonempty ((Work.Pi6.EFACTS.homComplex (AddCircle (1 : ℚ)) C).homology (n - 1) ≅
      (Work.Pi6.EFACTS.homComplex ℤ C).homology n) := by
  haveI hproj : ∀ k : ℕ, Module.Projective ℤ ↥(C.X k) := fun k => by
    haveI := hfree k
    exact Module.Projective.of_free
  let S : ShortComplex (CochainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk (homComplexMap intToRat C) (homComplexMap ratToQZ C)
      (coeffConn_homComplexMap_comp_zero C)
  have hdeg : ∀ k : ℕ,
      (S.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) k)).ShortExact := by
    intro k
    haveI : Module.Projective ℤ ↥(C.X k) := hproj k
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      change Function.Exact (fun f : ↥(C.X k) →ₗ[ℤ] ℤ => intToRat.comp f)
        (fun f : ↥(C.X k) →ₗ[ℤ] ℚ => ratToQZ.comp f)
      exact coeffConn_postcomp_exact C k
    · rw [ModuleCat.mono_iff_injective]
      change Function.Injective (fun f : ↥(C.X k) →ₗ[ℤ] ℤ => intToRat.comp f)
      intro f g h
      exact LinearMap.ext fun m => coeffConn_intToRat_injective (LinearMap.congr_fun h m)
    · rw [ModuleCat.epi_iff_surjective]
      change Function.Surjective (fun f : ↥(C.X k) →ₗ[ℤ] ℚ => ratToQZ.comp f)
      intro f
      exact Module.projective_lifting_property (R := ℤ) (P := ↥(C.X k)) (M := ℚ)
        (N := AddCircle (1 : ℚ)) ratToQZ f coeffConn_ratToQZ_surjective
  have hS : S.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact S hdeg
  have hij : (ComplexShape.up ℕ).Rel (n - 1) n := by
    rw [ComplexShape.up_Rel]
    omega
  exact ⟨hS.δIso (n - 1) n hij h1 h2⟩

end

end Work.Pi6.EFACTS
