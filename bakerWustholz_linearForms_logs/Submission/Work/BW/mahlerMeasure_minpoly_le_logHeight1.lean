import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Mahler measure of a minimal polynomial vs. the Weil height

For an algebraic integer `β` in a number field `K`, the Mahler measure of its minimal
polynomial (viewed over `ℂ`) is at most `exp (logHeight₁ β)` where `Height.logHeight₁` is the
unnormalised (relative to `K`) logarithmic height.

The proof decomposes the height into its archimedean and non-archimedean parts.

* The archimedean part `∑_v mult(v) · log⁺|β|_v` equals the sum `∑_φ log⁺‖φ β‖` over all
  complex embeddings `φ : K →+* ℂ` (grouping embeddings by infinite place).
* Each embedding value `φ β` is a root of `minpoly ℚ β`, and every root of `minpoly ℤ β` over
  `ℂ` occurs as `φ β` for some embedding; hence the Mahler measure of the (monic, separable)
  minimal polynomial — whose logarithmic form is the sum of `log⁺‖·‖` over its roots — is
  bounded by the embedding sum.
* The non-archimedean part is nonnegative, so it can be dropped.
-/

open Polynomial NumberField Finset Real

namespace Work.BW

/-- The logarithmic Mahler measure of `(minpoly ℤ β).map ℂ` is the sum of `log⁺ ‖r‖` over its
(distinct) roots (the minimal polynomial is monic). -/
private lemma log_mahlerMeasure_minpoly_map_eq_sum_roots {K : Type*} [Field K] [NumberField K]
    (β : K) (hint : IsIntegral ℤ β) :
    Real.log (((minpoly ℤ β).map (Int.castRingHom ℂ)).mahlerMeasure)
      = (((minpoly ℤ β).map (Int.castRingHom ℂ)).roots.map (fun a => log⁺ ‖a‖)).sum := by
  rw [← Polynomial.logMahlerMeasure_eq_log_MahlerMeasure,
    Polynomial.logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots]
  have hmonic : ((minpoly ℤ β).map (Int.castRingHom ℂ)).Monic := (minpoly.monic hint).map _
  rw [hmonic.leadingCoeff]
  simp

/-- The archimedean part of the height, expressed as a sum over the complex embeddings. -/
private lemma sum_infinitePlace_eq_sum_embeddings {K : Type*} [Field K] [NumberField K] (β : K) :
    ∑ v : InfinitePlace K, (v.mult : ℝ) * log⁺ (v β)
      = ∑ φ : K →+* ℂ, log⁺ ‖φ β‖ := by
  classical
  rw [show (∑ v : InfinitePlace K, (v.mult : ℝ) * log⁺ (v β))
      = ∑ w ∈ (univ : Finset (InfinitePlace K)),
          ∑ φ ∈ (univ : Finset (K →+* ℂ)).filter (fun φ => InfinitePlace.mk φ = w),
            log⁺ ((InfinitePlace.mk φ) β) from ?_]
  · rw [sum_fiberwise_of_maps_to (s := (univ : Finset (K →+* ℂ)))
      (t := (univ : Finset (InfinitePlace K))) (g := fun φ => InfinitePlace.mk φ)]
    · apply Finset.sum_congr rfl
      intro φ _
      rw [InfinitePlace.apply]
    · intro φ _
      simp
  · apply Finset.sum_congr rfl
    intro w _
    rw [show (∑ φ ∈ (univ : Finset (K →+* ℂ)).filter (fun φ => InfinitePlace.mk φ = w),
        log⁺ ((InfinitePlace.mk φ) β))
        = ∑ _φ ∈ (univ : Finset (K →+* ℂ)).filter (fun φ => InfinitePlace.mk φ = w),
            log⁺ (w β) by
      apply Finset.sum_congr rfl
      intro φ hφ
      rw [(Finset.mem_filter.mp hφ).2]]
    rw [Finset.sum_const, nsmul_eq_mul, InfinitePlace.card_filter_mk_eq]

/-- The archimedean part of the height is at most the full height. -/
private lemma sum_infinitePlace_le_logHeight₁ {K : Type*} [Field K] [NumberField K] (β : K) :
    ∑ v : InfinitePlace K, (v.mult : ℝ) * log⁺ (v β) ≤ Height.logHeight₁ β := by
  rw [NumberField.logHeight₁_eq]
  have h := finsum_nonneg (f := fun v : FinitePlace K => log⁺ (v β)) (fun _ => posLog_nonneg)
  linarith

/-- The Mahler measure of the minimal polynomial of `β`, viewed over `ℂ`, is bounded by the sum
of `log⁺ ‖φ β‖` over the complex embeddings of `K`. -/
private lemma log_mahlerMeasure_le_sum_embeddings {K : Type*} [Field K] [NumberField K] (β : K)
    (hint : IsIntegral ℤ β) :
    Real.log (((minpoly ℤ β).map (Int.castRingHom ℂ)).mahlerMeasure)
      ≤ ∑ φ : K →+* ℂ, log⁺ ‖φ β‖ := by
  classical
  have hnodup : ((minpoly ℤ β).map (Int.castRingHom ℂ)).roots.Nodup := by
    apply Polynomial.nodup_roots
    rw [show (minpoly ℤ β).map (Int.castRingHom ℂ) = (minpoly ℚ β).map (algebraMap ℚ ℂ) by
      rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint, Polynomial.map_map]; congr 1]
    exact (separable_map (algebraMap ℚ ℂ)).mpr (IsSeparable.of_integral ℚ β)
  set U := (univ : Finset (K →+* ℂ)).image (fun φ => φ β) with hU
  have hsub : ((minpoly ℤ β).map (Int.castRingHom ℂ)).roots.toFinset ⊆ U := by
    intro r hr
    rw [hU, Finset.mem_image]
    rw [Multiset.mem_toFinset, mem_roots'] at hr
    obtain ⟨_, hroot⟩ := hr
    rw [IsRoot.def] at hroot
    rw [show (minpoly ℤ β).map (Int.castRingHom ℂ) = (minpoly ℤ β).map (algebraMap ℤ ℂ) by
        rw [algebraMap_int_eq]] at hroot
    rw [eval_map_algebraMap] at hroot
    have hre : r ∈ (minpoly ℚ β).rootSet ℂ := by
      rw [Polynomial.mem_rootSet]
      refine ⟨?_, ?_⟩
      · rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint]
        exact ((minpoly.monic hint).map _).ne_zero
      · rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint, aeval_map_algebraMap]
        exact hroot
    rw [← NumberField.Embeddings.range_eval_eq_rootSet_minpoly K ℂ β] at hre
    obtain ⟨φ, hφ⟩ := hre
    exact ⟨φ, Finset.mem_univ _, hφ⟩
  calc Real.log (((minpoly ℤ β).map (Int.castRingHom ℂ)).mahlerMeasure)
      = (((minpoly ℤ β).map (Int.castRingHom ℂ)).roots.map (fun a => log⁺ ‖a‖)).sum :=
        log_mahlerMeasure_minpoly_map_eq_sum_roots β hint
    _ ≤ ∑ r ∈ ((minpoly ℤ β).map (Int.castRingHom ℂ)).roots.toFinset, log⁺ ‖r‖ := by
        rw [Finset.sum_multiset_map_count]
        apply Finset.sum_le_sum
        intro r hr
        rw [Multiset.count_eq_one_of_mem hnodup (Multiset.mem_toFinset.mp hr), one_smul]
    _ ≤ ∑ r ∈ U, log⁺ ‖r‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => posLog_nonneg)
    _ ≤ ∑ φ : K →+* ℂ, log⁺ ‖φ β‖ := by
        rw [← Finset.sum_fiberwise_of_maps_to (s := (univ : Finset (K →+* ℂ))) (t := U)
          (g := fun φ => φ β) (f := fun φ => log⁺ ‖φ β‖)
          (fun φ _ => Finset.mem_image.mpr ⟨φ, Finset.mem_univ _, rfl⟩)]
        apply Finset.sum_le_sum
        intro r hr
        have h1 : 1 ≤ ((univ : Finset (K →+* ℂ)).filter (fun φ => φ β = r)).card := by
          obtain ⟨φ, -, hφ⟩ := Finset.mem_image.mp hr
          exact Finset.card_pos.mpr ⟨φ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hφ⟩⟩
        have h2 : ∑ φ ∈ (univ : Finset (K →+* ℂ)).filter (fun φ => φ β = r), log⁺ ‖φ β‖
            = ∑ φ ∈ (univ : Finset (K →+* ℂ)).filter (fun φ => φ β = r), log⁺ ‖r‖ :=
          Finset.sum_congr rfl (fun φ hφ => by rw [(Finset.mem_filter.mp hφ).2])
        rw [h2, Finset.sum_const, nsmul_eq_mul]
        have hcard : (1:ℝ) ≤ (((univ : Finset (K →+* ℂ)).filter (fun φ => φ β = r)).card : ℝ) := by
          exact_mod_cast h1
        simpa using mul_le_mul_of_nonneg_right hcard (posLog_nonneg (x := ‖r‖))

/-- The Mahler measure of the minimal polynomial of an algebraic integer `β` in a number field `K`,
viewed over `ℂ`, is at most `exp (logHeight₁ β)`. Equivalently `log M(β) ≤ h(β)` where
`Height.logHeight₁` is the unnormalised (relative) height of `β` over `K`.

This is the standard identity: for `β` of degree `δ = [ℚ(β):ℚ]` and `[K:ℚ] = d` one has
`logHeight₁ β = (d/δ) · log M(β)`; here we only need the inequality `log M(β) ≤ logHeight₁ β`. -/
theorem mahlerMeasure_minpoly_le_logHeight1 {K : Type*} [Field K] [NumberField K] (β : K)
    (hint : IsIntegral ℤ β) :
    Real.log (((minpoly ℤ β).map (Int.castRingHom ℂ)).mahlerMeasure) ≤ Height.logHeight₁ β := by
  calc Real.log (((minpoly ℤ β).map (Int.castRingHom ℂ)).mahlerMeasure)
      ≤ ∑ φ : K →+* ℂ, log⁺ ‖φ β‖ := log_mahlerMeasure_le_sum_embeddings β hint
    _ = ∑ v : InfinitePlace K, (v.mult : ℝ) * log⁺ (v β) :=
        (sum_infinitePlace_eq_sum_embeddings β).symm
    _ ≤ Height.logHeight₁ β := sum_infinitePlace_le_logHeight₁ β

end Work.BW
