import Mathlib
import Submission.Commons.Analysis.MeasureTheory.sphere_isometry_measurableEquiv_measurePreserving
import Submission.Commons.Analysis.MeasureTheory.zonal_fibre_integral
import Submission.Commons.Analysis.InnerProductSpace.exists_orthonormalBasis_head
import Submission.Commons.Analysis.Radon.sphericalRadon_rot

namespace Commons.Analysis.Radon

open _root_.MeasureTheory
open scoped RealInnerProductSpace Pointwise Interval

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

/-! ## Auxiliary lemmas for the radial reduction of the spherical Radon transform -/

/-- The total surface measure of the unit sphere of a finite-dimensional real inner product
space depends only on the dimension. -/
theorem toSphere_real_univ_eq_of_finrank_eq {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [FiniteDimensional ℝ F] [Nontrivial F]
    (h : Module.finrank ℝ E = Module.finrank ℝ F) :
    ((volume : Measure E).toSphere).real Set.univ = ((volume : Measure F).toSphere).real Set.univ := by
  have hiso : Nonempty (E ≃ₗᵢ[ℝ] F) := by
    refine ⟨(stdOrthonormalBasis ℝ E).repr.trans ?_ |>.trans (stdOrthonormalBasis ℝ F).repr.symm⟩
    rw [h]
    exact LinearIsometryEquiv.refl ℝ _
  obtain ⟨L⟩ := hiso
  obtain ⟨e, hmp, -⟩ :=
    Commons.Analysis.MeasureTheory.sphere_isometry_measurableEquiv_measurePreserving L
  have hμν : ((volume : Measure E).toSphere : Measure (Metric.sphere (0:E) 1)) Set.univ
      = ((volume : Measure F).toSphere : Measure (Metric.sphere (0:F) 1)) Set.univ := by
    rw [← hmp.map_eq, Measure.map_apply e.measurable MeasurableSet.univ]
    simp
  rw [Measure.real, Measure.real, hμν]

/-- The fibre of `Fin k` at an index has cardinality `k - 1`. -/
lemma card_fibre_fin (k : ℕ) (i : Fin k) : Fintype.card {j : Fin k // j ≠ i} = k - 1 := by
  have h := Fintype.card_subtype_compl (fun j : Fin k => j = i)
  rw [Fintype.card_fin, Fintype.card_subtype_eq] at h
  simpa using h

/-- **Zonal (Funk–Hecke) reduction in a coordinate.**  The integral over the unit sphere of
`ℝ^k` of a function of the `i`-th coordinate reduces to the one-dimensional integral with the
weight `(1 - s²)^((k-3)/2)`, times the surface area of the unit sphere of `ℝ^(k-1)`. -/
theorem euclidean_zonal_integral {k : ℕ} (hk : 2 ≤ k) (i : Fin k) (F : ℝ → ℝ) :
    (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1,
        F ((θ : EuclideanSpace ℝ (Fin k)) i)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin k))).toSphere))
      = (((volume : Measure (EuclideanSpace ℝ (Fin (k - 1)))).toSphere).real Set.univ)
        * ∫ s in (-1 : ℝ)..1, F s * (1 - s ^ 2) ^ (((k : ℝ) - 3)/2) := by
  have hk1 : 1 ≤ k := by omega
  haveI : Nonempty {j : Fin k // j ≠ i} := by
    obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) i
    exact ⟨⟨j, hj⟩⟩
  haveI : Nonempty (Fin (k - 1)) := ⟨⟨0, by omega⟩⟩
  set C : ℝ := (((volume : Measure (EuclideanSpace ℝ (Fin (k - 1)))).toSphere).real Set.univ) with hC
  have hz := Commons.Analysis.MeasureTheory.zonal_fibre_integral (n := k) (i := i) hk F
  have hcard : Fintype.card {j : Fin k // j ≠ i} = k - 1 := card_fibre_fin k i
  have hexp : (((Fintype.card {j : Fin k // j ≠ i} : ℝ) - 2) / 2)
      = ((k : ℝ) - 3) / 2 := by
    rw [hcard]
    rw [Nat.cast_sub hk1]
    ring
  have hCW : ((((volume : Measure (EuclideanSpace ℝ {j : Fin k // j ≠ i})).toSphere).real
        Set.univ)) = C := by
    rw [hC]
    refine toSphere_real_univ_eq_of_finrank_eq ?_
    rw [finrank_euclideanSpace, finrank_euclideanSpace]
    rw [hcard]
    simp
  have hinner : ∀ t : ℝ,
      (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ {j : Fin k // j ≠ i}) 1,
          F t * (1 - t ^ 2) ^ (((Fintype.card {j : Fin k // j ≠ i} : ℝ) - 2) / 2)
          ∂((volume : Measure (EuclideanSpace ℝ {j : Fin k // j ≠ i})).toSphere))
        = (F t * (1 - t ^ 2) ^ (((k : ℝ) - 3) / 2)) * C := by
    intro t
    rw [integral_const, smul_eq_mul, hCW, hexp]
    ring
  rw [hz, hC]
  simp_rw [hinner]
  rw [setIntegral_congr_set (Ioo_ae_eq_Ioc (a := (-1:ℝ)) (b := 1))]
  rw [← intervalIntegral.integral_of_le (show (-1:ℝ) ≤ 1 by norm_num)]
  rw [intervalIntegral.integral_mul_const]
  rw [mul_comm]

/-- **Zonal reduction along a unit vector.**  For a finite-dimensional real inner product space
`V` of dimension `k ≥ 2`, a unit vector `u` and a scalar `a`, the integral of `γ (a ⟪ω, u⟫)`
over the unit sphere of `V` reduces to the one-dimensional integral with weight
`(1 - s²)^((k-3)/2)`. -/
theorem zonal_integral_unit {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    {k : ℕ} (hV : Module.finrank ℝ V = k) (hk : 2 ≤ k)
    (u : V) (hu : ‖u‖ = 1) (a : ℝ) (γ : ℝ → ℝ) :
    (∫ ω : Metric.sphere (0 : V) 1, γ (a * ⟪(ω : V), u⟫)
        ∂((volume : Measure V).toSphere))
      = (((volume : Measure (EuclideanSpace ℝ (Fin (k - 1)))).toSphere).real Set.univ)
        * ∫ s in (-1 : ℝ)..1, γ (a * s) * (1 - s ^ 2) ^ (((k : ℝ) - 3)/2) := by
  haveI : NeZero k := ⟨by omega⟩
  obtain ⟨b, hb0⟩ :=
    Commons.Analysis.InnerProductSpace.exists_orthonormalBasis_apply_eq_of_norm_eq_one
      (ι := Fin k) (by rw [hV, Fintype.card_fin]) (0 : Fin k) hu
  let L : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k) := b.repr
  have hmp := sphereCongr_measurePreserving L
  have key : (∫ ω : Metric.sphere (0 : V) 1, γ (a * ⟪(ω : V), u⟫)
        ∂((volume : Measure V).toSphere))
      = ∫ y : Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1,
          γ (a * ((y : EuclideanSpace ℝ (Fin k)) 0))
          ∂((volume : Measure (EuclideanSpace ℝ (Fin k))).toSphere) := by
    rw [← MeasureTheory.MeasurePreserving.integral_comp' hmp
      (fun y : Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 =>
        γ (a * ((y : EuclideanSpace ℝ (Fin k)) 0)))]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with ω
    have hcoord : ((↑(sphereCongr L ω) : EuclideanSpace ℝ (Fin k)) 0) = ⟪(ω : V), u⟫ := by
      rw [sphereCongr_apply L ω]
      rw [show ((L ω : EuclideanSpace ℝ (Fin k)) 0) = (b.repr ω).ofLp 0 from rfl]
      rw [b.repr_apply_apply ω 0, hb0, real_inner_comm]
    rw [hcoord]
  rw [key]
  exact euclidean_zonal_integral hk 0 (fun t => γ (a * t))

/-- **Zonal reduction along an arbitrary vector.**  For a finite-dimensional real inner product
space `V` of dimension `k ≥ 2` and an arbitrary vector `w`, the integral of `γ ⟪ω, w⟫` over the
unit sphere of `V` reduces to the one-dimensional integral with weight `(1 - s²)^((k-3)/2)` and
argument `‖w‖ s`. -/
theorem zonal_integral_of_finrank {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    {k : ℕ} (hV : Module.finrank ℝ V = k) (hk : 2 ≤ k)
    (w : V) (γ : ℝ → ℝ) :
    (∫ ω : Metric.sphere (0 : V) 1, γ ⟪(ω : V), w⟫ ∂((volume : Measure V).toSphere))
      = (((volume : Measure (EuclideanSpace ℝ (Fin (k - 1)))).toSphere).real Set.univ)
        * ∫ s in (-1 : ℝ)..1, γ (‖w‖ * s) * (1 - s ^ 2) ^ (((k : ℝ) - 3)/2) := by
  haveI : Nontrivial V := Module.finrank_pos_iff.mp (by rw [hV]; omega)
  by_cases hw : w = 0
  · subst hw
    haveI : NeZero k := ⟨by omega⟩
    haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
    haveI : Nonempty (Fin (k - 1)) := ⟨⟨0, by omega⟩⟩
    have hS : ((volume : Measure V).toSphere).real Set.univ
        = (((volume : Measure (EuclideanSpace ℝ (Fin (k - 1)))).toSphere).real Set.univ)
          * ∫ s in (-1 : ℝ)..1, (1 - s ^ 2) ^ (((k : ℝ) - 3)/2) := by
      have h := euclidean_zonal_integral hk (0 : Fin k) (fun _ : ℝ => (1:ℝ))
      simp only [integral_const, smul_eq_mul, one_mul, mul_one] at h
      exact (toSphere_real_univ_eq_of_finrank_eq
        (E := V) (F := EuclideanSpace ℝ (Fin k)) (by rw [hV, finrank_euclideanSpace, Fintype.card_fin])).trans h
    have hL : (∫ ω : Metric.sphere (0 : V) 1, γ ⟪(ω : V), (0 : V)⟫
          ∂((volume : Measure V).toSphere))
        = γ 0 * ((volume : Measure V).toSphere).real Set.univ := by
      simp only [inner_zero_right]
      rw [integral_const, smul_eq_mul]
      ring
    have hR : (((volume : Measure (EuclideanSpace ℝ (Fin (k - 1)))).toSphere).real Set.univ)
          * ∫ s in (-1 : ℝ)..1, γ (‖(0 : V)‖ * s) * (1 - s ^ 2) ^ (((k : ℝ) - 3)/2)
        = γ 0 * ((volume : Measure V).toSphere).real Set.univ := by
      rw [hS, norm_zero]
      simp only [zero_mul]
      rw [intervalIntegral.integral_const_mul]
      ring
    rw [hL, hR]
  · have hwnorm : (‖w‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hw
    have hu : ‖(↑‖w‖ : ℝ)⁻¹ • w‖ = 1 := norm_smul_inv_norm hw
    have hinner : ∀ ω : V, ⟪(ω : V), w⟫ = ‖w‖ * ⟪(ω : V), (↑‖w‖ : ℝ)⁻¹ • w⟫ := by
      intro ω
      rw [inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hwnorm, one_mul]
    calc
      (∫ ω : Metric.sphere (0 : V) 1, γ ⟪(ω : V), w⟫ ∂((volume : Measure V).toSphere))
          = ∫ ω : Metric.sphere (0 : V) 1, γ (‖w‖ * ⟪(ω : V), (↑‖w‖ : ℝ)⁻¹ • w⟫)
              ∂((volume : Measure V).toSphere) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with ω
            rw [hinner ω]
      _ = (((volume : Measure (EuclideanSpace ℝ (Fin (k - 1)))).toSphere).real Set.univ)
            * ∫ s in (-1 : ℝ)..1, γ (‖w‖ * s) * (1 - s ^ 2) ^ (((k : ℝ) - 3)/2) :=
            zonal_integral_unit hV hk ((↑‖w‖ : ℝ)⁻¹ • w) hu ‖w‖ γ

/-- **Radial reduction of the spherical Radon transform.**  Let `ξ, e` be unit vectors of
`ℝᵈ` with `d ≥ 3` and `γ : ℝ → ℝ` continuous.  Then the integral of `γ ∘ ⟪·, e⟫` over the
unit sphere of the orthogonal complement of `ξ` equals the surface area of `S^{d-3}` times the
one-dimensional integral with the classical weight. -/
theorem radial_reduction_of_radonOver {d : ℕ} (hd : 3 ≤ d) (γ : ℝ → ℝ) (hγ : Continuous γ)
    (e ξ : EuclideanSpace ℝ (Fin d)) (he : ‖e‖ = 1) (hξ : ‖ξ‖ = 1) :
    (∫ ω : Metric.sphere (0 : ((ℝ ∙ ξ)ᗮ)) 1,
        γ ⟪((ω : ((ℝ ∙ ξ)ᗮ)) : EuclideanSpace ℝ (Fin d)), e⟫
        ∂(MeasureTheory.Measure.toSphere (volume : Measure ((ℝ ∙ ξ)ᗮ))))
      = ((MeasureTheory.Measure.toSphere (volume : Measure (EuclideanSpace ℝ (Fin (d - 2)))))
            Set.univ).toReal
          * ∫ s in (-1 : ℝ)..1, γ (Real.sqrt (1 - ⟪ξ, e⟫ ^ 2) * s) * (1 - s ^ 2) ^ ((d : ℝ)/2 - 2) := by
  set V : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := (ℝ ∙ ξ)ᗮ with hVdef
  have hξ0 : ξ ≠ 0 := by
    intro h; rw [h] at hξ; simp at hξ
  have hfin_span : Module.finrank ℝ (ℝ ∙ ξ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) = 1 :=
    finrank_span_singleton hξ0
  have hfin : Module.finrank ℝ V = d - 1 := by
    have h := Submodule.finrank_add_finrank_orthogonal
      (ℝ ∙ ξ : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    rw [hfin_span, finrank_euclideanSpace, Fintype.card_fin] at h
    rw [hVdef]
    omega
  have hmem : e - ⟪e, ξ⟫ • ξ ∈ V := by
    rw [hVdef, Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu
    rw [← hc, inner_smul_left]
    have hzero : ⟪ξ, e - ⟪e, ξ⟫ • ξ⟫ = 0 := by
      rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hξ,
        real_inner_comm ξ e]
      ring
    rw [hzero, mul_zero]
  let ePerp : V := ⟨e - ⟪e, ξ⟫ • ξ, hmem⟩
  have hinner_eq : ∀ ω : V, ⟪((ω : V) : EuclideanSpace ℝ (Fin d)), e⟫ = ⟪ω, ePerp⟫ := by
    intro ω
    have hωξ : ⟪((ω : V) : EuclideanSpace ℝ (Fin d)), ξ⟫ = 0 := by
      have hωmem : ((ω : V) : EuclideanSpace ℝ (Fin d)) ∈ (ℝ ∙ ξ)ᗮ := by
        rw [← hVdef]; exact ω.2
      exact Submodule.inner_left_of_mem_orthogonal (Submodule.mem_span_singleton_self ξ) hωmem
    have hdecomp : e = ((ePerp : V) : EuclideanSpace ℝ (Fin d)) + ⟪e, ξ⟫ • ξ := by
      simp [ePerp]
    rw [hdecomp, inner_add_right, inner_smul_right, hωξ, mul_zero, add_zero]
    exact (Submodule.coe_inner V ω ePerp).symm
  have hnorm_ePerp : ‖ePerp‖ = Real.sqrt (1 - ⟪ξ, e⟫ ^ 2) := by
    have hsq : ‖ePerp‖ ^ 2 = 1 - ⟪ξ, e⟫ ^ 2 := by
      have hval : ((ePerp : V) : EuclideanSpace ℝ (Fin d)) = e - ⟪e, ξ⟫ • ξ := rfl
      rw [← real_inner_self_eq_norm_sq ePerp, Submodule.coe_inner, hval]
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        real_inner_self_eq_norm_sq, hξ, he, real_inner_comm ξ e]
      ring
    rw [← Real.sqrt_sq (norm_nonneg ePerp), hsq]
  have hexp : (((d - 1 : ℕ) : ℝ) - 3) / 2 = (d : ℝ) / 2 - 2 := by
    have hd1 : 1 ≤ d := by omega
    rw [Nat.cast_sub hd1]
    ring
  have hz := zonal_integral_of_finrank (V := V) (k := d - 1) hfin (by omega) ePerp γ
  have hL : (∫ ω : Metric.sphere (0 : V) 1, γ ⟪((ω : V) : EuclideanSpace ℝ (Fin d)), e⟫
        ∂(MeasureTheory.Measure.toSphere (volume : Measure V)))
      = ∫ ω : Metric.sphere (0 : V) 1, γ ⟪(ω : V), ePerp⟫
        ∂(MeasureTheory.Measure.toSphere (volume : Measure V)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with ω
    rw [hinner_eq ω]
  rw [hL, hz]
  simp_rw [hnorm_ePerp, hexp]
  rw [Measure.real]

end Commons.Analysis.Radon
