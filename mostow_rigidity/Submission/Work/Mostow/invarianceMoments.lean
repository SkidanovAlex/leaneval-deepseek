import Mathlib
import Submission.Work.Mostow.integral_comp_eq_of_map_eq
import Submission.Work.Mostow.integrable_inner_mul
import Submission.Work.Mostow.integral_inner_self_eq_one

namespace Work.Mostow

open MeasureTheory

noncomputable section

/-- The bilinear "second moment" form `(v,w) ↦ ∫ ξ, ⟪ξ,v⟫ * ⟪ξ,w⟫ ∂ν`. -/
def momForm {n : ℕ} (ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))
    (v w : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ ξ, (inner ℝ ξ v) * (inner ℝ ξ w) ∂ν

/-- The associated quadratic form `v ↦ ∫ ξ, ⟪ξ,v⟫ ^ 2 ∂ν`. -/
def momQuad {n : ℕ} (ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))
    (v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ ξ, (inner ℝ ξ v) ^ 2 ∂ν

theorem invarianceMoments {n : ℕ} (ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))
    [MeasureTheory.IsProbabilityMeasure ν]
    (hsupp : ν (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)ᶜ = 0)
    (hinv : ∀ A : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n), ν.map A = ν)
    (htrans : ∀ e u : EuclideanSpace ℝ (Fin n), ‖e‖ = 1 → ‖u‖ = 1 →
      ∃ A : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n), A e = u) :
    (∫ ξ, ξ ∂ν) = 0 ∧
    (∀ v w : EuclideanSpace ℝ (Fin n),
      ∫ ξ, (inner ℝ ξ v) * (inner ℝ ξ w) ∂ν = (inner ℝ v w) / n) := by
  by_cases hn : n = 0
  · -- degenerate case: the sphere is empty, contradicting the probability axiom
    subst hn
    exfalso
    have huniv : ν Set.univ = 0 := by
      refine measure_mono_null (fun x _ => ?_) hsupp
      intro hx
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx
      have hx0 : x = 0 := Subsingleton.elim x 0
      rw [hx0, norm_zero] at hx
      exact absurd hx (by norm_num)
    rw [measure_univ] at huniv
    exact one_ne_zero huniv
  · have hae : ∀ᵐ ξ ∂ν, ‖ξ‖ = 1 := by
      rw [ae_iff]
      have hset : {ξ : EuclideanSpace ℝ (Fin n) | ¬ ‖ξ‖ = 1} =
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)ᶜ := by
        ext x
        simp
      rw [hset]
      exact hsupp
    -- integrability of the second-moment integrands
    have hInt : ∀ v w : EuclideanSpace ℝ (Fin n),
        Integrable (fun ξ => (inner ℝ ξ v) * (inner ℝ ξ w)) ν :=
      fun v w => integrable_inner_mul ν hsupp v w
    have hInt_sq : ∀ x : EuclideanSpace ℝ (Fin n),
        Integrable (fun ξ => (inner ℝ ξ x) ^ 2) ν := by
      intro x
      convert hInt x x using 1
      ext ξ; rw [pow_two]
    -- ## First moment vanishes
    have hvec : ∫ ξ, ξ ∂ν = 0 := by
      have hnegmap : ν.map (LinearIsometryEquiv.neg ℝ) = ν := hinv _
      have hcomp := integral_comp_eq_of_map_eq (μ := ν)
        (LinearIsometryEquiv.neg ℝ).continuous.measurable hnegmap
        (fun ξ : EuclideanSpace ℝ (Fin n) => ξ) measurable_id.aestronglyMeasurable
      have hnegfun : (LinearIsometryEquiv.neg ℝ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =
          fun x => -x := by funext x; rfl
      rw [hnegfun, MeasureTheory.integral_neg] at hcomp
      have hII : (∫ ξ, ξ ∂ν) + (∫ ξ, ξ ∂ν) = 0 := (eq_neg_iff_add_eq_zero).mp hcomp.symm
      have h2 : (2 : ℝ) • (∫ ξ, ξ ∂ν) = 0 := by rw [two_smul ℝ]; exact hII
      exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
    -- ## Invariance of the second-moment form
    have hBinv : ∀ (A : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
        (v w : EuclideanSpace ℝ (Fin n)), momForm ν (A v) (A w) = momForm ν v w := by
      intro A v w
      have hmap : ν.map A.symm = ν := hinv A.symm
      have hstep : (fun ξ : EuclideanSpace ℝ (Fin n) => (inner ℝ ξ (A v)) * (inner ℝ ξ (A w)))
          = (fun ξ : EuclideanSpace ℝ (Fin n) =>
              (inner ℝ (A.symm ξ) v) * (inner ℝ (A.symm ξ) w)) := by
        funext ξ
        have e1 : inner ℝ ξ (A v) = inner ℝ (A.symm ξ) v := by
          have h := A.inner_map_map (A.symm ξ) v
          rwa [A.apply_symm_apply] at h
        have e2 : inner ℝ ξ (A w) = inner ℝ (A.symm ξ) w := by
          have h := A.inner_map_map (A.symm ξ) w
          rwa [A.apply_symm_apply] at h
        rw [e1, e2]
      change (∫ ξ, (inner ℝ ξ (A v)) * (inner ℝ ξ (A w)) ∂ν)
        = ∫ ξ, (inner ℝ ξ v) * (inner ℝ ξ w) ∂ν
      rw [hstep]
      exact integral_comp_eq_of_map_eq (μ := ν) A.symm.continuous.measurable hmap
        (fun ξ => (inner ℝ ξ v) * (inner ℝ ξ w)) (hInt v w).aestronglyMeasurable
    have hQB : ∀ v : EuclideanSpace ℝ (Fin n), momQuad ν v = momForm ν v v := by
      intro v
      change (∫ ξ, (inner ℝ ξ v) ^ 2 ∂ν) = ∫ ξ, (inner ℝ ξ v) * (inner ℝ ξ v) ∂ν
      simp only [pow_two]
    have hQinv : ∀ (A : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
        (v : EuclideanSpace ℝ (Fin n)), momQuad ν (A v) = momQuad ν v := by
      intro A v
      rw [hQB, hQB]
      exact hBinv A v v
    have hhom : ∀ (r : ℝ) (u : EuclideanSpace ℝ (Fin n)),
        momQuad ν (r • u) = r ^ 2 * momQuad ν u := by
      intro r u
      change (∫ ξ, (inner ℝ ξ (r • u)) ^ 2 ∂ν) = r ^ 2 * ∫ ξ, (inner ℝ ξ u) ^ 2 ∂ν
      have hfun : (fun ξ : EuclideanSpace ℝ (Fin n) => (inner ℝ ξ (r • u)) ^ 2)
          = fun ξ : EuclideanSpace ℝ (Fin n) => r ^ 2 * (inner ℝ ξ u) ^ 2 := by
        funext ξ
        rw [real_inner_smul_right, mul_pow]
      rw [hfun, MeasureTheory.integral_const_mul]
    -- ## The quadratic form depends only on the norm
    have hQnorm : ∀ v w : EuclideanSpace ℝ (Fin n), ‖v‖ = ‖w‖ → momQuad ν v = momQuad ν w := by
      intro v w hvw
      by_cases hv : v = 0
      · subst hv
        have hw : w = 0 := by
          have h : ‖w‖ = 0 := by rw [← hvw]; exact norm_zero
          exact norm_eq_zero.mp h
        subst hw
        rfl
      · have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
        have hwn : 0 < ‖w‖ := by rw [← hvw]; exact hvn
        set ê : EuclideanSpace ℝ (Fin n) := ‖v‖⁻¹ • v with hê
        set û : EuclideanSpace ℝ (Fin n) := ‖w‖⁻¹ • w with hû
        have hên : ‖ê‖ = 1 := by
          rw [hê, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvn),
            inv_mul_cancel₀ (ne_of_gt hvn)]
        have hûn : ‖û‖ = 1 := by
          rw [hû, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwn),
            inv_mul_cancel₀ (ne_of_gt hwn)]
        obtain ⟨A, hA⟩ := htrans ê û hên hûn
        have hv_eq : ‖v‖ • ê = v := by rw [hê, smul_inv_smul₀ (ne_of_gt hvn)]
        have hw_eq : ‖w‖ • û = w := by rw [hû, smul_inv_smul₀ (ne_of_gt hwn)]
        calc momQuad ν v = momQuad ν (‖v‖ • ê) := by rw [hv_eq]
          _ = ‖v‖ ^ 2 * momQuad ν ê := hhom ‖v‖ ê
          _ = ‖w‖ ^ 2 * momQuad ν û := by rw [← hQinv A ê, hA, hvw]
          _ = momQuad ν (‖w‖ • û) := (hhom ‖w‖ û).symm
          _ = momQuad ν w := by rw [hw_eq]
    -- ## The value of the quadratic form on the norm: `c = Q (unit)`
    have hpos : 0 < n := Nat.pos_of_ne_zero hn
    let b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := EuclideanSpace.basisFun (Fin n) ℝ
    let i₀ : Fin n := ⟨0, hpos⟩
    let c : ℝ := momQuad ν (b i₀)
    have hQv : ∀ v : EuclideanSpace ℝ (Fin n), momQuad ν v = c * ‖v‖ ^ 2 := by
      intro v
      by_cases hv : v = 0
      · subst hv
        rw [hQB]
        change (∫ ξ, (inner ℝ ξ (0 : EuclideanSpace ℝ (Fin n)))
            * (inner ℝ ξ (0 : EuclideanSpace ℝ (Fin n))) ∂ν)
          = c * ‖(0 : EuclideanSpace ℝ (Fin n))‖ ^ 2
        simp [inner_zero_right]
      · have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
        set ê : EuclideanSpace ℝ (Fin n) := ‖v‖⁻¹ • v with hê
        have hên : ‖ê‖ = 1 := by
          rw [hê, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvn),
            inv_mul_cancel₀ (ne_of_gt hvn)]
        have hv_eq : ‖v‖ • ê = v := by rw [hê, smul_inv_smul₀ (ne_of_gt hvn)]
        have hQê : momQuad ν ê = c := hQnorm ê (b i₀) (by rw [hên, b.norm_eq_one i₀])
        calc momQuad ν v = momQuad ν (‖v‖ • ê) := by rw [hv_eq]
          _ = ‖v‖ ^ 2 * momQuad ν ê := hhom ‖v‖ ê
          _ = ‖v‖ ^ 2 * c := by rw [hQê]
          _ = c * ‖v‖ ^ 2 := by rw [mul_comm]
    -- ## The trace normalisation `n * c = 1`
    have hInnerSelf : ∫ ξ, inner ℝ ξ ξ ∂ν = 1 := integral_inner_self_eq_one ν hsupp
    have hsum : (∑ i : Fin n, momQuad ν (b i)) = 1 := by
      have hstep : (∑ i : Fin n, momQuad ν (b i))
          = ∫ ξ, (∑ i : Fin n, (inner ℝ ξ (b i)) ^ 2) ∂ν := by
        change (∑ i : Fin n, ∫ ξ, (inner ℝ ξ (b i)) ^ 2 ∂ν)
          = ∫ ξ, (∑ i : Fin n, (inner ℝ ξ (b i)) ^ 2) ∂ν
        exact (MeasureTheory.integral_finsetSum (Finset.univ) (fun i _ => hInt_sq (b i))).symm
      rw [hstep]
      have hfun : (fun ξ : EuclideanSpace ℝ (Fin n) => ∑ i : Fin n, (inner ℝ ξ (b i)) ^ 2)
          = fun ξ : EuclideanSpace ℝ (Fin n) => inner ℝ ξ ξ := by
        funext ξ
        rw [← b.sum_inner_mul_inner ξ ξ]
        apply Finset.sum_congr rfl
        intro i _
        rw [real_inner_comm (b i) ξ, pow_two]
      rw [hfun]
      exact hInnerSelf
    have hnc : (n : ℝ) * c = 1 := by
      have h1 : (∑ i : Fin n, momQuad ν (b i)) = (n : ℝ) * c := by
        have hpt : ∀ i : Fin n, momQuad ν (b i) = c := by
          intro i
          rw [hQv (b i), b.norm_eq_one i]
          ring
        rw [Finset.sum_congr rfl (fun i _ => hpt i)]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← h1]
      exact hsum
    have hc_eq : c = 1 / n := by
      rw [eq_div_iff (Nat.cast_ne_zero.mpr hn), mul_comm]
      exact hnc
    -- ## Polarisation: `B(v,w) = c ⟪v,w⟫`
    have hnorm : ∀ v w : EuclideanSpace ℝ (Fin n),
        ‖v + w‖ ^ 2 - ‖v - w‖ ^ 2 = 4 * inner ℝ v w := by
      intro v w
      rw [norm_add_sq_real, norm_sub_sq_real]
      ring
    have hpol : ∀ v w : EuclideanSpace ℝ (Fin n), momForm ν v w = c * inner ℝ v w := by
      intro v w
      have hkey : (fun ξ : EuclideanSpace ℝ (Fin n) =>
            (inner ℝ ξ (v + w)) ^ 2 - (inner ℝ ξ (v - w)) ^ 2)
          = fun ξ : EuclideanSpace ℝ (Fin n) => 4 * ((inner ℝ ξ v) * (inner ℝ ξ w)) := by
        funext ξ
        rw [inner_add_right, inner_sub_right]
        ring
      have h1 : (∫ ξ, ((inner ℝ ξ (v + w)) ^ 2 - (inner ℝ ξ (v - w)) ^ 2) ∂ν)
          = 4 * momForm ν v w := by
        rw [hkey, MeasureTheory.integral_const_mul]
        rfl
      have h2 : (∫ ξ, ((inner ℝ ξ (v + w)) ^ 2 - (inner ℝ ξ (v - w)) ^ 2) ∂ν)
          = momQuad ν (v + w) - momQuad ν (v - w) := by
        rw [MeasureTheory.integral_sub (hInt_sq (v + w)) (hInt_sq (v - w))]
        rfl
      have h3 : momQuad ν (v + w) - momQuad ν (v - w) = 4 * (c * inner ℝ v w) := by
        rw [hQv (v + w), hQv (v - w), ← mul_sub, hnorm v w]
        ring
      have h4 : 4 * momForm ν v w = 4 * (c * inner ℝ v w) := (h1.symm.trans h2).trans h3
      exact mul_left_cancel₀ (by norm_num : (4 : ℝ) ≠ 0) h4
    refine ⟨hvec, ?_⟩
    intro v w
    change momForm ν v w = inner ℝ v w / n
    rw [hpol v w, hc_eq, one_div, div_eq_mul_inv, mul_comm]

end

end Work.Mostow
