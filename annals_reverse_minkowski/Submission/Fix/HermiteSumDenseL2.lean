-- ⚠ IMPORT-CLASH WORKAROUND (session 123): verbatim copy of Submission.Commons.Analysis.GaussianMeasure.hermite_sum_dense_L2
-- with the import chain redirected so that the duplicate constant `toLp_norm_sq` of
-- `…bobkov_strong_nD` is not pulled into the same environment as
-- `…brascamp_lieb_truncated`.  Do not import both this file and the commons original.
import Mathlib
import Submission.Fix.HermiteProductDenseL2
import Submission.HermiteProductMemLp

open MeasureTheory
open scoped BigOperators ENNReal

namespace Commons.Analysis.GaussianMeasure

noncomputable section

/-- The Gaussian measure with density `exp (-‖x‖^2 / 2)` on `ℝ^N`. -/
private abbrev gaussN (N : ℕ) : Measure (EuclideanSpace ℝ (Fin N)) :=
  volume.withDensity (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))

/-- The tensor product of Hermite polynomials indexed by `α`. -/
private abbrev hermFun {N : ℕ} (α : Fin N → ℕ) : EuclideanSpace ℝ (Fin N) → ℝ :=
  fun x => ∏ i, Polynomial.aeval (x.ofLp i) (Polynomial.hermite (α i))

/-- The corresponding element of `L²`. -/
private def hermToLp {N : ℕ} (α : Fin N → ℕ) : Lp ℝ 2 (gaussN N) :=
  (memLp_hermite_product α).toLp (hermFun α)

private lemma hermToLp_coeFn {N : ℕ} (α : Fin N → ℕ) :
    ⇑(hermToLp α) =ᵐ[gaussN N] hermFun α :=
  MemLp.coeFn_toLp (memLp_hermite_product α)

/-- Coercion of a finite sum in `L²` to the pointwise finite sum. -/
private lemma coeFn_finset_sum {N : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Lp ℝ 2 (gaussN N)) :
    (∑ i ∈ s, f i : Lp ℝ 2 (gaussN N)) =ᵐ[gaussN N] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction with
  | empty =>
      have hR : (fun x : EuclideanSpace ℝ (Fin N) => ∑ i ∈ (∅ : Finset ι), f i x)
          = (0 : EuclideanSpace ℝ (Fin N) → ℝ) := by funext x; simp
      rw [hR, Finset.sum_empty]
      exact Lp.coeFn_zero ℝ 2 (gaussN N)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x h1 h2
      rw [h1, Pi.add_apply, h2, Finset.sum_insert ha]

/-- Coercion of a finite sum of scalar multiples in `L²`. -/
private lemma coeFn_finset_sum_smul {N : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (f : ι → Lp ℝ 2 (gaussN N)) :
    (∑ i ∈ s, c i • f i : Lp ℝ 2 (gaussN N)) =ᵐ[gaussN N] fun x => ∑ i ∈ s, c i * f i x := by
  classical
  induction s using Finset.induction with
  | empty =>
      have hR : (fun x : EuclideanSpace ℝ (Fin N) => ∑ i ∈ (∅ : Finset ι), c i * f i x)
          = (0 : EuclideanSpace ℝ (Fin N) → ℝ) := by funext x; simp
      rw [hR, Finset.sum_empty]
      exact Lp.coeFn_zero ℝ 2 (gaussN N)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (c a • f a) (∑ i ∈ s, c i • f i),
        Lp.coeFn_smul (c a) (f a), ih] with x h1 h2 h3
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul, h3, Finset.sum_insert ha]

/-- Combining finitely many almost-everywhere equalities of functions. -/
private lemma ae_eq_finset_sum {ι : Type*} {N : ℕ} (s : Finset ι)
    (u v : ι → EuclideanSpace ℝ (Fin N) → ℝ)
    (h : ∀ i ∈ s, u i =ᵐ[gaussN N] v i) :
    (fun x => ∑ i ∈ s, u i x) =ᵐ[gaussN N] fun x => ∑ i ∈ s, v i x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have h1 : u a =ᵐ[gaussN N] v a := h a (Finset.mem_insert_self a s)
      have h2 : (fun x => ∑ i ∈ s, u i x) =ᵐ[gaussN N] fun x => ∑ i ∈ s, v i x :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      filter_upwards [h1, h2] with x hx hxs
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hx, hxs]

/-- The span of the Hermite tensor products is dense in `L²` of the Gaussian measure. -/
private lemma dense_hermite_span {N : ℕ} (f : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf : MemLp f 2 (gaussN N)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : Finset (Fin N → ℕ)) (c : (Fin N → ℕ) → ℝ),
      ∫ x, (f x - ∑ α ∈ s, c α * (∏ i, Polynomial.aeval (x.ofLp i) (Polynomial.hermite (α i)))) ^ 2
        ∂(gaussN N) < ε ^ 2 := by
  classical
  let S : Submodule ℝ (Lp ℝ 2 (gaussN N)) :=
    Submodule.span ℝ (Set.range (hermToLp (N := N)))
  have hSorth : Sᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro G hG
    rw [Submodule.mem_orthogonal] at hG
    have hGint : ∀ α : Fin N → ℕ, ∫ a, G a * hermFun α a ∂(gaussN N) = 0 := by
      intro α
      have hmem : hermToLp α ∈ S := Submodule.subset_span (Set.mem_range_self α)
      have h1 := hG (hermToLp α) hmem
      rw [L2.inner_def] at h1
      rw [← h1]
      apply integral_congr_ae
      filter_upwards [hermToLp_coeFn α] with a ha
      rw [ha, RCLike.inner_apply]
      simp
    have hz := hermite_product_dense_L2 G (Lp.memLp G) hGint
    exact Lp.ext (hz.trans (Lp.coeFn_zero ℝ 2 (gaussN N)).symm)
  have htop : S.topologicalClosure = ⊤ := Submodule.topologicalClosure_eq_top_iff.mpr hSorth
  have hmem : hf.toLp f ∈ (S.topologicalClosure : Set (Lp ℝ 2 (gaussN N))) := by
    rw [htop]; trivial
  rw [Submodule.topologicalClosure_coe] at hmem
  obtain ⟨y, hyS, hdist⟩ := (Metric.mem_closure_iff.mp hmem) ε hε
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
    (show y ∈ Submodule.span ℝ (Set.range (hermToLp (N := N))) from hyS)
  refine ⟨c.support, fun α => c α, ?_⟩
  set g : Lp ℝ 2 (gaussN N) := c.sum (fun i a => a • hermToLp i) with hg
  have hgcoe : ⇑g =ᵐ[gaussN N] fun x => ∑ α ∈ c.support, c α * hermFun α x := by
    have h1 : g = ∑ i ∈ c.support, c i • hermToLp i := by
      rw [hg]; simp [Finsupp.sum]
    rw [h1]
    refine (coeFn_finset_sum_smul c.support c (fun i => hermToLp i)).trans ?_
    refine ae_eq_finset_sum c.support (fun i _ => c i * (hermToLp i) _)
      (fun i _ => c i * hermFun i _) (fun i _ => ?_)
    filter_upwards [hermToLp_coeFn i] with x hx
    rw [hx]
  have hgy : g = y := by rw [hg]; exact hc
  have hsq : ‖hf.toLp f - g‖ ^ 2 < ε ^ 2 := by
    have hlt : ‖hf.toLp f - g‖ < ε := by rw [hgy]; simpa [dist_eq_norm] using hdist
    nlinarith [hlt, norm_nonneg (hf.toLp f - g), hε]
  have hcoe : ⇑(hf.toLp f - g) =ᵐ[gaussN N]
      fun x => f x - ∑ α ∈ c.support, c α * hermFun α x := by
    filter_upwards [hf.coeFn_toLp, Lp.coeFn_sub (hf.toLp f) g, hgcoe] with x h1 h2 h3
    rw [h2, Pi.sub_apply, h1, h3]
  have hint : ∫ x, (f x - ∑ α ∈ c.support, c α * hermFun α x) ^ 2 ∂(gaussN N)
      = inner ℝ (hf.toLp f - g) (hf.toLp f - g) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hcoe] with x hx
    rw [← hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  rw [hint, real_inner_self_eq_norm_sq]
  exact hsq

theorem hermite_sum_dense_L2 {N : ℕ} (f : EuclideanSpace ℝ (Fin N) → ℝ) (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.withDensity (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2))))) (ε : ℝ) (hε : 0 < ε) : ∃ (s : Finset (Fin N → ℕ)) (c : (Fin N → ℕ) → ℝ), ∫ x : EuclideanSpace ℝ (Fin N), (f x - ∑ α ∈ s, c α * ∏ i, Polynomial.aeval (x.ofLp i) (Polynomial.hermite (α i))) ^ 2 ∂(MeasureTheory.volume.withDensity (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))) < ε ^ 2 := by
  simpa only [gaussN] using dense_hermite_span f hf ε hε

end

end Commons.Analysis.GaussianMeasure
