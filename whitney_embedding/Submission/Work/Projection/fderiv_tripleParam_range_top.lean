import Mathlib
import Submission.Work.Whitney.TripleLocusDefs
import Submission.Work.Projection.range_sup_eq_top_of_det_ne_zero_smooth
import Submission.Work.Projection.fderiv_pairZ_smooth
import Submission.Work.Projection.hasFDerivAt_projVec_bilinear
import Submission.Work.Projection.mfderiv_projVec_range_eq
import Submission.Work.Projection.fderiv_tripleParam_apply_chart

namespace Work.Projection

open scoped Manifold ContDiff
open Topology

/-! ## The linear algebra of the last step

The derivative of the triple parametrisation at a point of `tripleDomTrans` is
`(δv, δu) ↦ (P_u (Dq (δv 1)) - P_u (Dp (δv 0)) - α • δu, P_u (Dr (δv 2)) - P_u (Dp (δv 0)) - β • δu)`
and its surjectivity is the following abstract fact: only the two ranges
`range (P_u ∘ Dp)` and `range (P_u ∘ Dq)` (which span everything by transversality of the double
point `(x,y)`) together with the two *different* non-zero scalars `α`, `β` matter; the range of the
third derivative is irrelevant because the second equation is absorbed by `β • δu`. -/

/-- **Linear algebra of the triple point submersion.**  Let `f0`, `f1`, `f2` be linear maps
`V → W` with `range f0 ⊔ range f1 = ⊤`, and let `α ≠ 0`, `β ≠ 0`, `α ≠ β`.  Then
`(v, u) ↦ (f1 (v 1) - f0 (v 0) - α • u, f2 (v 2) - f0 (v 0) - β • u)` is surjective
(`range f2` is unconstrained: the second equation is absorbed by `β • u`). -/
theorem linear_surj_tripleParam_aux {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (f0 f1 f2 : V →ₗ[ℝ] W) (hsup : f0.range ⊔ f1.range = ⊤)
    {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (hαβ : α ≠ β) :
    Function.Surjective (fun y : (Fin 3 → V) × W =>
      (f1 (y.1 1) - f0 (y.1 0) - α • y.2, f2 (y.1 2) - f0 (y.1 0) - β • y.2)) := by
  rintro ⟨s1, s2⟩
  have hmem : β • s1 - α • s2 ∈ f0.range ⊔ f1.range := by
    rw [hsup]; exact Submodule.mem_top
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨v0, hv0⟩ := LinearMap.mem_range.mp (Submodule.smul_mem f0.range (α - β)⁻¹ hp)
  obtain ⟨v1, hv1⟩ := LinearMap.mem_range.mp (Submodule.smul_mem f1.range β⁻¹ hq)
  have hαβ' : α - β ≠ 0 := sub_ne_zero.mpr hαβ
  have hkey : (α - β) • (f0 v0) + β • (f1 v1) = β • s1 - α • s2 := by
    rw [hv0, hv1, smul_inv_smul₀ hαβ', smul_inv_smul₀ hβ]
    exact hpq
  set u : W := α⁻¹ • (f1 v1 - f0 v0 - s1) with hu_def
  have hu : α • u = f1 v1 - f0 v0 - s1 := by
    rw [hu_def]; exact smul_inv_smul₀ hα _
  have hkey' : α • (f0 v0) + β • (f1 v1) = (β • s1 - α • s2) + β • (f0 v0) := by
    have h := hkey
    rw [sub_smul] at h
    rw [← h]; abel
  refine ⟨(![v0, v1, (0 : V)], u), ?_⟩
  have hw0 : (![v0, v1, (0 : V)] : Fin 3 → V) 0 = v0 := by simp
  have hw1 : (![v0, v1, (0 : V)] : Fin 3 → V) 1 = v1 := by simp
  have hw2 : (![v0, v1, (0 : V)] : Fin 3 → V) 2 = 0 := by simp
  refine Prod.ext ?_ ?_
  · dsimp only
    rw [hw1, hw0, hu]; abel
  · dsimp only
    rw [hw2, hw0, map_zero, zero_sub]
    have hcomm : α • (β • u) = β • (f1 v1 - f0 v0 - s1) := by
      rw [smul_smul, mul_comm, ← smul_smul, hu]
    have hA : α • (- f0 v0 - β • u - s2)
        = -(α • (f0 v0) + β • (f1 v1)) + (β • (f0 v0) + β • s1 - α • s2) := by
      rw [smul_sub, smul_sub, smul_neg, hcomm, smul_sub, smul_sub]
      abel
    have h1 : α • (- f0 v0 - β • u - s2) = 0 := by
      rw [hA, hkey']; abel
    have h2 : - f0 v0 - β • u - s2 = 0 := (smul_eq_zero.mp h1).resolve_left hα
    exact sub_eq_zero.mp h2

/-- **The triple parametrisation is a submersion where the pair `(x,y)` is transverse.**

`tripleParam e p q r` (defined in `Submission.Work.Whitney.TripleLocusDefs`) sends a triple of
chart parameters `(v 0, v 1, v 2)` and a direction `u` to
`(projVec u (e y - e x), projVec u (e z - e x))`, so its zero set describes the directions `u` for
which the three chart points are collapsed to one point by `projVec u ∘ e`.

Let `x = (chartAt p).symm (v 0)` and `y = (chartAt q).symm (v 1)`, and suppose that `(v, u)` lies
in `tripleDomTrans e p q r`.  Unfolding `Submission.Work.Whitney.TripleLocusDefs`, this means:
the three chart parameters lie in the chart targets; the last coordinates
`α = (pairZ e p q (v 0, v 1)) last` and `β = (pairZ e p r (v 0, v 2)) last` are non-zero and
**different**; and `det (fderiv (pairParam e p q)) (v 0, v 1) ≠ 0`, i.e. the double point `(x,y)`
is transverse.  Assume moreover that `tripleParam e p q r (v, u) = 0`.  Then the derivative of
`tripleParam e p q r` at `(v, u)` is surjective.

Writing `w₁ = pairZ e p q (v 0, v 1)`, `w₂ = pairZ e p r (v 0, v 2)`, `P_u = projVec u` and
`D w₁`, `D w₂` for the derivatives of the two components with respect to the chart parameters, the
derivative of `tripleParam` sends `(δv, δu)` to
`(P_u (D w₁ δv) - α • δu, P_u (D w₂ δv) - β • δu)`
(`Work.Projection.fderiv_tripleParam_apply_chart`).

From `tripleParam e p q r (v, u) = 0` and `α ≠ 0` one gets `u = extract (w₁)`, hence
`pairDirPt e p q ((chartAt p).symm (v 0)) ((chartAt q).symm (v 1)) = u`, so
`Work.Projection.range_sup_eq_top_of_det_ne_zero_smooth` with the non-vanishing determinant gives
`range (P_u ∘ fderiv (chartRep e p)) ⊔ range (P_u ∘ fderiv (chartRep e q)) = ⊤`
(rewriting the two `mfderiv` ranges with `Work.Projection.mfderiv_projVec_range_eq`); call this
subspace `A`.  The surjectivity of the derivative then follows from
`Work.Projection.linear_surj_tripleParam_aux`, where the range of the `r`-derivative is irrelevant
and `α ≠ β` is what allows the two equations to be combined. -/
theorem fderiv_tripleParam_range_top {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) e)
    (p q r : M) (x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)))
    (hx : x ∈ tripleDomTrans e p q r) (h0 : tripleParam e p q r x = 0) :
    (fderiv ℝ (tripleParam e p q r) x).range = ⊤ := by
  rw [mem_tripleDomTrans] at hx
  obtain ⟨hxD, hdet⟩ := hx
  rw [mem_tripleDom] at hxD
  obtain ⟨hv0, hv1, hv2, hα, hβ, hαβ⟩ := hxD
  set xp : M := (chartAt (EuclideanSpace ℝ (Fin n)) p).symm (x.1 0) with hxp_def
  set yq : M := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm (x.1 1) with hyq_def
  have hchartp : (chartAt (EuclideanSpace ℝ (Fin n)) p) xp = x.1 0 := by
    rw [hxp_def]; exact (chartAt (EuclideanSpace ℝ (Fin n)) p).right_inv hv0
  have hchartq : (chartAt (EuclideanSpace ℝ (Fin n)) q) yq = x.1 1 := by
    rw [hyq_def]; exact (chartAt (EuclideanSpace ℝ (Fin n)) q).right_inv hv1
  have hxps : xp ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source :=
    (chartAt (EuclideanSpace ℝ (Fin n)) p).map_target hv0
  have hyqs : yq ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).source :=
    (chartAt (EuclideanSpace ℝ (Fin n)) q).map_target hv1
  have hu : x.2 = pairDirPt e p q xp yq := by
    have h01 : projVec x.2 (pairZ e p q (x.1 0, x.1 1)) = 0 :=
      (tripleParam_eq_zero_iff.mp h0).1
    obtain ⟨c, hc⟩ := (projVec_eq_zero_iff x.2 (pairZ e p q (x.1 0, x.1 1))).mp h01
    have hcα : c = (pairZ e p q (x.1 0, x.1 1)) (Fin.last (2 * n)) := by
      have h := congrArg (fun z : EuclideanSpace ℝ (Fin (2 * n + 1)) => z (Fin.last (2 * n))) hc
      simpa using h.symm
    have hne : c ≠ 0 := by rw [hcα]; exact hα
    have hext : extract (pairZ e p q (x.1 0, x.1 1)) = x.2 := by
      rw [hc]; exact extract_smul_vVec x.2 hne
    simp only [pairDirPt, pairDir, hchartp, hchartq]
    exact hext.symm
  have hzp : (pairZ e p q ((chartAt (EuclideanSpace ℝ (Fin n)) p) xp,
      (chartAt (EuclideanSpace ℝ (Fin n)) q) yq)) (Fin.last (2 * n)) ≠ 0 := by
    rw [hchartp, hchartq]; exact hα
  have hdetp : (fderiv ℝ (pairParam e p q) ((chartAt (EuclideanSpace ℝ (Fin n)) p) xp,
      (chartAt (EuclideanSpace ℝ (Fin n)) q) yq)).det ≠ 0 := by
    rw [hchartp, hchartq]; exact hdet
  have hsup0 := range_sup_eq_top_of_det_ne_zero_smooth e he p q xp yq hxps hyqs hzp hdetp
  rw [← hu] at hsup0
  rw [mfderiv_projVec_range_eq e he p xp hxps x.2,
      mfderiv_projVec_range_eq e he q yq hyqs x.2] at hsup0
  rw [hchartp, hchartq] at hsup0
  rw [LinearMap.range_eq_top]
  intro z
  have hpoint := fderiv_tripleParam_apply_chart e he p q r x hv0 hv1 hv2
  have hsurj := linear_surj_tripleParam_aux (V := EuclideanSpace ℝ (Fin n))
    (W := EuclideanSpace ℝ (Fin (2 * n)))
    ((projVec x.2).comp (fderiv ℝ (chartRep e p) (x.1 0)))
    ((projVec x.2).comp (fderiv ℝ (chartRep e q) (x.1 1)))
    ((projVec x.2).comp (fderiv ℝ (chartRep e r) (x.1 2)))
    hsup0 hα hβ hαβ
  obtain ⟨y, hy⟩ := hsurj z
  refine ⟨y, ?_⟩
  change (fderiv ℝ (tripleParam e p q r) x) y = z
  rw [hpoint y]
  exact hy

end Work.Projection
