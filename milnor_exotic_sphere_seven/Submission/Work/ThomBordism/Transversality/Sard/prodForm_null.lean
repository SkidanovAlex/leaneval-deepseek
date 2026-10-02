import Mathlib
import Submission.Work.ThomBordism.Transversality.Sard.Strat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Fubini step of rectangular Sard: `prodForm_null`

This file proves `Work.ThomBordism.Transversality.Sard.prodForm_null`, the step of the induction
that proves Sard's theorem in the rectangular case `n ≥ m` (`SardEuclidOn n m` implies
`SardEuclidOn (n+1) (m+1)`).

The statement says: for a `C^∞` map `γ : ℝ × ℝⁿ → ℝᵐ`, the critical *values* of the "product form"
map
`G : ℝ × ℝⁿ → ℝ × ℝᵐ`, `G (t, x) = (t, γ (t, x))`
have measure zero, assuming Sard for `C^∞` maps `ℝⁿ → ℝᵐ`.

The proof is the standard one.

* **The critical set.**  `fderiv ℝ G p = (fst : ℝ × ℝⁿ →L ℝ).prod (fderiv ℝ γ p)`, and the
  *pair* map `A.prod B` is surjective iff `B ∘ inr` is (`surjective_fst_prod_iff`); `B ∘ inr` is
  the derivative of the slice `x ↦ γ (p.1, x)`.  Hence
  `IsCriticalPoint G p ↔ IsCriticalPoint (fun x => γ (p.1, x)) p.2`
  (`isCriticalPoint_prodForm_iff`).
* **Measurability.**  The set of non-surjective continuous linear maps between
  finite-dimensional spaces is closed (`isOpen_setOf_surjective_clm`), hence (being `C^∞`)
  the critical set of `G` is closed; intersecting it with `closedBall 0 N` produces the compact
  pieces of a countable exhaustion of `Crit G`, whose images under the continuous `G` are compact
  and therefore measurable.
* **Fubini.**  Each slice `{y | (t, y) ∈ G '' (Crit G ∩ closedBall 0 N)}` is contained in the
  image `γ_t '' Crit γ_t` of the critical set of the slice map `γ_t = (x ↦ γ (t, x))`, which has
  measure zero by the induction hypothesis.  Tonelli (`measure_prod_null_of_ae_null`) then gives
  that each piece is null; a countable union of null sets is null.
-/

open scoped Topology MeasureTheory
open MeasureTheory Set Function

namespace Work.ThomBordism.Transversality.Sard

noncomputable section

/-- **Surjectivity of a continuous linear map is an open condition** (finite-dimensional case):
a surjective map has a continuous right inverse, and small perturbations of it stay surjective
because they stay invertible on the image of that right inverse. -/
theorem isOpen_setOf_surjective_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] :
    IsOpen {L : E →L[ℝ] F | Function.Surjective L} := by
  rw [isOpen_iff_mem_nhds]
  intro L hL
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective L.toLinearMap
    (LinearMap.range_eq_top.mpr hL)
  let R : F →L[ℝ] E := LinearMap.toContinuousLinearMap g
  have hR : L.comp R = 1 := by
    ext v
    have h1 := LinearMap.congr_fun hg v
    simpa [R] using h1
  let Φ : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] F) :=
    LinearMap.mkContinuous
      { toFun := fun L' => L'.comp R
        map_add' := fun a b => by ext v; simp [ContinuousLinearMap.add_comp]
        map_smul' := fun c a => by ext v; simp }
      ‖R‖ (fun L' => by
        rw [mul_comm]
        exact ContinuousLinearMap.opNorm_comp_le L' R)
  have hopen : IsOpen (Φ ⁻¹' {x : F →L[ℝ] F | IsUnit x}) :=
    Units.isOpen.preimage Φ.continuous
  have hmem : L ∈ Φ ⁻¹' {x : F →L[ℝ] F | IsUnit x} := by
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [show Φ L = L.comp R from rfl, hR]
    exact isUnit_one
  filter_upwards [hopen.mem_nhds hmem] with L' hL'
  intro y
  obtain ⟨u, hu⟩ := hL'
  have h2 : (↑u : F →L[ℝ] F) = L'.comp R := hu.trans (show Φ L' = L'.comp R from rfl)
  have key : (L'.comp R) ((↑(u⁻¹) : F →L[ℝ] F) y) = y := by
    rw [← h2, ← mul_apply_eq_comp, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    rfl
  exact ⟨R ((↑(u⁻¹) : F →L[ℝ] F) y), key⟩

/-- `(fst : ℝ × E →L ℝ).prod B` is surjective iff `B ∘ inr` is: the first component of the
pair map is independent of `B`, so surjectivity of the pair is exactly the surjectivity of `B`
along the kernel `{0} × E` of `fst`. -/
theorem surjective_fst_prod_iff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : (ℝ × E) →L[ℝ] F) :
    Function.Surjective ((ContinuousLinearMap.fst ℝ ℝ E).prod B) ↔
      Function.Surjective (B.comp (ContinuousLinearMap.inr ℝ ℝ E)) := by
  constructor
  · intro h y
    obtain ⟨z, hz⟩ := h (0, y)
    rw [ContinuousLinearMap.prod_apply] at hz
    have hz1 : z.1 = 0 := (Prod.mk.injEq _ _ _ _).mp hz |>.1
    have hz2 : B z = y := (Prod.mk.injEq _ _ _ _).mp hz |>.2
    refine ⟨z.2, ?_⟩
    rw [ContinuousLinearMap.comp_apply]
    have hzEq : z = (0, z.2) := by ext <;> simp [hz1]
    change B (0, z.2) = y
    rw [← hzEq]
    exact hz2
  · intro h b
    obtain ⟨v, hv⟩ := h (b.2 - B (b.1, 0))
    rw [ContinuousLinearMap.comp_apply] at hv
    have hv' : B (0, v) = b.2 - B (b.1, 0) := by
      change B ((ContinuousLinearMap.inr ℝ ℝ E) v) = _ at hv
      exact hv
    refine ⟨(b.1, v), ?_⟩
    rw [ContinuousLinearMap.prod_apply]
    refine Prod.ext rfl ?_
    show B (b.1, v) = b.2
    have hsplit : (b.1, v) = (b.1, 0) + (0, v) := by ext <;> simp
    rw [hsplit, map_add, hv']
    abel

/-- The derivative of the product-form map `p ↦ (p.1, γ p)` is the pair of the derivative of the
first projection and the derivative of `γ`. -/
theorem fderiv_prodForm {n m : ℕ}
    {γ : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hγ : Work.ThomBordism.Transversality.CInf γ) (p : ℝ × EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, γ p)) p
      = (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n))).prod (fderiv ℝ γ p) := by
  have hne : Work.ThomBordism.Transversality.smoothHeight ≠ 0 := by
    simp [Work.ThomBordism.Transversality.smoothHeight]
  have h2 : HasFDerivAt γ (fderiv ℝ γ p) p := ((hγ.differentiable hne) p).hasFDerivAt
  exact (hasFDerivAt_fst.prodMk h2).fderiv

/-- The derivative of the slice `x ↦ γ (p.1, x)` is the derivative of `γ` at `p` composed with
the inclusion `x ↦ (0, x)` of the second factor. -/
theorem fderiv_prodForm_snd {n m : ℕ}
    {γ : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hγ : Work.ThomBordism.Transversality.CInf γ) (p : ℝ × EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => γ (p.1, x)) p.2
      = (fderiv ℝ γ p).comp (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin n))) := by
  have hne : Work.ThomBordism.Transversality.smoothHeight ≠ 0 := by
    simp [Work.ThomBordism.Transversality.smoothHeight]
  have h2 : HasFDerivAt γ (fderiv ℝ γ p) p := ((hγ.differentiable hne) p).hasFDerivAt
  exact (h2.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)).fderiv

/-- **The critical points of the product form are the critical points of the slices**: `p` is a
critical point of `G : (t, x) ↦ (t, γ (t, x))` iff `x` is a critical point of the slice
`x ↦ γ (p.1, x)`. -/
theorem isCriticalPoint_prodForm_iff {n m : ℕ}
    {γ : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hγ : Work.ThomBordism.Transversality.CInf γ) (p : ℝ × EuclideanSpace ℝ (Fin n)) :
    Work.ThomBordism.Transversality.IsCriticalPoint
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, γ p)) p ↔
      Work.ThomBordism.Transversality.IsCriticalPoint
        (fun x : EuclideanSpace ℝ (Fin n) => γ (p.1, x)) p.2 := by
  rw [Work.ThomBordism.Transversality.IsCriticalPoint,
    Work.ThomBordism.Transversality.IsCriticalPoint]
  rw [fderiv_prodForm hγ p, surjective_fst_prod_iff, fderiv_prodForm_snd hγ p]

/-- **The Fubini step of rectangular Sard.**  If Sard's theorem holds for `C^∞` maps
`ℝⁿ → ℝᵐ` (`hIH`), then the critical values of the product-form map
`p ↦ (p.1, γ p) : ℝ × ℝⁿ → ℝ × ℝᵐ` have measure zero (for the product Lebesgue measure). -/
theorem prodForm_null {n m : ℕ}
    (hIH : Work.ThomBordism.Transversality.SardEuclidOn n m)
    {γ : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hγ : Work.ThomBordism.Transversality.CInf γ) :
    MeasureTheory.volume ((fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, γ p)) ''
      {p | Work.ThomBordism.Transversality.IsCriticalPoint
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, γ p)) p}) = 0 := by
  set G : ℝ × EuclideanSpace ℝ (Fin n) → ℝ × EuclideanSpace ℝ (Fin m) :=
    (fun p => (p.1, γ p)) with hGdef
  have hne : Work.ThomBordism.Transversality.smoothHeight ≠ 0 := by
    simp [Work.ThomBordism.Transversality.smoothHeight]
  have hGcd : ContDiff ℝ Work.ThomBordism.Transversality.smoothHeight G := by
    rw [hGdef]; exact contDiff_fst.prodMk hγ
  have hGcont : Continuous G := hGcd.continuous
  -- The critical set of `G` is closed (non-surjectivity of the derivative is a closed condition).
  have hcritclosed : IsClosed {p : ℝ × EuclideanSpace ℝ (Fin n) |
      Work.ThomBordism.Transversality.IsCriticalPoint G p} := by
    have hopen : IsOpen {p : ℝ × EuclideanSpace ℝ (Fin n) |
        Function.Surjective (fderiv ℝ G p)} :=
      isOpen_setOf_surjective_clm.preimage (hGcd.continuous_fderiv hne)
    simpa only [Work.ThomBordism.Transversality.IsCriticalPoint, Set.compl_ofPred]
      using hopen.isClosed_compl
  -- Every slice of each compact piece is contained in the critical image of the slice map.
  have hslice : ∀ (N : ℕ) (t : ℝ), volume (Prod.mk t ⁻¹'
      (G '' ({p | Work.ThomBordism.Transversality.IsCriticalPoint G p} ∩
        Metric.closedBall 0 (N:ℝ)))) = 0 := by
    intro N t
    refine measure_mono_null ?_ (by
      simpa using hIH (fun x : EuclideanSpace ℝ (Fin n) => γ (t, x)) univ isOpen_univ
        ((hγ.comp (contDiff_const.prodMk contDiff_id)).contDiffOn))
    intro y hy
    rw [Set.mem_preimage, Set.mem_image] at hy
    obtain ⟨p, hp, hpG⟩ := hy
    rw [Set.mem_inter_iff] at hp
    obtain ⟨hpcrit, -⟩ := hp
    rw [Set.mem_image]
    have hp1 : p.1 = t := by
      have hh := congrArg Prod.fst hpG
      simpa [hGdef] using hh
    have hpy : γ (t, p.2) = y := by
      have hh := congrArg Prod.snd hpG
      simp [hGdef] at hh
      change γ (p.1, p.2) = y at hh
      rw [hp1] at hh
      exact hh
    refine ⟨p.2, ?_, hpy⟩
    have := (isCriticalPoint_prodForm_iff hγ p).mp hpcrit
    rwa [hp1] at this
  -- Each compact piece is measurable with null slices, hence null by Tonelli.
  have hpiece : ∀ N : ℕ, volume (G '' ({p | Work.ThomBordism.Transversality.IsCriticalPoint G p}
      ∩ Metric.closedBall 0 (N:ℝ))) = 0 := by
    intro N
    have hcomp : IsCompact (G '' ({p | Work.ThomBordism.Transversality.IsCriticalPoint G p}
        ∩ Metric.closedBall 0 (N:ℝ))) :=
      IsCompact.of_isClosed_subset
        (isCompact_closedBall (0 : ℝ × EuclideanSpace ℝ (Fin n)) (N:ℝ))
        (hcritclosed.inter Metric.isClosed_closedBall) Set.inter_subset_right |>.image hGcont
    exact MeasureTheory.Measure.measure_prod_null_of_ae_null hcomp.isClosed.measurableSet
      (Filter.Eventually.of_forall fun t => hslice N t)
  -- The critical image is the countable union of the pieces.
  have hS : G '' {p | Work.ThomBordism.Transversality.IsCriticalPoint G p}
      = ⋃ N : ℕ, G '' ({p | Work.ThomBordism.Transversality.IsCriticalPoint G p}
          ∩ Metric.closedBall 0 (N:ℝ)) := by
    rw [← Set.image_iUnion]
    congr 1
    rw [← Set.inter_iUnion, Metric.iUnion_closedBall_nat, Set.inter_univ]
  rw [hS]
  exact measure_iUnion_null hpiece

end

end Work.ThomBordism.Transversality.Sard
