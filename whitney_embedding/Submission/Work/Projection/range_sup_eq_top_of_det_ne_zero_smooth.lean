import Mathlib
import Submission.Work.Projection.TransverseDefs
import Submission.Work.Projection.range_sup_eq_top_of_det_ne_zero
import Submission.Work.Projection.fderiv_pairParam_smooth
import Submission.Work.Projection.fderiv_pairZ_smooth
import Submission.Work.Projection.range_sub_comp_eq_sup

set_option linter.style.haveILetI false

namespace Work.Projection

open scoped Manifold ContDiff
open Topology

/-- The range of a composite of continuous linear maps is the image of the range of the second
under the first: the continuous linear version of `LinearMap.range_comp`. -/
lemma clm_range_comp_smooth {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] (A : F →L[𝕜] G) (B : E →L[𝕜] F) :
    (A ∘L B).range = Submodule.map (A : F →ₗ[𝕜] G) B.range := by
  ext x
  rw [LinearMap.mem_range, Submodule.mem_map]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨B y, ⟨y, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, rfl⟩

/-- **Regularity of the pair parametrisation is exactly transversality of the corresponding double
point.**  Let `e : M → ℝ^{2n+1}` be smooth (with `M` carrying the *smooth* (`C^∞`) manifold
structure, i.e. the order `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`), let `x`, `y` be points of `M` lying in
the sources of the charts at `p` and `q`, and let `u = Work.Projection.pairDirPt e p q x y` be the
direction determined by the pair.  If the determinant of the derivative of the pair parametrisation
`Work.Projection.pairParam e p q` at the pair of chart coordinates is non-zero (i.e. the pair is not
a critical point), then the two tangent images of `g : z ↦ projVec u (e z)` at `x` and at `y` span
the whole target `ℝ^{2n}`.  The hypothesis `hz` says that the last coordinate of
`Work.Projection.pairZ e p q (chartAt p x, chartAt q y) = e y - e x` does not vanish, i.e. that
`(chartAt p x, chartAt q y)` lies in the domain `Work.Projection.pairDom e p q`.  This is identical
to `Work.Projection.range_sup_eq_top_of_det_ne_zero` in
`Submission.Work.Projection.range_sup_eq_top_of_det_ne_zero` except that the hypothesis is
smoothness rather than analyticity, so its proof can be transcribed with the `of_le` downgrading
removed (the imported `fderiv_pairParam_smooth` is the smooth-order transcription of the derivative
computation). -/
theorem range_sup_eq_top_of_det_ne_zero_smooth {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) e)
    (p q : M) (x y : M) (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).source)
    (hz : (pairZ e p q ((chartAt (EuclideanSpace ℝ (Fin n)) p) x,
        (chartAt (EuclideanSpace ℝ (Fin n)) q) y)) (Fin.last (2 * n)) ≠ 0)
    (hdet : (fderiv ℝ (pairParam e p q) ((chartAt (EuclideanSpace ℝ (Fin n)) p) x,
        (chartAt (EuclideanSpace ℝ (Fin n)) q) y)).det ≠ 0) :
    (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
        (fun z => projVec (pairDirPt e p q x y) (e z)) x).range ⊔
    (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
        (fun z => projVec (pairDirPt e p q x y) (e z)) y).range = ⊤ := by
  -- the smooth structure of the statement is exactly what the helpers need
  haveI : IsManifold (𝓡 n) 1 M := IsManifold.of_le (m := 1) (n := ∞) (by simp)
  have he' : ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ e := he
  have ha : (chartAt (EuclideanSpace ℝ (Fin n)) p) x ∈
      (chartAt (EuclideanSpace ℝ (Fin n)) p).target := (chartAt _ p).map_source hx
  have hb : (chartAt (EuclideanSpace ℝ (Fin n)) q) y ∈
      (chartAt (EuclideanSpace ℝ (Fin n)) q).target := (chartAt _ q).map_source hy
  -- the derivative of the pair parametrisation, and the direction determined by the pair
  have hfp := fderiv_pairParam_smooth e he p q ((chartAt (EuclideanSpace ℝ (Fin n)) p) x)
    ((chartAt (EuclideanSpace ℝ (Fin n)) q) y) ha hb hz
  set u := pairDirPt e p q x y with hu_def
  have hu : u = pairDir e p q ((chartAt (EuclideanSpace ℝ (Fin n)) p) x,
      (chartAt (EuclideanSpace ℝ (Fin n)) q) y) := rfl
  rw [← hu] at hfp
  set c := (pairZ e p q ((chartAt (EuclideanSpace ℝ (Fin n)) p) x,
      (chartAt (EuclideanSpace ℝ (Fin n)) q) y)) (Fin.last (2 * n)) with hc_def
  have hc : c ≠ 0 := hz
  -- non-vanishing of the determinant makes the derivative of the parametrisation bijective
  have hsurj_f : Function.Surjective (fderiv ℝ (pairParam e p q)
      ((chartAt (EuclideanSpace ℝ (Fin n)) p) x,
       (chartAt (EuclideanSpace ℝ (Fin n)) q) y)) := by
    have hker : ((fderiv ℝ (pairParam e p q) ((chartAt (EuclideanSpace ℝ (Fin n)) p) x,
        (chartAt (EuclideanSpace ℝ (Fin n)) q) y)) :
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ]
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))).ker = ⊥ := by
      by_contra h
      exact hdet ((LinearMap.det_eq_zero_iff_ker_ne_bot).mpr h)
    exact LinearMap.surjective_of_injective (LinearMap.ker_eq_bot.mp hker)
  rw [hfp] at hsurj_f
  set P : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    LinearMap.toContinuousLinearMap (pairEquiv n).toLinearMap with hP_def
  have hP_inj : Function.Injective P := by
    show Function.Injective (⇑(pairEquiv n)); exact (pairEquiv n).injective
  set Q : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      EuclideanSpace ℝ (Fin (2 * n)) :=
    projVec u ∘L fderiv ℝ (pairZ e p q) ((chartAt (EuclideanSpace ℝ (Fin n)) p) x,
      (chartAt (EuclideanSpace ℝ (Fin n)) q) y) with hQ_def
  have hR : Function.Surjective (c⁻¹ • Q) := by
    intro z
    obtain ⟨v, hv⟩ := hsurj_f (P z)
    exact ⟨v, hP_inj hv⟩
  have hQsurj : Function.Surjective Q := by
    intro w
    obtain ⟨v, hv⟩ := hR (c⁻¹ • w)
    refine ⟨v, ?_⟩
    have hv' : c⁻¹ • (Q v) = c⁻¹ • w := hv
    have := congrArg (fun t => c • t) hv'
    simpa [smul_smul, hc] using this
  have hQtop : Q.range = ⊤ := LinearMap.range_eq_top.mpr hQsurj
  -- the ranges of `projVec u ∘ d_e` at the two chart centres
  have hfZ := fderiv_pairZ_smooth e he p q ((chartAt (EuclideanSpace ℝ (Fin n)) p) x)
    ((chartAt (EuclideanSpace ℝ (Fin n)) q) y) ha hb
  set Dq := fderiv ℝ (chartRep e q) ((chartAt (EuclideanSpace ℝ (Fin n)) q) y) with hDq_def
  set Dp := fderiv ℝ (chartRep e p) ((chartAt (EuclideanSpace ℝ (Fin n)) p) x) with hDp_def
  have hQeq : Q = (projVec u ∘L Dq) ∘L
        ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) -
      (projVec u ∘L Dp) ∘L
        ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) := by
    rw [hQ_def, hfZ, ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.comp_assoc]
  have hQrange : Q.range = (projVec u ∘L Dq).range ⊔ (projVec u ∘L Dp).range := by
    rw [hQeq]
    exact range_sub_comp_eq_sup (projVec u ∘L Dq) (projVec u ∘L Dp)
  have hg : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ (fun z => projVec u (e z)) :=
    (projVec u).contMDiff.comp he'
  -- the same two ranges, expressed by the manifold derivatives of `z ↦ projVec u (e z)`
  have hrx : (mfderiv (𝓡 n) (𝓡 (2 * n)) (fun z => projVec u (e z)) x).range
      = (projVec u ∘L Dp).range := by
    let Mx : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
      mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) x
    have hMx : Mx.range = ⊤ := (mdifferentiable_chart (I := 𝓡 n) p).range_mfderiv_eq_top hx
    rw [mfderiv_chartAt_decomp (N := 2 * n) (fun z => projVec u (e z)) hg p x hx]
    have h1 : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
          projVec u (e ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y)))
          ((chartAt (EuclideanSpace ℝ (Fin n)) p) x)
        = (projVec u) ∘L fderiv ℝ (chartRep e p)
          ((chartAt (EuclideanSpace ℝ (Fin n)) p) x) := by
      have hcomp' : (fun y : EuclideanSpace ℝ (Fin n) =>
            projVec u (e ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y)))
          = ⇑(projVec u) ∘ chartRep e p := rfl
      rw [hcomp', fderiv_comp ((chartAt (EuclideanSpace ℝ (Fin n)) p) x)
        (projVec u).differentiableAt (differentiableAt_chartRep e he' p ha)]
      rw [ContinuousLinearMap.fderiv (projVec u)]
    rw [h1]
    change (((projVec u) ∘L fderiv ℝ (chartRep e p)
      ((chartAt (EuclideanSpace ℝ (Fin n)) p) x)) ∘L Mx).range
        = (projVec u ∘L Dp).range
    rw [clm_range_comp_smooth, hMx, Submodule.map_top, ← hDp_def]
  have hry : (mfderiv (𝓡 n) (𝓡 (2 * n)) (fun z => projVec u (e z)) y).range
      = (projVec u ∘L Dq).range := by
    let My : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
      mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) q) y
    have hMy : My.range = ⊤ := (mdifferentiable_chart (I := 𝓡 n) q).range_mfderiv_eq_top hy
    rw [mfderiv_chartAt_decomp (N := 2 * n) (fun z => projVec u (e z)) hg q y hy]
    have h1 : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) =>
          projVec u (e ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm z)))
          ((chartAt (EuclideanSpace ℝ (Fin n)) q) y)
        = (projVec u) ∘L fderiv ℝ (chartRep e q)
          ((chartAt (EuclideanSpace ℝ (Fin n)) q) y) := by
      have hcomp' : (fun z : EuclideanSpace ℝ (Fin n) =>
            projVec u (e ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm z)))
          = ⇑(projVec u) ∘ chartRep e q := rfl
      rw [hcomp', fderiv_comp ((chartAt (EuclideanSpace ℝ (Fin n)) q) y)
        (projVec u).differentiableAt (differentiableAt_chartRep e he' q hb)]
      rw [ContinuousLinearMap.fderiv (projVec u)]
    rw [h1]
    change (((projVec u) ∘L fderiv ℝ (chartRep e q)
      ((chartAt (EuclideanSpace ℝ (Fin n)) q) y)) ∘L My).range
        = (projVec u ∘L Dq).range
    rw [clm_range_comp_smooth, hMy, Submodule.map_top, ← hDq_def]
  have hmain : (projVec u ∘L Dp).range ⊔ (projVec u ∘L Dq).range = ⊤ := by
    rw [sup_comm, ← hQrange]
    exact hQtop
  rw [hrx, hry]
  exact hmain

end Work.Projection
