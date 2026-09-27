import Mathlib
import Submission.Work.Whitney.DoublePoint
import Submission.Work.Whitney.exists_bump_model_pair_smooth

/-!
# The signed determinant of a double point, computed in a *single* chart

`Work.Whitney.doubleDet f p q u v` reads the "two sheets" determinant of a candidate double point
through the charts `chartAt p` and `chartAt q`.  For the *sign bookkeeping* of the self-intersection
cancellation it is much more convenient to use **one** chart `c` for both points: this file
introduces

* `Work.Whitney.doubleDetC f c p q` — the determinant of
  `pairEquiv n ∘ ((D (f ∘ c.symm) (c p)) coprod (D (f ∘ c.symm) (c q)))`,

i.e. the signed determinant of the double point `(p, q)` *as seen in the chart `c`*.  When `c`
contains both `p` and `q`, this is the honest local intersection number of the two sheets; the
signs of two `doubleDetC`-values computed in the same chart are directly comparable, which is what
the Whitney cancellation needs.

The two signs are related to the "intrinsic" `doubleDet` by the determinants of the chart
transitions, which are positive for charts that are close to one another.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

/-- The signed determinant of a double point of a map `g : ℝⁿ → ℝ^{2n}` at the parameters `u, v`:
the determinant of the "two sheets" map `(x, y) ↦ Dg u x + Dg v y`, read through the block
identification `Work.Projection.pairEquiv n`. -/
noncomputable def doubleDetRep {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n)))
    (u v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  LinearMap.det (((Work.Projection.pairEquiv n).toLinearMap).comp
    (((fderiv ℝ g u).coprod (fderiv ℝ g v)).toLinearMap))

/-- **The signed determinant of a double point of `f : M → ℝ^{2n}`, computed in a single chart
`c`.** -/
noncomputable def doubleDetC {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (p q : M) : ℝ :=
  doubleDetRep (fun u => f (c.symm u)) (c p) (c q)

theorem doubleDetC_def {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (p q : M) :
    doubleDetC f c p q = doubleDetRep (fun u => f (c.symm u)) (c p) (c q) := rfl

/-- `doubleDet` is the single-chart version read through the two charts at the two points. -/
theorem doubleDet_eq_doubleDetRep {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (p q : M)
    (u v : EuclideanSpace ℝ (Fin n)) :
    doubleDet f p q u v =
      LinearMap.det (((Work.Projection.pairEquiv n).toLinearMap).comp
        (((fderiv ℝ (chartRepM f p) u).coprod
          (fderiv ℝ (chartRepM f q) v)).toLinearMap)) := rfl

/-- If the two points live in the same chart `c` and the chart representations coincide there, the
intrinsic `doubleDet` and the single-chart `doubleDetC` agree on the nose. -/
theorem doubleDetC_eq_doubleDetRep_comp {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (p q : M) :
    doubleDetC f c p q = doubleDetRep (f ∘ c.symm) (c p) (c q) := rfl

/-- `doubleDetC` is the same as `doubleDet` when the chart `c` is the chart at `p` **and** at `q`,
evaluated at the chart coordinates of the points themselves. -/
theorem doubleDetC_self {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (p q r : M) :
    doubleDetC f (chartAt (EuclideanSpace ℝ (Fin n)) r) p q
      = doubleDetRep (chartRepM f r) ((chartAt (EuclideanSpace ℝ (Fin n)) r) p)
          ((chartAt (EuclideanSpace ℝ (Fin n)) r) q) := rfl

/-- **A nonzero single-chart determinant is exactly transversality of the two sheets in that
chart.**  This is the single-chart companion of `Work.Whitney.doubleDet_ne_zero_iff`. -/
theorem doubleDetRep_ne_zero_iff {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n)))
    (u v : EuclideanSpace ℝ (Fin n)) :
    doubleDetRep g u v ≠ 0 ↔
      (fderiv ℝ g u).range ⊔ (fderiv ℝ g v).range = ⊤ := by
  rw [doubleDetRep]
  set Ap : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) := fderiv ℝ g u with hAp
  set Aq : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) := fderiv ℝ g v with hAq
  set L : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      EuclideanSpace ℝ (Fin (2 * n)) := Ap.coprod Aq with hL
  set Φ : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    ((Work.Projection.pairEquiv n).toLinearMap).comp L.toLinearMap with hΦ
  have hdetiff : (LinearMap.det Φ ≠ 0) ↔ Function.Injective ⇑Φ := by
    rw [ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]
  rw [hdetiff]
  have hinjiff : Function.Injective ⇑Φ ↔ Function.Injective ⇑(L.toLinearMap) := by
    constructor
    · intro h x y hxy
      apply h
      simp only [hΦ, LinearMap.comp_apply, hxy]
    · intro h x y hxy
      apply h
      have := congrArg (⇑((Work.Projection.pairEquiv n).symm)) hxy
      simpa only [hΦ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        using this
  have hLrange : L.toLinearMap.range = Ap.range ⊔ Aq.range := by
    rw [hL, ContinuousLinearMap.coe_coprod, LinearMap.range_coprod]
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * n))) := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
    omega
  have hiff : Function.Injective ⇑(L.toLinearMap) ↔ Ap.range ⊔ Aq.range = ⊤ := by
    rw [← hLrange, LinearMap.range_eq_top]
    exact LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
  rw [hinjiff, hiff, hAp, hAq]

end Work.Whitney
