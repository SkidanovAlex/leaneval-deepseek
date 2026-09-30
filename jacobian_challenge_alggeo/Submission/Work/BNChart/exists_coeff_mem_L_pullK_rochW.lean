import Mathlib
import Submission.Work.BNChart.Chart
import Submission.Work.CurveBasics.Curve.BCSquare.fieldMap_algebraMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.BNChart

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
open scoped Work.GCBasics

universe u

open Work.CurveBasics Work.GCBasics Work.Charts

noncomputable section

theorem exists_coeff_mem_L_pullK_rochW {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (h : Work.RiemannRoch.Curve.genus C ≠ 0) {F : Type u} [Field F] [Algebra K F]
    {f : (C.baseChange F).functionField}
    (hf : f ∈ (C.baseChange F).L (Work.Charts.pullK C (Work.BNChart.rochW C))) :
    ∃ c : Work.BNChart.chartIdx C → F,
      f = ∑ j, c j • (Work.CurveBasics.Curve.bcSquare C F).fieldMap.hom
        ↑((Work.BNChart.canonBasis C h) j) := by
  classical
  let S := Curve.bcSquare C F
  let D := RiemannRoch.Curve.canonical C
  let vloc : chartIdx C → C.functionField := fun j => ↑(canonBasis C h j)
  let v : chartIdx C → (C.baseChange F).functionField := fun j => S.fieldMap.hom (vloc j)
  have hsmul : ∀ (a : K) (x : C.functionField),
      S.fieldMap.hom (a • x) = (algebraMap K F a) • S.fieldMap.hom x := by
    intro a x
    rw [Algebra.smul_def, map_mul, Curve.BCSquare.fieldMap_algebraMap, Algebra.smul_def]
  let φ : C.functionField →ₛₗ[algebraMap K F] (C.baseChange F).functionField :=
    { toFun := S.fieldMap.hom
      map_add' := fun x y => map_add S.fieldMap.hom x y
      map_smul' := hsmul }
  have hvspan : Submodule.span K (Set.range vloc) = C.L D :=
    (Submodule.span_range_subtype_eq_top_iff (C.L D) (fun j => (canonBasis C h j).2)).mp
      (canonBasis C h).span_eq
  have himg : φ '' Set.range vloc = Set.range v := by
    ext y
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨vloc i, ⟨i, rfl⟩, rfl⟩
  have hspan : Submodule.span F (S.fieldMap.hom '' ↑(C.L D)) ≤
      Submodule.span F (Set.range v) := by
    rw [Submodule.span_le]
    rintro y ⟨g, hg, rfl⟩
    have hg' : g ∈ Submodule.span K (Set.range vloc) := hvspan ▸ hg
    have h1 := (Submodule.image_span_subset_span φ (Set.range vloc)) ⟨g, hg', rfl⟩
    rw [himg] at h1
    exact h1
  have hf' : f ∈ Submodule.span F (S.fieldMap.hom '' ↑(C.L D)) := by
    have h1 : f ∈ (C.baseChange F).L (S.divMap D) := by
      rw [← pullK_rochW_bcSquare C F]
      exact hf
    rwa [Curve.BCSquare.L_divMap S D] at h1
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp (hspan hf')
  exact ⟨c, hc.symm⟩

end

end Work.BNChart
