import Mathlib
import Submission.Work.BNChart.Chart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.BNChart

open Work.CurveBasics Work.GCBasics Work.Charts
open scoped Classical

universe u

variable {K : Type u} [Field K]

/-- **Expansion of an element of the Riemann–Roch space in the functions `fieldMap (canonBasis)`.**

Every element `f` of `L (pullK C (rochW C))` is an `F`-linear combination of the base-changed
canonical basis functions `fieldMap (canonBasis C h j)`.  This is the companion of
`Work.BNChart.linearIndependent_fieldMap_canonBasis` (which gives linear independence of that
family): `pullK C (rochW C) = (bcSquare C F).divMap (canonical C)`
(`Work.BNChart.pullK_rochW_bcSquare`), so flat base change for `H⁰`
(`Work.CurveBasics.Curve.BCSquare.L_divMap`) identifies `L (pullK C (rochW C))` with the `F`-span
of `fieldMap '' L (canonical C)`, and an element `g` of `L (canonical C)` is a `K`-combination of
the `canonBasis C h j` (`Module.Basis.sum_repr`), which `fieldMap` — a `K`-algebra homomorphism
for the pullback structure, `Curve.BCSquare.fieldMap_algebraMap` — turns into an `F`-combination
of the `fieldMap (canonBasis C h j)`. -/
private theorem coeff_expansion_helper {C : Curve K} (h : RiemannRoch.Curve.genus C ≠ 0)
    {F : Type u} [Field F] [Algebra K F] {f : (C.baseChange F).functionField}
    (hf : f ∈ (C.baseChange F).L (pullK C (rochW C))) :
    ∃ c : chartIdx C → F, f = ∑ j, c j • (Curve.bcSquare C F).fieldMap.hom
        ↑((canonBasis C h) j) := by
  let v : chartIdx C → (C.baseChange F).functionField := fun j =>
    (Curve.bcSquare C F).fieldMap.hom ↑((canonBasis C h) j)
  -- a single element of `L (canonical C)` expands in the `fieldMap (canonBasis C h j)`
  have hv : ∀ g : ↥(C.L (RiemannRoch.Curve.canonical C)),
      (Curve.bcSquare C F).fieldMap.hom (g : C.functionField) = ∑ j,
        (algebraMap K F (((canonBasis C h).repr g) j)) • v j := by
    intro g
    have hrep : (∑ j, ((canonBasis C h).repr g) j • (canonBasis C h) j :
        ↥(C.L (RiemannRoch.Curve.canonical C))) = g :=
      (canonBasis C h).sum_repr g
    conv_lhs => rw [← hrep]
    rw [Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Submodule.coe_smul, Algebra.smul_def, map_mul,
      Curve.BCSquare.fieldMap_algebraMap, Algebra.smul_def]
  -- flat base change identifies `L (pullK C (rochW C))` with the span of the base-changed
  -- canonical space
  rw [pullK_rochW_bcSquare C F] at hf
  rw [Curve.BCSquare.L_divMap (Curve.bcSquare C F) (RiemannRoch.Curve.canonical C)] at hf
  have key : ∀ x : (C.baseChange F).functionField,
      x ∈ Submodule.span F ((Curve.bcSquare C F).fieldMap.hom ''
        ↑(C.L (RiemannRoch.Curve.canonical C))) → ∃ c : chartIdx C → F,
          x = ∑ j, c j • v j := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨g, hg, rfl⟩ := hy
        exact ⟨_, hv ⟨g, hg⟩⟩
    | zero => exact ⟨0, by simp⟩
    | add u w _ _ ihu ihw =>
        obtain ⟨c, rfl⟩ := ihu
        obtain ⟨c', rfl⟩ := ihw
        exact ⟨c + c', by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
    | smul a u _ ihu =>
        obtain ⟨c, rfl⟩ := ihu
        exact ⟨a • c, by simp only [Pi.smul_apply, smul_assoc, Finset.smul_sum]⟩
  obtain ⟨c, hc⟩ := key f hf
  exact ⟨c, hc⟩

/-- **The true direction of the Brill–Noether criterion.**

If the evaluation matrix `(s_j(x_m))` (with `s_j = chartSection C h j` the sections of the
canonical divisor on the chart open `chartU C`, and `x_m` points of `C_F` landing in it) is
invertible, then the degree-`g` divisor `D = ∑ m, ptDiv (x m)` is non-special.

No distinctness of the points `x m` is needed.  Indeed if `0 ≠ f ∈ L (pullK C (rochW C) - D)`,
write `f = ∑ j, c j • fieldMap (h_j)` with `h_j = canonBasis C h j`; by
`Work.BNChart.linearIndependent_fieldMap_canonBasis` a nonzero `f` has a nonzero coefficient
vector `c`.  At every `m`, `ord_{ptPlace (x m)} f ≥ D (ptPlace (x m)) ≥ 1`, so the bridge
`Work.BNChart.EvalSectionBridge C` gives `∑ j, c j * s_j(x m) = 0`; this for all `m` means the
invertible matrix `(s_j(x m))` kills the nonzero vector `c`, a contradiction.

Route: `Work.Charts.iOf_eq_zero_iff_no_vanishing` (`iOf = 0` if and only if every nonzero element
of `L (pullK C (rochW C))` vanishes to order strictly less than `D` at some place of the support
of `D`; its `hdisj` hypothesis is `Work.BNChart.pullK_rochW_apply_ptPlace_eq_zero`),
`Work.BNChart.ordAt_fieldMap_nonneg`, `Curve.BCSquare.L_divMap` (to expand `f` in the
`fieldMap (h_j)`) and the linear algebra fact that an invertible square matrix has zero kernel. -/
theorem iOf_eq_zero_of_det_ne_zero_point {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (h : RiemannRoch.Curve.genus C ≠ 0) {F : Type u} [Field F] [Algebra K F]
    (hbridge : Work.BNChart.EvalSectionBridge C)
    (x : Fin ((RiemannRoch.Curve.genus C - 1) + 1) → Work.SpecLin.CurveFPt C F)
    (hxU : ∀ m, (x m).left (IsLocalRing.closedPoint F) ∈ Work.BNChart.chartU C)
    (hdet : (Matrix.det (Matrix.of (fun j m => Work.Charts.evalSection (x m).left (hxU m)
      (Work.BNChart.chartSection C h j)))) ≠ 0) :
    Work.Charts.iOf C (Work.BNChart.rochW C) (∑ m, Work.SpecLin.ptDiv (x m)) = 0 := by
  classical
  set D : Dv C F := ∑ m, SpecLin.ptDiv (x m) with hDdef
  -- The divisor `D` is effective.
  have hD : D.IsEffective := by
    intro Q
    rw [hDdef, Finsupp.finsetSum_apply]
    exact Finset.sum_nonneg (fun m _ => SpecLin.ptDiv_isEffective (x m) Q)
  -- `D` has multiplicity at least one at each place `ptPlace (x m)`.
  have hDle : ∀ m : Fin ((RiemannRoch.Curve.genus C - 1) + 1),
      1 ≤ D (SpecLin.ptPlace (x m)) := by
    intro m
    rw [hDdef, Finsupp.finsetSum_apply]
    have h1 : SpecLin.ptDiv (x m) (SpecLin.ptPlace (x m)) = 1 := by
      rw [SpecLin.ptDiv_apply]
      simp
    have h2 := Finset.single_le_sum (f := fun m' => SpecLin.ptDiv (x m')
        (SpecLin.ptPlace (x m)))
      (fun m' _ => SpecLin.ptDiv_isEffective (x m') _) (Finset.mem_univ m)
    rw [h1] at h2
    simpa using h2
  -- Reduce `iOf = 0` to the vanishing of `L (pullK C (rochW C) - D)`.
  rw [Charts.iOf, GCBasics.ell]
  haveI : FiniteDimensional F ↥((C.baseChange F).L (pullK C (rochW C) - D)) :=
    Work.CurveBasics.Linear.finiteDimensional_L (C.baseChange F) _
  rw [finrank_zero_iff_forall_zero]
  intro f0
  refine Subtype.ext ?_
  simp only [Submodule.coe_zero]
  by_contra hfne
  -- `f ∈ L (pullK C (rochW C))`, so expand it in the functions `fieldMap (canonBasis C h)`.
  have hfL : (f0 : (C.baseChange F).functionField) ∈
      (C.baseChange F).L (pullK C (rochW C)) := by
    refine Curve.L_mono (C.baseChange F) ?_ f0.2
    rw [Curve.Div.le_iff]
    intro Q
    have h := hD Q
    simp only [Finsupp.sub_apply]
    linarith
  obtain ⟨c, hc⟩ := coeff_expansion_helper (C := C) (F := F) h hfL
  have hcne : c ≠ 0 := by
    intro hc0
    exact hfne (by rw [hc, hc0]; simp)
  -- The bridge gives the matrix equation `∑ j, c j * s_j (x m) = 0` for every `m`.
  have hmat : ∀ m : Fin ((RiemannRoch.Curve.genus C - 1) + 1),
      ∑ j, c j * Charts.evalSection (x m).left (hxU m) (chartSection C h j) = 0 := by
    intro m
    -- `ord` of `f` at `ptPlace (x m)` is at least `D (ptPlace (x m)) ≥ 1`
    have hord : (1 : ℤ) ≤ (C.baseChange F).ordAt (f0 : (C.baseChange F).functionField)
        (SpecLin.ptPlace (x m)) := by
      have heff : ((C.baseChange F).div (f0 : (C.baseChange F).functionField)
          + (pullK C (rochW C) - D)).IsEffective :=
        (Curve.mem_L_iff (C.baseChange F)).mp f0.2 |>.resolve_left hfne
      have h1 := (Curve.isEffective_div_add_iff (C.baseChange F)).mp heff
        (SpecLin.ptPlace (x m))
      simp only [Finsupp.sub_apply] at h1
      rw [pullK_rochW_apply_ptPlace_eq_zero C (x m) (hxU m)] at h1
      have h2 : D (SpecLin.ptPlace (x m)) ≤
          (C.baseChange F).ordAt (f0 : (C.baseChange F).functionField)
            (SpecLin.ptPlace (x m)) := by
        simpa only [zero_sub, neg_neg, Curve.ordAt] using h1
      have h3 := hDle m
      linarith
    have hfne' : (∑ j, c j • (Curve.bcSquare C F).fieldMap.hom
        ↑((canonBasis C h) j)) ≠ 0 := by
      rw [← hc]
      exact hfne
    have hreg : 0 ≤ (C.baseChange F).ordAt
        (∑ j, c j • (Curve.bcSquare C F).fieldMap.hom ↑((canonBasis C h) j))
        (SpecLin.ptPlace (x m)) := by
      rw [← hc]
      linarith
    have hb := hbridge (F := F) (n := (RiemannRoch.Curve.genus C - 1) + 1) (by omega)
      (x m) (fun j => ((canonBasis C h) j : C.functionField)) (chartU C)
      (fun j => chartU_le_regularOpens C h j) (hxU m) c hfne' hreg
    have hpos : 0 < (C.baseChange F).ordAt
        (∑ j, c j • (Curve.bcSquare C F).fieldMap.hom ↑((canonBasis C h) j))
        (SpecLin.ptPlace (x m)) := by
      rw [← hc]
      linarith
    have hh := hb.mpr hpos
    simpa only [chartSection] using hh
  -- The invertible evaluation matrix kills the nonzero vector `c`.
  have hc0 : c = 0 := by
    have hmv : Matrix.mulVec (Matrix.of (fun j m => Charts.evalSection (x m).left (hxU m)
        (chartSection C h j))).transpose c = 0 := by
      funext m
      have hm := hmat m
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply]
      rw [Finset.sum_congr rfl (fun j _ => mul_comm
        ((fun j m => Charts.evalSection (x m).left (hxU m) (chartSection C h j)) j m)
        (c j))]
      exact hm
    have hinj := Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det (Matrix.of (fun j m => Charts.evalSection (x m).left
        (hxU m) (chartSection C h j))).transpose).mpr (by
        rw [Matrix.det_transpose]
        exact isUnit_iff_ne_zero.mpr hdet))
    exact hinj (by rw [hmv, Matrix.mulVec_zero])
  exact hcne hc0

end Work.BNChart
