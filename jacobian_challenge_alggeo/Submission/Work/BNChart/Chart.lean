/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area BNChart (Submission/Work/NOTES_LEAD_jacobian_closure.md §2.B2)

# Area BNChart, B2 — the chart data: a basis of `L(W₀)`, the affine open `U`, its sections

This file fixes the *data* of the Brill–Noether chart of a concrete curve `C : Curve K`:

* `canonBasis C h : Basis (Fin ((genus C - 1) + 1)) K (C.L (canonical C))` — a `K`-basis of
  the Riemann–Roch space of a canonical divisor `W₀ = canonical C`, indexed by the successor
  shape `(genus C - 1) + 1` so that it can be used with `rochDataPos C h` without casts;
* `chartU C` — an affine open of `C` avoiding the support of `W₀` (and containing the generic
  point); it is the affine chart `Sym^g(U)` of the Brill–Noether construction;
* `chartSection C h j` — the section of the structure sheaf of `C` over `chartU C` representing
  `canonBasis C h j` (possible because `U` avoids `supp W₀`, where the basis elements are
  regular); these are the sections `s_j` of the Brill–Noether determinant;
* `basis_bc` — the `F`-basis of `L (pullK C (rochW C))` obtained from `canonBasis C h` by base
  change of the field (`L_divMap`, `linearIndependent_fieldMap`).

The mathematical content is in the two bridge lemmas that connect the *sections* `s_j` on `C`
with the *functions* `canonBasis C h j` on the base-changed curve: evaluation of a section at
an `F`-point of `C` agrees with evaluation of the base-changed function at the associated place
of `C_F` (`evalSection_eq_evalAt`), and it depends only on the underlying point of the
`F`-point (`evalSection_congr`).  Those two live one per file in this directory.
-/
import Submission.Work.BNChart.Basic
import Submission.Work.SymQuot.SymGeomInst
import Submission.Work.SymQuot.SymProps
import Submission.Work.SpecLin.Chart.RegularOpensMap
import Submission.Work.CurveBasics.Curve.BCSquare.L_divMap
import Submission.Work.CurveBasics.Curve.BCSquare.linearIndependent_fieldMap
import Submission.Work.CurveBasics.Curve.BCSquare.fieldMapTensor
import Submission.Work.CurveBasics.Curve.BCSquare.fieldMap_injective
import Submission.Work.CurveBasics.Curve.BCSquare.tensorLift_injective
import Submission.Work.CurveBasics.SeparatingElement.linearIndependent_pow_of_isDomain_tensor
import Submission.Work.CurveBasics.BaseChange.exists_affine_nbhd
import Submission.Work.CurveBasics.Linear.finiteDimensional_L
import Submission.Work.Charts.ChartCg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
open scoped Work.GCBasics

namespace Work.BNChart

open Work.CurveBasics Work.GCBasics Work.Charts

noncomputable section

variable {K : Type u} [Field K]

/-! ### The index type of the chart -/

/-- The index type of the Brill–Noether chart: the successor shape `(genus C - 1) + 1`, which
is definitionally the genus of `rochDataPos C h` (and hence of every `Fin`-indexed object built
from it), and is `genus C` whenever `genus C ≠ 0`. -/
abbrev chartIdx (C : Curve K) : Type := Fin ((RiemannRoch.Curve.genus C - 1) + 1)

/-- The cardinality of `chartIdx C` is `(genus C - 1) + 1`. -/
theorem card_chartIdx (C : Curve K) : Fintype.card (chartIdx C) = (RiemannRoch.Curve.genus C - 1) + 1 :=
  Fintype.card_fin _

open scoped TensorProduct in
/-- **The image of a linearly independent family of functions under the base-change map is
linearly independent**, with the index type allowed to live in a universe smaller than the
field.  This is `Curve.BCSquare.linearIndependent_fieldMap` with the universe restriction
removed, so that it applies to `Fin n`-indexed families over a field `K : Type u`. -/
theorem linearIndependent_fieldMap' {k : Type u} [Field k] {F : Type u} [Field F]
    [Algebra k F] {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') {ι : Type*}
    {v : ι → C.functionField} (hv : LinearIndependent k v) :
    LinearIndependent F (fun i => S.fieldMap.hom (v i)) := by
  classical
  have hw : LinearIndependent F (fun i => (1 : F) ⊗ₜ[k] v i) :=
    SeparatingElement.linearIndependent_tmul_one hv
  rw [linearIndependent_iff] at hw ⊢
  intro l hl
  have hl' : ∑ i ∈ l.support, l i • S.fieldMap.hom (v i) = 0 := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at hl
    exact hl
  apply hw l
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Curve.BCSquare.tensorLift_injective S ?_
  rw [map_zero, map_sum]
  rw [Finset.sum_congr rfl (fun i _ => ?_)]
  · exact hl'
  · rw [Curve.BCSquare.tensorLift_smul, Curve.BCSquare.tensorLift_one_tmul]

/-! ### A basis of `L (canonical C)` -/

/-- **A `K`-basis of the Riemann-Roch space of a canonical divisor.**

Since a canonical divisor `W₀` has `ℓ(W₀) = g` (`RiemannRoch.Curve.IsCanonical.l_eq`), the
space `C.L W₀` is finite dimensional of dimension `genus C`, hence — using
`(genus C - 1) + 1 = genus C` for `genus C ≠ 0` — has a basis indexed by `chartIdx C`. -/
noncomputable def canonBasis (C : Curve K) (h : RiemannRoch.Curve.genus C ≠ 0) :
    Module.Basis (chartIdx C) K (C.L (RiemannRoch.Curve.canonical C)) :=
  Module.finBasisOfFinrankEq K _
    (by
      haveI := Work.CurveBasics.Linear.finiteDimensional_L C (RiemannRoch.Curve.canonical C)
      have h1 : Module.finrank K (C.L (RiemannRoch.Curve.canonical C))
          = RiemannRoch.Curve.genus C :=
        (RiemannRoch.Curve.isCanonical_canonical C).l_eq
      rw [h1]
      have := Nat.pos_of_ne_zero h
      omega)

/-- The basis elements of `canonBasis` lie in `L (canonical C)`. -/
theorem canonBasis_mem (C : Curve K) (h : RiemannRoch.Curve.genus C ≠ 0) (j : chartIdx C) :
    ((canonBasis C h j : C.L (RiemannRoch.Curve.canonical C)) : C.functionField)
      ∈ C.L (RiemannRoch.Curve.canonical C) :=
  (canonBasis C h j).2

/-- The basis elements of `canonBasis` are nonzero rational functions. -/
theorem canonBasis_ne_zero (C : Curve K) (h : RiemannRoch.Curve.genus C ≠ 0) (j : chartIdx C) :
    ((canonBasis C h j : C.L (RiemannRoch.Curve.canonical C)) : C.functionField) ≠ 0 := by
  intro h0
  have := (canonBasis C h).linearIndependent
  exact (canonBasis C h).ne_zero j (Subtype.ext (by simpa using h0))

/-! ### The affine open `U` of the chart -/

/-- **The affine open of `C` supporting the chart**: an affine open neighbourhood of the generic
point avoiding the support of the canonical divisor `canonical C` (so that the basis elements of
`canonBasis C h` are regular on it, and so that `pullK C (rochW C)` vanishes at the places
above it). -/
noncomputable def chartU (C : Curve K) : C.left.Opens :=
  Classical.choose (Work.CurveBasics.BaseChange.exists_affine_nbhd_avoiding C
    (Finset.finite_toSet ((RiemannRoch.Curve.canonical C).support))
    (fun Q _ => SpecLin.Chart.genericPoint_ne_place_point C Q))

/-- The chart open is affine. -/
theorem isAffineOpen_chartU (C : Curve K) : IsAffineOpen (chartU C) :=
  (Classical.choose_spec (Work.CurveBasics.BaseChange.exists_affine_nbhd_avoiding C
    (Finset.finite_toSet ((RiemannRoch.Curve.canonical C).support))
    (fun Q _ => SpecLin.Chart.genericPoint_ne_place_point C Q))).1

/-- The generic point lies in the chart open. -/
theorem genericPoint_mem_chartU (C : Curve K) : genericPoint C.left ∈ chartU C :=
  (Classical.choose_spec (Work.CurveBasics.BaseChange.exists_affine_nbhd_avoiding C
    (Finset.finite_toSet ((RiemannRoch.Curve.canonical C).support))
    (fun Q _ => SpecLin.Chart.genericPoint_ne_place_point C Q))).2.1

instance (C : Curve K) : Nonempty (chartU C) := ⟨genericPoint C.left, genericPoint_mem_chartU C⟩

/-- A place whose point lies in the chart open is not in the support of the canonical divisor. -/
theorem notMem_support_chartU (C : Curve K) (Q : C.Place) (hQ : Q.point ∈ chartU C) :
    Q ∉ (RiemannRoch.Curve.canonical C).support :=
  (Classical.choose_spec (Work.CurveBasics.BaseChange.exists_affine_nbhd_avoiding C
    (Finset.finite_toSet ((RiemannRoch.Curve.canonical C).support))
    (fun Q _ => SpecLin.Chart.genericPoint_ne_place_point C Q))).2.2 Q hQ

/-- The canonical divisor vanishes at the places of the chart open. -/
theorem canonical_apply_eq_zero_of_mem_chartU (C : Curve K) (Q : C.Place)
    (hQ : Q.point ∈ chartU C) : (RiemannRoch.Curve.canonical C) Q = 0 :=
  Finsupp.notMem_support_iff.mp (notMem_support_chartU C Q hQ)

/-- Every basis element of `canonBasis` is regular on the chart open: it lies in `L(W₀)`, and
`W₀` vanishes on `U`. -/
theorem chartU_le_regularOpens (C : Curve K) (h : RiemannRoch.Curve.genus C ≠ 0)
    (j : chartIdx C) : chartU C ≤ SpecLin.Chart.regularOpens C
      ((canonBasis C h j : C.L (RiemannRoch.Curve.canonical C)) : C.functionField) := by
  intro z hz
  rw [SpecLin.Chart.mem_regularOpens]
  intro Q hQ
  have hmem := canonBasis_mem C h j
  rw [Curve.mem_L_iff] at hmem
  have hne := canonBasis_ne_zero C h j
  have heff : (C.div ((canonBasis C h j : C.L (RiemannRoch.Curve.canonical C)) : C.functionField)
      + RiemannRoch.Curve.canonical C).IsEffective := hmem.resolve_left hne
  have hQ' := heff Q
  simp only [Finsupp.add_apply, Curve.div_apply] at hQ'
  have h0 : (RiemannRoch.Curve.canonical C) Q = 0 :=
    canonical_apply_eq_zero_of_mem_chartU C Q (hQ ▸ hz)
  rw [h0, add_zero] at hQ'
  exact hQ'

/-! ### The sections `s_j` of the chart -/

/-- **The sections of the Brill–Noether determinant**: the restriction to `chartU C` of the
section of the structure sheaf representing `canonBasis C h j`. -/
noncomputable def chartSection (C : Curve K) (h : RiemannRoch.Curve.genus C ≠ 0)
    (j : chartIdx C) : Γ(C.left, chartU C) :=
  (C.left.presheaf.map (homOfLE (chartU_le_regularOpens C h j)).op)
    (SpecLin.Chart.regularOpensSection C
      ((canonBasis C h j : C.L (RiemannRoch.Curve.canonical C)) : C.functionField))

/-- The section `chartSection C h j` represents the rational function `canonBasis C h j`. -/
theorem germToFunctionField_chartSection (C : Curve K) (h : RiemannRoch.Curve.genus C ≠ 0)
    (j : chartIdx C) :
    (C.germToFunctionField (chartU C)).hom (chartSection C h j)
      = ((canonBasis C h j : C.L (RiemannRoch.Curve.canonical C)) : C.functionField) := by
  haveI : Nonempty (SpecLin.Chart.regularOpens C
      ((canonBasis C h j : C.L (RiemannRoch.Curve.canonical C)) : C.functionField)) :=
    SpecLin.Chart.nonempty_regularOpens C _
  haveI : Nonempty (chartU C) := ⟨genericPoint C.left, genericPoint_mem_chartU C⟩
  rw [chartSection, SpecLin.Chart.germToFunctionField_map_eq,
    SpecLin.Chart.germToFunctionField_regularOpensSection]

/-! ### The auxiliary place `Q` of the chart -/

/-- A curve has a place (a closed point): `C.left` is a Jacobson space and nonempty, so it has
a closed point. -/
theorem exists_place (C : Curve K) : Nonempty C.Place := by
  have hlc : IsLocallyClosed (Set.univ : Set C.left) :=
    ⟨Set.univ, Set.univ, isOpen_univ, isClosed_univ, by simp⟩
  obtain ⟨x, hx⟩ := nonempty_inter_closedPoints (X := C.left) (Z := Set.univ)
    Set.univ_nonempty hlc
  exact ⟨⟨x, mem_closedPoints_iff.mp hx.2⟩⟩

/-- A place of `C`, used as the auxiliary place `Q` of the Brill–Noether chart. -/
noncomputable def chartQ (C : Curve K) : C.Place := Classical.choice (exists_place C)

open scoped TensorProduct in
/-- The place `ptPlace x` lies over the underlying point of the `F`-point `x`: the projection of
a base-change square maps `ptToPoint x` to `x.left (closedPoint F)`. -/
theorem bcSquare_pi_ptToPoint (C : Curve K) {F : Type u} [Field F] [Algebra K F]
    (x : SpecLin.CurveFPt C F) :
    (Curve.bcSquare C F).π (SpecLin.ptToPoint x)
      = x.left (IsLocalRing.closedPoint F) := by
  rw [SpecLin.ptToPoint, ← SpecLin.ptLeft_fst (C := C) x]
  rfl

/-- **The pullback of the canonical divisor vanishes at the place of a point landing in the
chart open.**  The coefficient of `divMap (canonical C)` at a place `Q` is
`canonical C (under Q) * ramIdx Q` when the point below is closed, and `canonical C` vanishes
at every place whose point lies in `chartU C`. -/
theorem pullK_rochW_apply_ptPlace_eq_zero (C : Curve K) {F : Type u} [Field F] [Algebra K F]
    (x : SpecLin.CurveFPt C F) (hx : x.left (IsLocalRing.closedPoint F) ∈ chartU C) :
    pullK C (rochW C) (SpecLin.ptPlace x) = 0 := by
  rw [pullK_rochW_bcSquare C F, Curve.BCSquare.divMap_apply, Curve.BCSquare.divMapCoeff]
  by_cases h : IsClosed ({(Curve.bcSquare C F).π (SpecLin.ptPlace x).point} : Set C.left)
  · rw [dif_pos h]
    have hmem : ((Curve.bcSquare C F).under (SpecLin.ptPlace x) h).point ∈ chartU C := by
      show (Curve.bcSquare C F).π (SpecLin.ptPlace x).point ∈ chartU C
      show (Curve.bcSquare C F).π (SpecLin.ptToPoint x) ∈ chartU C
      rw [bcSquare_pi_ptToPoint C x]
      exact hx
    rw [canonical_apply_eq_zero_of_mem_chartU C _ hmem, zero_mul]
  · rw [dif_neg h]

/-- **A function of `L (canonical C)` is regular at the place of a point landing in the chart
open.**  After base change of the field, `fieldMap h` lies in
`L (divMap (canonical C)) = L (pullK C (rochW C))`, and the latter divisor vanishes at the place
of any point landing in `chartU C` (`pullK_rochW_apply_ptPlace_eq_zero`). -/
theorem ordAt_fieldMap_nonneg (C : Curve K) {F : Type u} [Field F] [Algebra K F]
    {h : C.functionField} (hh : h ∈ C.L (RiemannRoch.Curve.canonical C))
    (x : SpecLin.CurveFPt C F) (hx : x.left (IsLocalRing.closedPoint F) ∈ chartU C) :
    0 ≤ (C.baseChange F).ordAt ((Curve.bcSquare C F).fieldMap.hom h) (SpecLin.ptPlace x) := by
  rcases eq_or_ne h 0 with rfl | hne
  · rw [map_zero, Work.CurveBasics.Curve.ordAt, Scheme.ord_zero]
    simp
  · have hmem : (Curve.bcSquare C F).fieldMap.hom h ∈
        (C.baseChange F).L ((Curve.bcSquare C F).divMap (RiemannRoch.Curve.canonical C)) := by
      rw [Curve.BCSquare.L_divMap]
      exact Submodule.subset_span ⟨h, hh, rfl⟩
    rw [Curve.mem_L_iff] at hmem
    have hne' : (Curve.bcSquare C F).fieldMap.hom h ≠ 0 :=
      fun h0 => hne (Curve.BCSquare.fieldMap_injective (Curve.bcSquare C F) (by simpa using h0))
    have heff := hmem.resolve_left hne'
    have hQ := heff (SpecLin.ptPlace x)
    simp only [Finsupp.add_apply, Curve.div_apply] at hQ
    have h0 : (Curve.bcSquare C F).divMap (RiemannRoch.Curve.canonical C)
        (SpecLin.ptPlace x) = 0 := by
      rw [← pullK_rochW_bcSquare C F]
      exact pullK_rochW_apply_ptPlace_eq_zero C x hx
    rw [h0, add_zero] at hQ
    exact hQ

/-- **B2, the bridge between the sections `s_j` on `C` and the functions `fieldMap (h_j)` on
`C_F`** (the statement of `Work.BNChart.evalSection_eq_evalAt`, packaged as a `Prop` so that it
can be taken as a hypothesis by lemmas proved before it lands).

For an `F`-point `x` of `C`, an open `U` containing the underlying point of `x` on which the
rational functions `h j` are regular, and coefficients `c j`, the `F`-linear combination
`∑ j, c j • fieldMap (h j)` of base-changed rational functions has *positive order of vanishing*
at the place `ptPlace x` of `C_F` if and only if the corresponding `F`-linear combination of the
values of the sections representing `h j` on `U` is zero.  Both `0 < n` (so that `Fin n` is
nonempty) and the non-vanishing of the combination are needed: `ordAt 0 = 0`, so without
`f ≠ 0` the equivalence fails. -/
def EvalSectionBridge (C : Curve K) : Prop :=
  ∀ {F : Type u} [Field F] [Algebra K F] {n : ℕ} (_hn : 0 < n)
    (x : SpecLin.CurveFPt C F) (h : Fin n → C.functionField) (U : C.left.Opens)
    (hU : ∀ j, U ≤ SpecLin.Chart.regularOpens C (h j))
    (hxU : x.left (IsLocalRing.closedPoint F) ∈ U) (c : Fin n → F)
    (_hf : (∑ j, c j • (Curve.bcSquare C F).fieldMap.hom (h j)) ≠ 0)
    (_hreg : 0 ≤ (C.baseChange F).ordAt
      (∑ j, c j • (Curve.bcSquare C F).fieldMap.hom (h j)) (SpecLin.ptPlace x)),
    (∑ j, c j * Charts.evalSection x.left hxU
        ((C.left.presheaf.map (CategoryTheory.homOfLE (hU j)).op)
          (SpecLin.Chart.regularOpensSection C (h j)))) = 0 ↔
      0 < (C.baseChange F).ordAt
        (∑ j, c j • (Curve.bcSquare C F).fieldMap.hom (h j)) (SpecLin.ptPlace x)

/-! ### The base-changed basis of `L (pullK C (rochW C))` -/

/-- **B2: a basis of `L (pullK C (rochW C))`.**

Base change of the field is flat, so `L (divMap W₀) = span_F (fieldMap '' L W₀)`
(`Curve.BCSquare.L_divMap`), and the span of the image of a basis has the same dimension as
`L W₀` (`Curve.BCSquare.finrank_span_image_fieldMap`).  Hence
`L (pullK C (rochW C))` is `F`-finite of dimension `(genus C - 1) + 1` and carries a basis with
that index type. -/
noncomputable def basis_bc (C : Curve K) (h : RiemannRoch.Curve.genus C ≠ 0)
    (F : Type u) [Field F] [Algebra K F] :
    Module.Basis (chartIdx C) F ((C.baseChange F).L (pullK C (rochW C))) :=
  Module.finBasisOfFinrankEq F _
    (by
      haveI : Module.Finite F ((C.baseChange F).L (pullK C (rochW C))) :=
        Work.CurveBasics.Linear.finiteDimensional_L (C.baseChange F) _
      have h1 : Module.finrank F ((C.baseChange F).L (pullK C (rochW C)))
          = RiemannRoch.Curve.genus C := by
        rw [show Module.finrank F ((C.baseChange F).L (pullK C (rochW C)))
              = (C.baseChange F).l (pullK C (rochW C)) from rfl,
          pullK_rochW_bcSquare C F, Curve.BCSquare.l_divMap]
        exact (RiemannRoch.Curve.isCanonical_canonical C).l_eq
      rw [h1]
      have := Nat.pos_of_ne_zero h
      omega)

/-- **The image of `canonBasis` under the base-change map of function fields is linearly
independent.**  This is `Curve.BCSquare.linearIndependent_fieldMap`, with the index type
allowed to live in a *smaller* universe than the field (so that it applies to
`Fin ((genus C - 1) + 1)` for `K : Type u`). -/
theorem linearIndependent_fieldMap_canonBasis (C : Curve K) (h : RiemannRoch.Curve.genus C ≠ 0)
    (F : Type u) [Field F] [Algebra K F] :
    LinearIndependent F (fun j : chartIdx C => (Curve.bcSquare C F).fieldMap.hom
      ((canonBasis C h j : C.L (RiemannRoch.Curve.canonical C)) : C.functionField)) := by
  refine linearIndependent_fieldMap' (Curve.bcSquare C F) ?_
  have hLI : LinearIndependent K (fun j : chartIdx C =>
      ((canonBasis C h j : C.L (RiemannRoch.Curve.canonical C)) : C.functionField)) :=
    (canonBasis C h).linearIndependent.map'
      (Submodule.subtype (C.L (RiemannRoch.Curve.canonical C)))
      (Submodule.ker_subtype _)
  exact hLI

/-- Alias of `basis_bc` (the B2 deliverable is usually quoted under this name). -/
abbrev baseBasis (C : Curve K) (h : RiemannRoch.Curve.genus C ≠ 0)
    (F : Type u) [Field F] [Algebra K F] :
    Module.Basis (chartIdx C) F ((C.baseChange F).L (pullK C (rochW C))) :=
  basis_bc C h F

end

end Work.BNChart
