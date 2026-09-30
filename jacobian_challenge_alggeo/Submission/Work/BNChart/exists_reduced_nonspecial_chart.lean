import Mathlib
import Submission.Work.BNChart.Chart
import Submission.Work.BNChart.reduced_nonspecial_support
import Submission.Work.Charts.place_degree_eq_one_of_isAlgClosed
import Submission.Work.Charts.infinite_places_compl_finset
import Submission.Work.Charts.finite_places_notMem_of_ne_bot
import Submission.Work.SpecLin.Points.ptDiv_complete
import Submission.Work.SpecLin.Points.ptDiv_deg
import Submission.Work.CurveBasics.BCSquare

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

namespace Work.BNChart

open Work.CurveBasics Work.GCBasics Work.Charts

noncomputable section

variable {K : Type u} [Field K]

/-- **The version of `exists_reduced_nonspecial_chart` for an arbitrary algebraically closed
base-change field.**

Let `C` be a smooth proper geometrically irreducible curve over `K` of nonzero genus, and let
`F/K` be an algebraically closed field extension.  Since `F` is algebraically closed, every
place of `C_F` has degree one (`Work.Charts.place_degree_eq_one_of_isAlgClosed`), so the
hypothesis of `Work.BNChart.reduced_nonspecial_support` for the preimage `U_F` of the chart
open is satisfied: the degree-one places of `U_F` are infinite.  Running that lemma produces
an effective divisor `D` of degree `genus C`, supported in `U_F`, with `i D = 0`, all of whose
coefficients are `1` and all of whose places have degree one.  Its support therefore has
exactly `genus C = (genus C - 1) + 1` elements, so it can be enumerated by
`Fin ((genus C - 1) + 1)`.  By `Work.SpecLin.Points.ptDiv_complete` each of those degree-one
places is the point divisor of an `F`-point of `C`; this gives the required family `x`, which
is injective on places, lands in the chart open, and satisfies
`∑ m, ptDiv (x m) = D`, so that `iOf C (rochW C) (∑ m, ptDiv (x m)) = i (C.baseChange F) D = 0`
by `Work.BNChart.iOf_rochW_eq_i`. -/
theorem exists_reduced_nonspecial_chart_isAlgClosed {K : Type u} [Field K] {F : Type u}
    [Field F] [Algebra K F] [IsAlgClosed F] (C : Work.CurveBasics.Curve K)
    (h : RiemannRoch.Curve.genus C ≠ 0) :
    ∃ x : Fin ((RiemannRoch.Curve.genus C - 1) + 1) → Work.SpecLin.CurveFPt C F,
      Function.Injective (fun m => Work.SpecLin.ptPlace (x m)) ∧
      (∀ m, (x m).left (IsLocalRing.closedPoint F) ∈ Work.BNChart.chartU C) ∧
      Work.Charts.iOf C (Work.BNChart.rochW C) (∑ m, Work.SpecLin.ptDiv (x m)) = 0 := by
  classical
  -- The preimage `U_F` of the chart open in `C_F`.
  set UF : (C.baseChange F).left.Opens := (Curve.bcSquare C F).preimage (chartU C) with hUF
  -- `U_F` is nonempty (hence `≠ ⊥`), because `chartU C` is nonempty and `π` is surjective.
  have hne : UF ≠ ⊥ := by
    intro hbot
    haveI : Nonempty ((Curve.bcSquare C F).preimage (chartU C)) := inferInstance
    rw [hUF] at hbot
    have h2 : Nonempty (⊥ : (C.baseChange F).left.Opens) := hbot ▸ ‹Nonempty _›
    exact h2.elim (fun x => x.2)
  -- The degree-one places of `U_F` are infinite.
  have hinf : {P : (C.baseChange F).Place | P.degree = 1 ∧ P.point ∈ UF}.Infinite := by
    have hfinU : {P : (C.baseChange F).Place | P.point ∉ UF}.Finite :=
      Work.Charts.finite_places_notMem_of_ne_bot (C.baseChange F) UF hne
    have huniv : (Set.univ : Set (C.baseChange F).Place).Infinite := by
      simpa using Work.Charts.infinite_places_compl_finset (C.baseChange F) (∅ : Finset _)
    have hInfU : {P : (C.baseChange F).Place | P.point ∈ UF}.Infinite := by
      have hh := huniv.sdiff hfinU
      convert hh using 1
      ext P
      simp
    exact Set.Infinite.mono
      (fun P hP => ⟨Work.Charts.place_degree_eq_one_of_isAlgClosed (C.baseChange F) P, hP⟩)
      hInfU
  -- The reduced non-special divisor `D`.
  obtain ⟨D, _hDeff, hDdeg, hDi, hDred⟩ :=
    reduced_nonspecial_support (C.baseChange F) UF hinf
  have hDred_deg : ∀ P, D P ≠ 0 → P.degree = 1 := fun P hP => (hDred P hP).1
  have hDred_mem : ∀ P, D P ≠ 0 → P.point ∈ UF := fun P hP => (hDred P hP).2.1
  have hDred_one : ∀ P, D P ≠ 0 → D P = 1 := fun P hP => (hDred P hP).2.2
  -- The support of `D` has `genus C` elements.
  have hcardgen : D.support.card = RiemannRoch.Curve.genus (C.baseChange F) := by
    have hdegsum : (C.baseChange F).deg D = ∑ P ∈ D.support, D P * (P.degree : ℤ) := by
      change D.sum (fun P n => n * ((C.baseChange F).hom.residueDegree P.point : ℤ)) = _
      rw [Finsupp.sum_of_support_subset D (Finset.Subset.refl _)
          (fun P n => n * (P.degree : ℤ)) (fun i hi => by simp)]
    have hone : ∀ P ∈ D.support, D P * (P.degree : ℤ) = 1 := by
      intro P hP
      have hne' : D P ≠ 0 := Finsupp.mem_support_iff.mp hP
      rw [hDred_one P hne', hDred_deg P hne']; norm_num
    have hcardZ : (D.support.card : ℤ) = ∑ P ∈ D.support, D P * (P.degree : ℤ) := by
      rw [Finset.sum_congr rfl hone]
      simp [Finset.sum_const]
    have h1 : (D.support.card : ℤ) = (RiemannRoch.Curve.genus (C.baseChange F) : ℤ) := by
      rw [hcardZ, ← hdegsum, hDdeg]
    exact_mod_cast h1
  have hcardn : D.support.card = (RiemannRoch.Curve.genus C - 1) + 1 := by
    rw [hcardgen, RiemannRoch.Curve.genus_eq (Curve.bcSquare C F),
      Nat.sub_add_cancel (Nat.pos_of_ne_zero h)]
  -- Enumerate the support by `Fin ((genus C - 1) + 1)`.
  let n : ℕ := (RiemannRoch.Curve.genus C - 1) + 1
  have hcardn' : D.support.card = n := hcardn
  let ψ : Fin n ≃ {Q // Q ∈ D.support} :=
    (Fin.castOrderIso hcardn').toEquiv.symm.trans (Finset.equivFin D.support).symm
  -- Each place of the support is the point divisor of an `F`-point of `C`.
  have hex : ∀ m : Fin n, ∃ p : SpecLin.CurveFPt C F,
      SpecLin.ptDiv p = Work.CurveBasics.Curve.Div.place ((ψ m).1) := by
    intro m
    have hmem : (ψ m).1 ∈ D.support := (ψ m).2
    have hne' : D (ψ m).1 ≠ 0 := Finsupp.mem_support_iff.mp hmem
    have hdeg1 : ((ψ m).1).degree = 1 := hDred_deg _ hne'
    have heff : (Work.CurveBasics.Curve.Div.place ((ψ m).1)).IsEffective := by
      intro Q
      rw [Work.CurveBasics.Curve.Div.place, Finsupp.single_apply]
      split_ifs <;> norm_num
    have hdeg : (C.baseChange F).deg (Work.CurveBasics.Curve.Div.place ((ψ m).1)) = 1 := by
      rw [Work.CurveBasics.Curve.deg_place]
      exact_mod_cast hdeg1
    exact SpecLin.Points.ptDiv_complete _ heff hdeg
  choose x hxspec using hex
  -- The place of `x m` is the `m`-th place of the support.
  have hxplace : ∀ m : Fin n, SpecLin.ptPlace (x m) = (ψ m).1 := by
    intro m
    exact Finsupp.single_left_injective (by norm_num : (1:ℤ) ≠ 0) (hxspec m)
  -- `x m` lands in the chart open.
  have hxmem : ∀ m : Fin n, (x m).left (IsLocalRing.closedPoint F) ∈ chartU C := by
    intro m
    have hmem : (ψ m).1 ∈ D.support := (ψ m).2
    have hne' : D (ψ m).1 ≠ 0 := Finsupp.mem_support_iff.mp hmem
    have hmemUF : ((ψ m).1).point ∈ UF := hDred_mem _ hne'
    rw [hUF] at hmemUF
    have hpt : ((ψ m).1).point = SpecLin.ptToPoint (x m) := by
      rw [← hxplace m]; rfl
    rw [hpt] at hmemUF
    have hm : (Curve.bcSquare C F).π (SpecLin.ptToPoint (x m)) ∈ chartU C := by
      simpa only [Work.CurveBasics.Curve.BCSquare.preimage,
        AlgebraicGeometry.Scheme.Hom.mem_preimage] using hmemUF
    rwa [bcSquare_pi_ptToPoint C (x m)] at hm
  -- The `x m` are pairwise distinct.
  have hxinj : Function.Injective (fun m : Fin n => SpecLin.ptPlace (x m)) := by
    intro m m' hh
    have h1 : (ψ m).1 = (ψ m').1 := (hxplace m).symm.trans (hh.trans (hxplace m'))
    exact ψ.injective (Subtype.ext h1)
  -- The sum of the point divisors is `D`.
  have hsum : (∑ m : Fin n, SpecLin.ptDiv (x m)) = D := by
    have hstep1 : (∑ m : Fin n, SpecLin.ptDiv (x m))
        = ∑ m : Fin n, Work.CurveBasics.Curve.Div.place ((ψ m).1) := by
      apply Finset.sum_congr rfl; intro m _; exact hxspec m
    have hstep2 : (∑ m : Fin n, Work.CurveBasics.Curve.Div.place ((ψ m).1))
        = ∑ Q : {Q // Q ∈ D.support}, Work.CurveBasics.Curve.Div.place Q.1 :=
      Equiv.sum_comp ψ (fun Q => Work.CurveBasics.Curve.Div.place Q.1)
    have hstep3 : (∑ Q : {Q // Q ∈ D.support}, Work.CurveBasics.Curve.Div.place Q.1)
        = ∑ Q ∈ D.support, Work.CurveBasics.Curve.Div.place Q :=
      (Finset.sum_subtype D.support (fun x => Iff.rfl)
        (fun Q => Work.CurveBasics.Curve.Div.place Q)).symm
    have hstep4 : (∑ Q ∈ D.support, Work.CurveBasics.Curve.Div.place Q)
        = ∑ Q ∈ D.support, Finsupp.single Q (D Q) := by
      apply Finset.sum_congr rfl; intro Q hQ
      rw [Work.CurveBasics.Curve.Div.place, hDred_one Q (Finsupp.mem_support_iff.mp hQ)]
    have hstep5 : (∑ Q ∈ D.support, Finsupp.single Q (D Q)) = D :=
      (Finsupp.sum_of_support_subset D (Finset.Subset.refl _) Finsupp.single
        (fun i hi => Finsupp.single_zero i)).symm.trans (Finsupp.sum_single D)
    exact hstep1.trans (hstep2.trans (hstep3.trans (hstep4.trans hstep5)))
  refine ⟨x, hxinj, hxmem, ?_⟩
  rw [hsum, iOf_rochW_eq_i C F D, hDi]

/-- **A non-special degree-`g` divisor with pairwise distinct points, supported in the chart
open, over a field extension.**

Take `F := AlgebraicClosure K`, so that every place of `C_F` has degree one
(`Work.Charts.place_degree_eq_one_of_isAlgClosed`).  With `U_F := (Curve.bcSquare C F).π ⁻¹ᵁ
(chartU C)` the preimage of the chart open, the degree-one places of `U_F` are infinite
(`Work.Charts.infinite_places_compl_finset` for `C_F` together with
`Work.Charts.finite_places_notMem_of_ne_bot` for `U_F ≠ ⊥`, which holds because `chartU C`
contains the generic point and `π` is surjective), so
`Work.BNChart.reduced_nonspecial_support (C.baseChange F) U_F` produces an effective divisor `D`
of degree `genus C` with `i D = 0`, supported in `U_F`, with every coefficient `1` and every
place of degree one (its support therefore has exactly `genus C` elements).  Enumerate the places
of the support by `Fin ((genus C - 1) + 1)`, and use `Work.SpecLin.Points.ptDiv_complete` on each
single place to find an `F`-point `x m` of `C` with `ptDiv (x m) = Finsupp.single P 1`; then
`ptPlace (x m) = P`.  The `x m` are pairwise distinct (their places are), land in `chartU C`
(because `Work.BNChart.bcSquare_pi_ptToPoint` gives `π (P.point) = (x m).left (closedPoint F)`
and `P.point ∈ U_F = π ⁻¹ᵁ (chartU C)`), and `∑ m, ptDiv (x m) = D` has
`iOf C (rochW C) (·) = i (C.baseChange F) D = 0` by `Work.BNChart.iOf_rochW_eq_i`.

The declaration must live in `namespace Work.BNChart`. -/
theorem exists_reduced_nonspecial_chart {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    (h : RiemannRoch.Curve.genus C ≠ 0) :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra K F)
      (x : Fin ((RiemannRoch.Curve.genus C - 1) + 1) → Work.SpecLin.CurveFPt C F),
      Function.Injective (fun m => Work.SpecLin.ptPlace (x m)) ∧
      (∀ m, (x m).left (IsLocalRing.closedPoint F) ∈ Work.BNChart.chartU C) ∧
      Work.Charts.iOf C (Work.BNChart.rochW C) (∑ m, Work.SpecLin.ptDiv (x m)) = 0 := by
  refine ⟨AlgebraicClosure K, inferInstance, inferInstance, ?_⟩
  exact exists_reduced_nonspecial_chart_isAlgClosed C h

end

end Work.BNChart
