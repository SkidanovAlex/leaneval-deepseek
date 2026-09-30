import Mathlib
import Submission.Work.CurveBasics.All
import Submission.Work.SpecLin.Chart.Regular
import Submission.Work.RiemannRoch.RR.riemann_exists_polynomial_ordAt_pos
import Submission.Work.RiemannRoch.RR.riemann_poleDivisor_aeval
import Submission.Work.SpecLin.Alt.ordAt_add_one
import Submission.Work.SpecLin.Alt.ordAt_aeval_prod

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SpecLin.Alt

open Work.CurveBasics

/-- **A transcendental rational function regular on a prescribed finite set of points.**

`C` a smooth proper geometrically irreducible curve over `K`, `S ⊆ C` finite.  Then there is
`x ∈ K(C)` transcendental over `K` whose pole set is disjoint from `S`, i.e. `x` is regular at
every point of `S` (`Work.SpecLin.Chart.regularOpens C x` is by definition the complement of the
pole set of `x`).

Suggested route (no Riemann-Roch; works also for finite `K`).  Let
`S' := {Q : C.Place | Q.point ∈ S}`; it is finite since `S` is.  Take any transcendental
`x₀ : K(C)` (e.g. `Work.CurveBasics.exists_separating_element`, or a uniformizer of a place,
transcendental because every element of `K(C)` algebraic over `K` is a constant,
`Work.CurveBasics.Basic.eq_algebraMap_of_isAlgebraic`).

Case A: no `Q ∈ S'` with `0 ≤ C.ordAt x₀ Q`.  Then `x := (x₀ + 1)⁻¹` works: for `Q ∈ S'`,
`ord_Q (x₀+1) = ord_Q x₀ < 0`, so `ord_Q x > 0`.

Case B: otherwise let `P = {Q ∈ S' | 0 ≤ C.ordAt x₀ Q}` (finite, nonempty) and for `Q ∈ P` let
`f_Q ∈ K[T]` be the minimal polynomial over `K` of the value `x₀(Q) ∈ κ(Q)` (the image of `x₀`
under the evaluation `O_{C,Q} → κ(Q)`, available since `0 ≤ ord_Q x₀`; `κ(Q)` is finite over `K`
by `Curve.Place.degree_eq_finrank` and `Curve.Place.residueDegree_pos`).  Put
`F := ∏_{Q ∈ P} f_Q` and `x := (F(x₀) + 1)⁻¹`.  For `Q ∈ P` one has `ord_Q (F(x₀)) > 0`, hence
`ord_Q (F(x₀)+1) = 0` and `ord_Q x = 0`; for `Q ∈ S'` with `ord_Q x₀ < 0`, `F` is nonconstant, so
`ord_Q F(x₀) < 0` and `ord_Q x > 0`.  Finally `x` is transcendental, being the inverse of the
transcendental element `F(x₀)+1`.

Useful API: `Work.SpecLin.Chart.mem_regularOpens`, `place_mem_regularOpens_iff`,
`Curve.div_apply`, `Curve.div_mul`, `Curve.div_inv`, `Scheme.ord_mul`, `Scheme.ord_add`,
`Curve.Order.ordAt_inv`, `Work.CurveBasics.BaseChange.mem_range_algebraMap_stalk_iff`. -/
theorem exists_regular_transcendental {K : Type*} [Field K] (C : Work.CurveBasics.Curve K)
    (S : Set C.left) (hS : S.Finite) :
    ∃ x : C.functionField, Transcendental K x ∧
      S ⊆ (Work.SpecLin.Chart.regularOpens C x : Set C.left) := by
  classical
  -- a transcendental element of the function field
  obtain ⟨x₀, hx₀⟩ := Work.CurveBasics.exists_transcendental C
  haveI hfin : FiniteDimensional ↥(IntermediateField.adjoin K ({x₀} : Set C.functionField))
      C.functionField :=
    Work.CurveBasics.Order.finiteDimensional_adjoin_functionField C hx₀
  -- the finite set of places lying over `S`
  set S' : Set C.Place := {Q | Q.point ∈ S} with hS'def
  have hS'fin : S'.Finite := by
    have h : S' = (fun Q : C.Place => Q.point) ⁻¹' S := rfl
    rw [h]
    exact Set.Finite.preimage (Set.injOn_of_injective Subtype.val_injective) hS
  -- the places of `S'` at which `x₀` is regular
  set P : Set C.Place := {Q | Q ∈ S' ∧ 0 ≤ C.ordAt x₀ Q} with hPdef
  have hPfin : P.Finite := hS'fin.subset (fun Q hQ => hQ.1)
  -- at each `Q ∈ P` some nonzero polynomial expression in `x₀` vanishes at `Q`
  have hpoly : ∀ Q : C.Place, Q ∈ P →
      ∃ μ : Polynomial K, μ ≠ 0 ∧ 0 < C.ordAt (Polynomial.aeval x₀ μ) Q :=
    fun Q hQ => Work.RiemannRoch.RR.riemann_exists_polynomial_ordAt_pos C x₀ hx₀ Q hQ.2
  let μ : C.Place → Polynomial K := fun Q => if h : Q ∈ P then Classical.choose (hpoly Q h) else 1
  let F : Polynomial K := Polynomial.X * ∏ Q ∈ hPfin.toFinset, μ Q
  have hμspec : ∀ Q (hQ : Q ∈ P), μ Q = Classical.choose (hpoly Q hQ) := by
    intro Q hQ; dsimp only [μ]; rw [dite_eq_left hQ]
  have hμne : ∀ Q, Q ∈ P → μ Q ≠ 0 := by
    intro Q hQ; rw [hμspec Q hQ]; exact (Classical.choose_spec (hpoly Q hQ)).1
  have hμpos : ∀ Q, Q ∈ P → 0 < C.ordAt (Polynomial.aeval x₀ (μ Q)) Q := by
    intro Q hQ; rw [hμspec Q hQ]; exact (Classical.choose_spec (hpoly Q hQ)).2
  have hprod_ne : (∏ Q ∈ hPfin.toFinset, μ Q) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro Q hQ
    exact hμne Q (hPfin.mem_toFinset.mp hQ)
  have hF_ne : F ≠ 0 := by
    dsimp only [F]; exact mul_ne_zero Polynomial.X_ne_zero hprod_ne
  have hF_nat_ge : 1 ≤ F.natDegree := by
    dsimp only [F]
    rw [Polynomial.natDegree_mul Polynomial.X_ne_zero hprod_ne, Polynomial.natDegree_X]
    omega
  have hF_nat : F.natDegree ≠ 0 := by omega
  have hF_lead : F.leadingCoeff ∈ nonZeroDivisors K := by
    rw [mem_nonZeroDivisors_iff]
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rcases mul_eq_zero.mp hx with h | h
      · exact absurd h (Polynomial.leadingCoeff_ne_zero.mpr hF_ne)
      · exact h
    · rcases mul_eq_zero.mp hx with h | h
      · exact h
      · exact absurd h (Polynomial.leadingCoeff_ne_zero.mpr hF_ne)
  have htrans_aeval : Transcendental K (Polynomial.aeval x₀ F) := hx₀.aeval F hF_nat hF_lead
  have hF_aeval : Polynomial.aeval x₀ F
      = x₀ * ∏ Q ∈ hPfin.toFinset, Polynomial.aeval x₀ (μ Q) := by
    dsimp only [F]
    rw [Polynomial.aeval_mul, Polynomial.aeval_X]
    congr 1
    exact map_prod (Polynomial.aeval x₀) μ hPfin.toFinset
  have hμs : ∀ Q ∈ hPfin.toFinset, μ Q ≠ 0 := fun Q hQ => hμne Q (hPfin.mem_toFinset.mp hQ)
  have hprod_ne' : (∏ Q ∈ hPfin.toFinset, Polynomial.aeval x₀ (μ Q)) ≠ 0 := by
    rw [← map_prod (Polynomial.aeval x₀) μ hPfin.toFinset]
    exact fun h => hprod_ne (transcendental_iff_injective.mp hx₀ (by simpa using h))
  have hF_ord : ∀ Q : C.Place, C.ordAt (Polynomial.aeval x₀ F) Q
      = C.ordAt x₀ Q + ∑ Q' ∈ hPfin.toFinset, C.ordAt (Polynomial.aeval x₀ (μ Q')) Q := by
    intro Q
    rw [hF_aeval, C.ordAt_mul hx₀.ne_zero hprod_ne',
      ← map_prod (Polynomial.aeval x₀) μ hPfin.toFinset,
      ordAt_aeval_prod C x₀ hx₀ hPfin.toFinset μ hμs Q]
  -- at the places of `P` the value of `F` vanishes
  have hP_pos : ∀ Q ∈ P, 0 < C.ordAt (Polynomial.aeval x₀ F) Q := by
    intro Q hQ
    have hle : C.ordAt (Polynomial.aeval x₀ (μ Q)) Q
        ≤ ∑ Q' ∈ hPfin.toFinset, C.ordAt (Polynomial.aeval x₀ (μ Q')) Q :=
      Finset.single_le_sum
        (fun Q' hQ' => Work.RiemannRoch.RR.ordAt_aeval_nonneg C Q x₀ (μ Q') hQ.2)
        (hPfin.mem_toFinset.mpr hQ)
    linarith [hF_ord Q, hμpos Q hQ, hle, hQ.2]
  -- while at the places of `S'` at which `x₀` has a pole, `F(x₀)` has a pole as well
  have hP_neg : ∀ Q : C.Place, Q ∈ S' → Q ∉ P → C.ordAt (Polynomial.aeval x₀ F) Q < 0 := by
    intro Q hQS' hQnotP
    have hlt : C.ordAt x₀ Q < 0 := by
      have h : ¬ (0 ≤ C.ordAt x₀ Q) := fun h => hQnotP (show Q ∈ P from ⟨hQS', h⟩)
      exact not_le.mp h
    rw [Work.RiemannRoch.RR.ordAt_aeval_eq_of_neg C Q x₀ F hF_ne hlt]
    have hpos : (0 : ℤ) < (F.natDegree : ℤ) := by
      exact_mod_cast (show 0 < F.natDegree by omega)
    exact mul_neg_of_pos_of_neg hpos hlt
  let y : C.functionField := Polynomial.aeval x₀ F + 1
  let x : C.functionField := y⁻¹
  refine ⟨x, ?_, ?_⟩
  · -- `x` is transcendental: it is the inverse of the transcendental element `y`
    have hy : Transcendental K y := by
      intro halg
      apply htrans_aeval
      have h : IsAlgebraic K (Polynomial.aeval x₀ F + 1 - 1) :=
        IsAlgebraic.sub halg isAlgebraic_one
      simpa only [add_sub_cancel_right] using h
    intro halg
    exact hy (IsAlgebraic.inv_iff.mp (show IsAlgebraic K y⁻¹ from halg))
  · -- `x` is regular at every place lying over `S`
    intro z hz
    refine (Work.SpecLin.Chart.mem_regularOpens C x).mpr ?_
    intro Q hQ
    have hQS' : Q ∈ S' := by rw [hS'def]; show Q.point ∈ S; rw [hQ]; exact hz
    by_cases hQP : Q ∈ P
    · have h1 := (ordAt_add_one C Q (Polynomial.aeval x₀ F)).1 (hP_pos Q hQP)
      have hyne : y ≠ 0 := by dsimp only [y]; exact h1.2
      have hordy : C.ordAt y Q = 0 := by dsimp only [y]; exact h1.1
      have hxord : C.ordAt x Q = -C.ordAt y Q := by dsimp only [x]; exact C.ordAt_inv hyne Q
      rw [hxord, hordy]; norm_num
    · have h1 := (ordAt_add_one C Q (Polynomial.aeval x₀ F)).2 (hP_neg Q hQS' hQP)
      have hyne : y ≠ 0 := by dsimp only [y]; exact h1.2
      have hordy : C.ordAt y Q = C.ordAt (Polynomial.aeval x₀ F) Q := by
        dsimp only [y]; exact h1.1
      have hxord : C.ordAt x Q = -C.ordAt y Q := by dsimp only [x]; exact C.ordAt_inv hyne Q
      rw [hxord, hordy]
      linarith [hP_neg Q hQS' hQP]

end Work.SpecLin.Alt
