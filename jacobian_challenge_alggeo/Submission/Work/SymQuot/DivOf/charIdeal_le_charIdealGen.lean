import Mathlib
import Submission.Work.SymQuot.DivOf.C1Defs
import Submission.Work.SymQuot.DivOf.CharIdealGenDefs
import Submission.Work.SymQuot.DivOf.CharIdeal
import Submission.Work.SymQuot.DivOf.GenCharpoly
import Submission.Work.SymQuot.DivOf.LeGen.genCharpoly_coeff_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.DivOf

universe u
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
open Work.CurveBasics

/-! ### The coefficientwise `φ`-image of the generic characteristic polynomial

`ChartPt.genCharpolyValue` applies `φ` to the coefficients of `genCharpoly`.  We name the
coefficients of that element:

* `genCoeff d b k ∈ MvPolynomial (Fin r) F` is
  `∑_α monomial α (φ ((genCharpoly C n d.V b).coeff k).coeff α)`;
* `genCharpolyValue_eq_sum` re-reads `ChartPt.genCharpolyValue` in terms of it;
* `genCoeff_coeff` computes its coefficients: the coefficient of `β` is the `φ`-value of the
  corresponding invariant coefficient of `genCharpoly`.

For the family `Fin 1 ∋ _ ↦ b` (a single section), `genCoeff_coeff_one` computes the
coefficient of `X₀ ^ (n - k)`: by `genCharpoly_coeff_one` it is `φ ((charpoly ...).coeff k)`,
which is exactly the coefficient occurring in `ChartPt.charpolyValue`.
-/

/-- **The coefficientwise `φ`-image of the `k`-th coefficient of the generic characteristic
polynomial**: the polynomial `∑_α X^α · φ (coefficient of α)`. -/
noncomputable def genCoeff {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F} (d : ChartPt C n p) {r : ℕ}
    (b : Fin r → C.left.presheaf.obj (Opposite.op d.V)) (k : ℕ) :
    MvPolynomial (Fin r) F :=
  ∑ α ∈ ((genCharpoly C n d.V b).coeff k).support,
    MvPolynomial.monomial α (d.φ ⟨((genCharpoly C n d.V b).coeff k).coeff α,
      genCharpoly_coeff_coeff_mem d.V b k α⟩)

/-- `ChartPt.genCharpolyValue` is the sum of the `C (genCoeff d b k) * X ^ k`. -/
theorem genCharpolyValue_eq_sum {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F} (d : ChartPt C n p) {r : ℕ}
    (b : Fin r → C.left.presheaf.obj (Opposite.op d.V)) :
    d.genCharpolyValue b =
      ∑ k ∈ Finset.range (n+1), Polynomial.C (genCoeff d b k) * Polynomial.X ^ k := by
  rw [ChartPt.genCharpolyValue]
  rfl

/-- **The coefficients of `genCoeff`**: the coefficient of `β` is the `φ`-value of the
corresponding invariant coefficient of `genCharpoly`. -/
theorem genCoeff_coeff {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F} (d : ChartPt C n p) {r : ℕ}
    (b : Fin r → C.left.presheaf.obj (Opposite.op d.V)) (k : ℕ) (β : Fin r →₀ ℕ) :
    (genCoeff d b k).coeff β =
      d.φ ⟨((genCharpoly C n d.V b).coeff k).coeff β, genCharpoly_coeff_coeff_mem d.V b k β⟩ := by
  classical
  rw [genCoeff, MvPolynomial.coeff_sum]
  rw [Finset.sum_congr rfl (fun α _ => by rw [MvPolynomial.coeff_monomial])]
  rw [Finset.sum_ite_eq']
  by_cases hβ : β ∈ ((genCharpoly C n d.V b).coeff k).support
  · rw [ite_eq_left hβ]
  · rw [ite_eq_right hβ]
    have h0 : ((genCharpoly C n d.V b).coeff k).coeff β = 0 :=
      MvPolynomial.notMem_support_iff.mp hβ
    have h : d.φ ⟨((genCharpoly C n d.V b).coeff k).coeff β,
        genCharpoly_coeff_coeff_mem d.V b k β⟩ = d.φ (0 : ↥d.chartRingOf) :=
      congrArg d.φ (Subtype.ext h0)
    rw [h, map_zero]

/-- **The coefficient of `X₀ ^ (n - k)` in `genCoeff` for a single section** is the `φ`-value of
the `k`-th coefficient of the characteristic polynomial `χ_b`. -/
theorem genCoeff_coeff_one {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F} (d : ChartPt C n p)
    (b : C.left.presheaf.obj (Opposite.op d.V)) {k : ℕ} (hk : k ≤ n) :
    (genCoeff d (fun _ : Fin 1 => b) k).coeff (Finsupp.single 0 (n - k)) =
      d.φ ⟨(charpoly C n d.V b).coeff k,
        charpoly_coeff_mem_chartInvariants C n d.V (symPiOpen_invariant C n d.V) b k⟩ := by
  have hcoe : ((genCharpoly C n d.V (fun _ : Fin 1 => b)).coeff k).coeff
        (Finsupp.single 0 (n - k)) = (charpoly C n d.V b).coeff k := by
    rw [LeGen.genCharpoly_coeff_one d.V b hk, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow]
    simp
  rw [genCoeff_coeff]
  by_cases hβ : Finsupp.single (0 : Fin 1) (n - k) ∈
      ((genCharpoly C n d.V (fun _ : Fin 1 => b)).coeff k).support
  · exact congrArg d.φ (Subtype.ext hcoe)
  · have h0 : ((genCharpoly C n d.V (fun _ : Fin 1 => b)).coeff k).coeff
        (Finsupp.single 0 (n - k)) = 0 := MvPolynomial.notMem_support_iff.mp hβ
    have hχ : (charpoly C n d.V b).coeff k = 0 := hcoe.symm.trans h0
    have hsubL : (⟨((genCharpoly C n d.V (fun _ : Fin 1 => b)).coeff k).coeff
          (Finsupp.single 0 (n - k)),
        genCharpoly_coeff_coeff_mem d.V (fun _ : Fin 1 => b) k (Finsupp.single 0 (n - k))⟩ :
        ↥d.chartRingOf) = 0 :=
      Subtype.ext h0
    have hsubR : (⟨(charpoly C n d.V b).coeff k,
        charpoly_coeff_mem_chartInvariants C n d.V (symPiOpen_invariant C n d.V) b k⟩ :
        ↥d.chartRingOf) = 0 :=
      Subtype.ext hχ
    rw [hsubL, hsubR, map_zero]

/-- **The `k`-th term of the generic generator at `r = 1`**: its coefficient of `X₀ ^ n` is the
`k`-th term of `eval₂ s (secAlpha b) (charpolyValue b)`. -/
theorem genCoeff_term_eq {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F} (d : ChartPt C n p)
    (b : C.left.presheaf.obj (Opposite.op d.V)) (k : ℕ) (hk : k ∈ Finset.range (n+1)) :
    (MvPolynomial.map (secConst C F d.V) (genCoeff d (fun _ : Fin 1 => b) k) *
        (MvPolynomial.C (secAlpha C F d.V b) * MvPolynomial.X 0) ^ k).coeff (Finsupp.single 0 n)
      = secConst C F d.V (d.φ ⟨(charpoly C n d.V b).coeff k,
            charpoly_coeff_mem_chartInvariants C n d.V (symPiOpen_invariant C n d.V) b k⟩)
          * (secAlpha C F d.V b) ^ k := by
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hC : (MvPolynomial.C (secAlpha C F d.V b) * MvPolynomial.X (0 : Fin 1)) ^ k
      = MvPolynomial.C ((secAlpha C F d.V b) ^ k) * MvPolynomial.X (0 : Fin 1) ^ k := by
    rw [mul_pow, MvPolynomial.C_pow]
  rw [hC]
  rw [show MvPolynomial.map (secConst C F d.V) (genCoeff d (fun _ : Fin 1 => b) k) *
      (MvPolynomial.C ((secAlpha C F d.V b) ^ k) * MvPolynomial.X 0 ^ k)
      = MvPolynomial.C ((secAlpha C F d.V b) ^ k) *
        (MvPolynomial.map (secConst C F d.V) (genCoeff d (fun _ : Fin 1 => b) k) *
          MvPolynomial.X 0 ^ k)
      from by ring]
  rw [MvPolynomial.coeff_C_mul]
  have hidx : Finsupp.single (0 : Fin 1) n = Finsupp.single 0 (n - k) + Finsupp.single 0 k := by
    rw [← Finsupp.single_add, Nat.sub_add_cancel hkn]
  rw [hidx, MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_mul_monomial, mul_one,
    MvPolynomial.coeff_map, genCoeff_coeff_one d b hkn, mul_comm]

/-- **The generator `χ_b(b)` of `charIdeal` is the coefficient of `X₀ ^ n` of the generic
generator for the single section `b`**, hence lies in `charIdealGen`. -/
theorem charIdeal_generator_mem {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F} (d : ChartPt C n p)
    (b : C.left.presheaf.obj (Opposite.op d.V)) :
    Polynomial.eval₂ (sectionsAlgebraMap (C.baseChange F) (C.bcOpens F d.V))
      (((Curve.baseChangeFst C F).app d.V).hom b) (d.charpolyValue b) ∈ charIdealGen F d := by
  rw [show Polynomial.eval₂ (sectionsAlgebraMap (C.baseChange F) (C.bcOpens F d.V))
      (((Curve.baseChangeFst C F).app d.V).hom b) (d.charpolyValue b)
      = Polynomial.eval₂ (secConst C F d.V) (secAlpha C F d.V b) (d.charpolyValue b) from by
        rw [← secAlpha_eq_app]
        rfl]
  rw [show Polynomial.eval₂ (secConst C F d.V) (secAlpha C F d.V b) (d.charpolyValue b)
      = (d.genGenerator (K := K) (fun _ : Fin 1 => b)).coeff (Finsupp.single 0 n) from by
    rw [show Polynomial.eval₂ (secConst C F d.V) (secAlpha C F d.V b) (d.charpolyValue b)
        = ∑ k ∈ Finset.range (n+1),
          secConst C F d.V (d.φ ⟨(charpoly C n d.V b).coeff k,
            charpoly_coeff_mem_chartInvariants C n d.V (symPiOpen_invariant C n d.V) b k⟩)
          * (secAlpha C F d.V b) ^ k from by
      rw [ChartPt.charpolyValue_def, Polynomial.eval₂_finsetSum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X]]
    rw [show (d.genGenerator (K := K) (fun _ : Fin 1 => b)).coeff (Finsupp.single 0 n)
        = ∑ k ∈ Finset.range (n+1),
          (MvPolynomial.map (secConst C F d.V) (genCoeff d (fun _ : Fin 1 => b) k) *
            (MvPolynomial.C (secAlpha C F d.V b) * MvPolynomial.X 0) ^ k).coeff
              (Finsupp.single 0 n) from by
      rw [ChartPt.genGenerator, Fin.sum_univ_one, genCharpolyValue_eq_sum,
        Polynomial.eval₂_finsetSum, MvPolynomial.coeff_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X]]
    refine Finset.sum_congr rfl fun k hk => ?_
    exact (genCoeff_term_eq d b k hk).symm]
  rw [charIdealGen]
  exact Ideal.subset_span ⟨1, (fun _ : Fin 1 => b), Finsupp.single 0 n, rfl⟩

theorem charIdeal_le_charIdealGen {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F} (d : ChartPt C n p) :
    charIdeal F d ≤ charIdealGen F d := by
  rw [charIdeal]
  refine Ideal.span_le.mpr ?_
  rintro g ⟨b, rfl⟩
  exact charIdeal_generator_mem d b

namespace Work.SymQuot.DivOf

/-- Compatibility copy of `Work.SymQuot.DivOf.charIdeal_le_charIdealGen` under the doubled
name produced by the original skeleton of this file. -/
theorem charIdeal_le_charIdealGen {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F} (d : ChartPt C n p) :
    charIdeal F d ≤ charIdealGen F d :=
  _root_.Work.SymQuot.DivOf.charIdeal_le_charIdealGen d

end Work.SymQuot.DivOf

end Work.SymQuot.DivOf
