import Mathlib
import Submission.Work.MotK.LinkCertDefs
import Submission.Work.MotK.ChartCompAux
import Submission.Work.MotK.UnitChartC
import Submission.Work.MotK.KleinTwLinkComp2
import Submission.Work.MotK.ChartGambTilNeZero
import Submission.Work.MotK.ChartBilinRNeZero
import Submission.Work.MotK.ChartSdualNeZero
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.ChartCompC` — the two affine chart maps of the T-twisted link are inverse

The T-twisted Crauder--Katz link is given on the affine charts `v₀ = 0`, `v₄ = 1`
(and `w₀ = 0`, `w₄ = 1` on the target) by the two rational maps

* `f = kleinTwP ∘ kleinTwStereo` (forward), with chart coordinates `φ_j = f̂_{j+1}/f̂₄`,
* `χ = kleinTwPi p ∘ kleinTwR` (inverse), with chart coordinates `η_j = ǧ_{j+1}/ǧ₄`,

whose pullbacks are the `K`-algebra endomorphisms `Ψ = aeval φ` and `Φ = aeval η` of
`FracC K = Frac K[x₀,x₁,x₂]` (`Work.MotK.PsiCh`, `Work.MotK.PhiCh`).

`ChartCompC` states that the two composites are the identity *on the three coordinate
generators*.  The proof computes the two pullbacks explicitly.  Writing
`c = (A f̂₄)⁻¹`, `d = (A ǧ₄)⁻¹` (with `A = algebraMap K[x₀,x₁,x₂] (FracC K)`), the two unit
identities of the link (`KleinTwLinkComp2`, resp. `KleinTwLinkComp1`) give, on the substituted
chart vectors,
`Ψ(ǧᵢ) = c³ · A(-GambC) · A(chartᵢ)`  and  `Φ(f̂ᵢ) = d⁴ · A(b(p,R chart)² s'(chart)) · A(chartᵢ)`;
since `chart_{j+1} = X_j` and `chart₄ = 1`, the two ratios are the two composite scalars, and the
conclusion follows because both are nonzero: `f̂₄ ≠ 0`, `ǧ₄ ≠ 0` (`UnitChartC`), `GambC ≠ 0`
(`ChartGambTilNeZero` together with `GambC = C((a·h)⁻¹)^6 · GambTil`), and the two factors
`b(p,R chart) ≠ 0`, `s'(chart) ≠ 0` (`ChartBilinRNeZero`, `ChartSdualNeZero`).
-/

set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

namespace Work.MotK

open MvPolynomial

/-- Componentwise form of the composite `χ ∘ f = -GambC · id` of `KleinTwLinkComp2`: the
`i`-th component of the pullback of the inverse chart map along the forward chart map is
`-(GambC) · chartᵢ`. -/
theorem aeval_bwPoly_gen (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0)
    (i : Fin 5) :
    MvPolynomial.aeval (fhatC K a b h) (bwPoly K a b h i)
      = -(GambC K a b h) * chartC K i := by
  have hp : (fun i => MvPolynomial.C (kleinPointT a b h i)) = pRaC K a b h := rfl
  rw [TGen.AevalBwPoly, ← MvPolynomial.C_eq_algebraMap, UnitChartCAux.fhatC_eq K a b h, ← hp]
  rw [show kleinTwPi (fun i => MvPolynomial.C (kleinPointT a b h i))
        (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
            (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
              (fun i => MvPolynomial.C (kleinPointT a b h i)) (chartC K))))
      = fun k => -(GambC K a b h) * chartC K k from
    KleinTwLinkComp2 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (fun i => MvPolynomial.C (kleinPointT a b h i)) (chartC K)
      (kleinTwQ_pRaC K a b h ha hh) (by simp) (UnitChartCAux.chartC0 K)]

/-- Componentwise form of the composite `f ∘ χ` of `KleinTwLinkComp1`: the `i`-th component of
the pullback of the forward chart map along the inverse chart map is
`b(p,R chart)² · s'(chart) · chartᵢ`. -/
theorem aeval_fwPoly_gen (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0)
    (i : Fin 5) :
    MvPolynomial.aeval (ghatC K a b h) (fwPoly K a b h i)
      = (kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
            (pRaC K a b h)
            (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chartC K))) ^ 2
          * kleinTwSDualInv (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chartC K)
          * chartC K i := by
  have hp : (fun i => MvPolynomial.C (kleinPointT a b h i)) = pRaC K a b h := rfl
  rw [TGen.AevalFwPoly, ← MvPolynomial.C_eq_algebraMap, UnitChartCAux.ghatC_eq K a b h, ← hp]
  rw [show kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (fun i => MvPolynomial.C (kleinPointT a b h i))
          (kleinTwPi (fun i => MvPolynomial.C (kleinPointT a b h i))
            (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chartC K))))
      = fun k => (kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b)
            (MvPolynomial.C h) (fun i => MvPolynomial.C (kleinPointT a b h i))
            (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chartC K))) ^ 2
          * kleinTwSDualInv (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chartC K)
          * chartC K k from
    KleinTwLinkComp1 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (fun i => MvPolynomial.C (kleinPointT a b h i)) (chartC K)
      (kleinTwQ_pRaC K a b h ha hh) (UnitChartCAux.chartC0 K)]

/-- The substitution of the chart coordinates into the inverse chart map's component `ǧᵢ` is
`c³ · A(-GambC)`, where `c = (A f̂₄)⁻¹`. -/
theorem psiCh_ghatC_gen (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0)
    (hf4 : fhatC K a b h 4 ≠ 0) (i : Fin 5) :
    PsiCh K a b h (ghatC K a b h i)
      = ((algebraMap (MvPolynomial (Fin 3) K) (FracC K) (fhatC K a b h 4))⁻¹) ^ 3
        * algebraMap (MvPolynomial (Fin 3) K) (FracC K)
            (MvPolynomial.aeval (fhatC K a b h) (bwPoly K a b h i)) := by
  have hf4' : algebraMap (MvPolynomial (Fin 3) K) (FracC K) (fhatC K a b h 4) ≠ 0 := fun h0 =>
    hf4 (IsFractionRing.injective (MvPolynomial (Fin 3) K) (FracC K) (by rw [h0, map_zero]))
  have hvec := UnitChartCAux.psiCh_chartC K a b h ha hh hf4'
  rw [← UnitChartCAux.aeval_chartC_bwPoly K a b h i,
    UnitChartCAux.algHom_aeval (PsiCh K a b h) (chartC K) (bwPoly K a b h i), hvec,
    UnitChartCAux.aeval_smul_bwPoly (c := (algebraMap (MvPolynomial (Fin 3) K) (FracC K)
        (fhatC K a b h 4))⁻¹)
      (y := fun i => algebraMap (MvPolynomial (Fin 3) K) (FracC K) (fhatC K a b h i)) (j := i),
    UnitChartCAux.aeval_algebraMap (y := fhatC K a b h) (P := bwPoly K a b h i)]

/-- The substitution of the chart coordinates into the forward chart map's component `f̂ᵢ` is
`d⁴ · A(b(p,R chart)² s'(chart))`, where `d = (A ǧ₄)⁻¹`. -/
theorem phiCh_fhatC_gen (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0)
    (hg4 : ghatC K a b h 4 ≠ 0) (i : Fin 5) :
    PhiCh K a b h (fhatC K a b h i)
      = ((algebraMap (MvPolynomial (Fin 3) K) (FracC K) (ghatC K a b h 4))⁻¹) ^ 4
        * algebraMap (MvPolynomial (Fin 3) K) (FracC K)
            (MvPolynomial.aeval (ghatC K a b h) (fwPoly K a b h i)) := by
  have hg4' : algebraMap (MvPolynomial (Fin 3) K) (FracC K) (ghatC K a b h 4) ≠ 0 := fun h0 =>
    hg4 (IsFractionRing.injective (MvPolynomial (Fin 3) K) (FracC K) (by rw [h0, map_zero]))
  have hvec := UnitChartCAux.etaCh_chartC K a b h hg4'
  rw [← UnitChartCAux.aeval_chartC_fwPoly K a b h i,
    UnitChartCAux.algHom_aeval (PhiCh K a b h) (chartC K) (fwPoly K a b h i), hvec,
    UnitChartCAux.aeval_smul_fwPoly (c := (algebraMap (MvPolynomial (Fin 3) K) (FracC K)
        (ghatC K a b h 4))⁻¹)
      (y := fun i => algebraMap (MvPolynomial (Fin 3) K) (FracC K) (ghatC K a b h i)) (j := i),
    UnitChartCAux.aeval_algebraMap (y := ghatC K a b h) (P := fwPoly K a b h i)]

/-- Explicit value of the pullback of a chart function along the forward chart map:
`Ψ(ǧᵢ) = c³ · A(-GambC) · A(chartᵢ)`. -/
theorem PsiCh_ghatC_val (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0)
    (hf4 : fhatC K a b h 4 ≠ 0) (i : Fin 5) :
    PsiCh K a b h (ghatC K a b h i)
      = ((algebraMap (MvPolynomial (Fin 3) K) (FracC K) (fhatC K a b h 4))⁻¹) ^ 3
        * algebraMap (MvPolynomial (Fin 3) K) (FracC K) (-(GambC K a b h))
        * algebraMap (MvPolynomial (Fin 3) K) (FracC K) (chartC K i) := by
  rw [psiCh_ghatC_gen K a b h ha hh hf4 i, aeval_bwPoly_gen K a b h ha hh i]
  simp only [map_mul, map_neg]
  first | refl_ring1 | ring

/-- Explicit value of the pullback of a chart function along the inverse chart map:
`Φ(f̂ᵢ) = d⁴ · A(b(p,R chart)² s'(chart)) · A(chartᵢ)`. -/
theorem PhiCh_fhatC_val (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0)
    (hg4 : ghatC K a b h 4 ≠ 0) (i : Fin 5) :
    PhiCh K a b h (fhatC K a b h i)
      = ((algebraMap (MvPolynomial (Fin 3) K) (FracC K) (ghatC K a b h 4))⁻¹) ^ 4
        * algebraMap (MvPolynomial (Fin 3) K) (FracC K)
            ((kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
                (pRaC K a b h)
                (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
                  (chartC K))) ^ 2
              * kleinTwSDualInv (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
                  (chartC K))
        * algebraMap (MvPolynomial (Fin 3) K) (FracC K) (chartC K i) := by
  rw [phiCh_fhatC_gen K a b h ha hh hg4 i, aeval_fwPoly_gen K a b h ha hh i]
  simp only [map_mul, map_pow]
  first | refl_ring1 | ring

/-- The affine chart's `(j+1)`-st coordinate is the `j`-th coordinate function. -/
theorem chartC_succ (K : Type*) [CommRing K] (j : Fin 3) :
    chartC K ⟨j.val + 1, by omega⟩ = MvPolynomial.X j := by
  fin_cases j <;> rfl

/-- The composite scalar `c³ · A(-GambC)` of the forward chart map is nonzero. -/
theorem cC_ne_zero (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0)
    (hf4 : fhatC K a b h 4 ≠ 0) (hG : GambC K a b h ≠ 0) :
    ((algebraMap (MvPolynomial (Fin 3) K) (FracC K) (fhatC K a b h 4))⁻¹) ^ 3
      * algebraMap (MvPolynomial (Fin 3) K) (FracC K) (-(GambC K a b h)) ≠ 0 := by
  have hf4' : algebraMap (MvPolynomial (Fin 3) K) (FracC K) (fhatC K a b h 4) ≠ 0 := fun h0 =>
    hf4 (IsFractionRing.injective (MvPolynomial (Fin 3) K) (FracC K) (by rw [h0, map_zero]))
  refine mul_ne_zero (pow_ne_zero 3 (inv_ne_zero hf4')) ?_
  rw [map_neg]
  exact neg_ne_zero.mpr (fun h0 =>
    hG (IsFractionRing.injective (MvPolynomial (Fin 3) K) (FracC K) (by rw [h0, map_zero])))

/-- The composite scalar `d⁴ · A(b(p,R chart)² s'(chart))` of the inverse chart map is nonzero. -/
theorem dC_ne_zero (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0)
    (hg4 : ghatC K a b h 4 ≠ 0)
    (hB : kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (pRaC K a b h)
      (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chartC K)) ≠ 0)
    (hS : kleinTwSDualInv (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (chartC K) ≠ 0) :
    ((algebraMap (MvPolynomial (Fin 3) K) (FracC K) (ghatC K a b h 4))⁻¹) ^ 4
      * algebraMap (MvPolynomial (Fin 3) K) (FracC K)
          ((kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
              (pRaC K a b h)
              (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
                (chartC K))) ^ 2
            * kleinTwSDualInv (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
                (chartC K)) ≠ 0 := by
  have hg4' : algebraMap (MvPolynomial (Fin 3) K) (FracC K) (ghatC K a b h 4) ≠ 0 := fun h0 =>
    hg4 (IsFractionRing.injective (MvPolynomial (Fin 3) K) (FracC K) (by rw [h0, map_zero]))
  refine mul_ne_zero (pow_ne_zero 4 (inv_ne_zero hg4')) ?_
  refine fun h0 => ?_
  have h0' : (kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (pRaC K a b h)
      (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chartC K))) ^ 2
      * kleinTwSDualInv (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chartC K) = 0 :=
    IsFractionRing.injective (MvPolynomial (Fin 3) K) (FracC K) (by rw [h0, map_zero])
  rcases mul_eq_zero.mp h0' with h | h
  · exact hB (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)
  · exact hS h

/-- `GambC ≠ 0`: the source equation of the T-twisted link does not vanish identically. -/
theorem GambC_ne_zero (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    GambC K a b h ≠ 0 := by
  rw [GambC_eq_C_mul_GambTil (K := K) a b h ha hh]
  refine mul_ne_zero (pow_ne_zero 6 fun h0 => ?_) (ChartGambTilNeZero K a b h ha hb hh)
  have h1 := congrArg (fun p : MvPolynomial (Fin 3) K => p.coeff 0) h0
  simp only [MvPolynomial.coeff_C, MvPolynomial.coeff_zero] at h1
  exact inv_ne_zero (mul_ne_zero ha hh) h1

/-- Assembly: the two chart maps of the T-twisted link are inverse on the coordinate generators,
given the non-vanishing of the two composite scalars. -/
theorem ChartCompC_aux (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (hG : GambC K a b h ≠ 0)
    (hB : kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (pRaC K a b h)
      (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chartC K)) ≠ 0)
    (hS : kleinTwSDualInv (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (chartC K) ≠ 0) :
    (∀ j : Fin 3,
      PsiCh K a b h (ghatC K a b h ⟨j.val + 1, by omega⟩)
          * (PsiCh K a b h (ghatC K a b h 4))⁻¹
        = algebraMap (MvPolynomial (Fin 3) K) (FracC K) (MvPolynomial.X j) ∧
      PhiCh K a b h (fhatC K a b h ⟨j.val + 1, by omega⟩)
          * (PhiCh K a b h (fhatC K a b h 4))⁻¹
        = algebraMap (MvPolynomial (Fin 3) K) (FracC K) (MvPolynomial.X j)) := by
  have hf4 := UnitChartCAux.fhatC_four_ne_zero K a b h ha hb hh
  have hg4 := UnitChartCAux.ghatC_four_ne_zero K a b h ha hb hh
  have hz1 := cC_ne_zero K a b h ha hh hf4 hG
  have hz2 := dC_ne_zero K a b h ha hh hg4 hB hS
  intro j
  constructor
  · have h1 := PsiCh_ghatC_val K a b h ha hh hf4 ⟨j.val + 1, by omega⟩
    have h2 := PsiCh_ghatC_val K a b h ha hh hf4 4
    rw [h1, h2, chartC_succ K j, UnitChartCAux.chartC4 K, map_one, mul_one]
    exact UnitChartCAux.mul_aux (mul_inv_cancel₀ hz1)
  · have h1 := PhiCh_fhatC_val K a b h ha hh hg4 ⟨j.val + 1, by omega⟩
    have h2 := PhiCh_fhatC_val K a b h ha hh hg4 4
    rw [h1, h2, chartC_succ K j, UnitChartCAux.chartC4 K, map_one, mul_one]
    exact UnitChartCAux.mul_aux (mul_inv_cancel₀ hz2)

theorem ChartCompC (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (j : Fin 3) :
    Work.MotK.PsiCh K a b h (Work.MotK.ghatC K a b h ⟨j.val + 1, by omega⟩)
        * (Work.MotK.PsiCh K a b h (Work.MotK.ghatC K a b h 4))⁻¹
      = algebraMap (MvPolynomial (Fin 3) K) (Work.MotK.FracC K) (MvPolynomial.X j) ∧
    Work.MotK.PhiCh K a b h (Work.MotK.fhatC K a b h ⟨j.val + 1, by omega⟩)
        * (Work.MotK.PhiCh K a b h (Work.MotK.fhatC K a b h 4))⁻¹
      = algebraMap (MvPolynomial (Fin 3) K) (Work.MotK.FracC K) (MvPolynomial.X j) :=
  ChartCompC_aux K a b h ha hb hh (GambC_ne_zero K a b h ha hb hh)
    (ChartBilinRNeZero K a b h ha hb hh) (ChartSdualNeZero K a b h ha hb hh) j

end Work.MotK
