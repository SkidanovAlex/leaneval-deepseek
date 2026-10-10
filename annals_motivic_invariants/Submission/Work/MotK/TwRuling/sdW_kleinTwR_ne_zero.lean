import Mathlib
import Submission.Work.MotK.TGen.SdualTBrick
import Submission.Work.MotK.KleinTwRuleMem
import Submission.Work.MotK.TwDataMod5
import Submission.Work.MotK.TwRule.KleinTwRuleEval
import Submission.Work.MotK.TwRuling.sdY_curve
import Submission.Work.MotK.TwRuling.SdThetaSdualT
import Submission.Work.MotK.TwRuling.TwSixCoeffDefs
import Submission.Work.MotK.TwRuling.TwSixAssemblyDefs
import Submission.Work.MotK.TwRuling.sexticTw_notMem_kernel
import Submission.Work.MotK.TwRuling.sdCoeff6_mem
import Submission.Work.MotK.TwRuling.sdCoeff6_notMem_twIdeal6
import Submission.Work.MotK.TwRuling.sdCoeff6_eval_family
import Submission.Work.MotK.TwRuling.coeff_disjunction
import Submission.Work.MotK.TwRuling.kappaP_kernel_hypotheses
import Submission.Work.MotK.TwRuling.aeval_kappaP
import Submission.Work.MotK.TwRuling.coeff_rpEval
import Submission.Work.MotK.TwRuling.sdW_ne_zero_of_coeff
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TwRuling.sdW_kleinTwR_ne_zero`

**Target.** For a good Klein datum `D` over a field `K` and `h ≠ 0`,

    kleinTwR (algebraMap K (sdA K D h) D.a) … (sdW K D h) ≠ 0 ,

where `sdA K D h = RatFunc ↥(twistFieldTG K D h)` and `sdW K D h = A(sdY) + t·B(sdY)` is the
ruling point of the target ruling divisor.

## Route (in final form)

1. `sdW_kleinTwR_eq` (below, proved): the inverse cubic map `kleinTwR` is projectively constant on
   the ruling line, so `kleinTwR (sdW) i = kleinTwR (sdW) 0 · sdY i`.  Hence the target is
   *equivalent* to `kleinTwR (sdW) 0 ≠ 0`, i.e. to `kleinTwR0 (sdW) ≠ 0`.

2. `Work.MotK.TwRuling.sdW_ne_zero_of_coeff`: if the `j`-th coefficient of the ruling polynomial
   `rpEval K D h = R₀(A(twCoordG) + T·B(twCoordG)) ∈ OmG K D [T]` is nonzero, then the target
   holds (the natural map `RatFunc ↥F →+* RatFunc (OmG K D)` sends `kleinTwR0 (sdW)` to the image
   of `rpEval`).

3. So it suffices to find `j` with `(rpEval K D h).coeff j ≠ 0`, i.e. (by `coeff_rpEval`) with
   `aeval (twCoordG) (sdCoeff6 R a b h j) ≠ 0` (`R = KbG K`, `a, b, h` the images of `D.a, D.b, h`).
   By `aeval_kappaP`, `aeval (kappaP) F = κ₀^6 · aeval (twCoordG) F` for `F` of degree `6`, and by
   `sexticTw_notMem_kernel` (applied to `kappaP`, whose span is `L(5·O)` and which satisfies the
   five twisted Pfaffians — `kappaP_kernel_hypotheses`) it *suffices* that
   `sdCoeff6 R a b h j ∉ twIdeal6 R a b h` for some `j ∈ {2,3}`.

4. `Work.MotK.TwRuling.coeff_disjunction` supplies such a `j ∈ {2,3}` from `D.Good`, using
   - `sdCoeff6_notMem_twIdeal6` (`j = 3`, valid when `27a⁵ ≠ 11b⁵`),
   - `sdCoeff6_notMem_two'` (below, `j = 2`, valid when `57a⁵ ≠ b⁵`),
   and the three exceptional characteristics `2, 3, 5` (in char `3` the first form is `b⁵ ≠ 0`; in
   char `5` the second is excluded by `good_bFive_ne_charFive`; in char `2` both forms are
   `a⁵ + b⁵` and are excluded by `good_ne_charTwo`).

5. `Work.MotK.TwRuling.sdCoeff6_mem` supplies the homogeneity input of `sexticTw_notMem_kernel`.

## Status / what is and is not proved here

* `Work.MotK.TwRuling.sdW_kleinTwR_ne_zero_charNeTwo_of_sdCoeff6` (below) is **proved and
  axiom-clean** (only `propext`, `Classical.choice`, `Quot.sound`): the target in
  characteristic `≠ 2`.  It uses `Work.MotK.TwRuling.coeff_disjunction_charNeTwo` (below), the
  variant of `coeff_disjunction` in which the characteristic-`2` branch is excluded by
  `(2 : K) ≠ 0` instead of by `good_ne_charTwo`.

* `Work.MotK.TwRuling.sdW_kleinTwR_ne_zero` (the target as requested) is proved from
  `Work.MotK.TwRuling.coeff_disjunction`, whose **only** unproved input is

      Work.MotK.TwRuling.good_ne_charTwo : ringChar K = 2 → D.a ^ 5 ≠ D.b ^ 5 .

  `#print axioms Work.MotK.TwRuling.sdW_kleinTwR_ne_zero` therefore still shows `sorryAx`.
  In characteristic `2`, `a⁵ = b⁵` is equivalent to `a = b` (Frobenius), and then
  *all four* forms `sdCoeff6 a b h j` (`j = 0..3`) lie in the twisted Pfaffian ideal `twIdeal6`
  (verified by a Gröbner computation over `GF(2)`); by the exactness of the degree-six kernel
  lemma this makes `rpEval K D h = 0` and hence `kleinTwR (sdW) = 0`.  So the target *is*
  equivalent to `good_ne_charTwo`, and the latter is the one remaining mathematical gap.

  The route to `good_ne_charTwo` that the area owner is building is
  `Work.MotK.TwRuling.c4_cube_of_good`
  (`c₄(E)³ · kleinDisc(a,b)⁵ = kleinC4(a,b)³ · Δ(E)`, the Klein–Fisher invariant identity) plus
  `Work.MotK.TwRuling.charTwo_ab_ne_of_j` (already proved, in `coeff_disjunction.lean`);
  `c4_cube_of_good` in turn needs `Work.MotK.TwRuling.ker_aeval_eq_span_kleinP` and
  `Work.MotK.TwRuling.j_eq_of_functionField_algEquiv`.
-/

namespace Work.MotK.TwRuling

open MvPolynomial

/-! ## The `j = 2` non-membership in the degree-six part of the twisted Pfaffian ideal

The `j = 3` case is `Work.MotK.TwRuling.sdCoeff6_notMem_twIdeal6`; the same evaluation argument
(using the lemmas `zpt`, `kleinTwP_zpt`, `aeval_kleinTwP_zpt` of that module) covers `j = 2`, whose
value at the point `z` is `a⁷αb¹⁰h⁵(57a⁵ − b⁵)` by `sdCoeff6_eval_family`. -/

/-- The value of `aeval (zpt L a b h α) (sdCoeff6 L a b h 2)`, read off
`Work.MotK.TwRuling.sdCoeff6_eval_family` (`zpt` is literally the same point). -/
theorem aeval_sdCoeff6_two (L : Type*) [Field L] (a b h α : L) (hab : a * b ≠ 0) (hh : h ≠ 0)
    (hα : α ^ 5 = -(1 / h ^ 2)) :
    MvPolynomial.aeval (zpt L a b h α) (sdCoeff6 L a b h 2)
      = a ^ 7 * α * b ^ 10 * h ^ 5 * (57 * a ^ 5 - b ^ 5) :=
  (Work.MotK.TwRuling.sdCoeff6_eval_family L a b h α hab hh hα).2.1

/-- `sdCoeff6 L a b h 2 ∉ twIdeal6 L a b h` whenever `57a⁵ ≠ b⁵` (the `j = 2` twin of
`Work.MotK.TwRuling.sdCoeff6_notMem_twIdeal6`). -/
theorem sdCoeff6_notMem_two' (L : Type*) [Field L] [IsAlgClosed L] (a b h : L)
    (hab : a * b ≠ 0) (hh : h ≠ 0) (h2 : 57 * a ^ 5 - b ^ 5 ≠ 0) :
    Work.MotK.TwRuling.sdCoeff6 L a b h 2 ∉
      Submodule.span L (Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = 4} =>
        Work.MotK.kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (fun i => MvPolynomial.X i) q.1 * MvPolynomial.monomial q.2.1 1)) := by
  intro hmem
  obtain ⟨ha, hb⟩ := mul_ne_zero_iff.mp hab
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (-(1 / h ^ 2)) (by norm_num : 0 < 5)
  have hpaff := Work.MotK.TwRuling.kleinTwP_zpt L a b h α hh hα
  have hα0 : α ≠ 0 := by
    intro h0
    rw [h0] at hα
    have h1 : -(1 / h ^ 2) = 0 := by
      rw [← hα]
      first | refl_ring1 | ring
    exact div_ne_zero one_ne_zero (pow_ne_zero 2 hh) (neg_eq_zero.mp h1)
  have hval : MvPolynomial.aeval (Work.MotK.TwRuling.zpt L a b h α)
      (Work.MotK.TwRuling.sdCoeff6 L a b h 2) ≠ 0 := by
    rw [aeval_sdCoeff6_two L a b h α hab hh hα]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) h2
    · exact pow_ne_zero 7 ha
    · exact hα0
    · exact pow_ne_zero 10 hb
    · exact pow_ne_zero 5 hh
  have hker : ∀ F ∈ Submodule.span L (Set.range (fun q : Fin 5 ×
        {m : Fin 5 →₀ ℕ // m.support.sum m = 4} =>
        Work.MotK.kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (fun i => MvPolynomial.X i) q.1 * MvPolynomial.monomial q.2.1 1)),
      MvPolynomial.aeval (Work.MotK.TwRuling.zpt L a b h α) F = 0 := by
    intro F hF
    have hle : Submodule.span L (Set.range (fun q : Fin 5 ×
          {m : Fin 5 →₀ ℕ // m.support.sum m = 4} =>
          Work.MotK.kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
            (fun i => MvPolynomial.X i) q.1 * MvPolynomial.monomial q.2.1 1))
        ≤ LinearMap.ker (MvPolynomial.aeval (Work.MotK.TwRuling.zpt L a b h α)).toLinearMap := by
      rw [Submodule.span_le]
      rintro G ⟨q, rfl⟩
      refine LinearMap.mem_ker.mpr ?_
      show MvPolynomial.aeval (Work.MotK.TwRuling.zpt L a b h α)
        (Work.MotK.kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (fun i => MvPolynomial.X i) q.1 * MvPolynomial.monomial q.2.1 1) = 0
      rw [map_mul, Work.MotK.TwRuling.aeval_kleinTwP_zpt L a b h α q.1, hpaff q.1, zero_mul]
    exact LinearMap.mem_ker.mp (hle hF)
  exact hval (hker _ hmem)

/-- **The ruling identity in `sdA`.**  For a good Klein datum `D` and `h ≠ 0`, the inverse cubic
map `R = kleinTwR` is projectively constant on the ruling line through the twisted Klein point
`sdY`, hence `R_i(sdW) = R_0(sdW) · (sdY) i`. -/
theorem sdW_kleinTwR_eq (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h : K) (hh : h ≠ 0) (i : Fin 5) :
    Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
        (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
        (algebraMap K (Work.MotK.TGen.sdA K D h) h)
        (Work.MotK.TGen.sdW K D h) i
      = Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
          (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
          (algebraMap K (Work.MotK.TGen.sdA K D h) h)
          (Work.MotK.TGen.sdW K D h) 0 * Work.MotK.TGen.sdY K D h i := by
  set W := Work.MotK.TGen.sdW K D h with hW
  set Y := Work.MotK.TGen.sdY K D h with hY
  have hcurve : ∀ k : Fin 5,
      Work.MotK.kleinTwP (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
        (algebraMap K (Work.MotK.TGen.sdA K D h) D.b) (algebraMap K (Work.MotK.TGen.sdA K D h) h)
        Y k = 0 := by
    intro k
    rw [hY]
    exact sdY_curve K D hD h hh k
  have hpt : Work.MotK.kleinTwRulePt (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
      (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
      (algebraMap K (Work.MotK.TGen.sdA K D h) h)
      Y 1 (RatFunc.X) = W := by
    rw [hW, hY]
    funext j
    simp only [Work.MotK.kleinTwRulePt, Work.MotK.TGen.sdW, Work.MotK.TGen.sdRuleA,
      Work.MotK.TGen.sdRuleB]
    first | refl_ring1 | ring
  have hY0 : Y 0 = 1 := by rw [hY]; exact sdY_zero K D hD h
  have hR1 := Work.MotK.TwRule.KleinTwRuleEval K (Work.MotK.TGen.sdA K D h) D.a D.b h 1
    (RatFunc.X) Y hcurve i 0
  rw [hpt] at hR1
  rw [hY0, mul_one] at hR1
  exact hR1

/-- The main step: if some coefficient form `sdCoeff6 a b h j` lies outside the degree-six part
of the twisted Pfaffian ideal, then the target holds. -/
theorem sdW_kleinTwR_ne_zero_of_notMem (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h : K) (hh : h ≠ 0)
    (habR : algebraMap K (Work.MotK.KbG K) D.a * algebraMap K (Work.MotK.KbG K) D.b ≠ 0)
    (hhR : algebraMap K (Work.MotK.KbG K) h ≠ 0) (j : ℕ)
    (hFnot : Work.MotK.TwRuling.sdCoeff6 (Work.MotK.KbG K) (algebraMap K (Work.MotK.KbG K) D.a)
        (algebraMap K (Work.MotK.KbG K) D.b) (algebraMap K (Work.MotK.KbG K) h) j ∉
      Work.MotK.TwRuling.twIdeal6 (Work.MotK.KbG K) (algebraMap K (Work.MotK.KbG K) D.a)
        (algebraMap K (Work.MotK.KbG K) D.b) (algebraMap K (Work.MotK.KbG K) h)) :
    Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
      (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
      (algebraMap K (Work.MotK.TGen.sdA K D h) h)
      (Work.MotK.TGen.sdW K D h) ≠ 0 := by
  classical
  obtain ⟨hκmem, hspans, hκ⟩ := Work.MotK.TwRuling.kappaP_kernel_hypotheses K D hD h hh
  have hne := Work.MotK.TwRuling.sexticTw_notMem_kernel (Work.MotK.KbG K)
    (D.E.baseChange (Work.MotK.KbG K)) _ _ _ habR hhR
    (Work.MotK.TwRuling.kappaP K D h) hκmem hspans hκ
    (Work.MotK.TwRuling.sdCoeff6 (Work.MotK.KbG K) (algebraMap K (Work.MotK.KbG K) D.a)
      (algebraMap K (Work.MotK.KbG K) D.b) (algebraMap K (Work.MotK.KbG K) h) j)
    (Work.MotK.TwRuling.sdCoeff6_mem _ _ _ _ j) hFnot
  have hne' : MvPolynomial.aeval (Work.MotK.twCoordG K D h)
      (Work.MotK.TwRuling.sdCoeff6 (Work.MotK.KbG K) (algebraMap K (Work.MotK.KbG K) D.a)
        (algebraMap K (Work.MotK.KbG K) D.b) (algebraMap K (Work.MotK.KbG K) h) j) ≠ 0 := by
    intro h0
    refine hne ?_
    rw [Work.MotK.TwRuling.aeval_kappaP K D hD h _
      (Work.MotK.TwRuling.sdCoeff6_mem _ _ _ _ j), h0, mul_zero]
  have hcoeff : (Work.MotK.TwRuling.rpEval K D h).coeff j ≠ 0 := by
    rw [Work.MotK.TwRuling.coeff_rpEval K D h j]
    exact hne'
  exact Work.MotK.TwRuling.sdW_ne_zero_of_coeff K D h hh j hcoeff

/-- `Work.MotK.TwRuling.coeff_disjunction` in characteristic `≠ 2`.  The same elimination of `b⁵`
gives `(600 : K) = 0`, so the characteristic is `2`, `3` or `5`; here the branch `2` is impossible,
and the branches `3`, `5` are handled exactly as in `Work.MotK.TwRuling.coeff_disjunction`.
Consequently this statement does **not** depend on `Work.MotK.TwRuling.good_ne_charTwo`. -/
theorem coeff_disjunction_charNeTwo (K : Type) [Field K] (h2K : (2 : K) ≠ 0)
    (D : Work.MotV.KleinData K) (hD : D.Good) :
    (27 * (algebraMap K (Work.MotK.KbG K) D.a) ^ 5
        - 11 * (algebraMap K (Work.MotK.KbG K) D.b) ^ 5 ≠ 0)
    ∨ (57 * (algebraMap K (Work.MotK.KbG K) D.a) ^ 5
        - (algebraMap K (Work.MotK.KbG K) D.b) ^ 5 ≠ 0) := by
  set A : Work.MotK.KbG K := algebraMap K (Work.MotK.KbG K) D.a with hA
  set B : Work.MotK.KbG K := algebraMap K (Work.MotK.KbG K) D.b with hB
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  -- `a` and `b` are nonzero
  have hDa : D.a ≠ 0 := (mul_ne_zero_iff.mp hD.ab_ne).1
  have hDb : D.b ≠ 0 := (mul_ne_zero_iff.mp hD.ab_ne).2
  have hA0 : A ≠ 0 := by
    rw [hA]
    exact fun h => hDa ((algebraMap K (Work.MotK.KbG K)).injective (by rw [h, map_zero]))
  have hB0 : B ≠ 0 := by
    rw [hB]
    exact fun h => hDb ((algebraMap K (Work.MotK.KbG K)).injective (by rw [h, map_zero]))
  -- eliminating `b⁵` gives `600 · a⁵ = 0`, hence `(600 : K) = 0`
  have h600R : (600 : Work.MotK.KbG K) = 0 := by
    have h : (600 : Work.MotK.KbG K) * A ^ 5 = 0 := by
      linear_combination (norm := first | refl_ring1 | ring1) -h1 + 11 * h2
    exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero 5 hA0)
  have h600K : (600 : K) = 0 := by
    have hm : algebraMap K (Work.MotK.KbG K) (600 : K) = (600 : Work.MotK.KbG K) :=
      map_ofNat (algebraMap K (Work.MotK.KbG K)) 600
    refine (algebraMap K (Work.MotK.KbG K)).injective ?_
    rw [hm, map_zero]
    exact h600R
  -- factor `600 = 2³ · 3 · 5²`
  have hfac : (2 : K) ^ 3 * (3 : K) * (5 : K) ^ 2 = 0 := by
    rw [← h600K]; norm_num
  rcases mul_eq_zero.mp hfac with h23 | h5sq
  · rcases mul_eq_zero.mp h23 with h2c | h3c
    · -- characteristic `2`: excluded by hypothesis
      exact h2K ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp h2c)
    · -- characteristic `3`: the second form becomes `-b⁵`
      have h3K : (3 : K) = 0 := h3c
      have h3R : (3 : Work.MotK.KbG K) = 0 := by
        have hm : algebraMap K (Work.MotK.KbG K) (3 : K) = (3 : Work.MotK.KbG K) :=
          map_ofNat (algebraMap K (Work.MotK.KbG K)) 3
        rw [← hm, h3K, map_zero]
      have hB5 : B ^ 5 = 0 := by
        have hneg : -(B ^ 5) = 0 := by
          linear_combination (norm := first | refl_ring1 | ring1) h2 - (19 * A ^ 5) * h3R
        exact neg_eq_zero.mp hneg
      exact hB0 ((pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0)).mp hB5)
  · -- characteristic `5`: both forms become `2a⁵ - b⁵`
    have h5K : (5 : K) = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h5sq
    have h5R : (5 : Work.MotK.KbG K) = 0 := by
      have hm : algebraMap K (Work.MotK.KbG K) (5 : K) = (5 : Work.MotK.KbG K) :=
        map_ofNat (algebraMap K (Work.MotK.KbG K)) 5
      rw [← hm, h5K, map_zero]
    have hne : D.b ^ 5 ≠ 2 * D.a ^ 5 :=
      Work.MotK.TwRuling.good_bFive_ne_charFive K D hD
        (Work.MotK.TwRuling.ringChar_eq_of_prime_cast_eq_zero (p := 5) (by norm_num) h5K)
    have hAB : 2 * A ^ 5 - B ^ 5 = 0 := by
      linear_combination (norm := first | refl_ring1 | ring1) h1 - (5 * A ^ 5 - 2 * B ^ 5) * h5R
    have heq : B ^ 5 = 2 * A ^ 5 := (sub_eq_zero.mp hAB).symm
    rw [hA, hB] at heq
    exact hne ((algebraMap K (Work.MotK.KbG K)).injective
      (by simpa only [map_pow, map_mul, map_ofNat] using heq))

/-- **The target.**  The inverse cubic map `kleinTwR` of the T-twisted Crauder–Katz link does not
vanish on the ruling point `sdW K D h` of the target ruling divisor. -/
theorem sdW_kleinTwR_ne_zero (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h : K) (hh : h ≠ 0) :
    Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
      (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
      (algebraMap K (Work.MotK.TGen.sdA K D h) h)
      (Work.MotK.TGen.sdW K D h) ≠ 0 := by
  have habR : algebraMap K (Work.MotK.KbG K) D.a * algebraMap K (Work.MotK.KbG K) D.b ≠ 0 := by
    rw [← map_mul]
    exact fun h0 => hD.ab_ne ((algebraMap K (Work.MotK.KbG K)).injective (by rw [h0, map_zero]))
  have hhR : algebraMap K (Work.MotK.KbG K) h ≠ 0 :=
    fun h0 => hh ((algebraMap K (Work.MotK.KbG K)).injective (by rw [h0, map_zero]))
  obtain h3 | h2 := Work.MotK.TwRuling.coeff_disjunction K D hD
  · exact Work.MotK.TwRuling.sdW_kleinTwR_ne_zero_of_notMem K D hD h hh habR hhR 3
      (Work.MotK.TwRuling.sdCoeff6_notMem_twIdeal6 (Work.MotK.KbG K) _ _ _ habR hhR h3)
  · exact Work.MotK.TwRuling.sdW_kleinTwR_ne_zero_of_notMem K D hD h hh habR hhR 2
      (sdCoeff6_notMem_two' (Work.MotK.KbG K) _ _ _ habR hhR h2)

/-- **The target in characteristic `≠ 2`** — the `sdCoeff6` route (this statement is *sorry-free*:
it does not use `Work.MotK.TwRuling.good_ne_charTwo`).

⚠ The name carries the suffix `_of_sdCoeff6` to avoid a clash with
`Work.MotK.TwRuling.sdW_kleinTwR_ne_zero_charNeTwo` of
`Submission/Work/MotK/TwRuling/sdW_kleinTwR_ne_zero_charNeTwo.lean` (the independent `sdCubic`
route to the same statement).  Either of the two may be used downstream. -/
theorem sdW_kleinTwR_ne_zero_charNeTwo_of_sdCoeff6 (K : Type) [Field K] (h2K : (2 : K) ≠ 0)
    (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0) :
    Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
      (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
      (algebraMap K (Work.MotK.TGen.sdA K D h) h)
      (Work.MotK.TGen.sdW K D h) ≠ 0 := by
  have habR : algebraMap K (Work.MotK.KbG K) D.a * algebraMap K (Work.MotK.KbG K) D.b ≠ 0 := by
    rw [← map_mul]
    exact fun h0 => hD.ab_ne ((algebraMap K (Work.MotK.KbG K)).injective (by rw [h0, map_zero]))
  have hhR : algebraMap K (Work.MotK.KbG K) h ≠ 0 :=
    fun h0 => hh ((algebraMap K (Work.MotK.KbG K)).injective (by rw [h0, map_zero]))
  obtain h3 | h2 := Work.MotK.TwRuling.coeff_disjunction_charNeTwo K h2K D hD
  · exact Work.MotK.TwRuling.sdW_kleinTwR_ne_zero_of_notMem K D hD h hh habR hhR 3
      (Work.MotK.TwRuling.sdCoeff6_notMem_twIdeal6 (Work.MotK.KbG K) _ _ _ habR hhR h3)
  · exact Work.MotK.TwRuling.sdW_kleinTwR_ne_zero_of_notMem K D hD h hh habR hhR 2
      (sdCoeff6_notMem_two' (Work.MotK.KbG K) _ _ _ habR hhR h2)

end Work.MotK.TwRuling
