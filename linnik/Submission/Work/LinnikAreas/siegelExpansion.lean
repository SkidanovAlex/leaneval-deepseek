import Mathlib
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.Setup
import Submission.Work.LinnikAreas.CIDefs
import Submission.Work.LinnikAreas.Kernel
import Submission.Work.LinnikAreas.Assembly
import Submission.Work.LinnikAreas.ZetaPrincipalDefs
import Submission.Work.LinnikAreas.ClassIdentity
import Submission.Work.LinnikAreas.ChiSumSubPrimitive
import Submission.Work.LinnikAreas.ClassSumOrthogonality
import Submission.Work.LinnikAreas.ClassLambdaSumDecomp
import Submission.Work.LinnikAreas.UniformPrimePowerTail
import Submission.Work.LinnikAreas.UniformNonCoprimeTail
import Submission.Work.LinnikAreas.ZeroSumBoxComparison
import Submission.Work.LinnikAreas.siegelZetaZeroFree
import Submission.Commons.NumberTheory.Linnik.tentMellin_bridge_scale
import Submission.Work.LinnikAreas.zetaTentExplicit
import Submission.Work.LinnikAreas.zetaBoxComparison

namespace Work.LinnikAreas

set_option maxHeartbeats 1600000

/-! ## 1. Elementary conversions -/

lemma primeClassSum_eq_primePS {q : ℕ} [NeZero q] (a : ℕ) :
    ((Siegel.primeClassSum q (11/2) (3/10) a : ℝ) : ℂ)
      = primePS (q := q) a (Siegel.classLimit q (11/2)) := by
  rw [Siegel.primeClassSum, primePS]
  have hflt : ((Finset.Icc 1 (Siegel.classLimit q (11/2))).filter
        (fun n : ℕ => n ≡ a [MOD q])).filter (fun n : ℕ => n.Prime)
      = (Finset.Icc 1 (Siegel.classLimit q (11/2))).filter
        (fun p : ℕ => p.Prime ∧ p ≡ a [MOD q]) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr (fun n _ => ?_)
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [hflt, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hp : n.Prime := (Finset.mem_filter.mp hn).2.1
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
  simp only [Siegel.tent, tentW]
  push_cast
  try ring

lemma allSum_eq_tentWeight_sum (q X : ℕ) :
    allSum q X = ∑ n ∈ Finset.Icc 1 X, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
      ((Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
        (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ) := by
  rw [allSum]

lemma ncsSumC_eq_ofReal (q X : ℕ) : ncsSumC q X = ((ncsSum q X : ℝ) : ℂ) := by
  rw [ncsSumC, ncsSum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  push_cast
  try ring

/-- The character sums (and the total von Mangoldt sum) do not change when the upper limit is
raised beyond `classLimit q L`: the extra terms carry a vanishing tent weight. -/
lemma chiSum_eq_of_le_classLimit {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) {q X : ℕ}
    (hq : 2 ≤ q) (hX : Siegel.classLimit q (11/2) ≤ X) :
    chiSum ψ q X = chiSum ψ q (Siegel.classLimit q (11/2)) := by
  have hq1 : (1:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hlog : 0 < Real.log (q:ℝ) := Real.log_pos hq1
  have hqr : 0 < (q:ℝ) ^ ((11:ℝ)/2) := Real.rpow_pos_of_pos (by positivity) _
  rw [chiSum, chiSum]
  symm
  have hsub : Finset.Icc 1 (Siegel.classLimit q (11/2)) ⊆ Finset.Icc 1 X := by
    intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, le_trans hn.2 hX⟩
  refine Finset.sum_subset hsub ?_
  intro n hn hnot
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hlt : Siegel.classLimit q (11/2) < n := by
    by_contra h
    exact hnot (Finset.mem_Icc.mpr ⟨hn1, not_lt.mp h⟩)
  have hqLn : (q:ℝ)^((11:ℝ)/2) < (n:ℝ) := by
    have h1 : (q:ℝ)^((11:ℝ)/2) < ((Siegel.classLimit q (11/2) : ℕ) : ℝ) + 1 := by
      rw [Siegel.classLimit]; exact Nat.lt_floor_add_one _
    have h2 : ((Siegel.classLimit q (11/2) : ℕ) : ℝ) + 1 ≤ (n:ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hlt : Siegel.classLimit q (11/2) + 1 ≤ n)
    linarith
  have hloglt : ((11:ℝ)/2) * Real.log (q:ℝ) < Real.log (n:ℝ) := by
    have h := Real.log_lt_log hqr hqLn
    rwa [Real.log_rpow (by positivity : (0:ℝ) < (q:ℝ))] at h
  have hx : (11:ℝ)/2 ≤ Real.log (n:ℝ)/Real.log (q:ℝ) := by
    rw [le_div_iff₀ hlog]; linarith
  have hzero : Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
      (Real.log (n:ℝ)/Real.log (q:ℝ)) = 0 :=
    (Commons.NumberTheory.Linnik.tentWeight_bounds (by norm_num) (by norm_num)).2.2.2 _ hx
  simp only [tentW]
  rw [hzero]
  simp

lemma allSum_eq_of_le_classLimit {q X : ℕ} (hq : 2 ≤ q)
    (hX : Siegel.classLimit q (11/2) ≤ X) :
    allSum q X = allSum q (Siegel.classLimit q (11/2)) := by
  have hq1 : (1:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hlog : 0 < Real.log (q:ℝ) := Real.log_pos hq1
  have hqr : 0 < (q:ℝ) ^ ((11:ℝ)/2) := Real.rpow_pos_of_pos (by positivity) _
  rw [allSum, allSum]
  symm
  have hsub : Finset.Icc 1 (Siegel.classLimit q (11/2)) ⊆ Finset.Icc 1 X := by
    intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, le_trans hn.2 hX⟩
  refine Finset.sum_subset hsub ?_
  intro n hn hnot
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hlt : Siegel.classLimit q (11/2) < n := by
    by_contra h
    exact hnot (Finset.mem_Icc.mpr ⟨hn1, not_lt.mp h⟩)
  have hqLn : (q:ℝ)^((11:ℝ)/2) < (n:ℝ) := by
    have h1 : (q:ℝ)^((11:ℝ)/2) < ((Siegel.classLimit q (11/2) : ℕ) : ℝ) + 1 := by
      rw [Siegel.classLimit]; exact Nat.lt_floor_add_one _
    have h2 : ((Siegel.classLimit q (11/2) : ℕ) : ℝ) + 1 ≤ (n:ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hlt : Siegel.classLimit q (11/2) + 1 ≤ n)
    linarith
  have hloglt : ((11:ℝ)/2) * Real.log (q:ℝ) < Real.log (n:ℝ) := by
    have h := Real.log_lt_log hqr hqLn
    rwa [Real.log_rpow (by positivity : (0:ℝ) < (q:ℝ))] at h
  have hx : (11:ℝ)/2 ≤ Real.log (n:ℝ)/Real.log (q:ℝ) := by
    rw [le_div_iff₀ hlog]; linarith
  have hzero : Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
      (Real.log (n:ℝ)/Real.log (q:ℝ)) = 0 :=
    (Commons.NumberTheory.Linnik.tentWeight_bounds (by norm_num) (by norm_num)).2.2.2 _ hx
  simp only [tentW]
  rw [hzero]
  simp


/-! ## 2. The three uniform inputs, as predicates -/

/-- The uniform per-character bridge: the conclusion of
`Commons.NumberTheory.Linnik.tentMellin_bridge_scale` at `L = 11/2`, `K = 3/10` and scale `q`,
in the form in which we consume it. -/
def BridgeUniform (Cb : ℝ) : Prop :=
  ∀ q : ℕ, 2 ≤ q → ∀ {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N),
    ψ ≠ 1 → ψ.IsPrimitive → N ≤ q → ∀ Z : ℂ,
      (Filter.Tendsto (fun ρ : ℝ => ∑ᶠ u : ℂ,
          (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction ψ)
            (Metric.closedBall 0 ρ)) u : ℤ) : ℂ) *
            (Complex.exp (-(((11/2 - 2 * (3/10) : ℝ) : ℂ) * ((1 - u) * ((Real.log (q:ℝ) : ℂ))))) *
              (((1 - Complex.exp (-(((3/10 : ℝ) : ℂ) * ((1 - u) * ((Real.log (q:ℝ) : ℂ)))))) /
                  ((1 - u) * ((Real.log (q:ℝ) : ℂ)))) ^ 2)))
        Filter.atTop (nhds Z)) →
      ∀ X : ℕ, (q : ℝ) ^ ((11:ℝ)/2) ≤ (X : ℝ) →
        ‖((Real.log (q:ℝ) : ℂ))⁻¹ * chiSum ψ q X + Z‖ ≤
          Cb * ((q : ℝ) ^ (-(49:ℝ)/10) +
              (Real.log (q:ℝ))⁻¹ * ((q : ℝ) ^ (-(147:ℝ)/20)) * (1 + Real.log (q:ℝ)))

/-- The `ζ`-bridge (the statement of `Work.LinnikAreas.zetaTentExplicit`). -/
def ZetaBridgeAt (CZ : ℝ) : Prop :=
  ∀ q : ℕ, 2 ≤ q → ∀ Z : ℂ,
    (Filter.Tendsto (fun ρ : ℝ => zetaBallSum q ρ) Filter.atTop (nhds Z)) →
    ∀ X : ℕ, (q : ℝ) ^ ((11:ℝ)/2) ≤ (X : ℝ) →
      ‖((Real.log (q : ℝ)) : ℂ)⁻¹ *
          (∑ n ∈ Finset.Icc 1 X, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
            ((Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
              (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)) + Z‖
        ≤ CZ * ((q : ℝ) ^ (-(49:ℝ)/10) +
            (Real.log (q : ℝ))⁻¹ * ((q : ℝ) ^ (-(147:ℝ)/20)) * (1 + Real.log (q : ℝ)))

/-- The `ζ`-box comparison (the statement of `Work.LinnikAreas.zetaBoxComparison`). -/
def ZetaBoxAt (CZ : ℝ) : Prop :=
  ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q], ∀ R : ℝ, 1 ≤ R →
    ∃ Z : ℂ,
      (Filter.Tendsto (fun ρ : ℝ => zetaBallSum q ρ) Filter.atTop (nhds Z)) ∧
      ‖Z + (3/10 : ℝ)^2 - Work.LinnikContract.boxSum q (11/2) (3/10) R
          (1 : DirichletCharacter ℂ q)‖
        ≤ farSumP q R + CZ * (q : ℝ) ^ (-(49:ℝ)/10)

/-! ## 3. The per-character and principal bounds -/

/-- `classSum` is the cast of `primePS` plus the cast of `classPP`. -/
lemma classSum_eq_primePS_add_classPP {q : ℕ} [NeZero q] (a X : ℕ) :
    classSum (q := q) a X = primePS (q := q) a X + ((classPP (q := q) a X : ℝ) : ℂ) := by
  show (∑ n ∈ Finset.Ioc 0 X, ((ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q) n : ℝ) : ℂ) *
      (((tentW (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ) / (n : ℂ)))
    = primePS (q := q) a X + ((classPP (q := q) a X : ℝ) : ℂ)
  rw [ClassLambdaSumDecomp (q := q) a X, ofReal_primeSum_eq_primePS, ofReal_classPP_eq]

lemma classSum_classLimit_eq {q : ℕ} [NeZero q] (a : ℕ) :
    classSum (q := q) a (Siegel.classLimit q (11/2))
      = primePS (q := q) a (Siegel.classLimit q (11/2))
        + ((classPP (q := q) a (Siegel.classLimit q (11/2)) : ℝ) : ℂ) :=
  classSum_eq_primePS_add_classPP a _

/-- The principal character is `1` on the unit `a mod q`. -/
lemma one_apply_of_coprime {q : ℕ} [NeZero q] {a : ℕ} (ha : a.Coprime q) :
    (1 : DirichletCharacter ℂ q) (a : ZMod q) = 1 := by
  rw [one_apply_eq_indicator, if_pos (isUnit_of_coprime ha)]

/-- The uniform bridge of `tentMellin_bridge_scale` implies the per-character box expansion. -/
lemma chiSum_box_bound {q : ℕ} [NeZero q] {Cb : ℝ} (hbr : BridgeUniform Cb)
    (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {R : ℝ} (hR : 1 ≤ R) :
    ‖((Real.log (q:ℝ) : ℂ))⁻¹ * chiSum χ q (Siegel.classLimit q (11/2))
        + Work.LinnikContract.boxSum q (11/2) (3/10) R χ‖
      ≤ Cb * ((q : ℝ) ^ (-(49:ℝ)/10) +
              (Real.log (q:ℝ))⁻¹ * ((q : ℝ) ^ (-(147:ℝ)/20)) * (1 + Real.log (q:ℝ)))
        + (Real.log (q:ℝ))⁻¹ * ncsSum q (Siegel.classLimit q (11/2))
        + farSum q (11/2) (3/10) R χ := by
  haveI : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  have hq1 : (1:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hlogpos : 0 < Real.log (q:ℝ) := Real.log_pos hq1
  have hχne : χ.primitiveCharacter ≠ 1 := Siegel.primitive_ne_one hχ
  have hprim : χ.primitiveCharacter.IsPrimitive := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hNq : χ.conductor ≤ q := Nat.le_of_dvd (NeZero.pos q) (DirichletCharacter.conductor_dvd_level χ)
  obtain ⟨Z, hZtend, hZbox⟩ := ZeroSumBoxComparison χ hχ (R := R) (by linarith)
  set X' : ℕ := Siegel.classLimit q (11/2) + 1 with hX'def
  have hX'cast : (X' : ℝ) = ((Siegel.classLimit q (11/2) : ℕ) : ℝ) + 1 := by
    rw [hX'def]; push_cast; ring
  have hX'ge : (q : ℝ) ^ ((11:ℝ)/2) ≤ (X' : ℝ) := by
    have h := Nat.lt_floor_add_one ((q:ℝ)^((11:ℝ)/2))
    have h2 : ((Siegel.classLimit q (11/2) : ℕ) : ℝ) = ((⌊(q:ℝ)^((11:ℝ)/2)⌋₊ : ℕ) : ℝ) := rfl
    rw [← h2] at h
    rw [hX'cast]; linarith
  have hZtend' : Filter.Tendsto (fun ρ : ℝ => ∑ᶠ u : ℂ,
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 ρ)) u : ℤ) : ℂ) *
        (Complex.exp (-(((11/2 - 2 * (3/10) : ℝ) : ℂ) * ((1 - u) * ((Real.log (q:ℝ) : ℂ))))) *
          (((1 - Complex.exp (-(((3/10 : ℝ) : ℂ) * ((1 - u) * ((Real.log (q:ℝ) : ℂ)))))) /
              ((1 - u) * ((Real.log (q:ℝ) : ℂ)))) ^ 2)))
      Filter.atTop (nhds Z) := by
    refine hZtend.congr' (Filter.Eventually.of_forall (fun ρ => ?_))
    refine finsum_congr (fun u => ?_)
    rw [Hk_eq_exp_form u q]
  have hb := hbr q hq χ.primitiveCharacter hχne hprim hNq Z hZtend' X' hX'ge
  have hinv : chiSum χ.primitiveCharacter q X'
      = chiSum χ.primitiveCharacter q (Siegel.classLimit q (11/2)) := by
    refine chiSum_eq_of_le_classLimit χ.primitiveCharacter hq ?_
    rw [hX'def]; exact le_add_right le_rfl
  rw [hinv] at hb
  have hdel : ‖((Real.log (q:ℝ) : ℂ))⁻¹ * (chiSum χ q (Siegel.classLimit q (11/2))
        - chiSum χ.primitiveCharacter q (Siegel.classLimit q (11/2)))‖
      ≤ ((Real.log (q:ℝ))⁻¹) * ncsSum q (Siegel.classLimit q (11/2)) := by
    rw [norm_mul, norm_inv]
    have h := ChiSumSubPrimitive χ hχ (Siegel.classLimit q (11/2))
    rw [norm_ofReal_of_nonneg hlogpos.le]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  calc ‖((Real.log (q:ℝ) : ℂ))⁻¹ * chiSum χ q (Siegel.classLimit q (11/2))
        + Work.LinnikContract.boxSum q (11/2) (3/10) R χ‖
      = ‖(((Real.log (q:ℝ) : ℂ))⁻¹ * (chiSum χ q (Siegel.classLimit q (11/2))
            - chiSum χ.primitiveCharacter q (Siegel.classLimit q (11/2))))
          + (((Real.log (q:ℝ) : ℂ))⁻¹ * chiSum χ.primitiveCharacter q (Siegel.classLimit q (11/2)) + Z)
          + (Work.LinnikContract.boxSum q (11/2) (3/10) R χ - Z)‖ := by ring_nf
    _ ≤ Cb * ((q : ℝ) ^ (-(49:ℝ)/10) +
              (Real.log (q:ℝ))⁻¹ * ((q : ℝ) ^ (-(147:ℝ)/20)) * (1 + Real.log (q:ℝ)))
        + (Real.log (q:ℝ))⁻¹ * ncsSum q (Siegel.classLimit q (11/2))
        + farSum q (11/2) (3/10) R χ := by
        have hC : ‖Work.LinnikContract.boxSum q (11/2) (3/10) R χ - Z‖
            ≤ farSum q (11/2) (3/10) R χ := by
          rw [norm_sub_rev]; exact hZbox
        have hAB : ‖((Real.log (q:ℝ) : ℂ))⁻¹ * (chiSum χ q (Siegel.classLimit q (11/2))
              - chiSum χ.primitiveCharacter q (Siegel.classLimit q (11/2)))
            + (((Real.log (q:ℝ) : ℂ))⁻¹ * chiSum χ.primitiveCharacter q (Siegel.classLimit q (11/2)) + Z)‖
            ≤ Cb * ((q : ℝ) ^ (-(49:ℝ)/10) +
              (Real.log (q:ℝ))⁻¹ * ((q : ℝ) ^ (-(147:ℝ)/20)) * (1 + Real.log (q:ℝ)))
              + (Real.log (q:ℝ))⁻¹ * ncsSum q (Siegel.classLimit q (11/2)) := by
          refine le_trans (norm_add_le _ _) ?_
          linarith [hdel, hb]
        refine le_trans (norm_add_le _ _) ?_
        linarith [hAB, hC]

/-- The `ζ`-part of the box-restricted expansion. -/
lemma principal_box_bound {q : ℕ} [NeZero q] {CZ1 CZ2 : ℝ} (hZ1 : ZetaBridgeAt CZ1)
    (hZ2 : ZetaBoxAt CZ2) (hq : 2 ≤ q) {R : ℝ} (hR : 1 ≤ R) :
    ‖((Real.log (q:ℝ) : ℂ))⁻¹ * chiSum (1 : DirichletCharacter ℂ q) q (Siegel.classLimit q (11/2))
        - (3/10 : ℝ)^2 + Work.LinnikContract.boxSum q (11/2) (3/10) R
            (1 : DirichletCharacter ℂ q)‖
      ≤ CZ1 * ((q : ℝ) ^ (-(49:ℝ)/10) +
              (Real.log (q:ℝ))⁻¹ * ((q : ℝ) ^ (-(147:ℝ)/20)) * (1 + Real.log (q:ℝ)))
        + CZ2 * (q:ℝ)^(-(49:ℝ)/10)
        + (Real.log (q:ℝ))⁻¹ * ncsSum q (Siegel.classLimit q (11/2))
        + farSumP q R := by
  obtain ⟨Z, hZtend, hZbox⟩ := hZ2 q hq R hR
  set X' : ℕ := Siegel.classLimit q (11/2) + 1 with hX'def
  have hX'cast : (X' : ℝ) = ((Siegel.classLimit q (11/2) : ℕ) : ℝ) + 1 := by
    rw [hX'def]; push_cast; ring
  have hX'ge : (q : ℝ) ^ ((11:ℝ)/2) ≤ (X' : ℝ) := by
    have h := Nat.lt_floor_add_one ((q:ℝ)^((11:ℝ)/2))
    have h2 : ((Siegel.classLimit q (11/2) : ℕ) : ℝ) = ((⌊(q:ℝ)^((11:ℝ)/2)⌋₊ : ℕ) : ℝ) := rfl
    rw [← h2] at h
    rw [hX'cast]; linarith
  have hb := hZ1 q hq Z hZtend X' hX'ge
  have hsumPB : (∑ n ∈ Finset.Icc 1 X', ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
        ((Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
          (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)) = allSum q X' := rfl
  rw [hsumPB] at hb
  have halleq : allSum q X' = allSum q (Siegel.classLimit q (11/2)) := by
    refine allSum_eq_of_le_classLimit hq ?_
    rw [hX'def]; exact le_add_right le_rfl
  rw [halleq] at hb
  have hchi1 := chiSum_one_eq (q := q) (Siegel.classLimit q (11/2))
  have hncscast := ncsSumC_eq_ofReal q (Siegel.classLimit q (11/2))
  have hncsnn : 0 ≤ ncsSum q (Siegel.classLimit q (11/2)) :=
    Finset.sum_nonneg (fun n hn => by
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
      have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
      have hwt : 0 ≤ tentW (Real.log (n:ℝ) / Real.log (q:ℝ)) :=
        (Commons.NumberTheory.Linnik.tentWeight_bounds (L := 11/2) (K := 3/10)
          (by norm_num) (by norm_num)).1 _
      have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      positivity)
  set Lc : ℂ := ((Real.log (q:ℝ) : ℝ) : ℂ) with hLcdef
  have hlogpos : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hLcne : Lc ≠ 0 := by
    rw [hLcdef]; exact Complex.ofReal_ne_zero.mpr (ne_of_gt hlogpos)
  have hnormLcinv : ‖Lc⁻¹‖ = (Real.log (q:ℝ))⁻¹ := by
    rw [norm_inv, hLcdef, Complex.norm_of_nonneg hlogpos.le]
  have hnormncs : ‖((ncsSum q (Siegel.classLimit q (11/2)) : ℝ) : ℂ)‖
      = ncsSum q (Siegel.classLimit q (11/2)) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hncsnn]
  have hterm1 : ‖Lc⁻¹ * allSum q (Siegel.classLimit q (11/2)) + Z‖ ≤ CZ1 * ((q : ℝ) ^ (-(49:ℝ)/10) +
              (Real.log (q:ℝ))⁻¹ * ((q : ℝ) ^ (-(147:ℝ)/20)) * (1 + Real.log (q:ℝ))) := by
    simpa only [hLcdef] using hb
  have hterm2 : ‖Lc⁻¹ * ncsSumC q (Siegel.classLimit q (11/2))‖
      ≤ (Real.log (q:ℝ))⁻¹ * ncsSum q (Siegel.classLimit q (11/2)) := by
    rw [hncscast, norm_mul, hnormLcinv, hnormncs]
  have hterm3 : ‖Work.LinnikContract.boxSum q (11/2) (3/10) R (1 : DirichletCharacter ℂ q) - Z
        - (3/10 : ℝ)^2‖ ≤ farSumP q R + CZ2 * (q:ℝ)^(-(49:ℝ)/10) := by
    have hEq : Work.LinnikContract.boxSum q (11/2) (3/10) R (1 : DirichletCharacter ℂ q) - Z
        - (3/10 : ℝ)^2
        = -(Z + (3/10 : ℝ)^2 - Work.LinnikContract.boxSum q (11/2) (3/10) R
            (1 : DirichletCharacter ℂ q)) := by ring
    rw [hEq, norm_neg]
    exact hZbox
  calc ‖Lc⁻¹ * chiSum (1 : DirichletCharacter ℂ q) q (Siegel.classLimit q (11/2))
        - (3/10 : ℝ)^2 + Work.LinnikContract.boxSum q (11/2) (3/10) R (1 : DirichletCharacter ℂ q)‖
      = ‖((Lc⁻¹ * allSum q (Siegel.classLimit q (11/2)) + Z) - Lc⁻¹ * ncsSumC q (Siegel.classLimit q (11/2))
          + (Work.LinnikContract.boxSum q (11/2) (3/10) R (1 : DirichletCharacter ℂ q) - Z - (3/10 : ℝ)^2))‖ := by
        rw [hchi1]; ring_nf
    _ ≤ _ := by
        have hAB : ‖(Lc⁻¹ * allSum q (Siegel.classLimit q (11/2)) + Z)
            - Lc⁻¹ * ncsSumC q (Siegel.classLimit q (11/2))‖
            ≤ CZ1 * ((q : ℝ) ^ (-(49:ℝ)/10) +
              (Real.log (q:ℝ))⁻¹ * ((q : ℝ) ^ (-(147:ℝ)/20)) * (1 + Real.log (q:ℝ)))
              + (Real.log (q:ℝ))⁻¹ * ncsSum q (Siegel.classLimit q (11/2)) := by
          refine le_trans (norm_sub_le _ _) ?_
          linarith [hterm1, hterm2]
        refine le_trans (norm_add_le _ _) ?_
        linarith [hAB, hterm3]

/-! ## 4. Numerical thresholds -/

lemma eventually_const_log_pow_mul_rpow {a b : ℝ} (hab : a < b) (k : ℕ) (C : ℝ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      C * (Real.log (q:ℝ))^k * (q:ℝ)^a ≤ (q:ℝ)^b := by
  by_cases hC : C ≤ 0
  · refine ⟨2, fun q hq => ?_⟩
    have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
    have hlog : 0 ≤ Real.log (q:ℝ) := Real.log_nonneg hq1
    have hqpos : 0 < (q:ℝ) := by linarith
    have h1 : C * (Real.log (q:ℝ))^k ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hC (pow_nonneg hlog k)
    have h2 : C * (Real.log (q:ℝ))^k * (q:ℝ)^a ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h1 (Real.rpow_nonneg hqpos.le a)
    exact le_trans h2 (le_of_lt (Real.rpow_pos_of_pos hqpos b))
  · push_neg at hC
    set ε : ℝ := (b - a) / (2 * ((k:ℝ) + 1)) with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; positivity
    have hkε : (k:ℝ) * ε ≤ (b - a) / 2 := by
      rw [hεdef, mul_comm (k:ℝ), div_mul_eq_mul_div]
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
      nlinarith [show (0:ℝ) < b - a by linarith]
    obtain ⟨q₀, hq₀⟩ : ∃ q₀ : ℕ,
        (C * ε ^ (-(k:ℝ))) ^ (2 / (b - a)) ≤ (q₀ : ℝ) := exists_nat_ge _
    refine ⟨max q₀ 2, fun q hq => ?_⟩
    have hqq₀ : q₀ ≤ q := le_trans (le_max_left _ _) hq
    have hqpos : 0 < (q:ℝ) := by
      have : 0 < q := by omega
      exact_mod_cast this
    have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
    have hlog : 0 ≤ Real.log (q:ℝ) := Real.log_nonneg hq1
    have hlogbound : Real.log (q:ℝ) ≤ (q:ℝ)^ε / ε :=
      Real.log_natCast_le_rpow_div q hεpos
    have hpow : (Real.log (q:ℝ))^k ≤ ((q:ℝ)^ε / ε)^k := pow_le_pow_left₀ hlog hlogbound k
    have hpow' : ((q:ℝ)^ε / ε)^k = (q:ℝ)^((k:ℝ)*ε) / ε^k := by
      rw [div_pow, div_eq_mul_inv, div_eq_mul_inv]
      congr 1
      rw [← Real.rpow_natCast ((q:ℝ)^ε) k, (Real.rpow_mul hqpos.le ε (k:ℝ)).symm]
      congr 1
      ring
    have h1 : C * (Real.log (q:ℝ))^k * (q:ℝ)^a
        ≤ C * ((q:ℝ)^((k:ℝ)*ε) / ε^k) * (q:ℝ)^a := by
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hqpos.le a)
      exact mul_le_mul_of_nonneg_left (le_trans hpow (le_of_eq hpow')) hC.le
    have h2 : C * ((q:ℝ)^((k:ℝ)*ε) / ε^k) * (q:ℝ)^a
        = (C * ε ^ (-(k:ℝ))) * (q:ℝ)^((k:ℝ)*ε + a) := by
      rw [← Real.rpow_natCast ε k, Real.rpow_neg hεpos.le, Real.rpow_add hqpos]
      field_simp
    have hexp : (k:ℝ)*ε + a ≤ (a + b) / 2 := by linarith
    have h3 : (q:ℝ)^((k:ℝ)*ε + a) ≤ (q:ℝ)^((a+b)/2) :=
      Real.rpow_le_rpow_of_exponent_le hq1 hexp
    have h4 : C * ε ^ (-(k:ℝ)) ≤ (q:ℝ)^((b-a)/2) := by
      have hbase : 0 ≤ C * ε ^ (-(k:ℝ)) := by positivity
      have hc : (0:ℝ) ≤ (b-a)/2 := by linarith
      have h := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (C * ε ^ (-(k:ℝ))) ^ (2 / (b - a)))
        hq₀ hc
      have hmul : ((C * ε ^ (-(k:ℝ))) ^ (2 / (b - a))) ^ ((b - a)/2) = C * ε ^ (-(k:ℝ)) := by
        rw [← Real.rpow_mul hbase]
        have he : (2 / (b - a)) * ((b - a)/2) = 1 := by
          rw [div_mul_div_comm]
          rw [show (b - a) * 2 = 2 * (b - a) by ring,
            div_self (ne_of_gt (by linarith : (0:ℝ) < 2 * (b - a)))]
        rw [he, Real.rpow_one]
      have hq0le : (q₀:ℝ) ≤ (q:ℝ) := by exact_mod_cast hqq₀
      have h2' : (q₀:ℝ)^((b-a)/2) ≤ (q:ℝ)^((b-a)/2) := Real.rpow_le_rpow (by positivity) hq0le hc
      rw [hmul] at h
      linarith
    calc C * (Real.log (q:ℝ))^k * (q:ℝ)^a
        ≤ (C * ε ^ (-(k:ℝ))) * (q:ℝ)^((k:ℝ)*ε + a) := le_trans h1 (le_of_eq h2)
      _ ≤ (q:ℝ)^((b-a)/2) * (q:ℝ)^((a+b)/2) :=
          mul_le_mul h4 h3 (Real.rpow_nonneg hqpos.le _) (Real.rpow_nonneg hqpos.le _)
      _ = (q:ℝ)^b := by
          rw [← Real.rpow_add hqpos]
          congr 1
          ring

lemma exists_const_log_pow_le {a : ℝ} (ha : a < -2) (k : ℕ) (C : ℝ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      C * (Real.log (q:ℝ))^k * (q:ℝ)^a ≤ (1/24) * (q:ℝ)^(-(2:ℝ)) := by
  obtain ⟨q₀, hq₀⟩ := eventually_const_log_pow_mul_rpow ha k (24 * C)
  refine ⟨max q₀ 2, fun q hq => ?_⟩
  have h := hq₀ q (le_trans (le_max_left _ _) hq)
  have h' : (1/24) * (24 * C * (Real.log (q:ℝ))^k * (q:ℝ)^a) ≤ (1/24) * (q:ℝ)^(-(2:ℝ)) :=
    mul_le_mul_of_nonneg_left h (by norm_num)
  calc C * (Real.log (q:ℝ))^k * (q:ℝ)^a
      = (1/24) * (24 * C * (Real.log (q:ℝ))^k * (q:ℝ)^a) := by ring
    _ ≤ (1/24) * (q:ℝ)^(-(2:ℝ)) := h'

lemma log_inv_le_one {q : ℕ} (hq : 3 ≤ q) : (Real.log (q:ℝ))⁻¹ ≤ 1 := by
  have h3 : (1:ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 3)).mpr Real.exp_one_lt_three
  have hlog1 : (1:ℝ) ≤ Real.log (q:ℝ) := by
    have hle : Real.log 3 ≤ Real.log (q:ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hq)
    linarith
  have hpos : 0 < Real.log (q:ℝ) := by linarith
  rw [inv_le_iff_one_le_mul₀ hpos]
  linarith

lemma log_one_le {q : ℕ} (hq : 3 ≤ q) : (1:ℝ) ≤ Real.log (q:ℝ) := by
  have h3 : (1:ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 3)).mpr Real.exp_one_lt_three
  have hle : Real.log 3 ≤ Real.log (q:ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hq)
  linarith

/-- The error shape of the per-character bridge. -/
noncomputable def Err (q : ℕ) : ℝ :=
  (q:ℝ)^(-(49:ℝ)/10) + (Real.log (q:ℝ))⁻¹ * (q:ℝ)^(-(147:ℝ)/20) * (1 + Real.log (q:ℝ))

lemma Err_nonneg {q : ℕ} (hq : 3 ≤ q) : 0 ≤ Err q := by
  have hqpos : 0 < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlogpos : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have h1 : 0 < (q:ℝ)^(-(49:ℝ)/10) := Real.rpow_pos_of_pos hqpos _
  have h2 : 0 < (q:ℝ)^(-(147:ℝ)/20) := Real.rpow_pos_of_pos hqpos _
  have h3 : 0 ≤ (Real.log (q:ℝ))⁻¹ := le_of_lt (inv_pos.mpr hlogpos)
  have h4 : 0 ≤ 1 + Real.log (q:ℝ) := by linarith [log_one_le hq]
  rw [Err]
  positivity

lemma threshold_bridge (C : ℝ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → C * Err q ≤ (1/8) * (q:ℝ)^(-(2:ℝ)) := by
  by_cases hC : C ≤ 0
  · refine ⟨3, fun q hq => ?_⟩
    have hqpos : 0 < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hErrn : 0 ≤ Err q := Err_nonneg (q := q) (by omega)
    have h2 : (0:ℝ) < (1/8) * (q:ℝ)^(-(2:ℝ)) := by
      have := Real.rpow_pos_of_pos hqpos (-(2:ℝ)); positivity
    nlinarith [hErrn, hC, h2]
  push_neg at hC
  obtain ⟨q1, h1⟩ := exists_const_log_pow_le (a := -(49:ℝ)/10) (by norm_num) 0 C
  obtain ⟨q2, h2⟩ := exists_const_log_pow_le (a := -(147:ℝ)/20) (by norm_num) 0 C
  obtain ⟨q3, h3⟩ := exists_const_log_pow_le (a := -(147:ℝ)/20) (by norm_num) 1 C
  refine ⟨max (max q1 q2) (max q3 3), fun q hq => ?_⟩
  have H1 : q1 ≤ q := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hq)
  have H2 : q2 ≤ q := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hq)
  have H3 : q3 ≤ q := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hq)
  have Hq : 3 ≤ q := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hq)
  have hqpos : 0 < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hlogpos : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hloginv : (Real.log (q:ℝ))⁻¹ ≤ 1 := log_inv_le_one Hq
  have hlog1 : (1:ℝ) ≤ Real.log (q:ℝ) := log_one_le Hq
  have hq49 : (q:ℝ)^(-(49:ℝ)/10) ≤ (q:ℝ)^(-(2:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
  have hq20 : (q:ℝ)^(-(147:ℝ)/20) ≤ (q:ℝ)^(-(2:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
  have hrpow2 : (0:ℝ) < (q:ℝ)^(-(2:ℝ)) := Real.rpow_pos_of_pos hqpos _
  have hlogmul : (Real.log (q:ℝ))⁻¹ * (q:ℝ)^(-(147:ℝ)/20) * (1 + Real.log (q:ℝ))
      ≤ (q:ℝ)^(-(147:ℝ)/20) + (q:ℝ)^(-(147:ℝ)/20) * Real.log (q:ℝ) := by
    have h2' : 0 < (q:ℝ)^(-(147:ℝ)/20) := Real.rpow_pos_of_pos hqpos _
    have h1' : (Real.log (q:ℝ))⁻¹ * (q:ℝ)^(-(147:ℝ)/20) ≤ (q:ℝ)^(-(147:ℝ)/20) := by
      have := mul_le_mul_of_nonneg_right hloginv (le_of_lt h2')
      rwa [one_mul] at this
    have h3' : 0 ≤ 1 + Real.log (q:ℝ) := by linarith [hlog1]
    calc (Real.log (q:ℝ))⁻¹ * (q:ℝ)^(-(147:ℝ)/20) * (1 + Real.log (q:ℝ))
        ≤ (q:ℝ)^(-(147:ℝ)/20) * (1 + Real.log (q:ℝ)) :=
          mul_le_mul_of_nonneg_right h1' h3'
      _ = (q:ℝ)^(-(147:ℝ)/20) + (q:ℝ)^(-(147:ℝ)/20) * Real.log (q:ℝ) := by ring
  have hsum : C * Err q
      ≤ C * ((q:ℝ)^(-(49:ℝ)/10) + (q:ℝ)^(-(147:ℝ)/20) + (q:ℝ)^(-(147:ℝ)/20) * Real.log (q:ℝ)) := by
    rw [Err]
    refine mul_le_mul_of_nonneg_left ?_ hC.le
    linarith [hlogmul]
  have hA := h1 q H1
  have hB := h2 q H2
  have hC' := h3 q H3
  simp only [pow_zero, mul_one] at hA hB
  simp only [pow_one] at hC'
  linarith [hA, hB, hC', hsum, hq49, hq20, hrpow2]

lemma threshold_zeta1 (C : ℝ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → C * Err q ≤ (1/8) * (q:ℝ)^(-(2:ℝ)) :=
  threshold_bridge C

lemma threshold_zeta2 (C : ℝ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → C * (q:ℝ)^(-(49:ℝ)/10) ≤ (1/8) * (q:ℝ)^(-(2:ℝ)) := by
  by_cases hC : C ≤ 0
  · refine ⟨3, fun q hq => ?_⟩
    have hqpos : 0 < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
    have h2 : (0:ℝ) < (1/8) * (q:ℝ)^(-(2:ℝ)) := by
      have := Real.rpow_pos_of_pos hqpos (-(2:ℝ)); positivity
    have h3 : 0 < (q:ℝ)^(-(49:ℝ)/10) := Real.rpow_pos_of_pos hqpos _
    nlinarith [hC, h2, h3]
  push_neg at hC
  obtain ⟨q1, h1⟩ := exists_const_log_pow_le (a := -(49:ℝ)/10) (by norm_num) 0 C
  refine ⟨max q1 3, fun q hq => ?_⟩
  have H1 : q1 ≤ q := le_trans (le_max_left _ _) hq
  have Hq : 3 ≤ q := le_trans (le_max_right _ _) hq
  have hqpos : 0 < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hq49 : (q:ℝ)^(-(49:ℝ)/10) ≤ (q:ℝ)^(-(2:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
  have hrpow2 : (0:ℝ) < (q:ℝ)^(-(2:ℝ)) := Real.rpow_pos_of_pos hqpos _
  have hA := h1 q H1
  simp only [pow_zero, mul_one] at hA
  linarith [hA, hq49, hrpow2]

lemma threshold_ncs (C : ℝ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      (Real.log (q:ℝ))⁻¹ * (C * (Real.log (q:ℝ))^2 * (q:ℝ)^(-(49:ℝ)/10))
        ≤ (1/8) * (q:ℝ)^(-(2:ℝ)) := by
  by_cases hC : C ≤ 0
  · refine ⟨3, fun q hq => ?_⟩
    have hqpos : 0 < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hlogpos : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
    have h2 : (0:ℝ) < (1/8) * (q:ℝ)^(-(2:ℝ)) := by
      have := Real.rpow_pos_of_pos hqpos (-(2:ℝ)); positivity
    have h4 : 0 < (q:ℝ)^(-(49:ℝ)/10) := Real.rpow_pos_of_pos hqpos _
    have h5 : 0 ≤ (Real.log (q:ℝ))⁻¹ := le_of_lt (inv_pos.mpr hlogpos)
    have h6 : C * (Real.log (q:ℝ))^2 * (q:ℝ)^(-(49:ℝ)/10) ≤ 0 := by
      have : (Real.log (q:ℝ))^2 * (q:ℝ)^(-(49:ℝ)/10) > 0 := by positivity
      nlinarith [hC, this]
    have := mul_nonpos_of_nonneg_of_nonpos h5 h6
    linarith
  push_neg at hC
  obtain ⟨q1, h1⟩ := exists_const_log_pow_le (a := -(49:ℝ)/10) (by norm_num) 1 C
  refine ⟨max q1 3, fun q hq => ?_⟩
  have H1 : q1 ≤ q := le_trans (le_max_left _ _) hq
  have Hq : 3 ≤ q := le_trans (le_max_right _ _) hq
  have hqpos : 0 < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlogpos : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hlog1 : (1:ℝ) ≤ Real.log (q:ℝ) := log_one_le Hq
  have hA := h1 q H1
  simp only [pow_one] at hA
  have hEq : (Real.log (q:ℝ))⁻¹ * (C * (Real.log (q:ℝ))^2 * (q:ℝ)^(-(49:ℝ)/10))
      = C * (Real.log (q:ℝ)) * (q:ℝ)^(-(49:ℝ)/10) := by
    have hsq : (Real.log (q:ℝ))^2 = Real.log (q:ℝ) * Real.log (q:ℝ) := by ring
    rw [hsq]
    field_simp
  rw [hEq]
  have hrpow2 : (0:ℝ) < (q:ℝ)^(-(2:ℝ)) := Real.rpow_pos_of_pos hqpos _
  linarith [hA, hrpow2, hlog1]

lemma threshold_pp (C : ℝ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      (Real.log (q:ℝ))⁻¹ * (C * (q:ℝ)^(-(49:ℝ)/20)) ≤ (1/8) * (q:ℝ)^(-(2:ℝ)) := by
  by_cases hC : C ≤ 0
  · refine ⟨3, fun q hq => ?_⟩
    have hqpos : 0 < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hlogpos : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
    have h2 : (0:ℝ) < (1/8) * (q:ℝ)^(-(2:ℝ)) := by
      have := Real.rpow_pos_of_pos hqpos (-(2:ℝ)); positivity
    have h4 : 0 < (q:ℝ)^(-(49:ℝ)/20) := Real.rpow_pos_of_pos hqpos _
    have h5 : 0 ≤ (Real.log (q:ℝ))⁻¹ := le_of_lt (inv_pos.mpr hlogpos)
    have h6 : C * (q:ℝ)^(-(49:ℝ)/20) ≤ 0 := by nlinarith [hC, h4]
    have := mul_nonpos_of_nonneg_of_nonpos h5 h6
    linarith
  push_neg at hC
  obtain ⟨q1, h1⟩ := exists_const_log_pow_le (a := -(49:ℝ)/20) (by norm_num) 0 C
  refine ⟨max q1 3, fun q hq => ?_⟩
  have H1 : q1 ≤ q := le_trans (le_max_left _ _) hq
  have Hq : 3 ≤ q := le_trans (le_max_right _ _) hq
  have hqpos : 0 < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hloginv : (Real.log (q:ℝ))⁻¹ ≤ 1 := log_inv_le_one Hq
  have hA := h1 q H1
  simp only [pow_zero, mul_one] at hA
  have hle : (Real.log (q:ℝ))⁻¹ * (C * (q:ℝ)^(-(49:ℝ)/20)) ≤ C * (q:ℝ)^(-(49:ℝ)/20) := by
    have h2' : 0 < (q:ℝ)^(-(49:ℝ)/20) := Real.rpow_pos_of_pos hqpos _
    have h3 : (Real.log (q:ℝ))⁻¹ * (C * (q:ℝ)^(-(49:ℝ)/20))
        = ((Real.log (q:ℝ))⁻¹ * C) * (q:ℝ)^(-(49:ℝ)/20) := by ring
    rw [h3]
    have hCinv : (Real.log (q:ℝ))⁻¹ * C ≤ C := by
      have h := mul_le_mul_of_nonneg_right hloginv hC.le
      rwa [one_mul] at h
    exact mul_le_mul_of_nonneg_right hCinv h2'.le
  have hrpow2 : (0:ℝ) < (q:ℝ)^(-(2:ℝ)) := Real.rpow_pos_of_pos hqpos _
  have h24 : (1/24) * (q:ℝ)^(-(2:ℝ)) ≤ (1/8) * (q:ℝ)^(-(2:ℝ)) := by linarith
  linarith [hA, hle, h24]

lemma one_div_sq_eq_rpow (q : ℕ) : 1 / (q:ℝ)^2 = (q:ℝ)^(-(2:ℝ)) := by
  have h : (0:ℝ) ≤ (q:ℝ) := by positivity
  rw [one_div, ← Real.rpow_two (q:ℝ), ← Real.rpow_neg h]

theorem expansion_of_zeta_inputs {CZ1 CZ2 : ℝ} (hCZ1pos : 0 < CZ1) (hCZ2pos : 0 < CZ2)
    (hZ1 : ZetaBridgeAt CZ1) (hZ2 : ZetaBoxAt CZ2) :
    ∀ R : ℝ, 1 ≤ R → Siegel.ExpansionInput R := by
  obtain ⟨Cb, hCbpos, hCb⟩ := Commons.NumberTheory.Linnik.tentMellin_bridge_scale
    (L := 11/2) (K := 3/10) (by norm_num) (by norm_num)
  have hbr : BridgeUniform Cb := by
    intro q hq N hN ψ hψ hψprim hNq Z hZ X hX
    haveI : NeZero N := hN
    haveI : NeZero q := ⟨by omega⟩
    have h := hCb (N := N) ψ hψ hψprim (Q := q) hNq Z hZ X hX
    have e1 : (11:ℝ)/2 - 2 * ((3:ℝ)/10) = (49:ℝ)/10 := by norm_num
    have e2 : (-((3:ℝ)/2)) * ((11:ℝ)/2 - 2 * ((3:ℝ)/10)) = -((147:ℝ)/20) := by norm_num
    rw [e2, e1] at h
    have e3 : (-(49:ℝ))/10 = -((49:ℝ)/10) := by norm_num
    have e4 : (-(147:ℝ))/20 = -((147:ℝ)/20) := by norm_num
    rw [← e3, ← e4] at h
    rw [chiSum]
    simp only [tentW]
    exact h
  obtain ⟨Cpp, hCpppos, hCpp⟩ := UniformPrimePowerTail
  obtain ⟨Cnc, hCncpos, hCnc⟩ := UniformNonCoprimeTail
  obtain ⟨q1, hq1⟩ := threshold_bridge Cb
  obtain ⟨q2, hq2⟩ := threshold_zeta1 CZ1
  obtain ⟨q3, hq3⟩ := threshold_zeta2 CZ2
  obtain ⟨q4, hq4⟩ := threshold_ncs Cnc
  obtain ⟨q5, hq5⟩ := threshold_pp Cpp
  intro R hR
  refine ⟨max q1 (max q2 (max q3 (max q4 (max q5 3)))), ?_⟩
  intro q hq hqne a ha
  simp only [max_le_iff] at hq
  obtain ⟨H1, H2, H3, H4, H5, Hq3⟩ := hq
  haveI : NeZero q := hqne
  have hq2' : 2 ≤ q := by omega
  set X₀ : ℕ := Siegel.classLimit q (11/2) with hX₀
  set φr : ℝ := (q.totient : ℝ) with hφr
  have hqpos : 0 < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlogpos : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hφpos : 0 < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hφne : (q.totient : ℝ) ≠ 0 := ne_of_gt hφpos
  have hφCne : ((q.totient : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_natCast (q.totient)]
    exact Complex.ofReal_ne_zero.mpr hφne
  have hφle : (1:ℝ) ≤ (q.totient : ℝ) := by
    have h : 1 ≤ q.totient := Nat.one_le_iff_ne_zero.mpr (Nat.totient_pos.mpr (by omega)).ne'
    exact_mod_cast h
  have hφinvle : ((q.totient : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hφle
  have hφrpos : 0 < φr := by rw [hφr]; exact hφpos
  have hφrne : φr ≠ 0 := ne_of_gt hφrpos
  have hφrinvle : φr⁻¹ ≤ 1 := by rw [hφr]; exact hφinvle
  have hncsnn : 0 ≤ ncsSum q X₀ :=
    Finset.sum_nonneg (fun n hn => by
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
      have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
      have hwt : 0 ≤ tentW (Real.log (n:ℝ) / Real.log (q:ℝ)) :=
        (Commons.NumberTheory.Linnik.tentWeight_bounds (L := 11/2) (K := 3/10)
          (by norm_num) (by norm_num)).1 _
      have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      positivity)
  set Lc : ℂ := ((Real.log (q:ℝ) : ℝ) : ℂ) with hLc
  have hLcne : Lc ≠ 0 := by
    rw [hLc]; exact Complex.ofReal_ne_zero.mpr (ne_of_gt hlogpos)
  have hlogne : Real.log (q:ℝ) ≠ 0 := ne_of_gt hlogpos
  have hstarnorm : ∀ χ : DirichletCharacter ℂ q,
      ‖(starRingEnd ℂ) (χ (a : ZMod q))‖ = 1 := by
    intro χ
    rw [starRingEnd_apply, norm_star]
    have hu : IsUnit (a : ZMod q) := isUnit_of_coprime ha
    have h : χ (a : ZMod q) = χ (hu.unit : ZMod q) := by rw [hu.unit_spec]
    rw [h]
    exact DirichletCharacter.unit_norm_eq_one χ hu.unit
  set E1 : ℂ := Lc⁻¹ * chiSum (1 : DirichletCharacter ℂ q) q X₀ - (3/10:ℝ)^2
      + Work.LinnikContract.boxSum q (11/2) (3/10) R (1 : DirichletCharacter ℂ q) with hE1
  set Echi : DirichletCharacter ℂ q → ℂ :=
    fun χ => Lc⁻¹ * chiSum χ q X₀ + Work.LinnikContract.boxSum q (11/2) (3/10) R χ with hEchi
  set SE : ℂ := ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      (starRingEnd ℂ) (χ (a : ZMod q)) * Echi χ with hSE
  set E : ℂ := E1 + SE with hEdef
  set B : ℂ := ∑ χ : DirichletCharacter ℂ q,
      (starRingEnd ℂ) (χ (a : ZMod q)) * Work.LinnikContract.boxSum q (11/2) (3/10) R χ with hB
  have hE1b : ‖E1‖ ≤ CZ1 * Err q + CZ2 * (q:ℝ)^(-(49:ℝ)/10)
      + (Real.log (q:ℝ))⁻¹ * ncsSum q X₀ + farSumP q R := by
    rw [hE1, hX₀]
    exact principal_box_bound hZ1 hZ2 hq2' hR
  have hEchib : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      ‖Echi χ‖ ≤ Cb * Err q + (Real.log (q:ℝ))⁻¹ * ncsSum q X₀
        + farSum q (11/2) (3/10) R χ := by
    intro χ hχmem
    have hχ : χ ≠ 1 := (Finset.mem_erase.mp hχmem).1
    rw [hEchi, hX₀, Err]
    exact chiSum_box_bound hbr hq2' χ hχ hR
  have hSEb : ‖SE‖ ≤ (q.totient : ℝ) * (Cb * Err q + (Real.log (q:ℝ))⁻¹ * ncsSum q X₀)
      + ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), farSum q (11/2) (3/10) R χ := by
    rw [hSE]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        ‖(starRingEnd ℂ) (χ (a : ZMod q)) * Echi χ‖
          ≤ Cb * Err q + (Real.log (q:ℝ))⁻¹ * ncsSum q X₀ + farSum q (11/2) (3/10) R χ := by
      intro χ hχmem
      rw [norm_mul, hstarnorm χ, one_mul]
      exact hEchib χ hχmem
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hcard : ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) ≤ (q.totient : ℝ) := by
      have hc : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
      have hle : (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card ≤ q.totient := by
        rw [← hc]; exact Finset.card_le_card (Finset.erase_subset _ _)
      exact_mod_cast hle
    have htermnn : 0 ≤ Cb * Err q + (Real.log (q:ℝ))⁻¹ * ncsSum q X₀ := by
      have hErrn : 0 ≤ Cb * Err q := mul_nonneg hCbpos.le (Err_nonneg Hq3)
      have h2 : 0 ≤ (Real.log (q:ℝ))⁻¹ * ncsSum q X₀ :=
        mul_nonneg (le_of_lt (inv_pos.mpr hlogpos)) hncsnn
      linarith
    have h1 : ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ)
        * (Cb * Err q + (Real.log (q:ℝ))⁻¹ * ncsSum q X₀)
        ≤ (q.totient : ℝ) * (Cb * Err q + (Real.log (q:ℝ))⁻¹ * ncsSum q X₀) :=
      mul_le_mul_of_nonneg_right hcard htermnn
    calc ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            (Cb * Err q + (Real.log (q:ℝ))⁻¹ * ncsSum q X₀ + farSum q (11/2) (3/10) R χ)
        = ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ)
            * (Cb * Err q + (Real.log (q:ℝ))⁻¹ * ncsSum q X₀)
          + ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), farSum q (11/2) (3/10) R χ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
          try ring
      _ ≤ (q.totient : ℝ) * (Cb * Err q + (Real.log (q:ℝ))⁻¹ * ncsSum q X₀)
          + ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), farSum q (11/2) (3/10) R χ :=
          add_le_add h1 le_rfl
  have hEnorm : ‖E‖ ≤ CZ1 * Err q + CZ2 * (q:ℝ)^(-(49:ℝ)/10)
      + (Real.log (q:ℝ))⁻¹ * ncsSum q X₀ + farSumP q R
      + ((q.totient : ℝ) * (Cb * Err q + (Real.log (q:ℝ))⁻¹ * ncsSum q X₀)
        + ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), farSum q (11/2) (3/10) R χ) := by
    rw [hEdef]
    refine le_trans (norm_add_le _ _) (add_le_add hE1b hSEb)
  have hEchi1 : Echi (1 : DirichletCharacter ℂ q) = (3/10:ℝ)^2 + E1 := by
    rw [hEchi, hE1]; ring
  have hsumEchi : (∑ χ : DirichletCharacter ℂ q, (starRingEnd ℂ) (χ (a : ZMod q)) * Echi χ)
      = (3/10:ℝ)^2 + E := by
    rw [hEdef]
    rw [← Finset.sum_erase_add (Finset.univ)
      (fun χ : DirichletCharacter ℂ q => (starRingEnd ℂ) (χ (a : ZMod q)) * Echi χ)
      (Finset.mem_univ 1)]
    rw [one_apply_of_coprime ha, hEchi1]
    simp only [map_one, one_mul]
    ring
  have hsum_chi : (∑ χ : DirichletCharacter ℂ q, (starRingEnd ℂ) (χ (a : ZMod q)) * chiSum χ q X₀)
      = Lc * ((3/10:ℝ)^2 + E - B) := by
    have hpt : ∀ χ : DirichletCharacter ℂ q,
        (starRingEnd ℂ) (χ (a : ZMod q)) * chiSum χ q X₀
        = Lc * ((starRingEnd ℂ) (χ (a : ZMod q)) * Echi χ
            - (starRingEnd ℂ) (χ (a : ZMod q))
              * Work.LinnikContract.boxSum q (11/2) (3/10) R χ) := by
      intro χ
      have hsub : Lc⁻¹ * chiSum χ q X₀
          = Echi χ - Work.LinnikContract.boxSum q (11/2) (3/10) R χ := by
        rw [hEchi]; ring
      have hEq : chiSum χ q X₀ = Lc * (Lc⁻¹ * chiSum χ q X₀) := by
        rw [← mul_assoc, mul_inv_cancel₀ hLcne, one_mul]
      rw [hEq, hsub]
      ring
    have h1 : (∑ χ : DirichletCharacter ℂ q, (starRingEnd ℂ) (χ (a : ZMod q)) * chiSum χ q X₀)
        = ∑ χ : DirichletCharacter ℂ q, Lc * ((starRingEnd ℂ) (χ (a : ZMod q)) * Echi χ
            - (starRingEnd ℂ) (χ (a : ZMod q))
              * Work.LinnikContract.boxSum q (11/2) (3/10) R χ) :=
      Finset.sum_congr rfl (fun χ _ => hpt χ)
    rw [h1, ← Finset.mul_sum, Finset.sum_sub_distrib, hsumEchi, ← hB]
    try ring
  have hkey : Lc⁻¹ * classSum (q := q) a X₀ = ((φr⁻¹ : ℝ) : ℂ) * ((3/10:ℝ)^2 - B + E) := by
    have hφ : ((q.totient : ℂ))⁻¹ = ((φr⁻¹ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast (q.totient), ← hφr]
      exact (Complex.ofReal_inv φr).symm
    rw [ClassSumOrthogonality (q := q) a ha X₀, hsum_chi, hφ]
    field_simp
    ring
  have hdecomp : classSum (q := q) a X₀
      = ((Siegel.primeClassSum q (11/2) (3/10) a : ℝ) : ℂ) + ((classPP (q := q) a X₀ : ℝ) : ℂ) := by
    rw [hX₀, classSum_classLimit_eq, ← primeClassSum_eq_primePS]
  have hc2 : Lc⁻¹ * ((Siegel.primeClassSum q (11/2) (3/10) a : ℝ) : ℂ)
      = ((φr⁻¹ : ℝ) : ℂ) * ((3/10:ℝ)^2 - B + E)
        - Lc⁻¹ * ((classPP (q := q) a X₀ : ℝ) : ℂ) := by
    rw [← hkey, hdecomp, mul_add]
    ring
  have hBre : B.re = Siegel.signedBoxSumAll q (11/2) (3/10) R a := by
    rw [hB, Siegel.signedBoxSumAll, Complex.re_sum]
  have hre1 : (Lc⁻¹ * ((Siegel.primeClassSum q (11/2) (3/10) a : ℝ) : ℂ)).re
      = (Real.log (q:ℝ))⁻¹ * Siegel.primeClassSum q (11/2) (3/10) a := by
    have h1 : Lc⁻¹ * ((Siegel.primeClassSum q (11/2) (3/10) a : ℝ) : ℂ)
        = ((((Real.log (q:ℝ))⁻¹ * Siegel.primeClassSum q (11/2) (3/10) a : ℝ)) : ℂ) := by
      rw [hLc]
      push_cast
      ring
    rw [h1, Complex.ofReal_re]
  have hre2 : (((φr⁻¹ : ℝ) : ℂ) * ((3/10:ℝ)^2 - B + E)).re
      = φr⁻¹ * ((3/10:ℝ)^2 - Siegel.signedBoxSumAll q (11/2) (3/10) R a + E.re) := by
    rw [Complex.re_ofReal_mul]
    rw [Complex.add_re]
    rw [Complex.sub_re]
    have h2 : (((3/10:ℝ)^2 : ℂ)).re = (3/10:ℝ)^2 := by norm_num
    rw [h2, hBre]
    try ring
  have hre3 : (Lc⁻¹ * ((classPP (q := q) a X₀ : ℝ) : ℂ)).re
      = (Real.log (q:ℝ))⁻¹ * classPP (q := q) a X₀ := by
    have h1 : Lc⁻¹ * ((classPP (q := q) a X₀ : ℝ) : ℂ)
        = ((((Real.log (q:ℝ))⁻¹ * classPP (q := q) a X₀ : ℝ)) : ℂ) := by
      rw [hLc]
      push_cast
      ring
    rw [h1, Complex.ofReal_re]
  have hmain : (Real.log (q:ℝ))⁻¹ * Siegel.primeClassSum q (11/2) (3/10) a
      - φr⁻¹ * ((3/10:ℝ)^2 - Siegel.signedBoxSumAll q (11/2) (3/10) R a)
      = φr⁻¹ * E.re - (Real.log (q:ℝ))⁻¹ * classPP (q := q) a X₀ := by
    have h := congrArg Complex.re hc2
    rw [Complex.sub_re, hre1, hre2, hre3] at h
    linarith [h]
  have hclassPPnn : 0 ≤ classPP (q := q) a X₀ := by
    refine Finset.sum_nonneg (fun n hn => ?_)
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
    have hwt : 0 ≤ tentW (Real.log (n:ℝ) / Real.log (q:ℝ)) :=
      (Commons.NumberTheory.Linnik.tentWeight_bounds (L := 11/2) (K := 3/10)
        (by norm_num) (by norm_num)).1 _
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    positivity
  have hFZ : Siegel.farZeroSum q (11/2) (3/10) R = farSumP q R
      + ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), farSum q (11/2) (3/10) R χ := by
    have h1 : Siegel.farZeroSum q (11/2) (3/10) R
        = ∑ χ : DirichletCharacter ℂ q, farSum q (11/2) (3/10) R χ := rfl
    rw [h1, ← Finset.sum_erase_add (Finset.univ)
      (fun χ : DirichletCharacter ℂ q => farSum q (11/2) (3/10) R χ) (Finset.mem_univ 1), add_comm]
    simp only [farSum, farSumP]
  have hfarPnn : 0 ≤ farSumP q R := by
    rw [farSumP]
    refine tsum_nonneg (fun ρ => ?_)
    split_ifs with h
    · exact le_refl 0
    · exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hfarZnn : 0 ≤ Siegel.farZeroSum q (11/2) (3/10) R := by
    rw [Siegel.farZeroSum]
    refine Finset.sum_nonneg (fun χ _ => ?_)
    refine tsum_nonneg (fun ρ => ?_)
    split_ifs with h
    · exact le_refl 0
    · exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hEfin : ‖E‖ ≤ CZ1 * Err q + CZ2 * (q:ℝ)^(-(49:ℝ)/10)
      + ((q.totient : ℝ) * (Cb * Err q + (Real.log (q:ℝ))⁻¹ * ncsSum q X₀))
      + (Real.log (q:ℝ))⁻¹ * ncsSum q X₀
      + Siegel.farZeroSum q (11/2) (3/10) R := by
    refine le_trans hEnorm ?_
    rw [hFZ]
    linarith
  have hErr1 := hq1 q H1
  have hErr2 := hq2 q H2
  have hErr3 := hq3 q H3
  have hErr4 := hq4 q H4
  have hErr5 := hq5 q H5
  have hncs_bound : (Real.log (q:ℝ))⁻¹ * ncsSum q X₀
      ≤ (Real.log (q:ℝ))⁻¹ * (Cnc * (Real.log (q:ℝ))^2 * (q:ℝ)^(-(49:ℝ)/10)) := by
    have h : (Real.log (q:ℝ))⁻¹ * ncsSum q X₀
        ≤ (Real.log (q:ℝ))⁻¹ * (Cnc * (Real.log (q:ℝ))^2 * (q:ℝ)^(-(49/10:ℝ))) :=
      mul_le_mul_of_nonneg_left (by
        rw [hX₀]
        simpa only [ncsSum, tentW] using hCnc q hq2' (Siegel.classLimit q (11/2)))
        (le_of_lt (inv_pos.mpr hlogpos))
    rwa [show (q:ℝ)^(-(49/10:ℝ)) = (q:ℝ)^(-(49:ℝ)/10) from by congr 1; norm_num] at h
  have hpp_bound : (Real.log (q:ℝ))⁻¹ * classPP (q := q) a X₀
      ≤ (Real.log (q:ℝ))⁻¹ * (Cpp * (q:ℝ)^(-(49:ℝ)/20)) := by
    have h : (Real.log (q:ℝ))⁻¹ * classPP (q := q) a X₀
        ≤ (Real.log (q:ℝ))⁻¹ * (Cpp * (q:ℝ)^(-(49/20:ℝ))) :=
      mul_le_mul_of_nonneg_left (by
        rw [hX₀]
        simpa only [classPP, tentW] using hCpp q hq2' a (Siegel.classLimit q (11/2)))
        (le_of_lt (inv_pos.mpr hlogpos))
    rwa [show (q:ℝ)^(-(49/20:ℝ)) = (q:ℝ)^(-(49:ℝ)/20) from by congr 1; norm_num] at h
  have hPPn : 0 ≤ (Real.log (q:ℝ))⁻¹ * classPP (q := q) a X₀ :=
    mul_nonneg (le_of_lt (inv_pos.mpr hlogpos)) hclassPPnn
  rw [one_div_sq_eq_rpow, hmain]
  have htri : |φr⁻¹ * E.re - (Real.log (q:ℝ))⁻¹ * classPP (q := q) a X₀|
      ≤ |φr⁻¹ * E.re| + |(Real.log (q:ℝ))⁻¹ * classPP (q := q) a X₀| := by
    have hEq : φr⁻¹ * E.re - (Real.log (q:ℝ))⁻¹ * classPP (q := q) a X₀
        = φr⁻¹ * E.re + (-((Real.log (q:ℝ))⁻¹ * classPP (q := q) a X₀)) := by ring
    rw [hEq]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_neg]
  have hstep1 : |φr⁻¹ * E.re - (Real.log (q:ℝ))⁻¹ * classPP (q := q) a X₀|
      ≤ φr⁻¹ * ‖E‖ + (Real.log (q:ℝ))⁻¹ * classPP (q := q) a X₀ := by
    refine le_trans htri ?_
    have h2 : |φr⁻¹ * E.re| ≤ φr⁻¹ * ‖E‖ := by
      rw [abs_mul, abs_of_nonneg (le_of_lt (inv_pos.mpr hφrpos))]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm E) (le_of_lt (inv_pos.mpr hφrpos))
    have h3 : |(Real.log (q:ℝ))⁻¹ * classPP (q := q) a X₀|
        = (Real.log (q:ℝ))⁻¹ * classPP (q := q) a X₀ := abs_of_nonneg hPPn
    exact add_le_add h2 (le_of_eq h3)
  refine le_trans hstep1 ?_
  have hE2 := mul_le_mul_of_nonneg_left hEfin (le_of_lt (inv_pos.mpr hφrpos))
  have hφ3 : φr⁻¹ * (φr * (Cb * Err q + (Real.log (q:ℝ))⁻¹ * ncsSum q X₀))
      = Cb * Err q + (Real.log (q:ℝ))⁻¹ * ncsSum q X₀ := by
    rw [← mul_assoc, inv_mul_cancel₀ hφrne, one_mul]
  have hφ4 : φr⁻¹ * (CZ1 * Err q) ≤ CZ1 * Err q := by
    have h0 : 0 ≤ CZ1 * Err q := mul_nonneg hCZ1pos.le (Err_nonneg Hq3)
    nlinarith [hφrinvle, h0]
  have hφ5 : φr⁻¹ * (CZ2 * (q:ℝ)^(-(49:ℝ)/10)) ≤ CZ2 * (q:ℝ)^(-(49:ℝ)/10) := by
    have h0 : 0 ≤ CZ2 * (q:ℝ)^(-(49:ℝ)/10) :=
      mul_nonneg hCZ2pos.le (Real.rpow_nonneg hqpos.le _)
    nlinarith [hφrinvle, h0]
  have hφ6 : φr⁻¹ * ((Real.log (q:ℝ))⁻¹ * ncsSum q X₀) ≤ (Real.log (q:ℝ))⁻¹ * ncsSum q X₀ := by
    have h0 : 0 ≤ (Real.log (q:ℝ))⁻¹ * ncsSum q X₀ :=
      mul_nonneg (le_of_lt (inv_pos.mpr hlogpos)) hncsnn
    nlinarith [hφrinvle, h0]
  have hφ7 : φr⁻¹ * Siegel.farZeroSum q (11/2) (3/10) R
      ≤ Siegel.farZeroSum q (11/2) (3/10) R := by
    nlinarith [hφrinvle, hfarZnn]
  have hsum2 : φr⁻¹ * ‖E‖ + (Real.log (q:ℝ))⁻¹ * classPP (q := q) a X₀
      ≤ (q:ℝ)^(-(2:ℝ)) + φr⁻¹ * Siegel.farZeroSum q (11/2) (3/10) R := by
    have hmid : φr⁻¹ * ‖E‖
        ≤ CZ1 * Err q + CZ2 * (q:ℝ)^(-(49:ℝ)/10)
          + (Cb * Err q + (Real.log (q:ℝ))⁻¹ * ncsSum q X₀)
          + (Real.log (q:ℝ))⁻¹ * ncsSum q X₀
          + φr⁻¹ * Siegel.farZeroSum q (11/2) (3/10) R := by
      refine le_trans hE2 ?_
      linarith [hφ4, hφ5, hφ3, hφ6, hφ7]
    linarith [hmid, hErr1, hErr2, hErr3, hErr4, hErr5, hPPn, hncs_bound, hpp_bound]
  linarith [hsum2]

/-- **The class-sum expansion of Heath-Brown §13 in the Siegel case** (the input `S4` of
`Work.LinnikAreas.Siegel`): with `L = 11/2`, `K = 3/10`, the tent-weighted *prime* class sum
satisfies `|𝓛⁻¹ Σ_{p ≡ a (q)} (log p)/p·f(log p/𝓛) - φ(q)⁻¹(K² - Σ_χ Re(χ̄(a)·boxSum_χ))| ≤
q⁻² + φ(q)⁻¹·(mass of the zeros outside the box)` for all `q ≥ q₀(R)`.

The proof combines

* `ζ`: the explicit formula with the tent kernel (`Work.LinnikAreas.zetaTentExplicit`) and the
  comparison of its zero-sum limit with the box sum (`Work.LinnikAreas.zetaBoxComparison`);
* `χ ≠ 1`: the uniform explicit formula `tentMellin_bridge_scale` and the comparison
  `ZeroSumBoxComparison`;
* the arithmetic bookkeeping (`ClassSumOrthogonality`, `ChiSumSubPrimitive`,
  `UniformPrimePowerTail`, `UniformNonCoprimeTail`) and the numerical threshold lemmas above. -/
theorem siegelExpansion : ∀ R : ℝ, 1 ≤ R → Work.LinnikAreas.Siegel.ExpansionInput R := by
  obtain ⟨CZ1, hCZ1pos, hZ1⟩ := zetaTentExplicit
  obtain ⟨CZ2, hCZ2pos, hZ2⟩ := zetaBoxComparison
  exact expansion_of_zeta_inputs hCZ1pos hCZ2pos hZ1 hZ2

end Work.LinnikAreas
