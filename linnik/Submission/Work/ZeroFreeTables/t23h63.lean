import Mathlib
import Submission.Work.ZeroFreeTables.t23Defs
import Submission.Work.ZeroFreeTables.HB63_TestFn
import Submission.Work.ZeroFreeTables.hbLemma6_2_engine
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.LinnikAreas.BGTZ.LFunction_eq_zero_imp_zeroMult

open DirichletCharacter Complex
open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-!
# `GlueH63`: HB Lemma 6.3 for the witness of the Tables 2/3 argument

`GlueH63` (`t23Defs`) is the `F`-language form of HB Lemma 6.3 at the tables' test functions
`tf72T lam` (`lam ∈ t23lams`), with the constant `CertSlack = 2c + 4ε` of `c = 1/8 + 10⁻⁶`,
`ε = 10⁻³`.  It is proved here by instantiating the already-proved abstract form
`HB63_TestFn` (`HB63_TestFn.lean`) and translating the hypotheses:

* `F`-values are turned into integrals by `TestFn_F_eq_integral`;
* the divisor/multiplicity hypotheses come from `zeroMult χ₁ ρ₁ = 1` and
  `zeroMult χ₁ ρ' ≠ 0` through `divisor_ne_zero_of_zeroMult` (`hbLemma6_2_engine`);
* the box-maximality of HB Lemma 6.3 is the `zeroMult`-maximality hypothesis, with
  `LFunction χ₁.primitiveCharacter u = 0` in the critical strip upgraded to
  `zeroMult χ₁ u ≠ 0` by `LFunction_eq_zero_imp_zeroMult`
  (`LinnikAreas/BGTZ`), and the cases `u.re ≥ 1`, `u.re ≤ 0` handled directly;
* the finitely many side conditions of the form "for `q` large" are combined over the
  literal list `t23lams` by `exists_forall_list`/`exists_log_ge`/`exists_log_log_ge`.
-/

/-- Combining finitely many "for all large `q`" clauses. -/
private lemma exists_forall_list {α : Type*} (l : List α) (P : α → ℕ → Prop)
    (h : ∀ a ∈ l, ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → P a q) :
    ∃ q₀ : ℕ, ∀ a ∈ l, ∀ q : ℕ, q₀ ≤ q → P a q := by
  induction l with
  | nil => exact ⟨0, fun a ha => by simp at ha⟩
  | cons a as ih =>
      obtain ⟨q₁, h₁⟩ := h a (by simp)
      obtain ⟨q₂, h₂⟩ := ih (fun b hb => h b (by simp [hb]))
      refine ⟨max q₁ q₂, fun b hb q hq => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact h₁ q (le_trans (le_max_left _ _) hq)
      · exact h₂ b hb' q (le_trans (le_max_right _ _) hq)

/-- `K ≤ log q` for all large `q`. -/
private lemma exists_log_ge (K : ℝ) : ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → K ≤ Real.log (q : ℝ) := by
  refine ⟨Nat.ceil (Real.exp K) + 3, fun q hq => ?_⟩
  have hq1 : (0 : ℝ) < (q : ℝ) := by
    have : (1 : ℕ) < q := by omega
    exact_mod_cast (lt_trans Nat.zero_lt_one this)
  have h2 : Real.exp K ≤ (q : ℝ) := by
    have hle : Real.exp K ≤ ((Nat.ceil (Real.exp K) : ℕ) : ℝ) := Nat.le_ceil _
    have hle2 : ((Nat.ceil (Real.exp K) : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (by omega : Nat.ceil (Real.exp K) ≤ q)
    linarith
  exact (Real.le_log_iff_exp_le hq1).mpr h2

/-- `A ≤ log log q` for all large `q`. -/
private lemma exists_log_log_ge (A : ℝ) : ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
    A ≤ Real.log (Real.log (q : ℝ)) := by
  obtain ⟨Q, hQ⟩ := exists_log_ge (Real.exp A)
  refine ⟨Q, fun q hq => ?_⟩
  have h1 : Real.exp A ≤ Real.log (q : ℝ) := hQ q hq
  have hpos : 0 < Real.log (q : ℝ) := lt_of_lt_of_le (Real.exp_pos A) h1
  exact (Real.le_log_iff_exp_le hpos).mpr h1

theorem t23h63 : Work.ZeroFreeTables.GlueH63 := by
  unfold Work.ZeroFreeTables.GlueH63
  intro δ hδ0 hδ2
  have key : ∃ Q : ℕ, ∀ lam ∈ t23lams, ∀ q : ℕ, Q ≤ q →
      ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) [NeZero χ₁.conductor] (ρ₁ ρ' : ℂ) (Hb : ℝ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
      zeroMult χ₁ ρ' ≠ 0 → ρ' ≠ ρ₁ →
      |ρ'.im| ≤ 10 * Real.log (q : ℝ) → |ρ'.im| + δ ≤ Hb →
      (∀ u : ℂ, zeroMult χ₁ u ≠ 0 → |u.im| ≤ Hb → u = ρ₁ ∨ lamOf q ρ' ≤ lamOf q u) →
      lamOf q ρ' ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
      lamOf q ρ' ≤ δ * Real.log (q : ℝ) →
      lamOf q ρ₁ ≤ 2 / 5 →
      zeroMult χ₁ ρ₁ = 1 →
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        Commons.NumberTheory.Linnik.L52Hyp χ₁ (1 / 8 + 1 / 1000000) ε δ) →
      ∀ (hlam : 0 < lam),
        0 ≤ 2 * (tf72T lam hlam).F (-(lamOf q ρ')) - 2 * (tf72T lam hlam).F (lamOf q ρ₁ - lamOf q ρ')
          - (tf72T lam hlam).F 0 + (tf72T lam hlam).f 0 * CertSlack := by
    have hpos_list : t23lams.Forall (fun l : ℝ => 0 < l) := by
      simp only [t23lams, List.forall_cons]
      norm_num
    refine exists_forall_list t23lams _ ?_
    intro lam hmem
    have hlam0 : 0 < lam := (List.forall_iff_forall_mem.mp hpos_list) lam hmem
    obtain ⟨qT, hqT⟩ := HB63_TestFn (tf72T lam hlam0) (1 / 1000) (by norm_num) δ hδ0
      (by linarith) (1 / 8 + 1 / 1000000)
    obtain ⟨Qa, hQa⟩ := exists_log_log_ge 16
    obtain ⟨Qb, hQb⟩ := exists_log_ge (2 / (5 * δ))
    obtain ⟨Qc, hQc⟩ := exists_log_log_ge (Real.exp (6 / 5))
    refine ⟨max (max qT (max Qa (max Qb Qc))) 3, ?_⟩
    intro q hq
    have hqT' : qT ≤ q :=
      le_trans (le_trans (le_max_left qT (max Qa (max Qb Qc)))
        (le_max_left (max qT (max Qa (max Qb Qc))) 3)) hq
    have hQa' : Qa ≤ q :=
      le_trans (le_trans (le_trans (le_max_left Qa (max Qb Qc))
        (le_max_right qT (max Qa (max Qb Qc))))
        (le_max_left (max qT (max Qa (max Qb Qc))) 3)) hq
    have hQb' : Qb ≤ q :=
      le_trans (le_trans (le_trans (le_trans (le_max_left Qb Qc)
        (le_max_right Qa (max Qb Qc))) (le_max_right qT (max Qa (max Qb Qc))))
        (le_max_left (max qT (max Qa (max Qb Qc))) 3)) hq
    have hQc' : Qc ≤ q :=
      le_trans (le_trans (le_trans (le_trans (le_max_right Qb Qc)
        (le_max_right Qa (max Qb Qc))) (le_max_right qT (max Qa (max Qb Qc))))
        (le_max_left (max qT (max Qa (max Qb Qc))) 3)) hq
    have h3 : 3 ≤ q := le_trans (le_max_right (max qT (max Qa (max Qb Qc))) 3) hq
    intro _inst χ₁ _cinst ρ₁ ρ' Hb hmin hsq him0 hzm hne him hHb hbox hrect' hnear hsmall hmult hL52 hlam
    -- elementary consequences of `q ≥ 3` and of the hypotheses
    have hq2 : 2 ≤ q := by omega
    have hlogq_pos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
    have hχ : χ₁ ≠ 1 := hmin.1.1.1
    have hρ₁eq : ρ₁ = ((ρ₁.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [him0]
    have hρ₁strip : 0 < ρ₁.re ∧ ρ₁.re < 1 :=
      re_mem_Ioo_of_zeroMult χ₁ hχ (by rw [hmult]; norm_num)
    have hρ'strip : 0 < ρ'.re ∧ ρ'.re < 1 := re_mem_Ioo_of_zeroMult χ₁ hχ hzm
    have hL16 : (16 : ℝ) ≤ Real.log (Real.log (q : ℝ)) := hQa q hQa'
    have hLexp : Real.exp (6 / 5) ≤ Real.log (Real.log (q : ℝ)) := hQc q hQc'
    have h2δ : 2 / (5 * δ) ≤ Real.log (q : ℝ) := hQb q hQb'
    have hloglog_pos : 0 < Real.log (Real.log (q : ℝ)) := lt_of_lt_of_le (by norm_num) hL16
    -- the logarithmic side conditions
    have h25 : (2 : ℝ) / 5 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
      refine (Real.le_sqrt (by norm_num : (0:ℝ) ≤ 2 / 5) (by positivity)).mpr ?_
      nlinarith [hL16]
    have hlogloglog : (6 : ℝ) / 5 ≤ Real.log (Real.log (Real.log (q : ℝ))) :=
      (Real.le_log_iff_exp_le hloglog_pos).mpr hLexp
    have h1mρ₁ : 1 - ρ₁.re ≤ (2 / 5) / Real.log (q : ℝ) := by
      rw [le_div_iff₀ hlogq_pos]
      have h := hsmall
      simp only [lamOf] at h
      linarith
    have hβ₁ : |1 - ρ₁.re| ≤ δ := by
      have h1 : 1 - ρ₁.re ≤ δ := by
        refine le_trans h1mρ₁ ?_
        rw [div_le_iff₀ hlogq_pos]
        have h := mul_le_mul_of_nonneg_left h2δ hδ0.le
        rwa [show δ * (2 / (5 * δ)) = 2 / 5 from by field_simp [ne_of_gt hδ0]] at h
      rw [abs_of_nonneg (by linarith [hρ₁strip.2])]
      exact h1
    have hβ₁pt : |1 - ρ₁.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
      rw [abs_of_nonneg (by linarith [hρ₁strip.2])]
      exact le_trans h1mρ₁ (div_le_div_of_nonneg_right h25 hlogq_pos.le)
    have hlogL_le : Real.log (Real.log (Real.log (q : ℝ)))
        ≤ 2 * Real.sqrt (Real.log (Real.log (q : ℝ))) := by
      have h2 : Real.log (Real.log (Real.log (q : ℝ)))
          = 2 * Real.log (Real.sqrt (Real.log (Real.log (q : ℝ)))) := by
        rw [Real.log_sqrt hloglog_pos.le]
        ring
      rw [h2]
      have h3 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hloglog_pos)
      have h4 : 0 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := Real.sqrt_nonneg _
      linarith
    have hρ'pt : |1 - ρ'.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
      have h1mρ' : 1 - ρ'.re = (lamOf q ρ') / Real.log (q : ℝ) := by
        rw [lamOf]; field_simp
      have hstep : lamOf q ρ' ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
        have h4 : 0 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := Real.sqrt_nonneg _
        have h5 : Real.log (Real.log (Real.log (q : ℝ))) / 3
            ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by linarith
        exact le_trans hrect' h5
      rw [abs_of_nonneg (by linarith [hρ'strip.2]), h1mρ']
      exact div_le_div_of_nonneg_right hstep hlogq_pos.le
    have hβ' : |1 - ρ'.re| ≤ δ := by
      have h1 : 1 - ρ'.re ≤ δ := by
        have h2 : (1 - ρ'.re) * Real.log (q : ℝ) ≤ δ * Real.log (q : ℝ) := by
          have h := hnear
          simp only [lamOf] at h
          exact h
        by_contra hlt
        push_neg at hlt
        have h4 : δ * Real.log (q : ℝ) < (1 - ρ'.re) * Real.log (q : ℝ) :=
          mul_lt_mul_of_pos_right hlt hlogq_pos
        linarith
      rw [abs_of_nonneg (by linarith [hρ'strip.2])]
      exact h1
    have hrect₁ : lamOf q (((ρ₁.re : ℝ) : ℂ))
        ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := by
      have heq : lamOf q (((ρ₁.re : ℝ) : ℂ)) = lamOf q ρ₁ := by rw [← hρ₁eq]
      rw [heq]
      linarith [hlogloglog]
    -- the divisor/multiplicity hypotheses
    have hmem₁ : (((ρ₁.re : ℝ) : ℂ)) ∈ Metric.closedBall (0 : ℂ) (|ρ'.im| + 2) := by
      rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |ρ₁.re| ≤ 1 := by rw [abs_of_pos hρ₁strip.1]; linarith [hρ₁strip.2]
      linarith [abs_nonneg ρ'.im]
    have hmem' : ρ' ∈ Metric.closedBall (0 : ℂ) (|ρ'.im| + 2) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      refine le_trans (Complex.norm_le_abs_re_add_abs_im ρ') ?_
      have h1 : |ρ'.re| ≤ 2 := by rw [abs_of_pos hρ'strip.1]; linarith [hρ'strip.2]
      linarith [abs_nonneg ρ'.im]
    have hdiv₁ : (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|ρ'.im| + 2))) (((ρ₁.re : ℝ) : ℂ)) ≠ 0 :=
      divisor_ne_zero_of_zeroMult χ₁ hχ hmem₁ (by rw [← hρ₁eq, hmult]; norm_num)
    have hdiv' : (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|ρ'.im| + 2))) ρ' ≠ 0 :=
      divisor_ne_zero_of_zeroMult χ₁ hχ hmem' hzm
    have hne' : ρ' ≠ (((ρ₁.re : ℝ) : ℂ)) := by rw [← hρ₁eq]; exact hne
    have hmult₁ : (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|ρ'.im| + 2))) (((ρ₁.re : ℝ) : ℂ)) = 1 := by
      have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
          (Metric.closedBall 0 (|ρ'.im| + 2)) :=
        fun z _ => (DirichletCharacter.differentiable_completedLFunction
          (primitive_ne_one_of_ne_one χ₁ hχ)).analyticAt z
      rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hmem₁]
      have hzm₁ : zeroMult χ₁ (((ρ₁.re : ℝ) : ℂ)) = 1 := by rw [← hρ₁eq]; exact hmult
      have hord : analyticOrderNatAt (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
          (((ρ₁.re : ℝ) : ℂ)) = 1 := by
        simpa only [zeroMult] using hzm₁
      rw [hord]
      norm_num
    -- the box maximality of HB Lemma 6.3
    have hmax : ∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 → |u.im| ≤ Hb →
        u = (((ρ₁.re : ℝ) : ℂ)) ∨ u.re ≤ ρ'.re := by
      intro u hLu himu
      by_cases hre1 : 1 ≤ u.re
      · exact absurd hLu (DirichletCharacter.LFunction_ne_zero_of_one_le_re
          (χ := χ₁.primitiveCharacter) (Or.inl (primitive_ne_one_of_ne_one χ₁ hχ)) hre1)
      · by_cases hre0 : 0 < u.re
        · have huzm : zeroMult χ₁ u ≠ 0 := by
            have hLu' : DirichletCharacter.LFunction χ₁ u = 0 := by
              rw [Work.LinnikAreas.OtherCharRepel.LFunction_eq_primitiveCharacter_mul χ₁ hχ u,
                hLu, zero_mul]
            exact Work.LinnikAreas.BGTZ.LFunction_eq_zero_imp_zeroMult χ₁ hχ hre0
              (lt_of_not_ge hre1) hLu'
          rcases hbox u huzm himu with h | h
          · exact Or.inl (h.trans hρ₁eq)
          · refine Or.inr ?_
            have h' : (1 - ρ'.re) * Real.log (q : ℝ) ≤ (1 - u.re) * Real.log (q : ℝ) := by
              have hh := h
              simp only [lamOf] at hh
              exact hh
            by_contra hc
            push_neg at hc
            have h5 : ρ'.re * Real.log (q : ℝ) < u.re * Real.log (q : ℝ) :=
              mul_lt_mul_of_pos_right hc hlogq_pos
            linarith
        · exact Or.inr (by have h := le_of_not_gt hre0; linarith [hρ'strip.1])
    -- HB Lemma 6.3 at this witness
    have hmain := hqT q hqT' (χ := χ₁) (hχ := hχ) (hreal := hsq) (β₁ := ρ₁.re) (ρ' := ρ')
      (hβ₁ := hβ₁) (hβ' := hβ') (Hb := Hb) (hHb := hHb) (hγ10 := him) (hβ₁pt := hβ₁pt)
      (hρ'pt := hρ'pt) (hdiv₁ := hdiv₁) (hdiv' := hdiv') (hne := hne') (hmult₁ := hmult₁)
      (hmax := hmax) (hrect₁ := hrect₁) (hrect' := hrect')
      (H := hL52 (1 / 1000) (by norm_num) (by norm_num))
    -- translate the `F`-values into integrals
    have hF1 : (tf72T lam hlam0).F (-(lamOf q ρ'))
        = ∫ t in (0 : ℝ)..(tf72T lam hlam0).x₀,
            Real.exp ((lamOf q ρ') * t) * (tf72T lam hlam0).f t := by
      rw [TestFn_F_eq_integral]
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [show -((-(lamOf q ρ')) * t) = (lamOf q ρ') * t from by ring]
    have hF2 : (tf72T lam hlam0).F (lamOf q ρ₁ - lamOf q ρ')
        = ∫ t in (0 : ℝ)..(tf72T lam hlam0).x₀,
            Real.exp ((lamOf q ρ' - lamOf q ρ₁) * t) * (tf72T lam hlam0).f t := by
      rw [TestFn_F_eq_integral]
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [show -((lamOf q ρ₁ - lamOf q ρ') * t) = (lamOf q ρ' - lamOf q ρ₁) * t from by ring]
    have hF0 : (tf72T lam hlam0).F 0
        = ∫ t in (0 : ℝ)..(tf72T lam hlam0).x₀, (tf72T lam hlam0).f t := by
      rw [TestFn_F_eq_integral]
      apply intervalIntegral.integral_congr
      intro t _
      simp
    rw [Subsingleton.elim hlam hlam0]
    rw [hF1, hF2, hF0]
    rw [← hρ₁eq] at hmain
    have hconst : 2 * (1 / 8 + 1 / 1000000) + 4 * (1 / 1000) = CertSlack := by
      unfold CertSlack
      norm_num
    rw [hconst, mul_comm CertSlack ((tf72T lam hlam0).f 0)] at hmain
    linarith
  obtain ⟨Q, hQ⟩ := key
  exact ⟨Q, fun q hq _inst χ₁ _cinst ρ₁ ρ' Hb hmin hsq him0 hzm hne him hHb hbox hrect' hnear
    hsmall hmult hL52 lam hmem hlam =>
      hQ lam hmem q hq χ₁ ρ₁ ρ' Hb hmin hsq him0 hzm hne him hHb hbox hrect' hnear
        hsmall hmult hL52 hlam⟩

end Work.ZeroFreeTables
