/-
# ZeroFreeTables — `t23glue`

`Work.ZeroFreeTables.GlueH63`: Heath-Brown's Lemma 6.3 (the two-point `F`-inequality of §6)
at the test function of HB Lemma 7.2, in the shape in which the Tables 2/3 engine
(`HBTable2and3_engine`) consumes it: given the box witness `ρ'` (with height `Hb`), the
`δ`-near-line conditions, the `L52Hyp` input and the multiplicity `1` of the exceptional zero,
the §6 inequality holds at `(λ₀,λ₁) = (λ(ρ'), λ(ρ₁))` for every scale `λ` of the tables.

The analytic content is `HB63_TestFn` (HB Lemma 6.3 for an abstract test function); everything
here is the transfer of the setting hypotheses of `GlueH63` into the shape `HB63_TestFn` needs:
the critical strip for `zeroMult`-zeros, the multiplicities of the divisor of the completed
`L`-function (`zeroMultTransfer`), the box maximality into the `L`-maximality of Lemma 6.3
(`re_le_of_LFunction_zero_of_maximality`), and the two Archimedean "guards" that turn
`λ ≤ 2/5` resp. `λ ≤ (1/3)logloglog q` into the `δ`-window and §6 point conditions.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.t23Defs
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.HB63_TestFn
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultTransfer
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultStripPos
import Submission.Work.LinnikAreas.DhRepel.sameCharRepelNear
import Submission.Work.LinnikAreas.log_unbounded_nat

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## The two Archimedean guards -/

/-- **The exceptional-zero guard.**  For every `δ ∈ (0,1)` and every large enough `q`, a `β < 1`
with `(1-β) log q ≤ 2/5` is within `δ` of `1` and within HB's §6 point range
`√(log log q)/log q` (used at the exceptional zero `β₁`). -/
private lemma guardReal_aux (δ : ℝ) (hδ : 0 < δ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ β : ℝ,
      β < 1 → (1 - β) * Real.log (q : ℝ) ≤ 2 / 5 →
      |1 - β| ≤ δ ∧
      |1 - β| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
  obtain ⟨q₀, hq₀⟩ := Work.LinnikAreas.log_unbounded_nat
    (max ((2 : ℝ) / 5 / δ + 1) (Real.exp (Real.exp 4)))
  refine ⟨max q₀ 2, ?_⟩
  intro q hq β hβ hlam
  have hq₀' : q₀ ≤ q := le_trans (le_max_left _ _) hq
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hM := hq₀ q hq₀'
  have hA0 : (2 : ℝ) / 5 / δ + 1
      ≤ max ((2 : ℝ) / 5 / δ + 1) (Real.exp (Real.exp 4)) := le_max_left _ _
  have hge0 : Real.exp (Real.exp 4)
      ≤ max ((2 : ℝ) / 5 / δ + 1) (Real.exp (Real.exp 4)) := le_max_right _ _
  have hA : (2 : ℝ) / 5 / δ ≤ Real.log (q : ℝ) := by linarith [le_trans hA0 hM]
  have hge : Real.exp (Real.exp 4) ≤ Real.log (q : ℝ) := le_trans hge0 hM
  have h425 : (2 : ℝ) / 5 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
    have hexp : (4 : ℝ) / 25 ≤ Real.log (Real.log (q : ℝ)) := by
      have h1 : (4 : ℝ) / 25 ≤ Real.exp 4 := by
        have h := Real.one_le_exp (show (0 : ℝ) ≤ 4 by norm_num); linarith
      have h2 := Real.log_le_log (Real.exp_pos (Real.exp 4)) hge
      rw [Real.log_exp] at h2
      linarith
    have h3 := Real.sqrt_le_sqrt hexp
    rwa [show Real.sqrt ((4 : ℝ) / 25) = (2 : ℝ) / 5 by
      rw [show ((4 : ℝ) / 25) = ((2 : ℝ) / 5) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]] at h3
  have hkey : (2 : ℝ) / 5 ≤ Real.log (q : ℝ) * δ := by
    have h := (div_le_iff₀ hδ).mp hA
    linarith
  have h1 : 1 - β ≤ δ := by
    have ha : 1 - β ≤ (2 : ℝ) / 5 / Real.log (q : ℝ) := by
      rw [le_div_iff₀ hlogq]; exact hlam
    have hb : (2 : ℝ) / 5 / Real.log (q : ℝ) ≤ δ := by
      rw [div_le_iff₀ hlogq]; linarith
    linarith
  have h2 : 1 - β ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    have ha : 1 - β ≤ (2 : ℝ) / 5 / Real.log (q : ℝ) := by
      rw [le_div_iff₀ hlogq]; exact hlam
    have hb : (2 : ℝ) / 5 / Real.log (q : ℝ)
        ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) :=
      div_le_div_of_nonneg_right h425 hlogq.le
    linarith
  refine ⟨?_, ?_⟩ <;> rw [abs_of_pos (by linarith : (0 : ℝ) < 1 - β)] <;> assumption

/-- **The test-zero guard.**  For every large enough `q`: `log q > 0`, `√(log log q) ≥ 2/5`,
`(1/3) log log log q ≤ √(log log q)` and `log log log q / 3 ≥ 2/5` (used at the near-line zero
`ρ'`, where `λ(ρ') ≤ (1/3) log log log q`). -/
private lemma logGuard_aux :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      0 < Real.log (q : ℝ) ∧
      (2 : ℝ) / 5 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) ∧
      Real.log (Real.log (Real.log (q : ℝ))) / 3
        ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) ∧
      (2 : ℝ) / 5 ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := by
  obtain ⟨q₀, hq₀⟩ := Work.LinnikAreas.log_unbounded_nat (Real.exp (Real.exp 4))
  refine ⟨max q₀ 2, ?_⟩
  intro q hq
  have hq₀' : q₀ ≤ q := le_trans (le_max_left _ _) hq
  have hge : Real.exp (Real.exp 4) ≤ Real.log (q : ℝ) := hq₀ q hq₀'
  have hlogq : 0 < Real.log (q : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hge
  have hLL4 : Real.exp 4 ≤ Real.log (Real.log (q : ℝ)) := by
    have h2 := Real.log_le_log (Real.exp_pos (Real.exp 4)) hge
    rwa [Real.log_exp] at h2
  have hLLL4 : (4 : ℝ) ≤ Real.log (Real.log (Real.log (q : ℝ))) := by
    have h2 := Real.log_le_log (Real.exp_pos 4) hLL4
    rwa [Real.log_exp] at h2
  have hLLpos : 0 < Real.log (Real.log (q : ℝ)) := lt_of_lt_of_le (Real.exp_pos 4) hLL4
  have hsqrt : (2 : ℝ) / 5 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
    have hexp : (4 : ℝ) / 25 ≤ Real.log (Real.log (q : ℝ)) := by
      have h1 : (4 : ℝ) / 25 ≤ Real.exp 4 := by
        have h := Real.one_le_exp (show (0 : ℝ) ≤ 4 by norm_num); linarith
      linarith
    have h3 := Real.sqrt_le_sqrt hexp
    rwa [show Real.sqrt ((4 : ℝ) / 25) = (2 : ℝ) / 5 by
      rw [show ((4 : ℝ) / 25) = ((2 : ℝ) / 5) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]] at h3
  have hsq : Real.log (Real.log (Real.log (q : ℝ))) / 3
      ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
    have h := Real.log_le_rpow_div (x := Real.log (Real.log (q : ℝ)))
      (ε := (1 : ℝ) / 2) hLLpos.le (by norm_num)
    have h2 : (Real.log (Real.log (q : ℝ))) ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2)
        = 2 * Real.sqrt (Real.log (Real.log (q : ℝ))) := by
      rw [Real.sqrt_eq_rpow, div_eq_mul_inv, show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num, mul_comm]
    have h3 : Real.log (Real.log (Real.log (q : ℝ)))
        ≤ 2 * Real.sqrt (Real.log (Real.log (q : ℝ))) := by
      linarith [h, h2.le]
    linarith [Real.sqrt_nonneg (Real.log (Real.log (q : ℝ)))]
  exact ⟨hlogq, hsqrt, hsq, by linarith⟩

/-! ## The glue -/

theorem t23glue : Work.ZeroFreeTables.GlueH63 := by
  classical
  intro δ hδ0 hδ1
  obtain ⟨qA, hqA⟩ := guardReal_aux δ hδ0
  obtain ⟨qL, hqL⟩ := logGuard_aux
  have hδ1' : δ < 1 := by linarith
  let Q : ℝ → ℕ := fun lam => if h : 0 < lam then
      (HB63_TestFn (tf72T lam h) (1 / 1000) (by norm_num) δ hδ0 hδ1'
        (1 / 8 + 1 / 1000000)).choose
    else 0
  refine ⟨max (t23lams.toFinset.sup Q) (max qA (max qL 2)), ?_⟩
  intro q hq _inst χ₁ hcond ρ₁ ρ' Hb hmin hsq him0 hzm' hne hγ10 hHb hbox hcap'
    hδ2 hlam1 hmult1 hL52
  simp only [max_le_iff] at hq
  obtain ⟨hQT, hqA', hqL', hq2⟩ := hq
  -- basic facts about the two zeros
  have hZ1 : IsZ χ₁ ρ₁ := hmin.1.1
  have hχ1 : χ₁ ≠ 1 := hZ1.1
  have hzm1 : zeroMult χ₁ ρ₁ ≠ 0 := hZ1.2.1
  obtain ⟨hstrip₁0, hstrip₁1, _⟩ :=
    Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ1 hzm1
  obtain ⟨hstrip'0, hstrip'1, _⟩ :=
    Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ1 hzm'
  obtain ⟨hlogq, hsqrt25, hL3sqrt, hcapbig⟩ := hqL q hqL'
  have hρ₁eq : (ρ₁ : ℂ) = ((ρ₁.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him0]
  -- the two `δ`-window conditions and the two §6 point conditions
  have hβ₁ : |1 - ρ₁.re| ≤ δ := by
    have hlam : (1 - ρ₁.re) * Real.log (q : ℝ) ≤ 2 / 5 := by
      have h := hlam1
      rwa [lamOf] at h
    exact (hqA q hqA' ρ₁.re (by linarith) hlam).1
  have hβ₁pt : |1 - ρ₁.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    have hlam : (1 - ρ₁.re) * Real.log (q : ℝ) ≤ 2 / 5 := by
      have h := hlam1
      rwa [lamOf] at h
    exact (hqA q hqA' ρ₁.re (by linarith) hlam).2
  have hβ' : |1 - ρ'.re| ≤ δ := by
    have h1 : 1 - ρ'.re = lamOf q ρ' / Real.log (q : ℝ) := by rw [lamOf]; field_simp
    have hpos : 0 < lamOf q ρ' / Real.log (q : ℝ) := by rw [← h1]; linarith
    have h2 : lamOf q ρ' / Real.log (q : ℝ) ≤ δ := by
      rw [div_le_iff₀ hlogq]; exact hδ2
    rw [abs_le, h1]
    exact ⟨by linarith [hδ0, hpos], h2⟩
  have hρ'pt : |1 - ρ'.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    have h1 : 1 - ρ'.re = lamOf q ρ' / Real.log (q : ℝ) := by rw [lamOf]; field_simp
    have hpos : 0 < lamOf q ρ' / Real.log (q : ℝ) := by rw [← h1]; linarith
    have h2 : lamOf q ρ' / Real.log (q : ℝ)
        ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) :=
      div_le_div_of_nonneg_right (le_trans hcap' hL3sqrt) hlogq.le
    rw [abs_le, h1]
    exact ⟨by linarith [hδ0, hpos], h2⟩
  -- the rectangle condition at the exceptional zero
  have hcap₁ : lamOf q ((ρ₁.re : ℝ) : ℂ) ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := by
    rw [← hρ₁eq]
    linarith
  -- divisor facts
  have hprim : χ₁.primitiveCharacter ≠ 1 :=
    Work.LinnikAreas.OtherCharRepel.primitiveCharacter_ne_one χ₁ hχ1
  have hdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ₁.primitiveCharacter) :=
    DirichletCharacter.differentiable_completedLFunction hprim
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall (0 : ℂ) (|ρ'.im| + 2)) := fun z _ => hdiff.analyticAt z
  have hmem₁ : ρ₁ ∈ Metric.closedBall (0 : ℂ) (|ρ'.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : |ρ₁.re| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith [hstrip₁0], by linarith [hstrip₁1]⟩
    calc ‖ρ₁‖ ≤ |ρ₁.re| + |ρ₁.im| := Complex.norm_le_abs_re_add_abs_im ρ₁
      _ = |ρ₁.re| := by rw [him0]; simp
      _ ≤ |ρ'.im| + 2 := by linarith [abs_nonneg ρ'.im]
  have hmem' : ρ' ∈ Metric.closedBall (0 : ℂ) (|ρ'.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_trans (Complex.norm_le_abs_re_add_abs_im ρ') ?_
    have h2 : |ρ'.re| ≤ 2 := by
      rw [abs_le]; exact ⟨by linarith [hstrip'0], by linarith [hstrip'1]⟩
    linarith [abs_nonneg ρ'.im]
  have htr := Work.LinnikAreas.OtherCharRepel.zeroMultTransfer χ₁ hχ1
  have hdiv₁ : (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|ρ'.im| + 2))) ρ₁ ≠ 0 := htr.2.1 ρ₁ (|ρ'.im| + 2) hzm1 hmem₁
  have hdiv' : (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|ρ'.im| + 2))) ρ' ≠ 0 := htr.2.1 ρ' (|ρ'.im| + 2) hzm' hmem'
  have hdiv₁' : (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|ρ'.im| + 2))) ((ρ₁.re : ℝ) : ℂ) ≠ 0 := by
    rwa [← hρ₁eq]
  have hmult₁' : (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|ρ'.im| + 2))) ((ρ₁.re : ℝ) : ℂ) = 1 := by
    rw [← hρ₁eq, Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hmem₁]
    have h1 : analyticOrderNatAt (DirichletCharacter.completedLFunction χ₁.primitiveCharacter) ρ₁
        = 1 := by
      have h := hmult1
      rw [zeroMult] at h
      exact h
    rw [h1]; norm_num
  have hne' : ρ' ≠ ((ρ₁.re : ℝ) : ℂ) := by
    intro h
    exact hne (by rw [h, ← hρ₁eq])
  -- maximality of `ρ'` in the form used by HB Lemma 6.3
  have hmax := Work.LinnikAreas.DhRepel.re_le_of_LFunction_zero_of_maximality χ₁ hχ1 hzm1 hzm'
    (ρ₀ := ρ₁) (ρ' := ρ') (Hb := Hb) hbox
  have hmax' : ∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 →
      |u.im| ≤ Hb → u = ((ρ₁.re : ℝ) : ℂ) ∨ u.re ≤ ρ'.re := by
    intro u hu him
    rcases hmax u hu him with h | h
    · exact Or.inl (h.trans hρ₁eq)
    · exact Or.inr h
  intro lam hlammem hlam
  have hQle : Q lam ≤ q := by
    refine le_trans ?_ hQT
    exact Finset.le_sup (f := Q) (List.mem_toFinset.mpr hlammem)
  have hQchoose : (HB63_TestFn (tf72T lam hlam) (1 / 1000) (by norm_num) δ hδ0 hδ1'
      (1 / 8 + 1 / 1000000)).choose ≤ q := by
    have h := hQle
    simp only [Q] at h
    rwa [dif_pos hlam] at h
  have hmain := (HB63_TestFn (tf72T lam hlam) (1 / 1000) (by norm_num) δ hδ0 hδ1'
      (1 / 8 + 1 / 1000000)).choose_spec q hQchoose χ₁ hχ1 hsq (β₁ := ρ₁.re) (ρ' := ρ')
      hβ₁ hβ' (Hb := Hb) hHb hγ10 hβ₁pt hρ'pt hdiv₁' hdiv' hne' hmult₁' hmax' hcap₁ hcap'
      (hL52 (1 / 1000) (by norm_num) (by norm_num))
  -- the three integrals in Laplace-transform form
  have hF1 : (tf72T lam hlam).F (-(lamOf q ρ')) =
      ∫ t in (0 : ℝ)..(tf72T lam hlam).x₀,
        Real.exp ((lamOf q ρ') * t) * (tf72T lam hlam).f t := by
    rw [TestFn_F_eq_integral]
    exact intervalIntegral.integral_congr (fun t _ => by
      rw [show -((-(lamOf q ρ')) * t) = (lamOf q ρ') * t by ring])
  have hF2 : (tf72T lam hlam).F (lamOf q ((ρ₁.re : ℝ) : ℂ) - lamOf q ρ') =
      ∫ t in (0 : ℝ)..(tf72T lam hlam).x₀,
        Real.exp ((lamOf q ρ' - lamOf q ((ρ₁.re : ℝ) : ℂ)) * t) * (tf72T lam hlam).f t := by
    rw [TestFn_F_eq_integral]
    exact intervalIntegral.integral_congr (fun t _ => by
      rw [show -((lamOf q ((ρ₁.re : ℝ) : ℂ) - lamOf q ρ') * t)
        = (lamOf q ρ' - lamOf q ((ρ₁.re : ℝ) : ℂ)) * t by ring])
  have hF0 : (tf72T lam hlam).F 0 =
      ∫ t in (0 : ℝ)..(tf72T lam hlam).x₀, (tf72T lam hlam).f t := by
    rw [TestFn_F_eq_integral]
    exact intervalIntegral.integral_congr (fun t _ => by
      rw [zero_mul, neg_zero, Real.exp_zero, one_mul])
  have hmain' : 0 ≤ 2 * (tf72T lam hlam).F (-(lamOf q ρ'))
      - 2 * (tf72T lam hlam).F (lamOf q ((ρ₁.re : ℝ) : ℂ) - lamOf q ρ')
      - (tf72T lam hlam).F 0
      + (2 * (1 / 8 + 1 / 1000000) + 4 * (1 / 1000)) * (tf72T lam hlam).f 0 := by
    rw [hF1, hF2, hF0]
    exact hmain
  rw [show lamOf q ((ρ₁.re : ℝ) : ℂ) = lamOf q ρ₁ from
    congrArg (lamOf q) hρ₁eq.symm] at hmain'
  rw [show 2 * (1 / 8 + 1 / 1000000) + 4 * (1 / 1000) = CertSlack from by
    unfold CertSlack; norm_num] at hmain'
  rw [mul_comm CertSlack ((tf72T lam hlam).f 0)] at hmain'
  exact hmain'

end Work.ZeroFreeTables
