/-
# ZeroFreeTables/lam0w — `s6_real_low`

The first conjunct of Heath-Brown's Lemma 8.4 (PLMS 64 (1992) 265–338) in the case where the
second zero `ρ` is *real*, by Heath-Brown's own §6/§8 method: the `F`-method of §6 with the test
functions of §7 (HB Lemma 7.2), through the row mechanism of Tables 2 and 3.

* `s6_ineq_at`: HB Lemma 6.3 (the two-point `F`-inequality, available in the workspace as
  `HB63_TestFn`) instantiated at the test function of HB Lemma 7.2 at scale `lam`, with the
  setting hypotheses of the present lemma converted into the shape `HB63_TestFn` needs
  (multiplicity `1` of the exceptional zero, maximality of the test zero from the minimality
  hypothesis, the `δ`-window conditions, the rectangle conditions).
* the row data of Tables 2/3: each row `(λ, b, v)` carries its certificate (the failure
  `2F(−v) − 2F(b−v) < F(0) − K f(0)` of the §6 inequality at `(v,b)`, in the closed form of
  `hb72G`) and its coverage `2 log (1/b_next) ≤ v`;
* the assembly: the failure of the conclusion forces `λ(ρ)` below a row's `v`, and the §6
  inequality at that row's scale is contradicted.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Table4Defs
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.HB8Defs
import Submission.Work.ZeroFreeTables.HB63_TestFn
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.lam0w.TestFn_E_mono
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.t23Gclosed
import Submission.Work.ZeroFreeTables.Table4.HB82
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultTransfer
import Submission.Work.LinnikAreas.DhRepel.sameCharRepelNear
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity
import Submission.Work.LinnikAreas.OtherCharRepel.completedLFunction_analyticOrderAt_ne_top
import Submission.Work.ZeroFreeTables.tf72Fc_re_eq_hb72G
import Submission.Work.LinnikAreas.A5.boxAbs_le_deltaSum

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.lam0w

open Work.LinnikContract

/-- The constant `c = 1/8 + 10⁻⁶` of the `φ = 1/4` log-derivative input
(`Work.ZeroFreeTables.Table4.l52HypRealQuarter`) and the §6 slack `ε = 1/4000`.  The row
certificates use the coefficient `0.252 ≥ 2c + 4ε = 0.251002`. -/
def cS6 : ℝ := 1 / 8 + 1 / 1000000
def eS6 : ℝ := 1 / 4000

theorem two_c_add_four_e_le : 2 * cS6 + 4 * eS6 ≤ 252 / 1000 := by
  unfold cS6 eS6; norm_num

/-! ## The Laplace transform of HB Lemma 7.2's test function -/

theorem TF_eq_hb (lam : ℝ) (hlam : 0 < lam) (x : ℝ) :
    (tf72T lam hlam).F x = hb72G (-x/lam)/30 := by
  show (tf72Fc lam (x : ℂ)).re = _
  rw [tf72Fc_re_eq_hb72G lam x hlam]

theorem TF_zero (lam : ℝ) (hlam : 0 < lam) : (tf72T lam hlam).F 0 = 8/9 := by
  show (tf72Fc lam ((0:ℝ):ℂ)).re = 8/9
  rw [show ((0:ℝ):ℂ) = 0 from by norm_num]
  exact tf72Fc_zero_re lam hlam

theorem TF_f0 (lam : ℝ) (hlam : 0 < lam) : (tf72T lam hlam).f 0 = 16*lam/15 :=
  tf72f_at_zero lam hlam

/-! ## Two-sided rational Taylor bounds for `Real.exp` on `[0,16]` -/

/-- Rational bounds for `Real.exp x`, `0 ≤ x ≤ 16`, from the Taylor polynomial of `exp` at
`x/16` (12 terms, Lagrange remainder) and `exp x = (exp (x/16))¹⁶`. -/
theorem exp_bounds_gen {x lo hi : ℝ} (hx0 : 0 ≤ x) (hx16 : x ≤ 16)
    (hlo : lo ≤ ((∑ m ∈ Finset.range 12, (x / 16) ^ m / (Nat.factorial m : ℝ))
      - expErr (x/4)) ^ 16)
    (hhi : ((∑ m ∈ Finset.range 12, (x / 16) ^ m / (Nat.factorial m : ℝ))
      + expErr (x/4)) ^ 16 ≤ hi) :
    lo ≤ Real.exp x ∧ Real.exp x ≤ hi := by
  have hx16pos : (0:ℝ) ≤ x/16 := by positivity
  have hxle1 : x/16 ≤ 1 := by linarith
  have hb := Real.exp_bound (x := x/16) (n := 12)
    (by rw [abs_of_nonneg hx16pos]; exact hxle1) (by norm_num)
  have hxdiv : x / 4 / 4 = x / 16 := by ring
  have herr : |x/16| ^ 12 * ((Nat.succ 12 : ℝ) / ((Nat.factorial 12 : ℝ) * ((12 : ℕ) : ℝ)))
      = expErr (x/4) := by
    rw [abs_of_nonneg hx16pos, ← hxdiv]
    rfl
  rw [herr] at hb
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  have hT1 : (1:ℝ) ≤ ∑ m ∈ Finset.range 12, (x / 16) ^ m / (Nat.factorial m : ℝ) := by
    have h := Finset.single_le_sum (f := fun m : ℕ => (x/16)^m / (Nat.factorial m : ℝ))
      (fun i _ => by positivity) (Finset.mem_range.mpr (by norm_num : (0:ℕ) < 12))
    simpa using h
  have herr1 : expErr (x/4) ≤ 1 := by
    have hpow : (x/16) ^ 12 ≤ 1 := by
      apply pow_le_one₀ (by positivity); linarith
    have hc : (Nat.succ 12 : ℝ) / ((Nat.factorial 12 : ℝ) * ((12 : ℕ) : ℝ)) ≤ 1 := by norm_num
    have hc0 : (0:ℝ) ≤ (Nat.succ 12 : ℝ) / ((Nat.factorial 12 : ℝ) * ((12 : ℕ) : ℝ)) := by
      norm_num
    unfold expErr
    rw [hxdiv]
    calc (x/16)^12 * ((Nat.succ 12 : ℝ) / ((Nat.factorial 12 : ℝ) * ((12 : ℕ) : ℝ)))
        ≤ 1 * 1 := mul_le_mul hpow hc hc0 (by norm_num)
      _ = 1 := by norm_num
  have hTm : 0 ≤ (∑ m ∈ Finset.range 12, (x / 16) ^ m / (Nat.factorial m : ℝ)) - expErr (x/4) :=
    by linarith
  have h1 : ((∑ m ∈ Finset.range 12, (x / 16) ^ m / (Nat.factorial m : ℝ))
      - expErr (x/4)) ^ 16 ≤ (Real.exp (x/16))^16 :=
    pow_le_pow_left₀ hTm (by linarith) 16
  have h2 : (Real.exp (x/16))^16 ≤ ((∑ m ∈ Finset.range 12, (x / 16) ^ m
      / (Nat.factorial m : ℝ)) + expErr (x/4)) ^ 16 :=
    pow_le_pow_left₀ (Real.exp_pos _).le (by linarith) 16
  have hexp : Real.exp x = (Real.exp (x/16))^16 := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  exact ⟨by rw [hexp]; exact le_trans hlo h1, by rw [hexp]; exact le_trans h2 hhi⟩

/-! ## Heath-Brown's Lemma 6.3 at scale `lam` -/

/-- **HB Lemma 6.3 at the test function of Lemma 7.2 at scale `lam`**, in the setting of the
present lemma. -/
theorem s6_ineq_at (lam : ℝ) (hlam : 0 < lam) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (c : ℝ) (hc : c ≤ cS6) (Qδ : ℕ)
    (hprov : ∀ (q : ℕ), Qδ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → χ ^ 2 = 1 → Commons.NumberTheory.Linnik.L52Hyp χ c eS6 δ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
      zeroMult χ₁ ρ₁ = 1 →
      zeroMult χ₁ ρ ≠ 0 → |ρ.im| ≤ 2 → ρ ≠ ρ₁ → ρ.im = 0 →
      (∀ u : ℂ, zeroMult χ₁ u ≠ 0 → |u.im| ≤ 1 → u ≠ ρ₁ → lamOf q ρ ≤ lamOf q u) →
      lamOf q ρ₁ ≤ 1 / 5 → lamOf q ρ ≤ 12 →
      lamOf q ρ ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
      (1 / 5) / δ ≤ Real.log (q : ℝ) → 12 / δ ≤ Real.log (q : ℝ) →
      (1 / 5) ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) →
      12 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) →
      (1 : ℝ) / 5 ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
      0 ≤ 2 * (tf72T lam hlam).F (-(lamOf q ρ)) - 2 * (tf72T lam hlam).F (lamOf q ρ₁ - lamOf q ρ)
        - (tf72T lam hlam).F 0 + (2 * c + 4 * eS6) * (tf72T lam hlam).f 0 := by
  obtain ⟨qT, hT⟩ := HB63_TestFn (tf72T lam hlam) eS6 (by unfold eS6; norm_num)
    δ hδ0 hδ1 c
  refine ⟨max (max qT 3) Qδ, ?_⟩
  intro q hq _inst χ₁ ρ₁ ρ hwide hsq him0 hmult1 hzm him hne hρim0 hmin hlam1 hρ12 hcap
    hthr1 hthr2 hpt1 hpt2 hcap1
  have hqT : qT ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hq3 : 3 ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hqδ : Qδ ≤ q := le_trans (le_max_right _ _) hq
  letI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have hχ1 : χ₁ ≠ 1 := isZ_ne_one (isMin1_isZ hwide.1)
  have hq2 : 2 ≤ q := by omega
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hzm1 : zeroMult χ₁ ρ₁ ≠ 0 := by rw [hmult1]; norm_num
  have hstrip₁ := Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ1 hzm1 (u := ρ₁)
  have hstripρ := Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ1 hzm (u := ρ)
  -- the two `δ`-window conditions
  have hβ₁ : |1 - ρ₁.re| ≤ δ := by
    have h1 : 1 - ρ₁.re = lamOf q ρ₁ / Real.log (q : ℝ) := by rw [lamOf]; field_simp
    have h2 : lamOf q ρ₁ / Real.log (q : ℝ) ≤ δ := by
      calc lamOf q ρ₁ / Real.log (q : ℝ) ≤ (1 / 5) / Real.log (q : ℝ) :=
            div_le_div_of_nonneg_right hlam1 hlogq.le
        _ ≤ δ := by
            rw [div_le_iff₀ hlogq]
            linarith [(div_le_iff₀ hδ0).mp hthr1]
    rw [abs_le, h1]
    exact ⟨by linarith [hstrip₁.1], h2⟩
  have hβ' : |1 - ρ.re| ≤ δ := by
    have h1 : 1 - ρ.re = lamOf q ρ / Real.log (q : ℝ) := by rw [lamOf]; field_simp
    have h2 : lamOf q ρ / Real.log (q : ℝ) ≤ δ := by
      calc lamOf q ρ / Real.log (q : ℝ) ≤ 12 / Real.log (q : ℝ) :=
            div_le_div_of_nonneg_right hρ12 hlogq.le
        _ ≤ δ := by
            rw [div_le_iff₀ hlogq]
            linarith [(div_le_iff₀ hδ0).mp hthr2]
    rw [abs_le, h1]
    exact ⟨by linarith [hstripρ.1], h2⟩
  have hβ₁pt : |1 - ρ₁.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    have h1 : 1 - ρ₁.re = lamOf q ρ₁ / Real.log (q : ℝ) := by rw [lamOf]; field_simp
    have h2 : lamOf q ρ₁ / Real.log (q : ℝ)
        ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hlogq.le
    rw [abs_le, h1]
    exact ⟨by linarith [hstrip₁.1], h2⟩
  have hρ'pt : |1 - ρ.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    have h1 : 1 - ρ.re = lamOf q ρ / Real.log (q : ℝ) := by rw [lamOf]; field_simp
    have h2 : lamOf q ρ / Real.log (q : ℝ)
        ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hlogq.le
    rw [abs_le, h1]
    exact ⟨by linarith [hstripρ.1], h2⟩
  have hcap₁ : lamOf q (↑ρ₁.re : ℂ) ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := by
    have : (↑ρ₁.re : ℂ) = ρ₁ := by apply Complex.ext <;> simp [him0]
    rw [this]; linarith
  -- divisor facts
  have hdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ₁.primitiveCharacter) :=
    DirichletCharacter.differentiable_completedLFunction
      (Work.LinnikAreas.OtherCharRepel.primitiveCharacter_ne_one χ₁ hχ1)
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall (0:ℂ) (|ρ.im| + 2)) := fun z _ => hdiff.analyticAt z
  have hmem₁ : (ρ₁ : ℂ) ∈ Metric.closedBall (0:ℂ) (|ρ.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hρ₁ : ρ₁ = ((ρ₁.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him0]
    have h1 : |ρ₁.re| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith [hstrip₁.1], by linarith [hstrip₁.2.1]⟩
    calc ‖ρ₁‖ = |ρ₁.re| := by rw [hρ₁, Complex.norm_real]; simp
      _ ≤ |ρ.im| + 2 := by linarith [abs_nonneg ρ.im]
  have hmem' : ρ ∈ Metric.closedBall (0:ℂ) (|ρ.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_trans (Complex.norm_le_abs_re_add_abs_im ρ) ?_
    have h2 : |ρ.re| ≤ 2 := by
      rw [abs_le]; exact ⟨by linarith [hstripρ.1], by linarith [hstripρ.2.1]⟩
    linarith [abs_nonneg ρ.im]
  have hdiv₁ := (Work.LinnikAreas.OtherCharRepel.zeroMultTransfer χ₁ hχ1).2.1 ρ₁ (|ρ.im| + 2)
    hzm1 hmem₁
  have hdiv' := (Work.LinnikAreas.OtherCharRepel.zeroMultTransfer χ₁ hχ1).2.1 ρ (|ρ.im| + 2)
    hzm hmem'
  have hconj₁ : (ρ₁ : ℂ) = (↑ρ₁.re : ℂ) := by apply Complex.ext <;> simp [him0]
  have hdiv₁' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|ρ.im| + 2))) (↑ρ₁.re : ℂ) ≠ 0 := by rwa [← hconj₁]
  have hmult₁' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|ρ.im| + 2))) (↑ρ₁.re : ℂ) = 1 := by
    rw [← hconj₁, Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hmem₁]
    have h1 : analyticOrderNatAt (DirichletCharacter.completedLFunction χ₁.primitiveCharacter) ρ₁
        = 1 := by
      have := hmult1
      rw [zeroMult] at this
      exact this
    rw [h1]; norm_num
  have hne' : ρ ≠ (↑ρ₁.re : ℂ) := by
    intro h
    apply hne
    rw [h, ← hconj₁]
  have hmax : ∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 → |u.im| ≤ 1 →
      u = (↑ρ₁.re : ℂ) ∨ u.re ≤ ρ.re := by
    have h0 := Work.LinnikAreas.DhRepel.re_le_of_LFunction_zero_of_maximality χ₁ hχ1 hzm1 hzm
      (ρ₀ := ρ₁) (ρ' := ρ) (Hb := 1) ?_
    · intro u hu him
      rcases h0 u hu him with h | h
      · exact Or.inl (h.trans hconj₁)
      · exact Or.inr h
    · intro u hzu him
      rcases eq_or_ne u ρ₁ with h | h
      · exact Or.inl h
      · exact Or.inr (hmin u hzu him h)
  have hmain := hT q hqT χ₁ hχ1 hsq (β₁ := ρ₁.re) (ρ' := ρ) hβ₁ hβ'
    (Hb := 1) (by rw [hρim0]; simp only [abs_zero, zero_add]; linarith [hδ1])
    (by rw [hρim0]; simp only [abs_zero]; linarith [hlogq])
    hβ₁pt hρ'pt hdiv₁' hdiv' hne' hmult₁' hmax hcap₁ hcap (hprov q hqδ χ₁ hχ1 hsq)
  -- conversion of the three integrals into the Laplace-transform form
  have hF1 : (tf72T lam hlam).F (-(lamOf q ρ)) =
      ∫ t in (0:ℝ)..(tf72T lam hlam).x₀, Real.exp ((lamOf q ρ) * t) * (tf72T lam hlam).f t := by
    rw [TestFn_F_eq_integral]
    exact intervalIntegral.integral_congr (fun t _ => by
      rw [show -((-(lamOf q ρ)) * t) = (lamOf q ρ) * t by ring])
  have hF2' : (tf72T lam hlam).F (lamOf q (↑ρ₁.re : ℂ) - lamOf q ρ) =
      ∫ t in (0:ℝ)..(tf72T lam hlam).x₀,
        Real.exp ((lamOf q ρ - lamOf q (↑ρ₁.re : ℂ)) * t) * (tf72T lam hlam).f t := by
    rw [TestFn_F_eq_integral]
    exact intervalIntegral.integral_congr (fun t _ => by
      rw [show -((lamOf q (↑ρ₁.re : ℂ) - lamOf q ρ) * t)
        = (lamOf q ρ - lamOf q (↑ρ₁.re : ℂ)) * t by ring])
  have hF0 : (tf72T lam hlam).F 0 =
      ∫ t in (0:ℝ)..(tf72T lam hlam).x₀, (tf72T lam hlam).f t := by
    rw [TestFn_F_eq_integral]
    exact intervalIntegral.integral_congr (fun t _ => by
      rw [zero_mul, neg_zero, Real.exp_zero, one_mul])
  have hmain' : 0 ≤ 2 * (tf72T lam hlam).F (-(lamOf q ρ))
      - 2 * (tf72T lam hlam).F (lamOf q (↑ρ₁.re : ℂ) - lamOf q ρ)
      - (tf72T lam hlam).F 0 + (2 * c + 4 * eS6) * (tf72T lam hlam).f 0 := by
    rw [hF1, hF2', hF0]
    exact hmain
  have hlam_eq : lamOf q (↑ρ₁.re : ℂ) = lamOf q ρ₁ := by simp [lamOf, Complex.ofReal_re]
  rw [hlam_eq] at hmain'
  exact hmain'

/-! ## The test functions of the rows (HB Lemma 7.2 at the tabulated scales) -/

/-- HB Lemma 7.2's test function at scale `(23:ℝ)/10`. -/
def TM23 : TestFn := tf72T ((23:ℝ)/10) (by norm_num)

/-- HB Lemma 7.2's test function at scale `(47:ℝ)/20`. -/
def TM235 : TestFn := tf72T ((47:ℝ)/20) (by norm_num)

/-- HB Lemma 7.2's test function at scale `(12:ℝ)/5`. -/
def TM24 : TestFn := tf72T ((12:ℝ)/5) (by norm_num)

/-- HB Lemma 7.2's test function at scale `(49:ℝ)/20`. -/
def TM245 : TestFn := tf72T ((49:ℝ)/20) (by norm_num)

/-- HB Lemma 7.2's test function at scale `(5:ℝ)/2`. -/
def TM25 : TestFn := tf72T ((5:ℝ)/2) (by norm_num)

/-- HB Lemma 7.2's test function at scale `(51:ℝ)/20`. -/
def TM255 : TestFn := tf72T ((51:ℝ)/20) (by norm_num)

/-- HB Lemma 7.2's test function at scale `(13:ℝ)/5`. -/
def TM26 : TestFn := tf72T ((13:ℝ)/5) (by norm_num)

/-- HB Lemma 7.2's test function at scale `(53:ℝ)/20`. -/
def TM265 : TestFn := tf72T ((53:ℝ)/20) (by norm_num)

/-- HB Lemma 7.2's test function at scale `(27:ℝ)/10`. -/
def TM27 : TestFn := tf72T ((27:ℝ)/10) (by norm_num)

/-- HB Lemma 7.2's test function at scale `(11:ℝ)/4`. -/
def TM275 : TestFn := tf72T ((11:ℝ)/4) (by norm_num)

/-- HB Lemma 7.2's test function at scale `(14:ℝ)/5`. -/
def TM28 : TestFn := tf72T ((14:ℝ)/5) (by norm_num)

/-- HB Lemma 7.2's test function at scale `(57:ℝ)/20`. -/
def TM285 : TestFn := tf72T ((57:ℝ)/20) (by norm_num)

/-! ## The row certificates of Tables 2 and 3 -/

/-- Row 1 of the tables: `(λ, b, v) = ((23:ℝ)/10, (1:ℝ)/5, (33:ℝ)/10)`.
    The §6 inequality at scale `(23:ℝ)/10` fails at `(v,b)`, so `λ₁ ≤ (1:ℝ)/5` forces `λ(ρ) > (33:ℝ)/10`. -/
theorem rowCert_1 : 2 * (TM23.F (-((33:ℝ)/10)) - TM23.F ((1:ℝ)/5 - (33:ℝ)/10))
    < TM23.F 0 - TM23.f 0 * (252/1000) := by
  have hT : TM23 = tf72T ((23:ℝ)/10) (by norm_num) := rfl
  have h1 : TM23.F (-((33:ℝ)/10)) = hb72G (((33:ℝ)/10)/((23:ℝ)/10))/30 := by
    rw [hT, TF_eq_hb ((23:ℝ)/10) (by norm_num)]; norm_num
  have h2 : TM23.F ((1:ℝ)/5 - (33:ℝ)/10) = hb72G ((((33:ℝ)/10) - ((1:ℝ)/5))/((23:ℝ)/10))/30 := by
    rw [hT, TF_eq_hb ((23:ℝ)/10) (by norm_num)]; norm_num
  have h0 : TM23.F 0 = 8/9 := by
    rw [hT]; exact TF_zero ((23:ℝ)/10) (by norm_num)
  have hf : TM23.f 0 = 16*((23:ℝ)/10)/15 := by
    rw [hT]; exact TF_f0 ((23:ℝ)/10) (by norm_num)
  rw [h1, h2, h0, hf]
  rw [show ((33:ℝ)/10)/((23:ℝ)/10) = (33:ℝ)/23 by norm_num,
      show (((33:ℝ)/10) - ((1:ℝ)/5))/((23:ℝ)/10) = (31:ℝ)/23 by norm_num]
  rw [hb72G_closed (by norm_num : ((33:ℝ)/23) ≠ 0),
      hb72G_closed (by norm_num : ((31:ℝ)/23) ≠ 0)]
  rw [show 2 * ((33:ℝ)/23) = (66:ℝ)/23 by norm_num,
      show 2 * ((31:ℝ)/23) = (62:ℝ)/23 by norm_num]
  obtain ⟨hl1, hh1⟩ := exp_bounds_gen (x := (66:ℝ)/23)
    (lo := 17.6293505) (hi := 17.6293526) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨hl2, hh2⟩ := exp_bounds_gen (x := (62:ℝ)/23)
    (lo := 14.8151766) (hi := 14.8151787) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [hh1, hl2]

/-- Row 2 of the tables: `(λ, b, v) = ((47:ℝ)/20, (193:ℝ)/1000, (677:ℝ)/200)`.
    The §6 inequality at scale `(47:ℝ)/20` fails at `(v,b)`, so `λ₁ ≤ (193:ℝ)/1000` forces `λ(ρ) > (677:ℝ)/200`. -/
theorem rowCert_2 : 2 * (TM235.F (-((677:ℝ)/200)) - TM235.F ((193:ℝ)/1000 - (677:ℝ)/200))
    < TM235.F 0 - TM235.f 0 * (252/1000) := by
  have hT : TM235 = tf72T ((47:ℝ)/20) (by norm_num) := rfl
  have h1 : TM235.F (-((677:ℝ)/200)) = hb72G (((677:ℝ)/200)/((47:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((47:ℝ)/20) (by norm_num)]; norm_num
  have h2 : TM235.F ((193:ℝ)/1000 - (677:ℝ)/200) = hb72G ((((677:ℝ)/200) - ((193:ℝ)/1000))/((47:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((47:ℝ)/20) (by norm_num)]; norm_num
  have h0 : TM235.F 0 = 8/9 := by
    rw [hT]; exact TF_zero ((47:ℝ)/20) (by norm_num)
  have hf : TM235.f 0 = 16*((47:ℝ)/20)/15 := by
    rw [hT]; exact TF_f0 ((47:ℝ)/20) (by norm_num)
  rw [h1, h2, h0, hf]
  rw [show ((677:ℝ)/200)/((47:ℝ)/20) = (677:ℝ)/470 by norm_num,
      show (((677:ℝ)/200) - ((193:ℝ)/1000))/((47:ℝ)/20) = (1596:ℝ)/1175 by norm_num]
  rw [hb72G_closed (by norm_num : ((677:ℝ)/470) ≠ 0),
      hb72G_closed (by norm_num : ((1596:ℝ)/1175) ≠ 0)]
  rw [show 2 * ((677:ℝ)/470) = (677:ℝ)/235 by norm_num,
      show 2 * ((1596:ℝ)/1175) = (3192:ℝ)/1175 by norm_num]
  obtain ⟨hl1, hh1⟩ := exp_bounds_gen (x := (677:ℝ)/235)
    (lo := 17.8294397) (hi := 17.8294418) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨hl2, hh2⟩ := exp_bounds_gen (x := (3192:ℝ)/1175)
    (lo := 15.1287314) (hi := 15.1287335) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [hh1, hl2]

/-- Row 3 of the tables: `(λ, b, v) = ((47:ℝ)/20, (37:ℝ)/200, (697:ℝ)/200)`.
    The §6 inequality at scale `(47:ℝ)/20` fails at `(v,b)`, so `λ₁ ≤ (37:ℝ)/200` forces `λ(ρ) > (697:ℝ)/200`. -/
theorem rowCert_3 : 2 * (TM235.F (-((697:ℝ)/200)) - TM235.F ((37:ℝ)/200 - (697:ℝ)/200))
    < TM235.F 0 - TM235.f 0 * (252/1000) := by
  have hT : TM235 = tf72T ((47:ℝ)/20) (by norm_num) := rfl
  have h1 : TM235.F (-((697:ℝ)/200)) = hb72G (((697:ℝ)/200)/((47:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((47:ℝ)/20) (by norm_num)]; norm_num
  have h2 : TM235.F ((37:ℝ)/200 - (697:ℝ)/200) = hb72G ((((697:ℝ)/200) - ((37:ℝ)/200))/((47:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((47:ℝ)/20) (by norm_num)]; norm_num
  have h0 : TM235.F 0 = 8/9 := by
    rw [hT]; exact TF_zero ((47:ℝ)/20) (by norm_num)
  have hf : TM235.f 0 = 16*((47:ℝ)/20)/15 := by
    rw [hT]; exact TF_f0 ((47:ℝ)/20) (by norm_num)
  rw [h1, h2, h0, hf]
  rw [show ((697:ℝ)/200)/((47:ℝ)/20) = (697:ℝ)/470 by norm_num,
      show (((697:ℝ)/200) - ((37:ℝ)/200))/((47:ℝ)/20) = (66:ℝ)/47 by norm_num]
  rw [hb72G_closed (by norm_num : ((697:ℝ)/470) ≠ 0),
      hb72G_closed (by norm_num : ((66:ℝ)/47) ≠ 0)]
  rw [show 2 * ((697:ℝ)/470) = (697:ℝ)/235 by norm_num,
      show 2 * ((66:ℝ)/47) = (132:ℝ)/47 by norm_num]
  obtain ⟨hl1, hh1⟩ := exp_bounds_gen (x := (697:ℝ)/235)
    (lo := 19.4132805) (hi := 19.4132826) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨hl2, hh2⟩ := exp_bounds_gen (x := (132:ℝ)/47)
    (lo := 16.5851974) (hi := 16.5851995) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [hh1, hl2]

/-- Row 4 of the tables: `(λ, b, v) = ((47:ℝ)/20, (22:ℝ)/125, (359:ℝ)/100)`.
    The §6 inequality at scale `(47:ℝ)/20` fails at `(v,b)`, so `λ₁ ≤ (22:ℝ)/125` forces `λ(ρ) > (359:ℝ)/100`. -/
theorem rowCert_4 : 2 * (TM235.F (-((359:ℝ)/100)) - TM235.F ((22:ℝ)/125 - (359:ℝ)/100))
    < TM235.F 0 - TM235.f 0 * (252/1000) := by
  have hT : TM235 = tf72T ((47:ℝ)/20) (by norm_num) := rfl
  have h1 : TM235.F (-((359:ℝ)/100)) = hb72G (((359:ℝ)/100)/((47:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((47:ℝ)/20) (by norm_num)]; norm_num
  have h2 : TM235.F ((22:ℝ)/125 - (359:ℝ)/100) = hb72G ((((359:ℝ)/100) - ((22:ℝ)/125))/((47:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((47:ℝ)/20) (by norm_num)]; norm_num
  have h0 : TM235.F 0 = 8/9 := by
    rw [hT]; exact TF_zero ((47:ℝ)/20) (by norm_num)
  have hf : TM235.f 0 = 16*((47:ℝ)/20)/15 := by
    rw [hT]; exact TF_f0 ((47:ℝ)/20) (by norm_num)
  rw [h1, h2, h0, hf]
  rw [show ((359:ℝ)/100)/((47:ℝ)/20) = (359:ℝ)/235 by norm_num,
      show (((359:ℝ)/100) - ((22:ℝ)/125))/((47:ℝ)/20) = (1707:ℝ)/1175 by norm_num]
  rw [hb72G_closed (by norm_num : ((359:ℝ)/235) ≠ 0),
      hb72G_closed (by norm_num : ((1707:ℝ)/1175) ≠ 0)]
  rw [show 2 * ((359:ℝ)/235) = (718:ℝ)/235 by norm_num,
      show 2 * ((1707:ℝ)/1175) = (3414:ℝ)/1175 by norm_num]
  obtain ⟨hl1, hh1⟩ := exp_bounds_gen (x := (718:ℝ)/235)
    (lo := 21.2279583) (hi := 21.2279604) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨hl2, hh2⟩ := exp_bounds_gen (x := (3414:ℝ)/1175)
    (lo := 18.2749607) (hi := 18.2749628) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [hh1, hl2]

/-- Row 5 of the tables: `(λ, b, v) = ((47:ℝ)/20, (167:ℝ)/1000, (3713:ℝ)/1000)`.
    The §6 inequality at scale `(47:ℝ)/20` fails at `(v,b)`, so `λ₁ ≤ (167:ℝ)/1000` forces `λ(ρ) > (3713:ℝ)/1000`. -/
theorem rowCert_5 : 2 * (TM235.F (-((3713:ℝ)/1000)) - TM235.F ((167:ℝ)/1000 - (3713:ℝ)/1000))
    < TM235.F 0 - TM235.f 0 * (252/1000) := by
  have hT : TM235 = tf72T ((47:ℝ)/20) (by norm_num) := rfl
  have h1 : TM235.F (-((3713:ℝ)/1000)) = hb72G (((3713:ℝ)/1000)/((47:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((47:ℝ)/20) (by norm_num)]; norm_num
  have h2 : TM235.F ((167:ℝ)/1000 - (3713:ℝ)/1000) = hb72G ((((3713:ℝ)/1000) - ((167:ℝ)/1000))/((47:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((47:ℝ)/20) (by norm_num)]; norm_num
  have h0 : TM235.F 0 = 8/9 := by
    rw [hT]; exact TF_zero ((47:ℝ)/20) (by norm_num)
  have hf : TM235.f 0 = 16*((47:ℝ)/20)/15 := by
    rw [hT]; exact TF_f0 ((47:ℝ)/20) (by norm_num)
  rw [h1, h2, h0, hf]
  rw [show ((3713:ℝ)/1000)/((47:ℝ)/20) = (79:ℝ)/50 by norm_num,
      show (((3713:ℝ)/1000) - ((167:ℝ)/1000))/((47:ℝ)/20) = (1773:ℝ)/1175 by norm_num]
  rw [hb72G_closed (by norm_num : ((79:ℝ)/50) ≠ 0),
      hb72G_closed (by norm_num : ((1773:ℝ)/1175) ≠ 0)]
  rw [show 2 * ((79:ℝ)/50) = (79:ℝ)/25 by norm_num,
      show 2 * ((1773:ℝ)/1175) = (3546:ℝ)/1175 by norm_num]
  obtain ⟨hl1, hh1⟩ := exp_bounds_gen (x := (79:ℝ)/25)
    (lo := 23.5705949) (hi := 23.5705970) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨hl2, hh2⟩ := exp_bounds_gen (x := (3546:ℝ)/1175)
    (lo := 20.4477385) (hi := 20.4477406) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [hh1, hl2]

/-- Row 6 of the tables: `(λ, b, v) = ((12:ℝ)/5, (157:ℝ)/1000, (1929:ℝ)/500)`.
    The §6 inequality at scale `(12:ℝ)/5` fails at `(v,b)`, so `λ₁ ≤ (157:ℝ)/1000` forces `λ(ρ) > (1929:ℝ)/500`. -/
theorem rowCert_6 : 2 * (TM24.F (-((1929:ℝ)/500)) - TM24.F ((157:ℝ)/1000 - (1929:ℝ)/500))
    < TM24.F 0 - TM24.f 0 * (252/1000) := by
  have hT : TM24 = tf72T ((12:ℝ)/5) (by norm_num) := rfl
  have h1 : TM24.F (-((1929:ℝ)/500)) = hb72G (((1929:ℝ)/500)/((12:ℝ)/5))/30 := by
    rw [hT, TF_eq_hb ((12:ℝ)/5) (by norm_num)]; norm_num
  have h2 : TM24.F ((157:ℝ)/1000 - (1929:ℝ)/500) = hb72G ((((1929:ℝ)/500) - ((157:ℝ)/1000))/((12:ℝ)/5))/30 := by
    rw [hT, TF_eq_hb ((12:ℝ)/5) (by norm_num)]; norm_num
  have h0 : TM24.F 0 = 8/9 := by
    rw [hT]; exact TF_zero ((12:ℝ)/5) (by norm_num)
  have hf : TM24.f 0 = 16*((12:ℝ)/5)/15 := by
    rw [hT]; exact TF_f0 ((12:ℝ)/5) (by norm_num)
  rw [h1, h2, h0, hf]
  rw [show ((1929:ℝ)/500)/((12:ℝ)/5) = (643:ℝ)/400 by norm_num,
      show (((1929:ℝ)/500) - ((157:ℝ)/1000))/((12:ℝ)/5) = (3701:ℝ)/2400 by norm_num]
  rw [hb72G_closed (by norm_num : ((643:ℝ)/400) ≠ 0),
      hb72G_closed (by norm_num : ((3701:ℝ)/2400) ≠ 0)]
  rw [show 2 * ((643:ℝ)/400) = (643:ℝ)/200 by norm_num,
      show 2 * ((3701:ℝ)/2400) = (3701:ℝ)/1200 by norm_num]
  obtain ⟨hl1, hh1⟩ := exp_bounds_gen (x := (643:ℝ)/200)
    (lo := 24.9032909) (hi := 24.9032930) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨hl2, hh2⟩ := exp_bounds_gen (x := (3701:ℝ)/1200)
    (lo := 21.8492505) (hi := 21.8492526) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [hh1, hl2]

/-- Row 7 of the tables: `(λ, b, v) = ((12:ℝ)/5, (73:ℝ)/500, (403:ℝ)/100)`.
    The §6 inequality at scale `(12:ℝ)/5` fails at `(v,b)`, so `λ₁ ≤ (73:ℝ)/500` forces `λ(ρ) > (403:ℝ)/100`. -/
theorem rowCert_7 : 2 * (TM24.F (-((403:ℝ)/100)) - TM24.F ((73:ℝ)/500 - (403:ℝ)/100))
    < TM24.F 0 - TM24.f 0 * (252/1000) := by
  have hT : TM24 = tf72T ((12:ℝ)/5) (by norm_num) := rfl
  have h1 : TM24.F (-((403:ℝ)/100)) = hb72G (((403:ℝ)/100)/((12:ℝ)/5))/30 := by
    rw [hT, TF_eq_hb ((12:ℝ)/5) (by norm_num)]; norm_num
  have h2 : TM24.F ((73:ℝ)/500 - (403:ℝ)/100) = hb72G ((((403:ℝ)/100) - ((73:ℝ)/500))/((12:ℝ)/5))/30 := by
    rw [hT, TF_eq_hb ((12:ℝ)/5) (by norm_num)]; norm_num
  have h0 : TM24.F 0 = 8/9 := by
    rw [hT]; exact TF_zero ((12:ℝ)/5) (by norm_num)
  have hf : TM24.f 0 = 16*((12:ℝ)/5)/15 := by
    rw [hT]; exact TF_f0 ((12:ℝ)/5) (by norm_num)
  rw [h1, h2, h0, hf]
  rw [show ((403:ℝ)/100)/((12:ℝ)/5) = (403:ℝ)/240 by norm_num,
      show (((403:ℝ)/100) - ((73:ℝ)/500))/((12:ℝ)/5) = (971:ℝ)/600 by norm_num]
  rw [hb72G_closed (by norm_num : ((403:ℝ)/240) ≠ 0),
      hb72G_closed (by norm_num : ((971:ℝ)/600) ≠ 0)]
  rw [show 2 * ((403:ℝ)/240) = (403:ℝ)/120 by norm_num,
      show 2 * ((971:ℝ)/600) = (971:ℝ)/300 by norm_num]
  obtain ⟨hl1, hh1⟩ := exp_bounds_gen (x := (403:ℝ)/120)
    (lo := 28.7412478) (hi := 28.7412499) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨hl2, hh2⟩ := exp_bounds_gen (x := (971:ℝ)/300)
    (lo := 25.4487500) (hi := 25.4487521) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [hh1, hl2]

/-- Row 8 of the tables: `(λ, b, v) = ((49:ℝ)/20, (67:ℝ)/500, (4217:ℝ)/1000)`.
    The §6 inequality at scale `(49:ℝ)/20` fails at `(v,b)`, so `λ₁ ≤ (67:ℝ)/500` forces `λ(ρ) > (4217:ℝ)/1000`. -/
theorem rowCert_8 : 2 * (TM245.F (-((4217:ℝ)/1000)) - TM245.F ((67:ℝ)/500 - (4217:ℝ)/1000))
    < TM245.F 0 - TM245.f 0 * (252/1000) := by
  have hT : TM245 = tf72T ((49:ℝ)/20) (by norm_num) := rfl
  have h1 : TM245.F (-((4217:ℝ)/1000)) = hb72G (((4217:ℝ)/1000)/((49:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((49:ℝ)/20) (by norm_num)]; norm_num
  have h2 : TM245.F ((67:ℝ)/500 - (4217:ℝ)/1000) = hb72G ((((4217:ℝ)/1000) - ((67:ℝ)/500))/((49:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((49:ℝ)/20) (by norm_num)]; norm_num
  have h0 : TM245.F 0 = 8/9 := by
    rw [hT]; exact TF_zero ((49:ℝ)/20) (by norm_num)
  have hf : TM245.f 0 = 16*((49:ℝ)/20)/15 := by
    rw [hT]; exact TF_f0 ((49:ℝ)/20) (by norm_num)
  rw [h1, h2, h0, hf]
  rw [show ((4217:ℝ)/1000)/((49:ℝ)/20) = (4217:ℝ)/2450 by norm_num,
      show (((4217:ℝ)/1000) - ((67:ℝ)/500))/((49:ℝ)/20) = (4083:ℝ)/2450 by norm_num]
  rw [hb72G_closed (by norm_num : ((4217:ℝ)/2450) ≠ 0),
      hb72G_closed (by norm_num : ((4083:ℝ)/2450) ≠ 0)]
  rw [show 2 * ((4217:ℝ)/2450) = (4217:ℝ)/1225 by norm_num,
      show 2 * ((4083:ℝ)/2450) = (4083:ℝ)/1225 by norm_num]
  obtain ⟨hl1, hh1⟩ := exp_bounds_gen (x := (4217:ℝ)/1225)
    (lo := 31.2634269) (hi := 31.2634290) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨hl2, hh2⟩ := exp_bounds_gen (x := (4083:ℝ)/1225)
    (lo := 28.0239972) (hi := 28.0239993) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [hh1, hl2]

/-- Row 9 of the tables: `(λ, b, v) = ((49:ℝ)/20, (61:ℝ)/500, (4443:ℝ)/1000)`.
    The §6 inequality at scale `(49:ℝ)/20` fails at `(v,b)`, so `λ₁ ≤ (61:ℝ)/500` forces `λ(ρ) > (4443:ℝ)/1000`. -/
theorem rowCert_9 : 2 * (TM245.F (-((4443:ℝ)/1000)) - TM245.F ((61:ℝ)/500 - (4443:ℝ)/1000))
    < TM245.F 0 - TM245.f 0 * (252/1000) := by
  have hT : TM245 = tf72T ((49:ℝ)/20) (by norm_num) := rfl
  have h1 : TM245.F (-((4443:ℝ)/1000)) = hb72G (((4443:ℝ)/1000)/((49:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((49:ℝ)/20) (by norm_num)]; norm_num
  have h2 : TM245.F ((61:ℝ)/500 - (4443:ℝ)/1000) = hb72G ((((4443:ℝ)/1000) - ((61:ℝ)/500))/((49:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((49:ℝ)/20) (by norm_num)]; norm_num
  have h0 : TM245.F 0 = 8/9 := by
    rw [hT]; exact TF_zero ((49:ℝ)/20) (by norm_num)
  have hf : TM245.f 0 = 16*((49:ℝ)/20)/15 := by
    rw [hT]; exact TF_f0 ((49:ℝ)/20) (by norm_num)
  rw [h1, h2, h0, hf]
  rw [show ((4443:ℝ)/1000)/((49:ℝ)/20) = (4443:ℝ)/2450 by norm_num,
      show (((4443:ℝ)/1000) - ((61:ℝ)/500))/((49:ℝ)/20) = (4321:ℝ)/2450 by norm_num]
  rw [hb72G_closed (by norm_num : ((4443:ℝ)/2450) ≠ 0),
      hb72G_closed (by norm_num : ((4321:ℝ)/2450) ≠ 0)]
  rw [show 2 * ((4443:ℝ)/2450) = (4443:ℝ)/1225 by norm_num,
      show 2 * ((4321:ℝ)/2450) = (4321:ℝ)/1225 by norm_num]
  obtain ⟨hl1, hh1⟩ := exp_bounds_gen (x := (4443:ℝ)/1225)
    (lo := 37.5975447) (hi := 37.5975468) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨hl2, hh2⟩ := exp_bounds_gen (x := (4321:ℝ)/1225)
    (lo := 34.0335536) (hi := 34.0335557) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [hh1, hl2]

/-- Row 10 of the tables: `(λ, b, v) = ((49:ℝ)/20, (109:ℝ)/1000, (4697:ℝ)/1000)`.
    The §6 inequality at scale `(49:ℝ)/20` fails at `(v,b)`, so `λ₁ ≤ (109:ℝ)/1000` forces `λ(ρ) > (4697:ℝ)/1000`. -/
theorem rowCert_10 : 2 * (TM245.F (-((4697:ℝ)/1000)) - TM245.F ((109:ℝ)/1000 - (4697:ℝ)/1000))
    < TM245.F 0 - TM245.f 0 * (252/1000) := by
  have hT : TM245 = tf72T ((49:ℝ)/20) (by norm_num) := rfl
  have h1 : TM245.F (-((4697:ℝ)/1000)) = hb72G (((4697:ℝ)/1000)/((49:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((49:ℝ)/20) (by norm_num)]; norm_num
  have h2 : TM245.F ((109:ℝ)/1000 - (4697:ℝ)/1000) = hb72G ((((4697:ℝ)/1000) - ((109:ℝ)/1000))/((49:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((49:ℝ)/20) (by norm_num)]; norm_num
  have h0 : TM245.F 0 = 8/9 := by
    rw [hT]; exact TF_zero ((49:ℝ)/20) (by norm_num)
  have hf : TM245.f 0 = 16*((49:ℝ)/20)/15 := by
    rw [hT]; exact TF_f0 ((49:ℝ)/20) (by norm_num)
  rw [h1, h2, h0, hf]
  rw [show ((4697:ℝ)/1000)/((49:ℝ)/20) = (671:ℝ)/350 by norm_num,
      show (((4697:ℝ)/1000) - ((109:ℝ)/1000))/((49:ℝ)/20) = (2294:ℝ)/1225 by norm_num]
  rw [hb72G_closed (by norm_num : ((671:ℝ)/350) ≠ 0),
      hb72G_closed (by norm_num : ((2294:ℝ)/1225) ≠ 0)]
  rw [show 2 * ((671:ℝ)/350) = (671:ℝ)/175 by norm_num,
      show 2 * ((2294:ℝ)/1225) = (4588:ℝ)/1225 by norm_num]
  obtain ⟨hl1, hh1⟩ := exp_bounds_gen (x := (671:ℝ)/175)
    (lo := 46.2603717) (hi := 46.2603738) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨hl2, hh2⟩ := exp_bounds_gen (x := (4588:ℝ)/1225)
    (lo := 42.3219599) (hi := 42.3219620) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [hh1, hl2]

/-- Row 11 of the tables: `(λ, b, v) = ((5:ℝ)/2, (12:ℝ)/125, (1247:ℝ)/250)`.
    The §6 inequality at scale `(5:ℝ)/2` fails at `(v,b)`, so `λ₁ ≤ (12:ℝ)/125` forces `λ(ρ) > (1247:ℝ)/250`. -/
theorem rowCert_11 : 2 * (TM25.F (-((1247:ℝ)/250)) - TM25.F ((12:ℝ)/125 - (1247:ℝ)/250))
    < TM25.F 0 - TM25.f 0 * (252/1000) := by
  have hT : TM25 = tf72T ((5:ℝ)/2) (by norm_num) := rfl
  have h1 : TM25.F (-((1247:ℝ)/250)) = hb72G (((1247:ℝ)/250)/((5:ℝ)/2))/30 := by
    rw [hT, TF_eq_hb ((5:ℝ)/2) (by norm_num)]; norm_num
  have h2 : TM25.F ((12:ℝ)/125 - (1247:ℝ)/250) = hb72G ((((1247:ℝ)/250) - ((12:ℝ)/125))/((5:ℝ)/2))/30 := by
    rw [hT, TF_eq_hb ((5:ℝ)/2) (by norm_num)]; norm_num
  have h0 : TM25.F 0 = 8/9 := by
    rw [hT]; exact TF_zero ((5:ℝ)/2) (by norm_num)
  have hf : TM25.f 0 = 16*((5:ℝ)/2)/15 := by
    rw [hT]; exact TF_f0 ((5:ℝ)/2) (by norm_num)
  rw [h1, h2, h0, hf]
  rw [show ((1247:ℝ)/250)/((5:ℝ)/2) = (1247:ℝ)/625 by norm_num,
      show (((1247:ℝ)/250) - ((12:ℝ)/125))/((5:ℝ)/2) = (1223:ℝ)/625 by norm_num]
  rw [hb72G_closed (by norm_num : ((1247:ℝ)/625) ≠ 0),
      hb72G_closed (by norm_num : ((1223:ℝ)/625) ≠ 0)]
  rw [show 2 * ((1247:ℝ)/625) = (2494:ℝ)/625 by norm_num,
      show 2 * ((1223:ℝ)/625) = (2446:ℝ)/625 by norm_num]
  obtain ⟨hl1, hh1⟩ := exp_bounds_gen (x := (2494:ℝ)/625)
    (lo := 54.0765146) (hi := 54.0765167) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨hl2, hh2⟩ := exp_bounds_gen (x := (2446:ℝ)/625)
    (lo := 50.0789109) (hi := 50.0789130) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [hh1, hl2]

/-- Row 12 of the tables: `(λ, b, v) = ((51:ℝ)/20, (83:ℝ)/1000, (5329:ℝ)/1000)`.
    The §6 inequality at scale `(51:ℝ)/20` fails at `(v,b)`, so `λ₁ ≤ (83:ℝ)/1000` forces `λ(ρ) > (5329:ℝ)/1000`. -/
theorem rowCert_12 : 2 * (TM255.F (-((5329:ℝ)/1000)) - TM255.F ((83:ℝ)/1000 - (5329:ℝ)/1000))
    < TM255.F 0 - TM255.f 0 * (252/1000) := by
  have hT : TM255 = tf72T ((51:ℝ)/20) (by norm_num) := rfl
  have h1 : TM255.F (-((5329:ℝ)/1000)) = hb72G (((5329:ℝ)/1000)/((51:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((51:ℝ)/20) (by norm_num)]; norm_num
  have h2 : TM255.F ((83:ℝ)/1000 - (5329:ℝ)/1000) = hb72G ((((5329:ℝ)/1000) - ((83:ℝ)/1000))/((51:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((51:ℝ)/20) (by norm_num)]; norm_num
  have h0 : TM255.F 0 = 8/9 := by
    rw [hT]; exact TF_zero ((51:ℝ)/20) (by norm_num)
  have hf : TM255.f 0 = 16*((51:ℝ)/20)/15 := by
    rw [hT]; exact TF_f0 ((51:ℝ)/20) (by norm_num)
  rw [h1, h2, h0, hf]
  rw [show ((5329:ℝ)/1000)/((51:ℝ)/20) = (5329:ℝ)/2550 by norm_num,
      show (((5329:ℝ)/1000) - ((83:ℝ)/1000))/((51:ℝ)/20) = (2623:ℝ)/1275 by norm_num]
  rw [hb72G_closed (by norm_num : ((5329:ℝ)/2550) ≠ 0),
      hb72G_closed (by norm_num : ((2623:ℝ)/1275) ≠ 0)]
  rw [show 2 * ((5329:ℝ)/2550) = (5329:ℝ)/1275 by norm_num,
      show 2 * ((2623:ℝ)/1275) = (5246:ℝ)/1275 by norm_num]
  obtain ⟨hl1, hh1⟩ := exp_bounds_gen (x := (5329:ℝ)/1275)
    (lo := 65.3402235) (hi := 65.3402256) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨hl2, hh2⟩ := exp_bounds_gen (x := (5246:ℝ)/1275)
    (lo := 61.2221950) (hi := 61.2221971) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [hh1, hl2]

/-- Row 13 of the tables: `(λ, b, v) = ((51:ℝ)/20, (7:ℝ)/100, (1141:ℝ)/200)`.
    The §6 inequality at scale `(51:ℝ)/20` fails at `(v,b)`, so `λ₁ ≤ (7:ℝ)/100` forces `λ(ρ) > (1141:ℝ)/200`. -/
theorem rowCert_13 : 2 * (TM255.F (-((1141:ℝ)/200)) - TM255.F ((7:ℝ)/100 - (1141:ℝ)/200))
    < TM255.F 0 - TM255.f 0 * (252/1000) := by
  have hT : TM255 = tf72T ((51:ℝ)/20) (by norm_num) := rfl
  have h1 : TM255.F (-((1141:ℝ)/200)) = hb72G (((1141:ℝ)/200)/((51:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((51:ℝ)/20) (by norm_num)]; norm_num
  have h2 : TM255.F ((7:ℝ)/100 - (1141:ℝ)/200) = hb72G ((((1141:ℝ)/200) - ((7:ℝ)/100))/((51:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((51:ℝ)/20) (by norm_num)]; norm_num
  have h0 : TM255.F 0 = 8/9 := by
    rw [hT]; exact TF_zero ((51:ℝ)/20) (by norm_num)
  have hf : TM255.f 0 = 16*((51:ℝ)/20)/15 := by
    rw [hT]; exact TF_f0 ((51:ℝ)/20) (by norm_num)
  rw [h1, h2, h0, hf]
  rw [show ((1141:ℝ)/200)/((51:ℝ)/20) = (1141:ℝ)/510 by norm_num,
      show (((1141:ℝ)/200) - ((7:ℝ)/100))/((51:ℝ)/20) = (1127:ℝ)/510 by norm_num]
  rw [hb72G_closed (by norm_num : ((1141:ℝ)/510) ≠ 0),
      hb72G_closed (by norm_num : ((1127:ℝ)/510) ≠ 0)]
  rw [show 2 * ((1141:ℝ)/510) = (1141:ℝ)/255 by norm_num,
      show 2 * ((1127:ℝ)/510) = (1127:ℝ)/255 by norm_num]
  obtain ⟨hl1, hh1⟩ := exp_bounds_gen (x := (1141:ℝ)/255)
    (lo := 87.7515733) (hi := 87.7515754) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨hl2, hh2⟩ := exp_bounds_gen (x := (1127:ℝ)/255)
    (lo := 83.0637039) (hi := 83.0637060) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [hh1, hl2]

/-- Row 14 of the tables: `(λ, b, v) = ((13:ℝ)/5, (29:ℝ)/500, (771:ℝ)/125)`.
    The §6 inequality at scale `(13:ℝ)/5` fails at `(v,b)`, so `λ₁ ≤ (29:ℝ)/500` forces `λ(ρ) > (771:ℝ)/125`. -/
theorem rowCert_14 : 2 * (TM26.F (-((771:ℝ)/125)) - TM26.F ((29:ℝ)/500 - (771:ℝ)/125))
    < TM26.F 0 - TM26.f 0 * (252/1000) := by
  have hT : TM26 = tf72T ((13:ℝ)/5) (by norm_num) := rfl
  have h1 : TM26.F (-((771:ℝ)/125)) = hb72G (((771:ℝ)/125)/((13:ℝ)/5))/30 := by
    rw [hT, TF_eq_hb ((13:ℝ)/5) (by norm_num)]; norm_num
  have h2 : TM26.F ((29:ℝ)/500 - (771:ℝ)/125) = hb72G ((((771:ℝ)/125) - ((29:ℝ)/500))/((13:ℝ)/5))/30 := by
    rw [hT, TF_eq_hb ((13:ℝ)/5) (by norm_num)]; norm_num
  have h0 : TM26.F 0 = 8/9 := by
    rw [hT]; exact TF_zero ((13:ℝ)/5) (by norm_num)
  have hf : TM26.f 0 = 16*((13:ℝ)/5)/15 := by
    rw [hT]; exact TF_f0 ((13:ℝ)/5) (by norm_num)
  rw [h1, h2, h0, hf]
  rw [show ((771:ℝ)/125)/((13:ℝ)/5) = (771:ℝ)/325 by norm_num,
      show (((771:ℝ)/125) - ((29:ℝ)/500))/((13:ℝ)/5) = (47:ℝ)/20 by norm_num]
  rw [hb72G_closed (by norm_num : ((771:ℝ)/325) ≠ 0),
      hb72G_closed (by norm_num : ((47:ℝ)/20) ≠ 0)]
  rw [show 2 * ((771:ℝ)/325) = (1542:ℝ)/325 by norm_num,
      show 2 * ((47:ℝ)/20) = (47:ℝ)/10 by norm_num]
  obtain ⟨hl1, hh1⟩ := exp_bounds_gen (x := (1542:ℝ)/325)
    (lo := 114.9635792) (hi := 114.9635813) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨hl2, hh2⟩ := exp_bounds_gen (x := (47:ℝ)/10)
    (lo := 109.9471714) (hi := 109.9471735) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [hh1, hl2]

/-- Row 15 of the tables: `(λ, b, v) = ((53:ℝ)/20, (23:ℝ)/500, (3329:ℝ)/500)`.
    The §6 inequality at scale `(53:ℝ)/20` fails at `(v,b)`, so `λ₁ ≤ (23:ℝ)/500` forces `λ(ρ) > (3329:ℝ)/500`. -/
theorem rowCert_15 : 2 * (TM265.F (-((3329:ℝ)/500)) - TM265.F ((23:ℝ)/500 - (3329:ℝ)/500))
    < TM265.F 0 - TM265.f 0 * (252/1000) := by
  have hT : TM265 = tf72T ((53:ℝ)/20) (by norm_num) := rfl
  have h1 : TM265.F (-((3329:ℝ)/500)) = hb72G (((3329:ℝ)/500)/((53:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((53:ℝ)/20) (by norm_num)]; norm_num
  have h2 : TM265.F ((23:ℝ)/500 - (3329:ℝ)/500) = hb72G ((((3329:ℝ)/500) - ((23:ℝ)/500))/((53:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((53:ℝ)/20) (by norm_num)]; norm_num
  have h0 : TM265.F 0 = 8/9 := by
    rw [hT]; exact TF_zero ((53:ℝ)/20) (by norm_num)
  have hf : TM265.f 0 = 16*((53:ℝ)/20)/15 := by
    rw [hT]; exact TF_f0 ((53:ℝ)/20) (by norm_num)
  rw [h1, h2, h0, hf]
  rw [show ((3329:ℝ)/500)/((53:ℝ)/20) = (3329:ℝ)/1325 by norm_num,
      show (((3329:ℝ)/500) - ((23:ℝ)/500))/((53:ℝ)/20) = (3306:ℝ)/1325 by norm_num]
  rw [hb72G_closed (by norm_num : ((3329:ℝ)/1325) ≠ 0),
      hb72G_closed (by norm_num : ((3306:ℝ)/1325) ≠ 0)]
  rw [show 2 * ((3329:ℝ)/1325) = (6658:ℝ)/1325 by norm_num,
      show 2 * ((3306:ℝ)/1325) = (6612:ℝ)/1325 by norm_num]
  obtain ⟨hl1, hh1⟩ := exp_bounds_gen (x := (6658:ℝ)/1325)
    (lo := 152.1559001) (hi := 152.1559022) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨hl2, hh2⟩ := exp_bounds_gen (x := (6612:ℝ)/1325)
    (lo := 146.9641489) (hi := 146.9641510) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [hh1, hl2]

/-- Row 16 of the tables: `(λ, b, v) = ((53:ℝ)/20, (9:ℝ)/250, (3617:ℝ)/500)`.
    The §6 inequality at scale `(53:ℝ)/20` fails at `(v,b)`, so `λ₁ ≤ (9:ℝ)/250` forces `λ(ρ) > (3617:ℝ)/500`. -/
theorem rowCert_16 : 2 * (TM265.F (-((3617:ℝ)/500)) - TM265.F ((9:ℝ)/250 - (3617:ℝ)/500))
    < TM265.F 0 - TM265.f 0 * (252/1000) := by
  have hT : TM265 = tf72T ((53:ℝ)/20) (by norm_num) := rfl
  have h1 : TM265.F (-((3617:ℝ)/500)) = hb72G (((3617:ℝ)/500)/((53:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((53:ℝ)/20) (by norm_num)]; norm_num
  have h2 : TM265.F ((9:ℝ)/250 - (3617:ℝ)/500) = hb72G ((((3617:ℝ)/500) - ((9:ℝ)/250))/((53:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((53:ℝ)/20) (by norm_num)]; norm_num
  have h0 : TM265.F 0 = 8/9 := by
    rw [hT]; exact TF_zero ((53:ℝ)/20) (by norm_num)
  have hf : TM265.f 0 = 16*((53:ℝ)/20)/15 := by
    rw [hT]; exact TF_f0 ((53:ℝ)/20) (by norm_num)
  rw [h1, h2, h0, hf]
  rw [show ((3617:ℝ)/500)/((53:ℝ)/20) = (3617:ℝ)/1325 by norm_num,
      show (((3617:ℝ)/500) - ((9:ℝ)/250))/((53:ℝ)/20) = (3599:ℝ)/1325 by norm_num]
  rw [hb72G_closed (by norm_num : ((3617:ℝ)/1325) ≠ 0),
      hb72G_closed (by norm_num : ((3599:ℝ)/1325) ≠ 0)]
  rw [show 2 * ((3617:ℝ)/1325) = (7234:ℝ)/1325 by norm_num,
      show 2 * ((3599:ℝ)/1325) = (7198:ℝ)/1325 by norm_num]
  obtain ⟨hl1, hh1⟩ := exp_bounds_gen (x := (7234:ℝ)/1325)
    (lo := 235.0087240) (hi := 235.0087261) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨hl2, hh2⟩ := exp_bounds_gen (x := (7198:ℝ)/1325)
    (lo := 228.7095426) (hi := 228.7095447) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [hh1, hl2]

/-- Row 17 of the tables: `(λ, b, v) = ((27:ℝ)/10, (27:ℝ)/1000, (3917:ℝ)/500)`.
    The §6 inequality at scale `(27:ℝ)/10` fails at `(v,b)`, so `λ₁ ≤ (27:ℝ)/1000` forces `λ(ρ) > (3917:ℝ)/500`. -/
theorem rowCert_17 : 2 * (TM27.F (-((3917:ℝ)/500)) - TM27.F ((27:ℝ)/1000 - (3917:ℝ)/500))
    < TM27.F 0 - TM27.f 0 * (252/1000) := by
  have hT : TM27 = tf72T ((27:ℝ)/10) (by norm_num) := rfl
  have h1 : TM27.F (-((3917:ℝ)/500)) = hb72G (((3917:ℝ)/500)/((27:ℝ)/10))/30 := by
    rw [hT, TF_eq_hb ((27:ℝ)/10) (by norm_num)]; norm_num
  have h2 : TM27.F ((27:ℝ)/1000 - (3917:ℝ)/500) = hb72G ((((3917:ℝ)/500) - ((27:ℝ)/1000))/((27:ℝ)/10))/30 := by
    rw [hT, TF_eq_hb ((27:ℝ)/10) (by norm_num)]; norm_num
  have h0 : TM27.F 0 = 8/9 := by
    rw [hT]; exact TF_zero ((27:ℝ)/10) (by norm_num)
  have hf : TM27.f 0 = 16*((27:ℝ)/10)/15 := by
    rw [hT]; exact TF_f0 ((27:ℝ)/10) (by norm_num)
  rw [h1, h2, h0, hf]
  rw [show ((3917:ℝ)/500)/((27:ℝ)/10) = (3917:ℝ)/1350 by norm_num,
      show (((3917:ℝ)/500) - ((27:ℝ)/1000))/((27:ℝ)/10) = (7807:ℝ)/2700 by norm_num]
  rw [hb72G_closed (by norm_num : ((3917:ℝ)/1350) ≠ 0),
      hb72G_closed (by norm_num : ((7807:ℝ)/2700) ≠ 0)]
  rw [show 2 * ((3917:ℝ)/1350) = (3917:ℝ)/675 by norm_num,
      show 2 * ((7807:ℝ)/2700) = (7807:ℝ)/1350 by norm_num]
  obtain ⟨hl1, hh1⟩ := exp_bounds_gen (x := (3917:ℝ)/675)
    (lo := 331.2796755) (hi := 331.2796776) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨hl2, hh2⟩ := exp_bounds_gen (x := (7807:ℝ)/1350)
    (lo := 324.7198984) (hi := 324.7199005) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [hh1, hl2]

/-- Row 18 of the tables: `(λ, b, v) = ((11:ℝ)/4, (1:ℝ)/50, (8547:ℝ)/1000)`.
    The §6 inequality at scale `(11:ℝ)/4` fails at `(v,b)`, so `λ₁ ≤ (1:ℝ)/50` forces `λ(ρ) > (8547:ℝ)/1000`. -/
theorem rowCert_18 : 2 * (TM275.F (-((8547:ℝ)/1000)) - TM275.F ((1:ℝ)/50 - (8547:ℝ)/1000))
    < TM275.F 0 - TM275.f 0 * (252/1000) := by
  have hT : TM275 = tf72T ((11:ℝ)/4) (by norm_num) := rfl
  have h1 : TM275.F (-((8547:ℝ)/1000)) = hb72G (((8547:ℝ)/1000)/((11:ℝ)/4))/30 := by
    rw [hT, TF_eq_hb ((11:ℝ)/4) (by norm_num)]; norm_num
  have h2 : TM275.F ((1:ℝ)/50 - (8547:ℝ)/1000) = hb72G ((((8547:ℝ)/1000) - ((1:ℝ)/50))/((11:ℝ)/4))/30 := by
    rw [hT, TF_eq_hb ((11:ℝ)/4) (by norm_num)]; norm_num
  have h0 : TM275.F 0 = 8/9 := by
    rw [hT]; exact TF_zero ((11:ℝ)/4) (by norm_num)
  have hf : TM275.f 0 = 16*((11:ℝ)/4)/15 := by
    rw [hT]; exact TF_f0 ((11:ℝ)/4) (by norm_num)
  rw [h1, h2, h0, hf]
  rw [show ((8547:ℝ)/1000)/((11:ℝ)/4) = (777:ℝ)/250 by norm_num,
      show (((8547:ℝ)/1000) - ((1:ℝ)/50))/((11:ℝ)/4) = (8527:ℝ)/2750 by norm_num]
  rw [hb72G_closed (by norm_num : ((777:ℝ)/250) ≠ 0),
      hb72G_closed (by norm_num : ((8527:ℝ)/2750) ≠ 0)]
  rw [show 2 * ((777:ℝ)/250) = (777:ℝ)/125 by norm_num,
      show 2 * ((8527:ℝ)/2750) = (8527:ℝ)/1375 by norm_num]
  obtain ⟨hl1, hh1⟩ := exp_bounds_gen (x := (777:ℝ)/125)
    (lo := 500.6964343) (hi := 500.6964364) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨hl2, hh2⟩ := exp_bounds_gen (x := (8527:ℝ)/1375)
    (lo := 493.4662874) (hi := 493.4662895) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [hh1, hl2]

/-- Row 19 of the tables: `(λ, b, v) = ((11:ℝ)/4, (7:ℝ)/500, (461:ℝ)/50)`.
    The §6 inequality at scale `(11:ℝ)/4` fails at `(v,b)`, so `λ₁ ≤ (7:ℝ)/500` forces `λ(ρ) > (461:ℝ)/50`. -/
theorem rowCert_19 : 2 * (TM275.F (-((461:ℝ)/50)) - TM275.F ((7:ℝ)/500 - (461:ℝ)/50))
    < TM275.F 0 - TM275.f 0 * (252/1000) := by
  have hT : TM275 = tf72T ((11:ℝ)/4) (by norm_num) := rfl
  have h1 : TM275.F (-((461:ℝ)/50)) = hb72G (((461:ℝ)/50)/((11:ℝ)/4))/30 := by
    rw [hT, TF_eq_hb ((11:ℝ)/4) (by norm_num)]; norm_num
  have h2 : TM275.F ((7:ℝ)/500 - (461:ℝ)/50) = hb72G ((((461:ℝ)/50) - ((7:ℝ)/500))/((11:ℝ)/4))/30 := by
    rw [hT, TF_eq_hb ((11:ℝ)/4) (by norm_num)]; norm_num
  have h0 : TM275.F 0 = 8/9 := by
    rw [hT]; exact TF_zero ((11:ℝ)/4) (by norm_num)
  have hf : TM275.f 0 = 16*((11:ℝ)/4)/15 := by
    rw [hT]; exact TF_f0 ((11:ℝ)/4) (by norm_num)
  rw [h1, h2, h0, hf]
  rw [show ((461:ℝ)/50)/((11:ℝ)/4) = (922:ℝ)/275 by norm_num,
      show (((461:ℝ)/50) - ((7:ℝ)/500))/((11:ℝ)/4) = (4603:ℝ)/1375 by norm_num]
  rw [hb72G_closed (by norm_num : ((922:ℝ)/275) ≠ 0),
      hb72G_closed (by norm_num : ((4603:ℝ)/1375) ≠ 0)]
  rw [show 2 * ((922:ℝ)/275) = (1844:ℝ)/275 by norm_num,
      show 2 * ((4603:ℝ)/1375) = (9206:ℝ)/1375 by norm_num]
  obtain ⟨hl1, hh1⟩ := exp_bounds_gen (x := (1844:ℝ)/275)
    (lo := 816.8492360) (hi := 816.8492381) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨hl2, hh2⟩ := exp_bounds_gen (x := (9206:ℝ)/1375)
    (lo := 808.5744234) (hi := 808.5744255) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [hh1, hl2]

/-- Row 20 of the tables: `(λ, b, v) = ((14:ℝ)/5, (1:ℝ)/100, (4967:ℝ)/500)`.
    The §6 inequality at scale `(14:ℝ)/5` fails at `(v,b)`, so `λ₁ ≤ (1:ℝ)/100` forces `λ(ρ) > (4967:ℝ)/500`. -/
theorem rowCert_20 : 2 * (TM28.F (-((4967:ℝ)/500)) - TM28.F ((1:ℝ)/100 - (4967:ℝ)/500))
    < TM28.F 0 - TM28.f 0 * (252/1000) := by
  have hT : TM28 = tf72T ((14:ℝ)/5) (by norm_num) := rfl
  have h1 : TM28.F (-((4967:ℝ)/500)) = hb72G (((4967:ℝ)/500)/((14:ℝ)/5))/30 := by
    rw [hT, TF_eq_hb ((14:ℝ)/5) (by norm_num)]; norm_num
  have h2 : TM28.F ((1:ℝ)/100 - (4967:ℝ)/500) = hb72G ((((4967:ℝ)/500) - ((1:ℝ)/100))/((14:ℝ)/5))/30 := by
    rw [hT, TF_eq_hb ((14:ℝ)/5) (by norm_num)]; norm_num
  have h0 : TM28.F 0 = 8/9 := by
    rw [hT]; exact TF_zero ((14:ℝ)/5) (by norm_num)
  have hf : TM28.f 0 = 16*((14:ℝ)/5)/15 := by
    rw [hT]; exact TF_f0 ((14:ℝ)/5) (by norm_num)
  rw [h1, h2, h0, hf]
  rw [show ((4967:ℝ)/500)/((14:ℝ)/5) = (4967:ℝ)/1400 by norm_num,
      show (((4967:ℝ)/500) - ((1:ℝ)/100))/((14:ℝ)/5) = (2481:ℝ)/700 by norm_num]
  rw [hb72G_closed (by norm_num : ((4967:ℝ)/1400) ≠ 0),
      hb72G_closed (by norm_num : ((2481:ℝ)/700) ≠ 0)]
  rw [show 2 * ((4967:ℝ)/1400) = (4967:ℝ)/700 by norm_num,
      show 2 * ((2481:ℝ)/700) = (2481:ℝ)/350 by norm_num]
  obtain ⟨hl1, hh1⟩ := exp_bounds_gen (x := (4967:ℝ)/700)
    (lo := 1206.7840433) (hi := 1206.7840454) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨hl2, hh2⟩ := exp_bounds_gen (x := (2481:ℝ)/350)
    (lo := 1198.1948694) (hi := 1198.1948715) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [hh1, hl2]

/-- Row 21 of the tables: `(λ, b, v) = ((57:ℝ)/20, (7:ℝ)/1000, (2737:ℝ)/250)`.
    The §6 inequality at scale `(57:ℝ)/20` fails at `(v,b)`, so `λ₁ ≤ (7:ℝ)/1000` forces `λ(ρ) > (2737:ℝ)/250`. -/
theorem rowCert_21 : 2 * (TM285.F (-((2737:ℝ)/250)) - TM285.F ((7:ℝ)/1000 - (2737:ℝ)/250))
    < TM285.F 0 - TM285.f 0 * (252/1000) := by
  have hT : TM285 = tf72T ((57:ℝ)/20) (by norm_num) := rfl
  have h1 : TM285.F (-((2737:ℝ)/250)) = hb72G (((2737:ℝ)/250)/((57:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((57:ℝ)/20) (by norm_num)]; norm_num
  have h2 : TM285.F ((7:ℝ)/1000 - (2737:ℝ)/250) = hb72G ((((2737:ℝ)/250) - ((7:ℝ)/1000))/((57:ℝ)/20))/30 := by
    rw [hT, TF_eq_hb ((57:ℝ)/20) (by norm_num)]; norm_num
  have h0 : TM285.F 0 = 8/9 := by
    rw [hT]; exact TF_zero ((57:ℝ)/20) (by norm_num)
  have hf : TM285.f 0 = 16*((57:ℝ)/20)/15 := by
    rw [hT]; exact TF_f0 ((57:ℝ)/20) (by norm_num)
  rw [h1, h2, h0, hf]
  rw [show ((2737:ℝ)/250)/((57:ℝ)/20) = (5474:ℝ)/1425 by norm_num,
      show (((2737:ℝ)/250) - ((7:ℝ)/1000))/((57:ℝ)/20) = (3647:ℝ)/950 by norm_num]
  rw [hb72G_closed (by norm_num : ((5474:ℝ)/1425) ≠ 0),
      hb72G_closed (by norm_num : ((3647:ℝ)/950) ≠ 0)]
  rw [show 2 * ((5474:ℝ)/1425) = (10948:ℝ)/1425 by norm_num,
      show 2 * ((3647:ℝ)/950) = (3647:ℝ)/475 by norm_num]
  obtain ⟨hl1, hh1⟩ := exp_bounds_gen (x := (10948:ℝ)/1425)
    (lo := 2170.7044324) (hi := 2170.7044345) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨hl2, hh2⟩ := exp_bounds_gen (x := (3647:ℝ)/475)
    (lo := 2160.0674701) (hi := 2160.0674722) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [hh1, hl2]

/-! ## The coverage of the rows -/

/-- Row 1 covers `λ₁ ∈ [(193:ℝ)/1000, (1:ℝ)/5]`: `1.6500000 = v/2 ≥ log (1/λ₁)`. -/
theorem cov_1 {x : ℝ} (hx0 : 0 < x) (hx : ((193:ℝ)/1000) ≤ x) :
    2 * Real.log (1/x) ≤ ((33:ℝ)/10) := by
  have h1 : (1:ℝ)/x ≤ 1/((193:ℝ)/1000) := by
    rw [one_div, one_div]; exact inv_anti₀ (by norm_num) hx
  have h2 : (1:ℝ)/((193:ℝ)/1000) ≤ 5.2069788 := by norm_num
  have h3 : (5.2069788:ℝ) ≤ Real.exp ((33:ℝ)/20) := by
    obtain ⟨hlo, _⟩ := exp_bounds_gen (x := (33:ℝ)/20)
      (lo := 5.2069788) (hi := 5.2069809) (by norm_num) (by norm_num)
      (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
    exact hlo
  have h4 : Real.log (1/x) ≤ ((33:ℝ)/20) := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact le_trans h1 (le_trans h2 h3)
  linarith

/-- Row 2 covers `λ₁ ∈ [(37:ℝ)/200, (193:ℝ)/1000]`: `1.6925000 = v/2 ≥ log (1/λ₁)`. -/
theorem cov_2 {x : ℝ} (hx0 : 0 < x) (hx : ((37:ℝ)/200) ≤ x) :
    2 * Real.log (1/x) ≤ ((677:ℝ)/200) := by
  have h1 : (1:ℝ)/x ≤ 1/((37:ℝ)/200) := by
    rw [one_div, one_div]; exact inv_anti₀ (by norm_num) hx
  have h2 : (1:ℝ)/((37:ℝ)/200) ≤ 5.4330453 := by norm_num
  have h3 : (5.4330453:ℝ) ≤ Real.exp ((677:ℝ)/400) := by
    obtain ⟨hlo, _⟩ := exp_bounds_gen (x := (677:ℝ)/400)
      (lo := 5.4330453) (hi := 5.4330474) (by norm_num) (by norm_num)
      (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
    exact hlo
  have h4 : Real.log (1/x) ≤ ((677:ℝ)/400) := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact le_trans h1 (le_trans h2 h3)
  linarith

/-- Row 3 covers `λ₁ ∈ [(22:ℝ)/125, (37:ℝ)/200]`: `1.7425000 = v/2 ≥ log (1/λ₁)`. -/
theorem cov_3 {x : ℝ} (hx0 : 0 < x) (hx : ((22:ℝ)/125) ≤ x) :
    2 * Real.log (1/x) ≤ ((697:ℝ)/200) := by
  have h1 : (1:ℝ)/x ≤ 1/((22:ℝ)/125) := by
    rw [one_div, one_div]; exact inv_anti₀ (by norm_num) hx
  have h2 : (1:ℝ)/((22:ℝ)/125) ≤ 5.7116036 := by norm_num
  have h3 : (5.7116036:ℝ) ≤ Real.exp ((697:ℝ)/400) := by
    obtain ⟨hlo, _⟩ := exp_bounds_gen (x := (697:ℝ)/400)
      (lo := 5.7116036) (hi := 5.7116057) (by norm_num) (by norm_num)
      (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
    exact hlo
  have h4 : Real.log (1/x) ≤ ((697:ℝ)/400) := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact le_trans h1 (le_trans h2 h3)
  linarith

/-- Row 4 covers `λ₁ ∈ [(167:ℝ)/1000, (22:ℝ)/125]`: `1.7950000 = v/2 ≥ log (1/λ₁)`. -/
theorem cov_4 {x : ℝ} (hx0 : 0 < x) (hx : ((167:ℝ)/1000) ≤ x) :
    2 * Real.log (1/x) ≤ ((359:ℝ)/100) := by
  have h1 : (1:ℝ)/x ≤ 1/((167:ℝ)/1000) := by
    rw [one_div, one_div]; exact inv_anti₀ (by norm_num) hx
  have h2 : (1:ℝ)/((167:ℝ)/1000) ≤ 6.0194737 := by norm_num
  have h3 : (6.0194737:ℝ) ≤ Real.exp ((359:ℝ)/200) := by
    obtain ⟨hlo, _⟩ := exp_bounds_gen (x := (359:ℝ)/200)
      (lo := 6.0194737) (hi := 6.0194758) (by norm_num) (by norm_num)
      (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
    exact hlo
  have h4 : Real.log (1/x) ≤ ((359:ℝ)/200) := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact le_trans h1 (le_trans h2 h3)
  linarith

/-- Row 5 covers `λ₁ ∈ [(157:ℝ)/1000, (167:ℝ)/1000]`: `1.8565000 = v/2 ≥ log (1/λ₁)`. -/
theorem cov_5 {x : ℝ} (hx0 : 0 < x) (hx : ((157:ℝ)/1000) ≤ x) :
    2 * Real.log (1/x) ≤ ((3713:ℝ)/1000) := by
  have h1 : (1:ℝ)/x ≤ 1/((157:ℝ)/1000) := by
    rw [one_div, one_div]; exact inv_anti₀ (by norm_num) hx
  have h2 : (1:ℝ)/((157:ℝ)/1000) ≤ 6.4012919 := by norm_num
  have h3 : (6.4012919:ℝ) ≤ Real.exp ((3713:ℝ)/2000) := by
    obtain ⟨hlo, _⟩ := exp_bounds_gen (x := (3713:ℝ)/2000)
      (lo := 6.4012919) (hi := 6.4012940) (by norm_num) (by norm_num)
      (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
    exact hlo
  have h4 : Real.log (1/x) ≤ ((3713:ℝ)/2000) := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact le_trans h1 (le_trans h2 h3)
  linarith

/-- Row 6 covers `λ₁ ∈ [(73:ℝ)/500, (157:ℝ)/1000]`: `1.9290000 = v/2 ≥ log (1/λ₁)`. -/
theorem cov_6 {x : ℝ} (hx0 : 0 < x) (hx : ((73:ℝ)/500) ≤ x) :
    2 * Real.log (1/x) ≤ ((1929:ℝ)/500) := by
  have h1 : (1:ℝ)/x ≤ 1/((73:ℝ)/500) := by
    rw [one_div, one_div]; exact inv_anti₀ (by norm_num) hx
  have h2 : (1:ℝ)/((73:ℝ)/500) ≤ 6.8826231 := by norm_num
  have h3 : (6.8826231:ℝ) ≤ Real.exp ((1929:ℝ)/1000) := by
    obtain ⟨hlo, _⟩ := exp_bounds_gen (x := (1929:ℝ)/1000)
      (lo := 6.8826231) (hi := 6.8826252) (by norm_num) (by norm_num)
      (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
    exact hlo
  have h4 : Real.log (1/x) ≤ ((1929:ℝ)/1000) := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact le_trans h1 (le_trans h2 h3)
  linarith

/-- Row 7 covers `λ₁ ∈ [(67:ℝ)/500, (73:ℝ)/500]`: `2.0150000 = v/2 ≥ log (1/λ₁)`. -/
theorem cov_7 {x : ℝ} (hx0 : 0 < x) (hx : ((67:ℝ)/500) ≤ x) :
    2 * Real.log (1/x) ≤ ((403:ℝ)/100) := by
  have h1 : (1:ℝ)/x ≤ 1/((67:ℝ)/500) := by
    rw [one_div, one_div]; exact inv_anti₀ (by norm_num) hx
  have h2 : (1:ℝ)/((67:ℝ)/500) ≤ 7.5007263 := by norm_num
  have h3 : (7.5007263:ℝ) ≤ Real.exp ((403:ℝ)/200) := by
    obtain ⟨hlo, _⟩ := exp_bounds_gen (x := (403:ℝ)/200)
      (lo := 7.5007263) (hi := 7.5007284) (by norm_num) (by norm_num)
      (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
    exact hlo
  have h4 : Real.log (1/x) ≤ ((403:ℝ)/200) := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact le_trans h1 (le_trans h2 h3)
  linarith

/-- Row 8 covers `λ₁ ∈ [(61:ℝ)/500, (67:ℝ)/500]`: `2.1085000 = v/2 ≥ log (1/λ₁)`. -/
theorem cov_8 {x : ℝ} (hx0 : 0 < x) (hx : ((61:ℝ)/500) ≤ x) :
    2 * Real.log (1/x) ≤ ((4217:ℝ)/1000) := by
  have h1 : (1:ℝ)/x ≤ 1/((61:ℝ)/500) := by
    rw [one_div, one_div]; exact inv_anti₀ (by norm_num) hx
  have h2 : (1:ℝ)/((61:ℝ)/500) ≤ 8.2358771 := by norm_num
  have h3 : (8.2358771:ℝ) ≤ Real.exp ((4217:ℝ)/2000) := by
    obtain ⟨hlo, _⟩ := exp_bounds_gen (x := (4217:ℝ)/2000)
      (lo := 8.2358771) (hi := 8.2358792) (by norm_num) (by norm_num)
      (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
    exact hlo
  have h4 : Real.log (1/x) ≤ ((4217:ℝ)/2000) := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact le_trans h1 (le_trans h2 h3)
  linarith

/-- Row 9 covers `λ₁ ∈ [(109:ℝ)/1000, (61:ℝ)/500]`: `2.2215000 = v/2 ≥ log (1/λ₁)`. -/
theorem cov_9 {x : ℝ} (hx0 : 0 < x) (hx : ((109:ℝ)/1000) ≤ x) :
    2 * Real.log (1/x) ≤ ((4443:ℝ)/1000) := by
  have h1 : (1:ℝ)/x ≤ 1/((109:ℝ)/1000) := by
    rw [one_div, one_div]; exact inv_anti₀ (by norm_num) hx
  have h2 : (1:ℝ)/((109:ℝ)/1000) ≤ 9.2211512 := by norm_num
  have h3 : (9.2211512:ℝ) ≤ Real.exp ((4443:ℝ)/2000) := by
    obtain ⟨hlo, _⟩ := exp_bounds_gen (x := (4443:ℝ)/2000)
      (lo := 9.2211512) (hi := 9.2211533) (by norm_num) (by norm_num)
      (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
    exact hlo
  have h4 : Real.log (1/x) ≤ ((4443:ℝ)/2000) := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact le_trans h1 (le_trans h2 h3)
  linarith

/-- Row 10 covers `λ₁ ∈ [(12:ℝ)/125, (109:ℝ)/1000]`: `2.3485000 = v/2 ≥ log (1/λ₁)`. -/
theorem cov_10 {x : ℝ} (hx0 : 0 < x) (hx : ((12:ℝ)/125) ≤ x) :
    2 * Real.log (1/x) ≤ ((4697:ℝ)/1000) := by
  have h1 : (1:ℝ)/x ≤ 1/((12:ℝ)/125) := by
    rw [one_div, one_div]; exact inv_anti₀ (by norm_num) hx
  have h2 : (1:ℝ)/((12:ℝ)/125) ≤ 10.4698521 := by norm_num
  have h3 : (10.4698521:ℝ) ≤ Real.exp ((4697:ℝ)/2000) := by
    obtain ⟨hlo, _⟩ := exp_bounds_gen (x := (4697:ℝ)/2000)
      (lo := 10.4698521) (hi := 10.4698542) (by norm_num) (by norm_num)
      (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
    exact hlo
  have h4 : Real.log (1/x) ≤ ((4697:ℝ)/2000) := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact le_trans h1 (le_trans h2 h3)
  linarith

/-- Row 11 covers `λ₁ ∈ [(83:ℝ)/1000, (12:ℝ)/125]`: `2.4940000 = v/2 ≥ log (1/λ₁)`. -/
theorem cov_11 {x : ℝ} (hx0 : 0 < x) (hx : ((83:ℝ)/1000) ≤ x) :
    2 * Real.log (1/x) ≤ ((1247:ℝ)/250) := by
  have h1 : (1:ℝ)/x ≤ 1/((83:ℝ)/1000) := by
    rw [one_div, one_div]; exact inv_anti₀ (by norm_num) hx
  have h2 : (1:ℝ)/((83:ℝ)/1000) ≤ 12.1096168 := by norm_num
  have h3 : (12.1096168:ℝ) ≤ Real.exp ((1247:ℝ)/500) := by
    obtain ⟨hlo, _⟩ := exp_bounds_gen (x := (1247:ℝ)/500)
      (lo := 12.1096168) (hi := 12.1096189) (by norm_num) (by norm_num)
      (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
    exact hlo
  have h4 : Real.log (1/x) ≤ ((1247:ℝ)/500) := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact le_trans h1 (le_trans h2 h3)
  linarith

/-- Row 12 covers `λ₁ ∈ [(7:ℝ)/100, (83:ℝ)/1000]`: `2.6645000 = v/2 ≥ log (1/λ₁)`. -/
theorem cov_12 {x : ℝ} (hx0 : 0 < x) (hx : ((7:ℝ)/100) ≤ x) :
    2 * Real.log (1/x) ≤ ((5329:ℝ)/1000) := by
  have h1 : (1:ℝ)/x ≤ 1/((7:ℝ)/100) := by
    rw [one_div, one_div]; exact inv_anti₀ (by norm_num) hx
  have h2 : (1:ℝ)/((7:ℝ)/100) ≤ 14.3607663 := by norm_num
  have h3 : (14.3607663:ℝ) ≤ Real.exp ((5329:ℝ)/2000) := by
    obtain ⟨hlo, _⟩ := exp_bounds_gen (x := (5329:ℝ)/2000)
      (lo := 14.3607663) (hi := 14.3607684) (by norm_num) (by norm_num)
      (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
    exact hlo
  have h4 : Real.log (1/x) ≤ ((5329:ℝ)/2000) := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact le_trans h1 (le_trans h2 h3)
  linarith

/-- Row 13 covers `λ₁ ∈ [(29:ℝ)/500, (7:ℝ)/100]`: `2.8525000 = v/2 ≥ log (1/λ₁)`. -/
theorem cov_13 {x : ℝ} (hx0 : 0 < x) (hx : ((29:ℝ)/500) ≤ x) :
    2 * Real.log (1/x) ≤ ((1141:ℝ)/200) := by
  have h1 : (1:ℝ)/x ≤ 1/((29:ℝ)/500) := by
    rw [one_div, one_div]; exact inv_anti₀ (by norm_num) hx
  have h2 : (1:ℝ)/((29:ℝ)/500) ≤ 17.3310543 := by norm_num
  have h3 : (17.3310543:ℝ) ≤ Real.exp ((1141:ℝ)/400) := by
    obtain ⟨hlo, _⟩ := exp_bounds_gen (x := (1141:ℝ)/400)
      (lo := 17.3310543) (hi := 17.3310564) (by norm_num) (by norm_num)
      (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
    exact hlo
  have h4 : Real.log (1/x) ≤ ((1141:ℝ)/400) := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact le_trans h1 (le_trans h2 h3)
  linarith

/-- Row 14 covers `λ₁ ∈ [(23:ℝ)/500, (29:ℝ)/500]`: `3.0840000 = v/2 ≥ log (1/λ₁)`. -/
theorem cov_14 {x : ℝ} (hx0 : 0 < x) (hx : ((23:ℝ)/500) ≤ x) :
    2 * Real.log (1/x) ≤ ((771:ℝ)/125) := by
  have h1 : (1:ℝ)/x ≤ 1/((23:ℝ)/500) := by
    rw [one_div, one_div]; exact inv_anti₀ (by norm_num) hx
  have h2 : (1:ℝ)/((23:ℝ)/500) ≤ 21.8456093 := by norm_num
  have h3 : (21.8456093:ℝ) ≤ Real.exp ((771:ℝ)/250) := by
    obtain ⟨hlo, _⟩ := exp_bounds_gen (x := (771:ℝ)/250)
      (lo := 21.8456093) (hi := 21.8456114) (by norm_num) (by norm_num)
      (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
    exact hlo
  have h4 : Real.log (1/x) ≤ ((771:ℝ)/250) := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact le_trans h1 (le_trans h2 h3)
  linarith

/-- Row 15 covers `λ₁ ∈ [(9:ℝ)/250, (23:ℝ)/500]`: `3.3290000 = v/2 ≥ log (1/λ₁)`. -/
theorem cov_15 {x : ℝ} (hx0 : 0 < x) (hx : ((9:ℝ)/250) ≤ x) :
    2 * Real.log (1/x) ≤ ((3329:ℝ)/500) := by
  have h1 : (1:ℝ)/x ≤ 1/((9:ℝ)/250) := by
    rw [one_div, one_div]; exact inv_anti₀ (by norm_num) hx
  have h2 : (1:ℝ)/((9:ℝ)/250) ≤ 27.9104163 := by norm_num
  have h3 : (27.9104163:ℝ) ≤ Real.exp ((3329:ℝ)/1000) := by
    obtain ⟨hlo, _⟩ := exp_bounds_gen (x := (3329:ℝ)/1000)
      (lo := 27.9104163) (hi := 27.9104184) (by norm_num) (by norm_num)
      (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
    exact hlo
  have h4 : Real.log (1/x) ≤ ((3329:ℝ)/1000) := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact le_trans h1 (le_trans h2 h3)
  linarith

/-- Row 16 covers `λ₁ ∈ [(27:ℝ)/1000, (9:ℝ)/250]`: `3.6170000 = v/2 ≥ log (1/λ₁)`. -/
theorem cov_16 {x : ℝ} (hx0 : 0 < x) (hx : ((27:ℝ)/1000) ≤ x) :
    2 * Real.log (1/x) ≤ ((3617:ℝ)/500) := by
  have h1 : (1:ℝ)/x ≤ 1/((27:ℝ)/1000) := by
    rw [one_div, one_div]; exact inv_anti₀ (by norm_num) hx
  have h2 : (1:ℝ)/((27:ℝ)/1000) ≤ 37.2257219 := by norm_num
  have h3 : (37.2257219:ℝ) ≤ Real.exp ((3617:ℝ)/1000) := by
    obtain ⟨hlo, _⟩ := exp_bounds_gen (x := (3617:ℝ)/1000)
      (lo := 37.2257219) (hi := 37.2257240) (by norm_num) (by norm_num)
      (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
    exact hlo
  have h4 : Real.log (1/x) ≤ ((3617:ℝ)/1000) := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact le_trans h1 (le_trans h2 h3)
  linarith

/-- Row 17 covers `λ₁ ∈ [(1:ℝ)/50, (27:ℝ)/1000]`: `3.9170000 = v/2 ≥ log (1/λ₁)`. -/
theorem cov_17 {x : ℝ} (hx0 : 0 < x) (hx : ((1:ℝ)/50) ≤ x) :
    2 * Real.log (1/x) ≤ ((3917:ℝ)/500) := by
  have h1 : (1:ℝ)/x ≤ 1/((1:ℝ)/50) := by
    rw [one_div, one_div]; exact inv_anti₀ (by norm_num) hx
  have h2 : (1:ℝ)/((1:ℝ)/50) ≤ 50.2494690 := by norm_num
  have h3 : (50.2494690:ℝ) ≤ Real.exp ((3917:ℝ)/1000) := by
    obtain ⟨hlo, _⟩ := exp_bounds_gen (x := (3917:ℝ)/1000)
      (lo := 50.2494690) (hi := 50.2494711) (by norm_num) (by norm_num)
      (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
    exact hlo
  have h4 : Real.log (1/x) ≤ ((3917:ℝ)/1000) := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact le_trans h1 (le_trans h2 h3)
  linarith

/-- Row 18 covers `λ₁ ∈ [(7:ℝ)/500, (1:ℝ)/50]`: `4.2735000 = v/2 ≥ log (1/λ₁)`. -/
theorem cov_18 {x : ℝ} (hx0 : 0 < x) (hx : ((7:ℝ)/500) ≤ x) :
    2 * Real.log (1/x) ≤ ((8547:ℝ)/1000) := by
  have h1 : (1:ℝ)/x ≤ 1/((7:ℝ)/500) := by
    rw [one_div, one_div]; exact inv_anti₀ (by norm_num) hx
  have h2 : (1:ℝ)/((7:ℝ)/500) ≤ 71.7723989 := by norm_num
  have h3 : (71.7723989:ℝ) ≤ Real.exp ((8547:ℝ)/2000) := by
    obtain ⟨hlo, _⟩ := exp_bounds_gen (x := (8547:ℝ)/2000)
      (lo := 71.7723989) (hi := 71.7724010) (by norm_num) (by norm_num)
      (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
    exact hlo
  have h4 : Real.log (1/x) ≤ ((8547:ℝ)/2000) := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact le_trans h1 (le_trans h2 h3)
  linarith

/-- Row 19 covers `λ₁ ∈ [(1:ℝ)/100, (7:ℝ)/500]`: `4.6100000 = v/2 ≥ log (1/λ₁)`. -/
theorem cov_19 {x : ℝ} (hx0 : 0 < x) (hx : ((1:ℝ)/100) ≤ x) :
    2 * Real.log (1/x) ≤ ((461:ℝ)/50) := by
  have h1 : (1:ℝ)/x ≤ 1/((1:ℝ)/100) := by
    rw [one_div, one_div]; exact inv_anti₀ (by norm_num) hx
  have h2 : (1:ℝ)/((1:ℝ)/100) ≤ 100.4841486 := by norm_num
  have h3 : (100.4841486:ℝ) ≤ Real.exp ((461:ℝ)/100) := by
    obtain ⟨hlo, _⟩ := exp_bounds_gen (x := (461:ℝ)/100)
      (lo := 100.4841486) (hi := 100.4841507) (by norm_num) (by norm_num)
      (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
    exact hlo
  have h4 : Real.log (1/x) ≤ ((461:ℝ)/100) := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact le_trans h1 (le_trans h2 h3)
  linarith

/-- Row 20 covers `λ₁ ∈ [(7:ℝ)/1000, (1:ℝ)/100]`: `4.9670000 = v/2 ≥ log (1/λ₁)`. -/
theorem cov_20 {x : ℝ} (hx0 : 0 < x) (hx : ((7:ℝ)/1000) ≤ x) :
    2 * Real.log (1/x) ≤ ((4967:ℝ)/500) := by
  have h1 : (1:ℝ)/x ≤ 1/((7:ℝ)/1000) := by
    rw [one_div, one_div]; exact inv_anti₀ (by norm_num) hx
  have h2 : (1:ℝ)/((7:ℝ)/1000) ≤ 143.5954531 := by norm_num
  have h3 : (143.5954531:ℝ) ≤ Real.exp ((4967:ℝ)/1000) := by
    obtain ⟨hlo, _⟩ := exp_bounds_gen (x := (4967:ℝ)/1000)
      (lo := 143.5954531) (hi := 143.5954552) (by norm_num) (by norm_num)
      (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
    exact hlo
  have h4 : Real.log (1/x) ≤ ((4967:ℝ)/1000) := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact le_trans h1 (le_trans h2 h3)
  linarith

/-- `4 e ≤ (2737:ℝ)/250`, so the last row covers all remaining `λ₁`. -/
theorem four_exp_le : 4 * Real.exp 1 ≤ ((2737:ℝ)/250) := by
  obtain ⟨_, hhi⟩ := exp_bounds_gen (x := 1) (lo := 2.718) (hi := 2.72) (by norm_num) (by norm_num)
    (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  linarith
/-- The threshold conditions needed by the §6 inequality, all of the form "`log q` is large". -/
theorem exists_threshold (A B : ℝ) (hA : 0 < A) (hB : 0 ≤ B) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → 3 ≤ q ∧ A ≤ Real.log (q : ℝ) ∧
      B ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) ∧
      B ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := by
  let N : ℝ := max A (max 1 (max (B^2) (3*B)))
  have hAN : A ≤ N := by
    show A ≤ max A (max 1 (max (B^2) (3*B)))
    exact le_max_left _ _
  have h1N : 1 ≤ N := by
    show (1:ℝ) ≤ max A (max 1 (max (B^2) (3*B)))
    exact le_trans (le_max_left 1 _) (le_max_right A _)
  have hB2N : B^2 ≤ N := by
    show B^2 ≤ max A (max 1 (max (B^2) (3*B)))
    exact le_trans (le_max_left (B^2) (3*B)) (le_trans (le_max_right 1 _) (le_max_right A _))
  have hB3N : 3*B ≤ N := by
    show 3*B ≤ max A (max 1 (max (B^2) (3*B)))
    exact le_trans (le_max_right (B^2) (3*B)) (le_trans (le_max_right 1 _) (le_max_right A _))
  refine ⟨⌈Real.exp (Real.exp (Real.exp N))⌉₊ + 3, ?_⟩
  intro q hq
  have hq3 : 3 ≤ q := by omega
  have hExp : Real.exp (Real.exp (Real.exp N)) ≤ (q : ℝ) := by
    have h1 : Real.exp (Real.exp (Real.exp N)) ≤ (⌈Real.exp (Real.exp (Real.exp N))⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h2 : ((⌈Real.exp (Real.exp (Real.exp N))⌉₊ : ℕ) : ℝ)
        ≤ ((⌈Real.exp (Real.exp (Real.exp N))⌉₊ + 3 : ℕ) : ℝ) := by push_cast; linarith
    have h3 : ((⌈Real.exp (Real.exp (Real.exp N))⌉₊ + 3 : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast hq
    linarith
  have hlogq : Real.exp (Real.exp N) ≤ Real.log (q : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos (Real.exp (Real.exp N))) hExp
    rw [Real.log_exp] at h
    exact h
  have hNN : N ≤ Real.exp N := by
    have := Real.add_one_le_exp N; linarith
  have hNexpN : N ≤ Real.exp (Real.exp N) := le_trans hNN (Real.exp_le_exp.mpr hNN)
  have hloglog : Real.exp N ≤ Real.log (Real.log (q : ℝ)) := by
    have h := Real.log_le_log (Real.exp_pos (Real.exp N)) hlogq
    rw [Real.log_exp] at h
    exact h
  have hlogloglog : N ≤ Real.log (Real.log (Real.log (q : ℝ))) := by
    have h := Real.log_le_log (Real.exp_pos N) hloglog
    rw [Real.log_exp] at h
    exact h
  refine ⟨hq3, ?_, ?_, ?_⟩
  · exact le_trans (le_trans hAN hNexpN) hlogq
  · have hB2 : B^2 ≤ Real.log (Real.log (q : ℝ)) := le_trans hB2N (le_trans hNN hloglog)
    have hsq : Real.sqrt (B^2) ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := Real.sqrt_le_sqrt hB2
    rwa [Real.sqrt_sq hB] at hsq
  · linarith

/-! ## The assembly -/

theorem s6_real_low (ε : ℝ) (hε : 0 < ε) : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
      Work.LinnikContract.zeroMult χ₁ ρ₁ = 1 →
      ∀ ρ : ℂ, Work.LinnikContract.zeroMult χ₁ ρ ≠ 0 → |ρ.im| ≤ 2 → ρ ≠ ρ₁ → ρ.im = 0 →
      (∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u ≠ 0 → |u.im| ≤ 1 → u ≠ ρ₁ →
        Work.LinnikContract.lamOf q ρ ≤ Work.LinnikContract.lamOf q u) →
      Work.LinnikContract.lamOf q ρ₁ ≤ 1 / 5 →
      min (4 * Real.exp 1) ((2 - ε) * Real.log (1 / Work.LinnikContract.lamOf q ρ₁))
        ≤ Work.LinnikContract.lamOf q ρ := by
  obtain ⟨c, hcpos, hcle, δ, hδ0, hδ1, q52, h52⟩ :=
    Work.ZeroFreeTables.Table4.l52HypRealQuarter
  have hcc : c ≤ cS6 := hcle
  have hK : 2 * c + 4 * eS6 ≤ 252/1000 := by
    have h1 : c ≤ 1/8 + 1/1000000 := hcle
    unfold eS6
    linarith
  have hprov : ∀ (q : ℕ), q52 ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → χ ^ 2 = 1 → Commons.NumberTheory.Linnik.L52Hyp χ c eS6 δ := by
    intro q hq _inst χ _instc hχ hsq
    exact @h52 q hq _inst χ _instc hχ hsq eS6 (by unfold eS6; norm_num) (by unfold eS6; norm_num)
  obtain ⟨QA0, hQA0⟩ := s6_ineq_at ((23:ℝ)/10) (by norm_num) δ hδ0 hδ1 c hcc q52
    hprov
  obtain ⟨QA1, hQA1⟩ := s6_ineq_at ((47:ℝ)/20) (by norm_num) δ hδ0 hδ1 c hcc q52
    hprov
  obtain ⟨QA2, hQA2⟩ := s6_ineq_at ((12:ℝ)/5) (by norm_num) δ hδ0 hδ1 c hcc q52
    hprov
  obtain ⟨QA3, hQA3⟩ := s6_ineq_at ((49:ℝ)/20) (by norm_num) δ hδ0 hδ1 c hcc q52
    hprov
  obtain ⟨QA4, hQA4⟩ := s6_ineq_at ((5:ℝ)/2) (by norm_num) δ hδ0 hδ1 c hcc q52
    hprov
  obtain ⟨QA5, hQA5⟩ := s6_ineq_at ((51:ℝ)/20) (by norm_num) δ hδ0 hδ1 c hcc q52
    hprov
  obtain ⟨QA6, hQA6⟩ := s6_ineq_at ((13:ℝ)/5) (by norm_num) δ hδ0 hδ1 c hcc q52
    hprov
  obtain ⟨QA7, hQA7⟩ := s6_ineq_at ((53:ℝ)/20) (by norm_num) δ hδ0 hδ1 c hcc q52
    hprov
  obtain ⟨QA8, hQA8⟩ := s6_ineq_at ((27:ℝ)/10) (by norm_num) δ hδ0 hδ1 c hcc q52
    hprov
  obtain ⟨QA9, hQA9⟩ := s6_ineq_at ((11:ℝ)/4) (by norm_num) δ hδ0 hδ1 c hcc q52
    hprov
  obtain ⟨QA10, hQA10⟩ := s6_ineq_at ((14:ℝ)/5) (by norm_num) δ hδ0 hδ1 c hcc q52
    hprov
  obtain ⟨QA11, hQA11⟩ := s6_ineq_at ((57:ℝ)/20) (by norm_num) δ hδ0 hδ1 c hcc q52
    hprov
  obtain ⟨QC, hQC⟩ := exists_threshold (max ((1/5)/δ) (12/δ)) 12 (by positivity) (by norm_num)
  let Qs : Finset ℕ := {QC, QA0, QA1, QA2, QA3, QA4, QA5, QA6, QA7, QA8, QA9, QA10, QA11, q52, 3}
  have hQne : Qs.Nonempty := by simp [Qs]
  refine ⟨Qs.max' hQne, ?_⟩
  intro q hq _inst χ₁ ρ₁ hwide hsq him0 hmult1 ρ hzm him hne hρim0 hmin hlam1
  have hqQC : QC ≤ q := le_trans (Finset.le_max' Qs QC (by simp [Qs])) hq
  have hqA0 : QA0 ≤ q := le_trans (Finset.le_max' Qs QA0 (by simp [Qs])) hq
  have hqA1 : QA1 ≤ q := le_trans (Finset.le_max' Qs QA1 (by simp [Qs])) hq
  have hqA2 : QA2 ≤ q := le_trans (Finset.le_max' Qs QA2 (by simp [Qs])) hq
  have hqA3 : QA3 ≤ q := le_trans (Finset.le_max' Qs QA3 (by simp [Qs])) hq
  have hqA4 : QA4 ≤ q := le_trans (Finset.le_max' Qs QA4 (by simp [Qs])) hq
  have hqA5 : QA5 ≤ q := le_trans (Finset.le_max' Qs QA5 (by simp [Qs])) hq
  have hqA6 : QA6 ≤ q := le_trans (Finset.le_max' Qs QA6 (by simp [Qs])) hq
  have hqA7 : QA7 ≤ q := le_trans (Finset.le_max' Qs QA7 (by simp [Qs])) hq
  have hqA8 : QA8 ≤ q := le_trans (Finset.le_max' Qs QA8 (by simp [Qs])) hq
  have hqA9 : QA9 ≤ q := le_trans (Finset.le_max' Qs QA9 (by simp [Qs])) hq
  have hqA10 : QA10 ≤ q := le_trans (Finset.le_max' Qs QA10 (by simp [Qs])) hq
  have hqA11 : QA11 ≤ q := le_trans (Finset.le_max' Qs QA11 (by simp [Qs])) hq
  have hq52' : q52 ≤ q := le_trans (Finset.le_max' Qs q52 (by simp [Qs])) hq
  obtain ⟨hq3, hlogA, hptB, hcapB⟩ := hQC q hqQC
  have hlogδ1 : (1/5)/δ ≤ Real.log (q : ℝ) := le_trans (le_max_left _ _) hlogA
  have hlogδ2 : 12/δ ≤ Real.log (q : ℝ) := le_trans (le_max_right _ _) hlogA
  have hpt1 : (1/5) ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := le_trans (by norm_num) hptB
  have hpt2 : 12 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := hptB
  have hcap1 : (1:ℝ)/5 ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 :=
    le_trans (by linarith) hcapB
  have hcap2 : 12 ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := hcapB
  letI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have hχ1 : χ₁ ≠ 1 := isZ_ne_one (isMin1_isZ hwide.1)
  have hq2 : 2 ≤ q := by omega
  have hlam1pos : 0 < lamOf q ρ₁ :=
    (Work.LinnikAreas.OtherCharRepel.zeroMultStripPos (χ := χ₁) (u := ρ₁) hq2 hχ1
      (by rw [hmult1]; norm_num)).2.2
  have hlam1nn : 0 ≤ lamOf q ρ₁ := hlam1pos.le
  have hlam1le : lamOf q ρ₁ ≤ lamOf q ρ := by
    refine hwide.1.2 χ₁ ρ ⟨hχ1, hzm, ?_⟩
    rw [hρim0]; norm_num
  have hlam0nn : 0 ≤ lamOf q ρ := le_trans hlam1nn hlam1le
  by_cases h4e : 4 * Real.exp 1 ≤ lamOf q ρ
  · exact le_trans (min_le_left _ _) h4e
  push_neg at h4e
  have hlam012 : lamOf q ρ ≤ 12 := by
    have := Real.exp_one_lt_three; linarith
  have hlam0cap : lamOf q ρ ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 :=
    le_trans hlam012 hcap2
  by_contra hcon
  push_neg at hcon
  have hlam02L : lamOf q ρ < 2 * Real.log (1 / lamOf q ρ₁) := by
    have h1 : lamOf q ρ < (2 - ε) * Real.log (1 / lamOf q ρ₁) :=
      lt_of_lt_of_le hcon (min_le_right _ _)
    have hLnn : 0 ≤ Real.log (1 / lamOf q ρ₁) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hlam1pos]; linarith
    have h2 : (2 - ε) * Real.log (1 / lamOf q ρ₁) ≤ 2 * Real.log (1 / lamOf q ρ₁) :=
      mul_le_mul_of_nonneg_right (by linarith) hLnn
    linarith
  have hlam04e : lamOf q ρ < 4 * Real.exp 1 := lt_of_lt_of_le hcon (min_le_left _ _)
  have hineq1 : 0 ≤ 2 * TM23.F (-(lamOf q ρ)) - 2 * TM23.F (lamOf q ρ₁ - lamOf q ρ)
      - TM23.F 0 + (2 * c + 4 * eS6) * TM23.f 0 :=
    hQA0 q hqA0 χ₁ ρ₁ ρ hwide hsq him0 hmult1 hzm him hne hρim0 hmin hlam1
      hlam012 hlam0cap hlogδ1 hlogδ2 hpt1 hpt2 hcap1
  have hineq2 : 0 ≤ 2 * TM235.F (-(lamOf q ρ)) - 2 * TM235.F (lamOf q ρ₁ - lamOf q ρ)
      - TM235.F 0 + (2 * c + 4 * eS6) * TM235.f 0 :=
    hQA1 q hqA1 χ₁ ρ₁ ρ hwide hsq him0 hmult1 hzm him hne hρim0 hmin hlam1
      hlam012 hlam0cap hlogδ1 hlogδ2 hpt1 hpt2 hcap1
  have hineq3 : 0 ≤ 2 * TM24.F (-(lamOf q ρ)) - 2 * TM24.F (lamOf q ρ₁ - lamOf q ρ)
      - TM24.F 0 + (2 * c + 4 * eS6) * TM24.f 0 :=
    hQA2 q hqA2 χ₁ ρ₁ ρ hwide hsq him0 hmult1 hzm him hne hρim0 hmin hlam1
      hlam012 hlam0cap hlogδ1 hlogδ2 hpt1 hpt2 hcap1
  have hineq4 : 0 ≤ 2 * TM245.F (-(lamOf q ρ)) - 2 * TM245.F (lamOf q ρ₁ - lamOf q ρ)
      - TM245.F 0 + (2 * c + 4 * eS6) * TM245.f 0 :=
    hQA3 q hqA3 χ₁ ρ₁ ρ hwide hsq him0 hmult1 hzm him hne hρim0 hmin hlam1
      hlam012 hlam0cap hlogδ1 hlogδ2 hpt1 hpt2 hcap1
  have hineq5 : 0 ≤ 2 * TM25.F (-(lamOf q ρ)) - 2 * TM25.F (lamOf q ρ₁ - lamOf q ρ)
      - TM25.F 0 + (2 * c + 4 * eS6) * TM25.f 0 :=
    hQA4 q hqA4 χ₁ ρ₁ ρ hwide hsq him0 hmult1 hzm him hne hρim0 hmin hlam1
      hlam012 hlam0cap hlogδ1 hlogδ2 hpt1 hpt2 hcap1
  have hineq6 : 0 ≤ 2 * TM255.F (-(lamOf q ρ)) - 2 * TM255.F (lamOf q ρ₁ - lamOf q ρ)
      - TM255.F 0 + (2 * c + 4 * eS6) * TM255.f 0 :=
    hQA5 q hqA5 χ₁ ρ₁ ρ hwide hsq him0 hmult1 hzm him hne hρim0 hmin hlam1
      hlam012 hlam0cap hlogδ1 hlogδ2 hpt1 hpt2 hcap1
  have hineq7 : 0 ≤ 2 * TM26.F (-(lamOf q ρ)) - 2 * TM26.F (lamOf q ρ₁ - lamOf q ρ)
      - TM26.F 0 + (2 * c + 4 * eS6) * TM26.f 0 :=
    hQA6 q hqA6 χ₁ ρ₁ ρ hwide hsq him0 hmult1 hzm him hne hρim0 hmin hlam1
      hlam012 hlam0cap hlogδ1 hlogδ2 hpt1 hpt2 hcap1
  have hineq8 : 0 ≤ 2 * TM265.F (-(lamOf q ρ)) - 2 * TM265.F (lamOf q ρ₁ - lamOf q ρ)
      - TM265.F 0 + (2 * c + 4 * eS6) * TM265.f 0 :=
    hQA7 q hqA7 χ₁ ρ₁ ρ hwide hsq him0 hmult1 hzm him hne hρim0 hmin hlam1
      hlam012 hlam0cap hlogδ1 hlogδ2 hpt1 hpt2 hcap1
  have hineq9 : 0 ≤ 2 * TM27.F (-(lamOf q ρ)) - 2 * TM27.F (lamOf q ρ₁ - lamOf q ρ)
      - TM27.F 0 + (2 * c + 4 * eS6) * TM27.f 0 :=
    hQA8 q hqA8 χ₁ ρ₁ ρ hwide hsq him0 hmult1 hzm him hne hρim0 hmin hlam1
      hlam012 hlam0cap hlogδ1 hlogδ2 hpt1 hpt2 hcap1
  have hineq10 : 0 ≤ 2 * TM275.F (-(lamOf q ρ)) - 2 * TM275.F (lamOf q ρ₁ - lamOf q ρ)
      - TM275.F 0 + (2 * c + 4 * eS6) * TM275.f 0 :=
    hQA9 q hqA9 χ₁ ρ₁ ρ hwide hsq him0 hmult1 hzm him hne hρim0 hmin hlam1
      hlam012 hlam0cap hlogδ1 hlogδ2 hpt1 hpt2 hcap1
  have hineq11 : 0 ≤ 2 * TM28.F (-(lamOf q ρ)) - 2 * TM28.F (lamOf q ρ₁ - lamOf q ρ)
      - TM28.F 0 + (2 * c + 4 * eS6) * TM28.f 0 :=
    hQA10 q hqA10 χ₁ ρ₁ ρ hwide hsq him0 hmult1 hzm him hne hρim0 hmin hlam1
      hlam012 hlam0cap hlogδ1 hlogδ2 hpt1 hpt2 hcap1
  have hineq12 : 0 ≤ 2 * TM285.F (-(lamOf q ρ)) - 2 * TM285.F (lamOf q ρ₁ - lamOf q ρ)
      - TM285.F 0 + (2 * c + 4 * eS6) * TM285.f 0 :=
    hQA11 q hqA11 χ₁ ρ₁ ρ hwide hsq him0 hmult1 hzm him hne hρim0 hmin hlam1
      hlam012 hlam0cap hlogδ1 hlogδ2 hpt1 hpt2 hcap1
  by_cases hcase1 : ((193:ℝ)/1000) ≤ lamOf q ρ₁
  · -- row 1: `λ₁ ∈ [(193:ℝ)/1000, (1:ℝ)/5]`
    have hcov : 2 * Real.log (1 / lamOf q ρ₁) ≤ ((33:ℝ)/10) := cov_1 hlam1pos hcase1
    have hb : lamOf q ρ₁ ≤ ((1:ℝ)/5) := by linarith only [hlam1]
    have hv : lamOf q ρ ≤ ((33:ℝ)/10) := le_of_lt (lt_of_lt_of_le hlam02L hcov)
    have hmono := TestFn_E_mono TM23 hv hb hlam1nn
    have hKf : (2 * c + 4 * eS6) * TM23.f 0 ≤ (252/1000) * TM23.f 0 :=
      mul_le_mul_of_nonneg_right hK TM23.f0_pos.le
    have hA : TM23.F 0 - (2 * c + 4 * eS6) * TM23.f 0
        ≤ 2 * (TM23.F (-(lamOf q ρ)) - TM23.F (lamOf q ρ₁ - lamOf q ρ)) := by
      linarith only [hineq1]
    have hB : TM23.F 0 - (2 * c + 4 * eS6) * TM23.f 0
        < TM23.F 0 - (252/1000) * TM23.f 0 := by
      refine lt_of_le_of_lt (le_trans hA hmono) ?_
      linarith only [rowCert_1]
    linarith only [hB, hKf]
  by_cases hcase2 : ((37:ℝ)/200) ≤ lamOf q ρ₁
  · -- row 2: `λ₁ ∈ [(37:ℝ)/200, (193:ℝ)/1000]`
    have hcov : 2 * Real.log (1 / lamOf q ρ₁) ≤ ((677:ℝ)/200) := cov_2 hlam1pos hcase2
    have hb : lamOf q ρ₁ ≤ ((193:ℝ)/1000) := by
      have hlt := not_le.mp hcase1
      linarith only [hlt]
    have hv : lamOf q ρ ≤ ((677:ℝ)/200) := le_of_lt (lt_of_lt_of_le hlam02L hcov)
    have hmono := TestFn_E_mono TM235 hv hb hlam1nn
    have hKf : (2 * c + 4 * eS6) * TM235.f 0 ≤ (252/1000) * TM235.f 0 :=
      mul_le_mul_of_nonneg_right hK TM235.f0_pos.le
    have hA : TM235.F 0 - (2 * c + 4 * eS6) * TM235.f 0
        ≤ 2 * (TM235.F (-(lamOf q ρ)) - TM235.F (lamOf q ρ₁ - lamOf q ρ)) := by
      linarith only [hineq2]
    have hB : TM235.F 0 - (2 * c + 4 * eS6) * TM235.f 0
        < TM235.F 0 - (252/1000) * TM235.f 0 := by
      refine lt_of_le_of_lt (le_trans hA hmono) ?_
      linarith only [rowCert_2]
    linarith only [hB, hKf]
  by_cases hcase3 : ((22:ℝ)/125) ≤ lamOf q ρ₁
  · -- row 3: `λ₁ ∈ [(22:ℝ)/125, (37:ℝ)/200]`
    have hcov : 2 * Real.log (1 / lamOf q ρ₁) ≤ ((697:ℝ)/200) := cov_3 hlam1pos hcase3
    have hb : lamOf q ρ₁ ≤ ((37:ℝ)/200) := by
      have hlt := not_le.mp hcase2
      linarith only [hlt]
    have hv : lamOf q ρ ≤ ((697:ℝ)/200) := le_of_lt (lt_of_lt_of_le hlam02L hcov)
    have hmono := TestFn_E_mono TM235 hv hb hlam1nn
    have hKf : (2 * c + 4 * eS6) * TM235.f 0 ≤ (252/1000) * TM235.f 0 :=
      mul_le_mul_of_nonneg_right hK TM235.f0_pos.le
    have hA : TM235.F 0 - (2 * c + 4 * eS6) * TM235.f 0
        ≤ 2 * (TM235.F (-(lamOf q ρ)) - TM235.F (lamOf q ρ₁ - lamOf q ρ)) := by
      linarith only [hineq2]
    have hB : TM235.F 0 - (2 * c + 4 * eS6) * TM235.f 0
        < TM235.F 0 - (252/1000) * TM235.f 0 := by
      refine lt_of_le_of_lt (le_trans hA hmono) ?_
      linarith only [rowCert_3]
    linarith only [hB, hKf]
  by_cases hcase4 : ((167:ℝ)/1000) ≤ lamOf q ρ₁
  · -- row 4: `λ₁ ∈ [(167:ℝ)/1000, (22:ℝ)/125]`
    have hcov : 2 * Real.log (1 / lamOf q ρ₁) ≤ ((359:ℝ)/100) := cov_4 hlam1pos hcase4
    have hb : lamOf q ρ₁ ≤ ((22:ℝ)/125) := by
      have hlt := not_le.mp hcase3
      linarith only [hlt]
    have hv : lamOf q ρ ≤ ((359:ℝ)/100) := le_of_lt (lt_of_lt_of_le hlam02L hcov)
    have hmono := TestFn_E_mono TM235 hv hb hlam1nn
    have hKf : (2 * c + 4 * eS6) * TM235.f 0 ≤ (252/1000) * TM235.f 0 :=
      mul_le_mul_of_nonneg_right hK TM235.f0_pos.le
    have hA : TM235.F 0 - (2 * c + 4 * eS6) * TM235.f 0
        ≤ 2 * (TM235.F (-(lamOf q ρ)) - TM235.F (lamOf q ρ₁ - lamOf q ρ)) := by
      linarith only [hineq2]
    have hB : TM235.F 0 - (2 * c + 4 * eS6) * TM235.f 0
        < TM235.F 0 - (252/1000) * TM235.f 0 := by
      refine lt_of_le_of_lt (le_trans hA hmono) ?_
      linarith only [rowCert_4]
    linarith only [hB, hKf]
  by_cases hcase5 : ((157:ℝ)/1000) ≤ lamOf q ρ₁
  · -- row 5: `λ₁ ∈ [(157:ℝ)/1000, (167:ℝ)/1000]`
    have hcov : 2 * Real.log (1 / lamOf q ρ₁) ≤ ((3713:ℝ)/1000) := cov_5 hlam1pos hcase5
    have hb : lamOf q ρ₁ ≤ ((167:ℝ)/1000) := by
      have hlt := not_le.mp hcase4
      linarith only [hlt]
    have hv : lamOf q ρ ≤ ((3713:ℝ)/1000) := le_of_lt (lt_of_lt_of_le hlam02L hcov)
    have hmono := TestFn_E_mono TM235 hv hb hlam1nn
    have hKf : (2 * c + 4 * eS6) * TM235.f 0 ≤ (252/1000) * TM235.f 0 :=
      mul_le_mul_of_nonneg_right hK TM235.f0_pos.le
    have hA : TM235.F 0 - (2 * c + 4 * eS6) * TM235.f 0
        ≤ 2 * (TM235.F (-(lamOf q ρ)) - TM235.F (lamOf q ρ₁ - lamOf q ρ)) := by
      linarith only [hineq2]
    have hB : TM235.F 0 - (2 * c + 4 * eS6) * TM235.f 0
        < TM235.F 0 - (252/1000) * TM235.f 0 := by
      refine lt_of_le_of_lt (le_trans hA hmono) ?_
      linarith only [rowCert_5]
    linarith only [hB, hKf]
  by_cases hcase6 : ((73:ℝ)/500) ≤ lamOf q ρ₁
  · -- row 6: `λ₁ ∈ [(73:ℝ)/500, (157:ℝ)/1000]`
    have hcov : 2 * Real.log (1 / lamOf q ρ₁) ≤ ((1929:ℝ)/500) := cov_6 hlam1pos hcase6
    have hb : lamOf q ρ₁ ≤ ((157:ℝ)/1000) := by
      have hlt := not_le.mp hcase5
      linarith only [hlt]
    have hv : lamOf q ρ ≤ ((1929:ℝ)/500) := le_of_lt (lt_of_lt_of_le hlam02L hcov)
    have hmono := TestFn_E_mono TM24 hv hb hlam1nn
    have hKf : (2 * c + 4 * eS6) * TM24.f 0 ≤ (252/1000) * TM24.f 0 :=
      mul_le_mul_of_nonneg_right hK TM24.f0_pos.le
    have hA : TM24.F 0 - (2 * c + 4 * eS6) * TM24.f 0
        ≤ 2 * (TM24.F (-(lamOf q ρ)) - TM24.F (lamOf q ρ₁ - lamOf q ρ)) := by
      linarith only [hineq3]
    have hB : TM24.F 0 - (2 * c + 4 * eS6) * TM24.f 0
        < TM24.F 0 - (252/1000) * TM24.f 0 := by
      refine lt_of_le_of_lt (le_trans hA hmono) ?_
      linarith only [rowCert_6]
    linarith only [hB, hKf]
  by_cases hcase7 : ((67:ℝ)/500) ≤ lamOf q ρ₁
  · -- row 7: `λ₁ ∈ [(67:ℝ)/500, (73:ℝ)/500]`
    have hcov : 2 * Real.log (1 / lamOf q ρ₁) ≤ ((403:ℝ)/100) := cov_7 hlam1pos hcase7
    have hb : lamOf q ρ₁ ≤ ((73:ℝ)/500) := by
      have hlt := not_le.mp hcase6
      linarith only [hlt]
    have hv : lamOf q ρ ≤ ((403:ℝ)/100) := le_of_lt (lt_of_lt_of_le hlam02L hcov)
    have hmono := TestFn_E_mono TM24 hv hb hlam1nn
    have hKf : (2 * c + 4 * eS6) * TM24.f 0 ≤ (252/1000) * TM24.f 0 :=
      mul_le_mul_of_nonneg_right hK TM24.f0_pos.le
    have hA : TM24.F 0 - (2 * c + 4 * eS6) * TM24.f 0
        ≤ 2 * (TM24.F (-(lamOf q ρ)) - TM24.F (lamOf q ρ₁ - lamOf q ρ)) := by
      linarith only [hineq3]
    have hB : TM24.F 0 - (2 * c + 4 * eS6) * TM24.f 0
        < TM24.F 0 - (252/1000) * TM24.f 0 := by
      refine lt_of_le_of_lt (le_trans hA hmono) ?_
      linarith only [rowCert_7]
    linarith only [hB, hKf]
  by_cases hcase8 : ((61:ℝ)/500) ≤ lamOf q ρ₁
  · -- row 8: `λ₁ ∈ [(61:ℝ)/500, (67:ℝ)/500]`
    have hcov : 2 * Real.log (1 / lamOf q ρ₁) ≤ ((4217:ℝ)/1000) := cov_8 hlam1pos hcase8
    have hb : lamOf q ρ₁ ≤ ((67:ℝ)/500) := by
      have hlt := not_le.mp hcase7
      linarith only [hlt]
    have hv : lamOf q ρ ≤ ((4217:ℝ)/1000) := le_of_lt (lt_of_lt_of_le hlam02L hcov)
    have hmono := TestFn_E_mono TM245 hv hb hlam1nn
    have hKf : (2 * c + 4 * eS6) * TM245.f 0 ≤ (252/1000) * TM245.f 0 :=
      mul_le_mul_of_nonneg_right hK TM245.f0_pos.le
    have hA : TM245.F 0 - (2 * c + 4 * eS6) * TM245.f 0
        ≤ 2 * (TM245.F (-(lamOf q ρ)) - TM245.F (lamOf q ρ₁ - lamOf q ρ)) := by
      linarith only [hineq4]
    have hB : TM245.F 0 - (2 * c + 4 * eS6) * TM245.f 0
        < TM245.F 0 - (252/1000) * TM245.f 0 := by
      refine lt_of_le_of_lt (le_trans hA hmono) ?_
      linarith only [rowCert_8]
    linarith only [hB, hKf]
  by_cases hcase9 : ((109:ℝ)/1000) ≤ lamOf q ρ₁
  · -- row 9: `λ₁ ∈ [(109:ℝ)/1000, (61:ℝ)/500]`
    have hcov : 2 * Real.log (1 / lamOf q ρ₁) ≤ ((4443:ℝ)/1000) := cov_9 hlam1pos hcase9
    have hb : lamOf q ρ₁ ≤ ((61:ℝ)/500) := by
      have hlt := not_le.mp hcase8
      linarith only [hlt]
    have hv : lamOf q ρ ≤ ((4443:ℝ)/1000) := le_of_lt (lt_of_lt_of_le hlam02L hcov)
    have hmono := TestFn_E_mono TM245 hv hb hlam1nn
    have hKf : (2 * c + 4 * eS6) * TM245.f 0 ≤ (252/1000) * TM245.f 0 :=
      mul_le_mul_of_nonneg_right hK TM245.f0_pos.le
    have hA : TM245.F 0 - (2 * c + 4 * eS6) * TM245.f 0
        ≤ 2 * (TM245.F (-(lamOf q ρ)) - TM245.F (lamOf q ρ₁ - lamOf q ρ)) := by
      linarith only [hineq4]
    have hB : TM245.F 0 - (2 * c + 4 * eS6) * TM245.f 0
        < TM245.F 0 - (252/1000) * TM245.f 0 := by
      refine lt_of_le_of_lt (le_trans hA hmono) ?_
      linarith only [rowCert_9]
    linarith only [hB, hKf]
  by_cases hcase10 : ((12:ℝ)/125) ≤ lamOf q ρ₁
  · -- row 10: `λ₁ ∈ [(12:ℝ)/125, (109:ℝ)/1000]`
    have hcov : 2 * Real.log (1 / lamOf q ρ₁) ≤ ((4697:ℝ)/1000) := cov_10 hlam1pos hcase10
    have hb : lamOf q ρ₁ ≤ ((109:ℝ)/1000) := by
      have hlt := not_le.mp hcase9
      linarith only [hlt]
    have hv : lamOf q ρ ≤ ((4697:ℝ)/1000) := le_of_lt (lt_of_lt_of_le hlam02L hcov)
    have hmono := TestFn_E_mono TM245 hv hb hlam1nn
    have hKf : (2 * c + 4 * eS6) * TM245.f 0 ≤ (252/1000) * TM245.f 0 :=
      mul_le_mul_of_nonneg_right hK TM245.f0_pos.le
    have hA : TM245.F 0 - (2 * c + 4 * eS6) * TM245.f 0
        ≤ 2 * (TM245.F (-(lamOf q ρ)) - TM245.F (lamOf q ρ₁ - lamOf q ρ)) := by
      linarith only [hineq4]
    have hB : TM245.F 0 - (2 * c + 4 * eS6) * TM245.f 0
        < TM245.F 0 - (252/1000) * TM245.f 0 := by
      refine lt_of_le_of_lt (le_trans hA hmono) ?_
      linarith only [rowCert_10]
    linarith only [hB, hKf]
  by_cases hcase11 : ((83:ℝ)/1000) ≤ lamOf q ρ₁
  · -- row 11: `λ₁ ∈ [(83:ℝ)/1000, (12:ℝ)/125]`
    have hcov : 2 * Real.log (1 / lamOf q ρ₁) ≤ ((1247:ℝ)/250) := cov_11 hlam1pos hcase11
    have hb : lamOf q ρ₁ ≤ ((12:ℝ)/125) := by
      have hlt := not_le.mp hcase10
      linarith only [hlt]
    have hv : lamOf q ρ ≤ ((1247:ℝ)/250) := le_of_lt (lt_of_lt_of_le hlam02L hcov)
    have hmono := TestFn_E_mono TM25 hv hb hlam1nn
    have hKf : (2 * c + 4 * eS6) * TM25.f 0 ≤ (252/1000) * TM25.f 0 :=
      mul_le_mul_of_nonneg_right hK TM25.f0_pos.le
    have hA : TM25.F 0 - (2 * c + 4 * eS6) * TM25.f 0
        ≤ 2 * (TM25.F (-(lamOf q ρ)) - TM25.F (lamOf q ρ₁ - lamOf q ρ)) := by
      linarith only [hineq5]
    have hB : TM25.F 0 - (2 * c + 4 * eS6) * TM25.f 0
        < TM25.F 0 - (252/1000) * TM25.f 0 := by
      refine lt_of_le_of_lt (le_trans hA hmono) ?_
      linarith only [rowCert_11]
    linarith only [hB, hKf]
  by_cases hcase12 : ((7:ℝ)/100) ≤ lamOf q ρ₁
  · -- row 12: `λ₁ ∈ [(7:ℝ)/100, (83:ℝ)/1000]`
    have hcov : 2 * Real.log (1 / lamOf q ρ₁) ≤ ((5329:ℝ)/1000) := cov_12 hlam1pos hcase12
    have hb : lamOf q ρ₁ ≤ ((83:ℝ)/1000) := by
      have hlt := not_le.mp hcase11
      linarith only [hlt]
    have hv : lamOf q ρ ≤ ((5329:ℝ)/1000) := le_of_lt (lt_of_lt_of_le hlam02L hcov)
    have hmono := TestFn_E_mono TM255 hv hb hlam1nn
    have hKf : (2 * c + 4 * eS6) * TM255.f 0 ≤ (252/1000) * TM255.f 0 :=
      mul_le_mul_of_nonneg_right hK TM255.f0_pos.le
    have hA : TM255.F 0 - (2 * c + 4 * eS6) * TM255.f 0
        ≤ 2 * (TM255.F (-(lamOf q ρ)) - TM255.F (lamOf q ρ₁ - lamOf q ρ)) := by
      linarith only [hineq6]
    have hB : TM255.F 0 - (2 * c + 4 * eS6) * TM255.f 0
        < TM255.F 0 - (252/1000) * TM255.f 0 := by
      refine lt_of_le_of_lt (le_trans hA hmono) ?_
      linarith only [rowCert_12]
    linarith only [hB, hKf]
  by_cases hcase13 : ((29:ℝ)/500) ≤ lamOf q ρ₁
  · -- row 13: `λ₁ ∈ [(29:ℝ)/500, (7:ℝ)/100]`
    have hcov : 2 * Real.log (1 / lamOf q ρ₁) ≤ ((1141:ℝ)/200) := cov_13 hlam1pos hcase13
    have hb : lamOf q ρ₁ ≤ ((7:ℝ)/100) := by
      have hlt := not_le.mp hcase12
      linarith only [hlt]
    have hv : lamOf q ρ ≤ ((1141:ℝ)/200) := le_of_lt (lt_of_lt_of_le hlam02L hcov)
    have hmono := TestFn_E_mono TM255 hv hb hlam1nn
    have hKf : (2 * c + 4 * eS6) * TM255.f 0 ≤ (252/1000) * TM255.f 0 :=
      mul_le_mul_of_nonneg_right hK TM255.f0_pos.le
    have hA : TM255.F 0 - (2 * c + 4 * eS6) * TM255.f 0
        ≤ 2 * (TM255.F (-(lamOf q ρ)) - TM255.F (lamOf q ρ₁ - lamOf q ρ)) := by
      linarith only [hineq6]
    have hB : TM255.F 0 - (2 * c + 4 * eS6) * TM255.f 0
        < TM255.F 0 - (252/1000) * TM255.f 0 := by
      refine lt_of_le_of_lt (le_trans hA hmono) ?_
      linarith only [rowCert_13]
    linarith only [hB, hKf]
  by_cases hcase14 : ((23:ℝ)/500) ≤ lamOf q ρ₁
  · -- row 14: `λ₁ ∈ [(23:ℝ)/500, (29:ℝ)/500]`
    have hcov : 2 * Real.log (1 / lamOf q ρ₁) ≤ ((771:ℝ)/125) := cov_14 hlam1pos hcase14
    have hb : lamOf q ρ₁ ≤ ((29:ℝ)/500) := by
      have hlt := not_le.mp hcase13
      linarith only [hlt]
    have hv : lamOf q ρ ≤ ((771:ℝ)/125) := le_of_lt (lt_of_lt_of_le hlam02L hcov)
    have hmono := TestFn_E_mono TM26 hv hb hlam1nn
    have hKf : (2 * c + 4 * eS6) * TM26.f 0 ≤ (252/1000) * TM26.f 0 :=
      mul_le_mul_of_nonneg_right hK TM26.f0_pos.le
    have hA : TM26.F 0 - (2 * c + 4 * eS6) * TM26.f 0
        ≤ 2 * (TM26.F (-(lamOf q ρ)) - TM26.F (lamOf q ρ₁ - lamOf q ρ)) := by
      linarith only [hineq7]
    have hB : TM26.F 0 - (2 * c + 4 * eS6) * TM26.f 0
        < TM26.F 0 - (252/1000) * TM26.f 0 := by
      refine lt_of_le_of_lt (le_trans hA hmono) ?_
      linarith only [rowCert_14]
    linarith only [hB, hKf]
  by_cases hcase15 : ((9:ℝ)/250) ≤ lamOf q ρ₁
  · -- row 15: `λ₁ ∈ [(9:ℝ)/250, (23:ℝ)/500]`
    have hcov : 2 * Real.log (1 / lamOf q ρ₁) ≤ ((3329:ℝ)/500) := cov_15 hlam1pos hcase15
    have hb : lamOf q ρ₁ ≤ ((23:ℝ)/500) := by
      have hlt := not_le.mp hcase14
      linarith only [hlt]
    have hv : lamOf q ρ ≤ ((3329:ℝ)/500) := le_of_lt (lt_of_lt_of_le hlam02L hcov)
    have hmono := TestFn_E_mono TM265 hv hb hlam1nn
    have hKf : (2 * c + 4 * eS6) * TM265.f 0 ≤ (252/1000) * TM265.f 0 :=
      mul_le_mul_of_nonneg_right hK TM265.f0_pos.le
    have hA : TM265.F 0 - (2 * c + 4 * eS6) * TM265.f 0
        ≤ 2 * (TM265.F (-(lamOf q ρ)) - TM265.F (lamOf q ρ₁ - lamOf q ρ)) := by
      linarith only [hineq8]
    have hB : TM265.F 0 - (2 * c + 4 * eS6) * TM265.f 0
        < TM265.F 0 - (252/1000) * TM265.f 0 := by
      refine lt_of_le_of_lt (le_trans hA hmono) ?_
      linarith only [rowCert_15]
    linarith only [hB, hKf]
  by_cases hcase16 : ((27:ℝ)/1000) ≤ lamOf q ρ₁
  · -- row 16: `λ₁ ∈ [(27:ℝ)/1000, (9:ℝ)/250]`
    have hcov : 2 * Real.log (1 / lamOf q ρ₁) ≤ ((3617:ℝ)/500) := cov_16 hlam1pos hcase16
    have hb : lamOf q ρ₁ ≤ ((9:ℝ)/250) := by
      have hlt := not_le.mp hcase15
      linarith only [hlt]
    have hv : lamOf q ρ ≤ ((3617:ℝ)/500) := le_of_lt (lt_of_lt_of_le hlam02L hcov)
    have hmono := TestFn_E_mono TM265 hv hb hlam1nn
    have hKf : (2 * c + 4 * eS6) * TM265.f 0 ≤ (252/1000) * TM265.f 0 :=
      mul_le_mul_of_nonneg_right hK TM265.f0_pos.le
    have hA : TM265.F 0 - (2 * c + 4 * eS6) * TM265.f 0
        ≤ 2 * (TM265.F (-(lamOf q ρ)) - TM265.F (lamOf q ρ₁ - lamOf q ρ)) := by
      linarith only [hineq8]
    have hB : TM265.F 0 - (2 * c + 4 * eS6) * TM265.f 0
        < TM265.F 0 - (252/1000) * TM265.f 0 := by
      refine lt_of_le_of_lt (le_trans hA hmono) ?_
      linarith only [rowCert_16]
    linarith only [hB, hKf]
  by_cases hcase17 : ((1:ℝ)/50) ≤ lamOf q ρ₁
  · -- row 17: `λ₁ ∈ [(1:ℝ)/50, (27:ℝ)/1000]`
    have hcov : 2 * Real.log (1 / lamOf q ρ₁) ≤ ((3917:ℝ)/500) := cov_17 hlam1pos hcase17
    have hb : lamOf q ρ₁ ≤ ((27:ℝ)/1000) := by
      have hlt := not_le.mp hcase16
      linarith only [hlt]
    have hv : lamOf q ρ ≤ ((3917:ℝ)/500) := le_of_lt (lt_of_lt_of_le hlam02L hcov)
    have hmono := TestFn_E_mono TM27 hv hb hlam1nn
    have hKf : (2 * c + 4 * eS6) * TM27.f 0 ≤ (252/1000) * TM27.f 0 :=
      mul_le_mul_of_nonneg_right hK TM27.f0_pos.le
    have hA : TM27.F 0 - (2 * c + 4 * eS6) * TM27.f 0
        ≤ 2 * (TM27.F (-(lamOf q ρ)) - TM27.F (lamOf q ρ₁ - lamOf q ρ)) := by
      linarith only [hineq9]
    have hB : TM27.F 0 - (2 * c + 4 * eS6) * TM27.f 0
        < TM27.F 0 - (252/1000) * TM27.f 0 := by
      refine lt_of_le_of_lt (le_trans hA hmono) ?_
      linarith only [rowCert_17]
    linarith only [hB, hKf]
  by_cases hcase18 : ((7:ℝ)/500) ≤ lamOf q ρ₁
  · -- row 18: `λ₁ ∈ [(7:ℝ)/500, (1:ℝ)/50]`
    have hcov : 2 * Real.log (1 / lamOf q ρ₁) ≤ ((8547:ℝ)/1000) := cov_18 hlam1pos hcase18
    have hb : lamOf q ρ₁ ≤ ((1:ℝ)/50) := by
      have hlt := not_le.mp hcase17
      linarith only [hlt]
    have hv : lamOf q ρ ≤ ((8547:ℝ)/1000) := le_of_lt (lt_of_lt_of_le hlam02L hcov)
    have hmono := TestFn_E_mono TM275 hv hb hlam1nn
    have hKf : (2 * c + 4 * eS6) * TM275.f 0 ≤ (252/1000) * TM275.f 0 :=
      mul_le_mul_of_nonneg_right hK TM275.f0_pos.le
    have hA : TM275.F 0 - (2 * c + 4 * eS6) * TM275.f 0
        ≤ 2 * (TM275.F (-(lamOf q ρ)) - TM275.F (lamOf q ρ₁ - lamOf q ρ)) := by
      linarith only [hineq10]
    have hB : TM275.F 0 - (2 * c + 4 * eS6) * TM275.f 0
        < TM275.F 0 - (252/1000) * TM275.f 0 := by
      refine lt_of_le_of_lt (le_trans hA hmono) ?_
      linarith only [rowCert_18]
    linarith only [hB, hKf]
  by_cases hcase19 : ((1:ℝ)/100) ≤ lamOf q ρ₁
  · -- row 19: `λ₁ ∈ [(1:ℝ)/100, (7:ℝ)/500]`
    have hcov : 2 * Real.log (1 / lamOf q ρ₁) ≤ ((461:ℝ)/50) := cov_19 hlam1pos hcase19
    have hb : lamOf q ρ₁ ≤ ((7:ℝ)/500) := by
      have hlt := not_le.mp hcase18
      linarith only [hlt]
    have hv : lamOf q ρ ≤ ((461:ℝ)/50) := le_of_lt (lt_of_lt_of_le hlam02L hcov)
    have hmono := TestFn_E_mono TM275 hv hb hlam1nn
    have hKf : (2 * c + 4 * eS6) * TM275.f 0 ≤ (252/1000) * TM275.f 0 :=
      mul_le_mul_of_nonneg_right hK TM275.f0_pos.le
    have hA : TM275.F 0 - (2 * c + 4 * eS6) * TM275.f 0
        ≤ 2 * (TM275.F (-(lamOf q ρ)) - TM275.F (lamOf q ρ₁ - lamOf q ρ)) := by
      linarith only [hineq10]
    have hB : TM275.F 0 - (2 * c + 4 * eS6) * TM275.f 0
        < TM275.F 0 - (252/1000) * TM275.f 0 := by
      refine lt_of_le_of_lt (le_trans hA hmono) ?_
      linarith only [rowCert_19]
    linarith only [hB, hKf]
  by_cases hcase20 : ((7:ℝ)/1000) ≤ lamOf q ρ₁
  · -- row 20: `λ₁ ∈ [(7:ℝ)/1000, (1:ℝ)/100]`
    have hcov : 2 * Real.log (1 / lamOf q ρ₁) ≤ ((4967:ℝ)/500) := cov_20 hlam1pos hcase20
    have hb : lamOf q ρ₁ ≤ ((1:ℝ)/100) := by
      have hlt := not_le.mp hcase19
      linarith only [hlt]
    have hv : lamOf q ρ ≤ ((4967:ℝ)/500) := le_of_lt (lt_of_lt_of_le hlam02L hcov)
    have hmono := TestFn_E_mono TM28 hv hb hlam1nn
    have hKf : (2 * c + 4 * eS6) * TM28.f 0 ≤ (252/1000) * TM28.f 0 :=
      mul_le_mul_of_nonneg_right hK TM28.f0_pos.le
    have hA : TM28.F 0 - (2 * c + 4 * eS6) * TM28.f 0
        ≤ 2 * (TM28.F (-(lamOf q ρ)) - TM28.F (lamOf q ρ₁ - lamOf q ρ)) := by
      linarith only [hineq11]
    have hB : TM28.F 0 - (2 * c + 4 * eS6) * TM28.f 0
        < TM28.F 0 - (252/1000) * TM28.f 0 := by
      refine lt_of_le_of_lt (le_trans hA hmono) ?_
      linarith only [rowCert_20]
    linarith only [hB, hKf]
  · -- the last row: `λ₁ < (7:ℝ)/1000`
    have hb : lamOf q ρ₁ ≤ ((7:ℝ)/1000) := by
      have hlt := not_le.mp hcase20
      linarith only [hlt]
    have hv : lamOf q ρ ≤ ((2737:ℝ)/250) := le_of_lt (lt_of_lt_of_le hlam04e four_exp_le)
    have hmono := TestFn_E_mono TM285 hv hb hlam1nn
    have hKf : (2 * c + 4 * eS6) * TM285.f 0 ≤ (252/1000) * TM285.f 0 :=
      mul_le_mul_of_nonneg_right hK TM285.f0_pos.le
    have hA : TM285.F 0 - (2 * c + 4 * eS6) * TM285.f 0
        ≤ 2 * (TM285.F (-(lamOf q ρ)) - TM285.F (lamOf q ρ₁ - lamOf q ρ)) := by
      linarith only [hineq12]
    have hB : TM285.F 0 - (2 * c + 4 * eS6) * TM285.f 0
        < TM285.F 0 - (252/1000) * TM285.f 0 := by
      refine lt_of_le_of_lt (le_trans hA hmono) ?_
      linarith only [rowCert_21]
    linarith only [hB, hKf]

end Work.ZeroFreeTables.lam0w

