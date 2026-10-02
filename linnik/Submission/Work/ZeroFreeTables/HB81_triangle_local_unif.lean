/-
# ZeroFreeTables — `HB81_triangle_local_unif`

HB's §8.1 triangle inequality (the engine behind Lemma 8.1 of Heath-Brown's paper) in the
vocabulary of the frozen contract, in the **uniform in the box height** form: the threshold `q₀`
does not depend on `Hb`.

This is `Work.ZeroFreeTables.HB81_triangle_local` (proved in
`Submission/Work/ZeroFreeTables/HB81_capped.lean`) with the box height `Hb` moved from a parameter
of the theorem to a `∀`-binder *after* the threshold.  The move is legitimate because the engine
`Work.LinnikAreas.DhRepel.dhTrianglePtH` does not take `Hb` as an argument at all: the box height
enters only as a hypothesis of the returned proposition, so every threshold produced in the proof
(`DhRepel.dhTrianglePtH`, `DhCapped.siegelZeroSimple'`, `log_unbounded_nat`) is automatically
independent of `Hb`.  The two `private` helper lemmas of `HB81_capped.lean` used by the proof are
copied here (they are `private` there, hence not importable).

Consumers (the χ₁-window argument) obtain the box height from a pigeonhole, so they cannot name it
in advance; this form lets them extract the threshold first.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HB81_capped
import Submission.Work.LinnikAreas.DhRepel.dhTrianglePtH
import Submission.Work.LinnikAreas.DhCapped.SiegelSimple
import Submission.Work.LinnikAreas.log_unbounded_nat

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-! ## Helper lemmas copied from `HB81_capped.lean` (they are `private` there) -/


/-! ## Bridging the frozen contract to the §6 triangle of Heath-Brown -/

/-- The divisor of the completed `L`-function at a point of the disc equals `zeroMult`. -/
private theorem hb81u_divisor_eq_zeroMult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hχ : χ ≠ 1) {ρ : ℂ} {R : ℝ} (hmem : ρ ∈ Metric.closedBall (0:ℂ) R) :
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall (0:ℂ) R)) ρ = (Work.LinnikContract.zeroMult χ ρ : ℤ) := by
  have hpc : χ.primitiveCharacter ≠ 1 :=
    Work.LinnikAreas.OtherCharRepel.primitiveCharacter_ne_one χ hχ
  have hdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter) :=
    DirichletCharacter.differentiable_completedLFunction hpc
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall (0:ℂ) R) := fun z _ => hdiff.analyticAt z
  have hmer : MeromorphicOn (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall (0:ℂ) R) := han.meromorphicOn
  have hAn : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter) ρ :=
    hdiff.analyticAt ρ
  have htop : analyticOrderAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) ρ ≠ ⊤ :=
    Work.LinnikAreas.OtherCharRepel.completedLFunction_analyticOrderAt_ne_top
      χ.primitiveCharacter hpc ρ
  rw [MeromorphicOn.divisor_apply hmer hmem, hAn.meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt htop, ENat.map_natCast, WithTop.untop₀_coe]
  rfl

/-- Box maximality of `ρ₀` among the `zeroMult`-zeros of `χ₁` transfers to the `L`-function
maximality hypothesis of the §6 triangle. -/
private theorem hb81u_max_of_min {q : ℕ} [NeZero q] (hq2 : 2 ≤ q)
    (χ₁ : DirichletCharacter ℂ q) [NeZero χ₁.conductor] {ρ₁ ρ₀ : ℂ} {Hb : ℝ}
    (hχ₁ : χ₁ ≠ 1) (him1 : ρ₁.im = 0) (hρ0re : 0 < ρ₀.re)
    (hmax : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u ≠ 0 → |u.im| ≤ Hb →
      u = ρ₁ ∨ Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamOf q u) :
    ∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 → |u.im| ≤ Hb →
      u = ((ρ₁.re : ℝ) : ℂ) ∨ u.re ≤ ρ₀.re := by
  have hρ1eq : ρ₁ = ((ρ₁.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him1]
  have hχstar : χ₁.primitiveCharacter ≠ 1 :=
    Work.LinnikAreas.OtherCharRepel.primitiveCharacter_ne_one χ₁ hχ₁
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  intro u hu him
  by_cases hu1 : u = ((ρ₁.re : ℝ) : ℂ)
  · exact Or.inl hu1
  · refine Or.inr ?_
    by_cases hre : u.re ≤ 0
    · linarith only [hρ0re, hre]
    · push_neg at hre
      have hγ : χ₁.primitiveCharacter.gammaFactor u ≠ 0 :=
        Work.LinnikAreas.OtherCharRepel.gammaFactor_ne_zero_of_re_pos χ₁.primitiveCharacter hre
      have hu0 : u ≠ 0 := by rintro rfl; simp at hre
      have hcomp : DirichletCharacter.completedLFunction χ₁.primitiveCharacter u = 0 := by
        rw [Work.LinnikAreas.OtherCharRepel.completedLFunction_eq_LFunction_mul_gammaFactor
          χ₁.primitiveCharacter u (Or.inl hu0) hγ, hu, zero_mul]
      have hstrip : u.re < 1 :=
        (Commons.NumberTheory.Linnik.completedL_zero_strip χ₁.primitiveCharacter hχstar
          (DirichletCharacter.primitiveCharacter_isPrimitive χ₁) hcomp).2
      have hzmu : Work.LinnikContract.zeroMult χ₁ u ≠ 0 :=
        (Work.LinnikAreas.OtherCharRepel.zeroMultTransfer χ₁ hχ₁).2.2 u hu hre hstrip
      rcases hmax u hzmu him with h | h
      · exact absurd (h.trans hρ1eq) hu1
      · rw [Work.LinnikContract.lamOf, Work.LinnikContract.lamOf] at h
        nlinarith only [h, hlogq]
/-- **HB's `§8.1` triangle inequality with an `Hb`-independent threshold.**

This is `Work.ZeroFreeTables.HB81_triangle_local` with the box height `Hb` moved from a parameter
of the theorem to a `∀`-binder *after* the threshold `q₀`: beyond `q₀` — which depends only on
`x, εL, δ, c` — the §6 triangle inequality of HB's Lemma 8.1 holds for every real `χ₁` with a real
exceptional zero `ρ₁`, every other `zeroMult`-zero `ρ₀` that is `λ`-minimal in the box
`|Im| ≤ Hb` (any height `Hb` at all) and satisfies `|ρ₀.im| + δ ≤ Hb` and
`|ρ₀.im| ≤ 10 log q`. -/
theorem HB81_triangle_local_unif (x : ℝ) (hx : 0 < x) (εL : ℝ) (hεL : 0 < εL)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (c : ℝ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q)
      [NeZero χ₁.conductor] (ρ₁ ρ₀ : ℂ) (Hb : ℝ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
      Work.LinnikContract.zeroMult χ₁ ρ₀ ≠ 0 → ρ₀ ≠ ρ₁ →
      (∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u ≠ 0 → |u.im| ≤ Hb → u ≠ ρ₁ →
        Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamOf q u) →
      |ρ₀.im| + δ ≤ Hb → |ρ₀.im| ≤ 10 * Real.log (q : ℝ) →
      Work.LinnikContract.lamOf q ρ₁ ≤ 1 / 100 →
      Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamMax q →
      Commons.NumberTheory.Linnik.L52Hyp χ₁ c εL δ →
      0 ≤ 2 * (∫ t in (0:ℝ)..x, Real.exp (Work.LinnikContract.lamOf q ρ₀ * t) * (x - t))
        - 2 * (∫ t in (0:ℝ)..x,
            Real.exp ((Work.LinnikContract.lamOf q ρ₀ - Work.LinnikContract.lamOf q ρ₁) * t) * (x - t))
        - x ^ 2 / 2 + (2 * c + 4 * εL) * x := by
  obtain ⟨qT, hT⟩ := Work.LinnikAreas.DhRepel.dhTrianglePtH x hx εL hεL δ hδ0 hδ1 c
  obtain ⟨qS, hS⟩ := Work.LinnikAreas.DhCapped.siegelZeroSimple'
  obtain ⟨qL, hL⟩ := Work.LinnikAreas.log_unbounded_nat
    (max 100 (max (1 / (100 * δ)) (4 / (9 * δ ^ 2))))
  refine ⟨max (max qT qS) (max qL 3), ?_⟩
  intro q hq _inst χ₁ _instc ρ₁ ρ₀ Hb hmin hsq him hzm0 hne hmax0 hHb hγ10 h100 hcap H
  have hqT : qT ≤ q :=
    le_trans (le_max_left qT qS) (le_trans (le_max_left (max qT qS) (max qL 3)) hq)
  have hqS : qS ≤ q :=
    le_trans (le_max_right qT qS) (le_trans (le_max_left (max qT qS) (max qL 3)) hq)
  have hqL : qL ≤ q :=
    le_trans (le_max_left qL 3) (le_trans (le_max_right (max qT qS) (max qL 3)) hq)
  have hq3 : 3 ≤ q :=
    le_trans (le_max_right qL 3) (le_trans (le_max_right (max qT qS) (max qL 3)) hq)
  have hq2 : 2 ≤ q := by omega
  have hlogq : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hB1 : (100:ℝ) ≤ max 100 (max (1 / (100 * δ)) (4 / (9 * δ ^ 2))) := le_max_left _ _
  have hB2 : 1 / (100 * δ) ≤ max 100 (max (1 / (100 * δ)) (4 / (9 * δ ^ 2))) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hB3 : 4 / (9 * δ ^ 2) ≤ max 100 (max (1 / (100 * δ)) (4 / (9 * δ ^ 2))) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hlogq100 : (100:ℝ) ≤ Real.log (q:ℝ) := le_trans hB1 (hL q hqL)
  have hlogqδ : 1 / (100 * δ) ≤ Real.log (q:ℝ) := le_trans hB2 (hL q hqL)
  have hlogqδ2 : 4 / (9 * δ ^ 2) ≤ Real.log (q:ℝ) := le_trans hB3 (hL q hqL)
  have hχ1 : χ₁ ≠ 1 := hmin.1.1.1
  have hzm1 : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hmin.1.1.2.1
  obtain ⟨hρ1re0, hρ1re1, -⟩ := Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ1 hzm1
  obtain ⟨hρ0re0, hρ0re1, -⟩ := Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ1 hzm0
  have hρ1eq : ρ₁ = ((ρ₁.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hSie : Work.LinnikContract.zeroMult χ₁ ((ρ₁.re : ℝ) : ℂ) = 1 :=
    hS q hqS χ₁ ρ₁.re hχ1 hsq hρ1re1
      (by rw [← hρ1eq]; exact hzm1) (by rw [← hρ1eq]; exact h100)
  have hmem1 : ((ρ₁.re : ℝ) : ℂ) ∈ Metric.closedBall (0:ℂ) (|ρ₀.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith only [abs_nonneg ρ₀.im, hρ1re0, hρ1re1, hδ0, hδ1]
  have hmem0 : ρ₀ ∈ Metric.closedBall (0:ℂ) (|ρ₀.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_trans (Complex.norm_le_abs_re_add_abs_im ρ₀) ?_
    have hre : |ρ₀.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith only [hρ0re0, hρ0re1, hδ0, hδ1]
    linarith only [abs_nonneg ρ₀.im, hre, hδ0, hδ1]
  have hdiv1 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|ρ₀.im| + 2))) ((ρ₁.re : ℝ) : ℂ) ≠ 0 := by
    rw [hb81u_divisor_eq_zeroMult χ₁ hχ1 hmem1, hSie]; norm_num
  have hdiv0 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|ρ₀.im| + 2))) ρ₀ ≠ 0 := by
    rw [hb81u_divisor_eq_zeroMult χ₁ hχ1 hmem0]; exact_mod_cast hzm0
  have hmult1 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|ρ₀.im| + 2))) ((ρ₁.re : ℝ) : ℂ) = 1 := by
    rw [hb81u_divisor_eq_zeroMult χ₁ hχ1 hmem1, hSie]; norm_num
  have hne' : ρ₀ ≠ ((ρ₁.re : ℝ) : ℂ) := by rw [hρ1eq] at hne; exact hne
  have hmaxL : ∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 → |u.im| ≤ Hb →
      u = ((ρ₁.re : ℝ) : ℂ) ∨ u.re ≤ ρ₀.re :=
    hb81u_max_of_min hq2 χ₁ hχ1 him hρ0re0 (by
      intro u hzu himu
      by_cases h : u = ρ₁
      · exact Or.inl h
      · exact Or.inr (hmax0 u hzu himu h))
  have hrect1 : Work.LinnikContract.lamOf q ((ρ₁.re : ℝ) : ℂ) ≤ Work.LinnikContract.lamMax q := by
    rw [← hρ1eq]
    have hb : (4:ℝ) ≤ Real.log 100 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have he4 : Real.exp 4 = (Real.exp 1)^4 := by
        rw [show (4:ℝ) = ((4:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
      rw [he4]
      calc (Real.exp 1)^4 ≤ 3^4 := pow_le_pow_left₀ (Real.exp_pos 1).le (le_of_lt Real.exp_one_lt_three) 4
        _ ≤ 100 := by norm_num
    have hd : (1:ℝ) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith only [Real.exp_one_lt_three, hδ0, hδ1]
    have ha : Real.log 100 ≤ Real.log (Real.log (q:ℝ)) := Real.log_le_log (by norm_num) hlogq100
    have hc : Real.log 4 ≤ Real.log (Real.log (Real.log (q:ℝ))) :=
      Real.log_le_log (by norm_num) (by linarith only [ha, hb])
    have h1 : (1/100:ℝ) ≤ Work.LinnikContract.lamMax q := by
      rw [Work.LinnikContract.lamMax]; linarith only [hc, hd]
    linarith only [h100, h1]
  have hβ1 : |1 - ρ₁.re| ≤ δ := by
    have hlt : 0 < 1 - ρ₁.re := by linarith only [hρ1re1]
    rw [abs_of_pos hlt]
    have heq : 1 - ρ₁.re = Work.LinnikContract.lamOf q ρ₁ / Real.log (q:ℝ) := by
      rw [Work.LinnikContract.lamOf]; field_simp
    rw [heq, div_le_iff₀ hlogq]
    have h2 : 1 ≤ Real.log (q:ℝ) * (100 * δ) := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 100 * δ)] at hlogqδ; linarith only [hlogqδ]
    linarith only [h100, h2]
  have hLLL : Real.log (Real.log (Real.log (q:ℝ))) ≤ 2 * Real.sqrt (Real.log (Real.log (q:ℝ))) := by
    have hz0 : (0:ℝ) ≤ Real.log (Real.log (q:ℝ)) := by
      apply Real.log_nonneg; linarith only [hlogq100, hδ0, hδ1]
    have h := Real.log_le_rpow_div hz0 (show (0:ℝ) < (1:ℝ)/2 by norm_num)
    have h2 : (Real.log (Real.log (q:ℝ)))^((1:ℝ)/2) / ((1:ℝ)/2)
        = 2 * Real.sqrt (Real.log (Real.log (q:ℝ))) := by
      rw [Real.sqrt_eq_rpow, div_eq_mul_inv, show ((1:ℝ)/2)⁻¹ = (2:ℝ) by norm_num, mul_comm]
    linarith only [h, h2.le, h2.ge, h2]
  have hβ0 : |1 - ρ₀.re| ≤ δ := by
    have hlt : 0 < 1 - ρ₀.re := by linarith only [hρ0re1]
    rw [abs_of_pos hlt]
    have heq : 1 - ρ₀.re = Work.LinnikContract.lamOf q ρ₀ / Real.log (q:ℝ) := by
      rw [Work.LinnikContract.lamOf]; field_simp
    rw [heq, div_le_iff₀ hlogq]
    have h1 : Real.log (Real.log (q:ℝ)) ≤ Real.log (q:ℝ) := Real.log_le_self hlogq.le
    have h2 : Real.sqrt (Real.log (Real.log (q:ℝ))) ≤ Real.sqrt (Real.log (q:ℝ)) :=
      Real.sqrt_le_sqrt h1
    have h3 : 2 * Real.sqrt (Real.log (q:ℝ)) ≤ 3 * δ * Real.log (q:ℝ) := by
      have hs : 2 / (3 * δ) ≤ Real.sqrt (Real.log (q:ℝ)) := by
        rw [Real.le_sqrt (by positivity) hlogq.le]
        rw [show (2 / (3 * δ))^2 = 4 / (9 * δ^2) by field_simp <;> ring]
        exact hlogqδ2
      have hsnn : 0 ≤ Real.sqrt (Real.log (q:ℝ)) := Real.sqrt_nonneg _
      have hs2 : (Real.sqrt (Real.log (q:ℝ)))^2 = Real.log (q:ℝ) := Real.sq_sqrt hlogq.le
      have hkey : 2 ≤ 3 * δ * Real.sqrt (Real.log (q:ℝ)) := by
        have hmul := mul_le_mul_of_nonneg_right hs (by positivity : (0:ℝ) ≤ 3 * δ)
        have he : 2 / (3 * δ) * (3 * δ) = 2 := div_mul_cancel₀ 2 (by positivity : (3:ℝ) * δ ≠ 0)
        linarith only [hmul, he]
      nlinarith only [hkey, hsnn, hs2, hδ0, hδ1]
    have hlamMax : Work.LinnikContract.lamMax q ≤ δ * Real.log (q:ℝ) := by
      rw [Work.LinnikContract.lamMax]; linarith only [hLLL, h2, h3]
    linarith only [hcap, hlamMax]
  have hy1 : (1:ℝ) ≤ Real.log (Real.log (q:ℝ)) := by
    have h1 : Real.log 100 ≤ Real.log (Real.log (q:ℝ)) := Real.log_le_log (by norm_num) hlogq100
    have h2 : (1:ℝ) ≤ Real.log 100 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]; linarith only [Real.exp_one_lt_three, hδ0, hδ1]
    linarith only [h1, h2]
  have hs1 : (1/100:ℝ) ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := by
    have h : (1:ℝ) ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := Real.one_le_sqrt.mpr hy1
    linarith only [h, hδ0, hδ1]
  have hβ1pt : |1 - ρ₁.re| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
    have hlt : 0 < 1 - ρ₁.re := by linarith only [hρ1re1]
    rw [abs_of_pos hlt]
    have heq : 1 - ρ₁.re = Work.LinnikContract.lamOf q ρ₁ / Real.log (q:ℝ) := by
      rw [Work.LinnikContract.lamOf]; field_simp
    rw [heq]
    have h1 : Work.LinnikContract.lamOf q ρ₁ / Real.log (q:ℝ) ≤ (1/100) / Real.log (q:ℝ) :=
      div_le_div_of_nonneg_right h100 hlogq.le
    have h2 : (1/100:ℝ) / Real.log (q:ℝ)
        ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) :=
      div_le_div_of_nonneg_right hs1 hlogq.le
    linarith only [h1, h2]
  have hρ'pt : |1 - ρ₀.re| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
    have hlt : 0 < 1 - ρ₀.re := by linarith only [hρ0re1]
    rw [abs_of_pos hlt]
    have heq : 1 - ρ₀.re = Work.LinnikContract.lamOf q ρ₀ / Real.log (q:ℝ) := by
      rw [Work.LinnikContract.lamOf]; field_simp
    rw [heq]
    have hsqn : (0:ℝ) ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := Real.sqrt_nonneg _
    have h2 : Work.LinnikContract.lamMax q ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := by
      rw [Work.LinnikContract.lamMax]; linarith only [hLLL, hsqn, hδ0, hδ1, hs1]
    have h1 : Work.LinnikContract.lamOf q ρ₀ / Real.log (q:ℝ)
        ≤ Work.LinnikContract.lamMax q / Real.log (q:ℝ) :=
      div_le_div_of_nonneg_right hcap hlogq.le
    have h3 : Work.LinnikContract.lamMax q / Real.log (q:ℝ)
        ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) :=
      div_le_div_of_nonneg_right h2 hlogq.le
    linarith only [h1, h3]
  have hres := hT q hqT χ₁ hχ1 hsq (β₁ := ρ₁.re) (ρ' := ρ₀) hβ1 hβ0 hHb hγ10 hβ1pt hρ'pt
    hdiv1 hdiv0 hne' hmult1 hmaxL hrect1 hcap H
  rwa [← hρ1eq] at hres

end Work.ZeroFreeTables
