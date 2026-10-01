import Mathlib
import Submission.Work.LinnikAreas.Setup
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_ballZeroCount_uniform
import Submission.Commons.NumberTheory.Linnik.completedL_ballZeroCount
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip

open DirichletCharacter Complex
open scoped Classical BigOperators

noncomputable section

namespace Work.LinnikAreas

/-- At a point of a set on which `f` is analytic, the divisor of `f` equals the analytic
vanishing order (as an integer). -/
lemma divisor_eq_analyticOrderNatAt {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hz : z ∈ U) :
    MeromorphicOn.divisor f U z = (analyticOrderNatAt f z : ℤ) := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hz, (hf z hz).meromorphicOrderAt_eq]
  rcases eq_or_ne (analyticOrderAt f z) ⊤ with h | h
  · rw [h]; simp [analyticOrderNatAt, h]
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
    have h2 : analyticOrderNatAt f z = n := by rw [analyticOrderNatAt, ← hn]; simp
    rw [h2, ← hn]; simp

/-- The primitive character inducing a non-trivial character of level `q` is non-trivial. -/
lemma primitiveCharacter_ne_one' {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro h1
  have h := DirichletCharacter.changeLevel_primitiveCharacter χ
  rw [h1, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h
  exact hχ h.symm

/-- **Zero count vs. ball divisor sum.**  Let `F` be a function all of whose zeros lie in the
open critical strip `0 < Re < 1`.  Then the (multiplicity-weighted) number of zeros of `F` with
`σ ≤ Re ≤ 1` and `|Im| ≤ T` is at most the divisor sum of `F` over the disk
`closedBall (1/2) (T+2)`, which contains all these zeros. -/
lemma sum_if_le_ballDivisor {F : ℂ → ℂ} {σ T : ℝ}
    (han : AnalyticOnNhd ℂ F (Metric.closedBall ((1/2 : ℝ) : ℂ) (T + 2)))
    (hstrip : ∀ u : ℂ, F u = 0 → 0 < u.re ∧ u.re < 1) :
    (∑ᶠ u : ℂ, (if σ ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ T then
        (analyticOrderNatAt F u : ℝ) else 0))
      ≤ ∑ᶠ u : ℂ,
          (((MeromorphicOn.divisor F (Metric.closedBall ((1/2 : ℝ) : ℂ) (T + 2))) u : ℤ) : ℝ) := by
  classical
  set U : Set ℂ := Metric.closedBall ((1/2 : ℝ) : ℂ) (T + 2) with hU
  have hRnn : ∀ u : ℂ, 0 ≤ (((MeromorphicOn.divisor F U u : ℤ)) : ℝ) := by
    intro u
    by_cases hu : u ∈ U
    · exact Commons.NumberTheory.Linnik.divisor_real_nonneg_of_analyticOnNhd han hu
    · have hz : MeromorphicOn.divisor F U u = 0 := by
        rw [MeromorphicOn.divisor_def]; rw [if_neg]; intro h; exact hu h.2
      rw [hz]; simp
  have hpt : ∀ u : ℂ, (if σ ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ T then
      (analyticOrderNatAt F u : ℝ) else 0) ≤ (((MeromorphicOn.divisor F U u : ℤ)) : ℝ) := by
    intro u
    by_cases hc : σ ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ T
    · rw [if_pos hc]
      by_cases hz : analyticOrderNatAt F u = 0
      · rw [hz]; simp only [Nat.cast_zero]; exact hRnn u
      · have hFu : F u = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hz
        have hs := hstrip u hFu
        have huU : u ∈ U := by
          rw [hU, Metric.mem_closedBall, dist_eq_norm]
          have htri : ‖u - ((1/2 : ℝ) : ℂ)‖
              ≤ |(u - ((1/2 : ℝ) : ℂ)).re| + |(u - ((1/2 : ℝ) : ℂ)).im| :=
            Complex.norm_le_abs_re_add_abs_im _
          have hre : (u - ((1/2 : ℝ) : ℂ)).re = u.re - 1/2 := by simp
          have him : (u - ((1/2 : ℝ) : ℂ)).im = u.im := by simp
          rw [hre, him] at htri
          have h4 : |u.re - 1/2| ≤ 1/2 := by
            rw [abs_le]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
          have h5 : |u.im| ≤ T := hc.2.2
          linarith
        rw [divisor_eq_analyticOrderNatAt han huU]
        simp
    · rw [if_neg hc]; exact hRnn u
  have hRfin : Function.HasFiniteSupport
      (fun u : ℂ => (((MeromorphicOn.divisor F U u : ℤ)) : ℝ)) := by
    have hZ : (Function.support (fun u : ℂ => (MeromorphicOn.divisor F U u : ℤ))).Finite := by
      simpa [Function.HasFiniteSupport] using
        (MeromorphicOn.divisor_support_finite_of_subset (f := F) (U := U) (V := U)
          han.meromorphicOn (by rw [hU]; exact isCompact_closedBall _ _) (le_refl U))
    refine hZ.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    exact hu (by exact_mod_cast h0)
  have hffin : Function.HasFiniteSupport
      (fun u : ℂ => if σ ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ T then
        (analyticOrderNatAt F u : ℝ) else 0) :=
    hRfin.subset (by
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro hR0
      refine hu (le_antisymm ?_ ?_)
      · simpa [hR0] using hpt u
      · by_cases hc : σ ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ T <;> simp [hc])
  exact finsum_le_finsum' hffin hRfin hpt

end Work.LinnikAreas

namespace Work.LinnikAreas

/-- **Family zero count for the non-principal characters mod `q`.**

There is an absolute constant `c > 0` such that, for every `q ≥ 2`, every `σ ∈ [0,1]` and every
`T ≥ 1`, the total number of zeros (with multiplicity) of the completed L-functions of the
non-principal Dirichlet characters mod `q` in the rectangle `σ ≤ Re ρ ≤ 1`, `|Im ρ| ≤ T` is at
most `c·q·(T+2)·(log(q(T+2)) + 2)`. -/
theorem FamilyZeroCountNonPrincipal :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q], ∀ σ T : ℝ,
      0 ≤ σ → σ ≤ 1 → 1 ≤ T →
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            Work.LinnikAreas.zeroCountIn χ σ T)
          ≤ c * (q : ℝ) * (T + 2) * (Real.log ((q : ℝ) * (T + 2)) + 2) := by
  obtain ⟨c₁, hc₁, hball⟩ :=
    Commons.NumberTheory.DirichletCharacter.completedL_ballZeroCount_uniform
  refine ⟨6 * c₁, by positivity, ?_⟩
  intro q hq hqne σ T hσ0 hσ1 hT
  have hqpos : (0 : ℕ) < q := by omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hT2 : (0 : ℝ) < T + 2 := by linarith
  have hT2ge1 : (1 : ℝ) ≤ T + 2 := by linarith
  have h2q : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have h3T : (3 : ℝ) ≤ T + 2 := by linarith
  have h6 : (6 : ℝ) ≤ (q : ℝ) * (T + 2) := by
    calc (6 : ℝ) = 2 * 3 := by norm_num
      _ ≤ (q : ℝ) * (T + 2) := mul_le_mul h2q h3T (by norm_num) (by linarith)
  have hLnn : 0 ≤ Real.log ((q : ℝ) * (T + 2)) := Real.log_nonneg (by linarith)
  have hc1' : 0 ≤ c₁ := le_of_lt hc₁
  have hnorm : ‖((1/2 : ℝ) : ℂ)‖ = 1/2 := by norm_num
  -- cardinality of the family is at most `q`
  have hcard : ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) ≤ (q : ℝ) := by
    have h1 : (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card ≤ q.totient := by
      calc (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card
          ≤ (Finset.univ : Finset (DirichletCharacter ℂ q)).card := Finset.card_erase_le
        _ = Fintype.card (DirichletCharacter ℂ q) := Finset.card_univ
        _ = Nat.card (DirichletCharacter ℂ q) := (Nat.card_eq_fintype_card).symm
        _ = q.totient := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    calc ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) ≤ (q.totient : ℝ) := by
          exact_mod_cast h1
      _ ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  -- per-character bound
  have hper : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      Work.LinnikAreas.zeroCountIn χ σ T
        ≤ 6 * c₁ * (T + 2) * (Real.log ((q : ℝ) * (T + 2)) + 2) := by
    intro χ hχmem
    have hχ : χ ≠ 1 := (Finset.mem_erase.mp hχmem).1
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hψ1 : χ.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one' hχ
    have hψprim : χ.primitiveCharacter.IsPrimitive :=
      DirichletCharacter.primitiveCharacter_isPrimitive χ
    have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall ((1/2 : ℝ) : ℂ) (T + 2)) :=
      Commons.NumberTheory.Linnik.completedLFunction_analyticOnNhd χ.primitiveCharacter hψ1 _
    have hstrip : ∀ u : ℂ,
        DirichletCharacter.completedLFunction χ.primitiveCharacter u = 0 → 0 < u.re ∧ u.re < 1 :=
      fun u hu =>
        Commons.NumberTheory.DirichletCharacter.zerosInStrip χ.primitiveCharacter hψ1 hψprim u hu
    have hcmp := sum_if_le_ballDivisor
      (F := DirichletCharacter.completedLFunction χ.primitiveCharacter) (σ := σ) han hstrip
    have hzceq : Work.LinnikAreas.zeroCountIn χ σ T
        = (∑ᶠ u : ℂ, (if σ ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ T then
            (analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) u : ℝ)
            else 0)) := rfl
    rw [hzceq]
    have hb := hball (χ := χ.primitiveCharacter) hψ1 hψprim ((1/2 : ℝ) : ℂ) (T + 2) (by linarith)
    refine le_trans hcmp (le_trans hb ?_)
    have hlog1 : Real.log (‖((1/2 : ℝ) : ℂ)‖ + (T + 2) + 2)
        ≤ Real.log ((q : ℝ) * (T + 2)) := by
      apply Real.log_le_log
      · have hn := norm_nonneg (((1/2 : ℝ) : ℂ)); linarith
      · rw [hnorm]
        have hmul : 0 ≤ ((q : ℝ) - 2) * T := mul_nonneg (by linarith) (by linarith)
        nlinarith [h2q, hT, hmul]
    have hlogN : Real.log (((χ.conductor : ℕ) : ℝ)) ≤ Real.log ((q : ℝ) * (T + 2)) := by
      apply Real.log_le_log
      · exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
      · have hNq : ((χ.conductor : ℕ) : ℝ) ≤ (q : ℝ) := by
          exact_mod_cast (Nat.le_of_dvd hqpos χ.conductor_dvd_level)
        calc ((χ.conductor : ℕ) : ℝ) ≤ (q : ℝ) := hNq
          _ = (q : ℝ) * 1 := by ring
          _ ≤ (q : ℝ) * (T + 2) := mul_le_mul_of_nonneg_left hT2ge1 (le_of_lt hqR)
    have hbrknn : 0 ≤ Real.log (‖((1/2 : ℝ) : ℂ)‖ + (T + 2) + 2)
        + Real.log (((χ.conductor : ℕ) : ℝ)) + 2 := by
      have a : 0 ≤ Real.log (‖((1/2 : ℝ) : ℂ)‖ + (T + 2) + 2) :=
        Real.log_nonneg (by have hn := norm_nonneg (((1/2 : ℝ) : ℂ)); linarith)
      have b : 0 ≤ Real.log (((χ.conductor : ℕ) : ℝ)) :=
        Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero)
      linarith
    have hT3' : (T + 2) + 1 ≤ 2 * (T + 2) := by linarith
    have hstep1 := mul_le_mul_of_nonneg_left hT3' hc1'
    have h5 : 0 ≤ c₁ * (2 * (T + 2)) := mul_nonneg hc1' (by linarith)
    have hstep2 : c₁ * ((T + 2) + 1) * (Real.log (‖((1/2 : ℝ) : ℂ)‖ + (T + 2) + 2)
          + Real.log (((χ.conductor : ℕ) : ℝ)) + 2)
        ≤ c₁ * (2 * (T + 2)) * (2 * Real.log ((q : ℝ) * (T + 2)) + 2) := by
      have h3 : Real.log (‖((1/2 : ℝ) : ℂ)‖ + (T + 2) + 2)
          + Real.log (((χ.conductor : ℕ) : ℝ)) + 2 ≤ 2 * Real.log ((q : ℝ) * (T + 2)) + 2 := by
        linarith
      exact mul_le_mul hstep1 h3 hbrknn h5
    have hstep3 : c₁ * (2 * (T + 2)) * (2 * Real.log ((q : ℝ) * (T + 2)) + 2)
        ≤ 6 * c₁ * (T + 2) * (Real.log ((q : ℝ) * (T + 2)) + 2) := by
      have hkey : 0 ≤ 2 * (c₁ * (T + 2)) * (Real.log ((q : ℝ) * (T + 2)) + 4) :=
        mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hc1' (le_of_lt hT2)))
          (by linarith)
      nlinarith [hkey]
    linarith [hstep2, hstep3]
  calc (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          Work.LinnikAreas.zeroCountIn χ σ T)
      ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          (6 * c₁ * (T + 2) * (Real.log ((q : ℝ) * (T + 2)) + 2)) := Finset.sum_le_sum hper
    _ = ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ)
          * (6 * c₁ * (T + 2) * (Real.log ((q : ℝ) * (T + 2)) + 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (q : ℝ) * (6 * c₁ * (T + 2) * (Real.log ((q : ℝ) * (T + 2)) + 2)) := by
        refine mul_le_mul_of_nonneg_right hcard ?_
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc1') (by linarith)) (by linarith)
    _ = 6 * c₁ * (q : ℝ) * (T + 2) * (Real.log ((q : ℝ) * (T + 2)) + 2) := by ring

end Work.LinnikAreas
