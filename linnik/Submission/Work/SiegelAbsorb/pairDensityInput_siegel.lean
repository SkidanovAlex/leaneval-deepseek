import Mathlib
import Submission.Work.SiegelAbsorb.dhCapTrunc
import Submission.Work.SiegelAbsorb.famCount_nearLine
import Submission.Work.SiegelAbsorb.famCountCrudeCorollaries
import Submission.Work.SiegelAbsorb.lamOf_ge_exp_neg
import Submission.Work.LinnikAreas.PairDensityGen

/-!
# U6 of `AREA6_ROUTE_LEAD.md`: the `λ₁`-saving density input from the capped repulsion

The `λ₁`-saving log-free count `Siegel.PairDensityInput` is proved here **without** Montgomery's
sharp large sieve, i.e. without the all-`σ` family count `LogFreeFamHalf (5/2)`.  The only
analytic inputs are the three that the Siegel-absorption route makes available:

* `SiegelAbsorb.deuringHeilbronnCapTrunc` (U5): the capped Deuring–Heilbronn count
  `restCount ≤ C·λ₁·e^{(5/2+16/7)t}`, `5/2 + 16/7 = 67/14 < 24/5`, on the *truncated* range
  `t ≤ θ𝓛`, `θ = 7/100`;
* `SiegelAbsorb.famCount_nearLine` (U4): `famCount q σ 1 ≤ C·e^{(5/2)(1-σ)𝓛}` for `σ ≥ 93/100`;
* `SiegelAbsorb.logFreeFamHalf_crude` (U3): `famCount q σ 1 ≤ C·e^{(9/2)(1-σ)𝓛}` for all
  `σ ∈ [0,1]` (`9/2 < 49/10`);
* `SiegelAbsorb.lamOf_ge_exp_neg` (U2): Siegel's uniform bound `λ₁ ≥ q^{-a}` for every `a > 1/200`.

Fix Siegel data mod `q` and `0 < t ≤ 𝓛 = log q`; take the exponent `c = 24/5 > 9/2`.  Case (a):
`t ≤ θ𝓛` and `λ₁ ≤ ε₀` — U5 directly, `67/14 ≤ 24/5`.  Case (b): `t ≤ θ𝓛` and `λ₁ > ε₀` — the
family count alone gives `pairCount ≤ C e^{(5/2)t} ≤ C e^{(24/5)t}`, and the missing `λ₁` factor
comes from `λ₁ > ε₀`, so `C e^{(5/2)t} ≤ (C/ε₀)·λ₁·e^{(24/5)t}`.  Case (c): `t > θ𝓛`, any `λ₁` —
the crude count gives `pairCount ≤ C₃ e^{(9/2)t} = C₃ e^{(24/5)t}·e^{-(3/10)t}`, and
`e^{-(3/10)t} ≤ e^{-(3/10)θ𝓛} = e^{-(21/1000)𝓛} ≤ λ₁` by U2 with `a = 21/1000`.

Only the truncated range of U5 is needed, which is why no all-`σ` family count at coefficient
`≤ 2.6` (and hence no character AFE / fourth moment) is required.
-/

namespace Work.SiegelAbsorb

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

open Work.LinnikContract

/-- The pair count of `PairDensityInput` is dominated by the family count in `λ`-units:
for `q ≥ 2` and any `t`,
`pairCount χ₁ β₁ t ≤ famCount q (max 0 (1 - t/log q)) 1`. -/
lemma pairCount_le_famCount_max {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ) (t : ℝ) :
    Work.LinnikAreas.Siegel.pairCount χ₁ β₁ t
      ≤ Work.ZeroDensity.famCount q (max 0 (1 - t / Real.log q)) 1 := by
  have h1 := Work.ZeroDensity.Deuring.restCount_le_multCount χ₁ β₁ t
  rw [Work.ZeroDensity.restCount] at h1
  exact le_trans h1 (Work.ZeroDensity.Deuring.multCount_le_famCount hq t)

/-- **U6.** `Siegel.PairDensityInput` from the capped Deuring–Heilbronn repulsion, with the
witness exponent `c = 24/5`; see the module docstring for the three cases. -/
theorem pairDensityInput_siegel {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hrep : Work.LinnikAreas.RepulsionWithCap ε₀ (7 / 16)) :
    Work.LinnikAreas.Siegel.PairDensityInput := by
  -- the three analytic inputs of the Siegel-absorption route
  obtain ⟨Ca, _hCapos, qa, hcap⟩ := deuringHeilbronnCapTrunc hrep
  obtain ⟨Cn, hCnpos, hnear⟩ := famCount_nearLine
  obtain ⟨Cc, hCcpos, qc, hcrude⟩ := logFreeFamHalf_crude
  obtain ⟨qL, hL⟩ := lamOf_ge_exp_neg (a := (21 : ℝ) / 1000) (by norm_num)
  -- the constant `max (max Ca (Cn/ε₀)) Cc + 1`
  set K : ℝ := max (max Ca (Cn / ε₀)) Cc + 1 with hK
  have hCaK : Ca ≤ K := by
    rw [hK]
    linarith [le_max_left Ca (Cn / ε₀), le_max_left (max Ca (Cn / ε₀)) Cc]
  have hCnK : Cn / ε₀ ≤ K := by
    rw [hK]
    linarith [le_max_right Ca (Cn / ε₀), le_max_left (max Ca (Cn / ε₀)) Cc]
  have hCcK : Cc ≤ K := by
    rw [hK]
    linarith [le_max_right (max Ca (Cn / ε₀)) Cc]
  have hKpos : 0 < K := lt_of_lt_of_le hCcpos hCcK
  refine ⟨K, hKpos, 24 / 5, by norm_num, max (max qa (max 2 qc)) qL, ?_⟩
  intro q hq hqne χ₁ β₁ hχ₁ hsq hβ₁ hzm _hlam t ht htlog
  haveI := hqne
  have hqa : qa ≤ q := by omega
  have hq2 : 2 ≤ q := by omega
  have hqc : qc ≤ q := by omega
  have hqL : qL ≤ q := by omega
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hLpos : 0 < Work.LinnikContract.lamOf q (β₁ : ℂ) :=
    Work.LinnikAreas.Siegel.lamOf_pos hχ₁ hβ₁ hzm
  by_cases htθ : t ≤ (7 / 100) * Real.log q
  · by_cases hle : Work.LinnikContract.lamOf q (β₁ : ℂ) ≤ ε₀
    · -- ## (a) `t ≤ θ𝓛`, `λ₁ ≤ ε₀`: the truncated Deuring--Heilbronn count
      have h := hcap q hqa χ₁ β₁ hχ₁ hsq hβ₁ hzm hle t ht htθ
      rw [Work.ZeroDensity.restCount] at h
      calc Work.LinnikAreas.Siegel.pairCount χ₁ (β₁ : ℂ) t
          ≤ Ca * Work.LinnikContract.lamOf q (β₁ : ℂ) * Real.exp ((5 / 2 + 16 / 7) * t) := h
        _ ≤ K * Work.LinnikContract.lamOf q (β₁ : ℂ) * Real.exp ((24 / 5) * t) := by
            have hE : Real.exp ((5 / 2 + 16 / 7) * t) ≤ Real.exp ((24 / 5) * t) := by
              apply Real.exp_le_exp.mpr
              have hc : (5 : ℝ) / 2 + 16 / 7 ≤ 24 / 5 := by norm_num
              nlinarith [ht]
            calc Ca * Work.LinnikContract.lamOf q (β₁ : ℂ)
                    * Real.exp ((5 / 2 + 16 / 7) * t)
                ≤ K * Work.LinnikContract.lamOf q (β₁ : ℂ)
                    * Real.exp ((5 / 2 + 16 / 7) * t) :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hCaK hLpos.le) (Real.exp_nonneg _)
              _ ≤ K * Work.LinnikContract.lamOf q (β₁ : ℂ) * Real.exp ((24 / 5) * t) :=
                  mul_le_mul_of_nonneg_left hE (mul_nonneg hKpos.le hLpos.le)
    · -- ## (b) `t ≤ θ𝓛`, `λ₁ > ε₀`: the near-line family count suffices
      have hgt : ε₀ < Work.LinnikContract.lamOf q (β₁ : ℂ) := not_le.mp hle
      have hσ0 : 0 ≤ 1 - t / Real.log q := by
        have : t / Real.log q ≤ 1 := (div_le_one hlogq).mpr htlog
        linarith
      have hσ93 : 93 / 100 ≤ 1 - t / Real.log q := by
        have h1 : t / Real.log q ≤ 7 / 100 := (div_le_iff₀ hlogq).mpr (by linarith [htθ])
        linarith
      have hσ1 : 1 - t / Real.log q ≤ 1 := by
        have : 0 ≤ t / Real.log q := div_nonneg (le_of_lt ht) hlogq.le
        linarith
      have hstep : Work.LinnikAreas.Siegel.pairCount χ₁ (β₁ : ℂ) t
          ≤ Work.ZeroDensity.famCount q (1 - t / Real.log q) 1 := by
        have h1 := pairCount_le_famCount_max hq2 χ₁ (β₁ : ℂ) t
        rwa [max_eq_right hσ0] at h1
      have hfam := hnear q hq2 (1 - t / Real.log q) 1 hσ93 hσ1 le_rfl
      have hEq : (1 - (1 - t / Real.log q)) * Real.log q = t := by
        rw [sub_sub_cancel]
        exact div_mul_cancel₀ t hlogq.ne'
      rw [hEq, Real.one_rpow, mul_one] at hfam
      -- the `λ₁` factor from `λ₁ > ε₀`
      have hCnL : Cn ≤ (Cn / ε₀) * Work.LinnikContract.lamOf q (β₁ : ℂ) := by
        have h1 : (1 : ℝ) ≤ Work.LinnikContract.lamOf q (β₁ : ℂ) / ε₀ :=
          (one_le_div hε₀).mpr (le_of_lt hgt)
        calc Cn = Cn * 1 := (mul_one Cn).symm
          _ ≤ Cn * (Work.LinnikContract.lamOf q (β₁ : ℂ) / ε₀) :=
              mul_le_mul_of_nonneg_left h1 hCnpos.le
          _ = (Cn / ε₀) * Work.LinnikContract.lamOf q (β₁ : ℂ) := by ring
      calc Work.LinnikAreas.Siegel.pairCount χ₁ (β₁ : ℂ) t
          ≤ Work.ZeroDensity.famCount q (1 - t / Real.log q) 1 := hstep
        _ ≤ Cn * Real.exp ((5 / 2) * t) := hfam
        _ ≤ K * Work.LinnikContract.lamOf q (β₁ : ℂ) * Real.exp ((24 / 5) * t) := by
            have hE : Real.exp ((5 / 2) * t) ≤ Real.exp ((24 / 5) * t) := by
              apply Real.exp_le_exp.mpr
              have hc : (5 : ℝ) / 2 ≤ 24 / 5 := by norm_num
              nlinarith [ht]
            calc Cn * Real.exp ((5 / 2) * t)
                ≤ Cn * Real.exp ((24 / 5) * t) :=
                  mul_le_mul_of_nonneg_left hE hCnpos.le
              _ ≤ ((Cn / ε₀) * Work.LinnikContract.lamOf q (β₁ : ℂ))
                    * Real.exp ((24 / 5) * t) :=
                  mul_le_mul_of_nonneg_right hCnL (Real.exp_nonneg _)
              _ = (Cn / ε₀) * Work.LinnikContract.lamOf q (β₁ : ℂ)
                    * Real.exp ((24 / 5) * t) := by ring
              _ ≤ K * Work.LinnikContract.lamOf q (β₁ : ℂ) * Real.exp ((24 / 5) * t) :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hCnK hLpos.le) (Real.exp_nonneg _)
  · -- ## (c) `t > θ𝓛`, any `λ₁`: the crude family count and Siegel's lower bound for `λ₁`
    have htθ' : (7 / 100) * Real.log q < t := not_le.mp htθ
    set σ : ℝ := max 0 (1 - t / Real.log q) with hσdef
    have hσ0 : 0 ≤ σ := by rw [hσdef]; exact le_max_left _ _
    have hσ1 : σ ≤ 1 := by
      rw [hσdef]
      refine max_le (by norm_num) ?_
      have : 0 ≤ t / Real.log q := div_nonneg (le_of_lt ht) hlogq.le
      linarith
    have hstep : Work.LinnikAreas.Siegel.pairCount χ₁ (β₁ : ℂ) t
        ≤ Work.ZeroDensity.famCount q σ 1 := by
      rw [hσdef]
      exact pairCount_le_famCount_max hq2 χ₁ (β₁ : ℂ) t
    have hfam := hcrude q hqc σ hσ0 hσ1
    have hem : 1 - σ ≤ t / Real.log q := by
      rw [hσdef]
      rcases le_total 0 (1 - t / Real.log q) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    have hexp_le : (1 - σ) * Real.log q ≤ t := by
      have h1 : (1 - σ) * Real.log q ≤ (t / Real.log q) * Real.log q :=
        mul_le_mul_of_nonneg_right hem hlogq.le
      have h2 : (t / Real.log q) * Real.log q = t := by field_simp
      linarith
    have hfamt : Work.ZeroDensity.famCount q σ 1 ≤ Cc * Real.exp ((9 / 2) * t) := by
      calc Work.ZeroDensity.famCount q σ 1
          ≤ Cc * Real.exp ((9 / 2) * ((1 - σ) * Real.log q)) := hfam
        _ ≤ Cc * Real.exp ((9 / 2) * t) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCcpos.le
            exact mul_le_mul_of_nonneg_left hexp_le (by norm_num)
    have hEq : Real.exp ((9 / 2) * t)
        = Real.exp ((24 / 5) * t) * Real.exp (-(3 / 10) * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    -- Siegel's lower bound `λ₁ ≥ q^{-21/1000}` against the gap `9/2 → 24/5`
    have hlamlb : Real.exp (-(3 / 10) * t) ≤ Work.LinnikContract.lamOf q (β₁ : ℂ) := by
      refine le_trans (Real.exp_le_exp.mpr ?_) (hL q hqL χ₁ β₁ hχ₁ hsq hβ₁ hzm)
      have h1 : (21 / 1000) * Real.log q ≤ (3 / 10) * t := by
        have h2 := mul_lt_mul_of_pos_left htθ' (by norm_num : (0 : ℝ) < 3 / 10)
        have h3 : (3 / 10) * ((7 / 100) * Real.log q) = (21 / 1000) * Real.log q := by ring
        linarith
      linarith
    calc Work.LinnikAreas.Siegel.pairCount χ₁ (β₁ : ℂ) t
        ≤ Work.ZeroDensity.famCount q σ 1 := hstep
      _ ≤ Cc * Real.exp ((9 / 2) * t) := hfamt
      _ = Cc * (Real.exp ((24 / 5) * t) * Real.exp (-(3 / 10) * t)) := by rw [hEq]
      _ ≤ Cc * (Real.exp ((24 / 5) * t) * Work.LinnikContract.lamOf q (β₁ : ℂ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hlamlb (Real.exp_nonneg _)) hCcpos.le
      _ = Cc * Work.LinnikContract.lamOf q (β₁ : ℂ) * Real.exp ((24 / 5) * t) := by ring
      _ ≤ K * Work.LinnikContract.lamOf q (β₁ : ℂ) * Real.exp ((24 / 5) * t) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCcK hLpos.le) (Real.exp_nonneg _)

end

end Work.SiegelAbsorb
