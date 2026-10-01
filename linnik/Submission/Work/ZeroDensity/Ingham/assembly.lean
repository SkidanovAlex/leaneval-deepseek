import Mathlib
import Submission.Work.ZeroDensity.Ingham.Defs
import Submission.Work.ZeroDensity.Ingham.inghamArithmetic
import Submission.Work.ZeroDensity.Zeta.ZetaZeroDefs

/-!
# The assembly of Ingham's zero-density bound for `ζ`

`Work.ZeroDensity.Ingham.inGhamZetaDensity_of_pieces` is the *reduction* of the node
`Work.ZeroDensity.Montgomery.inGhamZetaDensity` to the two large-scale inputs of Montgomery's proof
(Montgomery–Vaughan, *Multiplicative Number Theory*, §28.4.1, at `q = Q = 1`):

* `hsep` — the separated-set reduction (`zetaSeparatedReduction`, proved):
  `N(σ,T) ≤ C T^ε #R` for a maximal `1`-separated set `R` of window zeros;
* `hcomb` — the combined large-values count (`zetaCountCombined`):
  `#R ≤ C T^ε ((log (AT))² + Y^{2-2σ} + (AT)K^{1-2σ} + T^{1/3}(T+K)^{2/3} Y^{(2-4σ)/3})`.

The arithmetic that turns the second bound, at `K = ⌊A T⌋` and `Y = (A T)^{3/(4-2σ)}`, into
`T^{3(1-σ)/(2-σ)+ε}` is the proved lemma `inghamArithmetic`.

## What remains

The body of the proof below is the bookkeeping: choose `A` and the constants, handle the bounded
range of `T` by the σ-blind zero count, apply `hsep` and then `hcomb` with `K = ⌊A T⌋`,
`Y = (A T)^{3/(4-2σ)}`, absorb `(log (AT))² ≤ C_ε T^{ε/2}` and feed the result to
`inghamArithmetic`.  It is currently left as `sorry`; the two inputs are being proved in parallel
in the same directory (`zetaSeparatedReduction` is already proved, `zetaCountCombined` is in
progress).
-/

open scoped Classical BigOperators
open MeasureTheory

namespace Work.ZeroDensity.Ingham


/-- **Bridge**: the `finsum` of the node's statement is the multiplicity-weighted zero count
`Work.ZeroDensity.Zeta.zetaZeroCount`.  (The extra conjunct `analyticOrderNatAt … ≠ 0` in the
indicator of the node's statement is redundant, since a zero of order `0` contributes `0`.) -/
theorem finsum_eq_zetaZeroCount (σ T : ℝ) :
    (∑ᶠ ρ : ℂ, (if analyticOrderNatAt completedRiemannZeta ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
      then (analyticOrderNatAt completedRiemannZeta ρ : ℝ) else 0))
      = Work.ZeroDensity.Zeta.zetaZeroCount σ T := by
  rw [Work.ZeroDensity.Zeta.zetaZeroCount]
  refine finsum_congr (fun ρ => ?_)
  by_cases h : analyticOrderNatAt completedRiemannZeta ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
  · rw [if_pos h, if_pos h.2]
  · rw [if_neg h]
    by_cases h' : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
    · rw [if_pos h']
      have hz : analyticOrderNatAt completedRiemannZeta ρ = 0 := by
        by_contra hc; exact h ⟨hc, h'⟩
      rw [hz]; norm_num
    · rw [if_neg h']

/-- **The assembly**: the separated-set reduction together with the combined large-values count
imply Ingham's zero-density bound for `ζ` in the exact form required by
`Work.ZeroDensity.Montgomery.inGhamZetaDensity`. -/
theorem inGhamZetaDensity_of_pieces
    (hsep : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (σ T : ℝ), 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      ∃ R : Finset ℂ,
        (∀ z ∈ R, analyticOrderNatAt completedRiemannZeta z ≠ 0 ∧
          σ ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T) ∧
        (∀ z ∈ R, ∀ z' ∈ R, z ≠ z' → 1 ≤ |z.im - z'.im|) ∧
        (∀ ρ : ℂ, analyticOrderNatAt completedRiemannZeta ρ ≠ 0 →
          σ ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T → ∃ z ∈ R, |ρ.im - z.im| ≤ 1) ∧
        (Work.ZeroDensity.Zeta.zetaZeroCount σ T ≤ C * T ^ ε * (R.card : ℝ)))
    (hcomb : ∀ (A : ℝ), 6 ≤ A → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (σ T : ℝ), 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
        ∀ (K : ℕ) (Y : ℝ), 1 ≤ K → 1 ≤ Y → Y ≤ (A * T) ^ 2 →
          ∀ R : Finset ℂ,
            (∀ z ∈ R, analyticOrderNatAt completedRiemannZeta z ≠ 0 ∧
              σ ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T) →
            (∀ z ∈ R, ∀ z' ∈ R, z ≠ z' → 1 ≤ |z.im - z'.im|) →
            (R.card : ℝ) ≤ C * T ^ ε *
              ((Real.log (A * T)) ^ 2 + Y ^ (2 - 2 * σ) + (A * T) * (K : ℝ) ^ (1 - 2 * σ)
                + T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3)
                    * Y ^ ((2 - 4 * σ) / 3))) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (σ T : ℝ), (1 : ℝ) / 2 ≤ σ → σ ≤ 1 → 1 ≤ T →
      (∑ᶠ ρ : ℂ, (if analyticOrderNatAt completedRiemannZeta ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
        then (analyticOrderNatAt completedRiemannZeta ρ : ℝ) else 0))
        ≤ C * T ^ (3 * (1 - σ) / (2 - σ) + ε) := by
  intro ε hε
  have hε4 : 0 < ε / 4 := by linarith
  have hε0 : (0:ℝ) < ε^2 := by positivity
  obtain ⟨C₀, hC₀pos, hsep'⟩ := hsep (ε / 4) hε4
  obtain ⟨Cc, hCcpos, hcomb'⟩ := hcomb 6 (by norm_num) (ε / 4) hε4
  obtain ⟨M, hMpos, harith⟩ := Work.ZeroDensity.Ingham.inghamArithmetic 6 (by norm_num)
  obtain ⟨Cb, hCbpos, hblind⟩ := Work.LinnikAreas.PrincipalZeroCount
  have hlogbound : ∀ T : ℝ, 1 ≤ T →
      (Real.log (6*T))^2 ≤ (64 * (6:ℝ)^(ε/4) / ε^2) * T^(ε/4) := by
    intro T hT1
    have hb0 : (0:ℝ) < 6*T := by linarith
    have h1 : Real.log (6*T) ≤ (6*T)^(ε/8) / (ε/8) :=
      Real.log_le_rpow_div (x := 6*T) (ε := ε/8) hb0.le (by linarith)
    have h2 : (6*T)^(ε/8)/(ε/8) = 8*(6*T)^(ε/8)/ε := by field_simp
    rw [h2] at h1
    have h3 : (0:ℝ) ≤ Real.log (6*T) := Real.log_nonneg (by linarith)
    have h5 : (Real.log (6*T))^2 ≤ (8*(6*T)^(ε/8)/ε)^2 := pow_le_pow_left₀ h3 h1 2
    refine le_trans h5 ?_
    have h6 : (8*(6*T)^(ε/8)/ε)^2 = 64*(6*T)^(ε/4)/ε^2 := by
      have h7 : ((6*T)^(ε/8))^2 = (6*T)^(ε/4) := by
        rw [← Real.rpow_natCast ((6*T)^(ε/8)) 2, ← Real.rpow_mul hb0.le]
        congr 1
        push_cast
        ring
      rw [div_pow, mul_pow, h7]
      norm_num
    rw [h6]
    have hmr : (6*T)^(ε/4) = 6^(ε/4) * T^(ε/4) :=
      Real.mul_rpow (x := 6) (y := T) (by norm_num) (by linarith : (0:ℝ) ≤ T)
    rw [hmr]
    have hfin : 64*(6^(ε/4)*T^(ε/4))/ε^2 = 64*6^(ε/4)/ε^2*T^(ε/4) := by ring
    rw [hfin]
  have hCpos : 0 < max (max (Cb * 4 * (Real.log 12 + 2)) 1)
      (C₀ * Cc * (64 * (6:ℝ)^(ε/4) / ε^2 + M) + 1) := by
    have h1 : (1:ℝ) ≤ max (Cb * 4 * (Real.log 12 + 2)) 1 := le_max_right _ _
    have h2 : (1:ℝ) ≤ max (max (Cb * 4 * (Real.log 12 + 2)) 1)
        (C₀ * Cc * (64 * (6:ℝ)^(ε/4) / ε^2 + M) + 1) := le_trans h1 (le_max_left _ _)
    linarith
  refine ⟨max (max (Cb * 4 * (Real.log 12 + 2)) 1)
    (C₀ * Cc * (64 * (6:ℝ)^(ε/4) / ε^2 + M) + 1), hCpos, ?_⟩
  intro σ T hσ hσ1 hT
  rw [finsum_eq_zetaZeroCount σ T]
  set Cf : ℝ := max (max (Cb * 4 * (Real.log 12 + 2)) 1)
    (C₀ * Cc * (64 * (6:ℝ)^(ε/4) / ε^2 + M) + 1) with hCf
  by_cases hT2 : T < 2
  · have hpow : (1:ℝ) ≤ T ^ (3*(1-σ)/(2-σ) + ε) := by
      calc (1:ℝ) = T ^ (0:ℝ) := (Real.rpow_zero T).symm
        _ ≤ T ^ (3*(1-σ)/(2-σ) + ε) :=
            Real.rpow_le_rpow_of_exponent_le hT (by
              have h1 : (0:ℝ) ≤ 1 - σ := by linarith
              have h2 : (0:ℝ) < 2 - σ := by linarith
              have h3 : (0:ℝ) ≤ 3*(1-σ)/(2-σ) := div_nonneg (by linarith) h2.le
              linarith [h3, hε])
    rw [Work.ZeroDensity.Zeta.zetaZeroCount_eq_zeroCountIn (q := 2) σ T]
    have hmain := hblind 2 (by norm_num) σ T (by linarith) hσ1 hT
    have hlogmono : Real.log ((2:ℝ)*(T+2)) + 2 ≤ Real.log 12 + 2 := by
      have h1 : (2:ℝ)*(T+2) ≤ 12 := by linarith
      have h2 : (0:ℝ) < (2:ℝ)*(T+2) := by linarith
      linarith [Real.log_le_log h2 h1]
    have hsig : (0:ℝ) ≤ Real.log ((2:ℝ)*(T+2)) + 2 := by
      linarith [Real.log_nonneg (show (1:ℝ) ≤ (2:ℝ)*(T+2) by linarith)]
    have hbound : Cb * (T+2) * (Real.log ((2:ℝ)*(T+2)) + 2) ≤ Cb * 4 * (Real.log 12 + 2) := by
      have h := mul_le_mul (by linarith : T + 2 ≤ 4) hlogmono hsig (by norm_num : (0:ℝ) ≤ 4)
      calc Cb*(T+2)*(Real.log ((2:ℝ)*(T+2))+2) = Cb*((T+2)*(Real.log ((2:ℝ)*(T+2))+2)) := by ring
        _ ≤ Cb*(4*(Real.log 12+2)) := mul_le_mul_of_nonneg_left h hCbpos.le
        _ = Cb*4*(Real.log 12+2) := by ring
    have hCf1 : Cb*4*(Real.log 12+2) ≤ Cf := by
      rw [hCf]
      exact le_trans (le_max_left _ _) (le_max_left _ _)
    calc Work.LinnikAreas.zeroCountIn (1 : DirichletCharacter ℂ 2) σ T
        ≤ Cb*(T+2)*(Real.log ((2:ℝ)*(T+2))+2) := hmain
      _ ≤ Cb*4*(Real.log 12+2) := hbound
      _ ≤ Cf := hCf1
      _ ≤ Cf * T ^ (3*(1-σ)/(2-σ)+ε) :=
          le_mul_of_one_le_right (le_of_lt hCpos) hpow
  · push_neg at hT2
    have hT0 : (0:ℝ) < T := by linarith
    have hT0' : (0:ℝ) ≤ T := le_of_lt hT0
    have hnn : ∀ a : ℝ, (0:ℝ) ≤ T^a := fun a => Real.rpow_nonneg hT0' a
    have hθnn : (0:ℝ) ≤ 3*(1-σ)/(2-σ) := by
      have h2 : (0:ℝ) < 2 - σ := by linarith
      exact div_nonneg (by linarith) h2.le
    have h6T1 : (1:ℝ) ≤ 6*T := by linarith
    have h4s : (0:ℝ) < 4 - 2*σ := by linarith
    have hexp0 : (0:ℝ) ≤ 3/(4-2*σ) := div_nonneg (by norm_num) h4s.le
    have hexp2 : 3/(4-2*σ) ≤ 2 := by rw [div_le_iff₀ h4s]; linarith
    obtain ⟨R, hRz, hRsep, _hRcov, hNbd⟩ := hsep' σ T hσ hσ1 hT2
    set Y : ℝ := (6*T)^(3/(4-2*σ)) with hYdef
    set K : ℕ := ⌊6*T⌋₊ with hKdef
    have hY1 : 1 ≤ Y := by
      rw [hYdef, ← Real.rpow_zero (6*T)]
      exact Real.rpow_le_rpow_of_exponent_le h6T1 hexp0
    have hY2 : Y ≤ (6*T)^2 := by
      have hr : Y ≤ (6*T)^(2:ℝ) := by
        rw [hYdef]
        exact Real.rpow_le_rpow_of_exponent_le h6T1 hexp2
      simpa [Real.rpow_two] using hr
    have hK1 : 1 ≤ K := by
      rw [hKdef]
      apply Nat.le_floor
      show ((1:ℕ):ℝ) ≤ 6*T
      push_cast
      linarith
    have hcard := hcomb' σ T hσ hσ1 hT2 K Y hK1 hY1 hY2 R hRz hRsep
    have har := harith σ T hσ hσ1 hT2 (ε/4) hε4
    rw [← hYdef, ← hKdef] at har
    have hbracket : (Real.log (6*T))^2 + Y^(2-2*σ) + (6*T)*(K:ℝ)^(1-2*σ)
        + T^((1:ℝ)/3)*(T+(K:ℝ))^((2:ℝ)/3)*Y^((2-4*σ)/3)
        ≤ (64 * (6:ℝ)^(ε/4) / ε^2) * T^(ε/4) + M * T^(3*(1-σ)/(2-σ) + ε/4) := by
      linarith [hlogbound T hT, har]
    have hn1 : (0:ℝ) ≤ C₀ * T^(ε/4) := mul_nonneg hC₀pos.le (hnn _)
    have hn2 : (0:ℝ) ≤ Cc * T^(ε/4) := mul_nonneg hCcpos.le (hnn _)
    have hB : Work.ZeroDensity.Zeta.zetaZeroCount σ T
        ≤ C₀ * Cc * T^(ε/2) * ((64*(6:ℝ)^(ε/4)/ε^2)*T^(ε/4)
            + M*T^(3*(1-σ)/(2-σ)+ε/4)) := by
      calc Work.ZeroDensity.Zeta.zetaZeroCount σ T ≤ C₀ * T^(ε/4) * (R.card:ℝ) := hNbd
        _ ≤ C₀ * T^(ε/4) * (Cc * T^(ε/4) * ((Real.log (6*T))^2 + Y^(2-2*σ)
              + (6*T)*(K:ℝ)^(1-2*σ)
              + T^((1:ℝ)/3)*(T+(K:ℝ))^((2:ℝ)/3)*Y^((2-4*σ)/3))) :=
            mul_le_mul_of_nonneg_left hcard hn1
        _ ≤ C₀ * T^(ε/4) * (Cc * T^(ε/4) * ((64*(6:ℝ)^(ε/4)/ε^2)*T^(ε/4)
              + M*T^(3*(1-σ)/(2-σ)+ε/4))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbracket hn2) hn1
        _ = C₀ * Cc * (T^(ε/4) * T^(ε/4)) * ((64*(6:ℝ)^(ε/4)/ε^2)*T^(ε/4)
              + M*T^(3*(1-σ)/(2-σ)+ε/4)) := by ring
        _ = C₀ * Cc * T^(ε/2) * ((64*(6:ℝ)^(ε/4)/ε^2)*T^(ε/4)
              + M*T^(3*(1-σ)/(2-σ)+ε/4)) := by
            rw [← Real.rpow_add hT0]
            rw [show ε/4 + ε/4 = ε/2 by ring]
    have hC : C₀ * Cc * T^(ε/2) * ((64*(6:ℝ)^(ε/4)/ε^2)*T^(ε/4)
          + M*T^(3*(1-σ)/(2-σ)+ε/4))
        ≤ (C₀ * Cc * (64*(6:ℝ)^(ε/4)/ε^2 + M) + 1) * T^(3*(1-σ)/(2-σ)+ε) := by
      have hexp1 : T^(ε/2) * T^(ε/4) ≤ T^(3*(1-σ)/(2-σ)+ε) := by
        rw [← Real.rpow_add hT0]
        apply Real.rpow_le_rpow_of_exponent_le hT
        nlinarith [hθnn, hε]
      have hexp2' : T^(ε/2) * T^(3*(1-σ)/(2-σ)+ε/4) ≤ T^(3*(1-σ)/(2-σ)+ε) := by
        rw [← Real.rpow_add hT0]
        apply Real.rpow_le_rpow_of_exponent_le hT
        linarith
      have hn3 : (0:ℝ) ≤ C₀ * Cc * (64*(6:ℝ)^(ε/4)/ε^2) := by
        have h6 : (0:ℝ) < (6:ℝ)^(ε/4) := Real.rpow_pos_of_pos (by norm_num) _
        exact mul_nonneg (mul_nonneg hC₀pos.le hCcpos.le)
          (div_nonneg (mul_nonneg (by norm_num) h6.le) hε0.le)
      have hn4 : (0:ℝ) ≤ C₀ * Cc * M := mul_nonneg (mul_nonneg hC₀pos.le hCcpos.le) hMpos.le
      have hn5 : (0:ℝ) ≤ C₀ * Cc * (64*(6:ℝ)^(ε/4)/ε^2 + M) := by
        have hL0 : (0:ℝ) ≤ 64*(6:ℝ)^(ε/4)/ε^2 := by
          have h6 : (0:ℝ) < (6:ℝ)^(ε/4) := Real.rpow_pos_of_pos (by norm_num) _
          exact div_nonneg (mul_nonneg (by norm_num) h6.le) hε0.le
        exact mul_nonneg (mul_nonneg hC₀pos.le hCcpos.le) (by linarith)
      have e1 : C₀*Cc*T^(ε/2)*((64*(6:ℝ)^(ε/4)/ε^2)*T^(ε/4))
          ≤ C₀*Cc*((64*(6:ℝ)^(ε/4)/ε^2)*T^(3*(1-σ)/(2-σ)+ε)) := by
        calc C₀*Cc*T^(ε/2)*((64*(6:ℝ)^(ε/4)/ε^2)*T^(ε/4))
            = (C₀*Cc*(64*(6:ℝ)^(ε/4)/ε^2)) * (T^(ε/2)*T^(ε/4)) := by ring
          _ ≤ (C₀*Cc*(64*(6:ℝ)^(ε/4)/ε^2)) * T^(3*(1-σ)/(2-σ)+ε) :=
              mul_le_mul_of_nonneg_left hexp1 hn3
          _ = C₀*Cc*((64*(6:ℝ)^(ε/4)/ε^2)*T^(3*(1-σ)/(2-σ)+ε)) := by ring
      have e2 : C₀*Cc*T^(ε/2)*(M*T^(3*(1-σ)/(2-σ)+ε/4))
          ≤ C₀*Cc*(M*T^(3*(1-σ)/(2-σ)+ε)) := by
        calc C₀*Cc*T^(ε/2)*(M*T^(3*(1-σ)/(2-σ)+ε/4))
            = (C₀*Cc*M)*(T^(ε/2)*T^(3*(1-σ)/(2-σ)+ε/4)) := by ring
          _ ≤ (C₀*Cc*M)*T^(3*(1-σ)/(2-σ)+ε) := mul_le_mul_of_nonneg_left hexp2' hn4
          _ = C₀*Cc*(M*T^(3*(1-σ)/(2-σ)+ε)) := by ring
      have hlast : C₀*Cc*((64*(6:ℝ)^(ε/4)/ε^2)*T^(3*(1-σ)/(2-σ)+ε))
            + C₀*Cc*(M*T^(3*(1-σ)/(2-σ)+ε))
          ≤ (C₀*Cc*(64*(6:ℝ)^(ε/4)/ε^2 + M) + 1)*T^(3*(1-σ)/(2-σ)+ε) := by
        have hnn2 : (0:ℝ) ≤ T^(3*(1-σ)/(2-σ)+ε) := hnn _
        have heq : C₀*Cc*((64*(6:ℝ)^(ε/4)/ε^2)*T^(3*(1-σ)/(2-σ)+ε))
              + C₀*Cc*(M*T^(3*(1-σ)/(2-σ)+ε))
            = (C₀*Cc*(64*(6:ℝ)^(ε/4)/ε^2 + M))*T^(3*(1-σ)/(2-σ)+ε) := by ring
        rw [heq]
        nlinarith [hnn2, hn5]
      calc C₀*Cc*T^(ε/2)*((64*(6:ℝ)^(ε/4)/ε^2)*T^(ε/4) + M*T^(3*(1-σ)/(2-σ)+ε/4))
          = C₀*Cc*T^(ε/2)*((64*(6:ℝ)^(ε/4)/ε^2)*T^(ε/4))
            + C₀*Cc*T^(ε/2)*(M*T^(3*(1-σ)/(2-σ)+ε/4)) := by ring
        _ ≤ C₀*Cc*((64*(6:ℝ)^(ε/4)/ε^2)*T^(3*(1-σ)/(2-σ)+ε))
            + C₀*Cc*(M*T^(3*(1-σ)/(2-σ)+ε)) := add_le_add e1 e2
        _ ≤ (C₀*Cc*(64*(6:ℝ)^(ε/4)/ε^2 + M) + 1)*T^(3*(1-σ)/(2-σ)+ε) := hlast
    have hCf2 : C₀ * Cc * (64*(6:ℝ)^(ε/4)/ε^2 + M) + 1 ≤ Cf := by
      rw [hCf]
      exact le_max_right _ _
    have hmono := mul_le_mul_of_nonneg_right hCf2 (hnn (3*(1-σ)/(2-σ)+ε))
    linarith [hB, hC, hmono]

end Work.ZeroDensity.Ingham
