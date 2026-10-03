import Mathlib
import Submission.Work.FIArea4.prop_11_1_defs
import Submission.Work.FIArea4.Wdyad_units
import Submission.Work.FIArea4.WdyadStratTau
import Submission.Work.FIArea4.WdyadTargetArith

import Submission.Work.FIArea4.box_lemmas
import Submission.Work.FIArea4.Wdyad_le_trivial
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow

namespace Work.FIArea4

/-- Friedlander–Iwaniec (11.18)–(11.19)/(11.24): the **dual form** of the Jacobi-twisted variance
over the dyadic box, i.e. `Σ_{R<r≤2R} Σ_{S<s≤2S} |Σ_{D<d≤2D} Σ_{a<d} γ_{a d} M((d,a),(r,s))|²`,
is bounded by the FI brace times `‖γ‖²`.  This is the key estimate of *The polynomial X² + Y⁴
captures its primes*, §§11–14 (Pólya–Vinogradov + Poisson summation/smooth majorant, the local
variance `W(d₁,d₂)`, Lemma 11.4, and the removal of the `DR` term of (11.23) by the `r ↔ s`
symmetry).

NOTE for the prover: do **not** import `Submission.Work.FIArea4.prop_11_1` (the full-box target):
this module must be proved from the definitions and the elementary/analytic inputs, and importing
the target would create an import cycle.  The pieces one may use are
`Submission.Work.FIArea4.prop_11_1_dual` (the duality principle `V_sup ≤ W_sup`, proved), the
Pólya–Vinogradov material in `Submission.Work.FIArea4.polya_vinogradov[_coprime]`, Lemma 11.2
(`jacobi_congruence_count`), the trivial local bound `Evar_le_trivial`, and Mathlib's Poisson
summation for Schwartz functions (`SchwartzMap.tsum_eq_tsum_fourier`). -/
theorem prop_11_1_W_dyad :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (D R S : ℕ) (γ : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
        Work.FIArea4.Wdyad D R S γ ≤
          C * (Work.FIArea4.braceV D R S ε
                + (D : ℝ) * (min R S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε))
            * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
                Complex.normSq (γ a d)) := by
  intro ε hε
  -- the `R ≤ S` case (general `γ`, via (11.23) + the trivial bound)
  obtain ⟨Ce, hCepos, hCe⟩ := Wdyad_le_of_RleS ε hε
  -- the (11.23) bracket
  obtain ⟨Cb, hCbpos, hCb⟩ := Wdyad_le_1123 ε hε
  -- Route S: the strata/divisor-count bound at the smaller exponent `ε/2`
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨Cτ, hCτpos, hCτ⟩ := Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (ε / 2) hε2
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Wdyad_units (ε / 2) hε2
  have hunit : ∀ (D₀ R S : ℕ) (β : ℕ → ℕ → ℂ), 1 ≤ D₀ → 1 ≤ R → 1 ≤ S →
      (∀ a d, β a d ≠ 0 → Nat.Coprime a d) →
      Work.FIArea4.Wdyad D₀ R S β ≤ C₁ * Work.FIArea4.WTb D₀ R S (ε / 2) * Work.FIArea4.WE D₀ β :=
    fun D₀ R S β h1 h2 h3 h4 => hC₁ D₀ R S β h1 h2 h3 h4
  obtain ⟨Ks, hKspos, hKs⟩ := Wdyad_le_tau_strata (ε / 2) hε2 C₁ hC₁pos hunit
  -- the constant
  refine ⟨max (max Ce (20 * Cb)) (3 * Cτ * (2 : ℝ) ^ (ε / 2) * Ks) + 1, by positivity, ?_⟩
  intro D R S γ hD hR hS
  have hWE : (0 : ℝ) ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
      Complex.normSq (γ a d) :=
    Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _))
  have hBnn : 0 ≤ Work.FIArea4.braceV D R S ε := WdyadGen.braceV_nonneg D R S ε
  have hTnn : (0 : ℝ) ≤ (D : ℝ) * (min R S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε) := by positivity
  have hTge : Work.FIArea4.braceV D R S ε
      ≤ Work.FIArea4.braceV D R S ε + (D : ℝ) * (min R S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε) := by
    linarith
  have hmax1 : Ce ≤ max (max Ce (20 * Cb)) (3 * Cτ * (2 : ℝ) ^ (ε / 2) * Ks) + 1 :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_add_of_nonneg_right zero_le_one)
  have hmax2 : 20 * Cb ≤ max (max Ce (20 * Cb)) (3 * Cτ * (2 : ℝ) ^ (ε / 2) * Ks) + 1 :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_add_of_nonneg_right zero_le_one)
  have hmax3 : 3 * Cτ * (2 : ℝ) ^ (ε / 2) * Ks
      ≤ max (max Ce (20 * Cb)) (3 * Cτ * (2 : ℝ) ^ (ε / 2) * Ks) + 1 :=
    le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one)
  by_cases hRS : R ≤ S
  · -- **Case `R ≤ S`**: (11.23)/trivial, bracket `braceV ≤ target`
    have h := hCe D R S γ hD hR hS hRS
    calc Work.FIArea4.Wdyad D R S γ ≤ Ce * Work.FIArea4.braceV D R S ε
            * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := h
      _ ≤ (max (max Ce (20 * Cb)) (3 * Cτ * (2 : ℝ) ^ (ε / 2) * Ks) + 1)
            * (Work.FIArea4.braceV D R S ε
                + (D : ℝ) * (min R S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε))
            * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
                Complex.normSq (γ a d)) := by
          apply mul_le_mul_of_nonneg_right _ hWE
          exact mul_le_mul hmax1 hTge hBnn (by positivity)
  · -- **Case `S < R`**
    have hSR' : S < R := not_le.mp hRS
    by_cases hsmall : (S : ℝ) ≤ 16 * (D : ℝ) ^ 2 * (((R : ℝ) * (S : ℝ)) ^ (2 * ε))
    · -- **Route S**: strata + divisor count
      have hτ : ∀ s ∈ Finset.Ioc S (2 * S), ((s.divisors.card : ℕ) : ℝ)
          ≤ Cτ * (2 : ℝ) ^ (ε / 2) * (((R : ℝ) * (S : ℝ)) ^ (ε / 2)) := by
        intro s hs
        obtain ⟨hsgt, hsle⟩ := Finset.mem_Ioc.mp hs
        have hs1 : 1 ≤ s := by omega
        have h1 : ((s.divisors.card : ℕ) : ℝ) ≤ Cτ * (s : ℝ) ^ (ε / 2) := hCτ s
        have h2 : (s : ℝ) ^ (ε / 2) ≤ (((2 * S : ℕ)) : ℝ) ^ (ε / 2) :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hsle) (by linarith)
        have h3 : (((2 * S : ℕ)) : ℝ) ^ (ε / 2)
            = (2 : ℝ) ^ (ε / 2) * ((S : ℝ) ^ (ε / 2)) := by
          rw [show (((2 * S : ℕ)) : ℝ) = 2 * (S : ℝ) by push_cast; ring,
            Real.mul_rpow (by norm_num) (by positivity)]
        have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
        have h4 : (S : ℝ) ^ (ε / 2) ≤ ((R : ℝ) * (S : ℝ)) ^ (ε / 2) := by
          apply Real.rpow_le_rpow (by positivity) _ (by linarith)
          nlinarith [hR1]
        calc ((s.divisors.card : ℕ) : ℝ) ≤ Cτ * (s : ℝ) ^ (ε / 2) := h1
          _ ≤ Cτ * (((2 * S : ℕ)) : ℝ) ^ (ε / 2) := by
              exact mul_le_mul_of_nonneg_left h2 hCτpos.le
          _ = Cτ * (2 : ℝ) ^ (ε / 2) * ((S : ℝ) ^ (ε / 2)) := by rw [h3]; ring
          _ ≤ Cτ * (2 : ℝ) ^ (ε / 2) * (((R : ℝ) * (S : ℝ)) ^ (ε / 2)) := by
              exact mul_le_mul_of_nonneg_left h4 (by positivity)
      have h1 := hKs D R S γ (Cτ * (2 : ℝ) ^ (ε / 2) * (((R : ℝ) * (S : ℝ)) ^ (ε / 2)))
        hD hR hS hSR' hτ
      have h2 := tau_mul_braceV_le ε hε Cτ hCτpos hD hR hS hsmall
      have h2' := mul_le_mul_of_nonneg_left h2 (le_of_lt hKspos)
      calc Work.FIArea4.Wdyad D R S γ
          ≤ Ks * (Cτ * (2 : ℝ) ^ (ε / 2) * (((R : ℝ) * (S : ℝ)) ^ (ε / 2)))
              * Work.FIArea4.braceV D R S (ε / 2)
              * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
                  Complex.normSq (γ a d)) := h1
        _ = Ks * ((Cτ * (2 : ℝ) ^ (ε / 2) * (((R : ℝ) * (S : ℝ)) ^ (ε / 2)))
              * Work.FIArea4.braceV D R S (ε / 2))
              * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
                  Complex.normSq (γ a d)) := by ring
        _ ≤ Ks * (3 * Cτ * (2 : ℝ) ^ (ε / 2) * (Work.FIArea4.braceV D R S ε
                + (D : ℝ) * (min R S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε)))
              * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
                  Complex.normSq (γ a d)) := by
            apply mul_le_mul_of_nonneg_right _ hWE
            exact h2'
        _ ≤ (max (max Ce (20 * Cb)) (3 * Cτ * (2 : ℝ) ^ (ε / 2) * Ks) + 1)
              * (Work.FIArea4.braceV D R S ε
                  + (D : ℝ) * (min R S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε))
              * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
                  Complex.normSq (γ a d)) := by
            apply mul_le_mul_of_nonneg_right _ hWE
            have hTnn' : (0 : ℝ) ≤ Work.FIArea4.braceV D R S ε
                + (D : ℝ) * (min R S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε) := by linarith
            rw [show Ks * (3 * Cτ * (2 : ℝ) ^ (ε / 2) * (Work.FIArea4.braceV D R S ε
                    + (D : ℝ) * (min R S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε)))
                  = 3 * Cτ * (2 : ℝ) ^ (ε / 2) * Ks * (Work.FIArea4.braceV D R S ε
                    + (D : ℝ) * (min R S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε)) by ring]
            exact mul_le_mul hmax3 le_rfl hTnn' (by positivity)
    · -- **Route B**: (11.23) alone
      push_neg at hsmall
      have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
      have hS1 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
      have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
      have hQ1 : (1 : ℝ) ≤ (R : ℝ) * (S : ℝ) := by nlinarith
      have hQ2e : (1 : ℝ) ≤ ((R : ℝ) * (S : ℝ)) ^ (2 * ε) :=
        one_le_RS_rpow (2 * ε) hR hS (by linarith)
      have hDleD2 : (D : ℝ) ≤ (D : ℝ) ^ 2 := by nlinarith [hD1]
      have hD2S : (D : ℝ) ^ 2 ≤ 16 * (D : ℝ) ^ 2 * (((R : ℝ) * (S : ℝ)) ^ (2 * ε)) := by
        nlinarith [hQ2e, hDleD2, hD1]
      have hDS1 : (D : ℝ) ≤ (S : ℝ) := by linarith [hDleD2, hD2S, hsmall]
      have hDS : D ≤ S := by exact_mod_cast hDS1
      have hS2 : (D : ℝ) ≤ (S : ℝ) * (S : ℝ) := by nlinarith [hDS1, hS1]
      have hDleRS2 : (D : ℝ) ≤ (R : ℝ) * (S : ℝ) * (S : ℝ) := by
        have hSR2 : (S : ℝ) * (S : ℝ) ≤ (R : ℝ) * (S : ℝ) * (S : ℝ) := by nlinarith [hR1, hS1]
        linarith [hS2, hSR2]
      have hpow : ((D : ℝ) * (R : ℝ)) ^ ε ≤ ((R : ℝ) * (S : ℝ)) ^ (2 * ε) := by
        have h2e : ((R : ℝ) * (S : ℝ)) ^ (2 * ε)
            = (((R : ℝ) * (S : ℝ)) ^ ε) * (((R : ℝ) * (S : ℝ)) ^ ε) := by
          rw [← Real.rpow_add (by positivity), show ε + ε = 2 * ε by ring]
        rw [h2e]
        have hstep1 : ((D : ℝ) * (R : ℝ)) ^ ε ≤ ((R : ℝ) * (S : ℝ) * (S : ℝ)) ^ ε :=
          Real.rpow_le_rpow (by positivity) (by nlinarith [hDleRS2]) hε.le
        have hstep2 : ((R : ℝ) * (S : ℝ) * (S : ℝ)) ^ ε
            = ((R : ℝ) * (S : ℝ)) ^ ε * (S : ℝ) ^ ε := by
          rw [show (R : ℝ) * (S : ℝ) * (S : ℝ) = ((R : ℝ) * (S : ℝ)) * (S : ℝ) by ring,
            Real.mul_rpow (by positivity) (by positivity)]
        have hstep3 : (S : ℝ) ^ ε ≤ ((R : ℝ) * (S : ℝ)) ^ ε :=
          Real.rpow_le_rpow (by positivity) (by nlinarith [hR1]) hε.le
        calc ((D : ℝ) * (R : ℝ)) ^ ε ≤ ((R : ℝ) * (S : ℝ) * (S : ℝ)) ^ ε := hstep1
          _ = ((R : ℝ) * (S : ℝ)) ^ ε * (S : ℝ) ^ ε := hstep2
          _ ≤ ((R : ℝ) * (S : ℝ)) ^ ε * ((R : ℝ) * (S : ℝ)) ^ ε :=
              mul_le_mul_of_nonneg_left hstep3 (Real.rpow_nonneg (by positivity) _)
      have hD32 : (D : ℝ) ^ ((3 : ℝ) / 2) ≤ (D : ℝ) ^ 2 := by
        calc (D : ℝ) ^ ((3 : ℝ) / 2) ≤ (D : ℝ) ^ (2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hD1 (by norm_num)
          _ = (D : ℝ) ^ 2 := by
              rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hk : (D : ℝ) ^ ((3 : ℝ) / 2) * (((D : ℝ) * (R : ℝ)) ^ ε) ≤ 16 * (S : ℝ) := by
        have h1 : (D : ℝ) ^ ((3 : ℝ) / 2) * (((D : ℝ) * (R : ℝ)) ^ ε)
            ≤ (D : ℝ) ^ 2 * (((R : ℝ) * (S : ℝ)) ^ (2 * ε)) :=
          mul_le_mul hD32 hpow (Real.rpow_nonneg (by positivity) _) (by positivity)
        have h2 : (D : ℝ) ^ 2 * (((R : ℝ) * (S : ℝ)) ^ (2 * ε))
            ≤ 16 * (D : ℝ) ^ 2 * (((R : ℝ) * (S : ℝ)) ^ (2 * ε)) := by
          nlinarith [hDleD2, hD1]
        linarith [h1, h2, hsmall]
      have hB : Work.FIArea4.Wdyad D R S γ ≤ Cb * B1123 D R S ε
          * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := by
        simpa only [B1123] using hCb D R S γ hD hR hS
      have hcomp := B1123_le_target ε hε hD hDS (le_of_lt hSR') hk
      calc Work.FIArea4.Wdyad D R S γ ≤ Cb * B1123 D R S ε
              * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := hB
        _ ≤ Cb * (20 * (Work.FIArea4.braceV D R S ε
                + (D : ℝ) * (min R S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε)))
              * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
                  Complex.normSq (γ a d)) := by
            apply mul_le_mul_of_nonneg_right _ hWE
            exact mul_le_mul_of_nonneg_left hcomp hCbpos.le
        _ ≤ (max (max Ce (20 * Cb)) (3 * Cτ * (2 : ℝ) ^ (ε / 2) * Ks) + 1)
              * (Work.FIArea4.braceV D R S ε
                  + (D : ℝ) * (min R S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε))
              * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
                  Complex.normSq (γ a d)) := by
            apply mul_le_mul_of_nonneg_right _ hWE
            have hTnn' : (0 : ℝ) ≤ Work.FIArea4.braceV D R S ε
                + (D : ℝ) * (min R S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε) := by linarith
            rw [show Cb * (20 * (Work.FIArea4.braceV D R S ε
                    + (D : ℝ) * (min R S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε)))
                  = 20 * Cb * (Work.FIArea4.braceV D R S ε
                    + (D : ℝ) * (min R S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε)) by ring]
            exact mul_le_mul hmax2 le_rfl hTnn' (by positivity)

end Work.FIArea4
