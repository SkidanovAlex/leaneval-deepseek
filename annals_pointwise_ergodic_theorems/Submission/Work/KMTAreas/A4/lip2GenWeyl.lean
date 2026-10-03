/-
# The inverse Weyl estimate of Proposition `lip-2` in the interval (`Icc`) form
(`Work.KMTAreas.A4.lip2GenWeyl`)

The target is `Work.KMTAreas.A4.WeylIccStatement P` (the conclusion of
`Work.KMTAreas.A4.lip2WeylIcc`): for a polynomial `P` of degree `d ≥ 2`, if the windowed sum

  `winSumIcc M γ ξ P s a b = ∑_{n ∈ Icc a b} win M γ (n - s) e (ξ P n)`

has modulus at least `ε`, with `2 ≤ M`, `0 < ε ≤ 1/2` and `ε ^ (-K) ≤ M`, then `ξ · lc P` is
within `C ε ^ (-K) / M ^ d` of a rational number of denominator at most `C ε ^ (-K)`.

## The route

1. `Work.KMTAreas.A4.lip2IccReduce`: the sliding-window decomposition of the smoothing kernel
   turns the windowed sum into an `ℓ¹`-combination of sharp interval sums of the unimodular
   sequence `winPhase γ ξ P s`, so the hypothesis produces an interval `[c,d]` of length `L ≤ CB M`
   with `ε M / CB ≤ ‖∑_{n ∈ Icc c d} winPhase‖`.
2. `Work.KMTAreas.A4.IWPtr` (built from the τ-free cascade `IWP_allG` by
   `Work.KMTAreas.A4.IWPtr_succ`): the inverse Weyl estimate for the phase
   `n ↦ e (τ n + ξ Q(n))` with a real linear term — which is what `winPhase` is, with `τ` a real
   representative of the modulation `γ`, on `[c,d]` (`winPhase_eq_const_mul_phLin`).  It applies
   whenever `Cip (S/L) ^ (-Kip) ≤ L` where `S = ‖∑_{Icc c d} winPhase‖`; the conversions of the
   resulting denominator and error bounds are `Work.KMTAreas.A4.lip2SuccessCaseConv`.
3. Otherwise (`L < Cip (S/L) ^ (-Kip)`) the amplitude bound `S ≥ ε M / CB` and the length bound
   `L ≤ CB M`, together with `ε ^ (-K') ≤ M`, force `M ≤ Λ`
   (`Work.KMTAreas.A4.lip2BoundedCaseArith`), and the trivial choice `q = 1`,
   `a' = round (ξ · lc P)` closes the estimate.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.IWPtr_succ
import Submission.Work.KMTAreas.A4.lip2IccReduce
import Submission.Work.KMTAreas.A4.lip2BoundedCaseArith
import Submission.Work.KMTAreas.A4.lip2SuccessCaseConv

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators
open Polynomial

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ### the τ-free cascade upgrade -/

theorem IWPtr_allG : IWPtrAll := by
  intro d hd
  obtain ⟨C, K, hC, hK, hIW⟩ := IWP_allG (d - 1) (by omega)
  obtain ⟨C', K', hC', hK', h⟩ := IWPtr_succ (d - 1) (by omega) C K hC hK hIW
  have hcast : (d - 1) + 1 = d := by omega
  exact ⟨C', K', hC', hK', by rwa [hcast] at h⟩

/-! ### small helpers -/

theorem icc_card (a b : ℤ) (h : a ≤ b) :
    ((Finset.Icc a b).card : ℝ) = (((b - a : ℤ) : ℝ) + 1) := by
  have h1 : (Finset.Icc a b).card = (b + 1 - a).toNat := Int.card_Icc a b
  have h2 : (0 : ℤ) ≤ b + 1 - a := by omega
  have h3 : (((b + 1 - a).toNat : ℤ)) = b + 1 - a := Int.toNat_of_nonneg h2
  rw [h1]
  calc (((b + 1 - a).toNat : ℕ) : ℝ) = ((((b + 1 - a).toNat : ℤ)) : ℝ) := by push_cast; ring
    _ = ((b + 1 - a : ℤ) : ℝ) := by rw [h3]
    _ = (((b - a : ℤ) : ℝ) + 1) := by push_cast; ring

/-! ### the assembly -/

theorem lip2GenWeyl (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) :
    Work.KMTAreas.A4.WeylIccStatement P := by
  classical
  obtain ⟨Cip, Kip, hCip, hKip, hIWPtr⟩ := IWPtr_allG P.natDegree hP
  obtain ⟨CBr, hCBrpos, hreduce⟩ := lip2IccReduce
  set CB : ℝ := max CBr 1 with hCBdef
  have hCBpos : 0 < CB := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hCB1 : (1 : ℝ) ≤ CB := le_max_right _ _
  have hCBrle : CBr ≤ CB := le_max_left _ _
  set K' : ℝ := max (Kip + (P.natDegree : ℝ)) (max (2 * Kip) 1) + 1 with hK'def
  have hKip' : Kip < K' := by
    have h : Kip ≤ max (Kip + (P.natDegree : ℝ)) (max (2 * Kip) 1) :=
      le_trans (le_add_of_nonneg_right (Nat.cast_nonneg _)) (le_max_left _ _)
    rw [hK'def]
    exact lt_of_le_of_lt h (lt_add_one _)
  have h1K' : (1 : ℝ) < K' := by
    have h : (1 : ℝ) ≤ max (Kip + (P.natDegree : ℝ)) (max (2 * Kip) 1) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    rw [hK'def]
    exact lt_of_le_of_lt h (lt_add_one _)
  have hK'pos : 0 < K' := lt_trans zero_lt_one h1K'
  have hKipd' : Kip + (P.natDegree : ℝ) ≤ K' := by
    have h : Kip + (P.natDegree : ℝ) ≤ max (Kip + (P.natDegree : ℝ)) (max (2 * Kip) 1) :=
      le_max_left _ _
    rw [hK'def]
    exact le_trans h (le_add_of_nonneg_right (by norm_num))
  have hmaxK' : max Kip 1 < K' := max_lt hKip' h1K'
  obtain ⟨Λ, hΛpos, hΛ⟩ := lip2BoundedCaseArith Cip Kip CB K' hCip hKip hCBpos hmaxK'
  obtain ⟨Cconv, hCconvpos, hconv⟩ :=
    lip2SuccessCaseConv Cip Kip CB K' hCip hKip hCB1 P.natDegree hKipd'
  set C' : ℝ := max (max Cconv (Λ ^ P.natDegree / 2)) 1 with hC'def
  have hC'pos : 0 < C' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC'1 : (1 : ℝ) ≤ C' := le_max_right _ _
  have hC'conv : Cconv ≤ C' := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC'Λ : Λ ^ P.natDegree / 2 ≤ C' := le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨C', K', hC'pos, hK'pos, ?_⟩
  intro M ε γ ξ s a b hM hε0 hε1 hεK hab hsum
  obtain ⟨c, d, hcd, hlen, hamp⟩ := hreduce P M ε γ ξ s a b hM hε0 (by linarith) hab hsum
  set L : ℝ := (((d - c : ℤ) : ℝ) + 1) with hLdef
  set S : ℝ := ‖∑ n ∈ Finset.Icc c d, winPhase γ ξ P s n‖ with hSdef
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h0 : (0 : ℤ) ≤ d - c := by omega
    have h1 : (0 : ℝ) ≤ ((d - c : ℤ) : ℝ) := by exact_mod_cast h0
    linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hSle : S ≤ L := by
    rw [hSdef, hLdef]
    calc ‖∑ n ∈ Finset.Icc c d, winPhase γ ξ P s n‖
        ≤ ∑ n ∈ Finset.Icc c d, ‖winPhase γ ξ P s n‖ := norm_sum_le _ _
      _ = ∑ _n ∈ Finset.Icc c d, (1 : ℝ) :=
          Finset.sum_congr rfl (fun n _ => winPhase_norm γ ξ P s n)
      _ = ((Finset.Icc c d).card : ℝ) := by simp
      _ = (((d - c : ℤ) : ℝ) + 1) := icc_card c d hcd
  have hMpos : 0 < M := by linarith
  have hamp' : ε * M / CB ≤ S := by
    rw [hSdef]
    calc ε * M / CB ≤ ε * M / CBr :=
          div_le_div_of_nonneg_left (by positivity) hCBrpos hCBrle
      _ ≤ ‖∑ n ∈ Finset.Icc c d, winPhase γ ξ P s n‖ := hamp
  have hSpos : 0 < S := lt_of_lt_of_le (by positivity : 0 < ε * M / CB) hamp'
  have hlen' : L ≤ CB * M := by
    rw [hLdef]
    calc (((d - c : ℤ) : ℝ) + 1) ≤ CBr * M := hlen
      _ ≤ CB * M := mul_le_mul_of_nonneg_right hCBrle hMpos.le
  by_cases hcase : Cip * (S / L) ^ (-Kip) ≤ L
  · -- ## the length hypothesis of `IWPtr` holds: apply the inverse Weyl estimate
    obtain ⟨γ₀, hγ₀⟩ := Quotient.exists_rep γ
    have hsumLin : ‖∑ n ∈ Finset.Icc c d, phLin P ξ γ₀ n‖ = S := by
      rw [hSdef]
      have hc : (∑ n ∈ Finset.Icc c d, winPhase γ ξ P s n)
          = ee (-(γ₀ * (s : ℝ))) * ∑ n ∈ Finset.Icc c d, phLin P ξ γ₀ n := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun n _ => winPhase_eq_const_mul_phLin γ ξ P s n hγ₀)
      rw [hc, norm_mul, ee_norm, one_mul]
    have hηpos : 0 < S / L := div_pos hSpos hLpos
    have hηle1 : S / L ≤ 1 := by rw [div_le_one hLpos]; exact hSle
    have hampIW : (S / L) * L ≤ ‖∑ n ∈ Finset.Icc c d, phLin P ξ γ₀ n‖ := by
      rw [hsumLin, div_mul_cancel₀ S (ne_of_gt hLpos)]
    obtain ⟨q, hq1, hqle, m, hm⟩ :=
      hIWPtr P rfl ξ γ₀ c d (S / L) hcd hηpos hηle1 hcase hampIW
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
    have hlead : (P.leadingCoeff : ℝ) = ((P.coeff P.natDegree : ℤ) : ℝ) := by
      rw [Polynomial.leadingCoeff]
    have hX : |(q : ℝ) * (ξ * (P.leadingCoeff : ℝ)) - (m : ℝ)|
        ≤ Cip * (S / L) ^ (-Kip) / L ^ P.natDegree := by
      rw [hlead]
      simpa only [mul_assoc] using hm
    obtain ⟨hqbound, hXbound⟩ :=
      hconv q S L M ε ((q : ℝ) * (ξ * (P.leadingCoeff : ℝ)) - (m : ℝ))
        hε0 (by linarith) hLpos hSpos hSle hlen' hamp' hqpos hqle hX
    refine ⟨q, m, hq1, ?_, ?_⟩
    · exact le_trans hqbound (mul_le_mul_of_nonneg_right hC'conv (Real.rpow_nonneg hε0.le _))
    · have habs : |ξ * (P.leadingCoeff : ℝ) - (m : ℝ) / (q : ℝ)|
          = |(q : ℝ) * (ξ * (P.leadingCoeff : ℝ)) - (m : ℝ)| / (q : ℝ) := by
        have h1 : (q : ℝ) * (ξ * (P.leadingCoeff : ℝ)) - (m : ℝ)
            = (q : ℝ) * (ξ * (P.leadingCoeff : ℝ) - (m : ℝ) / (q : ℝ)) := by
          rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hqpos)]
        rw [h1, abs_mul, abs_of_pos hqpos, mul_div_cancel_left₀ _ (ne_of_gt hqpos)]
      rw [habs]
      have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
      calc |(q : ℝ) * (ξ * (P.leadingCoeff : ℝ)) - (m : ℝ)| / (q : ℝ)
          ≤ |(q : ℝ) * (ξ * (P.leadingCoeff : ℝ)) - (m : ℝ)| := by
            rw [div_le_iff₀ hqpos]
            nlinarith [abs_nonneg ((q : ℝ) * (ξ * (P.leadingCoeff : ℝ)) - (m : ℝ)), hq1R]
        _ ≤ Cconv * ε ^ (-K') / M ^ P.natDegree := hXbound
        _ ≤ C' * ε ^ (-K') / M ^ P.natDegree :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hC'conv (Real.rpow_nonneg hε0.le _))
              (by positivity)
  · -- ## the length hypothesis fails: `M` is bounded, and `q = 1` suffices
    have hfail : L < Cip * (S / L) ^ (-Kip) := lt_of_not_ge hcase
    have hMle : M ≤ Λ :=
      hΛ M ε L S hε0 (by linarith) hεK hLpos hSpos hSle hfail hamp' hlen'
    have hεinv : (1 : ℝ) ≤ ε ^ (-K') :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε0 (by linarith) (by linarith)
    have hMd : M ^ P.natDegree ≤ Λ ^ P.natDegree :=
      pow_le_pow_left₀ hMpos.le hMle _
    have hbudget : (1 : ℝ) / 2 ≤ C' * ε ^ (-K') / M ^ P.natDegree := by
      have hΛd : 0 < Λ ^ P.natDegree := pow_pos hΛpos _
      have hMdpos : 0 < M ^ P.natDegree := pow_pos hMpos _
      have h1 : C' * 1 / Λ ^ P.natDegree ≤ C' * ε ^ (-K') / M ^ P.natDegree := by
        rw [div_le_div_iff₀ hΛd hMdpos]
        calc C' * 1 * M ^ P.natDegree = C' * M ^ P.natDegree := by ring
          _ ≤ C' * (ε ^ (-K') * M ^ P.natDegree) :=
              mul_le_mul_of_nonneg_left
                (by nlinarith [hεinv, hMdpos]) (le_of_lt hC'pos)
          _ = C' * ε ^ (-K') * M ^ P.natDegree := by ring
          _ ≤ C' * ε ^ (-K') * Λ ^ P.natDegree :=
              mul_le_mul_of_nonneg_left hMd (by positivity)
      have h2 : (1 : ℝ) / 2 ≤ C' * 1 / Λ ^ P.natDegree := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hΛd]
        nlinarith [hC'Λ, hΛd]
      linarith [h1, h2]
    refine ⟨1, round (ξ * (P.leadingCoeff : ℝ)), le_refl 1, ?_, ?_⟩
    · have h1 : (1 : ℝ) ≤ C' * ε ^ (-K') := by
        nlinarith [hC'1, hεinv, Real.rpow_pos_of_pos hε0 (-K')]
      simpa using h1
    · rw [Nat.cast_one, div_one]
      have hhalf : |ξ * (P.leadingCoeff : ℝ) - (round (ξ * (P.leadingCoeff : ℝ)) : ℝ)| ≤ 1 / 2 :=
        abs_sub_round _
      linarith [hhalf, hbudget]


end Work.KMTAreas.A4
