import Mathlib
import Submission.Work.BMF.mr_core_defs
import Submission.Work.BMF.mr_direct_range_defs
import Submission.Work.BMF.mr_direct.remPolySetEnergy
import Submission.Work.BMF.mr_direct.range_defs
import Submission.Work.BMF.mr_direct.badSetAux
import Submission.Work.mr_core.badPartAux.bp_largeSumHalf
import Submission.Work.BMF.mr_core.badPartCell_remBound
import Submission.Work.BMF.mr_core.badPartCell_eventual

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.mr_core.badPartCell`

The **per-cell** bound of the coarse Buchstab decomposition of `dirPolyD`, in the form used by
`Work.BMF.mr_core.badPart_le2`.  For a coarse prime cell `[e^{j/K}, e^{(j+1)/K}]` of the system
`[Pc Y, Qc B Y]`, with `Q_j(t) = Σ_{e^{j/K} ≤ p ≤ e^{(j+1)/K}} g p · p^{-(1+it)}` and
`R_j(t) = Work.BMF.mrDirect.remPolyR g (Pc Y) (Qc B Y) K Y (3Y) j t` (the Buchstab remainder
polynomial), and for *any* measurable `u ⊆ [-2T, 2T]` (in particular for the bad set
`Work.BMF.mrCore.badSet ε g Y (2T)`, whose fine-system structure is never used),

  `∫_u ‖Q_j R_j‖² ≤ C·(Ac B)²·(((1+B²)² e^{-B²/4} + 1/T₀)·(log Y)^{-47/24})`
                        `+ C·log (2T)·(log Y)^{-199}`,

uniformly in `j`, `u` and `R` (no dependence on the number of terms of `u` or on its measure).

Route (the two "semicircle" halves of the split at the threshold `Θ = (log Y)^{-100}`):

* `u_S = u ∩ {‖Q_j‖ < Θ}`: pointwise `‖Q_j R_j‖² ≤ Θ²‖R_j‖²`, and the mean square of the
  remainder polynomial over *any* measurable subset of `[-2T,2T]` is bounded by
  `Work.BMF.mr_direct.remPolySetEnergy` (`≤ C·(1 + 2T e^{j/K}/Y)`); since `e^{j/K} ≤ Qc B Y` and
  `2T·Qc B Y ≤ Y`, this gives `≤ 2C Θ² ≤ C' log(2T) (log Y)^{-199}`.
* `u_L = u ∩ {Θ ≤ ‖Q_j‖}`: pointwise `‖Q_j R_j‖² ≤ ρ²‖Q_j‖²` with
  `ρ ≤ C_ρ·Ac B·((1+B²/2)e^{-B²/8} + 1/√T₀)` the pointwise bound on the remainder polynomial
  (`Work.BMF.mr_core.badPartCell_remBound`), and `∫_{u_L}‖Q_j‖² ≤ C·K²/j²` is
  `Work.mr_core.badPartAux.bp_largeSumHalf` (Halász for primes plus the large-values count);
  finally `K²/j² ≤ 4(log Y)^{-47/24}` because `j/K ≥ log Pc/2`.

The constant `C` depends only on the absolute constants of the three inputs (in particular it is
independent of `ε, B, K, Y`), which is why the statement has the shape `∃C, ∀ B, ∀ K, ∀ᶠ Y`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory intervalIntegral Filter
open scoped BigOperators

namespace Work.BMF.mr_core

noncomputable section

/-! ### arithmetic -/

lemma badPartCell_arith_theta (Y : ℝ) (hlogY : 1 ≤ Real.log Y) (T : ℝ) (hlog2T : 1 ≤ Real.log (2 * T)) :
    (Work.BMF.mrCore.Theta Y) ^ 2 ≤ Real.log (2 * T) * (Real.log Y) ^ (-(199 : ℝ)) := by
  show ((Real.log Y) ^ (-(100 : ℝ))) ^ 2 ≤ Real.log (2 * T) * (Real.log Y) ^ (-(199 : ℝ))
  have hnn : 0 ≤ Real.log Y := by linarith
  have hpos : 0 < Real.log Y := by linarith
  have hsq : ((Real.log Y) ^ (-(100 : ℝ))) ^ 2 = (Real.log Y) ^ (-(200 : ℝ)) := by
    rw [← Real.rpow_natCast ((Real.log Y) ^ (-(100 : ℝ))) 2, ← Real.rpow_mul hnn]
    norm_num
  have hsplit : (Real.log Y) ^ (-(200 : ℝ))
      = (Real.log Y) ^ (-(199 : ℝ)) * (Real.log Y) ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hpos]
    norm_num
  have hinv : (Real.log Y) ^ (-(1 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hlogY (by norm_num)
  have hnn2 : 0 ≤ (Real.log Y) ^ (-(199 : ℝ)) := Real.rpow_nonneg hnn _
  calc ((Real.log Y) ^ (-(100 : ℝ))) ^ 2 = (Real.log Y) ^ (-(200 : ℝ)) := hsq
    _ = (Real.log Y) ^ (-(199 : ℝ)) * (Real.log Y) ^ (-(1 : ℝ)) := hsplit
    _ ≤ (Real.log Y) ^ (-(199 : ℝ)) * 1 := mul_le_mul_of_nonneg_left hinv hnn2
    _ ≤ (Real.log Y) ^ (-(199 : ℝ)) * Real.log (2 * T) := by
        apply mul_le_mul_of_nonneg_left _ hnn2
        linarith
    _ = Real.log (2 * T) * (Real.log Y) ^ (-(199 : ℝ)) := by ring

lemma badPartCell_arith_Ksq (K : ℝ) (j : ℕ) (Y : ℝ) (hlogYpos : 0 < Real.log Y)
    (hK : 0 < K) (h : (Real.log Y) ^ (47 / 48 : ℝ) ≤ 2 * ((j : ℝ) / K)) :
    K ^ 2 / (j : ℝ) ^ 2 ≤ 4 * (Real.log Y) ^ (-(47 / 24 : ℝ)) := by
  have hnn : 0 ≤ Real.log Y := hlogYpos.le
  have hlogPcpos : 0 < (Real.log Y) ^ (47 / 48 : ℝ) := Real.rpow_pos_of_pos hlogYpos _
  have hjpos : 0 < (j : ℝ) := by
    by_contra hcon
    have h0 : (j : ℝ) = 0 := le_antisymm (not_lt.mp hcon) (Nat.cast_nonneg j)
    rw [h0] at h
    simp at h
    linarith [hlogPcpos]
  have h' : K * (Real.log Y) ^ (47 / 48 : ℝ) ≤ 2 * (j : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left h hK.le
    have h2 : K * (2 * ((j : ℝ) / K)) = 2 * (j : ℝ) := by field_simp
    linarith [h1, h2.le, h2.ge]
  have hKj : K / (j : ℝ) ≤ 2 / (Real.log Y) ^ (47 / 48 : ℝ) := by
    rw [div_le_div_iff₀ hjpos hlogPcpos]
    linarith
  have hKjnn : 0 ≤ K / (j : ℝ) := by positivity
  have h2 : (K / (j : ℝ)) ^ 2 ≤ (2 / (Real.log Y) ^ (47 / 48 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hKjnn hKj 2
  have hsq : ((Real.log Y) ^ (47 / 48 : ℝ)) ^ 2 = (Real.log Y) ^ (47 / 24 : ℝ) := by
    rw [← Real.rpow_natCast ((Real.log Y) ^ (47 / 48 : ℝ)) 2, ← Real.rpow_mul hnn]
    norm_num
  have hrhs : (2 / (Real.log Y) ^ (47 / 48 : ℝ)) ^ 2
      = 4 * (Real.log Y) ^ (-(47 / 24 : ℝ)) := by
    rw [div_pow, hsq, show (2 : ℝ) ^ 2 = 4 by norm_num]
    rw [div_eq_mul_inv, ← Real.rpow_neg hnn]
  calc K ^ 2 / (j : ℝ) ^ 2 = (K / (j : ℝ)) ^ 2 := by rw [div_pow]
    _ ≤ (2 / (Real.log Y) ^ (47 / 48 : ℝ)) ^ 2 := h2
    _ = 4 * (Real.log Y) ^ (-(47 / 24 : ℝ)) := hrhs

lemma badPartCell_arith_oneadd (T Y Q : ℝ) (j : ℕ) (K : ℝ) (hYpos : 0 < Y) (hT : 0 ≤ T)
    (hexpj : Real.exp ((j : ℝ) / K) ≤ Q) (h2TQ : 2 * T * Q ≤ Y) :
    1 + 2 * T * Real.exp ((j : ℝ) / K) / Y ≤ 2 := by
  have h1 : 2 * T * Real.exp ((j : ℝ) / K) / Y ≤ 1 := by
    rw [div_le_one hYpos]
    exact le_trans (mul_le_mul_of_nonneg_left hexpj (by linarith : (0 : ℝ) ≤ 2 * T)) h2TQ
  linarith

lemma badPartCell_arith_rho (Crho AcB B T₀ x : ℝ) (hCrho : 0 < Crho) (hAcB : 0 ≤ AcB)
    (hB : 0 ≤ B) (hT₀ : 1 ≤ T₀) (hx0 : 0 ≤ x)
    (hx : x ≤ Crho * AcB * ((1 + B ^ 2 / 2) * Real.exp (-(B ^ 2 / 8)) + 1 / Real.sqrt T₀)) :
    x ^ 2 ≤ 2 * Crho ^ 2 * AcB ^ 2 * ((1 + B ^ 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) + 1 / T₀) := by
  have hT₀pos : 0 < T₀ := by linarith
  have hsq : (1 / Real.sqrt T₀) ^ 2 = 1 / T₀ := by
    rw [div_pow, one_pow, Real.sq_sqrt hT₀pos.le]
  have hexp : (Real.exp (-(B ^ 2 / 8))) ^ 2 = Real.exp (-(B ^ 2 / 4)) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have hstep : ((1 + B ^ 2 / 2) * Real.exp (-(B ^ 2 / 8)) + 1 / Real.sqrt T₀) ^ 2
      ≤ 2 * ((1 + B ^ 2 / 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) + 1 / T₀) := by
    have e1 : ((1 + B ^ 2 / 2) * Real.exp (-(B ^ 2 / 8))) ^ 2
        = (1 + B ^ 2 / 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) := by
      rw [mul_pow, hexp]
    have e2 : (2 * ((1 + B ^ 2 / 2) * Real.exp (-(B ^ 2 / 8)))
        * (1 / Real.sqrt T₀))
        ≤ ((1 + B ^ 2 / 2) * Real.exp (-(B ^ 2 / 8))) ^ 2 + (1 / Real.sqrt T₀) ^ 2 := by
      nlinarith [sq_nonneg ((1 + B ^ 2 / 2) * Real.exp (-(B ^ 2 / 8)) - 1 / Real.sqrt T₀)]
    have hexpand : ((1 + B ^ 2 / 2) * Real.exp (-(B ^ 2 / 8)) + 1 / Real.sqrt T₀) ^ 2
        = ((1 + B ^ 2 / 2) * Real.exp (-(B ^ 2 / 8))) ^ 2
          + 2 * ((1 + B ^ 2 / 2) * Real.exp (-(B ^ 2 / 8))) * (1 / Real.sqrt T₀)
          + (1 / Real.sqrt T₀) ^ 2 := by ring
    rw [hexpand, e1, hsq]
    linarith
  have hstep2 : ((1 + B ^ 2 / 2) * Real.exp (-(B ^ 2 / 8)) + 1 / Real.sqrt T₀) ^ 2
      ≤ 2 * ((1 + B ^ 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) + 1 / T₀) := by
    refine le_trans hstep ?_
    have hB2 : (1 + B ^ 2 / 2) ^ 2 ≤ (1 + B ^ 2) ^ 2 := by nlinarith [sq_nonneg B]
    have he : 0 ≤ Real.exp (-(B ^ 2 / 4)) := (Real.exp_pos _).le
    have : (1 + B ^ 2 / 2) ^ 2 * Real.exp (-(B ^ 2 / 4))
        ≤ (1 + B ^ 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) :=
      mul_le_mul_of_nonneg_right hB2 he
    linarith
  have hx2 : x ^ 2
      ≤ (Crho * AcB * ((1 + B ^ 2 / 2) * Real.exp (-(B ^ 2 / 8)) + 1 / Real.sqrt T₀)) ^ 2 :=
    pow_le_pow_left₀ hx0 hx 2
  calc x ^ 2
      ≤ (Crho * AcB * ((1 + B ^ 2 / 2) * Real.exp (-(B ^ 2 / 8)) + 1 / Real.sqrt T₀)) ^ 2 := hx2
    _ = Crho ^ 2 * AcB ^ 2
          * ((1 + B ^ 2 / 2) * Real.exp (-(B ^ 2 / 8)) + 1 / Real.sqrt T₀) ^ 2 := by ring
    _ ≤ Crho ^ 2 * AcB ^ 2 * (2 * ((1 + B ^ 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) + 1 / T₀)) :=
        mul_le_mul_of_nonneg_left hstep2 (by positivity)
    _ = 2 * Crho ^ 2 * AcB ^ 2 * ((1 + B ^ 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) + 1 / T₀) := by ring

theorem badPartCell (ε C₀ θ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hC₀ : 0 < C₀)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 1000 / ε ≤ B → ∀ K : ℝ, 4 ≤ K →
      ∀ᶠ Y in Filter.atTop, ∀ (T₀ : ℝ) (g : ℕ → ℂ) (H T : ℝ) (j : ℕ),
        1 ≤ T₀ →
        g 1 = 1 →
        (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) → (∀ n, ‖g n‖ ≤ 1) →
        2 ≤ Work.BMF.mrCore.Pc Y →
        Real.exp (Work.BMF.mrCore.logQc B Y) ≤ Y ^ (1 / 2 : ℝ) / 16 ^ 4 →
        (∑ p ∈ Work.BMF.primesIn (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y),
            1 / (p : ℝ)) ≤ B ^ 2 / 16 →
        (∀ u : ℝ, |u| ≤ 4 * T₀ →
          B ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y) →
        Y ^ θ ≤ H → H ≤ Y → 3 ≤ T → Y / H ≤ T → T ≤ T₀ → T ≤ 2 * C₀ / ε * (Y / H) →
        j ∈ Work.BMF.mrDirect.indexSet K (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y) →
        (∫ t in Work.BMF.mrCore.badSet ε g Y (2 * T),
            ‖Work.BMF.mrDirect.primePoly g K j t *
              Work.BMF.mrDirect.remPolyR g (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)
                K Y (3 * Y) j t‖ ^ 2)
          ≤ C * (Work.BMF.mrCore.Ac B) ^ 2 *
              (((1 + B ^ 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) + 1 / T₀)
                * (Real.log Y) ^ (-(47 / 24 : ℝ)))
            + C * Real.log (2 * T) * (Real.log Y) ^ (-(199 : ℝ)) := by
  obtain ⟨Crem, hCrem_pos, hRem⟩ := Work.BMF.mr_direct.remPolySetEnergy
  obtain ⟨Cls, Yls, hCls_pos, hYls_pos, hLs⟩ := Work.mr_core.badPartAux.bp_largeSumHalf
  obtain ⟨Crho, hCrho_pos, hRho⟩ := badPartCell_remBound
  refine ⟨2 * Crem + 8 * Crho ^ 2 * Cls + 1, by positivity, ?_⟩
  intro B hB K hK
  have hB8 : 8 ≤ B := by
    have h1 : (1 : ℝ) ≤ 1 / ε := by rw [one_le_div hε]; exact hε1
    have h2 : (1000 : ℝ) ≤ 1000 * (1 / ε) := by
      calc (1000 : ℝ) = 1000 * 1 := by ring
        _ ≤ 1000 * (1 / ε) := by linarith
    have h3 : 1000 * (1 / ε) = 1000 / ε := by ring
    linarith
  have hev := badPartCell_eventual ε C₀ θ B K hε hε1 hC₀ hθ₀ hθ₁ hB hK
  have hRhoAll := hRho B hB8 K hK
  filter_upwards [hev, Filter.eventually_ge_atTop Yls] with Y hEvY hYlsY
  intro T₀ g H T j hT₀1 hg1 hgmul hgbd hPc2 hQcY hprimes hdist hHθ hHY hT3 hTH hTleT₀ hTT hj
  obtain ⟨hY16, hIdx, hTor⟩ := hEvY
  have hYpos : 0 < Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hexp1_3 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
  have hlogY1 : 1 ≤ Real.log Y := by
    rw [Real.le_log_iff_exp_le hYpos]
    linarith [(by norm_num : (3 : ℝ) ≤ (16 : ℝ) ^ 8)]
  have hlogYpos : 0 < Real.log Y := lt_of_lt_of_le zero_lt_one hlogY1
  have hlogYnn : 0 ≤ Real.log Y := hlogYpos.le
  have hTpos : 0 < T := by linarith
  have h2Tpos : 0 < 2 * T := by linarith
  have h2T3 : (3 : ℝ) ≤ 2 * T := by linarith
  have hlog2T1 : 1 ≤ Real.log (2 * T) := by
    rw [Real.le_log_iff_exp_le h2Tpos]
    linarith
  obtain ⟨hlog2T, h2TQ, h4Texp⟩ := hTor H T hHθ hHY hT3 hTT
  set Θ : ℝ := Work.BMF.mrCore.Theta Y with hΘdef
  have hΘeq : Θ = (Real.log Y) ^ (-(100 : ℝ)) := rfl
  have hlogQcEq : Real.log (Work.BMF.mrCore.Qc B Y) = Work.BMF.mrCore.logQc B Y := by
    rw [Work.BMF.mrCore.Qc, Real.log_exp]
  have hKpos : 0 < K := by linarith
  have hK1 : (1 : ℝ) ≤ K := by linarith
  have hlogQcpos : 0 < Work.BMF.mrCore.logQc B Y := by
    rw [Work.BMF.mrCore.logQc, Work.BMF.mrCore.logPc]
    exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hlogYpos _)
  have hjle : (j : ℝ) / K ≤ Work.BMF.mrCore.logQc B Y := by
    have hmem := (Finset.mem_Icc.mp (by simpa only [Work.BMF.mrDirect.indexSet] using hj))
    have h1 : (j : ℝ) ≤ ((⌊K * Real.log (Work.BMF.mrCore.Qc B Y)⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast hmem.2
    rw [hlogQcEq] at h1
    have h2 : ((⌊K * Work.BMF.mrCore.logQc B Y⌋₊ : ℕ) : ℝ) ≤ K * Work.BMF.mrCore.logQc B Y :=
      Nat.floor_le (mul_nonneg hKpos.le hlogQcpos.le)
    rw [div_le_iff₀ hKpos]
    linarith
  have hexpj : Real.exp ((j : ℝ) / K) ≤ Work.BMF.mrCore.Qc B Y := by
    have h1 : Real.exp ((j : ℝ) / K) ≤ Real.exp (Work.BMF.mrCore.logQc B Y) :=
      Real.exp_le_exp.mpr hjle
    have h2 : Real.exp (Work.BMF.mrCore.logQc B Y) = Work.BMF.mrCore.Qc B Y := rfl
    rwa [h2] at h1
  have hexple : Real.exp ((((j : ℝ) + 1) / K)) ≤ Y := by
    have hsplit : (((j : ℝ) + 1) / K) = (j : ℝ) / K + 1 / K := by ring
    rw [hsplit, Real.exp_add]
    calc Real.exp ((j : ℝ) / K) * Real.exp (1 / K)
        ≤ Work.BMF.mrCore.Qc B Y * Real.exp (1 / K) :=
          mul_le_mul_of_nonneg_right hexpj (Real.exp_pos _).le
      _ ≤ Work.BMF.mrCore.Qc B Y * Real.exp (1 / 4) := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
            (Real.exp_pos (Work.BMF.mrCore.logQc B Y)).le
          rw [div_le_iff₀ hKpos]; linarith
      _ ≤ (Y ^ (1 / 2 : ℝ) / 16 ^ 4) * Real.exp (1 / 4) :=
          mul_le_mul_of_nonneg_right hQcY (Real.exp_pos _).le
      _ ≤ Y := by
          have he : Real.exp (1 / 4) ≤ 16 ^ 4 := by
            have h : Real.exp (1 / 4) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
            linarith [hexp1_3]
          have hnnYh : 0 ≤ Y ^ (1 / 2 : ℝ) / 16 ^ 4 :=
            div_nonneg (Real.rpow_nonneg hYpos.le _) (by norm_num)
          calc (Y ^ (1 / 2 : ℝ) / 16 ^ 4) * Real.exp (1 / 4)
              ≤ (Y ^ (1 / 2 : ℝ) / 16 ^ 4) * 16 ^ 4 :=
                mul_le_mul_of_nonneg_left he hnnYh
            _ = Y ^ (1 / 2 : ℝ) := by field_simp
            _ ≤ Y := Real.rpow_le_self_of_one_le hY1 (by norm_num)
  have hYexp : 1 ≤ Y * Real.exp (-(((j : ℝ) + 1) / K)) := by
    have h1 : Real.exp (-(((j : ℝ) + 1) / K)) = 1 / Real.exp ((((j : ℝ) + 1) / K)) := by
      rw [Real.exp_neg]; ring
    rw [h1]
    have h2 : Y * (1 / Real.exp ((((j : ℝ) + 1) / K)))
        = Y / Real.exp ((((j : ℝ) + 1) / K)) := by ring
    rw [h2, one_le_div (Real.exp_pos _)]
    exact hexple
  set u : Set ℝ := Work.BMF.mrCore.badSet ε g Y (2 * T) with hudef
  have humeas : MeasurableSet u := Work.BMF.mrCore.measurableSet_badSet ε g Y (2 * T)
  have husub : u ⊆ Set.Icc (-(2 * T)) (2 * T) := Work.BMF.mrCore.badSet_subset_Icc ε g Y (2 * T)
  set F : ℝ → ℝ := fun t => ‖Work.BMF.mrDirect.primePoly g K j t *
      Work.BMF.mrDirect.remPolyR g (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)
        K Y (3 * Y) j t‖ ^ 2 with hFdef
  have hFcont : Continuous F := by
    rw [hFdef]
    exact ((Work.BMF.mr_direct.continuous_primePoly g K j).mul
      (Work.BMF.mr_direct.continuous_remPolyR g (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)
        K Y (3 * Y) j hYpos)).norm.pow 2
  have hRcont : Continuous fun t : ℝ =>
      ‖Work.BMF.mrDirect.remPolyR g (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)
        K Y (3 * Y) j t‖ ^ 2 :=
    (Work.BMF.mr_direct.continuous_remPolyR g (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)
      K Y (3 * Y) j hYpos).norm.pow 2
  set AS : Set ℝ := u ∩ {t : ℝ | ‖Work.BMF.mrDirect.primePoly g K j t‖ < Θ} with hASdef
  set AL : Set ℝ := u ∩ {t : ℝ | Θ ≤ ‖Work.BMF.mrDirect.primePoly g K j t‖} with hALdef
  have hASmeas : MeasurableSet AS := humeas.inter
    (isOpen_lt (Work.BMF.mr_direct.continuous_primePoly g K j).norm continuous_const).measurableSet
  have hALmeas : MeasurableSet AL := humeas.inter
    (isClosed_le continuous_const (Work.BMF.mr_direct.continuous_primePoly g K j).norm).measurableSet
  have hASsub : AS ⊆ u := Set.inter_subset_left
  have hALsub : AL ⊆ u := Set.inter_subset_left
  have hASICC : AS ⊆ Set.Icc (-(2 * T)) (2 * T) := fun t ht => husub (hASsub ht)
  have hALICC : AL ⊆ Set.Icc (-(2 * T)) (2 * T) := fun t ht => husub (hALsub ht)
  have hUD : u = AS ∪ AL := by
    rw [hASdef, hALdef]
    ext t
    constructor
    · intro ht
      by_cases h : ‖Work.BMF.mrDirect.primePoly g K j t‖ < Θ
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr ⟨ht, not_lt.mp h⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  have hdisj : Disjoint AS AL := by
    rw [Set.disjoint_left]
    intro t ht1 ht2
    rw [hASdef] at ht1
    rw [hALdef] at ht2
    exact absurd (show Θ ≤ ‖Work.BMF.mrDirect.primePoly g K j t‖ from ht2.2) (not_le.mpr ht1.2)
  have hsplit : (∫ t in u, F t) = (∫ t in AS, F t) + (∫ t in AL, F t) :=
    Work.BMF.mr_direct.setIntegral_eq_add_of_union hFcont husub hASmeas hASsub hALmeas hALsub
      hUD hdisj
  have hX24 : (3 : ℝ) * Y ≤ 4 * Y := by linarith
  have hlogYrpow47 : 0 ≤ (Real.log Y) ^ (-(47 / 24 : ℝ)) := Real.rpow_nonneg hlogYnn _
  have hlogYrpow199 : 0 ≤ (Real.log Y) ^ (-(199 : ℝ)) := Real.rpow_nonneg hlogYnn _
  have hlog2Tnn : 0 ≤ Real.log (2 * T) := le_trans zero_le_one hlog2T1
  have hASbound : (∫ t in AS, F t) ≤ 2 * Crem * Real.log (2 * T) * (Real.log Y) ^ (-(199 : ℝ)) := by
    have hpt : ∀ t ∈ AS, F t ≤ Θ ^ 2 *
        ‖Work.BMF.mrDirect.remPolyR g (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)
          K Y (3 * Y) j t‖ ^ 2 := by
      intro t ht
      rw [hASdef] at ht
      have htQ : ‖Work.BMF.mrDirect.primePoly g K j t‖ < Θ := ht.2
      have hFs : F t = ‖Work.BMF.mrDirect.primePoly g K j t‖ ^ 2 *
          ‖Work.BMF.mrDirect.remPolyR g (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)
            K Y (3 * Y) j t‖ ^ 2 := by
        show ‖Work.BMF.mrDirect.primePoly g K j t *
            Work.BMF.mrDirect.remPolyR g (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)
              K Y (3 * Y) j t‖ ^ 2 = _
        rw [norm_mul, mul_pow]
      rw [hFs]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) htQ.le 2) (sq_nonneg _)
    have hInt1 : IntegrableOn F AS :=
      (hFcont.integrableOn_Icc (a := -(2 * T)) (b := 2 * T)).mono_set hASICC
    have hcont2 : Continuous (fun t : ℝ => Θ ^ 2 *
        ‖Work.BMF.mrDirect.remPolyR g (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)
          K Y (3 * Y) j t‖ ^ 2) := continuous_const.mul hRcont
    have hInt2 : IntegrableOn (fun t : ℝ => Θ ^ 2 *
        ‖Work.BMF.mrDirect.remPolyR g (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)
          K Y (3 * Y) j t‖ ^ 2) AS :=
      (hcont2.integrableOn_Icc (a := -(2 * T)) (b := 2 * T)).mono_set hASICC
    have hmono := MeasureTheory.setIntegral_mono_on hInt1 hInt2 hASmeas hpt
    have hcm : (∫ t in AS, Θ ^ 2 *
          ‖Work.BMF.mrDirect.remPolyR g (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)
            K Y (3 * Y) j t‖ ^ 2)
        = Θ ^ 2 * (∫ t in AS,
            ‖Work.BMF.mrDirect.remPolyR g (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)
              K Y (3 * Y) j t‖ ^ 2) := MeasureTheory.integral_const_mul (Θ ^ 2) _
    have hrem := hRem g hgbd (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y) K Y (3 * Y) j
      (2 * T) AS hY1 hK1 (by positivity) hX24 hYexp hASmeas hASICC
    have hone : 1 + 2 * T * Real.exp ((j : ℝ) / K) / Y ≤ 2 :=
      badPartCell_arith_oneadd T Y (Work.BMF.mrCore.Qc B Y) j K hYpos hTpos.le hexpj h2TQ
    calc (∫ t in AS, F t) ≤ (∫ t in AS, Θ ^ 2 *
          ‖Work.BMF.mrDirect.remPolyR g (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)
            K Y (3 * Y) j t‖ ^ 2) := hmono
      _ = Θ ^ 2 * (∫ t in AS,
            ‖Work.BMF.mrDirect.remPolyR g (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)
              K Y (3 * Y) j t‖ ^ 2) := hcm
      _ ≤ Θ ^ 2 * (Crem * 2) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg Θ)
          calc (∫ t in AS,
                ‖Work.BMF.mrDirect.remPolyR g (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)
                  K Y (3 * Y) j t‖ ^ 2)
              ≤ Crem * (1 + 2 * T * Real.exp ((j : ℝ) / K) / Y) := hrem
            _ ≤ Crem * 2 := mul_le_mul_of_nonneg_left hone hCrem_pos.le
      _ = Θ ^ 2 * (2 * Crem) := by ring
      _ ≤ 2 * Crem * Real.log (2 * T) * (Real.log Y) ^ (-(199 : ℝ)) := by
          have hθ : Θ ^ 2 ≤ Real.log (2 * T) * (Real.log Y) ^ (-(199 : ℝ)) :=
            badPartCell_arith_theta Y hlogY1 T hlog2T1
          calc Θ ^ 2 * (2 * Crem) = (2 * Crem) * Θ ^ 2 := by ring
            _ ≤ (2 * Crem) * (Real.log (2 * T) * (Real.log Y) ^ (-(199 : ℝ))) :=
                mul_le_mul_of_nonneg_left hθ (by positivity)
            _ = 2 * Crem * Real.log (2 * T) * (Real.log Y) ^ (-(199 : ℝ)) := by ring
  have hALbound : (∫ t in AL, F t) ≤ 8 * Crho ^ 2 * Cls * (Work.BMF.mrCore.Ac B) ^ 2 *
      (((1 + B ^ 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) + 1 / T₀)
        * (Real.log Y) ^ (-(47 / 24 : ℝ))) := by
    set ρ : ℝ := Crho * (Work.BMF.mrCore.Ac B) *
      ((1 + B ^ 2 / 2) * Real.exp (-(B ^ 2 / 8)) + 1 / Real.sqrt T₀) with hρdef
    have hρnn : 0 ≤ ρ := by
      rw [hρdef]
      have h1 : 0 ≤ (1 + B ^ 2 / 2) * Real.exp (-(B ^ 2 / 8)) :=
        mul_nonneg (by positivity) (Real.exp_pos _).le
      have h2 : 0 ≤ 1 / Real.sqrt T₀ := div_nonneg zero_le_one (Real.sqrt_nonneg _)
      exact mul_nonneg (mul_nonneg hCrho_pos.le (Real.exp_pos _).le) (add_nonneg h1 h2)
    have hρpt : ∀ t ∈ AL, ‖Work.BMF.mrDirect.remPolyR g (Work.BMF.mrCore.Pc Y)
        (Work.BMF.mrCore.Qc B Y) K Y (3 * Y) j t‖ ≤ ρ := by
      intro t ht
      have hICC := hALICC ht
      rw [Set.mem_Icc] at hICC
      have htabs : |t| ≤ 2 * T₀ := by
        rw [abs_le]
        constructor <;> linarith [hICC.1, hICC.2, hTleT₀]
      exact hRhoAll T₀ g Y j t hT₀1 hY16 hg1 hgmul hgbd hQcY hprimes hdist hj htabs
    have hpt : ∀ t ∈ AL, F t ≤ ρ ^ 2 * ‖Work.BMF.mrDirect.primePoly g K j t‖ ^ 2 := by
      intro t ht
      have hR := hρpt t ht
      have hFs : F t = ‖Work.BMF.mrDirect.primePoly g K j t‖ ^ 2 *
          ‖Work.BMF.mrDirect.remPolyR g (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)
            K Y (3 * Y) j t‖ ^ 2 := by
        show ‖Work.BMF.mrDirect.primePoly g K j t *
            Work.BMF.mrDirect.remPolyR g (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)
              K Y (3 * Y) j t‖ ^ 2 = _
        rw [norm_mul, mul_pow]
      rw [hFs]
      calc ‖Work.BMF.mrDirect.primePoly g K j t‖ ^ 2 *
            ‖Work.BMF.mrDirect.remPolyR g (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)
              K Y (3 * Y) j t‖ ^ 2
          ≤ ‖Work.BMF.mrDirect.primePoly g K j t‖ ^ 2 * ρ ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hR 2) (sq_nonneg _)
        _ = ρ ^ 2 * ‖Work.BMF.mrDirect.primePoly g K j t‖ ^ 2 := by ring
    have hInt1 : IntegrableOn F AL :=
      (hFcont.integrableOn_Icc (a := -(2 * T)) (b := 2 * T)).mono_set hALICC
    have hcont2 : Continuous (fun t : ℝ => ρ ^ 2 *
        ‖Work.BMF.mrDirect.primePoly g K j t‖ ^ 2) :=
      continuous_const.mul (((Work.BMF.mr_direct.continuous_primePoly g K j).norm).pow 2)
    have hInt2 : IntegrableOn (fun t : ℝ => ρ ^ 2 *
        ‖Work.BMF.mrDirect.primePoly g K j t‖ ^ 2) AL :=
      (hcont2.integrableOn_Icc (a := -(2 * T)) (b := 2 * T)).mono_set hALICC
    have hmono := MeasureTheory.setIntegral_mono_on hInt1 hInt2 hALmeas hpt
    have hcm : (∫ t in AL, ρ ^ 2 * ‖Work.BMF.mrDirect.primePoly g K j t‖ ^ 2)
        = ρ ^ 2 * (∫ t in AL, ‖Work.BMF.mrDirect.primePoly g K j t‖ ^ 2) :=
      MeasureTheory.integral_const_mul (ρ ^ 2) _
    have hALeq : AL ∩ {t : ℝ | Θ ≤ ‖Work.BMF.mrDirect.primePoly g K j t‖} = AL := by
      ext t
      constructor
      · intro h; exact h.1
      · intro h
        rw [hALdef] at h
        exact ⟨h, h.2⟩
    have hT'exp : 2 * (2 * T) ≤ Real.exp (((j : ℝ) / K / 2) ^ (21 / 20 : ℝ)) := by
      have hbase : (Real.log Y) ^ (47 / 48 : ℝ) / 4 ≤ ((j : ℝ) / K) / 2 := by
        linarith [hIdx j hj]
      have hnn1 : (0 : ℝ) ≤ (Real.log Y) ^ (47 / 48 : ℝ) / 4 := by positivity
      have hrpow : ((Real.log Y) ^ (47 / 48 : ℝ) / 4) ^ (21 / 20 : ℝ)
          ≤ (((j : ℝ) / K) / 2) ^ (21 / 20 : ℝ) :=
        Real.rpow_le_rpow hnn1 hbase (by norm_num)
      linarith [Real.exp_le_exp.mpr hrpow]
    have hLs' : (∫ t in AL, ‖Work.BMF.mrDirect.primePoly g K j t‖ ^ 2)
        ≤ Cls * K ^ 2 / (j : ℝ) ^ 2 := by
      have h := hLs K j g Y (2 * T) Θ AL hYlsY (by linarith) (hIdx j hj)
        (le_trans (le_of_lt Real.exp_one_lt_three) h2T3) hlog2T hT'exp hgbd hΘeq hALmeas hALICC
      rwa [hALeq] at h
    have hKsq := badPartCell_arith_Ksq K j Y hlogYpos hKpos (hIdx j hj)
    have hρ2 : ρ ^ 2 ≤ 2 * Crho ^ 2 * (Work.BMF.mrCore.Ac B) ^ 2 *
        ((1 + B ^ 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) + 1 / T₀) :=
      badPartCell_arith_rho Crho (Work.BMF.mrCore.Ac B) B T₀ ρ hCrho_pos (Real.exp_pos _).le
        (by positivity) hT₀1 hρnn hρdef.le
    have hClsK : Cls * K ^ 2 / (j : ℝ) ^ 2 ≤ Cls * (4 * (Real.log Y) ^ (-(47 / 24 : ℝ))) := by
      calc Cls * K ^ 2 / (j : ℝ) ^ 2 = Cls * (K ^ 2 / (j : ℝ) ^ 2) := by ring
        _ ≤ Cls * (4 * (Real.log Y) ^ (-(47 / 24 : ℝ))) :=
            mul_le_mul_of_nonneg_left hKsq hCls_pos.le
    calc (∫ t in AL, F t) ≤ (∫ t in AL, ρ ^ 2 *
          ‖Work.BMF.mrDirect.primePoly g K j t‖ ^ 2) := hmono
      _ = ρ ^ 2 * (∫ t in AL, ‖Work.BMF.mrDirect.primePoly g K j t‖ ^ 2) := hcm
      _ ≤ ρ ^ 2 * (Cls * K ^ 2 / (j : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hLs' (sq_nonneg _)
      _ ≤ (2 * Crho ^ 2 * (Work.BMF.mrCore.Ac B) ^ 2 *
              ((1 + B ^ 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) + 1 / T₀))
            * (Cls * (4 * (Real.log Y) ^ (-(47 / 24 : ℝ)))) := by
          have hb1 : 0 ≤ Cls * K ^ 2 / (j : ℝ) ^ 2 :=
            div_nonneg (mul_nonneg hCls_pos.le (sq_nonneg K)) (sq_nonneg (j : ℝ))
          have hb2 : 0 ≤ 2 * Crho ^ 2 * (Work.BMF.mrCore.Ac B) ^ 2 *
              ((1 + B ^ 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) + 1 / T₀) := by positivity
          exact mul_le_mul hρ2 hClsK hb1 hb2
      _ = 8 * Crho ^ 2 * Cls * (Work.BMF.mrCore.Ac B) ^ 2 *
            (((1 + B ^ 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) + 1 / T₀)
              * (Real.log Y) ^ (-(47 / 24 : ℝ))) := by ring
  have hfinal : (∫ t in AS, F t) + (∫ t in AL, F t) ≤
      (2 * Crem + 8 * Crho ^ 2 * Cls + 1) * (Work.BMF.mrCore.Ac B) ^ 2 *
          (((1 + B ^ 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) + 1 / T₀)
            * (Real.log Y) ^ (-(47 / 24 : ℝ)))
        + (2 * Crem + 8 * Crho ^ 2 * Cls + 1) * Real.log (2 * T)
            * (Real.log Y) ^ (-(199 : ℝ)) := by
    have hA1 : (∫ t in AL, F t) ≤ (2 * Crem + 8 * Crho ^ 2 * Cls + 1)
        * (Work.BMF.mrCore.Ac B) ^ 2 *
          (((1 + B ^ 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) + 1 / T₀)
            * (Real.log Y) ^ (-(47 / 24 : ℝ))) := by
      refine le_trans hALbound ?_
      have hle : 8 * Crho ^ 2 * Cls ≤ 2 * Crem + 8 * Crho ^ 2 * Cls + 1 := by
        have h0 : 0 ≤ 8 * Crho ^ 2 * Cls := by positivity
        linarith
      have hb : 0 ≤ ((1 + B ^ 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) + 1 / T₀)
          * (Real.log Y) ^ (-(47 / 24 : ℝ)) :=
        mul_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by positivity)) hlogYrpow47
      have hAc2 : 0 ≤ (Work.BMF.mrCore.Ac B) ^ 2 := sq_nonneg _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hAc2) hb
    have hA2 : (∫ t in AS, F t) ≤ (2 * Crem + 8 * Crho ^ 2 * Cls + 1)
        * Real.log (2 * T) * (Real.log Y) ^ (-(199 : ℝ)) := by
      refine le_trans hASbound ?_
      have hle : 2 * Crem ≤ 2 * Crem + 8 * Crho ^ 2 * Cls + 1 := by
        have h0 : 0 ≤ 8 * Crho ^ 2 * Cls := by positivity
        linarith
      have hb : 0 ≤ Real.log (2 * T) * (Real.log Y) ^ (-(199 : ℝ)) :=
        mul_nonneg hlog2Tnn hlogYrpow199
      calc 2 * Crem * Real.log (2 * T) * (Real.log Y) ^ (-(199 : ℝ))
          = (2 * Crem) * (Real.log (2 * T) * (Real.log Y) ^ (-(199 : ℝ))) := by ring
        _ ≤ (2 * Crem + 8 * Crho ^ 2 * Cls + 1)
              * (Real.log (2 * T) * (Real.log Y) ^ (-(199 : ℝ))) :=
            mul_le_mul_of_nonneg_right hle hb
        _ = (2 * Crem + 8 * Crho ^ 2 * Cls + 1) * Real.log (2 * T)
              * (Real.log Y) ^ (-(199 : ℝ)) := by ring
    linarith
  rw [hsplit]
  exact hfinal

end

end Work.BMF.mr_core
