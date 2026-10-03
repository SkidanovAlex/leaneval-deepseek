import Mathlib
import Submission.Work.KMTAreas.A7.VarphitildeDiffMultBound
import Submission.Work.KMTAreas.A7Hi.Gblock

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7Hi

noncomputable section

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTAreas.A7

/-! ## §1.  The Schwartz packaging of the unmodulated `d`-fold bump -/

/-- The unmodulated `d`-fold bump as a Schwartz function. -/
noncomputable def varphitildeNSch_g (d N k₂ : ℕ) : SchwartzMap ℝ ℂ :=
  (hasCompactSupport_varphitildeN d N k₂).toSchwartzMap (contDiff_varphitildeN_all d N k₂)

lemma varphitildeNSch_g_apply (d N k₂ : ℕ) (ξ : ℝ) :
    varphitildeNSch_g d N k₂ ξ = varphitildeN d N k₂ ξ :=
  HasCompactSupport.toSchwartzMap_toFun _ _ ξ

lemma varphitildeNSch_g_coe (d N k₂ : ℕ) :
    (varphitildeNSch_g d N k₂ : ℝ → ℂ) = varphitildeN d N k₂ :=
  funext (varphitildeNSch_g_apply d N k₂)

/-! ## §2.  Narrowness of the unmodulated bump on the Farey scales -/

/-- On the Farey scales the *unmodulated* `d`-fold bump is narrow at level `fareyK Cρc ρ l₂`. -/
lemma varphitildeN_narrow_of_farey_g (P : Polynomial ℤ) (d : ℕ) (hd : 1 ≤ d) {Cρc ρ : ℝ}
    (hCρc : 0 ≤ Cρc) {l₂ : ℕ} {a : ℕ → NNReal} {m : ℕ} {t : ℝ}
    (h : Farey Cρc ρ l₂ 0 a m) :
    ∀ ξ : ℝ, varphitildeN d (Nat.floor (a m)) 0 ξ ≠ 0 →
      ξ ∈ Work.Analysis.IonescuWainger.realArc (fareyK Cρc ρ l₂) := by
  intro ξ hξ
  have hξt : varphitildeNt P d (Nat.floor (a m)) 0 t ξ ≠ 0 := by
    show varphitildeN d (Nat.floor (a m)) 0 ξ *
      ee (PevalR P ((Nat.floor (a m) : ℝ) * t) * ξ) ≠ 0
    exact mul_ne_zero hξ (by simp [ee])
  exact narrow_of_farey_g P d hd hCρc h ξ hξt

/-! ## §3.  The two-endpoint multiplier input for the difference family -/

/-- **The two-endpoint multiplier input at `k₂ = 0` for the low-frequency difference.** -/
theorem multBound_varphitildeNt_diff_two_endpoints (P : Polynomial ℤ) (d : ℕ) (hd : 2 ≤ d)
    (hdP : P.natDegree ≤ d) (Λ : NNReal) (hΛ : 1 < Λ) (k₀ : ℕ) (hk₀ : 2 ≤ k₀) :
    ∃ C : NNReal, 0 < C ∧ ∀ (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) (a : ℕ → NNReal)
      (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
      (U : Finset ℕ) (ω : ℕ → Bool),
      IsLqMultiplierBound (ENNReal.ofReal (2 : ℝ))
          (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            (varphitildeNt P d (Nat.floor (a n)) 0 t ξ
              - varphitildeN d (Nat.floor (a n)) 0 ξ)) C ∧
        IsLqMultiplierBound (ENNReal.ofReal (2 * (k₀ : ℝ)))
          (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            (varphitildeNt P d (Nat.floor (a n)) 0 t ξ
              - varphitildeN d (Nat.floor (a n)) 0 ξ)) C := by
  have hk₀1 : (1 : ℝ) < 2 * (k₀ : ℝ) := by
    have h1 : (1 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast (by omega : 1 ≤ k₀)
    linarith
  obtain ⟨C₂, hC₂pos, hC₂⟩ := VarphitildeDiffMultBound P d hd hdP 2 (by norm_num) Λ hΛ
  obtain ⟨Ce, hCepos, hCe⟩ := VarphitildeDiffMultBound P d hd hdP (2 * (k₀ : ℝ)) hk₀1 Λ hΛ
  refine ⟨max C₂ Ce, lt_max_of_lt_left hC₂pos, ?_⟩
  intro t ht a ha ha1 U ω
  have hε : ∀ n : ℕ, ‖(if ω n then (1 : ℂ) else -1)‖ ≤ 1 := by
    intro n
    by_cases h : ω n <;> simp [h]
  refine ⟨?_, ?_⟩
  · exact IsLqMultiplierBound.mono (hC₂ t ht a ha ha1 U _ hε) (le_max_left _ _)
  · exact IsLqMultiplierBound.mono (hCe t ht a ha ha1 U _ hε) (le_max_right _ _)

/-! ## §4.  The Farey part of the low-frequency difference -/

/-- The clipped difference bump family as Schwartz functions. -/
noncomputable def fareyDiffSchG (P : Polynomial ℤ) (d : ℕ) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
    (Cρc : ℝ) (l₁ l₂ k₁ : ℕ) (m : ℕ) (t : ℝ) : SchwartzMap ℝ ℂ :=
  if core ρ C₀ l₁ l₂ k₁ 0 a m ∧ Farey Cρc ρ l₂ 0 a m then
    varphitildeNtSch_g P d (Nat.floor (a m)) 0 t - varphitildeNSch_g d (Nat.floor (a m)) 0
  else 0

lemma fareyDiffSchG_coe (P : Polynomial ℤ) (d : ℕ) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
    (Cρc : ℝ) (l₁ l₂ k₁ m : ℕ) (t : ℝ) :
    (fareyDiffSchG P d ρ C₀ a Cρc l₁ l₂ k₁ m t : ℝ → ℂ)
      = fun ξ : ℝ => if core ρ C₀ l₁ l₂ k₁ 0 a m ∧ Farey Cρc ρ l₂ 0 a m then
          varphitildeNt P d (Nat.floor (a m)) 0 t ξ - varphitildeN d (Nat.floor (a m)) 0 ξ
          else 0 := by
  unfold fareyDiffSchG
  by_cases h : core ρ C₀ l₁ l₂ k₁ 0 a m ∧ Farey Cρc ρ l₂ 0 a m
  · simp only [h]
    funext ξ
    simp [varphitildeNtSch_g_coe, varphitildeNSch_g_coe]
  · simp only [h, if_false]
    funext ξ
    simp

/-- **The Farey part of the `g`-side low-frequency difference.** -/
theorem lacunaryBumpFareyDiffPartBoundG (P : Polynomial ℤ) (d : ℕ) (hd : 2 ≤ d) (hdP : P.natDegree ≤ d)
    (C₀ : ℕ) (r : NNReal) (hr : 2 < r) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (Λ : NNReal) (hΛ : 1 < Λ) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρc : ℝ, 3 ≤ Cρc ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (l l₁ l₂ k₁ k₂ : ℕ) (hl : l ≤ l₂) (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1)
        (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (g : ℤ → ℂ),
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Tle ρ l (fun ξ : ℝ =>
            if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc ρ l₂ 0 a n
            then varphitildeNt P d (Nat.floor (a n)) 0 t ξ
              - varphitildeN d (Nat.floor (a n)) 0 ξ else 0) g x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (K * (1 + (l₂ : ℝ))) *
            MeasureTheory.eLpNorm g p MeasureTheory.Measure.count := by
  -- ## the endpoint exponent `2 k₀`
  set q : ℝ := p.toReal with hqdef
  have hq1 : 1 < q := by
    rw [hqdef, ← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  obtain ⟨k₀, hk₀2, hk₀max, hk₀dual⟩ := exists_endpoint_exponent q hq1
  -- ## the narrow-symbol variational estimate at the two endpoints
  obtain ⟨Cρ, hCρpos, K0, hK0pos, hvar⟩ :=
    varEst_of_narrow_symbols_twoEndpoints ρ hρ hρ1 r hr p hp hptop k₀ hk₀2
      (by rw [← hqdef]; exact hk₀max) (by rw [← hqdef]; exact hk₀dual)
  -- ## the two-endpoint multiplier input for the difference family
  obtain ⟨C, hCpos, hCmult⟩ := multBound_varphitildeNt_diff_two_endpoints P d hd hdP Λ hΛ k₀ hk₀2
  -- ## the narrowness constant
  obtain ⟨Cρc, hCρc3, hCρcCρ, hCρc1⟩ :
      ∃ Cρc : ℝ, 3 ≤ Cρc ∧ Cρ ≤ Cρc ∧ 1 < Cρc :=
    ⟨max Cρ 3 + 1, by linarith [le_max_right Cρ (3 : ℝ)],
      by linarith [le_max_left Cρ (3 : ℝ)], by linarith [le_max_right Cρ (3 : ℝ)]⟩
  refine ⟨Cρc, hCρc3, K0 * C, mul_pos hK0pos hCpos, ?_⟩
  intro l l₁ l₂ k₁ k₂ hl t ht a ha ha1 g
  have hCρ : GoodMajorArcs ρ Cρ l (fareyK Cρc ρ l₂) :=
    goodMajorArcs_fareyK hCρcCρ hCρpos.le hρ.le hl
  have hk : (2 : ℝ) ^ (fareyK Cρc ρ l₂) < 1 / 2 :=
    two_rpow_fareyK_lt_half hCρc1 hρ.le l₂
  let Φ : ℕ → SchwartzMap ℝ ℂ := fun m => fareyDiffSchG P d ρ C₀ a Cρc l₁ l₂ k₁ m t
  have hΦcoe : ∀ m : ℕ, (Φ m : ℝ → ℂ)
      = fun ξ : ℝ => if core ρ C₀ l₁ l₂ k₁ 0 a m ∧ Farey Cρc ρ l₂ 0 a m then
          varphitildeNt P d (Nat.floor (a m)) 0 t ξ - varphitildeN d (Nat.floor (a m)) 0 ξ
          else 0 :=
    fun m => fareyDiffSchG_coe P d ρ C₀ a Cρc l₁ l₂ k₁ m t
  -- ## narrowness
  have hnarrow : ∀ m ξ, (Φ m : ℝ → ℂ) ξ ≠ 0 → ξ ∈ realArc (fareyK Cρc ρ l₂) := by
    intro m ξ hξ
    by_cases hc : core ρ C₀ l₁ l₂ k₁ 0 a m ∧ Farey Cρc ρ l₂ 0 a m
    · have hD : varphitildeNt P d (Nat.floor (a m)) 0 t ξ
          - varphitildeN d (Nat.floor (a m)) 0 ξ ≠ 0 := by
        simpa only [hΦcoe m, hc, and_self, if_true] using hξ
      by_cases h1 : varphitildeNt P d (Nat.floor (a m)) 0 t ξ = 0
      · refine varphitildeN_narrow_of_farey_g P d (by omega) (le_trans (by norm_num : (0:ℝ) ≤ 3) hCρc3) (t := t) hc.2 ξ ?_
        intro h2
        rw [h1, h2, sub_zero] at hD
        exact hD rfl
      · exact narrow_of_farey_g P d (by omega) (le_trans (by norm_num : (0:ℝ) ≤ 3) hCρc3) hc.2 ξ h1
    · have h0 : (0 : ℂ) ≠ 0 := by simpa only [hΦcoe m, hc, if_false] using hξ
      exact absurd rfl h0
  -- ## the two-endpoint multiplier bound for the clipped family
  have hMult : ∀ (U : Finset ℕ) (ω : ℕ → Bool),
      IsLqMultiplierBound (2 : ENNReal)
          (fun ξ : ℝ => ∑ m ∈ U, (if ω m then (1 : ℂ) else -1) * (Φ m : ℝ → ℂ) ξ) C ∧
        IsLqMultiplierBound (ENNReal.ofReal (2 * (k₀ : ℝ)))
          (fun ξ : ℝ => ∑ m ∈ U, (if ω m then (1 : ℂ) else -1) * (Φ m : ℝ → ℂ) ξ) C := by
    intro U ω
    have hsum : (fun ξ : ℝ => ∑ m ∈ U, (if ω m then (1 : ℂ) else -1) * (Φ m : ℝ → ℂ) ξ)
        = fun ξ : ℝ => ∑ m ∈ U.filter (fun m => core ρ C₀ l₁ l₂ k₁ 0 a m ∧
              Farey Cρc ρ l₂ 0 a m),
            (if ω m then (1 : ℂ) else -1) *
              (varphitildeNt P d (Nat.floor (a m)) 0 t ξ
                - varphitildeN d (Nat.floor (a m)) 0 ξ) := by
      funext ξ
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [hΦcoe m]
      by_cases hc : core ρ C₀ l₁ l₂ k₁ 0 a m ∧ Farey Cρc ρ l₂ 0 a m
      · simp only [hc, and_self, if_true]
      · simp only [hc, if_false, mul_zero]
    rw [hsum]
    refine ⟨?_, (hCmult t ht a ha ha1 (U.filter _) ω).2⟩
    rw [← ofReal_two_eq]
    exact (hCmult t ht a ha ha1 (U.filter _) ω).1
  -- ## the variational estimate at the chosen height
  have hmain := hvar l (fareyK Cρc ρ l₂) hCρ hk C hCpos Φ hnarrow hMult g
  -- ## transport the symbol family to the clipped difference family
  have hcongr : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Tle ρ l (fun ξ : ℝ => if core ρ C₀ l₁ l₂ k₁ 0 a n ∧
            Farey Cρc ρ l₂ 0 a n then
            varphitildeNt P d (Nat.floor (a n)) 0 t ξ
              - varphitildeN d (Nat.floor (a n)) 0 ξ else 0) g x))
      = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Tle ρ l (Φ n : ℝ → ℂ) g x)) := by
    funext x
    congr 1
    funext n
    rw [(hΦcoe n).symm]
  rw [hcongr]
  -- ## the constant bookkeeping
  refine hmain.trans ?_
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
  have hlR : (l : ℝ) ≤ (l₂ : ℝ) := by exact_mod_cast hl
  have hK0C : (0 : ℝ) ≤ K0 * C := mul_nonneg hK0pos.le hCpos.le
  calc K0 * (1 + (l : ℝ)) * C = K0 * C * (1 + (l : ℝ)) := by ring
    _ ≤ K0 * C * (1 + (l₂ : ℝ)) := by nlinarith [hlR]

end

end Work.KMTAreas.A7Hi
