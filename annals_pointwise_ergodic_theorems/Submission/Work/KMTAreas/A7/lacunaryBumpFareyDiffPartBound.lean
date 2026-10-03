import Mathlib
import Submission.Work.KMTAreas.A7.lacunaryBumpAux
import Submission.Work.KMTAreas.A7.varphiNSch

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## The clipped difference family

The target `lacunaryBumpFareyDiffPartBound` controls the `r`-variation of the *difference* family
`n ↦ Tle ρ l (φ_{⌊a n⌋,t} − φ_{⌊a n⌋}) f`, clipped to the scales where `core` holds and where the
modulated bump of the bottom height `k₁ = 0` is narrow (`Farey`).  On the clipped scales both
`φ_N` and `φ_{N,t}` are supported in the narrow arc `realArc (fareyK Cρc ρ l₁)`, so the whole
family is a lacunary family of Schwartz symbols supported in that single arc; the two-endpoint
multiplier input `multBound_varphiNt_diff_two_endpoints` then supplies the hypotheses of
`varEst_of_narrow_symbols_twoEndpoints`. -/

/-- The clipped difference bump family `n ↦ (φ_{⌊a n⌋,t} − φ_{⌊a n⌋})·1_{core ∧ Farey}` as
Schwartz functions. -/
def fareyDiffSch (ρ : ℝ) (C₀ : ℕ) (Cρc : ℝ) (a : ℕ → NNReal) (l₁ l₂ k₂ : ℕ) (m : ℕ)
    (t : ℝ) : SchwartzMap ℝ ℂ :=
  if core ρ C₀ l₁ l₂ 0 k₂ a m ∧ Farey Cρc ρ l₁ 0 a m then
    varphiNtSch (Nat.floor (a m)) 0 t - varphiNSch (Nat.floor (a m)) 0
  else 0

/-- The function underlying `fareyDiffSch` is the clipped difference symbol. -/
lemma fareyDiffSch_coe (ρ : ℝ) (C₀ : ℕ) (Cρc : ℝ) (a : ℕ → NNReal) (l₁ l₂ k₂ m : ℕ) (t : ℝ) :
    (fareyDiffSch ρ C₀ Cρc a l₁ l₂ k₂ m t : ℝ → ℂ)
      = fun ξ : ℝ => if core ρ C₀ l₁ l₂ 0 k₂ a m ∧ Farey Cρc ρ l₁ 0 a m then
          varphiNt (Nat.floor (a m)) 0 t ξ - varphiN (Nat.floor (a m)) 0 ξ else 0 := by
  unfold fareyDiffSch
  by_cases h : core ρ C₀ l₁ l₂ 0 k₂ a m ∧ Farey Cρc ρ l₁ 0 a m
  · simp only [h]
    funext ξ
    simp
  · simp only [h, if_false]
    funext ξ
    simp

/-- The *unmodulated* bump `φ_N` at the bottom height is narrow on the Farey scales: its support
coincides with that of `φ_{N,t}` (the modulation is nowhere zero), so the support bound of
`varphiNt_support_le_all` applies to it. -/
lemma varphiN_narrow_of_farey {Cρc ρ : ℝ} {l₁ : ℕ} {a : ℕ → NNReal} {m : ℕ} {t : ℝ}
    (h : Farey Cρc ρ l₁ 0 a m) :
    ∀ ξ : ℝ, varphiN (Nat.floor (a m)) 0 ξ ≠ 0 → ξ ∈ realArc (fareyK Cρc ρ l₁) := by
  intro ξ hξ
  refine narrow_of_farey (t := t) h ξ ?_
  show varphiN (Nat.floor (a m)) 0 ξ * ee ((Nat.floor (a m) : ℝ) * t * ξ) ≠ 0
  exact mul_ne_zero hξ (by simp [ee])

theorem lacunaryBumpFareyDiffPartBound (C₀ : ℕ) (r : NNReal) (hr : 2 < r) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (Λ : NNReal) (hΛ : 1 < Λ) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρc : ℝ, 3 ≤ Cρc ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (l l₁ l₂ k₂ : ℕ) (hl : l ≤ l₁)
        (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1)
        (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (f : ℤ → ℂ),
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l (fun ξ : ℝ =>
            if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ 0 k₂ a n ∧
              Work.KMTAreas.A7.Farey Cρc ρ l₁ 0 a n
            then Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ -
              Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ else 0) f x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (K * (1 + (l₁ : ℝ))) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
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
  obtain ⟨C, hCpos, hCmult⟩ := multBound_varphiNt_diff_two_endpoints Λ hΛ k₀ hk₀2
  -- ## the narrowness constant
  obtain ⟨Cρc, hCρc3, hCρcCρ, hCρc1⟩ :
      ∃ Cρc : ℝ, 3 ≤ Cρc ∧ Cρ ≤ Cρc ∧ 1 < Cρc :=
    ⟨max Cρ 3 + 1, by linarith [le_max_right Cρ (3 : ℝ)],
      by linarith [le_max_left Cρ (3 : ℝ)], by linarith [le_max_right Cρ (3 : ℝ)]⟩
  refine ⟨Cρc, hCρc3, K0 * C, mul_pos hK0pos hCpos, ?_⟩
  intro l l₁ l₂ k₂ hl t ht a ha ha1 f
  -- ## the narrowness height and its two properties
  have hCρ : GoodMajorArcs ρ Cρ l (fareyK Cρc ρ l₁) :=
    goodMajorArcs_fareyK hCρcCρ hCρpos.le hρ.le hl
  have hk : (2 : ℝ) ^ (fareyK Cρc ρ l₁) < 1 / 2 :=
    two_rpow_fareyK_lt_half hCρc1 hρ.le l₁
  -- ## the clipped difference family as Schwartz maps
  let Φ : ℕ → SchwartzMap ℝ ℂ := fun m => fareyDiffSch ρ C₀ Cρc a l₁ l₂ k₂ m t
  have hΦcoe : ∀ m : ℕ, (Φ m : ℝ → ℂ)
      = fun ξ : ℝ => if core ρ C₀ l₁ l₂ 0 k₂ a m ∧ Farey Cρc ρ l₁ 0 a m then
          varphiNt (Nat.floor (a m)) 0 t ξ - varphiN (Nat.floor (a m)) 0 ξ else 0 :=
    fun m => fareyDiffSch_coe ρ C₀ Cρc a l₁ l₂ k₂ m t
  -- ## narrowness
  have hnarrow : ∀ m ξ, (Φ m : ℝ → ℂ) ξ ≠ 0 → ξ ∈ realArc (fareyK Cρc ρ l₁) := by
    intro m ξ hξ
    by_cases hc : core ρ C₀ l₁ l₂ 0 k₂ a m ∧ Farey Cρc ρ l₁ 0 a m
    · have hD : varphiNt (Nat.floor (a m)) 0 t ξ - varphiN (Nat.floor (a m)) 0 ξ ≠ 0 := by
        simpa only [hΦcoe m, hc, and_self, if_true] using hξ
      by_cases h1 : varphiNt (Nat.floor (a m)) 0 t ξ = 0
      · refine varphiN_narrow_of_farey (t := t) hc.2 ξ ?_
        intro h2
        rw [h1, h2, sub_zero] at hD
        exact hD rfl
      · exact narrow_of_farey (t := t) hc.2 ξ h1
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
        = fun ξ : ℝ => ∑ m ∈ U.filter (fun m => core ρ C₀ l₁ l₂ 0 k₂ a m ∧
              Farey Cρc ρ l₁ 0 a m),
            (if ω m then (1 : ℂ) else -1) *
              (varphiNt (Nat.floor (a m)) 0 t ξ - varphiN (Nat.floor (a m)) 0 ξ) := by
      funext ξ
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [hΦcoe m]
      by_cases hc : core ρ C₀ l₁ l₂ 0 k₂ a m ∧ Farey Cρc ρ l₁ 0 a m
      · simp only [hc, and_self, if_true]
      · simp only [hc, if_false, mul_zero]
    rw [hsum]
    refine ⟨?_, (hCmult t ht a ha ha1 (U.filter _) ω).2⟩
    rw [← ofReal_two_eq]
    exact (hCmult t ht a ha ha1 (U.filter _) ω).1
  -- ## the variational estimate at the chosen height
  have hmain := hvar l (fareyK Cρc ρ l₁) hCρ hk C hCpos Φ hnarrow hMult f
  -- ## transport the symbol family to the clipped difference family
  have hcongr : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Tle ρ l (fun ξ : ℝ => if core ρ C₀ l₁ l₂ 0 k₂ a n ∧
            Farey Cρc ρ l₁ 0 a n then
            varphiNt (Nat.floor (a n)) 0 t ξ - varphiN (Nat.floor (a n)) 0 ξ else 0) f x))
      = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Tle ρ l (Φ n : ℝ → ℂ) f x)) := by
    funext x
    congr 1
    funext n
    rw [(hΦcoe n).symm]
  rw [hcongr]
  -- ## the constant bookkeeping `K0 (1+l) C ≤ (K0 C) (1+l₁)`
  refine hmain.trans ?_
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
  have hlR : (l : ℝ) ≤ (l₁ : ℝ) := by exact_mod_cast hl
  have hK0C : (0 : ℝ) ≤ K0 * C := mul_nonneg hK0pos.le hCpos.le
  calc K0 * (1 + (l : ℝ)) * C = K0 * C * (1 + (l : ℝ)) := by ring
    _ ≤ K0 * C * (1 + (l₁ : ℝ)) := by nlinarith [hlR]

end

end Work.KMTAreas.A7
