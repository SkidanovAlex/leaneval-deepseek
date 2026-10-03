/-
# The Case B spike bound with the bounded-bump interface

`Work.KMTPlan.A6.caseBSpikeLe` with the single-scale estimate `hSS` in its `Linf` form: the two
extra hypotheses `MemLp (periodize φ) ⊤ circleMeasure`, `MemLp (periodize ψ) ⊤ circleMeasure` of
`SSUBodyAtLinf` are supplied for the two concrete bumps `φ_{N,0,j₁}(t)`, `φ̃_{N,L,j₂}(t)`,
`N = ⌊a 0⌋`, from their measurability, their narrow support and their pointwise bounds
(`Work.KMTPlan.A6.Linf.memLp_periodize_of_arc`), before invoking the `Linf` form
`Work.KMTPlan.A6.Linf.spikeNarrowL2` of the narrow spike bound.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowModelVarCaseBDefs
import Submission.Work.KMTPlan.A6.LinfSpikeNarrowL2

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6.Linf

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

private lemma norm_varphiNtj_k0_le_eight (N : ℕ) (j : ℤ) (t x : ℝ) (hj : j = 0 ∨ j = 1) :
    ‖Work.KMTPlan.A6.varphiNtj N 0 j t x‖ ≤ 8 := by
  rcases hj with rfl | rfl
  · have h : Work.KMTPlan.A6.varphiNtj N 0 0 t x = Work.KMTAreas.A7.varphiNt N 0 t x := by
      simp only [Work.KMTPlan.A6.varphiNtj, zpow_zero, one_mul]
    rw [h]
    exact le_trans (Work.KMTPlan.A6.varphiNt_norm_le_one N 0 t x) (by norm_num)
  · by_cases hz : Work.KMTAreas.A7.varphiNt N 0 t x = 0
    · rw [Work.KMTPlan.A6.varphiNtj, hz, mul_zero, norm_zero]
      norm_num
    · have h1 : Work.KMTPlan.A6.varphiNtj N 0 1 t x
          = (((N : ℝ) * x : ℝ) : ℂ) * Work.KMTAreas.A7.varphiNt N 0 t x := by
        simp only [Work.KMTPlan.A6.varphiNtj, Nat.cast_zero, neg_zero, Real.rpow_zero,
          one_mul, zpow_one]
      rw [h1, norm_mul]
      have h2 : ‖(((N : ℝ) * x : ℝ) : ℂ)‖ = |(N : ℝ) * x| := by simp
      rw [h2, abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
      have hx : |x| ≤ (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ)) := by
        simpa using Work.KMTAreas.A7.varphiNt_support N 0 t x hz
      have h3 : (N : ℝ) * |x|
          ≤ (N : ℝ) * (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ)) :=
        mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg N)
      have h4 : (N : ℝ) * (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ)) < 2 := by
        have hlt := Work.KMTPlan.A6.lt_two_mul_pow_logN N
        have hp : (0 : ℝ) < (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ)) :=
          Real.rpow_pos_of_pos (by norm_num) _
        have h5 := mul_lt_mul_of_pos_right hlt hp
        have h6 : (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)
            * (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ)) = 1 := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel, Real.rpow_zero]
        calc (N : ℝ) * (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ))
            < (2 * (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ))
                * (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ)) := h5
          _ = 2 * ((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)
                * (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ))) := by ring
          _ = 2 := by rw [h6, mul_one]
      calc (N : ℝ) * |x| * ‖Work.KMTAreas.A7.varphiNt N 0 t x‖
          ≤ ((N : ℝ) * (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ))) * 1 :=
            mul_le_mul h3 (Work.KMTPlan.A6.varphiNt_norm_le_one N 0 t x)
              (norm_nonneg _) (by positivity)
        _ ≤ 2 := by rw [mul_one]; exact le_of_lt h4
        _ ≤ 8 := by norm_num

/-! ## The spike bound -/

theorem caseBSpikeLe
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (ρ : ℝ) (hρ : 0 < ρ)
    {cS : ℝ} (hcS : 0 < cS) {Cssu : NNReal}
    (hSS : Work.KMTPlan.A6.SSUBodyAtLinf P cS Cssu ρ)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 8)
    (a : ℕ → NNReal) (l₁ l₂ L : ℕ) (j₁ j₂ : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
    (hk₁ : ¬ (0 = 0 ∧ j₁ = -1)) (hk₂ : ¬ (L = 0 ∧ j₂ = -1))
    (Bsp : ℕ)
    (hsup : ∀ Nr : ℕ, Work.Analysis.EndVar.inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (0 : ℤ) (L : ℤ) Nr →
      Nr ≤ Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ 0 L) →
      Bsp ≤ Work.KMTPlan.A6.lcL l₁ l₂ 0 L →
      L + 3 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ 0 L)
        ≤ (Work.Analysis.EndVar.logN Nr).toNat)
    (hBL : Bsp ≤ L) (hLc : Work.KMTPlan.A6.lcL l₁ l₂ 0 L = L)
    (hu1 : 1 ≤ Work.KMTAreas.A7.uScale ρ L)
    (huL : (max l₁ l₂ : ℝ) ≤ (Work.KMTAreas.A7.uScale ρ L : ℝ))
    (hu2 : (2 : ℝ) ^ (ρ * (max l₁ l₂ : ℝ)) ≤ (Work.KMTAreas.A7.uScale ρ L : ℝ))
    (hNA₁ : Work.Analysis.IonescuWainger.NonAliasing
      (-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ))) (Work.KMTAreas.A7.diffFreqs ρ l₁))
    (hNA₂ : Work.Analysis.IonescuWainger.NonAliasing
      (-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ))) (Work.KMTAreas.A7.diffFreqs ρ l₂))
    (h0 : Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ 0 L 0)
    {Cb : ℝ} (hCb : 0 < Cb)
    (hCbb : ∀ (N k : ℕ) (j : ℤ) (t : ℝ), j ∈ ({-1, 0, 1} : Finset ℤ) →
      ¬ (k = 0 ∧ j = -1) → 1 ≤ N → ∀ ξ : ℝ,
      ‖Work.KMTPlan.A6.varphitildeNtj P N k j t ξ‖ ≤ Cb)
    (f g : ℤ → ℂ) (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count) :
    MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal
        ‖Work.KMTPlan.A6.caseBSpike ρ P a f g l₁ l₂ 0 L j₁ j₂ t x‖)
        1 MeasureTheory.Measure.count
      ≤ (Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
          * (ENNReal.ofReal (max 8 Cb) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
          * (ENNReal.ofReal (max 8 Cb) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) := by
  classical
  -- the `f`-side twist is `0` or `1`
  have hj₁' : j₁ = 0 ∨ j₁ = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj₁
    rcases hj₁ with h | h | h
    · exact absurd ⟨rfl, h⟩ hk₁
    · exact Or.inl h
    · exact Or.inr h
  -- the window inequality `L + 3u ≤ Log N` at `N = ⌊a 0⌋`
  have hlogsup : L + 3 * Work.KMTAreas.A7.uScale ρ L
      ≤ (Work.Analysis.EndVar.logN (Nat.floor (a 0))).toNat := by
    obtain ⟨hidx, hcut⟩ := Work.KMTPlan.A6.lowSmallSet_iff.mp h0
    have h := hsup (Nat.floor (a 0)) hidx hcut (by rw [hLc]; exact hBL)
    rwa [hLc] at h
  -- `⌊a 0⌋ ≥ 1`: `logN N ≥ 3u ≥ 3` forces `max N 2 ≥ 2^3 = 8`
  have hNr : 1 ≤ Nat.floor (a 0) := by
    have h3 : 3 ≤ (Work.Analysis.EndVar.logN (Nat.floor (a 0))).toNat := by
      have := hu1
      omega
    have hval : (Work.Analysis.EndVar.logN (Nat.floor (a 0))).toNat
        = Nat.log 2 (max (Nat.floor (a 0)) 2) := by
      simp only [Work.Analysis.EndVar.logN, Int.toNat_natCast]
    rw [hval] at h3
    by_contra hcon
    push_neg at hcon
    have hlt : Nat.log 2 (max (Nat.floor (a 0)) 2) < 3 :=
      (Nat.log_lt_iff_lt_pow (b := 2) (by norm_num) (by omega)).mpr (by omega)
    omega
  -- the same inequality, as reals
  have hLU : (L : ℝ) + 3 * (Work.KMTAreas.A7.uScale ρ L : ℝ)
      ≤ (Work.Analysis.EndVar.logN (Nat.floor (a 0)) : ℝ) := by
    have h1 : ((L + 3 * Work.KMTAreas.A7.uScale ρ L : ℕ) : ℤ)
        ≤ (((Work.Analysis.EndVar.logN (Nat.floor (a 0))).toNat : ℕ) : ℤ) := by
      exact_mod_cast hlogsup
    push_cast at h1
    rw [Int.toNat_of_nonneg (Work.Analysis.EndVar.logN_nonneg _)] at h1
    have h3 : (((L : ℤ) + 3 * (Work.KMTAreas.A7.uScale ρ L : ℤ) : ℤ) : ℝ)
        ≤ ((Work.Analysis.EndVar.logN (Nat.floor (a 0)) : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith
  -- the `f`-side arc support
  have hφarc : ∀ ξ : ℝ, Work.KMTPlan.A6.varphiNtj (Nat.floor (a 0)) 0 j₁ t ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ (-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ))) := by
    intro ξ hξ
    have hφt : Work.KMTAreas.A7.varphiNt (Nat.floor (a 0)) 0 t ξ ≠ 0 := by
      intro hφ0
      exact hξ (by rw [Work.KMTPlan.A6.varphiNtj, hφ0, mul_zero])
    have h1 := Work.KMTAreas.A7.varphiNt_support (Nat.floor (a 0)) 0 t ξ hφt
    have hexp : -(Work.Analysis.EndVar.logN (Nat.floor (a 0)) : ℝ)
        ≤ ((-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ)) : ℤ) : ℝ) := by
      push_cast
      linarith
    have h1' : |ξ| ≤ (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN (Nat.floor (a 0)) : ℝ)) := by
      simpa using h1
    calc |ξ| ≤ (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN (Nat.floor (a 0)) : ℝ)) := h1'
      _ ≤ (2 : ℝ) ^ (-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ))) := by
          rw [← Real.rpow_intCast]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  -- the `g`-side arc support
  have hψarc : ∀ ξ : ℝ, Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a 0)) L j₂ t ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ)
        ^ (-(3 * (P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ L : ℤ))) := by
    intro ξ hξ
    have hψt : Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a 0)) L t ξ ≠ 0 := by
      intro hψ0
      exact hξ (by rw [Work.KMTPlan.A6.varphitildeNtj, hψ0, mul_zero])
    have h1 := Work.KMTAreas.A7.varphitildeNt_support_all P P.natDegree (Nat.floor (a 0)) L t ξ hψt
    have hd0 : (0 : ℝ) ≤ (P.natDegree : ℝ) := by positivity
    have hexp : (P.natDegree : ℝ)
          * ((L : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a 0)) : ℝ))
        ≤ ((-(3 * (P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ L : ℤ)) : ℤ) : ℝ) := by
      have h1' : (L : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a 0)) : ℝ)
          ≤ -3 * (Work.KMTAreas.A7.uScale ρ L : ℝ) := by linarith
      have h2' := mul_le_mul_of_nonneg_left h1' hd0
      have h3' : (P.natDegree : ℝ) * (-3 * (Work.KMTAreas.A7.uScale ρ L : ℝ))
          = ((-(3 * (P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ L : ℤ)) : ℤ) : ℝ) := by
        push_cast; ring
      linarith [h2', h3']
    calc |ξ| ≤ (2 : ℝ) ^ ((P.natDegree : ℝ)
          * ((L : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a 0)) : ℝ))) := h1
      _ ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ L : ℤ))) := by
          rw [← Real.rpow_intCast]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  -- the two pointwise bounds
  have hφb : ∀ ξ : ℝ, ‖Work.KMTPlan.A6.varphiNtj (Nat.floor (a 0)) 0 j₁ t ξ‖ ≤ max 8 Cb := by
    intro ξ
    exact le_trans (norm_varphiNtj_k0_le_eight (Nat.floor (a 0)) j₁ t ξ hj₁')
      (le_max_left _ _)
  have hψb : ∀ ξ : ℝ, ‖Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a 0)) L j₂ t ξ‖
      ≤ max 8 Cb := by
    intro ξ
    exact le_trans (hCbb (Nat.floor (a 0)) L j₂ t hj₂ hk₂ hNr ξ) (le_max_right _ _)
  -- the two `L^∞`-membership facts of the periodised bumps (the extra hypotheses of `hSS`)
  have hRφ : (0 : ℝ) ≤ (2 : ℝ) ^ (-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ))) := by positivity
  have hRψ : (0 : ℝ) ≤
      (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ L : ℤ))) := by positivity
  have hMlpφ : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize
      (Work.KMTPlan.A6.varphiNtj (Nat.floor (a 0)) 0 j₁ t)) ⊤
      Work.Analysis.IonescuWainger.circleMeasure :=
    memLp_periodize_of_arc (Work.KMTPlan.A6.varphiNtj (Nat.floor (a 0)) 0 j₁ t)
      (measurable_varphiNtj (Nat.floor (a 0)) 0 j₁ hj₁ t)
      ((2 : ℝ) ^ (-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ)))) (max 8 Cb)
      hRφ hφarc hφb
  have hMlpψ : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize
      (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a 0)) L j₂ t)) ⊤
      Work.Analysis.IonescuWainger.circleMeasure :=
    memLp_periodize_of_arc (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a 0)) L j₂ t)
      (measurable_varphitildeNtj P (Nat.floor (a 0)) L j₂ hj₂ t)
      ((2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ L : ℤ)))) (max 8 Cb)
      hRψ hψarc hψb
  -- the single-scale estimate
  have hCb' : (0 : ℝ) ≤ max 8 Cb := le_trans (by norm_num) (le_max_left _ _)
  have hmain := spikeNarrowL2 P hd ρ hρ hcS hSS l₁ l₂ (Work.KMTAreas.A7.uScale ρ L)
    hu1 huL hu2 (φ := Work.KMTPlan.A6.varphiNtj (Nat.floor (a 0)) 0 j₁ t)
    (ψ := Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a 0)) L j₂ t) (Cb := max 8 Cb)
    hCb' hφb hφarc hψb hψarc hMlpφ hMlpψ hNA₁ hNA₂ f g hf hg
  -- identify the spike with the single-scale expression
  have hfun : (fun x : ℤ => ENNReal.ofReal
        ‖Work.KMTPlan.A6.caseBSpike ρ P a f g l₁ l₂ 0 L j₁ j₂ t x‖)
      = (fun x : ℤ => ENNReal.ofReal
        ‖Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂
          (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ L))
          (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ L))
          (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTPlan.A6.varphiNtj (Nat.floor (a 0)) 0 j₁ t) f)
          (Work.KMTAreas.A7.Tm ρ l₂
            (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a 0)) L j₂ t) g) x‖) := by
    funext x
    simp only [Work.KMTPlan.A6.caseBSpike, hLc]
  rw [hfun]
  exact hmain

end

end Work.KMTPlan.A6.Linf
