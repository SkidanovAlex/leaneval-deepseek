/-
# Interval integrability in `t` of the frozen slices of the §6/§8 model estimate

`Work.KMTPlan.A6.mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x` is the frozen-`t` slice of the
§6/§8 model tuple: on the (decidable) core condition `mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n` it is

  `Btwist_{m_*}(T^{l₁}_{φ_{N,t,j₁}} F, T^{l₂}_{φ̃_{N,t,j₂}} G)(x)`,

`N = ⌊a n⌋`, `F = mdlF ρ u l₁ f`, `G = mdlG ρ u l₂ g`, `u = uScale ρ L`,
`L = max (max l₁ l₂) (max k₁ k₂)`, and `0` otherwise.

This file proves that, for fixed `n, x`, the slice is an *interval-integrable* function of the
modulation parameter `t` on `[1/2,1]`:

`IntervalIntegrable (fun t => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x) volume (1/2) 1`.

Since `IntervalIntegrable f μ a b` unfolds to `IntegrableOn f (uIoc a b) μ`
(`intervalIntegrable_iff`) and `uIoc (1/2) 1` has finite measure, `Integrable.of_bound` reduces
the claim to

* measurability in `t` — this is `Work.KMTPlan.A6.MdlSliceMeasurable` (proved), and
* a bound `‖slice t‖ ≤ C` uniform on `t ∈ [1/2,1]`.

The uniform bound is proved by splitting on the modified bumps:

* for `k = 0` and `j ≤ -2` the modified bump `varphiNtj N 0 j t` is *not integrable* (it behaves
  like `ξ^j` near the frequency origin, where the bump does not vanish), so the symbol of the
  Ionescu--Wainger multiplier is non-integrable, all its Fourier coefficients — hence the whole
  kernel of `Tle ρ l (varphiNtj N 0 j t)` — vanish (`Work.KMTAreas.A7.iwKernel_eq_zero_of_not_integrable`),
  and the slice is identically zero;
* otherwise (`k ≠ 0` or `0 ≤ j`) the modified bump is `C²` with compact support and with
  `t`-uniform `L¹`-bounds (`varphiNtj_bounds`, `varphitildeNtj_bounds`), so the kernel of the
  multiplier decays like `i^{-2}` uniformly in `t` (`iwKernel_decay_of_bump`) and the two
  multiplier images of the `ℓ²` model inputs are bounded uniformly in `t` and `y`
  (`Tle_bump_l2_bounded`); `exists_bound_Btwist_uniform` then bounds the twisted bilinear
  multiplier itself.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlSliceMeasurable
import Submission.Work.KMTPlan.A6.memLp_kmtProj
import Submission.Work.KMTPlan.A6.varphiNtj_bounds
import Submission.Work.KMTPlan.A6.Tle_bump_l2_bounded
import Submission.Work.KMTPlan.A6.varphitildeNtj_bounds
import Submission.Work.KMTPlan.A6.varphiNtj_Tle_eq_zero
import Submission.Work.KMTPlan.A6.MdlSliceDegenerate
import Submission.Work.KMTAreas.A7.exists_bound_Btwist_uniform

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial
open scoped ENNReal NNReal BigOperators
open Work.KMTAreas.A7
open Work.KMTContract
open Work.Analysis.IonescuWainger

/-! ## The model inputs are in `ℓ²` -/

theorem memLp_mdlF (ρ : ℝ) (u l : ℕ) {f : ℤ → ℂ} (hf : MemLp f 2 Measure.count) :
    MemLp (mdlF ρ u l f) 2 Measure.count := by
  have h1 : MemLp (kmtProj ρ l (-(u : ℤ)) f) 2 Measure.count := memLp_kmtProj ρ l _ hf
  have h2 : MemLp (kmtProj ρ (l - 1) (-(u : ℤ)) f) 2 Measure.count := memLp_kmtProj ρ (l - 1) _ hf
  rw [mdlF, Work.Analysis.EndVar.piExact]
  split
  · exact memLp_kmtProj ρ 0 _ hf
  · simpa [kmtPj] using h1.sub h2

theorem memLp_mdlG (ρ : ℝ) (P : Polynomial ℤ) (u l : ℕ) {g : ℤ → ℂ}
    (hg : MemLp g 2 Measure.count) :
    MemLp (mdlG ρ P u l g) 2 Measure.count := by
  have h1 : MemLp (kmtProj ρ l (-((P.natDegree : ℤ) * (u : ℤ))) g) 2 Measure.count :=
    memLp_kmtProj ρ l _ hg
  have h2 : MemLp (kmtProj ρ (l - 1) (-((P.natDegree : ℤ) * (u : ℤ))) g) 2 Measure.count :=
    memLp_kmtProj ρ (l - 1) _ hg
  rw [mdlG, Work.Analysis.EndVar.piExact]
  split
  · exact memLp_kmtProj ρ 0 _ hg
  · simpa [kmtPj] using h1.sub h2

/-! ## The twisted bilinear multiplier vanishes when one argument does -/

theorem Btwist_zero_left (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (k : ℤ → ℂ) (x : ℤ) : Btwist ρ P l₁ l₂ m₁ m₂ 0 k x = 0 := by
  simp [Btwist]

theorem Btwist_zero_right (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (h : ℤ → ℂ) (x : ℤ) : Btwist ρ P l₁ l₂ m₁ m₂ h 0 x = 0 := by
  simp [Btwist]

/-! ## The uniform bound in the "good" case -/

theorem bound_good (ρ : ℝ) (P : Polynomial ℤ) (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ)
    (j₁ j₂ : ℤ) (N : ℕ) (x : ℤ) (hf : MemLp f 2 Measure.count) (hg : MemLp g 2 Measure.count)
    (h₁ : k₁ ≠ 0 ∨ 0 ≤ j₁) (h₂ : k₂ ≠ 0 ∨ 0 ≤ j₂) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      ‖Btwist ρ P l₁ l₂ (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
          (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
          (Tle ρ l₁ (varphiNtj N k₁ j₁ t)
            (mdlF ρ (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f))
          (Tle ρ l₂ (varphitildeNtj P N k₂ j₂ t)
            (mdlG ρ P (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g))
          x‖ ≤ C := by
  -- uniform `L¹`-bounds for the two modified bumps
  obtain ⟨S₁, hS₁nn, hB₁⟩ := varphiNtj_bounds N k₁ j₁ h₁
  obtain ⟨S₂, hS₂nn, hB₂⟩ := varphitildeNtj_bounds P N k₂ j₂ h₂
  -- the two multiplier images are bounded, uniformly in `t ∈ [1/2,1]` and `y : ℤ`
  have hdec₁ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ i : ℤ,
      ‖TleKer ρ l₁ (fun ξ => varphiNtj N k₁ j₁ t ξ) i‖
        ≤ (4 * (((iwArithFreqs ρ l₁).card : ℝ) * S₁) + 1) * ‖kmtKernWeight i‖ := by
    intro t ht i
    exact iwKernel_decay_of_bump (iwArithFreqs ρ l₁) (hB₁ t ht).1 (hB₁ t ht).2.1
      hS₁nn (hB₁ t ht).2.2.1 (hB₁ t ht).2.2.2 i
  have hdec₂ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ i : ℤ,
      ‖TleKer ρ l₂ (fun ξ => varphitildeNtj P N k₂ j₂ t ξ) i‖
        ≤ (4 * (((iwArithFreqs ρ l₂).card : ℝ) * S₂) + 1) * ‖kmtKernWeight i‖ := by
    intro t ht i
    exact iwKernel_decay_of_bump (iwArithFreqs ρ l₂) (hB₂ t ht).1 (hB₂ t ht).2.1
      hS₂nn (hB₂ t ht).2.2.1 (hB₂ t ht).2.2.2 i
  obtain ⟨Ch, hCh⟩ := Tle_bump_l2_bounded ρ l₁ (C₀ := 4 * (((iwArithFreqs ρ l₁).card : ℝ) * S₁) + 1)
    (by positivity) hdec₁ (memLp_mdlF ρ (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ hf)
  obtain ⟨Ck, hCk⟩ := Tle_bump_l2_bounded ρ l₂ (C₀ := 4 * (((iwArithFreqs ρ l₂).card : ℝ) * S₂) + 1)
    (by positivity) hdec₂ (memLp_mdlG ρ P (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ hg)
  -- decay of the two continuous symbols `m_*` of the twisted bilinear multiplier
  have hcw₁ : ∃ Cd : ℝ, ∀ j : ℤ,
      ‖cw (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) j‖
        ≤ Cd / (1 + |(j : ℝ)|) ^ 2 := by
    obtain ⟨Cd, -, hCd⟩ := cw_etaCut_decay
      (-(2 * (uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ)))
    exact ⟨Cd, fun j => by simpa [mStarF] using hCd j⟩
  have hcw₂ : ∃ Cd : ℝ, ∀ j : ℤ,
      ‖cw (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) j‖
        ≤ Cd / (1 + |(j : ℝ)|) ^ 2 := by
    obtain ⟨Cd, -, hCd⟩ := cw_etaCut_decay
      (-((P.natDegree : ℤ) * 2 * (uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ)))
    exact ⟨Cd, fun j => by simpa [mStargF] using hCd j⟩
  obtain ⟨C, hC⟩ := exists_bound_Btwist_uniform ρ P l₁ l₂
    (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
    (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
    (fun t : ℝ => Tle ρ l₁ (varphiNtj N k₁ j₁ t)
      (mdlF ρ (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f))
    (fun t : ℝ => Tle ρ l₂ (varphitildeNtj P N k₂ j₂ t)
      (mdlG ρ P (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g))
    x hcw₁ hcw₂ ⟨Ch, hCh⟩ ⟨Ck, hCk⟩
  exact ⟨C, fun t ht => hC t ht⟩

/-! ## The target -/

theorem MdlSliceIntervalIntegrable (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (n : ℕ) (x : ℤ)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    (hk₁ : k₁ = 0 → j₁ ≠ -1) (hk₂ : k₂ = 0 → j₂ ≠ -1) :
    IntervalIntegrable (fun t : ℝ => Work.KMTPlan.A6.mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
      MeasureTheory.volume (1 / 2) 1 := by
  have hmeas : Measurable (fun t : ℝ =>
      Work.KMTPlan.A6.mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x) :=
    MdlSliceMeasurable ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ n x
  rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  by_cases hc : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · have hfun : (fun t : ℝ => Work.KMTPlan.A6.mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
        = fun t : ℝ =>
            Btwist ρ P l₁ l₂ (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
              (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
              (Tle ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t)
                (mdlF ρ (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f))
              (Tle ρ l₂ (varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
                (mdlG ρ P (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g)) x := by
      funext t
      rw [mdlSliceJ_apply, if_pos hc]
    rw [hfun]
    rcases em (k₁ = 0 ∧ j₁ ≤ -2) with hd₁ | hd₁
    · have hzero : (fun t : ℝ =>
          Btwist ρ P l₁ l₂ (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
            (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
            (Tle ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t)
              (mdlF ρ (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f))
            (Tle ρ l₂ (varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
              (mdlG ρ P (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g)) x)
          = fun _ : ℝ => (0 : ℂ) := by
        funext t
        have h0 : Tle ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t)
            (mdlF ρ (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f) = 0 := by
          rw [hd₁.1]
          exact varphiNtj_Tle_eq_zero ρ l₁ (Nat.floor (a n)) j₁ hd₁.2 t _
        rw [h0, Btwist_zero_left]
      rw [hzero]
      exact integrableOn_zero
    · rcases em (k₂ = 0 ∧ j₂ ≤ -2) with hd₂ | hd₂
      · have hzero : (fun t : ℝ =>
            Btwist ρ P l₁ l₂ (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
              (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
              (Tle ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t)
                (mdlF ρ (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f))
              (Tle ρ l₂ (varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
                (mdlG ρ P (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g)) x)
            = fun _ : ℝ => (0 : ℂ) := by
          funext t
          have h0 : Tle ρ l₂ (varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
              (mdlG ρ P (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g) = 0 := by
            rw [hd₂.1]
            exact varphitildeNtj_Tle_eq_zero_self P ρ l₂ (Nat.floor (a n)) j₂ hd₂.2 t _
          rw [h0, Btwist_zero_right]
        rw [hzero]
        exact integrableOn_zero
      · have hg₁ : k₁ ≠ 0 ∨ 0 ≤ j₁ := by
          by_cases hk : k₁ = 0
          · right
            have hne : j₁ ≠ -1 := hk₁ hk
            have hge : ¬ (j₁ ≤ -2) := fun hle => hd₁ ⟨hk, hle⟩
            omega
          · exact Or.inl hk
        have hg₂ : k₂ ≠ 0 ∨ 0 ≤ j₂ := by
          by_cases hk : k₂ = 0
          · right
            have hne : j₂ ≠ -1 := hk₂ hk
            have hge : ¬ (j₂ ≤ -2) := fun hle => hd₂ ⟨hk, hle⟩
            omega
          · exact Or.inl hk
        obtain ⟨C, hC⟩ := bound_good ρ P f g l₁ l₂ k₁ k₂ j₁ j₂ (Nat.floor (a n)) x hf hg hg₁ hg₂
        refine MeasureTheory.Integrable.of_bound ?_ C ?_
        · exact (hfun ▸ hmeas).aestronglyMeasurable
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
          exact hC t (Set.Ioc_subset_Icc_self ht)
  · have hzero : (fun t : ℝ => Work.KMTPlan.A6.mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
        = fun _ : ℝ => (0 : ℂ) := by
      funext t
      rw [mdlSliceJ_apply, if_neg hc]
    rw [hzero]
    exact integrableOn_zero

end

end Work.KMTPlan.A6
