import Mathlib
import Submission.Work.KMTPlan.A6.LowModApproxBoundedH.lvl0Defs
import Submission.Work.KMTPlan.A6.LowModApproxBoundedH.lvl0CoreMono
import Submission.Work.KMTPlan.A6.LowModApproxBoundedH.lvl0Threshold
import Submission.Work.KMTAreas.A7.varShiftDiffPrep
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6.LowModApproxBoundedH

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7

/-! ## Auxiliary lemmas for the `ρ`-transfer -/

/-- **The level-`0` Ionescu--Wainger multiplier is independent of `ρ`**: at height `0` the
arithmetic frequency set is the singleton `{0}` for every `ρ`, so the multiplier is the plain
convolution with the kernel of the periodised symbol. -/
private theorem Tle_zero_rho_indep (ρ ρ' : ℝ) (φ : ℝ → ℂ) :
    Work.KMTAreas.A7.Tle ρ 0 φ = Work.KMTAreas.A7.Tle ρ' 0 φ := by
  funext f x
  rw [Work.KMTAreas.A7.Tle_zero_eq ρ φ f, Work.KMTAreas.A7.Tle_zero_eq ρ' φ f]

/-- A `Λ`-lacunary family of scales with `a n ≥ 1` grows at least geometrically: `Λ^n ≤ a n`. -/
theorem lacunary_pow_le {Λ : NNReal} {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (n : ℕ) :
    (Λ : ℝ) ^ n ≤ (a n : ℝ) := by
  have hnn : ∀ n : ℕ, Λ ^ n ≤ a n := by
    intro n
    induction n with
    | zero => simpa using ha1 0
    | succ n ih =>
        have hmul : Λ * a n ≤ a (n + 1) := by
          have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
          exact le_of_lt ((lt_div_iff₀ hpos).mp (ha n))
        calc Λ ^ (n + 1) = Λ ^ n * Λ := by ring
          _ ≤ a n * Λ := mul_le_mul_of_nonneg_right ih bot_le
          _ = Λ * a n := by ring
          _ ≤ a (n + 1) := hmul
  exact_mod_cast hnn n

/-- For `Λ > 1` the geometric sequence `Λ^M` eventually dominates any prescribed level. -/
theorem exists_pow_ge (T : ℕ) {Λ : NNReal} (h : 1 < Λ) : ∃ M : ℕ, (T : ℝ) ≤ (Λ : ℝ) ^ M := by
  have h1 : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast h
  exact ((tendsto_pow_atTop_atTop_of_one_lt h1).eventually_ge_atTop (T : ℝ)).exists

/-- The elementary `ℝ≥0∞`-arithmetic of the transfer: the two pieces of the remainder
(`ε₀` plus `4 · M · ε₀`) are dominated by the single constant `max 1 (κ · (4M+1))` times `χ`. -/
theorem ennreal_transfer_arith (κ : NNReal) (M : ℕ) (χ : ENNReal) :
    (κ : ENNReal) * χ + 4 * ((M : ENNReal) * ((κ : ENNReal) * χ))
      ≤ (((max 1 (κ * (((4 * M + 1 : ℕ)) : NNReal)))) : ENNReal) * χ := by
  have hcast : ((((4 * M + 1 : ℕ)) : NNReal) : ENNReal) = 4 * (M : ENNReal) + 1 := by
    push_cast
    ring
  have hkey : ((κ : ENNReal) * (4 * (M : ENNReal) + 1))
      ≤ (((max 1 (κ * (((4 * M + 1 : ℕ)) : NNReal)))) : ENNReal) := by
    rw [← hcast, ← ENNReal.coe_mul]
    exact ENNReal.coe_le_coe.mpr (le_max_right (1 : NNReal) _)
  calc (κ : ENNReal) * χ + 4 * ((M : ENNReal) * ((κ : ENNReal) * χ))
      = ((κ : ENNReal) * (4 * (M : ENNReal) + 1)) * χ := by ring
    _ ≤ (((max 1 (κ * (((4 * M + 1 : ℕ)) : NNReal)))) : ENNReal) * χ :=
        mul_le_mul_of_nonneg_right hkey bot_le

/-
**The `ρ`-transfer for the level-`0` clipped estimate.**  From the level-`0` estimate for every
*small* `ρ' ≤ 1/(2C₀)` deduce it for every `ρ > 0`.

Why this is the right formulation: `Lvl0 P r C₀ B ρ` (see `LowModApproxBoundedH/lvl0Defs.lean`) is
the almost-everything-there-is statement — the *only* `ρ`-dependence in the family `lvl0Fam` is the
clip `core ρ C₀ l₁ l₂ k₁ k₂ a`, because the level-`0` operator `Tle ρ 0 φ = iwConv (iwArithFreqs ρ 0)
(periodize φ)` is independent of `ρ` (`Work.KMTAreas.A7.iwArithFreqs_zero : iwArithFreqs ρ 0 = {0}`,
so `Tle ρ 0 φ = Tle ρ' 0 φ` for all `ρ, ρ'` and all `φ`, `Tle_zero_rho_indep`).  Hence the two
families `lvl0Fam ρ …` and `lvl0Fam ρ' …` differ *only* on the index set where the two clips
disagree.

The proof below implements this as follows.

1. Apply the transfer to `ρ' := min ρ (1/(2*C₀))`, so `0 < ρ'`, `ρ' ≤ ρ` and `ρ' ≤ 1/(2C₀)`; the
   estimate at `ρ'` comes from `hsmall`, giving `C' : NNReal → NNReal`.
2. Since `lcL l₁ l₂ k₁ k₂ ≤ B`, the clip `core ρ …` is a tail in the scale: `core ρ C₀ l₁ l₂ k₁ k₂ a n`
   holds as soon as `⌊a n⌋ ≥ T`, where `T` is a threshold depending only on `ρ, C₀, B`
   (`lvl0Threshold`).
3. Lacunarity gives `(Λ : ℝ)^n ≤ a n` (`lacunary_pow_le`), hence for `n ≥ M`, where `M` is the
   first index with `(Λ:ℝ)^M ≥ T` (`exists_pow_ge`), *both* clips hold at `n`: `core ρ ⟹ core ρ'`
   because `ρ' ≤ ρ` (`lvl0CoreMono`).
4. `1_{core ρ} u = 1_{core ρ'} u - 1_{core ρ' \ core ρ} u` pointwise, where `u` is the unclipped
   family `n ↦ Tle ρ 0 (φ̃_{⌊a n⌋,t}) F`.  The variational assembly
   `eLpNorm_variationalNorm_le_of_approx` applied with the finite index set `range M` (on which the
   two clips may disagree) bounds the variational norm of the `ρ`-family by that of the `ρ'`-family
   plus the finite remainder; *both* terms are bounded by `C' Λ · ‖F‖₂`, because the remaining values
   `u n` occur at indices where `core ρ'` holds, so they are dominated by the supremum part of the
   `ρ'`-variational norm of the hypothesis.
5. Assemble: `Lvl0`'s constant is `Λ ↦ max 1 (C' Λ · (4 M + 1))`, and the index `M` (which depends
   on `Λ`) is absorbed into it (`ennreal_transfer_arith`).
-/
theorem lvl0Transfer (P : Polynomial ℤ) (r : NNReal) (hr : 2 < r) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (B : ℕ)
    (hsmall : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / (2 * (C₀ : ℝ)) →
      Work.KMTPlan.A6.LowModApproxBoundedH.Lvl0 P r C₀ B ρ) :
    ∀ ρ : ℝ, 0 < ρ → Work.KMTPlan.A6.LowModApproxBoundedH.Lvl0 P r C₀ B ρ := by
  classical
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) hr.le
  have hC₀R : (0 : ℝ) < (C₀ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC₀)
  have hden : (0 : ℝ) < 1 / (2 * (C₀ : ℝ)) := by
    apply div_pos one_pos
    linarith
  intro ρ hρ
  -- The transfer step: from the estimate at `ρ' ≤ ρ` get the estimate at `ρ`.
  have hgen : ∀ ρ' : ℝ, ρ' ≤ ρ → Work.KMTPlan.A6.LowModApproxBoundedH.Lvl0 P r C₀ B ρ' →
      Work.KMTPlan.A6.LowModApproxBoundedH.Lvl0 P r C₀ B ρ := by
    intro ρ' hρ'le hsmall'
    obtain ⟨C', hC'⟩ := hsmall'
    -- The threshold in the scale, uniform over the multi-indices with `lcL ≤ B`.
    obtain ⟨T, hT⟩ := lvl0Threshold ρ hρ C₀ hC₀ B
    -- The index bound `M` as a function of `Λ`: the first index with `(Λ:ℝ)^M ≥ T`.
    have hex : ∀ Λ : NNReal, ∃ M : ℕ, 1 < Λ → (T : ℝ) ≤ (Λ : ℝ) ^ M := by
      intro Λ
      by_cases h : 1 < Λ
      · exact ⟨Nat.find (exists_pow_ge T h), fun _ => Nat.find_spec (exists_pow_ge T h)⟩
      · exact ⟨0, fun h' => absurd h' h⟩
    let Mof : NNReal → ℕ := fun Λ => Nat.find (hex Λ)
    have hMof : ∀ Λ : NNReal, 1 < Λ → (T : ℝ) ≤ (Λ : ℝ) ^ (Mof Λ) :=
      fun Λ h => Nat.find_spec (hex Λ) h
    refine ⟨fun Λ => max 1 (C' Λ * (((4 * Mof Λ + 1 : ℕ)) : NNReal)), ?_⟩
    intro a Λ l₁ l₂ k₁ k₂ t F hΛ ha ha1 hlL ht
    have hMpow : (T : ℝ) ≤ (Λ : ℝ) ^ (Mof Λ) := hMof Λ hΛ
    -- `core ρ ⟹ core ρ'` because `ρ' ≤ ρ`.
    have hcm : ∀ n : ℕ, Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n →
        Work.KMTAreas.A7.core ρ' C₀ l₁ l₂ k₁ k₂ a n :=
      fun n h => lvl0CoreMono hρ'le C₀ l₁ l₂ k₁ k₂ a n h
    -- Both clips hold from the index `Mof Λ` on.
    have hcore : ∀ n : ℕ, Mof Λ ≤ n →
        Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
          Work.KMTAreas.A7.core ρ' C₀ l₁ l₂ k₁ k₂ a n := by
      intro n hn
      have hle : (T : ℝ) ≤ (a n : ℝ) :=
        le_trans hMpow (le_trans (pow_le_pow_right₀ hΛ.le hn) (lacunary_pow_le ha ha1 n))
      have hfloor : T ≤ Nat.floor (a n) := Nat.le_floor (by exact_mod_cast hle)
      have h1 : Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n :=
        hT l₁ l₂ k₁ k₂ hlL (Nat.floor (a n)) hfloor
      exact ⟨h1, hcm n h1⟩
    -- The two families agree from the index `Mof Λ` on.
    have hsupp : ∀ n : ℕ, n ∉ Finset.range (Mof Λ) →
        (fun x : ℤ => lvl0Fam ρ P C₀ a l₁ l₂ k₁ k₂ t F n x)
          = (fun x : ℤ => lvl0Fam ρ' P C₀ a l₁ l₂ k₁ k₂ t F n x) := by
      intro n hn
      have hn' : Mof Λ ≤ n := by
        by_contra hcon
        exact hn (Finset.mem_range.mpr (Nat.lt_of_not_le hcon))
      obtain ⟨h1, h2⟩ := hcore n hn'
      have hTle := Tle_zero_rho_indep ρ ρ'
        (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)
      funext x
      unfold lvl0Fam
      rw [if_pos h1, if_pos h2, hTle]
    -- The `ρ'`-family obeys the hypothesis.
    have hmajor : MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => lvl0Fam ρ' P C₀ a l₁ l₂ k₁ k₂ t F n x)) 2 MeasureTheory.Measure.count
        ≤ (C' Λ : ENNReal) * MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count :=
      hC' a Λ l₁ l₂ k₁ k₂ t F hΛ ha ha1 hlL ht
    -- Each remainder term is dominated by the `ρ'`-variational norm.
    have happrox : ∀ n ∈ Finset.range (Mof Λ),
        MeasureTheory.eLpNorm (fun x : ℤ => lvl0Fam ρ P C₀ a l₁ l₂ k₁ k₂ t F n x
            - lvl0Fam ρ' P C₀ a l₁ l₂ k₁ k₂ t F n x) 2 MeasureTheory.Measure.count
          ≤ (C' Λ : ENNReal) * MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count := by
      intro n _
      have hpt : ∀ x : ℤ, ‖lvl0Fam ρ P C₀ a l₁ l₂ k₁ k₂ t F n x
            - lvl0Fam ρ' P C₀ a l₁ l₂ k₁ k₂ t F n x‖ₑ
          ≤ ‖lvl0Fam ρ' P C₀ a l₁ l₂ k₁ k₂ t F n x‖ₑ := by
        intro x
        by_cases h : Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n
        · have h2 : Work.KMTAreas.A7.core ρ' C₀ l₁ l₂ k₁ k₂ a n := hcm n h
          have hTle := Tle_zero_rho_indep ρ ρ'
            (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)
          unfold lvl0Fam
          rw [if_pos h, if_pos h2, hTle, sub_self, enorm_zero]
          exact bot_le
        · unfold lvl0Fam
          rw [if_neg h]
          exact le_of_eq (by rw [zero_sub, enorm_neg])
      refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hpt).trans ?_
      refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (f := fun x : ℤ =>
          lvl0Fam ρ' P C₀ a l₁ l₂ k₁ k₂ t F n x) (g := fun x : ℤ =>
          variationalNorm r (fun m : ℕ => lvl0Fam ρ' P C₀ a l₁ l₂ k₁ k₂ t F m x)) ?_).trans hmajor
      intro x
      simpa only [enorm_eq_self] using
        Work.KMTAreas.A7.enorm_apply_le_variationalNorm (r := r)
          (u := fun m : ℕ => lvl0Fam ρ' P C₀ a l₁ l₂ k₁ k₂ t F m x) n
    have hsum : ∑ n ∈ Finset.range (Mof Λ),
          ((C' Λ : ENNReal) * MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count)
        ≤ (Mof Λ : ENNReal) *
            ((C' Λ : ENNReal) * MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count) := by
      refine le_of_eq ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have key := Submission.PointwiseErgodicTheorems.eLpNorm_variationalNorm_le_of_approx
      (p := 2) (r := r) (by norm_num) hr1
      (u := fun n x => lvl0Fam ρ P C₀ a l₁ l₂ k₁ k₂ t F n x)
      (w := fun n x => lvl0Fam ρ' P C₀ a l₁ l₂ k₁ k₂ t F n x)
      (s := Finset.range (Mof Λ))
      (ε := fun _ : ℕ => (C' Λ : ENNReal) * MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count)
      (M := (C' Λ : ENNReal) * MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count)
      (C := (Mof Λ : ENNReal) *
        ((C' Λ : ENNReal) * MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count))
      (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aestronglyMeasurable
      (fun n _ => (measurable_of_countable _).aestronglyMeasurable)
      hsupp happrox hsum hmajor
    refine key.trans ?_
    exact ennreal_transfer_arith (C' Λ) (Mof Λ)
      (MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count)
  exact hgen (min ρ (1 / (2 * (C₀ : ℝ)))) (min_le_left _ _)
    (hsmall (min ρ (1 / (2 * (C₀ : ℝ)))) (lt_min hρ hden) (min_le_right _ _))

end

end Work.KMTPlan.A6.LowModApproxBoundedH
