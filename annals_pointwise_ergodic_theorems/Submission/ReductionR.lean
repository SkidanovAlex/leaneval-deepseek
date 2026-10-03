import ChallengeDeps
import Mathlib.Tactic
import Submission.TelescopeR
import Submission.Reduction
import Submission.Port.Aesm

/-!
# The halved variational estimate implies the long variational estimate, for `r ≥ 1`

`Submission.Reduction` proves Krause--Mirek--Tao, Proposition 3.1 (iii), for the variational norm
of exponent `r = 3` — the exponent needed by Theorem 1.17 (i)--(iii).  This file records the
same reduction for an arbitrary exponent `r ≥ 1`, using the `r`-general pointwise telescoping of
`Submission.TelescopeR`.  Apart from the exponent, nothing changes: the constants `6` and `9` of
the reduction are independent of `r`.

This is the form needed by the deliverable: the remaining gap of the development is the paper's
estimate for the *halved* averages at the general exponent `r > 2`
(`Submission.ShiftHole.exists_varEstHalf_Cv`), and `Submission.ShiftHole.varEstZ_of_varEstHalf`
uses `varEstR_of_varEstHalfR` below to pass from it to the long variational estimate `VarEstZ`
on the integer shift model.  (The `r = 3` variant `Submission.Reduction.varEst_of_varEstHalf` is
used for the intermediate statements of Theorem 1.17 (i)--(iii).)
-/

set_option maxHeartbeats 8000000

namespace Submission

open _root_.PointwiseErgodicTheorems
set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- **The halved variational estimate for exponent `r`.**  The variational estimate for the
halved averages `Ã_N` at `Λ`-lacunary scales `N ≥ 1`. -/
def VarEstHalfR (T : 𝓧 ≃ᵐ 𝓧) (μ : Measure 𝓧) (P : ℤ[X]) (p₁ p₂ p : ℝ≥0∞) (r : ℝ≥0)
    (Cv : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ (f g : 𝓧 → ℂ) (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ) (a : ℕ → ℝ≥0) (Λ : ℝ≥0),
    1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) →
    eLpNorm (fun x => variationalNorm r (fun n => AhalfR T (a n) X P f g x)) p μ
      ≤ (Cv Λ : ℝ≥0∞) * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ

/-- **The long variational estimate for exponent `r`.** -/
def VarEstR (T : 𝓧 ≃ᵐ 𝓧) (μ : Measure 𝓧) (P : ℤ[X]) (p₁ p₂ p : ℝ≥0∞) (r : ℝ≥0)
    (Cv : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ (f g : 𝓧 → ℂ) (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ) (a : ℕ → ℝ≥0) (Λ : ℝ≥0),
    1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) →
    eLpNorm (fun x => variationalNorm r (fun n => A T (a n) X P f g x)) p μ
      ≤ (Cv Λ : ℝ≥0∞) * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ

lemma eLpNorm_halfSequence_le_gen {r : ℝ≥0} (hr : 1 ≤ r) {T : 𝓧 ≃ᵐ 𝓧} {μ : Measure 𝓧} {P : ℤ[X]} {p₁ p₂ p : ℝ≥0∞}
    {Cv : ℝ≥0 → ℝ≥0} (hT : MeasurePreserving T μ μ) (h1p : 1 ≤ p)
    (hHalf : VarEstHalfR T μ P p₁ p₂ p r Cv) {Λ : ℝ≥0} (hΛ : 1 < Λ) {a : ℕ → ℝ≥0}
    (ha : Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) {f g : 𝓧 → ℂ} (hf : MemLp f p₁ μ)
    (hg : MemLp g p₂ μ) (k : ℕ) :
    eLpNorm (fun x => variationalNorm r (fun n => AhalfR T (a n / 2 ^ k) X P f g x)) p μ
      ≤ 3 * ((Cv Λ : ℝ≥0∞) * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ) := by
  have hr0 : (0 : ℝ≥0) < r := lt_of_lt_of_le zero_lt_one hr
  set n₀ := shiftIdx Λ a hΛ ha ha1 k with hn₀
  set V : 𝓧 → ℝ≥0∞ := fun x => variationalNorm r (fun m =>
    AhalfR T (a (m + n₀) / 2 ^ k) X P f g x) with hV
  have hspec : Lacunary Λ (fun m => a (m + n₀) / 2 ^ k) ∧
      (∀ m, 1 ≤ a (m + n₀) / 2 ^ k) := by
    rw [hn₀]
    exact lacunary_shiftIdx Λ a hΛ ha ha1 k
  have hhalf : eLpNorm V p μ ≤ (Cv Λ : ℝ≥0∞) * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ :=
    hHalf f g hf hg (fun m => a (m + n₀) / 2 ^ k) Λ hΛ hspec.1 hspec.2
  have hmeas : AEStronglyMeasurable V μ :=
    (aemeasurable_variationalNorm (𝓧 := 𝓧) (μ := μ) (r := r) hr0 (fun m =>
      aemeasurable_AhalfR hT (a (m + n₀) / 2 ^ k) X P hf.aestronglyMeasurable.aemeasurable
        hg.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hV2 : AEStronglyMeasurable (fun x => V x + V x) μ := hmeas.add hmeas
  have hthree : eLpNorm (fun x => 3 * V x) p μ ≤ 3 * eLpNorm V p μ := by
    have hfun : (fun x => 3 * V x) = (fun x => V x + (V x + V x)) := by
      funext x; ring
    rw [hfun]
    calc eLpNorm (fun x => V x + (V x + V x)) p μ
        ≤ eLpNorm V p μ + eLpNorm (fun x => V x + V x) p μ := eLpNorm_add_le h1p
      _ ≤ eLpNorm V p μ + (eLpNorm V p μ + eLpNorm V p μ) :=
          add_le_add le_rfl (eLpNorm_add_le h1p)
      _ = 3 * eLpNorm V p μ := by ring
  have hprep : ∀ x, variationalNorm r (fun n => AhalfR T (a n / 2 ^ k) X P f g x) ≤ 3 * V x := by
    intro x
    have h := halfSequence_eq_prepend T Λ a hΛ ha ha1 k X P f g x
    rw [← hn₀] at h
    rw [h]
    exact variationalNorm_prependZeros_le (r := r) hr n₀
      (fun m => AhalfR T (a (m + n₀) / 2 ^ k) X P f g x)
  calc eLpNorm (fun x => variationalNorm r (fun n => AhalfR T (a n / 2 ^ k) X P f g x)) p μ
      ≤ eLpNorm (fun x => 3 * V x) p μ :=
        eLpNorm_mono_enorm (hf := (aemeasurable_variationalNorm (𝓧 := 𝓧) (μ := μ) (r := r) hr0
          (fun m => aemeasurable_AhalfR hT (a m / 2 ^ k) X P hf.aestronglyMeasurable.aemeasurable
            hg.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable) hprep
    _ ≤ 3 * eLpNorm V p μ := hthree
    _ ≤ 3 * ((Cv Λ : ℝ≥0∞) * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ) :=
        mul_le_mul_of_nonneg_left hhalf (by norm_num)


open Classical in
/-- The halved variational estimate implies the long variational estimate for the full averages.
The constant is `6 Cv Λ + 9 Cv Λ · rateConst Λ`: the first term comes from the geometric weight
`∑ 2^{-k} = 2` of the `2^{-k}` pieces, the second from the error term
`∑_n ⌊a n⌋⁻¹ (log₂ ⌊a n⌋ + 1)`. -/
theorem varEstR_of_varEstHalfR {r : ℝ≥0} (hr : 1 ≤ r) {T : 𝓧 ≃ᵐ 𝓧} {μ : Measure 𝓧} {P : ℤ[X]} {p₁ p₂ p : ℝ≥0∞}
    {Cv : ℝ≥0 → ℝ≥0} (hT : MeasurePreserving T μ μ) (h1p : 1 ≤ p) (hpT : p ≠ ⊤)
    (hHalf : VarEstHalfR T μ P p₁ p₂ p r Cv) :
    VarEstR T μ P p₁ p₂ p r (fun Λ => 6 * Cv Λ + 9 * rateConst Λ * Cv Λ) := by
  intro f g hf hg a Λ hΛ ha ha1
  have hr0 : (0 : ℝ≥0) < r := lt_of_lt_of_le zero_lt_one hr
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos h1p).ne'
  have hae : AEMeasurable f μ := hf.aestronglyMeasurable.aemeasurable
  have hbe : AEMeasurable g μ := hg.aestronglyMeasurable.aemeasurable
  set A0 : ℝ≥0∞ := (Cv Λ : ℝ≥0∞) * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ with hA0
  set FV : ℕ → 𝓧 → ℝ≥0∞ := fun k x => variationalNorm r (fun n => halfSeq T a P f g k n x) with hFV
  have hFVae : ∀ k, AEMeasurable (FV k) μ := fun k =>
    aemeasurable_variationalNorm (𝓧 := 𝓧) (μ := μ) (r := r) hr0 (fun n =>
      aemeasurable_AhalfR hT (a n / 2 ^ k) X P hae hbe)
  have hpiece : ∀ k, eLpNorm (FV k) p μ ≤ 3 * A0 := by
    intro k
    exact eLpNorm_halfSequence_le_gen hr hT h1p hHalf hΛ ha ha1 hf hg k
  set GG : ℕ → ℕ → 𝓧 → ℝ≥0∞ := fun n k x => ‖halfSeq T a P f g k n x‖ₑ with hGG
  have hGGle : ∀ n k x, GG n k x ≤ FV k x := fun n k x =>
    le_variationalNorm r (fun m => halfSeq T a P f g k m x) n
  have hGGae : ∀ n k, AEMeasurable (GG n k) μ := fun n k =>
    (aemeasurable_AhalfR hT (a n / 2 ^ k) X P hae hbe).enorm
  set U : 𝓧 → ℝ≥0∞ := fun x => ∑' k, ‖halfScalar k‖ₑ * FV k x with hU
  set E : 𝓧 → ℝ≥0∞ := fun x => ∑' n, (Nat.floor (a n) : ℝ≥0∞)⁻¹ * (∑' k, GG n k x) with hE
  have hpt : ∀ x, variationalNorm r (fun n => A T (a n) X P f g x) ≤ U x + 3 * E x :=
    fun x => variationalNorm_A_le_halfSeq_gen r hr T P f g a ha1 x
  have hUae : AEMeasurable U μ := by
    rw [hU]
    exact AEMeasurable.tsum (fun k => (hFVae k).const_mul _)
  have hEae : AEMeasurable E μ := by
    rw [hE]
    exact AEMeasurable.tsum (fun n => AEMeasurable.const_mul
      (AEMeasurable.tsum (fun k => hGGae n k)) _)
  have hU_le : eLpNorm U p μ ≤ ∑' k, ‖halfScalar k‖ₑ * eLpNorm (FV k) p μ := by
    rw [hU]
    refine (eLpNorm_tsum_le_tsum_eLpNorm (α := 𝓧) (ι := ℕ) (μ := μ) (p := p) h1p
      (f := fun k x => ‖halfScalar k‖ₑ * FV k x)
      (fun k => (hFVae k).const_mul _)).trans ?_
    refine ENNReal.tsum_le_tsum (fun k => le_of_eq ?_)
    exact Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (α := 𝓧) (μ := μ)
      (enorm_halfScalar_ne_top k) hp0 hpT
  have hU2 : ∑' k, ‖halfScalar k‖ₑ * eLpNorm (FV k) p μ ≤ 6 * A0 := by
    calc ∑' k, ‖halfScalar k‖ₑ * eLpNorm (FV k) p μ
        ≤ ∑' k, ‖halfScalar k‖ₑ * (3 * A0) :=
          ENNReal.tsum_le_tsum (fun k =>
            mul_le_mul_of_nonneg_left (hpiece k) (zero_le : (0:ℝ≥0∞) ≤ _))
      _ = (∑' k, ‖halfScalar k‖ₑ) * (3 * A0) := ENNReal.tsum_mul_right
      _ ≤ 2 * (3 * A0) :=
          mul_le_mul_of_nonneg_right tsum_enorm_halfScalar_le_two (zero_le : (0:ℝ≥0∞) ≤ _)
      _ = 6 * A0 := by ring
  have hE_le : eLpNorm E p μ ≤ ∑' n, (Nat.floor (a n) : ℝ≥0∞)⁻¹ *
      eLpNorm (fun x => ∑' k, GG n k x) p μ := by
    rw [hE]
    refine (eLpNorm_tsum_le_tsum_eLpNorm (α := 𝓧) (ι := ℕ) (μ := μ) (p := p) h1p
      (f := fun n x => (Nat.floor (a n) : ℝ≥0∞)⁻¹ * (∑' k, GG n k x))
      (fun n => AEMeasurable.const_mul (AEMeasurable.tsum (fun k => hGGae n k)) _)).trans ?_
    refine ENNReal.tsum_le_tsum (fun n => le_of_eq ?_)
    refine Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (α := 𝓧) (μ := μ) ?_ hp0 hpT
    rw [ENNReal.inv_ne_top]
    exact_mod_cast (Nat.floor_pos.mpr (ha1 n)).ne'
  have hE_fin : ∀ n, eLpNorm (fun x => ∑' k, GG n k x) p μ
      ≤ 3 * A0 * ((Nat.log2 (Nat.floor (a n)) + 1 : ℕ) : ℝ≥0∞) := by
    intro n
    set N : ℕ := Nat.log2 (Nat.floor (a n)) + 1 with hN
    have hlog_lt : ∀ k ≥ N, Nat.floor (a n) < 2 ^ k := by
      intro k hk
      have h1 : Nat.floor (a n) < 2 ^ (Nat.log2 (Nat.floor (a n)) + 1) := by
        rw [Nat.log2_eq_log_two]
        simpa [Nat.succ_eq_add_one] using
          Nat.lt_pow_succ_log_self (by norm_num) (Nat.floor (a n))
      exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by rw [← hN]; exact hk))
    have hzero : ∀ k ≥ N, ∀ x, GG n k x = 0 := by
      intro k hk x
      rw [hGG]
      simp only
      rw [show halfSeq T a P f g k n x = 0 from
        AhalfR_eq_zero_of_two_pow_gt T (hlog_lt k hk) X P f g x, enorm_zero]
    have htsum : (fun x => ∑' k, GG n k x)
        = fun x => ∑ k ∈ Finset.range N, GG n k x := by
      funext x
      exact tsum_eq_sum (fun k hk => hzero k (by
        simp only [Finset.mem_range, not_lt] at hk; omega) x)
    rw [htsum]
    have hfin : (fun x => ∑ k ∈ Finset.range N, GG n k x)
        = fun x => ∑ i : Fin N, GG n (i : ℕ) x := by
      funext x
      rw [Fin.sum_univ_eq_sum_range (α := ℝ≥0∞) (fun i => GG n i x) N]
    rw [hfin]
    calc eLpNorm (fun x => ∑ i : Fin N, GG n (i : ℕ) x) p μ
        = eLpNorm (fun x => ∑' i : Fin N, GG n (i : ℕ) x) p μ := by
          congr 1
          funext x
          exact (tsum_fintype (fun i : Fin N => GG n (i : ℕ) x)).symm
      _ ≤ ∑' i : Fin N, eLpNorm (GG n (i : ℕ)) p μ :=
          eLpNorm_tsum_le_tsum_eLpNorm (α := 𝓧) (μ := μ) (p := p) h1p
            (fun i => hGGae n (i : ℕ))
      _ ≤ ∑' _i : Fin N, (3 * A0) := by
          refine ENNReal.tsum_le_tsum (fun i => ?_)
          exact le_trans (eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => hGGle n (i : ℕ) x)) (hpiece (i : ℕ))
      _ = 3 * A0 * (N : ℝ≥0∞) := by
          rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hE2 : ∑' n, (Nat.floor (a n) : ℝ≥0∞)⁻¹ *
      eLpNorm (fun x => ∑' k, GG n k x) p μ ≤ 3 * A0 * (rateConst Λ : ℝ≥0∞) := by
    calc ∑' n, (Nat.floor (a n) : ℝ≥0∞)⁻¹ * eLpNorm (fun x => ∑' k, GG n k x) p μ
        ≤ ∑' n, (Nat.floor (a n) : ℝ≥0∞)⁻¹ *
            (3 * A0 * ((Nat.log2 (Nat.floor (a n)) + 1 : ℕ) : ℝ≥0∞)) :=
          ENNReal.tsum_le_tsum (fun n =>
            mul_le_mul_of_nonneg_left (hE_fin n) (zero_le : (0:ℝ≥0∞) ≤ _))
      _ = 3 * A0 * ∑' n, (Nat.floor (a n) : ℝ≥0∞)⁻¹ *
            ((Nat.log2 (Nat.floor (a n)) + 1 : ℕ) : ℝ≥0∞) := by
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr (fun n => by ac_rfl)
      _ ≤ 3 * A0 * (rateConst Λ : ℝ≥0∞) := by
          refine mul_le_mul_of_nonneg_left ?_ (zero_le : (0:ℝ≥0∞) ≤ _)
          rw [show (∑' n, (Nat.floor (a n) : ℝ≥0∞)⁻¹ *
                ((Nat.log2 (Nat.floor (a n)) + 1 : ℕ) : ℝ≥0∞))
              = ∑' n, ((Nat.log2 (Nat.floor (a n)) + 1 : ℕ) : ℝ≥0∞) *
                (Nat.floor (a n) : ℝ≥0∞)⁻¹ from tsum_congr (fun n => by ac_rfl)]
          exact rateConst_spec hΛ (x := a) (ha1 0) (lacunary_mul_le ha ha1)
  calc eLpNorm (fun x => variationalNorm r (fun n => A T (a n) X P f g x)) p μ
      ≤ eLpNorm (fun x => U x + 3 * E x) p μ :=
        eLpNorm_mono_enorm (hf := (aemeasurable_variationalNorm (𝓧 := 𝓧) (μ := μ) (r := r)
          (lt_of_lt_of_le zero_lt_one hr) (fun m => aemeasurable_A hT (a m) X P
            hf.aestronglyMeasurable.aemeasurable hg.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable) hpt
    _ ≤ eLpNorm U p μ + eLpNorm (fun x => 3 * E x) p μ :=
        eLpNorm_add_le h1p
    _ = eLpNorm U p μ + 3 * eLpNorm E p μ := by
        rw [Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (α := 𝓧) (μ := μ)
          (by norm_num : (3 : ℝ≥0∞) ≠ ⊤) hp0 hpT]
    _ ≤ (6 * A0) + 3 * (3 * A0 * (rateConst Λ : ℝ≥0∞)) :=
        add_le_add (hU_le.trans hU2) (mul_le_mul_of_nonneg_left (hE_le.trans hE2) (by norm_num))
    _ = ((6 * Cv Λ + 9 * rateConst Λ * Cv Λ : ℝ≥0) : ℝ≥0∞) * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ := by
        rw [hA0]
        push_cast
        ring

end PointwiseErgodicTheorems
end Submission
