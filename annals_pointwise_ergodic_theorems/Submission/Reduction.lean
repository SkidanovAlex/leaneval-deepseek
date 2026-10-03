import ChallengeDeps
import Mathlib.Tactic
import Submission.Telescope
import Submission.AEMeasurable
import Submission.LpMinkowski
import Submission.LogSum
import Submission.Commons.Analysis.Real.unbounded_of_lacunary
import Submission.Port.Aesm

/-!
# The halved variational estimate implies the full variational estimate

(Krause--Mirek--Tao, Proposition 3.1 (iii).)  We show that a variational estimate for the halved
averages `Ã_N` at `Λ`-lacunary integer scales `N ≥ 1` implies the long variational estimate for
the full averages.  The dyadic telescoping identity of `Submission.Telescope` reduces the full
average at scale `a n` to the halved averages at the rescaled scales `a n / 2^k`; the rescaled
families are still `Λ`-lacunary, and the truncation at small scales is handled by
`variationalNorm_prependZeros_le`.
-/

set_option maxHeartbeats 4000000

namespace Submission

open _root_.PointwiseErgodicTheorems
set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The `Λ`-lacunarity hypothesis in additive form. -/
lemma lacunary_mul_le {Λ : ℝ≥0} {a : ℕ → ℝ≥0} (ha : Lacunary Λ a) (ha' : ∀ n, 1 ≤ a n)
    (n : ℕ) : Λ * a n ≤ a (n + 1) := by
  have hpos : 0 < a n := lt_of_lt_of_le one_pos (ha' n)
  exact le_of_lt ((lt_div_iff₀ hpos).mp (ha n))

/-- A `Λ`-lacunary sequence of scales with `Λ > 1` and `a n ≥ 1` is unbounded, so every dyadic
scale is eventually dominated by `⌊a n⌋`. -/
lemma exists_floor_ge {Λ : ℝ≥0} {a : ℕ → ℝ≥0} (hΛ : 1 < Λ) (ha : Lacunary Λ a)
    (ha' : ∀ n, 1 ≤ a n) (K : ℕ) : ∃ n, K ≤ Nat.floor (a n) := by
  obtain ⟨n, hn⟩ := Commons.Analysis.Real.unbounded_of_lacunary hΛ
    (lt_of_lt_of_le one_pos (ha' 0)) (lacunary_mul_le ha ha') (K : ℝ≥0)
  refine ⟨n, ?_⟩
  have h : ((K : ℕ) : ℝ≥0) ≤ a n := hn n le_rfl
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · exact Nat.zero_le _
  · exact (Nat.le_floor_iff' hK.ne').mpr h

/-- The first index at which the `Λ`-lacunary sequence `a` reaches the dyadic scale `2^k`. -/
noncomputable def shiftIdx (Λ : ℝ≥0) (a : ℕ → ℝ≥0) (hΛ : 1 < Λ) (ha : Lacunary Λ a)
    (ha' : ∀ n, 1 ≤ a n) (k : ℕ) : ℕ :=
  Nat.find (exists_floor_ge hΛ ha ha' (2 ^ k))

/-- The rescaled sequence `m ↦ a (m + n₀) / 2^k` is again `Λ`-lacunary and takes values at least
`1`. -/
lemma lacunary_shiftIdx (Λ : ℝ≥0) (a : ℕ → ℝ≥0) (hΛ : 1 < Λ) (ha : Lacunary Λ a)
    (ha' : ∀ n, 1 ≤ a n) (k : ℕ) :
    Lacunary Λ (fun m => a (m + shiftIdx Λ a hΛ ha ha' k) / 2 ^ k) ∧
      (∀ m, 1 ≤ a (m + shiftIdx Λ a hΛ ha ha' k) / 2 ^ k) := by
  have hmono : Monotone a := Commons.Analysis.Real.monotone_of_lacunary hΛ (lacunary_mul_le ha ha')
  have hspec : ((2 : ℝ≥0) ^ k) ≤ (Nat.floor (a (shiftIdx Λ a hΛ ha ha' k)) : ℝ≥0) := by
    have h := Nat.find_spec (exists_floor_ge hΛ ha ha' (2 ^ k))
    rw [show ((2 : ℝ≥0) ^ k) = ((2 ^ k : ℕ) : ℝ≥0) from by simp [Nat.cast_pow]]
    exact Nat.cast_le.mpr h
  constructor
  · intro m
    have hden : ((2 : ℝ≥0) ^ k) ≠ 0 := by positivity
    rw [div_div_div_cancel_right₀ hden]
    have h := ha (m + shiftIdx Λ a hΛ ha ha' k)
    have heq : m + 1 + shiftIdx Λ a hΛ ha ha' k = (m + shiftIdx Λ a hΛ ha ha' k) + 1 := by omega
    rw [heq]
    exact h
  · intro m
    rw [le_div_iff₀ (by positivity : (0:ℝ≥0) < 2 ^ k), one_mul]
    exact le_trans (le_trans hspec (Nat.floor_le (show (0:ℝ≥0) ≤ a _ by positivity)))
      (hmono (show shiftIdx Λ a hΛ ha ha' k ≤ m + shiftIdx Λ a hΛ ha ha' k by omega))

/-- The halved averages at the rescaled scale, as a sequence shifted to the right. -/
lemma halfSequence_eq_prepend (T : 𝓧 ≃ᵐ 𝓧) (Λ : ℝ≥0) (a : ℕ → ℝ≥0) (hΛ : 1 < Λ)
    (ha : Lacunary Λ a) (ha' : ∀ n, 1 ≤ a n) (k : ℕ) (P₁ P₂ : ℤ[X]) (f g : 𝓧 → ℂ) (x : 𝓧) :
    (fun n => AhalfR T (a n / 2 ^ k) P₁ P₂ f g x)
      = fun n => if n < shiftIdx Λ a hΛ ha ha' k then 0
          else AhalfR T (a (n - shiftIdx Λ a hΛ ha ha' k + shiftIdx Λ a hΛ ha ha' k) / 2 ^ k)
            P₁ P₂ f g x := by
  funext n
  by_cases hn : n < shiftIdx Λ a hΛ ha ha' k
  · rw [if_pos hn]
    have hlt : Nat.floor (a n) < 2 ^ k := by
      by_contra hge
      push_neg at hge
      exact absurd (Nat.find_min' (exists_floor_ge hΛ ha ha' (2 ^ k)) hge) (not_le.mpr hn)
    exact AhalfR_eq_zero_of_two_pow_gt T hlt P₁ P₂ f g x
  · rw [if_neg hn, Nat.sub_add_cancel (Nat.le_of_not_lt hn)]

/-- The constant in the growth estimate `∑ ⌊a n⌋⁻¹ (log₂ ⌊a n⌋ + 1) ≤ rateConst Λ`. -/
noncomputable def rateConst (Λ : ℝ≥0) : ℝ≥0 :=
  if h : 1 < Λ then
    Classical.choose (LogSum.tsum_ennreal_log2_floor_div_le_of_lacunary Λ h)
  else 1

/-- The defining property of `rateConst`. -/
lemma rateConst_spec {Λ : ℝ≥0} (hΛ : 1 < Λ) {x : ℕ → ℝ≥0} (hx : 1 ≤ x 0)
    (hxl : ∀ n, Λ * x n ≤ x (n + 1)) :
    ∑' n, ((((Nat.log2 (Nat.floor (x n)) + 1 : ℕ)) : ℝ≥0∞) * ((Nat.floor (x n) : ℝ≥0∞))⁻¹)
      ≤ (rateConst Λ : ℝ≥0∞) := by
  rw [rateConst, dif_pos hΛ]
  exact Classical.choose_spec
    (LogSum.tsum_ennreal_log2_floor_div_le_of_lacunary Λ hΛ) x hx hxl

/-- **The halved variational estimate.**  The variational estimate for the halved averages `Ã_N`
at `Λ`-lacunary scales `N ≥ 1`. -/
def VarEstHalf (T : 𝓧 ≃ᵐ 𝓧) (μ : Measure 𝓧) (P : ℤ[X]) (p₁ p₂ p : ℝ≥0∞)
    (Cv : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ (f g : 𝓧 → ℂ) (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ) (a : ℕ → ℝ≥0) (Λ : ℝ≥0),
    1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) →
    eLpNorm (fun x => variationalNorm 3 (fun n => AhalfR T (a n) X P f g x)) p μ
      ≤ (Cv Λ : ℝ≥0∞) * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ

/-- The `Lᵖ` seminorm of the variational norm of the halved averages at a rescaled dyadic scale
is controlled by the halved variational estimate. -/
lemma eLpNorm_halfSequence_le {T : 𝓧 ≃ᵐ 𝓧} {μ : Measure 𝓧} {P : ℤ[X]} {p₁ p₂ p : ℝ≥0∞}
    {Cv : ℝ≥0 → ℝ≥0} (hT : MeasurePreserving T μ μ) (h1p : 1 ≤ p)
    (hHalf : VarEstHalf T μ P p₁ p₂ p Cv) {Λ : ℝ≥0} (hΛ : 1 < Λ) {a : ℕ → ℝ≥0}
    (ha : Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) {f g : 𝓧 → ℂ} (hf : MemLp f p₁ μ)
    (hg : MemLp g p₂ μ) (k : ℕ) :
    eLpNorm (fun x => variationalNorm 3 (fun n => AhalfR T (a n / 2 ^ k) X P f g x)) p μ
      ≤ 3 * ((Cv Λ : ℝ≥0∞) * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ) := by
  set n₀ := shiftIdx Λ a hΛ ha ha1 k with hn₀
  set V : 𝓧 → ℝ≥0∞ := fun x => variationalNorm 3 (fun m =>
    AhalfR T (a (m + n₀) / 2 ^ k) X P f g x) with hV
  have hspec : Lacunary Λ (fun m => a (m + n₀) / 2 ^ k) ∧
      (∀ m, 1 ≤ a (m + n₀) / 2 ^ k) := by
    rw [hn₀]
    exact lacunary_shiftIdx Λ a hΛ ha ha1 k
  have hhalf : eLpNorm V p μ ≤ (Cv Λ : ℝ≥0∞) * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ :=
    hHalf f g hf hg (fun m => a (m + n₀) / 2 ^ k) Λ hΛ hspec.1 hspec.2
  have hmeas : AEStronglyMeasurable V μ :=
    (aemeasurable_variationalNorm (by norm_num) (fun m =>
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
  have hprep : ∀ x, variationalNorm 3 (fun n => AhalfR T (a n / 2 ^ k) X P f g x) ≤ 3 * V x := by
    intro x
    have h := halfSequence_eq_prepend T Λ a hΛ ha ha1 k X P f g x
    rw [← hn₀] at h
    rw [h]
    exact variationalNorm_prependZeros_le (r := 3) (by norm_num) n₀
      (fun m => AhalfR T (a (m + n₀) / 2 ^ k) X P f g x)
  calc eLpNorm (fun x => variationalNorm 3 (fun n => AhalfR T (a n / 2 ^ k) X P f g x)) p μ
      ≤ eLpNorm (fun x => 3 * V x) p μ :=
        eLpNorm_mono_enorm (hf := (aemeasurable_variationalNorm (by norm_num) (fun m =>
          aemeasurable_AhalfR hT (a m / 2 ^ k) X P hf.aestronglyMeasurable.aemeasurable
            hg.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable) hprep
    _ ≤ 3 * eLpNorm V p μ := hthree
    _ ≤ 3 * ((Cv Λ : ℝ≥0∞) * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ) :=
        mul_le_mul_of_nonneg_left hhalf (by norm_num)

open Classical in
/-- The halved variational estimate implies the long variational estimate for the full averages.
The constant is `6 Cv Λ + 9 Cv Λ · rateConst Λ`: the first term comes from the geometric weight
`∑ 2^{-k} = 2` of the `2^{-k}` pieces, the second from the error term
`∑_n ⌊a n⌋⁻¹ (log₂ ⌊a n⌋ + 1)`. -/
theorem varEst_of_varEstHalf {T : 𝓧 ≃ᵐ 𝓧} {μ : Measure 𝓧} {P : ℤ[X]} {p₁ p₂ p : ℝ≥0∞}
    {Cv : ℝ≥0 → ℝ≥0} (hT : MeasurePreserving T μ μ) (h1p : 1 ≤ p) (hpT : p ≠ ⊤)
    (hHalf : VarEstHalf T μ P p₁ p₂ p Cv) :
    VarEst T μ P p₁ p₂ p (fun Λ => 6 * Cv Λ + 9 * rateConst Λ * Cv Λ) := by
  intro f g hf hg a Λ hΛ ha ha1
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos h1p).ne'
  have hae : AEMeasurable f μ := hf.aestronglyMeasurable.aemeasurable
  have hbe : AEMeasurable g μ := hg.aestronglyMeasurable.aemeasurable
  set A0 : ℝ≥0∞ := (Cv Λ : ℝ≥0∞) * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ with hA0
  set FV : ℕ → 𝓧 → ℝ≥0∞ := fun k x => variationalNorm 3 (fun n => halfSeq T a P f g k n x) with hFV
  have hFVae : ∀ k, AEMeasurable (FV k) μ := fun k =>
    aemeasurable_variationalNorm (by norm_num) (fun n =>
      aemeasurable_AhalfR hT (a n / 2 ^ k) X P hae hbe)
  have hpiece : ∀ k, eLpNorm (FV k) p μ ≤ 3 * A0 := by
    intro k
    exact eLpNorm_halfSequence_le hT h1p hHalf hΛ ha ha1 hf hg k
  set GG : ℕ → ℕ → 𝓧 → ℝ≥0∞ := fun n k x => ‖halfSeq T a P f g k n x‖ₑ with hGG
  have hGGle : ∀ n k x, GG n k x ≤ FV k x := fun n k x =>
    le_variationalNorm 3 (fun m => halfSeq T a P f g k m x) n
  have hGGae : ∀ n k, AEMeasurable (GG n k) μ := fun n k =>
    (aemeasurable_AhalfR hT (a n / 2 ^ k) X P hae hbe).enorm
  set U : 𝓧 → ℝ≥0∞ := fun x => ∑' k, ‖halfScalar k‖ₑ * FV k x with hU
  set E : 𝓧 → ℝ≥0∞ := fun x => ∑' n, (Nat.floor (a n) : ℝ≥0∞)⁻¹ * (∑' k, GG n k x) with hE
  have hpt : ∀ x, variationalNorm 3 (fun n => A T (a n) X P f g x) ≤ U x + 3 * E x :=
    fun x => variationalNorm_A_le_halfSeq T P f g a ha1 x
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
  calc eLpNorm (fun x => variationalNorm 3 (fun n => A T (a n) X P f g x)) p μ
      ≤ eLpNorm (fun x => U x + 3 * E x) p μ :=
        eLpNorm_mono_enorm (hf := (aemeasurable_variationalNorm (by norm_num) (fun m =>
          aemeasurable_A hT (a m) X P hf.aestronglyMeasurable.aemeasurable
            hg.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable) hpt
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

/-- The mean ergodic theorem (part (i) of Theorem 1.17) from the halved variational estimate,
using the dyadic telescoping reduction of `varEst_of_varEstHalf`. -/
theorem exists_tendsto_of_varEstHalf {T : 𝓧 ≃ᵐ 𝓧} {μ : Measure 𝓧} {P : ℤ[X]}
    {p₁ p₂ p : ℝ≥0∞} {Cv : ℝ≥0 → ℝ≥0} (hT : MeasurePreserving T μ μ)
    (hHalf : VarEstHalf T μ P p₁ p₂ p Cv)
    (hp0 : p ≠ 0) (hpT : p ≠ ⊤) (hp1 : 1 ≤ p) (hp₁ne : p₁ ≠ ⊤) (hp₂ne : p₂ ≠ ⊤)
    {f g : 𝓧 → ℂ} (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ) :
    ∃ h : 𝓧 → ℂ, MemLp h p μ
      ∧ (∀ᵐ x ∂μ, Tendsto (fun N : ℝ≥0 => A T N X P f g x) atTop (𝓝 (h x)))
      ∧ Tendsto (fun N : ℝ≥0 => eLpNorm (A T N X P f g - h) p μ) atTop (𝓝 0) :=
  exists_tendsto_eLpNorm_of_varEst hT (varEst_of_varEstHalf hT hp1 hpT hHalf)
    hp0 hpT hp1 hp₁ne hp₂ne hf hg

/-- The maximal estimate (part (iii) of Theorem 1.17) from the halved variational estimate. -/
theorem eLpNorm_maximal_le_of_varEstHalf {T : 𝓧 ≃ᵐ 𝓧} {μ : Measure 𝓧} {P : ℤ[X]}
    {p₁ p₂ p : ℝ≥0∞} {Cv : ℝ≥0 → ℝ≥0} (hT : MeasurePreserving T μ μ)
    (hHalf : VarEstHalf T μ P p₁ p₂ p Cv) (hp0 : p ≠ 0) (hpT : p ≠ ⊤) (hp1 : 1 ≤ p)
    {f g : 𝓧 → ℂ} (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ) :
    eLpNorm (fun x => ⨆ (N : ℕ+), ‖A T N X P f g x‖ₑ) p μ
      ≤ (2 * (6 * Cv (3 / 2) + 9 * rateConst (3 / 2) * Cv (3 / 2)) : ℝ≥0∞)
        * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ :=
  eLpNorm_maximal_le_of_varEst (varEst_of_varEstHalf hT hp1 hpT hHalf) hp0 hpT hf hg
    (AEMeasurable.iSup fun N : ℕ+ => (aemeasurable_A_of_measurePreserving T hT N X P
      hf.aemeasurable hg.aemeasurable).enorm).aestronglyMeasurable

end PointwiseErgodicTheorems
end Submission
