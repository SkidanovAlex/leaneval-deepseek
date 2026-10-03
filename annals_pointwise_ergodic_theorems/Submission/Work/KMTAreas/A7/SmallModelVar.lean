import Mathlib
import Submission.Work.KMTAreas.A7.smallBtwist_bilinear_of_bounded
import Submission.Work.KMTAreas.A7.variationalNorm_intervalIntegral_eLpNorm_le
import Submission.Work.KMTAreas.A7.smallCond_false_of_truncIndex_le
import Submission.Work.KMTAreas.A7.lossWeight_truncIndex_absorption
import Submission.Work.KMTPlan.A6.variationalNorm_le_VrFull
import Submission.Work.Analysis.Variation.rmVarBound_uniform_ge_one
import Submission.Work.KMTAreas.A7.SmallModelSingleScaleFibre
import Submission.Work.KMTAreas.A7.measurable_smallBtwist_slice
import Submission.Work.KMTAreas.A7.eLpNorm_smallModelTuple_eq_zero
import Submission.Work.KMTAreas.A7.Tm_randSymb_smallSymb
import Submission.Port.Aesm

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract Work.Analysis.EndVar

set_option maxHeartbeats 4000000

noncomputable section

open Work.Analysis.IonescuWainger

/-! ## The submodule of bounded sequences

The Rademacher--Menshov reduction is applied to the twisted bilinear multiplier `smallBtwist`,
which is only *conditionally* bilinear (the iterated series is defined with the junk-zero
convention); the bilinearity that the R-M inequality needs is available on bounded inputs
(`Work.KMTAreas.A7.smallBtwist_bilinear_of_bounded`).  We therefore run the R-M machinery in the
submodule of *bounded* sequences, which is what the abstract `V`, `W` of
`rademacher_menshov_bilinear_full` are for. -/

/-- The submodule of bounded complex sequences on `ℤ`. -/
def BddSeq : Submodule ℂ (ℤ → ℂ) where
  carrier := {u | ∃ C : ℝ, ∀ y : ℤ, ‖u y‖ ≤ C}
  zero_mem' := ⟨0, fun y => by simp⟩
  add_mem' := by
    rintro u v ⟨Cu, hu⟩ ⟨Cv, hv⟩
    exact ⟨Cu + Cv, fun y => by
      rw [Pi.add_apply]
      exact (norm_add_le _ _).trans (add_le_add (hu y) (hv y))⟩
  smul_mem' := by
    rintro c u ⟨Cu, hu⟩
    exact ⟨‖c‖ * Cu, fun y => by
      rw [Pi.smul_apply, smul_eq_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (hu y) (norm_nonneg _)⟩

/-! ## Summability of the coefficient kernels of the two `m_*` symbols -/

lemma summable_cw_mStarF_rho (ρ : ℝ) (L : ℕ) :
    Summable (fun j : ℤ => ‖cw (mStarF L) j‖) := by
  obtain ⟨C, hC, hdec⟩ := cw_etaCut_decay (-(2 * (L : ℤ)))
  have hmaj : Summable (fun j : ℤ => C / (1 + |(j : ℝ)|) ^ 2) := by
    have h := summable_one_div_sq_int.mul_left C
    have heq : (fun j : ℤ => C / (1 + |(j : ℝ)|) ^ 2)
        = fun j : ℤ => C * (1 / (1 + |(j : ℝ)|) ^ 2) := by
      funext j; rw [div_eq_mul_inv, one_div]
    rw [heq]; exact h
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hmaj
  simpa only [mStarF] using hdec j

lemma summable_cw_mStargF_rho (P : ℤ[X]) (u : ℕ) :
    Summable (fun j : ℤ => ‖cw (mStargF P.natDegree u) j‖) := by
  obtain ⟨C, hC, hdec⟩ := cw_etaCut_decay (-(((P.natDegree : ℤ)) * 2 * (u : ℤ)))
  have hmaj : Summable (fun j : ℤ => C / (1 + |(j : ℝ)|) ^ 2) := by
    have h := summable_one_div_sq_int.mul_left C
    have heq : (fun j : ℤ => C / (1 + |(j : ℝ)|) ^ 2)
        = fun j : ℤ => C * (1 / (1 + |(j : ℝ)|) ^ 2) := by
      funext j; rw [div_eq_mul_inv, one_div]
    rw [heq]; exact h
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hmaj
  simpa only [mStargF] using hdec j

/-! ## Gating in the symbol of `Tm` -/

/-- Gating a symbol by a proposition: `Tm` is linear in its symbol (`Tm_const_mul`), so gating the
symbol gates the output. -/
lemma Tm_gate (ρ : ℝ) (l : ℕ) (c : Prop) [Decidable c] (φ : ℝ → ℂ) (f : ℤ → ℂ) :
    Tm ρ l (fun ξ => if c then φ ξ else 0) f = fun y => if c then Tm ρ l φ f y else 0 := by
  have h1 : (fun ξ : ℝ => if c then φ ξ else 0)
      = fun ξ : ℝ => ((if c then (1 : ℂ) else 0)) * φ ξ := by
    funext ξ; by_cases h : c <;> simp [h]
  rw [h1, Tm_const_mul]
  funext y
  by_cases h : c <;> simp [h]

/-! ## Gating in the arguments of `smallBtwist` -/

/-- Gating both arguments of `smallBtwist` by the same proposition, for bounded inputs (the
homogeneity of `smallBtwist`, `Work.KMTAreas.A7.smallBtwist_bilinear_of_bounded`). -/
lemma smallBtwist_gate (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ L : ℕ) (c : Prop) [Decidable c]
    (u v : ℤ → ℂ) {Cu Cv : ℝ} (hu : ∀ y : ℤ, ‖u y‖ ≤ Cu) (hv : ∀ y : ℤ, ‖v y‖ ≤ Cv) :
    smallBtwist ρ P l₁ l₂ (mStarF L) (mStargF P.natDegree L)
        (fun y => if c then u y else 0) (fun y => if c then v y else 0)
      = fun x => if c then smallBtwist ρ P l₁ l₂ (mStarF L) (mStargF P.natDegree L) u v x
        else 0 := by
  set c' : ℂ := if c then (1 : ℂ) else 0 with hc'
  have hbdd : ∀ y : ℤ, ‖(c' • v) y‖ ≤ ‖c'‖ * Cv := fun y => by
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hv y) (norm_nonneg _)
  have hb₁ := smallBtwist_bilinear_of_bounded ρ P l₁ l₂ (mStarF L) (mStargF P.natDegree L)
    (summable_cw_mStarF_rho ρ L) (summable_cw_mStargF_rho P L) u 0 (c' • v) 0 Cu 0 (‖c'‖ * Cv) 0
    hu (by intro y; simp) hbdd (by intro y; simp)
  have hb₂ := smallBtwist_bilinear_of_bounded ρ P l₁ l₂ (mStarF L) (mStargF P.natDegree L)
    (summable_cw_mStarF_rho ρ L) (summable_cw_mStargF_rho P L) u 0 v 0 Cu 0 Cv 0
    hu (by intro y; simp) hv (by intro y; simp)
  have h1 : (fun y : ℤ => if c then u y else 0) = c' • u := by
    funext y; rw [Pi.smul_apply, smul_eq_mul, hc']; by_cases h : c <;> simp [h]
  have h2 : (fun y : ℤ => if c then v y else 0) = c' • v := by
    funext y; rw [Pi.smul_apply, smul_eq_mul, hc']; by_cases h : c <;> simp [h]
  rw [h1, h2, hb₁.2.2.1 c', hb₂.2.2.2.1 c']
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, hc']
  by_cases h : c <;> simp [h]

/-- `smallBtwist` vanishes when an argument vanishes (bounded inputs). -/
lemma smallBtwist_zero (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ L : ℕ) (u : ℤ → ℂ) {Cu : ℝ}
    (hu : ∀ y : ℤ, ‖u y‖ ≤ Cu) :
    smallBtwist ρ P l₁ l₂ (mStarF L) (mStargF P.natDegree L) 0 u = 0
      ∧ smallBtwist ρ P l₁ l₂ (mStarF L) (mStargF P.natDegree L) u 0 = 0 := by
  have hb := smallBtwist_bilinear_of_bounded ρ P l₁ l₂ (mStarF L) (mStargF P.natDegree L)
    (summable_cw_mStarF_rho ρ L) (summable_cw_mStargF_rho P L)
    u 0 u 0 Cu 0 Cu 0 hu (by intro y; simp) hu (by intro y; simp)
  exact ⟨hb.2.2.2.2.1, hb.2.2.2.2.2⟩

/-! ## The model tuple as the time average of the integrand -/

lemma smallModelTuple_eq_integral (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ) (n : ℕ) (x : ℤ) :
    smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x =
      ∫ t in ((1 : ℝ) / 2)..1, modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g n x := by
  rw [smallModelTuple_apply]
  by_cases h : smallCond ρ C₀ a l₁ l₂ k₁ k₂ n
  · simp only [h, if_true, modelInt]
    exact (intervalIntegral.integral_congr (fun t _ => by simp [h])).symm
  · simp only [h, if_false, modelInt]
    simp [h]

/-! ## The family vanishes past the truncation index -/

lemma modelInt_eq_zero_of_not_smallCond (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f g : ℤ → ℂ) {n : ℕ}
    (h : ¬ smallCond ρ C₀ a l₁ l₂ k₁ k₂ n) : modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g n = 0 := by
  funext x
  simp [modelInt, h]

/-! ## The `t`-Minkowski inequality, with the measurability hypothesis in slice form -/

/-- Minkowski's integral inequality for the variational norm of a time average, with the
measurability assumption in the (weaker, easier to establish) *slice* form: each `t ↦ X t n x`
is almost everywhere measurable. -/
theorem variationalNorm_intervalIntegral_eLpNorm_le' (r : NNReal) (hr : 1 ≤ r) (q : ENNReal)
    (hq : 1 ≤ q) (X : ℝ → ℕ → ℤ → ℂ) (C : ENNReal)
    (hX : ∀ n : ℕ, ∀ x : ℤ, AEMeasurable (fun t : ℝ => X t n x) volume)
    (h : ∀ t ∈ Set.Icc ((1 : ℝ) / 2) 1, MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => X t n x))
        q MeasureTheory.Measure.count ≤ C) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∫ t in ((1 : ℝ) / 2)..1, X t n x)) q MeasureTheory.Measure.count ≤ C := by
  classical
  rcases eq_or_ne C ⊤ with hC | hCtop
  · rw [hC]; exact le_top
  have hslice : ∀ t ∈ Set.Icc ((1 : ℝ) / 2) 1, ∀ x : ℤ,
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => X t n x) ≤ C :=
    fun t ht x => le_of_eLpNorm_count_le hq (h t ht) x
  have hbd : ∀ t ∈ Set.Ioc ((1 : ℝ) / 2) 1, ∀ n : ℕ, ∀ x : ℤ, ‖X t n x‖ ≤ C.toReal := by
    intro t ht n x
    have h1 : ‖X t n x‖ₑ ≤ C :=
      le_trans (enorm_apply_le_variationalNorm (r := r) (fun n : ℕ => X t n x) n)
        (hslice t (Set.Ioc_subset_Icc_self ht) x)
    rw [← ENNReal.ofReal_le_iff_le_toReal hCtop]
    rwa [ofReal_norm]
  have hint : ∀ n : ℕ, ∀ x : ℤ,
      Integrable (fun t : ℝ => X t n x) (volume.restrict (Set.Ioc ((1 : ℝ) / 2) 1)) := by
    intro n x
    refine Integrable.of_bound ?_ C.toReal ?_
    · exact ((hX n x).restrict).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      exact hbd t ht n x
  have hcrux : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => ∫ t in ((1 : ℝ) / 2)..1, X t n x)
      ≤ ∫⁻ t in Set.Ioc ((1 : ℝ) / 2) 1,
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => X t n x) := by
    intro x
    have hA := variationalNorm_integral_le (r := r) hr
      (ν := volume.restrict (Set.Ioc ((1 : ℝ) / 2) 1)) (g := fun t n => X t n x)
      (fun n => hint n x)
    simpa only [intervalIntegral.integral_of_le (by norm_num : ((1 : ℝ) / 2) ≤ 1)] using hA
  calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∫ t in ((1 : ℝ) / 2)..1, X t n x)) q MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ∫⁻ t in Set.Ioc ((1 : ℝ) / 2) 1,
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => X t n x))
          q MeasureTheory.Measure.count := by
        refine MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => ?_)
        simpa only [enorm_eq_self] using hcrux x
    _ ≤ C := eLpNorm_lintegral_le q hq (fun t x =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => X t n x)) C
        (fun t ht => h t (Set.Ioc_subset_Icc_self ht))

/-! ## The `n = 0` spike of the model integrand

The Rademacher--Menshov inequality is applied to the *anchored* family
`k ↦ Btwist … (Tm ρ l₁ (smallSymbF … k) f) (Tm ρ l₂ (smallSymbG … k) g)`, whose `k = 0` term
vanishes: this family agrees with the model integrand `modelInt … n` at every `n ≥ 1`, but it
*misses* the `n = 0` term, which therefore has to be estimated separately.  That term is a genuine
single-scale term, at the scale `N = ⌊a 0⌋`, gated by `smallCond … 0`; it is bounded by the deep
single-scale input `smallModelSingleScale_holds` applied to the *shifted* lacunary sequence
`shiftSeq a = (1, a 0, a 1, …)`, whose first difference is exactly the bump at the scale `⌊a 0⌋`.
The shift is legitimate because `smallCond … 0` forces `⌊a 0⌋ ≥ 4`, so the shifted sequence is
still lacunary with the (absolute) constant `min 2 Λ`. -/

/-- The shifted lacunary sequence `(1, a 0, a 1, …)`, whose first difference is the bump at the
scale `⌊a 0⌋`. -/
def shiftSeq (a : ℕ → ℝ≥0) : ℕ → ℝ≥0 := fun n => if n = 0 then 1 else a (n - 1)

@[simp] lemma shiftSeq_zero (a : ℕ → ℝ≥0) : shiftSeq a 0 = 1 := rfl

@[simp] lemma shiftSeq_one (a : ℕ → ℝ≥0) : shiftSeq a 1 = a 0 := by simp [shiftSeq]

lemma shiftSeq_succ (a : ℕ → ℝ≥0) (n : ℕ) : shiftSeq a (n + 1) = a n := by simp [shiftSeq]

lemma one_le_shiftSeq {a : ℕ → ℝ≥0} (ha1 : ∀ n, 1 ≤ a n) (n : ℕ) : 1 ≤ shiftSeq a n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
    simp [shiftSeq_succ, ha1 m]

/-- The index set, the small-scale cut and the main regime depend on the sequence only through
`⌊a n⌋`, so shifting the sequence does not change the gate at the first scale. -/
lemma smallCond_shiftSeq_one (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) :
    smallCond ρ C₀ (shiftSeq a) l₁ l₂ k₁ k₂ 1 = smallCond ρ C₀ a l₁ l₂ k₁ k₂ 0 := by
  unfold smallCond
  simp only [shiftSeq_one]

/-- The number of available scales is at least `1` in the range `ρ > 0`. -/
lemma one_le_uScale_pos {ρ : ℝ} (hρ : 0 < ρ) (L : ℕ) : 1 ≤ uScale ρ L := by
  simp only [uScale, Work.Analysis.EndVar.scaleCount, Int.floor_toNat]
  refine Nat.le_floor ?_
  simpa using Real.one_le_rpow (x := 2) (z := 2 * ρ * (L : ℝ)) (by norm_num) (by positivity)

/-- On the small-scale condition at `n = 0`, the first scale is at least `4`. -/
lemma two_lt_a_zero_of_smallCond {ρ : ℝ} (hρ : 0 < ρ) {C₀ : ℕ} {a : ℕ → ℝ≥0}
    {l₁ l₂ k₁ k₂ : ℕ} (h : smallCond ρ C₀ a l₁ l₂ k₁ k₂ 0) : 2 < a 0 := by
  obtain ⟨-, -, hmain⟩ := h
  obtain ⟨hk1, -⟩ := hmain
  have hu : 1 ≤ uScale ρ (max k₁ k₂) := one_le_uScale_pos hρ _
  have hlog : 2 ≤ Nat.log 2 (max (Nat.floor (a 0)) 2) := by
    have h1 : k₁ + 2 * uScale ρ (max k₁ k₂) ≤ Nat.log 2 (max (Nat.floor (a 0)) 2) := by
      simpa [Work.Analysis.EndVar.logN] using hk1
    omega
  have h4 : 4 ≤ max (Nat.floor (a 0)) 2 := by
    have := (Nat.le_log_iff_pow_le (by norm_num : 1 < 2)
      (by positivity : max (Nat.floor (a 0)) 2 ≠ 0)).mp hlog
    simpa using this
  have hx : 4 ≤ Nat.floor (a 0) := by
    by_cases hle : Nat.floor (a 0) ≤ 2
    · rw [max_eq_right hle] at h4; omega
    · push Not at hle
      rwa [max_eq_left hle.le] at h4
  have hreal : (4:ℝ) ≤ (a 0 : ℝ) :=
    le_trans (by exact_mod_cast hx) (Nat.floor_le (by positivity))
  have : (2:ℝ) < (a 0 : ℝ) := by linarith
  exact_mod_cast this

/-- The shifted sequence is lacunary, with the absolute constant `min 2 Λ`. -/
lemma lacunary_shiftSeq {Λ : ℝ≥0} {a : ℕ → ℝ≥0} (hΛ : 1 < Λ) (ha : Lacunary Λ a)
    (h20 : 2 < a 0) : Lacunary (min 2 Λ) (shiftSeq a) := by
  intro n
  have hle : min 2 Λ ≤ Λ := min_le_right _ _
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [shiftSeq_one, shiftSeq_zero, div_one]
    exact lt_of_le_of_lt (min_le_left _ _) h20
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
    rw [shiftSeq_succ, shiftSeq_succ]
    exact lt_of_le_of_lt hle (ha m)

/-- The sign vector of the spike: `ε 0 = 1` and `ε k = 0` for `k ≠ 0`. -/
def spikeSign : ℕ → ℂ := fun k => if k = 0 then 1 else 0

@[simp] lemma spikeSign_zero : spikeSign 0 = 1 := rfl

lemma spikeSign_norm_le_one (k : ℕ) : ‖spikeSign k‖ ≤ 1 := by
  by_cases h : k = 0 <;> simp [spikeSign, h]

/-- The randomised symbol at `K = 1` for the shifted sequence is the gated bump at scale
`⌊a 0⌋`. -/
lemma randSymb_shiftSeq_one (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) :
    randSymb (smallSymbF ρ C₀ (shiftSeq a) l₁ l₂ k₁ k₂ t) spikeSign 1
      = fun ξ => if smallCond ρ C₀ a l₁ l₂ k₁ k₂ 0 then
          varphiNt (Nat.floor (a 0)) k₁ t ξ else 0 := by
  funext ξ
  simp only [randSymb, Finset.sum_range_one, spikeSign_zero, one_mul, zero_add]
  unfold smallSymbF
  simp only [if_true, if_neg (by norm_num : ¬ ((1:ℕ) = 0)), shiftSeq_one,
    smallCond_shiftSeq_one, sub_zero]

lemma randSymb_shiftSeqG_one (P : ℤ[X]) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) :
    randSymb (smallSymbG ρ P C₀ (shiftSeq a) l₁ l₂ k₁ k₂ t) spikeSign 1
      = fun ξ => if smallCond ρ C₀ a l₁ l₂ k₁ k₂ 0 then
          varphitildeNt P P.natDegree (Nat.floor (a 0)) k₂ t ξ else 0 := by
  funext ξ
  simp only [randSymb, Finset.sum_range_one, spikeSign_zero, one_mul, zero_add]
  unfold smallSymbG
  simp only [if_true, if_neg (by norm_num : ¬ ((1:ℕ) = 0)), shiftSeq_one,
    smallCond_shiftSeq_one, sub_zero]

/-- **The anchoring identity at `n ≥ 1`**: the model integrand is the corresponding term of the
anchored Rademacher--Menshov family. -/
lemma modelInt_eq_anchored (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (ht : t ∈ Set.Icc ((1:ℝ)/2) 1) (f g : ℤ → ℂ) {Cf Cg : ℝ}
    (hf : ∀ y : ℤ, ‖f y‖ ≤ Cf) (hg : ∀ y : ℤ, ‖g y‖ ≤ Cg) {n : ℕ} (hn : n ≠ 0) :
    modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g n =
      (fun x => smallBtwist ρ P l₁ l₂ (mStarF (uScale ρ (smallL l₁ l₂ k₁ k₂)))
        (mStargF P.natDegree (uScale ρ (smallL l₁ l₂ k₁ k₂)))
        (Tm ρ l₁ (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t n) f)
        (Tm ρ l₂ (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t n) g) x) := by
  have hF : smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t n
      = fun ξ => if smallCond ρ C₀ a l₁ l₂ k₁ k₂ n then
          varphiNt (Nat.floor (a n)) k₁ t ξ else 0 := by
    funext ξ; simp [smallSymbF, hn]
  have hG : smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t n
      = fun ξ => if smallCond ρ C₀ a l₁ l₂ k₁ k₂ n then
          varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t ξ else 0 := by
    funext ξ; simp [smallSymbG, hn]
  unfold modelInt
  rw [hF, hG]
  have hTF : Tm ρ l₁ (fun ξ => if smallCond ρ C₀ a l₁ l₂ k₁ k₂ n then
      varphiNt (Nat.floor (a n)) k₁ t ξ else 0) f
      = fun y => if smallCond ρ C₀ a l₁ l₂ k₁ k₂ n then
          Tm ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f y else 0 :=
    Tm_gate ρ l₁ (smallCond ρ C₀ a l₁ l₂ k₁ k₂ n) (varphiNt (Nat.floor (a n)) k₁ t) f
  have hTG : Tm ρ l₂ (fun ξ => if smallCond ρ C₀ a l₁ l₂ k₁ k₂ n then
      varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t ξ else 0) g
      = fun y => if smallCond ρ C₀ a l₁ l₂ k₁ k₂ n then
          Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g y else 0 :=
    Tm_gate ρ l₂ (smallCond ρ C₀ a l₁ l₂ k₁ k₂ n)
      (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g
  rw [hTF, hTG]
  obtain ⟨Cu, hCu⟩ := Tm_varphiNt_bounded ρ l₁ (Nat.floor (a n)) k₁ f Cf hf
  obtain ⟨Cv, hCv⟩ := Tm_varphitildeNt_bounded P ρ l₂ P.natDegree (Nat.floor (a n)) k₂ g Cg hg
  rw [smallBtwist_gate ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂))
    (smallCond ρ C₀ a l₁ l₂ k₁ k₂ n) _ _
    (fun y => hCu t ht y) (fun y => hCv t ht y)]

/-- **The spike is a single-scale term.**  The `n = 0` term of the model integrand equals the
single-scale expression of the deep input at the shifted sequence, the sign vector `spikeSign` and
`K = 1`. -/
lemma spike_eq_modelInt_zero (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (ht : t ∈ Set.Icc ((1:ℝ)/2) 1) (f g : ℤ → ℂ) {Cf Cg : ℝ}
    (hf : ∀ y : ℤ, ‖f y‖ ≤ Cf) (hg : ∀ y : ℤ, ‖g y‖ ≤ Cg) :
    (fun x => smallBtwist ρ P l₁ l₂ (mStarF (uScale ρ (smallL l₁ l₂ k₁ k₂)))
        (mStargF P.natDegree (uScale ρ (smallL l₁ l₂ k₁ k₂)))
        (Tm ρ l₁ (randSymb (smallSymbF ρ C₀ (shiftSeq a) l₁ l₂ k₁ k₂ t) spikeSign 1) f)
        (Tm ρ l₂ (randSymb (smallSymbG ρ P C₀ (shiftSeq a) l₁ l₂ k₁ k₂ t) spikeSign 1) g) x)
      = modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 := by
  rw [randSymb_shiftSeq_one ρ C₀ a l₁ l₂ k₁ k₂ t, randSymb_shiftSeqG_one P ρ C₀ a l₁ l₂ k₁ k₂ t]
  have hTF : Tm ρ l₁ (fun ξ => if smallCond ρ C₀ a l₁ l₂ k₁ k₂ 0 then
      varphiNt (Nat.floor (a 0)) k₁ t ξ else 0) f
      = fun y => if smallCond ρ C₀ a l₁ l₂ k₁ k₂ 0 then
          Tm ρ l₁ (varphiNt (Nat.floor (a 0)) k₁ t) f y else 0 :=
    Tm_gate ρ l₁ (smallCond ρ C₀ a l₁ l₂ k₁ k₂ 0) (varphiNt (Nat.floor (a 0)) k₁ t) f
  have hTG : Tm ρ l₂ (fun ξ => if smallCond ρ C₀ a l₁ l₂ k₁ k₂ 0 then
      varphitildeNt P P.natDegree (Nat.floor (a 0)) k₂ t ξ else 0) g
      = fun y => if smallCond ρ C₀ a l₁ l₂ k₁ k₂ 0 then
          Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a 0)) k₂ t) g y else 0 :=
    Tm_gate ρ l₂ (smallCond ρ C₀ a l₁ l₂ k₁ k₂ 0)
      (varphitildeNt P P.natDegree (Nat.floor (a 0)) k₂ t) g
  rw [hTF, hTG]
  obtain ⟨Cu, hCu⟩ := Tm_varphiNt_bounded ρ l₁ (Nat.floor (a 0)) k₁ f Cf hf
  obtain ⟨Cv, hCv⟩ := Tm_varphitildeNt_bounded P ρ l₂ P.natDegree (Nat.floor (a 0)) k₂ g Cg hg
  rw [smallBtwist_gate ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂))
    (smallCond ρ C₀ a l₁ l₂ k₁ k₂ 0) _ _ (fun y => hCu t ht y) (fun y => hCv t ht y)]
  rfl

/-- **The spike bound**: the `n = 0` term of the model integrand obeys the single-scale estimate
whenever the single-scale expression at the shifted sequence does. -/
lemma eLpNorm_modelInt_zero_le (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (p₁ p₂ : ENNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (ht : t ∈ Set.Icc ((1:ℝ)/2) 1)
    (f g : ℤ → ℂ) {Cf Cg : ℝ} (hf : ∀ y : ℤ, ‖f y‖ ≤ Cf) (hg : ∀ y : ℤ, ‖g y‖ ≤ Cg)
    {W : ENNReal}
    (h : MeasureTheory.eLpNorm (fun x => smallBtwist ρ P l₁ l₂
        (mStarF (uScale ρ (smallL l₁ l₂ k₁ k₂)))
        (mStargF P.natDegree (uScale ρ (smallL l₁ l₂ k₁ k₂)))
        (Tm ρ l₁ (randSymb (smallSymbF ρ C₀ (shiftSeq a) l₁ l₂ k₁ k₂ t) spikeSign 1) f)
        (Tm ρ l₂ (randSymb (smallSymbG ρ P C₀ (shiftSeq a) l₁ l₂ k₁ k₂ t) spikeSign 1) g) x)
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count ≤ W) :
    MeasureTheory.eLpNorm (fun x => modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x)
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count ≤ W := by
  rw [← spike_eq_modelInt_zero ρ P C₀ a l₁ l₂ k₁ k₂ t ht f g hf hg]
  exact h

/-- The variational norm of a single spike. -/
lemma variationalNorm_spike (r : NNReal) (hr : 1 ≤ r) (c : ℂ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if n = 0 then c else 0)
      ≤ 4 * ‖c‖ₑ := by
  have h := Submission.PointwiseErgodicTheorems.variationalNorm_spike_le (r := r) hr 0 c
  simpa using h

/-! ## The coercion of the Rademacher--Menshov sums to the flat functions -/

/-- The `ℒᵖ`-coercion of the randomised Rademacher--Menshov sum on the `f`-side: the pointwise sum
of differences of the `f`-side pieces is the `Tm`-multiplier applied to the randomised symbol. -/
lemma coe_range_sum_smul_sub_f (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (f g : ℤ → ℂ) {Cf Cg : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hf : ∀ y : ℤ, ‖f y‖ ≤ Cf) (hg : ∀ y : ℤ, ‖g y‖ ≤ Cg) (ε : ℕ → ℂ)
    (uF : ℕ → BddSeq)
    (huF : ∀ k : ℕ, (uF k : ℤ → ℂ) = Tm ρ l₁ (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k) f) :
    ((∑ k ∈ Finset.range K, ε k • (uF (k + 1) - uF k) : BddSeq) : ℤ → ℂ)
      = Tm ρ l₁ (randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K) f := by
  rw [← (Tm_randSymb_smallSymb P ρ hρ hρ1 C₀ a l₁ l₂ k₁ k₂ K t ε f g hf hg l₁).1,
    Submodule.coe_sum]
  funext y
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, huF, huF]

/-- The same, on the `g`-side. -/
lemma coe_range_sum_smul_sub_g (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (f g : ℤ → ℂ) {Cf Cg : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hf : ∀ y : ℤ, ‖f y‖ ≤ Cf) (hg : ∀ y : ℤ, ‖g y‖ ≤ Cg) (ε : ℕ → ℂ)
    (uG : ℕ → BddSeq)
    (huG : ∀ k : ℕ, (uG k : ℤ → ℂ) = Tm ρ l₂ (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t k) g) :
    ((∑ k ∈ Finset.range K, ε k • (uG (k + 1) - uG k) : BddSeq) : ℤ → ℂ)
      = Tm ρ l₂ (randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K) g := by
  rw [← (Tm_randSymb_smallSymb P ρ hρ hρ1 C₀ a l₁ l₂ k₁ k₂ K t ε f g hf hg l₂).2,
    Submodule.coe_sum]
  funext y
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, huG, huG]

/-- **The `ℒᵖ` constant brick.**  If `a * (b * w) ≤ k * lw` for non-negative reals `a, w, k, lw`
and `b : ℝ≥0`, then the product `ofReal a * (b * ofReal w)` of `ℒᵖ`-constants is dominated by
`ofReal k * ofReal lw`. -/
lemma ofReal_const_le {a w lw k : ℝ} {b : ℝ≥0} (ha : 0 ≤ a) (hw : 0 ≤ w) (hlw : 0 ≤ lw)
    (hk : 0 ≤ k) (h : a * ((b : ℝ) * w) ≤ k * lw) :
    ENNReal.ofReal a * ((b : ENNReal) * ENNReal.ofReal w)
      ≤ ENNReal.ofReal k * ENNReal.ofReal lw := by
  have h1 : ENNReal.ofReal a * ENNReal.ofReal ((b : ℝ) * w) ≤ ENNReal.ofReal (k * lw) := by
    rw [← ENNReal.ofReal_mul ha]
    exact ENNReal.ofReal_le_ofReal h
  have h2 : ENNReal.ofReal ((b : ℝ) * w) = (b : ENNReal) * ENNReal.ofReal w :=
    (ENNReal.ofReal_mul b.2).trans
      (congrArg (fun z => z * ENNReal.ofReal w) (ENNReal.coe_nnreal_eq b).symm)
  have h3 : ENNReal.ofReal (k * lw) = ENNReal.ofReal k * ENNReal.ofReal lw :=
    ENNReal.ofReal_mul hk
  rw [h2, h3] at h1
  exact h1

/-! ## The assembly -/

theorem SmallModelVar (P : ℤ[X]) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) :
    ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
      ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
          ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) *
                ENNReal.ofReal (lossWeight c ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
  intro C₀ r hC₀ hr
  obtain ⟨A, hA, ρ₀, hρ₀, hD⟩ :=
    smallModelSingleScale_of_fibre P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum C₀ hC₀
  obtain ⟨S, hSpos, hSabs⟩ := lossWeight_truncIndex_absorption
  have hp₁ne : p₁ ≠ 0 := (lt_trans zero_lt_one hp₁).ne'
  have hp₂ne : p₂ ≠ 0 := (lt_trans zero_lt_one hp₂).ne'
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) hr.le
  have hr2 : (2 : NNReal) ≤ r := hr.le
  -- the `ℒᵖ`-exponent of the estimate
  have hspos : 0 < p₁⁻¹ + p₂⁻¹ :=
    lt_of_lt_of_le (ENNReal.inv_pos.mpr htp₁.ne)
      (le_trans (le_of_eq (add_zero _).symm) (add_le_add le_rfl bot_le))
  have hspe : 1 ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
  have hspetop : (p₁⁻¹ + p₂⁻¹)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hspos.ne'
  have hspene0 : (p₁⁻¹ + p₂⁻¹)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr (ENNReal.add_lt_top.mpr
      ⟨ENNReal.inv_lt_top.mpr (lt_trans zero_lt_one hp₁),
        ENNReal.inv_lt_top.mpr (lt_trans zero_lt_one hp₂)⟩).ne
  have hpeq1 : 1 ≤ (((p₁⁻¹ + p₂⁻¹)⁻¹).toReal) := by
    simpa using ENNReal.toReal_mono hspetop hspe
  obtain ⟨Cb, hCbpos, hCb⟩ := Work.Analysis.Variation.rmVarBound_uniform_ge_one
    (((p₁⁻¹ + p₂⁻¹)⁻¹).toReal) hpeq1 (V := BddSeq) (W := BddSeq) (X := ℤ) Measure.count
  rw [ENNReal.ofReal_toReal hspetop] at hCb
  refine ⟨A + 4, by linarith, min ρ₀ 1, lt_min hρ₀ (by norm_num), ?_⟩
  intro ρ hρ hρle
  have hρρ₀ : ρ ≤ ρ₀ := le_trans hρle (min_le_left _ _)
  have hρ1 : ρ ≤ 1 := le_trans hρle (min_le_right _ _)
  obtain ⟨Css, hCss⟩ := hD ρ hρ hρρ₀
  refine ⟨fun Λ => ↑(2 * max 1 (Nat.ceil (max (Cb * (Css Λ : ℝ) * S Λ)
      (4 * ((Css (min 2 Λ) : ℝ)) * S Λ)))), ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1
  set Ll : ℕ := truncIndex ρ Λ (smallL l₁ l₂ k₁ k₂) with hLl
  set Kc : ℕ := max 1 (Nat.ceil (max (Cb * (Css Λ : ℝ) * S Λ)
      (4 * ((Css (min 2 Λ) : ℝ)) * S Λ))) with hKc
  dsimp only
  rw [← hKc]
  set W : ℝ := (1 + lmaxR l₁ l₂ k₁ k₂) ^ A * (2 : ℝ) ^ (A * ρ * lmaxR l₁ l₂ k₁ k₂) with hW
  set LWr : ℝ := lossWeight (A + 4) ρ l₁ l₂ k₁ k₂ with hLWr
  set F : ENNReal := MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count with hF
  set G : ENNReal := MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count with hG
  have hlmaxnn : (0 : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
    have h0 : (0 : ℤ) ≤ Work.Analysis.EndVar.lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
      unfold Work.Analysis.EndVar.lmax
      positivity
    have h1 : (0 : ℝ) ≤ (Work.Analysis.EndVar.lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℝ) := by
      exact_mod_cast h0
    simpa [lmaxR] using h1
  have hbase : (0 : ℝ) < 1 + lmaxR l₁ l₂ k₁ k₂ := by linarith
  have hWpos : 0 < W := by
    rw [hW]
    exact mul_pos (Real.rpow_pos_of_pos hbase A)
      (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _)
  have hWnn : 0 ≤ W := hWpos.le
  have hLWpos : 0 < LWr := by
    rw [hLWr, lossWeight]
    exact mul_pos (Real.rpow_pos_of_pos hbase (A + 4))
      (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _)
  have hSnn : 0 ≤ S Λ := (hSpos Λ).le
  have hCΛnn : (0 : ℝ) ≤ (Css Λ : ℝ) := (Css Λ).2
  have hC2nn : (0 : ℝ) ≤ (Css (min 2 Λ) : ℝ) := (Css (min 2 Λ)).2
  have hX1ge1 : (1 : ℝ) ≤ ((Nat.log2 (Ll + 1) : ℝ) + 2) ^ 2 := by
    have hL : (0 : ℝ) ≤ (Nat.log2 (Ll + 1) : ℝ) := Nat.cast_nonneg _
    nlinarith [hL]
  have habs : ((Nat.log2 (Ll + 1) : ℝ) + 2) ^ 2 * W ≤ (S Λ) * LWr := by
    have h := hSabs ρ A Λ l₁ l₂ k₁ k₂ hρ hA
    rw [← hLl, ← hW, ← hLWr] at h
    exact h
  have hWle : W ≤ (S Λ) * LWr := by
    have h1 : W ≤ ((Nat.log2 (Ll + 1) : ℝ) + 2) ^ 2 * W := by
      nth_rewrite 1 [← one_mul W]
      exact mul_le_mul_of_nonneg_right hX1ge1 hWnn
    exact h1.trans habs
  have hKc1 : 1 ≤ Kc := by rw [hKc]; exact le_max_left 1 _
  have hceil₁ : Cb * (Css Λ : ℝ) * S Λ ≤ (Kc : ℝ) := by
    rw [hKc]
    have h1 : Cb * (Css Λ : ℝ) * S Λ ≤
        max (Cb * (Css Λ : ℝ) * S Λ) (4 * (Css (min 2 Λ) : ℝ) * S Λ) := le_max_left _ _
    have h2 : max (Cb * (Css Λ : ℝ) * S Λ) (4 * (Css (min 2 Λ) : ℝ) * S Λ) ≤
        ((max 1 (Nat.ceil (max (Cb * (Css Λ : ℝ) * S Λ)
          (4 * (Css (min 2 Λ) : ℝ) * S Λ))) : ℕ) : ℝ) := by
      refine le_trans (Nat.le_ceil _) ?_
      exact_mod_cast le_max_right (1 : ℕ) _
    exact le_trans h1 h2
  have hceil₂ : 4 * ((Css (min 2 Λ) : ℝ)) * S Λ ≤ (Kc : ℝ) := by
    rw [hKc]
    have h1 : 4 * ((Css (min 2 Λ) : ℝ)) * S Λ ≤
        max (Cb * (Css Λ : ℝ) * S Λ) (4 * (Css (min 2 Λ) : ℝ) * S Λ) := le_max_right _ _
    have h2 : max (Cb * (Css Λ : ℝ) * S Λ) (4 * (Css (min 2 Λ) : ℝ) * S Λ) ≤
        ((max 1 (Nat.ceil (max (Cb * (Css Λ : ℝ) * S Λ)
          (4 * (Css (min 2 Λ) : ℝ) * S Λ))) : ℕ) : ℝ) := by
      refine le_trans (Nat.le_ceil _) ?_
      exact_mod_cast le_max_right (1 : ℕ) _
    exact le_trans h1 h2
  have h2Kc : (((2 * Kc : ℕ) : ℝ≥0) : ENNReal) = 2 * (Kc : ENNReal) := by
    push_cast
    ring
  -- the two constants of the pieces
  have hCbX1nn : 0 ≤ Cb * ((Nat.log2 (Ll + 1) : ℝ) + 2) ^ 2 := by positivity
  have hAB : ENNReal.ofReal (Cb * ((Nat.log2 (Ll + 1) : ℝ) + 2) ^ 2) *
      ((Css Λ : ENNReal) * ENNReal.ofReal W)
      ≤ (Kc : ENNReal) * ENNReal.ofReal LWr := by
    have h := ofReal_const_le (a := Cb * ((Nat.log2 (Ll + 1) : ℝ) + 2) ^ 2) (b := Css Λ)
      (w := W) (k := (Kc : ℝ)) (lw := LWr) hCbX1nn hWnn hLWpos.le (by positivity)
      (show (Cb * ((Nat.log2 (Ll + 1) : ℝ) + 2) ^ 2) * ((Css Λ : ℝ) * W) ≤ (Kc : ℝ) * LWr by
        calc (Cb * ((Nat.log2 (Ll + 1) : ℝ) + 2) ^ 2) * ((Css Λ : ℝ) * W)
            = (Cb * (Css Λ : ℝ)) * (((Nat.log2 (Ll + 1) : ℝ) + 2) ^ 2 * W) := by ring
          _ ≤ (Cb * (Css Λ : ℝ)) * (S Λ * LWr) :=
              mul_le_mul_of_nonneg_left habs (mul_nonneg hCbpos.le hCΛnn)
          _ = (Cb * (Css Λ : ℝ) * S Λ) * LWr := by ring
          _ ≤ (Kc : ℝ) * LWr := mul_le_mul_of_nonneg_right hceil₁ hLWpos.le)
    rwa [ENNReal.ofReal_natCast] at h
  have hC2 : 4 * ((Css (min 2 Λ) : ENNReal) * ENNReal.ofReal W)
      ≤ (Kc : ENNReal) * ENNReal.ofReal LWr := by
    have h := ofReal_const_le (a := 4) (b := Css (min 2 Λ)) (w := W) (k := (Kc : ℝ)) (lw := LWr)
      (by norm_num) hWnn hLWpos.le (by positivity)
      (show (4 : ℝ) * ((Css (min 2 Λ) : ℝ) * W) ≤ (Kc : ℝ) * LWr by
        calc (4 : ℝ) * ((Css (min 2 Λ) : ℝ) * W)
            = 4 * (Css (min 2 Λ) : ℝ) * W := by ring
          _ ≤ 4 * (Css (min 2 Λ) : ℝ) * (S Λ * LWr) :=
              mul_le_mul_of_nonneg_left hWle (by positivity)
          _ = 4 * (Css (min 2 Λ) : ℝ) * S Λ * LWr := by ring
          _ ≤ (Kc : ℝ) * LWr := mul_le_mul_of_nonneg_right hceil₂ hLWpos.le)
    simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast] using h
  have hKkne : (((2 * Kc : ℕ) : ℝ≥0) : ENNReal) ≠ 0 := by
    simp only [ne_eq, ENNReal.coe_eq_zero, NNReal.coe_eq_zero, Nat.cast_eq_zero]
    omega
  -- degenerate cases: a vanishing input
  by_cases hf0 : F = 0
  · rw [eLpNorm_smallModelTuple_eq_zero ρ P C₀ a l₁ l₂ k₁ k₂ r p₁ p₂ hp₁ne hp₂ne f g
        (Or.inl (by rw [← hF]; exact hf0))]
    exact bot_le
  by_cases hg0 : G = 0
  · rw [eLpNorm_smallModelTuple_eq_zero ρ P C₀ a l₁ l₂ k₁ k₂ r p₁ p₂ hp₁ne hp₂ne f g
        (Or.inr (by rw [← hG]; exact hg0))]
    exact bot_le
  -- degenerate cases: an infinite input
  by_cases hftop : F = ⊤
  · have hne1 : ((((2 * Kc : ℕ) : ℝ≥0) : ENNReal) * ENNReal.ofReal LWr) ≠ 0 :=
      mul_ne_zero hKkne (ENNReal.ofReal_ne_zero_iff.mpr hLWpos)
    rw [hftop, ENNReal.mul_top hne1, ENNReal.top_mul hg0]
    exact le_top
  by_cases hgtop : G = ⊤
  · have hne1 : ((((2 * Kc : ℕ) : ℝ≥0) : ENNReal) * ENNReal.ofReal LWr * F) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hKkne (ENNReal.ofReal_ne_zero_iff.mpr hLWpos)) hf0
    rw [hgtop, ENNReal.mul_top hne1]
    exact le_top
  -- the main case: both `ℒᵖ`-norms are finite and non-zero
  obtain ⟨Cf, hCf⟩ := bounded_of_eLpNorm_count_lt_top hp₁ne
    (by rw [← hF]; exact lt_of_le_of_ne le_top hftop)
  obtain ⟨Cg, hCg⟩ := bounded_of_eLpNorm_count_lt_top hp₂ne
    (by rw [← hG]; exact lt_of_le_of_ne le_top hgtop)
  -- slice measurability of the time integrand
  have hXsl : ∀ n : ℕ, ∀ x : ℤ,
      AEMeasurable (fun t : ℝ => modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g n x) volume := by
    intro n x
    by_cases hc : smallCond ρ C₀ a l₁ l₂ k₁ k₂ n
    · have heq : (fun t : ℝ => modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g n x)
          = fun t : ℝ => smallBtwist ρ P l₁ l₂ (mStarF (uScale ρ (smallL l₁ l₂ k₁ k₂)))
              (mStargF P.natDegree (uScale ρ (smallL l₁ l₂ k₁ k₂)))
              (Tm ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f)
              (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x := by
        funext t
        unfold modelInt
        simp only [hc, if_true]
      rw [heq]
      exact (measurable_smallBtwist_slice P ρ (Nat.floor (a n)) l₁ l₂ k₁ k₂ f g x).aemeasurable
    · have heq : (fun t : ℝ => modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g n x)
          = fun _ : ℝ => (0 : ℂ) := by
        funext t
        exact congrFun (modelInt_eq_zero_of_not_smallCond ρ P C₀ a l₁ l₂ k₁ k₂ t f g hc) x
      rw [heq]
      exact aemeasurable_const
  -- the per-`t` single-scale bound
  have hkey : ∀ t ∈ Set.Icc ((1:ℝ)/2) 1,
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g n x))
        ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
      ≤ ((((2 * Kc : ℕ) : ℝ≥0) : ENNReal) * ENNReal.ofReal LWr * F * G) := by
    intro t ht
    have hbddF : ∀ k : ℕ, ∃ C : ℝ, ∀ y : ℤ,
        ‖Tm ρ l₁ (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k) f y‖ ≤ C :=
      fun k => (bump_Tm_bounded P ρ hρ hρ1 C₀ a l₁ l₂ k₁ k₂ t ht).1 k l₁ f ⟨Cf, hCf⟩
    have hbddG : ∀ k : ℕ, ∃ C : ℝ, ∀ y : ℤ,
        ‖Tm ρ l₂ (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t k) g y‖ ≤ C :=
      fun k => (bump_Tm_bounded P ρ hρ hρ1 C₀ a l₁ l₂ k₁ k₂ t ht).2 k l₂ g ⟨Cg, hCg⟩
    set uF : ℕ → BddSeq := fun k => ⟨Tm ρ l₁ (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k) f, hbddF k⟩
      with huF
    set uG : ℕ → BddSeq := fun k => ⟨Tm ρ l₂ (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t k) g, hbddG k⟩
      with huG
    have huF' : ∀ k : ℕ, (uF k : ℤ → ℂ) = Tm ρ l₁ (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k) f := by
      intro k; rw [huF]
    have huG' : ∀ k : ℕ, (uG k : ℤ → ℂ) = Tm ρ l₂ (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t k) g := by
      intro k; rw [huG]
    have hF0 : uF 0 = 0 := by
      refine Subtype.ext ?_
      rw [huF']
      simp [smallSymbF_zero, Tm_zero]
    have hG0 : uG 0 = 0 := by
      refine Subtype.ext ?_
      rw [huG']
      simp [smallSymbG_zero, Tm_zero]
    set B : BddSeq → BddSeq → ℤ → ℂ := fun u v x => smallBtwist ρ P l₁ l₂
        (mStarF (uScale ρ (smallL l₁ l₂ k₁ k₂)))
        (mStargF P.natDegree (uScale ρ (smallL l₁ l₂ k₁ k₂))) u.1 v.1 x with hB
    have hbil := fun (u u' v v' : BddSeq) =>
      smallBtwist_bilinear_of_bounded ρ P l₁ l₂
        (mStarF (uScale ρ (smallL l₁ l₂ k₁ k₂)))
        (mStargF P.natDegree (uScale ρ (smallL l₁ l₂ k₁ k₂)))
        (summable_cw_mStarF_rho ρ (uScale ρ (smallL l₁ l₂ k₁ k₂)))
        (summable_cw_mStargF_rho P (uScale ρ (smallL l₁ l₂ k₁ k₂)))
        u.1 u'.1 v.1 v'.1 u.2.choose u'.2.choose v.2.choose v'.2.choose
        u.2.choose_spec u'.2.choose_spec v.2.choose_spec v'.2.choose_spec
    have hB1 : ∀ u u' v : BddSeq, B (u + u') v = B u v + B u' v := by
      intro u u' v
      rw [hB]
      exact (hbil u u' v v).1
    have hB2 : ∀ u v v' : BddSeq, B u (v + v') = B u v + B u v' := by
      intro u v v'
      rw [hB]
      exact (hbil u u v v').2.1
    have hBs1 : ∀ (c : ℂ) (u v : BddSeq), B (c • u) v = c • B u v := by
      intro c u v
      rw [hB]
      exact (hbil u u v v).2.2.1 c
    have hBs2 : ∀ (c : ℂ) (u v : BddSeq), B u (c • v) = c • B u v := by
      intro c u v
      rw [hB]
      exact (hbil u u v v).2.2.2.1 c
    have hmeas : ∀ k k' : ℕ, AEMeasurable (fun x => B (uF k) (uG k') x) Measure.count :=
      fun k k' => (Measurable.of_discrete).aemeasurable
    have hRMhyp : ∀ (ε ε' : ℕ → ℂ), (∀ k, ‖ε k‖ ≤ 1) → (∀ k, ‖ε' k‖ ≤ 1) →
        MeasureTheory.eLpNorm (fun x => B (∑ k ∈ Finset.range (Ll + 1), ε k • (uF (k + 1) - uF k))
            (∑ k ∈ Finset.range (Ll + 1), ε' k • (uG (k + 1) - uG k)) x)
          ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
        ≤ ((Css Λ : ENNReal) * ENNReal.ofReal W * F * G) := by
      intro ε ε' hε hε'
      have h1 := coe_range_sum_smul_sub_f ρ P C₀ a l₁ l₂ k₁ k₂ (Ll + 1) t f g hρ hρ1 hCf hCg ε
        uF huF'
      have h2 := coe_range_sum_smul_sub_g ρ P C₀ a l₁ l₂ k₁ k₂ (Ll + 1) t f g hρ hρ1 hCf hCg ε'
        uG huG'
      have h3 : (fun x => B (∑ k ∈ Finset.range (Ll + 1), ε k • (uF (k + 1) - uF k))
            (∑ k ∈ Finset.range (Ll + 1), ε' k • (uG (k + 1) - uG k)) x)
          = fun x => smallBtwist ρ P l₁ l₂ (mStarF (uScale ρ (smallL l₁ l₂ k₁ k₂)))
              (mStargF P.natDegree (uScale ρ (smallL l₁ l₂ k₁ k₂)))
              (Tm ρ l₁ (randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε (Ll + 1)) f)
              (Tm ρ l₂ (randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε' (Ll + 1)) g) x := by
        funext x
        rw [hB]
        simp only [h1, h2]
      rw [h3]
      exact hCss a Λ l₁ l₂ k₁ k₂ (Ll + 1) t ε ε' f g hΛ ha ha1 hε hε' ht
    have hRM := hCb B hB1 hBs1 hB2 hBs2 (Ll + 1) uF uG
        (((Css Λ : ENNReal) * ENNReal.ofReal W * F * G)) hF0 hG0 hmeas hRMhyp
    set Z : ℕ → ℤ → ℂ := fun k x => B (uF k) (uG k) x with hZ
    have hZ0 : Z 0 = 0 := by
      rw [hZ]
      have h00 : B (0 : BddSeq) (uG 0) = 0 := by
        have h := hBs1 0 (uF 0) (uG 0)
        rw [hF0] at h
        simpa using h
      funext x
      show B (uF 0) (uG 0) x = 0
      rw [hF0, h00]
      rfl
    have hZvan : ∀ k : ℕ, Ll < k → Z k = 0 := by
      intro k hk
      have hk0 : k ≠ 0 := by omega
      have hnc : ¬ smallCond ρ C₀ a l₁ l₂ k₁ k₂ k :=
        smallCond_false_of_truncIndex_le ρ C₀ a Λ l₁ l₂ k₁ k₂ k hΛ ha ha1 (le_of_lt hk)
      have hsym : smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k = 0 := by
        funext ξ; simp [smallSymbF, hk0, hnc]
      have huFk : uF k = 0 := by
        refine Subtype.ext ?_
        rw [huF']
        simp [hsym, Tm_zero]
      have hzero : B (uF k) (uG k) = 0 := by
        rw [huFk]
        have h := hBs1 0 (0 : BddSeq) (uG k)
        simpa using h
      rw [hZ]
      funext x
      exact congrFun hzero x
    -- the `Z`-piece
    have hZle : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Z n x)) ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
        ≤ (Kc : ENNReal) * ENNReal.ofReal LWr * F * G := by
      have hstep : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Z n x)
          ≤ Work.Analysis.Variation.VrFull 2 (Ll + 1) (fun n : ℕ => Z n x) := fun x =>
        Work.KMTPlan.A6.variationalNorm_le_VrFull hr2 Ll (fun n => Z n x)
          (fun k hk => congrFun (hZvan k hk) x)
      have hmonoz : MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Z n x))
          ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
          ≤ MeasureTheory.eLpNorm (fun x : ℤ =>
              Work.Analysis.Variation.VrFull 2 (Ll + 1) (fun n : ℕ => Z n x))
            ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count :=
        MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hstep
      have hRM' : MeasureTheory.eLpNorm (fun x : ℤ =>
            Work.Analysis.Variation.VrFull 2 (Ll + 1) (fun n : ℕ => Z n x))
          ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
          ≤ (Kc : ENNReal) * ENNReal.ofReal LWr * F * G :=
        hRM.trans (by
          calc ENNReal.ofReal (Cb * ((Nat.log2 (Ll + 1) : ℝ) + 2) ^ 2) *
                ((Css Λ : ENNReal) * ENNReal.ofReal W * F * G)
              = (ENNReal.ofReal (Cb * ((Nat.log2 (Ll + 1) : ℝ) + 2) ^ 2) *
                  ((Css Λ : ENNReal) * ENNReal.ofReal W) * F) * G := by
                rw [← mul_assoc, ← mul_assoc]
            _ ≤ ((Kc : ENNReal) * ENNReal.ofReal LWr * F) * G :=
                mul_le_mul' (mul_le_mul' hAB le_rfl) le_rfl
            _ = (Kc : ENNReal) * ENNReal.ofReal LWr * F * G := rfl)
      exact hmonoz.trans hRM'
    -- the spike piece
    have hspike0 : MeasureTheory.eLpNorm (fun x : ℤ =>
        ‖modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x‖ₑ)
        ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
        ≤ (Css (min 2 Λ) : ENNReal) * ENNReal.ofReal W * F * G := by
      have hbase : MeasureTheory.eLpNorm (fun x => modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x)
          ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
          ≤ (Css (min 2 Λ) : ENNReal) * ENNReal.ofReal W * F * G := by
        by_cases hc0 : smallCond ρ C₀ a l₁ l₂ k₁ k₂ 0
        · have h20 : 2 < a 0 := two_lt_a_zero_of_smallCond hρ hc0
          have hlac : Lacunary (min 2 Λ) (shiftSeq a) := lacunary_shiftSeq hΛ ha h20
          have h1le : ∀ n, 1 ≤ shiftSeq a n := fun n => one_le_shiftSeq ha1 n
          have hlt : 1 < min 2 Λ := lt_min (by norm_num) hΛ
          exact eLpNorm_modelInt_zero_le ρ P C₀ a p₁ p₂ l₁ l₂ k₁ k₂ t ht f g hCf hCg
            (hCss (shiftSeq a) (min 2 Λ) l₁ l₂ k₁ k₂ 1 t spikeSign spikeSign f g hlt hlac
              h1le (fun k => spikeSign_norm_le_one k) (fun k => spikeSign_norm_le_one k) ht)
        · rw [modelInt_eq_zero_of_not_smallCond ρ P C₀ a l₁ l₂ k₁ k₂ t f g hc0]
          simp
      refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
        (f := fun x : ℤ => ‖modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x‖ₑ)
        (g := fun x : ℤ => modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x)
        (fun x => ?_)).trans hbase
      exact le_of_eq rfl
    have hspikele : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if n = 0 then modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x else 0))
        ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
        ≤ (Kc : ENNReal) * ENNReal.ofReal LWr * F * G := by
      have hstep : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if n = 0 then modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x else 0)
          ≤ 4 * ‖modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x‖ₑ := fun x =>
        variationalNorm_spike r hr1 (modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x)
      have h1 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if n = 0 then modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x else 0))
          ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
          ≤ MeasureTheory.eLpNorm (fun x : ℤ =>
              4 * ‖modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x‖ₑ)
            ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count :=
        MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hstep
      have h2 : MeasureTheory.eLpNorm (fun x : ℤ =>
            4 * ‖modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x‖ₑ)
          ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
          = 4 * MeasureTheory.eLpNorm (fun x : ℤ =>
              ‖modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x‖ₑ)
            ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count :=
        Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (μ := Measure.count)
          (c := (4 : ENNReal)) (by norm_num) (p := ((p₁⁻¹ + p₂⁻¹)⁻¹)) hspene0 hspetop
          (V := fun x : ℤ => ‖modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x‖ₑ)
      have h3 : (4 : ENNReal) * MeasureTheory.eLpNorm (fun x : ℤ =>
              ‖modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x‖ₑ)
            ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
          ≤ (Kc : ENNReal) * ENNReal.ofReal LWr * F * G := by
        calc (4 : ENNReal) * MeasureTheory.eLpNorm (fun x : ℤ =>
                ‖modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x‖ₑ)
                ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
            ≤ (4 : ENNReal) * ((Css (min 2 Λ) : ENNReal) * ENNReal.ofReal W * F * G) :=
              mul_le_mul' le_rfl hspike0
          _ = ((4 * ((Css (min 2 Λ) : ENNReal) * ENNReal.ofReal W)) * F) * G := by
              rw [← mul_assoc, ← mul_assoc]
          _ ≤ (((Kc : ENNReal) * ENNReal.ofReal LWr) * F) * G :=
              mul_le_mul' (mul_le_mul' hC2 le_rfl) le_rfl
          _ = (Kc : ENNReal) * ENNReal.ofReal LWr * F * G := rfl
      exact h1.trans ((le_of_eq h2).trans h3)
    -- the model integrand is the pointwise sum of the `Z`-piece and the spike
    have hsplitpt : ∀ n : ℕ, ∀ x : ℤ, modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g n x
        = Z n x + (if n = 0 then modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x else 0) := by
      intro n x
      by_cases hn : n = 0
      · subst hn
        rw [if_pos rfl]
        simp only [hZ0, Pi.zero_apply, zero_add]
      · rw [if_neg hn, add_zero]
        exact congrFun (modelInt_eq_anchored ρ P C₀ a l₁ l₂ k₁ k₂ t ht f g hCf hCg hn) x
    have hsplitfun : ∀ x : ℤ, (fun n : ℕ => modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g n x)
        = (fun n : ℕ => Z n x) + (fun n : ℕ => if n = 0 then
            modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x else 0) := by
      intro x
      funext n
      exact hsplitpt n x
    have hpoint : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g n x)
        ≤ PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Z n x)
          + PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if n = 0 then
                modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x else 0) := by
      intro x
      rw [hsplitfun x]
      exact variationalNorm_add_le (r := r) hr1 (fun n => Z n x)
        (fun n => if n = 0 then modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x else 0)
    have hmono : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g n x))
        ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Z n x)
            + PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if n = 0 then
                modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x else 0))
          ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count :=
      MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hpoint
    have hadd : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Z n x)
            + PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if n = 0 then
                modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x else 0))
          ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Z n x)) ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
          + MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if n = 0 then
                modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x else 0))
            ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count :=
      eLpNorm_add_le hspe
    have htwice : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Z n x)) ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
          + MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if n = 0 then
                modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g 0 x else 0))
            ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
        ≤ (((2 * Kc : ℕ) : ℝ≥0) : ENNReal) * ENNReal.ofReal LWr * F * G := by
      refine (add_le_add hZle hspikele).trans ?_
      rw [← two_mul, h2Kc]
      exact le_of_eq (by rw [← mul_assoc, ← mul_assoc, ← mul_assoc])
    exact hmono.trans (hadd.trans htwice)
  -- Minkowski's integral inequality in `t`, and the identification of the model tuple
  have hmink := variationalNorm_intervalIntegral_eLpNorm_le' r hr1 ((p₁⁻¹ + p₂⁻¹)⁻¹) hspe
      (fun t n x => modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g n x)
      ((((2 * Kc : ℕ) : ℝ≥0) : ENNReal) * ENNReal.ofReal LWr * F * G) hXsl hkey
  have hconv : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          ∫ t in ((1 : ℝ) / 2)..1, modelInt ρ P C₀ a l₁ l₂ k₁ k₂ t f g n x) := by
    funext x
    congr 1
    funext n
    exact smallModelTuple_eq_integral ρ P C₀ a l₁ l₂ k₁ k₂ f g n x
  rw [hconv]
  exact hmink

end

end Work.KMTAreas.A7
