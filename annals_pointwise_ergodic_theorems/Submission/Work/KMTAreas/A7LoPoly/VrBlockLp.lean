import Mathlib
import Submission.Work.KMTAreas.A7Hi2.supShallowLe
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7LoPoly

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-!
# The `Vʳ`-block bound for the low-pass Ionescu--Wainger walk on the good major arcs

The target `VrBlockLp` is the `(H)`-piece of the low-pass program: for `r ≥ 2`, `p > 1` and every
good-major-arc datum, the `ℓᵖ` norm of the **truncated `r`-variation** of the walk
`n ↦ lpf ρ l m₀ n f − lpf ρ l m₀ 0 f` (i.e. anchored at `0`) is bounded by
`C (log₂ M + 1) ‖f‖_{ℓᵖ}`.

The proof is the classical dyadic Rademacher--Men'shov route (the first three steps of the proof of
`A7Hi2.supShallowLe`):

1. the `ℓ^r`-norm is dominated by the `ℓ²`-norm for a finite family when `r ≥ 2`
   (`Vr_le_Vr_two`), so it suffices to bound `V²`;
2. the one-dimensional Rademacher--Men'shov inequality
   `V²(a) ≤ 2 Σ_{m ≤ log₂ M} incLp 2 M (2^m) a` (`Vr_two_le_sum_incLp`), where
   `incLp 2 M N a` is the `ℓ²`-norm of the jumps of `a` across the blocks of size `N` tiling `(0,M]`;
3. each such block square function is a single-chain block square function of the walk, bounded in
   `ℓᵖ` with an `l`-free constant by the *proved, unconditional*
   `Work.KMTAreas.A7Lpd.singleChain_blockSqSum_le` (`eLpNorm_incLp_le` below).

The loss is the number of dyadic scales, `log₂ M + 1`.
-/

/-! ## 1. The `ℓ^r ≤ ℓ²` comparison for finite `ℝ≥0∞`-families -/

/-- `∑ aᵢ^p ≤ (∑ aᵢ)^p` for `p ≥ 1` and `aᵢ ∈ ℝ≥0∞`. -/
lemma sum_rpow_le_rpow_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) {p : ℝ}
    (hp : 1 ≤ p) : ∑ i ∈ s, a i ^ p ≤ (∑ i ∈ s, a i) ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [ENNReal.zero_rpow_of_pos (by linarith : (0:ℝ) < p)]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      calc a i ^ p + ∑ j ∈ s, a j ^ p ≤ a i ^ p + (∑ j ∈ s, a j) ^ p := add_le_add le_rfl ih
        _ ≤ (a i + ∑ j ∈ s, a j) ^ p := ENNReal.add_rpow_le_rpow_add _ _ hp

/-- **The `ℓ^r ≤ ℓ²` comparison for finite families.**  For `r ≥ 2` and `aᵢ ∈ ℝ≥0∞`,
`(∑ aᵢ^r)^{1/r} ≤ (∑ aᵢ^2)^{1/2}`  (take `p = r/2 ≥ 1` in `sum_rpow_le_rpow_sum`, with `aᵢ`
replaced by `aᵢ²`). -/
lemma sum_rpow_le_sqrt {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) {r : ℝ}
    (hr : 2 ≤ r) :
    (∑ i ∈ s, a i ^ r) ^ (1 / r) ≤ (∑ i ∈ s, a i ^ (2:ℝ)) ^ ((1:ℝ) / 2) := by
  have hp1 : (1:ℝ) ≤ r / 2 := by linarith
  have hsum : ∑ i ∈ s, a i ^ r = ∑ i ∈ s, (a i ^ (2:ℝ)) ^ (r / 2) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [show r = 2 * (r / 2) by ring]
    rw [ENNReal.rpow_mul]
  rw [hsum]
  refine (ENNReal.rpow_le_rpow (sum_rpow_le_rpow_sum s (fun i => a i ^ (2:ℝ)) hp1)
    (by positivity : (0:ℝ) ≤ 1 / r)).trans ?_
  rw [← ENNReal.rpow_mul]
  rw [show r / 2 * (1 / r) = (1:ℝ) / 2 by field_simp]

/-- **The truncated variation is antitone in the exponent** (`r ≥ 2`): `Vʳ ≤ V²`. -/
lemma Vr_le_Vr_two (r : ℝ) (hr : 2 ≤ r) (M : ℕ) (a : ℕ → ℂ) :
    Work.Analysis.Variation.Vr r M a ≤ Work.Analysis.Variation.Vr 2 M a := by
  unfold Work.Analysis.Variation.Vr
  refine iSup_le fun J => iSup_le fun u => iSup_le fun hu => iSup_le fun hu0 =>
    iSup_le fun huK => ?_
  refine (sum_rpow_le_sqrt Finset.univ
    (fun j : Fin J => ‖a (u j.succ) - a (u j.castSucc)‖ₑ) hr).trans ?_
  exact le_iSup_of_le J (le_iSup_of_le u (le_iSup_of_le hu (le_iSup_of_le hu0
    (le_iSup_of_le huK (le_refl _)))))

/-! ## 2. Elementary `eLpNorm` helpers (duplicated from `A7Hi2.supShallowLe`) -/

/-- `‖z‖ₑ = ofReal ‖z‖` for a complex number. -/
private lemma enorm_eq_ofReal_norm' (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm]

/-- `eLpNorm` of an `ofReal`-valued function with nonnegative values equals the `eLpNorm` of the
real-valued function. -/
private lemma eLpNorm_ofReal_eq {g : ℤ → ℝ} (hg : ∀ x, 0 ≤ g x) {p : ENNReal}
    (hp0 : p ≠ 0) (hpt : p ≠ ⊤) :
    eLpNorm (fun x : ℤ => ENNReal.ofReal (g x)) p Measure.count = eLpNorm g p Measure.count := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hpt,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hpt]
  congr 1
  refine lintegral_congr fun x => ?_
  congr 1
  · rw [enorm_eq_self, enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, Real.nnnorm_of_nonneg (hg x),
      NNReal.coe_mk]

/-- Passing to the `enorm`-valued function does not change the `eLpNorm` of a `ℂ`-valued
sequence on `ℤ`. -/
private lemma eLpNorm_enorm_eq_local {g : ℤ → ℂ} {p : ENNReal} (h0 : p ≠ 0) (ht : p ≠ ⊤) :
    eLpNorm (fun x : ℤ => ‖g x‖ₑ) p Measure.count = eLpNorm g p Measure.count := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) h0 ht,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) h0 ht]
  simp only [enorm_eq_self]

/-- Scaling an `ℝ≥0∞`-valued function by a finite constant scales its `eLpNorm`. -/
private lemma eLpNorm_const_mul_enorm {g : ℤ → ℝ≥0∞} (c : ℝ≥0∞) (hc : c ≠ ⊤) {p : ENNReal}
    (hp0 : p ≠ 0) (hpt : p ≠ ⊤) :
    eLpNorm (fun x : ℤ => c * g x) p Measure.count = c * eLpNorm g p Measure.count := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hpt,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hpt]
  have hp' : (0 : ℝ) < p.toReal := ENNReal.toReal_pos hp0 hpt
  have h1 : ∀ x, ‖c * g x‖ₑ = c * ‖g x‖ₑ := fun x => by rw [enorm_eq_self, enorm_eq_self]
  simp only [h1]
  rw [show (fun x : ℤ => (c * ‖g x‖ₑ) ^ p.toReal)
      = fun x => c ^ p.toReal * ‖g x‖ₑ ^ p.toReal from
    funext fun x => ENNReal.mul_rpow_of_nonneg _ _ hp'.le]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp'.le hc)]
  rw [show (c ^ p.toReal * (∫⁻ x : ℤ, ‖g x‖ₑ ^ p.toReal ∂Measure.count)) ^ (1 / p.toReal)
      = (c ^ p.toReal) ^ (1 / p.toReal)
        * (∫⁻ x : ℤ, ‖g x‖ₑ ^ p.toReal ∂Measure.count) ^ (1 / p.toReal) from
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hp'.ne', ENNReal.rpow_one]

/-- `eLpNorm` of a finite sum of `ℝ≥0∞`-valued functions. -/
private lemma eLpNorm_finset_sum_le' {ι : Type*} (s : Finset ι) (F : ι → ℤ → ℝ≥0∞) {p : ENNReal}
    (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) :
    eLpNorm (fun x : ℤ => ∑ i ∈ s, F i x) p Measure.count
      ≤ ∑ i ∈ s, eLpNorm (F i) p Measure.count := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h1 : (fun x : ℤ => ∑ i ∈ insert a s, F i x)
        = (F a) + (fun x : ℤ => ∑ i ∈ s, F i x) := by
      funext x
      rw [Finset.sum_insert ha]
      rfl
    rw [h1]
    refine (Work.KMTAreas.A7.eLpNorm_add_le_ennreal hp1 hpt).trans ?_
    rw [Finset.sum_insert ha]
    exact add_le_add le_rfl ih

/-! ## 3. Rademacher--Men'shov at the exponent `2` -/

/-- `incLp 2 K M a` is the `ofReal` of the real `ℓ²`-increment norm over the `M`-blocks. -/
private lemma incLp_eq_ofReal (a : ℕ → ℂ) (K M : ℕ) :
    Work.Analysis.Variation.incLp 2 K M a
      = ENNReal.ofReal ((∑ q ∈ Finset.range (Work.Analysis.Variation.nb K M),
          ‖a (min (M * (q + 1)) K) - a (M * q)‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) := by
  unfold Work.Analysis.Variation.incLp
  have h₀ : (∑ x ∈ Finset.range (Work.Analysis.Variation.nb K M),
        ‖a (min (M * (x + 1)) K) - a (M * x)‖ₑ ^ (2 : ℝ))
      = ∑ x ∈ Finset.range (Work.Analysis.Variation.nb K M),
        ENNReal.ofReal (‖a (min (M * (x + 1)) K) - a (M * x)‖ ^ (2 : ℝ)) := by
    refine Finset.sum_congr rfl fun q _ => ?_
    have hz : ‖a (min (M * (q + 1)) K) - a (M * q)‖ₑ
        = ENNReal.ofReal ‖a (min (M * (q + 1)) K) - a (M * q)‖ := enorm_eq_ofReal_norm' _
    rw [hz, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
  rw [h₀, ← ENNReal.ofReal_sum_of_nonneg (fun q _ => Real.rpow_nonneg (norm_nonneg _) 2)]
  exact ENNReal.ofReal_rpow_of_nonneg
    (Finset.sum_nonneg fun q _ => Real.rpow_nonneg (norm_nonneg _) 2) (by norm_num)

/-- For `q < nb K M` the block end `M * q` is below `K`, so `min (M * q) K = M * q`. -/
private lemma min_mul_of_lt_nb {K M q : ℕ} (hM : 0 < M)
    (hq : q < Work.Analysis.Variation.nb K M) : min (M * q) K = M * q := by
  have hle : M * q ≤ K := by
    have hq1 : q + 1 ≤ Work.Analysis.Variation.nb K M := hq
    have h1 : M * (q + 1) ≤ M * Work.Analysis.Variation.nb K M := Nat.mul_le_mul_left M hq1
    have hsucc : M * (q + 1) = M * q + M := by ring
    have hnb : M * Work.Analysis.Variation.nb K M ≤ K + M - 1 := by
      rw [Work.Analysis.Variation.nb]; exact Nat.mul_div_le _ _
    omega
  exact min_eq_left hle

/-- **The one-dimensional Rademacher--Men'shov inequality with the explicit constant `2`.** -/
lemma Vr_two_le_sum_incLp (K : ℕ) (a : ℕ → ℂ) (ha0 : a 0 = 0) :
    Work.Analysis.Variation.Vr 2 K a ≤ ENNReal.ofReal 2 *
      ∑ m ∈ Finset.range (Nat.log2 K + 1), Work.Analysis.Variation.incLp 2 K (2 ^ m) a := by
  have hKM : K < 2 ^ (Nat.log2 K + 1) := by
    rcases Nat.eq_zero_or_pos K with hK0 | hK0
    · subst hK0
      rw [Nat.log2_zero]
      norm_num
    · exact (Nat.log2_lt (n := K) (k := Nat.log2 K + 1) hK0.ne').mp
        (Nat.lt_succ_self (Nat.log2 K))
  rw [show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) from by simp]
  unfold Work.Analysis.Variation.Vr
  apply iSup_le; intro J
  apply iSup_le; intro u
  apply iSup_le; intro hu
  apply iSup_le; intro hu0
  apply iSup_le; intro huK
  exact Work.Analysis.Variation.sum_jumps_le_incLp 2 (by norm_num) K (Nat.log2 K + 1) hKM a ha0
    u hu huK

/-! ## 4. The `ℓᵖ` bound for one block square function of the walk -/

/-- **The `ℓᵖ` bound for one dyadic block square function of the walk.**  This is the
single-chain block square function bound `singleChain_blockSqSum_le` applied to the chain
`i ↦ min (2^m * i) K`, transported to the `incLp` normalisation. -/
private lemma eLpNorm_incLp_le (ρ : ℝ) (l : ℕ) (m₀ : ℕ) (f : ℤ → ℂ) (p : ENNReal)
    (hp0 : p ≠ 0) (hpt : p ≠ ⊤) {C : ℝ}
    (hC : ∀ (J : ℕ) (N : ℕ → ℕ), Monotone N →
      eLpNorm (fun x : ℤ => (∑' i : ℕ, if i < J then
          ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (N (i + 1)) f x
            - Work.KMTAreas.A7Hi.lpf ρ l m₀ (N i) f x‖ ^ (2 : ℝ) else 0) ^ (1 / 2 : ℝ))
        p Measure.count ≤ ENNReal.ofReal C * eLpNorm f p Measure.count)
    (K m : ℕ) :
    eLpNorm (fun x : ℤ => Work.Analysis.Variation.incLp 2 K (2 ^ m)
        (fun n => Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x
          - Work.KMTAreas.A7Hi.lpf ρ l m₀ 0 f x)) p Measure.count
      ≤ ENNReal.ofReal C * eLpNorm f p Measure.count := by
  set M : ℕ := 2 ^ m with hMdef
  have hM : 0 < M := by rw [hMdef]; positivity
  set N : ℕ → ℕ := fun i => min (M * i) K with hNdef
  have hNmono : Monotone N := by
    intro a b hab
    unfold N
    exact min_le_min (Nat.mul_le_mul_left M hab) le_rfl
  have hmain := hC (Work.Analysis.Variation.nb K M) N hNmono
  have hfun : (fun x : ℤ => Work.Analysis.Variation.incLp 2 K M
        (fun n => Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x
          - Work.KMTAreas.A7Hi.lpf ρ l m₀ 0 f x))
      = fun x : ℤ => ENNReal.ofReal ((∑' i : ℕ, if i < Work.Analysis.Variation.nb K M then
          ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (N (i + 1)) f x
            - Work.KMTAreas.A7Hi.lpf ρ l m₀ (N i) f x‖ ^ (2 : ℝ) else 0) ^ (1 / 2 : ℝ)) := by
    funext x
    set A : ℕ → ℂ := fun n => Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x with hAx
    rw [incLp_eq_ofReal]
    congr 1
    congr 1
    have hterm : ∀ q : ℕ, q < Work.Analysis.Variation.nb K M →
        ‖(A (min (M * (q + 1)) K) - A 0) - (A (M * q) - A 0)‖
          = ‖A (N (q + 1)) - A (N q)‖ := by
      intro q hq
      have h1 : (A (min (M * (q + 1)) K) - A 0) - (A (M * q) - A 0)
          = A (min (M * (q + 1)) K) - A (M * q) := by ring
      rw [h1]
      simp only [hNdef]
      rw [min_mul_of_lt_nb hM hq]
    rw [tsum_eq_sum (s := Finset.range (Work.Analysis.Variation.nb K M))
      (f := fun i => if i < Work.Analysis.Variation.nb K M then
        ‖A (N (i + 1)) - A (N i)‖ ^ (2 : ℝ) else 0) ?_]
    · refine Finset.sum_congr rfl fun q hq => ?_
      rw [if_pos (Finset.mem_range.mp hq), hterm q (Finset.mem_range.mp hq)]
    · intro i hi
      rw [Finset.mem_range, not_lt] at hi
      rw [if_neg (by omega)]
  rw [hfun, eLpNorm_ofReal_eq (g := fun x : ℤ => (∑' i : ℕ,
      if i < Work.Analysis.Variation.nb K M then
        ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (N (i + 1)) f x
          - Work.KMTAreas.A7Hi.lpf ρ l m₀ (N i) f x‖ ^ (2 : ℝ) else 0) ^ (1 / 2 : ℝ))
    (fun x => Real.rpow_nonneg (tsum_nonneg fun i => by split_ifs <;> positivity) _) hp0 hpt]
  exact hmain

/-! ## 5. The target -/

theorem VrBlockLp (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : ℝ) (hr : 2 ≤ r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l m₀ M : ℕ), 1 ≤ M →
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.Variation.Vr r M
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x
            - Work.KMTAreas.A7Hi.lpf ρ l m₀ 0 f x)) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * ((Nat.log2 M : ℝ) + 1))
            * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨Cρc, hCρc, Cc, hCc, hchain⟩ :=
    Work.KMTAreas.A7Lpd.singleChain_blockSqSum_le ρ hρ hρ1 p hp hptop
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hpt : p ≠ ⊤ := ne_of_lt hptop
  refine ⟨Cρc, hCρc, 2 * Cc, by positivity, ?_⟩
  intro l m₀ M _hM hgood f
  -- per-scale block square function bound
  have hblock : ∀ m : ℕ, eLpNorm (fun x : ℤ => Work.Analysis.Variation.incLp 2 M (2 ^ m)
        (fun n => Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x
          - Work.KMTAreas.A7Hi.lpf ρ l m₀ 0 f x)) p Measure.count
      ≤ ENNReal.ofReal Cc * eLpNorm f p Measure.count :=
    fun m => eLpNorm_incLp_le ρ l m₀ f p hp0 hpt
      (fun J N hN => hchain l m₀ hgood f J N hN) M m
  -- Rademacher--Men'shov at the exponent `2`
  have hVr : eLpNorm (fun x : ℤ => Work.Analysis.Variation.Vr 2 M
        (fun n => Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x
          - Work.KMTAreas.A7Hi.lpf ρ l m₀ 0 f x)) p Measure.count
      ≤ ENNReal.ofReal (2 * ((Nat.log2 M + 1 : ℕ) : ℝ) * Cc)
          * eLpNorm f p Measure.count := by
    calc eLpNorm (fun x : ℤ => Work.Analysis.Variation.Vr 2 M
            (fun n => Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x
              - Work.KMTAreas.A7Hi.lpf ρ l m₀ 0 f x)) p Measure.count
        ≤ eLpNorm (fun x : ℤ => ENNReal.ofReal 2 *
            (∑ m ∈ Finset.range (Nat.log2 M + 1),
              Work.Analysis.Variation.incLp 2 M (2 ^ m)
                (fun n => Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x
                  - Work.KMTAreas.A7Hi.lpf ρ l m₀ 0 f x))) p Measure.count :=
          eLpNorm_mono_enorm (hf := by pw_aesm) fun x => by
            rw [enorm_eq_self, enorm_eq_self]
            exact Vr_two_le_sum_incLp M _ (by simp)
      _ = ENNReal.ofReal 2 * eLpNorm (fun x : ℤ =>
            ∑ m ∈ Finset.range (Nat.log2 M + 1),
              Work.Analysis.Variation.incLp 2 M (2 ^ m)
                (fun n => Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x
                  - Work.KMTAreas.A7Hi.lpf ρ l m₀ 0 f x)) p Measure.count :=
          eLpNorm_const_mul_enorm _ ENNReal.ofReal_ne_top hp0 hpt
      _ ≤ ENNReal.ofReal 2 * ∑ m ∈ Finset.range (Nat.log2 M + 1),
            eLpNorm (fun x : ℤ => Work.Analysis.Variation.incLp 2 M (2 ^ m)
              (fun n => Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x
                - Work.KMTAreas.A7Hi.lpf ρ l m₀ 0 f x)) p Measure.count :=
          mul_le_mul_of_nonneg_left (eLpNorm_finset_sum_le' _ _ (le_of_lt hp) hpt) (by positivity)
      _ ≤ ENNReal.ofReal 2 * ∑ _m ∈ Finset.range (Nat.log2 M + 1),
            ENNReal.ofReal Cc * eLpNorm f p Measure.count :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => hblock m) (by positivity)
      _ = ENNReal.ofReal (2 * ((Nat.log2 M + 1 : ℕ) : ℝ) * Cc)
            * eLpNorm f p Measure.count := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [← ENNReal.ofReal_natCast, ← mul_assoc,
            ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
            ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  -- the `Vʳ ≤ V²` comparison and the constant bookkeeping
  have hmono : eLpNorm (fun x : ℤ => Work.Analysis.Variation.Vr r M
        (fun n => Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x
          - Work.KMTAreas.A7Hi.lpf ρ l m₀ 0 f x)) p Measure.count
      ≤ eLpNorm (fun x : ℤ => Work.Analysis.Variation.Vr 2 M
        (fun n => Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x
          - Work.KMTAreas.A7Hi.lpf ρ l m₀ 0 f x)) p Measure.count :=
    eLpNorm_mono_enorm (hf := by pw_aesm) fun x => by
      rw [enorm_eq_self, enorm_eq_self]
      exact Vr_le_Vr_two r hr M _
  refine hmono.trans (hVr.trans ?_)
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
  have h0 : (0:ℝ) ≤ ((Nat.log2 M + 1 : ℕ) : ℝ) := by positivity
  have h1 : ((Nat.log2 M + 1 : ℕ) : ℝ) = (Nat.log2 M : ℝ) + 1 := by push_cast; ring
  rw [h1]
  nlinarith [h0, hCc.le]

end

end Work.KMTAreas.A7LoPoly
