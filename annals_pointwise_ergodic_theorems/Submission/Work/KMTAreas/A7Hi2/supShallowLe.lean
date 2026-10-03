import Mathlib
import Submission.Work.KMTAreas.A7Hi2.cutLevel
import Submission.Work.KMTAreas.A7Lpd.chainBlockVarFull
import Submission.Work.Analysis.Variation.rademacher_menshov_one_dim
import Submission.Work.Analysis.Variation.Basic
import Submission.Work.KMTAreas.A7.lacDilTriVar
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7Hi2

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-!
# The shallow-range values-supremum of the low-pass Ionescu--Wainger walk

The target `supShallowLe` bounds the supremum of `‖lpf ρ l₁ m₀ n f x‖` over the *shallow* range
`m₀ + n < cutLevel ρ l₁` in `ℓᵖ` by `C (1+l₁)² ‖f‖_{ℓᵖ}`.

The proof is the classical dyadic (Rademacher--Men'shov) route, which is *log-lossy in the
truncation* and is therefore exactly adapted to a *truncated* range:

1. `sup_{n ≤ K} ‖a n‖ ≤ 2 V²(a − a 0)` (the two-point chain; `VrFull_le_two_mul_Vr`);
2. the one-dimensional Rademacher--Men'shov inequality
   `V²(a) ≤ 2 Σ_{m ≤ log₂ K} incLp 2 K (2^m) a` (`Vr_two_le_sum_incLp` below, from
   `Work.Analysis.Variation.sum_jumps_le_incLp`), where `incLp 2 K M a` is the `ℓ²`-norm of the
   jumps of `a` across the *dyadic blocks* of size `M`;
3. each of these block square functions is an `ℓᵖ`-bounded "single chain block square function" of
   the walk with an `l₁`-free constant (`Work.KMTAreas.A7Lpd.singleChain_blockSqSum_le`);
4. the number of dyadic scales is `log₂ (cutLevel ρ l₁) + 1 = O(1 + l₁)` (see
   `exists_log2_cutLevel_le`), because `cutLevel ρ l₁ ≲ 2^{C 2^{l₁}}` and
   `Nat.log2 (2^{C 2^{l₁}}) = C 2^{l₁}`, while `2^{l₁} ≤ ... ` — the point is that the number of
   scales is `log₂` of `cutLevel`, hence `O(l₁)`.

The loss is *logarithmic in the truncation*; this is why the argument proves the truncated
(shallow) range and not the full maximal estimate, whose crux needs the `l₁`-free
"maximal ≤ square function" statement. -/

/-! ## Elementary helpers -/

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
private lemma Vr_two_le_sum_incLp (K : ℕ) (a : ℕ → ℂ) (ha0 : a 0 = 0) :
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
  exact Work.Analysis.Variation.sum_jumps_le_incLp 2 (by norm_num) K (Nat.log2 K + 1) hKM a ha0 u hu huK

/-! ## The number of dyadic scales -/

/-- **The number of dyadic scales up to `cutLevel ρ l₁` is `O(1 + l₁)`.**  Since
`iwQl ρ l₁ ≤ 2 ^ (C * 2 ^ l₁)` and `cutLevel ρ l₁ = clog 2 (3 iwQl ρ l₁) + 2`, we have
`cutLevel ρ l₁ ≤ 2 ^ ((N+4)(l₁+1)+10)` for some `N`, whence
`Nat.log2 (cutLevel ρ l₁) + 1 ≤ C (1 + l₁)`. -/
private theorem exists_log2_cutLevel_le (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ l₁ : ℕ,
      (Nat.log2 (cutLevel ρ l₁) + 1 : ℝ) ≤ C * (1 + (l₁ : ℝ)) := by
  obtain ⟨Cq, hCq, hQ⟩ := Work.Analysis.IonescuWainger.iwQl_le hρ hρ1
  obtain ⟨N, hN1, hN4, hNCq⟩ : ∃ N : ℕ, 1 ≤ N ∧ 4 ≤ N ∧ Cq ≤ (N : ℝ) :=
    ⟨⌈Cq⌉₊ + 5, by omega, by omega, by push_cast; linarith [Nat.le_ceil Cq]⟩
  refine ⟨(N : ℝ) + 15, by positivity, fun l₁ => ?_⟩
  have hpow : ((2 ^ (N * 2 ^ l₁) : ℕ) : ℝ) = (2 : ℝ) ^ ((N : ℝ) * (2 : ℝ) ^ (l₁ : ℝ)) := by
    have hcast : ((N * 2 ^ l₁ : ℕ) : ℝ) = (N : ℝ) * (2 : ℝ) ^ (l₁ : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_pow, ← Real.rpow_natCast]
      norm_num
    rw [Nat.cast_pow, ← Real.rpow_natCast, hcast]
    norm_num
  have key : cutLevel ρ l₁ ≤ 2 ^ ((N + 4) * (l₁ + 1) + 10) := by
    have hQnat : Work.Analysis.IonescuWainger.iwQl ρ l₁ ≤ 2 ^ (N * 2 ^ l₁) := by
      have h2 : (2 : ℝ) ^ (Cq * (2 : ℝ) ^ (l₁ : ℝ)) ≤ ((2 ^ (N * 2 ^ l₁) : ℕ) : ℝ) := by
        rw [hpow]
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (l₁ : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_right hNCq hp
      exact_mod_cast (hQ l₁).trans h2
    have h3 : 3 * Work.Analysis.IonescuWainger.iwQl ρ l₁ ≤ 2 ^ (N * 2 ^ l₁ + 2) := by
      calc 3 * Work.Analysis.IonescuWainger.iwQl ρ l₁ ≤ 3 * 2 ^ (N * 2 ^ l₁) :=
            Nat.mul_le_mul_left 3 hQnat
        _ ≤ 2 ^ (N * 2 ^ l₁ + 2) := by
            rw [pow_add]
            nlinarith [Nat.one_le_two_pow (n := N * 2 ^ l₁)]
    have hclog : Nat.clog 2 (3 * Work.Analysis.IonescuWainger.iwQl ρ l₁) ≤ N * 2 ^ l₁ + 2 :=
      (Nat.clog_le_iff_le_pow (by norm_num)).mpr h3
    have hcut : cutLevel ρ l₁ ≤ N * 2 ^ l₁ + 4 := by
      unfold cutLevel
      omega
    refine hcut.trans ?_
    have hexp : (N + 4) * (l₁ + 1) + 10 = N * l₁ + N + 4 * l₁ + 14 := by ring
    rw [hexp, pow_add, pow_add, pow_add]
    have hB : N ≤ 2 ^ N := Nat.le_of_lt Nat.lt_two_pow_self
    have hC : 2 ^ l₁ ≤ 2 ^ (N * l₁) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have hA : N * 2 ^ l₁ ≤ 2 ^ (N * l₁) * 2 ^ N := by
      calc N * 2 ^ l₁ ≤ 2 ^ N * 2 ^ l₁ := Nat.mul_le_mul_right _ hB
        _ ≤ 2 ^ N * 2 ^ (N * l₁) := Nat.mul_le_mul_left _ hC
        _ = 2 ^ (N * l₁) * 2 ^ N := by ring
    have hB4 : (4 : ℕ) ≤ 2 ^ (N * l₁) * 2 ^ N := by
      have h16 : (4 : ℕ) ≤ 2 ^ N := by
        calc (4 : ℕ) ≤ 2 ^ 4 := by norm_num
          _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN4
      calc (4 : ℕ) = 1 * 4 := by ring
        _ ≤ 2 ^ (N * l₁) * 2 ^ N :=
            Nat.mul_le_mul (Nat.one_le_two_pow (n := N * l₁)) h16
    have hX : N * 2 ^ l₁ + 4 ≤ 2 * (2 ^ (N * l₁) * 2 ^ N) := by
      calc N * 2 ^ l₁ + 4 ≤ 2 ^ (N * l₁) * 2 ^ N + 2 ^ (N * l₁) * 2 ^ N :=
            Nat.add_le_add hA hB4
        _ = 2 * (2 ^ (N * l₁) * 2 ^ N) := by ring
    have hY : 2 * (2 ^ (N * l₁) * 2 ^ N)
        ≤ 2 ^ (N * l₁) * 2 ^ N * 2 ^ (4 * l₁) * 2 ^ 14 := by
      have h1 : (1 : ℕ) ≤ 2 ^ (4 * l₁) := Nat.one_le_two_pow
      have h2 : (2 : ℕ) ≤ 2 ^ 14 := by norm_num
      calc 2 * (2 ^ (N * l₁) * 2 ^ N) = (2 ^ (N * l₁) * 2 ^ N) * 2 := by ring
        _ ≤ (2 ^ (N * l₁) * 2 ^ N) * 2 ^ 14 := Nat.mul_le_mul_left _ h2
        _ ≤ (2 ^ (N * l₁) * 2 ^ N) * 2 ^ (4 * l₁) * 2 ^ 14 := by
            have := Nat.mul_le_mul_left ((2 ^ (N * l₁) * 2 ^ N) * 2 ^ 14) h1
            simpa [mul_assoc] using this
        _ = 2 ^ (N * l₁) * 2 ^ N * 2 ^ (4 * l₁) * 2 ^ 14 := by ring
    exact hX.trans hY
  have hlog : (Nat.log2 (cutLevel ρ l₁) : ℝ) ≤ ((N : ℝ) + 4) * ((l₁ : ℝ) + 1) + 10 := by
    have hpos : cutLevel ρ l₁ ≠ 0 := by unfold cutLevel; omega
    have hle : Nat.log2 (cutLevel ρ l₁) ≤ (N + 4) * (l₁ + 1) + 10 := by
      by_contra hcon
      rw [Nat.not_le] at hcon
      have h2 := (Nat.le_log2 hpos).mp (le_of_lt hcon)
      have heq : 2 ^ ((N + 4) * (l₁ + 1) + 10) = cutLevel ρ l₁ := le_antisymm h2 key
      rw [← heq, Nat.log2_two_pow] at hcon
      exact absurd hcon (lt_irrefl _)
    exact_mod_cast hle
  have htarget : ((N : ℝ) + 4) * ((l₁ : ℝ) + 1) + 10 + 1
      ≤ ((N : ℝ) + 15) * (1 + (l₁ : ℝ)) := by
    nlinarith
  calc (Nat.log2 (cutLevel ρ l₁) + 1 : ℝ)
      = (Nat.log2 (cutLevel ρ l₁) : ℝ) + 1 := by norm_num
    _ ≤ (((N : ℝ) + 4) * ((l₁ : ℝ) + 1) + 10) + 1 := by linarith [hlog]
    _ ≤ ((N : ℝ) + 15) * (1 + (l₁ : ℝ)) := htarget

/-! ## The pointwise reduction to the variation -/

/-- **The shallow-range values supremum is dominated by the walk's variation.** -/
private lemma sup_shallow_le_Vr (ρ : ℝ) (l₁ m₀ : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    (⨆ (n : ℕ) (_ : m₀ + n < cutLevel ρ l₁), ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ)
      ≤ ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ
        + 2 * Work.Analysis.Variation.Vr 2 (cutLevel ρ l₁)
            (fun n => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x
              - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x) := by
  set K := cutLevel ρ l₁ with hK
  set A : ℕ → ℂ := fun n => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x with hAdef
  set B : ℕ → ℂ := fun n => A n - A 0 with hBdef
  have hB0 : B 0 = 0 := by simp [hBdef]
  have hle : ∀ n, n ≤ K → ‖B n‖ₑ ≤ (⨆ (n : ℕ) (_ : n ≤ K), ‖B n‖ₑ) := fun n hn =>
    le_trans (le_iSup (fun (_ : n ≤ K) => ‖B n‖ₑ) hn)
      (le_iSup (fun n : ℕ => ⨆ (_ : n ≤ K), ‖B n‖ₑ) n)
  have hleA : ∀ n, n ≤ K → ‖A n‖ₑ ≤ (⨆ (n : ℕ) (_ : n ≤ K), ‖A n‖ₑ) := fun n hn =>
    le_trans (le_iSup (fun (_ : n ≤ K) => ‖A n‖ₑ) hn)
      (le_iSup (fun n : ℕ => ⨆ (_ : n ≤ K), ‖A n‖ₑ) n)
  have hstep1 : (⨆ (n : ℕ) (_ : m₀ + n < K), ‖A n‖ₑ) ≤ (⨆ (n : ℕ) (_ : n ≤ K), ‖A n‖ₑ) := by
    refine iSup_le fun n => iSup_le fun hn => ?_
    exact hleA n (by omega)
  have hstep2 : (⨆ (n : ℕ) (_ : n ≤ K), ‖A n‖ₑ)
      ≤ ‖A 0‖ₑ + ⨆ (n : ℕ) (_ : n ≤ K), ‖B n‖ₑ := by
    refine iSup_le fun n => iSup_le fun hn => ?_
    have hC : ‖A n‖ₑ ≤ ‖A 0‖ₑ + ‖B n‖ₑ := by
      have h := enorm_add_le (A 0) (B n)
      have heq : A 0 + B n = A n := by simp [hBdef]
      rwa [heq] at h
    exact hC.trans (add_le_add le_rfl (hle n hn))
  have hstep3 : (⨆ (n : ℕ) (_ : n ≤ K), ‖B n‖ₑ) ≤ 2 * Work.Analysis.Variation.Vr 2 K B := by
    have h1 : (⨆ (n : ℕ) (_ : n ≤ K), ‖B n‖ₑ) ≤ ⨆ k : Fin (K + 1), ‖B k‖ₑ := by
      refine iSup_le fun n => iSup_le fun hn => ?_
      exact le_iSup (fun k : Fin (K + 1) => ‖B k‖ₑ) ⟨n, by omega⟩
    have h2 : (⨆ k : Fin (K + 1), ‖B k‖ₑ) ≤ Work.Analysis.Variation.VrFull 2 K B := by
      unfold Work.Analysis.Variation.VrFull
      exact le_add_right le_rfl
    have h3 : Work.Analysis.Variation.VrFull 2 K B ≤ 2 * Work.Analysis.Variation.Vr 2 K B :=
      Work.Analysis.Variation.VrFull_le_two_mul_Vr (by norm_num) hB0
    exact h1.trans (h2.trans h3)
  exact le_trans hstep1 (le_trans hstep2 (add_le_add le_rfl hstep3))

/-! ## The per-scale block square function bound -/

/-- **The `ℓᵖ` bound for one dyadic block square function of the walk.**  This is the
single-chain block square function bound `singleChain_blockSqSum_le` applied to the chain
`i ↦ min (2^m * i) K`, transported to the `incLp` normalisation. -/
private lemma eLpNorm_incLp_le (ρ : ℝ) (l₁ m₀ : ℕ) (f : ℤ → ℂ) (p : ENNReal)
    (hp0 : p ≠ 0) (hpt : p ≠ ⊤) {C : ℝ}
    (hC : ∀ (J : ℕ) (N : ℕ → ℕ), Monotone N →
      eLpNorm (fun x : ℤ => (∑' i : ℕ, if i < J then
          ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (N (i + 1)) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (N i) f x‖ ^ (2 : ℝ) else 0) ^ (1 / 2 : ℝ))
        p Measure.count ≤ ENNReal.ofReal C * eLpNorm f p Measure.count)
    (K m : ℕ) :
    eLpNorm (fun x : ℤ => Work.Analysis.Variation.incLp 2 K (2 ^ m)
        (fun n => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x)) p Measure.count
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
        (fun n => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x))
      = fun x : ℤ => ENNReal.ofReal ((∑' i : ℕ, if i < Work.Analysis.Variation.nb K M then
          ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (N (i + 1)) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (N i) f x‖ ^ (2 : ℝ) else 0) ^ (1 / 2 : ℝ)) := by
    funext x
    set A : ℕ → ℂ := fun n => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x with hAx
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
        ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (N (i + 1)) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (N i) f x‖ ^ (2 : ℝ) else 0) ^ (1 / 2 : ℝ))
    (fun x => Real.rpow_nonneg (tsum_nonneg fun i => by split_ifs <;> positivity) _) hp0 hpt]
  exact hmain

/-! ## The target -/

theorem supShallowLe (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ =>
          ⨆ (n : ℕ) (_ : m₀ + n < Work.KMTAreas.A7Hi2.cutLevel ρ l₁),
            ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ)
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨Cρc, hCρc, Cc, hCc, hchain⟩ :=
    Work.KMTAreas.A7Lpd.singleChain_blockSqSum_le ρ hρ hρ1 p hp hptop
  have hp1 : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  obtain ⟨Cρs, hCρs, Cs, hCs, hsingle⟩ :=
    Work.KMTAreas.A7.kmtProj_lp_bound_uniform ρ hρ hρ1 p.toReal hp1
  obtain ⟨Clog, hClog, hlog⟩ := exists_log2_cutLevel_le ρ hρ hρ1
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hpt : p ≠ ⊤ := ne_of_lt hptop
  have hpeq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal (ne_of_lt hptop)
  refine ⟨max Cρc Cρs, lt_max_of_lt_left hCρc, Cs + 4 * Cc * Clog + 1, by positivity, ?_⟩
  intro l₁ m₀ hgood f
  have hgc : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρc l₁ (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono (le_max_left _ _) hgood
  have hgs : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρs l₁ (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono (le_max_right _ _) hgood
  -- pointwise: the shallow sup is at most `‖T_0 f‖ + 2 V²`
  have hpoint : ∀ x : ℤ, (⨆ (n : ℕ) (_ : m₀ + n < cutLevel ρ l₁),
        ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ)
      ≤ ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ
        + 2 * Work.Analysis.Variation.Vr 2 (cutLevel ρ l₁)
            (fun n => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x
              - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x) :=
    fun x => sup_shallow_le_Vr ρ l₁ m₀ f x
  -- Rademacher--Men'shov and the block square functions
  have hblock : ∀ m : ℕ, eLpNorm (fun x : ℤ => Work.Analysis.Variation.incLp 2 (cutLevel ρ l₁) (2 ^ m)
        (fun n => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x)) p Measure.count
      ≤ ENNReal.ofReal Cc * eLpNorm f p Measure.count :=
    fun m => eLpNorm_incLp_le ρ l₁ m₀ f p hp0 hpt
      (fun J N hN => hchain l₁ m₀ hgc f J N hN) (cutLevel ρ l₁) m
  have hVr : eLpNorm (fun x : ℤ => Work.Analysis.Variation.Vr 2 (cutLevel ρ l₁)
        (fun n => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x)) p Measure.count
      ≤ ENNReal.ofReal (2 * ((Nat.log2 (cutLevel ρ l₁) + 1 : ℕ) : ℝ) * Cc)
          * eLpNorm f p Measure.count := by
    calc eLpNorm (fun x : ℤ => Work.Analysis.Variation.Vr 2 (cutLevel ρ l₁)
            (fun n => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x
              - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x)) p Measure.count
        ≤ eLpNorm (fun x : ℤ => ENNReal.ofReal 2 *
            (∑ m ∈ Finset.range (Nat.log2 (cutLevel ρ l₁) + 1),
              Work.Analysis.Variation.incLp 2 (cutLevel ρ l₁) (2 ^ m)
                (fun n => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x
                  - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x))) p Measure.count :=
          eLpNorm_mono_enorm (hf := by pw_aesm) fun x => by
            rw [enorm_eq_self, enorm_eq_self]
            exact Vr_two_le_sum_incLp (cutLevel ρ l₁) _ (by simp)
      _ = ENNReal.ofReal 2 * eLpNorm (fun x : ℤ =>
            ∑ m ∈ Finset.range (Nat.log2 (cutLevel ρ l₁) + 1),
              Work.Analysis.Variation.incLp 2 (cutLevel ρ l₁) (2 ^ m)
                (fun n => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x
                  - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x)) p Measure.count :=
          eLpNorm_const_mul_enorm _ ENNReal.ofReal_ne_top hp0 hpt
      _ ≤ ENNReal.ofReal 2 * ∑ m ∈ Finset.range (Nat.log2 (cutLevel ρ l₁) + 1),
            eLpNorm (fun x : ℤ => Work.Analysis.Variation.incLp 2 (cutLevel ρ l₁) (2 ^ m)
              (fun n => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x
                - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x)) p Measure.count :=
          mul_le_mul_of_nonneg_left (eLpNorm_finset_sum_le' _ _ (le_of_lt hp) hpt) (by positivity)
      _ ≤ ENNReal.ofReal 2 * ∑ _m ∈ Finset.range (Nat.log2 (cutLevel ρ l₁) + 1),
            ENNReal.ofReal Cc * eLpNorm f p Measure.count :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => hblock m) (by positivity)
      _ = ENNReal.ofReal (2 * ((Nat.log2 (cutLevel ρ l₁) + 1 : ℕ) : ℝ) * Cc)
            * eLpNorm f p Measure.count := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [← ENNReal.ofReal_natCast, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
            ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  -- single-scale bound for `T_0`
  have hfirst : eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
        p Measure.count ≤ ENNReal.ofReal Cs * eLpNorm f p Measure.count := by
    have h := hsingle l₁ (-(m₀ : ℤ)) hgs f
    rw [hpeq] at h
    have h0 : Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f
        = Work.KMTContract.kmtProj ρ l₁ (-(m₀ : ℤ)) f := by
      funext y
      simp only [Work.KMTAreas.A7Hi.lpf]
      norm_num
    rw [eLpNorm_enorm_eq_local hp0 hpt, h0]
    exact h
  -- the constant bookkeeping
  have hClog0 : (0 : ℝ) ≤ Clog := hClog.le
  have hCc0 : (0 : ℝ) ≤ Cc := hCc.le
  have hCs0 : (0 : ℝ) ≤ Cs := hCs.le
  have hl0 : (0 : ℝ) ≤ (l₁ : ℝ) := Nat.cast_nonneg l₁
  have h2a : 4 * ((Nat.log2 (cutLevel ρ l₁) + 1 : ℕ) : ℝ) * Cc
      ≤ 4 * Cc * Clog * (1 + (l₁ : ℝ)) := by
    have h := hlog l₁
    rw [Nat.cast_add, Nat.cast_one]
    nlinarith [h, hClog0, hCc0, hl0]
  have hfin : Cs + 4 * Cc * Clog * (1 + (l₁ : ℝ))
      ≤ (Cs + 4 * Cc * Clog + 1) * (1 + (l₁ : ℝ)) ^ 2 := by
    have h2 : (1 : ℝ) ≤ 1 + (l₁ : ℝ) := by linarith
    have h1 : (1 : ℝ) ≤ (1 + (l₁ : ℝ)) ^ 2 := by nlinarith
    have h3 : (1 + (l₁ : ℝ)) ≤ (1 + (l₁ : ℝ)) ^ 2 := by nlinarith [h2]
    have h4 : (0 : ℝ) ≤ (1 + (l₁ : ℝ)) ^ 2 := by positivity
    have hp1 : Cs ≤ Cs * (1 + (l₁ : ℝ)) ^ 2 := by
      simpa using mul_le_mul_of_nonneg_left h1 hCs0
    have hp2 : 4 * Cc * Clog * (1 + (l₁ : ℝ))
        ≤ 4 * Cc * Clog * (1 + (l₁ : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have key1 : Cs + 4 * Cc * Clog * (1 + (l₁ : ℝ))
        ≤ Cs * (1 + (l₁ : ℝ)) ^ 2 + 4 * Cc * Clog * (1 + (l₁ : ℝ)) ^ 2 := by linarith [hp1, hp2]
    have key2 : Cs * (1 + (l₁ : ℝ)) ^ 2 + 4 * Cc * Clog * (1 + (l₁ : ℝ)) ^ 2
        ≤ (Cs + 4 * Cc * Clog + 1) * (1 + (l₁ : ℝ)) ^ 2 := by nlinarith [h4]
    linarith [key1, key2]
  have hmono : eLpNorm (fun x : ℤ => ⨆ (n : ℕ) (_ : m₀ + n < cutLevel ρ l₁),
        ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ) p Measure.count
      ≤ eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ
          + 2 * Work.Analysis.Variation.Vr 2 (cutLevel ρ l₁)
              (fun n => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x
                - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x)) p Measure.count :=
    eLpNorm_mono_enorm (hf := by pw_aesm) fun x => by
      rw [enorm_eq_self, enorm_eq_self]
      exact hpoint x
  refine hmono.trans ?_
  · have hconst : (2 : ℝ≥0∞) * ENNReal.ofReal (2 * ((Nat.log2 (cutLevel ρ l₁) + 1 : ℕ) : ℝ) * Cc)
        = ENNReal.ofReal (4 * (((Nat.log2 (cutLevel ρ l₁) + 1 : ℕ) : ℝ) * Cc)) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    have hvr2 : eLpNorm (fun x : ℤ => 2 * Work.Analysis.Variation.Vr 2 (cutLevel ρ l₁)
            (fun n => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x
              - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x)) p Measure.count
        ≤ ENNReal.ofReal (4 * (((Nat.log2 (cutLevel ρ l₁) + 1 : ℕ) : ℝ) * Cc))
            * eLpNorm f p Measure.count := by
      calc eLpNorm (fun x : ℤ => 2 * Work.Analysis.Variation.Vr 2 (cutLevel ρ l₁)
              (fun n => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x
                - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x)) p Measure.count
          = (2 : ℝ≥0∞) * eLpNorm (fun x : ℤ => Work.Analysis.Variation.Vr 2 (cutLevel ρ l₁)
              (fun n => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x
                - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x)) p Measure.count :=
            eLpNorm_const_mul_enorm (2 : ℝ≥0∞) (by norm_num) hp0 hpt
        _ ≤ (2 : ℝ≥0∞) * (ENNReal.ofReal (2 * ((Nat.log2 (cutLevel ρ l₁) + 1 : ℕ) : ℝ) * Cc)
              * eLpNorm f p Measure.count) :=
            mul_le_mul_of_nonneg_left hVr (by positivity)
        _ = ENNReal.ofReal (4 * (((Nat.log2 (cutLevel ρ l₁) + 1 : ℕ) : ℝ) * Cc))
              * eLpNorm f p Measure.count := by rw [← mul_assoc, hconst]
    have hsum : eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ) p Measure.count
          + eLpNorm (fun x : ℤ => 2 * Work.Analysis.Variation.Vr 2 (cutLevel ρ l₁)
              (fun n => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x
                - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x)) p Measure.count
        ≤ ENNReal.ofReal (Cs + 4 * (((Nat.log2 (cutLevel ρ l₁) + 1 : ℕ) : ℝ) * Cc))
            * eLpNorm f p Measure.count := by
      rw [ENNReal.ofReal_add hCs0 (by positivity), add_mul]
      exact add_le_add hfirst hvr2
    have hfinal : Cs + 4 * (((Nat.log2 (cutLevel ρ l₁) + 1 : ℕ) : ℝ) * Cc)
        ≤ (Cs + 4 * Cc * Clog + 1) * (1 + (l₁ : ℝ)) ^ 2 := by
      nlinarith [h2a, hfin]
    calc eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ
            + 2 * Work.Analysis.Variation.Vr 2 (cutLevel ρ l₁)
                (fun n => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x
                  - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x)) p Measure.count
        ≤ eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ) p Measure.count
            + eLpNorm (fun x : ℤ => 2 * Work.Analysis.Variation.Vr 2 (cutLevel ρ l₁)
                (fun n => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x
                  - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x)) p Measure.count :=
          Work.KMTAreas.A7.eLpNorm_add_le_ennreal (le_of_lt hp) hpt (μ := Measure.count)
      _ ≤ ENNReal.ofReal (Cs + 4 * (((Nat.log2 (cutLevel ρ l₁) + 1 : ℕ) : ℝ) * Cc))
            * eLpNorm f p Measure.count := hsum
      _ ≤ ENNReal.ofReal ((Cs + 4 * Cc * Clog + 1) * (1 + (l₁ : ℝ)) ^ 2)
            * eLpNorm f p Measure.count :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hfinal) bot_le

end

end Work.KMTAreas.A7Hi2
