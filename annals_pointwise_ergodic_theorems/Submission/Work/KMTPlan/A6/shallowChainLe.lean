import Mathlib
import Submission.Work.KMTAreas.A7Hi2.cutLevel
import Submission.Work.KMTAreas.A7HiRep.chainPartSqFunLeTwo
import Submission.Work.KMTAreas.A7HiRep.chainPartSqFunPosAux
import Submission.Work.KMTAreas.A7Lpd.chainBlockVarFull
import Submission.Work.Analysis.Variation.rademacher_menshov_one_dim
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## Elementary `ℝ≥0∞` bookkeeping -/

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

/-! ## The dyadic increment functional -/

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

/-- Subtracting a constant from a sequence does not change its `ℓ²`-increment functional: the
increments are unchanged. -/
private lemma incLp_sub_const (r : ℝ) (K M : ℕ) (a : ℕ → ℂ) (z : ℂ) :
    Work.Analysis.Variation.incLp r K M (fun n : ℕ => a n - z)
      = Work.Analysis.Variation.incLp r K M a := by
  unfold Work.Analysis.Variation.incLp
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  ring

/-! ## The one-dimensional Rademacher--Men'shov inequality -/

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
  exact Work.Analysis.Variation.sum_jumps_le_incLp 2 (by norm_num) K (Nat.log2 K + 1) hKM a ha0
    u hu huK

/-! ## The chain part of a frozen walk -/

/-- **The `ℓ^r` norm of the jumps of a sequence along a chain in `[0, M]` is at most `Vr r M`.**
The chain `w` need not start at `0`; prepending `0` to it adds one nonnegative jump, which is why
`Vr` (anchored at `0`) still dominates.  (A local copy of the private lemma of
`Work.KMTAreas.A7LoPoly.chainPartHeadLe`.) -/
private lemma ofReal_norm_toLp_jumps_le_Vr (r : NNReal) (hr : 1 ≤ r) (c : ℕ → ℂ) (M J : ℕ)
    (w : ℕ → ℕ) (hw : Monotone w) (hwle : ∀ k : ℕ, w k ≤ M) :
    ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J => c (w ((i : ℕ) + 1)) - c (w (i : ℕ)))‖
      ≤ Work.Analysis.Variation.Vr (r : ℝ) M c := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  rw [Work.KMTAreas.A7.ofReal_norm_toLp_eq_sum r hr]
  -- the chain `0, w 0, w 1, …, w J` of `Vr` (with `J + 1` jumps)
  let u : Fin (J + 2) → ℕ := fun i => if (i : ℕ) = 0 then 0 else w ((i : ℕ) - 1)
  have hua : ∀ i : Fin (J + 2), u i = (if (i : ℕ) = 0 then 0 else w ((i : ℕ) - 1)) :=
    fun i => rfl
  have hu0 : u 0 = 0 := by rw [hua]; simp
  have hus : ∀ k : Fin (J + 1), u k.succ = w (k : ℕ) := by
    intro k
    rw [hua]
    simp
  have humono : Monotone u := by
    rw [Fin.monotone_iff_le_succ]
    intro i
    rw [hus i, hua i.castSucc, Fin.val_castSucc]
    by_cases hi : (i : ℕ) = 0
    · rw [if_pos hi]
      exact Nat.zero_le _
    · rw [if_neg hi]
      exact hw (Nat.sub_le _ _)
  have hule : ∀ i : Fin (J + 2), u i ≤ M := by
    intro i
    rw [hua i]
    by_cases hi : (i : ℕ) = 0
    · rw [if_pos hi]
      exact Nat.zero_le _
    · rw [if_neg hi]
      exact hwle _
  -- the `Vr` chain sum covers our chain sum
  have hsum_le : (∑ i : Fin J, ‖c (w ((i : ℕ) + 1)) - c (w (i : ℕ))‖ₑ ^ (r : ℝ))
      ≤ ∑ j : Fin (J + 1), ‖c (u j.succ) - c (u j.castSucc)‖ₑ ^ (r : ℝ) := by
    rw [Fin.sum_univ_succ]
    have heq : (∑ i : Fin J, ‖c (w ((i : ℕ) + 1)) - c (w (i : ℕ))‖ₑ ^ (r : ℝ))
        = ∑ k : Fin J, ‖c (u (k.succ).succ) - c (u (k.succ).castSucc)‖ₑ ^ (r : ℝ) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 : u ((k.succ).succ) = w ((k : ℕ) + 1) := hus k.succ
      have h2 : u ((k.succ).castSucc) = w (k : ℕ) := hus k.castSucc
      rw [h1, h2]
    rw [heq]
    exact le_add_left le_rfl
  calc (∑ i : Fin J, ‖c (w ((i : ℕ) + 1)) - c (w (i : ℕ))‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ))
      ≤ (∑ j : Fin (J + 1), ‖c (u j.succ) - c (u j.castSucc)‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ)) :=
        ENNReal.rpow_le_rpow hsum_le (by positivity)
    _ ≤ Work.Analysis.Variation.Vr (r : ℝ) M c := by
        rw [Work.Analysis.Variation.Vr]
        exact le_iSup_of_le (J + 1) (le_iSup_of_le u (le_iSup_of_le humono
          (le_iSup_of_le hu0 (le_iSup_of_le hule le_rfl))))

/-- **The chain part of a walk frozen at a level `M` is controlled by its head `2`-variation.**
If `c` does not see the level `M` (`c (min n M) = c n`) then every chain of `chainPart` may be
clamped at `M`, realising the same jump vector along a monotone chain with values in `[0, M]`. -/
private lemma chainPart_two_le_Vr_frozen (M : ℕ) (c : ℕ → ℂ) (hc : ∀ n, c (min n M) = c n) :
    Work.KMTAreas.A7Hi.chainPart 2 c ≤ Work.Analysis.Variation.Vr 2 M c := by
  unfold Work.KMTAreas.A7Hi.chainPart
  refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
  have hw : Monotone (fun k : ℕ => min (N k) M) := fun a b hab => min_le_min (hN hab) le_rfl
  have hwle : ∀ k : ℕ, min (N k) M ≤ M := fun k => min_le_right _ _
  have hjeq : (fun i : Fin J => c (N (i + 1)) - c (N i))
      = (fun i : Fin J => c (min (N ((i : ℕ) + 1)) M) - c (min (N (i : ℕ)) M)) := by
    funext i
    rw [hc (N ((i : ℕ) + 1)), hc (N (i : ℕ))]
  rw [hjeq]
  exact ofReal_norm_toLp_jumps_le_Vr (2 : NNReal) (by norm_num) c M J
    (fun k : ℕ => min (N k) M) hw hwle

/-! ## The pointwise reduction of the frozen chain part to the block square functions -/

/-- **The chain part of the frozen walk is dominated by the dyadic block square functions of the
frozen walk.**  Anchoring at `0` (`c = b - b 0`) and applying Rademacher--Men'shov. -/
private lemma chainPart_frozen_le (ρ : ℝ) (l₁ m₀ M : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    Work.KMTAreas.A7Hi.chainPart 2
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (min m M) f x)
      ≤ ENNReal.ofReal 2 * ∑ m ∈ Finset.range (Nat.log2 M + 1),
          Work.Analysis.Variation.incLp 2 M (2 ^ m)
            (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (min n M) f x) := by
  set a : ℕ → ℂ := fun n => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x with ha
  set b : ℕ → ℂ := fun n => a (min n M) with hb
  set c : ℕ → ℂ := fun n => b n - a 0 with hcdef
  have hb0 : b 0 = a 0 := by
    simp only [hb]
    rw [show min 0 M = 0 from min_eq_left (Nat.zero_le M)]
  have hc0 : c 0 = 0 := by
    simp only [hcdef, hb0]
    exact sub_self (a 0)
  have hfrozen : ∀ n, c (min n M) = c n := by
    intro n
    simp only [hcdef, hb, ha]
    rw [show min (min n M) M = min n M from by rw [min_assoc, min_self]]
  have hchain : Work.KMTAreas.A7Hi.chainPart 2 b = Work.KMTAreas.A7Hi.chainPart 2 c := by
    rw [← Work.KMTAreas.A7HiRep.chainPart_add_const 2 (-(a 0)) b]
    congr 1
    funext m
    rw [hcdef]
    ring
  have hinc : ∀ m : ℕ, Work.Analysis.Variation.incLp 2 M (2 ^ m) c
      = Work.Analysis.Variation.incLp 2 M (2 ^ m) b :=
    fun m => incLp_sub_const 2 M (2 ^ m) b (a 0)
  calc Work.KMTAreas.A7Hi.chainPart 2 b
      = Work.KMTAreas.A7Hi.chainPart 2 c := hchain
    _ ≤ Work.Analysis.Variation.Vr 2 M c := chainPart_two_le_Vr_frozen M c hfrozen
    _ ≤ ENNReal.ofReal 2 * ∑ m ∈ Finset.range (Nat.log2 M + 1),
          Work.Analysis.Variation.incLp 2 M (2 ^ m) c := Vr_two_le_sum_incLp M c hc0
    _ = ENNReal.ofReal 2 * ∑ m ∈ Finset.range (Nat.log2 M + 1),
          Work.Analysis.Variation.incLp 2 M (2 ^ m) b := by
        refine congrArg (fun t => ENNReal.ofReal 2 * t) ?_
        exact Finset.sum_congr rfl fun m _ => hinc m

/-! ## The `ℓᵖ` bound for one dyadic block square function of the frozen walk -/

/-- **The `ℓᵖ` bound for one dyadic block square function of the frozen walk.**  This is the
single-chain block square function bound `singleChain_blockSqSum_le` applied to the chain
`i ↦ min (2^m * i) M`, transported to the `incLp` normalisation. -/
private lemma eLpNorm_incLp_le (ρ : ℝ) (l₁ m₀ M : ℕ) (f : ℤ → ℂ) (p : ENNReal)
    (hp0 : p ≠ 0) (hpt : p ≠ ⊤) {C : ℝ}
    (hC : ∀ (J : ℕ) (N : ℕ → ℕ), Monotone N →
      eLpNorm (fun x : ℤ => (∑' i : ℕ, if i < J then
          ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (N (i + 1)) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (N i) f x‖ ^ (2 : ℝ) else 0) ^ (1 / 2 : ℝ))
        p Measure.count ≤ ENNReal.ofReal C * eLpNorm f p Measure.count)
    (m : ℕ) :
    eLpNorm (fun x : ℤ => Work.Analysis.Variation.incLp 2 M (2 ^ m)
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (min n M) f x)) p Measure.count
      ≤ ENNReal.ofReal C * eLpNorm f p Measure.count := by
  set Mb : ℕ := 2 ^ m with hMdef
  have hB : 0 < Mb := by rw [hMdef]; positivity
  set N : ℕ → ℕ := fun i => min (Mb * i) M with hNdef
  have hNmono : Monotone N := fun a b hab => min_le_min (Nat.mul_le_mul_left Mb hab) le_rfl
  have hmain := hC (Work.Analysis.Variation.nb M Mb) N hNmono
  have hfun : (fun x : ℤ => Work.Analysis.Variation.incLp 2 M Mb
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (min n M) f x))
      = fun x : ℤ => ENNReal.ofReal ((∑' i : ℕ,
          if i < Work.Analysis.Variation.nb M Mb then
            ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (N (i + 1)) f x
              - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (N i) f x‖ ^ (2 : ℝ) else 0)
          ^ (1 / 2 : ℝ)) := by
    funext x
    rw [incLp_eq_ofReal]
    congr 1
    congr 1
    have hterm : ∀ q : ℕ, q < Work.Analysis.Variation.nb M Mb →
        ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (min (min (Mb * (q + 1)) M) M) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (min (Mb * q) M) f x‖
          = ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (N (q + 1)) f x
              - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (N q) f x‖ := by
      intro q _
      simp only [hNdef]
      rw [show min (min (Mb * (q + 1)) M) M = min (Mb * (q + 1)) M from by
        rw [min_assoc, min_self]]
    rw [tsum_eq_sum (s := Finset.range (Work.Analysis.Variation.nb M Mb))
      (f := fun i : ℕ => if i < Work.Analysis.Variation.nb M Mb then
        ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (N (i + 1)) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (N i) f x‖ ^ (2 : ℝ) else 0) ?_]
    · refine Finset.sum_congr rfl fun q hq => ?_
      rw [if_pos (Finset.mem_range.mp hq), hterm q (Finset.mem_range.mp hq)]
    · intro i hi
      rw [Finset.mem_range, not_lt] at hi
      rw [if_neg (by omega)]
  rw [hfun, eLpNorm_ofReal_eq (g := fun x : ℤ => (∑' i : ℕ,
      if i < Work.Analysis.Variation.nb M Mb then
        ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (N (i + 1)) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (N i) f x‖ ^ (2 : ℝ) else 0) ^ (1 / 2 : ℝ))
    (fun x => Real.rpow_nonneg (tsum_nonneg fun i => by split_ifs <;> positivity) _) hp0 hpt]
  exact hmain

/-! ## The number of dyadic scales -/

/-- **The number of dyadic scales up to `cutLevel ρ l₁` is `O(1 + l₁)`.**  Since
`iwQl ρ l₁ ≤ 2 ^ (C * 2 ^ l₁)` and `cutLevel ρ l₁ = clog 2 (3 iwQl ρ l₁) + 2`, we have
`cutLevel ρ l₁ ≤ 2 ^ ((N+4)(l₁+1)+10)` for some `N`, whence
`Nat.log2 (cutLevel ρ l₁) + 1 ≤ C (1 + l₁)`. -/
private theorem exists_log2_cutLevel_le (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ l₁ : ℕ,
      (Nat.log2 (Work.KMTAreas.A7Hi2.cutLevel ρ l₁) + 1 : ℝ) ≤ C * (1 + (l₁ : ℝ)) := by
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
  have key : Work.KMTAreas.A7Hi2.cutLevel ρ l₁ ≤ 2 ^ ((N + 4) * (l₁ + 1) + 10) := by
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
    have hcut : Work.KMTAreas.A7Hi2.cutLevel ρ l₁ ≤ N * 2 ^ l₁ + 4 := by
      unfold Work.KMTAreas.A7Hi2.cutLevel
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
  have hlog : (Nat.log2 (Work.KMTAreas.A7Hi2.cutLevel ρ l₁) : ℝ)
      ≤ ((N : ℝ) + 4) * ((l₁ : ℝ) + 1) + 10 := by
    have hpos : Work.KMTAreas.A7Hi2.cutLevel ρ l₁ ≠ 0 := by
      unfold Work.KMTAreas.A7Hi2.cutLevel; omega
    have hle : Nat.log2 (Work.KMTAreas.A7Hi2.cutLevel ρ l₁) ≤ (N + 4) * (l₁ + 1) + 10 := by
      by_contra hcon
      rw [Nat.not_le] at hcon
      have h2 := (Nat.le_log2 hpos).mp (le_of_lt hcon)
      have heq : 2 ^ ((N + 4) * (l₁ + 1) + 10) = Work.KMTAreas.A7Hi2.cutLevel ρ l₁ :=
        le_antisymm h2 key
      rw [← heq, Nat.log2_two_pow] at hcon
      exact absurd hcon (lt_irrefl _)
    exact_mod_cast hle
  have htarget : ((N : ℝ) + 4) * ((l₁ : ℝ) + 1) + 10 + 1
      ≤ ((N : ℝ) + 15) * (1 + (l₁ : ℝ)) := by
    nlinarith
  calc (Nat.log2 (Work.KMTAreas.A7Hi2.cutLevel ρ l₁) + 1 : ℝ)
      = (Nat.log2 (Work.KMTAreas.A7Hi2.cutLevel ρ l₁) : ℝ) + 1 := by norm_num
    _ ≤ (((N : ℝ) + 4) * ((l₁ : ℝ) + 1) + 10) + 1 := by linarith [hlog]
    _ ≤ ((N : ℝ) + 15) * (1 + (l₁ : ℝ)) := htarget

/-! ## The target -/

/-- **The shallow-range chain bound for the Ionescu--Wainger low-pass walk.**

For `0 < ρ ≤ 1`, `2 < r`, `1 < p < ∞` there are `Cρ > 0` and `C > 0` such that for every `l₁`,
every base level `m₀`, every *frozen* level `M ≤ cutLevel ρ l₁` on the good major arcs
`GoodMajorArcs ρ Cρ l₁ (-(m₀:ℤ))` and every `f : ℤ → ℂ`,

  `‖ chainPart r (m ↦ lpf ρ l₁ m₀ (min m M) f) ‖_{ℓᵖ(ℤ)} ≤ ofReal (C * (1+l₁)) * ‖f‖_{ℓᵖ(ℤ)}`,

i.e. the chain part of the walk truncated (frozen) at a level `M` below the decimation cut
`cutLevel ρ l₁ = Nat.clog 2 (3 * iwQl ρ l₁) + 2` is controlled with only a *linear* loss in `l₁`.

Route (this is the `Vr`-analogue of the PROVED `Work.KMTAreas.A7Hi2.supShallowLe`):

* `chainPart r a ≤ chainPart 2 a` for `2 ≤ r` (`Work.KMTAreas.A7HiRep.chainPart_two_mono_exp`);
* the frozen walk only sees `[0, M]`, so `chainPart 2 b = chainPart 2 (b - b 0)` and the clamped
  chain argument gives `chainPart 2 (b - b 0) ≤ Vr 2 M (b - b 0)`;
* the one-dimensional Rademacher--Men'shov inequality
  `Vr 2 M c ≤ 2 * Σ_{m ≤ log₂ M} incLp 2 M (2^m) c`
  (`Work.Analysis.Variation.sum_jumps_le_incLp`), for the anchored sequence `c = b - b 0`;
* each dyadic block term `incLp 2 M (2^m) b` is the `ℓ²`-block-jump functional of the walk `b`
  along the monotone chain `i ↦ min (2^m * i) M`, so its `ℓᵖ` norm is at most `C * ‖f‖_p` with `C`
  free of `l₁, m₀, M` by `Work.KMTAreas.A7Lpd.singleChain_blockSqSum_le`;
* the number of dyadic scales is `log₂ M + 1 ≤ log₂ (cutLevel ρ l₁) + 1 ≲ 1 + l₁`, from
  `Work.Analysis.IonescuWainger.iwQl_le`. -/
theorem shallowChainLe (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ M : ℕ),
      M ≤ Work.KMTAreas.A7Hi2.cutLevel ρ l₁ →
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (min m M) f x))
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ))) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨Cρ, hCρ, Cc, hCc, hchain⟩ :=
    Work.KMTAreas.A7Lpd.singleChain_blockSqSum_le ρ hρ hρ1 p hp hptop
  obtain ⟨Clog, hClog, hlog⟩ := exists_log2_cutLevel_le ρ hρ hρ1
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hpt : p ≠ ⊤ := ne_of_lt hptop
  have hp1 : 1 ≤ p := le_of_lt hp
  refine ⟨Cρ, hCρ, 2 * Cc * Clog, by positivity, ?_⟩
  intro l₁ m₀ M hM hgood f
  -- the good-arc hypothesis descends to the constants of `singleChain_blockSqSum_le`
  have hgc : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) := hgood
  -- the pointwise bound by the dyadic block square functions
  have hpoint : ∀ x : ℤ,
      Work.KMTAreas.A7Hi.chainPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (min m M) f x)
        ≤ ENNReal.ofReal 2 * ∑ m ∈ Finset.range (Nat.log2 M + 1),
            Work.Analysis.Variation.incLp 2 M (2 ^ m)
              (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (min n M) f x) :=
    fun x => (Work.KMTAreas.A7HiRep.chainPart_two_mono_exp r (le_of_lt hr) _).trans
      (chainPart_frozen_le ρ l₁ m₀ M f x)
  -- the per-scale `ℓᵖ` bound
  have hblock : ∀ m : ℕ, eLpNorm (fun x : ℤ => Work.Analysis.Variation.incLp 2 M (2 ^ m)
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (min n M) f x)) p Measure.count
      ≤ ENNReal.ofReal Cc * eLpNorm f p Measure.count :=
    fun m => eLpNorm_incLp_le ρ l₁ m₀ M f p hp0 hpt
      (fun J N hN => hchain l₁ m₀ hgc f J N hN) m
  -- the sum over the dyadic scales, as a local abbreviation (so that the `eLpNorm` arguments below
  -- stay small)
  set Sfun : ℤ → ℝ≥0∞ := fun x => ∑ m ∈ Finset.range (Nat.log2 M + 1),
      Work.Analysis.Variation.incLp 2 M (2 ^ m)
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (min n M) f x) with hSdef
  -- the `ℓᵖ` bound for the sum over the dyadic scales
  have hS : eLpNorm Sfun p Measure.count
      ≤ ENNReal.ofReal (((Nat.log2 M + 1 : ℕ) : ℝ) * Cc) * eLpNorm f p Measure.count := by
    rw [hSdef]
    refine (eLpNorm_finset_sum_le' (Finset.range (Nat.log2 M + 1))
      (fun m (x : ℤ) => Work.Analysis.Variation.incLp 2 M (2 ^ m)
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (min n M) f x)) hp1 hpt).trans ?_
    refine (Finset.sum_le_sum fun m _ => hblock m).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  -- the number of dyadic scales is `O(1 + l₁)`
  have hlogM : (Nat.log2 M : ℝ) + 1 ≤ Clog * (1 + (l₁ : ℝ)) := by
    have h1 : (Nat.log2 M : ℝ) + 1 ≤ (Nat.log2 (Work.KMTAreas.A7Hi2.cutLevel ρ l₁) : ℝ) + 1 := by
      have h2 : Nat.log2 M ≤ Nat.log2 (Work.KMTAreas.A7Hi2.cutLevel ρ l₁) := by
        rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
        exact Nat.log_mono (b := 2) (c := 2) (m := M)
          (n := Work.KMTAreas.A7Hi2.cutLevel ρ l₁) (by norm_num) le_rfl hM
      have h3 : (Nat.log2 M : ℝ) ≤ (Nat.log2 (Work.KMTAreas.A7Hi2.cutLevel ρ l₁) : ℝ) := by
        exact_mod_cast h2
      linarith
    exact h1.trans (hlog l₁)
  -- the monotonicity of `eLpNorm` and the final bookkeeping
  have hmono : eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (min m M) f x)) p Measure.count
      ≤ eLpNorm (fun x : ℤ => ENNReal.ofReal 2 * Sfun x) p Measure.count := by
    refine eLpNorm_mono_enorm (hf := by pw_aesm) fun x => ?_
    rw [enorm_eq_self, enorm_eq_self]
    exact hpoint x
  have hT : eLpNorm (fun x : ℤ => ENNReal.ofReal 2 * Sfun x) p Measure.count
      = ENNReal.ofReal 2 * eLpNorm Sfun p Measure.count :=
    eLpNorm_const_mul_enorm _ ENNReal.ofReal_ne_top hp0 hpt
  have hstep : ENNReal.ofReal 2 * eLpNorm Sfun p Measure.count
      ≤ ENNReal.ofReal ((2 * Cc * Clog) * (1 + (l₁ : ℝ))) * eLpNorm f p Measure.count := by
    have ha := mul_le_mul_of_nonneg_left hS (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal 2)
    have hb : ENNReal.ofReal 2 * (ENNReal.ofReal (((Nat.log2 M + 1 : ℕ) : ℝ) * Cc)
            * eLpNorm f p Measure.count)
        = ENNReal.ofReal (2 * (((Nat.log2 M + 1 : ℕ) : ℝ) * Cc))
            * eLpNorm f p Measure.count := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hc : 2 * (((Nat.log2 M + 1 : ℕ) : ℝ) * Cc) ≤ (2 * Cc * Clog) * (1 + (l₁ : ℝ)) := by
      have hcast : ((Nat.log2 M + 1 : ℕ) : ℝ) = (Nat.log2 M : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      nlinarith [hlogM, hCc.le, hClog.le, (by positivity : (0 : ℝ) ≤ (l₁ : ℝ))]
    exact ha.trans (hb.le.trans
      (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hc) bot_le))
  exact hmono.trans (hT.le.trans hstep)

end

end Work.KMTPlan.A6
