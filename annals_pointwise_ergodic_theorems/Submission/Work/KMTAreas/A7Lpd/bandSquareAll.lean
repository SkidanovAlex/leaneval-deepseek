import Mathlib
import Submission.Work.KMTAreas.A7Hi.LowpassDefs
import Submission.Work.KMTAreas.A7Hi.FiberOpUniformLp
import Submission.Work.KMTAreas.A7.sqSum_lintegral_le_uniformSigns_noLin
import Submission.Work.KMTAreas.A7.isLqMultiplierBound_of_mikhlin
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7Lpd

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## The real-valued square sum versus the `ℝ≥0∞`-valued one

The band square function of the statement is the *real-valued* quantity
`(∑'_k ‖Δ_k f x‖ ^ 2) ^ (1/2)`, whereas the Khintchine/Marcinkiewicz--Zygmund engine
(`Work.KMTAreas.A7.sqSum_lintegral_le_uniformSigns_noLin`) and the Ionescu--Wainger
square-function bound `Work.KMTAreas.A7Hi.sqFun` are phrased with the `ℝ≥0∞`-valued norms
`‖·‖ₑ`.  The two agree whenever the real series is summable and the `ℝ≥0∞` one is the larger
otherwise (the real `tsum` of a non-summable non-negative family is `0` by definition), so the
real-valued square function is dominated pointwise by the `ℝ≥0∞`-valued one. -/

/-- `ofReal` of an arbitrary `tsum` of non-negative reals is at most the `ℝ≥0∞`-`tsum` of the
`ofReal`s (with equality when the real family is summable). -/
lemma ofReal_tsum_le_of_nonneg (b : ℕ → ℝ) (hb : ∀ k, 0 ≤ b k) :
    ENNReal.ofReal (∑' k, b k) ≤ ∑' k, ENNReal.ofReal (b k) := by
  by_cases hS : Summable b
  · rw [ENNReal.ofReal_tsum_of_nonneg hb hS]
  · rw [tsum_eq_zero_of_not_summable hS, ENNReal.ofReal_zero]
    exact zero_le

/-- The pointwise comparison of the two square functions. -/
lemma ofReal_sqSum_le_ennSqSum (z : ℕ → ℂ) :
    ENNReal.ofReal ((∑' k : ℕ, ‖z k‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
      ≤ (∑' k : ℕ, ‖z k‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hSnn : 0 ≤ ∑' k : ℕ, ‖z k‖ ^ (2 : ℝ) := tsum_nonneg (fun k => by positivity)
  rw [← ENNReal.ofReal_rpow_of_nonneg hSnn (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  refine le_trans (ofReal_tsum_le_of_nonneg _ (fun k => by positivity)) (le_of_eq ?_)
  exact tsum_congr (fun k => by
    rw [show ‖z k‖ₑ = ENNReal.ofReal ‖z k‖ by simp,
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)])

/-- **The `eLpNorm` comparison.**  The `ℓᵖ`-norm of the real-valued band square function of a
family `z` is at most the `ℓᵖ`-norm of its `ℝ≥0∞`-valued counterpart. -/
lemma eLpNorm_sqSum_le_eLpNorm_ennSqSum (p : ENNReal) (hp0 : p ≠ 0) (hptop : p ≠ ⊤)
    (z : ℕ → ℤ → ℂ) :
    MeasureTheory.eLpNorm (fun x : ℤ => (∑' k : ℕ, ‖z k x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) p
        MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm
          (fun x : ℤ => (∑' k : ℕ, ‖z k x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) p
          MeasureTheory.Measure.count := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hptop,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hptop]
  refine ENNReal.rpow_le_rpow (lintegral_mono fun x => ?_) (by positivity)
  rw [Real.enorm_eq_ofReal (by positivity), enorm_eq_self]
  exact ENNReal.rpow_le_rpow (ofReal_sqSum_le_ennSqSum (fun k => z k x))
    (by positivity)

/-! ## Elementary facts about the arcs and the rescaled cutoffs -/

/-- The arcs `ℝ_{≤k}` are monotone in `k`. -/
private lemma realArc_mono {j i : ℤ} (h : j ≤ i) :
    Work.Analysis.IonescuWainger.realArc j ⊆ Work.Analysis.IonescuWainger.realArc i := by
  have hj : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ i := zpow_le_zpow_right₀ (by norm_num) h
  intro x hx
  rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc] at hx ⊢
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- Membership in `realArc` from non-vanishing of `etaCutSchwartz`. -/
private lemma mem_realArc_of_etaCutSchwartz {k : ℤ} {x : ℝ}
    (h : (Work.KMTAreas.A7.etaCutSchwartz k : ℝ → ℂ) x ≠ 0) :
    x ∈ Work.Analysis.IonescuWainger.realArc k := by
  rw [Work.KMTAreas.A7.etaCutSchwartz_coe] at h
  exact Work.KMTAreas.A7.etaCut_ne_zero_mem_realArc k h

/-- The rescaled cutoff at the negative index `-j` is the dilation `η(2^j ·)`. -/
private lemma etaCut_neg_eq (j : ℕ) (ξ : ℝ) :
    Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-((j : ℤ))) ξ
      = Work.KMTContract.kmtEta ((2 : ℝ) ^ j * ξ) := by
  rw [Work.Analysis.IonescuWainger.etaCut, zpow_neg, zpow_natCast, div_inv_eq_mul, mul_comm]

/-- The same, in the index convention `-((m₀ : ℤ) + (m : ℤ))`. -/
private lemma etaCut_ann_eq (m₀ m : ℕ) (ξ : ℝ) :
    Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-((m₀ : ℤ) + (m : ℤ))) ξ
      = Work.KMTContract.kmtEta ((2 : ℝ) ^ (m₀ + m) * ξ) := by
  have h : (-((m₀ : ℤ) + (m : ℤ)) : ℤ) = -(((m₀ + m : ℕ)) : ℤ) := by push_cast; ring
  rw [h, etaCut_neg_eq]

/-! ## Operator linearity of `Tle` in a difference of two narrow symbols -/

/-- For a bounded input, `Tle` is additive in the *difference* of two narrow Schwartz symbols. -/
private lemma Tle_sub_of_bounded (ρ : ℝ) (l : ℕ) (k : ℤ) (hk : (2 : ℝ) ^ k < 1 / 2)
    (φ ψ : SchwartzMap ℝ ℂ)
    (hφ : ∀ ξ : ℝ, (φ : ℝ → ℂ) ξ ≠ 0 → ξ ∈ Work.Analysis.IonescuWainger.realArc k)
    (hψ : ∀ ξ : ℝ, (ψ : ℝ → ℂ) ξ ≠ 0 → ξ ∈ Work.Analysis.IonescuWainger.realArc k)
    {f : ℤ → ℂ} {B : ℝ} (hB : ∀ m : ℤ, ‖f m‖ ≤ B) :
    Work.KMTAreas.A7.Tle ρ l (fun ξ : ℝ => (φ : ℝ → ℂ) ξ - (ψ : ℝ → ℂ) ξ) f
      = Work.KMTAreas.A7.Tle ρ l φ f - Work.KMTAreas.A7.Tle ρ l ψ f := by
  classical
  have hnar : ∀ n ξ,
      ((fun n : ℕ => if n = 0 then φ else if n = 1 then ψ else (0 : SchwartzMap ℝ ℂ)) n
          : ℝ → ℂ) ξ ≠ 0 → ξ ∈ Work.Analysis.IonescuWainger.realArc k := by
    intro n ξ hξ
    by_cases h0 : n = 0
    · subst h0; simpa using hφ ξ hξ
    · by_cases h1 : n = 1
      · subst h1; simpa [h0] using hψ ξ hξ
      · have hz : ((fun n : ℕ => if n = 0 then φ else if n = 1 then ψ
            else (0 : SchwartzMap ℝ ℂ)) n : ℝ → ℂ) ξ = 0 := by simp [h0, h1]
        exact absurd hz hξ
  have hsub := Work.KMTAreas.A7.Tle_finsetSum_of_bounded ρ l k hk
    (fun n : ℕ => if n = 0 then φ else if n = 1 then ψ else (0 : SchwartzMap ℝ ℂ)) hnar
    ({0, 1} : Finset ℕ) (fun n => n = 0) hB
  have hL : (fun x : ℤ => ∑ n ∈ ({0, 1} : Finset ℕ),
        (if (decide (n = 0)) = true then (1 : ℂ) else -1) *
          Work.KMTAreas.A7.Tle ρ l
            (⇑(if n = 0 then φ else if n = 1 then ψ
              else (0 : SchwartzMap ℝ ℂ))) f x)
      = Work.KMTAreas.A7.Tle ρ l φ f - Work.KMTAreas.A7.Tle ρ l ψ f := by
    funext x
    rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
    simp
    ring_nf
  have hfun : (fun ξ : ℝ => (φ : ℝ → ℂ) ξ - (ψ : ℝ → ℂ) ξ)
      = (fun ξ : ℝ => ∑ n ∈ ({0, 1} : Finset ℕ),
        (if (decide (n = 0)) = true then (1 : ℂ) else -1) *
          ((if n = 0 then φ else if n = 1 then ψ else (0 : SchwartzMap ℝ ℂ)) : ℝ → ℂ) ξ) := by
    funext ξ
    rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
    simp
    ring_nf
  rw [hfun]
  exact hsub.symm.trans hL

/-! ## Summation by parts for the annulus family -/

/-- The `-1`-shifted indicator: `abelE c m = c (m-1)` for `m ≥ 1` and `0` for `m = 0`. -/
private noncomputable def abelE (c : ℕ → ℂ) (m : ℕ) : ℂ := if m = 0 then 0 else c (m - 1)

/-- The Abel coefficients of the annulus family: the coefficient of the `m`-th cutoff after
summation by parts. -/
private noncomputable def abelD (c : ℕ → ℂ) (m : ℕ) : ℂ := abelE c m - c m

private lemma abel_prefix (c : ℕ → ℂ) (k : ℕ) :
    (∑ m ∈ Finset.range k, abelD c m) = - abelE c k := by
  induction k with
  | zero => simp [abelD, abelE]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [abelD, abelE, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    ring

private lemma abel_aux (c g : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), c n * (g (n + 1) - g n))
      = (∑ m ∈ Finset.range (N + 1), abelD c m * g m) + c N * g (N + 1) := by
  induction N with
  | zero => simp [abelD, abelE]; ring
  | succ N ih =>
    have hL : (∑ n ∈ Finset.range (N + 1 + 1), c n * (g (n + 1) - g n))
        = (∑ n ∈ Finset.range (N + 1), c n * (g (n + 1) - g n))
          + c (N + 1) * (g (N + 1 + 1) - g (N + 1)) :=
      Finset.sum_range_succ (fun n => c n * (g (n + 1) - g n)) (N + 1)
    have hR : (∑ m ∈ Finset.range (N + 1 + 1), abelD c m * g m)
        = (∑ m ∈ Finset.range (N + 1), abelD c m * g m) + abelD c (N + 1) * g (N + 1) :=
      Finset.sum_range_succ (fun m => abelD c m * g m) (N + 1)
    rw [hL, ih, hR]
    have hd : abelD c (N + 1) = c N - c (N + 1) := by simp [abelD, abelE]
    rw [hd]
    ring

/-- **Summation by parts for the annulus family.** -/
private lemma abel_range (c g : ℕ → ℂ) (K : ℕ) (hc : c K = 0) :
    (∑ n ∈ Finset.range (K + 1), c n * (g (n + 1) - g n))
      = ∑ m ∈ Finset.range (K + 1), abelD c m * g m := by
  have h := abel_aux c g K
  rw [hc, zero_mul, add_zero] at h
  exact h

/-- The interval sums of the Abel coefficients are bounded by `4` (in fact by `2`). -/
private lemma abel_interval (c : ℕ → ℂ) (hc1 : ∀ n, ‖c n‖ ≤ 1) (u v : ℕ) :
    ‖∑ m ∈ Finset.Icc u v, abelD c m‖ ≤ 4 := by
  by_cases h : u ≤ v + 1
  · have hIco : Finset.Icc u v = Finset.Ico u (v + 1) :=
      (Finset.Ico_add_one_right_eq_Icc u v).symm
    rw [hIco, Finset.sum_Ico_eq_sub (fun m => abelD c m) h, abel_prefix c (v + 1),
      abel_prefix c u, sub_neg_eq_add]
    have harith : (-abelE c (v + 1) + abelE c u : ℂ) = -(abelE c (v + 1) - abelE c u) := by ring
    rw [harith]
    have h1 : ‖abelE c u‖ ≤ 1 := by
      by_cases hu : u = 0
      · simp only [abelE, hu, ↓reduceIte, norm_zero]
        norm_num
      · simp only [abelE, hu, ↓reduceIte]
        exact hc1 _
    have h2 : ‖abelE c (v + 1)‖ ≤ 1 := by
      have hne : v + 1 ≠ 0 := Nat.succ_ne_zero v
      simp only [abelE, hne, ↓reduceIte, Nat.add_sub_cancel]
      exact hc1 v
    calc ‖-(abelE c (v + 1) - abelE c u)‖ = ‖abelE c (v + 1) - abelE c u‖ := norm_neg _
      _ ≤ ‖abelE c (v + 1)‖ + ‖abelE c u‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add h2 h1
      _ ≤ 4 := by norm_num
  · have hemp : Finset.Icc u v = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    rw [hemp, Finset.sum_empty, norm_zero]
    norm_num

/-! ## The identification of the signed sum of increments with the `Tle` projection -/

/-- **The signed sum of the annulus increments is the `Tle` projection with the signed-sum symbol.**
For a bounded input `f` the finite signed sum `∑_{n ∈ U} ω n • (lpf (n+1) f − lpf n f)` equals the
single Ionescu--Wainger projection `Tle ρ l₁ S f` with `S` the signed sum of the annulus symbols
`η_{≤ -(m₀+n+1)} − η_{≤ -(m₀+n)}`. -/
private lemma signedSum_eq_Tle (ρ : ℝ) (l₁ m₀ : ℕ) (hm₀ : 2 ≤ m₀)
    (U : Finset ℕ) (ω : ℕ → Bool) (Sfun : ℝ → ℂ)
    (hS : ∀ ξ : ℝ, Sfun ξ = ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
            (-((m₀ : ℤ) + ((n + 1 : ℕ) : ℤ))) ξ
          - Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
            (-((m₀ : ℤ) + (n : ℤ))) ξ))
    {f : ℤ → ℂ} {B : ℝ} (hB : ∀ m : ℤ, ‖f m‖ ≤ B) :
    (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
        (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (n + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x))
      = Work.KMTAreas.A7.Tle ρ l₁ Sfun f := by
  classical
  have hk : (2 : ℝ) ^ (-(m₀ : ℤ)) < 1 / 2 := by
    have hle : (-(m₀ : ℤ)) ≤ (-2 : ℤ) := by omega
    calc (2 : ℝ) ^ (-(m₀ : ℤ)) ≤ (2 : ℝ) ^ (-2 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hle
      _ = 1 / 4 := by norm_num
      _ < 1 / 2 := by norm_num
  set Φ : ℕ → SchwartzMap ℝ ℂ := fun n =>
    Work.KMTAreas.A7.etaCutSchwartz (-((m₀ : ℤ) + ((n + 1 : ℕ) : ℤ)))
      - Work.KMTAreas.A7.etaCutSchwartz (-((m₀ : ℤ) + (n : ℤ))) with hΦdef
  have hΦcoe : ∀ n ξ, (Φ n : ℝ → ℂ) ξ
      = Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
            (-((m₀ : ℤ) + ((n + 1 : ℕ) : ℤ))) ξ
          - Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
            (-((m₀ : ℤ) + (n : ℤ))) ξ := by
    intro n ξ
    rw [hΦdef]
    simp
  have hnar : ∀ n ξ, (Φ n : ℝ → ℂ) ξ ≠ 0 →
      ξ ∈ Work.Analysis.IonescuWainger.realArc (-(m₀ : ℤ)) := by
    intro n ξ hξ
    rw [hΦcoe n ξ] at hξ
    by_cases h1 : Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
        (-((m₀ : ℤ) + ((n + 1 : ℕ) : ℤ))) ξ = 0
    · have h2 : Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
          (-((m₀ : ℤ) + (n : ℤ))) ξ ≠ 0 := by
        intro h2; exact hξ (by rw [h1, h2, sub_zero])
      exact realArc_mono (by omega) (Work.KMTAreas.A7.etaCut_ne_zero_mem_realArc _ h2)
    · exact realArc_mono (by omega) (Work.KMTAreas.A7.etaCut_ne_zero_mem_realArc _ h1)
  have hsum := Work.KMTAreas.A7.Tle_finsetSum_of_bounded ρ l₁ (-(m₀ : ℤ)) hk Φ hnar U ω hB
  have hfun : Sfun = fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * (Φ n : ℝ → ℂ) ξ := by
    funext ξ
    rw [hS ξ]
    exact Finset.sum_congr rfl (fun n _ => by rw [hΦcoe n ξ])
  have hterm : (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
        (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (n + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x))
      = (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          Work.KMTAreas.A7.Tle ρ l₁ (Φ n : ℝ → ℂ) f x) := by
    funext x
    refine Finset.sum_congr rfl (fun n _ => ?_)
    have hsub := Tle_sub_of_bounded ρ l₁ (-(m₀ : ℤ)) hk
      (Work.KMTAreas.A7.etaCutSchwartz (-((m₀ : ℤ) + ((n + 1 : ℕ) : ℤ))))
      (Work.KMTAreas.A7.etaCutSchwartz (-((m₀ : ℤ) + (n : ℤ))))
      (fun ξ hξ => realArc_mono (by omega) (mem_realArc_of_etaCutSchwartz hξ))
      (fun ξ hξ => realArc_mono (by omega) (mem_realArc_of_etaCutSchwartz hξ)) hB
    have hΦn : (Φ n : ℝ → ℂ)
        = fun ξ : ℝ => (Work.KMTAreas.A7.etaCutSchwartz (-((m₀ : ℤ) + ((n + 1 : ℕ) : ℤ)))
              : ℝ → ℂ) ξ
          - (Work.KMTAreas.A7.etaCutSchwartz (-((m₀ : ℤ) + (n : ℤ))) : ℝ → ℂ) ξ := by
      funext ξ
      rw [hΦdef]
      simp
    have e1 : Work.KMTAreas.A7.Tle ρ l₁
          (Work.KMTAreas.A7.etaCutSchwartz (-((m₀ : ℤ) + ((n + 1 : ℕ) : ℤ)))
            : ℝ → ℂ) f
        = Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (n + 1) f := by
      rw [Work.KMTAreas.A7.etaCutSchwartz_coe]
      rfl
    have e2 : Work.KMTAreas.A7.Tle ρ l₁
          (Work.KMTAreas.A7.etaCutSchwartz (-((m₀ : ℤ) + (n : ℤ))) : ℝ → ℂ) f
        = Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f := by
      rw [Work.KMTAreas.A7.etaCutSchwartz_coe]
      rfl
    have key : Work.KMTAreas.A7.Tle ρ l₁ (Φ n : ℝ → ℂ) f
        = Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (n + 1) f
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f := by
      rw [hΦn, hsub, e1, e2]
    exact congrArg (fun y => (if ω n then (1 : ℂ) else -1) * y) (congrFun key x).symm
  rw [hfun]
  rw [hterm]
  exact hsum

/-! ## From a `lintegral` bound of `G^q` to an `eLpNorm` bound of `G` -/

/-- If `∫⁻ G x ^ q ∂count ≤ ofReal A · ∫⁻ ‖f x‖ₑ ^ q ∂count` with `0 ≤ A`, then
`eLpNorm G (ofReal q) ≤ ofReal (A ^ (1/q)) · eLpNorm f (ofReal q)`. -/
private lemma eLpNorm_le_of_lintegral_rpow_le {G : ℤ → ℝ≥0∞} {f : ℤ → ℂ} {q : ℝ} (hq : 0 < q)
    {A : ℝ} (hA : 0 ≤ A)
    (h : ∫⁻ x : ℤ, G x ^ q ∂Measure.count
        ≤ ENNReal.ofReal A * ∫⁻ x : ℤ, ‖f x‖ₑ ^ q ∂Measure.count) :
    MeasureTheory.eLpNorm G (ENNReal.ofReal q) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (A ^ (1 / q)) *
          MeasureTheory.eLpNorm f (ENNReal.ofReal q) MeasureTheory.Measure.count := by
  have hqne : ENNReal.ofReal q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hq
  have hqtop : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hq.le
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hqne hqtop,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hqne hqtop, htoReal]
  have hG : ∀ x : ℤ, ‖G x‖ₑ = G x := fun x => enorm_eq_self _
  simp only [hG]
  calc (∫⁻ x : ℤ, G x ^ q ∂Measure.count) ^ (1 / q)
      ≤ (ENNReal.ofReal A * ∫⁻ x : ℤ, ‖f x‖ₑ ^ q ∂Measure.count) ^ (1 / q) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = (ENNReal.ofReal A) ^ (1 / q)
          * (∫⁻ x : ℤ, ‖f x‖ₑ ^ q ∂Measure.count) ^ (1 / q) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ = ENNReal.ofReal (A ^ (1 / q))
          * (∫⁻ x : ℤ, ‖f x‖ₑ ^ q ∂Measure.count) ^ (1 / q) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hA (by positivity)]

/-! ## The main theorem -/

/-- **The band-pass square-function bound for the increments of the low-pass Ionescu--Wainger family.** -/
theorem bandSquareUnif (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  classical
  obtain ⟨q, hq1, hpq⟩ : ∃ q : ℝ, 1 < q ∧ p = ENNReal.ofReal q :=
    ⟨p.toReal, by rw [← ENNReal.one_lt_ofReal, ENNReal.ofReal_toReal (ne_of_lt hptop)]; exact hp,
      (ENNReal.ofReal_toReal (ne_of_lt hptop)).symm⟩
  have hq0 : 0 < q := lt_trans zero_lt_one hq1
  obtain ⟨Cb, hCbpos, Cρb, hCρbpos, hbump⟩ :=
    Work.KMTAreas.A7Hi.iwLqBound_narrow_bump ρ hρ hρ1 q hq1
  have h2r1 : (1 : ℝ) < 2 * ((max 2 ⌈max q (q / (q - 1)) / 2⌉₊ : ℕ) : ℝ) := by
    have hge : (1 : ℝ) < ((max 2 ⌈max q (q / (q - 1)) / 2⌉₊ : ℕ) : ℝ) := by
      have : (1 : ℕ) < max 2 ⌈max q (q / (q - 1)) / 2⌉₊ :=
        lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      exact_mod_cast this
    linarith
  obtain ⟨Cq, hCqpos, hCqm⟩ := Work.KMTAreas.A7.isLqMultiplierBound_of_mikhlin
    (2 * ((max 2 ⌈max q (q / (q - 1)) / 2⌉₊ : ℕ) : ℝ)) h2r1
  obtain ⟨M0, M1, M2, hM0, hM1, hM2, hηcd, hη0, hη1, hη2, hηs0, hηs1, hηs2, hηd, hηd2⟩ :=
    Work.KMTAreas.A7.kmtEta_deriv_bounds
  have hηone : ∀ y : ℝ, |y| ≤ 1 / 2 → Work.KMTContract.kmtEta y = 1 :=
    fun y hy => Work.KMTContract.kmtEta_one hy
  have hη1in : ∀ y : ℝ, |y| < 1 / 2 → deriv Work.KMTContract.kmtEta y = 0 :=
    Work.KMTAreas.A7rand.kmtEta_deriv_eq_zero_of_abs_lt
  have hη2in : ∀ y : ℝ, |y| < 1 / 2 →
      iteratedDeriv 2 Work.KMTContract.kmtEta y = 0 :=
    Work.KMTAreas.A7rand.kmtEta_iteratedDeriv_two_eq_zero_of_abs_lt
  obtain ⟨A, hApos, hA⟩ := Work.KMTAreas.A7rand.lowpass_symbol_mikhlin Work.KMTContract.kmtEta
    M0 M1 M2 hM0 hM1 hM2 hηcd hη0 hη1 hη2 hηs0 hηs1 hηs2 hηd hηd2 hηone hη1in hη2in
  obtain ⟨Kc, hKcpos, hKhint⟩ := Work.KMTAreas.A7.sqSum_lintegral_le_uniformSigns_noLin q hq1
  set Mnn : NNReal := Real.toNNReal (Cq * A) with hMnndef
  have hMnnpos : (0 : NNReal) < Mnn :=
    Real.toNNReal_pos.mpr (mul_pos hCqpos hApos)
  set Mu : ℝ := ((Real.toNNReal (Cb * (Mnn : ℝ)) : NNReal) : ℝ) with hMudef
  have hMuNN : 0 ≤ Mu := NNReal.coe_nonneg _
  have hMupos : 0 < Mu := by
    rw [hMudef]
    exact_mod_cast (Real.toNNReal_pos.mpr (mul_pos hCbpos (by exact_mod_cast hMnnpos)))
  have hMuqpos : 0 < Mu ^ q := Real.rpow_pos_of_pos hMupos q
  set Cf : ℝ := (Kc * Mu ^ q) ^ (1 / q) with hCfdef
  have hCfpos : 0 < Cf := by
    rw [hCfdef]
    exact Real.rpow_pos_of_pos (mul_pos hKcpos hMuqpos) _
  refine ⟨max Cρb 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), Cf, hCfpos, ?_⟩
  intro l₁ m₀ hgood f
  rw [hpq]
  have hgoodb : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρb l₁ (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono (le_max_left _ _) hgood
  have hm₀ : 2 ≤ m₀ := by
    have h2ρ : (1 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l₁ : ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hCρ2 : (2 : ℝ) ≤ (max Cρb 2 : ℝ) := le_max_right _ _
    have hg := hgood
    rw [Work.Analysis.IonescuWainger.GoodMajorArcs] at hg
    have hm0le : ((max Cρb 2 : ℝ) * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) ≤ (m₀ : ℝ) := by
      push_cast at hg ⊢
      nlinarith [hg]
    have : (2 : ℝ) ≤ (m₀ : ℝ) := by nlinarith [hCρ2, h2ρ, hm0le]
    exact_mod_cast this
  have hk0 : (2 : ℝ) ^ (-(m₀ : ℤ)) < 1 / 2 := by
    have hle : (-(m₀ : ℤ)) ≤ (-2 : ℤ) := by omega
    calc (2 : ℝ) ^ (-(m₀ : ℤ)) ≤ (2 : ℝ) ^ (-2 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hle
      _ = 1 / 4 := by norm_num
      _ < 1 / 2 := by norm_num
  have hT : ∀ (U : Finset ℕ) (ω : ℕ → Bool) (g : ℤ → ℂ),
      ∫⁻ x : ℤ, ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (n + 1) g x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n g x)‖ₑ ^ q ∂Measure.count
        ≤ ENNReal.ofReal (Mu ^ q) * ∫⁻ x : ℤ, ‖g x‖ₑ ^ q ∂Measure.count := by
    intro U ω g
    by_cases htop : MeasureTheory.eLpNorm g (ENNReal.ofReal q) MeasureTheory.Measure.count = ⊤
    · have hlinf : ∫⁻ x : ℤ, ‖g x‖ₑ ^ q ∂Measure.count = ⊤ := by
        rw [Work.BourgainPlan.Maximal.lintegral_enorm_rpow_eq_eLpNorm_rpow g hq0, htop]
        exact ENNReal.top_rpow_of_pos hq0
      rw [hlinf, ENNReal.mul_top]
      · exact le_top
      · exact ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hMupos q)
    · obtain ⟨B, hB⟩ := Work.KMTAreas.A7.eLpNorm_finite_bounded (ENNReal.ofReal q)
          (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1.le) g
          (lt_top_iff_ne_top.mpr htop)
      set c : ℕ → ℂ := fun n => if n ∈ U then (if ω n then (1 : ℂ) else -1) else 0 with hcdef
      set K : ℕ := U.sup (fun n => n + 1) with hKdef
      have hK : ∀ n ∈ U, n + 1 ≤ K := fun n hn => Finset.le_sup hn
      have hcK : c K = 0 := by
        have hKU : K ∉ U := by
          intro hKU
          have := hK K hKU
          omega
        simp only [hcdef, hKU, ↓reduceIte]
      have hc1 : ∀ n, ‖c n‖ ≤ 1 := by
        intro n
        simp only [hcdef]
        split_ifs with h1 h2 <;> simp
      have hUsub : U ⊆ Finset.range (K + 1) := by
        intro n hn
        have := hK n hn
        simp only [Finset.mem_range]
        omega
      set ψ : ℝ → ℂ := fun ξ => ∑ m ∈ Finset.range (K + 1), abelD c m *
        Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
          (-((m₀ : ℤ) + (m : ℤ))) ξ with hψdef
      have hψnar : ∀ ξ : ℝ, ψ ξ ≠ 0 → ξ ∈ Work.Analysis.IonescuWainger.realArc (-(m₀ : ℤ)) := by
        intro ξ hξ
        rw [hψdef] at hξ
        by_contra hcon
        refine hξ (Finset.sum_eq_zero (fun m _ => ?_))
        have h0 : Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
            (-((m₀ : ℤ) + (m : ℤ))) ξ = 0 := by
          by_contra hne
          exact hcon (realArc_mono (by omega)
            (Work.KMTAreas.A7.etaCut_ne_zero_mem_realArc _ hne))
        rw [h0, mul_zero]
      have hψcd : ContDiff ℝ (⊤ : ℕ∞) ψ := by
        rw [hψdef]
        exact ContDiff.sum (s := Finset.range (K + 1))
          (f := fun m ξ => abelD c m * Work.Analysis.IonescuWainger.etaCut
            Work.KMTContract.kmtEta (-((m₀ : ℤ) + (m : ℤ))) ξ)
          (fun m _ => contDiff_const.mul (Work.KMTAreas.A7.contDiff_etaCut _))
      have hψcs : HasCompactSupport ψ :=
        HasCompactSupport.of_support_subset_isCompact
          (K := Work.Analysis.IonescuWainger.realArc (-(m₀ : ℤ))) isCompact_Icc
          (fun ξ hξ => hψnar ξ hξ)
      let Ssch : SchwartzMap ℝ ℂ := hψcs.toSchwartzMap hψcd
      have hScoe : (Ssch : ℝ → ℂ) = ψ := by
        funext ξ
        exact HasCompactSupport.toSchwartzMap_toFun hψcs hψcd ξ
      have hMikh' : Work.KMTAreas.A7.MikhlinBound
          (fun ξ => ∑ m ∈ Finset.range (K + 1), abelD c m *
            Work.KMTContract.kmtEta ((2 : ℝ) ^ (m₀ + m) * ξ)) A := by
        have hAh := hA (fun m => m₀ + m) (fun i j hij => Nat.add_le_add_left hij m₀) (K + 1)
          (abelD c) (abel_interval c hc1)
        exact ⟨hApos.le, hAh.2.1, hAh.2.2.1, hAh.2.2.2⟩
      have hψeq : ψ = fun ξ => ∑ m ∈ Finset.range (K + 1), abelD c m *
          Work.KMTContract.kmtEta ((2 : ℝ) ^ (m₀ + m) * ξ) := by
        funext ξ
        rw [hψdef]
        exact Finset.sum_congr rfl (fun m _ => by rw [etaCut_ann_eq])
      have hMikh : Work.KMTAreas.A7.MikhlinBound ψ A := hψeq ▸ hMikh'
      have hψcd2 : ContDiff ℝ 2 ψ := hψcd.of_le (WithTop.coe_le_coe.mpr le_top)
      obtain ⟨hM1', hM2'⟩ := hCqm hψcd2 hMikh
      have hMe : Work.Analysis.IWMultiplier.IsLqMultiplierBound
          (ENNReal.ofReal (2 * ((max 2 ⌈max q (q / (q - 1)) / 2⌉₊ : ℕ) : ℝ)))
          (Ssch : ℝ → ℂ) Mnn := by
        rw [hScoe, hMnndef]; exact hM1'
      have hMe' : Work.Analysis.IWMultiplier.IsLqMultiplierBound
          (ENNReal.ofReal (2 * ((max 2 ⌈max q (q / (q - 1)) / 2⌉₊ : ℕ) : ℝ)))
          (fun x : ℝ => star ((Ssch : ℝ → ℂ) x)) Mnn := by
        rw [hScoe, hMnndef]; exact hM2'
      have hSnar : ∀ x : ℝ, (Ssch : ℝ → ℂ) x ≠ 0 →
          x ∈ Work.Analysis.IonescuWainger.realArc (-(m₀ : ℤ)) := by
        intro x hx
        exact hψnar x (by rwa [hScoe] at hx)
      have hIW := hbump l₁ (-(m₀ : ℤ)) Ssch Mnn hgoodb hk0 hSnar hMe hMe'
      have hCBnnpos : (0 : NNReal) < Real.toNNReal (Cb * (Mnn : ℝ)) :=
        Real.toNNReal_pos.mpr (mul_pos hCbpos (by exact_mod_cast hMnnpos))
      have hbound := Work.KMTAreas.A7.eLpNorm_iwConv_le_of_IWLqBound
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁) Ssch hq1 hCBnnpos hIW g
      have hMuEq : ENNReal.ofReal Mu
          = ENNReal.ofReal ((Real.toNNReal (Cb * (Mnn : ℝ)) : NNReal) : ℝ) := by rw [hMudef]
      have hSfun : ∀ ξ : ℝ, (Ssch : ℝ → ℂ) ξ = ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
              (-((m₀ : ℤ) + ((n + 1 : ℕ) : ℤ))) ξ
            - Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
              (-((m₀ : ℤ) + (n : ℤ))) ξ) := by
        intro ξ
        let g₀ : ℕ → ℂ := fun m => Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
            (-((m₀ : ℤ) + (m : ℤ))) ξ
        have h1 : (Ssch : ℝ → ℂ) ξ = ∑ m ∈ Finset.range (K + 1), abelD c m * g₀ m := by
          simp only [hScoe, hψdef, g₀]
        rw [h1, ← abel_range c g₀ K hcK]
        have hsub2 : (∑ n ∈ Finset.range (K + 1), c n * (g₀ (n + 1) - g₀ n))
            = ∑ n ∈ U, c n * (g₀ (n + 1) - g₀ n) :=
          (Finset.sum_subset hUsub (fun n _ hn => by simp [hcdef, hn])).symm
        rw [hsub2]
        refine Finset.sum_congr rfl (fun n hn => ?_)
        have hcn : c n = (if ω n then (1 : ℂ) else -1) := by simp [hcdef, hn]
        rw [hcn]
      have hident := signedSum_eq_Tle ρ l₁ m₀ hm₀ U ω (Ssch : ℝ → ℂ) hSfun hB
      calc ∫⁻ x : ℤ, ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
              (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (n + 1) g x
                - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n g x)‖ₑ ^ q ∂Measure.count
          = ∫⁻ x : ℤ, ‖Work.KMTAreas.A7.Tle ρ l₁ (Ssch : ℝ → ℂ) g x‖ₑ ^ q ∂Measure.count := by
            refine lintegral_congr fun x => ?_
            rw [congrFun hident x]
        _ = (MeasureTheory.eLpNorm (Work.Analysis.IWMultiplier.iwConv
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
              (Work.Analysis.IonescuWainger.periodize (Ssch : ℝ → ℂ)) g)
              (ENNReal.ofReal q) MeasureTheory.Measure.count) ^ q :=
            Work.BourgainPlan.Maximal.lintegral_enorm_rpow_eq_eLpNorm_rpow _ hq0
        _ ≤ (ENNReal.ofReal Mu
              * MeasureTheory.eLpNorm g (ENNReal.ofReal q) MeasureTheory.Measure.count) ^ q := by
            refine ENNReal.rpow_le_rpow ?_ hq0.le
            rw [hMuEq]
            exact hbound
        _ = ENNReal.ofReal (Mu ^ q)
              * (MeasureTheory.eLpNorm g (ENNReal.ofReal q) MeasureTheory.Measure.count) ^ q := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
              ENNReal.ofReal_rpow_of_nonneg hMuNN hq0.le]
        _ = ENNReal.ofReal (Mu ^ q) * ∫⁻ x : ℤ, ‖g x‖ₑ ^ q ∂Measure.count := by
            rw [← Work.BourgainPlan.Maximal.lintegral_enorm_rpow_eq_eLpNorm_rpow g hq0]
  have hmeas : ∀ n (g : ℤ → ℂ), AEMeasurable
      (fun x : ℤ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (n + 1) g x
        - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n g x) MeasureTheory.Measure.count :=
    fun n g => (measurable_of_countable _).aemeasurable
  have hKh := hKhint (fun n g => fun x : ℤ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (n + 1) g x
      - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n g x) hmeas Mu hMuNN hT f
  have hsqpow : ∀ x : ℤ, (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f x) ^ q
      = (∑' n : ℕ, ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (n + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ ^ (2 : ℝ)) ^ (q / 2) := by
    intro x
    rw [Work.KMTAreas.A7Hi.sqFun, ← ENNReal.rpow_mul]
    ring_nf
  have hlin : ∫⁻ x : ℤ, (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f x) ^ q ∂Measure.count
      ≤ ENNReal.ofReal (Kc * Mu ^ q) * ∫⁻ x : ℤ, ‖f x‖ₑ ^ q ∂Measure.count := by
    rw [lintegral_congr fun x => hsqpow x]
    exact hKh
  have hfinal := eLpNorm_le_of_lintegral_rpow_le hq0
    (mul_nonneg hKcpos.le (Real.rpow_nonneg hMuNN q)) hlin
  rw [hCfdef]
  exact hfinal


/-- **The band square function of the annuli of the low-pass Ionescu--Wainger family is bounded
on `ℓᵖ(ℤ)` by `C (1+l) ‖f‖_{ℓᵖ}`, uniformly in the base level `m₀`**, on the good major arcs.

This is `Work.KMTAreas.A7Lpd.bandSquare` (and `Work.KMTAreas.A7MixedG.BandSquarePiece`) with the
`p`-th powers of the auxiliary quantities (`(∑'_k ‖Δ_k f x‖²)^{1/2}` is the *real-valued* band
square function of the annuli).  The proof follows `Submission/Work/KMTAreas/A7Hi2/sqFunBound.lean`
verbatim (Khintchine/Marcinkiewicz--Zygmund linearisation `sqSum_lintegral_le_uniformSigns_noLin`,
summation by parts, the uniform Mikhlin bound `lowpass_symbol_mikhlin` of the Abel-summed annulus
symbol, the even-endpoint Ionescu--Wainger transfer `iwLqBound_narrow_bump` and the interpolation
`eLpNorm_iwConv_le_of_IWLqBound`), except that the constants are *uniform in `l`*: the proof only
needs `GoodMajorArcs ρ Cρ l (-(m₀)) → 2 ≤ m₀`, and no step loses a power of `l`. -/
theorem bandSquareAll (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (l : ℕ) (m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => (∑' k : ℕ,
            ‖Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((k + 1 : ℕ)) : ℤ))) f x
              - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((k : ℕ) : ℤ))) f x‖ ^ (2 : ℝ))
              ^ (1 / 2 : ℝ)) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l : ℝ))) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨Cρ, hCρ, C, hC, hbound⟩ := bandSquareUnif ρ hρ hρ1 p hp hptop
  refine ⟨Cρ, hCρ, C, hC, ?_⟩
  intro l m₀ hgood f
  have hbridge := eLpNorm_sqSum_le_eLpNorm_ennSqSum p (ne_of_gt (lt_trans zero_lt_one hp))
    (ne_of_lt hptop)
    (fun k x => Work.KMTAreas.A7Hi.lpf ρ l m₀ (k + 1) f x
      - Work.KMTAreas.A7Hi.lpf ρ l m₀ k f x)
  have hzsq : (fun x : ℤ => (∑' k : ℕ,
        ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (k + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l m₀ k f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
      = Work.KMTAreas.A7Hi.sqFun ρ l m₀ f := rfl
  have hreal : (fun x : ℤ => (∑' k : ℕ,
        ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (k + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l m₀ k f x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
      = (fun x : ℤ => (∑' k : ℕ,
        ‖Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((k + 1 : ℕ)) : ℤ))) f x
          - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((k : ℕ) : ℤ))) f x‖ ^ (2 : ℝ))
          ^ (1 / 2 : ℝ)) := rfl
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
  have h1 : (1 : ℝ) ≤ 1 + (l : ℝ) := by linarith
  have hC1 : C ≤ C * (1 + (l : ℝ)) := by
    calc C = C * 1 := (mul_one C).symm
      _ ≤ C * (1 + (l : ℝ)) := mul_le_mul_of_nonneg_left h1 hC.le
  calc MeasureTheory.eLpNorm (fun x : ℤ => (∑' k : ℕ,
          ‖Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((k + 1 : ℕ)) : ℤ))) f x
            - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((k : ℕ) : ℤ))) f x‖ ^ (2 : ℝ))
            ^ (1 / 2 : ℝ)) p MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm (fun x : ℤ => (∑' k : ℕ,
          ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (k + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l m₀ k f x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) p
          MeasureTheory.Measure.count := by rw [hreal]
    _ ≤ MeasureTheory.eLpNorm (fun x : ℤ => (∑' k : ℕ,
          ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (k + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l m₀ k f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) p
          MeasureTheory.Measure.count := hbridge
    _ = MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l m₀ f) p
          MeasureTheory.Measure.count := by rw [hzsq]
    _ ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
        hbound l m₀ hgood f
    _ ≤ ENNReal.ofReal (C * (1 + (l : ℝ))) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
        mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hC1) bot_le

end

end Work.KMTAreas.A7Lpd
