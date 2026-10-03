import Mathlib
import Submission.Work.A6Big.Defs
import Submission.Work.KMTPlan.A6.mdlG_two_le_uniform
import Submission.Work.KMTPlan.A6.MdlSliceLinG
import Submission.Work.KMTPlan.A6.ballVarBound
import Submission.Work.KMTPlan.A6.BallVarBoundBddClean
-- definitions module, not the §8-chain file (see the note in `KMTPlan/A6Clean/packetFamG_aux.lean`)

namespace Work.A6Clean

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems

noncomputable section

/-! ## Elementary facts about the core condition `core ρ C₀ …` (`= mdlCore ρ C₀ …`)

`core ρ C₀ l₁ l₂ k₁ k₂ a n = inIndexSet C₀ (max l₁ l₂) k₁ k₂ ⌊a n⌋ ∧
splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < ⌊a n⌋ ∧ mainRegime ρ k₁ k₂ ⌊a n⌋` is *verbatim*
`Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n`, and its only `C₀`-dependence is through
`heightScale C₀ N = C₀ * logLogN N`, which is monotone in `C₀`.  Hence:

* `core` is monotone in `C₀`;
* `core` (being monotone in the physical scale `⌊a n⌋`) is *upward closed* in `n` along a monotone
  `a`, i.e. it is a tail `{n₀ ≤ ·}` (or empty);
* clipping to a tail costs at most a factor `2` in the variational norm
  (`variationalNorm_clip_le` + `variationalNorm_comp_mono_le`).

The last two combine into the reduction that lets us assume `1 ≤ C₀`. -/

/-- `mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n` is `core ρ C₀ l₁ l₂ k₁ k₂ a n` by definition. -/
theorem mdlCore_eq_core (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ) :
    Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
      = Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n := rfl

/-- **`core` is monotone in `C₀`.** -/
theorem core_mono_C₀ {ρ : ℝ} {C₀ C₀' : ℕ} (h : C₀ ≤ C₀') {a : ℕ → NNReal}
    {l₁ l₂ k₁ k₂ n : ℕ} (hc : Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n) :
    Work.KMTAreas.A7.core ρ C₀' l₁ l₂ k₁ k₂ a n := by
  obtain ⟨hin, hcut, hmain⟩ := hc
  obtain ⟨hi1, hi2, hi3⟩ := hin
  have hN : Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n))
      ≤ Work.Analysis.EndVar.heightScale C₀' (Nat.floor (a n)) := by
    simp only [Work.Analysis.EndVar.heightScale]
    exact Nat.mul_le_mul_right _ h
  have hcast : ((Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ)
      ≤ ((Work.Analysis.EndVar.heightScale C₀' (Nat.floor (a n)) : ℕ) : ℤ) := by
    exact_mod_cast hN
  exact ⟨⟨le_trans hi1 hcast, le_trans hi2 hcast, le_trans hi3 hcast⟩, hcut, hmain⟩

/-- **`core` is a tail in `n`.**  If `a` is monotone the core condition is upward closed in the
index (`core_mono`), so as soon as it holds at all it is `{n₀ ≤ ·}`. -/
theorem core_eq_tail {ρ : ℝ} {C₀ : ℕ} {a : ℕ → NNReal} (hamono : Monotone a)
    (l₁ l₂ k₁ k₂ : ℕ) (h : ∃ n, Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n) :
    ∃ n₀ : ℕ, ∀ n : ℕ, Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ↔ n₀ ≤ n := by
  refine ⟨Nat.find h, fun n => ⟨fun hn => ?_, fun hn => ?_⟩⟩
  · by_contra hcon
    rw [not_le] at hcon
    exact Nat.find_min h hcon hn
  · exact Work.KMTAreas.A7.core_mono hamono hn (Nat.find_spec h)

/-- **Clipping to a tail costs at most a factor `2`** in the variational norm. -/
theorem variationalNorm_clip_tail_le_add (r : NNReal) (hr : 1 ≤ r) (u : ℕ → ℂ) (n₀ : ℕ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if n₀ ≤ n then u n else 0)
      ≤ PointwiseErgodicTheorems.variationalNorm r u
        + PointwiseErgodicTheorems.variationalNorm r u := by
  refine (Work.KMTAreas.A7.variationalNorm_clip_le r hr u n₀).trans ?_
  exact add_le_add
    (Work.KMTAreas.A7.variationalNorm_comp_mono_le u (fun a b hab => Nat.add_le_add_right hab n₀))
    (Work.KMTAreas.A7.variationalNorm_comp_mono_le u (fun a b hab => Nat.add_le_add_right hab n₀))

/-- Two families clipped at indicator tails that agree at every index are equal. -/
theorem clip_tail_congr {S : ℕ → Prop} [∀ n, Decidable (S n)] {n₀ : ℕ}
    (h : ∀ n, S n ↔ n₀ ≤ n) (u : ℕ → ℂ) :
    (fun n : ℕ => if S n then u n else 0) = fun n : ℕ => if n₀ ≤ n then u n else 0 := by
  funext n
  by_cases hn : S n
  · simp only [hn, if_true, (h n).mp hn]
  · have hn' : ¬ (n₀ ≤ n) := fun hh => hn ((h n).mpr hh)
    simp only [hn, if_false, hn']

/-- A family clipped at an identically false condition vanishes. -/
theorem clip_false {S : ℕ → Prop} [∀ n, Decidable (S n)] (h : ∀ n, ¬ S n) (u : ℕ → ℂ) :
    (fun n : ℕ => if S n then u n else 0) = (0 : ℕ → ℂ) := by
  funext n
  simp only [h n, if_false, Pi.zero_apply]

/-- **The `C₀`-reduction for the clipped family.**  For `C₀ ≤ C₀'` the family clipped at
`core ρ C₀ …` is the family clipped at `core ρ C₀' …` restricted to the tail `core ρ C₀ …`, so its
variational norm is at most twice that of the `C₀'`-family. -/
theorem core_clip_C₀_le_add (r : NNReal) (hr : 1 ≤ r) {ρ : ℝ} {C₀ C₀' : ℕ} (h : C₀ ≤ C₀')
    {a : ℕ → NNReal} (hamono : Monotone a) (l₁ l₂ k₁ k₂ : ℕ) (F : ℕ → ℤ → ℂ) (x : ℤ) :
    PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n then F n x else 0)
      ≤ PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀' l₁ l₂ k₁ k₂ a n then F n x else 0)
        + PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀' l₁ l₂ k₁ k₂ a n then F n x else 0) := by
  by_cases hne : ∃ n : ℕ, Work.KMTAreas.A7.core ρ C₀' l₁ l₂ k₁ k₂ a n
  · obtain ⟨n₀', hn₀'⟩ := core_eq_tail hamono l₁ l₂ k₁ k₂ hne
    have hbig : (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀' l₁ l₂ k₁ k₂ a n then F n x else 0)
        = fun n : ℕ => if n₀' ≤ n then F n x else 0 :=
      clip_tail_congr hn₀' (fun n => F n x)
    by_cases hC : ∃ n : ℕ, Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n
    · obtain ⟨n₀, hn₀⟩ := core_eq_tail hamono l₁ l₂ k₁ k₂ hC
      have hsmall : (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n then F n x else 0)
          = fun n : ℕ => if n₀ ≤ n then F n x else 0 :=
        clip_tail_congr hn₀ (fun n => F n x)
      have hle : n₀' ≤ n₀ := by
        have h1 : Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n₀ := (hn₀ n₀).mpr le_rfl
        exact (hn₀' n₀).mp (core_mono_C₀ h h1)
      have hsub : (fun n : ℕ => if n₀ ≤ n then F n x else 0)
          = fun n : ℕ =>
              if n₀ ≤ n then (fun m : ℕ => if n₀' ≤ m then F m x else 0) n else 0 := by
        funext n
        by_cases hn : n₀ ≤ n
        · have hn' : n₀' ≤ n := le_trans hle hn
          simp only [hn, hn', if_true]
        · simp only [hn, if_false]
      rw [hsmall, hbig, hsub]
      exact variationalNorm_clip_tail_le_add r hr _ n₀
    · have hzero : (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n then F n x else 0)
          = (0 : ℕ → ℂ) :=
        clip_false (fun n hn => hC ⟨n, hn⟩) (fun n => F n x)
      rw [hzero, hbig, Work.KMTAreas.A7.variationalNorm_zero r hr]
      exact zero_le
  · have hzero : (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀' l₁ l₂ k₁ k₂ a n then F n x else 0)
        = (0 : ℕ → ℂ) :=
      clip_false (fun n hn => hne ⟨n, hn⟩) (fun n => F n x)
    have hzero₂ : (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n then F n x else 0)
        = (0 : ℕ → ℂ) :=
      clip_false (fun n hn => hne ⟨n, core_mono_C₀ h hn⟩) (fun n => F n x)
    rw [hzero, hzero₂, Work.KMTAreas.A7.variationalNorm_zero r hr]
    exact zero_le

/-- **The clip at `mdlCore` costs at most a factor `2`** (it is the tail `core ρ C₀ …`). -/
theorem mdlCore_clip_le_add (r : NNReal) (hr : 1 ≤ r) {ρ : ℝ} {C₀ : ℕ} {a : ℕ → NNReal}
    (hamono : Monotone a) (l₁ l₂ k₁ k₂ : ℕ) (F : ℕ → ℤ → ℂ) (x : ℤ) :
    PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then F n x else 0)
      ≤ PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => F n x)
        + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => F n x) := by
  by_cases hne : ∃ n : ℕ, Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · obtain ⟨n₀, hn₀⟩ := core_eq_tail hamono l₁ l₂ k₁ k₂ hne
    have htail : (fun n : ℕ =>
          if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then F n x else 0)
        = fun n : ℕ => if n₀ ≤ n then F n x else 0 := by
      funext n
      by_cases hn : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
      · simp only [hn, if_true, (hn₀ n).mp hn]
      · have hn' : ¬ (n₀ ≤ n) := fun hh => hn ((hn₀ n).mpr hh)
        simp only [hn, if_false, hn']
    rw [htail]
    exact variationalNorm_clip_tail_le_add r hr _ n₀
  · have hzero : (fun n : ℕ => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then F n x else 0)
        = (0 : ℕ → ℂ) :=
      clip_false (fun n hn => hne ⟨n, hn⟩) (fun n => F n x)
    rw [hzero, Work.KMTAreas.A7.variationalNorm_zero r hr]
    exact zero_le

/-! ## The target -/

/-- **Finiteness of the `ℓ²`-variational norm of the `g`-side model slice** (the `(2,2,1)` model
tuple of KMT §8).

The target is only a *finiteness* statement, so the numerical losses that the quantitative
estimates of the paper have to absorb are irrelevant.  Strategy:

* reduce `C₀` to `C₀' = max C₀ 1` (`core_clip_C₀_le_add`): `mdlCore = core` is monotone in `C₀` and
  is a tail in `n` (`core_mono`, `core_eq_tail`), and clipping to a tail costs at most a factor `2`
  (`variationalNorm_clip_le` + `variationalNorm_comp_mono_le`);
* for `k₂ ≠ 0 ∨ j₂ = 1` the proved quantitative estimate `sliceFam_bound_ne`
  (`Work.KMTPlan.A6.MdlSliceLinG`, valid for *all* `ρ ≤ 1`, `C₀ ≥ 1`) bounds the family by
  `C(Λ) · lossWeight · ‖g‖₂ < ⊤`;
* for `k₂ = j₂ = 0` the family is the `g`-side "ball" family `n ↦ Tle ρ l₂ (φ̃_{N_n,t}) W` of §8,
  which is bounded on `ℓ²` for *every* `ρ ≤ 1` and every level `l₂ ≤ B` by `ballVarBound`
  (the height-`0` ball estimate: split off the modulation, bound the deviation by the *pointwise
  symbol square-sum* — no uniformity-in-signs input) followed by `ballVarBoundBddClean`
  (the `α`-decomposition into `#(iwArithFreqs ρ l₂)` modulated copies of the height-`0` walk);
  the clip at `mdlCore` is a tail, hence costs another factor `2` (`mdlCore_clip_le_add`). -/
theorem mdlSliceG_varNorm_lt_top (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (C₀ : ℕ) (a : ℕ → NNReal) (Λ : NNReal) (hΛ : 1 < Λ)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n : ℕ, 1 ≤ a n)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (j₂ : ℤ) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
    (hk₂ : k₂ = 0 → j₂ ≠ -1) (g : ℤ → ℂ) (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (R : NNReal) (hR : 2 < R) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ =>
      Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n x)) 2 MeasureTheory.Measure.count < ⊤ := by
  classical
  have hR1 : (1 : NNReal) ≤ R := le_trans (by norm_num) hR.le
  have hj₂' : j₂ = -1 ∨ j₂ = 0 ∨ j₂ = 1 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hj₂
  -- ## the model input `W = mdlG ρ P (uScale ρ L) l₂ g`
  set W : ℤ → ℂ := Work.KMTPlan.A6.mdlG ρ P
    (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g with hW
  have hWmem : MeasureTheory.MemLp W 2 MeasureTheory.Measure.count := by
    obtain ⟨Cg, _hCgpos, hCg⟩ := Work.KMTPlan.A6.mdlG_two_le_uniform P hd ρ hρ hρ1
    have hl : l₂ ≤ max (max l₁ l₂) (max k₁ k₂) :=
      le_trans (le_max_right l₁ l₂) (le_max_left _ _)
    refine MeasureTheory.memLp_iff.mpr ?_
    rw [hW]
    exact lt_of_le_of_lt (hCg _ l₂ hl g) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.eLpNorm_lt_top)
  obtain ⟨BW, _hBW0, hBW⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℤ, ‖W y‖ ≤ B := by
    obtain ⟨B, hB⟩ :=
      Work.KMTAreas.A7.bounded_of_eLpNorm_count_lt_top (p := 2) (by norm_num) hWmem.eLpNorm_lt_top
    exact ⟨max B 0, le_max_right _ _, fun y => le_trans (hB y) (le_max_left _ _)⟩
  -- ## step 1: reduce `C₀` to `C₀' = max C₀ 1`
  set C₀' : ℕ := max C₀ 1 with _hC₀'def
  have hC₀'1 : 1 ≤ C₀' := le_max_right _ _
  have hC₀le : C₀ ≤ C₀' := le_max_left _ _
  have hamono : Monotone a := Work.KMTAreas.A7Hi2.monotone_of_lacunary hΛ ha ha1
  -- the sliced family is the clip, at `mdlCore`, of the common family `n ↦ Tle ρ l₂ φ̃_n W`
  have hslice : ∀ (C : ℕ) (n : ℕ),
      Work.KMTPlan.A6.mdlSliceG ρ P C a l₁ l₂ k₁ k₂ j₂ t g n
        = if Work.KMTPlan.A6.mdlCore ρ C a l₁ l₂ k₁ k₂ n then
            Work.KMTAreas.A7.Tle ρ l₂
              (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t) W
          else 0 := by
    intro C n
    rfl
  have hfam : ∀ (C : ℕ) (x : ℤ),
      (fun n : ℕ => Work.KMTPlan.A6.mdlSliceG ρ P C a l₁ l₂ k₁ k₂ j₂ t g n x)
        = fun n : ℕ => if Work.KMTPlan.A6.mdlCore ρ C a l₁ l₂ k₁ k₂ n then
            Work.KMTAreas.A7.Tle ρ l₂
              (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t) W x
          else 0 := by
    intro C x
    funext n
    have h := congrFun (hslice C n) x
    rw [h]
    by_cases hc : Work.KMTPlan.A6.mdlCore ρ C a l₁ l₂ k₁ k₂ n
    · simp only [hc, if_true]
    · simp only [hc, if_false]
      rfl
  have hstep1 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n x))
        2 MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTPlan.A6.mdlSliceG ρ P C₀' a l₁ l₂ k₁ k₂ j₂ t g n x))
          2 MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTPlan.A6.mdlSliceG ρ P C₀' a l₁ l₂ k₁ k₂ j₂ t g n x))
          2 MeasureTheory.Measure.count := by
    have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n x)
        ≤ PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => Work.KMTPlan.A6.mdlSliceG ρ P C₀' a l₁ l₂ k₁ k₂ j₂ t g n x)
          + PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => Work.KMTPlan.A6.mdlSliceG ρ P C₀' a l₁ l₂ k₁ k₂ j₂ t g n x) := by
      intro x
      rw [hfam C₀ x, hfam C₀' x]
      exact core_clip_C₀_le_add R hR1 hC₀le hamono l₁ l₂ k₁ k₂
        (fun n x => Work.KMTAreas.A7.Tle ρ l₂
          (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t) W x) x
    calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n x))
          2 MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => Work.KMTPlan.A6.mdlSliceG ρ P C₀' a l₁ l₂ k₁ k₂ j₂ t g n x)
            + PointwiseErgodicTheorems.variationalNorm R
              (fun n : ℕ => Work.KMTPlan.A6.mdlSliceG ρ P C₀' a l₁ l₂ k₁ k₂ j₂ t g n x))
            2 MeasureTheory.Measure.count :=
          Work.KMTAreas.A7.eLpNorm_mono_ennreal hpt (by norm_num) (by norm_num)
      _ ≤ MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => Work.KMTPlan.A6.mdlSliceG ρ P C₀' a l₁ l₂ k₁ k₂ j₂ t g n x))
            2 MeasureTheory.Measure.count
          + MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => Work.KMTPlan.A6.mdlSliceG ρ P C₀' a l₁ l₂ k₁ k₂ j₂ t g n x))
            2 MeasureTheory.Measure.count :=
        Work.KMTAreas.A7.eLpNorm_add_le_ennreal (by norm_num) (by norm_num)
  -- ## step 2: the `C₀'`-family has finite `ℓ²`-variational norm
  have hstep2 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTPlan.A6.mdlSliceG ρ P C₀' a l₁ l₂ k₁ k₂ j₂ t g n x))
        2 MeasureTheory.Measure.count < ⊤ := by
    by_cases hlow : k₂ = 0 ∧ j₂ = 0
    · -- ### the low case `k₂ = j₂ = 0`: the `g`-side "ball" family of §8
      obtain ⟨hk₂0, hj₂0⟩ := hlow
      subst hk₂0
      subst hj₂0
      -- the unclipped family `n ↦ Tle ρ l₂ (φ̃_{N_n,t}) W` is `ℓ²`-variationally bounded for
      -- every `ρ ≤ 1` (KMT §8, "ball" family: `ballVarBound` ∘ `ballVarBoundBddClean`)
      have huncl : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₂
            (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) 0 0 t) W x))
          2 MeasureTheory.Measure.count < ⊤ := by
        obtain ⟨C, _hCpos, hC⟩ := Work.KMTPlan.A6.ballVarBoundBddClean P hd R hR
          (Work.KMTPlan.A6.ballVarBound P hd R hR) l₂ Λ hΛ ρ hρ hρ1
        have h := hC a l₂ le_rfl ha ha1 t ht W
        exact lt_of_le_of_lt h (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hWmem.eLpNorm_lt_top)
      -- the clip at the core condition is a tail, so it costs at most a factor `2`
      refine lt_of_le_of_lt ?_ (ENNReal.add_lt_top.mpr ⟨huncl, huncl⟩)
      refine (Work.KMTAreas.A7.eLpNorm_mono_ennreal (fun x => ?_) (by norm_num)
        (by norm_num)).trans (Work.KMTAreas.A7.eLpNorm_add_le_ennreal (by norm_num) (by norm_num))
      rw [hfam C₀' x]
      exact mdlCore_clip_le_add R hR1 hamono l₁ l₂ k₁ 0
        (fun n x => Work.KMTAreas.A7.Tle ρ l₂
          (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) 0 0 t) W x) x
    · -- ### the non-low case: the quantitative estimate `sliceFam_bound_ne`
      have hne : k₂ ≠ 0 ∨ j₂ = 1 := by
        by_cases hk : k₂ = 0
        · refine Or.inr ?_
          rcases hj₂' with h | h | h
          · exact absurd h (hk₂ hk)
          · exact absurd ⟨hk, h⟩ hlow
          · exact h
        · exact Or.inl hk
      obtain ⟨C, _hCpos, hC⟩ := Work.KMTPlan.A6.sliceFam_bound_ne P hd C₀' hC₀'1 R hR 2
        (by norm_num) j₂ hj₂ Λ hΛ ρ hρ hρ1
      have h := hC a l₁ l₂ k₁ k₂ t g ha ha1 ht hne
      have hsF : Work.KMTPlan.A6.sliceFam P ρ C₀' a l₁ l₂ k₁ k₂ j₂ t g
          = Work.KMTPlan.A6.mdlSliceG ρ P C₀' a l₁ l₂ k₁ k₂ j₂ t g := by
        funext n x
        by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀' a l₁ l₂ k₁ k₂ n
        · simp only [Work.KMTPlan.A6.sliceFam, Work.KMTPlan.A6.mdlSliceG, hc, if_true]
        · simp only [Work.KMTPlan.A6.sliceFam, Work.KMTPlan.A6.mdlSliceG, hc, if_false]
          rfl
      rw [hsF] at h
      exact lt_of_le_of_lt h (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top
        ENNReal.ofReal_lt_top) hg.eLpNorm_lt_top)
  -- ## step 3: assemble
  exact lt_of_le_of_lt hstep1 (ENNReal.add_lt_top.mpr ⟨hstep2, hstep2⟩)

end

end Work.A6Clean
