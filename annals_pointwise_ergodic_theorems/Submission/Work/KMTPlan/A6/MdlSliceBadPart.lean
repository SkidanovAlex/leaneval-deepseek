/-
# `Work.KMTPlan.A6.MdlSliceBadPart` — the bad (non-narrow) scales of the frozen-`t` slice

Target: `Work.KMTPlan.A6.BadPartProp P hd hA1 hI` (see `MdlAdelicDefs.lean`), i.e. the estimate

  `‖ V^r_n ( 1_{¬ goodScale} · mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n · ) ‖_{ℓ¹(ℤ)}`
    `≤ K(Λ) · lossWeight A ρ l₁ l₂ k₁ k₂ · 2^{-c·max(l₁,l₂)} · ‖f‖₂ ‖g‖₂`

on the finitely many scales `N = ⌊a n⌋` on which the decimated-sampling transfer does **not**
apply (`¬ goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) N`, i.e. `N < 8·Q·2^{L+1}`).

## The proof

* **Step 1 (`badLmaxBound`).**  A non-zero slice at a bad scale forces
  `splitCut ρ L < N < 8·arithQ ρ (max l₁ l₂)·2^{L+1}` (`L = lcL l₁ l₂ k₁ k₂`); for
  `L > B(ρ)` this contradicts `splitCut_dominates`, so `L ≤ B(ρ)`.
* **Step 2 (`slicesTwoLe`).**  At bounded height `L ≤ B(ρ)` the two packet families obey
  `‖mdlSliceF … n‖₂ ≤ C‖f‖₂`, `‖mdlSliceG … n‖₂ ≤ C‖g‖₂` with `C = C(ρ, B)` (the bumps are
  narrow, `mainRegime` gives `2^{k_i} ≤ N`).
* **Step 3 (`MdlSliceCrudeUniform_ssu`, PROVED).**  The single-scale bound
  `‖Btwist ρ P l₁ l₂ (mStarF u) (mStargF d u) h k‖_{ℓ¹} ≤ C(ρ,B)·‖h‖₂·‖k‖₂`, combined with
  `mdlSliceJ_eq_Btwist` (PROVED), gives `‖G n‖_{ℓ¹} ≤ C(ρ,B)‖f‖₂‖g‖₂` for every scale.
* **Step 4 (`badScalesBounded`).**  With `L ≤ B(ρ)` and `arithQ ρ (max l₁ l₂) ≤ arithQ ρ B(ρ)`,
  a bad scale satisfies `a n < 8·arithQ ρ B(ρ)·2^{B+1}+1`; by lacunarity (`Λ^n ≤ a n`) there are
  no bad scales beyond `K(Λ, ρ, B)`.
* **Step 5 (the assembly below).**  The family is supported on `{0, …, K(Λ)-1}`, so
  `eLpNorm_variationalNorm_le_sum` (`Submission.SingleScale`) bounds its variational norm by
  `4 ∑_n ‖G n‖_{ℓ¹} ≤ K(Λ)·4·C(ρ,B)‖f‖₂‖g‖₂`, and the constant is absorbed by choosing
  `A = 1`, `c = 1` and `K(Λ) = ⌈K(Λ,ρ,B)⌉·4·C(ρ,B)·2^B + 1` (the loss weight is `≥ 1` and the
  gain `2^{-max(l₁,l₂)} ≥ 2^{-B}` in the surviving case).

All constants are chosen *after* `ρ` (the statement's outer `∀ ρ ≤ ρ₀` precedes `∃ K`), so the
`ρ`-dependent constants of steps 1--4 are admissible.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.badLmaxBound
import Submission.Work.KMTPlan.A6.badScalesBounded
import Submission.Work.KMTPlan.A6.slicesTwoLe

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

/-- **(varsum) with the constants kept symbolic.** -/
private lemma varFamily_le (r : ℝ≥0) (hr : 1 ≤ r) (u : ℕ → ℤ → ℂ) (s : Finset ℕ)
    (C0 : ℝ≥0∞) (hu : ∀ n, n ∉ s → u n = 0)
    (hper : ∀ n ∈ s, eLpNorm (u n) 1 Measure.count ≤ C0) :
    eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => u n x)) 1 Measure.count
      ≤ (s.card : ℝ≥0∞) * (4 * C0) := by
  refine (eLpNorm_variationalNorm_le_sum (r := r) hr (p := (1 : ENNReal)) (le_refl 1)
    (u := u) (s := s) hu
    (fun n _ => (measurable_of_countable (u n)).aestronglyMeasurable)).trans ?_
  calc ∑ n ∈ s, 4 * eLpNorm (u n) 1 Measure.count
      ≤ ∑ _n ∈ s, 4 * C0 :=
        Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hper n hn) (by norm_num)
    _ = (s.card : ℝ≥0∞) * (4 * C0) := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The assembly of `BadPartProp`, with the three delegated inputs as hypotheses. -/
private theorem badPart_of_inputs (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P)
    (hbadLmax : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
      ∃ B : ℕ, ∀ (l₁ l₂ k₁ k₂ N : ℕ),
        Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂) < N →
        N < 8 * Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) * 2 ^ (lcL l₁ l₂ k₁ k₂ + 1) →
        lcL l₁ l₂ k₁ k₂ ≤ B)
    (hbadScales : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ B : ℕ,
      ∃ K : NNReal → NNReal, ∀ (Λ : NNReal) (hΛ : 1 < Λ) (a : ℕ → NNReal)
        (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (l₁ l₂ k₁ k₂ : ℕ), lcL l₁ l₂ k₁ k₂ ≤ B → ∀ n : ℕ, K Λ ≤ n →
        goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)))
    (hslices : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ B : ℕ,
      ∃ C : ℝ, 0 < C ∧ ∀ (C₀ : ℕ) (a : ℕ → NNReal) (ha1 : ∀ n, 1 ≤ a n)
        (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ))
        (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) (hk₁ : k₁ = 0 → j₁ ≠ -1) (hk₂ : k₂ = 0 → j₂ ≠ -1)
        (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (f g : ℤ → ℂ) (n : ℕ),
        lcL l₁ l₂ k₁ k₂ ≤ B →
        (eLpNorm (mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) 2 Measure.count
            ≤ ENNReal.ofReal C * eLpNorm f 2 Measure.count) ∧
        (eLpNorm (mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) 2 Measure.count
            ≤ ENNReal.ofReal C * eLpNorm g 2 Measure.count)) :
    BadPartProp P hd hA1 hI := by
  classical
  refine ⟨1, one_pos, 1, zero_le_one, 1, one_pos, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨B, hB⟩ := hbadLmax ρ hρ hρ1
  obtain ⟨K₀, hK₀⟩ := hbadScales ρ hρ hρ1 B
  obtain ⟨Cb, hCbpos, hCb⟩ := MdlSliceCrudeUniform_ssu ρ hρ hρ1 P B
  obtain ⟨Cs, hCspos, hCs⟩ := hslices ρ hρ hρ1 B
  refine ⟨fun Λ => Real.toNNReal ((⌈(K₀ Λ : ℝ)⌉₊ : ℝ) * (4 * Cb * Cs * Cs) * 2 ^ B + 1), ?_⟩
  intro r hr C₀ hC₀ a Λ l₁ l₂ k₁ k₂ t j₁ j₂ hj₁ hj₂ f g hΛ ha ha1 ht hk₁ hk₂ hf hg
  have hr1 : (1 : ℝ≥0) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  set L : ℕ := lcL l₁ l₂ k₁ k₂ with hL
  set Q : ℕ := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) with hQ
  -- positivity of the loss weight at `A = 1`
  have hnn : (0 : ℝ) ≤ Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by
    rw [Work.KMTAreas.A7.lmaxR]
    have hz : (0 : ℤ) ≤ Work.Analysis.EndVar.lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
      rw [Work.Analysis.EndVar.lmax]
      exact le_trans (Int.natCast_nonneg l₁)
        (le_trans (le_max_left _ _) (le_max_left _ _))
    exact_mod_cast hz
  have hlwpos : 0 < Work.KMTAreas.A7.lossWeight 1 ρ l₁ l₂ k₁ k₂ := by
    rw [Work.KMTAreas.A7.lossWeight, Real.rpow_one]
    exact mul_pos (by linarith) (Real.rpow_pos_of_pos (by norm_num) _)
  have hlw1 : 1 ≤ Work.KMTAreas.A7.lossWeight 1 ρ l₁ l₂ k₁ k₂ := by
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (1 * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂)
            * (2 : ℝ) ^ (1 * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) :=
          mul_le_mul (by linarith) h2 (by norm_num) (by linarith)
      _ = Work.KMTAreas.A7.lossWeight 1 ρ l₁ l₂ k₁ k₂ := by
          rw [Work.KMTAreas.A7.lossWeight, Real.rpow_one]
  by_cases hLB : L ≤ B
  · -- ##################################################################
    -- ## Case 1: `L ≤ B`
    -- ##################################################################
    have hLB' : lcL l₁ l₂ k₁ k₂ ≤ B := by rw [← hL]; exact hLB
    have hmaxB : max l₁ l₂ ≤ B :=
      le_trans (by simp only [lcL]; exact le_max_left _ _) hLB'
    -- the support
    have hsupp : ∀ n, n ∉ Finset.range ⌈(K₀ Λ : ℝ)⌉₊ →
        (fun (n : ℕ) (x : ℤ) => if ¬ goodScale Q L (Nat.floor (a n))
          then mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x else 0) n = 0 := by
      intro n hn
      have hKn : ⌈(K₀ Λ : ℝ)⌉₊ ≤ n := by
        by_contra hcon
        exact hn (Finset.mem_range.mpr (lt_of_not_ge hcon))
      have hK0n : K₀ Λ ≤ n := by
        have h1 : (K₀ Λ : ℝ) ≤ (⌈(K₀ Λ : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : ((K₀ Λ : NNReal) : ℝ) ≤ (n : ℝ) := by
          have h3 : (⌈(K₀ Λ : ℝ)⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hKn
          linarith
        exact_mod_cast h2
      have hg : goodScale Q L (Nat.floor (a n)) := by
        rw [hQ, hL]
        exact hK₀ Λ hΛ a ha ha1 l₁ l₂ k₁ k₂ hLB' n hK0n
      funext x
      dsimp only
      exact if_neg (fun h => h hg)
    -- the per-scale bound
    have hper : ∀ n ∈ Finset.range ⌈(K₀ Λ : ℝ)⌉₊,
        eLpNorm ((fun (n : ℕ) (x : ℤ) => if ¬ goodScale Q L (Nat.floor (a n))
            then mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x else 0) n)
          1 Measure.count
          ≤ ENNReal.ofReal (Cb * Cs * Cs) * eLpNorm f 2 Measure.count
            * eLpNorm g 2 Measure.count := by
      intro n _
      dsimp only
      by_cases hbad : goodScale Q L (Nat.floor (a n))
      · have hz0 : (fun x : ℤ => if ¬ goodScale Q L (Nat.floor (a n)) then
            mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x else 0) = 0 := by
          funext x
          exact if_neg (fun h => h hbad)
        rw [hz0, eLpNorm_zero]
        exact bot_le
      · have hGn : (fun x : ℤ => if ¬ goodScale Q L (Nat.floor (a n)) then
            mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x else 0)
            = mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n := by
          funext x
          exact if_pos hbad
        rw [hGn]
        obtain ⟨hXF, hXG⟩ :=
          hCs C₀ a ha1 l₁ l₂ k₁ k₂ j₁ j₂ hj₁ hj₂ hk₁ hk₂ t ht f g n hLB'
        have huS : Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))
            = Work.KMTAreas.A7.uScale ρ L := by rw [hL, lcL]
        have hfun : mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n
            = fun x : ℤ => Work.KMTAreas.A7.Btwist ρ P l₁ l₂
                (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ L))
                (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ L))
                (mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n)
                (mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) x := by
          funext x
          rw [mdlSliceJ_eq_Btwist, huS]
        rw [hfun]
        have hFtop : eLpNorm (mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) 2 Measure.count ≠ ⊤ :=
          ne_of_lt (lt_of_le_of_lt hXF
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top))
        have hGtop : eLpNorm (mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) 2 Measure.count ≠ ⊤ :=
          ne_of_lt (lt_of_le_of_lt hXG
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.eLpNorm_lt_top))
        refine (hCb l₁ l₂ (Work.KMTAreas.A7.uScale ρ L) hmaxB _ _
          (memLp_two_count_of_ne_top hFtop) (memLp_two_count_of_ne_top hGtop)).trans ?_
        calc ENNReal.ofReal Cb * eLpNorm (mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) 2 Measure.count
              * eLpNorm (mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) 2 Measure.count
            ≤ ENNReal.ofReal Cb * (ENNReal.ofReal Cs * eLpNorm f 2 Measure.count)
                * (ENNReal.ofReal Cs * eLpNorm g 2 Measure.count) := by gcongr
          _ = ENNReal.ofReal (Cb * Cs * Cs) * eLpNorm f 2 Measure.count
                * eLpNorm g 2 Measure.count := by
              rw [ENNReal.ofReal_mul (mul_nonneg hCbpos.le hCspos.le),
                ENNReal.ofReal_mul hCbpos.le]
              ring
    -- the count `#(range ⌈(K₀ Λ : ℝ)⌉₊) = ⌈(K₀ Λ : ℝ)⌉₊`
    have hcardrange : ((Finset.range ⌈(K₀ Λ : ℝ)⌉₊).card : ℝ≥0∞) = (⌈(K₀ Λ : ℝ)⌉₊ : ℝ≥0∞) := by
      rw [Finset.card_range]
    refine (varFamily_le r hr1 _ (Finset.range ⌈(K₀ Λ : ℝ)⌉₊)
      (ENNReal.ofReal (Cb * Cs * Cs) * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count)
      hsupp hper).trans ?_
    rw [hcardrange]
    -- the constant comparison
    have hK0c : (0 : ℝ) ≤ (⌈(K₀ Λ : ℝ)⌉₊ : ℝ) := by positivity
    have hKcoe : ((Real.toNNReal ((⌈(K₀ Λ : ℝ)⌉₊ : ℝ) * (4 * Cb * Cs * Cs) * 2 ^ B + 1) : NNReal) : ENNReal)
        = ENNReal.ofReal ((⌈(K₀ Λ : ℝ)⌉₊ : ℝ) * (4 * Cb * Cs * Cs) * 2 ^ B + 1) := by
      have h0 : (0 : ℝ) ≤ (⌈(K₀ Λ : ℝ)⌉₊ : ℝ) * (4 * Cb * Cs * Cs) * 2 ^ B + 1 := by positivity
      rw [ENNReal.ofReal_eq_coe_nnreal h0, Real.toNNReal_of_nonneg h0]
    have hgain : (2 : ℝ) ^ (-(B : ℝ))
        ≤ (2 : ℝ) ^ (-(1 * (max (l₁ : ℝ) (l₂ : ℝ)))) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      rw [one_mul, ← Nat.cast_max l₁ l₂]
      exact neg_le_neg (by exact_mod_cast hmaxB)
    have hprod : (2 : ℝ) ^ (B : ℝ) * (2 : ℝ) ^ (-(B : ℝ)) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel, Real.rpow_zero]
    have hnat : (2 : ℝ) ^ B = (2 : ℝ) ^ (B : ℝ) := (Real.rpow_natCast 2 B).symm
    have hlwB : (2 : ℝ) ^ (-(B : ℝ))
        ≤ Work.KMTAreas.A7.lossWeight 1 ρ l₁ l₂ k₁ k₂
          * (2 : ℝ) ^ (-(1 * (max (l₁ : ℝ) (l₂ : ℝ)))) := by
      have h2 : Work.KMTAreas.A7.lossWeight 1 ρ l₁ l₂ k₁ k₂ * (2 : ℝ) ^ (-(B : ℝ))
          ≤ Work.KMTAreas.A7.lossWeight 1 ρ l₁ l₂ k₁ k₂
            * (2 : ℝ) ^ (-(1 * (max (l₁ : ℝ) (l₂ : ℝ)))) :=
        mul_le_mul_of_nonneg_left hgain hlwpos.le
      have h3 : (2 : ℝ) ^ (-(B : ℝ)) * 1 ≤ (2 : ℝ) ^ (-(B : ℝ))
          * Work.KMTAreas.A7.lossWeight 1 ρ l₁ l₂ k₁ k₂ := by
        rw [mul_one]
        exact le_mul_of_one_le_right (by positivity) hlw1
      calc (2 : ℝ) ^ (-(B : ℝ))
          = (2 : ℝ) ^ (-(B : ℝ)) * 1 := (mul_one _).symm
        _ ≤ (2 : ℝ) ^ (-(B : ℝ)) * Work.KMTAreas.A7.lossWeight 1 ρ l₁ l₂ k₁ k₂ := h3
        _ = Work.KMTAreas.A7.lossWeight 1 ρ l₁ l₂ k₁ k₂ * (2 : ℝ) ^ (-(B : ℝ)) := by ring
        _ ≤ _ := h2
    have hreal : (⌈(K₀ Λ : ℝ)⌉₊ : ℝ) * (4 * Cb * Cs * Cs)
        ≤ ((⌈(K₀ Λ : ℝ)⌉₊ : ℝ) * (4 * Cb * Cs * Cs) * 2 ^ B + 1)
          * (Work.KMTAreas.A7.lossWeight 1 ρ l₁ l₂ k₁ k₂
            * (2 : ℝ) ^ (-(1 * (max (l₁ : ℝ) (l₂ : ℝ))))) := by
      have hA2B : (0 : ℝ) ≤ (⌈(K₀ Λ : ℝ)⌉₊ : ℝ) * (4 * Cb * Cs * Cs) * 2 ^ B := by positivity
      calc (⌈(K₀ Λ : ℝ)⌉₊ : ℝ) * (4 * Cb * Cs * Cs)
          = (⌈(K₀ Λ : ℝ)⌉₊ : ℝ) * (4 * Cb * Cs * Cs) * ((2 : ℝ) ^ B * (2 : ℝ) ^ (-(B : ℝ))) := by
            rw [hnat, hprod, mul_one]
        _ = (⌈(K₀ Λ : ℝ)⌉₊ : ℝ) * (4 * Cb * Cs * Cs) * (2 : ℝ) ^ B * (2 : ℝ) ^ (-(B : ℝ)) := by ring
        _ ≤ (⌈(K₀ Λ : ℝ)⌉₊ : ℝ) * (4 * Cb * Cs * Cs) * (2 : ℝ) ^ B
              * (Work.KMTAreas.A7.lossWeight 1 ρ l₁ l₂ k₁ k₂
                * (2 : ℝ) ^ (-(1 * (max (l₁ : ℝ) (l₂ : ℝ))))) :=
            mul_le_mul_of_nonneg_left hlwB hA2B
        _ ≤ ((⌈(K₀ Λ : ℝ)⌉₊ : ℝ) * (4 * Cb * Cs * Cs) * 2 ^ B + 1)
              * (Work.KMTAreas.A7.lossWeight 1 ρ l₁ l₂ k₁ k₂
                * (2 : ℝ) ^ (-(1 * (max (l₁ : ℝ) (l₂ : ℝ))))) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            linarith
    have hFpnn : (0 : ℝ≥0∞) ≤ eLpNorm f 2 Measure.count := zero_le
    have hGpnn : (0 : ℝ≥0∞) ≤ eLpNorm g 2 Measure.count := zero_le
    have hENN : (⌈(K₀ Λ : ℝ)⌉₊ : ℝ≥0∞) * 4 * ENNReal.ofReal (Cb * Cs * Cs)
        ≤ ((Real.toNNReal ((⌈(K₀ Λ : ℝ)⌉₊ : ℝ) * (4 * Cb * Cs * Cs) * 2 ^ B + 1) : NNReal)
            : ℝ≥0∞)
          * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 1 ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(1 * (max (l₁ : ℝ) (l₂ : ℝ))))) := by
      rw [hKcoe]
      rw [← ENNReal.ofReal_mul (by positivity :
        (0 : ℝ) ≤ (⌈(K₀ Λ : ℝ)⌉₊ : ℝ) * (4 * Cb * Cs * Cs) * 2 ^ B + 1)]
      have hleft : (⌈(K₀ Λ : ℝ)⌉₊ : ℝ≥0∞) * 4 * ENNReal.ofReal (Cb * Cs * Cs)
          = ENNReal.ofReal ((⌈(K₀ Λ : ℝ)⌉₊ : ℝ) * (4 * Cb * Cs * Cs)) := by
        rw [← ENNReal.ofReal_natCast ⌈(K₀ Λ : ℝ)⌉₊, ← ENNReal.ofReal_ofNat 4,
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (⌈(K₀ Λ : ℝ)⌉₊ : ℝ)),
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (⌈(K₀ Λ : ℝ)⌉₊ : ℝ) * 4)]
        ring_nf
      rw [hleft]
      exact ENNReal.ofReal_le_ofReal hreal
    calc (⌈(K₀ Λ : ℝ)⌉₊ : ℝ≥0∞)
          * (4 * (ENNReal.ofReal (Cb * Cs * Cs) * eLpNorm f 2 Measure.count
            * eLpNorm g 2 Measure.count))
        = ((⌈(K₀ Λ : ℝ)⌉₊ : ℝ≥0∞) * 4 * ENNReal.ofReal (Cb * Cs * Cs))
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by ring
      _ ≤ (((Real.toNNReal ((⌈(K₀ Λ : ℝ)⌉₊ : ℝ) * (4 * Cb * Cs * Cs) * 2 ^ B + 1) : NNReal)
            : ℝ≥0∞)
          * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 1 ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(1 * (max (l₁ : ℝ) (l₂ : ℝ))))))
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hENN hFpnn) hGpnn
      _ = ((Real.toNNReal ((⌈(K₀ Λ : ℝ)⌉₊ : ℝ) * (4 * Cb * Cs * Cs) * 2 ^ B + 1) : NNReal)
            : ℝ≥0∞)
          * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 1 ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(1 * (max (l₁ : ℝ) (l₂ : ℝ)))))
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by ring
  · -- ##################################################################
    -- ## Case 2: `¬ L ≤ B`
    -- ##################################################################
    have hBlt' : B < lcL l₁ l₂ k₁ k₂ := by rw [← hL]; exact lt_of_not_ge hLB
    have hzero : ∀ (n : ℕ) (x : ℤ),
        (fun (n : ℕ) (x : ℤ) => if ¬ goodScale Q L (Nat.floor (a n))
          then mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x else 0) n x = 0 := by
      intro n x
      dsimp only
      by_cases hgood : goodScale Q L (Nat.floor (a n))
      · exact if_neg (fun h => h hgood)
      · rw [if_pos hgood]
        by_contra hne
        have hcore : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n := by
          by_contra hc
          rw [mdlSliceJ_apply, if_neg hc] at hne
          exact hne rfl
        have hsplit : Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂) < Nat.floor (a n) := by
          have h := (mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n).mp hcore
          exact h.2.1
        have hnot : ¬ (8 * Q * 2 ^ (L + 1) ≤ Nat.floor (a n)) := by
          simpa only [goodScale] using hgood
        have hlt : Nat.floor (a n)
            < 8 * Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) * 2 ^ (lcL l₁ l₂ k₁ k₂ + 1) := by
          rw [not_le] at hnot
          rw [hQ, hL] at hnot
          exact hnot
        exact absurd (hB l₁ l₂ k₁ k₂ (Nat.floor (a n)) hsplit hlt) (not_le.mpr hBlt')
    have hz : (fun x : ℤ => variationalNorm r (fun n : ℕ =>
          (fun (n : ℕ) (x : ℤ) => if ¬ goodScale Q L (Nat.floor (a n))
            then mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x else 0) n x))
        = fun _ => (0 : ℝ≥0∞) := by
      funext x
      have hfam2 : (fun n : ℕ => (fun (n : ℕ) (x : ℤ) => if ¬ goodScale Q L (Nat.floor (a n))
            then mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x else 0) n x)
          = fun _ => (0 : ℂ) := by
        funext n
        exact hzero n x
      rw [hfam2]
      have h0 : variationalNorm r (fun _ : ℕ => (0 : ℂ)) = 0 := by
        have h := variationalNorm_smul (r := r) hr1 (0 : ℂ) (fun _ : ℕ => (0 : ℂ))
        rw [zero_smul, enorm_zero, zero_mul] at h
        exact h
      exact h0
    rw [hz]
    have hz2 : (fun _ : ℤ => (0 : ℝ≥0∞)) = 0 := by funext x; rfl
    rw [hz2, MeasureTheory.eLpNorm_zero]
    exact bot_le

/-- **The frozen-`t` slice on the finitely many bad scales.** -/
theorem MdlSliceBadPart (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P) :
    Work.KMTPlan.A6.BadPartProp P hd hA1 hI :=
  badPart_of_inputs P hd hA1 hI
    (fun ρ hρ hρ1 => badLmaxBound ρ hρ hρ1)
    (fun ρ hρ hρ1 B => badScalesBounded ρ hρ hρ1 B)
    (fun ρ hρ hρ1 B => slicesTwoLe P hd ρ hρ hρ1 B)

end Work.KMTPlan.A6
