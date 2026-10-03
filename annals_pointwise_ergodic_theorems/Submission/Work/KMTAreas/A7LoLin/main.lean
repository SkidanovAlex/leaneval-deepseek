/-
# The assembly of the height-`0` linear lacunary variational estimate

This module reduces the target `Work.KMTAreas.A7.LoLinVar` to four inputs (each proved elsewhere):

* `hLow` — the bottom-height *unmodulated* low-pass lacunary variational estimate
  (`Work.KMTAreas.A7LoLin.lowpass0`, from Lépingle's inequality);
* `hFareyM` — the narrow (`Farey`-clipped) part of the *modulated* family at heights `k₁ ≥ 1`
  (`Work.KMTAreas.A7LoLin.fareyModK`);
* `hFareyD` — the narrow part of the modulated *difference* family at the bottom height
  (`Work.KMTAreas.A7LoLin.fareyModDiffK`);
* `hSingle` — the single-scale `ℓᵖ` bound `Work.KMTAreas.A7.Tle_varphiNt_single_scale`.

The index set is split into the *narrow* scales (`Farey`) and the complementary *bad* scales.  The
bad scales form an initial segment of length `O_Λ(k + Cρc)`
(`Work.KMTAreas.A7LoLin.badScale_bound_explicit`), so they are controlled by the single-scale bound
through the finite-support "spike" bound `(varsum)`
(`Submission.PointwiseErgodicTheorems.eLpNorm_variationalNorm_le_sum`).  At the bottom height
`k = 0` the modulated symbol has no uniform-in-signs multiplier bound (its value at the frequency
origin is `1`), so it is split into the unmodulated bump `varphiN` — handled by `hLow`, after
clipping to the (monotone) tail of narrow scales at the cost of a factor `3`
(`Work.KMTAreas.A7.eLpNorm_variationalNorm_clip_le`) — and the difference `varphiNt - varphiN`
(which vanishes at the origin), handled by `hFareyD`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lacunaryBumpAssembly
import Submission.Work.KMTAreas.A7.lacDilTriVar
import Submission.Work.KMTAreas.A7.bounded_of_eLpNorm_count_lt_top
import Submission.Work.KMTAreas.A7LoLin.badCount
import Submission.Work.KMTAreas.A7LoLin.lowpass0
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7LoLin

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7
open Work.Analysis.EndVar

noncomputable section

/-- **The bad (non-narrow) scales cost only a factor `O_Λ(k)`.** -/
theorem bad_prefix_bound {Λ : NNReal} (hΛ : 1 < Λ) (a : ℕ → NNReal)
    (ha : Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (M : ℕ) :
    ∀ n : ℕ, logN (Nat.floor (a n)) < (M : ℤ) →
      n < ⌈(M : ℝ) * (Real.log 2 / Real.log (Λ : ℝ))⌉₊ + 1 :=
  badScale_bound_explicit hΛ a ha ha1 M

/-- Monotonicity of a `Farey` predicate in the scale index. -/
theorem monotone_farey {Cρc ρ : ℝ} {l₁ k₁ : ℕ} {a : ℕ → NNReal} (hmono : Monotone a) :
    Monotone (fun n : ℕ => Farey Cρc ρ l₁ k₁ a n) := by
  intro m n hmn
  have h : logN (Nat.floor (a m)) ≤ logN (Nat.floor (a n)) :=
    logN_mono_aux (Nat.floor_mono (hmono hmn))
  intro hle
  simp only [Farey] at hle ⊢
  omega


/-- **The `k ≥ 1` case of the height-`0` linear lacunary variational estimate.** -/
theorem case_ge_one (ρ : ℝ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hpt : p < ⊤) (r : NNReal)
    (hr : 2 < r) (Λ : NNReal) (hΛ : 1 < Λ) (Cρc K C_s : ℝ) (hCρc : 3 ≤ Cρc) (hK : 0 < K)
    (hC_s : 0 < C_s)
    (hFareyM' : ∀ (k : ℕ), 1 ≤ k → ∀ (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1)
      (a : ℕ → NNReal) (ha : Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Tle ρ 0 (fun ξ : ℝ => if Farey Cρc ρ 0 k a n then
            varphiNt (Nat.floor (a n)) k t ξ else 0) f x)) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (K * (1 + (k : ℝ)))
            * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (hSingle' : ∀ (N k₁ : ℕ) (hNk : 2 ^ k₁ ≤ N) (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1)
      (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (Tle ρ 0 (varphiNt N k₁ t) f) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C_s * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (a : ℕ → NNReal) (ha : Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (k : ℕ) (hk : 1 ≤ k)
    (hkN : ∀ n, 2 ^ k ≤ Nat.floor (a n)) (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1)
    (f : ℤ → ℂ) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Tle ρ 0 (varphiNt (Nat.floor (a n)) k t) f x)) p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((max K (K + ((Cρc + 1) * (Real.log 2 / Real.log (Λ : ℝ)) + 2)
            * (4 * C_s))) * (1 + (k : ℝ)) ^ 2)
          * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  classical
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) hr.le
  have hp1 : (1 : ENNReal) ≤ p := hp.le
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  set cΛ : ℝ := Real.log 2 / Real.log (Λ : ℝ) with hcΛ
  have hcΛpos : 0 < cΛ := by
    rw [hcΛ]
    exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by exact_mod_cast hΛ))
  have hcΛ0 : 0 ≤ cΛ := hcΛpos.le
  set slope : ℝ := (Cρc + 1) * cΛ + 2 with hslope
  have hslope0 : 0 ≤ slope := by rw [hslope]; nlinarith
  -- trivial case: `‖f‖ = ∞`
  by_cases hftop : MeasureTheory.eLpNorm f p MeasureTheory.Measure.count = ⊤
  · rw [hftop]
    have hne : ENNReal.ofReal ((max K (K + slope * (4 * C_s))) * (1 + (k : ℝ)) ^ 2) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (by
        have h1 : 0 < max K (K + slope * (4 * C_s)) := lt_of_lt_of_le hK (le_max_left _ _)
        have h2 : (0 : ℝ) < 1 + (k : ℝ) := by positivity
        have h3 : 0 < (1 + (k : ℝ)) ^ 2 := by positivity
        exact mul_pos h1 h3)
    rw [ENNReal.mul_top hne]
    exact le_top
  obtain ⟨B, hB⟩ := bounded_of_eLpNorm_count_lt_top (p := p) hp0 (lt_top_iff_ne_top.mpr hftop)
  have hmonoA : Monotone a := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
    have h2 : Λ < a (n + 1) / a n := ha n
    have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
    have h3 : a n ≤ Λ * a n := by
      simpa using mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt hpos)
    exact le_trans h3 h1.le
  -- the good / bad split
  set G : ℕ → Prop := fun n => Farey Cρc ρ 0 k a n with hG
  have hmonoG : Monotone G := monotone_farey (Cρc := Cρc) (l₁ := 0) (k₁ := k) hmonoA
  set u : ℕ → ℤ → ℂ := fun n => Tle ρ 0 (varphiNt (Nat.floor (a n)) k t) f with hu
  have hsplit : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x)
      ≤ PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if G n then u n x else 0)
        + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if G n then 0 else u n x) := by
    intro x
    have hfun : (fun n : ℕ => u n x)
        = (fun n : ℕ => if G n then u n x else 0)
          + (fun n : ℕ => if G n then 0 else u n x) := by
      funext n
      by_cases h : G n <;> simp [h]
    rw [hfun]
    exact variationalNorm_add_le hr1 _ _
  -- the good piece
  have hgood : MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if G n then u n x else 0))
      p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (K * (1 + (k : ℝ))) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    have hEq : (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if G n then u n x else 0))
        = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Tle ρ 0
            (fun ξ : ℝ => if G n then varphiNt (Nat.floor (a n)) k t ξ else 0) f x) := by
      funext x
      congr 1
      funext n
      simp only [hu, hG]
      exact (congrFun (Tle_ite ρ 0 (Farey Cρc ρ 0 k a n)
        (φ := varphiNt (Nat.floor (a n)) k t) (f := f)) x).symm
    rw [hEq]
    exact hFareyM' k hk t ht a ha ha1 f
  -- the bad piece
  set F : ℤ := fareyK Cρc ρ 0 with hF
  set Mx : ℕ := (k - F).toNat with hMx
  set Jx : ℕ := ⌈(Mx : ℝ) * cΛ⌉₊ + 1 with hJx
  have hbad_idx : ∀ n : ℕ, ¬ G n → n < Jx := by
    intro n hn
    have h1 : F < (k : ℤ) - logN (Nat.floor (a n)) := by
      simp only [hG, Farey] at hn
      omega
    have h2 : logN (Nat.floor (a n)) < (k : ℤ) - F := by omega
    have h3 : (0 : ℤ) ≤ (k : ℤ) - F := by
      have := logN_nonneg (Nat.floor (a n)); omega
    have h4 : (Mx : ℤ) = (k : ℤ) - F := by
      simp only [hMx, Int.toNat_of_nonneg h3]
    rw [hJx, hcΛ]
    exact bad_prefix_bound hΛ a ha ha1 Mx n (by rw [h4]; exact h2)
  have hbad : MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if G n then 0 else u n x))
      p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((Jx : ℝ) * (4 * C_s))
          * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    set A : ENNReal := MeasureTheory.eLpNorm f p MeasureTheory.Measure.count with hA
    refine (eLpNorm_variationalNorm_le_sum (𝓧 := ℤ) (μ := MeasureTheory.Measure.count) hr1 hp1
      (u := fun n x => if G n then 0 else u n x) (s := Finset.range Jx) ?_ ?_).trans ?_
    · intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      have hGn : G n := by
        by_contra hc
        exact absurd (hbad_idx n hc) (not_lt.mpr hn)
      funext x
      simp [hGn]
    · intro n _
      exact (measurable_of_countable _).aestronglyMeasurable
    · have hle : ∀ n ∈ Finset.range Jx,
          4 * MeasureTheory.eLpNorm (fun x : ℤ => if G n then 0 else u n x) p
              MeasureTheory.Measure.count
            ≤ 4 * (ENNReal.ofReal C_s * A) := by
        intro n _
        refine mul_le_mul' le_rfl ?_
        by_cases hGn : G n
        · simp only [hGn, if_true, Pi.zero_apply]
          rw [MeasureTheory.eLpNorm_zero']
          exact bot_le
        · simp only [hGn, if_false, hu]
          exact hSingle' (Nat.floor (a n)) k (hkN n) t ht f
      refine (Finset.sum_le_sum hle).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [(ENNReal.ofReal_natCast Jx).symm]
      have h4 : (4 : ENNReal) * (ENNReal.ofReal C_s * A) = ENNReal.ofReal (4 * C_s) * A := by
        rw [← mul_assoc, ← ENNReal.ofReal_ofNat (4 : ℕ),
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      rw [h4, hA, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (Jx : ℝ))]
  -- combine
  have hmono : MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x)) p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if G n then u n x else 0)
          + PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if G n then 0 else u n x)) p MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (f := fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x))
      (g := fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if G n then u n x else 0)
          + PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if G n then 0 else u n x)) hsplit
  refine hmono.trans ?_
  refine (eLpNorm_add_le_ennreal
    (u := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => if G n then u n x else 0))
    (v := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => if G n then 0 else u n x)) hp1 (ne_of_lt hpt)).trans ?_
  refine (add_le_add hgood hbad).trans ?_
  set slope : ℝ := (Cρc + 1) * (Real.log 2 / Real.log (Λ : ℝ)) + 2 with hslope'
  have hFge : -Cρc - 1 ≤ (F : ℝ) := by
    have h := Int.lt_floor_add_one (-(Cρc * (2 : ℝ) ^ (ρ * ((0 : ℕ) : ℝ))))
    have h2 : (2 : ℝ) ^ (ρ * ((0 : ℕ) : ℝ)) = 1 := by norm_num
    rw [h2, mul_one] at h
    have hFdef : (F : ℝ) = ((⌊-(Cρc)⌋ : ℤ) : ℝ) := by
      simp only [hF, fareyK]
      norm_num
    rw [hFdef]
    linarith
  have hMbound : (Mx : ℝ) ≤ (k : ℝ) + Cρc + 1 := by
    have h3 : (0 : ℤ) ≤ (k : ℤ) - F := by
      have hF0 : F ≤ 0 := by
        have h1 : F = ⌊(-(Cρc) : ℝ)⌋ := by
          rw [hF, fareyK]
          norm_num
        rw [h1, Int.floor_le_iff]
        push_cast
        linarith [hCρc]
      have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
      linarith
    have h4 : (Mx : ℤ) = (k : ℤ) - F := by
      simp only [hMx, Int.toNat_of_nonneg h3]
    have h5 : ((Mx : ℤ) : ℝ) ≤ ((k : ℤ) - F : ℤ) := by
      rw [h4]
    have h6 : ((Mx : ℤ) : ℝ) = (Mx : ℝ) := by push_cast; ring
    have h7 : (((k : ℤ) - F : ℤ) : ℝ) = (k : ℝ) - (F : ℝ) := by push_cast; ring
    rw [h6, h7] at h5
    linarith
  have hJbound : (Jx : ℝ) ≤ slope * (1 + (k : ℝ)) := by
    have hJle : (Jx : ℝ) ≤ (Mx : ℝ) * cΛ + 2 := by
      have h := Nat.ceil_lt_add_one (mul_nonneg (by positivity : (0 : ℝ) ≤ (Mx : ℝ)) hcΛ0)
      rw [hJx]
      push_cast
      linarith
    have hk1 : (1 : ℝ) ≤ 1 + (k : ℝ) := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
    have hCρc0 : (0 : ℝ) ≤ Cρc := by linarith
    have h1 : (Mx : ℝ) * cΛ ≤ ((k : ℝ) + Cρc + 1) * cΛ :=
      mul_le_mul_of_nonneg_right hMbound hcΛ0
    have h2 : ((k : ℝ) + Cρc + 1) * cΛ + 2 ≤ slope * (1 + (k : ℝ)) := by
      rw [hslope']
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hexp : ((Cρc + 1) * cΛ + 2) * (1 + (k : ℝ))
          = ((k : ℝ) + Cρc + 1) * cΛ + 2 + ((k : ℝ) * Cρc * cΛ + 2 * (k : ℝ)) := by ring
      rw [hexp]
      have h4 : 0 ≤ (k : ℝ) * Cρc * cΛ + 2 * (k : ℝ) :=
        add_nonneg (mul_nonneg (mul_nonneg hk0 hCρc0) hcΛ0) (by linarith)
      linarith
    linarith
  have hAB : K * (1 + (k : ℝ)) + (Jx : ℝ) * (4 * C_s)
      ≤ max K (K + slope * (4 * C_s)) * (1 + (k : ℝ)) ^ 2 := by
    have hk1 : (1 : ℝ) ≤ 1 + (k : ℝ) := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
    have hsq : (1 + (k : ℝ)) ≤ (1 + (k : ℝ)) ^ 2 := by nlinarith
    have hmax0 : 0 ≤ max K (K + slope * (4 * C_s)) := le_trans hK.le (le_max_left _ _)
    have h4Cs : 0 ≤ 4 * C_s := by linarith
    have hsum : K * (1 + (k : ℝ)) + (Jx : ℝ) * (4 * C_s)
        ≤ (K + slope * (4 * C_s)) * (1 + (k : ℝ)) := by
      have h1 : (Jx : ℝ) * (4 * C_s) ≤ (slope * (1 + (k : ℝ))) * (4 * C_s) :=
        mul_le_mul_of_nonneg_right hJbound h4Cs
      have h2 : (slope * (1 + (k : ℝ))) * (4 * C_s) = (slope * (4 * C_s)) * (1 + (k : ℝ)) := by
        ring
      nlinarith [h1, hk1]
    calc K * (1 + (k : ℝ)) + (Jx : ℝ) * (4 * C_s)
        ≤ (K + slope * (4 * C_s)) * (1 + (k : ℝ)) := hsum
      _ ≤ max K (K + slope * (4 * C_s)) * (1 + (k : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
      _ ≤ max K (K + slope * (4 * C_s)) * (1 + (k : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hmax0
  calc ENNReal.ofReal (K * (1 + (k : ℝ))) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
        + ENNReal.ofReal ((Jx : ℝ) * (4 * C_s)) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
      = ENNReal.ofReal (K * (1 + (k : ℝ)) + (Jx : ℝ) * (4 * C_s))
          * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (max K (K + slope * (4 * C_s)) * (1 + (k : ℝ)) ^ 2)
          * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hAB) le_rfl


/-- **The `k = 0` case of the height-`0` linear lacunary variational estimate.** -/
theorem case_zero (ρ : ℝ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hpt : p < ⊤) (r : NNReal)
    (hr : 2 < r) (Λ : NNReal) (hΛ : 1 < Λ) (C_low : NNReal) (Cρc K_D C_s : ℝ) (hCρc : 3 ≤ Cρc)
    (hKD : 0 < K_D) (hC_s : 0 < C_s)
    (hLow' : ∀ (a : ℕ → NNReal) (ha : Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Tle ρ 0 (varphiN (Nat.floor (a n)) 0) f x)) p MeasureTheory.Measure.count
        ≤ (C_low : ENNReal) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (hFareyD' : ∀ (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (a : ℕ → NNReal)
      (ha : Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Tle ρ 0 (fun ξ : ℝ => if Farey Cρc ρ 0 0 a n then
            varphiNt (Nat.floor (a n)) 0 t ξ - varphiN (Nat.floor (a n)) 0 ξ else 0) f x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal K_D * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (hSingle' : ∀ (N k₁ : ℕ) (hNk : 2 ^ k₁ ≤ N) (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1)
      (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (Tle ρ 0 (varphiNt N k₁ t) f) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C_s * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (a : ℕ → NNReal) (ha : Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (t : ℝ)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (f : ℤ → ℂ) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Tle ρ 0 (varphiNt (Nat.floor (a n)) 0 t) f x)) p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (3 * (C_low : ℝ) + K_D
          + (⌈(Cρc + 1) * (Real.log 2 / Real.log (Λ : ℝ))⌉₊ + 1 : ℝ) * (4 * C_s))
          * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  classical
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) hr.le
  have hp1 : (1 : ENNReal) ≤ p := hp.le
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  set cΛ : ℝ := Real.log 2 / Real.log (Λ : ℝ) with hcΛ
  have hcΛpos : 0 < cΛ := by
    rw [hcΛ]
    exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by exact_mod_cast hΛ))
  have hcΛ0 : 0 ≤ cΛ := hcΛpos.le
  by_cases hftop : MeasureTheory.eLpNorm f p MeasureTheory.Measure.count = ⊤
  · rw [hftop]
    have hne : ENNReal.ofReal (3 * (C_low : ℝ) + K_D + (⌈(Cρc + 1) * cΛ⌉₊ + 1 : ℝ) * (4 * C_s))
        ≠ 0 := by
      refine ENNReal.ofReal_ne_zero_iff.mpr ?_
      have h1 : 0 < (⌈(Cρc + 1) * cΛ⌉₊ + 1 : ℝ) := by positivity
      nlinarith [hKD, hC_s, h1]
    rw [ENNReal.mul_top hne]
    exact le_top
  obtain ⟨B, hB⟩ := bounded_of_eLpNorm_count_lt_top (p := p) hp0 (lt_top_iff_ne_top.mpr hftop)
  have hmonoA : Monotone a := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
    have h2 : Λ < a (n + 1) / a n := ha n
    have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
    have h3 : a n ≤ Λ * a n := by
      simpa using mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt hpos)
    exact le_trans h3 h1.le
  -- the three families
  set G : ℕ → Prop := fun n => Farey Cρc ρ 0 0 a n with hG
  have hmonoG : Monotone G := monotone_farey (Cρc := Cρc) (l₁ := 0) (k₁ := 0) hmonoA
  set u0 : ℕ → ℤ → ℂ := fun n => Tle ρ 0 (varphiNt (Nat.floor (a n)) 0 t) f with hu0
  set u1 : ℕ → ℤ → ℂ := fun n => Tle ρ 0 (varphiN (Nat.floor (a n)) 0) f with hu1
  set u2 : ℕ → ℤ → ℂ := fun n => Tle ρ 0 (fun ξ : ℝ =>
      varphiNt (Nat.floor (a n)) 0 t ξ - varphiN (Nat.floor (a n)) 0 ξ) f with hu2
  -- the symbol split `u0 = u1 + u2`
  have hsplit12 : ∀ n x, u0 n x = u1 n x + u2 n x := by
    intro n x
    have hφ : Adm (Work.Analysis.IonescuWainger.iwArithFreqs ρ 0)
        (fun ξ : ℝ => varphiN (Nat.floor (a n)) 0 ξ) :=
      adm_of_bump (contDiff_varphiN (Nat.floor (a n)) 0)
        (hasCompactSupport_varphiN (Nat.floor (a n)) 0)
    have hψ : Adm (Work.Analysis.IonescuWainger.iwArithFreqs ρ 0)
        (fun ξ : ℝ => varphiNt (Nat.floor (a n)) 0 t ξ - varphiN (Nat.floor (a n)) 0 ξ) :=
      (adm_of_bump (contDiff_varphiNt (Nat.floor (a n)) 0 t)
        (hasCompactSupport_varphiNt (Nat.floor (a n)) 0 t)).sub
        (adm_of_bump (contDiff_varphiN (Nat.floor (a n)) 0)
          (hasCompactSupport_varphiN (Nat.floor (a n)) 0))
    have hadd := Tle_add_of_bounded (ρ := ρ) (l := 0)
      (φ := fun ξ : ℝ => varphiN (Nat.floor (a n)) 0 ξ)
      (ψ := fun ξ : ℝ => varphiNt (Nat.floor (a n)) 0 t ξ - varphiN (Nat.floor (a n)) 0 ξ)
      hφ hψ (f := f) hB
    have hsym : (fun ξ : ℝ => varphiN (Nat.floor (a n)) 0 ξ)
          + (fun ξ : ℝ => varphiNt (Nat.floor (a n)) 0 t ξ - varphiN (Nat.floor (a n)) 0 ξ)
        = fun ξ : ℝ => varphiNt (Nat.floor (a n)) 0 t ξ := by
      funext ξ
      simp only [Pi.add_apply]
      ring
    have h0 : u0 n = Tle ρ 0 ((fun ξ : ℝ => varphiN (Nat.floor (a n)) 0 ξ)
        + (fun ξ : ℝ => varphiNt (Nat.floor (a n)) 0 t ξ - varphiN (Nat.floor (a n)) 0 ξ)) f := by
      rw [hsym]
    rw [h0, hadd]
    simp only [hu1, hu2, Pi.add_apply]
  -- the index splitting
  have hsplitG : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u0 n x)
      ≤ PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if G n then u0 n x else 0)
        + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if G n then 0 else u0 n x) := by
    intro x
    have hfun : (fun n : ℕ => u0 n x)
        = (fun n : ℕ => if G n then u0 n x else 0) + (fun n : ℕ => if G n then 0 else u0 n x) := by
      funext n
      by_cases h : G n <;> simp [h]
    rw [hfun]
    exact variationalNorm_add_le hr1 _ _
  have hsplitG2 : ∀ x : ℤ,
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if G n then u0 n x else 0)
        ≤ PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if G n then u1 n x else 0)
          + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if G n then u2 n x else 0) := by
    intro x
    have hfun : (fun n : ℕ => if G n then u0 n x else 0)
        = (fun n : ℕ => if G n then u1 n x else 0)
          + (fun n : ℕ => if G n then u2 n x else 0) := by
      funext n
      by_cases h : G n
      · simp only [h, if_true, Pi.add_apply, hsplit12 n x]
      · simp [h]
    rw [hfun]
    exact variationalNorm_add_le hr1 _ _
  -- (i) the unmodulated narrow part
  have hclip : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if G n then u1 n x else 0)) p MeasureTheory.Measure.count
      ≤ 3 * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => u1 n x)) p MeasureTheory.Measure.count := by
    by_cases hGne : ∃ n, G n
    · have htail : ∀ n, Nat.find hGne ≤ n → G n := fun n hn => hmonoG hn (Nat.find_spec hGne)
      have hmin : ∀ n, n < Nat.find hGne → ¬ G n := fun n hn => Nat.find_min hGne hn
      exact eLpNorm_variationalNorm_clip_le hr1 p (Nat.find hGne) (fun n => u1 n)
        (fun n x => if G n then u1 n x else 0)
        (fun n hn => by funext x; rw [if_neg (hmin n hn)]; rfl)
        (fun n hn => by funext x; rw [if_pos (htail n hn)])
    · have heq : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if G n then u1 n x else 0))
          = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun _ : ℕ => (0 : ℂ)) := by
        funext x
        congr 1
        funext n
        rw [if_neg (fun hGn => hGne ⟨n, hGn⟩)]
      rw [heq, eLpNorm_variationalNorm_zero hr1 p]
      exact bot_le
  have hI : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if G n then u1 n x else 0)) p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (3 * (C_low : ℝ)) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    have h1 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => u1 n x)) p MeasureTheory.Measure.count
        ≤ (C_low : ENNReal) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
      simpa only [hu1] using hLow' a ha ha1 f
    calc _ ≤ 3 * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u1 n x))
            p MeasureTheory.Measure.count := hclip
      _ ≤ 3 * ((C_low : ENNReal) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :=
          mul_le_mul' le_rfl h1
      _ = ENNReal.ofReal (3 * (C_low : ℝ)) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
          simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat,
            ENNReal.ofReal_coe_nnreal]
          ring
  -- (ii) the modulated narrow part
  have hII : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if G n then u2 n x else 0)) p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal K_D * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    have hEq : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if G n then u2 n x else 0))
        = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Tle ρ 0
            (fun ξ : ℝ => if G n then varphiNt (Nat.floor (a n)) 0 t ξ
              - varphiN (Nat.floor (a n)) 0 ξ else 0) f x) := by
      funext x
      congr 1
      funext n
      simp only [hu2, hG]
      exact (congrFun (Tle_ite ρ 0 (Farey Cρc ρ 0 0 a n)
        (φ := fun ξ : ℝ => varphiNt (Nat.floor (a n)) 0 t ξ
          - varphiN (Nat.floor (a n)) 0 ξ) (f := f)) x).symm
    rw [hEq]
    exact hFareyD' t ht a ha ha1 f
  -- (iii) the bad part
  set F : ℤ := fareyK Cρc ρ 0 with hF
  set Mx : ℕ := (-F).toNat with hMx
  set JD : ℕ := ⌈(Mx : ℝ) * cΛ⌉₊ + 1 with hJD
  have hbad_idx : ∀ n : ℕ, ¬ G n → n < JD := by
    intro n hn
    have h1 : F < (0 : ℤ) - logN (Nat.floor (a n)) := by
      simp only [hG, Farey] at hn
      omega
    have h2 : logN (Nat.floor (a n)) < -F := by omega
    have h3 : (0 : ℤ) ≤ -F := by
      have := logN_nonneg (Nat.floor (a n)); omega
    have h4 : (Mx : ℤ) = -F := by
      simp only [hMx, Int.toNat_of_nonneg h3]
    rw [hJD, hcΛ]
    exact bad_prefix_bound hΛ a ha ha1 Mx n (by rw [h4]; exact h2)
  have hIII : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if G n then 0 else u0 n x)) p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((JD : ℝ) * (4 * C_s)) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    refine (eLpNorm_variationalNorm_le_sum (𝓧 := ℤ) (μ := MeasureTheory.Measure.count) hr1 hp1
      (u := fun n x => if G n then 0 else u0 n x) (s := Finset.range JD) ?_ ?_).trans ?_
    · intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      have hGn : G n := by
        by_contra hc
        exact absurd (hbad_idx n hc) (not_lt.mpr hn)
      funext x
      simp [hGn]
    · intro n _
      exact (measurable_of_countable _).aestronglyMeasurable
    · have hN1 : ∀ n : ℕ, 1 ≤ Nat.floor (a n) := by
        intro n
        simpa using Nat.floor_mono (ha1 n)
      have hle : ∀ n ∈ Finset.range JD,
          4 * MeasureTheory.eLpNorm (fun x : ℤ => if G n then 0 else u0 n x) p
              MeasureTheory.Measure.count
            ≤ 4 * (ENNReal.ofReal C_s * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) := by
        intro n _
        refine mul_le_mul' le_rfl ?_
        by_cases hGn : G n
        · simp only [hGn, if_true, Pi.zero_apply]
          rw [MeasureTheory.eLpNorm_zero']
          exact bot_le
        · simp only [hGn, if_false, hu0]
          exact hSingle' (Nat.floor (a n)) 0 (by simpa using hN1 n) t ht f
      refine (Finset.sum_le_sum hle).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [(ENNReal.ofReal_natCast JD).symm]
      have h4 : (4 : ENNReal) * (ENNReal.ofReal C_s * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
          = ENNReal.ofReal (4 * C_s) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
        simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]
        ring
      rw [h4, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (JD : ℝ))]
  -- combine
  have hmono : MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u0 n x)) p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if G n then u0 n x else 0)
          + PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if G n then 0 else u0 n x)) p MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
      (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u0 n x))
      (g := fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if G n then u0 n x else 0)
          + PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if G n then 0 else u0 n x)) hsplitG
  have hmono2 : MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if G n then u0 n x else 0))
        p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if G n then u1 n x else 0)
          + PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if G n then u2 n x else 0)) p MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
      (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if G n then u0 n x else 0))
      (g := fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if G n then u1 n x else 0)
          + PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if G n then u2 n x else 0)) hsplitG2
  have hsum : MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if G n then u1 n x else 0)
          + PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if G n then u2 n x else 0)) p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (3 * (C_low : ℝ)) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
        + ENNReal.ofReal K_D * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
    (eLpNorm_add_le_ennreal
      (u := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if G n then u1 n x else 0))
      (v := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if G n then u2 n x else 0)) hp1 (ne_of_lt hpt)).trans
      (add_le_add hI hII)
  have hsplitG' : MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u0 n x)) p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if G n then u1 n x else 0)
          + PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if G n then u2 n x else 0)) p MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if G n then 0 else u0 n x)) p MeasureTheory.Measure.count :=
    hmono.trans (((eLpNorm_add_le_ennreal
      (u := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if G n then u0 n x else 0))
      (v := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if G n then 0 else u0 n x)) hp1 (ne_of_lt hpt)).trans
      (add_le_add hmono2 le_rfl)))
  refine hsplitG'.trans ?_
  refine (add_le_add hsum hIII).trans ?_
  have hAB : 3 * (C_low : ℝ) + K_D + (JD : ℝ) * (4 * C_s)
      ≤ 3 * (C_low : ℝ) + K_D + (⌈(Cρc + 1) * cΛ⌉₊ + 1 : ℝ) * (4 * C_s) := by
    have hJle : (JD : ℝ) ≤ (⌈(Cρc + 1) * cΛ⌉₊ + 1 : ℝ) := by
      rw [hJD]
      have hMxle : (Mx : ℝ) ≤ (Cρc + 1) := by
        have h3 : (0 : ℤ) ≤ -F := by
          have hF0 : F ≤ 0 := by
            have h1 : F = ⌊(-(Cρc) : ℝ)⌋ := by
              rw [hF, fareyK]
              norm_num
            rw [h1, Int.floor_le_iff]
            push_cast
            linarith [hCρc]
          omega
        have h4 : (Mx : ℤ) = -F := by
          simp only [hMx, Int.toNat_of_nonneg h3]
        have h5 : ((Mx : ℤ) : ℝ) ≤ ((-F : ℤ) : ℝ) := by
          rw [h4]
        have h6 : ((Mx : ℤ) : ℝ) = (Mx : ℝ) := by push_cast; ring
        have h7 : (((-F : ℤ)) : ℝ) = -(F : ℝ) := by push_cast; ring
        have hFge : -Cρc - 1 ≤ (F : ℝ) := by
          have h := Int.lt_floor_add_one (-(Cρc * (2 : ℝ) ^ (ρ * ((0 : ℕ) : ℝ))))
          have h2 : (2 : ℝ) ^ (ρ * ((0 : ℕ) : ℝ)) = 1 := by norm_num
          rw [h2, mul_one] at h
          have hFdef : (F : ℝ) = ((⌊-(Cρc)⌋ : ℤ) : ℝ) := by
            simp only [hF, fareyK]
            norm_num
          rw [hFdef]
          linarith
        rw [h6, h7] at h5
        linarith
      have h1 : (Mx : ℝ) * cΛ ≤ (Cρc + 1) * cΛ := mul_le_mul_of_nonneg_right hMxle hcΛ0
      have h2 : (⌈(Mx : ℝ) * cΛ⌉₊ : ℝ) ≤ (⌈(Cρc + 1) * cΛ⌉₊ : ℝ) := by
        exact_mod_cast Nat.ceil_le_ceil h1
      push_cast
      linarith
    linarith [hJle, mul_le_mul_of_nonneg_right hJle (by linarith : (0 : ℝ) ≤ 4 * C_s)]
  calc ENNReal.ofReal (3 * (C_low : ℝ)) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
        + ENNReal.ofReal K_D * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
        + ENNReal.ofReal ((JD : ℝ) * (4 * C_s)) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
      = ENNReal.ofReal (3 * (C_low : ℝ) + K_D + (JD : ℝ) * (4 * C_s))
          * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
        rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (3 * (C_low : ℝ) + K_D + (⌈(Cρc + 1) * cΛ⌉₊ + 1 : ℝ) * (4 * C_s))
          * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hAB) le_rfl


/-- **The target `Work.KMTAreas.A7.LoLinVar` from its four analytic inputs.** -/
theorem LoLinVar_of_pieces (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p)
    (hpt : p < ⊤) (r : NNReal) (hr : 2 < r) (Λ : NNReal) (hΛ : 1 < Λ)
    (hLow : ∃ C : NNReal, ∀ (a : ℕ → NNReal) (ha : Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
      (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Tle ρ 0 (varphiN (Nat.floor (a n)) 0) f x)) p MeasureTheory.Measure.count
        ≤ (C : ENNReal) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (hFareyM : ∃ Cρc : ℝ, 3 ≤ Cρc ∧ ∃ K : ℝ, 0 < K ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (t : ℝ)
      (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (a : ℕ → NNReal) (ha : Lacunary Λ a)
      (ha1 : ∀ n, 1 ≤ a n) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Tle ρ 0 (fun ξ : ℝ => if Farey Cρc ρ 0 k a n then
            varphiNt (Nat.floor (a n)) k t ξ else 0) f x)) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (K * (1 + (k : ℝ))) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (hFareyD : ∃ Cρc : ℝ, 3 ≤ Cρc ∧ ∃ K : ℝ, 0 < K ∧ ∀ (t : ℝ)
      (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (a : ℕ → NNReal) (ha : Lacunary Λ a)
      (ha1 : ∀ n, 1 ≤ a n) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Tle ρ 0 (fun ξ : ℝ => if Farey Cρc ρ 0 0 a n then
            varphiNt (Nat.floor (a n)) 0 t ξ - varphiN (Nat.floor (a n)) 0 ξ else 0) f x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal K * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (hSingle : ∃ C : NNReal, 0 < C ∧ ∀ (N k₁ : ℕ) (hNk : 2 ^ k₁ ≤ N) (t : ℝ)
      (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (Tle ρ 0 (varphiNt N k₁ t) f) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C : ℝ) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :
    ∃ C : NNReal, ∀ (a : ℕ → NNReal) (ha : Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (k : ℕ)
      (hkN : ∀ n, 2 ^ k ≤ Nat.floor (a n)) (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1)
      (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Tle ρ 0 (varphiNt (Nat.floor (a n)) k t) f x))
          p MeasureTheory.Measure.count
        ≤ (C : ENNReal) * ENNReal.ofReal ((1 + (k : ℝ)) ^ 2)
            * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  classical
  obtain ⟨C_low, hLow'⟩ := hLow
  obtain ⟨Cρc_M, h3M, K_M, hKM, hFareyM'⟩ := hFareyM
  obtain ⟨Cρc_D, h3D, K_D, hKD, hFareyD'⟩ := hFareyD
  obtain ⟨C_s_nn, hCs_pos, hSingle'⟩ := hSingle
  set Cs : ℝ := (C_s_nn : ℝ) with hCs
  have hCs0 : 0 < Cs := by rw [hCs]; exact_mod_cast hCs_pos
  set cΛ : ℝ := Real.log 2 / Real.log (Λ : ℝ) with hcΛ2
  have hcΛpos : 0 < cΛ := by
    rw [hcΛ2]
    exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by exact_mod_cast hΛ))
  -- the `k ≥ 1` and `k = 0` constants
  set CTM : ℝ := max K_M (K_M + ((Cρc_M + 1) * cΛ + 2) * (4 * Cs)) with hCTM
  set CTZ : ℝ := 3 * (C_low : ℝ) + K_D + (⌈(Cρc_D + 1) * cΛ⌉₊ + 1 : ℝ) * (4 * Cs) with hCTZ
  have hCTM0 : 0 ≤ CTM := by
    rw [hCTM]
    exact le_trans hKM.le (le_max_left _ _)
  have hCTZ0 : 0 ≤ CTZ := by
    rw [hCTZ]
    have h1 : (0:ℝ) ≤ (C_low : ℝ) := C_low.coe_nonneg
    have h2 : (0:ℝ) < (⌈(Cρc_D + 1) * cΛ⌉₊ + 1 : ℝ) := by positivity
    nlinarith [hKD, hCs0]
  let Cmax : NNReal := ⟨max CTM CTZ, le_trans hCTM0 (le_max_left _ _)⟩
  have hC_eq : (Cmax : ENNReal) = ENNReal.ofReal (max CTM CTZ) := ENNReal.coe_nnreal_eq Cmax
  refine ⟨Cmax, ?_⟩
  intro a ha ha1 k hkN t ht f
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have h := case_zero ρ hρ1 p hp hpt r hr Λ hΛ C_low Cρc_D K_D Cs h3D hKD hCs0
      hLow' hFareyD'
      (fun N k₁ hNk t ht f => by
        rw [hCs]
        exact hSingle' N k₁ hNk t ht f) a ha ha1 t ht f
    refine h.trans ?_
    have h1 : ENNReal.ofReal (3 * (C_low : ℝ) + K_D
          + (↑⌈(Cρc_D + 1) * (Real.log 2 / Real.log ↑Λ)⌉₊ + 1 : ℝ) * (4 * Cs))
        ≤ (Cmax : ENNReal) * ENNReal.ofReal ((1 + ((0 : ℕ) : ℝ)) ^ 2) := by
      rw [hC_eq]
      have h2 : ENNReal.ofReal ((1 + ((0 : ℕ) : ℝ)) ^ 2) = 1 := by norm_num
      rw [h2, mul_one]
      exact ENNReal.ofReal_le_ofReal (by rw [hCTZ]; exact le_max_right _ _)
    exact mul_le_mul' h1 le_rfl
  · have h := case_ge_one ρ hρ1 p hp hpt r hr Λ hΛ Cρc_M K_M Cs h3M hKM hCs0 hFareyM'
      (fun N k₁ hNk t ht f => by
        rw [hCs]
        exact hSingle' N k₁ hNk t ht f) a ha ha1 k hkpos hkN t ht f
    refine h.trans ?_
    have hq : (0 : ℝ) ≤ (1 + (k : ℝ)) ^ 2 := by positivity
    have hmul : ENNReal.ofReal (max K_M (K_M + ((Cρc_M + 1) * cΛ + 2) * (4 * Cs))
          * (1 + (k : ℝ)) ^ 2)
        ≤ (Cmax : ENNReal) * ENNReal.ofReal ((1 + (k : ℝ)) ^ 2) := by
      rw [hC_eq]
      have hle : max K_M (K_M + ((Cρc_M + 1) * cΛ + 2) * (4 * Cs)) ≤ max CTM CTZ := by
        rw [hCTM]
        exact le_max_left _ _
      have hp0' : (0 : ℝ) ≤ max K_M (K_M + ((Cρc_M + 1) * cΛ + 2) * (4 * Cs)) :=
        le_trans hKM.le (le_max_left _ _)
      rw [ENNReal.ofReal_mul hp0']
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hle) le_rfl
    exact mul_le_mul' hmul le_rfl

end

end Work.KMTAreas.A7LoLin
