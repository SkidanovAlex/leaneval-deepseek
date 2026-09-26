import Mathlib
import Submission.Work.BoxShrink.crux
import Submission.Work.BoxSweep.sweep

namespace Work.BoxShrink

open LeanEval.KnotTheory.PardonDistortion
open scoped ENNReal

noncomputable section

/-- **A level exists both in a conull set and where an integral bound permits it.**

If `f : ℝ → ℝ≥0∞` takes only the values `⊤` and natural numbers, its integral over
`(a,b)` is at most `C (b - a)`, and a set `A` is conull, then some level `s ∈ (a,b)`
lies in `A` and satisfies `f s ≤ C`.

The proof is the pigeonhole of `Work.BoxSweep.exists_le_of_lintegral_le`, with the
observation that on the conull set `A` the integrand is `≥ ⌊C⌋ + 1` if it always
exceeds `C`, while the integral of the constant `⌊C⌋ + 1` over `(a,b)` is
`(⌊C⌋ + 1)(b - a) > C (b - a)`.  The integral comparison needs no measurability of
`A`, only `MeasureTheory.lintegral_mono_ae`. -/
theorem exists_of_ae_and_lintegral {f : ℝ → ℝ≥0∞} {A : Set ℝ} {a b C : ℝ}
    (hab : a < b) (hC : 0 ≤ C)
    (hf : ∀ s, f s = ⊤ ∨ ∃ k : ℕ, f s = (k : ℝ≥0∞))
    (hA : ∀ᵐ s ∂MeasureTheory.volume, A s)
    (hint : ∫⁻ s in Set.Ioo a b, f s ≤ ENNReal.ofReal (C * (b - a))) :
    ∃ s ∈ Set.Ioo a b, A s ∧ f s ≤ ENNReal.ofReal C := by
  by_contra h
  have hlt : ∀ s ∈ Set.Ioo a b, A s → ENNReal.ofReal C < f s := by
    intro s hs hAs
    by_contra hc
    exact h ⟨s, hs, hAs, le_of_not_gt hc⟩
  have hpt : ∀ s ∈ Set.Ioo a b, A s → ((⌊C⌋₊ + 1 : ℕ) : ℝ≥0∞) ≤ f s := by
    intro s hs hAs
    rcases hf s with htop | ⟨k, hk⟩
    · rw [htop]; exact le_top
    · rw [hk]
      have h1 : C < (k : ℝ) := by
        have h2 := hlt s hs hAs
        rw [hk] at h2
        have h3 : C < ((k : NNReal) : ℝ) := (ENNReal.ofReal_lt_coe_iff hC).mp h2
        simpa using h3
      have h4 : ⌊C⌋₊ + 1 ≤ k := by
        have h5 : (⌊C⌋₊ : ℝ) ≤ C := Nat.floor_le hC
        have h6 : ((⌊C⌋₊ : ℕ) : ℝ) < (k : ℝ) := lt_of_le_of_lt h5 h1
        have h7 : (⌊C⌋₊ : ℕ) < k := by exact_mod_cast h6
        omega
      exact_mod_cast h4
  have hae : ∀ᵐ s ∂MeasureTheory.volume,
      (Set.Ioo a b).indicator (fun _ => ((⌊C⌋₊ + 1 : ℕ) : ℝ≥0∞)) s
        ≤ (Set.Ioo a b).indicator f s := by
    filter_upwards [hA] with s hAs
    by_cases hs : s ∈ Set.Ioo a b
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
      exact hpt s hs hAs
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]
  have hmono := MeasureTheory.lintegral_mono_ae hae
  have hL : ∫⁻ s, (Set.Ioo a b).indicator (fun _ => ((⌊C⌋₊ + 1 : ℕ) : ℝ≥0∞)) s
      = (((⌊C⌋₊ + 1 : ℕ)) : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
    rw [MeasureTheory.lintegral_indicator measurableSet_Ioo, MeasureTheory.setLIntegral_const,
      Real.volume_Ioo]
  rw [hL] at hmono
  have hR : ∫⁻ s, (Set.Ioo a b).indicator f s = ∫⁻ s in Set.Ioo a b, f s :=
    MeasureTheory.lintegral_indicator measurableSet_Ioo f
  rw [hR] at hmono
  have hba : 0 < b - a := sub_pos.mpr hab
  have hprod : ENNReal.ofReal (C * (b - a))
      < (((⌊C⌋₊ + 1 : ℕ)) : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
    rw [← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((⌊C⌋₊ + 1 : ℕ) : ℝ))]
    refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg hC hba.le)).mpr ?_
    have h5 : (⌊C⌋₊ : ℝ) ≤ C := Nat.floor_le hC
    have h6 : C < (((⌊C⌋₊ + 1 : ℕ)) : ℝ) := by
      have := Nat.lt_floor_add_one C
      push_cast
      linarith
    nlinarith
  exact absurd (lt_of_lt_of_le hprod (hmono.trans hint)) (lt_irrefl _)

theorem sweepNice_of_ae (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot) {d : ℝ} (hd : 0 ≤ d) (hbound : Work.Sweep.IsDistortionBound K d) : ∀ (r : ℝ) (hr : 0 < r) (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)), (∀ᵐ s ∂MeasureTheory.volume, Work.BoxShrink.SlicedSphere (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) {y : LeanEval.KnotTheory.PardonDistortion.R3 | Submission.boxNorm c σ y = s}) → ∃ s ∈ Set.Ioo r ((1 + Submission.eps) * r), Work.BoxShrink.SlicedSphere (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) {y : LeanEval.KnotTheory.PardonDistortion.R3 | Submission.boxNorm c σ y = s} ∧ (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ Submission.boxNorm c σ (K.curve t) = s}) : ENNReal) ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d) ∧ ∃ u ∈ Set.Ioo (-(Submission.eps * r)) (Submission.eps * r), (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal) ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d) := by
  intro r hr c σ hGP
  classical
  set cc : ℝ := (1 + Submission.eps) * r with hcc
  have hrcc : r ≤ cc := by rw [hcc]; nlinarith [Submission.eps_pos]
  have hrcc_lt : r < cc := by rw [hcc]; nlinarith [Submission.eps_pos]
  have hC1_0 : 0 ≤ 10 * (1 + Submission.eps) / Submission.eps * d := by
    have h' : 10 * (1 + Submission.eps) / Submission.eps = 75 := by norm_num [Submission.eps]
    rw [h']; positivity
  -- the integral pigeonhole bound of the sweep
  have hint : ∫⁻ s in Set.Ioo r cc,
        Work.Sweep.levelCount (Work.BoxSweep.boxNormCurve K c σ) (Set.Icc 0 (2 * Real.pi)) s
      ≤ ENNReal.ofReal ((10 * (1 + Submission.eps) / Submission.eps * d) * (cc - r)) := by
    refine (Work.BoxSweep.lintegral_boxNorm_levelCount_le K c σ hr hrcc).trans ?_
    refine (Work.Sweep.arclengthIn_closedBall_le (K := K) hd hbound c (R := 5 / 2 * cc)).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have h' : 10 * (1 + Submission.eps) / Submission.eps * d * (cc - r) = 10 * d * cc := by
      have heps : (Submission.eps : ℝ) ≠ 0 := ne_of_gt Submission.eps_pos
      have hccdiff : cc - r = Submission.eps * r := by rw [hcc]; ring
      rw [hccdiff, hcc]
      calc 10 * (1 + Submission.eps) / Submission.eps * d * (Submission.eps * r)
          = 10 * d * ((1 + Submission.eps) / Submission.eps * Submission.eps * r) := by ring
        _ = 10 * d * ((1 + Submission.eps) * r) := by rw [div_mul_cancel₀ _ heps]
        _ = 10 * d * ((1 + Submission.eps) * r) := by ring
    rw [h', show 4 * d * (5 / 2 * cc) = 10 * d * cc by ring]
  -- intersect the conull set of general-position levels with the pigeonhole bound
  obtain ⟨s, hs, hslice, hcnt⟩ := exists_of_ae_and_lintegral
    (f := Work.Sweep.levelCount (Work.BoxSweep.boxNormCurve K c σ) (Set.Icc 0 (2 * Real.pi)))
    (A := {s : ℝ | Work.BoxShrink.SlicedSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        {y : LeanEval.KnotTheory.PardonDistortion.R3 | Submission.boxNorm c σ y = s}})
    hrcc_lt hC1_0 (fun s => Work.BoxSweep.levelCount_eq_top_or_nat _ _ s) hGP hint
  refine ⟨s, ?_, hslice, ?_, ?_⟩
  · exact hs
  · -- count with the half-open fundamental interval
    have hconv : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          Submission.boxNorm c σ (K.curve t) = s}) : ENNReal))
        ≤ Work.Sweep.levelCount (Work.BoxSweep.boxNormCurve K c σ)
            (Set.Icc 0 (2 * Real.pi)) s := by
      rw [Work.Sweep.levelCount_eq_encard]
      refine ENat.toENNReal_le.mpr (Set.encard_le_encard ?_)
      rintro t ⟨ht1, ht2⟩
      exact ⟨Set.Ico_subset_Icc_self ht1, ht2⟩
    exact hconv.trans hcnt
  · obtain ⟨u, hu, huC⟩ := Work.BoxSweep.exists_plane_level K c σ hd hbound hr
      (lt_trans hr hs.1) (by rw [← hcc]; exact le_of_lt hs.2)
    exact ⟨u, hu, huC⟩

end

end Work.BoxShrink
