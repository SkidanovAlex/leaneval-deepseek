import ChallengeDeps
import Submission.FUP.Spec
import Submission.FUP.Reduction
import Submission.FUP.Damping

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators
open Submission.FUP

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# Assembling Theorem 1.1 from the two deep inputs

This module performs the bookkeeping of §6.2 of Cohen's paper: assuming

* Han–Schlag's conditional fractal uncertainty principle (`thm:FUP_conditional_damping`), and
* the existence of damping functions for line-porous sets (`prop:existence_damping`),

the main theorem `theorem_1_1` follows.  Nothing here uses the deep theorems themselves; their
statements live in `Submission.FUP.Spec`.
-/

/-- Degenerate case: in a one-point space, ball porosity forces `X = ∅`. -/
lemma theorem_1_1_of_subsingleton [Subsingleton ℝᵈ] (ν : ℝ) (hν : 0 < ν) :
    ∀ (h : ℝ) (X Y : Set ℝᵈ) (hX : MeasurableSet X) (hY : MeasurableSet Y),
      h ∈ Set.Ioo 0 (1 / 100) →
      X ⊆ cube (-1) 1 → PorousOnBalls ν h 1 X → Y ⊆ cube (-h⁻¹) h⁻¹ →
        PorousOnLines ν 1 h⁻¹ Y → ∀ (f : Lp ℂ 2),
          (𝓕 f : Lp ℂ 2) =ᵐ[volume.restrict Yᶜ] 0 →
          (eLpNorm (X.indicator (f : ℝᵈ → ℂ)) 2).toReal ≤ 1 * h ^ (1:ℝ) * ‖f‖ := by
  intro h X Y hXm hYm hh hXsub hXpor hYsub hYpor f hf
  have h1 : h < 1 := by linarith [hh.2]
  have hXempty : X = ∅ := by
    obtain ⟨R, hR⟩ : ∃ R : ℝ, R ∈ Set.Ioo h 1 :=
      ⟨(h + 1) / 2, ⟨by linarith, by linarith⟩⟩
    rcases hXpor (0 : ℝᵈ) R hR with ⟨x, hx, hxempty⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    have hRpos : (0 : ℝ) < R := lt_trans hh.1 hR.1
    have hzball : z ∈ closedBall x (ν * R) := by
      rw [Metric.mem_closedBall]
      have hzx : z = x := Subsingleton.elim z x
      rw [hzx, dist_self]
      exact mul_nonneg (le_of_lt hν) (le_of_lt hRpos)
    have : z ∈ closedBall x (ν * R) ∩ X := ⟨hzball, hz⟩
    rw [hxempty] at this
    exact this
  have hzero : X.indicator (f : ℝᵈ → ℂ) = 0 := by
    rw [hXempty]
    exact Set.indicator_empty' _
  rw [hzero, eLpNorm_zero, ENNReal.toReal_zero]
  exact mul_nonneg (mul_nonneg (by norm_num)
    (Real.rpow_nonneg (le_of_lt hh.1) 1)) (norm_nonneg f)

/-- **Reduction of the main theorem to the two deep inputs.** -/
theorem theorem_1_1_of_black_boxes
    (hFUP : Spec.FUP_conditional_damping_statement (d := d))
    (hExD : Spec.existence_damping_statement (d := d)) :
    ∀ (ν : ℝ), 0 < ν → ∃ (β C : ℝ), β > 0 ∧ C > 0 ∧
      ∀ (h : ℝ) (X Y : Set ℝᵈ) (hX : MeasurableSet X) (hY : MeasurableSet Y),
        h ∈ Set.Ioo 0 (1 / 100) →
        X ⊆ cube (-1) 1 → PorousOnBalls ν h 1 X → Y ⊆ cube (-h⁻¹) h⁻¹ →
          PorousOnLines ν 1 h⁻¹ Y → ∀ (f : Lp ℂ 2),
            (𝓕 f : Lp ℂ 2) =ᵐ[volume.restrict Yᶜ] 0 →
            (eLpNorm (X.indicator (f : ℝᵈ → ℂ)) 2).toReal ≤ C * h ^ β * ‖f‖ := by
  intro ν hν
  rcases eq_or_ne d 0 with hd0 | hd0
  · rw [hd0]
    exact ⟨1, 1, by norm_num, by norm_num, theorem_1_1_of_subsingleton (d := 0) ν hν⟩
  · have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    have hsqd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
    have hsqd1 : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
    -- reduce `ν` to `ν' = min ν 1/2` via porosity monotonicity
    set ν' : ℝ := min ν (1 / 2) with hν'def
    have hν'pos : 0 < ν' := lt_min hν (by norm_num)
    have hν'le : ν' ≤ ν := min_le_left _ _
    have hν'half : ν' ≤ 1 / 2 := min_le_right _ _
    -- damping parameters coming from `prop:existence_damping`
    set μ : ℝ := max (10 * Real.sqrt (d : ℝ) / ν') (3 / 2) with hμdef
    have hμ1 : 1 < μ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hμge : 10 * Real.sqrt (d : ℝ) / ν' ≤ μ := le_max_left _ _
    obtain ⟨α, c₂f, c₃f, hαlt, hαpos, hc₂c₃, hmain⟩ := hExD (ν' / 2) (by positivity) μ hμ1
    set σ : ℝ := ν' / (20 * Real.sqrt (d : ℝ)) with hσdef
    have hσpos : 0 < σ := div_pos hν'pos (by positivity)
    have hσlt : σ < 1 := by
      rw [hσdef, div_lt_one (by positivity)]
      nlinarith [hν'half, hsqd1]
    have hσ : σ ∈ Set.Ioo 0 1 := ⟨hσpos, hσlt⟩
    -- apply Han–Schlag with `c₂ = c₂f σ`
    obtain ⟨cstar, hcstar, hFUPmain⟩ :=
      hFUP ν' hν'pos hν'half (c₂f σ) α (hc₂c₃ σ hσ).1 ⟨hαpos, hαlt⟩
    -- shrink `c₃`
    set c₃' : ℝ := min (c₃f σ) (cstar / 2) with hc₃'def
    have hc₃'pos : 0 < c₃' := lt_min (hc₂c₃ σ hσ).2 (by linarith [hcstar])
    have hc₃'lt : c₃' < cstar := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hc₃'le : c₃' ≤ c₃f σ := min_le_left _ _
    obtain ⟨β, C, hβ, hC, hFUPconcl⟩ := hFUPmain c₃' ⟨hc₃'pos, hc₃'lt⟩
    refine ⟨β, C, hβ, hC, ?_⟩
    intro h X Y hXm hYm hh hXsub hXpor hYsub hYpor f hf
    have hh1 : h ∈ Set.Ioo (0:ℝ) 1 := ⟨hh.1, by linarith [hh.2]⟩
    -- porosity of `X` and `Y` with the reduced parameter `ν'`
    have hXpor' : PorousOnBalls ν' h 1 X := PorousOnBalls.mono hXpor hν'le le_rfl le_rfl hh.1
    have hYpor' : PorousOnLines ν' 1 h⁻¹ Y :=
      PorousOnLines.mono hYpor hν'le le_rfl le_rfl (by norm_num)
    refine hFUPconcl h X Y hh1 hXsub hXpor' hYsub ?_ f ?_
    · -- the damping hypothesis for all translated dilates
      intro s hs η hη
      have hs0 : 0 < s := lt_trans hh.1 hs.1
      have hslo : s ≤ 8 * Real.sqrt (d : ℝ) / ν' := by
        have h8 : (8:ℝ) ≤ 8 * Real.sqrt (d : ℝ) / ν' := by
          rw [le_div_iff₀ hν'pos]
          nlinarith [hν'half, hsqd1]
        linarith [hs.2]
      set Z : Set ℝᵈ := (fun z : ℝᵈ => η + z) ''
            (addSet ((fun y : ℝᵈ => s • y) '' Y) (cube (-4) 4)) with hZdef
      have hZpor : PorousOnLines (ν' / 2) (10 * Real.sqrt (d : ℝ) / ν') (s * h⁻¹) Z :=
        sY_cube_eta_porous η (by omega) hν'pos hs0 hslo hYpor'
      have hZporμ : PorousOnLines (ν' / 2) μ (s * h⁻¹) Z :=
        PorousOnLines.mono hZpor le_rfl hμge le_rfl (by positivity)
      -- containment in a cube of half-width `12 s/h`
      have hZsub : Z ⊆ cube (-(12 * (h / s)⁻¹)) (12 * (h / s)⁻¹) := by
        rintro x ⟨w, hw, rfl⟩
        rcases hw with ⟨a, ha, b, hb, rfl⟩
        rcases ha with ⟨y, hy, rfl⟩
        have hy' := (mem_cube (-(h⁻¹)) h⁻¹ y).mp (hYsub hy)
        have hb' := (mem_cube (-4) 4 b).mp hb
        rw [mem_cube]
        intro i
        have hη'' : |η i| ≤ h⁻¹ * s + 5 :=
          abs_le.mpr ⟨by linarith [(hη i).1], (hη i).2⟩
        have hb'' : |b i| ≤ 4 := abs_le.mpr (hb' i)
        have hy'' : |y i| ≤ h⁻¹ := abs_le.mpr (hy' i)
        have hcube : |(η + (s • y + b)) i| ≤ 2 * s * h⁻¹ + 9 := by
          have e1 : (η + (s • y + b)) i = η i + (s * y i + b i) := rfl
          rw [e1]
          calc |η i + (s * y i + b i)| ≤ |η i| + |s * y i + b i| := abs_add_le _ _
            _ ≤ |η i| + (|s * y i| + |b i|) := by
                linarith [abs_add_le (s * y i) (b i)]
            _ = |η i| + (s * |y i| + |b i|) := by rw [abs_mul, abs_of_pos hs0]
            _ ≤ 2 * s * h⁻¹ + 9 := by
                have hhinv : 0 < h⁻¹ := inv_pos.mpr hh.1
                nlinarith [hη'', hy'', hb'', hs0]
        have hle : 2 * s * h⁻¹ + 9 ≤ 12 * (h / s)⁻¹ := by
          rw [inv_div, div_eq_mul_inv]
          have hs1' : 1 < s * h⁻¹ := by
            have htmp : 1 < s / h := (one_lt_div hh.1).mpr hs.1
            rwa [div_eq_mul_inv] at htmp
          nlinarith [hs1']
        constructor <;> linarith [abs_le.mp hcube]
      have hZh : PorousOnLines (ν' / 2) μ (h / s)⁻¹ Z := by
        rw [inv_div, div_eq_mul_inv]; exact hZporμ
      -- apply `prop:existence_damping` with reciprocal scale `h/s`
      have hdamp := hmain (h / s) (div_pos hh.1 hs0) Z hZsub hZh σ hσ
      -- shrink `c₃`
      exact admitsL2Damping_mono hdamp le_rfl (le_of_lt (hc₂c₃ σ hσ).1.1) le_rfl hc₃'le
    · -- the Fourier support condition
      have h1 : ∀ᵐ ξ ∂(volume.restrict (Yᶜ)),
          ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ = 0 := hf
      have h2 : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
          ξ ∈ Yᶜ → ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ = 0 :=
        (MeasureTheory.ae_restrict_iff' hYm.compl).mp h1
      refine h2.mono (fun ξ hξ hne => ?_)
      by_contra hnot
      exact hne (hξ (by simpa [Set.mem_compl_iff] using hnot))

end Submission.FUP
