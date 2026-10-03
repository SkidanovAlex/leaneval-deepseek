/-
# Auxiliary (sorry-free) material for `Work.KMTAreas.A7Lpd.lacunaryMaxConst`

For the target `lacunaryMaxConst` this file provides:

* the **telescoping** `∑_{i<K}(T_i f − T_{i+1} f) = T_0 f − T_K f`;
* the **two-point chain bound**: `‖a K − a 0‖ₑ ≤ varPart r a` for `2 ≤ r`;
* hence the **elementary reduction**: the supremum over `K` of the partial sums of the increments
  is dominated pointwise by the variation part `varPart 3` of the walk `k ↦ T_k f`;
* therefore: **if** `‖varPart 3 (k ↦ T_k f)‖_{ℓᵖ} ≤ C ‖(∑_k ‖T_k f − T_{k+1} f‖²)^{1/2}‖_{ℓᵖ}`
  (the classical Lépingle / Jones–Seeger–Wright real-variable step; requested separately as
  `Work.KMTAreas.A7Lpd.varPartSqFun`), **then** `lacunaryMaxConst` holds.

This module is deliberately self-contained and sorry-free, so that it can be imported by the
requested lemma without contamination.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.variationalNorm_le_sqSum
import Submission.Work.KMTAreas.A7.lacDilTriVar

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7Lpd

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- `(x ^ r) ^ (1/r) = x` in `ℝ≥0∞` for `r ≠ 0`. -/
private lemma rpow_rpow_inv' {r : ℝ} (hr : r ≠ 0) (x : ℝ≥0∞) : (x ^ r) ^ (1 / r) = x := by
  rw [one_div]; exact ENNReal.rpow_rpow_inv hr x

/-- **Telescoping of the two-point increments.** -/
lemma sum_range_kmtProj_sub (ρ : ℝ) (l : ℕ) (m₀ : ℕ) (f : ℤ → ℂ) (x : ℤ) (K : ℕ) :
    (∑ i ∈ Finset.range K,
        (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x
          - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x))
      = Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (0 : ℤ))) f x
        - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (K : ℤ))) f x := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, ih]; ring

/-- **The two-point chain.**  For `2 ≤ r`, the jump `a K − a 0` of the two-point chain `(0,K)` is
bounded by the variation part `varPart r a` of the variational norm. -/
lemma enorm_sub_zero_le_varPart {r : NNReal} (hr : 2 ≤ r) (a : ℕ → ℂ) (K : ℕ) :
    ‖a K - a 0‖ₑ ≤ Submission.PointwiseErgodicTheorems.varPart r a := by
  have hr0 : (r : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (r : ℝ) := by
      have h1 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      linarith
    exact this.ne'
  rw [Submission.PointwiseErgodicTheorems.varPart]
  refine le_iSup_of_le 1 ?_
  refine le_iSup_of_le (fun i : ℕ => if i = 0 then 0 else K) ?_
  refine le_iSup_of_le ?_ ?_
  · refine monotone_nat_of_le_succ fun i => ?_
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp
    · have h1 : i ≠ 0 := h.ne'
      have h2 : i + 1 ≠ 0 := by omega
      simp only [h1, h2, if_false]
      exact le_rfl
  · have hval : (fun i : Fin 1 =>
          a ((fun i : ℕ => if i = 0 then 0 else K) (i + 1))
            - a ((fun i : ℕ => if i = 0 then 0 else K) i))
        = fun _ : Fin 1 => a K - a 0 := by
      funext i
      have hi : (i : ℕ) = 0 := by omega
      rw [hi]
      simp
    rw [hval]
    have h1 := Work.KMTAreas.A7.ofReal_norm_toLp r hr 1 (fun _ : Fin 1 => a K - a 0)
    rw [Fin.sum_univ_one] at h1
    rw [h1, rpow_rpow_inv' hr0]

/-- **Elementary reduction.**  For `2 ≤ r` the supremum over `K` of the partial sums of the
increments is dominated, pointwise in `x`, by the variation part of the walk `k ↦ T_k f x`. -/
lemma iSup_partialSum_le_varPart (ρ : ℝ) (l : ℕ) (m₀ : ℕ) (f : ℤ → ℂ) {r : NNReal}
    (hr : 2 ≤ r) (x : ℤ) :
    (⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
        (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x
          - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x))‖ₑ)
      ≤ Submission.PointwiseErgodicTheorems.varPart r
          (fun k : ℕ => Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (k : ℤ))) f x) := by
  refine iSup_le fun K => ?_
  rw [sum_range_kmtProj_sub ρ l m₀ f x K]
  have hneg : Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (0 : ℤ))) f x
        - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (K : ℤ))) f x
      = -(Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (K : ℤ))) f x
          - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (0 : ℤ))) f x) := by ring
  rw [hneg, enorm_neg]
  have h := enorm_sub_zero_le_varPart hr
    (fun k : ℕ => Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (k : ℤ))) f x) K
  simpa only [Nat.cast_zero] using h

/-- **The reduction of the target to the variation part.**  If the variation part of the low-pass
family `k ↦ kmtProj ρ l (-(m₀+k)) f` is dominated in `ℓᵖ` by the band square function of its
increments (with an `l`-free constant), then `lacunaryMaxConst` holds. -/
theorem lacunaryMaxConst_of_varPart_le_sqFun (ρ : ℝ) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤)
    (hvar : ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (l : ℕ) (m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => Submission.PointwiseErgodicTheorems.varPart 3
            (fun k : ℕ => Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (k : ℤ))) f x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ => (∑' k : ℕ,
            ‖Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((k : ℕ) : ℤ))) f x
              - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((k + 1 : ℕ)) : ℤ))) f x‖ ^ (2 : ℝ))
            ^ (1 / 2 : ℝ)) p MeasureTheory.Measure.count) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (l : ℕ) (m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
            (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x
              - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x))‖ₑ)
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C *
            MeasureTheory.eLpNorm (fun x : ℤ => (∑' k : ℕ,
              ‖Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((k : ℕ) : ℤ))) f x
                - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((k + 1 : ℕ)) : ℤ))) f x‖ ^ (2 : ℝ))
                ^ (1 / 2 : ℝ)) p MeasureTheory.Measure.count := by
  obtain ⟨Cρ, hCρ, C, hC, hvar'⟩ := hvar
  refine ⟨Cρ, hCρ, C, hC, ?_⟩
  intro l m₀ hgood f
  have hp0 : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  have hpT : p ≠ ⊤ := ne_of_lt hptop
  have hmono := Work.KMTAreas.A7.eLpNorm_mono_ennreal
    (u := fun x : ℤ => (⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
        (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x
          - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x))‖ₑ))
    (v := fun x : ℤ => Submission.PointwiseErgodicTheorems.varPart 3
        (fun k : ℕ => Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (k : ℤ))) f x))
    (fun x => iSup_partialSum_le_varPart ρ l m₀ f (by norm_num) x) hp0 hpT
    (μ := MeasureTheory.Measure.count)
  exact hmono.trans (hvar' l m₀ hgood f)

end

end Work.KMTAreas.A7Lpd
