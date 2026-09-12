import Mathlib
import Submission.Threshold
import Submission.CanonAtom
import Submission.Sec3Core
import Submission.IntFun
import Submission.Prelim

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Lemma l:aux simple ac — the canonical LKR window bound

Tikhomirov 2020, Section 3.  The probability content of Lemma l:aux simple ac:

Under the canonical Bernoulli(`p`) space over `Fin ℓ` (`berP`, see
`Submission.Threshold`), suppose that among the `ℓ` coordinates of the integer
vector `x : Fin ℓ → ℤ`, the set `S` of coordinates with `|xⱼ| > N` has
`|S| ≥ δ₀·n`.  Then for *any* window of radius `N` (any centre `l : ℝ`), the
real probability that the weighted sum `Σⱼ ωⱼ·xⱼ` falls into the window is at
most `C₀/√(δ₀·n·p)` for a universal constant `C₀`:

`theorem lkr_canonical_bound`.

The proof applies the variable-radius Lévy–Kolmogorov–Rogozin inequality
(`Commons.Probability.Levy.rogozin_measurable`) on the canonical space at
radius `r := N` with radii `ρⱼ := min(|xⱼ|/3, N/2)` (else `N/2`): on the
`|S| ≥ δ₀n` coordinates with `|xⱼ| > N` the two-atom gaps are `≥ p`
(`Threshold.coord_gap_min`) and `ρⱼ ≥ N/3`, so the LKR denominator is
`≥ p·δ₀·n·N²/9`, giving the bound.

The deterministic averaging part of Lemma l:aux simple ac — the full statement,
`aux_simple_ac` — bounds the window sum `Σ_{a≤t≤b} (avgF f p ℓ x) t` for
`|b − a + 1| ≤ N` by the same universal constant times `√(δ₀·n·p)⁻¹`.  Its
proof: re-bin the window sum over the subsets `B` (`Sec3.avgF_aggregate`),
bound every combinatorial hit mass by the window measure at the interval
centre (`hit_le_measure`, via `window_containment`, `vOf_dot_eq_subSum` and
`CanonAtom.measure_ge_subsetSum`), apply `lkr_canonical_bound`, and aggregate
with the finite-window-mass lemma of `Submission.IntFun` (`norm₁ f ≤ 1`).
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Measure

namespace Submission.AuxSimpleAc

open Submission.Threshold
open Submission.CanonAtom
open Submission.Sec3
open Submission.IntFun
open Submission.Helpers
open Submission.Prelim

/-- The canonical LKR window bound (probability content of Lemma l:aux simple
ac).  There is a universal constant `C₀ > 0` such that for every `n ≥ 1`,
`δ₀ > 0`, `p ∈ (0,1/2]`, `N ≥ 1`, `ℓ`, integer vector `x`, subset
`S ⊆ {0..ℓ−1}` with `δ₀·n ≤ |S|` and `N < |xⱼ|` on `S`, and every centre
`l`, the real probability that `|Σⱼ ωⱼ·xⱼ − l| ≤ N` is at most
`C₀ / √(δ₀·n·p)`. -/
theorem lkr_canonical_bound :
    ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ {n : ℕ} (hn1 : 1 ≤ n) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {p : unitInterval}
      (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2),
      ∀ {N : ℕ} (hN1 : 1 ≤ N) {ℓ : ℕ},
        ∀ (x : Fin ℓ → ℤ) (S : Finset (Fin ℓ))
          (hScard : δ₀ * (n : ℝ) ≤ (S.card : ℝ))
          (hSbig : ∀ j : Fin ℓ, j ∈ S → (N : ℝ) < |(x j : ℝ)|),
          ∀ (l : ℝ),
            (berP (n := ℓ) p).real {ω : Fin ℓ → ℝ |
              |(∑ j : Fin ℓ, ω j * (x j : ℝ)) - l| ≤ (N : ℝ)} ≤
              C₀ / Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) := by
  rcases Commons.Probability.Levy.rogozin_measurable with ⟨C, hCpos, hCmain⟩
  let C₀ : ℝ := 24 * C + 1
  refine ⟨C₀, ?_, ?_⟩
  · dsimp [C₀]
    positivity
  · intro n hn1 δ₀ hδ₀ p hp₀ hp₁ N hN1 ℓ x S hScard hSbig l
    let r : ℝ := (N : ℝ)
    let ρ : Fin ℓ → ℝ := fun j => if (x j : ℝ) = 0 then r / 2 else min (|(x j : ℝ)| / 3) (r / 2)
    let ξ : Fin ℓ → (Fin ℓ → ℝ) → ℝ := fun j ω => ω j * (x j : ℝ)
    have hr0 : 0 < r := by
      dsimp [r]
      exact_mod_cast hN1
    have hρpos : ∀ j : Fin ℓ, 0 < ρ j := by
      intro j
      by_cases hj : (x j : ℝ) = 0
      · dsimp [ρ]
        rw [if_pos hj]
        positivity
      · dsimp [ρ]
        rw [if_neg hj]
        have hx : 0 < |(x j : ℝ)| := abs_pos.mpr hj
        exact lt_min (by positivity) (by positivity)
    have hρle : ∀ j : Fin ℓ, ρ j ≤ r := by
      intro j
      by_cases hj : (x j : ℝ) = 0
      · dsimp [ρ]
        rw [if_pos hj]
        exact half_le_self hr0.le
      · dsimp [ρ]
        rw [if_neg hj]
        exact le_trans (min_le_right _ _) (half_le_self hr0.le)
    have hξind : iIndepFun ξ (berP (n := ℓ) p) := by
      have hc : iIndepFun (fun (j : Fin ℓ) (ω : Fin ℓ → ℝ) => ω j * (x j : ℝ)) (berP (n := ℓ) p) := by
        simpa [Function.comp_def] using (ProbabilityTheory.iIndepFun.comp
          (f := fun (j : Fin ℓ) (ω : Fin ℓ → ℝ) => ω j)
          (g := fun (j : Fin ℓ) (t : ℝ) => t * (x j : ℝ)) (iIndepFun_proj p)
          (by intro j; fun_prop))
      simpa [ξ] using hc
    have hξmeas : ∀ j : Fin ℓ, Measurable (ξ j) := by
      intro j
      dsimp [ξ]
      fun_prop
    have hgapS : ∀ j : Fin ℓ, j ∈ S →
        (p : ℝ) ≤ 1 - (levyConcentration (berP (n := ℓ) p) (ξ j) (ρ j)).toReal := by
      intro j hj
      have hxj : (x j : ℝ) ≠ 0 := by
        intro hx0
        have h := hSbig j hj
        rw [hx0] at h
        simp at h
        have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
        linarith
      have hg := coord_gap_min (p := p) (hp₁) (x := fun j : Fin ℓ => (x j : ℝ)) r j hxj
      dsimp [ξ, ρ]
      rw [if_neg hxj]
      simpa using hg
    let D : ℝ := ∑ j : Fin ℓ,
        (1 - (levyConcentration (berP (n := ℓ) p) (ξ j) (ρ j)).toReal) * (ρ j) ^ 2
    have hDlow : (p : ℝ) * (r / 3) ^ 2 * δ₀ * (n : ℝ) ≤ D := by
      have htermS : ∀ j : Fin ℓ, j ∈ S → (p : ℝ) * (r / 3) ^ 2 ≤
          (1 - (levyConcentration (berP (n := ℓ) p) (ξ j) (ρ j)).toReal) * (ρ j) ^ 2 := by
        intro j hj
        have hxj : (x j : ℝ) ≠ 0 := by
          intro hx0
          have h := hSbig j hj
          rw [hx0] at h
          simp at h
          have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
          linarith
        have hgap := hgapS j hj
        have hρge : r / 3 ≤ ρ j := by
          dsimp [ρ]
          rw [if_neg hxj]
          have hbig : (N : ℝ) < |(x j : ℝ)| := hSbig j hj
          have h1 : r / 3 ≤ |(x j : ℝ)| / 3 := by
            dsimp [r]
            linarith
          have h2 : r / 3 ≤ r / 2 := by
            dsimp [r]
            linarith
          exact le_min h1 h2
        have hnonneg : 0 ≤ 1 - (levyConcentration (berP (n := ℓ) p) (ξ j) (ρ j)).toReal := by
          exact Submission.EqAux.one_sub_cf_toReal_nonneg (berP (n := ℓ) p) (ξ j) (ρ j)
        have hsq : (r / 3) ^ 2 ≤ (ρ j) ^ 2 := pow_le_pow_left₀ (by positivity) hρge 2
        calc
          (p : ℝ) * (r / 3) ^ 2 ≤
              (1 - (levyConcentration (berP (n := ℓ) p) (ξ j) (ρ j)).toReal) * (r / 3) ^ 2 := by
                exact mul_le_mul_of_nonneg_right hgap (sq_nonneg (r / 3))
          _ ≤ (1 - (levyConcentration (berP (n := ℓ) p) (ξ j) (ρ j)).toReal) * (ρ j) ^ 2 := by
                exact mul_le_mul_of_nonneg_left hsq hnonneg
      have hsumS : (∑ j ∈ S, (p : ℝ) * (r / 3) ^ 2) ≤ ∑ j ∈ S,
          (1 - (levyConcentration (berP (n := ℓ) p) (ξ j) (ρ j)).toReal) * (ρ j) ^ 2 := by
        exact Finset.sum_le_sum (by intro j hj; exact htermS j hj)
      have hsubset : (∑ j ∈ S,
          (1 - (levyConcentration (berP (n := ℓ) p) (ξ j) (ρ j)).toReal) * (ρ j) ^ 2) ≤ D := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (s := S) (t := Finset.univ)
        · intro j hj
          simp
        · intro j hjS hjU
          exact mul_nonneg (Submission.EqAux.one_sub_cf_toReal_nonneg (berP (n := ℓ) p) (ξ j) (ρ j)) (sq_nonneg (ρ j))
      calc
        (p : ℝ) * (r / 3) ^ 2 * δ₀ * (n : ℝ) = (p : ℝ) * (r / 3) ^ 2 * (δ₀ * (n : ℝ)) := by ring
        _ ≤ (p : ℝ) * (r / 3) ^ 2 * (S.card : ℝ) := by
              exact mul_le_mul_of_nonneg_left hScard (mul_nonneg (le_of_lt hp₀) (sq_nonneg (r / 3)))
        _ ≤ ∑ j ∈ S, (p : ℝ) * (r / 3) ^ 2 := by
              simpa [nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
                (Finset.card_nsmul_le_sum S (fun j => (p : ℝ) * (r / 3) ^ 2) ((p : ℝ) * (r / 3) ^ 2)
                  (by intro j hj; exact le_rfl))
        _ ≤ ∑ j ∈ S, (1 - (levyConcentration (berP (n := ℓ) p) (ξ j) (ρ j)).toReal) * (ρ j) ^ 2 := hsumS
        _ ≤ D := hsubset
    have hDpos : 0 < D := by
      have hlowpos : 0 < (p : ℝ) * (r / 3) ^ 2 * δ₀ * (n : ℝ) := by positivity
      exact lt_of_lt_of_le hlowpos hDlow
    have hLKR : sSup {a : ℝ≥0∞ | ∃ l' : ℝ, a = (berP (n := ℓ) p)
          {x : Fin ℓ → ℝ | |(∑ j : Fin ℓ, ξ j x) - l'| ≤ r}} ≤
        ENNReal.ofReal (C * r / Real.sqrt D) := by
      refine hCmain ℓ (Fin ℓ → ℝ) (berP (n := ℓ) p) ξ hξind hξmeas r hr0 ρ hρpos hρle ?_
      simpa [D, levyConcentration] using hDpos
    have hnonneg : 0 ≤ C * r / Real.sqrt D := by positivity
    have hcf_le : (berP (n := ℓ) p).real {ω : Fin ℓ → ℝ |
          |(∑ j : Fin ℓ, ξ j ω) - l| ≤ r} ≤ C * r / Real.sqrt D := by
      simpa [levyConcentration] using
        (real_mem_le_of_levyConcentration_le (berP (n := ℓ) p)
          (fun ω : Fin ℓ → ℝ => ∑ j : Fin ℓ, ξ j ω) (t := r) (τ := C * r / Real.sqrt D)
          hnonneg hLKR l)
    -- arithmetic: C·r/√D ≤ C·r/((r/3)·√(δ₀np)) = 3C/√(δ₀np) ≤ (24C+1)/√(δ₀np)
    have hsqD : Real.sqrt ((p : ℝ) * (r / 3) ^ 2 * δ₀ * (n : ℝ)) =
        (r / 3) * Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) := by
      rw [show (p : ℝ) * (r / 3) ^ 2 * δ₀ * (n : ℝ) = (δ₀ * (n : ℝ) * (p : ℝ)) * (r / 3) ^ 2 by ring]
      rw [Real.sqrt_mul (by positivity : 0 ≤ δ₀ * (n : ℝ) * (p : ℝ)) ((r / 3) ^ 2)]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
      · ring
      · positivity
    have hDsqrt' : (r / 3) * Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) ≤ Real.sqrt D := by
      rw [← hsqD]
      exact Real.sqrt_le_sqrt hDlow
    have hr3pos : 0 < r / 3 := by positivity
    have hsqrtbasepos : 0 < Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) := by
      exact Real.sqrt_pos.2 (by positivity)
    have hrec : 1 / Real.sqrt D ≤ 1 / ((r / 3) * Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ))) := by
      exact one_div_le_one_div_of_le (mul_pos hr3pos hsqrtbasepos) hDsqrt'
    have hdenEq : 1 / ((r / 3) * Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ))) =
        (3 / r) / Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) := by
      field_simp [show r ≠ 0 by positivity, show Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) ≠ 0 by positivity]
    have hmain : C * r / Real.sqrt D ≤ (24 * C + 1) / Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) := by
      calc
        C * r / Real.sqrt D = C * r * (1 / Real.sqrt D) := by ring
        _ ≤ C * r * (1 / ((r / 3) * Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)))) := by
              exact mul_le_mul_of_nonneg_left hrec (mul_nonneg (le_of_lt hCpos) hr0.le)
        _ = C * r * ((3 / r) / Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ))) := by rw [hdenEq]
        _ = (3 * C) / Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) := by
              field_simp [show r ≠ 0 by positivity]
        _ ≤ (24 * C + 1) / Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) := by
              have hnum : 3 * C ≤ 24 * C + 1 := by nlinarith [hCpos]
              exact div_le_div_of_nonneg_right hnum (le_of_lt hsqrtbasepos)
    have hLHS : (berP (n := ℓ) p).real {ω : Fin ℓ → ℝ |
        |(∑ j : Fin ℓ, ω j * (x j : ℝ)) - l| ≤ (N : ℝ)} ≤ C * r / Real.sqrt D := by
      simpa [ξ, r] using hcf_le
    exact le_trans hLHS hmain

/-! ## The deterministic averaging part (window sum bound) -/

/-- Dot product of the characteristic vector of `B` with `x` equals the
subset sum `subSum x B`. -/
lemma vOf_dot_eq_subSum {ℓ : ℕ} (x : Fin ℓ → ℤ) (B : Finset (Fin ℓ)) :
    (∑ j : Fin ℓ, vOf B j * (x j : ℝ)) = ((subSum x B : ℤ) : ℝ) := by
  classical
  have hBfilt : (Finset.univ : Finset (Fin ℓ)).filter (fun j => j ∈ B) = B := by
    ext j
    simp
  calc
    (∑ j : Fin ℓ, vOf B j * (x j : ℝ)) = ∑ j : Fin ℓ, (if j ∈ B then (x j : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h : j ∈ B <;> simp [vOf, h]
    _ = ∑ j ∈ (Finset.univ : Finset (Fin ℓ)).filter (fun j => j ∈ B), (x j : ℝ) := by
        exact (Finset.sum_filter (s := (Finset.univ : Finset (Fin ℓ)))
          (p := fun j => j ∈ B) (f := fun j : Fin ℓ => (x j : ℝ))).symm
    _ = ∑ j ∈ B, (x j : ℝ) := by rw [hBfilt]
    _ = ((∑ j ∈ B, x j : ℤ) : ℝ) := by
        rw [Int.cast_sum]
    _ = ((subSum x B : ℤ) : ℝ) := by rfl

/-- Window containment: if `s = t + d_B` for some `t ∈ [a,b]` (with `a ≤ b`,
`b − a + 1 ≤ N`), then the displacement `d_B` stays within distance `N` of the
centre `l := s − (a+b)/2`. -/
lemma window_containment {N : ℕ} {ℓ : ℕ} {x : Fin ℓ → ℤ} (a b : ℤ) (hab : a ≤ b)
    (hlen : (b : ℤ) - a + 1 ≤ (N : ℤ)) (B : Finset (Fin ℓ)) {s : ℤ}
    (hs : s ∈ (Finset.Icc a b).image (fun t : ℤ => t + subSum x B)) :
    |((subSum x B : ℤ) : ℝ) - ((s : ℝ) - (((a : ℝ) + (b : ℝ)) / 2))| ≤ (N : ℝ) := by
  classical
  rcases Finset.mem_image.mp hs with ⟨t, htI, htEq⟩
  have hmemI : a ≤ t ∧ t ≤ b := Finset.mem_Icc.mp htI
  have hcr : (t : ℝ) + ((subSum x B : ℤ) : ℝ) = (s : ℝ) := by
    exact_mod_cast htEq
  have hd : ((subSum x B : ℤ) : ℝ) = (s : ℝ) - (t : ℝ) := by
    linarith
  rw [hd]
  have hmid : |((s : ℝ) - (t : ℝ)) - ((s : ℝ) - (((a : ℝ) + (b : ℝ)) / 2))| =
      |(((a : ℝ) + (b : ℝ)) / 2) - (t : ℝ)| := by ring_nf
  rw [hmid]
  have ha_t : (a : ℝ) ≤ (t : ℝ) := by exact_mod_cast hmemI.1
  have ht_b : (t : ℝ) ≤ (b : ℝ) := by exact_mod_cast hmemI.2
  have htbd : |(((a : ℝ) + (b : ℝ)) / 2) - (t : ℝ)| ≤ ((b : ℝ) - (a : ℝ)) / 2 := by
    rw [abs_sub_comm]
    have h1 : (t : ℝ) - ((a : ℝ) + (b : ℝ)) / 2 ≤ ((b : ℝ) - (a : ℝ)) / 2 := by nlinarith
    have h2 : -(((b : ℝ) - (a : ℝ)) / 2) ≤ (t : ℝ) - ((a : ℝ) + (b : ℝ)) / 2 := by nlinarith
    exact abs_le.mpr ⟨h2, h1⟩
  have hlenR : ((b : ℝ) - (a : ℝ)) / 2 ≤ (N : ℝ) := by
    have hc : (b : ℝ) - (a : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hlen
    nlinarith
  exact le_trans htbd hlenR

/-- The canonical weighted-sum event is measurable. -/
lemma measurable_weightedSum {ℓ : ℕ} (x : Fin ℓ → ℤ) (l : ℝ) (r : ℝ) :
    MeasurableSet {ω : Fin ℓ → ℝ | |(∑ j : Fin ℓ, ω j * (x j : ℝ)) - l| ≤ r} := by
  have hg : Continuous (fun ω : Fin ℓ → ℝ => |(∑ j : Fin ℓ, ω j * (x j : ℝ)) - l|) := by
    fun_prop
  have hset : {ω : Fin ℓ → ℝ | |(∑ j : Fin ℓ, ω j * (x j : ℝ)) - l| ≤ r} =
      (fun ω : Fin ℓ → ℝ => |(∑ j : Fin ℓ, ω j * (x j : ℝ)) - l|) ⁻¹' (Set.Iic r) := by
    ext ω
    simp
  rw [hset]
  exact (isClosed_Iic.measurableSet : MeasurableSet (Set.Iic r)).preimage hg.measurable

/-- For every `s`, the combinatorial hit mass of `s` (over all subsets `B`
whose translated window `[a,b] + d_B` contains `s`) is bounded by the real
probability that the canonical weighted sum falls within distance `N` of the
centre `l := s − (a+b)/2`. -/
lemma hit_le_measure {N : ℕ} {ℓ : ℕ} (p : unitInterval) (x : Fin ℓ → ℤ) {a b : ℤ}
    (hab : a ≤ b) (hlen : (b : ℤ) - a + 1 ≤ (N : ℤ)) (s : ℤ) :
    (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
      wB ℓ p B * if s ∈ (Finset.Icc a b).image (fun t : ℤ => t + subSum x B) then 1 else 0) ≤
      (berP (n := ℓ) p).real {ω : Fin ℓ → ℝ |
        |(∑ j : Fin ℓ, ω j * (x j : ℝ)) - ((s : ℝ) - (((a : ℝ) + (b : ℝ)) / 2))| ≤ (N : ℝ)} := by
  classical
  let l : ℝ := (s : ℝ) - (((a : ℝ) + (b : ℝ)) / 2)
  let E : Set (Fin ℓ → ℝ) := {ω : Fin ℓ → ℝ |
    |(∑ j : Fin ℓ, ω j * (x j : ℝ)) - l| ≤ (N : ℝ)}
  have hE : MeasurableSet E := by
    dsimp [E, l]
    exact measurable_weightedSum x ((s : ℝ) - (((a : ℝ) + (b : ℝ)) / 2)) (N : ℝ)
  have hge := measure_ge_subsetSum (ℓ := ℓ) p E hE
  -- per-term comparison: s ∈ J_B ⟹ vOf B ∈ E
  have hterm : ∀ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
      wB ℓ p B * (if s ∈ (Finset.Icc a b).image (fun t : ℤ => t + subSum x B) then 1 else 0) ≤
      wB ℓ p B * (if vOf B ∈ E then 1 else 0) := by
    intro B hB
    by_cases hsB : s ∈ (Finset.Icc a b).image (fun t : ℤ => t + subSum x B)
    · have hE' : vOf B ∈ E := by
        dsimp [E, l]
        rw [vOf_dot_eq_subSum x B]
        simpa using (window_containment (N := N) (x := x) a b hab hlen B hsB)
      rw [if_pos hsB, if_pos hE']
    · rw [if_neg hsB]
      by_cases hE'' : vOf B ∈ E
      · rw [if_pos hE'']
        simpa using (wB_nonneg ℓ p B)
      · rw [if_neg hE'']
  calc
    (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
        wB ℓ p B * if s ∈ (Finset.Icc a b).image (fun t : ℤ => t + subSum x B) then 1 else 0)
        ≤ ∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
            wB ℓ p B * (if vOf B ∈ E then 1 else 0) := Finset.sum_le_sum hterm
    _ ≤ (berP (n := ℓ) p).real E := hge
    _ = (berP (n := ℓ) p).real {ω : Fin ℓ → ℝ |
        |(∑ j : Fin ℓ, ω j * (x j : ℝ)) - ((s : ℝ) - (((a : ℝ) + (b : ℝ)) / 2))| ≤ (N : ℝ)} := by
        rfl

/-- The window sum of the averaged function is bounded by the total mass of
`f` times the universal window bound (Lemma l:aux simple ac — deterministic
statement). -/
theorem aux_simple_ac :
    ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ {n : ℕ} (hn1 : 1 ≤ n) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {p : unitInterval}
      (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2),
      ∀ {N : ℕ} (hN1 : 1 ≤ N) {ℓ : ℕ},
        ∀ {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
          (hfmass : norm₁ f ≤ 1),
        ∀ (x : Fin ℓ → ℤ) (S : Finset (Fin ℓ))
          (hScard : δ₀ * (n : ℝ) ≤ (S.card : ℝ))
          (hSbig : ∀ j : Fin ℓ, j ∈ S → (N : ℝ) < |(x j : ℝ)|),
          ∀ (a b : ℤ) (hlen : (b : ℤ) - a + 1 ≤ (N : ℤ)),
            (∑ t ∈ Finset.Icc a b, avgF f p ℓ x t) ≤
              C₀ / Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) := by
  rcases lkr_canonical_bound with ⟨C₀, hC₀pos, hC₀main⟩
  refine ⟨C₀, hC₀pos, ?_⟩
  intro n hn1 δ₀ hδ₀ p hp₀ hp₁ N hN1 ℓ f hfpos hfsum hfmass x S hScard hSbig a b hlen
  let c₀ : ℝ := C₀ / Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ))
  have hc₀pos : 0 < c₀ := by
    dsimp [c₀]
    positivity
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn1
  have hwin : ∀ l : ℝ, (berP (n := ℓ) p).real {ω : Fin ℓ → ℝ |
      |(∑ j : Fin ℓ, ω j * (x j : ℝ)) - l| ≤ (N : ℝ)} ≤ c₀ := by
    intro l
    dsimp [c₀]
    exact hC₀main hn1 hδ₀ hp₀ hp₁ hN1 x S hScard hSbig l
  by_cases hab : a ≤ b
  · let W : Finset ℤ := (Finset.univ : Finset (Fin ℓ)).powerset.biUnion
      (fun B : Finset (Fin ℓ) => (Finset.Icc a b).image (fun t : ℤ => t + subSum x B))
    let hit : ℤ → ℝ := fun s =>
      ∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
        wB ℓ p B * if s ∈ (Finset.Icc a b).image (fun t : ℤ => t + subSum x B) then 1 else 0
    have hagg : (∑ t ∈ Finset.Icc a b, avgF f p ℓ x t) = ∑ s ∈ W, f s * hit s := by
      simpa [W, hit] using (avgF_aggregate (f := f) (p := p) (ℓ := ℓ) (x := x) (Finset.Icc a b))
    calc
      (∑ t ∈ Finset.Icc a b, avgF f p ℓ x t)
          = ∑ s ∈ W, f s * hit s := hagg
      _ ≤ ∑ s ∈ W, f s * c₀ := by
            apply Finset.sum_le_sum
            intro s hs
            have hh : hit s ≤ c₀ := by
              calc
                hit s
                    ≤ (berP (n := ℓ) p).real {ω : Fin ℓ → ℝ |
                        |(∑ j : Fin ℓ, ω j * (x j : ℝ)) - ((s : ℝ) - (((a : ℝ) + (b : ℝ)) / 2))| ≤ (N : ℝ)} := by
                        dsimp [hit]
                        exact hit_le_measure (ℓ := ℓ) p x hab hlen s
                _ ≤ c₀ := hwin ((s : ℝ) - (((a : ℝ) + (b : ℝ)) / 2))
            exact mul_le_mul_of_nonneg_left hh (hfpos s)
      _ = c₀ * (∑ s ∈ W, f s) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s hs
            ring
      _ ≤ c₀ * norm₁ f := by
            exact mul_le_mul_of_nonneg_left (Finset_sum_le_norm₁ hfpos hfsum W) hc₀pos.le
      _ ≤ c₀ := by
            simpa using (mul_le_mul_of_nonneg_left hfmass hc₀pos.le)
      _ = C₀ / Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) := by
            rfl
  · have hba : b < a := lt_of_not_ge hab
    have hI : (Finset.Icc a b : Finset ℤ) = ∅ := by
      ext t
      simp [Finset.mem_Icc]
      omega
    rw [hI]
    simp
    have hc₀pos' : 0 < c₀ := by
      dsimp [c₀]
      exact div_pos hC₀pos (Real.sqrt_pos.2 (by positivity))
    exact le_of_lt hc₀pos'  -- hmm simpler: positivity might work; keep explicit

end Submission.AuxSimpleAc
