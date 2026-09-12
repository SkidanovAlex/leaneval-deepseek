/-
The `eq aux` Littlewood–Offord dichotomy for weighted Bernoulli sums
(Tikhomirov 2020, equation (eq: aux ...)):

  cf(Σ_i b_i x_i, r(p)) ≤ 1 − p   for some r(p) > 0 and all unit vectors x,

with the two branches:
  · large-coordinate case (`bernoulli_weighted_sum_large_coord_le`, Prelim):
    if some |x_j| > 2r then every interval of length 2r captures the sum with
    probability at most 1−p, by conditioning on all coordinates but j;
  · small-coordinate case: via the Lévy–Kolmogorov–Rogozin inequality
    (to be supplied), with per-coordinate atom bound `coord_cf_atom_le`
    below.

This file is a repository for the eq-aux infrastructure that does not need the
LKR inequality itself (which is delegated to the shared Commons).
-/
import Mathlib
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Bernoulli
import Submission.Prelim
import Submission.AuxSingleVector
import ChallengeDeps

set_option autoImplicit false

namespace Submission.EqAux

noncomputable section

open Matrix MeasureTheory ProbabilityTheory Measure Filter unitInterval
open scoped ENNReal BigOperators

/-- Per-coordinate atom bound for the Lévy concentration function: for a
Bernoulli(p)-valued `b` and any real `x` with `2·t < |x|`, the two atoms of
`b·x` (at `0` and `x`, a distance `|x|` apart) cannot both fall into any
interval of length `2t`, so the concentration function at scale `t` is at most
the mass `1 − p` of the lighter single atom. -/
theorem coord_cf_atom_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] {b : Ω → ℝ} (hb_meas : Measurable b)
    {p : I} (hp : (p : ℝ) ≤ 1 / 2) (hb_law : P.map b = bernoulliMeasure 1 0 p)
    {x t : ℝ} (htsep : 2 * t < |x|) :
    Submission.Helpers.levyConcentration P (fun ω => b ω * x) t ≤
      ENNReal.ofReal (1 - (p : ℝ)) := by
  classical
  unfold Submission.Helpers.levyConcentration
  rw [sSup_le_iff]
  intro a ha
  rcases ha with ⟨l, rfl⟩
  let S : Set ℝ := {a : ℝ | |a * x - l| ≤ t}
  have hSmeas : MeasurableSet S := by
    have hg : Continuous (fun a : ℝ => |a * x - l|) := by
      refine continuous_abs.comp ?_
      refine Continuous.sub ?_ continuous_const
      exact continuous_id.mul continuous_const
    have hset : S = (fun a : ℝ => |a * x - l|) ⁻¹' Set.Iic t := by
      ext a
      simp [S, Set.mem_Iic]
    rw [hset]
    exact (isClosed_Iic.measurableSet : MeasurableSet (Set.Iic t)).preimage hg.measurable
  have hset : {ω : Ω | |b ω * x - l| ≤ t} = b ⁻¹' S := by
    ext ω
    simp [S]
  calc
    P {ω : Ω | |b ω * x - l| ≤ t} = P (b ⁻¹' S) := by rw [hset]
    _ = (P.map b) S := (Measure.map_apply hb_meas hSmeas).symm
    _ = (bernoulliMeasure 1 0 p) S := by rw [hb_law]
    _ ≤ ENNReal.ofReal (1 - (p : ℝ)) := by
          have hber := Submission.Prelim.bernoulliLaw_interval_le (p := p) hp (c := (0 : ℝ)) (x := x) (l := l) (r := t) htsep
          simpa [S] using hber

/-! ## ENNReal→real bookkeeping for the concentration function

The Lévy–Kolmogorov–Rogozin branch of `eq aux` needs per-coordinate bounds on
`1 − cf_i` (real values).  These lemmas convert the ENNReal bounds
(`cf ≤ ofReal(1−p)`, `cf ≤ 1`) into real bounds on `(cf).toReal`. -/

/-- `cf ≤ ofReal a` (with `0 ≤ a`) implies `cf.toReal ≤ a`. -/
lemma cf_toReal_le_of_le_ofReal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (ξ : Ω → ℝ) {t : ℝ} {a : ℝ} (ha : 0 ≤ a)
    (h : Submission.Helpers.levyConcentration P ξ t ≤ ENNReal.ofReal a) :
    (Submission.Helpers.levyConcentration P ξ t).toReal ≤ a := by
  have htop : Submission.Helpers.levyConcentration P ξ t ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have htr := (ENNReal.toReal_le_toReal htop ENNReal.ofReal_ne_top).mpr h
  simpa [ENNReal.toReal_ofReal ha] using htr

/-- `cf ≤ 1` on a probability space, so `1 − cf.toReal ≥ 0`. -/
lemma one_sub_cf_toReal_nonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (ξ : Ω → ℝ) (t : ℝ) :
    0 ≤ 1 - (Submission.Helpers.levyConcentration P ξ t).toReal := by
  have hle1 : Submission.Helpers.levyConcentration P ξ t ≤ (1 : ENNReal) :=
    Submission.Helpers.levyConcentration_le_one P ξ t
  have htop : Submission.Helpers.levyConcentration P ξ t ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num : (1 : ENNReal) ≠ ⊤) hle1
  have htr := (ENNReal.toReal_le_toReal htop (by norm_num : (1 : ENNReal) ≠ ⊤)).mpr hle1
  have : (Submission.Helpers.levyConcentration P ξ t).toReal ≤ 1 := by simpa using htr
  linarith

/-- For a non-zero weight `x`, the two atoms of `b·x` are farther than the
radius `|x|/3` apart, so the per-coordinate atom bound gives
`1 − cf(b·x, |x|/3) ≥ p`. -/
lemma one_sub_coord_cf_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] {b : Ω → ℝ} (hb_meas : Measurable b)
    {p : I} (hp : (p : ℝ) ≤ 1 / 2) (hb_law : P.map b = bernoulliMeasure 1 0 p)
    {x : ℝ} (hx : x ≠ 0) :
    (p : ℝ) ≤ 1 - (Submission.Helpers.levyConcentration P (fun ω => b ω * x) (|x| / 3)).toReal := by
  have hsep : 2 * (|x| / 3) < |x| := by
    have hx0 : 0 < |x| := abs_pos.mpr hx
    nlinarith
  have hatom := Submission.EqAux.coord_cf_atom_le P hb_meas hp hb_law (x := x) (t := |x| / 3) hsep
  have htr : (Submission.Helpers.levyConcentration P (fun ω => b ω * x) (|x| / 3)).toReal ≤ 1 - (p : ℝ) := by
    exact cf_toReal_le_of_le_ofReal P (fun ω => b ω * x) (t := |x| / 3) (a := 1 - (p : ℝ)) (by
      have hp1 : (p : ℝ) ≤ 1 := p.property.2
      linarith) hatom
  linarith

/-! ## R3: the denominator lower bound (`D ≥ p/9`)

These are the inputs to the Lévy–Kolmogorov–Rogozin branch of `eq aux`: with
per-coordinate radii `ρ_i := if x i = 0 then r₀/2 else |x i|/3` (positive,
and `≤ r₀` under the small-coordinate hypothesis) the atom bounds give
`1 − cf_i ≥ p` on nonzero coordinates, so the LKR denominator
`D := Σ_i (1 − cf_i)·ρ_i²` is at least `p/9` for a unit vector `x`. -/

/-- Per-coordinate contribution: for any real `x` and `r₀`, with
`ρ := if x = 0 then r₀/2 else |x|/3`, `(p/9)·x² ≤ (1 − cf(b·x, ρ))·ρ²`. -/
lemma coord_contrib {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] {b : Ω → ℝ} (hb_meas : Measurable b)
    {p : I} (hp : (p : ℝ) ≤ 1 / 2) (hb_law : P.map b = bernoulliMeasure 1 0 p)
    (x : ℝ) (r₀ : ℝ) :
    ((p : ℝ) / 9) * x ^ 2 ≤
      (1 - (Submission.Helpers.levyConcentration P (fun ω => b ω * x)
        (if x = 0 then r₀ / 2 else |x| / 3)).toReal) *
        (if x = 0 then r₀ / 2 else |x| / 3) ^ 2 := by
  by_cases hx0 : x = 0
  · have hif : (if x = 0 then r₀ / 2 else |x| / 3) = r₀ / 2 := by simp [hx0]
    rw [hif]
    simp [hx0]
    have hnonneg : 0 ≤ 1 - (Submission.Helpers.levyConcentration P (fun ω : Ω => 0) (r₀ / 2)).toReal :=
      one_sub_cf_toReal_nonneg P (fun ω : Ω => 0) (r₀ / 2)
    exact mul_nonneg hnonneg (sq_nonneg (r₀ / 2))
  · have hif : (if x = 0 then r₀ / 2 else |x| / 3) = |x| / 3 := by simp [hx0]
    rw [hif]
    have hge : (p : ℝ) ≤ 1 - (Submission.Helpers.levyConcentration P (fun ω => b ω * x) (|x| / 3)).toReal :=
      one_sub_coord_cf_ge P hb_meas hp hb_law hx0
    have hsq : (|x| / 3) ^ 2 = x ^ 2 / 9 := by
      rw [div_pow]
      congr 1
      rw [sq_abs]
      norm_num
    rw [hsq]
    have hx29 : 0 ≤ x ^ 2 / 9 := by positivity
    calc
      ((p : ℝ) / 9) * x ^ 2 = (p : ℝ) * (x ^ 2 / 9) := by ring
      _ ≤ (1 - (Submission.Helpers.levyConcentration P (fun ω => b ω * x) (|x| / 3)).toReal) * (x ^ 2 / 9) := by
            exact mul_le_mul_of_nonneg_right hge hx29

/-- Denominator lower bound: for unit `x` and per-coordinate radii
`ρ_i := if x i = 0 then r₀/2 else |x i|/3`,
`p/9 ≤ D := Σ_i (1 − cf(b_i·x_i, ρ_i))·ρ_i²`. -/
lemma denom_lower {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] {b : Fin n → Ω → ℝ} (hb_meas : ∀ i, Measurable (b i))
    {p : I} (hp : (p : ℝ) ≤ 1 / 2) (hb_law : ∀ i, HasLaw (b i) (bernoulliMeasure 1 0 p) P)
    {x : Fin n → ℝ} (hx : (∑ i, (x i) ^ 2) = 1) (r₀ : ℝ) :
    (p : ℝ) / 9 ≤
      ∑ i : Fin n,
        (1 - (Submission.Helpers.levyConcentration P (fun ω => b i ω * x i)
          (if x i = 0 then r₀ / 2 else |x i| / 3)).toReal) *
          (if x i = 0 then r₀ / 2 else |x i| / 3) ^ 2 := by
  classical
  have hterm : ∀ i : Fin n,
      ((p : ℝ) / 9) * (x i) ^ 2 ≤
        (1 - (Submission.Helpers.levyConcentration P (fun ω => b i ω * x i)
          (if x i = 0 then r₀ / 2 else |x i| / 3)).toReal) *
            (if x i = 0 then r₀ / 2 else |x i| / 3) ^ 2 := by
    intro i
    exact coord_contrib P (hb_meas i) hp (hb_law i).map_eq (x i) r₀
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun i hi => hterm i)
  calc
    (p : ℝ) / 9 = ((p : ℝ) / 9) * (∑ i : Fin n, (x i) ^ 2) := by
          rw [hx]
          ring
    _ = ∑ i : Fin n, ((p : ℝ) / 9) * (x i) ^ 2 := by
          rw [Finset.mul_sum]
    _ ≤ ∑ i : Fin n,
        (1 - (Submission.Helpers.levyConcentration P (fun ω => b i ω * x i)
          (if x i = 0 then r₀ / 2 else |x i| / 3)).toReal) *
            (if x i = 0 then r₀ / 2 else |x i| / 3) ^ 2 := hsum


end

end Submission.EqAux
