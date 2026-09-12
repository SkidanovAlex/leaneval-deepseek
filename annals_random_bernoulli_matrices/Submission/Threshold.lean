import Mathlib
import Submission.Helpers
import Submission.EqAux
import Submission.Concentration
import Submission.Commons.Probability.Levy.rogozin_measurable
import Submission.Commons.LinearAlgebra.Net.incompressible_spread

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Measure
open scoped ENNReal BigOperators

noncomputable section

/-!
# Layer 5 step 0: threshold function and Lemma l:threshold

Tikhomirov 2020, "Proof of Theorem A": for `x ∈ S^{n−1}` and `L > 0` the
*threshold* is the supremum of all `t ∈ (0,1]` with
`cf(Σ_i b_i x_i, t) > L·t` where `b_i` are independent Bernoulli(`p`)
variables.  Lemma l:threshold bounds the threshold of every
`(δ,ν)`-incompressible unit vector by `K/√n`.

This module builds the canonical Bernoulli(`p`) product space
`(Fin n → ℝ)` and proves the threshold lemma from the Commons
Lévy--Kolmogorov--Rogozin inequality (`rogozin_measurable`) and the
Commons incompressibility lemma (`incompressible_spread`).
-/

namespace Submission.Threshold

open Commons.LinearAlgebra.Net

/-! ## Canonical Bernoulli(p) product space -/

/-- Canonical space for `n` independent Bernoulli(`p`) coordinates. -/
def berP {n : ℕ} (p : unitInterval) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => bernoulliMeasure 1 0 p)

lemma isProbabilityMeasure_berP {n : ℕ} (p : unitInterval) :
    IsProbabilityMeasure (berP (n := n) p) := by
  unfold berP
  infer_instance

instance instIsProbabilityMeasure_berP {n : ℕ} (p : unitInterval) :
    IsProbabilityMeasure (berP (n := n) p) :=
  isProbabilityMeasure_berP p

/-- The coordinate projections are independent under `berP`. -/
lemma iIndepFun_proj {n : ℕ} (p : unitInterval) :
    iIndepFun (fun (i : Fin n) (ω : Fin n → ℝ) => ω i) (berP (n := n) p) := by
  unfold berP
  exact iIndepFun_pi (X := fun (_ : Fin n) => (id : ℝ → ℝ)) (fun _ => aemeasurable_id)

/-- The law of a coordinate projection is Bernoulli(`p`). -/
lemma marginal_proj {n : ℕ} (p : unitInterval) (i : Fin n) :
    (berP (n := n) p).map (fun ω : Fin n → ℝ => ω i) = bernoulliMeasure 1 0 p := by
  have hfun : (fun ω : Fin n → ℝ => ω i) =
      Function.eval (α := Fin n) (β := fun _ : Fin n => ℝ) i := by
    funext ω
    rfl
  unfold berP
  rw [hfun]
  exact (MeasureTheory.measurePreserving_eval (ι := Fin n) (α := fun _ : Fin n => ℝ)
    (μ := fun _ : Fin n => bernoulliMeasure 1 0 p) (i := i)).map_eq

/-- `HasLaw` form of the coordinate projection law. -/
lemma hasLaw_proj {n : ℕ} (p : unitInterval) (i : Fin n) :
    HasLaw (fun ω : Fin n → ℝ => ω i) (bernoulliMeasure 1 0 p) (berP (n := n) p) := by
  constructor
  · exact (measurable_pi_apply (δ := Fin n) (X := fun _ : Fin n => ℝ) i).aemeasurable
  · exact marginal_proj p i

/-! ## Lévy concentration of weighted Bernoulli sums and the threshold -/

/-- Lévy concentration function of the random sum `Σ_i ω_i·x_i` on the canonical space. -/
def cfP {n : ℕ} (p : unitInterval) (x : Fin n → ℝ) (t : ℝ) : ℝ≥0∞ :=
  Submission.Helpers.levyConcentration (berP (n := n) p)
    (fun ω : Fin n → ℝ => ∑ i : Fin n, ω i * x i) t

/-- Threshold of a unit vector `x` with slope `L` (Tikhomirov 2020). -/
def threshold {n : ℕ} (p : unitInterval) (x : Fin n → ℝ) (L : ℝ) : ℝ :=
  sSup {t : ℝ | 0 < t ∧ t ≤ 1 ∧ ENNReal.ofReal (L * t) < cfP (n := n) p x t}

/-- The threshold is at most one. -/
lemma threshold_le_one {n : ℕ} (p : unitInterval) (x : Fin n → ℝ) (L : ℝ) :
    threshold p x L ≤ 1 := by
  unfold threshold
  apply Real.sSup_le
  · intro t ht
    exact ht.2.1
  · norm_num

/-- If the concentration function is below the slope `L·τ` for all radii above
`K/√n`, then the threshold is at most `K/√n`. -/
lemma threshold_le_of_cf_le {n : ℕ} {p : unitInterval} {x : Fin n → ℝ} {L K : ℝ} {hn : 1 ≤ n}
    (hK : 0 < K)
    (hcf : ∀ τ : ℝ, K / Real.sqrt (n : ℝ) < τ →
      cfP (n := n) p x τ ≤ ENNReal.ofReal (L * τ)) :
    threshold p x L ≤ K / Real.sqrt (n : ℝ) := by
  unfold threshold
  apply Real.sSup_le
  · intro t ht
    by_contra hle
    have hKt : K / Real.sqrt (n : ℝ) < t := lt_of_not_ge hle
    have hcf' : cfP (n := n) p x t ≤ ENNReal.ofReal (L * t) := hcf t hKt
    exact (not_le_of_gt ht.2.2) hcf'
  · have hsq : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    positivity

/-! ## Lemma l:threshold

For every `p ∈ (0,1/2]`, `δ,ν ∈ (0,1]` there are `K > 0`, `L₀ ≥ 1` such that for
every `n ≥ 1` and every `(δ,ν)`-incompressible unit vector `x` and every
`L ≥ L₀`: `threshold p x L ≤ K/√n`.
The proof follows the paper: the incompressibility of `x` implies (by the
Commons lemma `incompressible_spread`) that many coordinates are of size at
least `ν/(2√n)`; the per-coordinate atom bounds give LKR gaps `≥ p` on those
coordinates, so the LKR denominator is `≥ p·ν⁴·δ/72` (for radii above
`ν/(3√n)`), and the LKR inequality bounds the concentration function by a
linear function of the radius with slope `C·√72/(ν²·√(p·δ))`. -/

/-- Per-coordinate gap at radius `min (|x_i|/3) (τ/2)`: for a nonzero
coordinate, `(1 − cf(ω_i·x_i, ρ_i)) ≥ p`. -/
lemma coord_gap_min {n : ℕ} {p : unitInterval} (hp₁ : (p : ℝ) ≤ 1 / 2)
    {x : Fin n → ℝ} (τ : ℝ) (i : Fin n) (hxi : x i ≠ 0) :
    (p : ℝ) ≤ 1 - (Submission.Helpers.levyConcentration (berP (n := n) p)
      (fun ω : Fin n → ℝ => ω i * x i) (min (|x i| / 3) (τ / 2))).toReal := by
  -- the coordinate b := ω ↦ ω i has the Bernoulli(p) law
  have hbmeas : Measurable (fun ω : Fin n → ℝ => ω i) := by fun_prop
  -- atom bound at the larger radius |x_i|/3
  have hatom : (p : ℝ) ≤ 1 - (Submission.Helpers.levyConcentration (berP (n := n) p)
      (fun ω : Fin n → ℝ => ω i * x i) (|x i| / 3)).toReal := by
    have hsep : 2 * (|x i| / 3) < |x i| := by
      have hx0 : 0 < |x i| := abs_pos.mpr hxi
      nlinarith
    have hle := Submission.EqAux.coord_cf_atom_le (P := berP (n := n) p) (b := fun ω : Fin n → ℝ => ω i)
      (hb_meas := hbmeas) (hp := hp₁) (hb_law := marginal_proj p i) (x := x i) (t := |x i| / 3) hsep
    have htr : (Submission.Helpers.levyConcentration (berP (n := n) p)
        (fun ω : Fin n → ℝ => ω i * x i) (|x i| / 3)).toReal ≤ 1 - (p : ℝ) := by
      exact Submission.EqAux.cf_toReal_le_of_le_ofReal (berP (n := n) p)
        (fun ω : Fin n → ℝ => ω i * x i) (t := |x i| / 3) (a := 1 - (p : ℝ)) (by
          have hp1 : (p : ℝ) ≤ 1 := p.property.2
          linarith) hle
    linarith
  -- monotonicity in the radius: min ≤ |x_i|/3
  have hmin : min (|x i| / 3) (τ / 2) ≤ |x i| / 3 := min_le_left _ _
  have hmono : Submission.Helpers.levyConcentration (berP (n := n) p)
      (fun ω : Fin n → ℝ => ω i * x i) (min (|x i| / 3) (τ / 2)) ≤
      Submission.Helpers.levyConcentration (berP (n := n) p)
      (fun ω : Fin n → ℝ => ω i * x i) (|x i| / 3) := by
    exact Submission.Helpers.levyConcentration_mono (berP (n := n) p)
      (fun ω : Fin n → ℝ => ω i * x i) hmin
  -- convert ENNReal monotonicity to real gaps
  have hle1 : (Submission.Helpers.levyConcentration (berP (n := n) p)
      (fun ω : Fin n → ℝ => ω i * x i) (min (|x i| / 3) (τ / 2))).toReal ≤
      (Submission.Helpers.levyConcentration (berP (n := n) p)
      (fun ω : Fin n → ℝ => ω i * x i) (|x i| / 3)).toReal := by
    have htop1 : Submission.Helpers.levyConcentration (berP (n := n) p)
        (fun ω : Fin n → ℝ => ω i * x i) (min (|x i| / 3) (τ / 2)) ≠ ⊤ :=
      ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
        (Submission.Helpers.levyConcentration_le_one (berP (n := n) p)
          (fun ω : Fin n → ℝ => ω i * x i) (min (|x i| / 3) (τ / 2)))
    have htop2 : Submission.Helpers.levyConcentration (berP (n := n) p)
        (fun ω : Fin n → ℝ => ω i * x i) (|x i| / 3) ≠ ⊤ :=
      ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
        (Submission.Helpers.levyConcentration_le_one (berP (n := n) p)
          (fun ω : Fin n → ℝ => ω i * x i) (|x i| / 3))
    exact (ENNReal.toReal_le_toReal htop1 htop2).2 hmono
  linarith

/-- If `τ ≥ ν/(3√n)` and `i ∈ σ` (so `|x_i| ≥ ν/(2√n)`), the radius
`ρ_i := min (|x_i|/3) (τ/2)` satisfies `(ρ_i)^2 ≥ (ν/(6√n))^2 = ν²/(36n)`. -/
lemma radius_sq_lower {n : ℕ} {ν τ : ℝ} {x : Fin n → ℝ} (σ : Finset (Fin n))
    (hn0 : 0 < (n : ℝ)) (hν₀ : 0 < ν)
    (hτge : ν / (3 * Real.sqrt (n : ℝ)) ≤ τ)
    (hσcoord : ∀ i : Fin n, i ∈ σ → ν / (2 * Real.sqrt (n : ℝ)) ≤ |x i|)
    (i : Fin n) (hi : i ∈ σ) :
    (ν / (6 * Real.sqrt (n : ℝ))) ^ 2 ≤
      (min (|x i| / 3) (τ / 2)) ^ 2 := by
  have hc1 : ν / (6 * Real.sqrt (n : ℝ)) ≤ |x i| / 3 := by
    have hbase := hσcoord i hi
    have hd : (ν / (2 * Real.sqrt (n : ℝ))) / 3 ≤ |x i| / 3 :=
      div_le_div_of_nonneg_right hbase (by norm_num : (0 : ℝ) ≤ 3)
    have hEq : (ν / (2 * Real.sqrt (n : ℝ))) / 3 = ν / (6 * Real.sqrt (n : ℝ)) := by
      rw [div_div]
      congr 1
      ring
    rwa [hEq] at hd
  have hc2 : ν / (6 * Real.sqrt (n : ℝ)) ≤ τ / 2 := by
    have hd : (ν / (3 * Real.sqrt (n : ℝ))) / 2 ≤ τ / 2 :=
      div_le_div_of_nonneg_right hτge (by norm_num : (0 : ℝ) ≤ 2)
    have hEq : (ν / (3 * Real.sqrt (n : ℝ))) / 2 = ν / (6 * Real.sqrt (n : ℝ)) := by
      rw [div_div]
      congr 1
      ring
    rwa [hEq] at hd
  have hmin : ν / (6 * Real.sqrt (n : ℝ)) ≤ min (|x i| / 3) (τ / 2) := le_min hc1 hc2
  have hA0 : 0 ≤ ν / (6 * Real.sqrt (n : ℝ)) := by positivity
  exact pow_le_pow_left₀ hA0 hmin 2


/-- Denominator lower bound for the LKR application in Lemma l:threshold.
With gaps `≥ p` on the spread set `σ` (whose coordinates are `≥ ν/(2√n)`)
and radii `ρ_i := if x_i = 0 then τ/2 else min (|x_i|/3) (τ/2)`, for
`τ ≥ ν/(3√n)` the LKR denominator `D := Σ_i (1−cf_i)·ρ_i²` is at least
`p·ν⁴·δ/72 > 0`. -/
lemma denom_lower_bound {n : ℕ} {p : unitInterval} (_hp₁ : (p : ℝ) ≤ 1 / 2)
    {δ ν τ : ℝ} (hδ₀ : 0 < δ) (hν₀ : 0 < ν)
    {x : Fin n → ℝ} {σ : Finset (Fin n)}
    (hn0 : 0 < (n : ℝ))
    (hσcard : ((σ.card : ℝ) ≥ (1 / 2) * ν ^ 2 * δ * (n : ℝ)))
    (hσcoord : ∀ i : Fin n, i ∈ σ → ν / (2 * Real.sqrt (n : ℝ)) ≤ |x i|)
    (_hτ0 : 0 < τ) (hτge : ν / (3 * Real.sqrt (n : ℝ)) ≤ τ)
    (hgap : ∀ i : Fin n, i ∈ σ →
      (p : ℝ) ≤ 1 - (Submission.Helpers.levyConcentration (berP (n := n) p)
        (fun ω : Fin n → ℝ => ω i * x i) (min (|x i| / 3) (τ / 2))).toReal) :
    (p : ℝ) * ν ^ 4 * δ / 72 ≤
      ∑ i : Fin n,
        (1 - (Submission.Helpers.levyConcentration (berP (n := n) p)
          (fun ω : Fin n → ℝ => ω i * x i)
            (if x i = 0 then τ / 2 else min (|x i| / 3) (τ / 2))).toReal) *
          (if x i = 0 then τ / 2 else min (|x i| / 3) (τ / 2)) ^ 2 := by
  classical
  let ρlow : ℝ := ν / (6 * Real.sqrt (n : ℝ))
  let term : Fin n → ℝ := fun i =>
    (1 - (Submission.Helpers.levyConcentration (berP (n := n) p)
      (fun ω : Fin n → ℝ => ω i * x i)
        (if x i = 0 then τ / 2 else min (|x i| / 3) (τ / 2))).toReal) *
      (if x i = 0 then τ / 2 else min (|x i| / 3) (τ / 2)) ^ 2
  -- per-coordinate lower bound on σ
  have htermσ : ∀ i : Fin n, i ∈ σ → (p : ℝ) * ρlow ^ 2 ≤ term i := by
    intro i hi
    have hxi0 : x i ≠ 0 := by
      intro hx0
      have h := hσcoord i hi
      rw [hx0] at h
      have hsqpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
      have : 0 < ν / (2 * Real.sqrt (n : ℝ)) := div_pos hν₀ (by positivity)
      linarith
    have hri : min (|x i| / 3) (τ / 2) = if x i = 0 then τ / 2 else min (|x i| / 3) (τ / 2) := by
      simp [hxi0]
    have hg := hgap i hi
    have h2 : ρlow ^ 2 ≤ (min (|x i| / 3) (τ / 2)) ^ 2 := by
      exact radius_sq_lower σ hn0 hν₀ hτge hσcoord i hi
    -- term i ≥ gap·(min ...)^2 = (1 − cf_i at radius min)·min^2
    have hnonneg_cf : 0 ≤ 1 - (Submission.Helpers.levyConcentration (berP (n := n) p)
        (fun ω : Fin n → ℝ => ω i * x i) (min (|x i| / 3) (τ / 2))).toReal := by
      exact Submission.EqAux.one_sub_cf_toReal_nonneg (berP (n := n) p)
        (fun ω : Fin n → ℝ => ω i * x i) (min (|x i| / 3) (τ / 2))
    have hmul : (p : ℝ) * ρlow ^ 2 ≤
        (1 - (Submission.Helpers.levyConcentration (berP (n := n) p)
          (fun ω : Fin n → ℝ => ω i * x i) (min (|x i| / 3) (τ / 2))).toReal) *
          (min (|x i| / 3) (τ / 2)) ^ 2 := by
      exact mul_le_mul hg h2 (by positivity) hnonneg_cf
    -- term i (with `if x i = 0 ...`) equals the min-radius expression since x i ≠ 0
    simpa [term, hxi0] using hmul
  -- sums: Σ_{i∈σ} ≥ card σ · (p·ρlow²)
  have hsum_ge : (σ.card : ℝ) * ((p : ℝ) * ρlow ^ 2) ≤ ∑ i ∈ σ, term i := by
    have hsum := Finset.card_nsmul_le_sum σ term ((p : ℝ) * ρlow ^ 2) (by
      intro i hi
      exact htermσ i hi)
    -- hsum : σ.card • (p·ρlow²) ≤ ∑ i ∈ σ, term i
    simpa [nsmul_eq_mul] using hsum
  -- Σ_{i∈σ} ≤ Σ_{i∈univ} = D
  have hsubset : ∑ i ∈ σ, term i ≤ ∑ i : Fin n, term i := by
    have hs := Finset.sum_le_sum_of_subset_of_nonneg (s := σ) (t := Finset.univ)
      (by intro i hi; simp) (by
        intro i hi hiσ
        have hc1 : 0 ≤ 1 - (Submission.Helpers.levyConcentration (berP (n := n) p)
            (fun ω : Fin n → ℝ => ω i * x i)
              (if x i = 0 then τ / 2 else min (|x i| / 3) (τ / 2))).toReal := by
          exact Submission.EqAux.one_sub_cf_toReal_nonneg (berP (n := n) p)
            (fun ω : Fin n → ℝ => ω i * x i)
              (if x i = 0 then τ / 2 else min (|x i| / 3) (τ / 2))
        have hsq : 0 ≤ (if x i = 0 then τ / 2 else min (|x i| / 3) (τ / 2)) ^ 2 :=
          sq_nonneg (if x i = 0 then τ / 2 else min (|x i| / 3) (τ / 2))
        exact mul_nonneg hc1 hsq)
    simpa [term] using hs
  -- cardinal arithmetic: card σ · (p·ρlow²) ≥ (1/2)ν²δn · p · ν²/(36n) = p·ν⁴·δ/72
  have hcard : (1 / 2) * ν ^ 2 * δ * (n : ℝ) ≤ (σ.card : ℝ) := hσcard
  have hlow_nonneg : 0 ≤ (p : ℝ) * ρlow ^ 2 := by
    have hp0 : 0 ≤ (p : ℝ) := p.property.1
    nlinarith [sq_nonneg ρlow, hp0]
  have hmul_card : (1 / 2) * ν ^ 2 * δ * (n : ℝ) * ((p : ℝ) * ρlow ^ 2) ≤
      (σ.card : ℝ) * ((p : ℝ) * ρlow ^ 2) :=
    mul_le_mul_of_nonneg_right hcard hlow_nonneg
  have hρlow2 : ρlow ^ 2 = ν ^ 2 / (36 * (n : ℝ)) := by
    dsimp [ρlow]
    rw [div_pow]
    have hden : (6 * Real.sqrt (n : ℝ)) ^ 2 = 36 * (n : ℝ) := by
      have hsq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hn0)
      nlinarith
    rw [hden]
  have hfinal_arith : (p : ℝ) * ν ^ 4 * δ / 72 ≤
      (1 / 2) * ν ^ 2 * δ * (n : ℝ) * ((p : ℝ) * ρlow ^ 2) := by
    rw [hρlow2]
    have hn0' : (n : ℝ) ≠ 0 := ne_of_gt hn0
    field_simp [hn0']
    nlinarith
  calc
    (p : ℝ) * ν ^ 4 * δ / 72
        ≤ (1 / 2) * ν ^ 2 * δ * (n : ℝ) * ((p : ℝ) * ρlow ^ 2) := hfinal_arith
    _ ≤ (σ.card : ℝ) * ((p : ℝ) * ρlow ^ 2) := hmul_card
    _ ≤ ∑ i ∈ σ, term i := hsum_ge
    _ ≤ ∑ i : Fin n, term i := hsubset
    _ = ∑ i : Fin n,
          (1 - (Submission.Helpers.levyConcentration (berP (n := n) p)
            (fun ω : Fin n → ℝ => ω i * x i)
              (if x i = 0 then τ / 2 else min (|x i| / 3) (τ / 2))).toReal) *
            (if x i = 0 then τ / 2 else min (|x i| / 3) (τ / 2)) ^ 2 := by
      rfl



/-- Lemma l:threshold (Tikhomirov 2020). For every `p ∈ (0,1/2]`,
`δ,ν ∈ (0,1]` there are `K > 0` and `L₀ ≥ 1` such that for every `n ≥ 1`
and every `(δ,ν)`-incompressible unit vector `x` and every `L ≥ L₀`, the
threshold `thres_p(x,L)` is at most `K/√n`. -/
theorem threshold_le_K_div_sqrt {p : unitInterval} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {δ ν : ℝ} (hδ₀ : 0 < δ) (hν₀ : 0 < ν) :
    ∃ K L₀ : ℝ, 0 < K ∧ 1 ≤ L₀ ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ (x : Fin n → ℝ), sqNorm x = 1 →
      (∀ z : Fin n → ℝ, sqNorm (x - z) ≤ ν ^ 2 →
        ¬ (((Finset.univ.filter (fun i => z i ≠ 0)).card : ℝ) ≤ δ * (n : ℝ))) →
      ∀ L : ℝ, L₀ ≤ L → threshold p x L ≤ K / Real.sqrt (n : ℝ) := by
  rcases Commons.Probability.Levy.rogozin_measurable with ⟨C, hCpos, hCmain⟩
  let K : ℝ := ν / 3
  let L0 : ℝ := max 1 (C * Real.sqrt 72 / (ν ^ 2 * Real.sqrt (p * δ)))
  refine ⟨K, L0, ?_, ?_, ?_⟩
  · -- 0 < K
    dsimp [K]
    positivity
  · -- 1 ≤ L0
    dsimp [L0]
    exact le_max_left _ _
  · intro n hn x hx hnot L hL
    -- we need the slope bound at every radius τ > K/√n
    apply threshold_le_of_cf_le (hn := hn)
    · dsimp [K]
      positivity
    · intro τ hτbig
      have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
      have hsqn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
      have hτ0 : 0 < τ := lt_trans (by dsimp [K]; positivity) hτbig
      have hτge : ν / (3 * Real.sqrt (n : ℝ)) ≤ τ := by
        dsimp [K] at hτbig
        have hle : ν / 3 / Real.sqrt (n : ℝ) ≤ τ := hτbig.le
        -- ν/3/√n = ν/(3√n)
        have hEq : ν / (3 * Real.sqrt (n : ℝ)) = (ν / 3) / Real.sqrt (n : ℝ) := by
          have h3 : (3 * Real.sqrt (n : ℝ)) ≠ 0 := by positivity
          have h1 : Real.sqrt (n : ℝ) ≠ 0 := by positivity
          field_simp [h3, h1]
        rw [hEq]
        exact hτbig.le
      -- spread set from incompressibility
      rcases Commons.LinearAlgebra.Net.incompressible_spread hn hδ₀ hν₀ x hx (by
        intro z hz
        exact hnot z hz) with ⟨σ, hσcard, hσcoord⟩
      -- independent family and radii
      let ξ : Fin n → (Fin n → ℝ) → ℝ := fun i ω => ω i * x i
      let ρ : Fin n → ℝ := fun i => if x i = 0 then τ / 2 else min (|x i| / 3) (τ / 2)
      have hξind : iIndepFun ξ (berP (n := n) p) := by
        have hc : iIndepFun (fun (i : Fin n) (ω : Fin n → ℝ) => ω i * x i) (berP (n := n) p) := by
          simpa [Function.comp_def] using (ProbabilityTheory.iIndepFun.comp
            (f := fun (i : Fin n) (ω : Fin n → ℝ) => ω i)
            (g := fun (i : Fin n) (t : ℝ) => t * x i) (iIndepFun_proj p)
            (by intro i; fun_prop))
        simpa [ξ] using hc
      have hξmeas : ∀ i : Fin n, Measurable (ξ i) := by
        intro i
        dsimp [ξ]
        fun_prop
      have hρpos : ∀ i : Fin n, 0 < ρ i := by
        intro i
        by_cases hi : x i = 0
        · dsimp [ρ]
          rw [if_pos hi]
          positivity
        · have hxabs : 0 < |x i| := abs_pos.mpr hi
          have hmin0 : 0 < min (|x i| / 3) (τ / 2) := lt_min (by positivity) (by positivity)
          dsimp [ρ]
          rw [if_neg hi]
          exact hmin0
      have hρle : ∀ i : Fin n, ρ i ≤ τ := by
        intro i
        by_cases hi : x i = 0
        · dsimp [ρ]
          rw [if_pos hi]
          exact half_le_self hτ0.le
        · dsimp [ρ]
          rw [if_neg hi]
          exact le_trans (min_le_right _ _) (half_le_self hτ0.le)
      -- gaps on the spread set
      have hgapσ : ∀ i : Fin n, i ∈ σ → (p : ℝ) ≤ 1 -
          (Submission.Helpers.levyConcentration (berP (n := n) p) (ξ i) (ρ i)).toReal := by
        intro i hi
        have hxi0 : x i ≠ 0 := by
          intro hx0
          have h := hσcoord i hi
          rw [hx0] at h
          have : 0 < ν / (2 * Real.sqrt (n : ℝ)) := div_pos hν₀ (by positivity)
          linarith
        have hg := coord_gap_min hp₁ τ i hxi0
        -- hg : p ≤ 1 − cf(ω_i·x_i, min(|x_i|/3)(τ/2)).toReal ; ρ i = that radius
        simpa [ξ, ρ, hxi0] using hg
      -- denominator lower bound
      let D : ℝ := ∑ i : Fin n,
          (1 - (Submission.Helpers.levyConcentration (berP (n := n) p) (ξ i) (ρ i)).toReal) * (ρ i) ^ 2
      have hDreal : (p : ℝ) * ν ^ 4 * δ / 72 ≤ D := by
        -- apply denom_lower_bound with ξ/ρ unfolded
        simpa [D, ξ, ρ] using (denom_lower_bound hp₁ hδ₀ hν₀ hn0 hσcard hσcoord hτ0 hτge (by
          intro i hi
          have hxi0 : x i ≠ 0 := by
            intro hx0
            have h := hσcoord i hi
            rw [hx0] at h
            have : 0 < ν / (2 * Real.sqrt (n : ℝ)) := div_pos hν₀ (by positivity)
            linarith
          have hg := hgapσ i hi
          simpa [ξ, ρ, hxi0] using hg))
      have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hDreal
      -- LKR application
      have hLKR : sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = (berP (n := n) p)
            {x : Fin n → ℝ | |(∑ i : Fin n, ξ i x) - l| ≤ τ}} ≤
          ENNReal.ofReal (C * τ / Real.sqrt D) := by
        refine hCmain n (Fin n → ℝ) (berP (n := n) p) ξ hξind hξmeas τ hτ0 ρ hρpos hρle ?_
        simpa [D, Submission.Helpers.levyConcentration] using hDpos
      -- connect to cfP
      have hcfτ : cfP (n := n) p x τ ≤ ENNReal.ofReal (C * τ / Real.sqrt D) := by
        simpa [cfP, D, Submission.Helpers.levyConcentration, ξ] using hLKR
      -- real arithmetic: C·τ/√D ≤ L·τ
      have hDnonneg : 0 ≤ D := le_of_lt hDpos
      let A : ℝ := ν ^ 2 * Real.sqrt (p * δ)
      have hApos : 0 < A := by
        dsimp [A]
        positivity
      have hDlow : A / Real.sqrt 72 ≤ Real.sqrt D := by
        -- √(p·ν⁴·δ/72) ≤ √D  (hDreal) and  √(p·ν⁴·δ/72) = A/√72
        have hsqrt := Real.sqrt_le_sqrt hDreal
        have hsqrt_eq : Real.sqrt ((p : ℝ) * ν ^ 4 * δ / 72) = A / Real.sqrt 72 := by
          dsimp [A]
          have hp0' : 0 ≤ (p : ℝ) := le_of_lt hp₀
          have hpδ : 0 ≤ (p : ℝ) * δ := mul_nonneg hp0' (le_of_lt hδ₀)
          rw [Real.sqrt_div]
          · have hx : (p : ℝ) * ν ^ 4 * δ = ((p : ℝ) * δ) * ν ^ 4 := by ring
            rw [hx]
            rw [Real.sqrt_mul hpδ (ν ^ 4)]
            have hν4 : Real.sqrt (ν ^ 4) = ν ^ 2 := by
              have hsq : ν ^ 4 = (ν ^ 2) ^ 2 := by ring
              rw [hsq, Real.sqrt_sq_eq_abs]
              exact abs_of_nonneg (sq_nonneg ν)
            rw [hν4]
            ring
          · exact mul_nonneg (mul_nonneg hp0' (by positivity : 0 ≤ ν ^ 4)) (le_of_lt hδ₀)
        rwa [hsqrt_eq] at hsqrt
      have hsqrtDpos : 0 < Real.sqrt D := Real.sqrt_pos.2 hDpos
      have hinv : 1 / Real.sqrt D ≤ Real.sqrt 72 / A := by
        have hpos : 0 < A / Real.sqrt 72 := div_pos hApos (by norm_num)
        have hrec := one_div_le_one_div_of_le hpos hDlow
        -- hrec : 1 / √D ≤ 1 / (A / √72)
        have heq : 1 / (A / Real.sqrt 72) = Real.sqrt 72 / A := by
          field_simp [show A ≠ 0 by positivity]
        rw [heq] at hrec
        exact hrec
      have hCτ : C * τ / Real.sqrt D ≤ L * τ := by
        have hm1' : C * τ * (1 / Real.sqrt D) ≤ C * τ * (Real.sqrt 72 / A) :=
          mul_le_mul_of_nonneg_left hinv (mul_nonneg (le_of_lt hCpos) (le_of_lt hτ0))
        have hident : C * τ / Real.sqrt D = C * τ * (1 / Real.sqrt D) := by
          rw [div_eq_mul_inv]
          congr 1
          rw [one_div]
        have hm1 : C * τ / Real.sqrt D ≤ C * τ * (Real.sqrt 72 / A) := by
          rwa [hident]
        have hLA : C * Real.sqrt 72 / A ≤ L := by
          have hle0 : C * Real.sqrt 72 / A ≤ L0 := by
            dsimp [L0]
            exact le_max_right _ _
          exact le_trans hle0 hL
        have hm2 : C * τ * (Real.sqrt 72 / A) ≤ L * τ := by
          have hswap : C * τ * (Real.sqrt 72 / A) = τ * (C * Real.sqrt 72 / A) := by
            field_simp [show A ≠ 0 by positivity]
          rw [hswap]
          simpa [mul_comm, mul_left_comm, mul_assoc] using (mul_le_mul_of_nonneg_right hLA (le_of_lt hτ0))
        exact le_trans hm1 hm2
      exact le_trans hcfτ (ENNReal.ofReal_le_ofReal hCτ)



/-! ## Threshold calculus

Two corollaries that the rest of the proof of Theorem A uses repeatedly:
scaling of the concentration function (`cfP_scale`) and the fact that above
the threshold the concentration is below the linear slope `L·r`
(`cfP_le_slope_of_threshold`).  Both follow directly from the definitions. -/

/-- Scaling: `cfP p (c•x) s = cfP p x (s/c)` for `c > 0`. -/
lemma cfP_scale {n : ℕ} {p : unitInterval} {x : Fin n → ℝ} {c s : ℝ} (hc : 0 < c) :
    cfP (n := n) p (fun i => c * x i) s = cfP (n := n) p x (s / c) := by
  -- S(c•x) = c·(S x) pointwise
  have hfun : (fun ω : Fin n → ℝ => ∑ i : Fin n, ω i * (c * x i)) =
      (fun ω : Fin n → ℝ => c * (∑ i : Fin n, ω i * x i)) := by
    funext ω
    have h1 : (∑ i : Fin n, ω i * (c * x i)) = ∑ i : Fin n, c * (ω i * x i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have h2 : (∑ i : Fin n, c * (ω i * x i)) = c * (∑ i : Fin n, ω i * x i) := by
      simpa using (Finset.mul_sum (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => ω i * x i) (a := c)).symm
    rw [h1, h2]
  unfold cfP
  rw [hfun]
  have hscale := Submission.Concentration.levyConcentration_scale_eq (berP (n := n) p)
    (fun ω : Fin n → ℝ => ∑ i : Fin n, ω i * x i) (a := c) (t := s / c) hc
  -- hscale : cf(P, c·ξ, c·(s/c)) = cf(P, ξ, s/c)
  have hcs : c * (s / c) = s := by field_simp [hc.ne']
  rwa [hcs] at hscale

/-- For every radius strictly above the threshold, the concentration function
is below the linear slope `L·r` (Tikhomirov 2020, definition of threshold). -/
lemma cfP_le_slope_of_threshold {n : ℕ} {p : unitInterval} {x : Fin n → ℝ} {L : ℝ}
    (hL : 1 ≤ L) {r : ℝ} (hr0 : 0 < r) (hr : threshold p x L < r) :
    cfP (n := n) p x r ≤ ENNReal.ofReal (L * r) := by
  by_cases hr1 : r ≤ 1
  · -- r ∈ (0,1] and r > threshold, so the defining set does not contain r
    have hnot : ¬ (ENNReal.ofReal (L * r) < cfP (n := n) p x r) := by
      intro hlt
      have hmem : r ∈ {t : ℝ | 0 < t ∧ t ≤ 1 ∧ ENNReal.ofReal (L * t) < cfP (n := n) p x t} := by
        exact ⟨hr0, hr1, hlt⟩
      have hle : r ≤ threshold p x L := by
        unfold threshold
        exact le_csSup (by
          -- the set is bounded above by 1
          refine ⟨1, ?_⟩
          intro t ht
          exact ht.2.1) hmem
      exact (not_le_of_gt hr) hle
    exact le_of_not_gt hnot
  · -- r > 1: cf ≤ 1 ≤ L·r
    have hcf1 : cfP (n := n) p x r ≤ (1 : ℝ≥0∞) :=
      Submission.Helpers.levyConcentration_le_one (berP (n := n) p)
        (fun ω : Fin n → ℝ => ∑ i : Fin n, ω i * x i) r
    have hLr : 1 ≤ L * r := by
      have hr1' : 1 < r := lt_of_not_ge hr1
      nlinarith
    calc
      cfP (n := n) p x r ≤ (1 : ℝ≥0∞) := hcf1
      _ = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal (L * r) := ENNReal.ofReal_le_ofReal hLr


/-! ## From `¬ compressible` to the spread hypothesis

The `(δ,ν)`-incompressible vectors that appear in the small-ball events of the
proof of Theorem A (unit vectors with `¬ Commons.compressible δ ν`) satisfy
the hypothesis of `incompressible_spread` / `threshold_le_K_div_sqrt`. -/

/-- A unit vector which is not `(δ,ν)`-compressible has, for every truncation
`z` within squared distance `ν²`, support strictly larger than `δ·n`. -/
lemma incompressible_of_not_compressible {n : ℕ} {δ ν : ℝ} {x : Fin n → ℝ}
    (hx : Commons.LinearAlgebra.Net.sqNorm x = 1)
    (hinc : ¬ Commons.LinearAlgebra.Net.compressible δ ν x) :
    ∀ z : Fin n → ℝ, Commons.LinearAlgebra.Net.sqNorm (x - z) ≤ ν ^ 2 →
      ¬ (((Finset.univ.filter (fun i => z i ≠ 0)).card : ℝ) ≤ δ * (n : ℝ)) := by
  intro z hz
  intro hcard
  exact hinc ⟨hx, z, hz, hcard⟩

/-- The threshold bound (Lemma l:threshold) instantiated for
`¬ compressible`-incompressible unit vectors. -/
theorem threshold_le_K_div_sqrt_of_incompressible {p : unitInterval} (hp₀ : 0 < (p : ℝ))
    (hp₁ : (p : ℝ) ≤ 1 / 2) {δ ν : ℝ} (hδ₀ : 0 < δ) (hν₀ : 0 < ν) :
    ∃ K L₀ : ℝ, 0 < K ∧ 1 ≤ L₀ ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ (x : Fin n → ℝ),
      Commons.LinearAlgebra.Net.sqNorm x = 1 →
      ¬ Commons.LinearAlgebra.Net.compressible δ ν x →
      ∀ L : ℝ, L₀ ≤ L → threshold p x L ≤ K / Real.sqrt (n : ℝ) := by
  rcases threshold_le_K_div_sqrt hp₀ hp₁ hδ₀ hν₀ with ⟨K, L₀, hK, hL₀, hmain⟩
  refine ⟨K, L₀, hK, hL₀, ?_⟩
  intro n hn x hx hinc L hL
  exact hmain n hn x hx (incompressible_of_not_compressible hx hinc) L hL



/-! ## Measure ↔ subset-weight bridge (canonical Bernoulli space)

The canonical product measure `berP p` is atomic on the support
`{0,1}^n`, each configuration being `e_B` (ones exactly on `B`) with mass
`wB(n,p,B) = p^{|B|}(1−p)^{n−|B|}`.  `berP_real_indVec` records that atom
mass; the slab-measure identity (a finite disjoint union over the good
subsets) is the next lemma. -/

/-- indicator vector of a subset `B ⊆ Fin n` (1 on B, 0 elsewhere). -/
def indVec {n : ℕ} (B : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ B then 1 else 0

/-- product of a two-valued function over a Finset splits by the filter. -/
lemma prod_ite_split {α : Type*} [DecidableEq α] (s : Finset α) (P : α → Prop)
    [DecidablePred P] (a b : ℝ) :
    (∏ i ∈ s, (if P i then a else b)) =
      a ^ ((s.filter P).card) * b ^ ((s.filter (fun i => ¬ P i)).card) := by
  classical
  calc
    (∏ i ∈ s, (if P i then a else b))
        = ∏ i ∈ s, ((if P i then a else 1) * (if ¬ P i then b else 1)) := by
          apply Finset.prod_congr rfl
          intro i hi
          by_cases hP : P i <;> simp [hP]
    _ = (∏ i ∈ s, (if P i then a else 1)) * (∏ i ∈ s, (if ¬ P i then b else 1)) := by
          rw [Finset.prod_mul_distrib]
    _ = a ^ (s.filter P).card * b ^ (s.filter (fun i => ¬ P i)).card := by
          rw [← Finset.prod_filter, ← Finset.prod_filter]
          rw [Finset.prod_const]
          rw [Finset.prod_const]

/-- mass of the exact-support configuration `e_B` under the canonical product
Bernoulli measure (real value): `p^{|B|}·(1−p)^{n−|B|}`. -/
lemma berP_real_indVec {n : ℕ} (p : unitInterval) (B : Finset (Fin n)) :
    (berP (n := n) p).real ({indVec B} : Set (Fin n → ℝ)) =
      (p : ℝ) ^ B.card * (1 - (p : ℝ)) ^ (n - B.card) := by
  classical
  have hpi := MeasureTheory.Measure.pi_pi (μ := fun _ : Fin n => bernoulliMeasure 1 0 p)
    (s := fun i : Fin n => ({indVec B i} : Set ℝ))
  have hset : (Set.univ.pi (fun i : Fin n => ({indVec B i} : Set ℝ))) = ({indVec B} : Set (Fin n → ℝ)) := by
    apply Set.ext
    intro ω
    constructor
    · intro h
      apply Set.mem_singleton_iff.mpr
      funext i
      exact h i trivial
    · intro h
      intro i hi
      rw [Set.mem_singleton_iff.mp h]
      exact rfl
  have hval : ∀ i : Fin n, ((bernoulliMeasure 1 0 p) ({indVec B i} : Set ℝ)).toReal =
      if i ∈ B then (p : ℝ) else 1 - (p : ℝ) := by
    intro i
    have hs : MeasurableSet ({indVec B i} : Set ℝ) := measurableSet_singleton (indVec B i)
    by_cases hi : i ∈ B
    · have hidx : indVec B i = 1 := by dsimp [indVec]; simp [hi]
      rw [if_pos hi]
      rw [hidx]
      rw [← Measure.real_def]
      exact bernoulliMeasure_real_apply_of_mem_of_notMem p (measurableSet_singleton 1) (by simp) (by simp)
    · have hidx : indVec B i = 0 := by dsimp [indVec]; simp [hi]
      rw [if_neg hi]
      rw [hidx]
      rw [← Measure.real_def]
      exact bernoulliMeasure_real_apply_of_notMem_of_mem p (measurableSet_singleton 0) (by simp) (by simp)
  unfold berP
  rw [Measure.real_def]
  rw [← hset]
  rw [hpi]
  rw [ENNReal.toReal_prod]
  calc
    (∏ i : Fin n, ((bernoulliMeasure 1 0 p) ({indVec B i} : Set ℝ)).toReal)
        = ∏ i : Fin n, (if i ∈ B then (p : ℝ) else 1 - (p : ℝ)) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact hval i
    _ = (p : ℝ) ^ B.card * (1 - (p : ℝ)) ^ (n - B.card) := by
          have hsplit := prod_ite_split (s := (Finset.univ : Finset (Fin n)))
            (P := fun i : Fin n => i ∈ B) (a := (p : ℝ)) (b := 1 - (p : ℝ))
          have hf1 : ((Finset.univ : Finset (Fin n)).filter (fun i : Fin n => i ∈ B)) = B := by
            apply Finset.ext
            intro i
            simp
          have hf2 : ((Finset.univ : Finset (Fin n)).filter (fun i : Fin n => ¬ i ∈ B)) =
              (Finset.univ : Finset (Fin n)) \ B := by
            apply Finset.ext
            intro i
            by_cases hi : i ∈ B <;> simp [hi]
          have hc1 : ((Finset.univ : Finset (Fin n)).filter (fun i : Fin n => i ∈ B)).card = B.card := by rw [hf1]
          have hc2 : ((Finset.univ : Finset (Fin n)).filter (fun i : Fin n => ¬ i ∈ B)).card = n - B.card := by
            rw [hf2]
            have hcd : ((Finset.univ : Finset (Fin n)) \ B).card =
                (Finset.univ : Finset (Fin n)).card - (B ∩ (Finset.univ : Finset (Fin n))).card :=
                  Finset.card_sdiff
            rw [hcd]
            have hBi : (B ∩ (Finset.univ : Finset (Fin n))) = B :=
              (Finset.inter_eq_left).mpr (Finset.subset_univ B)
            rw [hBi]
            simp
          rw [hsplit]
          rw [hc1, hc2]



/-- The threshold is positive (for `L > 0` and `p < 1`): some small positive
radius lies in the defining set, since the all-zero configuration carries
Bernoulli mass `(1−p)^n > 0`. -/
lemma threshold_pos {n : ℕ} (p : unitInterval) (x : Fin n → ℝ) {L : ℝ}
    (hp : (p : ℝ) < 1) (hL : 0 < L) :
    0 < threshold p x L := by
  classical
  unfold threshold
  let b : ℝ := (1 - (p : ℝ)) ^ n
  have hb0 : 0 < b := pow_pos (sub_pos.mpr hp) n
  let t : ℝ := min 1 (b / (2 * L))
  have ht0 : 0 < t := by
    dsimp [t]
    exact lt_min (by norm_num) (div_pos hb0 (by positivity))
  have ht1 : t ≤ 1 := by dsimp [t]; exact min_le_left _ _
  have hmem : t ∈ {t : ℝ | 0 < t ∧ t ≤ 1 ∧ ENNReal.ofReal (L * t) < cfP (n := n) p x t} := by
    refine ⟨ht0, ht1, ?_⟩
    have hLt : L * t ≤ b / 2 := by
      dsimp [t]
      have hm := mul_le_mul_of_nonneg_left (min_le_right 1 (b / (2 * L))) (le_of_lt hL)
      have hnorm : L * (b / (2 * L)) = b / 2 := by
        field_simp [ne_of_gt hL]
      rw [hnorm] at hm
      exact hm
    have hLt' : L * t < b := lt_of_le_of_lt hLt (by nlinarith [hb0])
    have hlt_ofReal : ENNReal.ofReal (L * t) < ENNReal.ofReal b :=
      (ENNReal.ofReal_lt_ofReal_iff hb0).2 hLt'
    have hcf : ENNReal.ofReal b ≤ cfP (n := n) p x t := by
      let E : Set (Fin n → ℝ) := {ω : Fin n → ℝ | |∑ i : Fin n, ω i * x i - 0| ≤ t}
      have hsub : ({indVec ∅} : Set (Fin n → ℝ)) ⊆ E := by
        intro ω hω
        rw [Set.mem_singleton_iff.mp hω]
        dsimp [E]
        have hsum : (∑ i : Fin n, indVec ∅ i * x i) = 0 := by simp [indVec]
        rw [hsum]
        simp
        exact le_of_lt ht0
      have hle_atom : berP (n := n) p ({indVec ∅} : Set (Fin n → ℝ)) ≤ berP (n := n) p E :=
        measure_mono hsub
      have hatom : berP (n := n) p ({indVec ∅} : Set (Fin n → ℝ)) = ENNReal.ofReal b := by
        dsimp [b]
        have htop : berP (n := n) p ({indVec ∅} : Set (Fin n → ℝ)) ≠ ⊤ := by
          exact MeasureTheory.measure_ne_top (berP (n := n) p) ({indVec ∅} : Set (Fin n → ℝ))
        rw [← ENNReal.ofReal_toReal htop]
        congr 1
        rw [← Measure.real_def]
        simpa using (berP_real_indVec p ∅)
      have hE_le_cf : berP (n := n) p E ≤ cfP (n := n) p x t := by
        unfold cfP
        exact Submission.Helpers.le_levyConcentration (berP (n := n) p)
          (fun ω : Fin n → ℝ => ∑ i : Fin n, ω i * x i) t 0
      calc
        ENNReal.ofReal b = berP (n := n) p ({indVec ∅} : Set (Fin n → ℝ)) := hatom.symm
        _ ≤ berP (n := n) p E := hle_atom
        _ ≤ cfP (n := n) p x t := hE_le_cf
    exact lt_of_lt_of_le hlt_ofReal hcf
  have hbd : BddAbove {t : ℝ | 0 < t ∧ t ≤ 1 ∧ ENNReal.ofReal (L * t) < cfP (n := n) p x t} := by
    refine ⟨1, ?_⟩
    intro y hy
    exact hy.2.1
  have hle : t ≤ threshold p x L := by
    unfold threshold
    exact le_csSup hbd hmem
  exact lt_of_lt_of_le ht0 hle


/-! ## Concentration-function calculus at the threshold radius

Small helper facts used by the spv (magic-vector) layer and the net argument:
finiteness, monotonicity in the radius, and the lower bound `cfP(x, th) ≥ L·th/2`
that comes from the definition of the threshold as a supremum. -/

/-- `cfP` is finite (the concentration of a probability measure never exceeds one). -/
lemma cfP_ne_top {n : ℕ} (p : unitInterval) (x : Fin n → ℝ) (t : ℝ) :
    cfP (n := n) p x t ≠ ⊤ := by
  have hle1 : cfP (n := n) p x t ≤ (1 : ℝ≥0∞) := by
    unfold cfP
    exact Submission.Helpers.levyConcentration_le_one (berP (n := n) p)
      (fun ω : Fin n → ℝ => ∑ i : Fin n, ω i * x i) t
  exact ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hle1

/-- The concentration function is monotone in the radius. -/
lemma cfP_mono {n : ℕ} (p : unitInterval) (x : Fin n → ℝ) {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    cfP (n := n) p x t₁ ≤ cfP (n := n) p x t₂ := by
  unfold cfP
  exact Submission.Helpers.levyConcentration_mono (berP (n := n) p)
    (fun ω : Fin n → ℝ => ∑ i : Fin n, ω i * x i) ht

/-- Real version of `cfP_mono`. -/
lemma cfP_toReal_mono {n : ℕ} (p : unitInterval) (x : Fin n → ℝ) {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    (cfP (n := n) p x t₁).toReal ≤ (cfP (n := n) p x t₂).toReal := by
  exact ENNReal.toReal_mono (cfP_ne_top p x t₂) (cfP_mono p x ht)

/-- A point of the threshold-defining set at radius at least half the threshold.
Since the threshold is the supremum of `{t ∈ (0,1] : L·t < cfP(x,t)}` and is
positive, some element lies above `th/2`. -/
lemma threshold_approx {n : ℕ} (p : unitInterval) (x : Fin n → ℝ) {L : ℝ}
    (hL : 0 < L) (hp : (p : ℝ) < 1) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ threshold p x L / 2 < t₀ ∧ t₀ ≤ threshold p x L ∧
      ENNReal.ofReal (L * t₀) < cfP (n := n) p x t₀ := by
  classical
  let S : Set ℝ := {t : ℝ | 0 < t ∧ t ≤ 1 ∧ ENNReal.ofReal (L * t) < cfP (n := n) p x t}
  have hthpos : 0 < threshold p x L := threshold_pos p x hp hL
  have hth_eq : sSup S = threshold p x L := by
    dsimp [S, threshold]
  have hbd : BddAbove S := by
    refine ⟨1, ?_⟩
    intro y hy
    exact hy.2.1
  have hraw : ∃ t₀ : ℝ, t₀ ∈ S ∧ threshold p x L / 2 < t₀ := by
    by_contra h
    push_neg at h
    have hsle : sSup S ≤ threshold p x L / 2 :=
      Real.sSup_le h (by nlinarith)
    have hthle : threshold p x L ≤ threshold p x L / 2 := by
      rwa [hth_eq] at hsle
    nlinarith
  rcases hraw with ⟨t₀, ht₀S, ht₀big⟩
  refine ⟨t₀, ht₀S.1, ht₀big, ?_, ht₀S.2.2⟩
  have hle0 : t₀ ≤ sSup S := le_csSup hbd ht₀S
  rwa [hth_eq] at hle0

/-- At the threshold radius the concentration function is at least `L·th/2`
(real form). -/
lemma cfP_threshold_lower {n : ℕ} (p : unitInterval) (x : Fin n → ℝ) {L : ℝ}
    (hL : 0 < L) (hp : (p : ℝ) < 1) :
    (1 / 2 : ℝ) * (L * threshold p x L) ≤
      (cfP (n := n) p x (threshold p x L)).toReal := by
  rcases threshold_approx p x hL hp with ⟨t₀, ht₀pos, ht₀big, ht₀le, ht₀mem⟩
  have hmono : cfP (n := n) p x t₀ ≤ cfP (n := n) p x (threshold p x L) :=
    cfP_mono p x ht₀le
  have hlt : ENNReal.ofReal (L * t₀) < cfP (n := n) p x (threshold p x L) :=
    lt_of_lt_of_le ht₀mem hmono
  have htop : cfP (n := n) p x (threshold p x L) ≠ ⊤ := cfP_ne_top p x (threshold p x L)
  have hto : (ENNReal.ofReal (L * t₀)).toReal ≤
      (cfP (n := n) p x (threshold p x L)).toReal :=
    ENNReal.toReal_mono htop (le_of_lt hlt)
  have hto0 : (ENNReal.ofReal (L * t₀)).toReal = L * t₀ :=
    ENNReal.toReal_ofReal (mul_nonneg (le_of_lt hL) (le_of_lt ht₀pos))
  have hm : L * (threshold p x L / 2) < L * t₀ := mul_lt_mul_of_pos_left ht₀big hL
  have hLt : (1 / 2 : ℝ) * (L * threshold p x L) ≤ L * t₀ := by nlinarith
  calc
    (1 / 2 : ℝ) * (L * threshold p x L) ≤ L * t₀ := hLt
    _ = (ENNReal.ofReal (L * t₀)).toReal := hto0.symm
    _ ≤ (cfP (n := n) p x (threshold p x L)).toReal := hto


/-- Scaling bridge used by the magic-vector layer: the concentration of the
scaled vector `(√n/th)·x` at radius `√n` equals the concentration of `x` at
the threshold radius. -/
lemma cfP_scale_threshold {n : ℕ} (p : unitInterval) (x : Fin n → ℝ) (hn : 1 ≤ n)
    {L : ℝ} (hL0 : 0 < L) (hp : (p : ℝ) < 1) :
    cfP (n := n) p (fun i : Fin n => (Real.sqrt (n : ℝ) / threshold p x L) * x i)
        (Real.sqrt (n : ℝ)) =
      cfP (n := n) p x (threshold p x L) := by
  have hth : 0 < threshold p x L := threshold_pos p x hp hL0
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hc : 0 < Real.sqrt (n : ℝ) / threshold p x L := div_pos hsqrt hth
  have h := cfP_scale (p := p) (x := x) (c := Real.sqrt (n : ℝ) / threshold p x L)
    (s := Real.sqrt (n : ℝ)) hc
  have hdiv : Real.sqrt (n : ℝ) /
      (Real.sqrt (n : ℝ) / threshold p x L) = threshold p x L := by
    field_simp [ne_of_gt hsqrt, ne_of_gt hth]
  rwa [hdiv] at h

end Submission.Threshold
