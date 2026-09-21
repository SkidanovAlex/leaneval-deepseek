import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.Existence.aw_data

/-!
# Smooth localisation of the odd `Θ`-data

The `Θ`-data of the odd transition-slope system (`KernelExt.ThetaM`) is built from the manifest
Abel kernel `KvecM`, which is only smooth where the two Abel radicands are positive, and from the
`τ`-average `G2M`, whose weight `(τ(1-τ))^{-1/2}` is singular at the endpoints.

This file sets up the *smooth localisation* used to prove that the localised data `awTheta` is
`C^∞` on all of `ℝ × ℝ × St`.  The idea is

* substitute `τ = sin²θ`, which removes the singularity:
  `∫_0^1 K τ / √(τ(1-τ)) dτ = ∫_0^{π/2} 2 K(sin²θ) dθ`;
* multiply by an explicit smooth *bump* `awPsi` in the slots `(u, σ, z 0, z 1)` that carries the
  Abel radicands, so that the product is smooth on *all* of `ℝ × ℝ × St`, independently of where
  `Kden` vanishes.

The bump is chosen so that

* `awPsi = 1` on the support `awSuppT` of the localising cutoffs of `aw_data`, and
* `awPsi ≠ 0` forces `u, σ ∈ (9/20, 21/20)` and `|z 0|, |z 1| > 1/5`, which is exactly the region
  where the Abel radicands are positive (`krad_pos_of_add_pos`).
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.Existence

open Work.OddVolterra

noncomputable section

/-! ## The localising bump -/

/-- The slope bump: `= 1` on `[9/20, 21/20]` (which contains the support `[19/40, 41/40]` of the
slope cutoffs) and `= 0` off `(0, 21/20 + 1/100)`.  Its non-zero points are `> 1/20`, which is
what the Abel radicand positivity needs. -/
def awPbeta : ContDiffBump (3 / 4 : ℝ) := ⟨3 / 10, 31 / 100, by norm_num, by norm_num⟩

/-- The state bump: `= 1` on `[1/4, 39/20]` (which contains the range of `z i` on `awSuppT`) and
`= 0` off `(21/100, 199/100)`.  Its non-zero points are `> 1/5` in modulus, which is what the Abel
radicand positivity needs. -/
def awPzeta : ContDiffBump (11 / 10 : ℝ) := ⟨17 / 20, 89 / 100, by norm_num, by norm_num⟩

lemma awPbeta_rIn : awPbeta.rIn = 3 / 10 := rfl
lemma awPbeta_rOut : awPbeta.rOut = 31 / 100 := rfl
lemma awPzeta_rIn : awPzeta.rIn = 17 / 20 := rfl
lemma awPzeta_rOut : awPzeta.rOut = 89 / 100 := rfl

/-- The localising bump of the `Θ`-data, in the slots `(u, σ, z 0, z 1)`. -/
def awPsi (u σ : ℝ) (z : St) : ℝ :=
  (awPbeta : ℝ → ℝ) u * (awPbeta : ℝ → ℝ) σ * (awPzeta : ℝ → ℝ) (z 0) *
    (awPzeta : ℝ → ℝ) (z 1)

lemma awPbeta_nonneg (t : ℝ) : 0 ≤ (awPbeta : ℝ → ℝ) t := ContDiffBump.nonneg awPbeta
lemma awPbeta_le_one (t : ℝ) : (awPbeta : ℝ → ℝ) t ≤ 1 := ContDiffBump.le_one awPbeta
lemma awPzeta_nonneg (t : ℝ) : 0 ≤ (awPzeta : ℝ → ℝ) t := ContDiffBump.nonneg awPzeta
lemma awPzeta_le_one (t : ℝ) : (awPzeta : ℝ → ℝ) t ≤ 1 := ContDiffBump.le_one awPzeta

/-- `awPbeta = 1` on `[9/20, 21/20]`. -/
lemma awPbeta_eq_one {t : ℝ} (ht : t ∈ Set.Icc (9 / 20 : ℝ) (21 / 20)) :
    (awPbeta : ℝ → ℝ) t = 1 := by
  refine ContDiffBump.one_of_mem_closedBall awPbeta ?_
  rw [awPbeta_rIn, Metric.mem_closedBall, Real.dist_eq]
  rw [Set.mem_Icc] at ht
  rw [abs_le]
  constructor <;> linarith [ht.1, ht.2]

/-- `awPzeta = 1` on `[1/4, 39/20]`. -/
lemma awPzeta_eq_one {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) (39 / 20)) :
    (awPzeta : ℝ → ℝ) t = 1 := by
  refine ContDiffBump.one_of_mem_closedBall awPzeta ?_
  rw [awPzeta_rIn, Metric.mem_closedBall, Real.dist_eq]
  rw [Set.mem_Icc] at ht
  rw [abs_le]
  constructor <;> linarith [ht.1, ht.2]

/-- The non-zero points of `awPbeta` lie in the open interval `(11/25, 53/50)`, i.e. in the
open ball of radius `rOut = 31/100` around the centre `3/4`. -/
lemma awPbeta_ne_zero_bounds {t : ℝ} (h : (awPbeta : ℝ → ℝ) t ≠ 0) :
    11 / 25 < t ∧ t < 53 / 50 := by
  constructor
  · by_contra hcon
    refine h (ContDiffBump.zero_of_le_dist awPbeta ?_)
    rw [awPbeta_rOut, Real.dist_eq, abs_of_nonpos (by linarith [not_lt.mp hcon])]
    linarith [not_lt.mp hcon]
  · by_contra hcon
    refine h (ContDiffBump.zero_of_le_dist awPbeta ?_)
    rw [awPbeta_rOut, Real.dist_eq, abs_of_nonneg (by linarith [not_lt.mp hcon])]
    linarith [not_lt.mp hcon]

lemma lt_of_awPbeta_ne_zero {t : ℝ} (h : (awPbeta : ℝ → ℝ) t ≠ 0) : 1 / 20 < t :=
  lt_trans (by norm_num) (awPbeta_ne_zero_bounds h).1

lemma awPbeta_ne_zero_lt {t : ℝ} (h : (awPbeta : ℝ → ℝ) t ≠ 0) : t < 107 / 100 :=
  lt_trans (awPbeta_ne_zero_bounds h).2 (by norm_num)

/-- The non-zero points of `awPzeta` are positive and lie in `(21/100, 199/100)`. -/
lemma awPzeta_ne_zero_bounds {t : ℝ} (h : (awPzeta : ℝ → ℝ) t ≠ 0) :
    21 / 100 < |t| ∧ |t| < 199 / 100 := by
  have hdist : dist t (11 / 10) < 89 / 100 := by
    by_contra hcon
    exact h (ContDiffBump.zero_of_le_dist awPzeta (by rw [awPzeta_rOut, Real.dist_eq]; exact not_lt.mp hcon))
  rw [Real.dist_eq] at hdist
  have hpos : 21 / 100 < t := by
    have := (abs_lt.mp hdist).1; linarith
  constructor
  · rw [abs_of_pos (by linarith)]; linarith [hpos]
  · rw [abs_of_pos (by linarith)]; linarith [(abs_lt.mp hdist).2]

/-- The non-zero points of `awPzeta` have modulus `> 1/5`. -/
lemma one_fifth_lt_abs_of_awPzeta_ne_zero {t : ℝ} (h : (awPzeta : ℝ → ℝ) t ≠ 0) :
    1 / 5 < |t| := by
  by_contra hcon
  rw [not_lt] at hcon
  refine h (ContDiffBump.zero_of_le_dist awPzeta ?_)
  have h1 : |(11 : ℝ) / 10| - |t| ≤ |(11 : ℝ) / 10 - t| := abs_sub_abs_le_abs_sub _ _
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 11 / 10)] at h1
  rw [awPzeta_rOut, Real.dist_eq, abs_sub_comm]
  linarith

lemma awPzeta_ne_zero_lt {t : ℝ} (h : (awPzeta : ℝ → ℝ) t ≠ 0) : t < 199 / 100 := by
  by_contra hcon
  exact h (ContDiffBump.zero_of_le_dist awPzeta (by
    rw [awPzeta_rOut, Real.dist_eq, abs_of_nonneg (by linarith [not_lt.mp hcon])]
    linarith [not_lt.mp hcon]))

/-! ## The closed support region and its interior -/

/-- The support region of the localising cutoffs `awChiT`: the slope window `[19/40, 41/40]` in
both slope slots and the state ball of radius `2/5` around the ball state. -/
def awSuppT : Set (ℝ × ℝ × St) :=
  {p | |p.1 - 3 / 4| ≤ 11 / 40 ∧ |p.2.1 - 3 / 4| ≤ 11 / 40 ∧
    ‖p.2.2 - baseState p.2.1‖ ≤ 2 / 5}

/-- The open region on which `awThetaMs` agrees with the paper's `ThetaM`: it contains the
support region `awSuppT` and is contained in the region where the localising bump `awPsi` is
identically `1` in the *first* variable (so that the two `u`-derivatives agree), while the state
ball is widened by `1/100` (keeping `z 0, z 1` inside the interval `[1/4, 39/20]` on which the
state bump equals `1`). -/
def awGoodT : Set (ℝ × ℝ × St) :=
  {p | |p.1 - 3 / 4| < 3 / 10 ∧ |p.2.1 - 3 / 4| < 3 / 10 ∧
    ‖p.2.2 - baseState p.2.1‖ < 41 / 100}

/-- The closed box containing the support of `awPsi`. -/
def awRclosed : Set (ℝ × ℝ × St) :=
  {p | 11 / 25 ≤ p.1 ∧ p.1 ≤ 53 / 50 ∧ 11 / 25 ≤ p.2.1 ∧ p.2.1 ≤ 53 / 50 ∧
    21 / 100 ≤ |p.2.2 0| ∧ |p.2.2 0| ≤ 199 / 100 ∧ 21 / 100 ≤ |p.2.2 1| ∧ |p.2.2 1| ≤ 199 / 100}

/-- An open region on which the manifest kernel composite is smooth.  It contains the closed box
`awRclosed` (hence the closure of the support of `awPsi`) and is contained in the region where the
Abel radicands are positive, which only requires `u, σ` positive and `|z i| > 1/5`. -/
def awR : Set (ℝ × ℝ × St) :=
  {p | 2 / 5 < p.1 ∧ p.1 < 11 / 10 ∧ 2 / 5 < p.2.1 ∧ p.2.1 < 11 / 10 ∧
    41 / 200 < |p.2.2 0| ∧ |p.2.2 0| < 2 ∧ 41 / 200 < |p.2.2 1| ∧ |p.2.2 1| < 2}

/-! ## The smooth localised `Θ`-data -/

/-- The smooth localised `τ`-average: the `sin²`-substituted manifest average multiplied by the
localising bump. -/
def awG2Ms (n : ℕ) (h : ℝ → ℝ) (u σ : ℝ) (z : St) (i : Fin 2) : ℝ :=
  ∫ θ in (0 : ℝ)..(Real.pi / 2),
    2 * awPsi u σ z *
      (Work.OddVolterra.KernelExt.KvecM n h (u + Real.sin θ ^ 2 * (σ - u)) σ
        (z 0) (z 1) (z 2) (z 3)) i

/-- The smooth localised `Θ`-data. -/
def awThetaMs (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : St) : St :=
  ![-z 2, -z 3,
    -(deriv (fun u : ℝ => awG2Ms n h u σ z 0) s),
    -(deriv (fun u : ℝ => awG2Ms n h u σ z 1) s)]

end

end Work.OddVolterra.Existence
