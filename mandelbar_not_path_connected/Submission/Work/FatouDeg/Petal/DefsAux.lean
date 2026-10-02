/-
Copyright: subproject `Submission/Work/FatouDeg/Petal/` of `mandelbar_not_path_connected`.

Ported verbatim from `Submission/Work/MultiPetal/` of the same project, with the exponent
hypothesis `4 ≤ m` weakened to `3 ≤ m` (see `Submission/Work/FatouDeg/NOTES.md`).

# The degenerate (multi-petal) parabolic germ `z ↦ z - z^m + z^(m+1) G z`: definitions

For `m : ℕ` with `3 ≤ m` and `G : Polynomial ℂ` we consider

  `Pfun m G z = z - z ^ m + z ^ (m + 1) * G z = z * (1 - z ^ (m-1) * (1 - z * G z))`.

At `0` this map has a parabolic fixed point of multiplicity `m`; the positive real axis is an
attracting direction.

The chart is `z ↦ z ^ (-(m-1)) = ((z ^ (m-1)))⁻¹`, in which the drift is constant `m-1`, and the
approximate Abel coordinate is

  `Afun m G z = ((z ^ (m-1)))⁻¹ * P z + β * log z`

where `P` and `β` are chosen so that the defect `Rfun m G z = A (P z) - A z - 1` vanishes to
order `m` at `0`.  The Fatou coordinate is then the sum of the defects along the orbit,

  `phifun m G z = A z + ∑' k, Rfun m G (P^[k] z)`,

which satisfies `phifun (P z) = phifun z + 1`.

The two domains are

* `Dom m ρ` — the *working* sector `(7m/8) * |Im z| < Re z` inside the ball of radius `2ρ`,
  on which `P` is defined, holomorphic, contracting, and on which the defect bound holds;
* `Pet m ρ` — the *petal* `m * |Im z| < Re z` inside the ball of radius `ρ` — the set required by
  the target statement.  Every point of `Pet` has a Cauchy disc inside `Dom`.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Topology
open Set Filter Metric

namespace Work.FatouDeg.Petal

/-- The polynomial map `P z = z - z ^ m + z ^ (m + 1) * G z`. -/
def Pfun (m : ℕ) (G : Polynomial ℂ) (z : ℂ) : ℂ := z - z ^ m + z ^ (m + 1) * G.eval z

/-- `u = 1 - X * G`, so that `P z = z * (1 - z ^ (m-1) * u z)`. -/
def upoly (G : Polynomial ℂ) : Polynomial ℂ := 1 - Polynomial.X * G

/-- The truncation of the formal inverse of `u`: `Q z = 1 / u z + O(z ^ (m-1))`. -/
def Qpoly (m : ℕ) (G : Polynomial ℂ) : Polynomial ℂ :=
  PowerSeries.trunc (m - 1) ((upoly G : PowerSeries ℂ)⁻¹)

/-- The polynomial `P` with `(m-1) * P - X * P' = Q`. -/
def Ppoly (m : ℕ) (G : Polynomial ℂ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (m - 1),
    Polynomial.monomial j ((Qpoly m G).coeff j / (((m - 1 : ℕ) : ℂ) - (j : ℂ)))

/-- The coefficient of the log term. -/
def betac (m : ℕ) (G : Polynomial ℂ) : ℂ :=
  ((upoly G) * (Qpoly m G)).coeff (m - 1) + (m : ℂ) / 2

/-- The approximate Abel coordinate in the chart `z ↦ (z ^ (m-1))⁻¹`. -/
def Afun (m : ℕ) (G : Polynomial ℂ) (z : ℂ) : ℂ :=
  (z ^ (m - 1))⁻¹ * (Ppoly m G).eval z + betac m G * Complex.log z

/-- The defect of `Afun` with respect to the Abel equation `A (P z) = A z + 1`. -/
def Rfun (m : ℕ) (G : Polynomial ℂ) (z : ℂ) : ℂ :=
  Afun m G (Pfun m G z) - Afun m G z - 1

/-- The Fatou coordinate: `A` plus the defects along the orbit. -/
def phifun (m : ℕ) (G : Polynomial ℂ) (z : ℂ) : ℂ :=
  Afun m G z + ∑' k : ℕ, Rfun m G ((Pfun m G)^[k] z)

/-- The petal: the sector `m * |Im z| < Re z` inside the ball of radius `ρ`. -/
def Pet (m : ℕ) (ρ : ℝ) : Set ℂ := Metric.ball 0 ρ ∩ {z : ℂ | (m : ℝ) * |z.im| < z.re}

/-- The working domain: the wider sector `(7m/8) * |Im z| < Re z` inside the ball of radius `2ρ`. -/
def Dom (m : ℕ) (ρ : ℝ) : Set ℂ :=
  Metric.ball 0 (2 * ρ) ∩ {z : ℂ | (7 * (m : ℝ) / 8) * |z.im| < z.re}

/-! ## Elementary set-theoretic properties -/

theorem mem_Pet {m : ℕ} {ρ : ℝ} {z : ℂ} :
    z ∈ Pet m ρ ↔ ‖z‖ < ρ ∧ (m : ℝ) * |z.im| < z.re := by
  simp [Pet, Metric.mem_ball, dist_zero_right]

theorem mem_Dom {m : ℕ} {ρ : ℝ} {z : ℂ} :
    z ∈ Dom m ρ ↔ ‖z‖ < 2 * ρ ∧ (7 * (m : ℝ) / 8) * |z.im| < z.re := by
  simp [Dom, Metric.mem_ball, dist_zero_right]

theorem Pet_subset_Dom (m : ℕ) (hm : 1 ≤ m) (ρ : ℝ) : Pet m ρ ⊆ Dom m ρ := by
  intro z hz
  rw [mem_Pet] at hz
  rw [mem_Dom]
  obtain ⟨h1, h2⟩ := hz
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hre : 0 < z.re := lt_of_le_of_lt (mul_nonneg hm0.le (abs_nonneg z.im)) h2
  have hn : 0 ≤ ‖z‖ := norm_nonneg z
  refine ⟨by linarith, ?_⟩
  calc (7 * (m : ℝ) / 8) * |z.im| = (7 / 8) * ((m : ℝ) * |z.im|) := by ring
    _ < (7 / 8) * z.re := mul_lt_mul_of_pos_left h2 (by norm_num)
    _ < z.re := by linarith

theorem isOpen_sector (c : ℝ) : IsOpen {z : ℂ | c * |z.im| < z.re} :=
  isOpen_lt (by fun_prop) (by fun_prop)

theorem isOpen_Pet (m : ℕ) (ρ : ℝ) : IsOpen (Pet m ρ) :=
  Metric.isOpen_ball.inter (isOpen_sector m)

theorem isOpen_Dom (m : ℕ) (ρ : ℝ) : IsOpen (Dom m ρ) :=
  Metric.isOpen_ball.inter (isOpen_sector _)

theorem convex_sector {c : ℝ} (hc : 0 ≤ c) : Convex ℝ {z : ℂ | c * |z.im| < z.re} := by
  intro z hz w hw a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hz hw ⊢
  have h1 : (a • z + b • w).re = a * z.re + b * w.re := by simp
  have h2 : (a • z + b • w).im = a * z.im + b * w.im := by simp
  rw [h1, h2]
  have h3 : |a * z.im + b * w.im| ≤ a * |z.im| + b * |w.im| := by
    calc |a * z.im + b * w.im| ≤ |a * z.im| + |b * w.im| := abs_add_le _ _
      _ = a * |z.im| + b * |w.im| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have h4 : c * |a * z.im + b * w.im| ≤ c * (a * |z.im| + b * |w.im|) :=
    mul_le_mul_of_nonneg_left h3 hc
  have h5 : c * (a * |z.im| + b * |w.im|) = a * (c * |z.im|) + b * (c * |w.im|) := by ring
  rw [h5] at h4
  have key : a * (c * |z.im|) + b * (c * |w.im|) < a * z.re + b * w.re := by
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · have hb1 : b = 1 := by linarith
      rw [← ha0, hb1]; simpa using hw
    · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hz hapos)
        (mul_le_mul_of_nonneg_left hw.le hb)
  linarith

theorem convex_Pet (m : ℕ) (ρ : ℝ) : Convex ℝ (Pet m ρ) :=
  (convex_ball 0 ρ).inter (convex_sector (Nat.cast_nonneg m))

theorem convex_Dom (m : ℕ) (ρ : ℝ) : Convex ℝ (Dom m ρ) :=
  (convex_ball 0 (2 * ρ)).inter (convex_sector (by positivity))

theorem zero_notMem_Pet (m : ℕ) (ρ : ℝ) : (0 : ℂ) ∉ Pet m ρ := by
  rw [mem_Pet]
  intro h
  have h2 : (m : ℝ) * |(0 : ℂ).im| < (0 : ℂ).re := h.2
  simp at h2

theorem zero_notMem_Dom (m : ℕ) (ρ : ℝ) : (0 : ℂ) ∉ Dom m ρ := by
  rw [mem_Dom]
  intro h
  have h2 : (7 * (m : ℝ) / 8) * |(0 : ℂ).im| < (0 : ℂ).re := h.2
  simp at h2

theorem Pet_nonempty (m : ℕ) (hm : 1 ≤ m) {ρ : ℝ} (hρ : 0 < ρ) : (Pet m ρ).Nonempty := by
  have hρ1 : (0 : ℝ) < min ρ 1 := lt_min hρ one_pos
  have h3 : (0 : ℝ) < (min ρ 1) / 2 := by linarith
  refine ⟨(((min ρ 1) / 2 : ℝ) : ℂ), ?_⟩
  rw [mem_Pet]
  refine ⟨?_, ?_⟩
  · have h2 : ‖(((min ρ 1) / 2 : ℝ) : ℂ)‖ ^ 2 = ((min ρ 1) / 2) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
    have hnorm : ‖(((min ρ 1) / 2 : ℝ) : ℂ)‖ = (min ρ 1) / 2 := by
      nlinarith [norm_nonneg (((min ρ 1) / 2 : ℝ) : ℂ)]
    rw [hnorm]
    have : (min ρ 1 : ℝ) ≤ ρ := min_le_left _ _
    linarith
  · rw [Complex.ofReal_im, abs_zero, mul_zero, Complex.ofReal_re]
    linarith

end Work.FatouDeg.Petal
