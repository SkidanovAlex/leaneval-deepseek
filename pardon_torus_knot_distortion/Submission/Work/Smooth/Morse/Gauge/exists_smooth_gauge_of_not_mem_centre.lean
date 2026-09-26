import Mathlib
import Submission.Work.Smooth.Morse.Gauge
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Morse.Surface.isCompact_torus

/-!
# Smoothing Pardon's box gauge away from the surface

The explicit gauge `Work.Smooth.Morse.boxGauge c σ k` of Pardon's box is a norm on `ℝ³` and hence
is *not* smooth at the centre `c` of the box (it behaves like the norm there, and the `ℓ^{2k}`-norm
has a corner at `0`).  Every statement of the sweep that needs a `C^∞` gauge, however, only uses
`boxGauge` *on the surface* `F = torus ψ`: the regions are `F ∩ {boxGauge < t}`.  So it suffices to
replace `boxGauge` by a `C^∞` function with the same values on `F`.

This file does exactly that, and is therefore the only place where the smoothness of the gauge is
established.  The construction is elementary:

* `gaugeSum c σ k y = ∑ᵢ ((y (σ i) - c (σ i)) / boxSide i)^{2k}` is a polynomial (so `C^∞`), and
  because the exponents `2k` are even it equals the sum `∑ᵢ |…|^{2k}` of `boxGauge`, so that
  `boxGauge c σ k y = (gaugeSum c σ k y)^{1/(2k)}` (`boxGauge_eq_gaugeSum`);
* the surface `F` is compact and avoids `c`, so `gaugeSum c σ k` has a strictly positive minimum
  `m` on it (`gaugeSum_pos`, `IsCompact.exists_isMinOn`);
* the `C^∞` function `gaugeBase m` of one variable agrees with the identity on `[m, ∞)` and is
  bounded below by `m/2 > 0`, via `Real.smoothTransition` (`gaugeBase_eq_of_le`, `gaugeBase_ge`);
* hence `g y = (gaugeBase m (gaugeSum c σ k y))^{1/(2k)}` is `C^∞` (the base is everywhere
  positive) and agrees with `boxGauge c σ k` on `F`, because there `gaugeSum c σ k ≥ m`.

The last two facts give the required equality of all sublevel regions on the surface.
-/

namespace Work.Smooth.Morse.Gauge

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-- The polynomial `∑ᵢ ((y (σ i) - c (σ i)) / boxSide i)^{2k}`.  Since the exponents are even it
equals the sum appearing in `boxGauge c σ k`, and it is `C^∞` everywhere (unlike the gauge, which
involves a root). -/
private def gaugeSum (c : R3) (σ : Equiv.Perm (Fin 3)) (k : ℕ) (y : R3) : ℝ :=
  ∑ i : Fin 3, ((y (σ i) - c (σ i)) / Submission.boxSide i) ^ (2 * k)

private lemma contDiff_gaugeSum (c : R3) (σ : Equiv.Perm (Fin 3)) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (gaugeSum c σ k) := by
  unfold gaugeSum
  fun_prop

/-- The even exponents let us drop the absolute values. -/
private lemma gaugeSum_eq_abs (c : R3) (σ : Equiv.Perm (Fin 3)) (k : ℕ) (y : R3) :
    gaugeSum c σ k y =
      ∑ i : Fin 3, |(y (σ i) - c (σ i)) / Submission.boxSide i| ^ (2 * k) := by
  unfold gaugeSum
  exact Finset.sum_congr rfl fun i _ => by rw [pow_mul, pow_mul, sq_abs]

/-- The gauge is the `(2k)`-th root of `gaugeSum`. -/
private lemma boxGauge_eq_gaugeSum (c : R3) (σ : Equiv.Perm (Fin 3)) (k : ℕ) (y : R3) :
    Work.Smooth.Morse.boxGauge c σ k y =
      (gaugeSum c σ k y) ^ (1 / (2 * (k : ℝ))) := by
  unfold Work.Smooth.Morse.boxGauge
  rw [← gaugeSum_eq_abs]

/-- `gaugeSum c σ k` vanishes only at the centre `c` of the box: its summands are the squared
coordinates of `y - c` rescaled by the (non-zero) side lengths and permuted by `σ`. -/
private lemma gaugeSum_pos {c : R3} {σ : Equiv.Perm (Fin 3)} {k : ℕ} {y : R3}
    (hy : y ≠ c) : 0 < gaugeSum c σ k y := by
  have hex : ∃ i : Fin 3, (y (σ i) - c (σ i)) / Submission.boxSide i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_ne_iff] at h
    refine hy ?_
    ext j
    obtain ⟨i, rfl⟩ := σ.surjective j
    have h1 : y (σ i) - c (σ i) = 0 := by
      rcases div_eq_zero_iff.mp (h i) with h' | h'
      · exact h'
      · exact absurd h' (ne_of_gt (Submission.boxSide_pos i))
    exact sub_eq_zero.mp h1
  obtain ⟨i, hi⟩ := hex
  have hmem : ((y (σ i) - c (σ i)) / Submission.boxSide i) ^ (2 * k) ≤ gaugeSum c σ k y := by
    rw [gaugeSum]
    exact Finset.single_le_sum
      (f := fun j : Fin 3 => ((y (σ j) - c (σ j)) / Submission.boxSide j) ^ (2 * k))
      (fun j _ => by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) k) (Finset.mem_univ i)
  have hpos : 0 < ((y (σ i) - c (σ i)) / Submission.boxSide i) ^ (2 * k) := by
    rw [pow_mul]
    exact pow_pos (sq_pos_of_ne_zero hi) k
  exact lt_of_lt_of_le hpos hmem

/-- A `C^∞` function of one variable which agrees with the identity on `[m, ∞)` and is bounded
below by `m/2` (for `m > 0`).  `Real.smoothTransition` interpolates between the constant `m/2` and
the identity over the interval `[m/2, m]`. -/
private def gaugeBase (m : ℝ) (u : ℝ) : ℝ :=
  m / 2 + Real.smoothTransition (2 * u / m - 1) * (u - m / 2)

private lemma contDiff_gaugeBase (m : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (gaugeBase m) := by
  unfold gaugeBase
  fun_prop

private lemma gaugeBase_ge {m : ℝ} (hm : 0 < m) (u : ℝ) : m / 2 ≤ gaugeBase m u := by
  unfold gaugeBase
  rcases le_or_gt (m / 2) u with h | h
  · have h1 : 0 ≤ Real.smoothTransition (2 * u / m - 1) := Real.smoothTransition.nonneg _
    have h2 : 0 ≤ u - m / 2 := by linarith
    nlinarith [mul_nonneg h1 h2]
  · have h2u : 2 * u ≤ m := by
      have hu : u ≤ m / 2 := le_of_lt h
      linarith
    have h2 : 2 * u / m - 1 ≤ 0 := by
      have h3 : 2 * u / m ≤ 1 := (div_le_one hm).mpr h2u
      linarith
    rw [Real.smoothTransition.zero_of_nonpos h2, zero_mul]
    linarith

private lemma gaugeBase_eq_of_le {m : ℝ} (hm : 0 < m) {u : ℝ} (hu : m ≤ u) :
    gaugeBase m u = u := by
  unfold gaugeBase
  have h2 : 2 * m ≤ 2 * u := by linarith
  have h3 : 2 ≤ 2 * u / m := (le_div_iff₀ hm).mpr h2
  have h1 : 1 ≤ 2 * u / m - 1 := by linarith
  rw [Real.smoothTransition.one_of_one_le h1, one_mul]
  ring

/-- Two functions which agree on the surface have the same sublevel regions on the surface. -/
private lemma region_congr {ψ : Submission.Diffeo} {g g' : R3 → ℝ}
    (h : ∀ y ∈ (Work.Smooth.Morse.torus ψ).carrier, g y = g' y) (t : ℝ) :
    Work.Smooth.Morse.region ψ g t = Work.Smooth.Morse.region ψ g' t := by
  ext x
  rw [Work.Smooth.Morse.mem_region, Work.Smooth.Morse.mem_region]
  constructor
  · rintro ⟨hx, hlt⟩
    exact ⟨hx, by rw [← h x hx]; exact hlt⟩
  · rintro ⟨hx, hlt⟩
    exact ⟨hx, by rw [h x hx]; exact hlt⟩

theorem exists_smooth_gauge_of_not_mem_centre (ψ : Submission.Diffeo) {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {k : ℕ}
    (hc : c ∉ (Work.Smooth.Morse.torus ψ).carrier) :
    ∃ g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧
      ∀ t : ℝ, Work.Smooth.Morse.region ψ g t = Work.Smooth.Morse.region ψ (Work.Smooth.Morse.boxGauge c σ k) t := by
  obtain ⟨y₀, hy₀K, hy₀min⟩ :=
    (Work.Smooth.Morse.Surface.isCompact_torus ψ).exists_isMinOn
      ⟨param ψ (0, 0), ⟨(0, 0), rfl⟩⟩ (contDiff_gaugeSum c σ k).continuous.continuousOn
  have hy₀ne : y₀ ≠ c := fun h => hc (h ▸ hy₀K)
  have hm_pos : 0 < gaugeSum c σ k y₀ := gaugeSum_pos hy₀ne
  refine ⟨fun y => (gaugeBase (gaugeSum c σ k y₀) (gaugeSum c σ k y)) ^ (1 / (2 * (k : ℝ))),
    ?_, ?_⟩
  · refine ContDiff.rpow_const_of_ne ?_ ?_
    · exact (contDiff_gaugeBase (gaugeSum c σ k y₀)).comp (contDiff_gaugeSum c σ k)
    · intro y
      exact ne_of_gt (lt_of_lt_of_le (half_pos hm_pos) (gaugeBase_ge hm_pos _))
  · intro t
    refine region_congr ?_ t
    intro y hy
    rw [boxGauge_eq_gaugeSum, gaugeBase_eq_of_le hm_pos (hy₀min hy)]

end

end Work.Smooth.Morse.Gauge
