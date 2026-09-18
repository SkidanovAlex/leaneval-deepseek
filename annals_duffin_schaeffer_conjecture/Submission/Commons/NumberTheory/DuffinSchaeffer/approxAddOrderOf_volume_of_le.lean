import Mathlib.NumberTheory.WellApproximable
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Volume of the set of points near points of exact additive order `q`

On the unit circle `UnitAddCircle`, `approxAddOrderOf UnitAddCircle q δ` is the
union (over the `φ(q)` reduced fractions `m/q`, `m` coprime to `q`) of the open
balls of radius `δ` around `↑(m/q)`. When `2δ ≤ 1/q` these balls are pairwise
disjoint, and each has volume `2δ` (with the normalised Haar measure of total
mass `1` on the circle). Hence the total volume is `φ(q) · 2δ`.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace Commons.NumberTheory.DuffinSchaeffer

namespace ApproxAddOrderOfVolumeOfLe

/-- The point `m/q` of the unit circle. -/
private abbrev pt (q m : ℕ) : UnitAddCircle := ↑((m : ℝ) / q)

/-- Reduced residues modulo `q`, as naturals `< q` coprime to `q`. -/
private abbrev reducedMod (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun a : ℕ => a.gcd q = 1)

/-- In the quotient `ℝ ⧸ ℤ` subtraction passes through the quotient map. -/
private lemma quot_sub (m m' q : ℕ) :
    ((↑((m' : ℝ) / q) : UnitAddCircle) - (↑((m : ℝ) / q) : UnitAddCircle)) =
    (↑(((m' : ℝ) / q) - ((m : ℝ) / q)) : UnitAddCircle) := by
  simp

/-- Real subtraction of two fractions with a common denominator. -/
private lemma real_sub_div (m m' q : ℕ) (hm : m ≤ m') :
    ((m' : ℝ) / q) - ((m : ℝ) / q) = ((m' - m : ℕ) : ℝ) / (q : ℝ) := by
  rw [← sub_div]
  rw [Nat.cast_sub hm]

/-- `pt q m₂ - pt q m₁ = ↑((m₂ - m₁)/q)` when `m₁ ≤ m₂`. -/
private lemma pt_sub_of_le (q m₁ m₂ : ℕ) (hm : m₁ ≤ m₂) :
    pt q m₂ - pt q m₁ = (↑(((m₂ - m₁ : ℕ) : ℝ) / (q : ℝ)) : UnitAddCircle) := by
  rw [quot_sub]
  congr 1
  exact real_sub_div m₁ m₂ q hm

/-- For `1 ≤ a < q` the circle norm of `a/q` is at least `1/q`. -/
private lemma norm_div_ge (q a : ℕ) (hq : 0 < q) (ha1 : 1 ≤ a) (haq : a < q) :
    (1 : ℝ) / q ≤ ‖((↑(((a : ℝ) / q))) : UnitAddCircle)‖ := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hmin1 : 1 ≤ (min (a % q) (q - a % q) : ℕ) := by
    rw [Nat.mod_eq_of_lt haq]
    apply le_min <;> omega
  have hminR : (1 : ℝ) ≤ ((min (a % q) (q - a % q) : ℕ) : ℝ) := by exact_mod_cast hmin1
  have hquot : (1 : ℝ) / (q : ℝ) ≤ (((min (a % q) (q - a % q) : ℕ) : ℝ) / (q : ℝ)) :=
    div_le_div_of_nonneg_right hminR (le_of_lt hqR)
  have hnorm : ‖((↑(((a : ℝ) / q))) : UnitAddCircle)‖ =
      (((min (a % q) (q - a % q) : ℕ) : ℝ) / (q : ℝ)) := by
    simpa [one_mul] using (AddCircle.norm_div_natCast (p := (1 : ℝ)) (m := a) (n := q))
  simpa [hnorm] using hquot

/-- Distinct points `m₁/q`, `m₂/q` with `m₁, m₂ < q` are at circle-distance at least `1/q`. -/
private lemma pt_norm_sub_ge (q m₁ m₂ : ℕ) (hq : 0 < q) (hm₁ : m₁ < q) (hm₂ : m₂ < q)
    (hne : m₁ ≠ m₂) : (1 : ℝ) / q ≤ ‖(pt q m₁ - pt q m₂)‖ := by
  rcases lt_or_gt_of_ne hne with h12 | h21
  · have hb : (1 : ℝ) / q ≤ ‖(pt q m₂ - pt q m₁)‖ := by
      rw [pt_sub_of_le q m₁ m₂ (le_of_lt h12)]
      exact norm_div_ge q (m₂ - m₁) hq (by omega) (by omega)
    have hsym : ‖(pt q m₂ - pt q m₁)‖ = ‖(pt q m₁ - pt q m₂)‖ := by
      rw [← neg_sub (a := pt q m₂) (b := pt q m₁), norm_neg]
    simpa [hsym] using hb
  · rw [pt_sub_of_le q m₂ m₁ (le_of_lt h21)]
    exact norm_div_ge q (m₁ - m₂) hq (by omega) (by omega)

/-- Balls of radius `δ` around distinct points `m/q` are disjoint when `2 * δ ≤ 1 / q`. -/
private lemma ball_disjoint_of_le (q : ℕ) (hq : 0 < q) (δ : ℝ) (hδq : 2 * δ ≤ 1 / (q : ℝ))
    (m₁ m₂ : ℕ) (hm₁ : m₁ < q) (hm₂ : m₂ < q) (hne : m₁ ≠ m₂) :
    Disjoint (ball (pt q m₁) δ) (ball (pt q m₂) δ) := by
  refine Metric.ball_disjoint_ball ?_
  rw [dist_eq_norm]
  have hdist : (1 : ℝ) / (q : ℝ) ≤ ‖(pt q m₁ - pt q m₂)‖ := by
    simpa using pt_norm_sub_ge q m₁ m₂ hq hm₁ hm₂ hne
  have hδq' : δ + δ ≤ (1 : ℝ) / (q : ℝ) := by
    simpa [two_mul] using hδq
  linarith

/-- Volume of a ball of radius `δ` in the unit circle when `2δ ≤ 1`. -/
private lemma ball_volume (c : UnitAddCircle) (δ : ℝ) (hδle1 : 2 * δ ≤ 1) :
    volume (ball c δ) = ENNReal.ofReal (2 * δ) := by
  rw [← (measure_congr (AddCircle.closedBall_ae_eq_ball (T := (1 : ℝ)) (x := c) (ε := δ)))]
  rw [AddCircle.volume_closedBall (T := (1 : ℝ)) (x := c) δ]
  rw [min_eq_right hδle1]

/-- `approxAddOrderOf UnitAddCircle q δ` is the union of the balls of radius `δ`
about the points `m/q` with `m` a reduced residue modulo `q`. -/
private lemma approx_eq_biUnion (q : ℕ) (hq : 0 < q) (δ : ℝ) :
    approxAddOrderOf UnitAddCircle q δ = ⋃ m ∈ reducedMod q, ball (pt q m) δ := by
  ext x
  rw [UnitAddCircle.mem_approxAddOrderOf_iff (hn := hq)]
  constructor
  · rintro ⟨m, hmlt, hgcd, hx⟩
    refine mem_iUnion₂.mpr ⟨m, ?_, ?_⟩
    · simpa [reducedMod, Finset.mem_filter] using ⟨hmlt, hgcd⟩
    · simpa [mem_ball, dist_eq_norm, pt] using hx
  · intro hx
    rcases mem_iUnion₂.mp hx with ⟨m, hmf, hxb⟩
    rw [mem_ball, dist_eq_norm, pt] at hxb
    rw [reducedMod, Finset.mem_filter] at hmf
    exact ⟨m, (by simpa using hmf.1 : m < q), hmf.2, hxb⟩

/-- The number of naturals `< q` coprime to `q` is `φ q`. -/
private lemma card_reducedMod (q : ℕ) : (reducedMod q).card = q.totient := by
  calc
    (reducedMod q).card = ((Finset.range q).filter (fun m : ℕ => q.Coprime m)).card := by
      congr 1
      refine Finset.filter_congr ?_
      intro m hm
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
    _ = q.totient := by
      exact (Nat.totient_eq_card_coprime q).symm

end ApproxAddOrderOfVolumeOfLe

/-- Volume of the points of `UnitAddCircle` at distance `< δ` of a point of exact additive
order `q`, for `2δ ≤ 1/q`. -/
theorem approxAddOrderOf_volume_of_le (q : ℕ) (hq : 0 < q) (δ : ℝ) (hδ : 0 ≤ δ)
    (hδq : 2 * δ ≤ 1 / (q : ℝ)) :
    MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δ) =
      (q.totient : ENNReal) * ENNReal.ofReal (2 * δ) := by
  classical
  open ApproxAddOrderOfVolumeOfLe in
  have hδ_nonneg : 0 ≤ δ := hδ
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hq)
  have h1div : (1 : ℝ) / (q : ℝ) ≤ 1 := (div_le_one₀ hqR).2 hq1
  have hδle1 : 2 * δ ≤ 1 := by linarith
  calc
    volume (approxAddOrderOf UnitAddCircle q δ) = volume (⋃ m ∈ reducedMod q, ball (pt q m) δ) := by
      congr 1
      exact approx_eq_biUnion q hq δ
    _ = ∑ m ∈ reducedMod q, volume (ball (pt q m) δ) := by
      refine MeasureTheory.measure_biUnion_finset ?_ ?_
      · intro m hm m' hm' hne
        have hm1 : m < q ∧ m.gcd q = 1 := by simpa [reducedMod, Finset.mem_filter] using hm
        have hm2 : m' < q ∧ m'.gcd q = 1 := by simpa [reducedMod, Finset.mem_filter] using hm'
        exact ball_disjoint_of_le q hq δ hδq m m' hm1.1 hm2.1 hne
      · intro m hm
        exact measurableSet_ball
    _ = ∑ m ∈ reducedMod q, ENNReal.ofReal (2 * δ) := by
      refine Finset.sum_congr rfl ?_
      intro m hm
      exact ball_volume (pt q m) δ hδle1
    _ = (reducedMod q).card • ENNReal.ofReal (2 * δ) := by
      rw [Finset.sum_const]
    _ = (q.totient : ENNReal) * ENNReal.ofReal (2 * δ) := by
      have hS : (reducedMod q).card = q.totient := card_reducedMod q
      rw [hS]
      simp

end Commons.NumberTheory.DuffinSchaeffer