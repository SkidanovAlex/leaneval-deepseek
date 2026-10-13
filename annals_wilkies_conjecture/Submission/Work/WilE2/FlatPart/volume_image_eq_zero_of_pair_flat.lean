import Mathlib
import Submission.Work.WilE2.SardDefs
import Submission.Work.WilE2.FlatPart.volume_closedBall_le_of_le_pow
import Submission.Work.WilE2.FlatPart.eq_zero_of_forall_le_ofReal_mul

/-!
# Pairwise flatness of order `j + 1 ≥ n` forces a null image

If `f : ℝⁿ → ℝ` is "flat of order `j+1`" along a bounded set `A ⊆ ℝⁿ`, in the sense that for
every `x ∈ A` and every `ε > 0` there is a radius `ρ > 0` with
`‖f y - f x‖ ≤ ε ‖y - x‖ ^ (j+1)` for all `y ∈ A`, `‖y - x‖ ≤ ρ`, and if `n ≤ j + 1`, then
`f '' A` has Lebesgue measure zero.

This is the pointwise ("pairwise") form of Peano's theorem for flat maps
(`Submission/Work/WilE2/volume_image_eq_zero_of_peano.lean`), which is the special case `j + 1 = n`
in which the hypothesis holds for *all* `y`.  The proof is the same Vitali covering argument: the
extra room `j + 1 ≥ n` only makes the image of each ball smaller.

The statement is false without `n ≤ j + 1` (take `f = id` on an interval and `j + 1 < n`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Topology

namespace Work.WilE2.FlatPart

/-- **Flat-along-`A` maps of order `k ≥ n` have null image.**  If at every point `x` of a bounded
set `A ⊆ ℝⁿ` the function `f : ℝⁿ → ℝ` is flat of order `k` *along `A`* — for every `ε > 0` there
is a ball around `x` on which `‖f y - f x‖ ≤ ε ‖y - x‖ ^ k` for all `y ∈ A` — and `k ≥ n`, then
`f '' A` is Lebesgue-null.

The proof is the Vitali covering argument of Peano's theorem.  For a fixed `ε > 0` choose at each
`x ∈ A` a radius `ρ x > 0` witnessing the hypothesis and put `r x = min (ρ x) 1 / 5`.  The Vitali
covering theorem (`Vitali.exists_disjoint_subfamily_covering_enlargement_ball`, `τ = 5`) extracts
a family `u ⊆ A` of pairwise disjoint balls `ball b (r b)` whose `5`-fold dilates cover `A`.  On
`ball b (5 * r b) ⊆ ball b (ρ b)` the function `f` deviates from `f b` by at most `ε (5 r b) ^ k`;
since `r b ≤ 1/5` and `k ≥ n`, `(5 r b) ^ k ≤ (5 r b) ^ n`, so `f '' A` is covered by balls whose
`n`-dimensional content is comparable to that of `ball b (r b)`.  Disjointness makes `u` countable
and bounds `∑_{b ∈ u} volume (ball b (r b))` by `volume (closedBall 0 (R + 1/5))`, where
`A ⊆ closedBall 0 R`; letting `ε → 0` gives the result. -/
theorem volume_image_eq_zero_of_flat_along {n k : ℕ} (hk : n ≤ k) (f : (Fin n → ℝ) → ℝ)
    (A : Set (Fin n → ℝ)) (hA : Bornology.IsBounded A)
    (h : ∀ x ∈ A, ∀ ε > 0, ∃ ρ > 0, ∀ y ∈ A, ‖y - x‖ ≤ ρ → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ k) :
    MeasureTheory.volume (f '' A) = 0 := by
  classical
  obtain ⟨R₀, hR₀⟩ := hA.subset_closedBall (0 : Fin n → ℝ)
  set R : ℝ := max R₀ 0 with hRdef
  have hRnn : 0 ≤ R := le_max_right _ _
  have hRsub : A ⊆ Metric.closedBall (0 : Fin n → ℝ) R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hmain : ∀ ε > 0, MeasureTheory.volume (f '' A) ≤
      ENNReal.ofReal (2 * ε * 5 ^ n * (R + 1 / 5) ^ n) := by
    intro ε hε
    have h' : ∀ x : Fin n → ℝ, ∃ ρ > 0,
        x ∈ A → ∀ y ∈ A, ‖y - x‖ ≤ ρ → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ k := by
      intro x
      by_cases hx : x ∈ A
      · obtain ⟨ρ, hρ, hP⟩ := h x hx ε hε
        exact ⟨ρ, hρ, fun _ => hP⟩
      · exact ⟨1, one_pos, fun hx' => absurd hx' hx⟩
    choose ρ hρspec using h'
    have hρpos : ∀ x, 0 < ρ x := fun x => (hρspec x).1
    have hρprop : ∀ x ∈ A, ∀ y ∈ A, ‖y - x‖ ≤ ρ x → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ k :=
      fun x hx => (hρspec x).2 hx
    set r : (Fin n → ℝ) → ℝ := fun x => min (ρ x) 1 / 5 with hrdef
    have hrpos : ∀ x, 0 < r x := by
      intro x
      rw [hrdef]
      exact div_pos (lt_min (hρpos x) one_pos) (by norm_num)
    have hrle : ∀ x, r x ≤ 1 / 5 := by
      intro x
      rw [hrdef]
      exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    obtain ⟨u, huA, hudisj, hucov⟩ :=
      Vitali.exists_disjoint_subfamily_covering_enlargement_ball (t := A)
        (x := fun z : Fin n → ℝ => z) (r := r) (R := 1 / 5) (fun a _ => hrle a) 5 (by norm_num)
    have hucount : u.Countable :=
      hudisj.countable_of_isOpen (fun i _ => Metric.isOpen_ball)
        (fun i _ => ⟨i, Metric.mem_ball_self (hrpos i)⟩)
    have hcoverA : A ⊆ ⋃ b ∈ u, Metric.ball b (5 * r b) := by
      intro a ha
      obtain ⟨b, hbu, hb⟩ := hucov a ha
      exact Set.mem_iUnion₂.mpr ⟨b, hbu, hb (Metric.mem_ball_self (hrpos a))⟩
    have himg : f '' A ⊆ ⋃ b ∈ u, Metric.closedBall (f b) (ε * (5 * r b) ^ k) := by
      rintro z ⟨y, hyA, rfl⟩
      obtain ⟨b, hbu, hby⟩ := Set.mem_iUnion₂.mp (hcoverA hyA)
      have hbA : b ∈ A := huA hbu
      have h5r : 5 * r b = min (ρ b) 1 := by rw [hrdef]; ring
      have hyb : ‖y - b‖ < 5 * r b := by
        rw [← dist_eq_norm]; exact Metric.mem_ball.mp hby
      have hbρ : ‖y - b‖ ≤ ρ b := by
        rw [h5r] at hyb
        exact hyb.le.trans (min_le_left _ _)
      refine Set.mem_iUnion₂.mpr ⟨b, hbu, ?_⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      refine (hρprop b hbA y hyA hbρ).trans ?_
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hyb.le k) hε.le
    have hterm : ∀ b : ↥u,
        MeasureTheory.volume (Metric.closedBall (f b.1) (ε * (5 * r b.1) ^ k))
          ≤ ENNReal.ofReal (2 * ε * 5 ^ n / 2 ^ n) *
            MeasureTheory.volume (Metric.ball b.1 (r b.1)) :=
      fun b => volume_closedBall_le_of_le_pow hk b.1 (hrpos b.1) (hrle b.1) hε (f b.1)
    have hsum1 : MeasureTheory.volume (f '' A) ≤
        ∑' b : ↥u, MeasureTheory.volume (Metric.closedBall (f b.1) (ε * (5 * r b.1) ^ k)) := by
      refine le_trans (MeasureTheory.measure_mono himg) ?_
      exact MeasureTheory.measure_biUnion_le MeasureTheory.volume hucount
        (fun b => Metric.closedBall (f b) (ε * (5 * r b) ^ k))
    have hsum2 : (∑' b : ↥u, MeasureTheory.volume (Metric.closedBall (f b.1) (ε * (5 * r b.1) ^ k)))
        ≤ ENNReal.ofReal (2 * ε * 5 ^ n / 2 ^ n) *
          ∑' b : ↥u, MeasureTheory.volume (Metric.ball b.1 (r b.1)) := by
      calc (∑' b : ↥u, MeasureTheory.volume (Metric.closedBall (f b.1) (ε * (5 * r b.1) ^ k)))
          ≤ ∑' b : ↥u, ENNReal.ofReal (2 * ε * 5 ^ n / 2 ^ n) *
              MeasureTheory.volume (Metric.ball b.1 (r b.1)) :=
            ENNReal.tsum_le_tsum (fun b => hterm b)
        _ = ENNReal.ofReal (2 * ε * 5 ^ n / 2 ^ n) *
              ∑' b : ↥u, MeasureTheory.volume (Metric.ball b.1 (r b.1)) :=
            ENNReal.tsum_mul_left
    have hdomain : (∑' b : ↥u, MeasureTheory.volume (Metric.ball b.1 (r b.1)))
        ≤ ENNReal.ofReal ((2 * (R + 1 / 5)) ^ n) := by
      have hbi := MeasureTheory.measure_biUnion (μ := MeasureTheory.volume) hucount hudisj
        (fun b _ => measurableSet_ball)
      rw [← hbi]
      calc MeasureTheory.volume (⋃ b ∈ u, Metric.ball b (r b))
          ≤ MeasureTheory.volume (Metric.closedBall (0 : Fin n → ℝ) (R + 1 / 5)) := by
            refine MeasureTheory.measure_mono ?_
            intro y hy
            obtain ⟨b, hbu, hyb⟩ := Set.mem_iUnion₂.mp hy
            rw [Metric.mem_closedBall]
            have hbR : dist b 0 ≤ R := Metric.mem_closedBall.mp (hRsub (huA hbu))
            have h3 : r b ≤ 1 / 5 := hrle b
            have h1 : dist y 0 ≤ dist y b + dist b 0 := dist_triangle y b 0
            have h2 : dist y b < r b := Metric.mem_ball.mp hyb
            linarith
        _ = ENNReal.ofReal ((2 * (R + 1 / 5)) ^ n) := by
            rw [Real.volume_pi_closedBall (0 : Fin n → ℝ) (by linarith), Fintype.card_fin]
    calc MeasureTheory.volume (f '' A)
        ≤ ∑' b : ↥u, MeasureTheory.volume (Metric.closedBall (f b.1) (ε * (5 * r b.1) ^ k)) := hsum1
      _ ≤ ENNReal.ofReal (2 * ε * 5 ^ n / 2 ^ n) *
          (∑' b : ↥u, MeasureTheory.volume (Metric.ball b.1 (r b.1))) := hsum2
      _ ≤ ENNReal.ofReal (2 * ε * 5 ^ n / 2 ^ n) * ENNReal.ofReal ((2 * (R + 1 / 5)) ^ n) :=
          mul_le_mul (le_refl _) hdomain bot_le bot_le
      _ = ENNReal.ofReal (2 * ε * 5 ^ n * (R + 1 / 5) ^ n) := by
          rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * ε * 5 ^ n / 2 ^ n)]
          congr 1
          rw [mul_pow]
          field_simp
          try ring
  have hC : (0:ℝ) ≤ 2 * 5 ^ n * (R + 1 / 5) ^ n :=
    mul_nonneg (by positivity) (pow_nonneg (by linarith) n)
  exact eq_zero_of_forall_le_ofReal_mul (a := MeasureTheory.volume (f '' A))
    (C := 2 * 5 ^ n * (R + 1 / 5) ^ n) hC (fun ε hε => by
      refine (hmain ε hε).trans (le_of_eq ?_)
      congr 1
      ring)

/-- **Pairwise flatness of order `j + 1 ≥ n` gives a null image.**  If `f : ℝⁿ → ℝ` is flat of
order `j + 1` along a bounded measurable set `A ⊆ ℝⁿ` — for every `x ∈ A` and `ε > 0` there is
`ρ > 0` with `‖f y - f x‖ ≤ ε ‖y - x‖ ^ (j+1)` for all `y ∈ A` at distance `≤ ρ` — and
`n ≤ j + 1`, then `f '' A` has Lebesgue measure zero. -/
theorem volume_image_eq_zero_of_pair_flat {n j : ℕ} (f : (Fin n → ℝ) → ℝ) (A : Set (Fin n → ℝ))
    (hA : Bornology.IsBounded A) (hA' : MeasurableSet A) (hj : n ≤ j + 1)
    (h : ∀ x ∈ A, ∀ ε > 0, ∃ ρ > 0, ∀ y ∈ A, ‖y - x‖ ≤ ρ → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ (j + 1)) :
    MeasureTheory.volume (f '' A) = 0 :=
  volume_image_eq_zero_of_flat_along hj f A hA h

end Work.WilE2.FlatPart
