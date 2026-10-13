import Mathlib
import Submission.Work.WilE2.FlatPart.volume_image_eq_zero_of_pair_flat
import Submission.Work.WilE2.FlatPart.volume_closedBall_le_of_le_pow

/-!
# Vector-valued flat maps: `n ≤ q * m` forces a null image

If `f : ℝⁿ → ℝᵐ` is flat of order `q` along a bounded set `A ⊆ ℝⁿ` — at every `x ∈ A` and every
`ε > 0` there is `ρ > 0` with `‖f y - f x‖ ≤ ε ‖y - x‖ ^ q` for `y ∈ A`, `‖y - x‖ ≤ ρ` — and
`n ≤ q * m`, then `f '' A` is Lebesgue-null.  This is the vector-valued form of Peano's theorem
for flat maps; it is proved by the same Vitali covering argument, the extra codimension being paid
for by the extra flatness order: the image of a ball of radius `5 r` is contained in a ball of
radius `ε (5 r) ^ q` in `ℝᵐ`, whose `m`-dimensional content is `ε ^ m (5 r) ^ (q * m) ≤ ε ^ m 5 ^ n
r ^ n` once `r ≤ 1/5` and `q * m ≥ n`.

The statement is false without `n ≤ q * m` (take `m = 1`, `f = id` and `q < n`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Topology

namespace Work.WilE9G.Sard

/-- **Ball estimate for vector-valued flat maps.**  If `n ≤ q * m` and `r ≤ 1/5`, then the
`m`-dimensional volume of a ball of radius `ε * (5 * r) ^ q` is at most
`ofReal (2 ^ m * ε ^ m * 5 ^ n / 2 ^ n)` times the `n`-dimensional volume of a ball of radius `r`:
the `m`-fold product `(5 r) ^ (q * m)` is dominated by `(5 r) ^ n` because `5 r ≤ 1`. -/
theorem volume_closedBall_le_of_le_pow_vec {n m q : ℕ} (hq : n ≤ q * m) (b : Fin n → ℝ) {r : ℝ}
    (hr : 0 < r) (hr5 : r ≤ 1 / 5) {ε : ℝ} (hε : 0 < ε) (c : Fin m → ℝ) :
    MeasureTheory.volume (Metric.closedBall c (ε * (5 * r) ^ q))
      ≤ ENNReal.ofReal (2 ^ m * ε ^ m * 5 ^ n / 2 ^ n) *
        MeasureTheory.volume (Metric.ball b r) := by
  have h5r0 : 0 ≤ 5 * r := by linarith
  have h5r1 : 5 * r ≤ 1 := by linarith
  have hrad : 0 ≤ ε * (5 * r) ^ q := mul_nonneg hε.le (pow_nonneg h5r0 q)
  rw [Real.volume_pi_closedBall c hrad, Real.volume_pi_ball b hr, Fintype.card_fin,
    Fintype.card_fin]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ m * ε ^ m * 5 ^ n / 2 ^ n)]
  apply ENNReal.ofReal_le_ofReal
  have hp : (5 * r) ^ (q * m) ≤ (5 * r) ^ n := pow_le_pow_of_le_one h5r0 h5r1 hq
  have h2 : (2 : ℝ) ^ m * ε ^ m * 5 ^ n / 2 ^ n * (2 * r) ^ n
      = 2 ^ m * ε ^ m * (5 * r) ^ n := by
    rw [mul_pow]
    field_simp
    ring
  rw [h2]
  calc (2 * (ε * (5 * r) ^ q)) ^ m
      = 2 ^ m * ε ^ m * (5 * r) ^ (q * m) := by
        rw [mul_pow, mul_pow, ← pow_mul]
        ring
    _ ≤ 2 ^ m * ε ^ m * (5 * r) ^ n :=
        mul_le_mul_of_nonneg_left hp (by positivity)

/-- **Flat-along-`A` vector-valued maps of order `q` with `n ≤ q * m` have null image.**  If at
every point `x` of a bounded set `A ⊆ ℝⁿ` the map `f : ℝⁿ → ℝᵐ` is flat of order `q` *along `A`*
-- for every `ε > 0` there is a ball around `x` on which `‖f y - f x‖ ≤ ε ‖y - x‖ ^ q` for all
`y ∈ A` -- and `n ≤ q * m`, then `f '' A` is Lebesgue-null.

The proof is the Vitali covering argument: for a fixed `ε > 0` choose at each `x ∈ A` a radius
`ρ x > 0` witnessing the hypothesis and put `r x = min (ρ x) 1 / 5`.  The Vitali covering theorem
(`Vitali.exists_disjoint_subfamily_covering_enlargement_ball`, `τ = 5`) extracts a family `u ⊆ A`
of pairwise disjoint balls `ball b (r b)` whose `5`-fold dilates cover `A`.  On `ball b (5 r b)` the
map `f` deviates from `f b` by at most `ε (5 r b) ^ q`, so `f '' A` is covered by the balls
`closedBall (f b) (ε (5 r b) ^ q)` of `ℝᵐ`; by `volume_closedBall_le_of_le_pow_vec` each of these
has `m`-volume comparable to the disjoint ball `ball b (r b)` in `ℝⁿ`, so the total is at most
`C ε ^ m`.  Letting `ε → 0` gives the result. -/
theorem volume_image_eq_zero_of_flat_along_vec {n m q : ℕ} (hm : 0 < m) (hq : n ≤ q * m)
    (f : (Fin n → ℝ) → (Fin m → ℝ)) (A : Set (Fin n → ℝ)) (hA : Bornology.IsBounded A)
    (h : ∀ x ∈ A, ∀ ε > 0, ∃ ρ > 0, ∀ y ∈ A, ‖y - x‖ ≤ ρ → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ q) :
    MeasureTheory.volume (f '' A) = 0 := by
  classical
  obtain ⟨R₀, hR₀⟩ := hA.subset_closedBall (0 : Fin n → ℝ)
  set R : ℝ := max R₀ 0 with hRdef
  have hRnn : 0 ≤ R := le_max_right _ _
  have hRsub : A ⊆ Metric.closedBall (0 : Fin n → ℝ) R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hmain : ∀ ε > 0, MeasureTheory.volume (f '' A) ≤
      ENNReal.ofReal (2 ^ m * 5 ^ n / 2 ^ n * (2 * (R + 1 / 5)) ^ n * ε ^ m) := by
    intro ε hε
    have h' : ∀ x : Fin n → ℝ, ∃ ρ > 0,
        x ∈ A → ∀ y ∈ A, ‖y - x‖ ≤ ρ → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ q := by
      intro x
      by_cases hx : x ∈ A
      · obtain ⟨ρ, hρ, hP⟩ := h x hx ε hε
        exact ⟨ρ, hρ, fun _ => hP⟩
      · exact ⟨1, one_pos, fun hx' => absurd hx' hx⟩
    choose ρ hρspec using h'
    have hρpos : ∀ x, 0 < ρ x := fun x => (hρspec x).1
    have hρprop : ∀ x ∈ A, ∀ y ∈ A, ‖y - x‖ ≤ ρ x → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ q :=
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
    have himg : f '' A ⊆ ⋃ b ∈ u, Metric.closedBall (f b) (ε * (5 * r b) ^ q) := by
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
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hyb.le q) hε.le
    have hterm : ∀ b : ↥u,
        MeasureTheory.volume (Metric.closedBall (f b.1) (ε * (5 * r b.1) ^ q))
          ≤ ENNReal.ofReal (2 ^ m * ε ^ m * 5 ^ n / 2 ^ n) *
            MeasureTheory.volume (Metric.ball b.1 (r b.1)) :=
      fun b => volume_closedBall_le_of_le_pow_vec (n := n) (m := m) (q := q) hq b.1
        (hrpos b.1) (hrle b.1) hε (f b.1)
    have hsum1 : MeasureTheory.volume (f '' A) ≤
        ∑' b : ↥u, MeasureTheory.volume (Metric.closedBall (f b.1) (ε * (5 * r b.1) ^ q)) := by
      refine le_trans (MeasureTheory.measure_mono himg) ?_
      exact MeasureTheory.measure_biUnion_le MeasureTheory.volume hucount
        (fun b => Metric.closedBall (f b) (ε * (5 * r b) ^ q))
    have hsum2 : (∑' b : ↥u, MeasureTheory.volume (Metric.closedBall (f b.1) (ε * (5 * r b.1) ^ q)))
        ≤ ENNReal.ofReal (2 ^ m * ε ^ m * 5 ^ n / 2 ^ n) *
          ∑' b : ↥u, MeasureTheory.volume (Metric.ball b.1 (r b.1)) := by
      calc (∑' b : ↥u, MeasureTheory.volume (Metric.closedBall (f b.1) (ε * (5 * r b.1) ^ q)))
          ≤ ∑' b : ↥u, ENNReal.ofReal (2 ^ m * ε ^ m * 5 ^ n / 2 ^ n) *
              MeasureTheory.volume (Metric.ball b.1 (r b.1)) :=
            ENNReal.tsum_le_tsum (fun b => hterm b)
        _ = ENNReal.ofReal (2 ^ m * ε ^ m * 5 ^ n / 2 ^ n) *
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
        ≤ ∑' b : ↥u, MeasureTheory.volume (Metric.closedBall (f b.1) (ε * (5 * r b.1) ^ q)) :=
          hsum1
      _ ≤ ENNReal.ofReal (2 ^ m * ε ^ m * 5 ^ n / 2 ^ n) *
          (∑' b : ↥u, MeasureTheory.volume (Metric.ball b.1 (r b.1))) := hsum2
      _ ≤ ENNReal.ofReal (2 ^ m * ε ^ m * 5 ^ n / 2 ^ n) *
          ENNReal.ofReal ((2 * (R + 1 / 5)) ^ n) :=
          mul_le_mul (le_refl _) hdomain bot_le bot_le
      _ = ENNReal.ofReal (2 ^ m * 5 ^ n / 2 ^ n * (2 * (R + 1 / 5)) ^ n * ε ^ m) := by
          rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ m * ε ^ m * 5 ^ n / 2 ^ n)]
          congr 1
          ring
  have hC : (0 : ℝ) ≤ 2 ^ m * 5 ^ n / 2 ^ n * (2 * (R + 1 / 5)) ^ n := by positivity
  refine Work.WilE2.FlatPart.eq_zero_of_forall_le_ofReal_mul
    (a := MeasureTheory.volume (f '' A)) (C := 2 ^ m * 5 ^ n / 2 ^ n * (2 * (R + 1 / 5)) ^ n)
    hC (fun ε hε => ?_)
  have hε1 : 0 < min ε 1 := lt_min hε one_pos
  have hle1 : min ε 1 ≤ 1 := min_le_right _ _
  have hpow : (min ε 1) ^ m ≤ min ε 1 := pow_le_of_le_one (le_of_lt hε1) hle1 hm.ne'
  calc MeasureTheory.volume (f '' A)
      ≤ ENNReal.ofReal (2 ^ m * 5 ^ n / 2 ^ n * (2 * (R + 1 / 5)) ^ n * (min ε 1) ^ m) :=
        hmain (min ε 1) hε1
    _ ≤ ENNReal.ofReal (2 ^ m * 5 ^ n / 2 ^ n * (2 * (R + 1 / 5)) ^ n * ε) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left (le_trans hpow (min_le_left ε 1)) hC

end Work.WilE9G.Sard
