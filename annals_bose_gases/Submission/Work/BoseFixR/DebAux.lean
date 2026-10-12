import Mathlib.Data.Int.Star
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixR.ChiR0Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.DebAux` — the vocabulary of the six-ball debit comparison

Shared definitions and elementary facts for the target `Work.BoseFixR.deb_le_sixBall`, which
compares the integral over the *crescent* `{u | dist(u, ℓℤ³) < ‖u‖/3}` of the autocorrelation
`u ↦ ∫ x, W x W (x+u)` divided by the nearest-lattice distance against the same autocorrelation
integrated over the six balls `ball (±ℓ eᵢ) ℓ/2` with the distance to the ball's centre.

The vocabulary:

* `debLatD ℓ u` — the nearest-lattice distance (verbatim the `Metric.infDist` of the target);
* `debLC ℓ i = lat ℓ (Pi.single i 1)` — the six centres `±ℓ eᵢ`;
* `debSet ℓ` — the crescent;
* `debPair W u = ∫ x, W x * W (x + u)` — the autocorrelation.

The elementary facts about the `ℓ`-lattice used by the geometric parts (the classification of the
label of a nearby lattice point of norm `ℓ`, and the fact that on the ball `ball v (ℓ/2)` the
nearest lattice point is the centre) are collected here.
-/

noncomputable section

open scoped Real BigOperators
open MeasureTheory Metric

namespace Work.BoseFixR

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The vocabulary -/

/-- The distance to the `ℓ`-lattice `ℓℤ³`, i.e. verbatim the
`Metric.infDist u (Set.range (fun n : Fin 3 → ℤ => lat ℓ n))` of the target. -/
noncomputable def debLatD (ℓ : ℝ) (z : E3) : ℝ :=
  Metric.infDist z (Set.range (fun n : Fin 3 → ℤ => lat ℓ n))

/-- The six centres `±ℓ eᵢ` of the target's right-hand side. -/
noncomputable def debLC (ℓ : ℝ) (i : Fin 3) : E3 := lat ℓ (Pi.single i (1 : ℤ))

/-- The crescent `{u | debLatD ℓ u < ‖u‖ / 3}` (the domain of the target's left-hand side). -/
noncomputable def debSet (ℓ : ℝ) : Set E3 := {u : E3 | debLatD ℓ u < ‖u‖ / 3}

/-- The autocorrelation `debPair W u = ∫ x, W x * W (x + u)`. -/
noncomputable def debPair (W : E3 → ℝ) (u : E3) : ℝ := ∫ x, W x * W (x + u)

lemma debLatD_nonneg (ℓ : ℝ) (z : E3) : 0 ≤ debLatD ℓ z := infDist_nonneg

lemma debLatD_le_dist {ℓ : ℝ} {z : E3} {n : Fin 3 → ℤ} :
    debLatD ℓ z ≤ ‖z - lat ℓ n‖ := by
  simpa [debLatD, dist_eq_norm] using
    (Metric.infDist_le_dist_of_mem (s := Set.range (fun n : Fin 3 → ℤ => lat ℓ n))
      (y := lat ℓ n) ⟨n, rfl⟩)

lemma debLatD_zero {ℓ : ℝ} : (0 : E3) ∈ Set.range (fun n : Fin 3 → ℤ => lat ℓ n) :=
  ⟨0, lat_zero ℓ⟩

lemma debSet_measurable (ℓ : ℝ) : MeasurableSet (debSet ℓ) := by
  have hcont : Continuous fun u : E3 => debLatD ℓ u - ‖u‖ / 3 :=
    (continuous_infDist_pt _).sub (continuous_norm.div_const 3)
  have hset : debSet ℓ = {u : E3 | debLatD ℓ u - ‖u‖ / 3 < 0} := by
    ext u
    simp [debSet, sub_neg]
  rw [hset]
  exact (isOpen_lt hcont continuous_const).measurableSet

/-! ## 2. The lattice norms -/

lemma deb_norm_lat {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (n : Fin 3 → ℤ) :
    ‖lat ℓ n‖ = ℓ * ‖lat1 n‖ := by
  rw [lat_eq_smul, norm_smul, Real.norm_of_nonneg hℓ]

lemma deb_lat1_norm_sq (n : Fin 3 → ℤ) :
    ‖lat1 n‖ ^ 2 = ((∑ i, n i ^ 2 : ℤ) : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [lat1, Real.norm_eq_abs, sq_abs]

lemma deb_one_le_norm_lat1 {n : Fin 3 → ℤ} (hn : n ≠ 0) : 1 ≤ ‖lat1 n‖ := by
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hn (funext hc)
  have h1 : (1 : ℝ) ≤ |(n i : ℝ)| := by
    have h' : (1 : ℤ) ≤ |n i| := Int.one_le_abs hi
    exact_mod_cast h'
  calc (1 : ℝ) ≤ |(n i : ℝ)| := h1
    _ = ‖(lat1 n) i‖ := by simp [lat1, Real.norm_eq_abs]
    _ ≤ ‖lat1 n‖ := PiLp.norm_apply_le _ _

lemma deb_lat1_norm_single (i : Fin 3) : ‖lat1 (Pi.single i (1 : ℤ))‖ = 1 := by
  have h := deb_lat1_norm_sq (Pi.single i (1 : ℤ))
  have h2 : (∑ j, (Pi.single i (1 : ℤ) : Fin 3 → ℤ) j ^ 2 : ℤ) = 1 := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · intro hmem; exact absurd (Finset.mem_univ i) hmem
  rw [h2] at h
  have hnn : (0 : ℝ) ≤ ‖lat1 (Pi.single i (1 : ℤ))‖ := norm_nonneg _
  push_cast at h
  nlinarith [h, hnn]

lemma deb_norm_lat_ge {ℓ : ℝ} (hℓ : 0 < ℓ) {n : Fin 3 → ℤ} (hn : n ≠ 0) :
    ℓ ≤ ‖lat ℓ n‖ := by
  rw [deb_norm_lat hℓ.le]
  nlinarith [deb_one_le_norm_lat1 hn, hℓ]

lemma deb_norm_lc {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (i : Fin 3) : ‖debLC ℓ i‖ = ℓ := by
  rw [debLC, deb_norm_lat hℓ, deb_lat1_norm_single, mul_one]

lemma deb_lat_neg (ℓ : ℝ) (n : Fin 3 → ℤ) : lat ℓ (-n) = -lat ℓ n := by
  ext i; simp [lat]

lemma deb_lat_sub (ℓ : ℝ) (n m : Fin 3 → ℤ) : lat ℓ (n - m) = lat ℓ n - lat ℓ m := by
  ext i; simp only [lat, WithLp.ofLp_sub, Pi.sub_apply]; push_cast; ring

lemma deb_lat_single_neg (ℓ : ℝ) (i : Fin 3) :
    lat ℓ (Pi.single i (-1 : ℤ)) = -debLC ℓ i := by
  have h : (Pi.single i (-1 : ℤ) : Fin 3 → ℤ)
      = -((Pi.single i (1 : ℤ) : Fin 3 → ℤ)) := by
    funext j
    by_cases hj : j = i <;> simp [Pi.single_apply, hj]
  rw [h, deb_lat_neg, debLC]

/-- **The label of a nearby lattice point of norm `ℓ` is `±eᵢ`.**  If `n ≠ 0` and
`‖lat1 n‖ < 4/3` (`lat1 n` is the unit-lattice point of the label `n`), then `n = ±eᵢ`. -/
theorem deb_lat1_classify {n : Fin 3 → ℤ} (hn : n ≠ 0) (h : ‖lat1 n‖ < 4 / 3) :
    ∃ i : Fin 3, n = Pi.single i (1 : ℤ) ∨ n = Pi.single i (-1) := by
  have hsq := deb_lat1_norm_sq n
  have hsq1 : ∀ a : ℤ, a ≠ 0 → (1 : ℤ) ≤ a ^ 2 := by
    intro a ha
    have habs : (1 : ℤ) ≤ |a| := Int.one_le_abs ha
    calc (1 : ℤ) = 1 * 1 := by ring
      _ ≤ |a| * |a| := mul_le_mul habs habs (by norm_num) (by positivity)
      _ = a ^ 2 := by rw [← sq_abs]; ring
  have hex : ∃ i : Fin 3, n i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hn (funext hc)
  obtain ⟨i, hi⟩ := hex
  have hk1 : (1 : ℤ) ≤ ∑ j, n j ^ 2 :=
    le_trans (hsq1 (n i) hi)
      (Finset.single_le_sum (f := fun j : Fin 3 => (n j) ^ 2) (fun j _ => sq_nonneg (n j))
        (Finset.mem_univ i))
  have hklt : (∑ j, n j ^ 2 : ℤ) ≤ 1 := by
    have h2 : ((∑ j, n j ^ 2 : ℤ) : ℝ) < 2 := by
      rw [← hsq]
      nlinarith [norm_nonneg (lat1 n), h]
    have h3 : (∑ j, n j ^ 2 : ℤ) < 2 := by exact_mod_cast h2
    omega
  have hone : ∀ j k : Fin 3, j ≠ k → n j ≠ 0 → n k ≠ 0 → False := by
    intro j k hjk hj hk
    have hsub : ∑ m ∈ ({j, k} : Finset (Fin 3)), (n m) ^ 2 ≤ ∑ m, (n m) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (by intro x _; exact Finset.mem_univ x)
        (by intro x _ _; exact sq_nonneg (n x))
    have hpair : ∑ m ∈ ({j, k} : Finset (Fin 3)), (n m) ^ 2 = (n j) ^ 2 + (n k) ^ 2 :=
      Finset.sum_pair hjk
    have h1 := hsq1 (n j) hj
    have h2 := hsq1 (n k) hk
    omega
  have hzero : ∀ j, j ≠ i → n j = 0 := fun j hj =>
    Decidable.byContradiction (fun hnj => hone j i hj hnj hi)
  have hsingle : n = Pi.single i (n i) := by
    funext j
    rw [Pi.single_apply]
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj, hzero j hj]
  have hni : n i = 1 ∨ n i = -1 := by
    refine sq_eq_one_iff.mp ?_
    have h1 := hsq1 (n i) hi
    have h2 := Finset.single_le_sum (f := fun j : Fin 3 => (n j) ^ 2)
      (fun j _ => sq_nonneg (n j)) (Finset.mem_univ i)
    omega
  rcases hni with h1 | h1
  · exact ⟨i, Or.inl (by rw [hsingle, h1])⟩
  · exact ⟨i, Or.inr (by rw [hsingle, h1])⟩

/-! ## 3. Elementary facts about the autocorrelation -/

/-- The autocorrelation of an `L¹`-function is a.e. strongly measurable (as a function of the
shift).  The proof replaces `W` by a strongly measurable representative and uses
`StronglyMeasurable.integral_prod_left`. -/
theorem debPair_aestronglyMeasurable {W : E3 → ℝ} (hW1 : Integrable W) :
    AEStronglyMeasurable (debPair W) volume := by
  show AEStronglyMeasurable (fun u => ∫ x, W x * W (x + u)) volume
  let W' := (hW1.aestronglyMeasurable).mk W
  have hW'sm : StronglyMeasurable W' := (hW1.aestronglyMeasurable).stronglyMeasurable_mk
  have hW'ae : W =ᵐ[volume] W' := (hW1.aestronglyMeasurable).ae_eq_mk
  have hsm : StronglyMeasurable (fun u : E3 => ∫ x, W' x * W' (x + u)) := by
    have huncurry : StronglyMeasurable
        (Function.uncurry fun x u : E3 => W' x * W' (x + u)) := by
      have h1 : StronglyMeasurable fun p : E3 × E3 => W' p.1 :=
        hW'sm.comp_measurable measurable_fst
      have h2 : StronglyMeasurable fun p : E3 × E3 => W' (p.1 + p.2) :=
        hW'sm.comp_measurable (measurable_fst.add measurable_snd)
      exact h1.mul h2
    exact huncurry.integral_prod_left
  refine hsm.aestronglyMeasurable.congr ?_
  filter_upwards with u
  refine (integral_congr_ae ?_).symm
  filter_upwards [hW'ae,
    (measurePreserving_add_right volume u).quasiMeasurePreserving.ae hW'ae] with x hx hx2
  rw [hx, hx2]

lemma debPair_nonneg {W : E3 → ℝ} (hWnn : 0 ≤ W) (u : E3) : 0 ≤ debPair W u := by
  rw [debPair]
  exact integral_nonneg fun x => mul_nonneg (hWnn x) (hWnn (x + u))

/-- If `W` is supported in `ball 0 R`, the autocorrelation vanishes outside `ball 0 (2R)`
(actually for `‖u‖ ≥ 2R`). -/
lemma debPair_eq_zero_of_norm_ge {R : ℝ} {W : E3 → ℝ}
    (hsupp : tsupport W ⊆ Metric.ball 0 R) {u : E3} (hu : 2 * R ≤ ‖u‖) : debPair W u = 0 := by
  have hzero : ∀ x, W x * W (x + u) = 0 := by
    intro x
    by_cases hx : W x = 0
    · rw [hx, zero_mul]
    by_cases hy : W (x + u) = 0
    · rw [hy, mul_zero]
    exfalso
    have hxR : ‖x‖ < R := by
      have hx' : x ∈ tsupport W := subset_tsupport W (Function.mem_support.mpr hx)
      simpa [Metric.mem_ball, dist_eq_norm] using hsupp hx'
    have hyR : ‖x + u‖ < R := by
      have hy' : x + u ∈ tsupport W := subset_tsupport W (Function.mem_support.mpr hy)
      simpa [Metric.mem_ball, dist_eq_norm] using hsupp hy'
    have htri : ‖u‖ ≤ ‖x‖ + ‖x + u‖ := by
      calc ‖u‖ = ‖(x + u) - x‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖x + u‖ + ‖x‖ := norm_sub_le _ _
        _ = ‖x‖ + ‖x + u‖ := by ring
    linarith
  rw [debPair]
  simp [hzero]

end Work.BoseFixR
