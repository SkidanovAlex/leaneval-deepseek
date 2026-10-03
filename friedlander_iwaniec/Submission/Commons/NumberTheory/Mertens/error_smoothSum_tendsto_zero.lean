import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Submission.Commons.NumberTheory.Mertens.tsum_primes_eq_sum_rpowDiff

open Filter Finset
open scoped BigOperators Topology

namespace Commons.NumberTheory.Mertens

noncomputable section

/-- telescoping difference `(k:ℝ)^(-ε) - ((k+1):ℝ)^(-ε)` for `k ≥ 2`, zero otherwise -/
def smoothCoeff (ε : ℝ) (k : ℕ) : ℝ :=
  if 2 ≤ k then (k : ℝ) ^ (-ε) - (((k + 1 : ℕ) : ℝ) ^ (-ε)) else 0

/-- smoothed summand `e k * smoothCoeff ε k` -/
def smoothTerm (e : ℕ → ℝ) (ε : ℝ) (k : ℕ) : ℝ := e k * smoothCoeff ε k

lemma smoothTerm_eq (e : ℕ → ℝ) (ε : ℝ) (k : ℕ) :
    smoothTerm e ε k =
      if 2 ≤ k then e k * (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) else 0 := by
  unfold smoothTerm smoothCoeff
  by_cases h : 2 ≤ k
  · simp [h]
  · simp [h]

lemma smoothCoeff_nonneg {ε : ℝ} (hε : 0 < ε) (k : ℕ) : 0 ≤ smoothCoeff ε k := by
  unfold smoothCoeff
  by_cases hk : 2 ≤ k
  · simpa [hk] using rpowDiff_nonneg hε (by omega : 1 ≤ k)
  · simp [hk]

lemma rpow_two_neg_le_one {ε : ℝ} (hε : 0 < ε) : (2 : ℝ) ^ (-ε) ≤ 1 := by
  calc
    (2 : ℝ) ^ (-ε) ≤ (1 : ℝ) ^ (-ε) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num : 0 < (1 : ℝ)) (by norm_num : (1 : ℝ) ≤ (2 : ℝ))
        (by linarith : -ε ≤ 0)
    _ = 1 := Real.one_rpow (-ε)

lemma hasSum_smoothCoeff {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun k : ℕ => smoothCoeff ε k) ((2 : ℝ) ^ (-ε)) := by
  let a : ℕ → ℝ := fun k => (k : ℝ) ^ (-ε)
  have ha0 : ∀ k : ℕ, 0 ≤ a k := by
    intro k
    dsimp [a]
    exact Real.rpow_nonneg (by positivity : 0 ≤ (k : ℝ)) (-ε)
  have hdec : ∀ k : ℕ, 2 ≤ k → a (k + 1) ≤ a k := by
    intro k hk
    have hd := rpowDiff_nonneg hε (by omega : 1 ≤ k)
    dsimp [a]
    exact sub_nonneg.mp hd
  have ht : Tendsto a atTop (nhds 0) := by
    dsimp [a]
    exact (tendsto_rpow_neg_atTop hε).comp tendsto_natCast_atTop_atTop
  have hh := hasSum_of_differences (a := a) (ha0 := ha0) (n := 2) (hdec := hdec) (ht := ht)
  refine hh.congr_fun ?_
  intro k
  by_cases hk : 2 ≤ k
  · simp [smoothCoeff, a, hk]
  · simp [smoothCoeff, hk]

lemma summable_smoothCoeff {ε : ℝ} (hε : 0 < ε) :
    Summable (fun k : ℕ => smoothCoeff ε k) :=
  (hasSum_smoothCoeff hε).summable

lemma eventually_abs_lt_of_tendsto_zero {e : ℕ → ℝ}
    (he : Filter.Tendsto e Filter.atTop (nhds 0)) (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᶠ k in Filter.atTop, |e k| < ρ := by
  rcases (Metric.tendsto_atTop.mp he) ρ hρ with ⟨N, hN⟩
  filter_upwards [Filter.eventually_ge_atTop N] with k hk
  simpa using hN k hk

lemma eventually_abs_le_one_of_tendsto_zero {e : ℕ → ℝ}
    (he : Filter.Tendsto e Filter.atTop (nhds 0)) :
    ∀ᶠ k in Filter.atTop, |e k| ≤ 1 := by
  filter_upwards [eventually_abs_lt_of_tendsto_zero he 1 zero_lt_one] with k hk
  exact le_of_lt hk

lemma summable_smoothTerm {e : ℕ → ℝ} (he : Filter.Tendsto e Filter.atTop (nhds 0))
    {ε : ℝ} (hε : 0 < ε) : Summable (fun k : ℕ => smoothTerm e ε k) := by
  rcases Filter.eventually_atTop.1 (eventually_abs_le_one_of_tendsto_zero he) with ⟨N, hN⟩
  have hc : Summable (fun k : ℕ => smoothCoeff ε k) := summable_smoothCoeff hε
  have hcshift : Summable (fun m : ℕ => smoothCoeff ε (m + N)) :=
    (summable_nat_add_iff (f := fun k : ℕ => smoothCoeff ε k) N).2 hc
  have htail : Summable (fun m : ℕ => smoothTerm e ε (m + N)) := by
    refine Summable.of_norm_bounded (f := fun m : ℕ => smoothTerm e ε (m + N))
      (g := fun m : ℕ => smoothCoeff ε (m + N)) hcshift ?_
    intro m
    have hb : |e (m + N)| ≤ 1 := hN (m + N) (by omega)
    have hc0 : 0 ≤ smoothCoeff ε (m + N) := smoothCoeff_nonneg hε (m + N)
    change ‖e (m + N) * smoothCoeff ε (m + N)‖ ≤ smoothCoeff ε (m + N)
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |e (m + N)| * |smoothCoeff ε (m + N)| ≤ 1 * |smoothCoeff ε (m + N)| := by
        exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      _ = |smoothCoeff ε (m + N)| := by simp
      _ = smoothCoeff ε (m + N) := abs_of_nonneg hc0
  exact (summable_nat_add_iff (f := fun k : ℕ => smoothTerm e ε k) N).1 htail

/-- fixed `k`: the coefficient `smoothCoeff ε k` tends to `0` as `ε → 0⁺` -/
lemma smoothCoeff_tendsto_zero (k : ℕ) :
    Filter.Tendsto (fun ε : ℝ => smoothCoeff ε k)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds 0) := by
  unfold smoothCoeff
  by_cases hk : 2 ≤ k
  · have h1 : Filter.Tendsto (fun ε : ℝ => (k : ℝ) ^ (-ε))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds 1) := by
      have hc : ContinuousAt (fun a : ℝ => (k : ℝ) ^ a) 0 := Real.continuousAt_const_rpow (by positivity)
      have hneg : Filter.Tendsto (fun ε : ℝ => -ε)
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (0 : ℝ)) := by
        simpa using ((continuous_neg : Continuous fun ε : ℝ => -ε).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
      have ht : Filter.Tendsto (fun ε : ℝ => (k : ℝ) ^ (-ε))
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds ((k : ℝ) ^ (0 : ℝ))) :=
        hc.tendsto.comp hneg
      simpa using ht
    have h2 : Filter.Tendsto (fun ε : ℝ => (((k + 1 : ℕ) : ℝ) ^ (-ε)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds 1) := by
      have hc : ContinuousAt (fun a : ℝ => (((k + 1 : ℕ) : ℝ) ^ a)) 0 :=
        Real.continuousAt_const_rpow (by positivity)
      have hneg : Filter.Tendsto (fun ε : ℝ => -ε)
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (0 : ℝ)) := by
        simpa using ((continuous_neg : Continuous fun ε : ℝ => -ε).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
      have ht : Filter.Tendsto (fun ε : ℝ => (((k + 1 : ℕ) : ℝ) ^ (-ε)))
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (((k + 1 : ℕ) : ℝ) ^ (0 : ℝ))) :=
        hc.tendsto.comp hneg
      simpa using ht
    have hz : (fun ε : ℝ => (if 2 ≤ k then (k : ℝ) ^ (-ε) - (((k + 1 : ℕ) : ℝ) ^ (-ε)) else 0)) =
        fun ε : ℝ => (k : ℝ) ^ (-ε) - (((k + 1 : ℕ) : ℝ) ^ (-ε)) := by
      funext ε
      simp [hk]
    rw [hz]
    simpa using (h1.sub h2)
  · have hz : (fun ε : ℝ => (if 2 ≤ k then (k : ℝ) ^ (-ε) - (((k + 1 : ℕ) : ℝ) ^ (-ε)) else 0)) =
      fun _ : ℝ => 0 := by
      funext ε
      simp [hk]
    rw [hz]
    exact tendsto_const_nhds

/-- finite head: `∑_{k < L} |e k| * smoothCoeff ε k → 0` as `ε → 0⁺` -/
lemma finiteHead_tendsto_zero (e : ℕ → ℝ) (L : ℕ) :
    Filter.Tendsto (fun ε : ℝ => ∑ k ∈ Finset.range L, |e k| * smoothCoeff ε k)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds 0) := by
  let f : ℕ → ℝ → ℝ := fun k ε => |e k| * smoothCoeff ε k
  have hf : ∀ k : ℕ, k ∈ Finset.range L →
      Filter.Tendsto (f k) (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds 0) := by
    intro k hk
    dsimp [f]
    simpa using (smoothCoeff_tendsto_zero k).const_mul (|e k|)
  simpa [f] using
    tendsto_finsetSum (s := Finset.range L) (f := f) (a := fun _ : ℕ => 0) hf

/-- split a tsum over `ℕ` into the finite head and the shifted tail -/
lemma tsum_eq_sum_add_shift {f : ℕ → ℝ} (hf : Summable f) (L : ℕ) :
    (∑' k : ℕ, f k) = (∑ k ∈ Finset.range L, f k) + ∑' m : ℕ, f (m + L) := by
  let g : ℝ := (∑' k : ℕ, f k) - (∑ k ∈ Finset.range L, f k)
  have hB : HasSum f (g + (∑ k ∈ Finset.range L, f k)) := by
    dsimp [g]
    rw [show (∑' k : ℕ, f k - ∑ x ∈ Finset.range L, f x) + (∑ x ∈ Finset.range L, f x) =
        (∑' k : ℕ, f k) by ring]
    exact hf.hasSum
  have hshift : HasSum (fun m : ℕ => f (m + L)) g :=
    (hasSum_nat_add_iff (f := f) L).2 hB
  calc
    (∑' k : ℕ, f k) = (∑ k ∈ Finset.range L, f k) + g := by dsimp [g]; ring
    _ = (∑ k ∈ Finset.range L, f k) + ∑' m : ℕ, f (m + L) := by rw [← hshift.tsum_eq]

/-- the tail (shift) of a nonnegative summable series is at most the whole sum -/
lemma tsum_shift_le_tsum {f : ℕ → ℝ} (hf0 : ∀ k : ℕ, 0 ≤ f k) (hf : Summable f) (L : ℕ) :
    (∑' m : ℕ, f (m + L)) ≤ (∑' k : ℕ, f k) := by
  have h := tsum_eq_sum_add_shift hf L
  calc
    (∑' m : ℕ, f (m + L)) = (∑' k : ℕ, f k) - (∑ k ∈ Finset.range L, f k) := by
      rw [h]
      ring
    _ ≤ ∑' k : ℕ, f k := sub_le_self _ (Finset.sum_nonneg (by intro k hk; exact hf0 k))

/-- absolute value of a tsum is at most the tsum of absolute values -/
lemma abs_tsum_le_tsum_abs {f : ℕ → ℝ} (hf : Summable f) :
    |∑' k : ℕ, f k| ≤ ∑' k : ℕ, |f k| := by
  have hfabs : Summable (fun k : ℕ => ‖f k‖) := summable_norm_iff.mpr hf
  calc
    |∑' k : ℕ, f k| = ‖∑' k : ℕ, f k‖ := by rw [← Real.norm_eq_abs]
    _ ≤ ∑' k : ℕ, ‖f k‖ := norm_tsum_le_tsum_norm hfabs
    _ = ∑' k : ℕ, |f k| := by
      apply tsum_congr
      intro k
      exact Real.norm_eq_abs (f k)

/-- tail mass (from `L` on) is at most `1` when `0 < ε` -/
lemma tailCoeff_le_one {ε : ℝ} (hε : 0 < ε) (L : ℕ) :
    (∑' m : ℕ, smoothCoeff ε (m + L)) ≤ 1 := by
  have hcs : Summable (fun k : ℕ => smoothCoeff ε k) := summable_smoothCoeff hε
  have hle : (∑' m : ℕ, smoothCoeff ε (m + L)) ≤ ∑' k : ℕ, smoothCoeff ε k :=
    tsum_shift_le_tsum (fun k => smoothCoeff_nonneg hε k) hcs L
  have htotal : (∑' k : ℕ, smoothCoeff ε k) ≤ 1 := by
    have hh := hasSum_smoothCoeff hε
    rw [hh.tsum_eq]
    exact rpow_two_neg_le_one hε
  exact le_trans hle htotal

/-- the fundamental estimate: if `|e k| ≤ δ/2` for all `k ≥ L`, then the whole
smoothed sum is bounded by the finite head (over `k < L`) plus `δ/2`. -/
lemma smoothSum_abs_le_of_tail_small {e : ℕ → ℝ} {ε δ : ℝ} {L : ℕ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (hLsmall : ∀ k : ℕ, L ≤ k → |e k| ≤ δ / 2)
    (hsumm : Summable (fun k : ℕ => smoothTerm e ε k)) :
    |∑' k : ℕ, smoothTerm e ε k| ≤
      (∑ k ∈ Finset.range L, |e k| * smoothCoeff ε k) + δ / 2 := by
  have hc0 : ∀ k : ℕ, 0 ≤ smoothCoeff ε k := fun k => smoothCoeff_nonneg hε k
  have hcs : Summable (fun k : ℕ => smoothCoeff ε k) := summable_smoothCoeff hε
  have hwabs : Summable (fun k : ℕ => |smoothTerm e ε k|) := by
    have hnorm : Summable (fun k : ℕ => ‖smoothTerm e ε k‖) := summable_norm_iff.mpr hsumm
    exact hnorm.congr (fun k : ℕ => Real.norm_eq_abs (smoothTerm e ε k))
  have hsplit := tsum_eq_sum_add_shift (f := fun k : ℕ => |smoothTerm e ε k|) hwabs L
  have hsumL : (∑ k ∈ Finset.range L, |smoothTerm e ε k|) =
      ∑ k ∈ Finset.range L, |e k| * smoothCoeff ε k := by
    apply Finset.sum_congr rfl
    intro k hk
    unfold smoothTerm
    rw [abs_mul, abs_of_nonneg (smoothCoeff_nonneg hε k)]
  have htaille : (∑' m : ℕ, |smoothTerm e ε (m + L)|) ≤
      ∑' m : ℕ, (δ / 2) * smoothCoeff ε (m + L) := by
    have hpt : ∀ m : ℕ, |smoothTerm e ε (m + L)| ≤ (δ / 2) * smoothCoeff ε (m + L) := by
      intro m
      have hb : |e (m + L)| ≤ δ / 2 := hLsmall (m + L) (by omega)
      unfold smoothTerm
      calc
        |e (m + L) * smoothCoeff ε (m + L)| = |e (m + L)| * |smoothCoeff ε (m + L)| := abs_mul _ _
        _ ≤ (δ / 2) * |smoothCoeff ε (m + L)| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
        _ = (δ / 2) * smoothCoeff ε (m + L) := by rw [abs_of_nonneg (smoothCoeff_nonneg hε (m + L))]
    have hs1 : Summable (fun m : ℕ => |smoothTerm e ε (m + L)|) :=
      (summable_nat_add_iff (f := fun k : ℕ => |smoothTerm e ε k|) L).2 hwabs
    have hs2 : Summable (fun m : ℕ => (δ / 2) * smoothCoeff ε (m + L)) :=
      Summable.mul_left (δ / 2) ((summable_nat_add_iff (f := fun k : ℕ => smoothCoeff ε k) L).2 hcs)
    exact Summable.tsum_le_tsum hpt hs1 hs2
  have hscaled : (∑' m : ℕ, (δ / 2) * smoothCoeff ε (m + L)) =
      (δ / 2) * (∑' m : ℕ, smoothCoeff ε (m + L)) := by
    have hs2 : Summable (fun m : ℕ => smoothCoeff ε (m + L)) :=
      (summable_nat_add_iff (f := fun k : ℕ => smoothCoeff ε k) L).2 hcs
    exact (HasSum.mul_left (δ / 2) hs2.hasSum).tsum_eq
  have htail1 : (δ / 2) * (∑' m : ℕ, smoothCoeff ε (m + L)) ≤ δ / 2 * 1 := by
    exact mul_le_mul_of_nonneg_left (tailCoeff_le_one hε L) (by positivity : 0 ≤ δ / 2)
  calc
    |∑' k : ℕ, smoothTerm e ε k| ≤ ∑' k : ℕ, |smoothTerm e ε k| := abs_tsum_le_tsum_abs hsumm
    _ = (∑ k ∈ Finset.range L, |smoothTerm e ε k|) +
        (∑' m : ℕ, |smoothTerm e ε (m + L)|) := hsplit
    _ = (∑ k ∈ Finset.range L, |e k| * smoothCoeff ε k) +
        (∑' m : ℕ, |smoothTerm e ε (m + L)|) := by rw [hsumL]
    _ ≤ (∑ k ∈ Finset.range L, |e k| * smoothCoeff ε k) +
        (∑' m : ℕ, (δ / 2) * smoothCoeff ε (m + L)) := by
          exact add_le_add_right htaille (∑ k ∈ Finset.range L, |e k| * smoothCoeff ε k)
    _ = (∑ k ∈ Finset.range L, |e k| * smoothCoeff ε k) +
        (δ / 2) * (∑' m : ℕ, smoothCoeff ε (m + L)) := by rw [hscaled]
    _ ≤ (∑ k ∈ Finset.range L, |e k| * smoothCoeff ε k) + δ / 2 * 1 := by
          exact add_le_add_right htail1 (∑ k ∈ Finset.range L, |e k| * smoothCoeff ε k)
    _ = (∑ k ∈ Finset.range L, |e k| * smoothCoeff ε k) + δ / 2 := by ring

/-- if `e k → 0`, the smoothed sum `∑' k, e k * smoothCoeff ε k` tends to `0` as `ε → 0⁺` -/
lemma smoothSum_tendsto_zero_of_tendsto_zero {e : ℕ → ℝ}
    (he : Filter.Tendsto e Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun ε : ℝ => ∑' k : ℕ, smoothTerm e ε k)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hδ2 : 0 < δ / 2 := by positivity
  rcases Filter.eventually_atTop.1 (eventually_abs_lt_of_tendsto_zero he (δ / 2) hδ2) with ⟨L0, hL0⟩
  let L : ℕ := max L0 2
  have hLsmall : ∀ k : ℕ, L ≤ k → |e k| ≤ δ / 2 := by
    intro k hk
    have hk0 : L0 ≤ k := by omega
    exact le_of_lt (hL0 k hk0)
  have hEst : ∀ ε : ℝ, 0 < ε →
      |∑' k : ℕ, smoothTerm e ε k| ≤
        (∑ k ∈ Finset.range L, |e k| * smoothCoeff ε k) + δ / 2 := by
    intro ε hε
    exact smoothSum_abs_le_of_tail_small hε hδ hLsmall (summable_smoothTerm he hε)
  have hpos0 : ∀ᶠ ε in (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))), 0 < ε :=
    Filter.mem_of_superset self_mem_nhdsWithin (fun x hx => hx)
  have hHδ : ∀ᶠ ε in (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))),
      (∑ k ∈ Finset.range L, |e k| * smoothCoeff ε k) < δ / 2 := by
    have h := (Metric.tendsto_nhds.mp (finiteHead_tendsto_zero e L)) (δ / 2) hδ2
    filter_upwards [hpos0, h] with ε hε hdist
    have hnonneg : 0 ≤ ∑ k ∈ Finset.range L, |e k| * smoothCoeff ε k := by
      apply Finset.sum_nonneg
      intro k hk
      exact mul_nonneg (abs_nonneg (e k)) (smoothCoeff_nonneg hε k)
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hdist
  have hfin : ∀ᶠ ε in (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))),
      dist (∑' k : ℕ, smoothTerm e ε k) 0 < δ := by
    filter_upwards [hpos0, hHδ] with ε hε hHsmall
    have hb := hEst ε hε
    have hlt : |∑' k : ℕ, smoothTerm e ε k| < δ := by nlinarith
    simpa [Real.dist_eq] using hlt
  exact hfin

theorem error_smoothSum_tendsto_zero {e : ℕ → ℝ}
    (he : Filter.Tendsto e Filter.atTop (nhds 0)) :
    (∀ ⦃ε : ℝ⦄, 0 < ε → Summable (fun k : ℕ =>
      if 2 ≤ k then e k * (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) else 0)) ∧
    Filter.Tendsto (fun ε : ℝ => (∑' k : ℕ, if 2 ≤ k then
      e k * (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) else 0))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds 0) := by
  constructor
  · intro ε hε
    have hsumm := summable_smoothTerm he hε
    refine hsumm.congr ?_
    intro k
    exact smoothTerm_eq e ε k
  · have hmain := smoothSum_tendsto_zero_of_tendsto_zero he
    refine hmain.congr' ?_
    filter_upwards with ε
    apply tsum_congr
    intro k
    exact smoothTerm_eq e ε k

end

end Commons.NumberTheory.Mertens