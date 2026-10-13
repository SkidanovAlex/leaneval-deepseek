import Mathlib
import Submission.Work.WilE2.exists_fin_Icc_cover
import Submission.Work.WilE2.sum_ofReal_grid
import Submission.Work.WilE2.norm_sub_le_grid

/-!
# Uniform flatness of order `q` with `n ≤ q * m` forces a null image

Let `A ⊆ ℝⁿ` be bounded and let `f : ℝⁿ → ℝᵐ` be *uniformly flat of order `q`* on `A`: for every
`ε > 0` there is `δ > 0` such that `‖f y - f x‖ ≤ ε ‖y - x‖ ^ q` whenever `x, y ∈ A` and
`‖y - x‖ ≤ δ`.  If `n ≤ q * m`, then `f '' A` has Lebesgue measure zero.

The proof is a one-scale covering estimate.  Fix `ε` together with its witness `δ`, and put
`d = min δ 1`.  A bounded set in `ℝⁿ` is contained in a sup-norm cube of side `2R`, which is cut
into `Nⁿ` cells of side `2R/N ≤ d` (`exists_fin_Icc_cover`, `norm_sub_le_grid`).  On each cell the
flatness hypothesis bounds the oscillation of `f` by `ε d ^ q`, so the image of the part of `A` in
one cell is contained in a sup-norm ball of radius `ε d ^ q` in `ℝᵐ`, of volume `(2 ε d ^ q) ^ m`
(`Real.volume_pi_closedBall`).  Summing over the `Nⁿ` cells gives

`volume (f '' A) ≤ (2 ε)^m * (N d)^n * d ^ (q m - n) ≤ (2 ε)^m * (2 R + 1)^n`,

using `d ≤ 1` and `n ≤ q * m`.  The right-hand side tends to `0` with `ε → 0`.
-/

set_option autoImplicit false

open MeasureTheory Metric Set

namespace Work.WilE2.RegVals

theorem volume_image_eq_zero_of_uniform_flat {n m q : ℕ} (hm : 0 < m) (hq : n ≤ q * m)
    (f : (Fin n → ℝ) → (Fin m → ℝ)) (A : Set (Fin n → ℝ)) (hA : Bornology.IsBounded A)
    (h : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ A, ∀ y ∈ A, ‖y - x‖ ≤ δ → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ q) :
    MeasureTheory.volume (f '' A) = 0 := by
  classical
  -- `A` lies in a closed sup-norm ball of positive radius `R`.
  obtain ⟨M₀, hM₀⟩ := hA.subset_closedBall (0 : Fin n → ℝ)
  set R : ℝ := |M₀| + 1 with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]
    have := abs_nonneg M₀
    linarith
  have hRsub : A ⊆ Metric.closedBall (0 : Fin n → ℝ) R :=
    hM₀.trans (Metric.closedBall_subset_closedBall (by rw [hRdef]; linarith [le_abs_self M₀]))
  -- The single-scale estimate.
  have hmain : ∀ ε > 0, MeasureTheory.volume (f '' A) ≤
      ENNReal.ofReal ((2 * ε) ^ m * (2 * R + 1) ^ n) := by
    intro ε hε
    obtain ⟨δ, hδpos, hδprop⟩ := h ε hε
    set d : ℝ := min δ 1 with hddef
    have hdpos : 0 < d := lt_min hδpos one_pos
    have hdle1 : d ≤ 1 := min_le_right _ _
    have hdleδ : d ≤ δ := min_le_left _ _
    -- the grid mesh
    set N : ℕ := ⌊2 * R / d⌋₊ + 1 with hNdef
    have hNpos : 0 < N := Nat.succ_pos _
    have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hNr : 2 * R / N ≤ d := by
      have h1 : 2 * R / d < (N : ℝ) := by
        rw [hNdef]; push_cast; exact Nat.lt_floor_add_one (2 * R / d)
      rw [div_lt_iff₀ hdpos] at h1
      rw [div_le_iff₀ hNposR]
      linarith
    have hNd : (N : ℝ) * d ≤ 2 * R + 1 := by
      have h2 : (N : ℝ) ≤ 2 * R / d + 1 := by
        rw [hNdef]; push_cast
        linarith [Nat.floor_le (show (0 : ℝ) ≤ 2 * R / d by positivity)]
      have h3 : (2 * R / d + 1) * d = 2 * R + d := by
        field_simp
        try ring
      have h4 := mul_le_mul_of_nonneg_right h2 hdpos.le
      rw [h3] at h4
      linarith
    -- each coordinate is bounded by `R`
    have hcoord : ∀ x ∈ A, ∀ i, |x i| ≤ R := by
      intro x hxA i
      have h1 : dist x 0 ≤ R := Metric.mem_closedBall.mp (hRsub hxA)
      rw [dist_zero_right] at h1
      calc |x i| = ‖x i‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖x‖ := norm_le_pi_norm x i
        _ ≤ R := h1
    -- the grid cells
    let C : (Fin n → Fin N) → Set (Fin n → ℝ) := fun v =>
      {x | ∀ i, x i ∈ Set.Icc (-R + 2 * R * (v i : ℝ) / N) (-R + 2 * R * ((v i : ℝ) + 1) / N)}
    have hcover : A ⊆ ⋃ v, C v := by
      intro x hxA
      choose v hv using fun i => exists_fin_Icc_cover hRpos hNpos (hcoord x hxA i)
      exact Set.mem_iUnion.mpr ⟨v, fun i => ⟨(hv i).1, (hv i).2⟩⟩
    have hcnn : (0 : ℝ) ≤ (2 * (ε * d ^ q)) ^ m :=
      pow_nonneg (mul_nonneg (by norm_num) (mul_nonneg hε.le (pow_nonneg hdpos.le q))) m
    have hpiece : ∀ v : Fin n → Fin N, MeasureTheory.volume (f '' (A ∩ C v)) ≤
        ENNReal.ofReal ((2 * (ε * d ^ q)) ^ m) := by
      intro v
      by_cases hne : (A ∩ C v).Nonempty
      · obtain ⟨x₀, hx₀⟩ := hne
        have hsub : f '' (A ∩ C v) ⊆ Metric.closedBall (f x₀) (ε * d ^ q) := by
          rintro z ⟨x, hx, rfl⟩
          have hdist : ‖x - x₀‖ ≤ d := by
            have h1 := norm_sub_le_grid hRpos.le hNpos v x₀ x hx₀.2 hx.2
            linarith
          have hdx : ‖x - x₀‖ ≤ δ := le_trans hdist hdleδ
          have hb := hδprop x₀ hx₀.1 x hx.1 hdx
          have h2 : ‖x - x₀‖ ^ q ≤ d ^ q := pow_le_pow_left₀ (norm_nonneg _) hdist q
          rw [Metric.mem_closedBall, dist_eq_norm]
          calc ‖f x - f x₀‖ ≤ ε * ‖x - x₀‖ ^ q := hb
            _ ≤ ε * d ^ q := mul_le_mul_of_nonneg_left h2 hε.le
        calc MeasureTheory.volume (f '' (A ∩ C v))
            ≤ MeasureTheory.volume (Metric.closedBall (f x₀) (ε * d ^ q)) :=
              MeasureTheory.measure_mono hsub
          _ = ENNReal.ofReal ((2 * (ε * d ^ q)) ^ m) := by
              rw [Real.volume_pi_closedBall (f x₀) (mul_nonneg hε.le (pow_nonneg hdpos.le q)),
                Fintype.card_fin]
      · have h0 : f '' (A ∩ C v) = ∅ := by
          rw [Set.image_eq_empty, Set.not_nonempty_iff_eq_empty.mp hne]
        rw [h0, MeasureTheory.measure_empty]
        exact bot_le
    have hsum : MeasureTheory.volume (f '' A) ≤
        ∑ v : Fin n → Fin N, MeasureTheory.volume (f '' (A ∩ C v)) := by
      have h1 : MeasureTheory.volume (f '' A) ≤
          MeasureTheory.volume (⋃ v : Fin n → Fin N, f '' (A ∩ C v)) := by
        apply MeasureTheory.measure_mono
        rintro z ⟨x, hxA, rfl⟩
        obtain ⟨v, hv⟩ := Set.mem_iUnion.mp (hcover hxA)
        exact Set.mem_iUnion.mpr ⟨v, ⟨x, ⟨hxA, hv⟩, rfl⟩⟩
      have h2 : MeasureTheory.volume (⋃ v : Fin n → Fin N, f '' (A ∩ C v)) ≤
          ∑ v : Fin n → Fin N, MeasureTheory.volume (f '' (A ∩ C v)) := by
        have h3 : MeasureTheory.volume
              (⋃ v ∈ (Finset.univ : Finset (Fin n → Fin N)), f '' (A ∩ C v)) ≤
            ∑ v ∈ (Finset.univ : Finset (Fin n → Fin N)),
              MeasureTheory.volume (f '' (A ∩ C v)) :=
          MeasureTheory.measure_biUnion_finset_le (Finset.univ : Finset (Fin n → Fin N))
            (fun v : Fin n → Fin N => f '' (A ∩ C v))
        simpa using h3
      exact le_trans h1 h2
    calc MeasureTheory.volume (f '' A)
        ≤ ∑ v : Fin n → Fin N, MeasureTheory.volume (f '' (A ∩ C v)) := hsum
      _ ≤ ∑ v : Fin n → Fin N, ENNReal.ofReal ((2 * (ε * d ^ q)) ^ m) :=
            Finset.sum_le_sum (fun v _ => hpiece v)
      _ = ENNReal.ofReal ((N : ℝ) ^ n * (2 * (ε * d ^ q)) ^ m) :=
            sum_ofReal_grid (n := n) (N := N) ((2 * (ε * d ^ q)) ^ m) hcnn
      _ ≤ ENNReal.ofReal ((2 * ε) ^ m * (2 * R + 1) ^ n) := by
            apply ENNReal.ofReal_le_ofReal
            have hfac : (2 * (ε * d ^ q)) ^ m = (2 : ℝ) ^ m * ε ^ m * d ^ (q * m) := by
              rw [mul_pow, mul_pow, ← pow_mul]
              ring
            have htwo : (2 : ℝ) ^ m * ε ^ m = (2 * ε) ^ m := (mul_pow 2 ε m).symm
            have hs1 : (N : ℝ) ^ n * d ^ (q * m) ≤ ((N : ℝ) * d) ^ n := by
              rw [mul_pow]
              exact mul_le_mul_of_nonneg_left
                (pow_le_pow_of_le_one hdpos.le hdle1 hq) (pow_nonneg (Nat.cast_nonneg N) n)
            have hs2 : ((N : ℝ) * d) ^ n ≤ (2 * R + 1) ^ n :=
              pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg N) hdpos.le) hNd n
            calc (N : ℝ) ^ n * (2 * (ε * d ^ q)) ^ m
                = (2 * ε) ^ m * ((N : ℝ) ^ n * d ^ (q * m)) := by
                  rw [hfac, htwo]; ring
              _ ≤ (2 * ε) ^ m * (2 * R + 1) ^ n :=
                  mul_le_mul_of_nonneg_left (le_trans hs1 hs2)
                    (pow_nonneg (by linarith [hε.le] : (0 : ℝ) ≤ 2 * ε) m)
  -- Pass to the limit `ε → 0`.
  have hfin : MeasureTheory.volume (f '' A) ≤ 0 := by
    have hlim : Filter.Tendsto
        (fun k : ℕ => ENNReal.ofReal ((2 * (1 / ((k : ℝ) + 1))) ^ m * (2 * R + 1) ^ n))
        Filter.atTop (nhds 0) := by
      have hbase : Filter.Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1)) ^ m) Filter.atTop
          (nhds 0) := by
        have h1 : Filter.Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1))) Filter.atTop (nhds (0 : ℝ)) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h2 := h1.pow m
        simpa [zero_pow hm.ne'] using h2
      have hfun : (fun k : ℕ => (2 * (1 / ((k : ℝ) + 1))) ^ m * (2 * R + 1) ^ n)
          = fun k : ℕ => ((2 : ℝ) ^ m * (2 * R + 1) ^ n) * (1 / ((k : ℝ) + 1)) ^ m := by
        funext k
        rw [mul_pow]
        ring
      have hc : Filter.Tendsto
          (fun k : ℕ => ((2 : ℝ) ^ m * (2 * R + 1) ^ n) * (1 / ((k : ℝ) + 1)) ^ m)
          Filter.atTop (nhds (((2 : ℝ) ^ m * (2 * R + 1) ^ n) * 0)) :=
        hbase.const_mul _
      have hg : Filter.Tendsto
          (fun k : ℕ => (2 * (1 / ((k : ℝ) + 1))) ^ m * (2 * R + 1) ^ n)
          Filter.atTop (nhds 0) := by
        rw [hfun]
        simpa using hc
      have hcomp := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hg
      simpa [Function.comp_def] using hcomp
    refine ge_of_tendsto hlim (Filter.Eventually.of_forall (fun k => ?_))
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    exact hmain _ hk
  exact le_antisymm hfin bot_le

end Work.WilE2.RegVals
