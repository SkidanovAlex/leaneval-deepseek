import Mathlib

/-!
# The range of a `C^1` periodic plane curve has measure zero

`Work.RPB.B1.volume_range_eq_zero`: if `u : ℝ → ℂ` is of class `C^1` and
`2π`-periodic, then `Set.range u` is Lebesgue-null.

The proof is the classical mesh argument.  A `C^1` function is Lipschitz on a
compact interval `[a,b]` (`ContDiffOn.exists_lipschitzOnWith`), so `u '' [a,b]`
is covered by `n+1` closed balls of radius `C (b-a)/(n+1)`
(mesh covering lemma, `Step 1`), whose total area is
`π C^2 (b-a)^2 / (n+1)`, which tends to `0` as `n → ∞` (`Step 2`, `Step 3`).
Finally `ℝ = ⋃_{k ∈ ℤ} [k, k+1]`, so `Set.range u` is a countable union of
images of compact intervals (`Step 4`).
-/

open MeasureTheory Set

namespace Work.RPB.B1

theorem volume_range_eq_zero (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u)
    (hper : ∀ t, u (t + 2 * Real.pi) = u t) :
    MeasureTheory.volume (Set.range u) = 0 := by
  -- ### Step 1: the mesh covering lemma
  have cover : ∀ {C : NNReal} {a b : ℝ}, a < b → LipschitzOnWith C u (Set.Icc a b) →
      ∀ n : ℕ,
      u '' Set.Icc a b ⊆ ⋃ i ∈ Finset.range (n + 1),
        Metric.closedBall (u (a + (i:ℝ) * ((b - a) / ((n:ℝ) + 1))))
          ((C:ℝ) * ((b - a) / ((n:ℝ) + 1))) := by
    intro C a b hab hC n
    rintro z ⟨x, hx, rfl⟩
    set δ : ℝ := (b - a) / ((n:ℝ) + 1) with hδ
    have hδpos : 0 < δ := by
      rw [hδ]; exact div_pos (sub_pos.mpr hab) (by positivity)
    have hn1 : ((n:ℝ) + 1) ≠ 0 := by positivity
    have hδeq : ((n:ℝ) + 1) * δ = b - a := by
      rw [hδ]; exact mul_div_cancel₀ (b - a) hn1
    have hx0 : (0:ℝ) ≤ x - a := by linarith [hx.1]
    have hxub : x - a ≤ ((n:ℝ) + 1) * δ := by linarith [hx.2, hδeq]
    set m : ℕ := ⌊(x - a) / δ⌋₊ with hm
    set i : ℕ := min n m with hi
    have hile : i ≤ n := by rw [hi]; exact min_le_left _ _
    have hmem : i ∈ Finset.range (n+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hile)
    have hDδ_nn : 0 ≤ (x - a) / δ := div_nonneg hx0 hδpos.le
    have hmδ : (m:ℝ) * δ ≤ x - a := by
      have hh := Nat.floor_le hDδ_nn
      rw [← hm] at hh
      exact (le_div_iff₀ hδpos).mp hh
    have hmlt : x - a < (m:ℝ) * δ + δ := by
      have hh := Nat.lt_floor_add_one ((x - a)/δ)
      rw [← hm] at hh
      have hh2 := (div_lt_iff₀ hδpos).mp hh
      rw [add_mul, one_mul] at hh2
      exact hh2
    have habs : |(x - a) - (i:ℝ) * δ| ≤ δ := by
      by_cases hmn : m ≤ n
      · have : i = m := by rw [hi]; exact min_eq_right hmn
        rw [this]
        have h1 : 0 ≤ (x - a) - (m:ℝ)*δ := by linarith
        rw [abs_of_nonneg h1]; linarith
      · have hnm : n < m := Nat.lt_of_not_le hmn
        have : i = n := by rw [hi]; exact min_eq_left hnm.le
        rw [this]
        have h1 : 0 ≤ (x - a) - (n:ℝ)*δ := by
          have hmge : ((n:ℝ) + 1) ≤ (m:ℝ) := by
            have : n + 1 ≤ m := hnm; exact_mod_cast this
          have h2 : ((n:ℝ) + 1) * δ ≤ (m:ℝ) * δ :=
            mul_le_mul_of_nonneg_right hmge hδpos.le
          linarith
        rw [abs_of_nonneg h1]
        have hxub' : x - a ≤ (n:ℝ)*δ + δ := by
          have h : ((n:ℝ)+1)*δ = (n:ℝ)*δ + δ := by rw [add_mul, one_mul]
          linarith [hxub, h]
        linarith
    have hcenter : (a + (i:ℝ)*δ) ∈ Set.Icc a b := by
      constructor
      · have : (0:ℝ) ≤ (i:ℝ)*δ := mul_nonneg (Nat.cast_nonneg i) hδpos.le
        linarith
      · have hiδ : (i:ℝ) * δ ≤ (n:ℝ) * δ :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hile) hδpos.le
        have hnδ : (n:ℝ) * δ ≤ b - a := by
          have hle : (n:ℝ) * δ ≤ ((n:ℝ)+1) * δ := by
            have : (n:ℝ) ≤ (n:ℝ)+1 := by linarith
            exact mul_le_mul_of_nonneg_right this hδpos.le
          linarith [hδeq]
        linarith
    refine Set.mem_iUnion₂.mpr ⟨i, hmem, ?_⟩
    rw [Metric.mem_closedBall]
    have hdist := hC.dist_le_mul x hx (a + (i:ℝ)*δ) hcenter
    rw [Real.dist_eq] at hdist
    have habs' : |x - (a + (i:ℝ)*δ)| ≤ δ := by
      have hx' : x - (a + (i:ℝ)*δ) = (x - a) - (i:ℝ)*δ := by ring
      rw [hx']; exact habs
    calc dist (u x) (u (a + (i:ℝ)*δ)) ≤ (C:ℝ) * |x - (a + (i:ℝ)*δ)| := hdist
      _ ≤ (C:ℝ) * δ := mul_le_mul_of_nonneg_left habs' C.coe_nonneg
  -- ### Step 2: the measure bound coming from a mesh cover
  have bound : ∀ {C : NNReal} {a b : ℝ} {n : ℕ},
      (u '' Set.Icc a b ⊆ ⋃ i ∈ Finset.range (n + 1),
        Metric.closedBall (u (a + (i:ℝ) * ((b - a) / ((n:ℝ) + 1))))
          ((C:ℝ) * ((b - a) / ((n:ℝ) + 1)))) →
      MeasureTheory.volume (u '' Set.Icc a b) ≤
        ENNReal.ofReal ((C:ℝ)^2 * (b - a)^2 * Real.pi / ((n:ℝ) + 1)) := by
    intro C a b n hcover
    have hballle : ∀ z : ℂ, MeasureTheory.volume
        (Metric.closedBall z ((C:ℝ) * ((b - a) / ((n:ℝ) + 1))))
        ≤ ENNReal.ofReal ((((C:ℝ) * ((b - a) / ((n:ℝ) + 1)))^2) * Real.pi) := by
      intro z
      set r : ℝ := (C:ℝ) * ((b - a) / ((n:ℝ) + 1)) with hr
      rw [Complex.volume_closedBall]
      have h2 : (↑NNReal.pi : ENNReal) = ENNReal.ofReal Real.pi := by
        rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
      have h3 : ENNReal.ofReal r ^ 2 ≤ ENNReal.ofReal (r ^ 2) := by
        by_cases hr' : 0 ≤ r
        · rw [ENNReal.ofReal_pow hr' 2]
        · push Not at hr'
          rw [ENNReal.ofReal_eq_zero.mpr hr'.le]
          simp
      calc ENNReal.ofReal r ^ 2 * ↑NNReal.pi
          = ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi := by rw [h2]
        _ ≤ ENNReal.ofReal (r ^ 2) * ENNReal.ofReal Real.pi :=
            mul_le_mul_of_nonneg_right h3 bot_le
        _ = ENNReal.ofReal (r ^ 2 * Real.pi) := (ENNReal.ofReal_mul (sq_nonneg r)).symm
    calc MeasureTheory.volume (u '' Set.Icc a b)
        ≤ MeasureTheory.volume (⋃ i ∈ Finset.range (n + 1),
            Metric.closedBall (u (a + (i:ℝ) * ((b - a) / ((n:ℝ) + 1))))
              ((C:ℝ) * ((b - a) / ((n:ℝ) + 1)))) := MeasureTheory.measure_mono hcover
      _ ≤ ∑ i ∈ Finset.range (n + 1), MeasureTheory.volume
            (Metric.closedBall (u (a + (i:ℝ) * ((b - a) / ((n:ℝ) + 1))))
              ((C:ℝ) * ((b - a) / ((n:ℝ) + 1)))) := measure_biUnion_finset_le _ _
      _ ≤ ∑ i ∈ Finset.range (n + 1), ENNReal.ofReal
            ((((C:ℝ) * ((b - a) / ((n:ℝ) + 1)))^2) * Real.pi) :=
          Finset.sum_le_sum (fun i _ => hballle _)
      _ = ENNReal.ofReal ((C:ℝ)^2 * (b - a)^2 * Real.pi / ((n:ℝ) + 1)) := by
          rw [Finset.sum_const, Finset.card_range]
          simp only [nsmul_eq_mul]
          rw [← ENNReal.ofReal_natCast (n+1)]
          rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ((n+1 : ℕ) : ℝ))]
          congr 1
          push_cast
          field_simp
  -- ### Step 3: the image of an arbitrary compact interval is null
  have h_int : ∀ a b : ℝ, MeasureTheory.volume (u '' Set.Icc a b) = 0 := by
    intro a b
    by_cases hba : b ≤ a
    · have hsub : u '' Set.Icc a b ⊆ {u a} := by
        rintro z ⟨x, hx, rfl⟩
        have : x = a := le_antisymm (le_trans hx.2 hba) hx.1
        simp [this]
      have hzero : MeasureTheory.volume ({u a} : Set ℂ) = 0 := by
        rw [← Metric.closedBall_zero (x := u a)]
        simp
      exact le_antisymm ((MeasureTheory.measure_mono hsub).trans (le_of_eq hzero)) zero_le
    · have hab : a < b := lt_of_not_ge hba
      obtain ⟨C, hC⟩ :=
        (hu.contDiffOn).exists_lipschitzOnWith (by norm_num) (convex_Icc a b) isCompact_Icc
      have hbound : ∀ n : ℕ, MeasureTheory.volume (u '' Set.Icc a b) ≤
          ENNReal.ofReal ((C : ℝ) ^ 2 * (b - a) ^ 2 * Real.pi / ((n : ℝ) + 1)) :=
        fun n => bound (cover hab hC n)
      have hreal : Filter.Tendsto
          (fun n : ℕ => ((C : ℝ) ^ 2 * (b - a) ^ 2 * Real.pi) / ((n : ℝ) + 1))
          Filter.atTop (nhds 0) := by
        simpa [div_eq_mul_inv] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
            ((C : ℝ) ^ 2 * (b - a) ^ 2 * Real.pi)
      have htend : Filter.Tendsto
          (fun n : ℕ => ENNReal.ofReal (((C : ℝ) ^ 2 * (b - a) ^ 2 * Real.pi) / ((n : ℝ) + 1)))
          Filter.atTop (nhds 0) := by
        simpa using ENNReal.tendsto_ofReal hreal
      exact le_antisymm (ge_of_tendsto' htend hbound) zero_le
  -- ### Step 4: `ℝ` is a countable union of compact intervals
  have hrange : Set.range u = ⋃ k : ℤ, u '' Set.Icc (k : ℝ) ((k : ℝ) + 1) := by
    ext q; constructor
    · rintro ⟨t, rfl⟩
      exact Set.mem_iUnion.mpr ⟨⌊t⌋, ⟨t, ⟨Int.floor_le t, (Int.lt_floor_add_one t).le⟩, rfl⟩⟩
    · intro h
      simp only [Set.mem_iUnion, Set.mem_image] at h
      obtain ⟨k, t, ht, hq⟩ := h
      exact ⟨t, hq⟩
  rw [hrange]
  exact measure_iUnion_null (fun k => h_int _ _)

end Work.RPB.B1
