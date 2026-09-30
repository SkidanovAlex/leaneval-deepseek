import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Helpers for the tail weighted `lintegral` bound

Elementary covering / window / series facts used by
`Work.BMF.mrlas.casdiv_tail_lint_bound` (and its two one-sided halves
`Work.BMF.mrlas.casdiv_tail_Ioi_le`, `Work.BMF.mrlas.casdiv_tail_Iio_le`).
-/

open MeasureTheory intervalIntegral Filter
open scoped ENNReal

namespace Work.BMF.mrlas

/-- The right half-line `Ioi T` is covered by the unit windows `Ioc (T+k) (T+k+1)`. -/
lemma iUnion_Ioc_cover_Ioi (T : ℝ) :
    Set.Ioi T ⊆ ⋃ k : ℕ, Set.Ioc (T + k) (T + k + 1) := by
  intro x hx
  rw [Set.mem_iUnion]
  have hy : 0 < x - T := by linarith [Set.mem_Ioi.mp hx]
  have hm1 : 1 ≤ Nat.ceil (x - T) := by
    have := Nat.ceil_pos.mpr hy; omega
  refine ⟨Nat.ceil (x - T) - 1, ?_⟩
  rw [Set.mem_Ioc]
  have h : ((Nat.ceil (x - T) - 1 : ℕ) : ℝ) = (Nat.ceil (x - T) : ℝ) - 1 := by
    simpa using Nat.cast_sub hm1
  constructor
  · rw [h]
    have := Nat.ceil_lt_add_one (le_of_lt hy)
    linarith
  · rw [h]
    have := Nat.le_ceil (x - T)
    linarith

/-- The right half-line `Ici T` is covered by the half-open unit windows `Ico (T+k) (T+k+1)`. -/
lemma iUnion_Ico_cover_Ici (T : ℝ) :
    Set.Ici T ⊆ ⋃ k : ℕ, Set.Ico (T + k) (T + k + 1) := by
  intro y hy
  rw [Set.mem_iUnion]
  have ha : 0 ≤ y - T := by linarith [Set.mem_Ici.mp hy]
  refine ⟨Nat.floor (y - T), ?_⟩
  rw [Set.mem_Ico]
  constructor
  · have := Nat.floor_le ha
    linarith
  · have := Nat.lt_floor_add_one (y - T)
    linarith

/-- The left half-line `Iio (-T)` is covered by the mirrored unit windows
`Ioc (-(T+k+1)) (-(T+k))`, which are of the form `Ioc c (c+1)`. -/
lemma iUnion_Ioc_cover_Iio (T : ℝ) :
    Set.Iio (-T) ⊆ ⋃ k : ℕ, Set.Ioc (-(T + k + 1)) (-(T + k)) := by
  intro x hx
  have hy : -x ∈ Set.Ici T := by
    rw [Set.mem_Ici]; linarith [Set.mem_Iio.mp hx]
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (iUnion_Ico_cover_Ici T hy)
  rw [Set.mem_iUnion]
  refine ⟨k, ?_⟩
  rw [Set.mem_Ico] at hk
  rw [Set.mem_Ioc]
  constructor <;> linarith [hk.1, hk.2]

/-- Pointwise-weighted window bound.  If every unit window of `F` has integral at most `B`,
`a ≥ 1`, `m ≥ 0` and `|τ| ≥ m` on the window `Icc c d`, then the `lintegral` of
`ENNReal.ofReal (F τ / (a²+τ²))` over `Ioc c d` is at most `B / (1+m²)`. -/
lemma window_lintegral_ofReal_le {F : ℝ → ℝ} (hF : Continuous F) (hFnn : ∀ τ, 0 ≤ F τ)
    {B a c d m : ℝ} (ha : 1 ≤ a) (hm : 0 ≤ m) (hcd : c ≤ d)
    (hwin : ∫ τ in c..d, F τ ≤ B) (hden : ∀ τ ∈ Set.Icc c d, m ≤ |τ|) :
    (∫⁻ τ in Set.Ioc c d, ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)))
      ≤ ENNReal.ofReal (B / (1 + m ^ 2)) := by
  set g : ℝ → ℝ := fun τ => F τ / (a^2 + τ^2) with hg
  have hdenpos : ∀ τ, 0 < a^2 + τ^2 := fun τ => by nlinarith [ha, sq_nonneg τ]
  have hgnn : ∀ τ, 0 ≤ g τ := fun τ => div_nonneg (hFnn τ) (le_of_lt (hdenpos τ))
  have hgc : Continuous g := hF.div (by continuity) (fun τ => ne_of_gt (hdenpos τ))
  have hint : IntervalIntegrable g volume c d := hgc.intervalIntegrable c d
  have hfi : Integrable g (volume.restrict (Set.Ioc c d)) := hint.1
  have hconv : (∫⁻ τ in Set.Ioc c d, ENNReal.ofReal (g τ))
      = ENNReal.ofReal (∫ τ in Set.Ioc c d, g τ) :=
    (ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hgnn)).symm
  rw [show (∫⁻ τ in Set.Ioc c d, ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)))
        = ∫⁻ τ in Set.Ioc c d, ENNReal.ofReal (g τ) from rfl, hconv]
  apply ENNReal.ofReal_le_ofReal
  have hIoc : (∫ τ in Set.Ioc c d, g τ) = ∫ τ in c..d, g τ := (integral_of_le hcd).symm
  rw [hIoc]
  have step1 : (∫ τ in c..d, g τ) ≤ ∫ τ in c..d, F τ / (1 + m^2) := by
    apply intervalIntegral.integral_mono_on hcd
    · exact hgc.intervalIntegrable c d
    · exact (hF.div_const _).intervalIntegrable c d
    · intro τ hτ
      rw [hg]
      have hmle : m^2 ≤ τ^2 := by
        have := hden τ hτ
        have h2 : m^2 ≤ |τ|^2 := pow_le_pow_left₀ hm this 2
        simpa [sq_abs] using h2
      have hdenle : 1 + m^2 ≤ a^2 + τ^2 := by nlinarith [ha, hmle]
      exact div_le_div_of_nonneg_left (hFnn τ) (by positivity) hdenle
  calc (∫ τ in c..d, g τ) ≤ ∫ τ in c..d, F τ / (1 + m^2) := step1
    _ = (∫ τ in c..d, F τ) / (1 + m^2) := intervalIntegral.integral_div _ _
    _ ≤ B / (1 + m^2) := div_le_div_of_nonneg_right hwin (by positivity)

/-- `∑_{k≥0} 1/(1+(T+k)²) ≤ 2/T` for `T ≥ 1`, together with summability of the summands.
(Telescoping: `1/(1+u²) ≤ 2/(u(u+1)) = 2(1/u - 1/(u+1))` and the latter series sums to `1/T`.) -/
lemma summable_and_tsum_one_div_one_add_sq_shift_le (T : ℝ) (hT : 1 ≤ T) :
    Summable (fun k : ℕ => (1:ℝ) / (1 + (T + k)^2)) ∧
      ∑' k : ℕ, (1:ℝ) / (1 + (T + k)^2) ≤ 2 / T := by
  have hTpos : 0 < T := by linarith
  set f : ℕ → ℝ := fun k => 1 / (T + k) with hf
  have hfle : ∀ k : ℕ, f (k+1) ≤ f k := by
    intro k
    rw [hf]
    refine one_div_le_one_div_of_le (by positivity) ?_
    push_cast; linarith
  have htel : HasSum (fun k : ℕ => f k - f (k+1)) (f 0) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => sub_nonneg.mpr (hfle k))]
    have hpart : ∀ n : ℕ, (∑ i ∈ Finset.range n, (f i - f (i+1))) = f 0 - f n := by
      intro n
      have h1 : (∑ i ∈ Finset.range n, (f i - f (i+1))) =
          - ∑ i ∈ Finset.range n, (f (i+1) - f i) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [h1, Finset.sum_range_sub]; ring
    have hlim : Tendsto (fun n : ℕ => f n) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => (T + n : ℝ)) atTop atTop :=
        tendsto_atTop_add_const_left atTop T (tendsto_natCast_atTop_atTop (R := ℝ))
      have h2 : Tendsto (fun n : ℕ => (T + n : ℝ)⁻¹) atTop (nhds 0) :=
        h1.inv_tendsto_atTop
      simpa [hf, one_div] using h2
    have hsub : Tendsto (fun n : ℕ => f 0 - f n) atTop (nhds (f 0 - 0)) :=
      (tendsto_const_nhds (x := f 0)).sub hlim
    simpa [hpart] using hsub
  have hsum_tel : Summable (fun k : ℕ => f k - f (k+1)) := htel.summable
  have htsum_tel : ∑' k : ℕ, (f k - f (k+1)) = f 0 := htel.tsum_eq
  have key : ∀ k : ℕ, (1:ℝ)/(1 + (T + k)^2) ≤ 2 * (f k - f (k+1)) := by
    intro k
    have hk : (1:ℝ) ≤ T + k := by linarith
    have hfk : f k - f (k+1) = 1 / ((T + k) * (T + k + 1)) := by
      rw [hf]; push_cast; field_simp; ring
    rw [hfk, mul_one_div]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 1 + (T+k)^2)]
    rw [div_mul_eq_mul_div]
    rw [le_div_iff₀ (by positivity : (0:ℝ) < (T+k)*(T+k+1))]
    nlinarith [hk, sq_nonneg (T + k)]
  have hg_summ : Summable (fun k : ℕ => (1:ℝ)/(1 + (T + k)^2)) :=
    Summable.of_nonneg_of_le (fun k => by positivity) key
      (hsum_tel.mul_left 2)
  refine ⟨hg_summ, ?_⟩
  have h2 : ∑' k : ℕ, 2 * (f k - f (k+1)) = 2 * (f 0) := by
    rw [tsum_mul_left, htsum_tel]
  have hbound : ∑' k : ℕ, (1:ℝ)/(1 + (T + k)^2) ≤ 2 * (f 0) := by
    rw [← h2]
    exact hg_summ.tsum_le_tsum key (hsum_tel.mul_left 2)
  refine le_trans hbound ?_
  rw [hf]; simp only [Nat.cast_zero, add_zero]
  rw [mul_one_div]

end Work.BMF.mrlas
