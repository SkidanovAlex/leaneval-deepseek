import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

set_option autoImplicit false
/-! ## Elementary algebra of the weight -/

theorem w_sq_eq (z : ℝ) : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
  have h1 : ((1 + z) ^ 2) ^ 2 = (1 + z) ^ 4 := by rw [← pow_mul]
  have h2 : (z ^ 2) ^ 2 = z ^ 4 := by rw [← pow_mul]
  rw [Work.Spaces.w, div_pow, h1, h2]

theorem one_le_w_sq {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 := by
  rw [w_sq_eq, le_div_iff₀ (by positivity)]
  simpa using pow_le_pow_left₀ (le_of_lt hz) (by linarith : z ≤ 1 + z) 4

theorem one_div_zpow_four_le_w_sq {z : ℝ} (hz : 0 < z) : 1 / z ^ 4 ≤ (Work.Spaces.w z) ^ 2 := by
  rw [w_sq_eq, div_le_div_iff_of_pos_right (by positivity)]
  exact one_le_pow₀ (by linarith)

theorem z_mul_w_sq_mul (z v : ℝ) (hz : z ≠ 0) :
    z * (v * Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 * (v ^ 2 / z ^ 3) := by
  rw [mul_pow, w_sq_eq]
  field_simp

theorem z_mul_w_sq_mul' (z v : ℝ) :
    z * (v * Work.Spaces.w z) ^ 2 = (Work.Spaces.w z) ^ 2 * (z * v ^ 2) := by ring

/-! ## Vanishing integrals on shrinking sets -/

/-- The intersection of the shrinking intervals `(0, 1/(n+1))` is empty. -/
theorem iInter_Ioo_one_div_succ_eq_empty :
    (⋂ n : ℕ, Set.Ioo (0 : ℝ) (1 / ((n : ℝ) + 1))) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hx0 : 0 < x := (Set.mem_iInter.mp hx 0).1
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx0
  exact absurd (Set.mem_iInter.mp hx n).2 (not_lt.mpr hn.le)

/-- The intersection of the shrinking tails `(n+1, ∞)` is empty. -/
theorem iInter_Ioi_nat_succ_eq_empty :
    (⋂ n : ℕ, Set.Ioi ((n : ℝ) + 1)) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨n, hn⟩ := exists_nat_gt x
  have h1 : x ∈ Set.Ioi ((n : ℝ) + 1) := Set.mem_iInter.mp hx n
  simp only [Set.mem_Ioi] at h1
  linarith

/-- **Vanishing integrals near `0`.**  For `g` integrable on `(0,1)` and `ε > 0` there is
`δ ∈ (0,1)` with `∫_{(0,δ)} |g| ≤ ε`. -/
theorem exists_setIntegral_Ioo_abs_le {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Ioo (0 : ℝ) 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∫ x in Set.Ioo (0 : ℝ) δ, |g x| ≤ ε := by
  have habs : IntegrableOn (fun x => |g x|) (Set.Ioo (0 : ℝ) 1) := Integrable.abs hg
  set s : ℕ → Set ℝ := fun n => Set.Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)) with hs
  have hsm : ∀ n, MeasurableSet (s n) := fun n => measurableSet_Ioo
  have hanti : Antitone s := by
    intro m n hmn x hx
    rw [hs] at hx ⊢
    simp only [Set.mem_Ioo] at hx ⊢
    refine ⟨hx.1, lt_of_lt_of_le hx.2 ?_⟩
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
    exact one_div_le_one_div_of_le (by positivity) hmn'
  have hint : IntegrableOn (fun x => |g x|) (s 0) := by
    rw [hs]; simpa using habs
  have hlim := Antitone.tendsto_setIntegral hsm hanti hint
  have hz : (∫ x in ⋂ n, s n, |g x|) = 0 := by
    rw [iInter_Ioo_one_div_succ_eq_empty]; simp
  rw [hz] at hlim
  obtain ⟨N, hN⟩ : ∃ N, ∀ b ≥ N, dist (∫ x in s b, |g x|) 0 < ε :=
    Filter.eventually_atTop.1 (hlim (Metric.ball_mem_nhds 0 hε))
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have h1 : ∫ x in s N, |g x| < ε := by
    have h := hN N le_rfl
    rwa [Real.dist_eq, sub_zero,
      abs_of_nonneg (integral_nonneg (fun x => abs_nonneg (g x)))] at h
  have hNle : (1 : ℝ) / ((N : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hN2lt : (1 : ℝ) / ((N : ℝ) + 2) < 1 / ((N : ℝ) + 1) := by
    rw [one_div, one_div, inv_lt_inv₀ (by positivity) (by positivity)]
    linarith
  have hsub : Set.Ioo (0 : ℝ) (1 / ((N : ℝ) + 2)) ⊆ s N := by
    intro x hx
    rw [hs]
    simp only [Set.mem_Ioo] at hx ⊢
    exact ⟨hx.1, lt_of_lt_of_le hx.2 hN2lt.le⟩
  have ht : IntegrableOn (fun x => |g x|) (s N) :=
    IntegrableOn.mono_set habs (fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hNle⟩)
  refine ⟨1 / ((N : ℝ) + 2), by positivity, by
      rw [div_lt_one (by positivity)]; linarith, ?_⟩
  exact le_trans (MeasureTheory.setIntegral_mono_set ht
    (Filter.Eventually.of_forall (fun x => abs_nonneg (g x)))
    (Filter.Eventually.of_forall hsub)) h1.le

/-- **Vanishing integrals at `∞`.**  For `g` integrable on `(1,∞)` and `ε > 0` there is
`R > 1` with `∫_{(R,∞)} |g| ≤ ε`. -/
theorem exists_setIntegral_Ioi_abs_le {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Ioi (1 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 1 < R ∧ ∫ x in Set.Ioi R, |g x| ≤ ε := by
  have habs : IntegrableOn (fun x => |g x|) (Set.Ioi (1 : ℝ)) := Integrable.abs hg
  set s : ℕ → Set ℝ := fun n => Set.Ioi ((n : ℝ) + 1) with hs
  have hsm : ∀ n, MeasurableSet (s n) := fun n => measurableSet_Ioi
  have hanti : Antitone s := by
    intro m n hmn x hx
    rw [hs] at hx ⊢
    simp only [Set.mem_Ioi] at hx ⊢
    have h : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
    linarith
  have hint : IntegrableOn (fun x => |g x|) (s 0) := by
    rw [hs]; simpa using habs
  have hlim := Antitone.tendsto_setIntegral hsm hanti hint
  have hz : (∫ x in ⋂ n, s n, |g x|) = 0 := by
    rw [iInter_Ioi_nat_succ_eq_empty]; simp
  rw [hz] at hlim
  obtain ⟨N, hN⟩ : ∃ N, ∀ b ≥ N, dist (∫ x in s b, |g x|) 0 < ε :=
    Filter.eventually_atTop.1 (hlim (Metric.ball_mem_nhds 0 hε))
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have h1 : ∫ x in s N, |g x| < ε := by
    have h := hN N le_rfl
    rwa [Real.dist_eq, sub_zero,
      abs_of_nonneg (integral_nonneg (fun x => abs_nonneg (g x)))] at h
  have hsN : IntegrableOn (fun x => |g x|) (s N) :=
    IntegrableOn.mono_set habs (fun x hx => by
      rw [hs] at hx; simp only [Set.mem_Ioi] at hx ⊢; linarith)
  have hsub : Set.Ioi ((N : ℝ) + 2) ⊆ s N := by
    intro x hx
    rw [hs]
    simp only [Set.mem_Ioi] at hx ⊢
    linarith
  refine ⟨(N : ℝ) + 2, by linarith, ?_⟩
  exact le_trans (MeasureTheory.setIntegral_mono_set hsN
    (Filter.Eventually.of_forall (fun x => abs_nonneg (g x)))
    (Filter.Eventually.of_forall hsub)) h1.le

end Work.FTS.StrongPersist.N6Trans.Hon
