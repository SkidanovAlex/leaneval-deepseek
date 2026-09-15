import Submission.FUP.GrowthTilde

open MeasureTheory Metric Filter Set
open scoped Real BigOperators Topology ContDiff

set_option autoImplicit false
set_option maxHeartbeats 3200000
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# The ray tails of the modified weight

The (positively oriented) **ray tail** of a weight `f : ℝᵈ → ℝ` at radius `R` in the direction
`v` is

  `rayTail f R v = ∫_{r > R} |f (r • v)| (1 + r²)⁻¹ dr`.

These are the quantities that control §4's passage to the limiting weight `ω̃ = ∑_k ω̃_k`: they
decay as `R → ∞`, uniformly in the direction `v`, *because the pieces `ω̃_k` have summable
`ℓ¹` mass* `∑_k |q_k| < ∞`.  The quantitative statement is

  `∑_k rayTail (ω̃_k) R v ≤ ∑_{k ≥ K(R)} |q_k|`  whenever `2^K ≤ R`,

which is the uniform (in `R` and `v`) decay replacing the false "uniform growth bound ⇒ uniform
convergence" statement of `Eomega_seq_statement` (see `ROADMAP.md`, Session 19).
-/

/-- The ray tail of `f` at radius `R` in the direction `v`. -/
noncomputable def rayTail (f : ℝᵈ → ℝ) (R : ℝ) (v : ℝᵈ) : ℝ :=
  ∫ r in Set.Ioi R, |f (r • v)| * (1 + r ^ 2)⁻¹

/-- The integrand `r ↦ |f (r v)| (1 + r²)⁻¹` is integrable when `f` is continuous with compact
support and `v ≠ 0`. -/
lemma integrable_rayIntegrand {f : ℝᵈ → ℝ} {v : ℝᵈ}
    (hcont : Continuous fun r : ℝ => f (r • v))
    (hcs : HasCompactSupport fun r : ℝ => f (r • v)) :
    Integrable (fun r : ℝ => |f (r • v)| * (1 + r ^ 2)⁻¹) := by
  have hden : Continuous fun r : ℝ => (1 : ℝ) + r ^ 2 := by fun_prop
  have hcont' : Continuous fun r : ℝ => |f (r • v)| * (1 + r ^ 2)⁻¹ :=
    hcont.abs.mul (hden.inv₀ (fun r => by positivity))
  have hcs' : HasCompactSupport fun r : ℝ => |f (r • v)| * (1 + r ^ 2)⁻¹ :=
    hcs.abs.mul_right (f' := fun r : ℝ => (1 + r ^ 2)⁻¹)
  exact hcont'.integrable_of_hasCompactSupport hcs'

/-- **The ray tail of a single piece.**  For `k ≥ 2` the tail integral of `|ω̃_k|` against the
weight `(1+r²)⁻¹` is at most the spherical projection `|q_k|`, uniformly in the direction `v` and
in `R ≥ 0`. -/
theorem rayTail_omegaTildePiece_le (k : ℕ) (hk2 : 2 ≤ k) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwk : ∀ x : ℝᵈ, omegaTildePiece (d := d) k w x ≤ 0) (v : ℝᵈ) (hv : ‖v‖ = 1) {R : ℝ}
    (hR : 0 ≤ R) :
    rayTail (omegaTildePiece (d := d) k w) R v ≤ |qk k w| := by
  have hk1 : 1 ≤ k := by omega
  have hline : Continuous fun r : ℝ => omegaTildePiece (d := d) k w (r • v) :=
    (contDiff_omegaTildePiece k hw hk1).continuous.comp (by fun_prop)
  have hcs : HasCompactSupport fun r : ℝ => omegaTildePiece (d := d) k w (r • v) :=
    hasCompactSupport_omegaTildePiece_ray k w v hv
  have hfint : Integrable fun r : ℝ =>
      |omegaTildePiece (d := d) k w (r • v)| * (1 + r ^ 2)⁻¹ :=
    integrable_rayIntegrand hline hcs
  have hdiv : Integrable (fun t : ℝ => omegaTildePiece (d := d) k w (t • v) / t ^ 2) :=
    Commons.Analysis.Calculus.integrable_div_sq_of_continuous_hasCompactSupport hline hcs
      (fun t ht => omegaTildePiece_ray_eq_zero_small k hk2 w v hv ht)
  have hdiv' : Integrable (fun t : ℝ => |omegaTildePiece (d := d) k w (t • v)| / t ^ 2) := by
    refine hdiv.abs.congr ?_
    filter_upwards with t
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 2)]
  have hae : ∀ᵐ r : ℝ ∂volume, r ≠ 0 := by
    rw [MeasureTheory.ae_iff]; simp
  have hstep1 : (∫ r in Set.Ioi R,
        |omegaTildePiece (d := d) k w (r • v)| * (1 + r ^ 2)⁻¹)
      ≤ ∫ r in Set.Ioi 0,
        |omegaTildePiece (d := d) k w (r • v)| * (1 + r ^ 2)⁻¹ :=
    setIntegral_mono_set hfint.integrableOn
      (Filter.Eventually.of_forall fun r => by positivity)
      (Filter.Eventually.of_forall fun r hr => lt_of_le_of_lt hR hr)
  have hstep2 : (∫ r in Set.Ioi 0,
        |omegaTildePiece (d := d) k w (r • v)| * (1 + r ^ 2)⁻¹)
      ≤ ∫ r in Set.Ioi 0, |omegaTildePiece (d := d) k w (r • v)| / r ^ 2 := by
    refine setIntegral_mono_ae hfint.integrableOn hdiv'.integrableOn ?_
    filter_upwards [hae] with r hr
    have hsq : (0 : ℝ) < r ^ 2 := sq_pos_of_ne_zero hr
    have hinv : (1 + r ^ 2)⁻¹ ≤ (r ^ 2)⁻¹ :=
      inv_anti₀ hsq (by linarith)
    calc |omegaTildePiece (d := d) k w (r • v)| * (1 + r ^ 2)⁻¹
        ≤ |omegaTildePiece (d := d) k w (r • v)| * (r ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
      _ = |omegaTildePiece (d := d) k w (r • v)| / r ^ 2 := by rw [div_eq_mul_inv]
  calc rayTail (omegaTildePiece (d := d) k w) R v
      = (∫ r in Set.Ioi R,
          |omegaTildePiece (d := d) k w (r • v)| * (1 + r ^ 2)⁻¹) := rfl
    _ ≤ _ := hstep1
    _ ≤ _ := hstep2
    _ = |qk k w| := setIntegral_Ioi_abs_omegaTildePiece_div_sq k hk2 hw hwk v hv

/-! ## Vanishing of the index tail -/

/-- Only finitely many modified pieces are non-zero at a given point. -/
lemma exists_omegaTildePiece_eq_zero_of_ge (w : ℝᵈ → ℝ) (x : ℝᵈ) :
    ∃ N : ℕ, ∀ k ≥ N, omegaTildePiece (d := d) k w x = 0 := by
  obtain ⟨n, hn⟩ := exists_pow_gt_norm x
  refine ⟨n + 1, fun k hk => ?_⟩
  refine omegaTildePiece_eq_zero_of_norm_le_pred k (by omega) w ?_
  exact le_trans hn.le (pow_le_pow_right₀ (by norm_num) (by omega))

/-- For a nonpositive modified weight the absolute value of the sum is the sum of the absolute
values. -/
lemma abs_omegaTildeSum_of_nonpos {w : ℝᵈ → ℝ}
    (hwk : ∀ (k : ℕ) (x : ℝᵈ), omegaTildePiece (d := d) k w x ≤ 0) (x : ℝᵈ) :
    (∑' k, |omegaTildePiece (d := d) k w x|) = |omegaTildeSum (d := d) w x| := by
  obtain ⟨N, hN⟩ := exists_omegaTildePiece_eq_zero_of_ge (d := d) w x
  have hsumm : Summable (fun k => omegaTildePiece (d := d) k w x) :=
    summable_of_ne_finset_zero (s := Finset.range N) fun k hk => by
      rw [Finset.mem_range, not_lt] at hk
      exact hN k hk
  have h1 : (∑' k, omegaTildePiece (d := d) k w x)
      = -(∑' k, |omegaTildePiece (d := d) k w x|) := by
    rw [← tsum_neg]
    exact tsum_congr fun k => by rw [abs_of_nonpos (hwk k x)]; ring
  rw [omegaTildeSum, h1, abs_neg,
    abs_of_nonneg (tsum_nonneg fun k => abs_nonneg _)]

/-! ## The tail of the spherical projections -/

/-- The `ℓ¹` tail `∑_{j} |q_{j+K}|` of the spherical projections. -/
noncomputable def qkTail (K : ℕ) (w : ℝᵈ → ℝ) : ℝ :=
  ∑' j : ℕ, |qk (K + j) w|

lemma qkTail_nonneg (K : ℕ) (w : ℝᵈ → ℝ) : 0 ≤ qkTail K w :=
  tsum_nonneg fun j => abs_nonneg _

/-- The tail of the `|q_k|` series tends to zero. -/
theorem qkTail_tendsto_zero (w : ℝᵈ → ℝ) :
    Tendsto (fun K : ℕ => qkTail K w) atTop (𝓝 0) := by
  refine Tendsto.congr' ?_ (tendsto_sum_nat_add fun k : ℕ => |qk k w|)
  filter_upwards with K
  exact tsum_congr fun j => by rw [Nat.add_comm]

/-- The shifted sequence `j ↦ |q_{j+K}|` is summable for `K ≥ 2`. -/
theorem summable_qk_shift (hd : 1 ≤ d) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwnonpos : ∀ x : ℝᵈ, w x ≤ 0) {Creg : ℝ} (hCreg : 0 < Creg)
    (hreg : ∀ x : ℝᵈ, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2))
    {Cgr : ℝ} (hint : IntegrableOn (fun r => Gstar w r / (1 + r ^ 2)) (Set.Ioi 0))
    (hgrle : (∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2)) ≤ Cgr) {K : ℕ} (hK : 2 ≤ K) :
    Summable (fun j : ℕ => |qk (K + j) w|) := by
  refine summable_of_sum_range_le (c := 128 * Cgr) (fun j => abs_nonneg _) fun n => ?_
  have h := Finset.sum_Ico_eq_sum_range (f := fun k => |qk k w|) K (K + n)
  simp only [Nat.add_sub_cancel_left] at h
  rw [← h]
  have hle : Finset.Ico K (K + n) ⊆ Finset.Icc 2 (K + n) := by
    intro k hk
    simp only [Finset.mem_Ico, Finset.mem_Icc] at hk ⊢
    exact ⟨by omega, by omega⟩
  have h2 := Finset.sum_le_sum_of_subset_of_nonneg hle (fun k _ _ => abs_nonneg (qk k w))
  have h3 := sum_abs_qk_Icc_le (d := d) hd (K + n) hw hwnonpos hCreg hreg hint hgrle
  linarith

/-- The finite sums of `|q_k|` over `[K, ...)` are dominated by the tail `qkTail K`. -/
theorem sum_Ico_qk_le_qkTail (hd : 1 ≤ d) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwnonpos : ∀ x : ℝᵈ, w x ≤ 0) {Creg : ℝ} (hCreg : 0 < Creg)
    (hreg : ∀ x : ℝᵈ, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2))
    {Cgr : ℝ} (hint : IntegrableOn (fun r => Gstar w r / (1 + r ^ 2)) (Set.Ioi 0))
    (hgrle : (∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2)) ≤ Cgr)
    {K n : ℕ} (hK : 2 ≤ K) :
    (∑ k ∈ Finset.Ico K n, |qk k w|) ≤ qkTail K w := by
  rw [Finset.sum_Ico_eq_sum_range (fun k => |qk k w|) K n]
  exact Summable.sum_le_tsum (Finset.range (n - K)) (fun j _ => abs_nonneg _)
    (summable_qk_shift (d := d) hd hw hwnonpos hCreg hreg hint hgrle hK)

/-- The ray tail is nonnegative. -/
lemma rayTail_nonneg (f : ℝᵈ → ℝ) (R : ℝ) (v : ℝᵈ) : 0 ≤ rayTail f R v :=
  setIntegral_nonneg measurableSet_Ioi fun r _ => mul_nonneg (abs_nonneg _) (by positivity)

/-- The ray tail of a piece vanishes once `R` is above its support. -/
lemma rayTail_omegaTildePiece_eq_zero (k : ℕ) {w : ℝᵈ → ℝ} {v : ℝᵈ} (hv : ‖v‖ = 1) {R : ℝ}
    (hR : (2 : ℝ) ^ (k + 1) ≤ R) :
    rayTail (omegaTildePiece (d := d) k w) R v = 0 := by
  rw [rayTail]
  have hz : (∫ r in Set.Ioi R, |omegaTildePiece (d := d) k w (r • v)| * (1 + r ^ 2)⁻¹)
      = ∫ r in Set.Ioi R, (0 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hRpos : 0 < r := lt_trans (lt_of_lt_of_le (by positivity : (0 : ℝ) < (2 : ℝ) ^ (k + 1)) hR) hr
    have hnorm : (2 : ℝ) ^ (k + 1) ≤ ‖r • v‖ := by
      rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos hRpos]
      exact le_of_lt (lt_of_le_of_lt hR hr)
    rw [omegaTildePiece_eq_zero_of_norm_ge k w hnorm, abs_zero, zero_mul]
  rw [hz]; simp

/-- Sums of ray tails of the pieces are dominated by the `q_k` tail. -/
theorem sum_range_rayTail_le (hd : 1 ≤ d) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwnonpos : ∀ x : ℝᵈ, w x ≤ 0)
    (hwk : ∀ (k : ℕ) (x : ℝᵈ), omegaTildePiece (d := d) k w x ≤ 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hreg : ∀ x : ℝᵈ, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2))
    {Cgr : ℝ} (hint : IntegrableOn (fun r => Gstar w r / (1 + r ^ 2)) (Set.Ioi 0))
    (hgrle : (∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2)) ≤ Cgr)
    (v : ℝᵈ) (hv : ‖v‖ = 1) {R : ℝ} (hR : 4 ≤ R) {K : ℕ} (hK : 2 ≤ K)
    (hRK : (2 : ℝ) ^ K ≤ R) (n : ℕ) :
    (∑ k ∈ Finset.range n, rayTail (omegaTildePiece (d := d) k w) R v) ≤ qkTail K w := by
  classical
  have hfilter : (Finset.range n).filter (fun k => K ≤ k) = Finset.Ico K n := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  have hstep1 : (∑ k ∈ Finset.range n, rayTail (omegaTildePiece (d := d) k w) R v)
      = ∑ k ∈ (Finset.range n).filter (fun k => K ≤ k),
          rayTail (omegaTildePiece (d := d) k w) R v := by
    rw [Finset.sum_subset (Finset.filter_subset _ _)]
    intro k hk hk'
    rw [Finset.mem_filter, not_and] at hk'
    have hklt : k < K := by
      by_contra h
      exact hk' hk (le_of_not_gt h)
    refine rayTail_omegaTildePiece_eq_zero k hv ?_
    exact le_trans (pow_le_pow_right₀ (by norm_num) (by omega)) hRK
  rw [hstep1]
  have hbound : (∑ k ∈ (Finset.range n).filter (fun k => K ≤ k),
        rayTail (omegaTildePiece (d := d) k w) R v)
      ≤ ∑ k ∈ (Finset.range n).filter (fun k => K ≤ k), |qk k w| :=
    Finset.sum_le_sum fun k hk => by
      have hkK : K ≤ k := (Finset.mem_filter.mp hk).2
      exact rayTail_omegaTildePiece_le k (by omega) hw (fun x => hwk k x) v hv (by linarith)
  have htail : (∑ k ∈ (Finset.range n).filter (fun k => K ≤ k), |qk k w|) ≤ qkTail K w := by
    rw [hfilter]
    exact sum_Ico_qk_le_qkTail hd hw hwnonpos hCreg hreg hint hgrle hK
  exact le_trans hbound htail

/-- **The ray tail of a truncation.** -/
theorem rayTail_truncSum_le (hd : 1 ≤ d) (n : ℕ) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwnonpos : ∀ x : ℝᵈ, w x ≤ 0) (hwzero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → w x = 0)
    (hwk : ∀ (k : ℕ) (x : ℝᵈ), omegaTildePiece (d := d) k w x ≤ 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hreg : ∀ x : ℝᵈ, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2))
    {Cgr : ℝ} (hint : IntegrableOn (fun r => Gstar w r / (1 + r ^ 2)) (Set.Ioi 0))
    (hgrle : (∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2)) ≤ Cgr)
    (v : ℝᵈ) (hv : ‖v‖ = 1) {R : ℝ} (hR : 4 ≤ R) {K : ℕ} (hK : 2 ≤ K)
    (hRK : (2 : ℝ) ^ K ≤ R) :
    rayTail (truncSum (d := d) n w) R v ≤ qkTail K w := by
  have hpt : ∀ x : ℝᵈ, |truncSum (d := d) n w x|
      = ∑ k ∈ Finset.range n, |omegaTildePiece (d := d) k w x| := by
    intro x
    rw [truncSum_apply]
    have h1 : (∑ k ∈ Finset.range n, omegaTildePiece (d := d) k w x) ≤ 0 :=
      Finset.sum_nonpos fun k _ => hwk k x
    rw [abs_of_nonpos h1, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [abs_of_nonpos (hwk k x)]
  have hint_k : ∀ k : ℕ, IntegrableOn
      (fun r : ℝ => |omegaTildePiece (d := d) k w (r • v)| * (1 + r ^ 2)⁻¹) (Set.Ioi R) := by
    intro k
    rcases Nat.eq_zero_or_pos k with h0 | h1
    · subst h0
      have hz : (fun r : ℝ => |omegaTildePiece (d := d) 0 w (r • v)| * (1 + r ^ 2)⁻¹)
          = fun _ => (0 : ℝ) := by
        funext r
        simp only [omegaTildePiece_zero_eq_zero w hwzero, Pi.zero_apply, abs_zero, zero_mul]
      rw [hz]
      exact integrableOn_zero
    · exact (integrable_rayIntegrand ((contDiff_omegaTildePiece k hw h1).continuous.comp
        (by fun_prop)) (hasCompactSupport_omegaTildePiece_ray k w v hv)).integrableOn
  have hInt : (∫ r in Set.Ioi R, |truncSum (d := d) n w (r • v)| * (1 + r ^ 2)⁻¹)
      = ∑ k ∈ Finset.range n, rayTail (omegaTildePiece (d := d) k w) R v := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun r _ => by rw [hpt, Finset.sum_mul])]
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun k _ => rfl
    · intro k _
      exact hint_k k
  rw [rayTail, hInt]
  exact sum_range_rayTail_le hd hw hwnonpos hwk hCreg hreg hint hgrle v hv hR hK hRK n

/-- The ray tails of the pieces form a summable family. -/
theorem summable_rayTail (hd : 1 ≤ d) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwnonpos : ∀ x : ℝᵈ, w x ≤ 0)
    (hwk : ∀ (k : ℕ) (x : ℝᵈ), omegaTildePiece (d := d) k w x ≤ 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hreg : ∀ x : ℝᵈ, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2))
    {Cgr : ℝ} (hint : IntegrableOn (fun r => Gstar w r / (1 + r ^ 2)) (Set.Ioi 0))
    (hgrle : (∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2)) ≤ Cgr)
    (v : ℝᵈ) (hv : ‖v‖ = 1) {R : ℝ} (hR : 4 ≤ R) {K : ℕ} (hK : 2 ≤ K)
    (hRK : (2 : ℝ) ^ K ≤ R) :
    Summable (fun k : ℕ => rayTail (omegaTildePiece (d := d) k w) R v) :=
  summable_of_sum_range_le (fun k => rayTail_nonneg _ _ _)
    (fun n => sum_range_rayTail_le hd hw hwnonpos hwk hCreg hreg hint hgrle v hv hR hK hRK n)

/-- **The ray tail of the modified weight.** -/
theorem rayTail_omegaTildeSum_le (hd : 1 ≤ d) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwnonpos : ∀ x : ℝᵈ, w x ≤ 0) (hwzero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → w x = 0)
    (hwk : ∀ (k : ℕ) (x : ℝᵈ), omegaTildePiece (d := d) k w x ≤ 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hreg : ∀ x : ℝᵈ, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2))
    {Cgr : ℝ} (hint : IntegrableOn (fun r => Gstar w r / (1 + r ^ 2)) (Set.Ioi 0))
    (hgrle : (∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2)) ≤ Cgr)
    (v : ℝᵈ) (hv : ‖v‖ = 1) {R : ℝ} (hR : 4 ≤ R) {K : ℕ} (hK : 2 ≤ K)
    (hRK : (2 : ℝ) ^ K ≤ R) :
    rayTail (omegaTildeSum (d := d) w) R v ≤ qkTail K w := by
  have hsumm := summable_rayTail hd hw hwnonpos hwk hCreg hreg hint hgrle v hv hR hK hRK
  have htsum_le : (∑' k, rayTail (omegaTildePiece (d := d) k w) R v) ≤ qkTail K w :=
    le_of_tendsto_of_tendsto' hsumm.hasSum.tendsto_sum_nat tendsto_const_nhds
      fun n => sum_range_rayTail_le hd hw hwnonpos hwk hCreg hreg hint hgrle v hv hR hK hRK n
  have hterm : ∀ k : ℕ, Integrable
      (fun r : ℝ => |omegaTildePiece (d := d) k w (r • v)| * (1 + r ^ 2)⁻¹)
      (volume.restrict (Set.Ioi R)) := by
    intro k
    rcases Nat.eq_zero_or_pos k with h0 | h1
    · subst h0
      have hz : (fun r : ℝ => |omegaTildePiece (d := d) 0 w (r • v)| * (1 + r ^ 2)⁻¹)
          = fun _ => (0 : ℝ) := by
        funext r
        simp only [omegaTildePiece_zero_eq_zero w hwzero, abs_zero, zero_mul]
      rw [hz]
      exact integrableOn_zero
    · exact (integrable_rayIntegrand ((contDiff_omegaTildePiece k hw h1).continuous.comp
        (by fun_prop)) (hasCompactSupport_omegaTildePiece_ray k w v hv)).integrableOn
  have hnorm : ∀ k : ℕ, (∫ r,
        ‖|omegaTildePiece (d := d) k w (r • v)| * (1 + r ^ 2)⁻¹‖
        ∂(volume.restrict (Set.Ioi R))) = rayTail (omegaTildePiece (d := d) k w) R v := by
    intro k
    rw [rayTail]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (by positivity))]
  have hsummF : Summable (fun k : ℕ => ∫ r,
      ‖|omegaTildePiece (d := d) k w (r • v)| * (1 + r ^ 2)⁻¹‖
      ∂(volume.restrict (Set.Ioi R))) := by
    simpa only [hnorm] using hsumm
  have hhas := hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Set.Ioi R))
    hterm hsummF
  have h1 : (∑' k, rayTail (omegaTildePiece (d := d) k w) R v)
      = ∫ r in Set.Ioi R, ∑' k,
          |omegaTildePiece (d := d) k w (r • v)| * (1 + r ^ 2)⁻¹ := by
    simp only [rayTail]
    exact hhas.tsum_eq
  have hInt_eq : (∫ r in Set.Ioi R, |omegaTildeSum (d := d) w (r • v)| * (1 + r ^ 2)⁻¹)
      = ∑' k, rayTail (omegaTildePiece (d := d) k w) R v := by
    rw [h1]
    exact setIntegral_congr_fun measurableSet_Ioi fun r _ => by
      rw [tsum_mul_right, ← abs_omegaTildeSum_of_nonpos hwk (r • v)]
  rw [rayTail, hInt_eq]
  exact htsum_le

end Submission.FUP