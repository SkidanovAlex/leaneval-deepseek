import Mathlib

namespace Work.IonescuWainger

open scoped BigOperators

/-- For `a > 0` and `n : ℕ`, comparing the `(n+1)`-st term of the reciprocal sum with the
integral increment `∫_{a n}^{a (n+1)} dt / (1 + t²) = arctan (a(n+1)) - arctan (a n)`; this is
the elementary "decreasing integrand" estimate behind the lattice-sum bound. -/
private lemma inv_one_add_sq_le_arctan_sub {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (1 + (a * ((n + 1 : ℕ) : ℝ)) ^ 2)⁻¹
      ≤ a⁻¹ * (Real.arctan (a * ((n + 1 : ℕ) : ℝ)) - Real.arctan (a * (n : ℝ))) := by
  have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by rw [hcast]; linarith
  have hcont : Continuous (fun t : ℝ => (1 + (a * t) ^ 2)⁻¹) := by
    apply Continuous.inv₀
    · fun_prop
    · intro t; positivity
  have hkey : (∫ u in (n:ℝ)..((n+1:ℕ):ℝ), (1 + (a * ((n+1:ℕ):ℝ))^2)⁻¹)
      ≤ ∫ u in (n:ℝ)..((n+1:ℕ):ℝ), (1 + (a * u) ^ 2)⁻¹ :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hle intervalIntegrable_const
      (hcont.intervalIntegrable _ _) (fun t ht => by
        have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg n) ht.1
        have hat : a * t ≤ a * ((n + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left ht.2 ha.le
        have hsq : (a * t) ^ 2 ≤ (a * ((n + 1 : ℕ) : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hat 2
        have hpos1 : (0:ℝ) < 1 + (a * t) ^ 2 := by positivity
        have hpos2 : (0:ℝ) < 1 + (a * ((n + 1 : ℕ) : ℝ)) ^ 2 := by positivity
        exact (inv_le_inv₀ hpos2 hpos1).mpr (by linarith))
  rw [intervalIntegral.integral_const] at hkey
  rw [intervalIntegral.integral_comp_mul_left (fun u : ℝ => (1 + u ^ 2)⁻¹) ha.ne'] at hkey
  rw [integral_inv_one_add_sq] at hkey
  simp only [smul_eq_mul] at hkey
  have hone : (((n + 1 : ℕ) : ℝ) - (n : ℝ)) = 1 := by rw [hcast]; ring
  rw [hone, one_mul] at hkey
  exact hkey

/-- Partial sums of the tail of the reciprocal sum are bounded by `a⁻¹ arctan (a N)`; this is
the arctan telescoping that produces the sharp constant `π/(2a)`. -/
private lemma sum_range_le_arctan {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∑ k ∈ Finset.range N, (1 + (a * ((k + 1 : ℕ) : ℝ)) ^ 2)⁻¹
      ≤ a⁻¹ * Real.arctan (a * (N : ℝ)) := by
  calc ∑ k ∈ Finset.range N, (1 + (a * ((k + 1 : ℕ) : ℝ)) ^ 2)⁻¹
      ≤ ∑ k ∈ Finset.range N,
          a⁻¹ * (Real.arctan (a * ((k + 1 : ℕ) : ℝ)) - Real.arctan (a * (k : ℝ))) :=
        Finset.sum_le_sum (fun k _ => inv_one_add_sq_le_arctan_sub ha k)
    _ = a⁻¹ * ∑ k ∈ Finset.range N,
          (Real.arctan (a * ((k + 1 : ℕ) : ℝ)) - Real.arctan (a * (k : ℝ))) := by
        rw [Finset.mul_sum]
    _ = a⁻¹ * (Real.arctan (a * (N : ℝ)) - Real.arctan 0) := by
        rw [Finset.sum_range_sub (fun i : ℕ => Real.arctan (a * (i : ℝ)))]
        norm_num
    _ = a⁻¹ * Real.arctan (a * (N : ℝ)) := by rw [Real.arctan_zero, sub_zero]

/-- Summability of the tail `∑_{k ≥ 1} (1 + (ak)²)⁻¹`, by comparison with `∑ k^{-2}`. -/
private lemma summable_tail {a : ℝ} (ha : 0 < a) :
    Summable (fun k : ℕ => (1 + (a * ((k + 1 : ℕ) : ℝ)) ^ 2)⁻¹) := by
  have hbase : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hshift : Summable (fun n : ℕ => ((((n + 1 : ℕ)) : ℝ) ^ 2)⁻¹) :=
    (summable_nat_add_iff 1).mpr hbase
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (hshift.mul_left ((a ^ 2)⁻¹))
  have h1 : (0:ℝ) < 1 + (a * (((k + 1 : ℕ)) : ℝ)) ^ 2 := by positivity
  have h2 : (0:ℝ) < a ^ 2 * ((((k + 1 : ℕ)) : ℝ)) ^ 2 := by positivity
  have hmain : (1 + (a * (((k + 1 : ℕ)) : ℝ)) ^ 2)⁻¹
      ≤ (a ^ 2 * ((((k + 1 : ℕ)) : ℝ)) ^ 2)⁻¹ := by
    apply (inv_le_inv₀ h1 h2).mpr
    nlinarith [sq_nonneg (a * (((k + 1 : ℕ)) : ℝ))]
  rwa [mul_inv] at hmain

/-- Summability of the full `ℕ`-indexed reciprocal sum. -/
private lemma summable_F {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => (1 + (a * (n : ℝ)) ^ 2)⁻¹) :=
  (summable_nat_add_iff 1).mp (summable_tail ha)

/-- The sharp bound for the tail: `∑_{k ≥ 1} (1 + (ak)²)⁻¹ ≤ π/(2a)`. -/
private lemma tsum_tail_le {a : ℝ} (ha : 0 < a) :
    ∑' k : ℕ, (1 + (a * ((k + 1 : ℕ) : ℝ)) ^ 2)⁻¹ ≤ a⁻¹ * (Real.pi / 2) := by
  have hsum : Summable (fun k : ℕ => (1 + (a * ((k + 1 : ℕ) : ℝ)) ^ 2)⁻¹) := summable_tail ha
  refine le_of_tendsto_of_tendsto' hsum.hasSum.tendsto_sum_nat tendsto_const_nhds (fun N => ?_)
  calc ∑ k ∈ Finset.range N, (1 + (a * ((k + 1 : ℕ) : ℝ)) ^ 2)⁻¹
      ≤ a⁻¹ * Real.arctan (a * (N : ℝ)) := sum_range_le_arctan ha N
    _ ≤ a⁻¹ * (Real.pi / 2) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ha.le)
        exact le_of_lt (Real.arctan_lt_pi_div_two _)

/-- **The reciprocal-sum bound of the `p = ∞` endpoint of Tao's `ortho-apply`(ii)**: for
`ε, Q > 0` the lattice sum `Σ_{m ∈ ℤ} (1 + (εQm)²)⁻¹` is at most `1 + π/(εQ)`, the `m = 0` term
contributing `1` and the tail being controlled by the integral `∫_0^∞ dt/(1+(εQt)²) = π/(2εQ)`.
This is the analytic input of the "weighted orthogonality" step. -/
theorem tsum_inv_one_add_sq_mul_le {ε Q : ℝ} (hε : 0 < ε) (hQ : 0 < Q) :
    ∑' m : ℤ, (1 + (ε * Q * (m : ℝ)) ^ 2)⁻¹ ≤ 1 + Real.pi / (ε * Q) := by
  set a : ℝ := ε * Q with ha
  have hapos : 0 < a := by rw [ha]; positivity
  let f : ℤ → ℝ := fun m => (1 + (a * (m : ℝ)) ^ 2)⁻¹
  change ∑' m : ℤ, f m ≤ 1 + Real.pi / a
  have hcast : ∀ n : ℕ, (((-(↑n + 1) : ℤ)) : ℝ) = -((n : ℝ) + 1) := fun n => by
    push_cast; ring
  have hcast2 : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) = ((n : ℝ) + 1) := fun n => by push_cast; ring
  have hF : Summable (fun n : ℕ => f ↑n) :=
    (summable_F hapos).congr (fun n => by simp [f])
  have hneg : Summable (fun n : ℕ => f (-(↑n + 1))) :=
    (summable_tail hapos).congr (fun n => by simp only [f]; rw [hcast n, hcast2 n]; congr 1; ring)
  have hdecomp : (∑' m : ℤ, f m) = (∑' n : ℕ, f ↑n) + (∑' n : ℕ, f (-(↑n + 1))) :=
    tsum_of_nat_of_neg_add_one hF hneg
  have hA : (∑' n : ℕ, f ↑n) = (∑' n : ℕ, (1 + (a * (n : ℝ)) ^ 2)⁻¹) :=
    tsum_congr (fun n => by simp [f])
  have hB : (∑' n : ℕ, f (-(↑n + 1))) = (∑' n : ℕ, (1 + (a * ((n + 1 : ℕ) : ℝ)) ^ 2)⁻¹) :=
    tsum_congr (fun n => by simp only [f]; rw [hcast n, hcast2 n]; congr 1; ring)
  have hF0 : (1 + (a * ((0 : ℕ) : ℝ)) ^ 2)⁻¹ = 1 := by norm_num
  have hkey2 : (∑' n : ℕ, (1 + (a * (n : ℝ)) ^ 2)⁻¹)
      = 1 + ∑' n : ℕ, (1 + (a * ((n + 1 : ℕ) : ℝ)) ^ 2)⁻¹ := by
    rw [(summable_F hapos).tsum_eq_zero_add, hF0]
  have htail := tsum_tail_le hapos
  have hmul : 2 * (∑' n : ℕ, (1 + (a * ((n + 1 : ℕ) : ℝ)) ^ 2)⁻¹) ≤ Real.pi / a := by
    have hfin : 2 * (a⁻¹ * (Real.pi / 2)) = Real.pi / a := by ring
    linarith [htail]
  rw [hdecomp, hA, hB, hkey2]
  linarith [hmul]

end Work.IonescuWainger
