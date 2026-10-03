import Mathlib
import Submission.Work.A7Hi2.RealScaleDefs
import Submission.Work.KMTAreas.A7.LoDevHormander

/-!
# The discrete Hörmander condition for `linDiffKernR`

`linDiffKernR K σ ρ U ω z = ∑_{n ∈ U} ω_n · (bumpKernR K (σ n) z − bumpKernR K (ρ n) z)` is the
signed sum of the differences of the two dilations of the Schwartz kernel `K` at the comparable
real scales `σ n`, `ρ n`.  This module proves the discrete Hörmander condition for it:

for every Schwartz `K` there is `A > 0` such that for every `2`-lacunary real families `σ`, `ρ` with
`ρ n ≤ σ n ≤ 2 ρ n`, every finite `U`, every sign pattern `ω` and every `y ≠ 0`,
`∫⁻ x in {x : ℤ | 2 |y| ≤ |x|}, ‖linDiffKernR (x - y) - linDiffKernR x‖ ≤ A`.

The route is the same as in the integral-scale analogue `Work.KMTAreas.A7.LoDevHormander`:

* the single-scale oscillation bound `‖bumpKernR K s (z - y) - bumpKernR K s z‖ ≤
  8 A |y| · s / (s + |z|)^3` (`bumpKernR_osc_le`, a mean value theorem bound on the rescaled
  Schwartz function, with `|y| ≤ |z| / 2` making the derivative decay uniform);
* the lacunary cubic summation `∑_{n ∈ U} s n / (s n + Z)^3 ≤ 8 / Z^2` for a real `2`-lacunary `s`
  (`linDiff_lacSumCubic`, obtained from the integral-scale `Work.KMTAreas.A7.loDev_lacSumCubic`
  through the dyadic surrogate `intScaleR`);
* the resulting pointwise bound `‖linDiffKernR (x - y) - linDiffKernR x‖ ≤ 16 C |y| / |x|^2` on
  `2 |y| ≤ |x|`, whose lattice sum is finite (`Commons.Analysis.Hilbert.tsum_int_ofReal_natAbs_inv_sq_le`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.A7Hi2

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## Cast helpers -/

lemma natAbs_cast_real (z : ℤ) : ((z.natAbs : ℝ)) = |(z : ℝ)| := by
  rw [← Int.cast_natCast, ← Int.abs_eq_natAbs, Int.cast_abs]

/-! ## The single-scale oscillation bound for the real dilations -/

lemma bumpKernR_osc_le (K : SchwartzMap ℝ ℂ) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ w : ℝ, ‖deriv (K : ℝ → ℂ) w‖ ≤ A * (1 + |w|) ^ (-3 : ℝ))
    (s : ℝ) (hs : 0 < s) (y z : ℤ) (hyz : 2 * y.natAbs ≤ z.natAbs) :
    ‖bumpKernR K s (z - y) - bumpKernR K s z‖
      ≤ 8 * A * (y.natAbs : ℝ) * (s / (s + ((z.natAbs : ℝ))) ^ 3) := by
  have hY : (0 : ℝ) ≤ (y.natAbs : ℝ) := Nat.cast_nonneg _
  have hZ : (0 : ℝ) ≤ (z.natAbs : ℝ) := Nat.cast_nonneg _
  set u : ℝ := (((z - y : ℤ)) : ℝ) / s with hu
  set v : ℝ := ((z : ℤ) : ℝ) / s with hv
  have hvabs : |v| = (z.natAbs : ℝ) / s := by
    rw [hv, abs_div, abs_of_pos hs, natAbs_cast_real]
  have huvabs : |u - v| = (y.natAbs : ℝ) / s := by
    have hsub : u - v = -(((y : ℤ)) : ℝ) / s := by
      rw [hu, hv, ← sub_div]
      congr 1
      push_cast
      ring
    rw [hsub, abs_div, abs_neg, abs_of_pos hs, natAbs_cast_real]
  have hsmall : |u - v| ≤ |v| / 2 := by
    rw [huvabs, hvabs, div_div]
    rw [div_le_div_iff₀ hs (by positivity : (0 : ℝ) < s * 2)]
    have h3 : (2 * (y.natAbs : ℝ)) ≤ (z.natAbs : ℝ) := by exact_mod_cast hyz
    nlinarith [h3, hs]
  set a : ℝ := min u v with ha
  set b : ℝ := max u v with hb
  have hab : a ≤ b := min_le_max
  have hderiv : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt (K : ℝ → ℂ) (deriv (K : ℝ → ℂ) t) (Set.Icc a b) t :=
    fun t _ => ((K.differentiable.differentiableAt).hasDerivAt).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico a b,
      ‖deriv (K : ℝ → ℂ) t‖ ≤ 8 * A * (1 + |v|) ^ (-3 : ℝ) := by
    intro t ht
    have htI : t ∈ Set.Icc a b := Set.Ico_subset_Icc_self ht
    have h1 : t ≤ max u v := by rw [ha, hb] at htI; exact htI.2
    have h2 : min u v ≤ t := by rw [ha, hb] at htI; exact htI.1
    have htv : |t - v| ≤ |u - v| := by
      have hlow : min u v ≤ v := min_le_right u v
      have hup : v ≤ max u v := le_max_right u v
      have hmaxmin : max u v - min u v = |u - v| := by
        rw [max_sub_min_eq_abs, abs_sub_comm]
      rw [abs_sub_le_iff]
      exact ⟨by linarith, by linarith⟩
    have htge : |v| / 2 ≤ |t| := by
      have h3 : |v| - |t| ≤ |v - t| := abs_sub_abs_le_abs_sub v t
      rw [abs_sub_comm] at h3
      linarith [htv, hsmall]
    have hA1 : (1 / 2) * (1 + |v|) ≤ 1 + |v| / 2 := by linarith [abs_nonneg v]
    have hpos1 : (0 : ℝ) < 1 + |v| / 2 := by positivity
    have h8 : ((1 : ℝ) / 2) ^ (-3 : ℝ) = 8 := by
      rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) from by norm_num, Real.rpow_neg (by norm_num),
        Real.rpow_natCast]
      norm_num
    calc ‖deriv (K : ℝ → ℂ) t‖ ≤ A * (1 + |t|) ^ (-3 : ℝ) := hA t
      _ ≤ A * (8 * (1 + |v|) ^ (-3 : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hA0
          calc (1 + |t|) ^ (-3 : ℝ) ≤ (1 + |v| / 2) ^ (-3 : ℝ) :=
                Real.rpow_le_rpow_of_nonpos hpos1 (by linarith) (by norm_num)
            _ ≤ ((1 / 2) * (1 + |v|)) ^ (-3 : ℝ) :=
                Real.rpow_le_rpow_of_nonpos (by positivity) hA1 (by norm_num)
            _ = 8 * (1 + |v|) ^ (-3 : ℝ) := by
                rw [Real.mul_rpow (by norm_num) (by positivity), h8]
      _ = 8 * A * (1 + |v|) ^ (-3 : ℝ) := by ring
  have hMVT : ‖(K : ℝ → ℂ) b - (K : ℝ → ℂ) a‖
      ≤ (8 * A * (1 + |v|) ^ (-3 : ℝ)) * (b - a) :=
    norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound b (Set.right_mem_Icc.mpr hab)
  have hsub2 : ‖(K : ℝ → ℂ) u - (K : ℝ → ℂ) v‖ = ‖(K : ℝ → ℂ) b - (K : ℝ → ℂ) a‖ := by
    rcases le_total u v with h | h
    · rw [hb, ha, max_eq_right h, min_eq_left h, norm_sub_rev]
    · rw [hb, ha, max_eq_left h, min_eq_right h]
  have hba : b - a = |u - v| := by
    rcases le_total u v with h | h
    · rw [hb, ha, max_eq_right h, min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [hb, ha, max_eq_left h, min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
  have hKuv : ‖(K : ℝ → ℂ) u - (K : ℝ → ℂ) v‖
      ≤ 8 * A * (1 + |v|) ^ (-3 : ℝ) * |u - v| := by
    rw [hsub2, ← hba]
    exact hMVT
  have hKeq : bumpKernR K s (z - y) - bumpKernR K s z
      = ((1 : ℂ) / ((s : ℝ) : ℂ)) * ((K : ℝ → ℂ) u - (K : ℝ → ℂ) v) := by
    unfold bumpKernR
    rw [hu, hv]
    ring
  have hcoef : ‖(1 : ℂ) / ((s : ℝ) : ℂ)‖ = 1 / s := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  calc ‖bumpKernR K s (z - y) - bumpKernR K s z‖
      = (1 / s) * ‖(K : ℝ → ℂ) u - (K : ℝ → ℂ) v‖ := by
        rw [hKeq, norm_mul, hcoef]
    _ ≤ (1 / s) * (8 * A * (1 + |v|) ^ (-3 : ℝ) * |u - v|) :=
        mul_le_mul_of_nonneg_left hKuv (by positivity)
    _ = 8 * A * (y.natAbs : ℝ) * (s / (s + ((z.natAbs : ℝ))) ^ 3) := by
        rw [huvabs, hvabs]
        exact Work.KMTAreas.A7.loDev_algebra s (y.natAbs : ℝ) (z.natAbs : ℝ) (8 * A) hs hZ

/-- The single-scale difference bound for the real dilations of a Schwartz kernel. -/
theorem bumpKernR_singleScaleDiff (K : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ), 0 < s → ∀ (y z : ℤ), 2 * y.natAbs ≤ z.natAbs →
      ‖bumpKernR K s (z - y) - bumpKernR K s z‖
        ≤ C * (y.natAbs : ℝ) * (s / (s + (z.natAbs : ℝ)) ^ 3) := by
  obtain ⟨A, hApos, hA⟩ := Work.KMTAreas.A7.loDev_deriv_decay K
  exact ⟨8 * A, by positivity,
    fun s hs y z hyz => bumpKernR_osc_le K hApos.le hA s hs y z hyz⟩

/-! ## The lacunary cubic summation for real scales -/

/-- For a real `2`-lacunary family `s` and `Z > 0`, `∑_{n ∈ U} s n / (s n + Z)^3 ≤ 8 / Z^2`.
This is the integral-scale `Work.KMTAreas.A7.loDev_lacSumCubic` transported along the dyadic
surrogate `intScaleR`, which satisfies `intScaleR (s n) ≤ s n < 2 intScaleR (s n)`. -/
lemma linDiff_lacSumCubic (s : ℕ → ℝ) (hs1 : ∀ n, 1 ≤ s n) (hs2 : ∀ n, 2 * s n ≤ s (n + 1))
    (U : Finset ℕ) {Z : ℝ} (hZ : 0 < Z) :
    ∑ n ∈ U, s n / (s n + Z) ^ 3 ≤ 8 / Z ^ 2 := by
  have hbase : ∑ n ∈ U, (((intScaleR (s n) : ℕ)) : ℝ)
        / ((((intScaleR (s n) : ℕ)) : ℝ) + Z) ^ 3 ≤ 4 / Z ^ 2 :=
    Work.KMTAreas.A7.loDev_lacSumCubic (fun n => intScaleR (s n))
      (fun n => intScaleR_lacunary hs1 hs2 n) U hZ
  have hpt : ∀ n ∈ U, s n / (s n + Z) ^ 3
      ≤ 2 * ((((intScaleR (s n) : ℕ)) : ℝ)
          / ((((intScaleR (s n) : ℕ)) : ℝ) + Z) ^ 3) := by
    intro n _
    have hapos : 0 < s n := lt_of_lt_of_le zero_lt_one (hs1 n)
    have hmpos : (0 : ℝ) < ((intScaleR (s n) : ℕ) : ℝ) := by
      have h : 0 < intScaleR (s n) := lt_of_lt_of_le Nat.zero_lt_one (one_le_intScaleR (s n))
      exact_mod_cast h
    have hle : ((intScaleR (s n) : ℕ) : ℝ) ≤ s n := intScaleR_le (hs1 n)
    have hlt : s n ≤ 2 * ((intScaleR (s n) : ℕ) : ℝ) := (lt_two_mul_intScaleR (hs1 n)).le
    have hmono : ((intScaleR (s n) : ℕ) : ℝ) + Z ≤ s n + Z := by linarith
    calc s n / (s n + Z) ^ 3
        ≤ (2 * ((intScaleR (s n) : ℕ) : ℝ)) / (s n + Z) ^ 3 :=
          div_le_div_of_nonneg_right hlt (by positivity)
      _ ≤ (2 * ((intScaleR (s n) : ℕ) : ℝ))
            / (((intScaleR (s n) : ℕ) : ℝ) + Z) ^ 3 := by
          refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
          exact pow_le_pow_left₀ (by positivity) hmono 3
      _ = 2 * ((((intScaleR (s n) : ℕ)) : ℝ)
            / ((((intScaleR (s n) : ℕ)) : ℝ) + Z) ^ 3) := by ring
  calc ∑ n ∈ U, s n / (s n + Z) ^ 3
      ≤ ∑ n ∈ U, 2 * ((((intScaleR (s n) : ℕ)) : ℝ)
            / ((((intScaleR (s n) : ℕ)) : ℝ) + Z) ^ 3) := Finset.sum_le_sum hpt
    _ = 2 * ∑ n ∈ U, ((((intScaleR (s n) : ℕ)) : ℝ)
            / ((((intScaleR (s n) : ℕ)) : ℝ) + Z) ^ 3) := by rw [Finset.mul_sum]
    _ ≤ 2 * (4 / Z ^ 2) := mul_le_mul_of_nonneg_left hbase (by norm_num)
    _ = 8 / Z ^ 2 := by ring

/-! ## The multi-scale pointwise bound -/

lemma linDiffKernR_pointwise (K : SchwartzMap ℝ ℂ) {C : ℝ} (hC : 0 < C)
    (hCb : ∀ (s : ℝ), 0 < s → ∀ (y z : ℤ), 2 * y.natAbs ≤ z.natAbs →
      ‖bumpKernR K s (z - y) - bumpKernR K s z‖
        ≤ C * (y.natAbs : ℝ) * (s / (s + (z.natAbs : ℝ)) ^ 3))
    (σ ρ : ℕ → ℝ) (hσ1 : ∀ n, 1 ≤ σ n) (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1))
    (hρ1 : ∀ n, 1 ≤ ρ n) (hρ2 : ∀ n, 2 * ρ n ≤ ρ (n + 1))
    (hcmp : ∀ n, ρ n ≤ σ n ∧ σ n ≤ 2 * ρ n)
    (U : Finset ℕ) (ω : ℕ → Bool) (y x : ℤ) (hy : y ≠ 0) (hx : 2 * y.natAbs ≤ x.natAbs) :
    ‖linDiffKernR K σ ρ U ω (x - y) - linDiffKernR K σ ρ U ω x‖
      ≤ (8 * C) * (2 * (y.natAbs : ℝ)) / ((x.natAbs : ℝ)) ^ 2 := by
  have hxpos : (0 : ℝ) < (x.natAbs : ℝ) := by
    have h2 : 0 < y.natAbs := Int.natAbs_pos.mpr hy
    have h3 : 0 < x.natAbs := by omega
    exact_mod_cast h3
  have hdiff : linDiffKernR K σ ρ U ω (x - y) - linDiffKernR K σ ρ U ω x
      = ∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n
          * (diffKernR K (σ n) (ρ n) (x - y) - diffKernR K (σ n) (ρ n) x) := by
    rw [linDiffKernR, linDiffKernR, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hdiff]
  calc ‖∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n
          * (diffKernR K (σ n) (ρ n) (x - y) - diffKernR K (σ n) (ρ n) x)‖
      ≤ ∑ n ∈ U, ‖Work.KMTAreas.ADev.bSign ω n
          * (diffKernR K (σ n) (ρ n) (x - y) - diffKernR K (σ n) (ρ n) x)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ U, ‖diffKernR K (σ n) (ρ n) (x - y) - diffKernR K (σ n) (ρ n) x‖ := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (Work.KMTAreas.ADev.norm_bSign_le ω n)
    _ ≤ ∑ n ∈ U, (C * (y.natAbs : ℝ) * ((σ n) / ((σ n) + (x.natAbs : ℝ)) ^ 3)
          + C * (y.natAbs : ℝ) * ((ρ n) / ((ρ n) + (x.natAbs : ℝ)) ^ 3)) := by
        refine Finset.sum_le_sum fun n _ => ?_
        have hσpos : 0 < σ n := lt_of_lt_of_le zero_lt_one (hσ1 n)
        have hρpos : 0 < ρ n := lt_of_lt_of_le zero_lt_one (hρ1 n)
        have hEq : diffKernR K (σ n) (ρ n) (x - y) - diffKernR K (σ n) (ρ n) x
            = (bumpKernR K (σ n) (x - y) - bumpKernR K (σ n) x)
              - (bumpKernR K (ρ n) (x - y) - bumpKernR K (ρ n) x) := by
          rw [diffKernR, diffKernR]; ring
        rw [hEq]
        have htri := norm_sub_le (bumpKernR K (σ n) (x - y) - bumpKernR K (σ n) x)
          (bumpKernR K (ρ n) (x - y) - bumpKernR K (ρ n) x)
        exact htri.trans (add_le_add (hCb (σ n) hσpos y x hx) (hCb (ρ n) hρpos y x hx))
    _ = C * (y.natAbs : ℝ) * (∑ n ∈ U, (σ n) / ((σ n) + (x.natAbs : ℝ)) ^ 3)
        + C * (y.natAbs : ℝ) * (∑ n ∈ U, (ρ n) / ((ρ n) + (x.natAbs : ℝ)) ^ 3) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ C * (y.natAbs : ℝ) * (8 / (x.natAbs : ℝ) ^ 2)
        + C * (y.natAbs : ℝ) * (8 / (x.natAbs : ℝ) ^ 2) := by
        refine add_le_add ?_ ?_
        · refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC.le (Nat.cast_nonneg _))
          exact linDiff_lacSumCubic σ hσ1 hσ2 U hxpos
        · refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC.le (Nat.cast_nonneg _))
          exact linDiff_lacSumCubic ρ hρ1 hρ2 U hxpos
    _ = (8 * C) * (2 * (y.natAbs : ℝ)) / ((x.natAbs : ℝ)) ^ 2 := by ring

/-! ## The target -/

theorem linDiffKernR_hormander (K : SchwartzMap ℝ ℂ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (σ ρ : ℕ → ℝ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      (∀ n, 1 ≤ ρ n) → (∀ n, 2 * ρ n ≤ ρ (n + 1)) →
      (∀ n, ρ n ≤ σ n ∧ σ n ≤ 2 * ρ n) → ∀ (U : Finset ℕ) (ω : ℕ → Bool) (y : ℤ), y ≠ 0 →
      ∫⁻ x in {x : ℤ | 2 * y.natAbs ≤ x.natAbs},
        ‖linDiffKernR K σ ρ U ω (x - y) - linDiffKernR K σ ρ U ω x‖ₑ
          ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) ≤ ENNReal.ofReal A := by
  obtain ⟨C, hCpos, hCb⟩ := bumpKernR_singleScaleDiff K
  refine ⟨32 * C, by positivity, ?_⟩
  intro σ ρ hσ1 hσ2 hρ1 hρ2 hcmp U ω y hy
  have hy1 : 1 ≤ y.natAbs := by
    have h := Int.natAbs_pos.mpr hy
    omega
  have hSmeas : MeasurableSet {x : ℤ | 2 * y.natAbs ≤ x.natAbs} :=
    Set.Countable.measurableSet (Set.to_countable _)
  have hpt : ∀ x ∈ {x : ℤ | 2 * y.natAbs ≤ x.natAbs},
      ‖linDiffKernR K σ ρ U ω (x - y) - linDiffKernR K σ ρ U ω x‖
        ≤ (8 * C) * (2 * (y.natAbs : ℝ)) / ((x.natAbs : ℝ)) ^ 2 :=
    fun x hx => linDiffKernR_pointwise K hCpos hCb σ ρ hσ1 hσ2 hρ1 hρ2 hcmp U ω y x hy
      (by simpa using hx)
  have hmain : ∫⁻ x in {x : ℤ | 2 * y.natAbs ≤ x.natAbs},
        ‖linDiffKernR K σ ρ U ω (x - y) - linDiffKernR K σ ρ U ω x‖ₑ
          ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ≤ ∑' x : ℤ, (if 2 * y.natAbs ≤ x.natAbs then
          ENNReal.ofReal ((8 * C) * (2 * (y.natAbs : ℝ)) / ((x.natAbs : ℝ)) ^ 2) else 0) := by
    rw [← lintegral_indicator hSmeas
      (fun x => ‖linDiffKernR K σ ρ U ω (x - y) - linDiffKernR K σ ρ U ω x‖ₑ)]
    calc ∫⁻ x, ({x : ℤ | 2 * y.natAbs ≤ x.natAbs}.indicator
            (fun x => ‖linDiffKernR K σ ρ U ω (x - y) - linDiffKernR K σ ρ U ω x‖ₑ) x)
          ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ∫⁻ x, ({x : ℤ | 2 * y.natAbs ≤ x.natAbs}.indicator
            (fun x => ENNReal.ofReal
              ((8 * C) * (2 * (y.natAbs : ℝ)) / ((x.natAbs : ℝ)) ^ 2)) x)
          ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ {x : ℤ | 2 * y.natAbs ≤ x.natAbs}
          · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
            calc ‖linDiffKernR K σ ρ U ω (x - y) - linDiffKernR K σ ρ U ω x‖ₑ
                = ENNReal.ofReal
                    ‖linDiffKernR K σ ρ U ω (x - y) - linDiffKernR K σ ρ U ω x‖ :=
                  (ofReal_norm (linDiffKernR K σ ρ U ω (x - y) - linDiffKernR K σ ρ U ω x)).symm
              _ ≤ ENNReal.ofReal
                    ((8 * C) * (2 * (y.natAbs : ℝ)) / ((x.natAbs : ℝ)) ^ 2) :=
                  ENNReal.ofReal_le_ofReal (hpt x hx)
          · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      _ = ∑' x : ℤ, ({x : ℤ | 2 * y.natAbs ≤ x.natAbs}.indicator
            (fun x => ENNReal.ofReal
              ((8 * C) * (2 * (y.natAbs : ℝ)) / ((x.natAbs : ℝ)) ^ 2)) x) :=
          lintegral_count _
      _ = ∑' x : ℤ, (if 2 * y.natAbs ≤ x.natAbs then
          ENNReal.ofReal ((8 * C) * (2 * (y.natAbs : ℝ)) / ((x.natAbs : ℝ)) ^ 2) else 0) := by
          refine tsum_congr fun x => ?_
          rw [Set.indicator_apply]
          by_cases hx : x ∈ {x : ℤ | 2 * y.natAbs ≤ x.natAbs}
          · rw [if_pos hx, if_pos (by simpa using hx)]
          · rw [if_neg hx, if_neg (by simpa using hx)]
  refine hmain.trans ?_
  calc ∑' x : ℤ, (if 2 * y.natAbs ≤ x.natAbs then
        ENNReal.ofReal ((8 * C) * (2 * (y.natAbs : ℝ)) / ((x.natAbs : ℝ)) ^ 2) else 0)
      ≤ ENNReal.ofReal (4 * (8 * C)) :=
        Work.KMTAreas.A7.loDev_lintegral_majorant (8 * C) (by positivity) hy1
    _ ≤ ENNReal.ofReal (32 * C) := ENNReal.ofReal_le_ofReal (by linarith)

end

end Work.A7Hi2
