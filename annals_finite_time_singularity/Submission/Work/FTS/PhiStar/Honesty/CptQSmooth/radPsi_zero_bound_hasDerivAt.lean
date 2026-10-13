import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_contDiffOn
import Submission.Work.FTS.PhiStar.Series.SmoothAux.Deleg.radPsi_rec
import Submission.Work.FTS.PhiStar.Honesty.CptQSmooth.Deleg.truncated_kernel_facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped ContDiff Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptQSmooth

open Work.FTS.PhiStar.RadialWAux (radPsi radP radPsi_zero_eq contDiffOn_tailIntegral)

/-!
# The `m = 0` (borderline) case of the outer rescaled Green piece `Ψ`

For a source `c` of class `C^{a+1}` on `(0,∞)` with `|c^{(k)}| ≤ K` there (`k ≤ a+1`) which
vanishes off `[a₀,b]` with `a₀ > 0`, the borderline piece

  `radPsi α 0 c z = ∫_{u > 1} c (z u) u^{-1} du`

is controlled uniformly: its first `a` derivatives are bounded by `C K` on `[z₀,∞)`, and it is
differentiable to order `a + 1` on `(0,∞)`.

The two ingredients are (i) the change of variables `t = z u`, which exhibits `radPsi α 0 c` as
the *tail integral* of `k t = c t / t` on `(0,∞)` (`radPsi_zero_eq`) — smoothness then follows
from `contDiffOn_tailIntegral` — and (ii) the observation that, because `c` is supported in
`[a₀,b]`, the outer integral may be truncated at the fixed `U = max 1 (2b/z₁)`, whereupon the
derivatives and their bounds are those of the truncated kernel
(`Deleg.truncated_kernel_facts`).
-/

/-- If the source vanishes off `[a₀,b]` then the rescaled outer integrand of `radPsi` vanishes
for `u` beyond `U = max 1 (2b/z₁)`, uniformly for `z ≥ z₁ > 0`. -/
lemma trunc_vanishing {c : ℝ → ℝ} {a₀ b z₁ : ℝ} (ha₀ : 0 < a₀) (hz₁ : 0 < z₁)
    (hsupp : ∀ t : ℝ, t ∉ Set.Icc a₀ b → c t = 0) :
    ∀ z : ℝ, z₁ ≤ z → ∀ u : ℝ, max 1 (2 * b / z₁) < u → c (z * u) = 0 := by
  intro z hz u hu
  by_contra hne
  have hmem : z * u ∈ Set.Icc a₀ b := by
    by_contra h
    exact hne (hsupp (z * u) h)
  rw [Set.mem_Icc] at hmem
  have hU2 : 2 * b / z₁ < u := lt_of_le_of_lt (le_max_right (1 : ℝ) (2 * b / z₁)) hu
  have h1u : (1 : ℝ) < u := lt_of_le_of_lt (le_max_left (1 : ℝ) (2 * b / z₁)) hu
  have hzu : b < z * u := by
    have h1 : z₁ * (2 * b / z₁) < z₁ * u := mul_lt_mul_of_pos_left hU2 hz₁
    have h2 : z₁ * (2 * b / z₁) = 2 * b := by field_simp
    have h3 : z₁ * u ≤ z * u :=
      mul_le_mul_of_nonneg_right hz (le_of_lt (lt_trans zero_lt_one h1u))
    rw [h2] at h1
    linarith
  linarith [hmem.2]

/-- The rescaled outer piece, truncated at `U = max 1 (2b/z₁)`: if the source is supported in
`[a₀,b]` then for `z ≥ z₁ > 0` the outer integral may be taken over the fixed interval `(1,U)`. -/
lemma radPsi_zero_eq_trunc {α : ℝ} {c : ℝ → ℝ} {a₀ b z₁ z : ℝ} (ha₀ : 0 < a₀) (hz₁ : 0 < z₁)
    (hsupp : ∀ t : ℝ, t ∉ Set.Icc a₀ b → c t = 0) (hz : z₁ ≤ z) :
    radPsi α 0 c z
      = ∫ u in (1 : ℝ)..(max 1 (2 * b / z₁)), c (z * u) * u ^ (-(radP α 0) - 1) := by
  set U : ℝ := max 1 (2 * b / z₁) with hUdef
  have hU1 : (1 : ℝ) ≤ U := le_max_left _ _
  rw [radPsi]
  have hsub : Set.Ioc (1 : ℝ) U ⊆ Set.Ioi (1 : ℝ) := fun x hx => hx.1
  have hvan : ∀ u ∈ Set.Ioi (1 : ℝ) \ Set.Ioc (1 : ℝ) U,
      c (z * u) * u ^ (-(radP α 0) - 1) = 0 := by
    intro u hu
    have hnu : ¬ (u ≤ U) := fun hle => hu.2 ⟨hu.1, hle⟩
    have huU : U < u := not_le.mp hnu
    rw [hUdef] at huU
    rw [trunc_vanishing ha₀ hz₁ hsupp z hz u huU, zero_mul]
  rw [MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub hvan]
  exact (intervalIntegral.integral_of_le hU1).symm

/-- Integrability of `t ↦ c t / t` on a tail, for a source which is continuous on `(0,∞)`,
bounded by `K` and supported in `[a₀,b]`, `a₀ > 0`. -/
lemma integrableOn_mul_inv_Ioi {c : ℝ → ℝ} {a₀ b K : ℝ} (ha₀ : 0 < a₀) (hK : 0 ≤ K)
    (hcont : ContinuousOn c (Set.Ioi 0)) (hb : ∀ t : ℝ, 0 < t → |c t| ≤ K)
    (hsupp : ∀ t : ℝ, t ∉ Set.Icc a₀ b → c t = 0) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => c t * t⁻¹) (Set.Ioi a) volume := by
  have hkc : ContinuousOn (fun t : ℝ => c t * t⁻¹) (Set.Ioi 0) :=
    hcont.mul (continuousOn_id.inv₀ fun t ht => ne_of_gt ht)
  have hbound : ∀ t ∈ Set.Icc a₀ b, ‖c t * t⁻¹‖ ≤ K / a₀ := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha₀ ht.1
    have h2 : |t⁻¹| ≤ a₀⁻¹ := by
      rw [abs_inv, abs_of_pos ht0]
      exact inv_anti₀ ha₀ ht.1
    rw [Real.norm_eq_abs, abs_mul, div_eq_mul_inv]
    exact mul_le_mul (hb t ht0) h2 (abs_nonneg _)
      (le_trans (abs_nonneg _) (hb t ht0))
  have hmeas : AEStronglyMeasurable (fun t : ℝ => c t * t⁻¹)
      (volume.restrict (Set.Icc a₀ b)) :=
    ((hkc.mono fun t ht => lt_of_lt_of_le ha₀ ht.1).aestronglyMeasurable measurableSet_Icc)
  have hint : IntegrableOn (fun t : ℝ => c t * t⁻¹) (Set.Icc a₀ b) volume :=
    IntegrableOn.of_bound measure_Icc_lt_top hmeas (K / a₀)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact hbound t ht)
  have hvan : (fun t : ℝ => c t * t⁻¹)
      = (Set.Icc a₀ b).indicator (fun t : ℝ => c t * t⁻¹) := by
    funext t
    by_cases ht : t ∈ Set.Icc a₀ b
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, hsupp t ht, zero_mul]
  have hkint : Integrable (fun t : ℝ => c t * t⁻¹) volume :=
    ((integrable_indicator_iff measurableSet_Icc).2 hint).congr
      (Eventually.of_forall (fun t => (congrFun hvan t).symm))
  exact hkint.mono_measure Measure.restrict_le_self

/-- Smoothness of the borderline outer piece `radPsi α 0 c`: on `(0,∞)` it is as smooth as the
source, no matter how small `α` is (the exponent `radP α 0 = 0` is critical, but the tail
integral `∫_{Ioi z} c t t^{-1} dt` is still differentiable, its integrand being continuous and
supported in `[a₀,b]`). -/
lemma radPsi_zero_contDiffOn {α : ℝ} {n : ℕ} {c : ℝ → ℝ} {a₀ b K : ℝ}
    (ha₀ : 0 < a₀) (hc : ContDiffOn ℝ (↑n) c (Set.Ioi 0)) (hb : Work.FTS.PhiStar.BddDeriv n c K)
    (hsupp : ∀ t : ℝ, t ∉ Set.Icc a₀ b → c t = 0) :
    ContDiffOn ℝ (↑n) (radPsi α 0 c) (Set.Ioi 0) := by
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hb 0 (Nat.zero_le n) 1 one_pos)
  have hbdd : ∀ t : ℝ, 0 < t → |c t| ≤ K := fun t ht => hb 0 (Nat.zero_le n) t ht
  have hk : ContDiffOn ℝ (↑n) (fun t : ℝ => c t * t⁻¹) (Set.Ioi 0) := by
    refine hc.mul ?_
    have h : ContDiffOn ℝ (↑n) (fun y : ℝ => y ^ (-1 : ℝ)) (Set.Ioi 0) :=
      contDiffOn_id.rpow_const_of_ne (p := (-1 : ℝ)) (fun x hx => ne_of_gt hx)
    exact h.congr (fun y _ => by rw [Real.rpow_neg_one])
  have hint : ∀ a ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun t : ℝ => c t * t⁻¹) (Set.Ioi a) volume :=
    fun a ha => integrableOn_mul_inv_Ioi ha₀ hK hc.continuousOn hbdd hsupp ha
  have hT : ContDiffOn ℝ (↑(n + 1)) (fun z => ∫ t in Set.Ioi z, c t * t⁻¹) (Set.Ioi 0) :=
    contDiffOn_tailIntegral (n := n) hk hint
  refine (hT.of_le (by exact_mod_cast Nat.le_succ n)).congr (fun z hz => ?_)
  exact radPsi_zero_eq hz

theorem radPsi_zero_bound_hasDerivAt {α : ℝ} {a : ℕ} {a₀ b z₀ : ℝ}
    (ha₀ : 0 < a₀) (hz₀ : 0 < z₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c : ℝ → ℝ} {K : ℝ}, 0 ≤ K →
      ContDiffOn ℝ (↑(a + 1)) c (Set.Ioi 0) → Work.FTS.PhiStar.BddDeriv (a + 1) c K →
      (∀ t : ℝ, t ∉ Set.Icc a₀ b → c t = 0) →
      (∀ j : ℕ, j ≤ a → ∀ z : ℝ, z₀ ≤ z →
          |iteratedDeriv j (fun z' => Work.FTS.PhiStar.RadialWAux.radPsi α 0 c z') z| ≤ C * K)
      ∧ (∀ j : ℕ, j + 1 ≤ a + 1 → ∀ z : ℝ, 0 < z →
          HasDerivAt (iteratedDeriv j (fun z' => Work.FTS.PhiStar.RadialWAux.radPsi α 0 c z'))
            (iteratedDeriv (j + 1) (fun z' => Work.FTS.PhiStar.RadialWAux.radPsi α 0 c z') z) z) := by
  set z₁ : ℝ := z₀ / 2 with hz₁def
  have hz₁ : 0 < z₁ := by rw [hz₁def]; linarith
  set U : ℝ := max 1 (2 * b / z₁) with hUdef
  have hU1 : (1 : ℝ) ≤ U := by rw [hUdef]; exact le_max_left _ _
  have hU0 : (0 : ℝ) < U := lt_of_lt_of_le zero_lt_one hU1
  refine ⟨U ^ (a + 2), pow_nonneg hU0.le _, ?_⟩
  intro c K hK hc hb hsupp
  have hsneg : -(radP α 0) - 1 ≤ (0 : ℝ) := by
    have h0 : radP α 0 = 0 := by simp [radP]
    rw [h0]; norm_num
  constructor
  · intro j hj z hz
    have hzpos : 0 < z := lt_of_lt_of_le hz₀ hz
    have hz1lt : z₁ < z := by rw [hz₁def]; linarith
    have hev : (fun z' => radPsi α 0 c z') =ᶠ[𝓝 z]
        fun x => ∫ u in (1 : ℝ)..U, c (x * u) * u ^ (-(radP α 0) - 1) := by
      have hmem : Set.Ici z₁ ∈ 𝓝 z :=
        mem_of_superset (isOpen_Ioi.mem_nhds hz1lt) (fun x hx => le_of_lt (show z₁ < x from hx))
      filter_upwards [hmem] with x hx
      rw [hUdef]
      exact radPsi_zero_eq_trunc ha₀ hz₁ hsupp hx
    have hbnd := (Work.FTS.PhiStar.Honesty.CptQSmooth.Deleg.truncated_kernel_facts
      (N := a + 1) (c := c) (K := K) (U := U) (s := -(radP α 0) - 1)
      hK hU1 hsneg hc hb j (by omega) z hzpos).2
    rw [max_eq_right hU1] at hbnd
    rw [hev.iteratedDeriv_eq j]
    exact hbnd.trans (by rw [mul_comm])
  · intro j hj z hz
    have hcd : ContDiffOn ℝ (↑(a + 1))
        (fun z' => radPsi α 0 c z') (Set.Ioi 0) :=
      radPsi_zero_contDiffOn ha₀ hc hb hsupp
    have hcAt : ContDiffAt ℝ (↑(a + 1)) (fun z' => radPsi α 0 c z') z :=
      hcd.contDiffAt (isOpen_Ioi.mem_nhds hz)
    exact Work.FTS.PhiStar.Series.SmoothAux.Deleg.rpr_hasDerivAt_iteratedDeriv hcAt (by omega)

end Work.FTS.PhiStar.Honesty.CptQSmooth
