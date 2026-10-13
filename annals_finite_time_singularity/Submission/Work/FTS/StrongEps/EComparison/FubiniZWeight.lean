import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

open MeasureTheory Set

/-- The point `b` belongs to the unordered interval `[a,b]` when `a ≤ b`. -/
private lemma fubiniZWeight_mem_uIcc {a b : ℝ} (hab : a ≤ b) : b ∈ Set.uIcc a b := by
  rw [Set.uIcc_of_le hab]
  exact ⟨hab, le_rfl⟩

/-- **Integration by parts for a triangular domain.**

For an interval integrable `g` and an absolutely continuous `φ` on `[a,b]` with `φ a = 0`,
```
∫_a^b φ'(t) (∫_t^b g(z) dz) dt = ∫_a^b g(z) φ(z) dz .
```
The primitive `t ↦ ∫_t^b g z dz` is absolutely continuous and, by the Lebesgue differentiation
theorem (`IntervalIntegrable.ae_hasDerivAt_integral`), has a.e. derivative `-g`; integration by
parts for absolutely continuous functions then gives the identity, the boundary term at `b`
vanishing because the integral over `[b,b]` is zero and the term at `a` vanishing because
`φ a = 0`. -/
private lemma fubiniZWeight_ibp_triangle {a b : ℝ} {g φ : ℝ → ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b)
    (hφ : AbsolutelyContinuousOnInterval φ a b) (hφa : φ a = 0) :
    ∫ t in a..b, deriv φ t * (∫ z in t..b, g z) = ∫ z in a..b, g z * φ z := by
  -- The two primitives `G t = ∫ z in b..t, g z` and its negative `F = -G`.
  let G : ℝ → ℝ := fun t => ∫ z in b..t, g z
  let F : ℝ → ℝ := -G
  have hF_eq : ∀ t, F t = ∫ z in t..b, g z := by
    intro t
    have hsym : ∫ z in b..t, g z = -∫ z in t..b, g z := intervalIntegral.integral_symm t b
    simp only [F, G, Pi.neg_apply]
    linarith
  have hGac : AbsolutelyContinuousOnInterval G a b :=
    IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral hg
      (fubiniZWeight_mem_uIcc hab)
  -- The a.e. derivative of `G`, from the Lebesgue differentiation theorem.
  have hGd : ∀ᵐ x, x ∈ Set.uIcc a b → HasDerivAt G (g x) x := by
    filter_upwards [IntervalIntegrable.ae_hasDerivAt_integral hg] with x hx hxab
    exact hx hxab b (fubiniZWeight_mem_uIcc hab)
  have hFd : ∀ᵐ x, x ∈ Set.uIcc a b → HasDerivAt F (-(g x)) x := by
    filter_upwards [hGd] with x hx hxab
    exact (hx hxab).neg
  have hFac : AbsolutelyContinuousOnInterval F a b := hGac.neg
  have hFb : F b = 0 := by rw [hF_eq b, intervalIntegral.integral_same]
  -- Replace `deriv F` by `-g` under the integral.
  have hderiv : ∫ x in a..b, deriv F x * φ x = -∫ x in a..b, g x * φ x := by
    have h1 : ∫ x in a..b, deriv F x * φ x = ∫ x in a..b, -(g x * φ x) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hFd] with x hx hxu
      rw [(hx (Set.uIoc_subset_uIcc hxu)).deriv, neg_mul]
    rw [h1, intervalIntegral.integral_neg]
  have hIBP := AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul hFac hφ
  have hmain : ∫ x in a..b, F x * deriv φ x = ∫ x in a..b, g x * φ x := by
    rw [hIBP, hFb, hφa, hderiv]
    ring
  rw [show (∫ t in a..b, deriv φ t * (∫ z in t..b, g z)) = ∫ t in a..b, deriv φ t * F t from
    intervalIntegral.integral_congr (fun t _ => by rw [hF_eq t])]
  rw [show (∫ t in a..b, deriv φ t * F t) = ∫ t in a..b, F t * deriv φ t from
    intervalIntegral.integral_congr (fun t _ => mul_comm _ _)]
  exact hmain

theorem FubiniZWeight {a b : ℝ} {W ρ : ℝ → ℝ}
    (hW : MeasureTheory.LocallyIntegrableOn W (Set.Ioi 0)) (ha : 0 < a) (hab : a < b)
    (hρ : ∀ n : ℕ, ContDiff ℝ n ρ) (hρc : HasCompactSupport ρ)
    (hsupp : tsupport ρ ⊆ Set.Ioo a b) :
    (∫ t in a..b, deriv (deriv ρ) t * (∫ z in t..b, W z * z))
      = ∫ z in a..b, W z * z * deriv ρ z := by
  -- `z ↦ W z * z` is locally integrable on `(0,∞)` (hence integrable on `[a,b]`, as `a > 0`).
  have hloc : MeasureTheory.LocallyIntegrableOn (fun z : ℝ => W z * z) (Set.Ioi 0) :=
    hW.mul_continuousOn continuous_id.continuousOn isOpen_Ioi.isLocallyClosed
  have hgIcc : MeasureTheory.IntegrableOn (fun z : ℝ => W z * z) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab.le]
    exact hloc.integrableOn_compact_subset (fun z hz => lt_of_lt_of_le ha hz.1) isCompact_Icc
  have hg : IntervalIntegrable (fun z : ℝ => W z * z) volume a b :=
    intervalIntegrable_iff.mpr (hgIcc.mono_set Set.uIoc_subset_uIcc)
  -- `deriv ρ` is Lipschitz (hence absolutely continuous) on `[a,b]`: it is `C¹` there.
  have hφ : AbsolutelyContinuousOnInterval (deriv ρ) a b := by
    have hd : ContDiffOn ℝ 1 (deriv ρ) (Set.uIcc a b) := by
      have h2 : ContDiffOn ℝ 2 ρ Set.univ := (hρ 2).contDiffOn
      exact (h2.deriv_of_isOpen isOpen_univ (by norm_num)).mono (Set.subset_univ _)
    obtain ⟨K, hK⟩ := hd.exists_lipschitzOnWith (by norm_num) (convex_uIcc a b) isCompact_uIcc
    exact hK.absolutelyContinuousOnInterval
  -- `deriv ρ` vanishes at `a`: `tsupport (deriv ρ) ⊆ tsupport ρ ⊆ (a,b)`.
  have hφa : deriv ρ a = 0 := by
    have ha_not : a ∉ tsupport ρ := fun h => (lt_irrefl a) (hsupp h).1
    exact image_eq_zero_of_notMem_tsupport (fun h => ha_not (tsupport_deriv_subset h))
  exact fubiniZWeight_ibp_triangle hab.le hg hφ hφa

end Work.FTS.StrongEps.EComparison
