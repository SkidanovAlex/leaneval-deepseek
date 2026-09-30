import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology

namespace Commons.Analysis.Calculus

theorem exists_uniform_injective_of_hasStrictFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : IsCompact K) {H : E × E → E} (f' : E → (E × E) →L[ℝ] E)
    (hstrict : ∀ x ∈ K, HasStrictFDerivAt H (f' x) (x, 0))
    (hdir : ∀ x ∈ K, ∀ z : E, f' x (0, z) = z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ∀ u v : E, ‖u‖ < ε → ‖v‖ < ε → H (x, u) = H (x, v) → u = v := by
  by_contra hcon
  push Not at hcon
  have key : ∀ n : ℕ, ∃ x ∈ K, ∃ u v : E,
      ‖u‖ < (1:ℝ)/(n+1) ∧ ‖v‖ < (1:ℝ)/(n+1) ∧ H (x, u) = H (x, v) ∧ u ≠ v :=
    fun n => hcon _ (by positivity)
  choose x hxK u v hu hv heq hne using key
  obtain ⟨x₀, hx₀K, φ, hφmono, hxφ⟩ := hK.tendsto_subseq hxK
  have hφ_atTop : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  have hu_tendsto : Tendsto u atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hu n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hv_tendsto : Tendsto v atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hv n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have huφ : Tendsto (fun n => u (φ n)) atTop (𝓝 0) := hu_tendsto.comp hφ_atTop
  have hvφ : Tendsto (fun n => v (φ n)) atTop (𝓝 0) := hv_tendsto.comp hφ_atTop
  have hxφ' : Tendsto (fun n => x (φ n)) atTop (𝓝 x₀) := hxφ
  have hq : Tendsto (fun n => ((x (φ n), u (φ n)), (x (φ n), v (φ n)))) atTop
      (𝓝 (((x₀, 0):E×E), ((x₀, 0):E×E))) :=
    (hxφ'.prodMk_nhds huφ).prodMk_nhds (hxφ'.prodMk_nhds hvφ)
  have hlit := (hstrict x₀ hx₀K).isLittleO.bound (show (0:ℝ) < 1/2 by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hq.eventually hlit)
  have hineq := hN N le_rfl
  have hp1 : H (x (φ N), u (φ N)) - H (x (φ N), v (φ N)) = 0 := by rw [heq (φ N), sub_self]
  have hpd : (x (φ N), u (φ N)) - (x (φ N), v (φ N)) = (0, u (φ N) - v (φ N)) := by
    rw [Prod.mk_sub_mk, sub_self]
  have hfd : f' x₀ ((x (φ N), u (φ N)) - (x (φ N), v (φ N))) = u (φ N) - v (φ N) := by
    rw [hpd, hdir x₀ hx₀K]
  rw [hp1, hfd, hpd, zero_sub, norm_neg, Prod.norm_def, norm_zero,
    max_eq_right (norm_nonneg _)] at hineq
  have hnorm : ‖u (φ N) - v (φ N)‖ = 0 := by
    linarith [norm_nonneg (u (φ N) - v (φ N))]
  exact hne (φ N) (sub_eq_zero.mp (norm_eq_zero.mp hnorm))

end Commons.Analysis.Calculus