import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Filter
open scoped Topology

namespace Commons.Analysis.Calculus

theorem exists_uniform_injective_of_hasStrictFDerivAt_of_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : IsCompact K) {F : E × E → E} (f' : E → (E × E →L[ℝ] E)) {a : E} {c : ℝ}
    (hc : 0 < c)
    (hstrict : ∀ x ∈ K, HasStrictFDerivAt F (f' x) (x, a))
    (hbound : ∀ x ∈ K, ∀ z : E, c * ‖z‖ ≤ ‖f' x ((0 : E), z)‖) :
    ∃ ε : ℝ, (0 < ε) ∧ (∀ x ∈ K, ∀ u v : E,
      dist u a < ε → dist v a < ε → F (x, u) = F (x, v) → u = v) := by
  by_contra hcon
  push Not at hcon
  have key : ∀ n : ℕ, ∃ x ∈ K, ∃ u v : E,
      dist u a < (1:ℝ)/(n+1) ∧ dist v a < (1:ℝ)/(n+1) ∧ F (x, u) = F (x, v) ∧ u ≠ v :=
    fun n => hcon _ (by positivity)
  choose x hxK u v hu hv heq hne using key
  obtain ⟨x₀, hx₀K, φ, hφmono, hxφ⟩ := hK.tendsto_subseq hxK
  have hφ_atTop : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  have hu_tendsto : Tendsto u atTop (𝓝 a) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hu n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hv_tendsto : Tendsto v atTop (𝓝 a) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hv n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have huφ : Tendsto (fun n => u (φ n)) atTop (𝓝 a) := hu_tendsto.comp hφ_atTop
  have hvφ : Tendsto (fun n => v (φ n)) atTop (𝓝 a) := hv_tendsto.comp hφ_atTop
  have hxφ' : Tendsto (fun n => x (φ n)) atTop (𝓝 x₀) := hxφ
  have hq : Tendsto (fun n => ((x (φ n), u (φ n)), (x (φ n), v (φ n)))) atTop
      (𝓝 (((x₀, a):E×E), ((x₀, a):E×E))) :=
    (hxφ'.prodMk_nhds huφ).prodMk_nhds (hxφ'.prodMk_nhds hvφ)
  have hlit := (hstrict x₀ hx₀K).isLittleO.bound (show (0:ℝ) < c/2 by linarith)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hq.eventually hlit)
  have hineq := hN N le_rfl
  have hp1 : F (x (φ N), u (φ N)) - F (x (φ N), v (φ N)) = 0 := by rw [heq (φ N), sub_self]
  have hpd : (x (φ N), u (φ N)) - (x (φ N), v (φ N)) = (0, u (φ N) - v (φ N)) := by
    rw [Prod.mk_sub_mk, sub_self]
  rw [hp1, hpd, zero_sub, norm_neg, Prod.norm_def, norm_zero,
    max_eq_right (norm_nonneg _)] at hineq
  have hb := hbound x₀ hx₀K (u (φ N) - v (φ N))
  have hnorm : ‖u (φ N) - v (φ N)‖ = 0 := by
    have hct : c * ‖u (φ N) - v (φ N)‖ ≤ c / 2 * ‖u (φ N) - v (φ N)‖ := le_trans hb hineq
    nlinarith [hc, norm_nonneg (u (φ N) - v (φ N))]
  exact hne (φ N) (sub_eq_zero.mp (norm_eq_zero.mp hnorm))

end Commons.Analysis.Calculus
