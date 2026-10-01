import Mathlib
import Submission.Work.LinnikAreas.A5.Weights
import Submission.Work.LinnikAreas.A5.g0_elementary

namespace Work.LinnikAreas.A5

open Set Filter
open scoped Topology

/-- `gc K`, cut off at `t = 0`, is the clamped affine function `t ↦ max (K − t) 0 / K`
multiplied by the indicator of `[0,∞)`. -/
private lemma gc_eq_clamp (K : ℝ) :
    gc K = fun t : ℝ => if 0 ≤ t then max (K - t) 0 / K else 0 := by
  funext t
  by_cases h0 : 0 ≤ t
  · by_cases ht : t ≤ K
    · rw [gc_of_mem h0 ht, if_pos h0, max_eq_left (by linarith : (0:ℝ) ≤ K - t)]
    · rw [gc_of_not_mem (fun hc => ht hc.2), if_pos h0,
        max_eq_right (by linarith [not_le.mp ht] : K - t ≤ 0), zero_div]
  · rw [gc_of_lt (not_le.mp h0), if_neg h0]

/-- Pointwise form of `gc_eq_clamp`: for `t ≥ 0`, `gc K t` is the clamped affine value
`max (K − t) 0 / K`. -/
private lemma gc_eq_clamp_apply {K t : ℝ} (h : 0 ≤ t) : gc K t = max (K - t) 0 / K := by
  rw [gc_eq_clamp K]
  exact if_pos h

/-- The affine model `t ↦ (K − t)/K` has vanishing second derivative. -/
private lemma iteratedDeriv_two_affine (K t : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => (K - s) / K) t = 0 := by
  have hfun : (fun s : ℝ => (K - s) / K) = fun s => K⁻¹ * (K - s) := by
    funext s; rw [div_eq_mul_inv, mul_comm]
  rw [hfun, iteratedDeriv_const_mul _ (by fun_prop : ContDiffAt ℝ 2 (fun s : ℝ => K - s) t)]
  have hfun2 : (fun s : ℝ => K - s) = (fun _ : ℝ => K) - (fun s : ℝ => s) := by
    funext s; simp
  rw [hfun2, iteratedDeriv_sub (by fun_prop) (by fun_prop)]
  have hid : iteratedDeriv 2 (fun s : ℝ => s) t = 0 := by
    change iteratedDeriv 2 id t = 0
    rw [iteratedDeriv_id]; norm_num
  rw [hid, iteratedDeriv_const]; norm_num

/-- Elementary regularity of the `λ = 0` endpoint test function
`gc K t = if 0 ≤ t ∧ t ≤ K then (K−t)/K else 0` of HB Lemma 13.3: it is continuous on
`[0,∞)`, `C²` on `(0,K)` with vanishing second derivative there, bounded by `1` on all of `ℝ`,
nonnegative everywhere, and vanishes for `t ≥ K`. -/
theorem gc_elementary (K : ℝ) (hK : 0 < K) :
    ContinuousOn (Work.LinnikAreas.A5.gc K) (Set.Ici 0) ∧
    ContDiffOn ℝ 2 (Work.LinnikAreas.A5.gc K) (Set.Ioo 0 K) ∧
    (∀ t ∈ Set.Ioo (0:ℝ) K, iteratedDeriv 2 (Work.LinnikAreas.A5.gc K) t = 0) ∧
    (∀ t : ℝ, ‖Work.LinnikAreas.A5.gc K t‖ ≤ 1) ∧
    (∀ t : ℝ, 0 ≤ Work.LinnikAreas.A5.gc K t) ∧
    (∀ t : ℝ, K ≤ t → Work.LinnikAreas.A5.gc K t = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity on `[0,∞)`, where `gc K` is the clamped affine function
    refine ((by fun_prop : Continuous fun t : ℝ => max (K - t) 0 / K).continuousOn).congr ?_
    intro t ht
    exact gc_eq_clamp_apply ht
  · -- smoothness on `(0,K)`, where `gc K` agrees with the affine model
    refine (by fun_prop : ContDiffOn ℝ 2 (fun t : ℝ => (K - t) / K) (Set.Ioo 0 K)).congr ?_
    intro t ht
    exact gc_of_mem (le_of_lt ht.1) ht.2.le
  · -- vanishing second derivative on `(0,K)`
    intro t ht
    have hmem : Set.Ioo (0:ℝ) K ∈ nhds t := isOpen_Ioo.mem_nhds ht
    have hev : gc K =ᶠ[nhds t] (fun s : ℝ => (K - s) / K) :=
      eventuallyEq_of_mem hmem (fun s hs => gc_of_mem (le_of_lt hs.1) hs.2.le)
    rw [hev.iteratedDeriv_eq 2, iteratedDeriv_two_affine]
  · -- the global bound `‖gc K‖ ≤ 1`
    intro t
    by_cases h0 : 0 ≤ t
    · rw [gc_eq_clamp_apply h0,
        Real.norm_of_nonneg (div_nonneg (le_max_right _ _) hK.le), div_le_one hK]
      exact max_le (by linarith) hK.le
    · rw [gc_of_lt (not_le.mp h0), norm_zero]; norm_num
  · -- nonnegativity everywhere
    intro t
    by_cases h0 : 0 ≤ t
    · rw [gc_eq_clamp_apply h0]; exact div_nonneg (le_max_right _ _) hK.le
    · rw [gc_of_lt (not_le.mp h0)]
  · -- vanishing for `t ≥ K`
    intro t ht
    exact gc_of_ge ht

end Work.LinnikAreas.A5
