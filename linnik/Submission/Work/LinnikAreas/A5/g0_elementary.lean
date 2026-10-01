import Mathlib
import Submission.Work.LinnikAreas.A5.Basic

open Set Filter
open scoped Topology

namespace Work.LinnikAreas.A5

/-- The affine model `t ↦ (K - t)/K` of `g0 K` on `(0,K)` has vanishing second derivative;
this is a helper for `g0_elementary`. -/
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

/-- Elementary regularity of `g0 K t = if t ≤ K then (K−t)/K else 0`
(`Work.LinnikAreas.A5.g0`): it is continuous on `[0,∞)` (indeed everywhere, since both branches
vanish at `t = K`), it is `C²` on `(0,K)` (where it equals the affine function `(K−t)/K`, whose
second derivative vanishes), and it satisfies `0 ≤ g0 ≤ 1`. -/
theorem g0_elementary (K : ℝ) (hK : 0 < K) :
    ContinuousOn (Work.LinnikAreas.A5.g0 K) (Set.Ici 0) ∧
    ContDiffOn ℝ 2 (Work.LinnikAreas.A5.g0 K) (Set.Ioo 0 K) ∧
    (∀ t ∈ Set.Ioo (0 : ℝ) K, ‖iteratedDeriv 2 (Work.LinnikAreas.A5.g0 K) t‖ ≤ 0) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) K, ‖Work.LinnikAreas.A5.g0 K t‖ ≤ 1) ∧
    (∀ t : ℝ, 0 ≤ Work.LinnikAreas.A5.g0 K t) := by
  -- `g0 K` is the clamped affine function `t ↦ max (K - t) 0 / K` (using `K > 0`).
  have hcongr : Work.LinnikAreas.A5.g0 K = fun t : ℝ => max (K - t) 0 / K := by
    funext t
    by_cases h : t ≤ K
    · rw [Work.LinnikAreas.A5.g0_of_le h, max_eq_left (by linarith : (0:ℝ) ≤ K - t)]
    · rw [Work.LinnikAreas.A5.g0_of_ge (not_le.mp h).le, max_eq_right (by linarith : K - t ≤ 0),
        zero_div]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- continuity on `[0,∞)`, from the clamped form
    rw [hcongr]; fun_prop
  · -- smoothness on `(0,K)`, where `g0 K` agrees with the affine model
    exact (by fun_prop : ContDiffOn ℝ 2 (fun t : ℝ => (K - t) / K) (Set.Ioo 0 K)).congr
      (fun t ht => Work.LinnikAreas.A5.g0_of_le ht.2.le)
  · -- vanishing second derivative on `(0,K)`
    intro t ht
    have hmem : Set.Ioo (0:ℝ) K ∈ nhds t := isOpen_Ioo.mem_nhds ht
    have hev : Work.LinnikAreas.A5.g0 K =ᶠ[nhds t] (fun s : ℝ => (K - s)/K) :=
      eventuallyEq_of_mem hmem (fun s hs => Work.LinnikAreas.A5.g0_of_le hs.2.le)
    rw [hev.iteratedDeriv_eq 2, iteratedDeriv_two_affine]
    simp
  · -- `‖g0 K t‖ ≤ 1` on `[0,K]`
    intro t ht
    rw [Work.LinnikAreas.A5.g0_of_le ht.2,
      Real.norm_of_nonneg (div_nonneg (by linarith [ht.2]) hK.le), div_le_one hK]
    linarith [ht.1]
  · -- nonnegativity everywhere
    intro t
    have := congrFun hcongr t
    rw [this]
    exact div_nonneg (le_max_right _ _) hK.le

end Work.LinnikAreas.A5
