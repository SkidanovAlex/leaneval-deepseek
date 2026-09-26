import Mathlib
import Submission.Work.JordanBrouwer3.Defs

/-!
# The two sides of the frontier of a convex body in `ℝ³`

Given a compact convex set `K ⊆ ℝ³` with nonempty interior, its topological frontier
`∂K` is a topological `2`-sphere (a "round" convex surface), and it separates `ℝ³` into the
bounded side `interior K` and the unbounded side `Kᶜ`.  This file constructs the corresponding
`Work.JordanBrouwer3.SphereSides (frontier K)`.

The only non-elementary ingredient is the connectedness of the *unbounded* side `Kᶜ`: the
complement of a compact convex set in a space of dimension `≥ 2` is connected.  The proof here is
by a "ray to infinity" argument:

* pick `c ∈ interior K`; for every `y ∉ K` the ray `{c + t • (y - c) | 1 ≤ t}` is contained in
  `Kᶜ` (convexity of `K`), and
* the exterior `H` of a closed ball containing `K` is preconnected, is contained in `Kᶜ`, and
  every one of those rays meets `H`.

Hence `Kᶜ` is the union of the rays and of the preconnected hub `H`, all sharing `H`, so it is
preconnected.  Each ray is the continuous image of `[1, ∞)`, and `H` is the image of
`S² × (r, ∞)` under `(u, t) ↦ c + t • (u - c)`.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.JordanBrouwer3

noncomputable section

/-- The closed (outward) ray from `c` through `y` and beyond it: `{c + t • (y - c) | 1 ≤ t}`. -/
def raySet (c y : R3) : Set R3 := (fun t : ℝ => c + t • (y - c)) '' (Ici 1)

theorem mem_raySet {c y z : R3} :
    z ∈ raySet c y ↔ ∃ t : ℝ, 1 ≤ t ∧ z = c + t • (y - c) := by
  rw [raySet, Set.mem_image]
  constructor
  · rintro ⟨t, ht, htz⟩; exact ⟨t, ht, htz.symm⟩
  · rintro ⟨t, ht, htz⟩; exact ⟨t, ht, htz.symm⟩

theorem isPreconnected_raySet (c y : R3) : IsPreconnected (raySet c y) := by
  have hcont : Continuous (fun t : ℝ => c + t • (y - c)) := by fun_prop
  have := (isPreconnected_Ici (a := (1 : ℝ))).image _ hcont.continuousOn
  simpa [raySet] using this

/-- **The exterior of a closed ball in `ℝ³` is preconnected.**  It is the image of
`S² × (r, ∞)` under `(u, t) ↦ c + t • (u - c)`, a continuous map from a preconnected set. -/
theorem isPreconnected_compl_closedBall (c : R3) {r : ℝ} (hr : 0 ≤ r) :
    IsPreconnected (Metric.closedBall c r)ᶜ := by
  have hrank : (1 : Cardinal) < Module.rank ℝ R3 := by
    have h : Module.rank ℝ R3 = Module.rank ℝ (Fin 3 → ℝ) :=
      (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).rank_eq
    rw [h, rank_fin_fun]; norm_num
  have hsphere : IsPreconnected (Metric.sphere c 1 : Set R3) := isPreconnected_sphere hrank c 1
  have hIoi : IsPreconnected (Ioi r : Set ℝ) := isPreconnected_Ioi
  have hprod : IsPreconnected ((Metric.sphere c 1 : Set R3) ×ˢ (Ioi r : Set ℝ)) := hsphere.prod hIoi
  have hcont : Continuous (fun p : R3 × ℝ => c + p.2 • (p.1 - c)) := by fun_prop
  have himg : IsPreconnected ((fun p : R3 × ℝ => c + p.2 • (p.1 - c)) ''
      ((Metric.sphere c 1 : Set R3) ×ˢ (Ioi r : Set ℝ))) := hprod.image _ hcont.continuousOn
  have hset : (fun p : R3 × ℝ => c + p.2 • (p.1 - c)) ''
      ((Metric.sphere c 1 : Set R3) ×ˢ (Ioi r : Set ℝ)) = (Metric.closedBall c r)ᶜ := by
    ext z
    constructor
    · intro hz
      rw [mem_image] at hz
      obtain ⟨⟨u, t⟩, ⟨hu, ht⟩, rfl⟩ := hz
      rw [mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
      rw [Metric.mem_sphere, dist_eq_norm] at hu
      rw [hu, mul_one, Real.norm_eq_abs]
      exact not_le.mpr (lt_abs.mpr (Or.inl ht))
    · intro hz
      rw [mem_compl_iff, Metric.mem_closedBall, dist_eq_norm] at hz
      have hrlt : r < ‖z - c‖ := not_le.mp hz
      have hpos : (0 : ℝ) < ‖z - c‖ := lt_of_le_of_lt hr hrlt
      rw [mem_image]
      refine ⟨(c + ‖z - c‖⁻¹ • (z - c), ‖z - c‖), ⟨?_, hrlt⟩, ?_⟩
      · rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hpos.ne']
      · dsimp only
        rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul, add_sub_cancel]
  rwa [hset] at himg

/-- **The part of the ray from `c` through `y` beyond `y` avoids a convex set containing `c`.**
If `y ∉ K` and `c ∈ K` with `K` convex, then `c + t • (y - c) ∉ K` for every `t ≥ 1`: otherwise
`y`, which is the convex combination `c + t⁻¹ • (c + t • (y - c) - c)` of `c` and that point,
would lie in `K`. -/
theorem raySet_subset_compl {K : Set R3} (hKcv : Convex ℝ K) {c : R3} (hc : c ∈ K)
    {y : R3} (hy : y ∉ K) : raySet c y ⊆ Kᶜ := by
  rw [raySet]
  rintro z ⟨t, ht, rfl⟩ hzK
  apply hy
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have h1 : (0 : ℝ) ≤ 1 / t := by positivity
  have hle : 1 / t ≤ 1 := by rw [div_le_one ht0]; exact ht
  have hmem : c + (1 / t) • ((c + t • (y - c)) - c) ∈ K := hKcv.add_smul_sub_mem hc hzK ⟨h1, hle⟩
  rwa [add_sub_cancel_left, smul_smul, div_mul_cancel₀ 1 ht0.ne', one_smul, add_sub_cancel] at hmem

/-- **The complement of a compact convex set with nonempty interior in `ℝ³` is preconnected.**

The exterior `H` of a closed ball containing `K` is a preconnected subset of `Kᶜ`, and every point
`y ∈ Kᶜ` is joined to `H` by the ray `raySet c y` (which lies in `Kᶜ`).  Hence `Kᶜ` is a union of
preconnected sets all meeting `H`, so it is preconnected. -/
theorem isPreconnected_compl_of_compact_convex {K : Set R3} (hKc : IsCompact K)
    (hKcv : Convex ℝ K) (hKi : (interior K).Nonempty) : IsPreconnected Kᶜ := by
  obtain ⟨c, hcint⟩ := hKi
  have hcK : c ∈ K := interior_subset hcint
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hKc.isBounded
  have hR : (0 : ℝ) ≤ C := by simpa using hC hcK hcK
  have hKsub : K ⊆ Metric.closedBall c C := by
    intro z hzK
    rw [Metric.mem_closedBall, dist_comm]
    exact hC hcK hzK
  set H : Set R3 := (Metric.closedBall c C)ᶜ with hHdef
  have hHpc : IsPreconnected H := isPreconnected_compl_closedBall c hR
  have hHsub : H ⊆ Kᶜ := fun z hz hzK => hz (hKsub hzK)
  have hHne : H.Nonempty := by
    obtain ⟨w, hw⟩ := exists_ne (0 : R3)
    have hwn : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
    refine ⟨c + ((C + 1) / ‖w‖) • w, ?_⟩
    rw [hHdef, mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) hwn.le),
      div_mul_cancel₀ (C + 1) hwn.ne']
    linarith
  have hApc : ∀ y : ↥(Kᶜ), IsPreconnected (raySet c (y : R3)) :=
    fun y => isPreconnected_raySet c (y : R3)
  have hAsub : ∀ y : ↥(Kᶜ), raySet c (y : R3) ⊆ Kᶜ :=
    fun y => raySet_subset_compl hKcv hcK y.2
  have hAH : ∀ y : ↥(Kᶜ), (raySet c (y : R3) ∩ H).Nonempty := by
    intro y
    have hyne : (y : R3) ≠ c := fun h => y.2 (h ▸ hcK)
    have hd : (0 : ℝ) < ‖(y : R3) - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyne)
    refine ⟨c + max 1 ((C + 1) / ‖(y : R3) - c‖) • ((y : R3) - c), ?_, ?_⟩
    · rw [mem_raySet]
      exact ⟨_, le_max_left _ _, rfl⟩
    · rw [hHdef, mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one (le_max_left _ _))]
      have hbound : (C + 1) / ‖(y : R3) - c‖ * ‖(y : R3) - c‖
          ≤ max 1 ((C + 1) / ‖(y : R3) - c‖) * ‖(y : R3) - c‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
      rw [div_mul_cancel₀ (C + 1) hd.ne'] at hbound
      exact not_le.mpr (lt_of_lt_of_le (by linarith) hbound)
  have hmain : IsPreconnected (⋃ y : ↥(Kᶜ), (H ∪ raySet c (y : R3))) := by
    apply isPreconnected_iUnion
    · obtain ⟨p, hp⟩ := hHne
      exact ⟨p, Set.mem_iInter.mpr (fun y => Or.inl hp)⟩
    · intro y
      obtain ⟨p, hpA, hpH⟩ := hAH y
      exact IsPreconnected.union p hpH hpA hHpc (hApc y)
  have hset : (⋃ y : ↥(Kᶜ), (H ∪ raySet c (y : R3))) = Kᶜ := by
    apply Subset.antisymm
    · intro z hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨y, hy⟩ := hz
      rcases hy with hyH | hyA
      · exact hHsub hyH
      · exact hAsub y hyA
    · intro z hz
      rw [Set.mem_iUnion]
      refine ⟨⟨z, hz⟩, ?_⟩
      right
      rw [mem_raySet]
      exact ⟨1, le_refl 1, by rw [one_smul, add_sub_cancel]⟩
  rwa [hset] at hmain

theorem sphereSides_of_convexFrontier {K : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hKc : IsCompact K) (hKcv : Convex ℝ K) (hKi : (interior K).Nonempty) :
    Nonempty (Work.JordanBrouwer3.SphereSides (frontier K)) := by
  have hVne : (Kᶜ).Nonempty := by
    obtain ⟨c, hcint⟩ := hKi
    have hcK : c ∈ K := interior_subset hcint
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hKc.isBounded
    have hR : (0 : ℝ) ≤ C := by simpa using hC hcK hcK
    obtain ⟨w, hw⟩ := exists_ne (0 : R3)
    have hwn : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
    refine ⟨c + ((C + 1) / ‖w‖) • w, ?_⟩
    rw [mem_compl_iff]
    intro hzK
    have hle := hC hcK hzK
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (by linarith) hwn.le), div_mul_cancel₀ (C + 1) hwn.ne'] at hle
    linarith
  refine ⟨{ U := interior K
            V := Kᶜ
            isOpen_U := isOpen_interior
            isOpen_V := hKc.isClosed.isOpen_compl
            disjoint := (disjoint_compl_right (a := K)).mono_left interior_subset
            cover := by rw [hKc.isClosed.frontier_eq, Set.compl_sdiff]
            nonempty_U := hKi
            nonempty_V := hVne
            isBounded_U := hKc.isBounded.subset interior_subset
            isBounded_S := hKc.isBounded.subset
              (frontier_subset_closure.trans (le_of_eq hKc.isClosed.closure_eq))
            frontier_U := by
              rw [IsOpen.frontier_eq isOpen_interior, hKc.isClosed.frontier_eq,
                hKcv.closure_interior_eq_closure_of_nonempty_interior hKi, hKc.isClosed.closure_eq]
            frontier_V := frontier_compl K
            isPreconnected_U := hKcv.interior.isPreconnected
            isPreconnected_V := isPreconnected_compl_of_compact_convex hKc hKcv hKi }⟩

end

end Work.JordanBrouwer3
