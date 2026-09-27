import Mathlib
import Submission.Work.Drive.refTripleRows

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology
attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

/-- **The transport's disjointness and level data at block `0` of the reference triple** — the missing
unprimed companion of `Work.Drive.transport_disins_reference_block'` (which is stated for block `1`).
Same proof with the roles of blocks `0` and `1` interchanged (the three ingredient lemmas
`chartPert_rotCapping_ne_chartPert_rotCapping_of_small`,
`chartPert_rotCapping_ne_refBlock_of_small`, `disjoint_range_refBlock_config_refPlane`,
`levelOf_chartPert_rotCapping_ne_cblk` are generic in the block index).  This is the block-`0` half of
the hypotheses of `Work.Drive.refTriple_topBdryMeet_zero_iff` and of
`Work.Drive.refTripleAt_blockT6At_of_data`. -/
theorem transport_disins_reference_block0 {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQcont : Continuous Q) {β : ℝ} (hβpos : 0 < β)
    (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → Work.Drive.levelOf (Q z) ≤ β)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam) (hβlam : β < lam)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Work.Drive.Zc γ →
      Disjoint (Work.Drive.chartDisk Q) (Work.Drive.rotCapping w '' Work.Drive.chartDisk Q))
    {u v : UnitAddCircle} (huv : v - u ∈ Work.Drive.Zc γ) (c : ℝ) (hc : 0 < c)
    (hcbot : ∀ z : ℂ, ‖z‖ ≤ 1 → c < Work.Drive.levelOf (Q z)) {cblk : Fin 3 → ℝ}
    (hcblk : cblk 2 = c / 4) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < r →
      (∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 →
        Work.Drive.chartPert (Work.Drive.blk 0 t) (Work.Drive.rotCapping u (Q z))
          ≠ Work.Drive.refBlock (fun s p => Work.Drive.chartPert s p) Q
              (Work.Drive.refPlanePres φ lam hlam) u v t 1 y) ∧
      (∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 →
        Work.Drive.chartPert (Work.Drive.blk 0 t) (Work.Drive.rotCapping u (Q z))
          ≠ Work.Drive.refBlock (fun s p => Work.Drive.chartPert s p) Q
              (Work.Drive.refPlanePres φ lam hlam) u v t 2 y) ∧
      Disjoint (Set.range (Work.Drive.refBlock (fun s p => Work.Drive.chartPert s p) Q
          (Work.Drive.refPlanePres φ lam hlam) u v t 1))
        (Set.range (Work.Drive.refBlock (fun s p => Work.Drive.chartPert s p) Q
          (Work.Drive.refPlanePres φ lam hlam) u v t 2)) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 →
        Work.Drive.levelOf (Work.Drive.chartPert (Work.Drive.blk 0 t)
          (Work.Drive.rotCapping u (Q z))) ≠ cblk 2) := by
  obtain ⟨r₁, hr₁, h₁⟩ :=
    chartPert_rotCapping_ne_chartPert_rotCapping_of_small (hγne := hγne) (Q := Q) hQcont hdisjZc
      (u := u) (v := v) huv
  obtain ⟨r₂, hr₂, h₂⟩ : ∃ r : ℝ, 0 < r ∧ ∀ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < r →
      2 * ‖t‖ < Real.log (lam / β) := by
    refine ⟨Real.log (lam / β) / 4, ?_, ?_⟩
    · have h1 : 1 < lam / β := (one_lt_div hβpos).mpr hβlam
      have h2 : 0 < Real.log (lam / β) := Real.log_pos h1
      linarith
    · intro t ht
      linarith [norm_nonneg t]
  obtain ⟨r₃, hr₃, h₃⟩ : ∃ r : ℝ, 0 < r ∧ ∀ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < r →
      ‖t‖ < Real.log 4 :=
    ⟨Real.log 4, Real.log_pos (by norm_num), fun t ht => ht⟩
  refine ⟨min (min r₁ r₂) r₃, lt_min (lt_min hr₁ hr₂) hr₃, fun t ht => ?_⟩
  have ht₁ : ‖t‖ < r₁ :=
    lt_of_lt_of_le ht (le_trans (min_le_left (min r₁ r₂) r₃) (min_le_left r₁ r₂))
  have ht₂ : ‖t‖ < r₂ :=
    lt_of_lt_of_le ht (le_trans (min_le_left (min r₁ r₂) r₃) (min_le_right r₁ r₂))
  have ht₃ : ‖t‖ < r₃ := lt_of_lt_of_le ht (min_le_right (min r₁ r₂) r₃)
  have hsmall : 2 * ‖t‖ < Real.log (lam / β) := h₂ t ht₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z y hz heq
    have h := h₁ (blk 0 t) (blk 1 t) (lt_of_le_of_lt (norm_blk_le 0 t) ht₁)
      (lt_of_le_of_lt (norm_blk_le 1 t) ht₁) z y hz
    rw [show refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 1 y
        = chartPert (blk 1 t) (rotCapping v (Q (sqDisk (foldBox y)))) from rfl] at heq
    exact h heq
  · intro z y hz
    exact chartPert_rotCapping_ne_refBlock_of_small hβpos hβ φ lam hlam hβlam u u v hsmall
      (k := 0) (by decide) z y hz
  · exact disjoint_range_refBlock_config_refPlane hβpos hβ φ lam hlam hβlam u v hsmall
      (k := 1) (by decide)
  · intro z hz
    exact levelOf_chartPert_rotCapping_ne_cblk c hc hcbot u hcblk (h₃ t ht₃) 0 z hz

end Work.Drive
