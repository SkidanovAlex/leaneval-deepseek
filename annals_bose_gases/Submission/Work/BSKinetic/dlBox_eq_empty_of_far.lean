import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BSKinetic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The sliding small box is empty far away from the origin

The `u`-indexed small box of the `dℓ`-localisation is

    `dlBox ℓ d u = acube ℓ ∩ ((ℓ·d)•u + acube (ℓ·d))`   (`DLInfra`),

the intersection of the big box `acube ℓ` with the box of side `ℓ·d` centred at `(ℓ·d)•u`.
The two boxes are congruent copies of `acube ℓ` and `acube (ℓ·d)`; they meet only if the
displacement `(ℓ·d)•u` is at most the sum of the two "radii" `√3·ℓ/2` and `√3·ℓ·d/2` of the
circumscribed balls, i.e. only if

    `ℓ·d·‖u‖ ≤ √3·ℓ/2 + √3·ℓ·d/2`,   equivalently   `‖u‖ ≤ √3·(1+d)/(2·d)`.

Hence for every `u` beyond the radius `√3*(1+d)/(2*d)` the box is empty.  This is the
"far vanishing" input of the sliding localisation: on that complement both factors of the
cutoff `chiB ℓ d u` vanish (`chiB_support_mem`), so every sliding word supported in
`dlBox ℓ d u` is zero there.
-/

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false

/-- A vector all of whose coordinates are bounded by `A` in absolute value has norm at most
`√3·A`. -/
private lemma norm_le_of_coord_le {A : ℝ} (hA : 0 ≤ A) {w : ℝ³}
    (hw : ∀ j : Fin 3, |w.ofLp j| ≤ A) : ‖w‖ ≤ Real.sqrt 3 * A :=
  coord_box_subset_eucl_ball hA hw

/-- **A point of the centred cube `acube ℓ` has norm at most `√3·ℓ/2`** (`ℓ > 0`): its
coordinates are bounded by `ℓ/2`. -/
lemma norm_le_of_mem_acube {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {x : ℝ³}
    (hx : x ∈ acube ℓ) : ‖x‖ ≤ Real.sqrt 3 * (ℓ / 2) := by
  refine norm_le_of_coord_le (by linarith) (fun j => ?_)
  have h := (mem_acube_iff ℓ x).mp hx j
  rw [Set.mem_Icc] at h
  rw [abs_le]
  exact ⟨by linarith [h.1], h.2⟩

/-- **Far vanishing, pointwise form.**  Any point `x` of the sliding small box
`dlBox ℓ d u = acube ℓ ∩ ((ℓ·d)•u + acube (ℓ·d))` forces
`‖u‖ ≤ √3*(1+d)/(2*d)`: indeed `‖x‖ ≤ √3·ℓ/2` and `‖x - (ℓ·d)•u‖ ≤ √3·ℓ·d/2`, so
`ℓ·d·‖u‖ ≤ ‖x‖ + ‖x - (ℓ·d)•u‖ ≤ √3·ℓ·(1+d)/2`. -/
lemma norm_le_of_mem_dlBox {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u x : ℝ³}
    (hx : x ∈ dlBox ℓ d u) : ‖u‖ ≤ Real.sqrt 3 * (1 + d) / (2 * d) := by
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  rw [dlBox, Set.mem_inter_iff] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hn1 : ‖x‖ ≤ Real.sqrt 3 * (ℓ / 2) := norm_le_of_mem_acube hℓ.le hx1
  have hn2 : ‖x - (ℓ * d) • u‖ ≤ Real.sqrt 3 * (ℓ * d / 2) :=
    norm_le_of_mem_acube hld.le hx2
  have ht : ‖(ℓ * d) • u‖ ≤ ‖x‖ + ‖x - (ℓ * d) • u‖ := by
    have hsplit : (ℓ * d) • u = x - (x - (ℓ * d) • u) :=
      (sub_sub_cancel x ((ℓ * d) • u)).symm
    nth_rewrite 1 [hsplit]
    exact norm_sub_le x (x - (ℓ * d) • u)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hld.le] at ht
  have hmain : ℓ * d * ‖u‖ ≤ Real.sqrt 3 * ℓ * (1 + d) / 2 := by
    have h3 : Real.sqrt 3 * ℓ * (1 + d) / 2
        = Real.sqrt 3 * (ℓ / 2) + Real.sqrt 3 * (ℓ * d / 2) := by ring
    rw [h3]
    linarith [ht, hn1, hn2]
  have hmain2 : d * ‖u‖ ≤ Real.sqrt 3 * (1 + d) / 2 := by
    have h : ℓ * (d * ‖u‖) ≤ ℓ * (Real.sqrt 3 * (1 + d) / 2) := by linarith [hmain]
    exact le_of_mul_le_mul_left h hℓ
  have hkey : ‖u‖ * (2 * d) ≤ Real.sqrt 3 * (1 + d) := by linarith [hmain2]
  exact (le_div_iff₀ (by linarith : (0 : ℝ) < 2 * d)).mpr hkey

theorem dlBox_eq_empty_of_far {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {u : EuclideanSpace ℝ (Fin 3)}
    (hu : Real.sqrt 3 * (1 + d) / (2 * d) < ‖u‖) :
    Submission.BoseGases.dlBox ℓ d u = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  exact absurd (norm_le_of_mem_dlBox hℓ hd hx) (not_le.mpr hu)

end Work.BSKinetic
