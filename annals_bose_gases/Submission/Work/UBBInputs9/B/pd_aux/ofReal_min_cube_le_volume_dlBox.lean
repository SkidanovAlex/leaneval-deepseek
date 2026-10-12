import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Analysis.Clamp.abs_clamp_sub_le
import Submission.Work.UBBInputs9.B.pd_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs9.B.pd_aux

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory

/-- Membership in the centred cube `acube γ` by absolute values of the coordinates. -/
lemma mem_acube_iff_abs_coord (γ : ℝ) (y : ℝ³) :
    y ∈ Submission.BoseGases.acube γ ↔ ∀ i : Fin 3, |y i| ≤ γ / 2 := by
  simp only [Submission.BoseGases.mem_acube_iff, Set.mem_Icc, abs_le, neg_div]

/-- **A sliding small box that meets the inner cube `acube (ℓ/2)` has volume `≥ (min (ℓ/4) (ℓ*d/2))³`.**

For `ℓ, d > 0` and `u z : ℝ³` with `z ∈ dlBox ℓ d u` (`= acube ℓ ∩ ((ℓ*d)•u + acube (ℓ*d))`)
and `|z i| ≤ ℓ/4` for all `i`, the Lebesgue volume of `dlBox ℓ d u` is at least
`ENNReal.ofReal ((min (ℓ/4) (ℓ*d/2))^3)`.

(The module `Submission.DLInfra` defines `Submission.BoseGases.dlBox`; `Submission.CentreBox`
defines `Submission.BoseGases.acube`, `acube_measurable`, `acube_volume`.  Both are already in
the import closure of `Submission.Work.UBBInputs9.B.pd_defs`, as is `Submission.BoseGases.mem_dlBox_iff`
(`x ∈ dlBox ℓ d u ↔ x ∈ acube ℓ ∧ x - (ℓ*d)•u ∈ acube (ℓ*d)`).)

HINT.  Put `γ := min (ℓ/4) (ℓ*d/2)`, `w := (ℓ*d) • u` and take the coordinatewise *clamp*
`z' : ℝ³ := fun i => max (w i - ℓ*d/2 + γ/2) (min (w i + ℓ*d/2 - γ/2) (z i))`, and
`C := {y : ℝ³ | y - z' ∈ acube γ}` (the translate `z' + acube γ` of a cube of side `γ`).
One has `0 < γ`, `γ ≤ ℓ/4`, `γ ≤ ℓ*d/2 ≤ ℓ*d`.  Facts (all coordinatewise):
* from `z ∈ dlBox ℓ d u`: `|z i| ≤ ℓ/2` and `|z i - w i| ≤ ℓ*d/2`;
* `z' i ∈ [w i - ℓ*d/2 + γ/2, w i + ℓ*d/2 - γ/2]`, so `|z' i - w i| ≤ ℓ*d/2 - γ/2`;
* `|z' i - z i| ≤ γ/2` (the clamp moves `z i` by at most `γ/2`);
* for `y ∈ C`: `|y i - z' i| ≤ γ/2`; hence `|y i - w i| ≤ ℓ*d/2`, so
  `y - w ∈ acube (ℓ*d)`; and `|y i| ≤ |z' i| + γ/2 ≤ |z i| + γ ≤ ℓ/4 + ℓ/4 = ℓ/2`, so
  `y ∈ acube ℓ`.  Together `y ∈ dlBox ℓ d u`, i.e. `C ⊆ dlBox ℓ d u`.
* `measure_mono` gives `volume C ≤ volume (dlBox ℓ d u)`, and
  `C = (fun y => (-z') + y) ⁻¹' acube γ`, so `volume C = volume (acube γ)` by
  `MeasureTheory.measure_preimage_add` (with `μ := volume`, `IsAddLeftInvariant`), which is
  `ENNReal.ofReal (γ^3)` by `Submission.BoseGases.acube_volume γ γ_nonneg`. -/
theorem ofReal_min_cube_le_volume_dlBox {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    ∀ (u z : EuclideanSpace ℝ (Fin 3)), z ∈ Submission.BoseGases.dlBox ℓ d u →
      (∀ i : Fin 3, |z i| ≤ ℓ / 4) →
        ENNReal.ofReal ((min (ℓ / 4) (ℓ * d / 2)) ^ 3) ≤
          (volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
            (Submission.BoseGases.dlBox ℓ d u) := by
  intro u z hz hz4
  -- the side length of the inner cube
  have hℓ4 : 0 < ℓ / 4 := by linarith
  have hLpos : 0 < ℓ * d / 2 := by
    have : 0 < ℓ * d := mul_pos hℓ hd
    linarith
  set γ : ℝ := min (ℓ / 4) (ℓ * d / 2) with hγdef
  have hγpos : 0 < γ := by rw [hγdef]; exact lt_min hℓ4 hLpos
  have hγ4 : γ ≤ ℓ / 4 := by rw [hγdef]; exact min_le_left _ _
  have hγld : γ ≤ ℓ * d := by
    have : γ ≤ ℓ * d / 2 := by rw [hγdef]; exact min_le_right _ _
    linarith
  -- coordinatewise consequences of `z ∈ dlBox ℓ d u`
  rw [Submission.BoseGases.mem_dlBox_iff] at hz
  have hz2 : ∀ i : Fin 3, |z i - ((ℓ * d) • u) i| ≤ ℓ * d / 2 := fun i => by
    have h := (Submission.BoseGases.mem_acube_iff (ℓ * d) (z - (ℓ * d) • u)).mp hz.2 i
    have hsub : (z - (ℓ * d) • u) i = z i - ((ℓ * d) • u) i := by
      simp only [PiLp.sub_apply]
    rw [hsub] at h
    exact abs_le.mpr ⟨by linarith [h.1], h.2⟩
  -- the clamped point `z'`, nearest point of the small cube around `(ℓ*d)•u` to `z`
  let z' : ℝ³ := WithLp.toLp 2 (fun i : Fin 3 =>
    max (((ℓ * d) • u) i - ℓ * d / 2 + γ / 2)
        (min (((ℓ * d) • u) i + ℓ * d / 2 - γ / 2) (z i)))
  have hz'c : ∀ i : Fin 3, z' i = max (((ℓ * d) • u) i - ℓ * d / 2 + γ / 2)
      (min (((ℓ * d) • u) i + ℓ * d / 2 - γ / 2) (z i)) := fun _ => rfl
  have hz'lo : ∀ i : Fin 3, ((ℓ * d) • u) i - ℓ * d / 2 + γ / 2 ≤ z' i := fun i => by
    rw [hz'c i]; exact le_max_left _ _
  have hz'hi : ∀ i : Fin 3, z' i ≤ ((ℓ * d) • u) i + ℓ * d / 2 - γ / 2 := fun i => by
    rw [hz'c i]; exact max_le (by linarith [hγld]) (min_le_left _ _)
  have hz'w : ∀ i : Fin 3, |z' i - ((ℓ * d) • u) i| ≤ ℓ * d / 2 - γ / 2 := fun i =>
    abs_le.mpr ⟨by linarith [hz'lo i], by linarith [hz'hi i]⟩
  have hz'z : ∀ i : Fin 3, |z' i - z i| ≤ γ / 2 := fun i => by
    have h2 := abs_le.mp (hz2 i)
    have h := Work.Analysis.Clamp.abs_clamp_sub_le
      (lo := ((ℓ * d) • u) i - ℓ * d / 2 + γ / 2)
      (hi := ((ℓ * d) • u) i + ℓ * d / 2 - γ / 2) (t := z i) (γ := γ)
      (by linarith [hγld]) hγpos.le (by linarith [h2.1]) (by linarith [h2.2])
    rwa [hz'c i]
  -- the small cube `C = z' + acube γ`
  let C : Set ℝ³ := {y : ℝ³ | ∀ i : Fin 3, |y i - z' i| ≤ γ / 2}
  have hsub : C ⊆ Submission.BoseGases.dlBox ℓ d u := by
    intro y hy
    have hy' : ∀ i : Fin 3, |y i - z' i| ≤ γ / 2 := hy
    have hyw : ∀ i : Fin 3, |y i - ((ℓ * d) • u) i| ≤ ℓ * d / 2 := fun i => by
      have h1 : |y i - ((ℓ * d) • u) i| ≤ |y i - z' i| + |z' i - ((ℓ * d) • u) i| := by
        have heq : y i - ((ℓ * d) • u) i
            = (y i - z' i) + (z' i - ((ℓ * d) • u) i) := by ring
        rw [heq]; exact abs_add_le _ _
      linarith [h1, hy' i, hz'w i]
    have hyy : ∀ i : Fin 3, |y i| ≤ ℓ / 2 := fun i => by
      have h1 : |y i| ≤ |y i - z' i| + |z' i - z i| + |z i| := by
        have heq : y i = (y i - z' i) + (z' i - z i) + z i := by ring
        calc |y i| = |(y i - z' i) + (z' i - z i) + z i| := congrArg abs heq
          _ ≤ |(y i - z' i) + (z' i - z i)| + |z i| := abs_add_le _ _
          _ ≤ |y i - z' i| + |z' i - z i| + |z i| := by
                linarith [abs_add_le (y i - z' i) (z' i - z i)]
      linarith [h1, hy' i, hz'z i, hz4 i, hγ4]
    rw [Submission.BoseGases.mem_dlBox_iff]
    refine ⟨?_, ?_⟩
    · rw [Submission.BoseGases.mem_acube_iff]
      intro i
      rw [Set.mem_Icc]
      exact ⟨by linarith [(abs_le.mp (hyy i)).1], (abs_le.mp (hyy i)).2⟩
    · rw [Submission.BoseGases.mem_acube_iff]
      intro i
      have hsub' : (y - (ℓ * d) • u) i = y i - ((ℓ * d) • u) i := by
        simp only [PiLp.sub_apply]
      rw [hsub']
      rw [Set.mem_Icc]
      exact ⟨by linarith [(abs_le.mp (hyw i)).1], (abs_le.mp (hyw i)).2⟩
  -- the volume of `C = z' + acube γ`
  have hvolC : (volume : Measure ℝ³) C = ENNReal.ofReal (γ ^ 3) := by
    have hset : C = (fun y : ℝ³ => (-z') + y) ⁻¹' Submission.BoseGases.acube γ := by
      ext y
      simp only [Set.mem_preimage, mem_acube_iff_abs_coord]
      constructor
      · intro hy i
        have hiff : ((-z') + y) i = y i - z' i := by
          simp only [PiLp.add_apply, PiLp.neg_apply]; ring
        rw [hiff]; exact hy i
      · intro hy i
        have hiff : ((-z') + y) i = y i - z' i := by
          simp only [PiLp.add_apply, PiLp.neg_apply]; ring
        have h := hy i
        rwa [hiff] at h
    rw [hset, measure_preimage_add volume (-z') (Submission.BoseGases.acube γ),
      Submission.BoseGases.acube_volume γ hγpos.le]
  calc ENNReal.ofReal (γ ^ 3) = (volume : Measure ℝ³) C := hvolC.symm
    _ ≤ (volume : Measure ℝ³) (Submission.BoseGases.dlBox ℓ d u) := measure_mono hsub

end Work.UBBInputs9.B.pd_aux
