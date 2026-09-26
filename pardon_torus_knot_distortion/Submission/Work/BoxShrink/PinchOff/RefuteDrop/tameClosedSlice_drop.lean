import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.dropTrace
import Submission.Work.BoxShrink.PinchOff.closure_Sigma_sdiff_Sigma_subset_sphereTrace
import Submission.Work.RefuteDrop.psiA1_shape
import Submission.Work.RefuteDrop.psiB_shape
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.psiA2_shape_alt

/-!
# The slice of the `RefuteDrop` configuration is closed-tame

The closure of the slice `Σ = Sigma dropDiffeo dropS dropC dropCyc dropU` — the trace of the cutting
plane `{x = 0}` on the surface `dropDiffeo(F_std)` inside the box `PBox dropS dropC dropCyc` — is
the union of four arcs of the surface, namely the two arcs `γB [uB4, uB1 + 2π]` and
`γB [uB2, uB3]` of the `B` branch of the trace and the two arcs `γA [zA1, yA2]` and
`γA [zA3, yA4]` of the `A` branch, where the eight parameters are the crossings of the box window
computed in `dropTrace.lean` (with the shapes proved in the sibling modules `psiB_shape`,
`psiA1_shape`, `psiA2_shape`).  This proves the honest tameness predicate `TameClosedSlice` at the
configuration of `RefuteDrop/Config.lean`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff.RefuteDrop

noncomputable section

/-! ## Periodicity of the window functions and of the branches -/

theorem gammaB_add_int_mul_two_pi (u : ℝ) (k : ℤ) :
    gammaB (u + (k : ℝ) * (2 * Real.pi)) = gammaB u :=
  (Function.Periodic.int_mul (show Function.Periodic gammaB (2 * Real.pi) from gammaB_add_two_pi) k) u

theorem gammaA_add_int_mul_two_pi (u : ℝ) (k : ℤ) :
    gammaA (u + (k : ℝ) * (2 * Real.pi)) = gammaA u :=
  (Function.Periodic.int_mul (show Function.Periodic gammaA (2 * Real.pi) from gammaA_add_two_pi) k) u

theorem psiB_add_two_pi (u : ℝ) : psiB (u + 2 * Real.pi) = psiB u := by
  simp only [psiB, trN2, trB2, trA, trS, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem psiA1_add_two_pi (u : ℝ) : psiA1 (u + 2 * Real.pi) = psiA1 u := by
  simp only [psiA1, trN1, trB1, trA, trS, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem psiA2_add_two_pi (u : ℝ) : psiA2 (u + 2 * Real.pi) = psiA2 u := by
  simp only [psiA2, trN2, trB2, trA, trS, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem psiB_add_int_mul_two_pi (u : ℝ) (k : ℤ) :
    psiB (u + (k : ℝ) * (2 * Real.pi)) = psiB u :=
  (Function.Periodic.int_mul (show Function.Periodic psiB (2 * Real.pi) from psiB_add_two_pi) k) u

theorem psiA1_add_int_mul_two_pi (u : ℝ) (k : ℤ) :
    psiA1 (u + (k : ℝ) * (2 * Real.pi)) = psiA1 u :=
  (Function.Periodic.int_mul (show Function.Periodic psiA1 (2 * Real.pi) from psiA1_add_two_pi) k) u

theorem psiA2_add_int_mul_two_pi (u : ℝ) (k : ℤ) :
    psiA2 (u + (k : ℝ) * (2 * Real.pi)) = psiA2 u :=
  (Function.Periodic.int_mul (show Function.Periodic psiA2 (2 * Real.pi) from psiA2_add_two_pi) k) u

/-! ## The box windows in terms of the branch coordinates -/

theorem gammaB_boxNorm_iff (u : ℝ) :
    Submission.boxNorm dropC dropCyc (gammaB u) < dropS ↔ psiB u < 0 := by
  rw [boxNorm_gammaB, dropS]
  constructor
  · intro h
    rw [psiB_lt_iff]
    exact lt_of_le_of_lt (le_max_left _ _) h
  · intro h
    rw [psiB_lt_iff] at h
    refine max_lt h ?_
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^(1/3:ℝ))]
    have hy := branchB_y_bound u
    rw [yclip] at hy
    linarith

theorem gammaA_boxNorm_iff (u : ℝ) :
    Submission.boxNorm dropC dropCyc (gammaA u) < dropS ↔ (psiA1 u < 0 ∧ psiA2 u < 0) := by
  rw [boxNorm_gammaA, dropS]
  rw [max_lt_iff]
  have hc : (0:ℝ) < (2:ℝ)^(1/3:ℝ) := by positivity
  constructor
  · rintro ⟨h2, h1⟩
    refine ⟨?_, ?_⟩
    · rw [psiA1_lt_iff, yclip]
      rw [div_lt_iff₀ hc] at h1
      linarith [h1]
    · exact (psiA2_lt_iff u).mpr h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · exact (psiA2_lt_iff u).mp h2
    · rw [psiA1_lt_iff, yclip] at h1
      rw [div_lt_iff₀ hc]
      linarith [h1]

/-- A point of the `B` branch with the box condition holds lies on the slice. -/
theorem gammaB_mem_Sigma (u : ℝ) (h : psiB u < 0) :
    gammaB u ∈ Work.BoxShrink.PinchOff.Sigma dropDiffeo dropS dropC dropCyc dropU := by
  refine ⟨⟨gammaB_mem_carrier u, ?_⟩, gammaB_mem_plane u⟩
  exact (Submission.mem_PBox_iff dropS dropC dropCyc _).mpr ((gammaB_boxNorm_iff u).mpr h)

/-- A point of the `A` branch with both box conditions holds lies on the slice. -/
theorem gammaA_mem_Sigma (u : ℝ) (h : psiA1 u < 0 ∧ psiA2 u < 0) :
    gammaA u ∈ Work.BoxShrink.PinchOff.Sigma dropDiffeo dropS dropC dropCyc dropU := by
  refine ⟨⟨gammaA_mem_carrier u, ?_⟩, gammaA_mem_plane u⟩
  exact (Submission.mem_PBox_iff dropS dropC dropCyc _).mpr ((gammaA_boxNorm_iff u).mpr h)

/-- The image of a closed interval on which the slice condition holds strictly lies in the
closure of the slice. -/
theorem image_Icc_subset_closure {a b : ℝ} (hab : a < b) (f : ℝ → R3) (hf : Continuous f)
    {S : Set R3} (h : ∀ u ∈ Set.Ioo a b, f u ∈ S) :
    f '' Set.Icc a b ⊆ closure S := by
  have h1 : closure (f '' Set.Ioo a b) ⊆ closure S :=
    closure_mono (fun y hy => by
      rcases hy with ⟨u, hu, rfl⟩
      exact h u hu)
  have h2 : f '' Set.Icc a b ⊆ f '' closure (Set.Ioo a b) := by
    rw [closure_Ioo (ne_of_lt hab)]
  calc f '' Set.Icc a b ⊆ f '' closure (Set.Ioo a b) := h2
    _ ⊆ closure (f '' Set.Ioo a b) := image_closure_subset_closure_image hf
    _ ⊆ closure S := h1

/-! ## The shapes of the three window functions

These are the analytic inputs: the sign structure of the three window functions, established in the
sibling modules `psiB_shape`, `psiA1_shape`, `psiA2_shape`. -/

theorem psiB_shape_use :
    (0 < uB1 ∧ uB1 < uB2 ∧ uB2 < uB3 ∧ uB3 < uB4 ∧ uB4 < 2 * Real.pi) ∧
      (uB1 ∈ Set.Ioo (0:ℝ) (ang (7/10)) ∧ uB2 ∈ Set.Ioo (ang (9/10)) (ang 5) ∧
        uB3 ∈ Set.Ioo (2 * Real.pi - ang 400) (2 * Real.pi - ang (3/2)) ∧
        uB4 ∈ Set.Ioo (2 * Real.pi - ang (11/10)) (2 * Real.pi - ang (1/5))) ∧
      (∀ u : ℝ, u ∈ Set.Icc (0:ℝ) (2 * Real.pi) →
        (psiB u ≤ 0 ↔
          u ∈ Set.Icc (0:ℝ) uB1 ∪ Set.Icc uB2 uB3 ∪ Set.Icc uB4 (2 * Real.pi))) ∧
      (∀ u : ℝ, u ∈ Set.Icc (0:ℝ) (2 * Real.pi) →
        (psiB u < 0 ↔
          u ∈ Set.Ico (0:ℝ) uB1 ∪ Set.Ioo uB2 uB3 ∪ Set.Ioc uB4 (2 * Real.pi))) :=
  Work.RefuteDrop.psiB_shape

theorem psiA1_shape_use :
    (yA1 < yA2 ∧ yA2 < yA3 ∧ yA3 < yA4 ∧ yA4 < 2 * Real.pi) ∧
      (yA1 ∈ Set.Ioo (ang (7/10)) (ang (5/2)) ∧ yA2 ∈ Set.Ioo (ang (9/2)) (ang 14) ∧
        yA3 ∈ Set.Ioo (2 * Real.pi - ang (3/2)) (2 * Real.pi - ang (2/5)) ∧
        yA4 ∈ Set.Ioo (2 * Real.pi - ang (1/5)) (2 * Real.pi - ang (1/15))) ∧
      (∀ u : ℝ, u ∈ Set.Icc (0:ℝ) (2 * Real.pi) →
        (psiA1 u ≤ 0 ↔ u ∈ Set.Icc yA1 yA2 ∪ Set.Icc yA3 yA4)) ∧
      (∀ u : ℝ, u ∈ Set.Icc (0:ℝ) (2 * Real.pi) →
        (psiA1 u < 0 ↔ u ∈ Set.Ioo yA1 yA2 ∪ Set.Ioo yA3 yA4)) :=
  Work.RefuteDrop.psiA1_shape

theorem psiA2_shape_use :
    (zA1 < zA2 ∧ zA2 < zA3 ∧ zA3 < zA4 ∧ zA4 < 2 * Real.pi) ∧
      (zA1 ∈ Set.Ioo (ang (5/2)) (ang (9/2)) ∧ zA2 ∈ Set.Ioo (ang 14) (ang 400) ∧
        zA3 ∈ Set.Ioo (2 * Real.pi - ang (2/5)) (2 * Real.pi - ang (1/5)) ∧
        zA4 ∈ Set.Ioo (2 * Real.pi - ang (1/15)) (2 * Real.pi - ang (1/1000))) ∧
      (∀ u : ℝ, u ∈ Set.Icc (0:ℝ) (2 * Real.pi) →
        (psiA2 u ≤ 0 ↔ u ∈ Set.Icc zA1 zA2 ∪ Set.Icc zA3 zA4)) ∧
      (∀ u : ℝ, u ∈ Set.Icc (0:ℝ) (2 * Real.pi) →
        (psiA2 u < 0 ↔ u ∈ Set.Ioo zA1 zA2 ∪ Set.Ioo zA3 zA4)) :=
  Work.BoxShrink.PinchOff.RefuteDrop.ZShape.psiA2_shape

/-! ## The four arcs of the closed slice -/

/-- The arc of the `B` branch running from `uB4` across the seam to `2π + uB1`. -/
noncomputable def arcB0 : C(Work.Smooth.Plane.ArcInterval, R3) :=
  ⟨fun t => gammaB (uB4 + (t : ℝ) * (2 * Real.pi + uB1 - uB4)),
    continuous_gammaB.comp (continuous_const.add (continuous_subtype_val.mul continuous_const))⟩

/-- The arc of the `B` branch between `uB2` and `uB3`. -/
noncomputable def arcB1 : C(Work.Smooth.Plane.ArcInterval, R3) :=
  ⟨fun t => gammaB (uB2 + (t : ℝ) * (uB3 - uB2)),
    continuous_gammaB.comp (continuous_const.add (continuous_subtype_val.mul continuous_const))⟩

/-- The arc of the `A` branch between `zA1` and `yA2`. -/
noncomputable def arcA2 : C(Work.Smooth.Plane.ArcInterval, R3) :=
  ⟨fun t => gammaA (zA1 + (t : ℝ) * (yA2 - zA1)),
    continuous_gammaA.comp (continuous_const.add (continuous_subtype_val.mul continuous_const))⟩

/-- The arc of the `A` branch between `zA3` and `yA4`. -/
noncomputable def arcA3 : C(Work.Smooth.Plane.ArcInterval, R3) :=
  ⟨fun t => gammaA (zA3 + (t : ℝ) * (yA4 - zA3)),
    continuous_gammaA.comp (continuous_const.add (continuous_subtype_val.mul continuous_const))⟩

/-- The point of the slice. -/
abbrev dropSigma : Set R3 :=
  Work.BoxShrink.PinchOff.Sigma dropDiffeo dropS dropC dropCyc dropU

/-! ## The interior of each arc lies on the slice -/

theorem psiB_neg_on_gap0 {u : ℝ} (h : u ∈ Set.Ioo uB4 (2 * Real.pi + uB1)) : psiB u < 0 := by
  obtain ⟨hord, hbr, hle, hlt⟩ := psiB_shape_use
  obtain ⟨h1, h2, h3, h4, h5⟩ := hord
  rcases le_or_gt u (2 * Real.pi) with hu | hu
  · have huIcc : u ∈ Set.Icc (0:ℝ) (2 * Real.pi) := ⟨by linarith [h.1, h1], hu⟩
    exact (hlt u huIcc).mpr (Or.inr ⟨h.1, hu⟩)
  · have h3' : psiB (u - 2 * Real.pi) < 0 := by
      have huIcc : u - 2 * Real.pi ∈ Set.Icc (0:ℝ) (2 * Real.pi) :=
        ⟨by linarith, by linarith [h.2, h1]⟩
      exact (hlt (u - 2 * Real.pi) huIcc).mpr
        (Or.inl (Or.inl ⟨by linarith, by linarith [h.2]⟩))
    have h4' : psiB ((u - 2 * Real.pi) + (1:ℤ) * (2 * Real.pi)) = psiB (u - 2 * Real.pi) :=
      psiB_add_int_mul_two_pi (u - 2 * Real.pi) 1
    rw [show (u - 2 * Real.pi) + (1:ℤ) * (2 * Real.pi) = u by push_cast; ring] at h4'
    linarith [h3', h4']

theorem psiB_neg_on_gap1 {u : ℝ} (h : u ∈ Set.Ioo uB2 uB3) : psiB u < 0 := by
  obtain ⟨hord, hbr, hle, hlt⟩ := psiB_shape_use
  obtain ⟨h1, h2, h3, h4, h5⟩ := hord
  exact (hlt u ⟨by linarith [h.1, h1, h2, h3], by linarith [h.2, h5]⟩).mpr (Or.inl (Or.inr h))

theorem psiA_neg_on_gap2 {u : ℝ} (h : u ∈ Set.Ioo zA1 yA2) : psiA1 u < 0 ∧ psiA2 u < 0 := by
  obtain ⟨hord1, hbr1, hle1, hlt1⟩ := psiA1_shape_use
  obtain ⟨hord2, hbr2, hle2, hlt2⟩ := psiA2_shape_use
  obtain ⟨h11, h12, h13, h14⟩ := hord1
  obtain ⟨h21, h22, h23, h24⟩ := hord2
  obtain ⟨hb11, hb12, hb13, hb14⟩ := hbr1
  obtain ⟨hb21, hb22, hb23, hb24⟩ := hbr2
  have hz1pos : (0:ℝ) < zA1 :=
    lt_trans (ang_pos (show (0:ℝ) < 5/2 by norm_num)) hb21.1
  have hy2lt : yA2 < 2 * Real.pi := by
    have hp := ang_lt_pi (show (0:ℝ) < 14 by norm_num)
    linarith [hb12.2, hp, Real.pi_pos]
  have hy1z1 : yA1 < zA1 := by linarith [hb11.2, hb21.1]
  have hy2z2 : yA2 < zA2 := by linarith [hb12.2, hb22.1]
  have hmem1 : u ∈ Set.Icc (0:ℝ) (2 * Real.pi) :=
    ⟨le_of_lt (lt_trans hz1pos h.1), le_of_lt (lt_trans h.2 hy2lt)⟩
  refine ⟨?_, ?_⟩
  · exact (hlt1 u hmem1).mpr (Or.inl ⟨lt_trans hy1z1 h.1, h.2⟩)
  · exact (hlt2 u hmem1).mpr (Or.inl ⟨h.1, lt_trans h.2 hy2z2⟩)

theorem psiA_neg_on_gap3 {u : ℝ} (h : u ∈ Set.Ioo zA3 yA4) : psiA1 u < 0 ∧ psiA2 u < 0 := by
  obtain ⟨hord1, hbr1, hle1, hlt1⟩ := psiA1_shape_use
  obtain ⟨hord2, hbr2, hle2, hlt2⟩ := psiA2_shape_use
  obtain ⟨h11, h12, h13, h14⟩ := hord1
  obtain ⟨h21, h22, h23, h24⟩ := hord2
  obtain ⟨hb11, hb12, hb13, hb14⟩ := hbr1
  obtain ⟨hb21, hb22, hb23, hb24⟩ := hbr2
  have hz3pos : (0:ℝ) < zA3 := by
    have hp := ang_lt_pi (show (0:ℝ) < 2/5 by norm_num)
    linarith [hb23.1, hp, Real.pi_pos]
  have hy4lt : yA4 < 2 * Real.pi := by
    have hp := ang_pos (show (0:ℝ) < 1/15 by norm_num)
    linarith [hb14.2, hp]
  have hy3z3 : yA3 < zA3 := by linarith [hb13.2, hb23.1]
  have hy4z4 : yA4 < zA4 := by linarith [hb14.2, hb24.1]
  have hmem1 : u ∈ Set.Icc (0:ℝ) (2 * Real.pi) :=
    ⟨le_of_lt (lt_trans hz3pos h.1), le_of_lt (lt_trans h.2 hy4lt)⟩
  refine ⟨?_, ?_⟩
  · exact (hlt1 u hmem1).mpr (Or.inr ⟨lt_trans hy3z3 h.1, h.2⟩)
  · exact (hlt2 u hmem1).mpr (Or.inr ⟨h.1, lt_trans h.2 hy4z4⟩)

/-! ## The arcs lie in the closure of the slice -/

theorem arcB0_mem (t : Work.Smooth.Plane.ArcInterval) : arcB0 t ∈ closure dropSigma := by
  obtain ⟨hord, hbr, hle, hlt⟩ := psiB_shape_use
  obtain ⟨h1, h2, h3, h4, h5⟩ := hord
  have hlt' : uB4 < 2 * Real.pi + uB1 := by linarith
  have hsub := image_Icc_subset_closure hlt' gammaB continuous_gammaB
    (S := dropSigma) (fun u hu => gammaB_mem_Sigma u (psiB_neg_on_gap0 hu))
  refine hsub ⟨uB4 + (t : ℝ) * (2 * Real.pi + uB1 - uB4),
    ⟨by have := t.2.1; nlinarith, by have := t.2.2; nlinarith⟩, rfl⟩

theorem arcB1_mem (t : Work.Smooth.Plane.ArcInterval) : arcB1 t ∈ closure dropSigma := by
  obtain ⟨hord, hbr, hle, hlt⟩ := psiB_shape_use
  obtain ⟨h1, h2, h3, h4, h5⟩ := hord
  have hsub := image_Icc_subset_closure h3 gammaB continuous_gammaB
    (S := dropSigma) (fun u hu => gammaB_mem_Sigma u (psiB_neg_on_gap1 hu))
  refine hsub ⟨uB2 + (t : ℝ) * (uB3 - uB2), ⟨by have := t.2.1; nlinarith, by have := t.2.2; nlinarith⟩, rfl⟩

theorem arcA2_mem (t : Work.Smooth.Plane.ArcInterval) : arcA2 t ∈ closure dropSigma := by
  obtain ⟨hord1, hbr1, hle1, hlt1⟩ := psiA1_shape_use
  obtain ⟨hord2, hbr2, hle2, hlt2⟩ := psiA2_shape_use
  obtain ⟨h11, h12, h13, h14⟩ := hord1
  obtain ⟨h21, h22, h23, h24⟩ := hord2
  obtain ⟨hb11, hb12, hb13, hb14⟩ := hbr1
  obtain ⟨hb21, hb22, hb23, hb24⟩ := hbr2
  have hz1y2 : zA1 < yA2 := by
    have h := ang_lt_ang (show (5/2 : ℝ) < 9/2 by norm_num)
    exact lt_of_lt_of_le hb21.2 (le_of_lt hb12.1)
  have hsub := image_Icc_subset_closure hz1y2 gammaA continuous_gammaA
    (S := dropSigma) (fun u hu => gammaA_mem_Sigma u (psiA_neg_on_gap2 hu))
  refine hsub ⟨zA1 + (t : ℝ) * (yA2 - zA1),
    ⟨by have := t.2.1; nlinarith, by have := t.2.2; nlinarith⟩, rfl⟩

theorem arcA3_mem (t : Work.Smooth.Plane.ArcInterval) : arcA3 t ∈ closure dropSigma := by
  obtain ⟨hord1, hbr1, hle1, hlt1⟩ := psiA1_shape_use
  obtain ⟨hord2, hbr2, hle2, hlt2⟩ := psiA2_shape_use
  obtain ⟨h11, h12, h13, h14⟩ := hord1
  obtain ⟨h21, h22, h23, h24⟩ := hord2
  obtain ⟨hb11, hb12, hb13, hb14⟩ := hbr1
  obtain ⟨hb21, hb22, hb23, hb24⟩ := hbr2
  have hz3y4 : zA3 < yA4 := by
    have h := ang_lt_ang (show (1/5 : ℝ) < 1 by norm_num)
    exact lt_of_lt_of_le hb23.2 (le_of_lt hb14.1)
  have hsub := image_Icc_subset_closure hz3y4 gammaA continuous_gammaA
    (S := dropSigma) (fun u hu => gammaA_mem_Sigma u (psiA_neg_on_gap3 hu))
  refine hsub ⟨zA3 + (t : ℝ) * (yA4 - zA3),
    ⟨by have := t.2.1; nlinarith, by have := t.2.2; nlinarith⟩, rfl⟩

/-! ## The closure of the slice -/

/-- **A point of the closure of the slice lies on the surface, in the cutting plane, and in the
closed box.** -/
theorem mem_closure_Sigma (x : R3) (hx : x ∈ closure dropSigma) :
    x ∈ (Work.Smooth.Morse.torus dropDiffeo).carrier ∧
      x (dropCyc 2) = dropC (dropCyc 2) + dropU ∧
      Submission.boxNorm dropC dropCyc x ≤ dropS := by
  have hSig : dropSigma =
      ((Work.Smooth.Morse.torus dropDiffeo).carrier ∩ Submission.PBox dropS dropC dropCyc)
        ∩ Work.BoxShrink.Core.cutPlane dropC dropCyc dropU := rfl
  rw [hSig] at hx
  have hAB := (closure_inter_subset hx).1
  have hcar : x ∈ closure (Work.Smooth.Morse.torus dropDiffeo).carrier :=
    (closure_inter_subset hAB).1
  have hbox : x ∈ closure (Submission.PBox dropS dropC dropCyc) :=
    (closure_inter_subset hAB).2
  have hcut : x ∈ closure (Work.BoxShrink.Core.cutPlane dropC dropCyc dropU) :=
    (closure_inter_subset hx).2
  refine ⟨?_, ?_, ?_⟩
  · rwa [IsClosed.closure_eq ((Work.Smooth.Morse.Surface.isCompact_torus dropDiffeo).isClosed)]
      at hcar
  · rw [(Work.BoxShrink.Core.isClosed_cutPlane dropC dropCyc dropU).closure_eq] at hcut
    exact hcut
  · exact Work.BoxShrink.PinchOff.closure_PBox_subset_boxNorm_le dropS dropC dropCyc hbox

/-- Reducing a parameter modulo `2π`. -/
theorem exists_reduce (u : ℝ) :
    ∃ k : ℤ, u - (k:ℝ) * (2 * Real.pi) ∈ Set.Ico (0:ℝ) (2 * Real.pi) := by
  refine ⟨⌊u / (2 * Real.pi)⌋, ?_, ?_⟩
  · have ht : (0:ℝ) < 2 * Real.pi := by positivity
    have h := Int.floor_le (u / (2 * Real.pi))
    rw [le_div_iff₀ ht] at h
    show (0:ℝ) ≤ u - (⌊u / (2 * Real.pi)⌋ : ℤ) * (2 * Real.pi)
    push_cast
    linarith
  · have ht : (0:ℝ) < 2 * Real.pi := by positivity
    have h := Int.lt_floor_add_one (u / (2 * Real.pi))
    rw [div_lt_iff₀ ht] at h
    show u - (⌊u / (2 * Real.pi)⌋ : ℤ) * (2 * Real.pi) < 2 * Real.pi
    push_cast at h ⊢
    linarith

/-! ## The arcs cover the intervals -/

theorem mem_range_arcB0 {u : ℝ} (hu : u ∈ Set.Icc uB4 (2 * Real.pi + uB1)) :
    gammaB u ∈ Set.range arcB0 := by
  obtain ⟨hord, hbr, hle, hlt⟩ := psiB_shape_use
  obtain ⟨h1, h2, h3, h4, h5⟩ := hord
  have hlen : (0:ℝ) < 2 * Real.pi + uB1 - uB4 := by linarith
  refine ⟨⟨(u - uB4) / (2 * Real.pi + uB1 - uB4), ⟨?_, ?_⟩⟩, ?_⟩
  · exact div_nonneg (by linarith [hu.1]) (le_of_lt hlen)
  · rw [div_le_one hlen]; linarith [hu.2]
  · show gammaB (uB4 + ((u - uB4) / (2 * Real.pi + uB1 - uB4)) * (2 * Real.pi + uB1 - uB4))
      = gammaB u
    rw [div_mul_cancel₀ _ (ne_of_gt hlen)]
    rw [show uB4 + (u - uB4) = u by ring]

theorem mem_range_arcB1 {u : ℝ} (hu : u ∈ Set.Icc uB2 uB3) :
    gammaB u ∈ Set.range arcB1 := by
  obtain ⟨hord, hbr, hle, hlt⟩ := psiB_shape_use
  obtain ⟨h1, h2, h3, h4, h5⟩ := hord
  have hlen : (0:ℝ) < uB3 - uB2 := by linarith
  refine ⟨⟨(u - uB2) / (uB3 - uB2), ⟨?_, ?_⟩⟩, ?_⟩
  · exact div_nonneg (by linarith [hu.1]) (le_of_lt hlen)
  · rw [div_le_one hlen]; linarith [hu.2]
  · show gammaB (uB2 + ((u - uB2) / (uB3 - uB2)) * (uB3 - uB2)) = gammaB u
    rw [div_mul_cancel₀ _ (ne_of_gt hlen)]
    rw [show uB2 + (u - uB2) = u by ring]

theorem mem_range_arcA2 {u : ℝ} (hu : u ∈ Set.Icc zA1 yA2) :
    gammaA u ∈ Set.range arcA2 := by
  obtain ⟨hord1, hbr1, hle1, hlt1⟩ := psiA1_shape_use
  obtain ⟨hord2, hbr2, hle2, hlt2⟩ := psiA2_shape_use
  obtain ⟨h11, h12, h13, h14⟩ := hord1
  obtain ⟨h21, h22, h23, h24⟩ := hord2
  obtain ⟨hb11, hb12, hb13, hb14⟩ := hbr1
  obtain ⟨hb21, hb22, hb23, hb24⟩ := hbr2
  have hz1y2 : zA1 < yA2 := by linarith [hb21.2, hb12.1]
  have hlen : (0:ℝ) < yA2 - zA1 := by linarith
  refine ⟨⟨(u - zA1) / (yA2 - zA1), ⟨?_, ?_⟩⟩, ?_⟩
  · exact div_nonneg (by linarith [hu.1]) (le_of_lt hlen)
  · rw [div_le_one hlen]; linarith [hu.2]
  · show gammaA (zA1 + ((u - zA1) / (yA2 - zA1)) * (yA2 - zA1)) = gammaA u
    rw [div_mul_cancel₀ _ (ne_of_gt hlen)]
    rw [show zA1 + (u - zA1) = u by ring]

theorem mem_range_arcA3 {u : ℝ} (hu : u ∈ Set.Icc zA3 yA4) :
    gammaA u ∈ Set.range arcA3 := by
  obtain ⟨hord1, hbr1, hle1, hlt1⟩ := psiA1_shape_use
  obtain ⟨hord2, hbr2, hle2, hlt2⟩ := psiA2_shape_use
  obtain ⟨h11, h12, h13, h14⟩ := hord1
  obtain ⟨h21, h22, h23, h24⟩ := hord2
  obtain ⟨hb11, hb12, hb13, hb14⟩ := hbr1
  obtain ⟨hb21, hb22, hb23, hb24⟩ := hbr2
  have hz3y4 : zA3 < yA4 := by linarith [hb23.2, hb14.1]
  have hlen : (0:ℝ) < yA4 - zA3 := by linarith
  refine ⟨⟨(u - zA3) / (yA4 - zA3), ⟨?_, ?_⟩⟩, ?_⟩
  · exact div_nonneg (by linarith [hu.1]) (le_of_lt hlen)
  · rw [div_le_one hlen]; linarith [hu.2]
  · show gammaA (zA3 + ((u - zA3) / (yA4 - zA3)) * (yA4 - zA3)) = gammaA u
    rw [div_mul_cancel₀ _ (ne_of_gt hlen)]
    rw [show zA3 + (u - zA3) = u by ring]

/-! ## The tameness theorem -/

theorem tameClosedSlice_drop :
    Work.BoxShrink.PinchOff.TameClosedSlice
      Work.BoxShrink.PinchOff.RefuteDrop.dropDiffeo
      Work.BoxShrink.PinchOff.RefuteDrop.dropS
      Work.BoxShrink.PinchOff.RefuteDrop.dropC
      Work.BoxShrink.PinchOff.RefuteDrop.dropCyc
      Work.BoxShrink.PinchOff.RefuteDrop.dropU := by
  obtain ⟨hBord, hBbr, hBle, hBlt⟩ := psiB_shape_use
  obtain ⟨hA1ord, hA1br, hA1le, hA1lt⟩ := psiA1_shape_use
  obtain ⟨hA2ord, hA2br, hA2le, hA2lt⟩ := psiA2_shape_use
  obtain ⟨hB1, hB2, hB3, hB4, hB5⟩ := hBord
  obtain ⟨hA11, hA12, hA13, hA14⟩ := hA1ord
  obtain ⟨hA21, hA22, hA23, hA24⟩ := hA2ord
  obtain ⟨hb11, hb12, hb13, hb14⟩ := hA1br
  obtain ⟨hb21, hb22, hb23, hb24⟩ := hA2br
  have hy1z1 : yA1 < zA1 := by linarith [hb11.2, hb21.1]
  have hz1y2 : zA1 < yA2 := by linarith [hb21.2, hb12.1]
  have hy2z2 : yA2 < zA2 := by linarith [hb12.2, hb22.1]
  have hy3z3 : yA3 < zA3 := by linarith [hb13.2, hb23.1]
  have hz3y4 : zA3 < yA4 := by linarith [hb23.2, hb14.1]
  have hy4z4 : yA4 < zA4 := by linarith [hb14.2, hb24.1]
  refine ⟨Fin 4, inferInstance, ![arcB0, arcB1, arcA2, arcA3], 0, Fin.elim0, ?_, ?_, ?_⟩
  · intro j t
    fin_cases j
    · exact arcB0_mem t
    · exact arcB1_mem t
    · exact arcA2_mem t
    · exact arcA3_mem t
  · intro i
    exact i.elim0
  · intro x hx
    obtain ⟨hxcar, hxplane, hxbox⟩ := mem_closure_Sigma x hx
    rcases trace_eq_branches x hxcar hxplane with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · -- a point of the `B` branch
      obtain ⟨k, hk⟩ := exists_reduce u
      set u' := u - (k:ℝ) * (2 * Real.pi) with hu'def
      have hper : gammaB u = gammaB u' := by
        have h := gammaB_add_int_mul_two_pi u (-k)
        rw [show u + ((-k : ℤ) : ℝ) * (2 * Real.pi) = u' by push_cast [hu'def]; ring] at h
        rw [h]
      have hbox' : Submission.boxNorm dropC dropCyc (gammaB u') ≤ dropS := by
        rw [← hper]; exact hxbox
      have hpsi : psiB u' ≤ 0 := by
        rw [boxNorm_gammaB] at hbox'
        rw [psiB_iff]
        exact le_trans (le_max_left _ _) hbox'
      have hsh := (hBle u' ⟨hk.1, le_of_lt hk.2⟩).mp hpsi
      rw [Set.mem_union, Set.mem_union] at hsh
      rcases hsh with (hcase | hcase) | hcase
      · -- `u' ∈ [0, uB1]`: the arc `arcB0` at `u' + 2π`
        refine Or.inl ⟨0, ?_⟩
        have hmem : u' + 2 * Real.pi ∈ Set.Icc uB4 (2 * Real.pi + uB1) :=
          ⟨by linarith [hB5, hk.1, Real.pi_pos], by linarith [hcase.2]⟩
        have hper2 : gammaB u = gammaB (u' + 2 * Real.pi) := by
          rw [hper]
          have h := gammaB_add_int_mul_two_pi u' 1
          rw [show u' + (1:ℤ) * (2 * Real.pi) = u' + 2 * Real.pi by push_cast; ring] at h
          exact h.symm
        rw [hper2]
        simpa using mem_range_arcB0 hmem
      · -- `u' ∈ [uB2, uB3]`: the arc `arcB1`
        refine Or.inl ⟨1, ?_⟩
        rw [hper]
        simpa using mem_range_arcB1 hcase
      · -- `u' ∈ [uB4, 2π]`: the arc `arcB0` at `u'`
        refine Or.inl ⟨0, ?_⟩
        have hmem : u' ∈ Set.Icc uB4 (2 * Real.pi + uB1) :=
          ⟨hcase.1, by linarith [hcase.2, hB1]⟩
        rw [hper]
        simpa using mem_range_arcB0 hmem
    · -- a point of the `A` branch
      obtain ⟨k, hk⟩ := exists_reduce u
      set u' := u - (k:ℝ) * (2 * Real.pi) with hu'def
      have hper : gammaA u = gammaA u' := by
        have h := gammaA_add_int_mul_two_pi u (-k)
        rw [show u + ((-k : ℤ) : ℝ) * (2 * Real.pi) = u' by push_cast [hu'def]; ring] at h
        rw [h]
      have hbox' : Submission.boxNorm dropC dropCyc (gammaA u') ≤ dropS := by
        rw [← hper]; exact hxbox
      have hmem : u' ∈ Set.Icc (0:ℝ) (2 * Real.pi) := ⟨hk.1, le_of_lt hk.2⟩
      have hpsi2 : psiA2 u' ≤ 0 := by
        rw [boxNorm_gammaA] at hbox'
        rw [psiA2_iff]
        exact le_trans (le_max_left _ _) hbox'
      have hpsi1 : psiA1 u' ≤ 0 := by
        rw [boxNorm_gammaA] at hbox'
        rw [psiA1_iff]
        have h2 := le_trans (le_max_right _ _) hbox'
        rw [div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^(1/3:ℝ))] at h2
        rw [yclip]
        exact h2
      have hy2z3 : yA2 < zA3 := by
        have h1 : ang 14 < Real.pi := ang_lt_pi (by norm_num)
        have h2 : Real.pi ≤ 2 * Real.pi - ang (2/5) := by
          have hp := ang_lt_pi (show (0:ℝ) < 2/5 by norm_num)
          linarith
        linarith [hb12.2, h1, h2, hb23.1]
      have hz2y3 : zA2 < yA3 := by
        have h1 : ang 400 < Real.pi := ang_lt_pi (by norm_num)
        have h2 : Real.pi ≤ 2 * Real.pi - ang (3/2) := by
          have hp := ang_lt_pi (show (0:ℝ) < 3/2 by norm_num)
          linarith
        linarith [hb22.2, h1, h2, hb13.1]
      have hsh1 := (hA1le u' hmem).mp hpsi1
      have hsh2 := (hA2le u' hmem).mp hpsi2
      rw [Set.mem_union] at hsh1 hsh2
      rcases hsh1 with hcase1 | hcase1 <;> rcases hsh2 with hcase2 | hcase2
      · -- `u' ∈ [zA1, yA2]`
        refine Or.inl ⟨2, ?_⟩
        rw [hper]
        simpa using mem_range_arcA2 ⟨hcase2.1, hcase1.2⟩
      · exfalso; linarith [hcase1.2, hcase2.1, hy2z3]
      · exfalso; linarith [hcase1.1, hcase2.2, hz2y3]
      · -- `u' ∈ [zA3, yA4]`
        refine Or.inl ⟨3, ?_⟩
        rw [hper]
        simpa using mem_range_arcA3 ⟨hcase2.1, hcase1.2⟩

end

end Work.BoxShrink.PinchOff.RefuteDrop
