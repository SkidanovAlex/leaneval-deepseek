import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.brouwer_fixed_point_square

namespace Work.RPB1a.Caratheodory.Brouwer

open Set Metric
open scoped Topology

/-!
# The crossing lemma for a left-to-right and a bottom-to-top path in the square

`Work.RPB1a.Caratheodory.Brouwer.crossing_lemma_paths`: a continuous path joining the left and the
right sides of the square `[-1,1] × [-1,1]` and a continuous path joining the bottom and the top
sides must meet.

The proof is the standard Gale/Gauld argument: assuming that the paths are disjoint, the vector
field
`G (s,t) = ((v t).1 - (h s).1, (h s).2 - (v t).2)`
is nowhere zero on the square, and its normalisation `F = G / ‖G‖` by the sup norm (which on
`ℝ × ℝ` is the product norm) is a continuous self-map of the square.  Brouwer's fixed point theorem
for the square (`brouwer_fixed_point_square`) supplies a fixed point `x`.
Since `‖F x‖ = 1`, one of the two coordinates of `x` has absolute value `1`; combining the fixed
point equation with the endpoint conditions `(h (−1)).1 = −1`, `(h 1).1 = 1`, `(v (−1)).2 = −1`,
`(v 1).2 = 1` then gives a contradiction (the four cases are `crossingAux_galeMap_ne_self`).

Because the normalisation `G ↦ G/‖G‖` is only continuous where `G ≠ 0`, the map fed to Brouwer is
precomposed with the (coordinatewise) clamp of `ℝ × ℝ` onto the square, which is the identity
there; this makes it continuous everywhere and square-valued everywhere.
-/

namespace CrossingAux

/-! ### Elementary facts about the sup norm on `ℝ × ℝ` -/

lemma norm_pair (p : ℝ × ℝ) : ‖p‖ = max |p.1| |p.2| := by
  rw [Prod.norm_def]
  simp [Real.norm_eq_abs]

lemma fst_eq_of_inv_smul_eq {p x : ℝ × ℝ} (h : (‖p‖)⁻¹ • p = x) :
    (‖p‖)⁻¹ * p.1 = x.1 := by
  have := congrArg Prod.fst h
  simpa using this

lemma snd_eq_of_inv_smul_eq {p x : ℝ × ℝ} (h : (‖p‖)⁻¹ • p = x) :
    (‖p‖)⁻¹ * p.2 = x.2 := by
  have := congrArg Prod.snd h
  simpa using this

lemma fst_eq_mul_of_inv_smul_eq {p x : ℝ × ℝ} (h : (‖p‖)⁻¹ • p = x) (hp : p ≠ 0) :
    p.1 = ‖p‖ * x.1 := by
  have hnne : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  have h1 := fst_eq_of_inv_smul_eq h
  calc p.1 = ‖p‖ * ((‖p‖)⁻¹ * p.1) := by
        rw [← mul_assoc, mul_inv_cancel₀ hnne, one_mul]
    _ = ‖p‖ * x.1 := by rw [h1]

lemma snd_eq_mul_of_inv_smul_eq {p x : ℝ × ℝ} (h : (‖p‖)⁻¹ • p = x) (hp : p ≠ 0) :
    p.2 = ‖p‖ * x.2 := by
  have hnne : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  have h2 := snd_eq_of_inv_smul_eq h
  calc p.2 = ‖p‖ * ((‖p‖)⁻¹ * p.2) := by
        rw [← mul_assoc, mul_inv_cancel₀ hnne, one_mul]
    _ = ‖p‖ * x.2 := by rw [h2]

/-- If the normalised vector `p / ‖p‖` equals `x`, then one coordinate of `x` has absolute value
`1`: the sup norm of the normalised vector is `1`, while its coordinates are the coordinates of `x`
rescaled by `max |x.1| |x.2|`. -/
lemma max_abs_eq_one_of_inv_smul_eq {p x : ℝ × ℝ} (h : (‖p‖)⁻¹ • p = x) (hp : p ≠ 0) :
    max |x.1| |x.2| = 1 := by
  have hn : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have hnne : ‖p‖ ≠ 0 := ne_of_gt hn
  have h1 := fst_eq_mul_of_inv_smul_eq h hp
  have h2 := snd_eq_mul_of_inv_smul_eq h hp
  have hm : ‖p‖ = max |p.1| |p.2| := norm_pair p
  have hcalc : max |p.1| |p.2| = ‖p‖ * max |x.1| |x.2| := by
    rw [h1, h2, abs_mul, abs_mul, abs_of_pos hn]
    exact (mul_max_of_nonneg (a := ‖p‖) |x.1| |x.2| (norm_nonneg p)).symm
  have hfinal : ‖p‖ = ‖p‖ * max |x.1| |x.2| := by
    calc ‖p‖ = max |p.1| |p.2| := hm
      _ = ‖p‖ * max |x.1| |x.2| := hcalc
  have : ‖p‖ * max |x.1| |x.2| = ‖p‖ * 1 := by rw [mul_one]; exact hfinal.symm
  exact mul_left_cancel₀ hnne this

/-! ### Clamping into the square -/

/-- Coordinatewise clamp of `ℝ` into `[-1,1]`. -/
noncomputable def clampR (t : ℝ) : ℝ := min 1 (max (-1) t)

/-- Coordinatewise clamp of `ℝ × ℝ` into the square `[-1,1] × [-1,1]`. -/
noncomputable def clampSquare (x : ℝ × ℝ) : ℝ × ℝ := (clampR x.1, clampR x.2)

lemma continuous_clampR : Continuous clampR :=
  continuous_const.min (continuous_const.max continuous_id)

lemma continuous_clampSquare : Continuous clampSquare :=
  continuous_clampR.prodMap continuous_clampR

lemma clampR_mem (t : ℝ) : clampR t ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

lemma clampR_eq_of_mem {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) : clampR t = t := by
  rw [clampR, min_eq_right (max_le (by norm_num) ht.2), max_eq_right ht.1]

lemma clampSquare_mem (x : ℝ × ℝ) :
    clampSquare x ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
  rw [Set.mem_prod]
  exact ⟨clampR_mem x.1, clampR_mem x.2⟩

lemma clampSquare_eq_of_mem {x : ℝ × ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) : clampSquare x = x := by
  obtain ⟨h1, h2⟩ := Set.mem_prod.mp hx
  exact Prod.ext (clampR_eq_of_mem h1) (clampR_eq_of_mem h2)

/-! ### The Gale/Gauld vector field has no fixed point in the square -/

/-- **The Gale/Gauld map has no fixed point in the square.**  If a left-to-right path `h` and a
bottom-to-top path `v` in the square are disjoint, then the vector field
`((v t).1 - (h s).1, (h s).2 - (v t).2)`, normalised by the sup norm, cannot point at `(s,t)`
itself. -/
lemma galeMap_ne_self {h v : ℝ → ℝ × ℝ}
    (hhm : ∀ t ∈ Set.Icc (-1 : ℝ) 1, h t ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)
    (hvm : ∀ t ∈ Set.Icc (-1 : ℝ) 1, v t ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)
    (hh_left : (h (-1)).1 = -1) (hh_right : (h 1).1 = 1)
    (hv_bot : (v (-1)).2 = -1) (hv_top : (v 1).2 = 1)
    (hdisj : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ∀ t ∈ Set.Icc (-1 : ℝ) 1, h s ≠ v t)
    (x : ℝ × ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) :
    (‖((v x.2).1 - (h x.1).1, (h x.1).2 - (v x.2).2)‖)⁻¹ •
      ((v x.2).1 - (h x.1).1, (h x.1).2 - (v x.2).2) ≠ x := by
  intro hfix
  obtain ⟨hx1, hx2⟩ := Set.mem_prod.mp hx
  set p : ℝ × ℝ := ((v x.2).1 - (h x.1).1, (h x.1).2 - (v x.2).2) with hp
  have hpne : p ≠ 0 := by
    intro h0
    have e1 : (v x.2).1 - (h x.1).1 = 0 := by
      have := congrArg Prod.fst h0
      simpa [hp] using this
    have e2 : (h x.1).2 - (v x.2).2 = 0 := by
      have := congrArg Prod.snd h0
      simpa [hp] using this
    exact hdisj x.1 hx1 x.2 hx2 (Prod.ext (sub_eq_zero.mp e1).symm (sub_eq_zero.mp e2))
  have hp1 : (v x.2).1 - (h x.1).1 = ‖p‖ * x.1 := by
    have := fst_eq_mul_of_inv_smul_eq hfix hpne
    simpa [hp] using this
  have hp2 : (h x.1).2 - (v x.2).2 = ‖p‖ * x.2 := by
    have := snd_eq_mul_of_inv_smul_eq hfix hpne
    simpa [hp] using this
  have hn : 0 < ‖p‖ := norm_pos_iff.mpr hpne
  have hmax : max |x.1| |x.2| = 1 := max_abs_eq_one_of_inv_smul_eq hfix hpne
  have hcase : |x.1| = 1 ∨ |x.2| = 1 := by
    rcases (max_eq_iff.mp hmax) with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hh1l : -1 ≤ (h x.1).1 := (Set.mem_prod.mp (hhm x.1 hx1)).1.1
  have hh1m : (h x.1).1 ≤ 1 := (Set.mem_prod.mp (hhm x.1 hx1)).1.2
  have hh2l : -1 ≤ (h x.1).2 := (Set.mem_prod.mp (hhm x.1 hx1)).2.1
  have hh2m : (h x.1).2 ≤ 1 := (Set.mem_prod.mp (hhm x.1 hx1)).2.2
  have hv1l : -1 ≤ (v x.2).1 := (Set.mem_prod.mp (hvm x.2 hx2)).1.1
  have hv1m : (v x.2).1 ≤ 1 := (Set.mem_prod.mp (hvm x.2 hx2)).1.2
  have hv2l : -1 ≤ (v x.2).2 := (Set.mem_prod.mp (hvm x.2 hx2)).2.1
  have hv2m : (v x.2).2 ≤ 1 := (Set.mem_prod.mp (hvm x.2 hx2)).2.2
  rcases hcase with hx1abs | hx2abs
  · rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hx1abs with hx1eq | hx1eq
    · -- `x.1 = 1`, so `(v x.2).1 = 1 + ‖p‖ > 1`, against `(v x.2).1 ≤ 1`
      have hhe : (h x.1).1 = 1 := by rw [hx1eq, hh_right]
      have hp1' : (v x.2).1 - 1 = ‖p‖ := by
        rw [hhe, hx1eq, mul_one] at hp1
        exact hp1
      linarith
    · -- `x.1 = -1`, so `(v x.2).1 = -1 - ‖p‖ < -1`, against `-1 ≤ (v x.2).1`
      have hhe : (h x.1).1 = -1 := by rw [hx1eq, hh_left]
      have hp1' : (v x.2).1 + 1 = -‖p‖ := by
        rw [hhe, hx1eq] at hp1
        ring_nf at hp1
        linarith
      linarith
  · rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hx2abs with hx2eq | hx2eq
    · -- `x.2 = 1`, so `(h x.1).2 = 1 + ‖p‖ > 1`, against `(h x.1).2 ≤ 1`
      have hve : (v x.2).2 = 1 := by rw [hx2eq, hv_top]
      have hp2' : (h x.1).2 - 1 = ‖p‖ := by
        rw [hve, hx2eq, mul_one] at hp2
        exact hp2
      linarith
    · -- `x.2 = -1`, so `(h x.1).2 = -1 - ‖p‖ < -1`, against `-1 ≤ (h x.1).2`
      have hve : (v x.2).2 = -1 := by rw [hx2eq, hv_bot]
      have hp2' : (h x.1).2 + 1 = -‖p‖ := by
        rw [hve, hx2eq] at hp2
        ring_nf at hp2
        linarith
      linarith

end CrossingAux

open CrossingAux

/-- A "left-to-right" path in the square `[-1,1] x [-1,1]` and a "bottom-to-top" path in the
square must meet.

Standard route (Gale/Gauld): assume `h s ≠ v t` for all `s, t` and apply
`brouwer_fixed_point_square` to `(s,t) ↦ ((v t).1 - (h s).1, (h s).2 - (v t).2) / |h s - v t|`. -/
theorem crossing_lemma_paths {h v : ℝ → ℝ × ℝ} (hh : Continuous h) (hv : Continuous v)
    (hhm : ∀ t ∈ Set.Icc (-1 : ℝ) 1, h t ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)
    (hvm : ∀ t ∈ Set.Icc (-1 : ℝ) 1, v t ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)
    (hh_left : (h (-1)).1 = -1) (hh_right : (h 1).1 = 1)
    (hv_bot : (v (-1)).2 = -1) (hv_top : (v 1).2 = 1) :
    ∃ s ∈ Set.Icc (-1 : ℝ) 1, ∃ t ∈ Set.Icc (-1 : ℝ) 1, h s = v t := by
  by_contra hcon
  push Not at hcon
  -- the Gale/Gauld vector field, precomposed with the clamp so that it is defined and continuous
  -- on all of `ℝ × ℝ`
  set g : ℝ × ℝ → ℝ × ℝ := fun x =>
    ((v (clampSquare x).2).1 - (h (clampSquare x).1).1,
     (h (clampSquare x).1).2 - (v (clampSquare x).2).2) with hg
  -- its sup-norm normalisation
  set F : ℝ × ℝ → ℝ × ℝ := fun x => (‖g x‖)⁻¹ • g x with hF
  have hgcont : Continuous g := by
    rw [hg]
    refine Continuous.prodMk ?_ ?_
    · exact ((continuous_fst.comp (hv.comp (continuous_snd.comp continuous_clampSquare))).sub
        (continuous_fst.comp (hh.comp (continuous_fst.comp continuous_clampSquare))))
    · exact ((continuous_snd.comp (hh.comp (continuous_fst.comp continuous_clampSquare))).sub
        (continuous_snd.comp (hv.comp (continuous_snd.comp continuous_clampSquare))))
  have hgne : ∀ x, g x ≠ 0 := by
    intro x h0
    have e1 : (v (clampSquare x).2).1 - (h (clampSquare x).1).1 = 0 := by
      have := congrArg Prod.fst h0
      simpa [hg] using this
    have e2 : (h (clampSquare x).1).2 - (v (clampSquare x).2).2 = 0 := by
      have := congrArg Prod.snd h0
      simpa [hg] using this
    exact hcon (clampSquare x).1 (clampSquare_mem x).1 (clampSquare x).2 (clampSquare_mem x).2
      (Prod.ext (sub_eq_zero.mp e1).symm (sub_eq_zero.mp e2))
  have hFcont : Continuous F := by
    rw [hF]
    exact (hgcont.norm.inv₀ (fun x => norm_ne_zero_iff.mpr (hgne x))).smul hgcont
  have hFmaps : ∀ x ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1,
      F x ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
    intro x hx
    have hnorm : ‖F x‖ = 1 := by
      rw [hF, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hgne x))]
    have h1 : |(F x).1| ≤ 1 := by
      have := norm_fst_le (F x)
      rw [Real.norm_eq_abs, hnorm] at this
      exact this
    have h2 : |(F x).2| ≤ 1 := by
      have := norm_snd_le (F x)
      rw [Real.norm_eq_abs, hnorm] at this
      exact this
    rw [Set.mem_prod]
    exact ⟨abs_le.mp h1, abs_le.mp h2⟩
  obtain ⟨x, hx, hfix⟩ := brouwer_fixed_point_square F hFcont hFmaps
  have hfix' : (‖((v x.2).1 - (h x.1).1, (h x.1).2 - (v x.2).2)‖)⁻¹ •
      ((v x.2).1 - (h x.1).1, (h x.1).2 - (v x.2).2) = x := by
    simpa [hF, hg, clampSquare_eq_of_mem hx] using hfix
  exact (galeMap_ne_self hhm hvm hh_left hh_right hv_bot hv_top hcon x hx) hfix'

end Work.RPB1a.Caratheodory.Brouwer
