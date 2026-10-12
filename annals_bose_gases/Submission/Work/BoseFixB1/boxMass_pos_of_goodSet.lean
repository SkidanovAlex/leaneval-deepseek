import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Analysis.Clamp.abs_clamp_sub_le
import Submission.Work.SmallBoxSliding.boxMass_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Every sliding box on the good set has positive volume

The sliding localisation of FS `thm:aprioriHLambda` uses the boxes
`B(u) = acube ℓ ∩ ((ℓd)•u + acube (ℓd))` for `u` in the *good set*
`G = {u : ∀ j, |((ℓd)•u)_j| ≤ ½ℓ(1+d) − μ^{-1/3}}`.  On `G` the chemical
potential `μ` does not blow up (`Geom.goodSet_shortSide`), and in particular
every `B(u)`, `u ∈ G`, has **positive volume**.

The proof is a quantitative interior argument.  Put

    m := min (min ℓ (ℓd)) (μ^{-1/3}) > 0 ,   R := ℓ/2 − m/2 ,

and let `cv` be the coordinatewise clamp of the box centre `w := (ℓd)•u` to the
cube `[−R,R]³`.  Good-set membership gives `|w_j| ≤ ℓ/2 + ℓd/2 − μ^{-1/3} ≤
ℓ/2 + ℓd/2 − m`, i.e. the interval `[w_j − ℓd/2, w_j + ℓd/2]` reaches at least
`m` units into the big interval `[−ℓ/2, ℓ/2]`; hence `|cv_j| ≤ R` and
`|cv_j − w_j| ≤ ℓd/2 − m/2`, so the translate `cv + acube m` of the centred cube
of side `m` lies inside `B(u)`.  Therefore

    boxMass ℓ d u = vol (B(u)) ≥ vol (acube m) = m³ > 0 .

(The regime hypothesis `μ^{-1/3} ≤ ℓd` which the corpus usually carries is *not*
needed: the minimum defining `m` absorbs it, and the statement is vacuous when
`½ℓ(1+d) − μ^{-1/3} < 0` makes the good set empty.)
-/

noncomputable section

open MeasureTheory
open scoped Real Topology ENNReal

namespace Work.BoseFixB1

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem boxMass_pos_of_goodSet {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
    {u : EuclideanSpace ℝ (Fin 3)} (hu : u ∈ Work.SmallBoxSliding.goodSet ℓ d μ) :
    0 < Work.SmallBoxSliding.boxMass ℓ d u := by
  have hδpos : 0 < μ ^ (-1 / 3 : ℝ) := Real.rpow_pos_of_pos hμ _
  set m : ℝ := min (min ℓ (ℓ * d)) (μ ^ (-1 / 3 : ℝ)) with hmdef
  have hmpos : 0 < m := by
    rw [hmdef]; exact lt_min (lt_min hℓ (mul_pos hℓ hd)) hδpos
  have hmℓ : m ≤ ℓ := by
    rw [hmdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hmℓd : m ≤ ℓ * d := by
    rw [hmdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hmδ : m ≤ μ ^ (-1 / 3 : ℝ) := by rw [hmdef]; exact min_le_right _ _
  -- the half-side `R = ℓ/2 − m/2` of the cube into which we clamp the centre
  set R : ℝ := ℓ / 2 - m / 2 with hRdef
  have hRnn : 0 ≤ R := by rw [hRdef]; linarith
  have hW : ∀ j : Fin 3, |((ℓ * d) • u).ofLp j| ≤ ℓ / 2 + ℓ * d / 2 - m := by
    intro j
    have h := hu j
    have h2 : (1 / 2 : ℝ) * ℓ * (1 + d) = ℓ / 2 + ℓ * d / 2 := by ring
    rw [h2] at h
    linarith [hmδ]
  -- the clamped centre: coordinatewise projection of `(ℓd)•u` onto `[−R,R]`
  set cv : ℝ³ :=
    WithLp.toLp 2 (fun j : Fin 3 => max (-R) (min R (((ℓ * d) • u).ofLp j))) with hcvdef
  have hcv : ∀ j : Fin 3, cv.ofLp j = max (-R) (min R (((ℓ * d) • u).ofLp j)) := by
    intro j
    rw [hcvdef]
  have hc_bound : ∀ j : Fin 3, |cv.ofLp j| ≤ R := by
    intro j
    rw [hcv j]
    exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hc_diff : ∀ j : Fin 3, |cv.ofLp j - ((ℓ * d) • u).ofLp j| ≤ ℓ * d / 2 - m / 2 := by
    intro j
    have h1 : -R - ((ℓ * d) • u).ofLp j ≤ (ℓ * d - m) / 2 := by
      have h := (abs_le.mp (hW j)).1
      rw [hRdef]; linarith
    have h2 : ((ℓ * d) • u).ofLp j - R ≤ (ℓ * d - m) / 2 := by
      have h := (abs_le.mp (hW j)).2
      rw [hRdef]; linarith
    have hclamp := Work.Analysis.Clamp.abs_clamp_sub_le (lo := -R) (hi := R)
      (t := ((ℓ * d) • u).ofLp j) (γ := ℓ * d - m) (by linarith) (by linarith) h1 h2
    rw [hcv j]
    linarith
  -- the translate `cv + acube m` of the small cube lies inside `B(u)`
  have hsub : {x : ℝ³ | x - cv ∈ Submission.BoseGases.acube m}
      ⊆ Submission.BoseGases.dlBox ℓ d u := by
    intro x hx
    rw [Submission.BoseGases.mem_dlBox_iff]
    refine ⟨?_, ?_⟩
    · rw [Submission.BoseGases.mem_acube_iff]
      intro j
      rw [Set.mem_Icc]
      have hxm : |x.ofLp j - cv.ofLp j| ≤ m / 2 := by
        have h := (Submission.BoseGases.mem_acube_iff m (x - cv)).mp hx j
        rw [Set.mem_Icc, PiLp.sub_apply] at h
        rw [abs_le]; exact ⟨by linarith [h.1], h.2⟩
      have htri : |x.ofLp j| ≤ |x.ofLp j - cv.ofLp j| + |cv.ofLp j| := by
        have h := abs_add_le (x.ofLp j - cv.ofLp j) (cv.ofLp j)
        rwa [sub_add_cancel] at h
      have hle : |x.ofLp j| ≤ m / 2 + R := by linarith [htri, hxm, hc_bound j]
      have hR : m / 2 + R = ℓ / 2 := by rw [hRdef]; ring
      rw [hR] at hle
      exact ⟨by linarith [(abs_le.mp hle).1], by linarith [(abs_le.mp hle).2]⟩
    · rw [Submission.BoseGases.mem_acube_iff]
      intro j
      rw [Set.mem_Icc, PiLp.sub_apply]
      have hxm : |x.ofLp j - cv.ofLp j| ≤ m / 2 := by
        have h := (Submission.BoseGases.mem_acube_iff m (x - cv)).mp hx j
        rw [Set.mem_Icc, PiLp.sub_apply] at h
        rw [abs_le]; exact ⟨by linarith [h.1], h.2⟩
      have htri : |x.ofLp j - ((ℓ * d) • u).ofLp j|
          ≤ |x.ofLp j - cv.ofLp j| + |cv.ofLp j - ((ℓ * d) • u).ofLp j| := by
        have h := abs_add_le (x.ofLp j - cv.ofLp j) (cv.ofLp j - ((ℓ * d) • u).ofLp j)
        have heq : (x.ofLp j - cv.ofLp j) + (cv.ofLp j - ((ℓ * d) • u).ofLp j)
            = x.ofLp j - ((ℓ * d) • u).ofLp j := by ring
        rwa [heq] at h
      have hle : |x.ofLp j - ((ℓ * d) • u).ofLp j| ≤ ℓ * d / 2 := by
        have hm2 : m / 2 + (ℓ * d / 2 - m / 2) = ℓ * d / 2 := by ring
        linarith [htri, hxm, hc_diff j, hm2]
      exact ⟨by linarith [(abs_le.mp hle).1], by linarith [(abs_le.mp hle).2]⟩
  -- the translate has the volume of `acube m`, and `m > 0`
  have hvol : ENNReal.ofReal (m ^ 3) ≤ (volume : Measure ℝ³)
      (Submission.BoseGases.dlBox ℓ d u) := by
    have hmono := MeasureTheory.measure_mono
      (μ := (volume : Measure ℝ³)) hsub
    have heq : (volume : Measure ℝ³) {x : ℝ³ | x - cv ∈ Submission.BoseGases.acube m}
        = (volume : Measure ℝ³) (Submission.BoseGases.acube m) := by
      have hset : {x : ℝ³ | x - cv ∈ Submission.BoseGases.acube m}
          = (fun y : ℝ³ => (-cv) + y) ⁻¹' Submission.BoseGases.acube m := by
        ext x; simp [sub_eq_add_neg, add_comm]
      rw [hset, MeasureTheory.measure_preimage_add volume (-cv) (Submission.BoseGases.acube m)]
    calc ENNReal.ofReal (m ^ 3)
        = (volume : Measure ℝ³) (Submission.BoseGases.acube m) :=
          (Submission.BoseGases.acube_volume m hmpos.le).symm
      _ = (volume : Measure ℝ³) {x : ℝ³ | x - cv ∈ Submission.BoseGases.acube m} := heq.symm
      _ ≤ _ := hmono
  rw [Work.SmallBoxSliding.boxMass_eq_measureReal, Measure.real_def]
  have hfin : (volume : Measure ℝ³) (Submission.BoseGases.dlBox ℓ d u) ≠ ⊤ :=
    ne_of_lt (Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u)
  have hle := ENNReal.toReal_mono hfin hvol
  rw [ENNReal.toReal_ofReal (pow_pos hmpos 3).le] at hle
  linarith [pow_pos hmpos 3]

end Work.BoseFixB1
