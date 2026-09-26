import Submission.Work.Smooth.Schoenflies.NullHomotopyRel
import Submission.Work.InnermostDisk.descend_continuousMap
import Submission.Work.Smooth.SphereJordan.annulusSchoenflies_of_plain

/-!
# A null-homotopic loop extends over the disc

The converse of `Work.Smooth.Schoenflies.NullHomotopicRel.of_discExtension`: a null-homotopy of the
loop `c` relative to its base point, avoiding `x`, descends through the quotient map
`Work.Smooth.Schoenflies.conePoint : [0,1]² → 𝔻` to a continuous map `F : 𝔻 → ℂ` which avoids `x`
and restricts to `c` on the boundary circle (and sends the centre of the disc to `c 0`).

The quotient map is `conePoint (s, t) = (1 - s) e^{2π i t}`: it is a continuous surjection from the
compact square onto the Hausdorff disc, hence a quotient map, and the descent is
`Work.InnermostDisk.descend_continuousMap`.  The homotopy conditions are exactly what is needed for
well-definedness on the fibres: the right edge `{1} × [0,1]` collapses to the centre and maps
constantly to `c 0` (`H (1, t) = c 0`), and the two horizontal edges are identified
(`H (s, 0) = H (s, 1)`); on the left edge the map is `t ↦ c (2π t)`.

## Main results

* `coneAngle`, `coneAngle_mem`, `exp_coneAngle` — the angle in `[0,1]` of a point of `ℂ`;
* `conePoint_surjective` — the cone map is onto the disc;
* `conePoint_fiber` — the fibres of the cone map are as described above;
* `exists_discExtension_of_nullHomotopicRel` — the extension.
-/

open Set

namespace Work.Smooth.Schoenflies

noncomputable section

/-- **The angle in `[0,1]` of a point of `ℂ`**: the argument of `z` as a fraction of `2π`, taken in
`[0,1)`.  It is chosen so that `e^{2π i · coneAngle z} = e^{i · arg z}`. -/
def coneAngle (z : ℂ) : ℝ :=
  Complex.arg z / (2 * Real.pi) + if Complex.arg z < 0 then 1 else 0

/-- The angle lies in the interval `[0,1]`. -/
theorem coneAngle_mem (z : ℂ) : coneAngle z ∈ Set.Icc (0 : ℝ) 1 := by
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hle := Complex.arg_le_pi z
  have hgt := Complex.neg_pi_lt_arg z
  rw [coneAngle]
  split_ifs with h
  · constructor
    · have h1 : -Real.pi / (2 * Real.pi) < Complex.arg z / (2 * Real.pi) :=
        div_lt_div_of_pos_right hgt hpos
      have h2 : -Real.pi / (2 * Real.pi) = -(1 / 2 : ℝ) := by
        field_simp
      linarith
    · have h1 : Complex.arg z / (2 * Real.pi) < 0 := div_neg_of_neg_of_pos h hpos
      linarith
  · constructor
    · have h1 : 0 ≤ Complex.arg z / (2 * Real.pi) := div_nonneg (not_lt.mp h) hpos.le
      linarith
    · have h1 : Complex.arg z / (2 * Real.pi) ≤ 1 := by
        rw [div_le_one hpos]
        linarith [hle, Real.pi_pos]
      linarith

/-- The exponential of the angle recovers the direction of `z`. -/
theorem exp_coneAngle (z : ℂ) :
    Complex.exp ((↑(2 * Real.pi * coneAngle z) : ℂ) * Complex.I)
      = Complex.exp ((↑(Complex.arg z) : ℂ) * Complex.I) := by
  rw [coneAngle]
  split_ifs with h
  · have h2 : 2 * Real.pi * (Complex.arg z / (2 * Real.pi) + 1) = Complex.arg z + 2 * Real.pi := by
      field_simp; try ring
    rw [h2]
    push_cast
    rw [show (↑(Complex.arg z) + 2 * (Real.pi : ℂ)) * Complex.I
        = ↑(Complex.arg z) * Complex.I + ((1 : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) from by
      ring]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · have h2 : 2 * Real.pi * (Complex.arg z / (2 * Real.pi) + 0) = Complex.arg z := by
      field_simp; try ring
    rw [h2]

/-- **The cone map is onto the closed disc**: `z` is the image of `(1 - ‖z‖, coneAngle z)`. -/
theorem conePoint_surjective : Function.Surjective conePoint := by
  intro z
  have hz : ‖(z : ℂ)‖ ≤ 1 := by
    have h := z.2
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  refine ⟨(⟨1 - ‖(z : ℂ)‖, ⟨by linarith [norm_nonneg (z : ℂ), hz],
      by linarith [norm_nonneg (z : ℂ), hz]⟩⟩,
    ⟨coneAngle (z : ℂ), coneAngle_mem _⟩), ?_⟩
  apply Subtype.ext
  simp only [conePoint]
  have hs : (1 - ((1 - ‖(z : ℂ)‖ : ℝ)) : ℝ) = ‖(z : ℂ)‖ := by ring
  rw [show (((1 - ((1 - ‖(z : ℂ)‖ : ℝ)) : ℝ)) : ℂ) = ((‖(z : ℂ)‖ : ℝ) : ℂ) from by rw [hs],
    exp_coneAngle]
  exact Complex.norm_mul_exp_arg_mul_I (z : ℂ)

/-- The norm of the cone point: `‖conePoint (s, t)‖ = 1 - s`. -/
theorem norm_conePoint (p : Work.Smooth.Plane.ArcInterval × Work.Smooth.Plane.ArcInterval) :
    ‖(conePoint p : ℂ)‖ = 1 - (p.1 : ℝ) := by
  rw [conePoint_coe, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    show ‖(((1 - (p.1 : ℝ)) : ℝ) : ℂ)‖ = |(1 - (p.1 : ℝ))| from by
      rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs],
    abs_of_nonneg (by linarith [p.1.2.2])]

/-- **The fibres of the cone map.**  If `H` is constant on the right edge and on the pairs
`(s, 0)`, `(s, 1)`, then `H` is constant on the fibres of `conePoint`: it descends to the disc. -/
theorem conePoint_fiber {c : ℝ → ℂ} {H : C(Work.Smooth.Plane.ArcInterval ×
      Work.Smooth.Plane.ArcInterval, ℂ)}
    (h0 : ∀ t, H (0, t) = c (2 * Real.pi * t)) (h1 : ∀ t, H (1, t) = c 0)
    (hrel : ∀ s, H (s, 0) = H (s, 1)) :
    ∀ p q, conePoint p = conePoint q → H p = H q := by
  intro p q hpq
  have hs : p.1 = q.1 := by
    have h := congrArg (fun z : Work.Smooth.Jordan.Disc => ‖(z : ℂ)‖) hpq
    rw [norm_conePoint, norm_conePoint] at h
    exact Subtype.ext (by linarith)
  rcases eq_or_ne p.1 1 with hp1 | hp1
  · have hq1 : q.1 = 1 := by rw [← hs]; exact hp1
    rw [show p = ((1 : Work.Smooth.Plane.ArcInterval), p.2) from Prod.ext hp1 rfl,
      show q = ((1 : Work.Smooth.Plane.ArcInterval), q.2) from Prod.ext hq1 rfl, h1, h1]
  · have hp1lt : (p.1 : ℝ) < 1 := lt_of_le_of_ne p.1.2.2 (fun h => hp1 (Subtype.ext h))
    have hq1 : q.1 = p.1 := hs.symm
    have hcoe := congrArg (fun z : Work.Smooth.Jordan.Disc => (z : ℂ)) hpq
    rw [conePoint_coe, conePoint_coe] at hcoe
    have hcoef : (((1 - (p.1 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      linarith
    have hexp : Complex.exp (((((2 * Real.pi * (p.2 : ℝ)) : ℝ)) : ℂ) * Complex.I)
        = Complex.exp (((((2 * Real.pi * (q.2 : ℝ)) : ℝ)) : ℂ) * Complex.I) := by
      refine mul_left_cancel₀ hcoef ?_
      have hq1' : ((1 - (q.1 : ℝ)) : ℝ) = (1 - (p.1 : ℝ)) := by rw [hq1]
      rw [hq1'] at hcoe
      exact hcoe
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    have hdiff : (p.2 : ℝ) - (q.2 : ℝ) = (n : ℝ) := by
      have h2' : 2 * Real.pi * (p.2 : ℝ)
          = 2 * Real.pi * (q.2 : ℝ) + (n : ℝ) * (2 * Real.pi) := by
        have h := congrArg Complex.im hn
        simpa using h
      have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
      have h3 : 2 * Real.pi * ((p.2 : ℝ) - (q.2 : ℝ)) = 2 * Real.pi * (n : ℝ) := by linarith
      exact mul_left_cancel₀ (ne_of_gt hpi) h3
    have hnub : n ≤ 1 := by
      have : (n : ℝ) ≤ 1 := by linarith [hdiff, p.2.2.2, q.2.2.1]
      exact_mod_cast this
    have hnlb : -1 ≤ n := by
      have : (-1 : ℝ) ≤ (n : ℝ) := by linarith [hdiff, p.2.2.1, q.2.2.2]
      exact_mod_cast this
    have hcases : n = -1 ∨ n = 0 ∨ n = 1 := by omega
    rcases hcases with hcase | hcase | hcase
    · have hd : (p.2 : ℝ) - (q.2 : ℝ) = -1 := by rw [hcase] at hdiff; simpa using hdiff
      have hp2 : (p.2 : ℝ) = 0 := by linarith [hd, p.2.2.1, q.2.2.2]
      have hq2 : (q.2 : ℝ) = 1 := by linarith [hd, p.2.2.1, q.2.2.2]
      rw [show p = (p.1, p.2) from rfl, show q = (q.1, q.2) from rfl,
        show p.2 = (0 : Work.Smooth.Plane.ArcInterval) from Subtype.ext hp2,
        show q.2 = (1 : Work.Smooth.Plane.ArcInterval) from Subtype.ext hq2,
        ← hrel q.1, hq1]
    · have hd : (p.2 : ℝ) - (q.2 : ℝ) = 0 := by rw [hcase] at hdiff; simpa using hdiff
      rw [show p = (p.1, p.2) from rfl, show q = (q.1, q.2) from rfl,
        show p.2 = q.2 from Subtype.ext (by linarith), hq1]
    · have hd : (p.2 : ℝ) - (q.2 : ℝ) = 1 := by rw [hcase] at hdiff; simpa using hdiff
      have hp2 : (p.2 : ℝ) = 1 := by linarith [hd, p.2.2.2, q.2.2.1]
      have hq2 : (q.2 : ℝ) = 0 := by linarith [hd, p.2.2.2, q.2.2.1]
      rw [show p = (p.1, p.2) from rfl, show q = (q.1, q.2) from rfl,
        show p.2 = (1 : Work.Smooth.Plane.ArcInterval) from Subtype.ext hp2,
        show q.2 = (0 : Work.Smooth.Plane.ArcInterval) from Subtype.ext hq2,
        ← hrel p.1, hq1]

/-- **A null-homotopy of the loop relative to its base point extends over the disc.**  The extension
avoids the point `x` and restricts to `c` on the boundary circle; it sends the centre of the disc
to `c 0`. -/
theorem exists_discExtension_of_nullHomotopicRel {c : ℝ → ℂ} (hc : Continuous c)
    (hper : Function.Periodic c (2 * Real.pi)) {x : ℂ}
    (h : NullHomotopicRel c x) :
    ∃ F : C(Work.Smooth.SphereJordan.Disc, ℂ),
      (∀ z : Work.Smooth.SphereJordan.Disc, (F z : ℂ) ≠ x) ∧
      (∀ θ : ℝ, (F (Work.Smooth.SphereJordan.circlePoint θ) : ℂ) = c θ) ∧
      F 0 = c 0 := by
  obtain ⟨H, hne, h0, h1, hrel⟩ := h
  obtain ⟨g, hgcont, hg⟩ := Work.InnermostDisk.descend_continuousMap (f := conePoint)
    continuous_conePoint conePoint_surjective H.continuous (conePoint_fiber h0 h1 hrel)
  refine ⟨⟨g, hgcont⟩, ?_, ?_, ?_⟩
  · intro z
    obtain ⟨p, rfl⟩ := conePoint_surjective z
    show g (conePoint p) ≠ x
    rw [hg p]
    exact hne p
  · intro θ
    obtain ⟨t, k, htk⟩ : ∃ t : Work.Smooth.Plane.ArcInterval, ∃ k : ℤ,
        θ = 2 * Real.pi * (t : ℝ) + (k : ℝ) * (2 * Real.pi) := by
      set k : ℤ := ⌊θ / (2 * Real.pi)⌋ with hk
      refine ⟨⟨θ / (2 * Real.pi) - k, ?_, ?_⟩, k, ?_⟩
      · have := Int.floor_le (θ / (2 * Real.pi))
        linarith
      · have := Int.lt_floor_add_one (θ / (2 * Real.pi))
        linarith
      · have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
        field_simp
        ring
    have hcp : Work.Smooth.SphereJordan.circlePoint θ
        = Work.Smooth.SphereJordan.circlePoint (2 * Real.pi * (t : ℝ)) := by
      rw [htk]
      exact Work.Smooth.SphereJordan.circlePoint_add_int_mul _ k
    have hcθ : c θ = c (2 * Real.pi * (t : ℝ)) := by
      rw [htk]
      simpa using hper.int_mul k (2 * Real.pi * (t : ℝ))
    rw [hcp, hcθ]
    show g (Work.Smooth.SphereJordan.circlePoint (2 * Real.pi * (t : ℝ)))
      = c (2 * Real.pi * (t : ℝ))
    rw [show Work.Smooth.SphereJordan.circlePoint (2 * Real.pi * (t : ℝ)) = conePoint (0, t) from
      (conePoint_zero t).symm]
    rw [hg]
    exact h0 t
  · rw [show (0 : Work.Smooth.SphereJordan.Disc) = conePoint (1, 0) from (conePoint_one 0).symm]
    show g (conePoint (1, 0)) = c 0
    rw [hg]
    exact h1 0

end

end Work.Smooth.Schoenflies
