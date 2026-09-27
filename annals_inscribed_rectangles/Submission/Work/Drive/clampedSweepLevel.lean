import Mathlib
import Submission.Work.Drive.endLevelObstruction
import Submission.Work.Drive.levelOf_clampedSweep

/-!
# The class and the level of a clamped sweep, and the unique sweep parameter at a given level

Two elementary but load-bearing facts about the radial sweep `D = clampedSweep c ψ P` of a plane
presentation `P` (`Submission/Work/Drive/clampedSweep.lean`), used by the *end contribution* of the
chain route:

* **the sweep preserves the projective class** (`Work.Drive.cls_clampedSweep`): the radial sweep only
  changes the level of a point, so `class (D x) = class (P (x 0, x 1))`.  Consequently, if the three
  sweeps of a triple point meet, then the *classes* of the three plane points coincide — this is what
  pins the parameter triple down to the collision class of the three rotated planes;

* **the level equation has exactly one interior solution** (`Work.Drive.existsUnique_levelOf_clampedSweep_eq`):
  for a strictly decreasing cutoff `ψ` with `ψ 0 = 1`, `ψ 1 = 0` and a level `L` strictly between the
  truncation level `c` and the plane's level `r = levelOf (P y)`, there is exactly one
  `t ∈ (0,1)` with `levelOf (D (y, t)) = L`.  This is the strict form of
  `Work.Drive.exists_radial_level_eq_of_lt_level` (which provides existence in `(0,1)`) and is what
  makes the bottom triple point of the distinct-level design *unique*: the interior radial parameters
  of the two non-bottom blocks are forced.

Together with the class of a sweep, these give the exact description of the bottom triple points of the
corrected end design (`END_LEVEL_OBSTRUCTION.md` §3): at a bottom triple point of the block with the
largest truncation level, the three class coordinates are the collision parameter of the three rotated
planes and the levels force the two interior radial parameters.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- **A clamped sweep preserves the projective class**: it is the plane point radially rescaled. -/
theorem cls_clampedSweep (c : ℝ) (ψ : ℝ → ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (x : EuclideanSpace ℝ (Fin 3)) :
    (cappingSpaceHomeoProj (clampedSweep c ψ P x)).2
      = (cappingSpaceHomeoProj (P (mk2 (x 0) (x 1)))).2 := by
  rw [clampedSweep_apply, CapSmooth.cappingSpaceHomeoProj_scaleCapping]

/-- **The unique interior sweep parameter at a prescribed level.**  For a continuous, strictly
decreasing cutoff `ψ` with `ψ 0 = 1` and `ψ 1 = 0`, and a level `L` strictly between the truncation
level `c` and the plane's level `r`, the radial sweep meets the level `L` at exactly one interior
radial parameter. -/
theorem existsUnique_levelOf_clampedSweep_eq {c L : ℝ} (hc : 0 < c) {ψ : ℝ → ℝ}
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0) (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (hanti : StrictAntiOn ψ (Set.Icc (0 : ℝ) 1))
    {P : EuclideanSpace ℝ (Fin 2) → CappingSpace} {y : EuclideanSpace ℝ (Fin 2)} {L : ℝ}
    (hLc : c < L) (hLr : L < levelOf (P y)) :
    ∃! t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 ∧
      levelOf (clampedSweep c ψ P (radVec y t)) = L := by
  set r : ℝ := levelOf (P y) with hrdef
  have hrpos : 0 < r := by rw [hrdef]; exact levelOf_pos _
  have hcr : c < r := lt_trans hLc hLr
  have hlog : Real.log c < Real.log r := Real.log_lt_log hc hcr
  set A : ℝ := Real.log c - Real.log r with hAdef
  have hA : A < 0 := by rw [hAdef]; linarith
  -- the level of the sweep, as an explicit function of the radial parameter
  have hlevel : ∀ t : ℝ,
      levelOf (clampedSweep c ψ P (radVec y t))
        = Real.exp (ψ t * A) * r := by
    intro t
    rw [levelOf_clampedSweep, clampScale]
    have hpt : mk2 ((radVec y t).ofLp 0) ((radVec y t).ofLp 1) = y := by
      rw [radVec_apply_zero, radVec_apply_one, mk2_eta]
    have ht2 : (radVec y t).ofLp 2 = t := radVec_apply_two y t
    rw [hpt, ht2, hrdef, hAdef]
  set G : ℝ → ℝ := fun t => Real.exp (ψ t * A) * r with hGdef
  have hG : ∀ t, levelOf (clampedSweep c ψ P (radVec y t)) = G t := fun t => hlevel t
  have hG0 : G 0 = c := by
    rw [hGdef]
    simp only [hψ0, one_mul]
    rw [show Real.exp A = c / r by
      rw [hAdef, Real.exp_sub, Real.exp_log hc, Real.exp_log hrpos], div_mul_cancel₀ c (ne_of_gt hrpos)]
  have hG1 : G 1 = r := by
    rw [hGdef]
    simp only [hψ1, zero_mul, Real.exp_zero, one_mul]
  -- `G` is continuous and strictly increasing on `[0,1]`
  have hGcont : ContinuousOn G (Set.Icc (0 : ℝ) 1) := by
    rw [hGdef]
    exact ((Real.continuous_exp.comp_continuousOn (hcont.mul continuousOn_const)).mul
      continuousOn_const)
  have hGmono : StrictMonoOn G (Set.Icc (0 : ℝ) 1) := by
    intro t ht t' ht' htt'
    have h1 : ψ t' < ψ t := hanti ht ht' htt'
    have h2 : ψ t * A < ψ t' * A := mul_lt_mul_of_neg_right h1 hA
    have h3 : Real.exp (ψ t * A) < Real.exp (ψ t' * A) := Real.exp_lt_exp.mpr h2
    rw [hGdef]
    exact mul_lt_mul_of_pos_right h3 hrpos
  -- existence by the intermediate value theorem
  obtain ⟨t₀, ht₀, ht₀val⟩ : ∃ t ∈ Set.Icc (0 : ℝ) 1, G t = L := by
    have hsub : Set.Icc (G 0) (G 1) ⊆ G '' Set.Icc (0 : ℝ) 1 :=
      intermediate_value_Icc (by norm_num) hGcont
    have hL : L ∈ Set.Icc (G 0) (G 1) := by
      rw [hG0, hG1]
      exact ⟨le_of_lt hLc, le_of_lt hLr⟩
    obtain ⟨t, ht, htv⟩ := hsub hL
    exact ⟨t, ht, htv⟩
  have ht₀int : t₀ ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [Set.mem_Icc] at ht₀
    refine ⟨lt_of_le_of_ne ht₀.1 ?_, lt_of_le_of_ne ht₀.2 ?_⟩
    · intro h0
      have hc0 : G t₀ = c := by rw [← h0, hG0]
      have : L = c := by rw [← ht₀val, hc0]
      exact absurd this (ne_of_gt hLc)
    · intro h1
      have hr0 : G t₀ = r := by rw [h1, hG1]
      have : L = r := by rw [← ht₀val, hr0]
      exact absurd this (ne_of_lt hLr)
  refine ⟨t₀, ⟨ht₀int, by rw [hG t₀]; exact ht₀val⟩, ?_⟩
  -- uniqueness
  rintro t ⟨htint, htval⟩
  have htmem : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt htint.1, le_of_lt htint.2⟩
  have hval : G t = G t₀ := by rw [← hG t, htval, ht₀val]
  rcases lt_trichotomy t t₀ with h | h | h
  · exact absurd hval (ne_of_lt (hGmono htmem ht₀ h))
  · exact h
  · exact absurd hval.symm (ne_of_lt (hGmono ht₀ htmem h))

/-! ## The bounds on the level of a clamped sweep, in **local** form

The cutoff of the endgame has to satisfy the engine's radial non-degeneracy `ha`, which asks
`deriv ψ (x k 2) ≠ 0` at *every* triple point — including the block that is on its bottom or top face,
i.e. at `x k 2 ∈ {0,1}`.  A smooth cutoff with values in `[0,1]` and `ψ 0 = 1` has `deriv ψ 0 = 0`
(`0` is a maximum), so the two requirements are incompatible and the cutoff must be, for instance,
`ψ t = 1 - t` (the profile used in `Submission/Work/Drive/haReduction.lean`): it takes values in `[0,1]`
on `[0,1]` only.  The lemmas below therefore record the two level bounds with the *local* hypothesis
`∀ t ∈ [0,1], ψ t ∈ [0,1]`, which is what such a cutoff satisfies and what the parameter cubes
(`unitBox 2`) provide. -/

/-- **Local `le_levelOf_clampedSweep`**: for a cutoff whose values on `[0,1]` lie in `[0,1]` and a
plane above the truncation level, the sweep does not go below its truncation level. -/
theorem le_levelOf_clampedSweep_local {c : ℝ} (hc : 0 < c) {ψ : ℝ → ℝ}
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (x : EuclideanSpace ℝ (Fin 3))
    (hx : x 2 ∈ Set.Icc (0 : ℝ) 1)
    (hr : c ≤ levelOf (P (mk2 (x 0) (x 1)))) :
    c ≤ levelOf (clampedSweep c ψ P x) := by
  set r : ℝ := levelOf (P (mk2 (x 0) (x 1))) with hrdef
  have hrpos : 0 < r := by rw [hrdef]; exact levelOf_pos _
  have hlog : Real.log c ≤ Real.log r := Real.log_le_log hc (by rw [hrdef]; exact hr)
  have hd : Real.log c - Real.log r ≤ 0 := by linarith
  have hu1 : ψ (x 2) ≤ 1 := (hψ01 (x 2) hx).2
  have hu0 : 0 ≤ ψ (x 2) := (hψ01 (x 2) hx).1
  have hmul : (1 : ℝ) * (Real.log c - Real.log r) ≤ ψ (x 2) * (Real.log c - Real.log r) := by
    have h : (1 - ψ (x 2)) * (Real.log c - Real.log r) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hd
    nlinarith
  have hexp : Real.exp (Real.log c - Real.log r)
      ≤ Real.exp (ψ (x 2) * (Real.log c - Real.log r)) :=
    Real.exp_le_exp.mpr (by simpa using hmul)
  have hbase : Real.exp (Real.log c - Real.log r) * r = c := by
    rw [Real.exp_sub, Real.exp_log hc, Real.exp_log hrpos, div_mul_cancel₀ c (ne_of_gt hrpos)]
  rw [levelOf_clampedSweep, clampScale]
  calc c = Real.exp (Real.log c - Real.log r) * r := hbase.symm
    _ ≤ Real.exp (ψ (x 2) * (Real.log c - Real.log r)) * r :=
        mul_le_mul_of_nonneg_right hexp (le_of_lt hrpos)

/-- **The sweep of a plane *above* the truncation level never overshoots the plane's level**
(locally): for a cutoff with values in `[0,1]` on `[0,1]` and `c ≤ levelOf (P (x 0, x 1))`,
`levelOf (clampedSweep c ψ P x) ≤ levelOf (P (x 0, x 1))`. -/
theorem levelOf_clampedSweep_le_local {c : ℝ} (hc : 0 < c) {ψ : ℝ → ℝ}
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (x : EuclideanSpace ℝ (Fin 3))
    (hx : x 2 ∈ Set.Icc (0 : ℝ) 1)
    (hr : c ≤ levelOf (P (mk2 (x 0) (x 1)))) :
    levelOf (clampedSweep c ψ P x) ≤ levelOf (P (mk2 (x 0) (x 1))) := by
  set r : ℝ := levelOf (P (mk2 (x 0) (x 1))) with hrdef
  have hrpos : 0 < r := by rw [hrdef]; exact levelOf_pos _
  have hlog : Real.log c - Real.log r ≤ 0 := by
    have := Real.log_le_log hc hr
    linarith
  have hu0 : 0 ≤ ψ (x 2) := (hψ01 (x 2) hx).1
  have hexp : Real.exp (ψ (x 2) * (Real.log c - Real.log r)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos hu0 hlog)
  rw [levelOf_clampedSweep, clampScale]
  exact mul_le_of_le_one_left (le_of_lt hrpos) hexp

end

end Work.Drive
