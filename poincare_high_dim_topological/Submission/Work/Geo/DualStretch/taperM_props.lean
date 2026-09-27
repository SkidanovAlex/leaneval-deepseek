import Mathlib
import Submission.Work.Geo.DualStretch.Defs
import Submission.Work.Geo.DualStretch.coord_spec

namespace Work.Geo.DualStretch

open Set Metric
open scoped Classical

/-!
# Properties of the taper `taperM` (`taperM_props`)

`taperM β p P hP α M x = 1 + (M - 1) * clamp01 (infDist (segOf … x) (BdrySeg β) / ((β - α)/2))`
is the factor by which the high part of `x` is rescaled by the Stallings/Connell stretch.  We record
its three characteristic properties:

* it takes values in `[1, M]` (for `M ≥ 1`);
* it equals `1` on the join segments that lie in the boundary of the cube `closedCube β`
  (so the stretch is the identity there);
* it equals `M` on the join segments that meet the smaller cube `closedCube α`, because such a
  segment is at distance at least `β - α` from every segment lying in `bdryCube β`, and
  `β - α ≥ (β - α)/2`.

The essential geometric input is the last point: if `p` is a convex combination of `u, w` lying in
`closedCube α`, and `q` is a convex combination (with the *same* coefficient) of `v, z` with
`(v, z) ∈ BdrySeg β`, then `β = ‖q j‖ ≤ α + max (dist u v) (dist w z)`, whence
`β - α ≤ dist (u,w) (v,z)` for the product (max) metric.  Every point of a segment in `bdryCube β`
has a coordinate of absolute value `β`, and coordinates are bounded by the norm (which on
`EuclideanSpace` is the `ℓ²`-norm, so this is `PiLp.norm_apply_le`).
-/

variable {n : ℕ}

/-- A convex combination of two reals is bounded by the maximum of their absolute values. -/
private lemma abs_convex (t a b : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |(1 - t) * a + t * b| ≤ max |a| |b| := by
  obtain ⟨ht0, ht1⟩ := ht
  set M := max |a| |b| with hM
  have h1 : (1 - t) * |a| ≤ (1 - t) * M :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
  have h2 : t * |b| ≤ t * M := mul_le_mul_of_nonneg_left (le_max_right _ _) ht0
  calc |(1 - t) * a + t * b| ≤ |(1 - t) * a| + |t * b| := abs_add_le _ _
    _ = (1 - t) * |a| + t * |b| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t), abs_of_nonneg ht0]
    _ ≤ (1 - t) * M + t * M := add_le_add h1 h2
    _ = M := by ring

theorem taperM_props {n : ℕ} (hn : 0 < n) (P : PL.Cx n) (hP : P.faces.Finite) {β α M : ℝ} {p : ℕ}
    (hαβ : α < β) (hM : 1 ≤ M) :
    (∀ x : PL.E n, 1 ≤ Work.Geo.DualStretch.taperM β p P hP α M x ∧
        Work.Geo.DualStretch.taperM β p P hP α M x ≤ M) ∧
      (∀ x : PL.E n, Work.Geo.DualStretch.segOf β p P hP x ∈ Work.Geo.DualStretch.BdrySeg β →
        Work.Geo.DualStretch.taperM β p P hP α M x = 1) ∧
      (∀ x : PL.E n, (∃ t ∈ Set.Icc (0 : ℝ) 1,
          (1 - t) • (Work.Geo.DualStretch.segOf β p P hP x).1 +
            t • (Work.Geo.DualStretch.segOf β p P hP x).2 ∈ PL.closedCube α) →
        Work.Geo.DualStretch.taperM β p P hP α M x = M) := by
  have hhalf : 0 < (β - α) / 2 := by linarith
  have clamp_le : ∀ t : ℝ, clamp01 t ≤ 1 := fun t => max_le zero_le_one (min_le_left _ _)
  have clamp_nn : ∀ t : ℝ, 0 ≤ clamp01 t := fun t => le_max_left _ _
  refine ⟨fun x => ⟨?_, ?_⟩, ?_, ?_⟩
  · -- `1 ≤ taperM`
    unfold taperM
    have := clamp_nn (Metric.infDist (segOf β p P hP x) (BdrySeg β) / ((β - α) / 2))
    nlinarith [hM]
  · -- `taperM ≤ M`
    unfold taperM
    have := clamp_le (Metric.infDist (segOf β p P hP x) (BdrySeg β) / ((β - α) / 2))
    nlinarith [hM]
  · -- `taperM = 1` on the boundary segments
    intro x hx
    unfold taperM
    rw [Metric.infDist_zero_of_mem hx, zero_div]
    norm_num [clamp01]
  · -- `taperM = M` on the segments meeting `closedCube α`
    intro x ⟨t, ht, hpt⟩
    set q := segOf β p P hP x with hq
    have hpt' : (1 - t) • q.1 + t • q.2 ∈ PL.closedCube α := by
      rw [hq]; exact hpt
    let i : Fin n := ⟨0, hn⟩
    -- the hypothesis is non-vacuous, so `clamp01` is being applied to a non-empty configuration
    have hα0 : 0 ≤ α := by
      have h1 : |((1 - t) • q.1 + t • q.2) i| ≤ α := hpt' i
      linarith [abs_nonneg (((1 - t) • q.1 + t • q.2) i)]
    have hβ0 : 0 ≤ β := by linarith
    -- `BdrySeg β` is non-empty: it contains the constant segment at `β • eᵢ`
    have hSne : (BdrySeg (n := n) β).Nonempty := by
      refine ⟨(PiLp.single 2 i β, PiLp.single 2 i β), ?_⟩
      intro s hs
      have hc : (PiLp.single 2 i β : PL.E n) ∈ bdryCube β := by
        refine ⟨i, ?_⟩
        rw [show (PiLp.single 2 i β : PL.E n) i = β from by simp]
        exact abs_of_nonneg hβ0
      have hs' : (1 - s) • (PiLp.single 2 i β : PL.E n) + s • (PiLp.single 2 i β : PL.E n)
          = PiLp.single 2 i β := by module
      rw [hs']
      exact hc
    -- the key distance bound
    have hkey : ∀ r ∈ BdrySeg β, β - α ≤ dist q r := by
      intro r hr
      have hr' : ∃ j, |((1 - t) • r.1 + t • r.2) j| = β := hr t ht
      obtain ⟨j, hj⟩ := hr'
      have hPq : |((1 - t) • q.1 + t • q.2) j| ≤ α := hpt' j
      have hexp : ((1 - t) • q.1 + t • q.2) j - ((1 - t) • r.1 + t • r.2) j
          = (1 - t) * (q.1 j - r.1 j) + t * (q.2 j - r.2 j) := by
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        ring
      have hle1 : |((1 - t) • q.1 + t • q.2) j - ((1 - t) • r.1 + t • r.2) j|
          ≤ max |q.1 j - r.1 j| |q.2 j - r.2 j| := by
        rw [hexp]; exact abs_convex t _ _ ht
      have hc1 : |q.1 j - r.1 j| ≤ dist q.1 r.1 := by
        have h := PiLp.norm_apply_le (q.1 - r.1) j
        rw [dist_eq_norm]; simpa using h
      have hc2 : |q.2 j - r.2 j| ≤ dist q.2 r.2 := by
        have h := PiLp.norm_apply_le (q.2 - r.2) j
        rw [dist_eq_norm]; simpa using h
      have hmax : max |q.1 j - r.1 j| |q.2 j - r.2 j| ≤ dist q r := by
        rw [Prod.dist_eq]
        exact max_le_max hc1 hc2
      have htri : |((1 - t) • r.1 + t • r.2) j| ≤
          |((1 - t) • q.1 + t • q.2) j - ((1 - t) • r.1 + t • r.2) j| +
            |((1 - t) • q.1 + t • q.2) j| := by
        have h := abs_add_le (((1 - t) • r.1 + t • r.2) j - ((1 - t) • q.1 + t • q.2) j)
          (((1 - t) • q.1 + t • q.2) j)
        rw [sub_add_cancel, abs_sub_comm] at h
        exact h
      rw [hj] at htri
      linarith
    have hd : β - α ≤ Metric.infDist q (BdrySeg β) := (Metric.le_infDist hSne).mpr hkey
    have hone : 1 ≤ Metric.infDist q (BdrySeg β) / ((β - α) / 2) := by
      rw [one_le_div hhalf]; linarith
    have hclamp : clamp01 (Metric.infDist q (BdrySeg β) / ((β - α) / 2)) = 1 := by
      rw [clamp01, min_eq_left hone, max_eq_right zero_le_one]
    unfold taperM
    rw [← hq, hclamp]
    ring

end Work.Geo.DualStretch
