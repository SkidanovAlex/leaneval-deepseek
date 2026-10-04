import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.periodization_contDiff_periodic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The periodization of an arbitrary smooth compactly supported function

For a smooth `Φ : (ι → ℝ) → ℂ` with compact support, the periodization

`P z = ∑' m : ι → ℤ, Φ (z + iVec m)`

is smooth and `1`-periodic in every coordinate.

This generalises `Work.Diff.STE.periodization_contDiff_periodic`, which needs the support of `Φ`
to be contained in the open unit cube `(-1/2, 1/2)^ι`.  Here only compactness of the support is
assumed, so the standard *local finiteness* argument is used: at a point `z` the sum is finite
(only the multi-indices in a box depending on `z` can contribute, because the support of `Φ` is
contained in a box), and the same box already carries the whole sum on a neighbourhood of `z`.
Hence, locally, the periodization is a finite sum of translates of `Φ`, which is smooth.

The periodicity is, as in the cube-supported case, a pure reindexing of the sum
(`Equiv.addLeft`), and needs no hypothesis at all on `Φ`.
-/

noncomputable section

namespace Work.Diff.STE.B3.SymCalcStep8

open Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A smooth compactly supported function has its topological support inside a coordinate box:
there is `R ≥ 0` with `|y i| ≤ R` for every `y` in the (compact) support. -/
lemma exists_bound_tsupport {Φ : (ι → ℝ) → ℂ} (hcs : HasCompactSupport Φ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y ∈ tsupport Φ, ∀ i, |y i| ≤ R := by
  have hb : Bornology.IsBounded (tsupport Φ) := hcs.isBounded
  rw [Metric.isBounded_iff_subset_closedBall (0 : ι → ℝ)] at hb
  obtain ⟨r, hr⟩ := hb
  refine ⟨max r 0, le_max_right _ _, fun y hy i => ?_⟩
  have h1 : ‖y‖ ≤ r := by
    have := hr hy
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have h2 : |y i| ≤ ‖y‖ := by
    have := norm_le_pi_norm y i
    simpa [Real.norm_eq_abs] using this
  exact le_trans h2 (le_trans h1 (le_max_left _ _))

/-- The periodization of a smooth compactly supported function is smooth at every point: near `z`
only the multi-indices in the box `|m i| ≤ ⌊|z i| + R⌋ + 2` contribute, so the sum coincides with
a finite sum of translates of `Φ` on a neighbourhood of `z`. -/
lemma contDiffAt_periodization_compact {Φ : (ι → ℝ) → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hcs : HasCompactSupport Φ) (z : ι → ℝ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => ∑' m : ι → ℤ, Φ (y + iVec m)) z := by
  classical
  obtain ⟨R, hR0, hR⟩ := exists_bound_tsupport hcs
  set N : ι → ℤ := fun i => ⌊|z i| + R⌋ + 2 with hN
  set S : Finset (ι → ℤ) := Fintype.piFinset (fun i => Finset.Icc (-(N i)) (N i)) with hS
  have hfin : ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => ∑ m ∈ S, Φ (y + iVec m)) := by
    apply ContDiff.sum
    intro m _
    exact hΦ.comp (by simpa using (contDiff_id.add (contDiff_const :
      ContDiff ℝ (⊤ : ℕ∞) (fun _ : ι → ℝ => iVec m))))
  refine hfin.contDiffAt.congr_of_eventuallyEq ?_
  refine Filter.eventually_of_mem (Metric.ball_mem_nhds z (by norm_num : (0 : ℝ) < 1 / 2)) ?_
  intro y hy
  show (∑' m : ι → ℤ, Φ (y + iVec m)) = ∑ m ∈ S, Φ (y + iVec m)
  rw [tsum_eq_sum (s := S) ?_]
  intro m hm
  by_contra hc
  have hmem : y + iVec m ∈ tsupport Φ := subset_tsupport _ (Function.mem_support.mpr hc)
  have hyi : ∀ i, |y i| ≤ |z i| + 1 / 2 := by
    intro i
    have h1 : |y i - z i| ≤ ‖y - z‖ := by
      rw [← Real.norm_eq_abs (y i - z i), ← Pi.sub_apply]
      exact norm_le_pi_norm _ i
    have h2 : ‖y - z‖ < 1 / 2 := by
      have := hy; rw [Metric.mem_ball, dist_eq_norm] at this; exact this
    calc |y i| = |(y i - z i) + z i| := by ring_nf
      _ ≤ |y i - z i| + |z i| := abs_add_le _ _
      _ ≤ |z i| + 1 / 2 := by linarith
  have hmi : ∀ i, m i ∈ Finset.Icc (-(N i)) (N i) := by
    intro i
    have h1 : |y i + ((m i : ℤ) : ℝ)| ≤ R := by
      have := hR (y + iVec m) hmem i
      simpa [Pi.add_apply, iVec_apply] using this
    have h2 : |((m i : ℤ) : ℝ)| ≤ R + |z i| + 1 / 2 := by
      have h3 : |((m i : ℤ) : ℝ)| = |(y i + ((m i : ℤ) : ℝ)) - y i| := by ring_nf
      rw [h3]
      calc |(y i + ((m i : ℤ) : ℝ)) - y i| ≤ |y i + ((m i : ℤ) : ℝ)| + |y i| := by
            rw [sub_eq_add_neg]
            calc |(y i + ((m i : ℤ) : ℝ)) + (-y i)|
                ≤ |y i + ((m i : ℤ) : ℝ)| + |-y i| := abs_add_le _ _
              _ = |y i + ((m i : ℤ) : ℝ)| + |y i| := by rw [abs_neg]
        _ ≤ R + |z i| + 1 / 2 := by linarith [hyi i]
    have h3 : |((m i : ℤ) : ℝ)| < ((N i : ℤ) : ℝ) := by
      have h4 : |z i| + R + 1 / 2 < ((⌊|z i| + R⌋ + 2 : ℤ) : ℝ) := by
        have := Int.lt_floor_add_one (|z i| + R)
        push_cast
        linarith
      rw [hN]
      calc |((m i : ℤ) : ℝ)| ≤ R + |z i| + 1 / 2 := h2
        _ = |z i| + R + 1 / 2 := by ring
        _ < _ := h4
    have h6 : |m i| < N i := by
      rw [← Int.cast_abs] at h3
      exact_mod_cast h3
    exact Finset.mem_Icc.mpr (by have h := (abs_lt.mp h6); constructor <;> omega)
  exact hm (by rw [hS]; exact Fintype.mem_piFinset.mpr hmi)

/-- The periodization of a smooth compactly supported function is smooth. -/
lemma contDiff_periodization_compact {Φ : (ι → ℝ) → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hcs : HasCompactSupport Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ι → ℝ => ∑' m : ι → ℤ, Φ (z + iVec m)) :=
  contDiff_iff_contDiffAt.mpr (fun z => contDiffAt_periodization_compact hΦ hcs z)

/-- The periodization of any function is `1`-periodic in every coordinate; this is a reindexing of
the sum by the translation `m ↦ eᵢ + m` on `ι → ℤ`. -/
lemma periodic_periodization_compact (Φ : (ι → ℝ) → ℂ) :
    Periodic1 (fun z : ι → ℝ => ∑' m : ι → ℤ, Φ (z + iVec m)) := by
  intro i x
  change ∑' m : ι → ℤ, Φ ((x + Pi.single i 1) + iVec m) = ∑' m : ι → ℤ, Φ (x + iVec m)
  have h : ∀ m : ι → ℤ, Φ ((x + Pi.single i 1) + iVec m)
      = Φ (x + iVec (Pi.single i (1 : ℤ) + m)) := by
    intro m
    congr 1
    funext j
    by_cases hji : j = i
    · subst hji; simp [Pi.single_eq_same]; ring
    · simp [Pi.single_eq_of_ne hji]
  rw [tsum_congr h]
  exact (Equiv.addLeft (Pi.single i (1 : ℤ))).tsum_eq (fun n : ι → ℤ => Φ (x + iVec n))

theorem periodization_compact_contDiff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Φ : (ι → ℝ) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hcs : HasCompactSupport Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ι → ℝ => ∑' m : ι → ℤ, Φ (z + Work.Diff.STE.iVec m)) ∧
      Work.Diff.STE.Periodic1 (fun z : ι → ℝ => ∑' m : ι → ℤ, Φ (z + Work.Diff.STE.iVec m)) :=
  ⟨contDiff_periodization_compact hΦ hcs, periodic_periodization_compact Φ⟩

end Work.Diff.STE.B3.SymCalcStep8
