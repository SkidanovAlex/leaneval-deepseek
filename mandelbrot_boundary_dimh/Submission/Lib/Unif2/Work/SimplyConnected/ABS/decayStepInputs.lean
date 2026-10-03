import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.GreenSetupReg
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.CircleSubMeanValue

/-!
# Inputs for the barrier comparison of the limsup Perron envelope

Two groups of elementary facts used by the comparison argument that bounds a member `v` of
`Submission.limFamily Ω f M` by `ε + C · u` near a boundary point `p`:

* the library notion `Submission.SubharmonicOnX` implies the *continuity-free* circle
  sub-mean-value inequality `CircleSubMeanValueAtX` (which drops the continuity clause);

* the *clamped barrier* `clampBarrier u V C = min (if x ∈ V then u x else C) C` is upper
  semicontinuous as soon as `u` is continuous on `V`: its sublevel sets are `V ∩ {u < t}` when
  `t ≤ C`, and `univ` when `C < t`.

With `SuperMVIOnX.neg_*` (`superMVIMinPrinciple.lean`) and
`usc_le_of_circleSubMeanValue_preconnected` (`lsc_le_of_circleSubMeanValue.lean`), these reduce the
minimum principle for the u.s.c. clamped barrier to the *proved* maximum principle for upper
semicontinuous functions satisfying the circle sub-mean-value inequality.
-/

open Filter Set
open Classical
open scoped Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ## From `Submission.SubharmonicOnX` to the continuity-free notion -/

/-- The library's subharmonicity at a point (which bundles continuity) implies the continuity-free
circle sub-mean-value inequality. -/
theorem CircleSubMeanValueAtX.of_subharmonicOnXAt {v : X → ℝ} {x : X}
    (h : Submission.SubharmonicOnXAt v x) : CircleSubMeanValueAtX v x := by
  rw [Submission.SubharmonicOnXAt, Submission.SubharmonicAtChart] at h
  obtain ⟨-, ρ, hρ, hsub, -, hmvi⟩ := h
  exact ⟨ρ, hρ, hsub, hmvi⟩

/-- The set version of `CircleSubMeanValueAtX.of_subharmonicOnXAt`. -/
theorem CircleSubMeanValueAtX.of_subharmonicOnX {v : X → ℝ} {U : Set X}
    (h : Submission.SubharmonicOnX v U) : ∀ x ∈ U, CircleSubMeanValueAtX v x :=
  fun x hx => CircleSubMeanValueAtX.of_subharmonicOnXAt (h.2 x hx)

/-! ## The clamped barrier -/

/-- The barrier `u` clamped above by `C` inside `V`, and set equal to `C` outside `V`. -/
def clampBarrier (u : X → ℝ) (V : Set X) (C : ℝ) : X → ℝ :=
  fun x => min (if x ∈ V then u x else C) C

theorem clampBarrier_of_mem {u : X → ℝ} {V : Set X} {C : ℝ} {x : X} (hx : x ∈ V) :
    clampBarrier u V C x = min (u x) C := by
  simp only [clampBarrier, if_pos hx]

theorem clampBarrier_of_not_mem {u : X → ℝ} {V : Set X} {C : ℝ} {x : X} (hx : x ∉ V) :
    clampBarrier u V C x = C := by
  simp only [clampBarrier, if_neg hx, min_self]

/-- The clamped barrier never exceeds `C`. -/
theorem clampBarrier_le (u : X → ℝ) (V : Set X) (C : ℝ) (x : X) :
    clampBarrier u V C x ≤ C := min_le_right _ _

/-- On `V` the clamped barrier is `min (u ·) C`. -/
theorem clampBarrier_eq_min {u : X → ℝ} {V : Set X} {C : ℝ} {x : X} (hx : x ∈ V) :
    clampBarrier u V C x = min (u x) C := clampBarrier_of_mem hx

/-- **Sublevel sets of the clamped barrier.**  For `t ≤ C` the set `{clampBarrier u V C < t}` is
`V ∩ {u < t}`; for `C < t` it is all of `X`. -/
theorem isOpen_setOf_clampBarrier_lt {u : X → ℝ} {V : Set X} (hVo : IsOpen V)
    (hcont : ContinuousOn u V) (C t : ℝ) :
    IsOpen {x : X | clampBarrier u V C x < t} := by
  by_cases ht : t ≤ C
  · have hset : {x : X | clampBarrier u V C x < t} = V ∩ u ⁻¹' Set.Iio t := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iio]
      constructor
      · intro hx
        by_cases hxV : x ∈ V
        · refine ⟨hxV, ?_⟩
          rw [clampBarrier_of_mem hxV] at hx
          rcases min_lt_iff.mp hx with h | h
          · exact h
          · exact absurd h (not_lt.mpr ht)
        · rw [clampBarrier_of_not_mem hxV] at hx
          exact absurd hx (not_lt.mpr ht)
      · rintro ⟨hxV, hxu⟩
        rw [clampBarrier_of_mem hxV]
        exact lt_of_le_of_lt (min_le_left _ _) hxu
    rw [hset]
    exact hcont.isOpen_inter_preimage hVo (isOpen_Iio (a := t))
  · push Not at ht
    have hset : {x : X | clampBarrier u V C x < t} = Set.univ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      by_cases hxV : x ∈ V
      · rw [clampBarrier_of_mem hxV]
        exact lt_of_le_of_lt (min_le_right _ _) ht
      · rw [clampBarrier_of_not_mem hxV]
        exact ht
    rw [hset]
    exact isOpen_univ

/-- **The clamped barrier is upper semicontinuous** as soon as `u` is continuous on `V`. -/
theorem upperSemicontinuousOn_clampBarrier {u : X → ℝ} {V : Set X} (hVo : IsOpen V)
    (hcont : ContinuousOn u V) (C : ℝ) :
    UpperSemicontinuousOn (clampBarrier u V C) Set.univ := by
  rw [upperSemicontinuousOn_iff_preimage_Iio]
  intro t
  exact ⟨{x : X | clampBarrier u V C x < t},
    isOpen_setOf_clampBarrier_lt hVo hcont C t, by ext x; simp⟩

end Work.SimplyConnected.ABS
