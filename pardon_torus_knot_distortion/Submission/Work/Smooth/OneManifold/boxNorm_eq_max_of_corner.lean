import Mathlib
import Submission.Work.Smooth.BoxGeneric.Defs

/-!
# The box norm near a corner is the maximum of the two tight faces

At a corner point `y` of the box sphere of level `s > 0` — two distinct signed faces `(i, ε)`,
`(j, ε')` are tight at `y` and the third face norm is strictly below `s` — the box norm agrees, on a
whole neighbourhood of `y`, with the maximum `max (faceLin c σ i ε) (faceLin c σ j ε')` of the two
tight signed faces.

This is the local identity used by the local models of the box-norm level set; it is the analogue
for corners of `Work.Smooth.BoxGeneric.LocalSurface.eventually_boxNorm_eq_faceLin`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Filter

namespace Work.Smooth.OneManifold

noncomputable section

open scoped Topology

/-- On the positive part of a signed face, the signed face is the face norm. -/
lemma faceNorm_eq_faceLin_of_nonneg {c : R3} {σ : Equiv.Perm (Fin 3)} {i : Fin 3}
    {ε : ℝ} {y : R3} (hε : ε = 1 ∨ ε = -1) (h : 0 ≤ Work.Smooth.BoxGeneric.faceLin c σ i ε y) :
    Work.Smooth.BoxGeneric.faceNorm c σ i y = Work.Smooth.BoxGeneric.faceLin c σ i ε y := by
  have habs : |ε| = 1 := by rcases hε with h | h <;> simp [h]
  have hsgn : Work.Smooth.BoxGeneric.signedFace c σ i y =
      ε * Work.Smooth.BoxGeneric.faceLin c σ i ε y := by
    rcases hε with h | h
    · rw [h, Work.Smooth.BoxGeneric.faceLin_one]; ring
    · rw [h, Work.Smooth.BoxGeneric.faceLin_neg_one]; ring
  rw [Work.Smooth.BoxGeneric.faceNorm_eq_abs_signedFace, hsgn, abs_mul, habs, one_mul,
    abs_of_nonneg h]

/-- **The box norm near a corner is the maximum of the two tight faces.** -/
theorem eventually_boxNorm_eq_max_of_corner {c : R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ} {y : R3}
    {i j : Fin 3} {ε ε' : ℝ} (hs : 0 < s) (hij : i ≠ j) (hε : ε = 1 ∨ ε = -1)
    (hε' : ε' = 1 ∨ ε' = -1)
    (hacti : Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε y)
    (hactj : Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s j ε' y)
    (huniq : ∀ k : Fin 3, k ≠ i → k ≠ j → Work.Smooth.BoxGeneric.faceNorm c σ k y < s) :
    ∀ᶠ x in nhds y, Submission.boxNorm c σ x =
      max (Work.Smooth.BoxGeneric.faceLin c σ i ε x)
        (Work.Smooth.BoxGeneric.faceLin c σ j ε' x) := by
  -- the two tight faces stay positive
  have hposi : ∀ᶠ x in nhds y, 0 < Work.Smooth.BoxGeneric.faceLin c σ i ε x :=
    (isOpen_lt continuous_const (Work.Smooth.BoxGeneric.contDiff_faceLin c σ i ε).continuous).mem_nhds
      (by show (0 : ℝ) < Work.Smooth.BoxGeneric.faceLin c σ i ε y; rw [hacti.1]; exact hs)
  have hposj : ∀ᶠ x in nhds y, 0 < Work.Smooth.BoxGeneric.faceLin c σ j ε' x :=
    (isOpen_lt continuous_const (Work.Smooth.BoxGeneric.contDiff_faceLin c σ j ε').continuous).mem_nhds
      (by show (0 : ℝ) < Work.Smooth.BoxGeneric.faceLin c σ j ε' y; rw [hactj.1]; exact hs)
  -- the third face stays strictly below the maximum of the two tight ones
  have hthird : ∀ᶠ x in nhds y, ∀ k : Fin 3, k ≠ i → k ≠ j →
      Work.Smooth.BoxGeneric.faceNorm c σ k x <
        max (Work.Smooth.BoxGeneric.faceLin c σ i ε x)
          (Work.Smooth.BoxGeneric.faceLin c σ j ε' x) := by
    rw [Filter.eventually_all]
    intro k
    by_cases hk : k ≠ i ∧ k ≠ j
    · obtain ⟨hki, hkj⟩ := hk
      have hne : ∀ᶠ x in nhds y, Work.Smooth.BoxGeneric.faceNorm c σ k x <
          max (Work.Smooth.BoxGeneric.faceLin c σ i ε x)
            (Work.Smooth.BoxGeneric.faceLin c σ j ε' x) :=
        (isOpen_lt (Work.Smooth.BoxGeneric.continuous_faceNorm c σ k)
          ((Work.Smooth.BoxGeneric.contDiff_faceLin c σ i ε).continuous.max
            (Work.Smooth.BoxGeneric.contDiff_faceLin c σ j ε').continuous)).mem_nhds (by
          show Work.Smooth.BoxGeneric.faceNorm c σ k y <
            max (Work.Smooth.BoxGeneric.faceLin c σ i ε y)
              (Work.Smooth.BoxGeneric.faceLin c σ j ε' y)
          rw [hacti.1, hactj.1, max_self]
          exact huniq k hki hkj)
      exact hne.mono (fun x hx _ _ => hx)
    · refine Filter.Eventually.of_forall fun x h1 h2 => ?_
      rcases not_and_or.mp hk with h | h
      · exact absurd (not_not.mp h) h1
      · exact absurd (not_not.mp h) h2
  filter_upwards [hposi, hposj, hthird] with x hxi hxj hx3
  have hnormi : Work.Smooth.BoxGeneric.faceNorm c σ i x =
      Work.Smooth.BoxGeneric.faceLin c σ i ε x :=
    faceNorm_eq_faceLin_of_nonneg hε (le_of_lt hxi)
  have hnormj : Work.Smooth.BoxGeneric.faceNorm c σ j x =
      Work.Smooth.BoxGeneric.faceLin c σ j ε' x :=
    faceNorm_eq_faceLin_of_nonneg hε' (le_of_lt hxj)
  refine le_antisymm ?_ ?_
  · rw [Work.Smooth.BoxGeneric.boxNorm_le_iff]
    intro k
    by_cases hki : k = i
    · rw [hki, hnormi]
      exact le_max_left _ _
    · by_cases hkj : k = j
      · rw [hkj, hnormj]
        exact le_max_right _ _
      · exact le_of_lt (hx3 k hki hkj)
  · rw [← hnormi, ← hnormj]
    exact max_le (Work.Smooth.BoxGeneric.faceNorm_le_boxNorm c σ i x)
      (Work.Smooth.BoxGeneric.faceNorm_le_boxNorm c σ j x)

end

end Work.Smooth.OneManifold
