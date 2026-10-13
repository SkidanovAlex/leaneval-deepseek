import Mathlib

set_option autoImplicit false

open scoped Topology

namespace Work.WilE2

/-- Gluing two functions at a common point `a` at which they have the same derivative.

If `f a = g a` and both `f` and `g` have derivative `c` at `a`, then the piecewise function
`u ↦ if u ≤ a then f u else g u` has derivative `c` at `a` as well.

The content is that `HasDerivAt` is a two-sided (punctured) statement, and it is the conjunction
of the two one-sided statements on `Iic a` and `Ioi a`: on each of them the glued function agrees
with `f` resp. `g`, and `Iic a ∪ Ioi a = univ`. -/
private lemma glue_hasDerivAt_pt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {a : ℝ} {c : E} (hfa : f a = g a)
    (hf : HasDerivAt f c a) (hg : HasDerivAt g c a) :
    HasDerivAt (fun u => if u ≤ a then f u else g u) c a := by
  rw [← hasDerivWithinAt_univ]
  rw [show (Set.univ : Set ℝ) = Set.Iic a ∪ Set.Ioi a from (Set.Iic_union_Ioi (a := a)).symm]
  apply HasDerivWithinAt.union
  · refine hf.hasDerivWithinAt.congr ?_ ?_
    · intro u hu; rw [ite_eq_left (Set.mem_Iic.mp hu)]
    · simp [hfa]
  · refine hg.hasDerivWithinAt.congr ?_ ?_
    · intro u hu
      rw [Set.mem_Ioi] at hu
      rw [ite_eq_right (not_le.mpr hu)]
    · simp [hfa]

theorem glue_integral_curve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : E → E} {f g : ℝ → E} {a : ℝ} (hfa : f a = g a)
    (hf : ∀ t ≤ a, HasDerivAt f (v (f t)) t) (hg : ∀ t, a ≤ t → HasDerivAt g (v (g t)) t) :
    ∀ t, HasDerivAt (fun u => if u ≤ a then f u else g u)
      (v ((fun u => if u ≤ a then f u else g u) t)) t := by
  intro t
  let h : ℝ → E := fun u => if u ≤ a then f u else g u
  change HasDerivAt h (v (h t)) t
  have hval_f : ∀ u ≤ a, h u = f u := fun u hu => by
    show (if u ≤ a then f u else g u) = f u
    rw [ite_eq_left hu]
  have hval_g : ∀ u, a < u → h u = g u := fun u hu => by
    show (if u ≤ a then f u else g u) = g u
    rw [ite_eq_right (not_le.mpr hu)]
  rcases lt_trichotomy t a with ht | hta | ht
  · -- `t < a`: the glued function agrees with `f` near `t`.
    have heq : h =ᶠ[𝓝 t] f := by
      filter_upwards [IsOpen.mem_nhds isOpen_Iio ht] with u hu
      exact hval_f u hu.le
    have hft : HasDerivAt h (v (f t)) t := heq.hasDerivAt_iff.mpr (hf t ht.le)
    rw [hval_f t ht.le]
    exact hft
  · -- `t = a`: use the one-sided information from `f` (on `Iic a`) and `g` (on `Ioi a`).
    rw [hta]
    have hg' : HasDerivAt g (v (f a)) a := by
      have h1 := hg a le_rfl
      rw [← hfa] at h1
      exact h1
    have key := glue_hasDerivAt_pt hfa (hf a le_rfl) hg'
    rw [hval_f a le_rfl]
    exact key
  · -- `a < t`: the glued function agrees with `g` near `t`.
    have heq : h =ᶠ[𝓝 t] g := by
      filter_upwards [IsOpen.mem_nhds isOpen_Ioi ht] with u hu
      exact hval_g u hu
    have hgt : HasDerivAt h (v (g t)) t := heq.hasDerivAt_iff.mpr (hg t ht.le)
    rw [hval_g t ht]
    exact hgt

end Work.WilE2
