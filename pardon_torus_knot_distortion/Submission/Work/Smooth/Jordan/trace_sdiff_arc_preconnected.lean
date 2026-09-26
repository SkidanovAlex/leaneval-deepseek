import Mathlib
import Submission.Work.SphereJordan.gammaInjOnArc
import Submission.Work.Smooth.Jordan.Defs

/-!
# The complement of an arc of a simple closed curve is preconnected

For a simple closed plane curve `c : PlaneCurve` (`Work.Smooth.Jordan.PlaneCurve.IsSimple`, i.e.
injective on one period `[0, 2π)`) the trace is a topological circle.  Removing the image of an
arc of parameter length `< 2π` therefore leaves a (nonempty, when the arc is proper) arc, which is
preconnected.  This is the content of `trace_sdiff_arc_preconnected`.

The proof is purely order-theoretic and uses no topology of the plane: writing
`trace = γ '' [a, a + 2π]` (periodicity), a point of the trace lies outside `γ '' [a, b]` exactly
when it is `γ t` for some `t` in the open interval `(b, a + 2π)`.  Indeed the two parameter
intervals `[a, b]` and `[b, a + 2π]` meet in `{b, a + 2π}`, and distinct parameters of either
interval giving the same point must differ by a multiple of `2π`, which is impossible on the
length-`< 2π` ranges involved (`Work.SphereJordan.gamma_eq_imp_mod`).  The image of an interval
under a continuous map is preconnected, so the set is preconnected.
-/

open Set

namespace Work.Smooth.Jordan

noncomputable section

/-- **The trace of a `2π`-periodic curve is the image of any interval of length `2π`.**  In
particular `c.trace = c.γ '' Set.Icc a (a + 2 * Real.pi)`. -/
theorem trace_eq_image_Icc_shift (c : PlaneCurve) (a : ℝ) :
    c.trace = c.γ '' Set.Icc a (a + 2 * Real.pi) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨u, rfl⟩
    set k : ℤ := ⌊(u - a) / (2 * Real.pi)⌋ with hk
    refine ⟨u - (k:ℝ) * (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
    · have hpos : (0:ℝ) < 2 * Real.pi := by positivity
      have h := (le_div_iff₀ hpos).mp (Int.floor_le ((u - a) / (2 * Real.pi)))
      have : (k : ℝ) * (2 * Real.pi) ≤ u - a := by linarith
      linarith
    · have hpos : (0:ℝ) < 2 * Real.pi := by positivity
      have h := (div_lt_iff₀ hpos).mp (Int.lt_floor_add_one ((u - a) / (2 * Real.pi)))
      have : u - a < ((k:ℝ) + 1) * (2 * Real.pi) := by linarith
      linarith
    · have hper := c.periodic.int_mul k (u - (k:ℝ) * (2 * Real.pi))
      rw [show u - (k:ℝ) * (2*Real.pi) + (k:ℝ) * (2*Real.pi) = u from by ring] at hper
      exact hper.symm
  · rintro _ ⟨t, _, rfl⟩
    exact ⟨t, rfl⟩

theorem trace_sdiff_arc_preconnected {c : Work.Smooth.Jordan.PlaneCurve} (hs : c.IsSimple)
    {a b : ℝ} (hab : a ≤ b) (hlen : b - a < 2 * Real.pi) :
    IsPreconnected (c.trace \ c.γ '' (Set.Icc a b)) := by
  have htrace := trace_eq_image_Icc_shift c a
  have heq : c.trace \ c.γ '' (Set.Icc a b) = c.γ '' (Set.Ioo b (a + 2 * Real.pi)) := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨hxtr, hxnot⟩ := hx
      rw [htrace] at hxtr
      obtain ⟨t, ht, rfl⟩ := hxtr
      have htI : t ∈ Set.Ioo b (a + 2 * Real.pi) := by
        constructor
        · by_contra hcon
          push Not at hcon
          exact hxnot ⟨t, ⟨ht.1, hcon⟩, rfl⟩
        · by_contra hcon
          push Not at hcon
          have ht2 : t = a + 2 * Real.pi := le_antisymm ht.2 hcon
          refine hxnot ⟨a, ⟨le_refl a, hab⟩, ?_⟩
          rw [ht2]
          exact (c.periodic a).symm
      exact ⟨t, htI, rfl⟩
    · rintro _ ⟨t, ht, rfl⟩
      refine ⟨⟨t, rfl⟩, ?_⟩
      rintro ⟨s, hs', hse⟩
      obtain ⟨k, hk⟩ := Work.SphereJordan.gamma_eq_imp_mod hs hse
      have hk_lt : (k:ℝ) * (2*Real.pi) < 0 := by
        have : s - t < 0 := by linarith [hs'.2, ht.1]
        rw [hk] at this; linarith
      have hk_gt : -2 * Real.pi < (k:ℝ) * (2*Real.pi) := by
        have : a - (a + 2*Real.pi) < s - t := by linarith [hs'.1, ht.2]
        rw [hk] at this; linarith
      have h1 : (-1:ℝ) < (k:ℝ) := by nlinarith [hk_gt]
      have h2 : (k:ℝ) < 0 := by nlinarith [hk_lt]
      have hkg : (-1:ℤ) < k := by exact_mod_cast h1
      have hkl : k < (0:ℤ) := by exact_mod_cast h2
      omega
  rw [heq]
  exact (isPreconnected_Ioo (a := b) (b := a + 2 * Real.pi)).image c.γ c.cont.continuousOn

end

end Work.Smooth.Jordan
