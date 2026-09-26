import Mathlib
import Submission.Work.Smooth.JordanSeparation.Defs

/-!
# The far-chord bound for a simple closed plane curve

A simple `C¹` closed plane curve `c` (injective on one period `[0, 2π)`) separates parameters that
are *far apart* modulo `2π`: two parameters `t, t' ∈ [0, 2π)` whose distance `|t' - t|` lies in a
closed window `[ε, 2π - ε]` with `0 < ε ≤ π` have images bounded away from each other by a positive
constant `η` depending only on `c` and `ε`.

The proof is the standard compactness argument.  The function `(t, t') ↦ ‖γ t - γ t'‖` is
continuous on the compact square `[0, 2π]²`; on the closed subset where `ε ≤ |t' - t| ≤ 2π - ε`
it is strictly positive — the pair `(0, π)` lies in that set because `ε ≤ π`, and any pair there
has distinct images because a common image forces the two parameters to be congruent modulo `2π`
(periodicity) and hence, since both lie in `[0, 2π]`, to differ by `0` or `±2π`, both of which are
excluded by the window.  The extreme value theorem (`IsCompact.exists_isMinOn`) then produces the
uniform positive lower bound.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- The canonical representative in `[0, 2π)` of a parameter: `2π` is sent to `0`, everything
else is fixed. -/
def modTwoPi (x : ℝ) : ℝ := if x = 2 * Real.pi then 0 else x

theorem modTwoPi_of_lt {x : ℝ} (h : x < 2 * Real.pi) : modTwoPi x = x := by
  unfold modTwoPi; rw [if_neg (ne_of_lt h)]

theorem modTwoPi_of_eq {x : ℝ} (h : x = 2 * Real.pi) : modTwoPi x = 0 := by
  unfold modTwoPi; rw [if_pos h]

/-- **The far-chord positivity.**  If `t, t' ∈ [0, 2π]` and `ε ≤ |t' - t| ≤ 2π - ε` with `ε > 0`
for a `2π`-periodic curve injective on `[0, 2π)`, then `γ t ≠ γ t'`.  Indeed, a common image forces
the canonical representatives `modTwoPi t`, `modTwoPi t' ∈ [0, 2π)` to be equal, which leaves only
`t = t'` or `{t, t'} = {0, 2π}`, both excluded by the window. -/
theorem gamma_ne_of_far (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    (hsimple : c.toPlaneCurve.IsSimple) {ε : ℝ} (hε : 0 < ε)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) (2 * Real.pi))
    (hb : b ∈ Set.Icc (0 : ℝ) (2 * Real.pi))
    (hlo : ε ≤ |b - a|) (hhi : |b - a| ≤ 2 * Real.pi - ε) :
    c.γ a ≠ c.γ b := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  intro hγ
  have hu_mem : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      modTwoPi x ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
    intro x hx
    rcases lt_or_eq_of_le hx.2 with h | h
    · rw [modTwoPi_of_lt h]; exact ⟨hx.1, h⟩
    · rw [modTwoPi_of_eq h]; exact ⟨le_refl 0, h2pi⟩
  have hu_per : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi), c.γ (modTwoPi x) = c.γ x := by
    intro x hx
    rcases lt_or_eq_of_le hx.2 with h | h
    · rw [modTwoPi_of_lt h]
    · rw [modTwoPi_of_eq h, h]; simpa using (c.periodic 0).symm
  have hu_ne : modTwoPi a ≠ modTwoPi b := by
    intro h
    rcases lt_or_eq_of_le ha.2 with h1 | h1
    · rcases lt_or_eq_of_le hb.2 with h2 | h2
      · rw [modTwoPi_of_lt h1, modTwoPi_of_lt h2] at h
        have : |b - a| = 0 := by rw [h]; simp
        rw [this] at hlo; linarith
      · rw [modTwoPi_of_lt h1, modTwoPi_of_eq h2] at h
        have ha0 : a = 0 := h
        have habs : |b - a| = 2 * Real.pi := by
          rw [h2, ha0, sub_zero, abs_of_pos h2pi]
        rw [habs] at hhi; linarith
    · rcases lt_or_eq_of_le hb.2 with h2 | h2
      · rw [modTwoPi_of_eq h1, modTwoPi_of_lt h2] at h
        have hb0 : b = 0 := h.symm
        have habs : |b - a| = 2 * Real.pi := by
          rw [hb0, h1, zero_sub, abs_neg, abs_of_pos h2pi]
        rw [habs] at hhi; linarith
      · rw [modTwoPi_of_eq h1, modTwoPi_of_eq h2] at h
        have : |b - a| = 0 := by rw [h1, h2]; simp
        rw [this] at hlo; linarith
  have hkey : c.γ (modTwoPi a) = c.γ (modTwoPi b) := by
    rw [hu_per a ha, hu_per b hb, hγ]
  exact hu_ne (hsimple (hu_mem a ha) (hu_mem b hb) hkey)

theorem far_chord_bound (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    (hsimple : c.toPlaneCurve.IsSimple) {ε : ℝ} (hε : 0 < ε) (hεπ : ε ≤ Real.pi) :
    ∃ η : ℝ, 0 < η ∧ ∀ t t' : ℝ, t ∈ Set.Ico 0 (2 * Real.pi) →
      t' ∈ Set.Ico 0 (2 * Real.pi) → ε ≤ |t' - t| → |t' - t| ≤ 2 * Real.pi - ε →
        η ≤ ‖c.γ t - c.γ t'‖ := by
  -- The compact set of "far" pairs of parameters.
  set S : Set (ℝ × ℝ) := {p | p.1 ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧
      p.2 ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧ ε ≤ |p.2 - p.1| ∧
      |p.2 - p.1| ≤ 2 * Real.pi - ε} with hS_def
  have hsub : S ⊆ Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    intro p hp; rw [hS_def] at hp; exact ⟨hp.1, hp.2.1⟩
  have hclosed : IsClosed S := by
    have heq : S = (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) ∩
        {p : ℝ × ℝ | |p.2 - p.1| ∈ Set.Icc ε (2 * Real.pi - ε)} := by
      ext p
      rw [hS_def, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_ofPred_eq,
        Set.mem_Icc, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩
    rw [heq]
    exact (isClosed_Icc.prod isClosed_Icc).inter
      (isClosed_Icc.preimage (continuous_snd.sub continuous_fst).abs)
  have hS_compact : IsCompact S :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hclosed hsub
  -- `S` is nonempty, because `ε ≤ π` makes `(0, π)` a far pair.
  have hSne : S.Nonempty := by
    refine ⟨((0 : ℝ), Real.pi), ?_⟩
    rw [hS_def]
    refine ⟨⟨le_refl 0, by linarith [Real.pi_pos]⟩,
      ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩, ?_, ?_⟩
    · rw [sub_zero, abs_of_pos Real.pi_pos]; exact hεπ
    · rw [sub_zero, abs_of_pos Real.pi_pos]; linarith
  have hf_cont : Continuous fun p : ℝ × ℝ => ‖c.γ p.1 - c.γ p.2‖ :=
    ((c.cont.comp continuous_fst).sub (c.cont.comp continuous_snd)).norm
  have hf_pos : ∀ p ∈ S, 0 < ‖c.γ p.1 - c.γ p.2‖ := by
    intro p hp
    rw [hS_def] at hp
    exact norm_pos_iff.mpr (sub_ne_zero.mpr
      (gamma_ne_of_far c hsimple hε hp.1 hp.2.1 hp.2.2.1 hp.2.2.2))
  -- The extreme value theorem: the minimum of the chord length on the compact far set.
  obtain ⟨p, hp_mem, hmin⟩ := hS_compact.exists_isMinOn hSne hf_cont.continuousOn
  rw [isMinOn_iff] at hmin
  refine ⟨‖c.γ p.1 - c.γ p.2‖, hf_pos p hp_mem, ?_⟩
  intro t t' ht ht' hlo hhi
  exact hmin (t, t') (by
    rw [hS_def]; exact ⟨⟨ht.1, ht.2.le⟩, ⟨ht'.1, ht'.2.le⟩, hlo, hhi⟩)

end

end Work.Smooth.JordanSeparation
