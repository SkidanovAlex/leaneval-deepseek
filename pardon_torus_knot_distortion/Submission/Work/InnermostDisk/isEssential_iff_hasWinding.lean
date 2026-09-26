import Mathlib
import Submission.Work.InnermostDisk.Defs
import Submission.Work.TorusCover.Main

/-!
# Essential loops: `Work.CoreTopology.IsEssential` is `Work.TorusCover.IsEssential`

The two chapters of the development use two different (but equivalent) encodings of the
winding vector of a closed curve on a parametrised torus `P`:

* `Work.CoreTopology.IsEssential P γ` says that some `LiftOf P γ` — a pair of continuous
  parameter functions `(Θ, Φ)` with `P.psi (Θ t) (Φ t) = γ t` — has nonzero winding vector,
  where the winding vector is read off from the displacement of the lift over one period
  (`Work.CoreTopology.LiftOf.winding`).
* `Work.TorusCover.IsEssential P.psi γ.γ` says that there is a nonzero `v : ℤ × ℤ` and a
  *periodic* lift `Λ : ℝ → ℝ × ℝ` of `γ` with `Λ (t + 2π) = Λ t + periodShift v`.

The two are the same notion: the parameters of a lift are exactly the coordinates of a lift in
the `Work.TorusCover` sense, and `LiftOf.winding` is characterised (`LiftOf.winding_spec`) by
the displacement of the parameters over one period `[0, 2π]`, which is what `IsPeriodicLift`
records.  This file records the equivalence so that results proved in either vocabulary apply
in the other.

The bridge is used, in particular, to transport the innermost-disc machinery
(`Work.InnermostDisk.Defs`) — which is phrased in `Work.CoreTopology` terms because the discs
and spheres live in `ℝ³` — to the covering-space results of `Work.TorusCover`.
-/

open Work.CoreTopology

namespace Work.InnermostDisk

noncomputable section

/-- **A `LiftOf` is determined by its displacement over one period.**  If the parameters of a
lift `L` advance, over the period `[0, 2π]`, by `2π` times a pair of integers `v`, then `v` is
the winding vector of `L`.  (Conversely `LiftOf.winding_spec` gives exactly this displacement
for `L.winding`, so this is the uniqueness half of the characterisation of the winding
vector.) -/
lemma winding_eq_of_displacement {P : Work.CoreTopology.ParamTorus}
    {γ : Work.CoreTopology.ClosedCurve P} (L : Work.CoreTopology.LiftOf P γ) (v : ℤ × ℤ)
    (h1 : L.Θ (2 * Real.pi) = L.Θ 0 + (v.1 : ℝ) * (2 * Real.pi))
    (h2 : L.Φ (2 * Real.pi) = L.Φ 0 + (v.2 : ℝ) * (2 * Real.pi)) :
    L.winding = v := by
  have hspec := L.winding_spec
  have hne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hfst : ((L.winding).1 : ℝ) = (v.1 : ℝ) := by
    apply mul_right_cancel₀ hne
    linarith [hspec.1, h1]
  have hsnd : ((L.winding).2 : ℝ) = (v.2 : ℝ) := by
    apply mul_right_cancel₀ hne
    linarith [hspec.2, h2]
  exact Prod.ext (by exact_mod_cast hfst) (by exact_mod_cast hsnd)

/-- **`Work.CoreTopology.IsEssential` agrees with `Work.TorusCover.IsEssential`.**

A closed curve `γ` on the surface `P.carrier` of a parametrised torus is essential in the sense
of the `Work.CoreTopology` vocabulary (a lift whose parameters do not return to themselves
after one period) if and only if it is essential in the sense of the covering-space vocabulary
of `Work.TorusCover` (a nonzero winding vector `v`, realised by a lift advancing by the period
shift `periodShift v` over one period).

Both directions are the translation of the parameters `(Θ, Φ)` of a lift into the lift
`Λ : ℝ → ℝ × ℝ` of `Work.TorusCover` and back.  In the forward direction the displacement over
one period is `periodShift L.winding` by `LiftOf.period_shift_winding`; in the backward
direction it is read off at `t = 0`, and `winding_eq_of_displacement` identifies the winding
vector of the resulting `LiftOf` with `v`. -/
theorem isEssential_iff_hasWinding (P : Work.CoreTopology.ParamTorus)
    (γ : Work.CoreTopology.ClosedCurve P) :
    Work.CoreTopology.IsEssential P γ ↔ Work.TorusCover.IsEssential P.psi γ.γ := by
  constructor
  · -- A lift with nonzero winding vector is a periodic lift through `periodShift`.
    rintro ⟨L, hL⟩
    refine ⟨L.winding, hL, ⟨fun t => (L.Θ t, L.Φ t), ⟨L.contΘ.prodMk L.contΦ, ?_⟩, ?_⟩⟩
    · intro t; exact L.lifts t
    · intro t
      obtain ⟨h1, h2⟩ := L.period_shift_winding t
      refine Prod.ext ?_ ?_ <;>
        simp only [Work.TorusCover.periodShift, Prod.fst_add, Prod.snd_add]
      · exact h1
      · exact h2
  · -- A periodic lift through `periodShift v` gives a lift with winding vector `v`.
    rintro ⟨v, hv, Λ, ⟨hcont, hmap⟩, hshift⟩
    have hs := hshift 0
    simp only [zero_add] at hs
    have h1 : (Λ (2 * Real.pi)).1 = (Λ 0).1 + (v.1 : ℝ) * (2 * Real.pi) :=
      congrArg Prod.fst (by simpa [Work.TorusCover.periodShift] using hs)
    have h2 : (Λ (2 * Real.pi)).2 = (Λ 0).2 + (v.2 : ℝ) * (2 * Real.pi) :=
      congrArg Prod.snd (by simpa [Work.TorusCover.periodShift] using hs)
    let L : Work.CoreTopology.LiftOf P γ :=
      { Θ := fun t => (Λ t).1
        Φ := fun t => (Λ t).2
        contΘ := continuous_fst.comp hcont
        contΦ := continuous_snd.comp hcont
        lifts := hmap }
    refine ⟨L, ?_⟩
    have h1' : L.Θ (2 * Real.pi) = L.Θ 0 + (v.1 : ℝ) * (2 * Real.pi) := by simpa [L] using h1
    have h2' : L.Φ (2 * Real.pi) = L.Φ 0 + (v.2 : ℝ) * (2 * Real.pi) := by simpa [L] using h2
    show L.winding ≠ (0, 0)
    rw [winding_eq_of_displacement L v h1' h2']
    exact hv

end

end Work.InnermostDisk
