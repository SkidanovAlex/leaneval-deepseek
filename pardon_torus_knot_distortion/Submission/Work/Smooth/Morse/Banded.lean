import Mathlib
import Submission.Work.Smooth.Morse.Sweep
import Submission.Work.Smooth.Morse.Flow
import Submission.Work.Smooth.Morse.Sweep.windingSpan_locally_const_of_regularValue
import Submission.Work.Smooth.Morse.MorseModel.windingSpan_locally_const_of_span_eq

/-!
# The sweep restricted to a band of levels

`Submission.Work.Smooth.Morse.Sweep` proves that the winding span of the sublevel regions
`region ψ g t = F ∩ {g < t}` is *independent of* `t`, from the local models at *every* critical
value.  For the application to Pardon's box family this is more than is available (and more than is
needed): the box is swept only through a bounded band of scales `t ∈ [a,b]`, and the general
position of Pardon's family of spheres is only controlled in that band.  This file proves the
*banded* form of the whole sweep chapter:

* `Work.Smooth.Morse.eq_of_locally_constOn` — a quantity on `ℝ` which is locally constant at every
  point of `[a,b]` is constant on `[a,b]` (the banded form of
  `Work.SurgeryInvariance.eq_of_locally_const`, via the preconnectedness of the unit interval);

* `Work.Smooth.Morse.windingSpan_locally_const_of_level_on`,
  `Work.Smooth.Morse.windingSpan_eq_of_levelSweep_on`,
  `Work.Smooth.Morse.containsEssentialLoop_iff_of_levelSweep_on` — the transport/crossing inputs
  only for critical values in the band;

* `Work.Smooth.Morse.windingSpan_locally_const_of_crossing_on`,
  `Work.Smooth.Morse.windingSpan_eq_of_levelSweep_of_crossing_on`,
  `Work.Smooth.Morse.containsEssentialLoop_iff_of_levelSweep_of_crossing_on`,
  `Work.Smooth.Morse.containsEssentialLoop_of_levelSweep_of_crossing_on` — the same with the
  transport input discharged by
  `Work.Smooth.Morse.regularEquivalent_of_contDiff` (item 3).

The `_on` suffix always means "with the hypotheses restricted to the band `Set.Icc a b`".
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse

noncomputable section

variable {ψ : Submission.Diffeo} {g : R3 → ℝ} {a b : ℝ}

/-- **A quantity on `ℝ` which is locally constant at every point of `[a,b]` is constant on
`[a,b]`.**  This is the banded form of `Work.SurgeryInvariance.eq_of_locally_const`: the local
models of the sweep are only available on a bounded band of levels, and the argument works on the
subtype `↥(Set.Icc a b)` because `Set.Icc a b` is preconnected. -/
theorem eq_of_locally_constOn {α : Type*} {f : ℝ → α} {a b : ℝ}
    (h : ∀ x ∈ Set.Icc a b, ∃ ε : ℝ, 0 < ε ∧ ∀ y : ℝ, |y - x| < ε → f y = f x)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) : f s = f t := by
  have hlc : IsLocallyConstant (fun x : Set.Icc a b => f (x : ℝ)) := by
    intro u
    rw [Metric.isOpen_iff]
    intro x hx
    obtain ⟨ε, hε, hc⟩ := h (x : ℝ) x.2
    refine ⟨ε, hε, fun y hy => ?_⟩
    have hy' : |(y : ℝ) - (x : ℝ)| < ε := by
      have h1 : dist (y : ℝ) (x : ℝ) < ε := by
        simpa only [Metric.mem_ball, Subtype.dist_eq] using hy
      simpa [Real.dist_eq] using h1
    show f (y : ℝ) ∈ u
    rw [hc (y : ℝ) hy']
    exact hx
  have : PreconnectedSpace (Set.Icc a b) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  exact IsLocallyConstant.apply_eq_of_isPreconnected hlc isPreconnected_univ
    (x := (⟨s, hs⟩ : Set.Icc a b)) (y := (⟨t, ht⟩ : Set.Icc a b))
    (mem_univ _) (mem_univ _)

/-! ## The banded sweep with the local models as hypotheses -/

/-- **The local constancy of the winding span at a point of the band**, from the transport input
`RegularEquivalent ψ g` (item 3) at the regular points and the local model `DiscModel ψ g t₀` at the
critical values of the band. -/
theorem windingSpan_locally_const_of_level_on (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hg : Continuous g) (hcrit : LocallyFiniteCriticalValues ψ g) (hreg : RegularEquivalent ψ g)
    (hdisc : ∀ t₀ ∈ criticalValues ψ g ∩ Set.Icc a b, DiscModel ψ g t₀)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - x| < ε →
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g s) =
        Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g x) := by
  by_cases h : IsRegularValue ψ g x
  · exact Work.Smooth.Morse.Sweep.windingSpan_locally_const_of_regularValue ψ hcrit hreg h
  · exact Work.Smooth.Morse.MorseModel.windingSpan_locally_const ψ hg
      (hdisc x ⟨not_not.mp h, hx⟩)

/-- **The banded sweep theorem, with the transport as a hypothesis.**  If the sweep data of the
level family of `g` is available on the band — the Morse/Sard input, the transport
`RegularEquivalent` across regular intervals, and the local model `DiscModel` at the critical
values *of the band* — then the two winding spans agree. -/
theorem windingSpan_eq_of_levelSweep_on (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hg : Continuous g) (hcrit : LocallyFiniteCriticalValues ψ g) (hreg : RegularEquivalent ψ g)
    (hdisc : ∀ t₀ ∈ criticalValues ψ g ∩ Set.Icc a b, DiscModel ψ g t₀)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) :
    Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g s) =
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g t) :=
  eq_of_locally_constOn (f := fun u : ℝ => Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g u))
    (fun _ hx => windingSpan_locally_const_of_level_on ψ hg hcrit hreg hdisc hx) hs ht

/-- The banded form of `Work.Smooth.Morse.containsEssentialLoop_iff_of_levelSweep`. -/
theorem containsEssentialLoop_iff_of_levelSweep_on (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hg : Continuous g) (hcrit : LocallyFiniteCriticalValues ψ g) (hreg : RegularEquivalent ψ g)
    (hdisc : ∀ t₀ ∈ criticalValues ψ g ∩ Set.Icc a b, DiscModel ψ g t₀)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) :
    (torus ψ).ContainsEssentialLoop (region ψ g s) ↔
      (torus ψ).ContainsEssentialLoop (region ψ g t) := by
  rw [← Work.SurgeryInvariance.windingSpan_ne_bot_iff (torus ψ) (region ψ g s),
    ← Work.SurgeryInvariance.windingSpan_ne_bot_iff (torus ψ) (region ψ g t),
    windingSpan_eq_of_levelSweep_on ψ hg hcrit hreg hdisc hs ht]

/-! ## The banded sweep with the transport discharged -/

/-- **The banded sweep theorem, with the transport discharged.**  For `g` of class `C^∞` the
hypothesis `RegularEquivalent ψ g` of `Work.Smooth.Morse.windingSpan_eq_of_levelSweep_on` is
`Work.Smooth.Morse.regularEquivalent_of_contDiff` (item 3, proved), so the only inputs left are the
Morse/Sard hypothesis and the local model at the critical values of the band. -/
theorem windingSpan_locally_const_of_crossing_on (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hcrit : LocallyFiniteCriticalValues ψ g)
    (hcross : ∀ t₀ ∈ criticalValues ψ g ∩ Set.Icc a b, ∃ ε : ℝ, 0 < ε ∧
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ - ε)) =
        Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ + ε)))
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - x| < ε →
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g s) =
        Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g x) := by
  by_cases h : IsRegularValue ψ g x
  · exact Work.Smooth.Morse.Sweep.windingSpan_locally_const_of_regularValue ψ hcrit
      (regularEquivalent_of_contDiff ψ hg) h
  · exact Work.Smooth.Morse.MorseModel.windingSpan_locally_const_of_span_eq ψ
      (hcross x ⟨not_not.mp h, hx⟩)

/-- **Item 5 on a band, with the local model in the satisfiable "crossing" form.**

The hypothesis `hcross` asks, at every critical value `t₀` of the band, only for the equality of
the winding spans of the two regions just below and just above `t₀`.  This is the weakest local
model that still gives the persistence, and — unlike `DiscModel` — it is not restricted to the
bottom of the range of `g|_F`: it is exactly what a family of spheres put in general position
supplies, and it is vacuous on a band without critical values. -/
theorem windingSpan_eq_of_levelSweep_of_crossing_on (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hcrit : LocallyFiniteCriticalValues ψ g)
    (hcross : ∀ t₀ ∈ criticalValues ψ g ∩ Set.Icc a b, ∃ ε : ℝ, 0 < ε ∧
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ - ε)) =
        Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ + ε)))
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) :
    Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g s) =
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g t) :=
  eq_of_locally_constOn (f := fun u : ℝ => Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g u))
    (fun _ hx => windingSpan_locally_const_of_crossing_on ψ hg hcrit hcross hx) hs ht

/-- **Pardon's persistence on a band, in the satisfiable form.**  For `s, t` in the band the
property "the region contains an essential loop of the torus" takes the same value. -/
theorem containsEssentialLoop_iff_of_levelSweep_of_crossing_on (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hcrit : LocallyFiniteCriticalValues ψ g)
    (hcross : ∀ t₀ ∈ criticalValues ψ g ∩ Set.Icc a b, ∃ ε : ℝ, 0 < ε ∧
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ - ε)) =
        Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ + ε)))
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) :
    (torus ψ).ContainsEssentialLoop (region ψ g s) ↔
      (torus ψ).ContainsEssentialLoop (region ψ g t) := by
  rw [← Work.SurgeryInvariance.windingSpan_ne_bot_iff (torus ψ) (region ψ g s),
    ← Work.SurgeryInvariance.windingSpan_ne_bot_iff (torus ψ) (region ψ g t),
    windingSpan_eq_of_levelSweep_of_crossing_on ψ hg hcrit hcross hs ht]

/-- The one-directional form: a loop of the region at the *upper* end of the band is transported
down to a loop at the *lower* end (`s ≤ t`). -/
theorem containsEssentialLoop_of_levelSweep_of_crossing_on (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hcrit : LocallyFiniteCriticalValues ψ g)
    (hcross : ∀ t₀ ∈ criticalValues ψ g ∩ Set.Icc a b, ∃ ε : ℝ, 0 < ε ∧
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ - ε)) =
        Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ + ε)))
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (_hst : s ≤ t)
    (h : (torus ψ).ContainsEssentialLoop (region ψ g t)) :
    (torus ψ).ContainsEssentialLoop (region ψ g s) :=
  (containsEssentialLoop_iff_of_levelSweep_of_crossing_on ψ hg hcrit hcross hs ht).mpr h

end

end Work.Smooth.Morse
