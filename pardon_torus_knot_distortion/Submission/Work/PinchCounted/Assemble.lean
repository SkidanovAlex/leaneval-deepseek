import Submission.Work.PinchCounted.Counting

/-!
# Pardon's Step 2 as data: the pinching family with its intermediate spheres

`Counting.lean` proves the engine which turns Pardon's counting into span-preserving local models:
*every loop of `F` contained in a low-count intermediate sphere is inessential*.  This module names
the exact geometric datum that engine consumes, so that a construction of Pardon's pinching family
has a single interface to hit.

`CountedSweep P β` records, for the pinching family of Pardon's Lemma 3:

* the regions `region t = F ∩ int(S_t)`, open in the surface, and the finite set of exceptional
  parameters;
* the intermediate spheres `sphere t`, each carrying Pardon's two inputs: the cleaning of its trace
  (`CleansInSphere`, Pardon's innermost-disc step) and the count `#(S_t ∩ β) < I(F,β)`;
* the local moves: away from `exc` the loop content is transported (`RegionEquivalent`, Pardon's
  "no surgery, no change"), and at `t ∈ exc` the region changes by an *open* piece `Z` of `F` whose
  **loops are matched by loops of the intermediate sphere** (same winding vector) — this is the
  geometric heart of Pardon's Step 2: the changed piece is a collar of the trace `F ∩ S_t` of the
  pinching sphere, so its loops are homotopic in `F` to loops of that trace, which meet `β` fewer
  than `I(F,β)` times and are therefore inessential.

The conversion to the library's sweep is `sweepLoops_of_countedSweep` (below), and with it the whole
chapter: a `CountedSweep` with the two endpoint conditions is a
`Work.PinchCounted.PinchSweep`, hence gives Pardon's Lemma 3 conclusion.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PinchCounted

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **Pardon's pinching family with the counting of his proof**, as data: the regions, the
intermediate spheres with their two counting inputs, and the local moves whose changed pieces have
their loops on the intermediate spheres. -/
structure CountedSweep (P : Work.CoreTopology.ParamTorus) (β : Work.CoreTopology.ClosedCurve P) where
  /-- the region `F ∩ int(S_t)` of the family -/
  region : ℝ → Set R3
  /-- it is open in the surface (automatic for `F ∩ int(S_t)`) -/
  region_open : ∀ t : ℝ, Work.SurgeryInvariance.IsOpenInCarrier P (region t)
  /-- the exceptional (surgery) parameters -/
  exc : Finset ℝ
  /-- the intermediate sphere `S_t` -/
  sphere : ℝ → Set R3
  /-- Pardon's innermost-disc input at `S_t` -/
  sphere_clean : ∀ t : ℝ, Work.InnermostDisk.CleansInSphere P (sphere t)
  /-- Pardon's count at `S_t`: `#(S_t ∩ β) < I(F,β)` -/
  sphere_count : ∀ t : ℝ,
    Set.encard (Set.range β.γ ∩ sphere t) < Work.CoreTopology.pardonsI P β
  /-- away from the exceptional parameters the loop content is transported -/
  regular : ∀ t : ℝ, t ∉ exc → ∃ ε : ℝ, 0 < ε ∧ (∀ s : ℝ, |s - t| < ε → s ∉ exc) ∧
    ∀ s : ℝ, |s - t| < ε → Work.SurgeryInvariance.RegionEquivalent P (region t) (region s)
  /-- at an exceptional parameter the region changes by an open piece of `F` whose loops are
  *matched* (with their winding vectors) by loops of the intermediate sphere, or is transported.

  This is Pardon's description of the pinched neck: the changed piece is a collar of the trace
  `F ∩ S_t` of the intermediate sphere, so every loop in it is freely homotopic in `F` to a loop of
  that trace, hence has the same winding vector.  (Asking the loops of the changed piece to *lie on*
  `S_t` would be too strong: the core of a collar is not on the sphere.) -/
  surgery : ∀ t : ℝ, t ∈ exc → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε →
    (∃ Z : Set R3, Work.SurgeryInvariance.IsOpenInCarrier P Z ∧
      (∀ γ : Work.CoreTopology.ClosedCurve P, (∀ u : ℝ, γ u ∈ Z) →
        ∃ γ' : Work.CoreTopology.ClosedCurve P, (∀ u : ℝ, γ' u ∈ sphere t) ∧
          Work.SurgeryInvariance.windingOf P γ' = Work.SurgeryInvariance.windingOf P γ) ∧
      ((region t = region s ∪ Z ∧ Disjoint (region s) Z) ∨
        (region s = region t ∪ Z ∧ Disjoint (region t) Z)))
    ∨ Work.SurgeryInvariance.RegionEquivalent P (region t) (region s)

namespace CountedSweep

variable {β : Work.CoreTopology.ClosedCurve P}

/-- **Any piece of the surface whose loops are matched by loops of a low-count sphere has vanishing
winding span.**  This is the engine of Pardon's Step 2 in the shape the local moves consume: `Z` is
the changed piece, `S` the intermediate sphere; every loop of `Z` has a partner in `S` with the same
winding vector, and Pardon's Lemma 2 makes every loop of `S` inessential, so no loop of `Z` is
essential. -/
theorem windingSpan_eq_bot_of_loops_match {Z S : Set R3}
    (hclean : Work.InnermostDisk.CleansInSphere P S)
    (hcount : Set.encard (Set.range β.γ ∩ S) < Work.CoreTopology.pardonsI P β)
    (hmatch : ∀ γ : Work.CoreTopology.ClosedCurve P, (∀ u : ℝ, γ u ∈ Z) →
      ∃ γ' : Work.CoreTopology.ClosedCurve P, (∀ u : ℝ, γ' u ∈ S) ∧
        Work.SurgeryInvariance.windingOf P γ' = Work.SurgeryInvariance.windingOf P γ) :
    Work.SurgeryInvariance.WindingSpan P Z = ⊥ := by
  refine (Work.SurgeryInvariance.WindingSpan_eq_bot_iff P Z).mpr ?_
  rintro ⟨γ, hγ, hmemZ⟩
  obtain ⟨γ', hγ', hw⟩ := hmatch γ hmemZ
  have hine : ¬ Work.CoreTopology.IsEssential P γ' :=
    Work.InnermostDisk.mustbeinessential_of_cleansInSphere P β S hclean hcount γ' hγ'
  rw [Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero] at hine
  exact hine (hw ▸ ((Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P γ).mp hγ))

/-- **The special case in which the loops of `Z` lie on `S`**: then they are matched by themselves,
so the previous engine applies. -/
theorem windingSpan_eq_bot_of_loops_mem {Z S : Set R3}
    (hclean : Work.InnermostDisk.CleansInSphere P S)
    (hcount : Set.encard (Set.range β.γ ∩ S) < Work.CoreTopology.pardonsI P β)
    (hZ : ∀ γ : Work.CoreTopology.ClosedCurve P, (∀ u : ℝ, γ u ∈ Z) → ∀ u : ℝ, γ u ∈ S) :
    Work.SurgeryInvariance.WindingSpan P Z = ⊥ :=
  windingSpan_eq_bot_of_loops_match hclean hcount fun γ hγ => ⟨γ, hZ γ hγ, rfl⟩

end CountedSweep

/-! ## The residual: Pardon's Step 2 exists at every counted configuration -/

open scoped ENNReal

/-- **Pardon's Step 2, as the residual of the counted form.**  At every configuration carrying the
counting data of the crux there is a `CountedSweep P β` (the pinching family together with its
intermediate spheres, their cleanings and their counts) whose region at time `0` is the region inside
the box and whose region at time `1` is the two half-regions together with an open piece of
vanishing span disjoint from them.

This is strictly weaker than `Work.PinchCounted.CountedPinchSweep` — the datum asks for the
*geometric* content of Pardon's proof (the changed pieces are collars of the traces of the
intermediate spheres, which meet `β` fewer than `I(F,β)` times), not for the zero-span local models,
which then follow from the counting (`CountedSweep.windingSpan_eq_bot_of_loops_match`). -/
def CountedStep2 : Prop :=
  ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.InnermostDisk.CleansDiscs (Work.Smooth.Morse.torus ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (Work.Smooth.Morse.torus ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (Work.Smooth.Morse.torus ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          ∃ D : CountedSweep (Work.Smooth.Morse.torus ψ)
              (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
                (Work.CoreTopology.standardCurve p q)),
            D.region 0 = Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ ∧
            (∃ Z : Set R3, Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ) Z ∧
              Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ) Z = ⊥ ∧
              Disjoint (PinchSweep.halves (Work.Smooth.Morse.torus ψ) s c σ u) Z ∧
              D.region 1 = PinchSweep.halves (Work.Smooth.Morse.torus ψ) s c σ u ∪ Z)

/-! ## Non-vacuity: the datum with constant regions and empty spheres -/

/-- The empty set is cleaned. -/
theorem cleansInSphere_empty (P : Work.CoreTopology.ParamTorus) :
    Work.InnermostDisk.CleansInSphere P (∅ : Set R3) := by
  intro α _ h
  exact absurd (h 0) (Set.notMem_empty _)

/-- **A `CountedSweep` from constant regions and empty intermediate spheres**: the non-vacuity
witness for the datum.  The regular moves are trivial (the region never changes) and there are no
exceptional parameters, so only the two counting inputs are used — and for the empty sphere they are
immediate (`0 < I(F,β)`, the empty set carries no loop). -/
def countedSweepOfConst (P : Work.CoreTopology.ParamTorus) (β : Work.CoreTopology.ClosedCurve P)
    {X : Set R3} (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hβ : 0 < Work.CoreTopology.pardonsI P β) : CountedSweep P β where
  region := fun _ => X
  region_open := fun _ => hX
  exc := ∅
  sphere := fun _ => ∅
  sphere_clean := fun _ => cleansInSphere_empty P
  sphere_count := fun _ => by
    rw [Set.inter_empty, Set.encard_empty]
    exact hβ
  regular := by
    intro t _
    exact ⟨1, one_pos, by simp, fun s _ =>
      ⟨fun γ hγ => ⟨γ, hγ, rfl⟩, fun γ hγ => ⟨γ, hγ, rfl⟩⟩⟩
  surgery := by intro t ht; simp at ht

end

end Work.PinchCounted
