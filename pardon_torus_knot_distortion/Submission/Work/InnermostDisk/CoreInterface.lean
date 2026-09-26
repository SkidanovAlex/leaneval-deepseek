import Submission.Work.InnermostDisk.Reduction
import Submission.Work.CoreTopology.EssentialLoop

/-!
# The interface with `Work.CoreTopology.mustbeinessential`

`Work.CoreTopology.mustbeinessential` proves Pardon's lemma from the hypothesis `hclean`: an
essential loop `α` of `F` contained in the sphere `S` can be replaced by a simple essential
compressing loop `α'` meeting `β` *no more often than `α` does*.

Pardon's own innermost argument does **not** produce that comparison: the replacement loop is an
innermost component of `S ∩ F`, and all one knows is that it lies in `S`, whence
`#(α' ∩ β) ≤ #(S ∩ β)` (this is the form `CleansInSphere` used by
`Work.InnermostDisk.Reduction.mustbeinessential_of_inputs`, which reproves the lemma with exactly
that weaker hypothesis).

Since the comparison is nevertheless harmless to ask for, this file records it as the predicate
`CleansInSphereMeetingAtMost`, proves that it really is the `hclean` of
`Work.CoreTopology.mustbeinessential`, and re-derives Pardon's lemma through that theorem — so
that a formalizer who establishes the stronger form can keep using the existing results
verbatim.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology

namespace Work.InnermostDisk

noncomputable section

/-- `CleansInSphere P S` together with the comparison of intersection counts with `β` which is
the hypothesis `hclean` of `Work.CoreTopology.mustbeinessential`. -/
def CleansInSphereMeetingAtMost (P : ParamTorus) (β : ClosedCurve P) (S : Set R3) : Prop :=
  ∀ α : ClosedCurve P, IsEssential P α → (∀ t : ℝ, α.γ t ∈ S) →
    ∃ α' : ClosedCurve P, IsSimple P α' ∧ IsEssential P α' ∧ BoundsDiskInComplement P α' ∧
      (∀ t : ℝ, α'.γ t ∈ S) ∧
      Set.encard (Set.range α'.γ ∩ Set.range β.γ) ≤ Set.encard (Set.range α.γ ∩ Set.range β.γ)

/-- The stronger form is in particular the form `CleansInSphere` used by the reduction. -/
theorem CleansInSphere.of_meetingAtMost {P : ParamTorus} {β : ClosedCurve P} {S : Set R3}
    (h : CleansInSphereMeetingAtMost P β S) : CleansInSphere P S :=
  fun α hα hαS => by
    obtain ⟨α', h1, h2, h3, h4, -⟩ := h α hα hαS
    exact ⟨α', h1, h2, h3, h4⟩

/-- **The stronger form is exactly the `hclean` of `Work.CoreTopology.mustbeinessential`.** -/
theorem hclean_of_cleansInSphereMeetingAtMost {P : ParamTorus} {β : ClosedCurve P} {S : Set R3}
    (h : CleansInSphereMeetingAtMost P β S) :
    ∀ α : ClosedCurve P, IsEssential P α → (∀ t : ℝ, α.γ t ∈ S) →
      ∃ α' : ClosedCurve P, IsSimple P α' ∧ IsEssential P α' ∧
        BoundsDiskInComplement P α' ∧
        Set.encard (Set.range α'.γ ∩ Set.range β.γ) ≤
          Set.encard (Set.range α.γ ∩ Set.range β.γ) :=
  fun α hα hαS => by
    obtain ⟨α', h1, h2, h3, -, h5⟩ := h α hα hαS
    exact ⟨α', h1, h2, h3, h5⟩

/-- **Pardon's Lemma through `Work.CoreTopology.mustbeinessential`.**  From the strong form of
the cleaning hypothesis (which is Pardon's `hclean`), the existing theorem applies verbatim. -/
theorem mustbeinessential_via_core (P : ParamTorus) (β : ClosedCurve P) (S : Set R3)
    (h : CleansInSphereMeetingAtMost P β S)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α :=
  mustbeinessential P β S (hclean_of_cleansInSphereMeetingAtMost h) hSβ

/-- The same with the invariant `I(F, β)` kept abstract, through
`Work.CoreTopology.mustbeinessential_core`. -/
theorem mustbeinessential_core_via_core (P : ParamTorus) (β : ClosedCurve P) (S : Set R3)
    (I : ℕ∞)
    (hI : ∀ α : ClosedCurve P, IsSimple P α → IsEssential P α → BoundsDiskInComplement P α →
      I ≤ Set.encard (Set.range α.γ ∩ Set.range β.γ))
    (h : CleansInSphereMeetingAtMost P β S) (hSβ : Set.encard (Set.range β.γ ∩ S) < I) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α :=
  mustbeinessential_core P β S I hI (hclean_of_cleansInSphereMeetingAtMost h) hSβ

/-- The contrapositive through `Work.CoreTopology.le_pardonsI_of_essential_in_sphere`. -/
theorem le_pardonsI_of_essential_in_sphere_via_core (P : ParamTorus) (β : ClosedCurve P)
    (S : Set R3) (h : CleansInSphereMeetingAtMost P β S) (α : ClosedCurve P)
    (hαS : ∀ t : ℝ, α.γ t ∈ S) (hα : IsEssential P α) :
    pardonsI P β ≤ Set.encard (Set.range β.γ ∩ S) :=
  le_pardonsI_of_essential_in_sphere P β S (hclean_of_cleansInSphereMeetingAtMost h)
    α hαS hα

/-! ## Pardon's Lemma, component form -/

/-- **Pardon's Lemma 4.2 in component form.**  If the finitely many curves `c i` of `F` all lie in
the sphere `S`, and `S` meets `β` in fewer than `I(F, β)` points, then every one of them is
inessential in `F` — Pardon's own formulation, "every curve in `S ∩ F` is inessential in `F`". -/
theorem not_isEssential_of_mem_sphere_of_inputs {P : ParamTorus} {β : ClosedCurve P} {S : Set R3}
    {ι : Type} [Fintype ι] (c : ι → ClosedCurve P) (hIn : InnermostDiscInput P S)
    (hCl : CleansDiscs P) (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β)
    (hcS : ∀ i : ι, ∀ t : ℝ, (c i).γ t ∈ S) : ∀ i : ι, ¬ IsEssential P (c i) :=
  fun i => mustbeinessential_of_inputs P β S hIn hCl hSβ (c i) (hcS i)

/-! ## Geometric forms in the vocabulary of `Work.CoreTopology.EssentialLoop` -/

/-- Pardon's Lemma in the `ContainsEssentialLoop` vocabulary, from the two innermost-disc
inputs. -/
theorem not_containsEssentialLoop' {β : ClosedCurve standard} {S : Set R3}
    (hIn : InnermostDiscInput standard S) (hCl : CleansDiscs standard)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI standard β) :
    ¬ ContainsEssentialLoop S :=
  not_containsEssentialLoop_of_inputs β S hIn hCl hSβ

/-- The same, for the simple essential loops of
`Work.CoreTopology.ContainsSimpleEssentialLoop`. -/
theorem not_containsSimpleEssentialLoop_of_inputs {β : ClosedCurve standard} {S : Set R3}
    (hIn : InnermostDiscInput standard S) (hCl : CleansDiscs standard)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI standard β) :
    ¬ ContainsSimpleEssentialLoop S :=
  fun h => not_containsEssentialLoop_of_inputs β S hIn hCl hSβ h.toContainsEssentialLoop

/-- `Work.CoreTopology.ContainsEssentialLoop` is the standard-torus instance of the general
`Work.CoreTopology.ParamTorus.ContainsEssentialLoop`. -/
theorem paramTorus_containsEssentialLoop_iff (U : Set R3) :
    ParamTorus.ContainsEssentialLoop standard U ↔ ContainsEssentialLoop U :=
  Iff.rfl

end

end Work.InnermostDisk
