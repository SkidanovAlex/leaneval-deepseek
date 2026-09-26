import Submission.Work.InnermostDisk.Clean
import Submission.Work.InnermostDisk.not_isEssential_of_section
import Submission.Work.CoreTopology.IntersectionNumberStandard

/-!
# Unconditional instances of Pardon's lemma, and the standard `(p,q)` curve

The reduction `Work.InnermostDisk.Reduction.mustbeinessential_of_inputs` proves Pardon's Lemma
from the two innermost-disc inputs.  This file records the cases in which the inputs are
available *unconditionally*, so that the lemma is seen to be non-vacuous:

* `mustbeinessential_of_subset_section` — if the sphere `S` is contained in a *chart* of the
  parametrisation (a set carrying a continuous section `σ` of `P.psi`), then every loop of `F`
  inside `S` is inessential, with no input at all.  This is the chart/section lemma
  `not_isEssential_of_section` in the form used by Pardon's proof.
* `mustbeinessential_of_emptySlice` — if the sphere `S` meets `F` in a single essential loop
  which bounds a disc inside `S` whose interior misses `F`, then again the lemma holds with no
  input: the innermost disc has an empty slice, so the cut-and-paste has nothing to do
  (`Work.InnermostDisk.boundsDiskInComplement_of_isEmpty`).
* `not_containsEssentialLoop_standardCurve_of_inputs` — the `(p,q)` form on the standard torus,
  using the digit computation `I(F, β) = min p q` of `Work.CoreTopology.pardonsI_standard`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology

namespace Work.InnermostDisk

noncomputable section

/-! ## Loops lying in a chart -/

/-- **Pardon's conclusion for a region lying in a chart of the parametrisation.**  If `S` is
contained in a set `s` carrying a continuous section `σ` of `P.psi`, then every loop of `F`
inside `S` is inessential — unconditionally, with no innermost-disc input. -/
theorem not_isEssential_of_subset_section {P : ParamTorus} {S s : Set R3}
    (σ : C(s, ℝ × ℝ)) (hσ : ∀ x : s, P.psi (σ x).1 (σ x).2 = (x : R3)) (hS : S ⊆ s) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α :=
  fun α hα => not_isEssential_of_section σ hσ fun t => hS (hα t)

/-- The same, in the `CleansInSphere` form consumed by the reduction: a region lying in a chart
admits no essential loop, so every essential loop inside it can be replaced by a compressing one
(vacuously). -/
theorem cleansInSphere_of_subset_section {P : ParamTorus} {S s : Set R3}
    (σ : C(s, ℝ × ℝ)) (hσ : ∀ x : s, P.psi (σ x).1 (σ x).2 = (x : R3)) (hS : S ⊆ s) :
    CleansInSphere P S :=
  fun α hα hαS => absurd hα (not_isEssential_of_subset_section σ hσ hS α hαS)

/-- A region lying in a chart of the parametrisation contains no essential loop at all, so it
satisfies Pardon's first innermost input vacuously. -/
theorem innermostDiscInput_of_subset_section {P : ParamTorus} {S s : Set R3}
    (σ : C(s, ℝ × ℝ)) (hσ : ∀ x : s, P.psi (σ x).1 (σ x).2 = (x : R3)) (hS : S ⊆ s) :
    InnermostDiscInput P S := by
  rintro ⟨α, hα, hαS⟩
  exact absurd hα (not_isEssential_of_subset_section σ hσ hS α hαS)

/-! ## Innermost discs with an empty slice -/

/-- An innermost disc in `S` whose section is empty, built from the pair (essential loop,
spanning disc inside `S` with interior disjoint from `F`). -/
def innermostDiscOfEmptySlice {P : ParamTorus} {S : Set R3} {α : ClosedCurve P}
    (hsimple : IsSimple P α) (hess : IsEssential P α) (hmem : ∀ t : ℝ, α.γ t ∈ S)
    {e : C(Disc, R3)} (hinj : Function.Injective e)
    (hboundary : ∀ θ : ℝ, e (circlePoint θ) = α.γ θ) (he : ∀ z : Disc, e z ∈ S)
    (hno : ∀ z : Disc, ‖(z : ℂ)‖ < 1 → e z ∈ P.carrier → False) :
    InnermostDisc P S where
  α := α
  simple := hsimple
  essential := hess
  mem := hmem
  e := e
  inj := hinj
  boundary := hboundary
  e_mem := he
  ι := Empty
  fintype := inferInstance
  curves := fun i => isEmptyElim i
  curves_simple := fun i => isEmptyElim i
  curves_inessential := fun i => isEmptyElim i
  curves_disjoint := fun i => isEmptyElim i
  curves_subset := fun i => isEmptyElim i
  covers := fun z hz hc => (hno z hz hc).elim

/-- The boundary of such a disc is already a compressing loop. -/
theorem boundsDiskInComplement_of_emptySlice {P : ParamTorus} {α : ClosedCurve P}
    {e : C(Disc, R3)} (hinj : Function.Injective e)
    (hboundary : ∀ θ : ℝ, e (circlePoint θ) = α.γ θ)
    (hno : ∀ z : Disc, ‖(z : ℂ)‖ < 1 → e z ∈ P.carrier → False) :
    BoundsDiskInComplement P α :=
  ⟨e, hinj, hboundary, hno⟩

/-- **The innermost-disc input when the innermost disc has an empty slice.**  If every time `S`
contains an essential loop it admits an essential loop bounding a disc inside `S` whose interior
misses `F` altogether, then `S` satisfies Pardon's first input. -/
def InnermostDiscInputEmptySlice (P : ParamTorus) (S : Set R3) : Prop :=
  (∃ α : ClosedCurve P, IsEssential P α ∧ ∀ t : ℝ, α.γ t ∈ S) →
    ∃ α : ClosedCurve P, IsSimple P α ∧ IsEssential P α ∧ (∀ t : ℝ, α.γ t ∈ S) ∧
      ∃ e : C(Disc, R3), Function.Injective e ∧ (∀ θ : ℝ, e (circlePoint θ) = α.γ θ) ∧
        (∀ z : Disc, e z ∈ S) ∧ (∀ z : Disc, ‖(z : ℂ)‖ < 1 → e z ∈ P.carrier → False)

theorem innermostDiscInput_of_emptySlice {P : ParamTorus} {S : Set R3}
    (h : InnermostDiscInputEmptySlice P S) : InnermostDiscInput P S := by
  intro hS
  obtain ⟨α, hsimple, hess, hmem, e, hinj, hboundary, he, hno⟩ := h hS
  exact ⟨innermostDiscOfEmptySlice hsimple hess hmem hinj hboundary he hno⟩

/-- An empty-slice innermost input is a cleaning step: the loop produced bounds a disc whose
interior is already disjoint from `F`. -/
theorem cleansInSphere_of_emptySlice {P : ParamTorus} {S : Set R3}
    (hIn : InnermostDiscInputEmptySlice P S) : CleansInSphere P S := by
  intro α hα hαS
  obtain ⟨α', hsimple, hess, hmem, e, hinj, hboundary, -, hno⟩ := hIn ⟨α, hα, hαS⟩
  exact ⟨α', hsimple, hess, ⟨e, hinj, hboundary, hno⟩, hmem⟩

/-- **Pardon's Lemma when the sphere meets `F` only along an essential loop that already bounds
a disc inside the sphere with interior disjoint from `F`.**  No innermost-disc input is needed:
the disc needs no cleaning. -/
theorem mustbeinessential_of_emptySlice (P : ParamTorus) (β : ClosedCurve P) (S : Set R3)
    (hIn : InnermostDiscInputEmptySlice P S)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α :=
  mustbeinessential_of_cleansInSphere P β S (cleansInSphere_of_emptySlice hIn) hSβ

/-! ## The standard torus and the standard `(p,q)`-curve -/

/-- **Pardon's Lemma for the standard torus and the standard `(p,q)`-curve**, in the form in
which it is used: a region meeting the curve in fewer than `min p q` points contains no essential
loop of the torus. -/
theorem not_containsEssentialLoop_standardCurve_of_inputs (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (S : Set R3) (hIn : InnermostDiscInput standard S)
    (hCl : CleansDiscs standard)
    (hSβ : Set.encard (Set.range (standardCurve p q).γ ∩ S) < (Nat.min p q : ℕ∞)) :
    ¬ ContainsEssentialLoop S := by
  rw [← pardonsI_standard p q hp hq hc] at hSβ
  exact not_containsEssentialLoop_of_inputs (standardCurve p q) S hIn hCl hSβ

/-- The same, with the cut-and-paste step isolated. -/
theorem not_containsEssentialLoop_standardCurve_of_removesOneCurve (p q : ℕ) (hp : 0 < p)
    (hq : 0 < q) (hc : Nat.Coprime p q) (S : Set R3) (hIn : InnermostDiscInput standard S)
    (hRem : RemovesOneCurve standard)
    (hSβ : Set.encard (Set.range (standardCurve p q).γ ∩ S) < (Nat.min p q : ℕ∞)) :
    ¬ ContainsEssentialLoop S :=
  not_containsEssentialLoop_standardCurve_of_inputs p q hp hq hc S hIn
    (cleansDiscs_of_removesOneCurve hRem) hSβ

end

end Work.InnermostDisk
