import Submission.Work.CoreTopology.Disk

/-!
# Pardon's lemma `mustbeinessential`

Let `F = P.carrier` be a parametrised torus, `β` a simple closed curve on `F`, and
`S ⊆ ℝ³` a sphere transverse to `F` and `β`.  Pardon's "mustbeinessential" lemma says that
if `S` meets `β` in fewer than `I(F, β)` points, then every component of `S ∩ F` is
*inessential* in `F` (bounds a disc in `F`, equivalently is null-homotopic in `F`).

The proof is a two-stage innermost argument:

* if some essential component existed, take one innermost in the sphere `S`: it bounds a
  disc `D ⊆ S` whose interior meets `F` only in inessential curves of `F`;
* the innermost argument *on `F`* then removes those curves, so `α` bounds an embedded
  disc in `ℝ³` whose interior is disjoint from `F`;
* by definition of `I(F, β)`, such an `α` meets `β` at least `I(F, β)` times — but
  `α ⊆ S`, so it meets `β` at most `#(S ∩ β) < I(F, β)` times.  Contradiction.

The two bullet points are exactly the geometric input, isolated below as the hypothesis
`hclean`: *any* essential closed curve of `F` lying in `S` can be replaced by an essential
closed curve bounding a disc in the complement of `F` and meeting `β` no more often.  The
content of the present file is the reduction, which is what the definition of `I` supplies.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreTopology

noncomputable section

variable {P : ParamTorus}

/-- **Pardon's Lemma 2, "mustbeinessential".**

If `S` is a sphere which is transverse to `F` and `β` and meets `β` in strictly fewer than
`I(F, β)` points, then every closed curve of `F` whose image lies in `S` is inessential in
`F`.

The hypothesis `hclean` is the geometric content of Pardon's innermost argument: an
essential curve of `F` contained in `S` (which, in the application, is a component of
`S ∩ F` that is innermost in `S`) can be replaced by an essential curve that bounds an
embedded disc whose interior is disjoint from `F`, without increasing the number of its
intersections with `β`.  The hypothesis `hSβ` is `#(S ∩ β) < I(F, β)`. -/
theorem mustbeinessential (P : ParamTorus) (β : ClosedCurve P) (S : Set R3)
    (hclean : ∀ α : ClosedCurve P, IsEssential P α → (∀ t : ℝ, α.γ t ∈ S) →
      ∃ α' : ClosedCurve P, IsSimple P α' ∧ IsEssential P α' ∧
        BoundsDiskInComplement P α' ∧
        Set.encard (Set.range α'.γ ∩ Set.range β.γ) ≤
          Set.encard (Set.range α.γ ∩ Set.range β.γ))
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α := by
  intro α hαS hess
  obtain ⟨α', hsimple', hess', hb', hle⟩ := hclean α hess hαS
  -- `α'` is a simple compressing essential loop, so it meets `β` at least `I(F,β)` times
  have h1 : pardonsI P β ≤ Set.encard (Set.range α'.γ ∩ Set.range β.γ) :=
    pardonsI_le hsimple' hess' hb'
  -- `α` lies in `S`, so it meets `β` no more often than `S` does
  have h2 : Set.encard (Set.range α.γ ∩ Set.range β.γ) ≤ Set.encard (Set.range β.γ ∩ S) := by
    apply Set.encard_mono
    rintro x ⟨⟨t, rfl⟩, hxb⟩
    exact ⟨hxb, hαS t⟩
  exact absurd (lt_of_le_of_lt (le_trans h1 (le_trans hle h2)) hSβ) (lt_irrefl _)

/-- **Pardon's Lemma 2, with the invariant `I(F, β)` kept abstract.**

This is the form to use when `I` is Pardon's invariant rather than the `ℕ∞`-valued version
`pardonsI` defined in this directory (which is an upper bound for Pardon's `I` in general: it
counts the intersections of the *given* representative instead of minimising over its isotopy
class).  The only property of `I` which is used is that it is a lower bound for the number of
intersections of every simple compressing essential loop with `β`. -/
theorem mustbeinessential_core (P : ParamTorus) (β : ClosedCurve P) (S : Set R3) (I : ℕ∞)
    (hI : ∀ α : ClosedCurve P, IsSimple P α → IsEssential P α → BoundsDiskInComplement P α →
      I ≤ Set.encard (Set.range α.γ ∩ Set.range β.γ))
    (hclean : ∀ α : ClosedCurve P, IsEssential P α → (∀ t : ℝ, α.γ t ∈ S) →
      ∃ α' : ClosedCurve P, IsSimple P α' ∧ IsEssential P α' ∧
        BoundsDiskInComplement P α' ∧
        Set.encard (Set.range α'.γ ∩ Set.range β.γ) ≤
          Set.encard (Set.range α.γ ∩ Set.range β.γ))
    (hSβ : Set.encard (Set.range β.γ ∩ S) < I) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α := by
  intro α hαS hess
  obtain ⟨α', hsimple', hess', hb', hle⟩ := hclean α hess hαS
  have h1 : I ≤ Set.encard (Set.range α'.γ ∩ Set.range β.γ) := hI α' hsimple' hess' hb'
  have h2 : Set.encard (Set.range α.γ ∩ Set.range β.γ) ≤ Set.encard (Set.range β.γ ∩ S) := by
    apply Set.encard_mono
    rintro x ⟨⟨t, rfl⟩, hxb⟩
    exact ⟨hxb, hαS t⟩
  exact absurd (lt_of_le_of_lt (le_trans h1 (le_trans hle h2)) hSβ) (lt_irrefl _)

/-- `mustbeinessential` is the special case of `mustbeinessential_core` with `I = pardonsI P β`. -/
theorem mustbeinessential_of_core (P : ParamTorus) (β : ClosedCurve P) (S : Set R3)
    (hclean : ∀ α : ClosedCurve P, IsEssential P α → (∀ t : ℝ, α.γ t ∈ S) →
      ∃ α' : ClosedCurve P, IsSimple P α' ∧ IsEssential P α' ∧
        BoundsDiskInComplement P α' ∧
        Set.encard (Set.range α'.γ ∩ Set.range β.γ) ≤
          Set.encard (Set.range α.γ ∩ Set.range β.γ))
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α :=
  mustbeinessential_core P β S (pardonsI P β)
    (fun _ hsimple hess hb => pardonsI_le hsimple hess hb) hclean hSβ

/-- Contrapositive form of `mustbeinessential`: if there *is* an essential closed curve of
`F` contained in the sphere `S`, then `S` meets `β` in at least `I(F, β)` points. -/
theorem le_pardonsI_of_essential_in_sphere (P : ParamTorus) (β : ClosedCurve P) (S : Set R3)
    (hclean : ∀ α : ClosedCurve P, IsEssential P α → (∀ t : ℝ, α.γ t ∈ S) →
      ∃ α' : ClosedCurve P, IsSimple P α' ∧ IsEssential P α' ∧
        BoundsDiskInComplement P α' ∧
        Set.encard (Set.range α'.γ ∩ Set.range β.γ) ≤
          Set.encard (Set.range α.γ ∩ Set.range β.γ))
    (α : ClosedCurve P) (hαS : ∀ t : ℝ, α.γ t ∈ S) (hess : IsEssential P α) :
    pardonsI P β ≤ Set.encard (Set.range β.γ ∩ S) :=
  le_of_not_gt fun h => (mustbeinessential P β S hclean h) α hαS hess

end

end Work.CoreTopology
