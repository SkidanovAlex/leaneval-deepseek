import Submission.Work.InnermostDisk.Defs
import Submission.Work.CoreTopology.EssentialLoop

/-!
# Pardon's `mustbeinessential` from the two innermost-disc inputs

This file contains the *reduction*: the purely formal part of Pardon's Lemma 4.2, i.e. his
third step.  The two geometric steps are the hypotheses `InnermostDiscInput` and
`CleansDiscs` of `Work.InnermostDisk.Defs`; given them, the lemma is unconditional.

The proof of the lemma is a contradiction argument.  Suppose an essential loop `α` of `F`
lies in the sphere `S`, and let `S` meet `β` in fewer than `I(F, β)` points.

* `InnermostDiscInput` produces an essential simple loop `α' ⊆ S` which is innermost, i.e.
  bounds a disc `D ⊆ S` whose interior meets `F` only in inessential curves of `F`
  (`InnermostDisc`);
* `CleansDiscs` cleans `D` up, so that `α'` bounds an embedded disc whose interior is
  disjoint from `F`: `α'` is a *compressing* loop, i.e. an element of Pardon's `U`;
* `pardonsI_le` therefore gives `I(F, β) ≤ #(α' ∩ β)`, while `α' ⊆ S` gives
  `#(α' ∩ β) ≤ #(S ∩ β) < I(F, β)`: a contradiction.

Note that the replacement loop `α'` is found *inside the sphere* `S`; this is why the
conclusion is the whole statement "no essential loop of `F` is contained in `S`", and not the
form `hclean` of `Work.CoreTopology.mustbeinessential` (which additionally asks that `α'` meet
`β` no more often than the original `α` does — something Pardon's argument does not provide).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology

namespace Work.InnermostDisk

noncomputable section

/-! ## The two inputs give `CleansInSphere` -/

/-- The local form of Pardon's second step, for a single sphere `S`: every innermost disc
inside `S` can be cleaned.  (`CleansDiscs` is the global form, quantified over all `S`.) -/
def CleansDiscsOn (P : ParamTorus) (S : Set R3) : Prop :=
  ∀ D : InnermostDisc P S, BoundsDiskInComplement P D.α

/-- The global second step gives the local one. -/
theorem CleansDiscsOn.of_cleansDiscs {P : ParamTorus} {S : Set R3} (h : CleansDiscs P) :
    CleansDiscsOn P S :=
  fun D => h S D

/-- **Steps 1 and 2 of Pardon's proof combine.**  If `S` admits innermost discs and innermost
discs inside `S` can be cleaned, then every essential loop of `F` inside `S` can be replaced by a
simple essential compressing loop inside `S`. -/
theorem cleansInSphere_of_inputs' {P : ParamTorus} {S : Set R3}
    (hIn : InnermostDiscInput P S) (hCl : CleansDiscsOn P S) : CleansInSphere P S := by
  intro α hα hαS
  obtain ⟨D⟩ := hIn ⟨α, hα, hαS⟩
  exact ⟨D.α, D.simple, D.essential, hCl D, D.mem⟩

/-- **Steps 1 and 2 of Pardon's proof combine** (global form of the second step). -/
theorem cleansInSphere_of_inputs {P : ParamTorus} {S : Set R3}
    (hIn : InnermostDiscInput P S) (hCl : CleansDiscs P) : CleansInSphere P S :=
  cleansInSphere_of_inputs' hIn (CleansDiscsOn.of_cleansDiscs hCl)

/-- A single compressing loop inside `S` already forces `S` to meet `β` at least `I(F, β)`
times.  This is the elementary counting step at the end of Pardon's proof, isolated for
reuse. -/
theorem le_pardonsI_of_compressing_loop_mem {P : ParamTorus} {β α : ClosedCurve P} {S : Set R3}
    (hsimple : IsSimple P α) (hess : IsEssential P α) (hb : BoundsDiskInComplement P α)
    (hαS : ∀ t : ℝ, α.γ t ∈ S) :
    pardonsI P β ≤ Set.encard (Set.range β.γ ∩ S) := by
  refine le_trans (pardonsI_le hsimple hess hb) ?_
  apply Set.encard_mono
  rintro x ⟨⟨t, rfl⟩, hxb⟩
  exact ⟨hxb, hαS t⟩

theorem cleansInSphere_of_sphereInput {P : ParamTorus} {S : Set R3}
    (hIn : SphereInnermostInput P) (hS : IsEmbeddedSphere S) (hCl : CleansDiscs P) :
    CleansInSphere P S :=
  cleansInSphere_of_inputs (InnermostDiscInput.of_sphere hIn hS) hCl

/-! ## Pardon's Lemma from `CleansInSphere` -/

/-- **Pardon's Lemma ("mustbeinessential"), third step.**  If `S` meets `β` in fewer than
`I(F, β)` points then every closed curve of `F` contained in `S` is inessential, assuming the
geometric content `CleansInSphere P S` of the two innermost arguments. -/
theorem mustbeinessential_of_cleansInSphere (P : ParamTorus) (β : ClosedCurve P) (S : Set R3)
    (hclean : CleansInSphere P S)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α := by
  intro α hαS hα
  obtain ⟨α', hsimple', hess', hb', hα'S⟩ := hclean α hα hαS
  -- `α'` is a simple compressing essential loop, hence meets `β` at least `I(F, β)` times
  have h1 : pardonsI P β ≤ Set.encard (Set.range α'.γ ∩ Set.range β.γ) :=
    pardonsI_le hsimple' hess' hb'
  -- and since `α' ⊆ S`, it meets `β` at most as often as `S` does
  have h2 : Set.encard (Set.range α'.γ ∩ Set.range β.γ) ≤ Set.encard (Set.range β.γ ∩ S) := by
    apply Set.encard_mono
    rintro x ⟨⟨t, rfl⟩, hxb⟩
    exact ⟨hxb, hα'S t⟩
  exact absurd (lt_of_le_of_lt (le_trans h1 h2) hSβ) (lt_irrefl _)

/-- **Pardon's Lemma, with the invariant `I` kept abstract.**  This is the form to use when
`I` is Pardon's invariant rather than the `ℕ∞`-valued version `pardonsI`. -/
theorem mustbeinessential_core_of_cleansInSphere (P : ParamTorus) (β : ClosedCurve P)
    (S : Set R3) (I : ℕ∞)
    (hI : ∀ α : ClosedCurve P, IsSimple P α → IsEssential P α → BoundsDiskInComplement P α →
      I ≤ Set.encard (Set.range α.γ ∩ Set.range β.γ))
    (hclean : CleansInSphere P S) (hSβ : Set.encard (Set.range β.γ ∩ S) < I) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α := by
  intro α hαS hα
  obtain ⟨α', hsimple', hess', hb', hα'S⟩ := hclean α hα hαS
  have h1 : I ≤ Set.encard (Set.range α'.γ ∩ Set.range β.γ) := hI α' hsimple' hess' hb'
  have h2 : Set.encard (Set.range α'.γ ∩ Set.range β.γ) ≤ Set.encard (Set.range β.γ ∩ S) := by
    apply Set.encard_mono
    rintro x ⟨⟨t, rfl⟩, hxb⟩
    exact ⟨hxb, hα'S t⟩
  exact absurd (lt_of_le_of_lt (le_trans h1 h2) hSβ) (lt_irrefl _)

/-! ## Pardon's Lemma from the two geometric inputs -/

/-- **Pardon's Lemma 4.2 ("mustbeinessential") from the two innermost-disc inputs.** -/
theorem mustbeinessential_of_inputs (P : ParamTorus) (β : ClosedCurve P) (S : Set R3)
    (hIn : InnermostDiscInput P S) (hCl : CleansDiscs P)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α :=
  mustbeinessential_of_cleansInSphere P β S (cleansInSphere_of_inputs hIn hCl) hSβ

/-- **Pardon's Lemma 4.2, sphere-conditioned form of the inputs.** -/
theorem mustbeinessential_of_embeddedSphere (P : ParamTorus) (β : ClosedCurve P)
    (S : Set R3) (hS : IsEmbeddedSphere S) (hIn : SphereInnermostInput P)
    (hCl : CleansDiscs P) (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α :=
  mustbeinessential_of_inputs P β S (InnermostDiscInput.of_sphere hIn hS) hCl hSβ

/-- **Pardon's Lemma 4.2 with abstract `I`, from the two geometric inputs.** -/
theorem mustbeinessential_core_of_inputs (P : ParamTorus) (β : ClosedCurve P) (S : Set R3)
    (I : ℕ∞)
    (hI : ∀ α : ClosedCurve P, IsSimple P α → IsEssential P α → BoundsDiskInComplement P α →
      I ≤ Set.encard (Set.range α.γ ∩ Set.range β.γ))
    (hIn : InnermostDiscInput P S) (hCl : CleansDiscs P)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < I) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α :=
  mustbeinessential_core_of_cleansInSphere P β S I hI (cleansInSphere_of_inputs hIn hCl) hSβ

/-! ## The counting step, contrapositive form -/

/-- **No compressing loop is contained in a sphere meeting `β` too rarely.**  If `S` meets `β` in
fewer than `I(F, β)` points, then no simple essential loop of `F` inside `S` bounds a disc whose
interior avoids `F`.  This is unconditional — it is Pardon's counting argument on its own, and it
is the reason why the whole of Pardon's Lemma reduces to exhibiting *one* compressing loop inside
`S`. -/
theorem not_boundsDiskInComplement_of_mem_sphere {P : ParamTorus} {β α : ClosedCurve P}
    {S : Set R3} (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β)
    (hsimple : IsSimple P α) (hess : IsEssential P α) (hαS : ∀ t : ℝ, α.γ t ∈ S) :
    ¬ BoundsDiskInComplement P α :=
  fun hb => absurd (lt_of_le_of_lt (le_pardonsI_of_compressing_loop_mem hsimple hess hb hαS) hSβ)
    (lt_irrefl _)


/-! ## Contrapositive forms -/

/-- **Contrapositive of Pardon's Lemma.**  If an essential closed curve of `F` is contained in
`S`, then `S` meets `β` in at least `I(F, β)` points. -/
theorem le_pardonsI_of_cleansInSphere (P : ParamTorus) (β : ClosedCurve P) (S : Set R3)
    (hclean : CleansInSphere P S) (α : ClosedCurve P) (hαS : ∀ t : ℝ, α.γ t ∈ S)
    (hα : IsEssential P α) :
    pardonsI P β ≤ Set.encard (Set.range β.γ ∩ S) :=
  le_of_not_gt fun h => (mustbeinessential_of_cleansInSphere P β S hclean h) α hαS hα

/-- **Contrapositive of Pardon's Lemma, from the two geometric inputs.** -/
theorem le_pardonsI_of_inputs (P : ParamTorus) (β : ClosedCurve P) (S : Set R3)
    (hIn : InnermostDiscInput P S) (hCl : CleansDiscs P)
    (α : ClosedCurve P) (hαS : ∀ t : ℝ, α.γ t ∈ S) (hα : IsEssential P α) :
    pardonsI P β ≤ Set.encard (Set.range β.γ ∩ S) :=
  le_pardonsI_of_cleansInSphere P β S (cleansInSphere_of_inputs hIn hCl) α hαS hα

/-! ## The geometric form for the standard torus -/

/-- **Pardon's Lemma 4.2 in the geometric vocabulary of the standard torus.**  If the region
`S ⊆ ℝ³` meets the `(p,q)`-curve in fewer than `I(F, β)` points, then it contains no essential
loop of the torus — assuming the two innermost-disc inputs. -/
theorem not_containsEssentialLoop_of_cleansInSphere (β : ClosedCurve standard) (S : Set R3)
    (hclean : CleansInSphere standard S)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI standard β) :
    ¬ ContainsEssentialLoop S := by
  rintro ⟨γ, hγ, hγS⟩
  exact (mustbeinessential_of_cleansInSphere standard β S hclean hSβ γ hγS) hγ

/-- **Geometric form from the two geometric inputs.** -/
theorem not_containsEssentialLoop_of_inputs (β : ClosedCurve standard) (S : Set R3)
    (hIn : InnermostDiscInput standard S) (hCl : CleansDiscs standard)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI standard β) :
    ¬ ContainsEssentialLoop S :=
  not_containsEssentialLoop_of_cleansInSphere β S (cleansInSphere_of_inputs hIn hCl) hSβ

end

end Work.InnermostDisk
