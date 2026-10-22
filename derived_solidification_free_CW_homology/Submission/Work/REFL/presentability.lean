import Submission.Work.REFL.pointwise_colimit_isSheaf
import Submission.Work.REFL.sections_filtered
import Submission.Work.REFL.atoms_presentable
import Submission.Work.REFL.test_objects_presentable

/-!
# AREA REFL — the presentability facts, unconditionally

The presentability chain of the area is stated as a sequence of `Prop`-valued hypotheses in
`Basic.lean` (`PointwiseColimitIsSheaf → SectionsFiltered → AtomsPresentable →
TestObjectsPresentable`), each with its own module proving the implication, so that the pieces can
be handed out and checked separately.

Now that every link is proved, this file records the resulting *unconditional* statements, which
are the facts a caller actually wants:

* `Work.REFL.sections_preserves_filtered_colimits` — the sections functor `M ↦ M(S)` preserves
  filtered colimits (filtered colimits of light condensed abelian groups are computed
  sectionwise);
* `Work.REFL.zfree_isCardinalPresentable` — `ℤ[S]` is `ℵ₀`-presentable (compact) for each light
  profinite `S`;
* `Work.REFL.tmul_P_zfree_isCardinalPresentable` — the test objects `P ⊗ ℤ[S]` are
  `ℵ₀`-presentable.

(The last one uses that `P` is a retract of `ℤ[ℕ∪{∞}]` and `ℤ[S] ⊗ ℤ[T] ≅ ℤ[S × T]`.)
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.REFL

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- **Filtered colimits of light condensed abelian groups are computed sectionwise.** -/
theorem sections_preserves_filtered_colimits : SectionsFiltered :=
  sections_filtered pointwise_colimit_isSheaf

/-- **The free objects `ℤ[S]` are `ℵ₀`-presentable** (compact). -/
theorem zfree_isCardinalPresentable : AtomsPresentable :=
  atoms_presentable sections_preserves_filtered_colimits

/-- **The test objects `P ⊗ ℤ[S]` are `ℵ₀`-presentable** (compact). -/
theorem tmul_P_zfree_isCardinalPresentable : TestObjectsPresentable :=
  test_objects_presentable zfree_isCardinalPresentable

/-- Unfolded form of `Work.REFL.sections_preserves_filtered_colimits`: `M ↦ M(S)` commutes with
filtered colimits, for every light profinite `S`. -/
theorem sections_preservesColimitsOfShape (J : Type) [SmallCategory J] [IsFiltered J]
    (S : LightProfinite.{0}) : PreservesColimitsOfShape J (sections S) :=
  sections_preserves_filtered_colimits J S

/-- Unfolded form of `Work.REFL.zfree_isCardinalPresentable`. -/
theorem zfree_isCardinalPresentable_apply (S : LightProfinite.{0}) :
    IsCardinalPresentable ((free ℤ).obj S.toCondensed) (Cardinal.aleph0 : Cardinal.{0}) :=
  zfree_isCardinalPresentable S

/-- Unfolded form of `Work.REFL.tmul_P_zfree_isCardinalPresentable`. -/
theorem tmul_P_zfree_isCardinalPresentable_apply (S : LightProfinite.{0}) :
    IsCardinalPresentable (P ⊗ (free ℤ).obj S.toCondensed) (Cardinal.aleph0 : Cardinal.{0}) :=
  tmul_P_zfree_isCardinalPresentable S

end Work.REFL
