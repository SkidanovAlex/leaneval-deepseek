/-
  WilC5 — `SatTotSat`: the *total theory* `SatTot` is satisfiable.

  `SatTot` is the union, over the levels `x : SatIdx κ`, of the images of the complete theories
  `SatTh3 x` of the structures `SatMod3 x` built by the transfinite construction, transported to the
  language `L[[SatCTotal]]` of *all* constants along `SatIncTotal x`.

  The proof is the finite-satisfiability (compactness) assembly of the construction:

  * A finite set `T0` of sentences of `SatTot` mentions only finitely many levels, so
    `SatIdxBdd2` bounds the levels of the sentences of `T0` above.  We may therefore bound them
    *strictly*, by a level `z'` (the index type has no greatest element).
  * The level theories form a chain: `SatMain` says that `SatMod3 z` realizes every sentence of the
    specification `SatSpecG z`, and the specification of a level contains the images of the theories
    of all *lower* levels.  This gives `SatTh3MonoTot` below: for `x < z` and `σ ∈ SatTh3 x`, the
    image `(SatLangMap (SatIncTotal x)).onSentence σ` belongs to
    `(SatLangMap (SatIncTotal z)).onTheory (SatTh3 z)`.
  * Hence `T0` is contained in the image of a *single* theory `SatTh3 z'`.  That image is
    satisfiable, because `SatTh3 z'` is the complete theory of the nonempty structure `SatMod3 z'`
    and an injective language map preserves satisfiability.
-/
import Mathlib
import Submission.Work.WilC5.SatSetup
import Submission.Work.WilC5.SatBuild
import Submission.Work.WilC5.SatCore
import Submission.Work.WilC5.SatMain
import Submission.Work.WilC5.SatIdxBdd2
import Submission.Work.WilC5.SatMapFinSat
import Submission.Work.WilC5.SatHull

open FirstOrder Language
open scoped FirstOrder

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilC5

/-! ## Functoriality of `SatLangMap` on sentences -/

/-- `SatLangMap` is functorial: pushing a sentence forward along `f : C → C'` and then along
`g : C' → C''` is the same as pushing it forward along `g ∘ f`. -/
theorem SatLangMap_compW5 {L : FirstOrder.Language.{0, 0}} {C C' C'' : Type} (f : C → C')
    (g : C' → C'') (τ : (SatLang L C).Sentence) :
    (SatLangMap g).onSentence ((SatLangMap f).onSentence τ)
      = (SatLangMap (L := L) (g ∘ f)).onSentence τ := by
  -- `SatLangMap f` is `L.lhomWithConstantsMap f` definitionally, and the latter is a `sumMap`
  -- on which the composition law is checked symbolwise.
  have h : SatLangMap (L := L) (g ∘ f) = (SatLangMap g).comp (SatLangMap f) := by
    change L.lhomWithConstantsMap (g ∘ f) =
      (L.lhomWithConstantsMap g).comp (L.lhomWithConstantsMap f)
    apply LHom.funext
    · funext n
      funext x
      rcases x with a | c
      · rfl
      · cases n with
        | zero => rfl
        | succ k => exact isEmptyElim c
    · funext n
      funext x
      rcases x with a | c
      · rfl
      · exact isEmptyElim c
  rw [h]
  exact (congrFun (LHom.comp_onBoundedFormula (SatLangMap g) (SatLangMap f)) τ).symm

/-! ## Monotonicity of the level theories -/

/-- The level theories form a chain: for `x < z` the image of `SatTh3 x` in the language of all
constants is contained in the image of `SatTh3 z`.

Indeed the specification `SatSpecG z` contains the image of `SatTh3 x` under `SatInc` (it is its
"old" part), and `SatMain` says that `SatMod3 z` realizes everything in `SatSpecG z`; since
`SatTh3 z` is the complete theory of `SatMod3 z`, that image lies in `SatTh3 z`. -/
theorem SatTh3MonoTotW5 {L : FirstOrder.Language.{0, 0}} {M : Type} [instM : L.Structure M]
    {κ : Cardinal.{0}} (hM : Nonempty M) {x z : SatIdx κ} (h : x < z)
    (τ : (SatLang L (SatC L M κ x)).Sentence) (hτ : τ ∈ SatTh3 L M κ x) :
    (SatLangMap (SatIncTotal L M κ x)).onSentence τ
      ∈ (SatLangMap (SatIncTotal L M κ z)).onTheory (SatTh3 L M κ z) := by
  have hspec : (SatLangMap (SatInc L M κ (le_of_lt h))).onSentence τ ∈ SatSpecG L M κ z :=
    (mem_SatSpecG L M κ).mpr (Or.inr (Or.inl ⟨x, h, τ, hτ, rfl⟩))
  have hmono : (SatLangMap (SatInc L M κ (le_of_lt h))).onSentence τ ∈ SatTh3 L M κ z :=
    (SatMain L M κ hM z).2 _ hspec
  refine LHom.mem_onTheory.mpr
    ⟨(SatLangMap (SatInc L M κ (le_of_lt h))).onSentence τ, hmono, ?_⟩
  rw [SatLangMap_compW5 (L := L) (SatInc L M κ (le_of_lt h)) (SatIncTotal L M κ z) τ]
  exact congrArg (fun k => (SatLangMap (L := L) k).onSentence τ)
    (SatIncTotal_comp L M κ (le_of_lt h))

/-! ## The compactness assembly -/

/-- `SatTot` is finitely satisfiable: every finite set of sentences of the total theory is
contained in the image of a single level theory, which is satisfiable. -/
theorem SatTot_finSat {L : FirstOrder.Language.{0, 0}} {M : Type} [instM : L.Structure M]
    {κ : Cardinal.{0}} (hM : Nonempty M) : (SatTot L M κ).IsFinitelySatisfiable := by
  intro T0 hT0
  -- Each sentence of `T0` lies in the image of some level; the levels of `T0` are finitely many.
  rw [SatTot] at hT0
  have hg : ∀ σ : {s // s ∈ T0}, ∃ x : SatIdx κ,
      (σ.1 : (SatLang L (SatCt L M κ)).Sentence)
        ∈ (SatLangMap (SatIncTotal L M κ x)).onTheory (SatTh3 L M κ x) :=
    fun σ => Set.mem_iUnion.mp (hT0 σ.2)
  let g : {s // s ∈ T0} → SatIdx κ := fun σ => Classical.choose (hg σ)
  have hgspec : ∀ σ, (σ.1 : (SatLang L (SatCt L M κ)).Sentence)
      ∈ (SatLangMap (SatIncTotal L M κ (g σ))).onTheory (SatTh3 L M κ (g σ)) :=
    fun σ => Classical.choose_spec (hg σ)
  obtain ⟨z, hz⟩ := SatIdxBdd2 κ (↑(T0.attach.image g) : Set (SatIdx κ))
    (Or.inl (T0.attach.image g).finite_toSet)
  -- Bound the levels strictly, so that the monotonicity lemma applies to each of them.
  obtain ⟨z', hzz'⟩ := exists_gt z
  have hsub : (↑T0 : (SatLang L (SatCt L M κ)).Theory)
      ⊆ (SatLangMap (SatIncTotal L M κ z')).onTheory (SatTh3 L M κ z') := by
    intro σ hσ
    have hgz : g ⟨σ, hσ⟩ ≤ z :=
      hz _ (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨σ, hσ⟩, Finset.mem_attach _ _, rfl⟩))
    have hlt : g ⟨σ, hσ⟩ < z' := lt_of_le_of_lt hgz hzz'
    obtain ⟨τ, hτ, hτεq⟩ := LHom.mem_onTheory.mp (hgspec ⟨σ, hσ⟩)
    have hτεq' : (SatLangMap (SatIncTotal L M κ (g ⟨σ, hσ⟩))).onSentence τ = σ := hτεq
    rw [← hτεq']
    exact SatTh3MonoTotW5 hM hlt τ hτ
  -- The image of a single level theory is satisfiable: an injective language map pushes the
  -- satisfiability of the complete theory of the nonempty model `SatMod3 z'` forward.
  have hT : (SatTh3 L M κ z').IsSatisfiable := by
    have h := @FirstOrder.Language.completeTheory.isSatisfiable (SatLang L (SatC L M κ z'))
      (SatMod3 L M κ z') (SatStruc3 L M κ z') (SatMod3_nonempty L M κ z')
    simpa only [SatTh3] using h
  have hsat : ((SatLangMap (SatIncTotal L M κ z')).onTheory (SatTh3 L M κ z')).IsSatisfiable :=
    (Theory.isSatisfiable_onTheory_iff
      (SatLangMap_injective (SatIncTotal L M κ z') (SatIncTotal_injective L M κ z'))).2 hT
  exact hsat.mono hsub

theorem SatTotSat {L : FirstOrder.Language.{0, 0}} {M : Type} [instM : L.Structure M]
    {κ : Cardinal.{0}} (hM : Nonempty M) : (SatTot L M κ).IsSatisfiable :=
  (Theory.isSatisfiable_iff_isFinitelySatisfiable).2 (SatTot_finSat hM)

end Work.WilC5
