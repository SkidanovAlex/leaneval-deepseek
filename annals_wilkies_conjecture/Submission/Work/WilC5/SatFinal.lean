/-
  WilC5 — the final assembly: the term hull is a `κ`-saturated elementary extension of `M`.
-/
import Mathlib
import Submission.Work.WilC5.SatEmb
import Submission.Work.WilC5.SatHullModelsDiagram
import Submission.Work.WilC5.IsElementary_of_finSat
import Submission.Work.WilC5.Saturation

open FirstOrder Language
open scoped FirstOrder

-- `SatLang L C` is `L[[C]]` and `SatCt` is a `Σ`-type; both are defined by `def`s/`abbrev`s, so the
-- tactic machinery refuses to unfold them when elaborating implicit arguments.  Marking them
-- implicit-reducible for the duration of this file makes the library lemmas applicable; this is a
-- purely syntactic device and does not change any statement.
attribute [local implicit_reducible] FirstOrder.Language.withConstants Work.WilC5.SatC

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilC5

variable (L : FirstOrder.Language.{0, 0}) (M : Type) [instM : L.Structure M] (κ : Cardinal.{0})

/-- **Every nonempty structure has a `κ`-saturated elementary extension.** -/
theorem SatExists (L : FirstOrder.Language.{0, 0}) (M : Type) [instM : L.Structure M]
    (κ : Cardinal.{0}) (hM : Nonempty M) :
    ∃ (N : Type) (instN : L.Structure N) (f : @ElementaryEmbedding L M N _ instN),
      @IsSaturated L N instN κ := by
  have hN : @Theory.Model (SatLang L (SatCt L M κ)) (SatNC L M κ hM) (SatNstruc L M κ hM)
      (SatTot L M κ) := SatNmodel L M κ hM
  letI : (SatLang L (SatCt L M κ)).Structure (SatNC L M κ hM) := SatNstruc L M κ hM
  letI : L.Structure (SatNC L M κ hM) := SatReduct L M κ (SatNC L M κ hM)
  -- elementarity of the term hull
  have hel : (SatHull L M κ (SatNC L M κ hM)).IsElementary := by
    refine IsElementary_of_finSat (SatHull L M κ (SatNC L M κ hM)) κ ?_
    intro A hA p hp
    exact SatHullStrong L M κ hM (SatNC L M κ hM) hN A hA p hp
  letI : L.Structure ↥(SatHull L M κ (SatNC L M κ hM)) :=
    FirstOrder.Language.Substructure.inducedStructure
      (S := SatHull L M κ (SatNC L M κ hM))
  let e : ↥(SatHull L M κ (SatNC L M κ hM)) ↪ₑ[L] (SatNC L M κ hM) :=
    (⟨SatHull L M κ (SatNC L M κ hM), hel⟩ :
      L.ElementarySubstructure (SatNC L M κ hM)).subtype
  -- `S` is `κ`-saturated
  have hsat : @IsSaturated L ↥(SatHull L M κ (SatNC L M κ hM))
      (FirstOrder.Language.Substructure.inducedStructure
        (S := SatHull L M κ (SatNC L M κ hM))) κ := by
    intro A hA p hp
    have hpN : ∀ F : Finset (L.Formula (A ⊕ Fin 1)), (∀ φ ∈ F, φ ∈ p) →
        ∃ a : SatNC L M κ hM, ∀ φ ∈ F,
          @Formula.Realize L (SatNC L M κ hM) (SatReduct L M κ (SatNC L M κ hM))
            (A ⊕ Fin 1) φ
            (Sum.elim (fun x : A => (x : SatNC L M κ hM)) (fun _ : Fin 1 => a)) := by
      intro F hF
      obtain ⟨x, hx⟩ := hp F hF
      refine ⟨((x 0 : ↥(SatHull L M κ (SatNC L M κ hM))) : SatNC L M κ hM), fun φ hφ => ?_⟩
      have hval : (⇑e ∘ Sum.elim (Subtype.val : A → ↥(SatHull L M κ (SatNC L M κ hM))) x)
          = (Sum.elim (fun x : A => (x : SatNC L M κ hM))
              (fun _ : Fin 1 => ((x 0 : ↥(SatHull L M κ (SatNC L M κ hM))) : SatNC L M κ hM))) := by
        funext i
        rcases i with a' | k
        · rfl
        · exact congrArg (fun y : ↥(SatHull L M κ (SatNC L M κ hM)) => (y : SatNC L M κ hM))
            (congrArg x (Subsingleton.elim k 0))
      have h2 := (e.map_formula φ (Sum.elim Subtype.val x)).mpr (hx φ hφ)
      rwa [hval] at h2
    obtain ⟨a, ha⟩ := SatHullStrong L M κ hM (SatNC L M κ hM) hN A (Or.inr hA) p hpN
    refine ⟨fun _ => a, fun φ hφ => ?_⟩
    refine (e.map_formula φ (Sum.elim (Subtype.val : A → ↥(SatHull L M κ (SatNC L M κ hM)))
      (fun _ : Fin 1 => a))).mp ?_
    have hvv : (⇑e ∘ Sum.elim (Subtype.val : A → ↥(SatHull L M κ (SatNC L M κ hM)))
          (fun _ : Fin 1 => a))
        = (Sum.elim (fun x : A => (x : SatNC L M κ hM))
            (fun _ : Fin 1 => (a : SatNC L M κ hM))) := by
      funext i
      rcases i with a' | k <;> rfl
    rw [hvv]
    exact ha φ hφ
  -- the elementary embedding `M → S`
  letI : (SatLang L M).Structure ↥(SatHull L M κ (SatNC L M κ hM)) := SatEmbStruct L M κ hM
  have hdiag := SatHullModelsDiagram (L := L) (M := M) (κ := κ) hM
  haveI hExp : (L.lhomWithConstants M).IsExpansionOn ↥(SatHull L M κ (SatNC L M κ hM)) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  refine ⟨↥(SatHull L M κ (SatNC L M κ hM)),
    FirstOrder.Language.Substructure.inducedStructure (S := SatHull L M κ (SatNC L M κ hM)),
    @ElementaryEmbedding.ofModelsElementaryDiagram L M instM ↥(SatHull L M κ (SatNC L M κ hM))
      (FirstOrder.Language.Substructure.inducedStructure (S := SatHull L M κ (SatNC L M κ hM)))
      (SatEmbStruct L M κ hM) _ hdiag, hsat⟩

end Work.WilC5
