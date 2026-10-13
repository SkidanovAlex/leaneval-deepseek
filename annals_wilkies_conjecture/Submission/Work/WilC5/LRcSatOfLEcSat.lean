/-
  WilC5 — **`κ`-saturation transfers from `LEc` to the `rexp`-reduct `LRc`.**

  The one-element step of vdDMM §4 is stated for the `LEc`-structure of a model of
  `TE = Th(ℝ_exp)` — its hypothesis is `@IsSaturated LEc L _ κ` — but the cut-realisation lemma
  `Work.WilC5.realizes_cut` (`realizes_cut.lean`) is stated for the `LRc`-structure of the
  `rexp`-reduct.  The two are the same thing: every `LRc`-formula is equivalent, over an
  `LEc`-structure, to an `LEc`-formula (`Work.WilC5.formulaTrans`, `Translate.lean`), because the
  only extra symbol of `LRc` — the restricted exponential `rexp` — is the `LEc`-definable function
  `rexpFromExp`.  Hence a `κ`-saturated `LEc`-structure is `κ`-saturated for its `rexp`-reduct: an
  `LRc`-type pulls back to an `LEc`-type with the same finite satisfiability.

  (This is the plumbing that lets the §4 layer — which is written in the `LRc` language, with
  `reductStruct` as the `LRc`-structure on a model of `TE` — use the canonical cut/type machinery
  of the `rexp`-setting.)
-/
import Mathlib
import Submission.Work.WilC5.Saturation
import Submission.Work.WilC5.Translate
import Submission.Work.WilC5.realizes_cut

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

attribute [local instance] Work.WilC5.reductStruct

/-- **`κ`-saturation of the `rexp`-reduct of a `κ`-saturated model of `TE`.** -/
theorem lrcSaturated_of_lecSaturated {M : Type} [LEc.Structure M] (κ : Cardinal.{0})
    (h : @Work.WilC5.IsSaturated LEc M _ κ) :
    @Work.WilC5.IsSaturated LRc M (reductStruct M) κ := by
  classical
  letI : LRc.Structure M := reductStruct M
  intro A hA p hp
  set q : Set (LEc.Formula (A ⊕ Fin 1)) := {ψ | ∃ φ ∈ p, ψ = formulaTrans φ} with hq
  have hqmem : ∀ ψ, ψ ∈ q ↔ ∃ φ ∈ p, ψ = formulaTrans φ := fun ψ => Iff.rfl
  have hqfin : ∀ F : Finset (LEc.Formula (A ⊕ Fin 1)), (∀ ψ ∈ F, ψ ∈ q) →
      ∃ x : Fin 1 → M, ∀ ψ ∈ F,
        @BoundedFormula.Realize LEc M _ (A ⊕ Fin 1) 0 ψ
          (Sum.elim Subtype.val x) (fun i : Fin 0 => i.elim0) := by
    intro F hF
    have hg : ∀ b : {ψ // ψ ∈ F},
        ∃ φ ∈ p, (b.1 : LEc.Formula (A ⊕ Fin 1)) = formulaTrans φ :=
      fun b => (hqmem b.1).mp (hF b.1 b.2)
    set g : {ψ // ψ ∈ F} → LRc.Formula (A ⊕ Fin 1) :=
      fun b => Classical.choose (hg b) with hgdef
    have hg_mem : ∀ b : {ψ // ψ ∈ F}, g b ∈ p := fun b => (Classical.choose_spec (hg b)).1
    have hg_eq : ∀ b : {ψ // ψ ∈ F}, (b.1 : LEc.Formula (A ⊕ Fin 1)) =
        formulaTrans (g b) := fun b => (Classical.choose_spec (hg b)).2
    set G : Finset (LRc.Formula (A ⊕ Fin 1)) := F.attach.image g with hGdef
    have hGsub : ∀ φ ∈ G, φ ∈ p := by
      intro φ hφ
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hφ
      exact hg_mem b
    obtain ⟨x, hx⟩ := hp G hGsub
    refine ⟨x, fun ψ hψ => ?_⟩
    have hb : g ⟨ψ, hψ⟩ ∈ G :=
      Finset.mem_image.mpr ⟨⟨ψ, hψ⟩, Finset.mem_attach F ⟨ψ, hψ⟩, rfl⟩
    have h1 : @BoundedFormula.Realize LRc M (reductStruct M)
        (A ⊕ Fin 1) 0 (g ⟨ψ, hψ⟩) (Sum.elim Subtype.val x) (fun i : Fin 0 => i.elim0) :=
      hx (g ⟨ψ, hψ⟩) hb
    have hψeq : ψ = formulaTrans (g ⟨ψ, hψ⟩) := hg_eq ⟨ψ, hψ⟩
    rw [hψeq]
    exact (cutBounded_iff (formulaTrans (g ⟨ψ, hψ⟩))
      (Sum.elim Subtype.val x)).mpr ((formulaTrans_realize (g ⟨ψ, hψ⟩)
        (Sum.elim Subtype.val x) (fun i : Fin 0 => i.elim0)).mpr h1)
  obtain ⟨x, hx⟩ := h A hA q hqfin
  refine ⟨x, fun φ hφ => ?_⟩
  have hmem : formulaTrans φ ∈ q := ⟨φ, hφ, rfl⟩
  have h1 := hx (formulaTrans φ) hmem
  exact (cutBounded_iff φ (Sum.elim Subtype.val x)).mpr
    ((formulaTrans_realize φ (Sum.elim Subtype.val x) (fun i : Fin 0 => i.elim0)).mp
      ((cutBounded_iff (formulaTrans φ) (Sum.elim Subtype.val x)).mp h1))

end Work.WilC5
