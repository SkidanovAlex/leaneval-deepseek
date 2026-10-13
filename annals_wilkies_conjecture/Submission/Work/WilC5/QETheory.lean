/-
  WilC5 — the theory-level form of the residual content of C5.

  `TElog` is the theory of the standard `LElog`-structure `logStruct ℝ`, i.e. of
  `(ℝ, exp, log, ≤)` with the vdDMM logarithm.  This module contains

  * `Work.WilC5.logStruct_model_TElog` (*proved*, from the definitional translation
    `LogTranslation`): the definable expansion `logStruct M` of a model `M` of `TE` is a model of
    `TElog`.  Consequently the models of `TElog` are exactly the definable expansions of models of
    `TE`, and the `LEc`-sentences of `TElog` are exactly the axioms of `TE`;
  * `Work.WilC5.HasQE_TElog` (**the residual hole**): quantifier elimination for `TElog`, i.e.
    van den Dries–Macintyre–Marker, *The elementary theory of restricted analytic fields with
    exponentiation*, Ann. of Math. 140 (1994), Corollary 4.5 (used in their (4.10)).

  `Work.WilC5.DMM45_QE_of_hasQE` descends `HasQE_TElog` to the `LEc`-formula level
  (`Work.WilC5.DMM45_QE`), and `Synthesis.lean` derives `ModelComplete TE` from that.
-/
import Submission.Work.WilC5.LogTranslation
import Submission.Work.WilC5.QE

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- `M ⊨ φ`, for a *sentence* `φ`, in the `emptyVar`/`emptyBnd` form used by the translation
`LogTranslation`. -/
theorem sentence_realize_iff_emptyBnd {L : Language} {M : Type} [L.Structure M]
    (φ : L.Sentence) :
    (M ⊨ φ) ↔ @BoundedFormula.Realize L M _ Empty 0 φ
      (emptyVar : Empty → M) (emptyBnd : Fin 0 → M) :=
  (sentenceRealize_iff_bounded (L := L) (M := M) φ).trans
    (sentence_realize_irrel (inferInstance) φ _ (emptyVar : Empty → M) _
      (emptyBnd : Fin 0 → M))

/-- **The definable expansion of a model of `TE` is a model of `TElog`.**

This is the point of the definitional translation `LogTranslation`: every `LElog`-sentence true in
the standard structure is, by translation, an `LEc`-sentence true in `ℝ`, hence belongs to
`TE = Th(ℝ_exp)`, hence holds in `M`; translating back, it holds in `logStruct M`. -/
theorem logStruct_model_TElog {M : Type} [LEc.Structure M] (hM : M ⊨ TE) : M ⊨ TElog := by
  rw [Theory.model_iff]
  intro σ hσ
  obtain ⟨ψ, hψ⟩ := LogTranslation σ
  have hRTE : ℝ ⊨ TE := show ℝ ⊨ LEc.completeTheory ℝ from inferInstance
  -- `σ` holds in the standard model, in the `BoundedFormula.Realize` form at `emptyVar`
  have hσR : @BoundedFormula.Realize LElog ℝ (logStruct ℝ) Empty 0 σ
      (emptyVar : Empty → ℝ) (emptyBnd : Fin 0 → ℝ) :=
    (sentence_realize_iff_emptyBnd (L := LElog) (M := ℝ) σ).mp
      ((Language.mem_completeTheory (M := ℝ) (L := LElog)).mp hσ)
  -- hence `ψ` holds in `ℝ`
  have hψR : @Sentence.Realize LEc ℝ _ ψ :=
    (sentence_realize_iff_emptyBnd (L := LEc) (M := ℝ) ψ).mpr
      ((hψ ℝ hRTE (emptyVar : Empty → ℝ) (emptyBnd : Fin 0 → ℝ)).mp hσR)
  -- `ψ` is an axiom of `TE`, hence holds in `M`; translating back gives `logStruct M ⊨ σ`
  have hψmem : ψ ∈ TE := mem_completeTheory.mpr hψR
  have hψM : @BoundedFormula.Realize LEc M _ Empty 0 ψ
      (emptyVar : Empty → M) (emptyBnd : Fin 0 → M) :=
    (sentence_realize_iff_emptyBnd (L := LEc) (M := M) ψ).mp
      ((Theory.model_iff TE).mp hM ψ hψmem)
  exact (sentence_realize_iff_emptyBnd (L := LElog) (M := M) σ).mpr
    ((hψ M hM (emptyVar : Empty → M) (emptyBnd : Fin 0 → M)).mpr hψM)

/-! The residual hole of the area used to be stated here as

    `theorem Work.WilC5.HasQE_TElog : Work.WilC5.HasQE Work.WilC5.TElog`

It has been replaced by the conditional form in `DMM41.lean`:
`Work.WilC5.HasQE_TElog_of_DMM41 (hMCr) (hOM) (hVI) : HasQE TElog`, derived there from vdDMM
Theorem 4.1 (the single remaining hole `Work.WilC5.DMM41`) through the quantifier-elimination
test `Work.WilC5.HasQEOfExtensionProperty`.  This keeps the inputs `hMCr`, `hOM`, `hVI` of the
frozen area C5 visible in the chain.
-/

end Work.WilC5
