import Mathlib
import Submission.Work.Coherence.Basic
import Submission.Work.Coherence.char_inv_eq_conj
import Submission.Work.CharCore.fdRep_simple_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Coherence.irr_conj`

The set `Irr G` of irreducible complex characters of a finite group is stable under complex
conjugation: if `χ` is an irreducible character of `G` then so is `g ↦ conj (χ g)`.

The mathematical content is that the contragredient (dual) of an irreducible representation is
irreducible, combined with the identity `χ g⁻¹ = conj (χ g)` for characters of a finite group
(`Work.Coherence.char_inv_eq_conj`).  Indeed the dual of a representation `ρ` has character
`g ↦ ρ.character g⁻¹` (`FDRep.char_dual`), and for finite `G` every `ρ g` has finite order, so
`ρ.character g⁻¹ = conj (ρ.character g)`.

Irreducibility of the contragredient is proved through the annihilator correspondence: a
subrepresentation `T` of `ρ` has an annihilator `T° = {φ | ∀ v ∈ T, φ v = 0}`, which is a
subrepresentation of `ρ.dual`; a subrepresentation `S` of `ρ.dual` has a coannihilator
`S° = {v | ∀ φ ∈ S, φ v = 0}`, which is a subrepresentation of `ρ`.  The double annihilator of a
subspace of a vector space recovers the subspace (`Subspace.dualAnnihilator_dualCoannihilator_eq`,
`Subspace.dualCoannihilator_dualAnnihilator_eq`), so annihilator and coannihilator are inverse
bijections, `⊥` and `⊤` correspond, and the simple order transfers.

The statement is phrased with the character set `Work.Coherence.Irr`; the bridge between
simplicity of a bundled representation `V : FDRep ℂ G` and irreducibility of its underlying
representation `V.ρ` is `Work.CharCore.fdRep_simple_iff`.
-/

noncomputable section

open Classical

namespace Work.Coherence

section DualIsIrreducible

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V}

/-- The annihilator `T° = {φ | ∀ v ∈ T, φ v = 0}` of a subrepresentation `T` of `ρ`, viewed as a
subrepresentation of the contragredient `ρ.dual`.  It is `ρ.dual`-stable because
`(ρ.dual g φ) v = φ (ρ g⁻¹ v)` and `ρ g⁻¹ v ∈ T` for `v ∈ T`. -/
private def irrConjAnn (T : Subrepresentation ρ) : Subrepresentation ρ.dual where
  toSubmodule := T.toSubmodule.dualAnnihilator
  apply_mem_toSubmodule := fun g φ hφ => by
    rw [Submodule.mem_dualAnnihilator] at hφ ⊢
    intro v hv
    have hmem : ρ g⁻¹ v ∈ T.toSubmodule := T.apply_mem_toSubmodule g⁻¹ hv
    have h0 : φ (ρ g⁻¹ v) = 0 := hφ _ hmem
    simpa [Module.Dual.transpose_apply] using h0

/-- The coannihilator `S° = {v | ∀ φ ∈ S, φ v = 0}` of a subrepresentation `S` of the
contragredient `ρ.dual`, viewed as a subrepresentation of `ρ`.  It is `ρ`-stable because
`(ρ.dual g⁻¹) φ ∈ S` for `φ ∈ S`. -/
private def irrConjCoann (S : Subrepresentation ρ.dual) : Subrepresentation ρ where
  toSubmodule := S.toSubmodule.dualCoannihilator
  apply_mem_toSubmodule := fun g v hv => by
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro φ hφ
    have hmem : (ρ.dual g⁻¹) φ ∈ S.toSubmodule := S.apply_mem_toSubmodule g⁻¹ hφ
    have h0 : ((ρ.dual g⁻¹) φ) v = 0 := hv _ hmem
    simpa [Module.Dual.transpose_apply] using h0

private lemma irrConjAnn_injective : Function.Injective (irrConjAnn (ρ := ρ)) := by
  intro T₁ T₂ h
  have h' : T₁.toSubmodule.dualAnnihilator = T₂.toSubmodule.dualAnnihilator :=
    congrArg Subrepresentation.toSubmodule h
  apply Subrepresentation.toSubmodule_injective
  calc T₁.toSubmodule
      = T₁.toSubmodule.dualAnnihilator.dualCoannihilator :=
        (Subspace.dualAnnihilator_dualCoannihilator_eq (W := T₁.toSubmodule)).symm
    _ = T₂.toSubmodule.dualAnnihilator.dualCoannihilator := by rw [h']
    _ = T₂.toSubmodule := Subspace.dualAnnihilator_dualCoannihilator_eq

private lemma irrConjCoann_injective : Function.Injective (irrConjCoann (ρ := ρ)) := by
  intro S₁ S₂ h
  have h' : S₁.toSubmodule.dualCoannihilator = S₂.toSubmodule.dualCoannihilator :=
    congrArg Subrepresentation.toSubmodule h
  apply Subrepresentation.toSubmodule_injective
  calc S₁.toSubmodule
      = S₁.toSubmodule.dualCoannihilator.dualAnnihilator :=
        (Subspace.dualCoannihilator_dualAnnihilator_eq (W := S₁.toSubmodule)).symm
    _ = S₂.toSubmodule.dualCoannihilator.dualAnnihilator := by rw [h']
    _ = S₂.toSubmodule := Subspace.dualCoannihilator_dualAnnihilator_eq

/-- **The contragredient of an irreducible representation is irreducible.** -/
private theorem irrConj_dual_irreducible (h : ρ.IsIrreducible) : ρ.dual.IsIrreducible := by
  haveI := h
  haveI : Nontrivial (Subrepresentation ρ.dual) :=
    Function.Injective.nontrivial (irrConjAnn_injective (ρ := ρ))
  refine IsSimpleOrder.of_forall_eq_top (fun S hS => ?_)
  rcases IsSimpleOrder.eq_bot_or_eq_top (irrConjCoann S) with hT | hT
  · have hsub : S.toSubmodule = ⊤ := by
      calc S.toSubmodule
          = S.toSubmodule.dualCoannihilator.dualAnnihilator :=
            (Subspace.dualCoannihilator_dualAnnihilator_eq (W := S.toSubmodule)).symm
        _ = (⊥ : Submodule ℂ V).dualAnnihilator := by
              rw [show S.toSubmodule.dualCoannihilator = (⊥ : Submodule ℂ V) from
                congrArg Subrepresentation.toSubmodule hT]
        _ = ⊤ := Submodule.dualAnnihilator_bot
    exact Subrepresentation.toSubmodule_injective (by rw [hsub]; rfl)
  · exfalso
    apply hS
    have hsub : S.toSubmodule = ⊥ := by
      calc S.toSubmodule
          = S.toSubmodule.dualCoannihilator.dualAnnihilator :=
            (Subspace.dualCoannihilator_dualAnnihilator_eq (W := S.toSubmodule)).symm
        _ = (⊤ : Submodule ℂ V).dualAnnihilator := by
              rw [show S.toSubmodule.dualCoannihilator = (⊤ : Submodule ℂ V) from
                congrArg Subrepresentation.toSubmodule hT]
        _ = ⊥ := Submodule.dualAnnihilator_top
    exact Subrepresentation.toSubmodule_injective (by rw [hsub]; rfl)

end DualIsIrreducible

/-- **Complex conjugation preserves irreducibility of characters.**  The conjugate of an
irreducible complex character of a finite group is again irreducible: it is the character of the
contragredient of any representation affording `χ`, and the contragredient of an irreducible
representation is irreducible. -/
theorem irr_conj {G : Type*} [Group G] [Fintype G] {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    (fun g => starRingEnd ℂ (χ g)) ∈ Irr G := by
  obtain ⟨V, hV, rfl⟩ := hχ
  refine ⟨FDRep.of (Representation.dual V.ρ), ?_, ?_⟩
  · rw [Work.CharCore.fdRep_simple_iff, FDRep.of_ρ']
    exact irrConj_dual_irreducible (ρ := V.ρ) ((Work.CharCore.fdRep_simple_iff V).mp hV)
  · funext g
    rw [FDRep.char_dual]
    exact char_inv_eq_conj V g

end Work.Coherence
