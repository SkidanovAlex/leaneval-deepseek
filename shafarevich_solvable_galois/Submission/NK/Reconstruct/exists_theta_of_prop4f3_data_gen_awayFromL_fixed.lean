import Mathlib
import Submission.NK.Reconstruct.levelPairData
import Submission.NK.Reconstruct.prop4f3AwayFromL
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shimizu's Theorem 4.0 with the same `τ` at several levels

`NK.Reconstruct.exists_theta_of_prop4f3_data_gen_awayFromL`
(`Submission/Work/Reconstruct/prop4f3AwayFromL.lean`) produces some `τ ∈ Gal(L/ℚ)` with
`K₁.L = K₂.L.map (Θ τ).symm.toAlgHom`, from the Frobenius correspondence *modulo torsion* at
completely split primes of residue characteristic `≠ ℓ`.

The present statement is the **fixed-`τ`** form of that assembly: instead of asserting the existence
of `τ`, it takes `τ ∈ Gal(L/ℚ)` together with the conclusion of Shimizu's Proposition 4f.3 *at that
fixed `τ`*,

  `∀ γ, gammaHausMk (σbar (ambientPi K₁ L h₁ ℓ γ)) = gammaHausMk (ambientPi K₂ L h₂ ℓ (tauStar (Θ τ) γ))`,

and concludes the field equality `K₁.L = K₂.L.map (Θ τ).symm.toAlgHom` for *that* `τ`.

This is what a caller running Shimizu's totally imaginary twist needs: the twist applies the
machinery of 4f.3–4f.5 to two different pairs `(L₁, L₁')` and `(L₂, L₂')` and has to intersect the
resulting fields, which is legitimate only if the two applications use the *same* `τ ∈ G(Lₐᵤₓ/ℚ)`.
The proof is exactly the assembly of `NK.Reconstruct.exists_theta_of_prop4f3_data_gen_awayFromL`
with the existential `τ` already in hand.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4
(Theorem 4.0, Proposition 4f.3, Proposition 4f.6).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

open scoped NumberField Pointwise

theorem exists_theta_of_prop4f3_data_gen_awayFromL_fixed {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (K₁ K₂ : NK.Reconstruct.NumFieldIn ℚ Ω) (L : NK.Reconstruct.FrobLevel ℚ Ω)
    (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥L.L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (σbar : NK.Reconstruct.Gamma ↥K₁.L Ω ℓ ≃* NK.Reconstruct.Gamma ↥K₂.L Ω ℓ)
    (hσbar : Continuous ⇑σbar)
    (Θ : Gal(↥L.L/ℚ) → Ω ≃ₐ[ℚ] Ω)
    (hΘmem : ∀ τ, ∀ x : Ω, x ∈ L.L ↔ Θ τ x ∈ L.L)
    (hΘres : ∀ τ (x : ↥L.L), Θ τ (x : Ω) = (τ x : Ω))
    (τ : Gal(↥L.L/ℚ))
    (hτ : ∀ γ : NK.Reconstruct.Gamma ↥L.L Ω ℓ,
      NK.Reconstruct.gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ
          (σbar (NK.Reconstruct.ambientPi K₁ L h₁ ℓ γ))
        = NK.Reconstruct.gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ
            (NK.Reconstruct.ambientPi K₂ L h₂ ℓ
              (NK.Reconstruct.tauStar L.L ℓ ((Θ τ : Ω ≃+* Ω)) (hΘmem τ) γ)))
    (hcomplex : ∃ v : NumberField.InfinitePlace ↥K₁.L, NumberField.InfinitePlace.IsComplex v)
    (h45 : NK.Reconstruct.Fourf5InputGen Ω ℓ) :
    K₁.L = K₂.L.map (Θ τ).symm.toAlgHom := by
  classical
  -- Step 1: the `θ⁻¹`-image `M` of `K₂`, and the transport isomorphism `Ψ : Γ_M ≅ Γ_{K₂}`.
  set M : NumFieldIn ℚ Ω := K₂.map (Θ τ) with hMdef
  have hM : M.L = K₂.L.map (Θ τ).symm.toAlgHom := NumFieldIn.map_L K₂ (Θ τ)
  haveI : IsSepClosure ↥M.L Ω := hM ▸ isSepClosure_level (K₂.L.map (Θ τ).symm.toAlgHom)
  have hθL : ∀ x : Ω, x ∈ L.L ↔ (Θ τ) x ∈ L.L := hΘmem τ
  have hML : M.L ≤ L.L := by
    rw [hM]
    exact le_trans (IntermediateField.map_mono (Θ τ).symm.toAlgHom h₂)
      (map_symm_le_self L.L (Θ τ) hθL)
  obtain ⟨Ψ, hΨcont, hΨeq⟩ := thetaGammaTransport_gen K₂ (Θ τ) ℓ M hM L h₂ hML hθL
  -- Step 2: `σbar' := Ψ⁻¹ ∘ σbar`, and the reformulation of the pinning hypothesis.
  have hΨsymm_cont : Continuous ⇑(Ψ.symm : Gamma ↥K₂.L Ω ℓ →* Gamma ↥M.L Ω ℓ) :=
    continuous_symm_of_mulEquiv Ψ hΨcont
  let σbar' : Gamma ↥K₁.L Ω ℓ ≃* Gamma ↥M.L Ω ℓ := σbar.trans Ψ.symm
  have hσbar'cont : Continuous ⇑σbar' := hΨsymm_cont.comp hσbar
  have heq : ∀ γ : Gamma ↥L.L Ω ℓ,
      gammaHausMk (K := ↥M.L) (K' := Ω) ℓ (σbar' (ambientPi K₁ L h₁ ℓ γ))
        = gammaHausMk (K := ↥M.L) (K' := Ω) ℓ (ambientPi M L hML ℓ γ) := by
    intro γ
    have hτγ := hτ γ
    have hΨeqγ : (ambientPi K₂ L h₂ ℓ) (tauStar L.L ℓ (Θ τ) hθL γ)
        = Ψ (ambientPi M L hML ℓ γ) := by
      have h1 := DFunLike.congr_fun hΨeq γ
      rwa [MonoidHom.comp_apply] at h1
    have hstep : gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ
        (σbar (ambientPi K₁ L h₁ ℓ γ))
        = gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ (Ψ (ambientPi M L hML ℓ γ)) := by
      rw [hτγ, hΨeqγ]
    have h3 := congrArg
      (gammaHausLift ℓ (Ψ.symm : Gamma ↥K₂.L Ω ℓ →* Gamma ↥M.L Ω ℓ) hΨsymm_cont) hstep
    rw [gammaHausLift_comp, gammaHausLift_comp] at h3
    simpa [σbar', MulEquiv.trans_apply] using h3
  -- Step 3: Lemma 4f.4 for the pair `(K₁, M)`, then join with `L`.
  have h4f4 := lemma4f4_gen K₁ M L h₁ hML ℓ σbar' hσbar'cont heq
  have hsup : (levelInfinityOf K₁ ℓ ⊔ L.L : IntermediateField ℚ Ω)
      = (L.L ⊔ levelInfinityOf M ℓ : IntermediateField ℚ Ω) := by
    calc (levelInfinityOf K₁ ℓ ⊔ L.L : IntermediateField ℚ Ω)
        = (levelInfinityOf K₁ ℓ ⊔ M.L) ⊔ L.L := by rw [sup_assoc, sup_eq_right.mpr hML]
      _ = (K₁.L ⊔ levelInfinityOf M ℓ) ⊔ L.L := by rw [h4f4]
      _ = L.L ⊔ levelInfinityOf M ℓ := by
          rw [sup_assoc, sup_comm (levelInfinityOf M ℓ) L.L, ← sup_assoc,
            sup_eq_right.mpr h₁]
  -- Step 4: Proposition 4f.5 identifies `M` with `K₁`.
  have hKM : K₁.L = M.L := h45 K₁ M L h₁ hML hsup hcomplex
  exact hKM.trans hM

end NK.Reconstruct
