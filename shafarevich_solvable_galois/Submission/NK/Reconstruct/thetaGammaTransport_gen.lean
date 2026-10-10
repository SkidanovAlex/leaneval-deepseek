import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.Lemmas
import Submission.NK.Reconstruct.generalBaseChange_galToGamma
import Submission.NK.Reconstruct.thetaGammaTransport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Reconstruct

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

/-- **The transport identity of Shimizu's Proposition 4f.3 / Theorem 4.0, for an arbitrary number
field `K` (not necessarily Galois over `ℚ`).**  This is `NK.Reconstruct.thetaGammaTransport` with
the base fields `K` and `M` generalised from finite Galois levels over `ℚ` to arbitrary finite
number-field levels over `ℚ` (`NK.Reconstruct.NumFieldIn ℚ Ω`), which is the form needed for the
assembly of Shimizu's §4 (the level pairs `(L, levelMap ϕ L)`). -/
theorem thetaGammaTransport_gen {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (K : NK.Reconstruct.NumFieldIn ℚ Ω) (θ : Ω ≃ₐ[ℚ] Ω) (ℓ : ℕ) [Fact ℓ.Prime]
    (M : NK.Reconstruct.NumFieldIn ℚ Ω) (hM : M.L = K.L.map θ.symm.toAlgHom)
    [IsSepClosure ↥M.L Ω] [IsSepClosure ↥K.L Ω]
    (L : NK.Reconstruct.FrobLevel ℚ Ω) [IsSepClosure ↥L.L Ω]
    (hKL : K.L ≤ L.L) (hML : M.L ≤ L.L) (hθL : ∀ x : Ω, x ∈ L.L ↔ θ x ∈ L.L) :
    ∃ Ψ : NK.Reconstruct.Gamma ↥M.L Ω ℓ ≃* NK.Reconstruct.Gamma ↥K.L Ω ℓ,
      Continuous ⇑Ψ ∧
      (NK.Reconstruct.ambientPi K L hKL ℓ).comp (NK.Reconstruct.tauStar L.L ℓ θ hθL)
        = (Ψ : NK.Reconstruct.Gamma ↥M.L Ω ℓ →* NK.Reconstruct.Gamma ↥K.L Ω ℓ).comp
            (NK.Reconstruct.ambientPi M L hML ℓ) := by
  classical
  -- `θ.symm` maps the embedded copy of `K.L` onto that of `M.L`.
  have hMB : Submission.NeukirchUchida.MapsBase (algebraMap ↥M.L Ω) (algebraMap ↥K.L Ω)
      (θ.symm : Ω ≃+* Ω) := mapsBase_of_map_eq K.L M.L θ.symm hM
  -- Conjugation by `θ` is a homeomorphism `Gal(Ω/M.L) ≃* Gal(Ω/K.L)`.
  have hφ : IsHomeomorph
      (Submission.NeukirchUchida.conjHomEquiv hMB : Gal(Ω/↥M.L) → Gal(Ω/↥K.L)) :=
    NK.NeukirchUchida.isHomeomorph_conjHomEquiv (θ.symm : Ω ≃+* Ω) hMB
  -- The isomorphism `Ψ : Γ_M ≅ Γ_K` induced by it.
  obtain ⟨Ψ, hΨ, -⟩ := NK.Reconstruct.exists_gammaEquivOfPhi
    (Submission.NeukirchUchida.conjHomEquiv hMB) hφ ℓ
  -- Continuity: `galToGamma_M` is a quotient map (compact → Hausdorff) and
  -- `Ψ ∘ galToGamma_M = galToGamma_K ∘ ϕ` is continuous.
  have hΨcont : Continuous ⇑Ψ := by
    haveI : T2Space (NK.Reconstruct.Gamma ↥M.L Ω ℓ) := inferInstance
    have hquot : Topology.IsQuotientMap ⇑(NK.Reconstruct.galToGamma (K := ↥M.L) (K' := Ω) ℓ) :=
      Topology.IsQuotientMap.of_surjective_continuous
        (NK.Reconstruct.galToGamma_surjective (K := ↥M.L) (K' := Ω) ℓ)
        (NK.Reconstruct.galToGamma_continuous (K := ↥M.L) (K' := Ω) ℓ)
    refine (Topology.IsQuotientMap.continuous_iff hquot).mpr ?_
    have heq : (⇑Ψ) ∘ (⇑(NK.Reconstruct.galToGamma (K := ↥M.L) (K' := Ω) ℓ))
        = (⇑(NK.Reconstruct.galToGamma (K := ↥K.L) (K' := Ω) ℓ)) ∘
            (⇑(Submission.NeukirchUchida.conjHomEquiv hMB)) := by
      funext g
      exact hΨ g
    rw [heq]
    exact (NK.Reconstruct.galToGamma_continuous (K := ↥K.L) (K' := Ω) ℓ).comp hφ.continuous
  refine ⟨Ψ, hΨcont, ?_⟩
  -- Both sides are homomorphisms out of `Γ_L`; it suffices to compare them on the image of the
  -- surjection `galToGamma : Gal(Ω/L) ↠ Γ_L`.
  refine MonoidHom.ext (fun γ => ?_)
  obtain ⟨σ, hσ⟩ := NK.Reconstruct.galToGamma_surjective (K := ↥L.L) (K' := Ω) ℓ γ
  rw [← hσ]
  simp only [MonoidHom.comp_apply]
  change (NK.Reconstruct.ambientPi K L hKL ℓ)
      (NK.Reconstruct.tauStar L.L ℓ θ.toRingEquiv hθL
        (NK.Reconstruct.galToGamma (K := ↥L.L) (K' := Ω) ℓ σ))
    = Ψ ((NK.Reconstruct.ambientPi M L hML ℓ)
        (NK.Reconstruct.galToGamma (K := ↥L.L) (K' := Ω) ℓ σ))
  -- `τ^*(galToGamma σ) = galToGamma (θ σ θ⁻¹)`.
  rw [NK.Reconstruct.tauStar_galToGamma]
  -- The two base changes, at the levels `L/K` and `L/M`.
  have hK : (NK.Reconstruct.ambientPi K L hKL ℓ)
      (NK.Reconstruct.galToGamma (K := ↥L.L) (K' := Ω) ℓ
        (NK.Reconstruct.ringConjHom L.L (θ : Ω ≃+* Ω) hθL σ))
      = NK.Reconstruct.galToGamma (K := ↥K.L) (K' := Ω) ℓ
          (NK.Reconstruct.galRestrict hKL
            (NK.Reconstruct.ringConjHom L.L (θ : Ω ≃+* Ω) hθL σ)) :=
    NK.Reconstruct.ambientPi_galToGamma K L hKL ℓ
      (NK.Reconstruct.ringConjHom L.L (θ : Ω ≃+* Ω) hθL σ)
  have hMstep : (NK.Reconstruct.ambientPi M L hML ℓ)
      (NK.Reconstruct.galToGamma (K := ↥L.L) (K' := Ω) ℓ σ)
      = NK.Reconstruct.galToGamma (K := ↥M.L) (K' := Ω) ℓ
          (NK.Reconstruct.galRestrict hML σ) :=
    NK.Reconstruct.ambientPi_galToGamma M L hML ℓ σ
  -- The two conjugates of `σ` agree as automorphisms of `Ω/K.L`.
  have hDE : NK.Reconstruct.galRestrict hKL
        (NK.Reconstruct.ringConjHom L.L (θ : Ω ≃+* Ω) hθL σ)
      = Submission.NeukirchUchida.conjHomEquiv hMB (NK.Reconstruct.galRestrict hML σ) := by
    ext x
    rw [NK.Reconstruct.galRestrict_apply, NK.Reconstruct.ringConjHom_apply,
      show (Submission.NeukirchUchida.conjHomEquiv hMB
          (NK.Reconstruct.galRestrict hML σ)) x
        = (Submission.NeukirchUchida.conj hMB (NK.Reconstruct.galRestrict hML σ)) x from rfl,
      Submission.NeukirchUchida.conj_apply, NK.Reconstruct.galRestrict_apply]
    rfl
  -- Assemble: `π_{L/K} τ^* = galToGamma (θσθ⁻¹) = Ψ π_{L/M}`.
  exact Eq.trans hK (Eq.trans
    (congrArg ⇑(NK.Reconstruct.galToGamma (K := ↥K.L) (K' := Ω) ℓ) hDE)
    (Eq.symm (Eq.trans (congrArg ⇑Ψ hMstep) (hΨ _))))

end NK.Reconstruct
