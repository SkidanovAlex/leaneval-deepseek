import Mathlib
import Submission.NK.Reconstruct.ambient4f3
import Submission.NK.Reconstruct.tauStarDef
import Submission.NK.Reconstruct.conjLevel
import Submission.NK.Reconstruct.gammaBaseChangeHom_galToGamma
import Submission.NK.Reconstruct.exists_gammaEquivOfPhi
import Submission.NK.Reconstruct.galToGamma_continuous
import Submission.NK.NeukirchUchida.isHomeomorph_conjHomEquiv

namespace NK.Reconstruct

open scoped NumberField

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The transport identity of Shimizu's Proposition 4f.3 (Theorem 4.0)

This file proves the identity by which the base change `π_{L/K}` is carried along a `ℚ`-algebra
automorphism `θ` of the separable closure `Ω`:

  `π_{L/K} ∘ τ^*_θ = Ψ ∘ π_{L/θ⁻¹(K)}`

where `Ψ : Γ_{θ⁻¹(K)} ≅ Γ_K` is the isomorphism induced by conjugation with `θ`.

## Route

Everything is read off on the images of the canonical surjections
`galToGamma : Gal(Ω/K) ↠ Γ_K` (the latter is continuous, and it is a quotient map because
`Gal(Ω/K)` is compact and `Γ_K` is Hausdorff — this is how the continuity of `Ψ` is obtained
without a level-by-level argument):

* `mapsBase_of_map_eq` turns the hypothesis `M.L = K.L.map θ.symm.toAlgHom` into Shimizu's
  `MapsBase` for the ring isomorphism `σ = θ.symm : Ω ≃+* Ω` (it maps the embedded copy of the
  base field `K.L` onto that of `M.L`), so that `Submission.NeukirchUchida.conjHomEquiv` gives the
  group isomorphism `Gal(Ω/M.L) ≃* Gal(Ω/K.L)`, `g ↦ θ g θ⁻¹`, which is a *homeomorphism*
  (`NK.NeukirchUchida.isHomeomorph_conjHomEquiv`);
* `NK.Reconstruct.exists_gammaEquivOfPhi` (applied to that homeomorphism) produces
  `Ψ : Γ_M ≅ Γ_K` with `Ψ (galToGamma g) = galToGamma (θ g θ⁻¹)`;
* the identity itself is then a computation on the image of `galToGamma`: on the one hand
  `tauStar_galToGamma` followed by `gammaBaseChangeHom_galToGamma` at the level `L/K` gives
  `galToGamma ((θ σ θ⁻¹)|_K)`, on the other hand `gammaBaseChangeHom_galToGamma` at the level
  `L/M` followed by the defining property of `Ψ` gives the same thing, the two conjugate
  automorphisms of `Ω` being equal because both are `x ↦ θ (σ (θ⁻¹ x))`.
-/

/-! ## Two elementary computations with the `ℚ`-algebra structure of an intermediate field -/

/-- The range of the structure map of an intermediate field of `Ω/ℚ` is the intermediate field
itself. -/
theorem coe_range_algebraMap {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (X : IntermediateField ℚ Ω) :
    ((algebraMap ↥X Ω).range : Set Ω) = (X : Set Ω) := by
  ext x
  rw [SetLike.mem_coe, RingHom.mem_range]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

/-- The image of the range of the structure map of `X` under a `ℚ`-algebra automorphism `e` of `Ω`
is the image of the level `X` under `e`. -/
theorem coe_map_range_algebraMap {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (X : IntermediateField ℚ Ω) (e : Ω ≃ₐ[ℚ] Ω) :
    ((Subring.map (e.toRingEquiv : Ω →+* Ω) (algebraMap ↥X Ω).range : Subring Ω) : Set Ω)
      = ((X.map e.toAlgHom : IntermediateField ℚ Ω) : Set Ω) := by
  rw [Subring.coe_map, coe_range_algebraMap, IntermediateField.coe_map]
  rfl

/-- **`MapsBase` from the level condition.**  If the intermediate field `Y` is the image of `X`
under a `ℚ`-algebra automorphism `e` of `Ω`, then `e` (read as a ring isomorphism) maps the
embedded copy of the base field `↥X` onto that of `↥Y`: this is exactly Shimizu's hypothesis
`M.L = K.L.map θ.symm.toAlgHom` in the form required by
`Submission.NeukirchUchida.conjHomEquiv`. -/
theorem mapsBase_of_map_eq {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (X Y : IntermediateField ℚ Ω) (e : Ω ≃ₐ[ℚ] Ω) (h : Y = X.map e.toAlgHom) :
    Submission.NeukirchUchida.MapsBase (algebraMap ↥Y Ω) (algebraMap ↥X Ω)
      (e.toRingEquiv : Ω ≃+* Ω) := by
  show Subring.map (e.toRingEquiv : Ω →+* Ω) (algebraMap ↥X Ω).range = (algebraMap ↥Y Ω).range
  refine Subring.ext (fun x => ?_)
  have h2 : x ∈ ((Subring.map (e.toRingEquiv : Ω →+* Ω) (algebraMap ↥X Ω).range : Subring Ω)
        : Set Ω)
      ↔ x ∈ ((algebraMap ↥Y Ω).range : Set Ω) := by
    rw [coe_map_range_algebraMap, h, coe_range_algebraMap]
  exact h2

/-- **The transport identity of Shimizu's Proposition 4f.3 / Theorem 4.0.**  Let `Ω/ℚ` be Galois and
separably closed, `θ` a `ℚ`-algebra automorphism of `Ω`, `K ⊆ L` finite Galois levels of `Ω/ℚ`
which `θ` preserves as a set (`hθL`), and `M` a finite Galois level with
`M.L = K.L.map θ.symm.toAlgHom` (the `θ⁻¹`-image of `K`, which lies in `L`).

Then there is a **continuous** isomorphism `Ψ : Γ_M ≅ Γ_K` — the one induced level-by-level by
conjugation with `θ` (`g ↦ θ g θ⁻¹`, which maps `Gal(Ω/θ⁻¹K)` into `Gal(Ω/K)`; its continuity is
what Shimizu's Lemma 4f.4 needs for the isomorphism `Ψ⁻¹ ∘ σbar`) — such that

  `π_{L/K} ∘ τ^*_θ = Ψ ∘ π_{L/M}`.

On `galToGamma`-elements the identity reads: for `σ ∈ Gal(Ω/L)`,
`π_{L/K}(τ^*(galToGamma σ)) = galToGamma (θ σ θ⁻¹)` (by `gammaBaseChangeHom_galToGamma` and
`tauStar_galToGamma`); while `π_{L/M}(galToGamma σ) = galToGamma_M σ` (because `σ` fixes
`L ⊇ θ⁻¹(K)`), and `Ψ` is conjugation by `θ`.  Levelwise this is exactly the existing
`NK.Reconstruct.conjLevelAlgEquivHom_restrictNormalHom` of `conjLevel.lean`; the projective-limit
gluing is the work. -/
theorem thetaGammaTransport {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (K : NK.Reconstruct.FrobLevel ℚ Ω) (θ : Ω ≃ₐ[ℚ] Ω) (ℓ : ℕ) [Fact ℓ.Prime]
    (M : NK.Reconstruct.FrobLevel ℚ Ω) (hM : M.L = K.L.map θ.symm.toAlgHom)
    [IsSepClosure ↥M.L Ω] [IsSepClosure ↥K.L Ω]
    (L : NK.Reconstruct.FrobLevel ℚ Ω) [IsSepClosure ↥L.L Ω]
    (hKL : K.L ≤ L.L) (hML : M.L ≤ L.L) (hθL : ∀ x : Ω, x ∈ L.L ↔ θ x ∈ L.L) :
    ∃ Ψ : NK.Reconstruct.Gamma ↥M.L Ω ℓ ≃* NK.Reconstruct.Gamma ↥K.L Ω ℓ,
      Continuous ⇑Ψ ∧
      (NK.Reconstruct.ambientPi (NumFieldIn.ofFrobLevel K) L hKL ℓ).comp
          (NK.Reconstruct.tauStar L.L ℓ θ hθL)
        = (Ψ : NK.Reconstruct.Gamma ↥M.L Ω ℓ →* NK.Reconstruct.Gamma ↥K.L Ω ℓ).comp
            (NK.Reconstruct.ambientPi (NumFieldIn.ofFrobLevel M) L hML ℓ) := by
  classical
  -- `θ.symm` maps the embedded copy of `K.L` onto that of `M.L`.
  have hMB : Submission.NeukirchUchida.MapsBase (algebraMap ↥M.L Ω) (algebraMap ↥K.L Ω)
      (θ.symm : Ω ≃+* Ω) := mapsBase_of_map_eq K.L M.L θ.symm hM
  -- Conjugation by `θ` is a homeomorphism `Gal(Ω/M.L) ≃* Gal(Ω/K.L)`.
  have hφ : IsHomeomorph
      (Submission.NeukirchUchida.conjHomEquiv hMB : Gal(Ω/↥M.L) → Gal(Ω/↥K.L)) :=
    NK.NeukirchUchida.isHomeomorph_conjHomEquiv (θ.symm : Ω ≃+* Ω) hMB
  -- The isomorphism `Ψ : Γ_M ≅ Γ_K` induced by it (Shimizu's `σ̄` in this setting).
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
  change (NK.Reconstruct.ambientPi (NumFieldIn.ofFrobLevel K) L hKL ℓ)
      (NK.Reconstruct.tauStar L.L ℓ θ.toRingEquiv hθL
        (NK.Reconstruct.galToGamma (K := ↥L.L) (K' := Ω) ℓ σ))
    = Ψ ((NK.Reconstruct.ambientPi (NumFieldIn.ofFrobLevel M) L hML ℓ)
        (NK.Reconstruct.galToGamma (K := ↥L.L) (K' := Ω) ℓ σ))
  -- `τ^*(galToGamma σ) = galToGamma (θ σ θ⁻¹)`.
  rw [NK.Reconstruct.tauStar_galToGamma]
  -- The two base changes, at the levels `L/K` and `L/M`.
  have hK : (NK.Reconstruct.ambientPi (NumFieldIn.ofFrobLevel K) L hKL ℓ)
      (NK.Reconstruct.galToGamma (K := ↥L.L) (K' := Ω) ℓ
        (NK.Reconstruct.ringConjHom L.L (θ : Ω ≃+* Ω) hθL σ))
      = NK.Reconstruct.galToGamma (K := ↥K.L) (K' := Ω) ℓ
          (AlgEquiv.restrictScalars ↥K.L
            (show Gal(Ω/↥(NK.Reconstruct.levelExtend K L hKL).L) from
              NK.Reconstruct.ringConjHom L.L (θ : Ω ≃+* Ω) hθL σ)) :=
    NK.Reconstruct.gammaBaseChangeHom_galToGamma (K := ↥K.L) (K' := Ω) ℓ
      (NK.Reconstruct.levelExtend K L hKL) _
  have hMstep : (NK.Reconstruct.ambientPi (NumFieldIn.ofFrobLevel M) L hML ℓ)
      (NK.Reconstruct.galToGamma (K := ↥L.L) (K' := Ω) ℓ σ)
      = NK.Reconstruct.galToGamma (K := ↥M.L) (K' := Ω) ℓ
          (AlgEquiv.restrictScalars ↥M.L
            (show Gal(Ω/↥(NK.Reconstruct.levelExtend M L hML).L) from σ)) :=
    NK.Reconstruct.gammaBaseChangeHom_galToGamma (K := ↥M.L) (K' := Ω) ℓ
      (NK.Reconstruct.levelExtend M L hML) _
  -- The two conjugates of `σ` agree as automorphisms of `Ω/K.L`.
  have hDE : AlgEquiv.restrictScalars ↥K.L
        (show Gal(Ω/↥(NK.Reconstruct.levelExtend K L hKL).L) from
          NK.Reconstruct.ringConjHom L.L (θ : Ω ≃+* Ω) hθL σ)
      = Submission.NeukirchUchida.conjHomEquiv hMB
          (AlgEquiv.restrictScalars ↥M.L
            (show Gal(Ω/↥(NK.Reconstruct.levelExtend M L hML).L) from σ)) := by
    ext x
    rw [AlgEquiv.restrictScalars_apply, NK.Reconstruct.ringConjHom_apply,
      show (Submission.NeukirchUchida.conjHomEquiv hMB
          (AlgEquiv.restrictScalars ↥M.L
            (show Gal(Ω/↥(NK.Reconstruct.levelExtend M L hML).L) from σ))) x
        = (Submission.NeukirchUchida.conj hMB
          (AlgEquiv.restrictScalars ↥M.L
            (show Gal(Ω/↥(NK.Reconstruct.levelExtend M L hML).L) from σ))) x from rfl,
      Submission.NeukirchUchida.conj_apply, AlgEquiv.restrictScalars_apply]
    rfl
  -- Assemble: `π_{L/K} τ^* = galToGamma (θσθ⁻¹) = Ψ π_{L/M}`.
  exact Eq.trans hK (Eq.trans
    (congrArg ⇑(NK.Reconstruct.galToGamma (K := ↥K.L) (K' := Ω) ℓ) hDE)
    (Eq.symm (Eq.trans (congrArg ⇑Ψ hMstep) (hΨ _))))

end NK.Reconstruct
