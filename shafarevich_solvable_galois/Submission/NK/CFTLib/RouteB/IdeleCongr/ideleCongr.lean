/-
Transport of the idèle group along a `K`-algebra isomorphism `e : L ≃ₐ[K] L'` of number fields.

Given a compatible family of local field isomorphisms `Φ v : L_v ≃+* L'_{congr e v}` (carrying
local units onto local units, and continuous), we build the induced isomorphism
`𝕀 L ≃* 𝕀 L'` and show that it commutes with the Galois actions
(`σ` on the left, `AlgEquiv.autCongr e σ` on the right) and carries principal idèles to principal
idèles.

The key point is that the hypotheses on `Φ` (compatibility with the embeddings of `L`, and
continuity) determine `Φ` uniquely, so that the local field isomorphisms `Φ v` automatically
intertwine the canonical local isomorphisms `Place.localRingEquiv` attached to the Galois actions.
This is proved by the density of `L` in `L_v` (`NK.GlobalCFT.Galois.denseRange_algebraMap_localField`).
-/
import Mathlib
import Submission.NK.CFTLib.RouteB.IdeleCongr.PlaceCongr
import Submission.NK.GlobalCFTdeep.Transport.IdeleTransport
import Submission.NK.GlobalCFT.Galois.globalCFT_localRingEquiv_comp
import Submission.NK.GlobalCFT.Galois.globalCFT_mul_smul_idele
import Submission.NK.GlobalCFT.Galois.globalCFT_smul_place_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.RouteB.IdeleCongr

open NK.GlobalCFT

variable {K L L' : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Field L'] [NumberField L'] [Algebra K L] [Algebra K L']

/-! ### Elementary transport of units along an equality of places -/

/-- Transporting a unit of a local field along an equality of places commutes with the coercion to
the ambient local field. -/
lemma units_coe_cast {L : Type} [Field L] [NumberField L] {a b : Place L} (h : a = b)
    (u : (Place.localField L a)ˣ) :
    ((h ▸ u : (Place.localField L b)ˣ) : Place.localField L b)
      = h ▸ (u : Place.localField L a) := by
  cases h; rfl

/-! ### The local isomorphisms `Φ v` intertwine the canonical local isomorphisms -/

/-- **The twist lemma.**  Let `Φ v : L_v ≃+* L'_{congr e v}` be a system of local field
isomorphisms compatible with the embeddings of `L` (`hmap`) and continuous (`hcont`).  If
`σ : Gal(L/K)` acts on `L`, `τ` acts on `L'` and `τ` agrees with `σ` on the image of `e`
(`hτ`), then `Φ` transports the canonical local isomorphism attached to `σ` to the one attached to
`τ`, transported along the corresponding equality `h` of the places of `L'`.

The proof is the standard density argument: after moving the transport along `h` out of the way,
both sides are continuous ring homomorphisms `L_v → L'_{τ • congr e v}` which agree on the dense
image of `L` in `L_v`. -/
theorem localRingEquiv_twist (e : L ≃ₐ[K] L')
    (Φ : (v : Place L) → Place.localField L v ≃+* Place.localField L' (Place.congr e v))
    (hmap : ∀ (v : Place L) (x : L),
      Φ v (algebraMap L (Place.localField L v) x) =
        algebraMap L' (Place.localField L' (Place.congr e v)) (e x))
    (hcont : ∀ v : Place L, Continuous (Φ v))
    {σ : L ≃ₐ[K] L} {τ : L' ≃ₐ[K] L'} (hτ : ∀ x : L, τ (e x) = e (σ x))
    (v : Place L) (h : Place.congr e (σ • v) = τ • Place.congr e v)
    (y : Place.localField L v) :
    h ▸ (Φ (σ • v) (Place.localRingEquiv σ v y))
      = Place.localRingEquiv τ (Place.congr e v) (Φ v y) := by
  have hdense : DenseRange (algebraMap L (Place.localField L v)) :=
    NK.GlobalCFT.Galois.denseRange_algebraMap_localField v
  have hcont₁ : Continuous (fun z => h ▸ (Φ (σ • v) (Place.localRingEquiv σ v z))) :=
    NK.GlobalCFT.Galois.continuous_localField_cast h
      ((hcont (σ • v)).comp (NK.GlobalCFT.Galois.continuous_localRingEquiv σ v))
  have hcont₂ : Continuous
      (fun z => Place.localRingEquiv τ (Place.congr e v) (Φ v z)) :=
    (NK.GlobalCFT.Galois.continuous_localRingEquiv τ (Place.congr e v)).comp (hcont v)
  have hfun : (fun z => h ▸ (Φ (σ • v) (Place.localRingEquiv σ v z))) =
      fun z => Place.localRingEquiv τ (Place.congr e v) (Φ v z) := by
    refine DenseRange.equalizer hdense hcont₁ hcont₂ ?_
    funext x
    simp only [Function.comp_apply]
    rw [Place.localRingEquiv_algebraMap σ v x,
      hmap (σ • v) (σ x),
      NK.GlobalCFT.Galois.localField_cast_algebraMap h (e (σ x)),
      hmap v x,
      Place.localRingEquiv_algebraMap τ (Place.congr e v) (e x),
      hτ x]
  exact congrFun hfun y

/-- The form of `localRingEquiv_twist` used for the Galois equivariance of the idèle transport:
for `τ = (AlgEquiv.autCongr e σ)⁻¹` and `σ⁻¹`, the inverse of the canonical local isomorphism
attached to `τ` undoes the transport of `Φ (σ⁻¹ • v)`. -/
theorem phi_symm_twist (e : L ≃ₐ[K] L')
    (Φ : (v : Place L) → Place.localField L v ≃+* Place.localField L' (Place.congr e v))
    (hmap : ∀ (v : Place L) (x : L),
      Φ v (algebraMap L (Place.localField L v) x) =
        algebraMap L' (Place.localField L' (Place.congr e v)) (e x))
    (hcont : ∀ v : Place L, Continuous (Φ v))
    (σ : L ≃ₐ[K] L) (v : Place L)
    (h2 : Place.congr e (σ⁻¹ • v) = (AlgEquiv.autCongr e σ)⁻¹ • Place.congr e v)
    (z : Place.localField L (σ⁻¹ • v)) :
    (Place.localRingEquiv (AlgEquiv.autCongr e σ)⁻¹ (Place.congr e v)).symm
        (h2 ▸ (Φ (σ⁻¹ • v) z))
      = Φ v ((Place.localRingEquiv σ⁻¹ v).symm z) := by
  have hτ : ∀ x : L, (AlgEquiv.autCongr e σ)⁻¹ (e x) = e (σ⁻¹ x) := by
    intro x
    simp [AlgEquiv.autCongr_apply]
  have h := localRingEquiv_twist e Φ hmap hcont hτ v h2 ((Place.localRingEquiv σ⁻¹ v).symm z)
  rw [RingEquiv.apply_symm_apply] at h
  rw [h, RingEquiv.symm_apply_apply]

/-! ### The idèle transport -/

/-- **The transport of the idèle group** along a `K`-algebra isomorphism `e : L ≃ₐ[K] L'` and a
compatible system of local field isomorphisms `Φ`, obtained by reindexing the product of local
unit groups along the bijection `Place.congr e` of places. -/
def ideleCongrEquiv (e : L ≃ₐ[K] L')
    (Φ : (v : Place L) → Place.localField L v ≃+* Place.localField L' (Place.congr e v))
    (hunits : ∀ (v : Place L) (u : (Place.localField L v)ˣ),
      u ∈ Place.localUnits L v ↔
        Units.map (Φ v).toMonoidHom u ∈ Place.localUnits L' (Place.congr e v)) :
    Idele L ≃* Idele L' :=
  NK.GlobalCFTdeep.Transport.IdeleTransport.ideleEquiv (Place.congr e) Φ hunits

variable {e : L ≃ₐ[K] L'}
  {Φ : (v : Place L) → Place.localField L v ≃+* Place.localField L' (Place.congr e v)}
  {hunits : ∀ (v : Place L) (u : (Place.localField L v)ˣ),
      u ∈ Place.localUnits L v ↔
        Units.map (Φ v).toMonoidHom u ∈ Place.localUnits L' (Place.congr e v)}

/-- The evaluation of the idèle transport at the place `congr e v`. -/
theorem ideleCongrEquiv_apply_place (x : Idele L) (v : Place L) :
    ideleCongrEquiv e Φ hunits x (Place.congr e v) = Units.map (Φ v).toMonoidHom (x v) :=
  NK.GlobalCFTdeep.Transport.IdeleTransport.ideleEquiv_apply_placeEquiv
    (Place.congr e) Φ hunits x v

/-- The idèle transport carries principal idèles to principal idèles. -/
theorem ideleCongrEquiv_principalIdele (hmap : ∀ (v : Place L) (x : L),
      Φ v (algebraMap L (Place.localField L v) x) =
        algebraMap L' (Place.localField L' (Place.congr e v)) (e x)) (k : Lˣ) :
    ideleCongrEquiv e Φ hunits (Idele.principalIdele L k)
      = Idele.principalIdele L' (Units.map e.toMonoidHom k) := by
  refine Idele.ext fun w => ?_
  obtain ⟨v, rfl⟩ := (Place.congr e).surjective w
  rw [ideleCongrEquiv_apply_place, Idele.principalIdele_apply, Idele.principalIdele_apply]
  refine Units.ext ?_
  simp only [Units.coe_map]
  exact hmap v ↑k

/-- **The Galois equivariance of the idèle transport.** -/
theorem ideleCongrEquiv_smul (hmap : ∀ (v : Place L) (x : L),
      Φ v (algebraMap L (Place.localField L v) x) =
        algebraMap L' (Place.localField L' (Place.congr e v)) (e x))
    (hcont : ∀ v : Place L, Continuous (Φ v)) (σ : L ≃ₐ[K] L) (x : Idele L) :
    ideleCongrEquiv e Φ hunits (σ • x)
      = AlgEquiv.autCongr e σ • (ideleCongrEquiv e Φ hunits x) := by
  refine Idele.ext fun w => ?_
  obtain ⟨v, rfl⟩ := (Place.congr e).surjective w
  have h2 : Place.congr e (σ⁻¹ • v) = (AlgEquiv.autCongr e σ)⁻¹ • Place.congr e v := by
    rw [← map_inv]; exact Place.congr_smul e σ⁻¹ v
  rw [ideleCongrEquiv_apply_place, Idele.smul_apply, Idele.smul_apply]
  have hcast : (ideleCongrEquiv e Φ hunits x) ((AlgEquiv.autCongr e σ)⁻¹ • Place.congr e v)
      = h2 ▸ ((ideleCongrEquiv e Φ hunits x) (Place.congr e (σ⁻¹ • v))) :=
    (NK.GlobalCFT.Galois.globalCFT_cast_dep_apply
      (fun w => (ideleCongrEquiv e Φ hunits x) w) h2).symm
  rw [hcast, ideleCongrEquiv_apply_place]
  refine Units.ext ?_
  simp only [Units.coe_map]
  rw [units_coe_cast h2, Units.coe_map]
  exact (phi_symm_twist e Φ hmap hcont σ v h2 _).symm

/-! ### The main theorem -/

theorem ideleCongr {K L L' : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Field L'] [NumberField L'] [Algebra K L] [Algebra K L'] (e : L ≃ₐ[K] L')
    (Φ : (v : NK.GlobalCFT.Place L) → NK.GlobalCFT.Place.localField L v ≃+*
      NK.GlobalCFT.Place.localField L' (NK.GlobalCFT.Place.congr e v))
    (hmap : ∀ (v : NK.GlobalCFT.Place L) (x : L),
      Φ v (algebraMap L (NK.GlobalCFT.Place.localField L v) x) =
        algebraMap L' (NK.GlobalCFT.Place.localField L' (NK.GlobalCFT.Place.congr e v)) (e x))
    (hunits : ∀ (v : NK.GlobalCFT.Place L) (u : (NK.GlobalCFT.Place.localField L v)ˣ),
      u ∈ NK.GlobalCFT.Place.localUnits L v ↔
        Units.map (Φ v).toMonoidHom u ∈
          NK.GlobalCFT.Place.localUnits L' (NK.GlobalCFT.Place.congr e v))
    (hcont : ∀ v : NK.GlobalCFT.Place L, Continuous (Φ v)) :
    ∃ Ψ : NK.GlobalCFT.Idele L ≃* NK.GlobalCFT.Idele L',
      Subgroup.map Ψ.toMonoidHom (NK.GlobalCFT.Idele.principalSubgroup L) =
          NK.GlobalCFT.Idele.principalSubgroup L' ∧
        (∀ (σ : L ≃ₐ[K] L) (x : NK.GlobalCFT.Idele L),
          Ψ (σ • x) = (AlgEquiv.autCongr e σ) • Ψ x) := by
  refine ⟨ideleCongrEquiv e Φ hunits, ?_, ?_⟩
  · refine le_antisymm ?_ ?_
    · intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      rw [Idele.mem_principalSubgroup] at hz ⊢
      obtain ⟨k, rfl⟩ := hz
      exact ⟨Units.map e.toMonoidHom k, (ideleCongrEquiv_principalIdele hmap k).symm⟩
    · intro y hy
      rw [Idele.mem_principalSubgroup] at hy
      obtain ⟨k, rfl⟩ := hy
      refine Subgroup.mem_map.mpr ⟨Idele.principalIdele L (Units.map e.symm.toMonoidHom k), ?_, ?_⟩
      · exact Idele.mem_principalSubgroup.mpr ⟨_, rfl⟩
      · show ideleCongrEquiv e Φ hunits
            (Idele.principalIdele L (Units.map e.symm.toMonoidHom k)) = Idele.principalIdele L' k
        rw [ideleCongrEquiv_principalIdele hmap]
        congr 1
        ext
        simp
  · intro σ x
    exact ideleCongrEquiv_smul hmap hcont σ x

end NK.CFTLib.RouteB.IdeleCongr
