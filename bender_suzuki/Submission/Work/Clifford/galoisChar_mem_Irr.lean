import Mathlib
import Submission.Work.Clifford.CFun
import Submission.Work.Clifford.cfInner_eq_ite_of_mem_Irr
import Submission.Work.Clifford.simple_of_finrank_hom_self_eq_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

open Classical

namespace Work.Clifford

section Twist

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [Module.Finite ℂ M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `σ`-twist of a linear endomorphism, transported to coordinates via a basis, then
made into a linear endomorphism of `ι → ℂ`. -/
noncomputable def twistFun (σ : ℂ ≃+* ℂ) (b : Module.Basis ι ℂ M) (f : M →ₗ[ℂ] M) :
    (ι → ℂ) →ₗ[ℂ] (ι → ℂ) :=
  Matrix.toLin' ((LinearMap.toMatrix b b f).map (σ : ℂ →+* ℂ))

theorem twistFun_one (σ : ℂ ≃+* ℂ) (b : Module.Basis ι ℂ M) : twistFun σ b 1 = 1 := by
  rw [twistFun, LinearMap.toMatrix_one,
    Matrix.map_one (σ : ℂ →+* ℂ) (map_zero σ) (map_one σ), Matrix.toLin'_one]
  rfl

theorem twistFun_mul (σ : ℂ ≃+* ℂ) (b : Module.Basis ι ℂ M) (f g : M →ₗ[ℂ] M) :
    twistFun σ b (f * g) = twistFun σ b f * twistFun σ b g := by
  rw [twistFun, twistFun, twistFun, LinearMap.toMatrix_mul, Matrix.map_mul,
    Matrix.toLin'_mul]
  rfl

/-- The `σ`-twist as a monoid homomorphism. -/
noncomputable def twistHom (σ : ℂ ≃+* ℂ) (b : Module.Basis ι ℂ M) :
    (M →ₗ[ℂ] M) →* ((ι → ℂ) →ₗ[ℂ] (ι → ℂ)) where
  toFun := twistFun σ b
  map_one' := twistFun_one σ b
  map_mul' := twistFun_mul σ b

@[simp] theorem twistHom_apply (σ : ℂ ≃+* ℂ) (b : Module.Basis ι ℂ M) (f : M →ₗ[ℂ] M) :
    twistHom σ b f = twistFun σ b f := rfl

end Twist

section Main

variable {G : Type*} [Group G] [Fintype G]

/-- Applying a ring automorphism `σ` of `ℂ` entrywise to a matrix representation gives a
representation whose character is `σ` applied to the original character. -/
theorem exists_fdRep_char_galois (σ : ℂ ≃+* ℂ) (W : FDRep ℂ G) :
    ∃ W' : FDRep ℂ G, W'.character = fun g => σ (W.character g) := by
  classical
  let b := Module.finBasis ℂ ↥W.V
  let ρ' : Representation ℂ G (Fin (Module.finrank ℂ ↥W.V) → ℂ) :=
    (twistHom σ b).comp W.ρ
  refine ⟨FDRep.of ρ', ?_⟩
  have hchar : ∀ g : G, (FDRep.of ρ').character g = σ (W.character g) := by
    intro g
    show LinearMap.trace ℂ (Fin (Module.finrank ℂ ↥W.V) → ℂ)
      (((FDRep.of ρ').ρ) g) = σ (W.character g)
    rw [FDRep.of_ρ']
    show LinearMap.trace ℂ (Fin (Module.finrank ℂ ↥W.V) → ℂ)
      (Matrix.toLin' ((LinearMap.toMatrix b b (W.ρ g)).map (σ : ℂ →+* ℂ)))
      = σ (W.character g)
    rw [Matrix.trace_toLin'_eq]
    have h1 : ((LinearMap.toMatrix b b (W.ρ g)).map (σ : ℂ →+* ℂ)).trace
        = (σ : ℂ →+* ℂ) ((LinearMap.toMatrix b b (W.ρ g)).trace) :=
      (AddMonoidHom.map_trace (σ : ℂ →+* ℂ) (LinearMap.toMatrix b b (W.ρ g))).symm
    rw [h1]
    have h2 : (LinearMap.toMatrix b b (W.ρ g)).trace = W.character g := by
      show _ = LinearMap.trace ℂ ↥W.V (W.ρ g)
      exact (LinearMap.trace_eq_matrix_trace ℂ b (W.ρ g)).symm
    rw [h2]
    exact congrFun (RingEquiv.coe_toRingHom σ) (W.character g)
  exact funext hchar

/-- **The `cfInner`-self pairing of the Galois twist of an irreducible character is `1`.** -/
theorem cfInner_galoisChar_self (σ : ℂ ≃+* ℂ) {χ : G → ℂ}
    (hχ : χ ∈ Work.Clifford.Irr G) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g : G, σ (χ g) * starRingEnd ℂ (σ (χ g)) = 1 := by
  classical
  obtain ⟨V, -, hVχ⟩ := (mem_Irr (G := G) (χ := χ)).mp hχ
  obtain ⟨W', hW'⟩ := exists_fdRep_char_galois σ V
  have hf : W'.character = fun g => σ (χ g) := by rw [hW', hVχ]
  have hstarχ : ∀ h : G, starRingEnd ℂ (χ h) = χ h⁻¹ := by
    intro h
    rw [← congrFun hVχ h, ← congrFun hVχ h⁻¹]
    exact star_char_eq_char_inv V h
  have hpoint : ∀ g : G, starRingEnd ℂ (σ (χ g)) = σ (starRingEnd ℂ (χ g)) := by
    intro g
    rw [hstarχ g, ← congrFun hf g, star_char_eq_char_inv W' g, congrFun hf g⁻¹]
  have hsum : (∑ g : G, σ (χ g) * starRingEnd ℂ (σ (χ g)))
      = σ (∑ g : G, χ g * starRingEnd ℂ (χ g)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun g _ => by rw [hpoint g, map_mul]
  rw [hsum]
  have hσc : σ ((Fintype.card G : ℂ)⁻¹) = (Fintype.card G : ℂ)⁻¹ := by
    rw [map_inv₀, map_natCast]
  rw [← hσc, ← map_mul]
  change σ (Work.Clifford.cfInner χ χ) = 1
  rw [cfInner_eq_ite_of_mem_Irr hχ hχ]
  simp

/-- **The endomorphism space of the Galois twist of an irreducible character is
one-dimensional.** -/
theorem finrank_hom_self_galoisChar (σ : ℂ ≃+* ℂ) {χ : G → ℂ}
    (hχ : χ ∈ Work.Clifford.Irr G) :
    ∃ W' : FDRep ℂ G, W'.character = (fun g => σ (χ g)) ∧
      Module.finrank ℂ (W' ⟶ W') = 1 := by
  classical
  obtain ⟨V, -, hVχ⟩ := (mem_Irr (G := G) (χ := χ)).mp hχ
  obtain ⟨W', hW'⟩ := exists_fdRep_char_galois σ V
  have hf : W'.character = fun g => σ (χ g) := by rw [hW', hVχ]
  refine ⟨W', hf, ?_⟩
  have hstarχ : ∀ h : G, starRingEnd ℂ (χ h) = χ h⁻¹ := by
    intro h
    rw [← congrFun hVχ h, ← congrFun hVχ h⁻¹]
    exact star_char_eq_char_inv V h
  have hpoint : ∀ g : G, starRingEnd ℂ (σ (χ g)) = σ (starRingEnd ℂ (χ g)) := by
    intro g
    rw [hstarχ g, ← congrFun hf g, star_char_eq_char_inv W' g, congrFun hf g⁻¹]
  have h1 := FDRep.scalar_product_char_eq_finrank_equivariant W' W'
  have h2 : ((Module.finrank ℂ (W' ⟶ W') : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
    rw [← h1, Nat.card_eq_fintype_card]
    have hsum : (∑ g : G, W'.character g * W'.character g⁻¹)
        = ∑ g : G, σ (χ g) * starRingEnd ℂ (σ (χ g)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [congrFun hf x⁻¹, hpoint x, congrFun hf x, hstarχ x]
    rw [hsum, cfInner_galoisChar_self σ hχ]
    norm_num
  exact Nat.cast_injective h2

/-- A reformulation of `cfInner_galoisChar_self` as the `cfInner` of the twisted function. -/
theorem cfInner_twist_self (σ : ℂ ≃+* ℂ) {χ : G → ℂ} (hχ : χ ∈ Work.Clifford.Irr G) :
    Work.Clifford.cfInner (fun g => σ (χ g)) (fun g => σ (χ g)) = 1 :=
  cfInner_galoisChar_self σ hχ

theorem galoisChar_mem_Irr {G : Type*} [Group G] [Fintype G] (σ : ℂ ≃+* ℂ) {χ : G → ℂ}
    (hχ : χ ∈ Work.Clifford.Irr G) :
    (fun g : G => σ (χ g)) ∈ Work.Clifford.Irr G := by
  obtain ⟨W', hf, hfin⟩ := finrank_hom_self_galoisChar σ hχ
  exact ⟨W', simple_of_finrank_hom_self_eq_one W' hfin, hf⟩

end Main

end Work.Clifford
