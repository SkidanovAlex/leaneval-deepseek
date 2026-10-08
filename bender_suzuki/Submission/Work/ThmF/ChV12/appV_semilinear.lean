import Mathlib
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

/-- The additive equivalence `E ≃+ E` given by the action of `u : U`
(the inverse being the action of `u⁻¹`). -/
private def smulAddEquiv {U E : Type*} [Group U] [AddCommGroup E] [DistribMulAction U E]
    (u : U) : E ≃+ E where
  toFun := fun x => u • x
  invFun := fun x => u⁻¹ • x
  left_inv := fun x => by
    change u⁻¹ • (u • x) = x
    rw [← mul_smul, inv_mul_cancel, one_smul]
  right_inv := fun x => by
    change u • (u⁻¹ • x) = x
    rw [← mul_smul, mul_inv_cancel, one_smul]
  map_add' := fun x y => smul_add u x y

open Classical in theorem appV_semilinear {E K U : Type} [AddCommGroup E] [Fintype E] [CommGroup K] [Fintype K] [Group U] [DistribMulAction K E] [DistribMulAction U E] [MulDistribMulAction U K] (hcompat : ∀ (u : U) (k : K) (x : E), u • (k • x) = (u • k) • (u • x)) (F : Type) [Field F] (e : E ≃+ F) (κ : K ≃* Fˣ) (s : E) (hes : e s = 1) (hκ : ∀ (k : K) (x : E), e (k • x) = (κ k : F) * e x) (hUs : ∀ u : U, u • s = s) : ∃ ρ : U →* (F ≃+* F), (∀ (u : U) (x : E), e (u • x) = ρ u (e x)) ∧ ∀ (u : U) (k : K), (κ (u • k) : F) = ρ u (κ k) := by
  -- The additive automorphism of `F` induced by `u`: `y ↦ e (u • e.symm y)`.
  let φ : U → (F ≃+ F) := fun u => e.symm.trans ((smulAddEquiv u).trans e)
  have φ_apply : ∀ (u : U) (y : F), φ u y = e (u • e.symm y) := by
    intro u y
    simp [φ, smulAddEquiv, AddEquiv.trans_apply]
  -- `e` sends the `K`-orbit of `s` to the units of `F`.
  have e_smul_s : ∀ k : K, e (k • s) = (κ k : F) := by
    intro k
    rw [hκ k s, hes, mul_one]
  have symm_kappa : ∀ k : K, e.symm (κ k : F) = k • s := by
    intro k
    rw [← e_smul_s k]
    exact e.symm_apply_apply (k • s)
  -- The induced automorphism is compatible with the `K`-action.
  have φ_kappa : ∀ (u : U) (k : K), φ u (κ k) = (κ (u • k) : F) := by
    intro u k
    rw [φ_apply, symm_kappa k, hcompat u k s, hUs u, e_smul_s (u • k)]
  -- Multiplicativity on the units of `F`.
  have mul_units : ∀ (u : U) (a b : Fˣ),
      φ u ((a : F) * (b : F)) = φ u (a : F) * φ u (b : F) := by
    intro u a b
    obtain ⟨ka, rfl⟩ := κ.surjective a
    obtain ⟨kb, rfl⟩ := κ.surjective b
    have h1 : ((κ ka : Fˣ) : F) * ((κ kb : Fˣ) : F) = ((κ (ka * kb) : Fˣ) : F) := by
      rw [← Units.val_mul, map_mul]
    rw [h1, φ_kappa u (ka * kb), φ_kappa u ka, φ_kappa u kb, smul_mul',
      map_mul, Units.val_mul]
  -- Multiplicativity everywhere.
  have φ_mul : ∀ (u : U) (a b : F), φ u (a * b) = φ u a * φ u b := by
    intro u a b
    by_cases ha : a = 0
    · subst ha
      simp
    · by_cases hb : b = 0
      · subst hb
        simp
      · have := mul_units u (Units.mk0 a ha) (Units.mk0 b hb)
        simpa using this
  -- Package into a ring equivalence.
  let ρfun : U → (F ≃+* F) := fun u => { φ u with map_mul' := φ_mul u }
  have ρ_one : ρfun 1 = 1 := by
    ext x
    simp [ρfun, φ_apply]
  have ρ_mul : ∀ u v : U, ρfun (u * v) = ρfun u * ρfun v := by
    intro u v
    ext x
    simp [ρfun, φ_apply, mul_smul]
  let ρ : U →* (F ≃+* F) := { toFun := ρfun, map_one' := ρ_one, map_mul' := ρ_mul }
  refine ⟨ρ, ?_, ?_⟩
  · intro u x
    change e (u • x) = ρfun u (e x)
    simp [ρfun, φ_apply]
  · intro u k
    change (κ (u • k) : F) = ρfun u (κ k)
    simp [ρfun, φ_kappa]

end Work.ThmF.ChV12
