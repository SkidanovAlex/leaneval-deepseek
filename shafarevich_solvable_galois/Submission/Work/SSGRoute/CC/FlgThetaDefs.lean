import Mathlib
import Submission.Work.SSGRoute.CC.MagFourDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Infrastructure for `flgThetaSpan_le`

Setting: `A = MonoidAlgebra (ZMod 2) (FreeMonoid X)`, `σ : X → X` an involution (`hσ`),
`sigA X σ` the induced algebra endomorphism of `A` (see `magFourDefs.lean`), `σA = sigAL X σ`
the same map as a `ZMod 2`-linear map.

This file collects the vocabulary and the elementary facts used by
`Work.SSGRoute.flgThetaSpan_le`:

* `flgSq x = x*x`, `flgGen p = x*x + [x,y]` (the generators of `Tsub X`);
* `flgBilin σ u v = u * σA v + σA v * u`, the bilinear form appearing in the polarisation
  identity for `φ`;
* `flgDeltaL σ = σA + id`;
* the involutivity of `sigA X σ`, the action of `sigA X σ` on squares and brackets;
* the two degree-`4` identities
  `flgSq_sq_identity : x²·z² + z²·x² = brk4(x,z,x,z)` and
  `flgSq_brk_identity : x²·[z,w] + [z,w]·x² = brk4(x,z,w,x) + brk4(x,w,z,x)`;
* the additivity of `flgBilin` in each variable and the polarisation identity
  `φ(u+v) = φ(u) + φ(v) + (σA + id)(flgBilin σ u v)`.
-/

namespace Work.SSGRoute.CC

noncomputable section

variable {X : Type}

/-! ## The involution `sigA X σ` and its action on squares and brackets -/

/-- `sigA X σ` on a monomial. -/
theorem sigmaA_single' (X : Type) (σ : X → X) (w : FreeMonoid X) (c : ZMod 2) :
    sigA X σ (MonoidAlgebra.single w c) = MonoidAlgebra.single (FreeMonoid.map σ w) c := by
  rw [sigA, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]

/-- `sigA X σ` is an involution when `σ` is one. -/
theorem sigA_sigA (X : Type) (σ : X → X) (hσ : ∀ x, σ (σ x) = x)
    (a : MonoidAlgebra (ZMod 2) (FreeMonoid X)) : sigA X σ (sigA X σ a) = a := by
  refine MonoidAlgebra.induction_on (motive := fun a => sigA X σ (sigA X σ a) = a) a ?_ ?_ ?_
  · intro m
    simp only [MonoidAlgebra.of_apply]
    rw [sigmaA_single' X σ m, sigmaA_single' X σ (FreeMonoid.map σ m)]
    rw [freeMonoid_map_comp (σ := σ) (τ := σ) m,
      show (σ ∘ σ) = id from funext hσ, FreeMonoid.map_id, MonoidHom.id_apply]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro r x hx
    have hr : r = 0 ∨ r = 1 := by revert r; decide
    rcases hr with rfl | rfl
    · simp
    · simpa using hx

/-- The square `x*x` of a letter in `A`. -/
noncomputable abbrev flgSq (X : Type) (x : X) : MonoidAlgebra (ZMod 2) (FreeMonoid X) :=
  flg_ltr X x * flg_ltr X x

/-- `sigA X σ` sends a square to the square of the image letter. -/
theorem sigA_flgSq_fact (X : Type) (σ : X → X) (x : X) :
    sigA X σ (flgSq X x) = flgSq X (σ x) := by
  rw [flgSq, flgSq, sigA_mul, sigA_ltr]

/-- `sigA X σ` sends a bracket of letters to the bracket of the image letters. -/
theorem sigA_brk_fact (X : Type) (σ : X → X) (x y : X) :
    sigA X σ (brk X (flg_ltr X x) (flg_ltr X y))
      = brk X (flg_ltr X (σ x)) (flg_ltr X (σ y)) := by
  simp only [brk, map_add, sigA_mul, sigA_ltr]

/-! ## The generators of `Tsub X`, and the bilinear form `flgBilin` -/

/-- The generator `x*x + [x,y]` of `Tsub X`. -/
noncomputable def flgGen (X : Type) (p : X × X) : MonoidAlgebra (ZMod 2) (FreeMonoid X) :=
  flg_ltr X p.1 * flg_ltr X p.1
    + (flg_ltr X p.2 * flg_ltr X p.1 + flg_ltr X p.1 * flg_ltr X p.2)

/-- `flgGen` is `x*x + [x,y]`. -/
theorem flgGen_eq (X : Type) (p : X × X) :
    flgGen X p = flgSq X p.1 + brk X (flg_ltr X p.1) (flg_ltr X p.2) := by
  simp only [flgGen, flgSq, brk]
  abel

/-- `Tsub X` is spanned by the elements `flgGen X p`. -/
theorem Tsub_eq_span_flgGen (X : Type) :
    Tsub X = Submodule.span (ZMod 2) (Set.range (flgGen X)) := rfl

/-- The generators of `Tsub X` lie in `Tsub X`. -/
theorem flgGen_mem_Tsub (X : Type) (p : X × X) : flgGen X p ∈ Tsub X :=
  Submodule.subset_span ⟨p, rfl⟩

/-- The squares of letters lie in `Tsub X`. -/
theorem flgSq_mem_Tsub (X : Type) (x : X) : flgSq X x ∈ Tsub X := by
  have h := flgGen_mem_Tsub X (x, x)
  rw [flgGen_eq X (x, x)] at h
  have h0 : brk X (flg_ltr X x) (flg_ltr X x) = 0 := by
    simp only [brk]
    exact flg_add_self _
  rw [h0, add_zero] at h
  exact h

/-- The bilinear form `(u,v) ↦ u * σA v + σA v * u`. -/
noncomputable def flgBilin (X : Type) (σ : X → X)
    (u v : MonoidAlgebra (ZMod 2) (FreeMonoid X)) : MonoidAlgebra (ZMod 2) (FreeMonoid X) :=
  u * sigA X σ v + sigA X σ v * u

/-- `σA + id`, as a linear map. -/
noncomputable abbrev flgDeltaL (X : Type) (σ : X → X) :
    MonoidAlgebra (ZMod 2) (FreeMonoid X) →ₗ[ZMod 2] MonoidAlgebra (ZMod 2) (FreeMonoid X) :=
  sigAL X σ + LinearMap.id

theorem flgDeltaW_eq_map (X : Type) (σ : X → X) :
    flgDeltaW X (sigAL X σ) = Submodule.map (flgDeltaL X σ) (Wsub X) := rfl

/-- `flgBilin` is additive in its first variable. -/
theorem flgBilin_add_left (X : Type) (σ : X → X)
    (u₁ u₂ v : MonoidAlgebra (ZMod 2) (FreeMonoid X)) :
    flgBilin X σ (u₁ + u₂) v = flgBilin X σ u₁ v + flgBilin X σ u₂ v := by
  simp only [flgBilin, mul_add, add_mul]
  abel

/-- `flgBilin` is additive in its second variable. -/
theorem flgBilin_add_right (X : Type) (σ : X → X)
    (u v₁ v₂ : MonoidAlgebra (ZMod 2) (FreeMonoid X)) :
    flgBilin X σ u (v₁ + v₂) = flgBilin X σ u v₁ + flgBilin X σ u v₂ := by
  simp only [flgBilin, map_add, mul_add, add_mul]
  abel

/-! ## The two degree-four identities -/

/-- `x²·z² + z²·x² = ⁅⁅⁅x,z⁆,x⁆,z⁆`. -/
theorem flgSq_sq_identity (X : Type) (x z : X) :
    flgSq X x * flgSq X z + flgSq X z * flgSq X x = brk4 X (x, z, x, z) := by
  simp only [flgSq, flg_ltr, brk4, brk, MonoidAlgebra.single_mul_single, mul_one, mul_add,
    add_mul, mul_assoc]
  abel_nf
  simp only [two_zsmul, flg_add_self, add_zero]

/-- `x²·⁅z,w⁆ + ⁅z,w⁆·x² = ⁅⁅⁅x,z⁆,w⁆,x⁆ + ⁅⁅⁅x,w⁆,z⁆,x⁆`. -/
theorem flgSq_brk_identity (X : Type) (x z w : X) :
    flgSq X x * brk X (flg_ltr X z) (flg_ltr X w)
      + brk X (flg_ltr X z) (flg_ltr X w) * flgSq X x
      = brk4 X (x, z, w, x) + brk4 X (x, w, z, x) := by
  simp only [flgSq, flg_ltr, brk4, brk, MonoidAlgebra.single_mul_single, mul_one, mul_add,
    add_mul, mul_assoc]
  abel_nf
  simp only [two_zsmul, flg_add_self, add_zero]

/-! ## The polarisation identity -/

/-- `flgDeltaL X σ` evaluated at `w` is `σA w + w`. -/
theorem flgDeltaL_apply (X : Type) (σ : X → X) (w : MonoidAlgebra (ZMod 2) (FreeMonoid X)) :
    flgDeltaL X σ w = sigA X σ w + w := rfl

/-- **Polarisation.**  `φ(u+v) = φ(u) + φ(v) + σA(⁅u,v⁆_σ) + ⁅u,v⁆_σ`, where
`⁅u,v⁆_σ = u·σA v + σA v·u`, i.e. `φ(u+v) = φ(u) + φ(v) + (σA + id)(u·σA v + σA v·u)`. -/
theorem phi_add_phi (X : Type) (σ : X → X) (hσ : ∀ x, σ (σ x) = x)
    (u v : MonoidAlgebra (ZMod 2) (FreeMonoid X)) :
    phi X σ (u + v)
      = phi X σ u + phi X σ v + (sigA X σ (flgBilin X σ u v) + flgBilin X σ u v) := by
  simp only [phi, flgBilin, map_add, sigA_mul, mul_add, add_mul]
  rw [sigA_sigA X σ hσ v]
  abel

end

end Work.SSGRoute.CC
