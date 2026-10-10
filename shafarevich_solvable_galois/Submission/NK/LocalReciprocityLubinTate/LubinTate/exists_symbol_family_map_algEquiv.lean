import Mathlib.FieldTheory.IntermediateField.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transporting a compatible family of symbols along an algebra equivalence

Let `e : Ω ≃ₐ[F] Ω'` be an isomorphism of `F`-extensions, let
`L : ℕ → IntermediateField F Ω` be an increasing tower of intermediate fields, and let
`Φ n : Fˣ →* (↥(L n) ≃ₐ[F] ↥(L n))` be a compatible family of "symbol" homomorphisms
(compatibility being with respect to the inclusions `L n ⊆ L n'` for `n ≤ n'`).

This file shows that the family can be transported along `e` to the images
`L' n = (L n).map e.toAlgHom`, by conjugating each `Φ n x` with the induced algebra
equivalence `↥(L n) ≃ₐ[F] ↥(L' n)`. The transported family has the same surjectivity
behaviour and the same kernels, and remains compatible with the inclusions `L' n ⊆ L' n'`.

The main result is `exists_symbol_family_map_algEquiv`.
-/

namespace NK.LocalReciprocityLubinTate.LubinTate

variable {F : Type*} [Field F]

/-- Conjugation by an `F`-algebra equivalence, as a monoid isomorphism between the
automorphism groups of the two fields.  In the *same* type it is the inner automorphism
`φ ↦ E ∘ φ ∘ E⁻¹`; here it is used to move automorphisms of `↥L` to automorphisms of the
isomorphic field `↥L'`. -/
noncomputable def conjAutMulEquiv {A B : Type*} [Field A] [Field B] [Algebra F A]
    [Algebra F B] (E : A ≃ₐ[F] B) : (A ≃ₐ[F] A) ≃* (B ≃ₐ[F] B) where
  toFun φ := E.symm.trans (φ.trans E)
  invFun ψ := E.trans (ψ.trans E.symm)
  left_inv φ := by ext x; simp [AlgEquiv.trans_apply]
  right_inv ψ := by ext x; simp [AlgEquiv.trans_apply]
  map_mul' φ ψ := by ext x; simp [AlgEquiv.trans_apply, AlgEquiv.mul_apply]

@[simp]
lemma conjAutMulEquiv_apply {A B : Type*} [Field A] [Field B] [Algebra F A] [Algebra F B]
    (E : A ≃ₐ[F] B) (φ : A ≃ₐ[F] A) (x : B) :
    conjAutMulEquiv E φ x = E (φ (E.symm x)) := rfl

variable {Ω Ω' : Type*} [Field Ω] [Field Ω'] [Algebra F Ω] [Algebra F Ω']

/-- The `F`-algebra equivalence between an intermediate field `L` of `Ω/F` and its image in
`Ω'` under an algebra equivalence `e : Ω ≃ₐ[F] Ω'`.  It is the restriction of `e`. -/
noncomputable def intermediateFieldMapAlgEquiv (e : Ω ≃ₐ[F] Ω')
    (L : IntermediateField F Ω) :
    ↥L ≃ₐ[F] ↥(IntermediateField.map e.toAlgHom L) :=
  IntermediateField.intermediateFieldMap e L

@[simp]
lemma intermediateFieldMapAlgEquiv_apply_coe (e : Ω ≃ₐ[F] Ω') (L : IntermediateField F Ω)
    (x : ↥L) : ↑(intermediateFieldMapAlgEquiv e L x) = e ↑x := rfl

@[simp]
lemma intermediateFieldMapAlgEquiv_symm_apply_coe (e : Ω ≃ₐ[F] Ω')
    (L : IntermediateField F Ω) (y : ↥(IntermediateField.map e.toAlgHom L)) :
    ↑((intermediateFieldMapAlgEquiv e L).symm y) = e.symm ↑y := rfl

/-- **Transport a compatible family of symbols along an algebra equivalence `e : Ω ≃ₐ[F] Ω'`.**

Conjugating each `Φ n x` by the induced algebra equivalence `↥(L n) ≃ₐ[F] ↥(L' n)`, where
`L' n = (L n).map e.toAlgHom`, produces a compatible family on the image tower, with the same
surjectivity behaviour and the same kernels. -/
theorem exists_symbol_family_map_algEquiv {F Ω Ω' : Type*} [Field F] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F Ω'] (e : Ω ≃ₐ[F] Ω')
    (L : ℕ → IntermediateField F Ω) (hmono : ∀ {n n' : ℕ}, n ≤ n' → L n ≤ L n')
    (Φ : ∀ n : ℕ, Fˣ →* (↥(L n) ≃ₐ[F] ↥(L n)))
    (hcomp : ∀ (n n' : ℕ) (h : n ≤ n') (x : Fˣ) (y : ↥(L n)),
        ((Φ n' x) ⟨y.1, hmono h y.2⟩ : ↥(L n')) =
          ⟨((Φ n x) y).1, hmono h ((Φ n x) y).2⟩) :
    ∃ Φ' : ∀ n : ℕ,
        Fˣ →* (↥(IntermediateField.map e.toAlgHom (L n)) ≃ₐ[F]
                ↥(IntermediateField.map e.toAlgHom (L n))),
      (∀ n, Function.Surjective (Φ n) ↔ Function.Surjective (Φ' n)) ∧
      (∀ n, MonoidHom.ker (Φ n) = MonoidHom.ker (Φ' n)) ∧
      (∀ (n n' : ℕ) (h : n ≤ n') (x : Fˣ) (y : ↥(IntermediateField.map e.toAlgHom (L n))),
        ((Φ' n' x) ⟨y.1, IntermediateField.map_mono e.toAlgHom (hmono h) y.2⟩ :
            ↥(IntermediateField.map e.toAlgHom (L n'))) =
          ⟨((Φ' n x) y).1,
            IntermediateField.map_mono e.toAlgHom (hmono h) ((Φ' n x) y).2⟩) := by
  -- The transported family: conjugate `Φ n x` by the restriction of `e`.
  let Φ' : ∀ n : ℕ,
        Fˣ →* (↥(IntermediateField.map e.toAlgHom (L n)) ≃ₐ[F]
                ↥(IntermediateField.map e.toAlgHom (L n))) :=
    fun n => (conjAutMulEquiv (intermediateFieldMapAlgEquiv e (L n))).toMonoidHom.comp (Φ n)
  -- Naturality of the inverse of the restriction of `e` with respect to the inclusions.
  have hnat_symm : ∀ {n n' : ℕ} (h : n ≤ n')
      (y : ↥(IntermediateField.map e.toAlgHom (L n))),
      (intermediateFieldMapAlgEquiv e (L n')).symm
          ⟨y.1, IntermediateField.map_mono e.toAlgHom (hmono h) y.2⟩ =
        ⟨((intermediateFieldMapAlgEquiv e (L n)).symm y).1,
          hmono h ((intermediateFieldMapAlgEquiv e (L n)).symm y).2⟩ := by
    intro n n' h y
    apply Subtype.ext
    simp
  refine ⟨Φ', ?_, ?_, ?_⟩
  · -- Surjectivity is preserved because conjugation is a bijection.
    intro n
    constructor
    · intro hφ ψ
      obtain ⟨φ, rfl⟩ := (conjAutMulEquiv (intermediateFieldMapAlgEquiv e (L n))).surjective ψ
      obtain ⟨x, hx⟩ := hφ φ
      exact ⟨x, by
        show conjAutMulEquiv (intermediateFieldMapAlgEquiv e (L n)) (Φ n x)
            = conjAutMulEquiv (intermediateFieldMapAlgEquiv e (L n)) φ
        rw [hx]⟩
    · intro hψ
      show Function.Surjective (Φ n)
      intro φ
      obtain ⟨x, hx⟩ := hψ (conjAutMulEquiv (intermediateFieldMapAlgEquiv e (L n)) φ)
      exact ⟨x, (conjAutMulEquiv (intermediateFieldMapAlgEquiv e (L n))).injective hx⟩
  · -- The kernel is unchanged because conjugation is injective and preserves `1`.
    intro n
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hx
      show conjAutMulEquiv (intermediateFieldMapAlgEquiv e (L n)) (Φ n x) = 1
      rw [hx, map_one]
    · intro hx
      have hx' : conjAutMulEquiv (intermediateFieldMapAlgEquiv e (L n)) (Φ n x) = 1 := hx
      exact (conjAutMulEquiv (intermediateFieldMapAlgEquiv e (L n))).injective
        (by rw [hx', map_one])
  · -- Compatibility is transported along with the family.
    intro n n' h x y
    change ((conjAutMulEquiv (intermediateFieldMapAlgEquiv e (L n')) (Φ n' x))
        ⟨y.1, IntermediateField.map_mono e.toAlgHom (hmono h) y.2⟩ :
        ↥(IntermediateField.map e.toAlgHom (L n'))) =
      ⟨((conjAutMulEquiv (intermediateFieldMapAlgEquiv e (L n)) (Φ n x)) y).1,
        IntermediateField.map_mono e.toAlgHom (hmono h)
          ((conjAutMulEquiv (intermediateFieldMapAlgEquiv e (L n)) (Φ n x)) y).2⟩
    apply Subtype.ext
    simp only [conjAutMulEquiv_apply, intermediateFieldMapAlgEquiv_apply_coe]
    rw [hnat_symm h y, hcomp n n' h x ((intermediateFieldMapAlgEquiv e (L n)).symm y)]

end NK.LocalReciprocityLubinTate.LubinTate
