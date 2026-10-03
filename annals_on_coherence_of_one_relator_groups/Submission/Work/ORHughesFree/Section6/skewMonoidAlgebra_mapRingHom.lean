import Mathlib

namespace Work.ORHughesFree.Section6

/-- Given a ring homomorphism `g : A →+* B` between rings equipped with a `ℤ`-action
(`Multiplicative ℤ`-action) that commutes with `g`, there is a ring homomorphism
`SkewMonoidAlgebra A (Multiplicative ℤ) →+* SkewMonoidAlgebra B (Multiplicative ℤ)`
acting coefficientwise, i.e. sending `single k a` to `single k (g a)`; moreover it is
injective whenever `g` is.

The homomorphism is built as `liftNCRingHom` applied to `single 1 ∘ g` and the
embedding `of B (Multiplicative ℤ)`. -/
theorem skewMonoidAlgebra_mapRingHom {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    {B : Type} [Ring B] [MulSemiringAction (Multiplicative ℤ) B]
    (g : A →+* B) (hg : ∀ (k : ℤ) (x : A),
      g ((Multiplicative.ofAdd k) • x) = (Multiplicative.ofAdd k) • g x) :
    ∃ G : SkewMonoidAlgebra A (Multiplicative ℤ) →+* SkewMonoidAlgebra B (Multiplicative ℤ),
      (∀ (k : Multiplicative ℤ) (a : A),
        G (SkewMonoidAlgebra.single k a) = SkewMonoidAlgebra.single k (g a)) ∧
      (Function.Injective g → Function.Injective G) := by
  classical
  -- `single 1 ∘ g : A →+* SkewMonoidAlgebra B (Multiplicative ℤ)`
  set f : A →+* SkewMonoidAlgebra B (Multiplicative ℤ) :=
    (SkewMonoidAlgebra.singleOneRingHom (G := Multiplicative ℤ)).comp g with hf
  -- the embedding of the group into its skew monoid algebra
  set φ : Multiplicative ℤ →* SkewMonoidAlgebra B (Multiplicative ℤ) :=
    SkewMonoidAlgebra.of B (Multiplicative ℤ) with hφ
  have hf_apply : ∀ a : A, f a = SkewMonoidAlgebra.single (1 : Multiplicative ℤ) (g a) := by
    intro a
    simp [hf, SkewMonoidAlgebra.singleOneRingHom, SkewMonoidAlgebra.singleAddHom]
  have hφ_apply : ∀ k : Multiplicative ℤ, φ k = SkewMonoidAlgebra.single k (1 : B) := by
    intro k
    simp [hφ, SkewMonoidAlgebra.of_apply]
  -- the compatibility condition making `liftNCRingHom` multiplicative
  have hcomm : ∀ {x : A} {y : Multiplicative ℤ}, f (y • x) * φ y = φ y * f x := by
    intro x y
    simp only [hf_apply, hφ_apply]
    rw [SkewMonoidAlgebra.single_mul_single, SkewMonoidAlgebra.single_mul_single]
    simp only [one_mul, mul_one, one_smul]
    have : g (y • x) = y • g x := by
      rw [← ofAdd_toAdd y]
      exact hg (Multiplicative.toAdd y) x
    rw [this]
  set G : SkewMonoidAlgebra A (Multiplicative ℤ) →+* SkewMonoidAlgebra B (Multiplicative ℤ) :=
    SkewMonoidAlgebra.liftNCRingHom f φ hcomm with hG
  have hG_single : ∀ (k : Multiplicative ℤ) (a : A),
      G (SkewMonoidAlgebra.single k a) = SkewMonoidAlgebra.single k (g a) := by
    intro k a
    rw [hG]
    change (SkewMonoidAlgebra.liftNC (f : A →+ SkewMonoidAlgebra B (Multiplicative ℤ)) φ)
      (SkewMonoidAlgebra.single k a) = SkewMonoidAlgebra.single k (g a)
    rw [SkewMonoidAlgebra.liftNC_single]
    change f a * φ k = SkewMonoidAlgebra.single k (g a)
    rw [hf_apply, hφ_apply, SkewMonoidAlgebra.single_mul_single]
    simp
  -- `G` acts coefficientwise, applying `g` to the coefficients
  have hG_coeff : ∀ (F : SkewMonoidAlgebra A (Multiplicative ℤ)) (k : Multiplicative ℤ),
      (G F).coeff k = g (F.coeff k) := by
    intro F
    induction F using SkewMonoidAlgebra.induction_on with
    | zero => intro k; simp
    | single k' a =>
        intro k
        rw [hG_single]
        simp only [SkewMonoidAlgebra.coeff_single]
        by_cases h : k' = k
        · subst h; simp
        · simp [h]
    | add F₁ F₂ ih₁ ih₂ =>
        intro k
        simp only [map_add, SkewMonoidAlgebra.coeff_add, Finsupp.add_apply, ih₁ k, ih₂ k]
  refine ⟨G, hG_single, ?_⟩
  intro hg_inj F₁ F₂ hFG
  apply SkewMonoidAlgebra.ext
  intro k
  exact hg_inj (by
    have := congr_arg (fun u : SkewMonoidAlgebra B (Multiplicative ℤ) => u.coeff k) hFG
    simpa [hG_coeff] using this)

end Work.ORHughesFree.Section6
