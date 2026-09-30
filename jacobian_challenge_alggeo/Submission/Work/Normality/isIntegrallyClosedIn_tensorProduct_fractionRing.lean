import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Normality

open TensorProduct

/-- The `A`-algebra structure on `A ⊗[P] P` computed on a pure tensor: multiplying the image of
`a` with the image of `algebraMap P A p` is the same as pushing `p` to the other factor. -/
lemma algebraMap_mul_algebraMap_tensorProduct_fractionRing {P A : Type*} [CommRing P] [CommRing A]
    [Algebra P A] (a : A) (p : P) :
    algebraMap A (TensorProduct P A (FractionRing P)) (a * algebraMap P A p)
      = a ⊗ₜ[P] algebraMap P (FractionRing P) p := by
  rw [map_mul, ← IsScalarTower.algebraMap_apply P A (TensorProduct P A (FractionRing P)),
      Algebra.TensorProduct.algebraMap_apply (S := A),
      Algebra.TensorProduct.algebraMap_apply (S := P),
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.algebraMap_self, RingHom.id_apply, one_mul,
      mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]

/-- Let `P` be an integrally closed domain and `A` a smooth `P`-algebra.  Then `A` is
integrally closed in its base change to the fraction field of `P`.

Proof sketch: use Mathlib's `TensorProduct.toIntegralClosure_bijective_of_smooth` with
`R := P`, `S := A`, `B := FractionRing P`; the source of `TensorProduct.toIntegralClosure`
is `A ⊗[P] integralClosure P (FractionRing P)`, which is `A ⊗[P] ⊥ ≃ A` since `P` is
integrally closed (`IsIntegrallyClosed.integralClosure_eq_bot`, `Algebra.botEquivOfInjective`),
and bijectivity of the map then says exactly that the range of `A → A ⊗[P] FractionRing P`
is the integral closure of `A` in `A ⊗[P] FractionRing P`, i.e. `IsIntegrallyClosedIn A _`.
Equivalently: `integralClosure A (A ⊗[P] FractionRing P) = ⊤`.) -/
theorem isIntegrallyClosedIn_tensorProduct_fractionRing {P : Type*} [CommRing P]
    [IsDomain P] [IsIntegrallyClosed P] {A : Type*} [CommRing A] [Algebra P A]
    [Algebra.Smooth P A] : IsIntegrallyClosedIn A (TensorProduct P A (FractionRing P)) := by
  classical
  -- `P` is integrally closed in its fraction ring.
  have hic_bot : integralClosure P (FractionRing P) = ⊥ :=
    IsIntegrallyClosed.integralClosure_eq_bot P (FractionRing P)
  -- The comparison map of `TensorProduct.toIntegralClosure` is bijective.
  have hbij := TensorProduct.toIntegralClosure_bijective_of_smooth (R := P) (S := A)
    (B := FractionRing P)
  -- `ψ` is the map `A ⊗[P] integralClosure P (FractionRing P) → A ⊗[P] FractionRing P`
  -- underlying `TensorProduct.toIntegralClosure`.
  let ψ : (A ⊗[P] integralClosure P (FractionRing P)) →ₐ[A] (TensorProduct P A (FractionRing P)) :=
    Algebra.TensorProduct.lTensor A (Subalgebra.val (integralClosure P (FractionRing P)))
  have hψ_apply : ∀ w, (TensorProduct.toIntegralClosure P A (FractionRing P) w).val = ψ w := by
    intro w
    have h : (Subalgebra.val (integralClosure A (TensorProduct P A (FractionRing P)))).comp
        (TensorProduct.toIntegralClosure P A (FractionRing P)) = ψ := by
      rw [TensorProduct.toIntegralClosure, AlgHom.val_comp_codRestrict]
    exact DFunLike.congr_fun h w
  -- Every element in the range of `ψ` lies in the range of `algebraMap A _`.
  have key : ∀ w : A ⊗[P] integralClosure P (FractionRing P),
      ψ w ∈ Set.range (algebraMap A (TensorProduct P A (FractionRing P))) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul a b =>
        obtain ⟨p, hp⟩ := Algebra.mem_bot.mp
          (show (b : FractionRing P) ∈ (⊥ : Subalgebra P (FractionRing P)) from hic_bot ▸ b.2)
        refine ⟨a * algebraMap P A p, ?_⟩
        have hψ : ψ (a ⊗ₜ[P] b) = a ⊗ₜ[P] algebraMap P (FractionRing P) p := by
          simp only [ψ, Algebra.TensorProduct.lTensor, Algebra.TensorProduct.map_tmul,
            AlgHom.id_apply, Subalgebra.coe_val]
          rw [← hp]
        rw [hψ, ← algebraMap_mul_algebraMap_tensorProduct_fractionRing a p]
    | add x y hx hy =>
        obtain ⟨y₁, hy₁⟩ := hx
        obtain ⟨y₂, hy₂⟩ := hy
        exact ⟨y₁ + y₂, by simp only [map_add, hy₁, hy₂]⟩
  refine isIntegrallyClosedIn_iff.mpr ⟨?_, ?_⟩
  · -- `A → A ⊗[P] FractionRing P` is injective (here: `includeLeft`, using flatness of `A`).
    intro x y hxy
    have h := Algebra.TensorProduct.includeLeft_injective (R := P) (S := A)
      (A := A) (B := FractionRing P) (IsFractionRing.injective P (FractionRing P))
    apply h
    simpa [Algebra.TensorProduct.algebraMap_apply] using hxy
  · -- every `A`-integral element of `A ⊗[P] FractionRing P` comes from `A`.
    rintro x hx
    obtain ⟨w, hw⟩ := hbij.2 ⟨x, hx⟩
    obtain ⟨y, hy⟩ := key w
    have hxw : x = ψ w := by
      have h2 := hψ_apply w
      rw [hw] at h2
      exact h2
    exact ⟨y, hy.trans hxw.symm⟩

end Work.Normality
