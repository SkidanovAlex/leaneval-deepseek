import Mathlib
import Submission.Work.SSGRoute.ExtChain.subsingleton_ext_fpRegular
import Submission.Work.SSGRoute.ExtChain.ext2_fn_two_helpers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The two-dimensional model of the regular `𝔽₂[H]`-module in coordinates

For a group `H` of order two with generator `σ ≠ 1`, the `𝔽₂`-vector space `𝔽₂[ε] = 𝔽₂[ε]/ε²` has
the basis `{1, σ}` on which `σ` acts by `1 ↦ σ`, `σ ↦ 1`.  In the "Jordan" coordinates `(x, z)`
in which `σ` acts by `(x, z) ↦ (x, x + z)` (the free `𝔽₂[σ]`-module on one generator), the change
of basis is

    `(x, z) ↦ (x + z)·1 + z·σ ∈ 𝔽₂[H]`,

which is the content of `shiftCoordinateEquiv` below, together with its equivariance.
-/

namespace Work.SSGRoute.ExtChain

open CategoryTheory

noncomputable section

variable {H : Type} [Group H]

/-- **The regular `𝔽₂[H]`-module in Jordan coordinates.**  For a group `H` of order two generated
by an involution `σ`, the `b`-fold product of the two-dimensional `𝔽₂`-space `(x, z) ↦ (x, x+z)`
is linearly equivalent to the free `𝔽₂[H]`-module of rank `b`, by the change of basis
`(x, z) ↦ (x + z)·1 + z·σ`, and the isomorphism is `σ`-equivariant. -/
theorem shiftCoordinateEquiv (σ : H) (hσne : σ ≠ 1) (hσ : σ * σ = 1)
    (hgen : ∀ g : H, g = 1 ∨ g = σ) (b : ℕ) :
    ∃ (Ψ : ((Fin b → ZMod 2) × (Fin b → ZMod 2)) ≃ₗ[ZMod 2]
        (Fin b → MonoidAlgebra (ZMod 2) H)),
      (∀ (x z : Fin b → ZMod 2) (j : Fin b),
        Ψ (x, z) j = MonoidAlgebra.single 1 (x j + z j) + MonoidAlgebra.single σ (z j)) ∧
      (∀ (x z : Fin b → ZMod 2), σ • (Ψ (x, z)) = Ψ (x, x + z)) := by
  classical
  have h2 : ∀ y : ZMod 2, y + y = 0 := fun y => by
    have h : (2 : ZMod 2) * y = 0 := by
      rw [show (2 : ZMod 2) = 0 from by decide, zero_mul]
    simpa [two_mul] using h
  have hadd : ∀ a b : ZMod 2, a + b + b = a := fun a b => by rw [add_assoc, h2, add_zero]
  have hdecomp : ∀ m : MonoidAlgebra (ZMod 2) H,
      m = MonoidAlgebra.single 1 (m.coeff 1) + MonoidAlgebra.single σ (m.coeff σ) := by
    intro m
    ext h
    rcases hgen h with rfl | rfl
    · simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single, Finsupp.add_apply,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne hσne.symm, add_zero]
    · simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single, Finsupp.add_apply,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne hσne, zero_add]
  -- the forward map
  let F : ((Fin b → ZMod 2) × (Fin b → ZMod 2)) →ₗ[ZMod 2]
      (Fin b → MonoidAlgebra (ZMod 2) H) :=
    { toFun := fun p => fun j =>
        MonoidAlgebra.single 1 (p.1 j + p.2 j) + MonoidAlgebra.single σ (p.2 j)
      map_add' := fun p q => by
        funext j
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, MonoidAlgebra.single_add]
        abel
      map_smul' := fun c p => by
        funext j
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_add,
          MonoidAlgebra.smul_single, RingHom.id_apply] }
  -- the backward map
  let G : (Fin b → MonoidAlgebra (ZMod 2) H) →ₗ[ZMod 2]
      ((Fin b → ZMod 2) × (Fin b → ZMod 2)) :=
    { toFun := fun f => ((fun j => (f j).coeff 1 + (f j).coeff σ), fun j => (f j).coeff σ)
      map_add' := fun f g => by
        refine Prod.ext ?_ ?_ <;> funext j <;>
          simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, MonoidAlgebra.coeff_add,
            Finsupp.add_apply] <;> abel
      map_smul' := fun c f => by
        refine Prod.ext ?_ ?_ <;> funext j <;>
          simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, MonoidAlgebra.coeff_smul,
            Finsupp.smul_apply, RingHom.id_apply, smul_add] }
  have hGF : ∀ p : (Fin b → ZMod 2) × (Fin b → ZMod 2), G (F p) = p := by
    intro p
    obtain ⟨x, z⟩ := p
    refine Prod.ext ?_ ?_
    · funext j
      show (MonoidAlgebra.single 1 (x j + z j) + MonoidAlgebra.single σ (z j)).coeff 1
          + (MonoidAlgebra.single 1 (x j + z j) + MonoidAlgebra.single σ (z j)).coeff σ = x j
      simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single, Finsupp.add_apply,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne hσne, Finsupp.single_eq_of_ne hσne.symm,
        add_zero, zero_add, hadd]
    · funext j
      show (MonoidAlgebra.single 1 (x j + z j) + MonoidAlgebra.single σ (z j)).coeff σ = z j
      simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single, Finsupp.add_apply,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne hσne, add_zero, zero_add]
  have hFG : ∀ f : Fin b → MonoidAlgebra (ZMod 2) H, F (G f) = f := by
    intro f
    funext j
    show MonoidAlgebra.single 1 ((f j).coeff 1 + (f j).coeff σ + (f j).coeff σ)
        + MonoidAlgebra.single σ ((f j).coeff σ) = f j
    rw [hadd ((f j).coeff 1) ((f j).coeff σ), ← hdecomp (f j)]
  have hbij : Function.Bijective F :=
    ⟨fun x y hxy => by rw [← hGF x, hxy, hGF y],
     fun y => ⟨G y, hFG y⟩⟩
  refine ⟨LinearEquiv.ofBijective F hbij, ?_, ?_⟩
  · intro x z j
    rfl
  · intro x z
    funext j
    show σ • (MonoidAlgebra.single 1 (x j + z j) + MonoidAlgebra.single σ (z j))
        = MonoidAlgebra.single 1 (x j + (x j + z j)) + MonoidAlgebra.single σ (x j + z j)
    rw [Work.CohomologicalShrinking.smul_monoidAlgebra, mul_add, MonoidAlgebra.single_mul_single,
      MonoidAlgebra.single_mul_single, mul_one, one_mul, hσ, one_mul]
    rw [show x j + (x j + z j) = z j from by rw [← add_assoc, h2, zero_add], add_comm]

end

end Work.SSGRoute.ExtChain
