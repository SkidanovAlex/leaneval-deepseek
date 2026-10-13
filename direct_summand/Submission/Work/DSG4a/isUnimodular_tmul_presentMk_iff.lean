import Mathlib
import Submission.Work.DSG4a.Present
import Submission.Work.DSG4a.mem_splitIdeal_presentMk

/-!
# DSG4a: unimodularity of the base change of a presented class

For a finite presentation `A^m ⧸ im D` (ref. `Submission.Work.DSG4a.Present`) and its class
`presentMk D e`, base change along an `A`-algebra `A'` gives the class `presentMk D' e'` of the
entrywise-extended data, and unimodularity is preserved and reflected.  This is the algebraic
statement that the canonical identification `A' ⊗[A] present D ≃ present D'` carries the class of
`e` to the class of `e'`.

The proof avoids constructing that isomorphism explicitly: both sides are shown to be equivalent to
the same elementary condition on a "dual vector" `w : Fin m → A'`:

* `isUnimodular_tmul_iff` (abstract): `IsUnimodular A' (1 ⊗ e) ↔ ∃ τ : M →ₗ[A] A', τ e = 1`;
* `exists_linearMap_presentMk_iff`: such a `τ` on `present D` is the same as a vector `w` with
  `transMap D w = 0` and `⟪w, e⟫ = 1`;
* `Module.IsUnimodular A' (presentMk D' e')` is the same condition by
  `mem_splitIdeal_presentMk` over `A'`.
-/

namespace Work.DSG4a

open TensorProduct

universe u

section Abstract

variable {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']
variable {M : Type u} [AddCommGroup M] [Module A M]

/-- **Base change of a unimodular element, functional form.**
For an `A`-algebra `A'` and an `A`-module `M`, the element `1 ⊗ e` of `A' ⊗[A] M` is unimodular
over `A'` iff there is an `A`-linear functional on `M` with values in `A'` taking the value `1`
at `e`.

No finiteness or flatness is needed: an `A'`-linear functional `σ` on `A' ⊗[A] M` restricts to
`τ m = σ (1 ⊗ m)`, and conversely `τ` extends by `σ (a ⊗ m) = a * τ m`. -/
lemma isUnimodular_tmul_iff (e : M) :
    Module.IsUnimodular A' ((1 : A') ⊗ₜ[A] e) ↔ ∃ τ : M →ₗ[A] A', τ e = 1 := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ.restrictScalars A ∘ₗ (TensorProduct.mk A A' M (1 : A')), ?_⟩
    simpa using hσ
  · rintro ⟨τ, hτ⟩
    refine ⟨AlgebraTensorModule.lift (R := A) (A := A') (P := A') (N := M)
      ((LinearMap.lsmul A' (M →ₗ[A] A')).flip τ), ?_⟩
    rw [AlgebraTensorModule.lift_tmul]
    show (1 : A') • τ e = 1
    rw [hτ, one_smul]

end Abstract

section Present

variable {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']

/-- **Functionals on a presented module, in coordinates.**
An `A`-linear functional `τ` on `A^m ⧸ im D` with `τ (presentMk D e) = 1` is exactly a vector
`w : Fin m → A'` satisfying `transMap D w = 0` (i.e. `∑ i, D i j * w i = 0` for all `j`) and
`∑ i, e i * w i = 1`, written with the structure map `A → A'`. -/
lemma exists_linearMap_presentMk_iff {m n : ℕ} (D : Fin m → Fin n → A) (e : Fin m → A) :
    (∃ τ : present D →ₗ[A] A', τ (presentMk D e) = 1) ↔
      ∃ w : Fin m → A', (∀ j, ∑ i, algebraMap A A' (D i j) * w i = 0) ∧
        (∑ i, algebraMap A A' (e i) * w i = 1) := by
  constructor
  · rintro ⟨τ, hτ⟩
    have hA : ∀ x : Fin m → A,
        τ (presentMk D x) = ∑ i, algebraMap A A' (x i) * τ (presentMk D (Pi.single i 1)) := by
      intro x
      conv_lhs => rw [← sum_single_smul (A := A) x]
      rw [map_sum, map_sum]
      simp only [map_smul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Algebra.smul_def]
    refine ⟨fun i => τ (presentMk D (Pi.single i 1)), ?_, ?_⟩
    · intro j
      have h0 : τ (presentMk D (matMap D (Pi.single j 1))) = 0 := by
        have hz : presentMk D (matMap D (Pi.single j 1)) = 0 := by
          rw [presentMk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact ⟨Pi.single j 1, rfl⟩
        rw [hz, map_zero]
      rw [← h0, hA]
      apply Finset.sum_congr rfl
      intro i _
      rw [matMap_apply]
      congr 1
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; rw [Pi.single_eq_of_ne hb, mul_zero]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    · rw [← hτ, hA]
  · rintro ⟨w, hw0, hw1⟩
    let τ₀ : (Fin m → A) →ₗ[A] A' :=
      { toFun := fun x => ∑ i, algebraMap A A' (x i) * w i
        map_add' := by
          intro x y
          simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
        map_smul' := by
          intro b x
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, map_mul]
          rw [Algebra.smul_def, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring }
    have hker : ∀ y ∈ LinearMap.range (matMap D), τ₀ y = 0 := by
      rintro y ⟨z, rfl⟩
      simp only [τ₀, LinearMap.coe_mk, AddHom.coe_mk, matMap_apply, map_sum, map_mul,
        Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro j _
      have : ∑ i, (algebraMap A A' (D i j) * algebraMap A A' (z j)) * w i =
          algebraMap A A' (z j) * ∑ i, algebraMap A A' (D i j) * w i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; ring
      rw [this, hw0 j, mul_zero]
    refine ⟨Submodule.liftQ (LinearMap.range (matMap D)) τ₀ ?_, ?_⟩
    · intro y hy; rw [LinearMap.mem_ker]; exact hker y hy
    · simp only [presentMk, Submodule.mkQ_apply]
      rw [Submodule.liftQ_apply]
      simp only [τ₀, LinearMap.coe_mk, AddHom.coe_mk]
      exact hw1

end Present

/-- **Unimodularity of a presented class is compatible with base change.**
The canonical identification `A' ⊗[A] (A^m ⧸ im D) ≃ A'^m ⧸ im D'` (with `D'` the entrywise
extension of `D`) carries `1 ⊗ presentMk D e` to `presentMk D' e'`, and unimodularity is an
invariant of that identification. -/
theorem isUnimodular_tmul_presentMk_iff {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
    {m n : ℕ} (D : Fin m → Fin n → A) (e : Fin m → A) :
    Module.IsUnimodular A' (TensorProduct.mk A A' (Work.DSG4a.present D) (1 : A')
        (Work.DSG4a.presentMk D e)) ↔
      Module.IsUnimodular A' (Work.DSG4a.presentMk (fun i j => algebraMap A A' (D i j))
        (fun i => algebraMap A A' (e i))) := by
  have hL : Module.IsUnimodular A' (TensorProduct.mk A A' (present D) (1 : A')
        (presentMk D e)) ↔
      ∃ w : Fin m → A', (∀ j, ∑ i, algebraMap A A' (D i j) * w i = 0) ∧
        (∑ i, algebraMap A A' (e i) * w i = 1) := by
    rw [TensorProduct.mk_apply, isUnimodular_tmul_iff]
    exact exists_linearMap_presentMk_iff D e
  have hR : Module.IsUnimodular A' (presentMk (fun i j => algebraMap A A' (D i j))
        (fun i => algebraMap A A' (e i))) ↔
      ∃ w : Fin m → A', (∀ j, ∑ i, algebraMap A A' (D i j) * w i = 0) ∧
        (∑ i, algebraMap A A' (e i) * w i = 1) := by
    rw [← one_mem_splitIdeal_iff, mem_splitIdeal_presentMk]
    constructor
    · rintro ⟨w, hw, hwe⟩
      refine ⟨w, mem_solSet.mp hw, ?_⟩
      rw [dot] at hwe
      rw [← hwe]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm]
    · rintro ⟨w, hw, hwe⟩
      refine ⟨w, mem_solSet.mpr hw, ?_⟩
      rw [dot]
      rw [← hwe]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm]
  rw [hL, hR]

end Work.DSG4a
