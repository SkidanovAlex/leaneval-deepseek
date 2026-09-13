import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Counting matrices whose kernel contains a subspace and whose range lies in a subspace

Let `V₁ ≤ (Fin n → ZMod 2)` and `W₁ ≤ (Fin m → ZMod 2)` be two `𝔽₂`-subspaces.  We count the
matrices `B : Matrix (Fin m) (Fin n) (ZMod 2)` such that `V₁ ≤ ker (B.mulVecLin)` and
`range (B.mulVecLin) ≤ W₁`, i.e. the `𝔽₂`-linear maps `(Fin n → ZMod 2) →ₗ (Fin m → ZMod 2)`
that vanish on `V₁` and take values in `W₁`.

Such a map is the same thing as a linear map `(Fin n → ZMod 2) ⧸ V₁ →ₗ W₁`, so the count equals
the number of linear maps between two `𝔽₂`-vector spaces of dimensions `n - dim V₁` and
`dim W₁`, namely `2 ^ (dim W₁ * (n - dim V₁))`.

The two ingredients are
* the general cardinality formula `Nat.card (U →ₗ[K] V) = |K|^(finrank U * finrank V)` for
  finite-dimensional vector spaces over a finite field (`natCard_linearMap` below), and
* the rank–nullity identity `finrank (M ⧸ S) + finrank S = finrank M`.
-/

namespace Commons.LinearAlgebra.Submodule

open LinearMap

/-- The number of linear maps between two finite-dimensional vector spaces over a field `K`
(of finite cardinality, so this is a genuine count) is `|K|^(finrank U * finrank V)`. -/
theorem natCard_linearMap (K : Type*) [Field K] (U V : Type*) [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [Module.Finite K U] [Module.Finite K V] :
    Nat.card (U →ₗ[K] V) = Nat.card K ^ (Module.finrank K U * Module.finrank K V) := by
  rw [Module.natCard_eq_pow_finrank (K := K) (V := U →ₗ[K] V),
    Module.finrank_linearMap K K U V]

/-- The linear map `M ⧸ V₁ →ₗ W₁` attached to a linear map `f : M →ₗ W` vanishing on `V₁` and
with range inside `W₁`: it is the unique factorisation of `f` through `M ⧸ V₁` with values in
`W₁`. -/
private noncomputable def hinv (m n : ℕ) (V₁ : Submodule (ZMod 2) (Fin n → ZMod 2))
    (W₁ : Submodule (ZMod 2) (Fin m → ZMod 2))
    (f : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (hf : V₁ ≤ LinearMap.ker f) (hf' : LinearMap.range f ≤ W₁) :
    ((Fin n → ZMod 2) ⧸ V₁) →ₗ[ZMod 2] W₁ :=
  LinearMap.codRestrict W₁ (V₁.liftQ f hf) (fun c => by
    have h : (V₁.liftQ f hf).range ≤ W₁ := by rw [Submodule.range_liftQ]; exact hf'
    exact h (LinearMap.mem_range_self _ c))

/-- Matrices satisfying the two subspace constraints are in bijection with linear maps
`(Fin n → ZMod 2) ⧸ V₁ →ₗ W₁`: factor out by `V₁` (using the vanishing condition) and then
restrict the codomain to `W₁`. -/
private noncomputable def homEquiv (m n : ℕ) (V₁ : Submodule (ZMod 2) (Fin n → ZMod 2))
    (W₁ : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    {f : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) //
        V₁ ≤ LinearMap.ker f ∧ LinearMap.range f ≤ W₁} ≃
      (((Fin n → ZMod 2) ⧸ V₁) →ₗ[ZMod 2] W₁) where
  toFun f := hinv m n V₁ W₁ f.1 f.2.1 f.2.2
  invFun g := ⟨W₁.subtype.comp (g.comp V₁.mkQ),
    ⟨by
      have h1 : V₁ ≤ LinearMap.ker (g.comp V₁.mkQ) := by
        rw [LinearMap.ker_comp]
        exact Submodule.le_comap_mkQ V₁ (LinearMap.ker g)
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mem_ker.mp (h1 hx), map_zero],
    by
      rintro y ⟨x, rfl⟩
      exact (g (V₁.mkQ x)).2⟩⟩
  left_inv f := by
    apply Subtype.ext
    have h1 : W₁.subtype.comp (hinv m n V₁ W₁ f.1 f.2.1 f.2.2) = V₁.liftQ f.1 f.2.1 := by
      ext c
      simp [hinv]
    calc W₁.subtype.comp ((hinv m n V₁ W₁ f.1 f.2.1 f.2.2).comp V₁.mkQ)
        = (W₁.subtype.comp (hinv m n V₁ W₁ f.1 f.2.1 f.2.2)).comp V₁.mkQ := by
          rw [LinearMap.comp_assoc]
      _ = (V₁.liftQ f.1 f.2.1).comp V₁.mkQ := by rw [h1]
      _ = f.1 := Submodule.liftQ_mkQ V₁ f.1 f.2.1
  right_inv g := by
    apply LinearMap.ext
    intro c
    refine Submodule.Quotient.induction_on V₁ c (fun x => ?_)
    apply Subtype.ext
    simp only [hinv, LinearMap.codRestrict_apply, Submodule.liftQ_apply, LinearMap.comp_apply,
      Submodule.mkQ_apply]
    rfl

theorem card_hom_subtype (m n : ℕ) (V₁ : Submodule (ZMod 2) (Fin n → ZMod 2))
    (W₁ : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    Nat.card {B : Matrix (Fin m) (Fin n) (ZMod 2) //
      V₁ ≤ LinearMap.ker B.mulVecLin ∧ LinearMap.range B.mulVecLin ≤ W₁}
      = 2 ^ (Module.finrank (ZMod 2) W₁ * (n - Module.finrank (ZMod 2) V₁)) := by
  have key : ∀ B : Matrix (Fin m) (Fin n) (ZMod 2), Matrix.toLin' B = B.mulVecLin := by
    intro B
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply, Matrix.mulVecLin_apply]
  have h1 : Nat.card {B : Matrix (Fin m) (Fin n) (ZMod 2) //
        V₁ ≤ LinearMap.ker B.mulVecLin ∧ LinearMap.range B.mulVecLin ≤ W₁}
      = Nat.card {f : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) //
        V₁ ≤ LinearMap.ker f ∧ LinearMap.range f ≤ W₁} :=
    Nat.card_congr
      (Equiv.subtypeEquiv (Matrix.toLin' (R := ZMod 2) (m := Fin m) (n := Fin n)).toEquiv
        (fun B => by
          show (V₁ ≤ LinearMap.ker B.mulVecLin ∧ LinearMap.range B.mulVecLin ≤ W₁) ↔
               (V₁ ≤ LinearMap.ker (Matrix.toLin' B) ∧ LinearMap.range (Matrix.toLin' B) ≤ W₁)
          rw [key B]))
  rw [h1]
  rw [Nat.card_congr (homEquiv m n V₁ W₁)]
  rw [natCard_linearMap (ZMod 2) _ W₁, Nat.card_zmod]
  have hdim : Module.finrank (ZMod 2) ((Fin n → ZMod 2) ⧸ V₁)
      = n - Module.finrank (ZMod 2) V₁ := by
    have h := Submodule.finrank_quotient_add_finrank (R := ZMod 2) (M := Fin n → ZMod 2) V₁
    have hX : Module.finrank (ZMod 2) (Fin n → ZMod 2) = n := by
      rw [Module.finrank_fintype_fun_eq_card]; simp
    rw [hX] at h
    omega
  rw [hdim, mul_comm]

end Commons.LinearAlgebra.Submodule