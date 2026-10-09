/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The algebraic skeleton of Shafarevich's shrinking procedure: basics

This file sets up the linear algebra used by Shafarevich's *shrinking procedure*
(Proposition 2 of A. Schmidt and K. Wingberg, *Šafarevič's theorem on solvable groups
as Galois groups*, arXiv:math/9809211, Section 2).

The setting is that of `𝔽_p[G]`-modules: `𝔽_p`-vector spaces with a `G`-action by
`𝔽_p`-linear maps.  Formally an "`𝔽_p[G]`-module structure" on `M` is the data

* `[AddCommGroup M]`, `[Module (ZMod p) M]` (the additive group and `𝔽_p`-structure),
* `[DistribMulAction G M]` (the `G`-action),
* `[SMulCommClass G (ZMod p) M]`, i.e. `g • (c • m) = c • (g • m)` (`G` acts by linear maps).

This is equivalent to a `Module (MonoidAlgebra (ZMod p) G) M` structure; we use the
former formulation because it is more convenient for tensor products and Pi types, and
we record the MonoidAlgebra bridge at the end of the file.

## Main definitions

* `Work.Shrinking.IsFpGModule` : the abbreviation for the class `SMulCommClass G (ZMod p) M`.
* `Work.Shrinking.foldMap a` : the folding map `φ_a : (Fin r → M) →ₗ[𝔽_p] M`, `x ↦ ∑ i, a i • x i`.

## Main results

* `Work.Shrinking.surjective_foldMap_iff` : `φ_a` is surjective iff `a ≠ 0` (for `M ≠ 0`).
* `Work.Shrinking.foldMap_equivariant` : `φ_a` is `G`-equivariant.
* diagonal `G`-actions on tensor products and tensor powers, with the module diamonds ruled out
  by the fact that `SMul`/`DistribMulAction` instances for these actions are constructed here.
* dimension and finiteness statements: `finrank_tensorPower`, `finite_of_moduleFinite`, ...
-/

import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Shrinking

open scoped TensorProduct

universe u

variable {p : ℕ}

/-! ## `𝔽_p[G]`-modules -/

/-- An `𝔽_p[G]`-module structure on `M`: the `G`-action is by `𝔽_p`-linear maps, i.e. it
commutes with the `𝔽_p`-scalars.  (The additive, scalar and action structures are the
typeclass hypotheses `AddCommGroup M`, `Module (ZMod p) M`, `DistribMulAction G M`.) -/
abbrev IsFpGModule (p : ℕ) (G : Type*) (M : Type*) [Group G] [AddCommGroup M]
    [Module (ZMod p) M] [DistribMulAction G M] : Prop :=
  SMulCommClass G (ZMod p) M

/-- The `𝔽_p`-linear map underlying the action of `g`. -/
def actLinear {G M : Type*} [Monoid G] [AddCommMonoid M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] (g : G) : M →ₗ[ZMod p] M where
  toFun m := g • m
  map_add' := smul_add g
  map_smul' := fun c m => smul_comm g c m

@[simp]
lemma actLinear_apply {G M : Type*} [Monoid G] [AddCommMonoid M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] (g : G) (m : M) :
    actLinear (p := p) g m = g • m := rfl

/-! ## The folding maps `φ_a`

For `a : Fin r → 𝔽_p` we define `φ_a : (Fin r → M) →ₗ[𝔽_p] M`, `x ↦ ∑ i, a i • x i`.
These are the maps of Proposition 2 of Schmidt–Wingberg (there called `φ_a`); the whole
point is that `φ_a` is `G`-equivariant and, for `a ≠ 0`, surjective. -/

section Fold

variable {M : Type*} [AddCommGroup M] [Module (ZMod p) M]

/-- The **folding map** `φ_a : (Fin r → M) →ₗ[𝔽_p] M`, `x ↦ ∑ i, a i • x i`. -/
def foldMap {r : ℕ} (a : Fin r → ZMod p) : (Fin r → M) →ₗ[ZMod p] M where
  toFun x := ∑ i, a i • x i
  map_add' x y := by simp [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm (a i) c (x i)

@[simp]
lemma foldMap_apply {r : ℕ} (a : Fin r → ZMod p) (x : Fin r → M) :
    foldMap a x = ∑ i, a i • x i := rfl

lemma foldMap_apply_single {r : ℕ} (a : Fin r → ZMod p) (i : Fin r) (m : M) :
    foldMap a (Pi.single i m) = a i • m := by
  rw [foldMap_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_eq_of_ne hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi

lemma foldMap_zero {r : ℕ} : foldMap (M := M) (0 : Fin r → ZMod p) = 0 := by
  ext x; simp [foldMap_apply]

variable {G : Type*} [Group G] [DistribMulAction G M] [SMulCommClass G (ZMod p) M]

/-- The folding map is `G`-equivariant for the pointwise action on `Fin r → M`. -/
lemma foldMap_equivariant {r : ℕ} (a : Fin r → ZMod p) (g : G) (x : Fin r → M) :
    foldMap a (g • x) = g • foldMap a x := by
  simp only [foldMap_apply, Pi.smul_apply]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => (smul_comm g (a i) (x i)).symm

/-- `φ_a` as an `𝔽_p[G]`-homomorphism, i.e. the packaged equivariance statement. -/
lemma foldMap_map_smul_iff (r : ℕ) (a : Fin r → ZMod p) (g : G) (x : Fin r → M) :
    foldMap a (g • x) = g • foldMap a x := foldMap_equivariant a g x

end Fold

section FoldSurjective

variable {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
variable {G : Type*} [Group G] [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
variable [Fact p.Prime]

/-- For `a ≠ 0`, the folding map `φ_a` is surjective: the `i`-th coordinate alone already
hits everything. -/
lemma foldMap_surjective_of_ne_zero {r : ℕ} {a : Fin r → ZMod p} (ha : a ≠ 0) :
    Function.Surjective (foldMap (M := M) a) := by
  intro m
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; exact ha (funext fun i => by simpa using not_exists.mp h i)
  refine ⟨Pi.single i ((a i)⁻¹ • m), ?_⟩
  rw [foldMap_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, ← smul_assoc, smul_eq_mul, mul_inv_cancel₀ hi, one_smul]
  · intro j _ hj; rw [Pi.single_eq_of_ne hj, smul_zero]
  · intro hi'; exact absurd (Finset.mem_univ i) hi'

/-- `φ_a` is surjective if and only if `a ≠ 0`, for `M` a nonzero `𝔽_p`-vector space. -/
lemma surjective_foldMap_iff [Nontrivial M] {r : ℕ} (a : Fin r → ZMod p) :
    Function.Surjective (foldMap (M := M) a) ↔ a ≠ 0 := by
  refine ⟨fun h ha => ?_, foldMap_surjective_of_ne_zero⟩
  subst ha
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨x, hx⟩ := h m
  rw [foldMap_apply] at hx
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at hx
  exact hm hx.symm

end FoldSurjective

/-! ## The diagonal `G`-action on tensor products

For `𝔽_p[G]`-modules `M` and `N` the tensor product `M ⊗[𝔽_p] N` carries the *diagonal*
action `g • (m ⊗ₜ n) = (g • m) ⊗ₜ (g • n)`.  Mathlib has no such instance, so we build it. -/

section DiagonalTensor

variable {G M N : Type*} [Group G]
  [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
  [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N] [SMulCommClass G (ZMod p) N]

/-- The monoid homomorphism `G →* End (M ⊗ N)` defining the diagonal action. -/
def diagTensorHom : G →* ((M ⊗[ZMod p] N) →ₗ[ZMod p] M ⊗[ZMod p] N) where
  toFun g := TensorProduct.map (actLinear (p := p) g) (actLinear (p := p) g)
  map_one' := by
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => rw [TensorProduct.map_tmul]; simp [actLinear]
    | add x y hx hy => simp [hx, hy]
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m n =>
      rw [Module.End.mul_apply, TensorProduct.map_tmul, TensorProduct.map_tmul]
      simp [actLinear, mul_smul]
    | add x y hx hy => simp [hx, hy]

instance instDistribMulActionTensorProduct : DistribMulAction G (M ⊗[ZMod p] N) where
  smul g x := diagTensorHom (p := p) g x
  one_smul x := by change diagTensorHom (p := p) 1 x = x; rw [map_one]; rfl
  mul_smul g h x := by
    change diagTensorHom (p := p) (g * h) x
      = diagTensorHom (p := p) g (diagTensorHom (p := p) h x)
    rw [map_mul, Module.End.mul_apply]
  smul_zero g := map_zero (diagTensorHom (p := p) g)
  smul_add g x y := map_add (diagTensorHom (p := p) g) x y

/-- The diagonal action on a pure tensor. -/
@[simp]
lemma diagTensor_smul_tmul (g : G) (m : M) (n : N) :
    g • (m ⊗ₜ[ZMod p] n) = (g • m) ⊗ₜ[ZMod p] (g • n) := by
  change diagTensorHom (p := p) g (m ⊗ₜ n) = _
  simp [diagTensorHom, actLinear]

lemma diagTensor_smul_def (g : G) (x : M ⊗[ZMod p] N) :
    g • x = TensorProduct.map (actLinear (p := p) g) (actLinear (p := p) g) x := rfl

instance instSMulCommClassTensorProduct : SMulCommClass G (ZMod p) (M ⊗[ZMod p] N) where
  smul_comm g c x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m n =>
      rw [TensorProduct.smul_tmul', diagTensor_smul_tmul, smul_comm g c m,
        ← TensorProduct.smul_tmul', ← diagTensor_smul_tmul]
    | add x y hx hy => simp [smul_add, hx, hy]

end DiagonalTensor

/-! ## The diagonal `G`-action on tensor powers -/

section DiagonalTensorPower

variable {G M : Type*} [Group G] [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction G M] [SMulCommClass G (ZMod p) M]

/-- The monoid homomorphism `G →* End (⨂[𝔽_p]^s M)` defining the diagonal action on the
`s`-th tensor power. -/
def diagTensorPowerHom (s : ℕ) : G →* ((⨂[ZMod p]^s M) →ₗ[ZMod p] ⨂[ZMod p]^s M) :=
  (PiTensorProduct.mapMonoidHom (R := ZMod p) (s := fun _ : Fin s => M)).comp
    (MonoidHom.pi fun _ : Fin s => DistribMulAction.toModuleEnd (ZMod p) M)

instance instDistribMulActionTensorPower (s : ℕ) : DistribMulAction G (⨂[ZMod p]^s M) where
  smul g x := diagTensorPowerHom (p := p) s g x
  one_smul x := by change diagTensorPowerHom (p := p) s 1 x = x; rw [map_one]; rfl
  mul_smul g h x := by
    change diagTensorPowerHom (p := p) s (g * h) x
      = diagTensorPowerHom (p := p) s g (diagTensorPowerHom (p := p) s h x)
    rw [map_mul, Module.End.mul_apply]
  smul_zero g := map_zero (diagTensorPowerHom (p := p) s g)
  smul_add g x y := map_add (diagTensorPowerHom (p := p) s g) x y

/-- The diagonal action on a pure tensor of the tensor power. -/
@[simp]
lemma smul_tprod_tensorPower (s : ℕ) (g : G) (x : Fin s → M) :
    g • (PiTensorProduct.tprod (ZMod p) x)
      = PiTensorProduct.tprod (ZMod p) (fun j => g • x j) := by
  change diagTensorPowerHom (p := p) s g (PiTensorProduct.tprod (ZMod p) x) = _
  rw [show diagTensorPowerHom (p := p) s g
      = PiTensorProduct.map (fun _ : Fin s => actLinear (p := p) g) from rfl]
  rw [PiTensorProduct.map_tprod]
  rfl

instance instSMulCommClassTensorPower (s : ℕ) : SMulCommClass G (ZMod p) (⨂[ZMod p]^s M) where
  smul_comm g c x := by
    change PiTensorProduct.map (fun _ : Fin s => actLinear (p := p) g) (c • x)
      = c • PiTensorProduct.map (fun _ : Fin s => actLinear (p := p) g) x
    exact map_smul _ _ _

end DiagonalTensorPower

/-! ### Packaged statements: the constructions are again `𝔽_p[G]`-modules -/

section IsFpGModuleInstances

variable {G M N : Type*} [Group G]
  [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M]

/-- The pointwise action on a finite product is `𝔽_p`-linear. -/
theorem isFpGModule_pi (r : ℕ) : IsFpGModule p G (Fin r → M) := inferInstance

/-- The diagonal action on a tensor product is `𝔽_p`-linear. -/
theorem isFpGModule_tensorProduct [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] : IsFpGModule p G (M ⊗[ZMod p] N) :=
  instSMulCommClassTensorProduct

/-- The diagonal action on a tensor power is `𝔽_p`-linear. -/
theorem isFpGModule_tensorPower (s : ℕ) : IsFpGModule p G (⨂[ZMod p]^s M) :=
  instSMulCommClassTensorPower s

end IsFpGModuleInstances

/-! ## Finiteness and dimension

A finitely generated `𝔽_p[G]`-module (for `G` finite) is a finite set, hence finite dimensional
over `𝔽_p`; dimension formulas for the constructions above. -/

section Finiteness

variable {G M N : Type*} [AddCommGroup M] [Module (ZMod p) M]

/-- Over a finite field of prime order, a finitely generated module is a finite set. -/
theorem finite_of_moduleFinite [Fact p.Prime] [Module.Finite (ZMod p) M] : Finite M :=
  Finite.of_injective (Module.finBasis (ZMod p) M).equivFun
    (Module.finBasis (ZMod p) M).equivFun.injective

/-- `Fin r → M` is finite-dimensional if `M` is. -/
instance instModuleFinitePi [Module.Finite (ZMod p) M] (r : ℕ) :
    Module.Finite (ZMod p) (Fin r → M) := inferInstance

/-- Dimension of a finite product of copies of `M`. -/
theorem finrank_fin_fun [Fact p.Prime] [Module.Finite (ZMod p) M] (r : ℕ) :
    Module.finrank (ZMod p) (Fin r → M) = r * Module.finrank (ZMod p) M := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp

/-- The `s`-th tensor power of a finite-dimensional `𝔽_p`-module is finite-dimensional. -/
theorem moduleFinite_tensorPower [Fact p.Prime] [Module.Finite (ZMod p) M] (s : ℕ) :
    Module.Finite (ZMod p) (⨂[ZMod p]^s M) :=
  Module.Finite.of_basis (Basis.piTensorProduct (fun _ : Fin s => Module.finBasis (ZMod p) M))

/-- Dimension of the `s`-th tensor power. -/
theorem finrank_tensorPower [Fact p.Prime] [Module.Finite (ZMod p) M] (s : ℕ) :
    Module.finrank (ZMod p) (⨂[ZMod p]^s M) = (Module.finrank (ZMod p) M) ^ s := by
  rw [Module.finrank_eq_card_basis
    (Basis.piTensorProduct (fun _ : Fin s => Module.finBasis (ZMod p) M))]
  simp

/-- Dimension of a tensor product of two finite-dimensional `𝔽_p`-modules. -/
theorem finrank_tensorProduct_eq [Fact p.Prime] [AddCommGroup N] [Module (ZMod p) N]
    [Module.Finite (ZMod p) M] [Module.Finite (ZMod p) N] :
    Module.finrank (ZMod p) (M ⊗[ZMod p] N)
      = Module.finrank (ZMod p) M * Module.finrank (ZMod p) N :=
  Module.finrank_tensorProduct

/-- Dimension of `(⨂^s M) ⊗ N`. -/
theorem finrank_tensorPower_tensor [Fact p.Prime] [AddCommGroup N] [Module (ZMod p) N]
    [Module.Finite (ZMod p) M] [Module.Finite (ZMod p) N] (s : ℕ) :
    Module.finrank (ZMod p) ((⨂[ZMod p]^s M) ⊗[ZMod p] N)
      = (Module.finrank (ZMod p) M) ^ s * Module.finrank (ZMod p) N := by
  rw [finrank_tensorProduct_eq, finrank_tensorPower]

end Finiteness

/-! ## The `MonoidAlgebra` bridge

Per the paper, `M` and `N` are *finitely generated* `𝔽_p[G]`-modules; for finite `G` this is
the same as being finite dimensional over `𝔽_p`.  Here we record the easy direction and the
statement that a finitely generated `𝔽_p[G]`-module (in the `MonoidAlgebra (ZMod p) G`
sense) is a finite set. -/

section MonoidAlgebraBridge

variable {G M : Type*} [Group G] [Fintype G] [AddCommGroup M] [Module (ZMod p) M]
  [Module (MonoidAlgebra (ZMod p) G) M]

instance instModuleFiniteMonoidAlgebra : Module.Finite (ZMod p) (MonoidAlgebra (ZMod p) G) :=
  Module.Finite.of_basis (MonoidAlgebra.basis G (ZMod p))

/-- A finitely generated module over the finite ring `𝔽_p[G]` (`G` finite) is finitely
generated as a `𝔽_p`-module. -/
theorem moduleFinite_of_moduleFinite_monoidAlgebra
    [IsScalarTower (ZMod p) (MonoidAlgebra (ZMod p) G) M]
    [Module.Finite (MonoidAlgebra (ZMod p) G) M] : Module.Finite (ZMod p) M :=
  Module.Finite.trans (MonoidAlgebra (ZMod p) G) M

/-- A finitely generated `𝔽_p[G]`-module (`G` finite) is a finite set, hence finite
dimensional over `𝔽_p`. -/
theorem finite_of_moduleFinite_monoidAlgebra [Fact p.Prime]
    [IsScalarTower (ZMod p) (MonoidAlgebra (ZMod p) G) M]
    [Module.Finite (MonoidAlgebra (ZMod p) G) M] : Finite M :=
  haveI := moduleFinite_of_moduleFinite_monoidAlgebra (p := p) (G := G) (M := M)
  finite_of_moduleFinite (p := p) (M := M)

end MonoidAlgebraBridge

end Work.Shrinking
