import Mathlib
import Submission.Work.HomologyMV.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `HomologyMV/`: the model groups

The Mayer–Vietoris computation of `H_*(M̂)` compares the terms of the sequence with the
*free* model groups coming from the geometry:

```
k :            0      1      2      3      ≥ 4
H_k(A ∩ B) :  ℤ⁵     ℤ¹⁵    ℤ¹⁵    ℤ⁵     0      (five cuspidal T³'s)
H_k(A)     :  ℤ      ℤ⁵     ℤ¹⁰    ℤ⁴     0      (M̄, i.e. RT's H(M̄))
H_k(B)     :  ℤ⁵     ℤ¹⁰    ℤ⁵     0      0      (five filling T²'s)
```

so that the middle term `H_k(A) ⊞ H_k(B)` has ranks `6, 15, 15, 4, 0, …` and the map
`φ_k : H_k(A ∩ B) → H_k(A) ⊞ H_k(B)` is an integer matrix of size `6×5`, `15×15`, `15×15`,
`4×5` in degrees `0,1,2,3` and the zero map above.

The *answer* of the computation is

```
H_k(M̂) ≅ ℤ  for k = 0, 4,   and   0 otherwise,
```

which is `Sol k`.

## Main definitions

* `freeMod n` — `ℤ^n` as an object of `ModuleCat ℤ`;
* `rankM`, `rankN`, `ModelM`, `ModelN` — the model groups `H_k(A∩B)` and `H_k(A) ⊞ H_k(B)`;
* `kerModel k` — the model for `ker φ_k`: `ℤ` in degree `3`, zero otherwise;
* `Sol k` — the model for `H_k(M̂)`, `ℤ` in degrees `0` and `4`, zero otherwise;
* `SurjCert`, `KernelCert` — the two certificate predicates the concrete matrices satisfy.
-/

namespace Work.HomologyMV

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

/-- `ℤ^n` as an object of `ModuleCat ℤ` (the free module on `Fin n`). -/
def freeMod (n : ℕ) : ModuleCat ℤ := ModuleCat.of ℤ (Fin n → ℤ)

/-- The rank of `H_k(A ∩ B) = ⊕_{v} H_k(T³)`: `5, 15, 15, 5, 0, …`. -/
def rankM : ℤ → ℕ := fun k =>
  if k = 0 then 5 else if k = 1 then 15 else if k = 2 then 15 else if k = 3 then 5 else 0

/-- The rank of `H_k(A) ⊞ H_k(B)`: `6, 15, 15, 4, 0, …`. -/
def rankN : ℤ → ℕ := fun k =>
  if k = 0 then 6 else if k = 1 then 15 else if k = 2 then 15 else if k = 3 then 4 else 0

/-- The model group for `H_k(A ∩ B)`. -/
def ModelM (k : ℤ) : ModuleCat ℤ := freeMod (rankM k)

/-- The model group for `H_k(A) ⊞ H_k(B)`. -/
def ModelN (k : ℤ) : ModuleCat ℤ := freeMod (rankN k)

/-- The model for `ker φ_k`: `ℤ` in degree `3` and the zero module otherwise. -/
def kerModel (k : ℤ) : ModuleCat ℤ := if k = 3 then ModuleCat.of ℤ ℤ else freeMod 0

/-- The model for `H_k(M̂)`: `ℤ` in degrees `0` and `4`, the zero module otherwise.  This is
the right-hand side of the target statement. -/
def Sol (k : ℕ) : ModuleCat ℤ :=
  if k = 0 ∨ k = 4 then ModuleCat.of ℤ ℤ else ModuleCat.of ℤ PUnit

@[simp] theorem rankM_zero : rankM 0 = 5 := rfl
@[simp] theorem rankM_one : rankM 1 = 15 := rfl
@[simp] theorem rankM_two : rankM 2 = 15 := rfl
@[simp] theorem rankM_three : rankM 3 = 5 := rfl
@[simp] theorem rankN_zero : rankN 0 = 6 := rfl
@[simp] theorem rankN_one : rankN 1 = 15 := rfl
@[simp] theorem rankN_two : rankN 2 = 15 := rfl
@[simp] theorem rankN_three : rankN 3 = 4 := rfl

theorem rankM_eq_zero (k : ℤ) (h0 : k ≠ 0) (h1 : k ≠ 1) (h2 : k ≠ 2) (h3 : k ≠ 3) :
    rankM k = 0 := by
  rw [rankM, if_neg h0, if_neg h1, if_neg h2, if_neg h3]

theorem rankN_eq_zero (k : ℤ) (h0 : k ≠ 0) (h1 : k ≠ 1) (h2 : k ≠ 2) (h3 : k ≠ 3) :
    rankN k = 0 := by
  rw [rankN, if_neg h0, if_neg h1, if_neg h2, if_neg h3]

@[simp] theorem kerModel_three : kerModel 3 = ModuleCat.of ℤ ℤ := rfl

theorem kerModel_eq_zero (k : ℤ) (h : k ≠ 3) : kerModel k = freeMod 0 := by
  rw [kerModel, if_neg h]

theorem kerModel_eq_zero_of_ge (k : ℤ) (h : 4 ≤ k) : kerModel k = freeMod 0 := by
  rw [kerModel_eq_zero k (by omega)]

@[simp] theorem Sol_zero : Sol 0 = ModuleCat.of ℤ ℤ := rfl
@[simp] theorem Sol_four : Sol 4 = ModuleCat.of ℤ ℤ := rfl

theorem Sol_eq_zero (k : ℕ) (h0 : k ≠ 0) (h4 : k ≠ 4) : Sol k = ModuleCat.of ℤ PUnit := by
  rw [Sol, if_neg (by simp [h0, h4])]

/-- The zero module `ℤ^0` is a zero object. -/
theorem isZero_freeMod_zero : IsZero (freeMod 0) := by
  rw [freeMod, ModuleCat.isZero_iff_subsingleton]
  infer_instance

/-- The model `Sol k` is a zero object unless `k = 0` or `k = 4`. -/
theorem isZero_Sol_of_ne {k : ℕ} (h0 : k ≠ 0) (h4 : k ≠ 4) : IsZero (Sol k) := by
  rw [Sol_eq_zero k h0 h4, ModuleCat.isZero_iff_subsingleton]
  infer_instance

/-- The two components of a `LinearEquiv` between subsingletons. -/
theorem linearEquiv_of_subsingleton {M N : Type} [AddCommGroup M] [Module ℤ M] [AddCommGroup N]
    [Module ℤ N] [Subsingleton M] [Subsingleton N] : Nonempty (M ≃ₗ[ℤ] N) :=
  ⟨LinearEquiv.ofSubsingleton M N⟩

/-- Any two zero objects of `ModuleCat ℤ` are isomorphic. -/
theorem iso_of_isZero {X Y : ModuleCat ℤ} (hX : IsZero X) (hY : IsZero Y) : Nonempty (X ≅ Y) :=
  ⟨hX.isoZero ≪≫ hY.isoZero.symm⟩

/-- A certificate that the model map `w` is surjective in all positive degrees: this is what
makes `H_k(M̂) = 0` for `k = 1, 2, 3`. -/
def SurjCert (w : ∀ k : ℤ, ModelM k ⟶ ModelN k) : Prop :=
  ∀ k : ℤ, 1 ≤ k → (w k).hom.range = ⊤

/-- A certificate describing the kernel of the model map `w` in every degree `k ≥ 0`: this is
what produces the answer `ℤ` in degree `4` and `0` in all other degrees. -/
def KernelCert (w : ∀ k : ℤ, ModelM k ⟶ ModelN k) : Prop :=
  ∀ k : ℤ, 0 ≤ k → Nonempty ((w k).hom.ker ≃ₗ[ℤ] ↥(kerModel k))

end

end Work.HomologyMV
