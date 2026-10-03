/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `R`-balanced tensor `S ⊗[R] L` of `S` with an `R`-module `L`

`Submission/Work/ORHughesFree/Epic/BalancedTensor.lean` constructs the `R`-balanced tensor square
`S ⊗[R] S` of a ring `S` that is an `(R,R)`-bimodule along a ring homomorphism `f : R →+* S`,
as the quotient of the `ℤ`-tensor product `S ⊗[ℤ] S` by the "balance" relations
`s·f r ⊗ t = s ⊗ f r·t`.

For the finite-descent step of `Work.Section3.exists_rank_diff_data_of_isEpic` (JZ, GAFA 2019,
Proposition 5.11) we need the same construction with the *second* factor an arbitrary `R`-module
`L`: the relations become `s·f r ⊗ l = s ⊗ r·l`.

This file sets up that construction (`BalancedTensorMod`, `tmulM`) together with the elementary
API: the balance relation, additivity in each variable, extensionality of additive maps agreeing
on elementary tensors, and the naturality in `L` (a linear map `L →ₗ[R] L'` induces an additive
map on the balanced tensors) which is what lets the finite-descent induction *enlarge* the
`R`-module along the way.
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.Epic
import Submission.Work.ORHughesFree.Epic.BalancedTensor

set_option autoImplicit false

universe u

namespace Work.Section3.RkFinModel

variable {R S : Type u} [Ring R] [Ring S]

/-- The "balance" relations `s·f r ⊗ l - s ⊗ r·l` inside the `ℤ`-tensor product `S ⊗[ℤ] L`, where
`S` is regarded as a left `R`-module through `f` and `L` is an `R`-module. -/
def balRelMod (f : R →+* S) (L : Type u) [AddCommGroup L] [Module R L] :
    Set (TensorProduct ℤ S L) :=
  {x | ∃ (s : S) (l : L) (r : R), x = (s * f r) ⊗ₜ[ℤ] l - s ⊗ₜ[ℤ] (r • l)}

/-- The `R`-balanced tensor product `S ⊗[R] L`. -/
abbrev BalancedTensorMod (f : R →+* S) (L : Type u) [AddCommGroup L] [Module R L] : Type u :=
  (TensorProduct ℤ S L) ⧸ AddSubgroup.closure (balRelMod f L)

namespace BalancedTensorMod

instance (f : R →+* S) (L : Type u) [AddCommGroup L] [Module R L] :
    AddCommGroup (BalancedTensorMod f L) := inferInstanceAs (AddCommGroup _)

/-- The canonical additive projection `S ⊗[ℤ] L → S ⊗[R] L`. -/
def mk (f : R →+* S) (L : Type u) [AddCommGroup L] [Module R L] :
    TensorProduct ℤ S L →+ BalancedTensorMod f L :=
  QuotientAddGroup.mk' _

/-- The class of the elementary tensor `s ⊗ l` in `S ⊗[R] L`. -/
def tmulM (f : R →+* S) {L : Type u} [AddCommGroup L] [Module R L] (s : S) (l : L) :
    BalancedTensorMod f L :=
  mk f L (s ⊗ₜ[ℤ] l)

theorem mk_eq_zero_of_mem (f : R →+* S) (L : Type u) [AddCommGroup L] [Module R L]
    {x : TensorProduct ℤ S L} (hx : x ∈ balRelMod f L) : mk f L x = 0 :=
  AddMonoidHom.mem_ker.mp (by
    rw [mk, QuotientAddGroup.ker_mk']
    exact AddSubgroup.subset_closure hx)

/-- The balance relation `s·f r ⊗ l = s ⊗ r·l`. -/
theorem tmulM_balance (f : R →+* S) {L : Type u} [AddCommGroup L] [Module R L]
    (s : S) (l : L) (r : R) : tmulM f (s * f r) l = tmulM f s (r • l) := by
  change mk f L ((s * f r) ⊗ₜ[ℤ] l) = mk f L (s ⊗ₜ[ℤ] (r • l))
  rw [← sub_eq_zero, ← map_sub]
  exact mk_eq_zero_of_mem f L ⟨s, l, r, rfl⟩

theorem tmulM_add (f : R →+* S) {L : Type u} [AddCommGroup L] [Module R L]
    (s s' : S) (l : L) : tmulM f (s + s') l = tmulM f s l + tmulM f s' l := by
  change mk f L ((s + s') ⊗ₜ[ℤ] l) = mk f L (s ⊗ₜ[ℤ] l) + mk f L (s' ⊗ₜ[ℤ] l)
  rw [TensorProduct.add_tmul, map_add]

theorem tmulM_add_right (f : R →+* S) {L : Type u} [AddCommGroup L] [Module R L]
    (s : S) (l l' : L) : tmulM f s (l + l') = tmulM f s l + tmulM f s l' := by
  change mk f L (s ⊗ₜ[ℤ] (l + l')) = mk f L (s ⊗ₜ[ℤ] l) + mk f L (s ⊗ₜ[ℤ] l')
  rw [TensorProduct.tmul_add, map_add]

theorem tmulM_smul (f : R →+* S) {L : Type u} [AddCommGroup L] [Module R L]
    (s : S) (n : ℤ) (l : L) : tmulM f s (n • l) = n • tmulM f s l := by
  change mk f L (s ⊗ₜ[ℤ] (n • l)) = n • mk f L (s ⊗ₜ[ℤ] l)
  rw [TensorProduct.tmul_smul, map_zsmul]

/-- `s ⊗ 0 = 0`. -/
theorem tmulM_zero_right (f : R →+* S) {L : Type u} [AddCommGroup L] [Module R L] (s : S) :
    tmulM f s (0 : L) = 0 := by
  change mk f L (s ⊗ₜ[ℤ] (0 : L)) = 0
  rw [TensorProduct.tmul_zero, map_zero]

/-- **Extensionality.**  Two additive maps out of `S ⊗[R] L` that agree on all elementary tensors
`tmulM s l` are equal. -/
theorem addHom_ext (f : R →+* S) {L : Type u} [AddCommGroup L] [Module R L]
    {A : Type*} [AddCommGroup A] {φ ψ : BalancedTensorMod f L →+ A}
    (h : ∀ s : S, ∀ l : L, φ (tmulM f s l) = ψ (tmulM f s l)) : φ = ψ := by
  have key : ∀ x : TensorProduct ℤ S L, φ (mk f L x) = ψ (mk f L x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero (mk f L), map_zero φ, map_zero ψ]
    | tmul a b => exact h a b
    | add a b ha hb => rw [map_add (mk f L) a b, map_add φ, map_add ψ, ha, hb]
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  simpa only [mk, QuotientAddGroup.mk'_apply] using key y

/-- **Universal property of `S ⊗[R] L`.**  An `R`-balanced `ℤ`-bilinear map `β : S × L → A` with
values in an abelian group factors uniquely through `S ⊗[R] L`. -/
noncomputable def lift (f : R →+* S) {L : Type u} [AddCommGroup L] [Module R L]
    {A : Type*} [AddCommGroup A] (β : S →ₗ[ℤ] L →ₗ[ℤ] A)
    (hβ : ∀ s : S, ∀ l : L, ∀ r : R, β (s * f r) l = β s (r • l)) :
    BalancedTensorMod f L →+ A :=
  QuotientAddGroup.lift (AddSubgroup.closure (balRelMod f L))
    (TensorProduct.lift β).toAddMonoidHom (by
    rw [AddSubgroup.closure_le]
    rintro x ⟨s, l, r, rfl⟩
    show (TensorProduct.lift β) ((s * f r) ⊗ₜ[ℤ] l - s ⊗ₜ[ℤ] (r • l)) = 0
    rw [map_sub, TensorProduct.lift.tmul, TensorProduct.lift.tmul, hβ s l r, sub_self])

theorem lift_tmulM (f : R →+* S) {L : Type u} [AddCommGroup L] [Module R L]
    {A : Type*} [AddCommGroup A] (β : S →ₗ[ℤ] L →ₗ[ℤ] A)
    (hβ : ∀ s : S, ∀ l : L, ∀ r : R, β (s * f r) l = β s (r • l)) (s : S) (l : L) :
    lift f β hβ (tmulM f s l) = β s l := by
  have h1 : lift f β hβ (tmulM f s l)
      = (TensorProduct.lift β).toAddMonoidHom (s ⊗ₜ[ℤ] l) := by
    rw [lift, tmulM, mk, QuotientAddGroup.mk'_apply, QuotientAddGroup.lift_mk]
  rw [h1]
  exact TensorProduct.lift.tmul s l

/-! ### A precise recipe for the finite-descent lemma

We record here the (constructive) route to

`Work.Section3.RkFinModel.exists_fp_model_of_tmul_eq_zero` :

from `h : BalancedTensor.tmul f z s = 0` produce a *finitely presented* `R`-module `L`, an
`R`-linear `φ : L →ₗ[R] S` and `r : L` with `φ r = s` and `BalancedTensorMod.tmulM f z r = 0`.

**Step 1 (two-level derivation extraction).**  `BalancedTensor f` is
`(S ⊗[ℤ] S) ⧸ AddSubgroup.closure (balRel f)` and `S ⊗[ℤ] S` is itself
`FreeAddMonoid (S × S) ⧸ (the bilinear congruence)`.  From `h` one extracts:
finitely many coefficients `c : Fin n → ℤ` and finitely many pairs `(s'_i, r'_i, t'_i)` with

  `(z ⊗ₜ[ℤ] s) = ∑ i, c i • ((s'_i * f (r'_i)) ⊗ₜ[ℤ] t'_i - s'_i ⊗ₜ[ℤ] (f (r'_i) * t'_i))`
  in `S ⊗[ℤ] S`,

i.e. a *finite* derivation using only the bilinear relations of the `ℤ`-tensor product and the
balance relations.  (Equivalently: the word `[(z, s)]` is related to the empty word in the
congruence on `FreeAddMonoid (S × S)` generated by the bilinear moves and the moves
`(s·f r, t) ↔ (s, f r·t)`.)

**Step 2 (the finite module).**  Let `T` be the (finite) set of all elements of `S` that occur as
a *second* component in the derivation of Step 1 together with all the second components that the
bilinear moves produce (i.e. `T` is closed under: if `t ∈ T` and the move `(a, t) ↔ (a', t) + (a'', t)`
occurs then `t ∈ T`; if the move `(a, t + t') ↔ (a, t) + (a, t')` occurs then `t + t' ∋ T`, etc.).
Take

  `L := (⨁_{w ∈ T} R) ⧸ K`   with `K` generated by the finitely many relations
  * `ρ (f r · t) - r • ρ t`   for each balance move `(s·f r, t) ↔ (s, f r·t)`,
  * `ρ (t + t') - ρ t - ρ t'`  for each splitting move,
  * `ρ (n • t) - n • ρ t`      for the `ℤ`-linearity moves,

and `φ : L →ₗ[R] S` the map `ρ w ↦ w` (well defined on the relations since `f r · t = f r · t`
and `(t + t') - t - t' = 0`).  `L` is finitely presented over `R` (a quotient of a finite free
module by a finitely generated submodule) and `φ (ρ s) = s`.

**Step 3 (transport).**  Inducting over the moves of Step 1, the *value*

  `∑ j, c_j • (a_j ⊗ₜ[ℤ] ρ (b_j))  ∈ S ⊗[ℤ] L`

is unchanged: the bilinear moves use `TensorProduct.add_tmul` / `TensorProduct.tmul_add` /
`TensorProduct.tmul_smul`, and the balance move uses the relation `ρ (f r · t) = r • ρ t` together
with `BalaacedTensorMod.tmulM_balance` (i.e. `(s * f r) ⊗ ρ t = s ⊗ (r • ρ t)` in `S ⊗[R] L`,
which holds by *definition* of `BalancedTensorMod`).  Hence

  `(z ⊗ₜ[ℤ] ρ s) = 0`  in  `S ⊗[ℤ] L`,

and applying the quotient map `mk f L : S ⊗[ℤ] L →+ S ⊗[R] L` gives
`BalancedTensorMod.tmulM f z (ρ s) = 0`.

The direct-sum additivity of `S ⊗[R] -` (vanishing is preserved by `L ↪ L × L'`) is what one uses
whenever a step wants to add a fresh generator/lift to `L`; the relations above are imposed only
for the finitely many moves actually occurring, so finite generation is automatic.

-/

/-! ### A precise recipe for `Work.Section3.rank_diff_of_fp_model`

Input: `S` von Neumann regular, `f : R →+* S`, an idempotent `e ∈ S` with `S·s = S·e`, a
finitely presented `R`-module `L`, an `R`-linear `φ : L → S` with `φ r = s`, and the vanishing
`z ⊗[R] r = 0` where `z = 1 - e`.

1. `e s = s = s e` (because `s ∈ S e` and `e` is idempotent), hence `ρ (oneByOne s) = ρ (oneByOne e)`
   for every `ρ` (sandwich `ρ e = ρ (e*s) ≤ ρ s ≤ ρ (s*e) = ρ e`); also `z s = 0`.
2. Let `r~ = tmulM f 1 r ∈ S ⊗[R] L` (the element `1 ⊗ r`).  `z • r~ = tmulM f z r = 0`, and the
   kernel of the `S`-linear surjection `S → S ⊗[R] L`, `x ↦ x • r~` is exactly `S z`:
   `x • r~ = 0 → x s = 0` (apply the `R`-linear map `S ⊗[R] L → S` induced by `φ`), hence
   `x ∈ S z`; the converse is `z • r~ = 0`.  So `S r~ ≅ S/Sz = S e ≅ S s`.
3. Write `L ≅ cokerMat M` for a matrix `M` over `R` (there is
   `Epic.LiDim.exists_cokerMat_linearEquiv_of_finitePresentation`) and let `v : Fin b → R`
   represent `r` under the surjection `R^b ↠ L`; then
   `S ⊗[R] L ≅ cokerMat (M.map f)` and `(S ⊗[R] L)/S r~ ≅ cokerMat ((fromRows M v).map f)`.
   (`Matrix.fromRows M v` is `M` stacked on top of the row `v`.)
4. The short exact sequence `0 → S r~ → S ⊗[R] L → (S ⊗[R] L)/S r~ → 0` splits, because `S` is von
   Neumann regular (every finitely generated submodule of a finitely generated *projective*
   `S`-module is a direct summand; `S ⊗[R] L` is finitely presented, hence projective, over `S`).
   Hence `fpDim ρ (S ⊗[R] L) = fpDim ρ (S r~) + fpDim ρ ((S ⊗[R] L)/S r~)`
   (`Epic.LiDim.fpDim_prod` + `Epic.LiDim.fpDim_le_add_of_exact`).
5. Finally `fpDim ρ (cokerMat (A.map f)) = b - ρ.rk a b (A.map f)`
   (`Epic.fpDim_eq_of_presentation`), so with `A₁ := M`, `A₂ := fromRows M v`,

     `ρ (oneByOne s) = 1 - fpDim ρ (S e) = fpDim ρ (cokerMat (M.map f))
        - fpDim ρ (cokerMat ((fromRows M v).map f))
        = ρ.rk a b (M.map f) - ρ.rk (a+b) b ((fromRows M v).map f)`.

   (Note the two matrices have the same number of *columns* `b`, as required by the statement.)

-/

end BalancedTensorMod

end Work.Section3.RkFinModel
