/-
# `HomologyIso/`: the linear algebra of the model groups

The two model groups of the Mayer–Vietoris computation are

* `ModelM k = ℤ^{rankM k}` — the model for `H_k(A ∩ B)`;
* `ModelN k = ℤ^{rankN k}` — the model for `H_k(A) ⊞ H_k(B)`.

Since `A` and `B` are computed by two *independent* complexes (`M̄` and the five filling tori
`T²_v`), the natural hypothesis for the second slot is the pair of identifications
`ModelA k ≅ H_k(A)` and `ModelB k ≅ H_k(B)` with `rankA + rankB = rankN`; this file provides the
purely algebraic remainder, the decomposition

`ModelN k ≅ ModelA k ⊞ ModelB k`,

i.e. the fact that `ℤ^{a+b} = ℤ^a ⊕ ℤ^b` in the bases of `Work.HomologyMV.Data`.

## Main definitions and results

* `rankA`, `rankB`, `ModelA`, `ModelB` — the ranks `(1,5,10,4)` and `5·(1,2,1)` and their free
  models;
* `rankN_eq_rankA_add_rankB` — `rankN = rankA + rankB`;
* `splitFin`, `splitFinLinear` — `(Fin a → ℤ) × (Fin b → ℤ) ≃ₗ[ℤ] (Fin (a+b) → ℤ)`;
* `modelNSplit` — `ModelN k ≅ ModelA k ⊞ ModelB k`;
* `homSubsingleton_of_subsingleton_target` — every morphism into a trivial module is zero (used
  for the negative degrees).
-/
import Submission.Work.HomologyIso.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.HomologyIso

noncomputable section

universe u

/-! ## §1  The ranks of the two pieces `A` and `B` -/

/-- The rank of `H_k(A) = H_k(M̄)`: `(1, 5, 10, 4)` in the degrees `0, 1, 2, 3` (Ratcliffe–Tschantz,
reproduced in `rtdata/`: `H(M̄) = (ℤ, ℤ⁵, ℤ¹⁰, ℤ⁴, 0)`). -/
def rankA : ℤ → ℕ := fun k =>
  if k = 0 then 1 else if k = 1 then 5 else if k = 2 then 10 else if k = 3 then 4 else 0

/-- The rank of `H_k(B)`: `B` is homotopy equivalent to the five filling tori `T²_v`, so
`H_k(B) = ⊕_{v=1..5} H_k(T²_v)` has rank `5·(1,2,1) = (5,10,5)` in degrees `0,1,2`. -/
def rankB : ℤ → ℕ := fun k =>
  if k = 0 then 5 else if k = 1 then 10 else if k = 2 then 5 else 0

/-- The free model `ℤ^{rankA k}` for `H_k(A)`. -/
def ModelA (k : ℤ) : ModuleCat ℤ := Work.HomologyMV.freeMod (rankA k)

/-- The free model `ℤ^{rankB k}` for `H_k(B)`. -/
def ModelB (k : ℤ) : ModuleCat ℤ := Work.HomologyMV.freeMod (rankB k)

@[simp] theorem rankA_zero : rankA 0 = 1 := rfl
@[simp] theorem rankA_one : rankA 1 = 5 := rfl
@[simp] theorem rankA_two : rankA 2 = 10 := rfl
@[simp] theorem rankA_three : rankA 3 = 4 := rfl
@[simp] theorem rankB_zero : rankB 0 = 5 := rfl
@[simp] theorem rankB_one : rankB 1 = 10 := rfl
@[simp] theorem rankB_two : rankB 2 = 5 := rfl

theorem rankA_eq_zero (k : ℤ) (h0 : k ≠ 0) (h1 : k ≠ 1) (h2 : k ≠ 2) (h3 : k ≠ 3) :
    rankA k = 0 := by
  rw [rankA, if_neg h0, if_neg h1, if_neg h2, if_neg h3]

theorem rankB_eq_zero (k : ℤ) (h0 : k ≠ 0) (h1 : k ≠ 1) (h2 : k ≠ 2) :
    rankB k = 0 := by
  rw [rankB, if_neg h0, if_neg h1, if_neg h2]

/-- **`rankN = rankA + rankB`** — the two pieces `A` and `B` account for the whole middle term
`H_k(A) ⊞ H_k(B)` of the Mayer–Vietoris sequence. -/
theorem rankN_eq_rankA_add_rankB (k : ℤ) :
    Work.HomologyMV.rankN k = rankA k + rankB k := by
  by_cases h0 : k = 0
  · subst h0; decide
  by_cases h1 : k = 1
  · subst h1; decide
  by_cases h2 : k = 2
  · subst h2; decide
  by_cases h3 : k = 3
  · subst h3; decide
  · rw [Work.HomologyMV.rankN_eq_zero k h0 h1 h2 h3, rankA_eq_zero k h0 h1 h2 h3,
      rankB_eq_zero k h0 h1 h2]

/-! ## §1b  The per-cusp ranks

The five cusps contribute *identical* pieces to the Mayer–Vietoris sequence (each is a `T³` and
each filling torus a `T²`), so the ranks above factor as `5 · (per-cusp rank)`:

* `rankT k = (1,3,3,1)` — the homology `H_k(T³)` of one cusp cross-section `S¹ × T²`;
* `rankT2 k = (1,2,1)` — the homology `H_k(T²)` of one filling torus.

These are the ranks the *generated* per-cusp data of `Submission/Work/HomologyIso/Gen/` computes
(`Work.HomologyIso.Gen.cuspCx_homology`, `Work.HomologyIso.Gen.t2Cx_homology`). -/

/-- The rank of `H_k(T³) = H_k(S¹ × T²)`: `(1,3,3,1)`. -/
def rankT : ℤ → ℕ := fun k =>
  if k = 0 then 1 else if k = 1 then 3 else if k = 2 then 3 else if k = 3 then 1 else 0

/-- The rank of `H_k(T²)`: `(1,2,1)`. -/
def rankT2 : ℤ → ℕ := fun k =>
  if k = 0 then 1 else if k = 1 then 2 else if k = 2 then 1 else 0

/-- The free model `ℤ^{rankT k}` for the homology of one cusp `T³`. -/
def ModelT (k : ℤ) : ModuleCat ℤ := Work.HomologyMV.freeMod (rankT k)

/-- The free model `ℤ^{rankT2 k}` for the homology of one filling torus `T²`. -/
def ModelT2 (k : ℤ) : ModuleCat ℤ := Work.HomologyMV.freeMod (rankT2 k)

@[simp] theorem rankT_zero : rankT 0 = 1 := rfl
@[simp] theorem rankT_one : rankT 1 = 3 := rfl
@[simp] theorem rankT_two : rankT 2 = 3 := rfl
@[simp] theorem rankT_three : rankT 3 = 1 := rfl
@[simp] theorem rankT2_zero : rankT2 0 = 1 := rfl
@[simp] theorem rankT2_one : rankT2 1 = 2 := rfl
@[simp] theorem rankT2_two : rankT2 2 = 1 := rfl

theorem rankT_eq_zero (k : ℤ) (h0 : k ≠ 0) (h1 : k ≠ 1) (h2 : k ≠ 2) (h3 : k ≠ 3) :
    rankT k = 0 := by
  rw [rankT, if_neg h0, if_neg h1, if_neg h2, if_neg h3]

theorem rankT2_eq_zero (k : ℤ) (h0 : k ≠ 0) (h1 : k ≠ 1) (h2 : k ≠ 2) : rankT2 k = 0 := by
  rw [rankT2, if_neg h0, if_neg h1, if_neg h2]

/-- **`rankM = 5 · rankT`**: `H_k(A ∩ B)` is the direct sum of the five cusps `T³`. -/
theorem rankM_eq_five_mul_rankT (k : ℤ) :
    Work.HomologyMV.rankM k = 5 * rankT k := by
  by_cases h0 : k = 0
  · subst h0; decide
  by_cases h1 : k = 1
  · subst h1; decide
  by_cases h2 : k = 2
  · subst h2; decide
  by_cases h3 : k = 3
  · subst h3; decide
  · rw [Work.HomologyMV.rankM_eq_zero k h0 h1 h2 h3, rankT_eq_zero k h0 h1 h2 h3]

/-- **`rankB = 5 · rankT2`**: `H_k(B)` is the direct sum of the five filling tori `T²`. -/
theorem rankB_eq_five_mul_rankT2 (k : ℤ) : rankB k = 5 * rankT2 k := by
  by_cases h0 : k = 0
  · subst h0; decide
  by_cases h1 : k = 1
  · subst h1; decide
  by_cases h2 : k = 2
  · subst h2; decide
  · rw [rankB_eq_zero k h0 h1 h2, rankT2_eq_zero k h0 h1 h2]

/-! ## §2  The splitting `ℤ^{a+b} ≅ ℤ^a ⊕ ℤ^b` -/

/-- `(Fin a → ℤ) × (Fin b → ℤ) ≃ (Fin (a + b) → ℤ)`: the concatenation of tuples, the inverse
being the splitting into the first `a` and the last `b` coordinates. -/
def splitFin (a b : ℕ) : (Fin a → ℤ) × (Fin b → ℤ) ≃ (Fin (a + b) → ℤ) where
  toFun v := Fin.append v.1 v.2
  invFun w := (fun i => w (Fin.castAdd b i), fun i => w (Fin.natAdd a i))
  left_inv v := by
    refine Prod.ext ?_ ?_ <;> funext i <;> simp [Fin.append_left, Fin.append_right]
  right_inv w := by
    funext i
    exact Fin.addCases (fun j => by simp [Fin.append_left])
      (fun j => by simp [Fin.append_right]) i

/-- **The linear form of `splitFin`**: `ℤ^{a+b} ≅ ℤ^a ⊕ ℤ^b`. -/
def splitFinLinear (a b : ℕ) : (Fin (a + b) → ℤ) ≃ₗ[ℤ] (Fin a → ℤ) × (Fin b → ℤ) where
  toFun := (splitFin a b).symm
  invFun := splitFin a b
  left_inv w := (splitFin a b).right_inv w
  right_inv v := (splitFin a b).left_inv v
  map_add' x y := rfl
  map_smul' c x := rfl

/-- Transport of tuples along an equality of the index type. -/
def castFinFun {n m : ℕ} (h : n = m) : (Fin n → ℤ) ≃ (Fin m → ℤ) where
  toFun w := w ∘ Fin.cast h.symm
  invFun w := w ∘ Fin.cast h
  left_inv w := by funext i; simp
  right_inv w := by funext i; simp

/-- The linear form of `castFinFun`. -/
def castFinFunLinear {n m : ℕ} (h : n = m) : (Fin n → ℤ) ≃ₗ[ℤ] (Fin m → ℤ) where
  toFun := castFinFun h
  invFun := castFinFun h.symm
  left_inv w := (castFinFun h).left_inv w
  right_inv w := (castFinFun h).right_inv w
  map_add' x y := rfl
  map_smul' c x := rfl

/-- The transport of a free model along an equality of the ranks. -/
def freeModCast {n m : ℕ} (h : n = m) :
    Work.HomologyMV.freeMod n ≅ Work.HomologyMV.freeMod m :=
  (castFinFunLinear h).toModuleIso

/-- **The algebraic splitting of the middle model:**
`ModelN k = ℤ^{rankN k} ≅ ℤ^{rankA k} ⊞ ℤ^{rankB k} = ModelA k ⊞ ModelB k`.

This is the only place where the equality of ranks `rankN = rankA + rankB` is used. -/
def modelNSplit (k : ℤ) : Work.HomologyMV.ModelN k ≅ ModelA k ⊞ ModelB k :=
  (LinearEquiv.toModuleIso
      (((castFinFunLinear (rankN_eq_rankA_add_rankB k)).trans
        (splitFinLinear (rankA k) (rankB k))))).trans
    (ModuleCat.biprodIsoProd (ModelA k) (ModelB k)).symm

/-! ## §3  The trivial module -/

/-- Every morphism of `ℤ`-modules into a trivial module is zero: the hom-set of `ModuleCat ℤ`
into a subsingleton object is a subsingleton. -/
instance homSubsingleton_of_subsingleton_target {X Y : ModuleCat ℤ} [Subsingleton (↥Y)] :
    Subsingleton (X ⟶ Y) :=
  ⟨fun f g => ModuleCat.hom_ext (LinearMap.ext fun x => Subsingleton.elim _ _)⟩

/-- The zero model `freeMod 0` is a zero object. -/
theorem isZero_freeMod_zero : IsZero (Work.HomologyMV.freeMod 0) :=
  Work.HomologyMV.isZero_freeMod_zero

/-- The module `mvZero = ℤ^0`, used for the terms of the sequence in negative degrees. -/
theorem isZero_mvZero : IsZero (Work.Final.mvZero) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  infer_instance

/-- **`freeMod 0 ≅ mvZero`**: the two descriptions of the trivial module. -/
def freeModZeroIso : Work.HomologyMV.freeMod 0 ≅ Work.Final.mvZero :=
  Work.HomologyMV.isZero_freeMod_zero.isoZero ≪≫ (isZero_mvZero).isoZero.symm

end

end Work.HomologyIso
