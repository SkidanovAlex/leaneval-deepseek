/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Order complexes (barycentric subdivisions) of finite posets

For a poset `α`, the **order complex** is the simplicial complex whose
`k`-simplices are the strictly increasing `(k+1)`-tuples of `α` (equivalently the
chains of `α` of cardinality `k+1`).  Its chain complex (with ℤ coefficients and
the alternating-sum differential) is `orderChain` below; `PolyCW.sdChain` is the
specialisation to the poset of cells of a `PolyCW`, i.e. the barycentric
subdivision of the complex.

## Main definitions

* `Simplex α k` — `k`-simplices: strictly increasing `Fin (k+1) → α`.
* `Simplex.face i` — the `i`-th face map (delete the `i`-th vertex).
* `Simplex.snoc σ e h` — the cone with a new top vertex `e`.
* `chainMod α k` — the free ℤ-module on `k`-simplices.
* `faceLM`, `D` — the face maps and the alternating-sum differential.

The key combinatorial identity behind `D ∘ D = 0` is
`Simplex.face_face` (two deletions in either order), from Mathlib's
`Fin.removeNth_removeNth_eq_swap`, together with the parity lemma
`Fin.neg_one_pow_succAbove_add_predAbove`.
-/

namespace Work.Subdivision

universe u

/-- Strict monotonicity of `Fin.succAbove`; used for the face maps. -/
theorem strictMono_succAbove {n : ℕ} (i : Fin (n + 1)) :
    StrictMono (i.succAbove : Fin n → Fin (n + 1)) := by
  intro a b hab
  rcases lt_or_ge (Fin.castSucc a) i with h1 | h1
  · rw [Fin.succAbove_of_castSucc_lt _ _ h1]
    rcases lt_or_ge (Fin.castSucc b) i with h2 | h2
    · rw [Fin.succAbove_of_castSucc_lt _ _ h2, Fin.castSucc_lt_castSucc_iff]
      exact hab
    · rw [Fin.succAbove_of_le_castSucc _ _ h2]
      exact Fin.castSucc_lt_succ_iff.mpr (le_of_lt hab)
  · rw [Fin.succAbove_of_le_castSucc _ _ h1]
    have h2 : ¬ (Fin.castSucc b < i) := by
      intro hh
      have : Fin.castSucc a < Fin.castSucc b := Fin.castSucc_lt_castSucc_iff.mpr hab
      exact absurd (lt_trans this hh) (not_lt_of_ge h1)
    rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt h2)]
    exact Fin.succ_lt_succ_iff.mpr hab

variable {α : Type u} [Preorder α]

/-- The `k`-simplices of the order complex of a poset `α`: strictly increasing
`(k+1)`-tuples of elements of `α`. -/
structure Simplex (α : Type u) [Preorder α] (k : ℕ) where
  /-- The underlying tuple. -/
  toFun : Fin (k + 1) → α
  /-- It is strictly increasing. -/
  strictMono : StrictMono toFun

namespace Simplex

variable {k : ℕ}

instance : CoeFun (Simplex α k) (fun _ => Fin (k + 1) → α) := ⟨Simplex.toFun⟩

@[simp] theorem toFun_eq_coe (σ : Simplex α k) : σ.toFun = σ := rfl

theorem strictMono_apply (σ : Simplex α k) : StrictMono (σ : Fin (k + 1) → α) :=
  σ.strictMono

theorem lt_of_lt {σ : Simplex α k} {i j : Fin (k + 1)} (h : i < j) : σ i < σ j :=
  σ.strictMono h

@[ext]
theorem ext {σ τ : Simplex α k} (h : ∀ i, σ i = τ i) : σ = τ := by
  cases σ; cases τ
  congr 1
  exact funext h

instance [DecidableEq α] : DecidableEq (Simplex α k) := fun a b =>
  if h : a.toFun = b.toFun then isTrue (by ext i; rw [h]) else isFalse fun hh => h (by rw [hh])

noncomputable instance [Fintype α] : Fintype (Simplex α k) :=
  Fintype.ofInjective Simplex.toFun fun a b h => by ext i; rw [h]

theorem injective_toFun : Function.Injective (Simplex.toFun (α := α) (k := k)) :=
  fun a b h => by ext i; rw [h]

/-- The `i`-th face of a `(k+1)`-simplex: drop the `i`-th vertex. -/
def face {k : ℕ} (i : Fin (k + 2)) (σ : Simplex α (k + 1)) : Simplex α k where
  toFun := fun j => σ (i.succAbove j)
  strictMono := σ.strictMono.comp (strictMono_succAbove i)

@[simp] theorem face_apply {k : ℕ} (i : Fin (k + 2)) (σ : Simplex α (k + 1))
    (j : Fin (k + 1)) : face i σ j = σ (i.succAbove j) := rfl

theorem face_toFun {k : ℕ} (i : Fin (k + 2)) (σ : Simplex α (k + 1)) :
    (face i σ).toFun = Fin.removeNth i σ.toFun := rfl

/-- **The fundamental combinatorial identity**: deleting two vertices in either
order gives the same face.  (The Δ-identity for the order complex.) -/
theorem face_face {k : ℕ} (i : Fin (k + 2)) (j : Fin (k + 3)) (σ : Simplex α (k + 2)) :
    face i (face j σ) = face (i.predAbove j) (face (j.succAbove i) σ) := by
  ext t
  exact congrFun (Fin.removeNth_removeNth_eq_swap σ.toFun i j) t

/-- The tuple obtained by appending a new last entry `e`. -/
def snocFun {k : ℕ} (f : Fin (k + 1) → α) (e : α) : Fin (k + 2) → α :=
  @Fin.snoc (k + 1) (fun _ => α) f e

theorem snocFun_castSucc {k : ℕ} (f : Fin (k + 1) → α) (e : α) (j : Fin (k + 1)) :
    snocFun f e j.castSucc = f j :=
  @Fin.snoc_castSucc (k + 1) (fun _ => α) e f j

theorem snocFun_last {k : ℕ} (f : Fin (k + 1) → α) (e : α) :
    snocFun f e (Fin.last (k + 1)) = e :=
  @Fin.snoc_last (k + 1) (fun _ => α) e f

theorem strictMono_snocFun {k : ℕ} (f : Fin (k + 1) → α) (e : α) (hf : StrictMono f)
    (he : ∀ j, f j < e) : StrictMono (snocFun f e) := by
  intro i j hij
  rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
  · have hi : i ≠ Fin.last (k + 1) := by
      intro hh
      rw [hh] at hij
      simp only [Fin.lt_def, Fin.val_last, Fin.val_castSucc] at hij
      have := j'.isLt; omega
    obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    rw [snocFun_castSucc, snocFun_castSucc]
    exact hf hij
  · have hi : i ≠ Fin.last (k + 1) := by
      intro hh
      rw [hh] at hij
      simp only [Fin.lt_def, Fin.val_last] at hij
      omega
    obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    rw [snocFun_castSucc, snocFun_last]
    exact he i'

/-- The cone of a simplex with a new top vertex `e`. -/
def snoc {k : ℕ} (σ : Simplex α k) (e : α) (h : ∀ i, σ i < e) : Simplex α (k + 1) where
  toFun := snocFun σ.toFun e
  strictMono := strictMono_snocFun σ.toFun e σ.strictMono h

@[simp] theorem snoc_toFun {k : ℕ} (σ : Simplex α k) (e : α) (h : ∀ i, σ i < e) :
    (snoc σ e h).toFun = snocFun σ.toFun e := rfl

@[simp] theorem snoc_apply_castSucc {k : ℕ} (σ : Simplex α k) (e : α)
    (h : ∀ i, σ i < e) (i : Fin (k + 1)) :
    snoc σ e h i.castSucc = σ i :=
  snocFun_castSucc σ.toFun e i

@[simp] theorem snoc_apply_last {k : ℕ} (σ : Simplex α k) (e : α) (h : ∀ i, σ i < e) :
    snoc σ e h (Fin.last (k + 1)) = e :=
  snocFun_last σ.toFun e

end Simplex

variable [DecidableEq α]

/-- The free ℤ-module on the `k`-simplices. -/
noncomputable abbrev chainMod (α : Type u) [Preorder α] (k : ℕ) : Type u := Simplex α k →₀ ℤ

/-- The `i`-th face map as a linear map on chains. -/
noncomputable def faceLM {k : ℕ} (i : Fin (k + 2)) :
    chainMod α (k + 1) →ₗ[ℤ] chainMod α k :=
  Finsupp.linearCombination ℤ fun σ : Simplex α (k+1) => Finsupp.single (Simplex.face i σ) 1

@[simp] theorem faceLM_single {k : ℕ} (i : Fin (k + 2)) (σ : Simplex α (k + 1)) :
    faceLM (α := α) i (Finsupp.single σ 1) = Finsupp.single (Simplex.face i σ) 1 := by
  simp [faceLM]

/-- The alternating sum of face maps: the differential of the order complex. -/
noncomputable def D (k : ℕ) : chainMod α (k + 1) →ₗ[ℤ] chainMod α k :=
  ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • faceLM (α := α) i

theorem D_single (k : ℕ) (σ : Simplex α (k + 1)) :
    D (α := α) k (Finsupp.single σ 1)
      = ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (Simplex.face i σ) 1 := by
  simp only [D, LinearMap.sum_apply, LinearMap.smul_apply, faceLM_single]

end Work.Subdivision
