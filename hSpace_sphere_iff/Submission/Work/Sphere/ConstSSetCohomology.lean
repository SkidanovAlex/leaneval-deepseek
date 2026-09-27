/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: hSpace_sphere_iff team

# The cohomology of a "constant" simplicial set

This file computes the rational simplicial cohomology of a simplicial set `S` which is
*levelwise constant*: there is a type `A` and, in every degree `n`, a bijection

`c n : A ≅ S _⦋n⦌`  (with inverse `v n`),

such that all face maps are the identity under this identification,

`S.δ i (c (n+1) x) = c n x`.

The typical example is the singular complex of a discrete space, e.g. `S⁰`
(`Submission/Work/Sphere/H_sph_zero.lean`).

The cochain complex of such an `S` is the "trivial" (or "constant") complex with
`C^n = (A → ℚ)`, in which the coboundary `δ : C^n → C^{n+1}` is multiplication by

`eps n = ∑_{i : Fin (n+2)} (-1)^i = 0` (for `n` even), `= 1` (for `n` odd).

Concretely, for `f : C^n`,

`(δ f) (c (n+1) x) = ∑_i (-1)^i f (S.δ_i (c (n+1) x)) = (∑_i (-1)^i) f (c n x) = eps n • f (c n x)`,

using only the face relation `S.δ i (c (n+1) x) = c n x` of `D` and the bijectivity of `c`.
Hence the coboundary is `0` in even degrees and an isomorphism in odd degrees, and the
cohomology is

* `H⁰ = (A → ℚ)` (there are no boundaries in degree `0` and every cochain is a cocycle), and
* `Hᵏ = 0` for `k > 0`.

The main statement is `Work.Sphere.ConstSSetCohomology`, the input used to identify the
cohomology of `S⁰` in `Submission/Work/Sphere/H_sph_zero.lean`.
-/
import Mathlib
import Submission.Work.Cohomology.Cohomology

open CategoryTheory Simplicial Opposite

namespace Work.Sphere

open Submission.Cohomology

noncomputable section

/-- Data exhibiting a simplicial set `S` as levelwise constant with values in `A`:
bijections `c n : A ≅ S _⦋n⦌` (with inverses `v n`) under which every face map is the
identity. -/
structure ConstSSetData (S : SSet.{0}) (A : Type) where
  /-- The bijection `A ≅ S _⦋n⦌` in degree `n`. -/
  c : (n : ℕ) → A → S.obj (Opposite.op (SimplexCategory.mk n))
  /-- Its inverse. -/
  v : (n : ℕ) → S.obj (Opposite.op (SimplexCategory.mk n)) → A
  /-- `v` is a left inverse of `c`. -/
  hc : ∀ (n : ℕ) (x : A), v n (c n x) = x
  /-- `v` is a right inverse of `c`. -/
  hv : ∀ (n : ℕ) (σ : S.obj (Opposite.op (SimplexCategory.mk n))), c n (v n σ) = σ
  /-- Every face map is the identity under the identification `A ≅ S _⦋n⦌`. -/
  hface : ∀ (n : ℕ) (i : Fin (n + 2)) (x : A),
      S.map (SimplexCategory.δ i).op (c (n + 1) x) = c n x

namespace ConstSSetData

variable {S : SSet.{0}} {A : Type} (D : ConstSSetData S A)

/-! ## The identification `C^n(S;ℚ) ≃ (A → ℚ)` -/

/-- On cochains, the levelwise bijection `c n` induces a linear equivalence
`C^n(S;ℚ) ≃ₗ[ℚ] (A → ℚ)`, namely precomposition with `c n`. -/
def cochainEquiv (n : ℕ) : Cochain S ℚ n ≃ₗ[ℚ] (A → ℚ) where
  toFun := precomp ℚ (D.c n)
  invFun := precomp ℚ (D.v n)
  map_add' := fun f g => rfl
  map_smul' := fun r f => rfl
  left_inv := by intro f; ext σ; simp [precomp_apply, D.hv n σ]
  right_inv := by intro g; ext x; simp [precomp_apply, D.hc n x]

@[simp] lemma cochainEquiv_apply (n : ℕ) (f : Cochain S ℚ n) (x : A) :
    cochainEquiv D n f x = f (D.c n x) := rfl

lemma cochainEquiv_symm_eq (n : ℕ) (g : A → ℚ) :
    (cochainEquiv D n).symm g = precomp ℚ (D.v n) g := by
  rw [LinearEquiv.symm_apply_eq]
  ext x
  simp only [cochainEquiv_apply, precomp_apply, D.hc n x]

@[simp] lemma cochainEquiv_symm_apply (n : ℕ) (g : A → ℚ)
    (σ : S.obj (Opposite.op (SimplexCategory.mk n))) :
    (cochainEquiv D n).symm g σ = g (D.v n σ) := by
  rw [cochainEquiv_symm_eq, precomp_apply]

/-! ## The multiplier `eps n`

`eps n` is the alternating sum of the `n + 2` faces of an `(n+1)`-simplex; it is the factor
by which the coboundary acts on the constant complex.  It is `0` in even degrees and `1` in
odd degrees, so the coboundary is `0` in even degrees and an isomorphism in odd degrees. -/

/-- `eps n = ∑_{i : Fin (n+2)} (-1)^i`. -/
def eps (n : ℕ) : ℤ := ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ)

lemma eps_eq_zero_of_even {n : ℕ} (h : Even n) : eps n = 0 := by
  have hn2 : Even (n + 2) := by
    obtain ⟨k, rfl⟩ := h
    exact ⟨k + 1, by ring⟩
  rw [eps, Fin.sum_neg_one_pow ℤ (n + 2), if_pos hn2]

lemma eps_eq_one_of_odd {n : ℕ} (h : ¬ Even n) : eps n = 1 := by
  rw [eps, Fin.sum_neg_one_pow ℤ (n + 2), if_neg]
  intro hn2
  rw [Nat.even_iff] at h hn2
  omega

/-! ## The coboundary on the constant complex -/

lemma delta_c (n : ℕ) (i : Fin (n + 2)) (x : A) :
    S.δ i (D.c (n + 1) x) = D.c n x := D.hface n i x

/-- The coboundary of a cochain, evaluated on the simplex `c (n+1) x`, is `eps n` times its
value at `c n x`. -/
lemma coboundary_c (n : ℕ) (f : Cochain S ℚ n) (x : A) :
    coboundary S ℚ n f (D.c (n + 1) x) = eps n • f (D.c n x) := by
  rw [coboundary_apply, eps, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [delta_c D n i x]

/-- The identification `C^n ≃ (A → ℚ)` intertwines the coboundary with multiplication by
`eps n`. -/
lemma cochainEquiv_coboundary (n : ℕ) (f : Cochain S ℚ n) :
    cochainEquiv D (n + 1) (coboundary S ℚ n f) = (eps n : ℚ) • cochainEquiv D n f := by
  ext x
  rw [cochainEquiv_apply, Pi.smul_apply, cochainEquiv_apply, coboundary_c D n f x]
  exact (Int.cast_smul_eq_zsmul ℚ (eps n) (f (D.c n x))).symm

/-- In even degrees the coboundary of the constant complex vanishes. -/
lemma coboundary_eq_zero_of_even (D : ConstSSetData S A) (n : ℕ) (h : Even n) :
    coboundary S ℚ n = 0 := by
  refine LinearMap.ext fun f => ?_
  apply (cochainEquiv D (n + 1)).injective
  rw [cochainEquiv_coboundary D n f, eps_eq_zero_of_even h]
  simp

/-- In odd degrees the coboundary of the constant complex is an isomorphism. -/
lemma coboundary_bijective_of_odd (D : ConstSSetData S A) (n : ℕ) (h : ¬ Even n) :
    Function.Bijective (coboundary S ℚ n) := by
  have key : coboundary S ℚ n
      = ((cochainEquiv D (n + 1)).symm.toLinearMap).comp (cochainEquiv D n).toLinearMap := by
    refine LinearMap.ext fun f => ?_
    apply (cochainEquiv D (n + 1)).injective
    rw [cochainEquiv_coboundary D n f, eps_eq_one_of_odd h]
    simp only [Int.cast_one, one_smul, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
  rw [key]
  exact (cochainEquiv D (n + 1)).symm.bijective.comp (cochainEquiv D n).bijective

/-! ## Cycles and boundaries -/

/-- In even degrees every cochain is a cocycle. -/
lemma cycles_eq_top_of_even (D : ConstSSetData S A) (n : ℕ) (h : Even n) :
    cycles S ℚ n = ⊤ := by
  rw [cycles, coboundary_eq_zero_of_even D n h, LinearMap.ker_zero]

/-- In odd degrees the only cocycle is `0`. -/
lemma cycles_eq_bot_of_odd (D : ConstSSetData S A) (n : ℕ) (h : ¬ Even n) :
    cycles S ℚ n = ⊥ := by
  rw [cycles, LinearMap.ker_eq_bot]
  exact (coboundary_bijective_of_odd D n h).1

/-- In odd degrees every cochain of degree `n+1` is a coboundary. -/
lemma boundaries_eq_top_of_odd (D : ConstSSetData S A) (n : ℕ) (h : ¬ Even n) :
    boundaries S ℚ (n + 1) = ⊤ := by
  show LinearMap.range (coboundary S ℚ n) = ⊤
  rw [LinearMap.range_eq_top]
  exact (coboundary_bijective_of_odd D n h).2

/-- There are no boundaries in degree `0`. -/
lemma boundariesInCycles_zero (_D : ConstSSetData S A) :
    boundariesInCycles S ℚ 0 = ⊥ := by
  rw [boundariesInCycles, show boundaries S ℚ 0 = (⊥ : Submodule ℚ (Cochain S ℚ 0)) from rfl,
    Submodule.comap_bot]
  exact Submodule.ker_subtype _

/-! ## Degree `0`: `H⁰ ≅ (A → ℚ)` -/

/-- Evaluation of a degree `0` cohomology class on the "constant" `0`-simplices: the map
`H⁰(S;ℚ) → (A → ℚ)` induced on the quotient `C⁰ / im δ^{-1} = C⁰` by the identification
`C⁰ ≃ (A → ℚ)`.  It is well defined because there are no boundaries in degree `0`. -/
def HzeroMap (D : ConstSSetData S A) : H S ℚ 0 →ₗ[ℚ] (A → ℚ) :=
  Submodule.liftQ (boundariesInCycles S ℚ 0)
    ((cochainEquiv D 0).toLinearMap.comp (Submodule.subtype (cycles S ℚ 0))) (by
      intro x hx
      rw [LinearMap.mem_ker]
      have hx0 : x = 0 := by
        rw [boundariesInCycles_zero D] at hx
        simpa using hx
      rw [hx0]
      simp)

@[simp] lemma HzeroMap_mk (D : ConstSSetData S A) (u : cycles S ℚ 0) :
    HzeroMap D (Submodule.Quotient.mk u) = cochainEquiv D 0 u := by
  rw [HzeroMap, Submodule.liftQ_apply]
  rfl

lemma HzeroMap_injective (D : ConstSSetData S A) : Function.Injective (HzeroMap D) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  rw [LinearMap.mem_ker] at hz
  induction z using Quot.inductionOn with
  | h u =>
    change HzeroMap D (Submodule.Quotient.mk u) = 0 at hz
    rw [HzeroMap_mk] at hz
    have hu0 : (u : Cochain S ℚ 0) = 0 := (LinearEquiv.map_eq_zero_iff (cochainEquiv D 0)).mp hz
    have hu : u = 0 := Subtype.ext hu0
    change Submodule.Quotient.mk u = 0
    rw [hu]
    simp

lemma HzeroMap_surjective (D : ConstSSetData S A) : Function.Surjective (HzeroMap D) := by
  intro g
  refine ⟨Submodule.Quotient.mk ⟨(cochainEquiv D 0).symm g, ?_⟩, ?_⟩
  · show (cochainEquiv D 0).symm g ∈ LinearMap.ker (coboundary S ℚ 0)
    rw [LinearMap.mem_ker, coboundary_eq_zero_of_even D 0 ⟨0, rfl⟩]
    rfl
  · rw [HzeroMap_mk]
    exact (cochainEquiv D 0).apply_symm_apply g

end ConstSSetData

/-- **The cohomology of a constant simplicial set.**  If `S` is levelwise in bijection with
`A` and all face maps are the identity under this bijection, then `Hᵏ(S;ℚ) = 0` for `k > 0`
and `H⁰(S;ℚ) ≅ (A → ℚ)`. -/
theorem ConstSSetCohomology (S : SSet.{0}) (A : Type)
    (c : (n : ℕ) → A → S.obj (Opposite.op (SimplexCategory.mk n)))
    (v : (n : ℕ) → S.obj (Opposite.op (SimplexCategory.mk n)) → A)
    (hc : ∀ (n : ℕ) (x : A), v n (c n x) = x)
    (hv : ∀ (n : ℕ) (σ : S.obj (Opposite.op (SimplexCategory.mk n))), c n (v n σ) = σ)
    (hface : ∀ (n : ℕ) (i : Fin (n + 2)) (x : A),
      S.map (SimplexCategory.δ i).op (c (n + 1) x) = c n x) :
    (∀ k : ℕ, 0 < k → Subsingleton (Submission.Cohomology.H S ℚ k)) ∧
      Nonempty (Submission.Cohomology.H S ℚ 0 ≃ₗ[ℚ] (A → ℚ)) := by
  let D : ConstSSetData S A := ⟨c, v, hc, hv, hface⟩
  refine ⟨?_, ?_⟩
  · intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
    rintro ⟨u, hu⟩
    rw [boundariesInCycles, Submodule.mem_comap]
    change (u : Cochain S ℚ (m + 1)) ∈ boundaries S ℚ (m + 1)
    by_cases hm : Even m
    · -- `m+1` is odd: the only cocycle in degree `m+1` is `0`, hence is a boundary
      have hodd : ¬ Even (m + 1) := fun h1 => (Nat.even_add_one.mp h1) hm
      have hcyc := ConstSSetData.cycles_eq_bot_of_odd D (m + 1) hodd
      have hu0 : u = 0 := by
        rw [hcyc] at hu
        simpa using hu
      rw [hu0]
      exact Submodule.zero_mem _
    · -- `m` is odd: the coboundary `δ_m` is surjective, so every degree `m+1` cochain is a
      -- boundary
      rw [ConstSSetData.boundaries_eq_top_of_odd D m hm]
      exact Submodule.mem_top
  · -- degree `0`
    exact ⟨LinearEquiv.ofBijective (ConstSSetData.HzeroMap D)
      ⟨ConstSSetData.HzeroMap_injective D, ConstSSetData.HzeroMap_surjective D⟩⟩

end

end Work.Sphere
