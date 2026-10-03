/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Fox derivatives for a finitely generated free group, and the Bieri–Strebel map

This file provides the Fox-derivative calculus for `F = FreeGroup (Fin n)` that is used to
prove the `⟸` direction of the Bieri–Strebel lemma
(`Work.ORFP2.IsFP2_of_extension`).

For a commutative ring `k` the `k[F]`-linear map

  `foxLambda k n : (Fin n →₀ k[F]) →ₗ[k[F]] k[F],  c ↦ ∑ i, c i * (Xᵢ - 1)`

has range the augmentation ideal `augIdeal k F` and is injective
(`Works.ORFP2.augIdeal_freeGroup_surjective`, `Work.ORFP2.augIdeal_freeGroup_injective`).
We record the resulting linear equivalence `foxEquiv`, the "Fox derivative"
`foxDelta k n m : Fin n →₀ k[F]` of `m : F` (characterised by
`∑ i, foxDelta m i * (Xᵢ - 1) = m - 1`), and its basic properties (a cocycle rule).

For a surjection `φ : F →* G` we push coefficients along `φ` (`foxPush`) and obtain the
elements `foxGamma k n φ m = foxPush (foxDelta m) ∈ k[G]ⁿ`; when `m ∈ ker φ` these lie in the
relation module of the presentation.
-/
import Mathlib
import Submission.Work.ORFP2.Basic
import Submission.Work.ORFP2.augIdeal_freeGroup_injective
import Submission.Work.ORFP2.augIdeal_freeGroup_surjective

set_option autoImplicit false
set_option linter.unusedVariables false

open MonoidAlgebra

namespace Work.ORFP2

variable (k : Type*) [CommRing k]

section Lambda

/-- The `k[F]`-linear map `(Fin n →₀ k[F]) →ₗ k[F]`, `c ↦ ∑ i, c i * (Xᵢ - 1)`, with
`F = FreeGroup (Fin n)`. -/
noncomputable def foxLambda (n : ℕ) :
    (Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) →ₗ[MonoidAlgebra k (FreeGroup (Fin n))]
      MonoidAlgebra k (FreeGroup (Fin n)) :=
  Finsupp.linearCombination (MonoidAlgebra k (FreeGroup (Fin n)))
    (fun i => MonoidAlgebra.single (FreeGroup.of i) (1 : k) - 1)

lemma foxLambda_apply (n : ℕ) (c : Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) :
    foxLambda k n c =
      c.sum (fun a x => x * (MonoidAlgebra.single (FreeGroup.of a) (1 : k) - 1)) := by
  simp only [foxLambda, Finsupp.linearCombination_apply, smul_eq_mul]

lemma foxLambda_injective (n : ℕ) : Function.Injective (foxLambda k n) := by
  intro c d h
  refine augIdeal_freeGroup_injective k (Fin n) ?_
  show c.sum (fun a x => x * (MonoidAlgebra.single (FreeGroup.of a) (1 : k) - 1)) =
      d.sum (fun a x => x * (MonoidAlgebra.single (FreeGroup.of a) (1 : k) - 1))
  rw [← foxLambda_apply k n c, ← foxLambda_apply k n d, h]

lemma foxLambda_range (n : ℕ) : LinearMap.range (foxLambda k n) = augIdeal k (FreeGroup (Fin n)) :=
  augIdeal_freeGroup_surjective k (Fin n)

/-- The `k[F]`-linear equivalence `(Fin n →₀ k[F]) ≃ₗ augIdeal k F`, `c ↦ ∑ i, c i * (Xᵢ - 1)`. -/
noncomputable def foxEquiv (n : ℕ) :
    (Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) ≃ₗ[MonoidAlgebra k (FreeGroup (Fin n))]
      augIdeal k (FreeGroup (Fin n)) :=
  LinearEquiv.ofBijective
    ((foxLambda k n).codRestrict (augIdeal k (FreeGroup (Fin n)))
      (fun c => by rw [← foxLambda_range k n]; exact LinearMap.mem_range_self _ c))
    ⟨fun _ _ h => foxLambda_injective k n (Subtype.ext_iff.mp h), fun y => by
      have hy : (y : MonoidAlgebra k (FreeGroup (Fin n))) ∈ LinearMap.range (foxLambda k n) := by
        rw [foxLambda_range k n]; exact y.2
      obtain ⟨c, hc⟩ := hy
      exact ⟨c, Subtype.ext hc⟩⟩

@[simp]
lemma foxEquiv_apply (n : ℕ) (c : Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) :
    ((foxEquiv k n) c : MonoidAlgebra k (FreeGroup (Fin n))) = foxLambda k n c := rfl

/-- The Fox derivative of a free group element: `foxDelta m` is the unique `c` with
`∑ i, c i * (Xᵢ - 1) = m - 1`. -/
noncomputable def foxDelta (n : ℕ) (m : FreeGroup (Fin n)) :
    Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n)) :=
  (foxEquiv k n).symm
    ⟨MonoidAlgebra.single m (1 : k) - 1,
      single_sub_one_mem_augIdeal k (FreeGroup (Fin n)) m⟩

lemma foxEquiv_foxDelta (n : ℕ) (m : FreeGroup (Fin n)) :
    (foxEquiv k n) (foxDelta k n m) =
      ⟨MonoidAlgebra.single m (1 : k) - 1,
        single_sub_one_mem_augIdeal k (FreeGroup (Fin n)) m⟩ :=
  (foxEquiv k n).apply_symm_apply _

lemma foxLambda_foxDelta (n : ℕ) (m : FreeGroup (Fin n)) :
    foxLambda k n (foxDelta k n m) = MonoidAlgebra.single m (1 : k) - 1 := by
  rw [← foxEquiv_apply, foxEquiv_foxDelta]

/-- The cocycle (Leibniz) rule for the Fox derivative. -/
lemma foxDelta_mul (n : ℕ) (a b : FreeGroup (Fin n)) :
    foxDelta k n (a * b) =
      (MonoidAlgebra.single a (1 : k)) • (foxDelta k n b) + foxDelta k n a := by
  apply (foxEquiv k n).injective
  simp only [map_add, map_smul, foxEquiv_foxDelta]
  apply Subtype.ext
  simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]
  rw [mul_sub, MonoidAlgebra.single_mul_single]
  simp only [mul_one]
  rw [sub_add_sub_cancel]

lemma foxDelta_one (n : ℕ) : foxDelta k n (1 : FreeGroup (Fin n)) = 0 := by
  have h := foxDelta_mul k n (1 : FreeGroup (Fin n)) 1
  simp only [mul_one] at h
  rw [← MonoidAlgebra.one_def, one_smul] at h
  have h' : foxDelta k n 1 + foxDelta k n 1 = foxDelta k n 1 + 0 := by
    rw [add_zero]; exact h.symm
  exact add_left_cancel h'

end Lambda

section Push

variable {G : Type*} [Group G] (n : ℕ) (φ : FreeGroup (Fin n) →* G)

/-- Push coefficients of `Fin n →₀ k[F]` forward along the algebra map induced by `φ`. -/
noncomputable def foxPush (c : Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) :
    Fin n →₀ MonoidAlgebra k G :=
  c.mapRange (MonoidAlgebra.mapDomainAlgHom k k φ) (map_zero _)

/-- The Bieri–Strebel element attached to `m : F`: the push-forward of its Fox derivative. -/
noncomputable def foxGamma (m : FreeGroup (Fin n)) : Fin n →₀ MonoidAlgebra k G :=
  foxPush k n φ (foxDelta k n m)

lemma foxPush_single (i : Fin n) (r : MonoidAlgebra k (FreeGroup (Fin n))) :
    foxPush k n φ (Finsupp.single i r) =
      Finsupp.single i (MonoidAlgebra.mapDomainAlgHom k k φ r) := by
  rw [foxPush]; exact Finsupp.mapRange_single

lemma foxPush_add (c d : Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) :
    foxPush k n φ (c + d) = foxPush k n φ c + foxPush k n φ d := by
  rw [foxPush, foxPush, foxPush]
  exact Finsupp.mapRange_add (fun x y => map_add (MonoidAlgebra.mapDomainAlgHom k k φ) x y) c d

lemma foxPush_smul (a : MonoidAlgebra k (FreeGroup (Fin n)))
    (c : Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) :
    foxPush k n φ (a • c) =
      (MonoidAlgebra.mapDomainAlgHom k k φ a) • foxPush k n φ c := by
  rw [foxPush, foxPush]
  exact Finsupp.mapRange_smul' a (MonoidAlgebra.mapDomainAlgHom k k φ a) c
    (fun x => by simp only [smul_eq_mul, map_mul])

lemma foxGamma_mul (a b : FreeGroup (Fin n)) :
    foxGamma k n φ (a * b) =
      (MonoidAlgebra.single (φ a) (1 : k)) • foxGamma k n φ b + foxGamma k n φ a := by
  rw [foxGamma, foxDelta_mul, foxPush_add, foxPush_smul, foxGamma, foxGamma]
  rw [show MonoidAlgebra.mapDomainAlgHom k k φ (MonoidAlgebra.single a (1 : k))
      = MonoidAlgebra.single (φ a) (1 : k) from by
        rw [MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single]]

lemma foxGamma_one : foxGamma k n φ (1 : FreeGroup (Fin n)) = 0 := by
  rw [foxGamma, foxDelta_one]
  exact Finsupp.mapRange_zero

/-- The relation map of the presentation `φ` intertwines `foxPush` with the Fox derivative:
`relMap (foxPush w) = φ * (foxLambda w)`. -/
lemma relMap_foxPush (w : Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) :
    relMap k G φ (foxPush k n φ w) =
      MonoidAlgebra.mapDomainAlgHom k k φ (foxLambda k n w) := by
  induction w using Finsupp.induction_linear with
  | zero => simp [foxPush, foxLambda, relMap]
  | add p q hp hq =>
      rw [foxPush_add]
      simp only [map_add]
      rw [hp, hq]
  | single i r =>
      rw [foxPush_single, relMap, Finsupp.linearCombination_single,
        foxLambda, Finsupp.linearCombination_single]
      simp only [smul_eq_mul, map_mul, map_sub, map_one,
        MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single]

lemma foxGamma_mul' (a b : FreeGroup (Fin n)) :
    foxGamma k n φ (a * b) =
      foxGamma k n φ a
        + (MonoidAlgebra.single (φ a) (1 : k)) • foxGamma k n φ b := by
  rw [foxGamma_mul, add_comm]

/-- For `m ∈ ker φ`, the pushed Fox derivative of `m` lies in the relation module. -/
lemma foxGamma_mem (m : FreeGroup (Fin n)) (hm : m ∈ MonoidHom.ker φ) :
    foxGamma k n φ m ∈ relationModule k G φ := by
  rw [relationModule, LinearMap.mem_ker, foxGamma, relMap_foxPush, foxLambda_foxDelta]
  rw [map_sub, MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single, map_one]
  rw [MonoidHom.mem_ker.mp hm, ← MonoidAlgebra.one_def, sub_self]

/-- Additivity of the pushed Fox derivative on `ker φ`. -/
lemma foxGamma_add (a b : FreeGroup (Fin n)) (ha : a ∈ MonoidHom.ker φ)
    (_hb : b ∈ MonoidHom.ker φ) :
    foxGamma k n φ (a * b) = foxGamma k n φ a + foxGamma k n φ b := by
  rw [foxGamma_mul', MonoidHom.mem_ker.mp ha, ← MonoidAlgebra.one_def, one_smul]

/-- Inverses of elements of `ker φ`: `foxGamma a⁻¹ = -foxGamma a`. -/
lemma foxGamma_inv (a : FreeGroup (Fin n)) (ha : a ∈ MonoidHom.ker φ) :
    foxGamma k n φ a⁻¹ = -foxGamma k n φ a := by
  have h := foxGamma_mul' k n φ a a⁻¹
  rw [mul_inv_cancel, foxGamma_one, MonoidHom.mem_ker.mp ha, ← MonoidAlgebra.one_def,
    one_smul] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- `single (φ g) 1 • foxGamma g⁻¹ = - foxGamma g`. -/
lemma single_phi_smul_foxGamma_inv (g : FreeGroup (Fin n)) :
    (MonoidAlgebra.single (φ g) (1 : k)) • foxGamma k n φ g⁻¹ = -foxGamma k n φ g := by
  have h := foxGamma_mul' k n φ g g⁻¹
  rw [mul_inv_cancel, foxGamma_one] at h
  -- h : 0 = foxGamma g + single (φ g) 1 • foxGamma g⁻¹
  exact eq_neg_of_add_eq_zero_right h.symm

/-- Equivariance of the pushed Fox derivative under conjugation, on `ker φ`. -/
lemma foxGamma_conj (g m : FreeGroup (Fin n)) (hm : m ∈ MonoidHom.ker φ) :
    foxGamma k n φ (g * m * g⁻¹) =
      (MonoidAlgebra.single (φ g) (1 : k)) • foxGamma k n φ m := by
  rw [show g * m * g⁻¹ = g * (m * g⁻¹) from by group, foxGamma_mul',
    foxGamma_mul', MonoidHom.mem_ker.mp hm, ← MonoidAlgebra.one_def, one_smul, smul_add,
    single_phi_smul_foxGamma_inv]
  abel

end Push

/-- The algebra map induced by a surjective group homomorphism is surjective. -/
lemma mapDomainAlgHom_surjective {F : Type*} [Group F] {G : Type*} [Group G]
    (φ : F →* G) (hφ : Function.Surjective φ) :
    Function.Surjective (MonoidAlgebra.mapDomainAlgHom k k φ) := by
  intro y
  induction y using MonoidAlgebra.induction_on with
  | of m =>
      obtain ⟨m', rfl⟩ := hφ m
      exact ⟨MonoidAlgebra.of k F m', by
        rw [MonoidAlgebra.of_apply, MonoidAlgebra.mapDomainAlgHom_apply,
          MonoidAlgebra.mapDomain_single, MonoidAlgebra.of_apply]⟩
  | add a b ha hb =>
      obtain ⟨x, hx⟩ := ha; obtain ⟨y, hy⟩ := hb
      exact ⟨x + y, by rw [map_add, hx, hy]⟩
  | smul r a ha =>
      obtain ⟨x, hx⟩ := ha
      exact ⟨r • x, by rw [map_smul, hx]⟩

end Work.ORFP2
