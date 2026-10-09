/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The index-`ℓ` subgroups of an abelian group as a projective space

For an additive commutative group `A` and a prime `ℓ`, the subgroups of `A` of index `ℓ`
are exactly the kernels of the *nonzero* additive homomorphisms `A →+ ℤ/ℓ`, and two such
homomorphisms have the same kernel if and only if they differ by a nonzero scalar.  Since
every additive homomorphism `A →+ ℤ/ℓ` kills `ℓA`, these homomorphisms are the same thing
as the `ℤ/ℓ`-linear forms on the elementary abelian quotient `A ⧸ ℓA`; hence the index-`ℓ`
subgroups of `A` are in bijection with the points of the projective space
`ℙ (ℤ/ℓ) (ellDual ℓ A)`.

The main result is `nIdx_eq_natCard_projectivization`:
`nIdx ℓ A = Nat.card (Projectivization (ZMod ℓ) (ellDual ℓ A))`.

No finiteness hypothesis is needed: the two sides are in bijection as sets, so their
`Nat.card`s agree (both being `0` when infinite).

## Main definitions and results

* `ellToAddHom`: the composite `A →+ ℤ/ℓ` of a linear form on `A ⧸ ℓA` with the quotient map;
* `index_ker_ellToAddHom`: the kernel of `ellToAddHom φ` has index `ℓ` for `φ ≠ 0`;
* `exists_ellDual_ker_eq_of_index`: conversely every index-`ℓ` subgroup of `A` arises
  as such a kernel;
* `exists_smul_eq_of_ker_eq`: two nonzero linear forms with the same kernel are proportional;
* `projToIndexSubgroups`: the bijection `ℙ (ℤ/ℓ) (ellDual ℓ A) ≃ {H // H.index = ℓ}`.
-/
import Mathlib
import Submission.NK.LocalCFT.Units.EllRank.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open Module

namespace NK.LocalCFT.Units.EllRank

section Aux

noncomputable section

variable {ℓ : ℕ} [Fact ℓ.Prime]

section Group

variable {A : Type*} [AddCommGroup A]

/-- The additive homomorphism `A →+ ℤ/ℓ` attached to a `ℤ/ℓ`-linear form on `A ⧸ ℓA`,
by composition with the quotient map `A → A ⧸ ℓA`. -/
def ellToAddHom (φ : ellDual ℓ A) : A →+ ZMod ℓ :=
  φ.toAddMonoidHom.comp (QuotientAddGroup.mk' (nsmulTop ℓ A))

@[simp]
theorem ellToAddHom_apply (φ : ellDual ℓ A) (x : A) :
    ellToAddHom φ x = φ (QuotientAddGroup.mk' (nsmulTop ℓ A) x) := rfl

theorem ellToAddHom_smul (c : ZMod ℓ) (φ : ellDual ℓ A) (x : A) :
    ellToAddHom (c • φ) x = c * ellToAddHom φ x := rfl

/-- Scaling a linear form by a nonzero scalar does not change the kernel of the attached
homomorphism `A →+ ℤ/ℓ`. -/
theorem ker_ellToAddHom_smul {c : ZMod ℓ} (hc : c ≠ 0) (φ : ellDual ℓ A) :
    (ellToAddHom (c • φ)).ker = (ellToAddHom φ).ker := by
  ext x
  simp only [AddMonoidHom.mem_ker, ellToAddHom_smul]
  exact mul_eq_zero.trans (or_iff_right hc)

/-- The kernel of the homomorphism attached to a nonzero form `φ : ellDual ℓ A` is an
index-`ℓ` subgroup of `A`. -/
theorem index_ker_ellToAddHom {φ : ellDual ℓ A} (hφ : φ ≠ 0) :
    (ellToAddHom φ).ker.index = ℓ := by
  rw [AddSubgroup.index_ker]
  rw [AddMonoidHom.range_eq_top.mpr ?_]
  · simp
  · intro y
    have h : Function.Surjective φ := LinearMap.surjective hφ
    obtain ⟨v, hv⟩ := h y
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (nsmulTop ℓ A) v
    exact ⟨x, hv⟩

/-- Every index-`ℓ` subgroup `H` of an additive commutative group `A` is the kernel of a
nonzero additive homomorphism `A →+ ℤ/ℓ` which factors through `A ⧸ ℓA`, i.e. of the form
`ellToAddHom φ` for some `φ : ellDual ℓ A`.

The quotient `A ⧸ H` has cardinality `ℓ`, hence is cyclic of order `ℓ`, giving an additive
isomorphism `ℤ/ℓ ≃+ A ⧸ H`; composing its inverse with the quotient map `A →+ A ⧸ H` yields
the homomorphism, which kills `ℓA` and therefore descends to `A ⧸ ℓA`. -/
theorem exists_ellDual_ker_eq_of_index (H : AddSubgroup A) (hH : H.index = ℓ) :
    ∃ φ : ellDual ℓ A, φ ≠ 0 ∧ (ellToAddHom φ).ker = H := by
  have hcard : Nat.card (A ⧸ H) = ℓ := by rw [← AddSubgroup.index_eq_card, hH]
  have hcyc : IsAddCyclic (A ⧸ H) := isAddCyclic_of_prime_card hcard
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  let e : ZMod ℓ ≃+ (A ⧸ H) := zmodAddEquivOfGenerator hg hcard
  let ψ : A →+ ZMod ℓ := e.symm.toAddMonoidHom.comp (QuotientAddGroup.mk' H)
  have hkerψ : ψ.ker = H := by
    ext x
    show e.symm (QuotientAddGroup.mk' H x) = 0 ↔ x ∈ H
    rw [AddEquiv.map_eq_zero_iff]
    simpa only [QuotientAddGroup.ker_mk' H] using
      (AddMonoidHom.mem_ker (f := QuotientAddGroup.mk' H) (x := x)).symm
  have hle : nsmulTop ℓ A ≤ H := by
    intro x hx
    rw [nsmulTop, AddSubgroup.mem_map] at hx
    obtain ⟨y, -, hy⟩ := hx
    rw [← hy, nsmulAddMonoidHom_apply]
    have h2 : (QuotientAddGroup.mk' H) (ℓ • y) = 0 := by
      rw [map_nsmul]
      have h3 : ℓ • ((QuotientAddGroup.mk' H) y) = 0 := by rw [← hcard]; simp
      exact h3
    have h4 : ℓ • y ∈ (QuotientAddGroup.mk' H).ker := AddMonoidHom.mem_ker.mpr h2
    simpa only [QuotientAddGroup.ker_mk' H] using h4
  let ψb : (A ⧸ nsmulTop ℓ A) →+ ZMod ℓ := QuotientAddGroup.lift (nsmulTop ℓ A) ψ (hkerψ ▸ hle)
  let φ : ellDual ℓ A := ψb.toZModLinearMap ℓ
  have hφψ : ∀ x : A, φ (QuotientAddGroup.mk' (nsmulTop ℓ A) x) = ψ x := by
    intro x
    show (AddMonoidHom.toZModLinearMap ℓ ψb) (QuotientAddGroup.mk' (nsmulTop ℓ A) x) = ψ x
    rw [AddMonoidHom.coe_toZModLinearMap]
    exact QuotientAddGroup.lift_mk (nsmulTop ℓ A) (hkerψ ▸ hle) x
  have hne : H ≠ ⊤ := by
    intro h
    rw [h, AddSubgroup.index_top] at hH
    exact (Fact.out : Nat.Prime ℓ).ne_one hH.symm
  obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne : H < ⊤)
  refine ⟨φ, ?_, ?_⟩
  · intro hφ0
    have h1 : φ (QuotientAddGroup.mk' (nsmulTop ℓ A) x) = 0 := by rw [hφ0]; rfl
    rw [hφψ x] at h1
    have h2 : x ∈ ψ.ker := AddMonoidHom.mem_ker.mpr h1
    rw [hkerψ] at h2
    exact hx h2
  · ext x
    rw [AddMonoidHom.mem_ker, ellToAddHom_apply, hφψ x, ← hkerψ]
    exact (AddMonoidHom.mem_ker (f := ψ) (x := x)).symm

/-- The quotient map `A → A ⧸ ℓA` is surjective, so equality of the kernels in `A` of the
attached homomorphisms is equivalent to equality of the kernels of the linear forms on
`A ⧸ ℓA`. -/
theorem ker_eq_of_ker_ellToAddHom_eq {φ ψ : ellDual ℓ A}
    (h : (ellToAddHom φ).ker = (ellToAddHom ψ).ker) :
    LinearMap.ker φ = LinearMap.ker ψ := by
  ext v
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (nsmulTop ℓ A) v
  have h' : x ∈ (ellToAddHom φ).ker ↔ x ∈ (ellToAddHom ψ).ker := by rw [h]
  simpa [AddMonoidHom.mem_ker, LinearMap.mem_ker] using h'

end Group

/-- Two linear forms on a vector space over a field with the same kernel are proportional.
(No nontriviality assumption is needed: the statement is trivial for the zero form.) -/
theorem exists_smul_eq_of_ker_eq {V : Type*} [AddCommGroup V] [Module (ZMod ℓ) V]
    {φ ψ : Module.Dual (ZMod ℓ) V} (h : LinearMap.ker φ = LinearMap.ker ψ) :
    ∃ c : ZMod ℓ, c • ψ = φ := by
  have hle : (⨅ _ : Unit, LinearMap.ker ψ) ≤ LinearMap.ker φ := by simp [h]
  have h2 := mem_span_of_iInf_ker_le_ker (𝕜 := ZMod ℓ) (ι := Unit)
      (L := fun _ : Unit => ψ) (K := φ) hle
  rw [Set.range_const, Submodule.mem_span_singleton] at h2
  exact h2

section Bijection

variable {A : Type*} [AddCommGroup A]

/-- The index-`ℓ` subgroup of `A` attached to a nonzero element of `ellDual ℓ A`. -/
def projToIndexSubgroup (φ : {φ : ellDual ℓ A // φ ≠ 0}) :
    {H : AddSubgroup A // H.index = ℓ} :=
  ⟨(ellToAddHom φ.1).ker, index_ker_ellToAddHom φ.2⟩

/-- The subgroup attached to a nonzero form only depends on the projective point, i.e. is
invariant under scaling. -/
theorem projToIndexSubgroup_scale (a b : {φ : ellDual ℓ A // φ ≠ 0}) (c : ZMod ℓ)
    (h : (a : ellDual ℓ A) = c • (b : ellDual ℓ A)) :
    projToIndexSubgroup a = projToIndexSubgroup b := by
  have hc : c ≠ 0 := by
    rintro rfl
    simp only [zero_smul] at h
    exact a.2 h
  simp only [projToIndexSubgroup, Subtype.mk.injEq]
  rw [h, ker_ellToAddHom_smul hc]

/-- **The index-`ℓ` subgroups of `A` as a projective space.** The map sending a nonzero
linear form on `A ⧸ ℓA` to the index-`ℓ` subgroup `ellToAddHom φ` of `A`. -/
def projToIndexSubgroups :
    Projectivization (ZMod ℓ) (ellDual ℓ A) → {H : AddSubgroup A // H.index = ℓ} :=
  Projectivization.lift projToIndexSubgroup projToIndexSubgroup_scale

/-- The map `projToIndexSubgroups` is a bijection: it is injective because two nonzero
linear forms with the same kernel are proportional, and surjective by
`exists_ellDual_ker_eq_of_index`. -/
theorem projToIndexSubgroups_bijective :
    Function.Bijective (projToIndexSubgroups (ℓ := ℓ) (A := A)) := by
  constructor
  · intro a b hab
    induction a using Projectivization.ind with
    | h φ hφ =>
      induction b using Projectivization.ind with
      | h ψ hψ =>
        rw [Projectivization.mk_eq_mk_iff]
        have hab' : projToIndexSubgroup (⟨φ, hφ⟩ : {φ : ellDual ℓ A // φ ≠ 0}) =
            projToIndexSubgroup ⟨ψ, hψ⟩ := by
          simpa [projToIndexSubgroups] using hab
        have hker : (ellToAddHom φ).ker = (ellToAddHom ψ).ker := congrArg Subtype.val hab'
        obtain ⟨c, hc⟩ := exists_smul_eq_of_ker_eq (ker_eq_of_ker_ellToAddHom_eq hker)
        have hc0 : c ≠ 0 := by
          rintro rfl
          simp only [zero_smul] at hc
          exact hφ hc.symm
        exact ⟨Units.mk0 c hc0, hc⟩
  · rintro ⟨H, hH⟩
    obtain ⟨φ, hφ, hker⟩ := exists_ellDual_ker_eq_of_index H hH
    exact ⟨Projectivization.mk (ZMod ℓ) φ hφ, by
      simp [projToIndexSubgroups, projToIndexSubgroup, hker]⟩

end Bijection

end

end Aux

/-- **The number of index-`ℓ` subgroups of `A` is the number of points of the projective
space of the dual of `A ⧸ ℓA`.** -/
theorem nIdx_eq_natCard_projectivization {ℓ : ℕ} [Fact ℓ.Prime] (A : Type*) [AddCommGroup A] :
    nIdx ℓ A = Nat.card (Projectivization (ZMod ℓ) (ellDual ℓ A)) := by
  exact (Nat.card_congr (Equiv.ofBijective _ projToIndexSubgroups_bijective)).symm

end NK.LocalCFT.Units.EllRank
