import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.PTembedding.kummer_ses_decomp
import Submission.Work.SSGRoute.PTfin.isDiscreteModule_subgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer sequence `1 → μ_n(Ω) → Ωˣ →^n Ωˣ → 1` over a closed subgroup of `G_k`

For a number field `k`, an algebraic closure `Ω` of `k` and a subgroup `H ≤ Gal(Ω/k)`, the `n`-th
power map on the units of `Ω` fits into the short exact sequence of discrete `↥H`-modules

`0 → μ_n(Ω) → Ωˣ →^{u ↦ uⁿ} Ωˣ → 0`,

exhibited here as a `Work.AbsoluteKummer.ShortExactSeq ↥H (μ_n(Ω)) Ωˣ Ωˣ`.

The algebraic content is Kummer theory over the algebraically closed field `Ω`: the kernel of the
`n`-th power map is exactly the group `μ_n(Ω)` of `n`-th roots of unity, and the `n`-th power map is
surjective.  The structural input is that the natural `Gal(Ω/k)`-action on `μ_n(Ω)` and on `Ωˣ` is
*discrete* (the stabiliser of an element is open because `Ω/k` is an algebraic — hence integral —
extension); this restricts to the subgroup `H` by
`Work.SSGRoute.PTfin.isDiscreteModule_subgroup`.  The closedness hypothesis on `H` is not needed
for the construction, but is part of the interface of the request.
-/

namespace Work.SSGRoute.PT

open Work

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

section Defs

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-! ## The Kummer maps -/

/-- **The Kummer inclusion** `μ_n(Ω) ↪ Ωˣ`: an `n`-th root of unity is sent to the underlying
unit of `Ω`. -/
def kummerIotaΩ (n : ℕ) : Additive (rootsOfUnity n Ω) →+ Additive (Units Ω) where
  toFun a := Additive.ofMul ((Additive.toMul a : rootsOfUnity n Ω) : Ωˣ)
  map_zero' := by
    apply Additive.toMul.injective
    simp
  map_add' a b := by
    apply Additive.toMul.injective
    simp

@[simp] theorem kummerIotaΩ_apply (n : ℕ) (a : Additive (rootsOfUnity n Ω)) :
    kummerIotaΩ (Ω := Ω) n a
      = Additive.ofMul ((Additive.toMul a : rootsOfUnity n Ω) : Ωˣ) := rfl

/-- **The `n`-th power endomorphism** of `Ωˣ`, written additively as multiplication by `n`. -/
def kummerPiΩ (n : ℕ) : Additive (Units Ω) →+ Additive (Units Ω) where
  toFun a := n • a
  map_zero' := by simp
  map_add' a b := by
    show n • (a + b) = n • a + n • b
    exact smul_add n a b

@[simp] theorem kummerPiΩ_apply (n : ℕ) (a : Additive (Units Ω)) :
    kummerPiΩ (Ω := Ω) n a = n • a := rfl

/-! ## Equivariance -/

/-- The Kummer inclusion is equivariant for the full Galois group. -/
theorem kummerIotaΩ_equivariant_full (n : ℕ) :
    Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) (kummerIotaΩ (Ω := Ω) n) := by
  intro σ a
  apply Additive.toMul.injective
  show ((PTembedding.MupKummer.muMapOfField k Ω n σ (Additive.toMul a) : rootsOfUnity n Ω) : Ωˣ)
      = (Work.SSGRoute.algEquivUnitsMapΩ k Ω σ)
          ((Additive.toMul a : rootsOfUnity n Ω) : Ωˣ)
  rw [PTembedding.MupKummer.muMapOfField_coe,
      PTembedding.MupCard.algEquivUnitsMapOfField_eq_algEquivUnitsMapΩ]

/-- The Kummer inclusion is equivariant for any subgroup `H ≤ Gal(Ω/k)`. -/
theorem kummerIotaΩ_equivariant (n : ℕ) (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    Work.GroupCohomology.IsEquivariant ↥H (kummerIotaΩ (Ω := Ω) n) := by
  intro g a
  exact kummerIotaΩ_equivariant_full (k := k) (Ω := Ω) n (g : Ω ≃ₐ[k] Ω) a

/-- The `n`-th power endomorphism commutes with the action of any subgroup `H ≤ Gal(Ω/k)`. -/
theorem kummerPiΩ_equivariant (n : ℕ) (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    Work.GroupCohomology.IsEquivariant ↥H (kummerPiΩ (Ω := Ω) n) := by
  intro g a
  show n • (g • a) = g • (n • a)
  rw [PTembedding.MupCard.smul_nsmul_comm]

/-! ## The Kummer sequence -/

/-- The Kummer inclusion is injective. -/
theorem kummerIotaΩ_injective (n : ℕ) : Function.Injective (kummerIotaΩ (Ω := Ω) n) := by
  intro a b h
  have h' : ((Additive.toMul a : rootsOfUnity n Ω) : Ωˣ)
      = ((Additive.toMul b : rootsOfUnity n Ω) : Ωˣ) := by
    simpa using congrArg Additive.toMul h
  exact Additive.toMul.injective (Subtype.ext h')

/-- The `n`-th power map on `Ωˣ` is surjective, `Ω` being algebraically closed. -/
theorem kummerPiΩ_surjective [IsAlgClosed Ω] (n : ℕ) [NeZero n] :
    Function.Surjective (kummerPiΩ (Ω := Ω) n) := by
  intro b
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul b : Units Ω) : Ω)
    (Nat.pos_of_ne_zero (NeZero.ne n))
  have hz0 : z ≠ 0 := by
    intro h
    have h1 : ((Additive.toMul b : Units Ω) : Ω) = 0 := by
      rw [← hz, h, zero_pow (NeZero.ne n)]
    exact (Additive.toMul b).ne_zero h1
  refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
  apply Additive.toMul.injective
  rw [kummerPiΩ_apply, PTembedding.MupCard.toMul_nsmul, toMul_ofMul]
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0]; exact hz)

/-- The kernel of the `n`-th power map on `Ωˣ` is exactly `μ_n(Ω)`. -/
theorem kummerIotaΩ_range_eq_ker_pi (n : ℕ) :
    (kummerIotaΩ (Ω := Ω) n).range = (kummerPiΩ (Ω := Ω) n).ker := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    rw [AddMonoidHom.mem_ker, kummerPiΩ_apply]
    apply Additive.toMul.injective
    rw [PTembedding.MupCard.toMul_nsmul, toMul_zero]
    exact (Additive.toMul a).2
  · intro hb
    rw [AddMonoidHom.mem_ker, kummerPiΩ_apply] at hb
    have hpow : (Additive.toMul b : Units Ω) ^ n = 1 := by
      have h := congrArg Additive.toMul hb
      simpa [PTembedding.MupCard.toMul_nsmul] using h
    refine ⟨Additive.ofMul (⟨Additive.toMul b, (mem_rootsOfUnity n _).mpr hpow⟩ :
      rootsOfUnity n Ω), ?_⟩
    rw [kummerIotaΩ_apply, toMul_ofMul]
    exact ofMul_toMul b

/-! ## Discreteness of the coefficients -/

/-- `μ_n(Ω)` is a discrete `Gal(Ω/k)`-module: the stabiliser of a root of unity is the stabiliser
of its underlying element, which is open because `Ω/k` is algebraic. -/
theorem isDiscreteModule_addRootsOfUnityΩ (n : ℕ) :
    Work.AbsoluteKummer.IsDiscreteModule (Ω ≃ₐ[k] Ω) (Additive (rootsOfUnity n Ω)) := by
  intro a
  have hstab : (MulAction.stabilizer (Ω ≃ₐ[k] Ω) a : Set (Ω ≃ₐ[k] Ω)) =
      (MulAction.stabilizer (Ω ≃ₐ[k] Ω)
        (Additive.ofMul ((Additive.toMul a : rootsOfUnity n Ω) : Ωˣ)) :
          Set (Ω ≃ₐ[k] Ω)) := by
    ext σ
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact PTembedding.MupCard.smul_muAdd_eq_iff n σ a
  rw [hstab, Work.SSGRoute.stabilizer_addUnits_ofMulΩ]
  exact stabilizer_isOpen_of_isIntegral _

/-- `μ_n(Ω)` is a discrete `↥H`-module. -/
theorem isDiscreteModule_subgroup_addRootsOfUnity (n : ℕ) (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    Work.AbsoluteKummer.IsDiscreteModule ↥H (Additive (rootsOfUnity n Ω)) :=
  Work.SSGRoute.PTfin.isDiscreteModule_subgroup H
    (isDiscreteModule_addRootsOfUnityΩ (k := k) (Ω := Ω) n)

/-- `Ωˣ` is a discrete `↥H`-module. -/
theorem isDiscreteModule_subgroup_addUnits (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    Work.AbsoluteKummer.IsDiscreteModule ↥H (Additive (Units Ω)) :=
  Work.SSGRoute.PTfin.isDiscreteModule_subgroup H
    (Work.SSGRoute.isDiscreteModule_addUnitsΩ k Ω)

end Defs

/-! ## The main statement -/

theorem exists_kummerSES_units (n : ℕ) [NeZero n] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (hH : IsClosed (H : Set (Ω ≃ₐ[k] Ω))) :
    ∃ S : Work.AbsoluteKummer.ShortExactSeq ↥H (Additive (rootsOfUnity n Ω))
        (Additive (Units Ω)) (Additive (Units Ω)),
      (∀ u : Additive (Units Ω), S.pi u = n • u) ∧
      (∀ x : Additive (rootsOfUnity n Ω),
        S.iota x = Additive.ofMul ((Additive.toMul x : rootsOfUnity n Ω) : Ωˣ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  exact ⟨{ iota := kummerIotaΩ n
           pi := kummerPiΩ n
           iota_equivariant := kummerIotaΩ_equivariant n H
           pi_equivariant := kummerPiΩ_equivariant n H
           iota_injective := kummerIotaΩ_injective n
           pi_surjective := kummerPiΩ_surjective n
           range_iota_eq_ker_pi := kummerIotaΩ_range_eq_ker_pi n
           isDiscreteM := isDiscreteModule_subgroup_addRootsOfUnity n H
           isDiscreteN := isDiscreteModule_subgroup_addUnits H
           isDiscreteP := isDiscreteModule_subgroup_addUnits H },
    fun _ => rfl, fun _ => rfl⟩

end

end Work.SSGRoute.PT
