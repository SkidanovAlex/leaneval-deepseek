import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.AbsoluteKummer.Coefficients
import Submission.Work.AbsoluteKummer.SES
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.Kummer

open scoped Classical

noncomputable section

/-- The Kummer inclusion `μ_n(k̄) ↪ k̄ˣ`, as an additive homomorphism. -/
def kummerIota {k : Type*} [Field k] (n : ℕ) :
    Additive (rootsOfUnity n (AlgebraicClosure k)) →+ Additive (AlgebraicClosure k)ˣ where
  toFun a := Additive.ofMul
    ((Additive.toMul a : rootsOfUnity n (AlgebraicClosure k)) : (AlgebraicClosure k)ˣ)
  map_zero' := by simp
  map_add' a b := by simp

/-- The Kummer projection `k̄ˣ → k̄ˣ`, `u ↦ u ^ n`, as an additive homomorphism. -/
def kummerPi {k : Type*} [Field k] (n : ℕ) :
    Additive (AlgebraicClosure k)ˣ →+ Additive (AlgebraicClosure k)ˣ where
  toFun a := Additive.ofMul (Additive.toMul a ^ n)
  map_zero' := by simp
  map_add' a b := by simp [mul_pow]

@[simp] theorem kummerIota_apply {k : Type*} [Field k] (n : ℕ)
    (a : Additive (rootsOfUnity n (AlgebraicClosure k))) :
    kummerIota n a = Additive.ofMul
      ((Additive.toMul a : rootsOfUnity n (AlgebraicClosure k)) : (AlgebraicClosure k)ˣ) := rfl

@[simp] theorem kummerPi_apply {k : Type*} [Field k] (n : ℕ)
    (a : Additive (AlgebraicClosure k)ˣ) :
    kummerPi n a = Additive.ofMul (Additive.toMul a ^ n) := rfl

theorem kummerIota_equivariant {k : Type*} [Field k] (n : ℕ) :
    Work.GroupCohomology.IsEquivariant (G k) (kummerIota (k := k) n) := by
  intro σ a
  apply Additive.toMul.injective
  simp only [kummerIota_apply, toMul_ofMul, addRootsOfUnity_smul_toMul_val,
    addUnits_smul_toMul]

theorem kummerPi_equivariant {k : Type*} [Field k] (n : ℕ) :
    Work.GroupCohomology.IsEquivariant (G k) (kummerPi (k := k) n) := by
  intro σ a
  apply Additive.toMul.injective
  simp only [kummerPi_apply, toMul_ofMul, addUnits_smul_toMul, map_pow]

theorem kummerIota_injective {k : Type*} [Field k] (n : ℕ) :
    Function.Injective (kummerIota (k := k) n) := by
  intro a b h
  simp only [kummerIota_apply] at h
  exact Additive.toMul.injective (Subtype.ext (Additive.ofMul.injective h))

theorem kummerPi_surjective {k : Type*} [Field k] (n : ℕ) [NeZero n] :
    Function.Surjective (kummerPi (k := k) n) := by
  intro b
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq
    (((Additive.toMul b : (AlgebraicClosure k)ˣ) : AlgebraicClosure k))
    (Nat.pos_of_ne_zero (NeZero.ne n))
  have hz0 : z ≠ 0 := by
    intro h
    have h1 : ((Additive.toMul b : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) = 0 := by
      rw [← hz, h, zero_pow (NeZero.ne n)]
    exact (Additive.toMul b).ne_zero h1
  refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
  apply Additive.toMul.injective
  simp only [kummerPi_apply, toMul_ofMul]
  exact Units.ext (by rw [Units.val_pow_eq_pow_val]; simpa using hz)

theorem kummerIota_range_eq_ker_pi {k : Type*} [Field k] (n : ℕ) :
    (kummerIota (k := k) n).range = (kummerPi (k := k) n).ker := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    rw [AddMonoidHom.mem_ker, kummerPi_apply, kummerIota_apply, toMul_ofMul]
    have h1 : (((Additive.toMul a : rootsOfUnity n (AlgebraicClosure k)) :
        (AlgebraicClosure k)ˣ)) ^ n = 1 := (Additive.toMul a).2
    rw [h1, ofMul_one]
  · intro hb
    rw [AddMonoidHom.mem_ker, kummerPi_apply] at hb
    have hpow : (Additive.toMul b : (AlgebraicClosure k)ˣ) ^ n = 1 := by
      have h := congrArg Additive.toMul hb
      simpa only [toMul_ofMul, toMul_zero] using h
    refine ⟨Additive.ofMul (⟨Additive.toMul b, (mem_rootsOfUnity n _).mpr hpow⟩ :
      rootsOfUnity n (AlgebraicClosure k)), ?_⟩
    rw [kummerIota_apply, toMul_ofMul]
    exact ofMul_toMul b

theorem kummerSES {k : Type*} [Field k] {n : ℕ} [NeZero n] : ∃ S : Work.AbsoluteKummer.ShortExactSeq (Work.AbsoluteKummer.G k) (Additive (rootsOfUnity n (AlgebraicClosure k))) (Additive (AlgebraicClosure k)ˣ) (Additive (AlgebraicClosure k)ˣ), (∀ x : rootsOfUnity n (AlgebraicClosure k), S.iota (Additive.ofMul x) = Additive.ofMul (x : (AlgebraicClosure k)ˣ)) ∧ (∀ u : (AlgebraicClosure k)ˣ, S.pi (Additive.ofMul u) = Additive.ofMul (u ^ n)) := by
  refine ⟨{ iota := kummerIota (k := k) n
            pi := kummerPi (k := k) n
            iota_equivariant := kummerIota_equivariant (k := k) n
            pi_equivariant := kummerPi_equivariant (k := k) n
            iota_injective := kummerIota_injective (k := k) n
            pi_surjective := kummerPi_surjective (k := k) n
            range_iota_eq_ker_pi := kummerIota_range_eq_ker_pi (k := k) n
            isDiscreteM := isDiscreteModule_addRootsOfUnity k n
            isDiscreteN := isDiscreteModule_addUnits k
            isDiscreteP := isDiscreteModule_addUnits k }, ?_, ?_⟩
  · intro x
    simp only [kummerIota_apply, toMul_ofMul]
  · intro u
    simp only [kummerPi_apply, toMul_ofMul]

end

end Work.AbsoluteKummer.Kummer
