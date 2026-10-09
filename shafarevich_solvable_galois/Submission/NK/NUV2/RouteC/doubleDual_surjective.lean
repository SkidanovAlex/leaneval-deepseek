import Mathlib
import Submission.NK.NUV2.RouteC.delta_qmodz
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The double dual of a finite group with `ℚ/ℤ` coefficients

Main result of this file:

`NK.NUV2.RouteC.doubleDual_surjective` : for a finite group `Γ` and any additive map
`Φ : (Additive Γ →+ ℚ/ℤ) →+ ℚ/ℤ`, there is `g : Γ` such that `Φ χ = χ (Additive.ofMul g)` for
all characters `χ`.

Mathematically this is just Pontryagin duality for the finite abelian group `Γᵃᵇ`, since
`Hom(Γ, ℚ/ℤ) = Hom(Γᵃᵇ, ℚ/ℤ)` and the evaluation map
`Γᵃᵇ → Hom(Hom(Γᵃᵇ, ℚ/ℤ), ℚ/ℤ)` is an isomorphism.  We prove this in two steps.

## The bridge to complex characters

For a finite abelian group `A` we build the (additive) equivalence
`bridge : (A →+ qmodZ) ≃+ AddChar A ℂ`,
sending a character `χ` to `a ↦ exp (2 * π * I * χ a)`.  It is an equivalence because for finite
`A` the values of any `ℂ`-valued character are roots of unity, hence exponentials of rationals
(`Complex.mem_rootsOfUnity`), and because `exp (2 * π * I * ·)` is injective on `ℚ/ℤ`
(`expQmodZ_injective`, a direct computation using `Complex.exp_eq_exp_iff_exists_int`).
Pontryagin duality for finite abelian groups in the form proved in Mathlib
(`AddChar.doubleDualEmb_bijective`) then gives the abelian case
`abelian_doubleDual_surjective`.

## Reduction to the abelianization

For a general finite group `Γ`, any additive map `χ : Additive Γ →+ qmodZ` factors through
`Abelianization.of : Γ →* Abelianization Γ` (`exists_abelianization_lift`, an application of the
universal property `Abelianization.lift`), so the abelian case applies to
`Additive (Abelianization Γ)` and one lifts the resulting element of `Abelianization Γ` to `Γ`.
-/

open Complex

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace NK.NUV2.RouteC

/-! ## The exponential map `ℚ/ℤ → ℂˣ` -/

/-- The exponential map `ℚ/ℤ → ℂ`, `x ↦ exp (2 * π * I * x)`, viewed as a map of additive
groups into `Additive ℂ` (i.e. a monoid homomorphism into `ℂ` under multiplication).  It is
well defined on `ℚ/ℤ` because `exp (2 * π * I * n) = 1` for all integers `n`. -/
noncomputable def expQmodZ : qmodZ →+ Additive ℂ :=
  QuotientAddGroup.lift (AddSubgroup.closure ({(1:ℚ)} : Set ℚ))
    { toFun := fun a : ℚ => Additive.ofMul (Complex.exp (2 * Real.pi * Complex.I * a))
      map_zero' := by
        show Additive.ofMul (Complex.exp (2 * Real.pi * Complex.I * ((0:ℚ):ℂ))) = Additive.ofMul 1
        simp
      map_add' := fun a b => by
        apply Additive.ext
        show Complex.exp (2 * Real.pi * Complex.I * ((a+b : ℚ):ℂ)) =
          Complex.exp (2 * Real.pi * Complex.I * (a:ℂ)) * Complex.exp (2 * Real.pi * Complex.I * (b:ℂ))
        have h : (2 * ↑Real.pi * I * ((a+b : ℚ) : ℂ)) =
            (2 * ↑Real.pi * I * (a:ℂ)) + (2 * ↑Real.pi * I * (b:ℂ)) := by push_cast; ring
        rw [h, Complex.exp_add] }
    (by
      intro h hh
      simp only [AddMonoidHom.mem_ker]
      rw [← AddSubgroup.zmultiples_eq_closure, AddSubgroup.mem_zmultiples_iff] at hh
      obtain ⟨k, hk⟩ := hh
      rw [← hk]
      simp only [show (k : ℤ) • (1:ℚ) = (k:ℚ) by simp]
      apply Additive.ext
      show Complex.exp (2 * ↑Real.pi * I * ((k:ℚ):ℂ)) = 1
      rw [Complex.exp_eq_one_iff]
      exact ⟨k, by push_cast; ring⟩)

/-- Computation rule for `expQmodZ` on representatives. -/
theorem expQmodZ_coe (a : ℚ) :
    expQmodZ ((a : ℚ) : qmodZ) = Additive.ofMul (Complex.exp (2 * Real.pi * Complex.I * a)) := by
  rw [expQmodZ, QuotientAddGroup.lift_mk']
  rfl

/-- The exponential map `ℚ/ℤ → ℂˣ` is injective. -/
theorem expQmodZ_injective : Function.Injective expQmodZ := by
  intro x y hxy
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.closure ({(1:ℚ)} : Set ℚ)) x
  obtain ⟨b, hb⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.closure ({(1:ℚ)} : Set ℚ)) y
  rw [← ha, ← hb] at hxy
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, expQmodZ_coe, expQmodZ_coe] at hxy
  have h1 : Complex.exp (2 * ↑Real.pi * I * (a:ℂ)) = Complex.exp (2 * ↑Real.pi * I * (b:ℂ)) :=
    Additive.ofMul.injective hxy
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
  have hπ : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Complex.I_ne_zero, Real.pi_ne_zero]
  have hmul : (2 * ↑Real.pi * I) * ((a:ℂ) - (b:ℂ)) = (2 * ↑Real.pi * I) * (n:ℂ) := by
    rw [mul_comm ((n:ℂ)) (2 * ↑Real.pi * I)] at hn
    have h2 : (2 * ↑Real.pi * I) * ((a:ℂ) - (b:ℂ)) =
        (2 * ↑Real.pi * I) * (a:ℂ) - (2 * ↑Real.pi * I) * (b:ℂ) := by ring
    rw [h2, hn]
    ring
  have h2 : (a:ℂ) - (b:ℂ) = (n:ℂ) := mul_left_cancel₀ hπ hmul
  have h3 : a - b = (n:ℚ) := by exact_mod_cast h2
  rw [← ha, ← hb, QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_iff_sub_mem]
  rw [h3, AddSubgroup.mem_closure_singleton]
  exact ⟨n, by simp⟩

/-! ## The bridge between `ℚ/ℤ`-characters and `ℂ`-valued characters -/

variable {A : Type*} [AddCommGroup A] [Finite A]

/-- The `ℂ`-valued character attached to a `ℚ/ℤ`-valued character: `a ↦ exp (2 * π * I * χ a)`. -/
noncomputable def toComplexChar (χ : A →+ qmodZ) : AddChar A ℂ where
  toFun a := (expQmodZ (χ a)).toMul
  map_zero_eq_one' := by
    rw [map_zero]
    simp
  map_add_eq_mul' a b := by
    show (expQmodZ (χ (a+b))).toMul = (expQmodZ (χ a)).toMul * (expQmodZ (χ b)).toMul
    rw [map_add χ a b, map_add expQmodZ (χ a) (χ b), toMul_add]

/-- `toComplexChar` as an additive homomorphism. -/
noncomputable def toComplexCharHom : (A →+ qmodZ) →+ AddChar A ℂ where
  toFun := toComplexChar
  map_zero' := by
    ext a
    simp [toComplexChar]
  map_add' χ χ' := by
    ext a
    show (expQmodZ ((χ + χ') a)).toMul = (expQmodZ (χ a)).toMul * (expQmodZ (χ' a)).toMul
    rw [AddMonoidHom.add_apply, map_add expQmodZ (χ a) (χ' a), toMul_add]

theorem toComplexCharHom_injective : Function.Injective (toComplexCharHom (A := A)) := by
  intro χ χ' h
  ext a
  apply expQmodZ_injective
  have h2 : (toComplexChar χ) a = (toComplexChar χ') a := DFunLike.congr_fun h a
  exact Additive.toMul.injective (by simpa [toComplexChar] using h2)

/-- Every `ℂ`-valued character of a finite group is the exponential of a `ℚ/ℤ`-valued
character: its values are roots of unity. -/
theorem toComplexCharHom_surjective : Function.Surjective (toComplexCharHom (A := A)) := by
  intro ψ
  have hroot : ∀ a : A, ∃ q : qmodZ, expQmodZ q = Additive.ofMul (ψ a) := by
    intro a
    have hn : 0 < addOrderOf a := addOrderOf_pos a
    haveI : NeZero (addOrderOf a) := ⟨Nat.pos_iff_ne_zero.mp hn⟩
    have hpow : (ψ a) ^ (addOrderOf a) = 1 := by
      rw [← ψ.map_nsmul_eq_pow, addOrderOf_nsmul_eq_zero, ψ.map_zero_eq_one]
    have hne : ψ a ≠ 0 := by
      intro h0
      have h1 := ψ.map_add_eq_mul a (-a)
      rw [add_neg_cancel, ψ.map_zero_eq_one, h0, zero_mul] at h1
      exact one_ne_zero h1
    let u : Units ℂ := Units.mk0 (ψ a) hne
    have hmem : u ∈ rootsOfUnity (addOrderOf a) ℂ := by
      rw [_root_.mem_rootsOfUnity, Units.ext_iff]
      simpa [u] using hpow
    obtain ⟨i, hi, hieq⟩ := (Complex.mem_rootsOfUnity (addOrderOf a) u).mp hmem
    refine ⟨(((i : ℚ) / (addOrderOf a) : ℚ) : qmodZ), ?_⟩
    rw [expQmodZ_coe]
    congr 1
    have hval : (u : ℂ) = ψ a := rfl
    rw [← hval, ← hieq]
    congr 1
    push_cast
    ring
  let χfun : A → qmodZ := fun a => Classical.choose (hroot a)
  have hχ : ∀ a, expQmodZ (χfun a) = Additive.ofMul (ψ a) := fun a => Classical.choose_spec (hroot a)
  have hadd : ∀ a b, χfun (a + b) = χfun a + χfun b := by
    intro a b
    apply expQmodZ_injective
    rw [hχ (a+b), map_add expQmodZ (χfun a) (χfun b), hχ a, hχ b]
    exact congrArg Additive.ofMul (ψ.map_add_eq_mul a b)
  refine ⟨AddMonoidHom.mk' χfun hadd, ?_⟩
  ext a
  show (expQmodZ (χfun a)).toMul = ψ a
  rw [hχ a]
  simp

/-- **Pontryagin duality with `ℚ/ℤ` coefficients as a bridge to complex characters**:
for a finite abelian group `A`, the additive group of characters `A →+ ℚ/ℤ` is additively
equivalent to the group of `ℂ`-valued additive characters, via `χ ↦ exp (2 π i χ ·)`. -/
noncomputable def qmodZDualEquivComplex :
    (A →+ qmodZ) ≃+ AddChar A ℂ :=
  AddEquiv.ofBijective (toComplexCharHom (A := A))
    ⟨toComplexCharHom_injective, toComplexCharHom_surjective⟩

/-! ## The abelian case -/

/-- The double dual evaluation character attached to `Φ : Hom(A, ℚ/ℤ) →+ ℚ/ℤ`, transported to
`ℂ`-valued characters along `qmodZDualEquivComplex`. -/
noncomputable def etaOfComplex (Φ : (A →+ qmodZ) →+ qmodZ) : AddChar (AddChar A ℂ) ℂ :=
  { toFun ψ := (expQmodZ (Φ ((qmodZDualEquivComplex (A := A)).symm ψ))).toMul
    map_zero_eq_one' := by
      show (expQmodZ (Φ ((qmodZDualEquivComplex (A := A)).symm 0))).toMul = 1
      rw [map_zero, map_zero]
      simp
    map_add_eq_mul' ψ ψ' := by
      show (expQmodZ (Φ ((qmodZDualEquivComplex (A := A)).symm (ψ + ψ')))).toMul =
        (expQmodZ (Φ ((qmodZDualEquivComplex (A := A)).symm ψ))).toMul *
        (expQmodZ (Φ ((qmodZDualEquivComplex (A := A)).symm ψ'))).toMul
      rw [map_add (qmodZDualEquivComplex (A := A)).symm ψ ψ', map_add Φ _ _,
        map_add expQmodZ _ _, toMul_add] }

/-- **Pontryagin duality for a finite abelian group with `ℚ/ℤ` coefficients**: every additive map
on the character group is evaluation at an element. -/
theorem abelian_doubleDual_surjective {A : Type*} [AddCommGroup A] [Finite A]
    (Φ : (A →+ qmodZ) →+ qmodZ) : ∃ a : A, ∀ χ : A →+ qmodZ, Φ χ = χ a := by
  obtain ⟨a, ha⟩ := AddChar.doubleDualEmb_bijective.2 (etaOfComplex (A := A) Φ)
  refine ⟨a, fun χ => ?_⟩
  apply expQmodZ_injective
  apply Additive.toMul.injective
  have h1 : (expQmodZ (Φ χ)).toMul = etaOfComplex (A := A) Φ (qmodZDualEquivComplex (A := A) χ) := by
    show (expQmodZ (Φ χ)).toMul =
      (expQmodZ (Φ ((qmodZDualEquivComplex (A := A)).symm
        (qmodZDualEquivComplex (A := A) χ)))).toMul
    rw [AddEquiv.symm_apply_apply]
  have h2 : etaOfComplex (A := A) Φ (qmodZDualEquivComplex (A := A) χ) =
      (expQmodZ (χ a)).toMul := by
    rw [← ha, AddChar.doubleDualEmb_apply]
    rfl
  rw [h1, h2]

/-! ## Reduction to the abelianization -/

/-- Any `ℚ/ℤ`-valued character of a group factors through its abelianization. -/
theorem exists_abelianization_lift {Γ : Type*} [Group Γ] (χ : Additive Γ →+ qmodZ) :
    ∃ χ' : Additive (Abelianization Γ) →+ qmodZ,
      ∀ g : Γ, χ' (Additive.ofMul (Abelianization.of g)) = χ (Additive.ofMul g) := by
  let χm : Γ →* Multiplicative qmodZ :=
    { toFun := fun g => Multiplicative.ofAdd (χ (Additive.ofMul g))
      map_one' := by
        show Multiplicative.ofAdd (χ (Additive.ofMul (1:Γ))) = 1
        rw [show Additive.ofMul (1:Γ) = 0 from rfl, map_zero]
        rfl
      map_mul' := fun g h => by
        show Multiplicative.ofAdd (χ (Additive.ofMul (g*h))) =
          Multiplicative.ofAdd (χ (Additive.ofMul g)) * Multiplicative.ofAdd (χ (Additive.ofMul h))
        rw [show Additive.ofMul (g*h) = Additive.ofMul g + Additive.ofMul h from rfl, map_add]
        rfl }
  let χm' := Abelianization.lift χm
  refine ⟨{ toFun := fun a => Multiplicative.toAdd (χm' (Additive.toMul a))
            map_zero' := ?_
            map_add' := ?_ }, ?_⟩
  · show Multiplicative.toAdd (χm' (Additive.toMul (0 : Additive (Abelianization Γ)))) = 0
    rw [show Additive.toMul (0 : Additive (Abelianization Γ)) = 1 from rfl, map_one]
    rfl
  · intro a b
    show Multiplicative.toAdd (χm' (Additive.toMul (a + b))) =
      Multiplicative.toAdd (χm' (Additive.toMul a)) + Multiplicative.toAdd (χm' (Additive.toMul b))
    rw [toMul_add, map_mul, toAdd_mul]
  · intro g
    show Multiplicative.toAdd
      (χm' (Additive.toMul (Additive.ofMul (Abelianization.of g)))) = χ (Additive.ofMul g)
    rw [show Additive.toMul (Additive.ofMul (Abelianization.of g)) = Abelianization.of g from rfl,
      Abelianization.lift_apply_of]
    rfl

/-! ## The main theorem -/

theorem doubleDual_surjective {Γ : Type} [Group Γ] [Fintype Γ]
    (Φ : (Additive Γ →+ NK.NUV2.RouteC.qmodZ) →+ NK.NUV2.RouteC.qmodZ) :
    ∃ g : Γ, ∀ χ : Additive Γ →+ NK.NUV2.RouteC.qmodZ,
      Φ χ = χ (Additive.ofMul g) := by
  haveI : Finite Γ := Fintype.finite inferInstance
  let q : Additive Γ →+ Additive (Abelianization Γ) :=
    { toFun := fun x => Additive.ofMul (Abelianization.of (Additive.toMul x))
      map_zero' := by simp
      map_add' := by intro x y; simp [toMul_add] }
  let ΦA : (Additive (Abelianization Γ) →+ qmodZ) →+ qmodZ :=
    { toFun := fun ψ => Φ (ψ.comp q)
      map_zero' := by simp
      map_add' := fun ψ ψ' => by
        show Φ ((ψ + ψ').comp q) = Φ (ψ.comp q) + Φ (ψ'.comp q)
        rw [AddMonoidHom.add_comp, map_add] }
  obtain ⟨a, ha⟩ := abelian_doubleDual_surjective (A := Additive (Abelianization Γ)) ΦA
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (Additive.toMul a)
  refine ⟨g, fun χ => ?_⟩
  obtain ⟨χ', hχ'⟩ := exists_abelianization_lift χ
  have hcomp_fun : ∀ x : Additive Γ, χ' (q x) = χ x := by
    intro x
    have h := hχ' (Additive.toMul x)
    simpa [q] using h
  have hcomp : χ'.comp q = χ := AddMonoidHom.ext hcomp_fun
  have hga : q (Additive.ofMul g) = a := by
    show Additive.ofMul (Abelianization.of g) = a
    rw [show Abelianization.of g = Additive.toMul a from hg]
    exact ofMul_toMul a
  calc Φ χ = ΦA χ' := by
        show Φ χ = Φ (χ'.comp q)
        rw [hcomp]
    _ = χ' a := ha χ'
    _ = χ (Additive.ofMul g) := by rw [← hga, hcomp_fun]

end NK.NUV2.RouteC
