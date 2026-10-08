import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_basic
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_index_zpowers_tau
import Submission.Work.BrauerSuzuki.Quaternion.rho_mul_pow_order
import Submission.Work.BrauerSuzuki.Quaternion.coset_cover
import Submission.Work.BrauerSuzuki.Quaternion.I_pow_add
import Submission.Work.BrauerSuzuki.Quaternion.tau_zpow_mem_zpowers_two_four
import Submission.Work.CharCore.exists_irr_of_monoidHom
import Submission.Work.CharCore.vchar_norm_one
import Submission.Work.Induction.isVChar_indFun
import Submission.Work.Induction.indFun_apply_one
import Submission.Work.Induction.indFun_apply_eq_zero
import Submission.Work.Clifford.clifford_induction_mem_Irr
import Submission.Work.Clifford.Orbit

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The characters of a generalized quaternion group: setup

Let `P = ⟨τ, ρ⟩` be a generalized quaternion group in Dade's normal form
(`Work.BrauerSuzuki.GenQuaternionData`), so `τ` has order `2 ^ n` with `n ≥ 2`,
`ρ τ ρ⁻¹ = τ⁻¹` and `ρ ^ 2 = τ ^ (2 ^ (n-1))`.

This file fixes the notation and the two characters used in
`Work.BrauerSuzuki.Quaternion.characters`:

* `tauSub d = ⟨τ⟩`, the cyclic subgroup of index two (`tauSub_index`), which is normal
  (`tauSub_normal`); every element of `P` outside it is `ρ * h` with `h ∈ ⟨τ⟩`
  (`eq_rho_mul_of_notMem`);
* `signHom d : P →* ℂˣ`, the non-trivial linear character of the quotient `P / ⟨τ⟩`
  (from `signHom_index_two`), with `signFun d x = 1` on `⟨τ⟩` and `-1` off it;
* `tauHom d : ↥⟨τ⟩ →* ℂˣ`, the linear character of the cyclic group `⟨τ⟩` with
  `τ ↦ I` (`Iunit = √-1`), and `lamFun d = (tauHom d · : ℂ)`, the corresponding
  one-dimensional character of `⟨τ⟩` (`lamFun d (τ ^ i) = I ^ i`);
* `th = indFun ⟨τ⟩ (lamFun d)`, the induced character, which is irreducible
  (`indFun_lamFun_mem_Irr`); its values at elements of `⟨τ⟩` are
  `lamFun d x + lamFun d x⁻¹` (`indFun_lamFun_apply_mem`) and it vanishes off `⟨τ⟩`
  (`indFun_lamFun_apply_notMem`).

The facts recorded here are exactly those needed to check the character values in
`Work.BrauerSuzuki.Quaternion.characters`.
-/

noncomputable section

open Classical

namespace Work.BrauerSuzuki.Quaternion

variable {P : Type*} [Group P] [Fintype P]

/-! ## The cyclic subgroup `⟨τ⟩` -/

/-- The cyclic subgroup `⟨τ⟩` of a generalized quaternion group. -/
abbrev tauSub (d : GenQuaternionData P) : Subgroup P := Subgroup.zpowers d.tau

@[simp] theorem mem_tauSub {d : GenQuaternionData P} {x : P} :
    x ∈ tauSub d ↔ x ∈ Subgroup.zpowers d.tau := Iff.rfl

/-- `⟨τ⟩` has index two in `P`. -/
theorem tauSub_index (d : GenQuaternionData P) : (tauSub d).index = 2 :=
  genQuaternionData_index_zpowers_tau P d

instance tauSub_normal (d : GenQuaternionData P) : (tauSub d).Normal :=
  Subgroup.normal_of_index_eq_two (tauSub_index d)

/-- `ρ ∉ ⟨τ⟩`. -/
theorem rho_notMem_tauSub (d : GenQuaternionData P) : d.rho ∉ tauSub d :=
  genQuaternionData_rho_notMem_zpowers_tau d

/-- `P` has an element outside `⟨τ⟩` (namely `ρ`). -/
theorem exists_notMem_tauSub (d : GenQuaternionData P) : ∃ x : P, x ∉ tauSub d :=
  ⟨d.rho, rho_notMem_tauSub d⟩

/-- Every element outside `⟨τ⟩` is of the form `ρ * h` with `h ∈ ⟨τ⟩`: the two cosets of
`⟨τ⟩` are `⟨τ⟩` and `ρ ⟨τ⟩`. -/
theorem eq_rho_mul_of_notMem (d : GenQuaternionData P) {g : P} (hg : g ∉ tauSub d) :
    ∃ h ∈ tauSub d, g = d.rho * h := by
  rcases coset_cover d g with h | ⟨h, hh, hgh⟩
  · exact absurd h hg
  · exact ⟨h, hh, hgh⟩

/-- The generator `τ`, viewed as an element of `⟨τ⟩`. -/
def genTau (d : GenQuaternionData P) : ↥(tauSub d) :=
  ⟨d.tau, Subgroup.mem_zpowers d.tau⟩

@[simp] theorem genTau_val (d : GenQuaternionData P) : ((genTau d : ↥(tauSub d)) : P) = d.tau :=
  rfl

theorem genTau_order (d : GenQuaternionData P) : orderOf (genTau d) = 2 ^ d.n := by
  rw [← Subgroup.orderOf_coe (genTau d)]
  exact d.tau_order

/-- `genTau d` generates the subgroup `⟨τ⟩`. -/
theorem mem_zpowers_genTau (d : GenQuaternionData P) :
    ∀ x : ↥(tauSub d), x ∈ Subgroup.zpowers (genTau d) := by
  intro x
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow, genTau_val, hk])⟩

/-- `τ ^ i` as an element of `⟨τ⟩` is `(genTau d) ^ i`. -/
theorem genTau_zpow (d : GenQuaternionData P) (i : ℤ) :
    (genTau d) ^ i
      = ⟨d.tau ^ i, Subgroup.zpow_mem (Subgroup.zpowers d.tau) (Subgroup.mem_zpowers d.tau) i⟩ :=
  Subtype.ext (by simp [Subgroup.coe_zpow])

/-! ## The character `τ ↦ I` of `⟨τ⟩` -/

/-- `I = √-1` as a unit of `ℂ`. -/
def Iunit : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero

@[simp] theorem Iunit_val : ((Iunit : ℂˣ) : ℂ) = Complex.I :=
  Units.val_mk0 Complex.I_ne_zero

theorem Iunit_pow_four : Iunit ^ 4 = 1 := by
  ext
  simp [Iunit, Complex.I_pow_four]

theorem Iunit_zpow_val (i : ℤ) : ((Iunit ^ i : ℂˣ) : ℂ) = Complex.I ^ i := by
  simpa using map_zpow (Units.coeHom ℂ) Iunit i

/-- `orderOf Iunit = 4` divides `orderOf τ = 2 ^ d.n`, since `d.n ≥ 2`. -/
theorem orderOf_Iunit_dvd (d : GenQuaternionData P) : orderOf Iunit ∣ orderOf (genTau d) := by
  rw [genTau_order, orderOf_dvd_iff_pow_eq_one]
  have hn : 2 ≤ d.n := d.hn
  obtain ⟨m, hm⟩ : ∃ m, d.n = m + 2 := ⟨d.n - 2, by omega⟩
  have hpow : 2 ^ (m + 2) = 4 * 2 ^ m := by
    rw [pow_add]; ring
  rw [hm, hpow, pow_mul, Iunit_pow_four, one_pow]

/-- The linear character of the cyclic group `⟨τ⟩` sending `τ` to `I`. -/
def tauHom (d : GenQuaternionData P) : ↥(tauSub d) →* ℂˣ :=
  monoidHomOfForallMemZpowers (mem_zpowers_genTau d) (orderOf_Iunit_dvd d)

@[simp] theorem tauHom_genTau (d : GenQuaternionData P) : tauHom d (genTau d) = Iunit :=
  monoidHomOfForallMemZpowers_apply_gen (mem_zpowers_genTau d) (orderOf_Iunit_dvd d)

theorem tauHom_genTau_zpow (d : GenQuaternionData P) (i : ℤ) :
    tauHom d ((genTau d) ^ i) = Iunit ^ i := by
  rw [map_zpow, tauHom_genTau]

/-- The one-dimensional character of `⟨τ⟩` with `λ (τ ^ i) = I ^ i`, as a function
with values in `ℂ`. -/
def lamFun (d : GenQuaternionData P) : ↥(tauSub d) → ℂ := fun x => (tauHom d x : ℂ)

theorem lamFun_apply (d : GenQuaternionData P) (x : ↥(tauSub d)) :
    lamFun d x = (tauHom d x : ℂ) := rfl

/-- `lamFun d` is an irreducible character of `⟨τ⟩`. -/
theorem lamFun_mem_Irr (d : GenQuaternionData P) : lamFun d ∈ CharCore.Irr ↥(tauSub d) := by
  obtain ⟨χ, hχ, hval⟩ := CharCore.exists_irr_of_monoidHom (tauHom d)
  rw [show lamFun d = χ from funext fun x => (hval x).symm]
  exact hχ

/-- `lamFun d` is an irreducible character in the sense of `Work.Clifford`. -/
theorem lamFun_mem_CliffordIrr (d : GenQuaternionData P) :
    lamFun d ∈ Work.Clifford.Irr ↥(tauSub d) :=
  (Work.Clifford.mem_Irr_charCore_iff).mpr (lamFun_mem_Irr d)

@[simp] theorem lamFun_one (d : GenQuaternionData P) : lamFun d 1 = 1 := by
  show ((tauHom d 1 : ℂˣ) : ℂ) = 1
  simp

theorem lamFun_inv (d : GenQuaternionData P) (x : ↥(tauSub d)) :
    lamFun d x⁻¹ = (lamFun d x)⁻¹ := by
  show ((tauHom d x⁻¹ : ℂˣ) : ℂ) = (((tauHom d x : ℂˣ) : ℂ))⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val]

/-- `lamFun d ((genTau d) ^ i) = I ^ i`. -/
theorem lamFun_genTau_zpow (d : GenQuaternionData P) (i : ℤ) :
    lamFun d ((genTau d) ^ i) = Complex.I ^ i := by
  show ((tauHom d ((genTau d) ^ i) : ℂˣ) : ℂ) = Complex.I ^ i
  rw [tauHom_genTau_zpow, Iunit_zpow_val]

/-- The value of `λ` at `τ ^ i`. -/
theorem lamFun_tau_zpow (d : GenQuaternionData P) (i : ℤ) :
    lamFun d ⟨d.tau ^ i,
      Subgroup.zpow_mem (Subgroup.zpowers d.tau) (Subgroup.mem_zpowers d.tau) i⟩
      = Complex.I ^ i := by
  rw [← genTau_zpow d i, lamFun_genTau_zpow]

/-- `λ` is constant on conjugacy classes of `⟨τ⟩` (the target `ℂˣ` is commutative). -/
theorem lamFun_conj (d : GenQuaternionData P) (y x : ↥(tauSub d)) :
    lamFun d (y * x * y⁻¹) = lamFun d x := by
  have h : tauHom d (y * x * y⁻¹) = tauHom d x := by
    rw [map_mul, map_mul, map_inv]
    calc tauHom d y * tauHom d x * (tauHom d y)⁻¹
        = (tauHom d x * tauHom d y) * (tauHom d y)⁻¹ := by
          rw [mul_comm (tauHom d y) (tauHom d x)]
      _ = tauHom d x := by rw [mul_assoc, mul_inv_cancel, mul_one]
  exact congrArg (fun u : ℂˣ => (u : ℂ)) h

/-- `λ` is a class function. -/
theorem lamFun_isClassFun (d : GenQuaternionData P) : CharCore.IsClassFun (lamFun d) :=
  fun g h => lamFun_conj d h g

/-! ## Conjugation by `ρ` on `⟨τ⟩` -/

/-- The conjugate of `x ∈ ⟨τ⟩` by `ρ`, as an element of `⟨τ⟩`; it equals `x⁻¹`. -/
abbrev rhoConj (d : GenQuaternionData P) (x : ↥(tauSub d)) : ↥(tauSub d) :=
  ⟨d.rho * (x : P) * d.rho⁻¹,
    (genQuaternionData_rho_conj_mem_inv d x.2).symm ▸ Subgroup.inv_mem _ x.2⟩

theorem rhoConj_val (d : GenQuaternionData P) (x : ↥(tauSub d)) :
    ((rhoConj d x : ↥(tauSub d)) : P) = (x⁻¹ : ↥(tauSub d)) :=
  genQuaternionData_rho_conj_mem_inv d x.2

/-- Conjugation by `ρ` inverts the value of `λ`. -/
theorem lamFun_rhoConj (d : GenQuaternionData P) (x : ↥(tauSub d)) :
    lamFun d (rhoConj d x) = lamFun d x⁻¹ := by
  have h : rhoConj d x = x⁻¹ := Subtype.ext (rhoConj_val d x)
  rw [h]

/-- The conjugate of `τ` by `ρ` is `τ⁻¹`, so `λ^ρ (τ) = I⁻¹ ≠ I = λ (τ)`: `λ` is not
invariant under `ρ`. -/
theorem conjFun_rho_lamFun_ne (d : GenQuaternionData P) :
    Work.Clifford.conjFun (tauSub d) d.rho (lamFun d) ≠ lamFun d := by
  intro h
  have h1 : Work.Clifford.conjFun (tauSub d) d.rho (lamFun d) (genTau d) = lamFun d (genTau d) := by
    rw [h]
  rw [Work.Clifford.conjFun_apply] at h1
  have h2 : lamFun d (rhoConj d (genTau d)) = lamFun d (genTau d) := h1
  rw [lamFun_rhoConj, lamFun_inv] at h2
  rw [show lamFun d (genTau d) = Complex.I from by
    simpa using lamFun_genTau_zpow d 1] at h2
  have h3 : (Complex.I : ℂ)⁻¹ = Complex.I := h2
  have h4 : (Complex.I : ℂ) ^ 2 = 1 := by
    have h5 := congrArg (fun z : ℂ => z * Complex.I) h3
    simp only [inv_mul_cancel₀ Complex.I_ne_zero] at h5
    simpa [sq] using h5.symm
  rw [Complex.I_sq] at h4
  norm_num at h4

/-- Elements of `⟨τ⟩` fix `λ` under conjugation. -/
theorem conjFun_mem_lamFun (d : GenQuaternionData P) {g : P} (hg : g ∈ tauSub d) :
    Work.Clifford.conjFun (tauSub d) g (lamFun d) = lamFun d :=
  Work.Clifford.conjFun_eq_self_of_isClassFun (lamFun_isClassFun d) hg

/-- The inertia group of `λ` is `⟨τ⟩` itself. -/
theorem inertia_lamFun (d : GenQuaternionData P) :
    Work.Clifford.inertia (tauSub d) (lamFun d) = tauSub d := by
  refine le_antisymm ?_ (Work.Clifford.le_inertia_of_mem_Irr (lamFun_mem_CliffordIrr d))
  intro g hg
  by_contra hgH
  obtain ⟨h, hh, rfl⟩ := eq_rho_mul_of_notMem d hgH
  -- `ρ * h = h⁻¹ * ρ`, and conjugation by `h⁻¹ ∈ ⟨τ⟩` fixes `λ`
  have hfac : d.rho * h = h⁻¹ * d.rho := by
    rw [← genQuaternionData_rho_conj_mem_inv d hh]
    group
  have h1 : Work.Clifford.conjFun (tauSub d) (d.rho * h) (lamFun d) = lamFun d := hg
  rw [hfac, Work.Clifford.conjFun_mul,
    conjFun_mem_lamFun d (Subgroup.inv_mem _ hh)] at h1
  exact conjFun_rho_lamFun_ne d h1

/-! ## The induced character `Ind_{⟨τ⟩}^P λ` -/

/-- The norm of the induced character `Ind λ` is one. -/
theorem cfInner_indFun_lamFun_self (d : GenQuaternionData P) :
    CharCore.cfInner (Work.Induction.indFun (tauSub d) (lamFun d))
      (Work.Induction.indFun (tauSub d) (lamFun d)) = 1 := by
  rw [Work.Clifford.cfInner_indFun_normal' (lamFun_mem_CliffordIrr d), inertia_lamFun]
  refine mul_inv_cancel₀ ?_
  rw [Nat.card_eq_fintype_card, Nat.cast_ne_zero]
  exact Fintype.card_ne_zero

/-- The degree of `Ind λ` is two (the index of `⟨τ⟩` times `λ 1`). -/
theorem indFun_lamFun_one (d : GenQuaternionData P) :
    Work.Induction.indFun (tauSub d) (lamFun d) 1 = 2 := by
  rw [Work.Induction.indFun_apply_one, tauSub_index d, lamFun_one]
  norm_num

end Work.BrauerSuzuki.Quaternion
