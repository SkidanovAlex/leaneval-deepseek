/-
Copyright (c) 2024. All rights reserved.

# Suzuki 2-groups: the fourth-power map on a class-two subgroup

Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), §2--§3.

Let `A ≤ C` be subgroups of a group, with `C` centralising `A`, `C² ⊆ A`, `[C,C] = A²` and
`A` of exponent dividing `4`.  Then `C` has class two, all commutators of `C` lie in the
abelian group `A`, and the fourth-power map `x ↦ x⁴` is a homomorphism `C → A²`: indeed for
`x, y ∈ C` we have `(xy)² = [y,x]·x²·y²` and `[y,x]² = 1` (every element of `A²` is an
involution, `A` having exponent `4`), so `(xy)⁴ = x⁴y⁴`.

The kernel of this homomorphism is described by the equivalence
`f x = f y ↔ x y⁻¹ ∈ f.ker`, which is the form used in
`Submission/Work/Higman/xi_alt_pairing_false.lean`.
-/

import Mathlib
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.OmegaAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- **The fourth-power map of a class-two subgroup covering `A ^ (2)`.**  If `A ≤ C`,
`C` centralises `A`, `C ^ (2) ≤ A`, `⁅C, C⁆ = A ^ (2)` and `A` has exponent dividing `4`, then
`x ↦ x ^ 4` is a homomorphism `↥C →* ↥(A ^ (2))`, and two elements have the same image exactly
when they are congruent modulo its kernel. -/
theorem exists_pow_four_hom {P : Type} [Group P] [Finite P] {A C : Subgroup P}
    (hAC : A ≤ C) (hZ : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c)
    (hC2 : Work.Higman.powSub C 2 ≤ A)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    (hexp : ∀ a ∈ A, a ^ 4 = 1) :
    ∃ f : ↥C →* ↥(Work.Higman.powSub A 2),
      (∀ x : ↥C, (f x : P) = (x : P) ^ 4) ∧
      (∀ x y : ↥C, f x = f y ↔ (x : P) * (y : P)⁻¹ ∈ f.ker.map C.subtype) := by
  have hab : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv => (hZ v (hAC hv) u hu).symm
  -- every element of `A²` is an involution
  have hVsq : ∀ v ∈ powSub A 2, v ^ 2 = 1 := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := (mem_powSub_iff hab).mp hv
    rw [← pow_mul, show 2 * 2 = 4 from rfl]
    exact hexp a ha
  -- the fourth power is multiplicative on `C`
  have hpow4 : ∀ x y : P, x ∈ C → y ∈ C → (x * y) ^ 4 = x ^ 4 * y ^ 4 := by
    intro x y hx hy
    have hcom : ⁅y, x⁆ ∈ A := by
      have h1 : ⁅y, x⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hy hx
      rw [hCd] at h1
      exact powSub_le (by norm_num) h1
    have hx2 : x ^ 2 ∈ A := hC2 (pow_mem_powSub (n := 2) hx)
    have hy2 : y ^ 2 ∈ A := hC2 (pow_mem_powSub (n := 2) hy)
    have hunfold : y * x = ⁅y, x⁆ * x * y := by
      rw [← mul_mul_inv_eq_commutator_mul y x]; group
    have hcx : x * ⁅y, x⁆ = ⁅y, x⁆ * x := hZ x hx ⁅y, x⁆ hcom
    have hfinal : x * ⁅y, x⁆ * x * y * y = ⁅y, x⁆ * (x ^ 2 * y ^ 2) := by
      rw [hcx, pow_two, pow_two]
      group
    have hsq : (x * y) ^ 2 = ⁅y, x⁆ * (x ^ 2 * y ^ 2) := by
      calc (x * y) ^ 2 = x * (y * x) * y := by rw [pow_two]; group
        _ = x * (⁅y, x⁆ * x * y) * y := by rw [hunfold]
        _ = x * ⁅y, x⁆ * x * y * y := by group
        _ = ⁅y, x⁆ * (x ^ 2 * y ^ 2) := hfinal
    have hc2 : ⁅y, x⁆ ^ 2 = 1 :=
      hVsq _ (by rw [← hCd]; exact Subgroup.commutator_mem_commutator hy hx)
    calc (x * y) ^ 4 = ((x * y) ^ 2) ^ 2 := by rw [← pow_mul]
      _ = (⁅y, x⁆ * (x ^ 2 * y ^ 2)) ^ 2 := by rw [hsq]
      _ = ⁅y, x⁆ ^ 2 * (x ^ 2 * y ^ 2) ^ 2 :=
            Commute.mul_pow (hab _ hcom _ (A.mul_mem hx2 hy2)) 2
      _ = x ^ 4 * y ^ 4 := by
            rw [hc2, one_mul, Commute.mul_pow (hab _ hx2 _ hy2) 2]
            simp only [← pow_mul, Nat.reduceMul]
  have hmem : ∀ x : P, x ∈ C → x ^ 4 ∈ powSub A 2 := by
    intro x hx
    have h1 : x ^ 2 ∈ A := hC2 (pow_mem_powSub (n := 2) hx)
    have h2 : (x ^ 2) ^ 2 ∈ powSub A 2 := pow_mem_powSub (n := 2) h1
    simpa [← pow_mul] using h2
  let f : ↥C →* ↥(powSub A 2) :=
    { toFun := fun x => ⟨(x : P) ^ 4, hmem x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (hpow4 x y x.2 y.2) }
  refine ⟨f, fun x => rfl, ?_⟩
  intro x y
  constructor
  · intro hxy
    refine Subgroup.mem_map.mpr ⟨⟨(x : P) * (y : P)⁻¹, C.mul_mem x.2 (C.inv_mem y.2)⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    have hzeq : (⟨(x : P) * (y : P)⁻¹, C.mul_mem x.2 (C.inv_mem y.2)⟩ : ↥C) = x * y⁻¹ := by
      apply Subtype.ext
      simp
    rw [hzeq, map_mul, map_inv, hxy, mul_inv_cancel]
  · rintro ⟨z, hz, hzx⟩
    have hfz : f z = 1 := MonoidHom.mem_ker.mp hz
    have hzeq : z = x * y⁻¹ := by
      apply Subtype.ext
      simpa using hzx
    rw [hzeq, map_mul, map_inv] at hfz
    have h2 := congrArg (fun w => w * f y) hfz
    simpa using h2

end Work.Higman
