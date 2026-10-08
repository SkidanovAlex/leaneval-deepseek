/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The order of `hypTorus F d` when `d` is a square

For `d = μ ^ 2` with `μ ≠ 0` in a finite field `F` of odd characteristic, the group
`hypTorus F d = {!![a, d*b; b, a] | a² - d·b² = 1}` has exactly `q - 1` elements, `q = |F|`:
`(a, b) ↦ a + μ·b` is a bijection from the conic `a² - d·b² = 1` onto `Fˣ` (with inverse
`u ↦ ((u + u⁻¹)/2, (u - u⁻¹)/(2μ))`), and the matrices `!![a, d*b; b, a]` are determined by
`(a, b)`.  The companion statement for `d` a non-square is `Work.L2F.Conic.hypTorus_card`.
-/
import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Conic.mem_hypTorus

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Conic

variable {F : Type*} [Field F]

/-- The matrix `!![a, d*b; b, a]` of the conic `a² - d b² = 1`, as an element of `SL(2,F)`. -/
private def matOfConic (d : F) (p : F × F) (hp : p.1 ^ 2 - d * p.2 ^ 2 = 1) :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![p.1, d * p.2; p.2, p.1], by
    rw [Matrix.det_fin_two_of]
    linear_combination hp⟩

private lemma matOfConic_mem (d : F) (p : F × F) (hp : p.1 ^ 2 - d * p.2 ^ 2 = 1) :
    matOfConic d p hp ∈ Work.L2F.hypTorusSet F d :=
  ⟨p.1, p.2, hp, rfl⟩

private lemma matOfConic_inj (d : F) (p q : F × F) (hp : p.1 ^ 2 - d * p.2 ^ 2 = 1)
    (hq : q.1 ^ 2 - d * q.2 ^ 2 = 1) (heq : matOfConic d p hp = matOfConic d q hq) : p = q := by
  have hmat := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) F =>
    (x : Matrix (Fin 2) (Fin 2) F)) heq
  have h0 := congrFun (congrFun hmat 0) 0
  have h1 := congrFun (congrFun hmat 1) 0
  simp only [matOfConic, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one] at h0 h1
  exact Prod.ext h0 h1

private lemma matOfConic_surj (d : F) (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : x ∈ Work.L2F.hypTorus F d) :
    ∃ p : F × F, ∃ hp : p.1 ^ 2 - d * p.2 ^ 2 = 1, matOfConic d p hp = x := by
  obtain ⟨a, b, hab, hx'⟩ := (mem_hypTorus F d x).mp hx
  exact ⟨(a, b), hab, Subtype.ext hx'.symm⟩

/-- `hypTorus F d` and the conic `a² - d·b² = 1` have the same number of elements. -/
private theorem ncard_hypTorus_eq_conic (d : F) :
    (Work.L2F.hypTorus F d : Set (Matrix.SpecialLinearGroup (Fin 2) F)).ncard =
      {p : F × F | p.1 ^ 2 - d * p.2 ^ 2 = 1}.ncard :=
  (Set.ncard_congr (s := {p : F × F | p.1 ^ 2 - d * p.2 ^ 2 = 1})
    (t := (Work.L2F.hypTorus F d : Set (Matrix.SpecialLinearGroup (Fin 2) F)))
    (fun p hp => matOfConic d p hp)
    (fun p hp => Subgroup.subset_closure (matOfConic_mem d p hp))
    (fun p q hp hq heq => matOfConic_inj d p q hp hq heq)
    (fun x hx => matOfConic_surj d x hx)).symm

/-- The conic `a² - d·b² = 1` for `d = μ²`, `μ ≠ 0`, has `q - 1` points: `(a, b) ↦ a + μ·b` is a
bijection onto `Fˣ`. -/
private theorem ncard_conic_sq [Fintype F] (h2 : (2 : F) ≠ 0) (d μ : F) (hμ : μ ≠ 0)
    (hd : d = μ ^ 2) :
    {p : F × F | p.1 ^ 2 - d * p.2 ^ 2 = 1}.ncard = Nat.card F - 1 := by
  have h2μ : 2 * μ ≠ 0 := mul_ne_zero h2 hμ
  have hsquare : ∀ a b : F, (a + μ * b) * (a - μ * b) = a ^ 2 - d * b ^ 2 := by
    intro a b
    rw [hd]
    ring
  have key_plus : ∀ u : Fˣ, ((u : F) + (u : F)⁻¹) / 2 + μ * (((u : F) - (u : F)⁻¹) / (2 * μ))
      = (u : F) := by
    intro u
    field_simp
    ring
  have key_minus : ∀ u : Fˣ, ((u : F) + (u : F)⁻¹) / 2 - μ * (((u : F) - (u : F)⁻¹) / (2 * μ))
      = (u : F)⁻¹ := by
    intro u
    field_simp
    ring
  have key_mem : ∀ u : Fˣ,
      (((u : F) + (u : F)⁻¹) / 2) ^ 2 - d * ((((u : F) - (u : F)⁻¹) / (2 * μ))) ^ 2 = 1 := by
    intro u
    rw [← hsquare]
    rw [key_plus, key_minus]
    simp
  let toUnit : ∀ (p : F × F), p.1 ^ 2 - d * p.2 ^ 2 = 1 → Fˣ :=
    fun p hp => Units.mk (p.1 + μ * p.2) (p.1 - μ * p.2) (by rw [hsquare, hp])
      (by rw [mul_comm, hsquare, hp])
  have coe_toUnit : ∀ (p : F × F) (hp : p.1 ^ 2 - d * p.2 ^ 2 = 1),
      ((toUnit p hp : Fˣ) : F) = p.1 + μ * p.2 := fun p hp => rfl
  have coe_inv_toUnit : ∀ (p : F × F) (hp : p.1 ^ 2 - d * p.2 ^ 2 = 1),
      (((toUnit p hp)⁻¹ : Fˣ) : F) = p.1 - μ * p.2 := by
    intro p hp
    show ((↑((Units.mk (p.1 + μ * p.2) (p.1 - μ * p.2) _ _)⁻¹)) : F) = p.1 - μ * p.2
    rw [Units.inv_mk]
  have psi_toUnit : ∀ (p : F × F) (hp : p.1 ^ 2 - d * p.2 ^ 2 = 1),
      (((toUnit p hp : Fˣ) : F) + ((toUnit p hp)⁻¹ : Fˣ)) / 2
        = p.1 := by
    intro p hp
    rw [coe_toUnit p hp, coe_inv_toUnit p hp]
    field_simp
    ring
  have psi_toUnit' : ∀ (p : F × F) (hp : p.1 ^ 2 - d * p.2 ^ 2 = 1),
      (((toUnit p hp : Fˣ) : F) - ((toUnit p hp)⁻¹ : Fˣ)) / (2 * μ) = p.2 := by
    intro p hp
    rw [coe_toUnit p hp, coe_inv_toUnit p hp]
    field_simp
    ring
  have key : {p : F × F | p.1 ^ 2 - d * p.2 ^ 2 = 1}.ncard = (Set.univ : Set Fˣ).ncard := by
    apply Set.ncard_congr (fun p hp => toUnit p hp)
    · intro p hp
      exact Set.mem_univ _
    · intro p q hp hq heq
      have e1 : (((toUnit p hp : Fˣ) : F) + ((toUnit p hp)⁻¹ : Fˣ)) / 2
          = (((toUnit q hq : Fˣ) : F) + ((toUnit q hq)⁻¹ : Fˣ)) / 2 := by rw [heq]
      have e2 : (((toUnit p hp : Fˣ) : F) - ((toUnit p hp)⁻¹ : Fˣ)) / (2 * μ)
          = (((toUnit q hq : Fˣ) : F) - ((toUnit q hq)⁻¹ : Fˣ)) / (2 * μ) := by rw [heq]
      rw [psi_toUnit p hp, psi_toUnit q hq] at e1
      rw [psi_toUnit' p hp, psi_toUnit' q hq] at e2
      exact Prod.ext e1 e2
    · intro u hu
      refine ⟨(((u : F) + (u : F)⁻¹) / 2, ((u : F) - (u : F)⁻¹) / (2 * μ)), key_mem u, ?_⟩
      exact Units.ext (key_plus u)
  rw [key, Set.ncard_univ, Nat.card_units]

/-- **The order of the torus `hypTorus F d` when `d` is a square.**  For `d = μ ^ 2` with
`μ ≠ 0` in a finite field `F` of odd characteristic, `hypTorus F d = {!![a, d*b; b, a] | a² - d·b² =
1}` has exactly `q - 1` elements, `q = |F|` (the companion statement for `d` a non-square is
`Work.L2F.Conic.hypTorus_card`, giving `q + 1`). -/
theorem hypTorus_card_sq (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) (d μ : F)
    (hμ : μ ≠ 0) (hd : d = μ ^ 2) :
    Nat.card (Work.L2F.hypTorus F d) = Nat.card F - 1 := by
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, ncard_hypTorus_eq_conic,
    ncard_conic_sq h2 d μ hμ hd]

end Work.L2F.Conic
