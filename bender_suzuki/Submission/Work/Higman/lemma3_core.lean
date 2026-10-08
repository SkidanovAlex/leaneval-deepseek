/-
Copyright (c) 2024. All rights reserved.

# Higman (1963), Lemma 3: the core machinery

This file isolates, at the top level, the machinery that Higman's Lemma 3 uses.

Let `A` be a `ξ`-invariant abelian normal subgroup of a Suzuki 2-group `P`.  For `u : P`:

* the *conjugation derivation* `Δ_u : A →* A`, `Δ_u(a) = u⁻¹ a u a⁻¹`, a group homomorphism
  whose values lie in `A ^ (2)` (unipotence of a Suzuki 2-group, `l3Delta_mem_powSub_two`);
* the operator identity `Δ_u(Δ_u a) = Δ_u(a)⁻²` when `u * u ∈ A` (`l3Delta_delta`);
* a *square root* `ν_u(a)` of `Δ_u(a)` inside `A` (`l3Sqrt_sq`), which is additive modulo
  `A ^ (2)` (`l3Sqrt_mul`), well defined modulo `A ^ (2)` (`l3Sqrt_wd`), and satisfies
  `ν_u(1) ∈ A ^ (2)` (`l3Sqrt_one`);
* `Δ_u` maps `A ^ (2)` into `A ^ (4)` (`l3Delta_le_four`).

The declarations are named `l3*` so as not to collide with the scratch material developed in
other files of this workspace.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.homogeneous_structure

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-! ## The conjugation derivation `Δ_u` -/

/-- `⁅u⁻¹, a⁆ = u⁻¹ * a * u * a⁻¹`. -/
theorem l3_commutator_inv_eq (u a : P) : ⁅u⁻¹, a⁆ = u⁻¹ * a * u * a⁻¹ := by
  rw [commutatorElement_def]
  group

/-- `Δ_u(a) = u⁻¹ * a * u * a⁻¹` lies in `A ^ (2)` (unipotence of a Suzuki 2-group). -/
theorem l3Delta_mem_powSub_two (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (u : P) (a : ↥A) : u⁻¹ * (a : P) * u * (a : P)⁻¹ ∈ powSub A 2 := by
  rw [← l3_commutator_inv_eq]
  exact commutator_mem_powSub_two h hA u⁻¹ (a : P) a.2

/-- The conjugation derivation `Δ_u`, as a homomorphism `A →* A`. -/
def l3Delta {A : Subgroup P} (hAn : A.Normal)
    (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (u : P) : ↥A →* ↥A where
  toFun a := ⟨u⁻¹ * (a : P) * u * (a : P)⁻¹, by
    have h1 : u⁻¹ * (a : P) * u ∈ A := by simpa using hAn.conj_mem (a : P) a.2 u⁻¹
    exact A.mul_mem h1 (A.inv_mem a.2)⟩
  map_one' := by
    apply Subtype.ext
    show u⁻¹ * (1 : P) * u * (1 : P)⁻¹ = 1
    group
  map_mul' x y := by
    apply Subtype.ext
    show u⁻¹ * ((x : P) * (y : P)) * u * ((x : P) * (y : P))⁻¹
      = (u⁻¹ * (x : P) * u * (x : P)⁻¹) * (u⁻¹ * (y : P) * u * (y : P)⁻¹)
    have hxb : u⁻¹ * (y : P) * u ∈ A := by simpa using hAn.conj_mem (y : P) y.2 u⁻¹
    have hmem : (u⁻¹ * (y : P) * u) * (y : P)⁻¹ ∈ A := A.mul_mem hxb (A.inv_mem y.2)
    calc u⁻¹ * ((x : P) * (y : P)) * u * ((x : P) * (y : P))⁻¹
        = (u⁻¹ * (x : P) * u) * (((u⁻¹ * (y : P) * u) * (y : P)⁻¹) * (x : P)⁻¹) := by
          rw [mul_inv_rev,
            show u⁻¹ * ((x : P) * (y : P)) * u = (u⁻¹ * (x : P) * u) * (u⁻¹ * (y : P) * u)
              from by group]
          group
      _ = (u⁻¹ * (x : P) * u) * ((x : P)⁻¹ * ((u⁻¹ * (y : P) * u) * (y : P)⁻¹)) := by
          rw [hAb _ hmem (x : P)⁻¹ (A.inv_mem x.2)]
      _ = (u⁻¹ * (x : P) * u * (x : P)⁻¹) * (u⁻¹ * (y : P) * u * (y : P)⁻¹) := by group

@[simp] theorem l3Delta_apply {A : Subgroup P} (hAn : A.Normal)
    (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (u : P) (a : ↥A) :
    ((l3Delta hAn hAb u a : ↥A) : P) = u⁻¹ * (a : P) * u * (a : P)⁻¹ := rfl

/-- The product formula for `Δ_u`, at the level of elements of `P`. -/
theorem l3Delta_mul_apply {A : Subgroup P} (hAn : A.Normal)
    (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (u : P) {a b : P} (ha : a ∈ A) (hb : b ∈ A) :
    u⁻¹ * (a * b) * u * (a * b)⁻¹
      = (u⁻¹ * a * u * a⁻¹) * (u⁻¹ * b * u * b⁻¹) := by
  have hxb : u⁻¹ * b * u ∈ A := by simpa using hAn.conj_mem b hb u⁻¹
  have hmem : (u⁻¹ * b * u) * b⁻¹ ∈ A := A.mul_mem hxb (A.inv_mem hb)
  calc u⁻¹ * (a * b) * u * (a * b)⁻¹
      = (u⁻¹ * a * u) * (((u⁻¹ * b * u) * b⁻¹) * a⁻¹) := by
        rw [mul_inv_rev,
          show u⁻¹ * (a * b) * u = (u⁻¹ * a * u) * (u⁻¹ * b * u) from by group]
        group
    _ = (u⁻¹ * a * u) * (a⁻¹ * ((u⁻¹ * b * u) * b⁻¹)) := by
        rw [hAb _ hmem a⁻¹ (A.inv_mem ha)]
    _ = (u⁻¹ * a * u * a⁻¹) * (u⁻¹ * b * u * b⁻¹) := by group

/-- `(z * z) * (z * z) = z ^ 4`. -/
theorem l3_four (z : P) : (z * z) * (z * z) = z ^ 4 := by
  rw [show z ^ 4 = z ^ (2 + 2) from by norm_num, pow_add, pow_two]

/-- Squares in an abelian subgroup multiply. -/
theorem l3_sq_mul {A : Subgroup P} (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {x y : P} (hx : x ∈ A) (hy : y ∈ A) : (x * y) * (x * y) = (x * x) * (y * y) := by
  have hcomm : Commute x y := hAb x hx y hy
  rw [← pow_two, hcomm.mul_pow, pow_two, pow_two]

/-- `a * Δ_u(a) = u⁻¹ * a * u`. -/
theorem l3Delta_mul_conj {A : Subgroup P} (hAn : A.Normal)
    (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (u : P) (a : ↥A) :
    (a : P) * ((l3Delta hAn hAb u a : ↥A) : P) = u⁻¹ * (a : P) * u := by
  have h1 : u⁻¹ * (a : P) * u ∈ A := by simpa using hAn.conj_mem (a : P) a.2 u⁻¹
  have hcomm : Commute (a : P) ((u⁻¹ * (a : P) * u) * (a : P)⁻¹) :=
    hAb (a : P) a.2 _ (A.mul_mem h1 (A.inv_mem a.2))
  rw [l3Delta_apply, hcomm.eq]
  group

/-- If `u * u ∈ A` then conjugation by `u` is an involution on `A`, hence
`Δ_u(Δ_u a) = Δ_u(a)⁻²` (the operator identity `(1 + Δ)² = 1`). -/
theorem l3Delta_delta (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    {u : P} (hu : u * u ∈ A) (a : ↥A) :
    ((l3Delta hA.normal hA.abelian u (l3Delta hA.normal hA.abelian u a) : ↥A) : P)
      = ((l3Delta hA.normal hA.abelian u a : ↥A) : P)⁻¹
        * ((l3Delta hA.normal hA.abelian u a : ↥A) : P)⁻¹ := by
  set d : P := ((l3Delta hA.normal hA.abelian u a : ↥A) : P) with hd
  have hφ : u⁻¹ * (a : P) * u = (a : P) * d := (l3Delta_mul_conj hA.normal hA.abelian u a).symm
  have hφd : d * ((l3Delta hA.normal hA.abelian u (l3Delta hA.normal hA.abelian u a) : ↥A) : P)
      = u⁻¹ * d * u :=
    l3Delta_mul_conj hA.normal hA.abelian u (l3Delta hA.normal hA.abelian u a)
  have hsq : u⁻¹ * (u⁻¹ * (a : P) * u) * u = (a : P) := by
    have happ : u⁻¹ * (u⁻¹ * (a : P) * u) * u = (u * u)⁻¹ * (a : P) * (u * u) := by group
    rw [happ]
    have hc : Commute ((u * u)⁻¹) (a : P) := hA.abelian _ (A.inv_mem hu) _ a.2
    rw [hc.eq]
    group
  have hsplit : u⁻¹ * ((a : P) * d) * u = (u⁻¹ * (a : P) * u) * (u⁻¹ * d * u) := by group
  have hcomb : (a : P) = (a : P) * (d * (d * ((l3Delta hA.normal hA.abelian u
      (l3Delta hA.normal hA.abelian u a) : ↥A) : P))) := by
    calc (a : P) = u⁻¹ * (u⁻¹ * (a : P) * u) * u := hsq.symm
      _ = u⁻¹ * ((a : P) * d) * u := by rw [hφ]
      _ = (u⁻¹ * (a : P) * u) * (u⁻¹ * d * u) := by rw [hsplit]
      _ = ((a : P) * d) * (d * ((l3Delta hA.normal hA.abelian u
            (l3Delta hA.normal hA.abelian u a) : ↥A) : P)) := by rw [hφ, hφd]
      _ = (a : P) * (d * (d * ((l3Delta hA.normal hA.abelian u
            (l3Delta hA.normal hA.abelian u a) : ↥A) : P))) := by group
  have hstuff : d * (d * ((l3Delta hA.normal hA.abelian u
      (l3Delta hA.normal hA.abelian u a) : ↥A) : P)) = 1 := by
    have h := congrArg (fun t : P => (a : P)⁻¹ * t) hcomb
    simpa [mul_assoc] using h.symm
  calc ((l3Delta hA.normal hA.abelian u (l3Delta hA.normal hA.abelian u a) : ↥A) : P)
      = (d * d)⁻¹ * (d * (d * ((l3Delta hA.normal hA.abelian u
          (l3Delta hA.normal hA.abelian u a) : ↥A) : P))) := by group
    _ = (d * d)⁻¹ * 1 := by rw [hstuff]
    _ = d⁻¹ * d⁻¹ := by group

/-! ## Elementary consequences of `x ^ 2 = 1 ↦ x ∈ A ^ (2)` -/

/-- Two elements of `A` with the same square differ by an element of `A ^ (2)`, provided every
element of `A` of order `≤ 2` is a square. -/
theorem l3_mul_inv_mem_powSub_two {A : Subgroup P}
    (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hA2 : ∀ x ∈ A, x * x = 1 → x ∈ powSub A 2)
    {x y : P} (hxA : x ∈ A) (hyA : y ∈ A) (h : x * x = y * y) :
    x * y⁻¹ ∈ powSub A 2 := by
  refine hA2 (x * y⁻¹) (A.mul_mem hxA (A.inv_mem hyA)) ?_
  have hc : Commute x y⁻¹ := hAb x hxA y⁻¹ (A.inv_mem hyA)
  have h2 : (x * y⁻¹) * (x * y⁻¹) = (x * x) * (y * y)⁻¹ := by
    rw [← pow_two, hc.mul_pow, show x ^ 2 = x * x from pow_two x, inv_pow, pow_two]
  rw [h2, h, mul_inv_cancel]

/-- If `x ∈ A` and `x * x ∈ A ^ (4)` then `x ∈ A ^ (2)`, provided `A [2] ⊆ A ^ (2)`. -/
theorem l3_mem_powSub_two_of_sq_mem_four {A : Subgroup P}
    (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hA2 : ∀ x ∈ A, x * x = 1 → x ∈ powSub A 2)
    {x : P} (hx : x ∈ A) (h : x * x ∈ powSub A 4) : x ∈ powSub A 2 := by
  obtain ⟨y, hyA, hy⟩ := (mem_powSub_iff hAb).mp h
  have hy2A : y * y ∈ A := A.mul_mem hyA hyA
  have hy2sq : y * y ∈ powSub A 2 := by
    rw [← pow_two]; exact pow_mem_powSub hyA
  have hyy : (y * y) * (y * y) = x * x := by
    rw [l3_four y, hy]
  have hc : Commute x (y * y)⁻¹ := hAb x hx (y * y)⁻¹ (A.inv_mem hy2A)
  have h1 : (x * (y * y)⁻¹) * (x * (y * y)⁻¹) = 1 := by
    have hsq : (x * (y * y)⁻¹) * (x * (y * y)⁻¹)
        = (x * x) * (((y * y) * (y * y))⁻¹) := by
      rw [← pow_two, hc.mul_pow, show x ^ 2 = x * x from pow_two x, inv_pow, pow_two]
    rw [hsq, hyy, mul_inv_cancel]
  have hmem2 : x * (y * y)⁻¹ ∈ powSub A 2 :=
    hA2 _ (A.mul_mem hx (A.inv_mem hy2A)) h1
  have hx_eq : x = (y * y) * (x * (y * y)⁻¹) := by
    rw [show (y * y) * (x * (y * y)⁻¹) = ((y * y) * x) * (y * y)⁻¹ from by group,
      hAb (y * y) hy2A x hx]
    group
  rw [hx_eq]
  exact Subgroup.mul_mem _ hy2sq hmem2

/-! ## The square root `ν_u` of `Δ_u` -/

/-- `Δ_u(a) ∈ A ^ (2)`, so every `a : ↥A` has a square root in `A` for `Δ_u`. -/
theorem l3_exists_sq_eq_delta (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (u : P) (a : ↥A) : ∃ x ∈ A, x * x = u⁻¹ * (a : P) * u * (a : P)⁻¹ := by
  obtain ⟨x, hxA, hx⟩ := (mem_powSub_iff hA.abelian).mp (l3Delta_mem_powSub_two h hA u a)
  exact ⟨x, hxA, by rwa [pow_two] at hx⟩

/-- The "square root of the conjugation derivation": `ν_u(a) ∈ A` with
`ν_u(a)² = Δ_u(a) = u⁻¹ a u a⁻¹`.  It is well defined modulo `A ^ (2)` (`l3Sqrt_wd`). -/
noncomputable def l3Sqrt (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (u : P) (a : ↥A) : ↥A :=
  ⟨Classical.choose (l3_exists_sq_eq_delta h hA u a),
    (Classical.choose_spec (l3_exists_sq_eq_delta h hA u a)).1⟩

theorem l3Sqrt_sq (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (u : P) (a : ↥A) :
    ((l3Sqrt h hA u a : ↥A) : P) * ((l3Sqrt h hA u a : ↥A) : P)
      = u⁻¹ * (a : P) * u * (a : P)⁻¹ :=
  (Classical.choose_spec (l3_exists_sq_eq_delta h hA u a)).2

/-- `ν_u` is additive modulo `A ^ (2)`. -/
theorem l3Sqrt_mul (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (hA2 : ∀ x ∈ A, x * x = 1 → x ∈ powSub A 2) (u : P) (a b : ↥A) :
    ((l3Sqrt h hA u (a * b) : ↥A) : P)
      * (((l3Sqrt h hA u a : ↥A) : P) * ((l3Sqrt h hA u b : ↥A) : P))⁻¹ ∈ powSub A 2 := by
  refine l3_mul_inv_mem_powSub_two hA.abelian hA2 (l3Sqrt h hA u (a * b)).2
    (A.mul_mem (l3Sqrt h hA u a).2 (l3Sqrt h hA u b).2) ?_
  rw [l3Sqrt_sq h hA u (a * b)]
  have hstep : (((l3Sqrt h hA u a : ↥A) : P) * ((l3Sqrt h hA u b : ↥A) : P))
      * (((l3Sqrt h hA u a : ↥A) : P) * ((l3Sqrt h hA u b : ↥A) : P))
      = (((l3Sqrt h hA u a : ↥A) : P) * ((l3Sqrt h hA u a : ↥A) : P))
        * (((l3Sqrt h hA u b : ↥A) : P) * ((l3Sqrt h hA u b : ↥A) : P)) :=
    l3_sq_mul hA.abelian (l3Sqrt h hA u a).2 (l3Sqrt h hA u b).2
  rw [hstep, l3Sqrt_sq h hA u a, l3Sqrt_sq h hA u b]
  exact l3Delta_mul_apply hA.normal hA.abelian u a.2 b.2

/-- The conjugation derivation maps `A ^ (2)` into `A ^ (4)`. -/
theorem l3Delta_le_four (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (u : P) {c : P} (hcA : c ∈ A) (hc2 : c ∈ powSub A 2) :
    u⁻¹ * c * u * c⁻¹ ∈ powSub A 4 := by
  obtain ⟨b, hbA, hb⟩ := (mem_powSub_iff hA.abelian).mp hc2
  obtain ⟨z, hzA, hz⟩ := (mem_powSub_iff hA.abelian).mp
    (l3Delta_mem_powSub_two h hA u ⟨b, hbA⟩)
  rw [← hb, show b ^ 2 = b * b from pow_two b,
    l3Delta_mul_apply hA.normal hA.abelian u hbA hbA, ← hz, pow_two, l3_four z]
  exact pow_mem_powSub hzA

/-- `ν_u` is well defined modulo `A ^ (2)`. -/
theorem l3Sqrt_wd (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (hA2 : ∀ x ∈ A, x * x = 1 → x ∈ powSub A 2) (u : P) (a : ↥A) {c : P}
    (hcA : c ∈ A) (hc2 : c ∈ powSub A 2) :
    ((l3Sqrt h hA u (a * ⟨c, hcA⟩) : ↥A) : P)
      * ((l3Sqrt h hA u a : ↥A) : P)⁻¹ ∈ powSub A 2 := by
  set x : P := ((l3Sqrt h hA u (a * ⟨c, hcA⟩) : ↥A) : P) with hxdef
  set y : P := ((l3Sqrt h hA u a : ↥A) : P) with hydef
  have hxA : x ∈ A := (l3Sqrt h hA u (a * ⟨c, hcA⟩)).2
  have hyA : y ∈ A := (l3Sqrt h hA u a).2
  have hx2 : x * x = u⁻¹ * ((a : P) * c) * u * ((a : P) * c)⁻¹ :=
    l3Sqrt_sq h hA u (a * ⟨c, hcA⟩)
  have hy2 : y * y = u⁻¹ * (a : P) * u * (a : P)⁻¹ := l3Sqrt_sq h hA u a
  refine l3_mem_powSub_two_of_sq_mem_four hA.abelian hA2
    (A.mul_mem hxA (A.inv_mem hyA)) ?_
  have hcomm : Commute x y⁻¹ := hA.abelian x hxA y⁻¹ (A.inv_mem hyA)
  have hsq : (x * y⁻¹) * (x * y⁻¹)
      = (u⁻¹ * ((a : P) * c) * u * ((a : P) * c)⁻¹)
        * (u⁻¹ * (a : P) * u * (a : P)⁻¹)⁻¹ := by
    rw [← pow_two, hcomm.mul_pow, show x ^ 2 = x * x from pow_two x,
      show (y⁻¹) ^ 2 = (y ^ 2)⁻¹ from inv_pow y 2, show y ^ 2 = y * y from pow_two y,
      hx2, hy2]
  rw [hsq, l3Delta_mul_apply hA.normal hA.abelian u a.2 hcA]
  have h1 : u⁻¹ * (a : P) * u * (a : P)⁻¹ ∈ A := (l3Delta hA.normal hA.abelian u a).2
  have h2 : u⁻¹ * c * u * c⁻¹ ∈ A := (l3Delta hA.normal hA.abelian u ⟨c, hcA⟩).2
  rw [(hA.abelian _ h1 _ h2), mul_assoc, mul_inv_cancel, mul_one]
  exact l3Delta_le_four h hA u hcA hc2

/-- `ν_u(1) ∈ A ^ (2)`. -/
theorem l3Sqrt_one (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (hA2 : ∀ x ∈ A, x * x = 1 → x ∈ powSub A 2) (u : P) :
    ((l3Sqrt h hA u 1 : ↥A) : P) ∈ powSub A 2 := by
  refine hA2 _ (l3Sqrt h hA u 1).2 ?_
  have h := l3Sqrt_sq h hA u (1 : ↥A)
  simpa only [Subgroup.coe_one, mul_one, inv_one, inv_mul_cancel] using h


/-! ## Restricting `ξ` to invariant subgroups -/

/-- The restriction of `ξ` to a `ξ`-invariant subgroup. -/
noncomputable def l3Axi (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A) : MulAut ↥A where
  toFun a := ⟨(h.xi : MulAut P) (a : P), by
    have h := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom a.2
    rwa [hAinv] at h⟩
  invFun a := ⟨(h.xi : MulAut P).symm (a : P),
    symm_mem_of_map_eq (h.xi : MulAut P) hAinv a.2⟩
  left_inv a := Subtype.ext (by simp)
  right_inv a := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

@[simp] theorem l3Axi_apply (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A) (a : ↥A) :
    ((l3Axi h hAinv a : ↥A) : P) = (h.xi : MulAut P) (a : P) := rfl

theorem l3Axi_pow_apply (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A) (k : ℕ) (a : ↥A) :
    (((l3Axi h hAinv) ^ k) a : P) = ((h.xi : MulAut P) ^ k) (a : P) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 : (((l3Axi h hAinv) ^ (k + 1)) a : P)
          = (h.xi : MulAut P) ((((l3Axi h hAinv) ^ k) a : ↥A) : P) := by
        rw [pow_succ', MulAut.mul_apply]
        rfl
      rw [h1, ih, pow_succ', MulAut.mul_apply]

/-- The restriction of `ξ` to a `ξ`-invariant subgroup `C`. -/
noncomputable def l3Cxi (h : IsSuzuki2Grp P) {C : Subgroup P}
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) : MulAut ↥C where
  toFun c := ⟨(h.xi : MulAut P) (c : P), by
    have h := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom c.2
    rwa [hCinv] at h⟩
  invFun c := ⟨(h.xi : MulAut P).symm (c : P),
    symm_mem_of_map_eq (h.xi : MulAut P) hCinv c.2⟩
  left_inv c := Subtype.ext (by simp)
  right_inv c := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

@[simp] theorem l3Cxi_apply (h : IsSuzuki2Grp P) {C : Subgroup P}
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) (c : ↥C) :
    ((l3Cxi h hCinv c : ↥C) : P) = (h.xi : MulAut P) (c : P) := rfl

/-! ## The quotient `A / A ^ (2)` -/

/-- `A ^ (2)` viewed as a subgroup of `A`. -/
def l3K (A : Subgroup P) : Subgroup ↥A := (powSub A 2).subgroupOf A

theorem l3K_mem {A : Subgroup P} {c : ↥A} : c ∈ l3K A ↔ (c : P) ∈ powSub A 2 :=
  Subgroup.mem_subgroupOf

/-- `A ^ (2)` is normal in `A` (it is the image of a normal subgroup of `P`). -/
instance l3K_normal_inst {A : Subgroup P} [hAn : A.Normal] : (l3K A).Normal := by
  refine Subgroup.Normal.mk (fun n hn g => ?_)
  rw [l3K_mem] at hn ⊢
  have hconj : A.map (MulAut.conj (g : P)).toMonoidHom = A :=
    Subgroup.normal_iff_map_conj_eq.mp hAn (g : P)
  have hmem : (MulAut.conj (g : P)) (n : P)
      ∈ (powSub A 2).map (MulAut.conj (g : P)).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hn
  rw [map_powSub (MulAut.conj (g : P)) hconj 2] at hmem
  simpa [MulAut.conj_apply] using hmem

/-- `ν_u` maps `A ^ (2)` into `A ^ (2)`. -/
theorem l3Sqrt_mem_of_mem (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (hA2 : ∀ x ∈ A, x * x = 1 → x ∈ powSub A 2) (u : P) {c : ↥A}
    (hc : (c : P) ∈ powSub A 2) : (l3Sqrt h hA u c : P) ∈ powSub A 2 := by
  have h2 : ((l3Sqrt h hA u ⟨(c : P), c.2⟩ : ↥A) : P) * (((l3Sqrt h hA u 1 : ↥A) : P))⁻¹
      ∈ powSub A 2 := by
    simpa only [one_mul] using l3Sqrt_wd h hA hA2 u (1 : ↥A) c.2 hc
  have h1 : ((l3Sqrt h hA u 1 : ↥A) : P) ∈ powSub A 2 := l3Sqrt_one h hA hA2 u
  have hmul := (powSub A 2).mul_mem h2 h1
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul

/-- `a ↦ ν_u(a)`, multiplicative modulo `A ^ (2)`. -/
theorem l3Sqrt_mul_mem (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (hA2 : ∀ x ∈ A, x * x = 1 → x ∈ powSub A 2) (u : P) (a b : ↥A) :
    (l3Sqrt h hA u (a * b))⁻¹ * (l3Sqrt h hA u a * l3Sqrt h hA u b) ∈ l3K A := by
  have hcomm : ∀ x y : ↥A, x * y = y * x := fun x y => Subtype.ext (hA.abelian x x.2 y y.2)
  have h1 : (l3Sqrt h hA u (a * b) * (l3Sqrt h hA u a * l3Sqrt h hA u b)⁻¹) ∈ l3K A := by
    rw [l3K_mem]
    simpa using l3Sqrt_mul h hA hA2 u a b
  have h2 : (l3Sqrt h hA u (a * b))⁻¹ * (l3Sqrt h hA u a * l3Sqrt h hA u b)
      = (l3Sqrt h hA u (a * b) * (l3Sqrt h hA u a * l3Sqrt h hA u b)⁻¹)⁻¹ := by
    rw [mul_inv_rev, inv_inv]
    exact (hcomm _ _).symm
  rw [h2]
  exact (l3K A).inv_mem h1

/-- The map `a ↦ ν_u(a)` as a monoid homomorphism `A → A / A ^ (2)`. -/
noncomputable def l3rhoFun (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (hA2 : ∀ x ∈ A, x * x = 1 → x ∈ powSub A 2) (u : P) [hAn : A.Normal] :
    ↥A →* ↥A ⧸ l3K A where
  toFun a := QuotientGroup.mk' (l3K A) (l3Sqrt h hA u a)
  map_one' := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, l3K_mem]
    exact l3Sqrt_one h hA hA2 u
  map_mul' a b := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      ← QuotientGroup.mk_mul, QuotientGroup.eq, l3K_mem]
    exact l3Sqrt_mul_mem h hA hA2 u a b

/-- **The map `ρ_u` on `A / A ^ (2)`.**  This is the operator whose values are supposed to be
idempotents in Higman's Lemma 3. -/
noncomputable def l3rho (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (hA2 : ∀ x ∈ A, x * x = 1 → x ∈ powSub A 2) (u : P) [hAn : A.Normal] :
    ↥A ⧸ l3K A →* ↥A ⧸ l3K A :=
  QuotientGroup.lift (l3K A) (l3rhoFun h hA hA2 u) (by
    intro c hc
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' (l3K A) (l3Sqrt h hA u c) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, l3K_mem]
    exact l3Sqrt_mem_of_mem h hA hA2 u ((l3K_mem).mp hc))

@[simp] theorem l3rhoFun_apply (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hA : IsXiAbelNormal h A) (hA2 : ∀ x ∈ A, x * x = 1 → x ∈ powSub A 2) (u : P)
    [hAn : A.Normal] (a : ↥A) :
    l3rhoFun h hA hA2 u a = QuotientGroup.mk' (l3K A) (l3Sqrt h hA u a) := rfl

theorem l3rho_mk (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (hA2 : ∀ x ∈ A, x * x = 1 → x ∈ powSub A 2) (u : P) [hAn : A.Normal] (a : ↥A) :
    l3rho h hA hA2 u (QuotientGroup.mk a) = QuotientGroup.mk (l3Sqrt h hA u a) := by
  rw [l3rho, QuotientGroup.lift_mk', l3rhoFun_apply, QuotientGroup.mk'_apply]

/-! ## The action of `ξ` on the quotient -/

theorem l3K_map (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A) :
    (l3K A).map (l3Axi h hAinv).toMonoidHom = l3K A := by
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    have hx' : (x : P) ∈ powSub A 2 := (l3K_mem).mp hx
    have hmem : (h.xi : MulAut P) (x : P) ∈ (powSub A 2).map (h.xi : MulAut P).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx'
    rw [map_powSub (h.xi : MulAut P) hAinv 2] at hmem
    rw [l3K_mem]
    rw [← hxy]
    simpa using hmem
  · intro y hy
    have hy' : (y : P) ∈ powSub A 2 := (l3K_mem).mp hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp (by
      rw [map_powSub (h.xi : MulAut P) hAinv 2]; exact hy')
    refine ⟨⟨x, powSub_le (by norm_num) hx⟩, ?_, ?_⟩
    · exact (l3K_mem).mpr hx
    · apply Subtype.ext
      simpa [l3Axi_apply] using hxy

/-- The automorphism of `A / A ^ (2)` induced by `ξ`. -/
noncomputable def l3xiBar (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A) [hAn : A.Normal] :
    MulAut (↥A ⧸ l3K A) :=
  QuotientGroup.congr (l3K A) (l3K A) (l3Axi h hAinv) (l3K_map h hAinv)

theorem l3xiBar_mk (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A) [hAn : A.Normal] (a : ↥A) :
    l3xiBar h hAinv (QuotientGroup.mk a) = QuotientGroup.mk (l3Axi h hAinv a) :=
  QuotientGroup.congr_mk (l3K A) (l3K A) (l3Axi h hAinv) (l3K_map h hAinv) a

theorem l3xiBar_pow_mk (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A) [hAn : A.Normal] (k : ℕ) (a : ↥A) :
    ((l3xiBar h hAinv) ^ k) (QuotientGroup.mk a)
      = QuotientGroup.mk (((l3Axi h hAinv) ^ k) a) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, l3xiBar_mk, pow_succ', MulAut.mul_apply]

end Work.Higman
