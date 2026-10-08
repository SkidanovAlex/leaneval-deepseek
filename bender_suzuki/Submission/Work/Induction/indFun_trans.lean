import Mathlib
import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical
open scoped Pointwise

/-!
# Transitivity of induction

`Work.Induction.indFun_trans` states that induction of class functions is transitive:
for subgroups `K ≤ H ≤ G` and `φ : K → ℂ`,
`Ind_H^G (Ind_{K}^{H} φ) = Ind_{K}^{G} φ`, where `Ind_{K}^{H}` is computed inside `H`
(the subgroup `K.subgroupOf H`).

The proof expands both sides as sums over `G` and `H`, and reindexes the double sum
over `G × H` by the product `z = x * y`: a fixed `z : G` has exactly `|H|` preimages
`(y, x)` with `x ∈ H`, `y ∈ G` and `x * y = z`.

Below, `extZero K φ : G → ℂ` is the zero extension of a function on a subgroup `K ≤ G`
to all of `G`.  It is `definitionally` the summand appearing in `indFun`, which makes the
bookkeeping (`indFun_eq_sum_extZero`, `indFun_subgroupOf_apply`) cheap.
-/

/-- The zero extension of a function on a subgroup `K ≤ G` to the whole group `G`. -/
noncomputable def extZero {G : Type*} [Group G] (K : Subgroup G) (φ : K → ℂ) : G → ℂ :=
  fun y => if hy : y ∈ K then φ ⟨y, hy⟩ else 0

theorem extZero_of_mem {G : Type*} [Group G] {K : Subgroup G} {φ : K → ℂ} {y : G}
    (hy : y ∈ K) : extZero K φ y = φ ⟨y, hy⟩ := dite_eq_left hy

theorem extZero_of_notMem {G : Type*} [Group G] {K : Subgroup G} {φ : K → ℂ} {y : G}
    (hy : y ∉ K) : extZero K φ y = 0 := dite_eq_right hy

/-- The defining sum of `indFun`, with the indicator-type summand written as a zero
extension of `φ`. -/
theorem indFun_eq_sum_extZero {G : Type*} [Group G] [Fintype G] (K : Subgroup G) (φ : K → ℂ)
    (g : G) :
    indFun K φ g = (Nat.card K : ℂ)⁻¹ * ∑ z : G, extZero K φ (z * g * z⁻¹) := by
  rw [indFun_apply_def]
  congr 1

/-- Switching to the ambient group `G`, induction from `K.subgroupOf H` is the same
double-conjugation sum as induction from `K`:
`∑_{x ∈ H} (φ extended by zero) (x * h * x⁻¹)`. -/
theorem indFun_subgroupOf_apply {G : Type*} [Group G] [Fintype G] {K H : Subgroup G}
    (hKH : K ≤ H) (φ : K → ℂ) (h : H) :
    indFun (K.subgroupOf H) (fun x : K.subgroupOf H => φ (Subgroup.subgroupOfEquivOfLe hKH x)) h
      = (Nat.card (K.subgroupOf H) : ℂ)⁻¹
        * ∑ x : H, extZero K φ ((x : G) * (h : G) * (x : G)⁻¹) := by
  rw [indFun_apply_def]
  congr 1

/-- Conjugating by `x ∈ H` an element outside `H` lands outside `H`, hence outside `K ≤ H`,
so the zero extension vanishes there. -/
theorem extZero_conj_eq_zero {G : Type*} [Group G] {K H : Subgroup G} (hKH : K ≤ H)
    (φ : K → ℂ) (x : H) (w : G) (hw : w ∉ H) :
    extZero K φ ((x : G) * w * (x : G)⁻¹) = 0 := by
  apply extZero_of_notMem
  intro hc
  apply hw
  have hcoe : (x : G)⁻¹ * ((x : G) * w * (x : G)⁻¹) * (x : G) = w := by group
  rw [← hcoe]
  exact H.mul_mem (H.mul_mem (H.inv_mem x.2) (hKH hc)) x.2

/-- Reindexing the double sum over `G × H` by the product `z = x * y`: every `z : G` has
exactly `|H|` preimages. -/
theorem sum_sum_reindex {G : Type*} [Group G] [Fintype G] (K H : Subgroup G) (φ : K → ℂ)
    (g : G) :
    (∑ y : G, ∑ x : H, extZero K φ ((x : G) * y * g * ((x : G) * y)⁻¹))
      = (Nat.card H : ℂ) * ∑ z : G, extZero K φ (z * g * z⁻¹) := by
  rw [Finset.sum_comm]
  have hterm : ∀ x : H, (∑ y : G, extZero K φ ((x : G) * y * g * ((x : G) * y)⁻¹))
      = ∑ z : G, extZero K φ (z * g * z⁻¹) := by
    intro x
    have hbij : Function.Bijective (fun y : G => (x : G) * y) :=
      Function.bijective_iff_has_inverse.mpr
        ⟨fun z => (x : G)⁻¹ * z, fun z => by group, fun z => by group⟩
    exact Finset.sum_bijective (fun y : G => (x : G) * y) hbij (fun i => by simp)
      (fun y _ => rfl)
  rw [Finset.sum_congr rfl (fun x _ => hterm x)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]

/-- `|H|⁻¹ * (b * (|H| * Z)) = b * Z`, the factor `|H|` coming from the number of
preimages in the reindexing of the double sum. -/
private theorem inv_card_mul_assoc {R : Type*} [Field R] (a b Z : R) (ha : a ≠ 0) :
    a⁻¹ * (b * (a * Z)) = b * Z := by
  rw [show a⁻¹ * (b * (a * Z)) = (a⁻¹ * a) * (b * Z) by ring, inv_mul_cancel₀ ha, one_mul]

-- Transitivity of induction: `Ind_H^G (Ind_K^H φ) = Ind_K^G φ` for `K ≤ H ≤ G`, as functions
-- on `G` (the first induction has ambient group `H` — the subgroup `K.subgroupOf H` — and the
-- second has ambient group `G`).  Expand the double sum over `(y, x) ∈ G × H` and reindex by
-- `z = x * y`: every `z : G` has exactly `|H|` preimages, the condition `(x*y)*g*(x*y)⁻¹ ∈ K`
-- implies `y*g*y⁻¹ = x⁻¹ * ((x*y)*g*(x*y)⁻¹) * x ∈ H` (as `x ∈ H` and `K ≤ H`, and conjugation
-- by `x ∈ H` maps `H` to itself), and `|H|⁻¹ * |K|⁻¹ * |H| = |K|⁻¹`.  The subgroup iso
-- `Subgroup.subgroupOfEquivOfLe hKH : K.subgroupOf H ≃* K` transports `φ` to `K.subgroupOf H`.
theorem indFun_trans {G : Type*} [Group G] [Fintype G] {K H : Subgroup G} (hKH : K ≤ H)
    (φ : K → ℂ) :
    Work.Induction.indFun H
        (Work.Induction.indFun (K.subgroupOf H)
          (fun x : K.subgroupOf H => φ (Subgroup.subgroupOfEquivOfLe hKH x)))
      = Work.Induction.indFun K φ := by
  ext g
  have hHne : (Nat.card H : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Nat.card_eq_fintype_card]
    exact Fintype.card_ne_zero
  have hcard : (Nat.card (K.subgroupOf H) : ℂ)⁻¹ = (Nat.card K : ℂ)⁻¹ := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv]
  -- Step 1: unfold the outer induction, and the inner induction on `h : H`.
  have htrans : indFun H (indFun (K.subgroupOf H)
        (fun x : K.subgroupOf H => φ (Subgroup.subgroupOfEquivOfLe hKH x))) g
      = (Nat.card H : ℂ)⁻¹ * ((Nat.card (K.subgroupOf H) : ℂ)⁻¹ *
          ∑ y : G, ∑ x : H, extZero K φ ((x : G) * y * g * ((x : G) * y)⁻¹)) := by
    conv_lhs => rw [indFun_apply_def]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases hy : y * g * y⁻¹ ∈ H
    · rw [dite_eq_left hy, indFun_subgroupOf_apply hKH φ ⟨y * g * y⁻¹, hy⟩]
      congr 1
      refine Finset.sum_congr rfl (fun x _ => ?_)
      apply congrArg (extZero K φ)
      group
    · -- if `y * g * y⁻¹ ∉ H` then each conjugate `x * (y * g * y⁻¹) * x⁻¹` is outside `K`,
      -- so the whole inner sum vanishes.
      rw [dite_eq_right hy]
      have hzero : (∑ x : H, extZero K φ ((x : G) * y * g * ((x : G) * y)⁻¹)) = 0 := by
        refine Finset.sum_eq_zero (fun x _ => ?_)
        rw [show (x : G) * y * g * ((x : G) * y)⁻¹
            = (x : G) * (y * g * y⁻¹) * (x : G)⁻¹ from by group]
        exact extZero_conj_eq_zero hKH φ x (y * g * y⁻¹) hy
      rw [hzero, mul_zero]
  -- Step 2: reindex and cancel `|H|⁻¹ * |H|`; the cardinals `|K.subgroupOf H|` and `|K|` agree.
  rw [htrans, sum_sum_reindex K H φ g, hcard, indFun_eq_sum_extZero K φ g]
  exact inv_card_mul_assoc _ _ _ hHne

end Work.Induction
