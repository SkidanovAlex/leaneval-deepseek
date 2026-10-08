/-
Copyright (c) 2024. All rights reserved.

# `A(n,θ)` is a Suzuki 2-group

Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), §4 (Columns IV and V of the table).
For a finite field `F = GF(2ⁿ)` and a non-trivial field automorphism `θ : F ≃+* F` of **odd**
order, the "type `A`" group
`A(n,θ) = {(α,ζ) | α,ζ ∈ F}`, `(α,ζ)(γ,η) = (α+γ, ζ+η+α·θ(γ))`
is a Suzuki 2-group: a non-abelian 2-group with more than one involution admitting a cyclic
group of automorphisms acting transitively on its involutions.

The automorphism is the "diagonal" one of Column IV: for `λ ∈ Fˣ` it is
`ξ(α,ζ) = (λ·α, λ·θ(λ)·ζ)`, and it acts on the `q - 1` involutions `(0,ζ)`, `ζ ≠ 0`, by
multiplication by `λ·θ(λ)`.  The subtle point is that `λ·θ(λ)` generates `Fˣ`: the map
`Φ(z) = z·θ(z)` is an injective group endomorphism of `Fˣ` because an element of its kernel
satisfies `θ(θ z) = z` while `θ` has odd order, so it is fixed by `θ`.

Everything is stated for a general finite field of characteristic two.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.Model
import Submission.Work.Higman.Family

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

noncomputable section

open LeanEval.GroupTheory.Defs

namespace Work.Higman

variable {F : Type*} [Field F] [CharP F 2]

/-! ## Involutions of `A(n,θ)`

In `A(n,θ)` squaring is `(α,ζ)² = (0, α·θ(α))`, so `x² = 1` iff `α = 0`; equivalently the
involutions are exactly the elements `(0,ζ)` with `ζ ≠ 0`, and they all lie in `Ω₁ = Z`. -/

theorem AType_sq_eq (θ : F ≃+* F) (x : AType F θ) :
    x ^ 2 = (⟨0, x.fst * θ x.fst⟩ : AType F θ) := by
  rw [TwoStep.sq_eq]; rfl

theorem AType_sq_eq_one_iff (θ : F ≃+* F) (x : AType F θ) : x ^ 2 = 1 ↔ x.fst = 0 := by
  rw [AType_sq_eq, show (1 : AType F θ) = (⟨0, 0⟩ : AType F θ) from by ext <;> simp]
  constructor
  · intro h
    have h' : x.fst * θ x.fst = 0 := by
      have := congrArg (fun y : AType F θ => y.snd) h
      simpa using this
    rcases mul_eq_zero.mp h' with h1 | h2
    · exact h1
    · exact θ.injective (by rw [h2, map_zero])
  · intro h
    rw [h, map_zero, mul_zero]

theorem AType_orderOf_eq_two_iff (θ : F ≃+* F) (x : AType F θ) :
    orderOf x = 2 ↔ x.fst = 0 ∧ x.snd ≠ 0 := by
  rw [orderOf_eq_prime_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(AType_sq_eq_one_iff θ x).mp h1, ?_⟩
    intro hs
    apply h2
    ext <;> simp [AType_sq_eq_one_iff θ x |>.mp h1, hs]
  · rintro ⟨h1, h2⟩
    refine ⟨(AType_sq_eq_one_iff θ x).mpr h1, ?_⟩
    intro h
    apply h2
    have := congrArg (fun y : AType F θ => y.snd) h
    simpa using this

/-! ## The field lemma: `z · θ z = 1 ⟹ z = 1` for `θ` of odd order -/

/-- Iterating an involution of the first coordinate: if `θ (θ w) = w` then `θ ^ (2m)` fixes `w`. -/
theorem theta_even_iterate (θ : F ≃+* F) {w : F} (hw : θ (θ w) = w) (m : ℕ) :
    (θ ^ (2 * m)) w = w := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h2m : 2 * (m + 1) = 2 * m + 2 := by ring
    rw [h2m, pow_add]
    change (θ ^ (2 * m)) ((θ ^ 2) w) = w
    rw [show (θ ^ 2) w = θ (θ w) from rfl, hw, ih]

/-- In characteristic two, `z · θ z = 1` forces `z = 1` when `θ` has odd order.

Indeed `z · θ z = 1` gives `θ z = z⁻¹`, hence `θ (θ z) = z`; iterating the latter, the odd order
of `θ` forces `θ z = z`, so `z = z⁻¹`, i.e. `z² = 1`, i.e. `z = 1`. -/
theorem mul_theta_self_eq_one (θ : F ≃+* F) (hodd : Odd (orderOf θ)) {z : F}
    (hz : z * θ z = 1) : z = 1 := by
  have hz1 : θ z = z⁻¹ := (inv_eq_of_mul_eq_one_right hz).symm
  have hz2 : θ (θ z) = z := by
    have h1 : θ (θ z) = θ (z⁻¹) := by rw [hz1]
    rw [h1, map_inv₀, hz1, inv_inv]
  obtain ⟨m, hm⟩ := hodd
  have h2m : (θ ^ (2 * m)) z = z := theta_even_iterate θ hz2 m
  have h1 : (θ ^ (2 * m + 1)) z = θ z := by
    rw [pow_succ']
    change θ ((θ ^ (2 * m)) z) = θ z
    rw [h2m]
  have hk : (θ ^ (2 * m + 1)) z = z := by rw [← hm, pow_orderOf_eq_one]; rfl
  have hz' : θ z = z := by rw [← h1]; exact hk
  have hzz : z * z = 1 := by simpa [hz'] using hz
  have hsq : z ^ 2 = 1 := by rw [pow_two]; exact hzz
  have h2 : (z + 1) ^ 2 = 0 := by
    rw [CharTwo.add_sq, hsq, one_pow, one_add_one_eq_two, CharTwo.two_eq_zero]
  have h3 : z + 1 = 0 := sq_eq_zero_iff.mp h2
  rw [eq_neg_of_add_eq_zero_left h3, CharTwo.neg_eq]

/-! ## The diagonal automorphism of Column IV -/

/-- The diagonal automorphism `(α,ζ) ↦ (λ·α, λ·θ(λ)·ζ)` of `A(n,θ)`. -/
def AType_diagMulEquiv (θ : F ≃+* F) (l : F) (hl : l ≠ 0) : AType F θ ≃* AType F θ where
  toFun x := ⟨l * x.fst, (l * θ l) * x.snd⟩
  invFun x := ⟨l⁻¹ * x.fst, (l * θ l)⁻¹ * x.snd⟩
  left_inv x := by
    have hμ : l * θ l ≠ 0 := mul_ne_zero hl ((RingEquiv.map_ne_zero_iff θ).mpr hl)
    ext
    · show l⁻¹ * (l * x.fst) = x.fst
      rw [← mul_assoc, inv_mul_cancel₀ hl, one_mul]
    · show (l * θ l)⁻¹ * ((l * θ l) * x.snd) = x.snd
      rw [← mul_assoc, inv_mul_cancel₀ hμ, one_mul]
  right_inv x := by
    have hμ : l * θ l ≠ 0 := mul_ne_zero hl ((RingEquiv.map_ne_zero_iff θ).mpr hl)
    ext
    · show l * (l⁻¹ * x.fst) = x.fst
      rw [← mul_assoc, mul_inv_cancel₀ hl, one_mul]
    · show (l * θ l) * ((l * θ l)⁻¹ * x.snd) = x.snd
      rw [← mul_assoc, mul_inv_cancel₀ hμ, one_mul]
  map_mul' x y := by
    ext
    · simp only [TwoStep.fst_mul]; ring
    · simp only [TwoStep.snd_mul, aCocycle, map_mul]; ring

/-- The `k`-th power of the diagonal automorphism. -/
theorem AType_diagMulEquiv_pow_apply (θ : F ≃+* F) (l : F) (hl : l ≠ 0) (k : ℕ)
    (x : AType F θ) :
    ((AType_diagMulEquiv θ l hl : AType F θ ≃* AType F θ) ^ k) x =
      (⟨l ^ k * x.fst, (l * θ l) ^ k * x.snd⟩ : AType F θ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change (AType_diagMulEquiv θ l hl) ((AType_diagMulEquiv θ l hl ^ k) x) = _
    rw [ih]
    show (⟨l * (l ^ k * x.fst), (l * θ l) * ((l * θ l) ^ k * x.snd)⟩ : AType F θ) =
      ⟨l ^ (k + 1) * x.fst, (l * θ l) ^ (k + 1) * x.snd⟩
    ext <;> (rw [pow_succ']; ring)

/-! ## `λ · θ λ` generates `Fˣ`

The map `Φ(z) = z · θ(z)` is an endomorphism of the finite group `Fˣ`; `ker Φ = 1` because
`z · θ z = 1` forces `z = 1` (previous section).  Hence `Φ` is surjective, and for a generator
`g` of `Fˣ` the element `Φ g = g · θ g` generates `Fˣ`. -/

theorem exists_pow_eq_of_mem_zpowers {G : Type*} [Group G] [Finite G] {x y : G}
    (h : y ∈ Subgroup.zpowers x) : ∃ k : ℕ, x ^ k = y := by
  classical
  have hx : IsOfFinOrder x := isOfFinOrder_of_finite x
  have h2 := (IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf hx).mp h
  rcases Finset.mem_image.mp h2 with ⟨k, -, hk⟩
  exact ⟨k, hk⟩

theorem exists_pow_mul_theta_eq [Finite F] (θ : F ≃+* F) (hodd : Odd (orderOf θ)) (g : Fˣ)
    (hg : ∀ x : Fˣ, x ∈ Subgroup.zpowers g) :
    ∀ w : F, w ≠ 0 → ∃ k : ℕ, ((g : F) * θ (g : F)) ^ k = w := by
  classical
  let Φ : Fˣ →* Fˣ :=
    { toFun := fun u => u * Units.map θ.toMonoidHom u
      map_one' := by simp
      map_mul' := fun u v => by
        rw [map_mul]
        exact mul_mul_mul_comm u v _ _ }
  have hinj : Function.Injective Φ := by
    intro u v huv
    have h1 : Φ (u * v⁻¹) = 1 := by
      rw [map_mul, huv, map_inv, mul_inv_cancel]
    have h2 : ((u * v⁻¹ : Fˣ) : F) * θ ((u * v⁻¹ : Fˣ) : F) = 1 := by
      have := congrArg (fun z : Fˣ => (z : F)) h1
      simpa [Φ, Units.coe_map] using this
    have h3 : ((u * v⁻¹ : Fˣ) : F) = 1 := mul_theta_self_eq_one θ hodd h2
    exact mul_inv_eq_one.mp (Units.ext h3)
  have hsurj : Function.Surjective Φ := Finite.surjective_of_injective hinj
  have htop : Subgroup.zpowers (Φ g) = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro w
    obtain ⟨v, rfl⟩ := hsurj w
    obtain ⟨k, hk⟩ := exists_pow_eq_of_mem_zpowers (hg v)
    rw [← hk, map_pow]
    exact Subgroup.mem_zpowers_iff.mpr ⟨(k : ℤ), by rw [zpow_natCast]⟩
  have hΦg : (Φ g : F) = (g : F) * θ (g : F) := by
    simp [Φ, Units.coe_map]
  intro w hw
  obtain ⟨k, hk⟩ := exists_pow_eq_of_mem_zpowers (show Units.mk0 w hw ∈ Subgroup.zpowers (Φ g) by
    rw [htop]; exact Subgroup.mem_top _)
  refine ⟨k, ?_⟩
  have h2 := congrArg (fun z : Fˣ => (z : F)) hk
  rw [Units.val_pow_eq_pow_val, hΦg] at h2
  exact h2

/-! ## The three elementary facts about `A(n,θ)` -/

theorem exists_nonfixed_of_ne_refl (θ : F ≃+* F) (hθ : θ ≠ RingEquiv.refl F) :
    ∃ c : F, θ c ≠ c := by
  by_contra h
  push Not at h
  exact hθ (RingEquiv.ext h)

theorem AType_not_commutative (θ : F ≃+* F) (hθ : θ ≠ RingEquiv.refl F) :
    ∃ x y : AType F θ, x * y ≠ y * x := by
  obtain ⟨c, hc⟩ := exists_nonfixed_of_ne_refl θ hθ
  refine ⟨⟨1, 0⟩, ⟨c, 0⟩, fun h => hc ?_⟩
  have h2 := congrArg (fun z : AType F θ => z.snd) h
  simp only [TwoStep.snd_mul, aCocycle] at h2
  simpa using h2

theorem AType_two_involutions (θ : F ≃+* F) (hθ : θ ≠ RingEquiv.refl F) :
    ∃ x y : AType F θ, orderOf x = 2 ∧ orderOf y = 2 ∧ x ≠ y := by
  obtain ⟨c, hc⟩ := exists_nonfixed_of_ne_refl θ hθ
  have hc0 : c ≠ 0 := fun h => hc (by rw [h, map_zero])
  have hc1 : c ≠ 1 := fun h => hc (by rw [h, map_one])
  refine ⟨⟨0, 1⟩, ⟨0, c⟩, ?_, ?_, ?_⟩
  · rw [AType_orderOf_eq_two_iff]; exact ⟨rfl, one_ne_zero⟩
  · rw [AType_orderOf_eq_two_iff]; exact ⟨rfl, hc0⟩
  · intro h
    have h2 := congrArg (fun z : AType F θ => z.snd) h
    simp at h2
    exact hc1 h2.symm

theorem AType_isPGroup [Finite F] (θ : F ≃+* F) : IsPGroup 2 (AType F θ) := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨m, -, hm⟩ := FiniteField.card F 2
  refine IsPGroup.of_card (n := 2 * (m : ℕ)) ?_
  rw [TwoStep.card_eq, ← Fintype.card_eq_nat_card, hm, ← pow_add]
  congr 1
  ring

/-! ## The theorem -/

/-- `A(n,θ)` is a Suzuki 2-group whenever `θ ≠ 1` has odd order (Higman 1963, §4: `A(n,θ)`
exists for `n` not a power of `2`, and `ξ` then has order `q - 1` and acts regularly). -/
theorem AType_isSuzukiTwoGroup (n : ℕ) (θ : GaloisField 2 n ≃+* GaloisField 2 n)
    (hθ : θ ≠ RingEquiv.refl _) (hodd : Odd (orderOf θ)) :
    Submission.Blueprint.IsSuzukiTwoGroup (Work.Higman.AType (GaloisField 2 n) θ) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField 2 n)ˣ)
  refine ⟨AType_isPGroup θ, AType_not_commutative θ hθ, AType_two_involutions θ hθ, ?_⟩
  refine ⟨AType_diagMulEquiv θ (g : GaloisField 2 n) (Units.ne_zero g), ?_⟩
  intro x y hx hy
  rw [AType_orderOf_eq_two_iff] at hx hy
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨k, hk⟩ :=
    exists_pow_mul_theta_eq θ hodd g hg (y.snd / x.snd) (div_ne_zero hy2 hx2)
  refine ⟨k, ?_⟩
  have hy' : y = ⟨0, y.snd⟩ := by
    apply TwoStep.ext_iff
    · simpa using hy1
    · rfl
  rw [hy', AType_diagMulEquiv_pow_apply, hx1, mul_zero]
  refine TwoStep.ext_iff rfl ?_
  rw [hk]
  exact div_mul_cancel₀ y.snd hx2

end Work.Higman
