import Mathlib
import Submission.Work.FIArea2.TsumDefs2
import Submission.Work.FIArea2.Tsum_odd_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Lifting the local congruence sum `TsumD` from `p^m` to `p^j`

`Work.FIArea2.TsumD p j m a h₁ h₂` is the exponential sum over `(x,y) ∈ (ZMod (p^j))²` with the
weak congruence `p^m ∣ y² - a x²`.  This file proves the "lifting" identity

  `TsumD p j m a h₁ h₂ = p^{2(j-m)} · [p^{j-m} ∣ h₁][p^{j-m} ∣ h₂] · Tsum (p^m) a (h₁/p^{j-m}) (h₂/p^{j-m})`.

The proof classifies `(x,y)` by the pair of residues `(x mod p^m, y mod p^m)` together with the
two "divided" coordinates `u = (x - (x mod p^m))/p^m`, `v = (y - (y mod p^m))/p^m`.  On each fibre
the congruence reduces to the one for `(x mod p^m, y mod p^m)`, and the additive character splits
off two copies of the incomplete geometric sum `∑_u e(u h / p^{j-m})`, which is `p^{j-m}` if
`p^{j-m} ∣ h` and `0` otherwise.
-/

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### The fibre decomposition `ZMod (p^j) ≃ ZMod (p^m) × ZMod (p^(j-m))` -/

/-- The lift `(x,u) ↦ x + p^m·u` from `ZMod (p^m) × ZMod (p^(j-m))` to `ZMod (p^j)`, written on
representatives. -/
def deplift (p j m : ℕ) (x : ZMod (p ^ m)) (u : ZMod (p ^ (j - m))) : ZMod (p ^ j) :=
  ((x.val + p ^ m * u.val : ℕ) : ZMod (p ^ j))

/-- The representative of `deplift x u` is `x.val + p^m·u.val`. -/
lemma deplift_val {p j m : ℕ} (hp : p.Prime) [NeZero p] (hmj : m ≤ j)
    (x : ZMod (p^m)) (u : ZMod (p^(j-m))) :
    (deplift p j m x u).val = x.val + p^m * u.val := by
  haveI : NeZero (p^j) := inferInstance
  rw [deplift, ZMod.val_natCast, Nat.mod_eq_of_lt]
  have hx : x.val < p ^ m := ZMod.val_lt x
  have hu : u.val < p ^ (j - m) := ZMod.val_lt u
  have h5 : p ^ m * p ^ (j - m) = p ^ j := by rw [← pow_add, Nat.add_sub_cancel' hmj]
  calc x.val + p ^ m * u.val < p ^ m + p ^ m * u.val := Nat.add_lt_add_right hx _
    _ = p ^ m * (u.val + 1) := by ring
    _ ≤ p ^ j := by rw [← h5]; exact Nat.mul_le_mul_left _ hu

/-- `deplift` is a bijection. -/
lemma deplift_bijective {p j m : ℕ} (hp : p.Prime) [NeZero p] (hmj : m ≤ j) :
    Function.Bijective (fun z : ZMod (p^m) × ZMod (p^(j-m)) => deplift p j m z.1 z.2) := by
  haveI : NeZero (p^j) := inferInstance
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro ⟨x,u⟩ ⟨x',u'⟩ h
    simp only at h
    have hval := congrArg ZMod.val h
    rw [deplift_val hp hmj x u, deplift_val hp hmj x' u'] at hval
    have hmod : x.val % p^m = x'.val % p^m := by
      have e1 : (x.val + p ^ m * u.val) % p^m = x.val % p^m := Nat.add_mul_mod_self_left _ _ _
      have e2 : (x'.val + p ^ m * u'.val) % p^m = x'.val % p^m := Nat.add_mul_mod_self_left _ _ _
      rw [← e1, ← e2, hval]
    rw [Nat.mod_eq_of_lt (ZMod.val_lt x), Nat.mod_eq_of_lt (ZMod.val_lt x')] at hmod
    have hxu : x = x' := ZMod.val_injective _ hmod
    have hpu : p^m * u.val = p^m * u'.val := by omega
    have huval : u.val = u'.val := Nat.mul_left_cancel (pow_pos hp.pos m) hpu
    exact Prod.ext hxu (ZMod.val_injective _ huval)
  · rw [Fintype.card_prod, ZMod.card, ZMod.card, ZMod.card, ← pow_add, Nat.add_sub_cancel' hmj]

/-- Reindexing a sum over `ZMod (p^j)` by the fibre decomposition. -/
lemma sum_deplift {p j m : ℕ} (hp : p.Prime) [NeZero p] (hmj : m ≤ j) (G : ZMod (p^j) → ℂ) :
    (∑ x : ZMod (p^j), G x)
      = ∑ x₀ : ZMod (p^m), ∑ u : ZMod (p^(j-m)), G (deplift p j m x₀ u) := by
  rw [← Fintype.sum_bijective (fun z : ZMod (p^m) × ZMod (p^(j-m)) => deplift p j m z.1 z.2)
        (deplift_bijective hp hmj) (fun z => G (deplift p j m z.1 z.2)) G (fun z => rfl)]
  exact Fintype.sum_prod_type _

/-! ### A four-fold factorisation of sums -/

/-- `∑_{a,b,c,d} G a b · E₂ c · E₃ d = (∑_{a,b} G a b)(∑_c E₂ c)(∑_d E₃ d)`. -/
lemma sum4_factor {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (G : α → β → ℂ) (E₂ : γ → ℂ) (E₃ : δ → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, G a b * E₂ c * E₃ d)
      = (∑ a, ∑ b, G a b) * (∑ c, E₂ c) * (∑ d, E₃ d) := by
  symm
  calc (∑ a, ∑ b, G a b) * (∑ c, E₂ c) * (∑ d, E₃ d)
      = (∑ a, ∑ b, G a b) * ((∑ c, E₂ c) * (∑ d, E₃ d)) := by ring
    _ = (∑ a, ∑ b, G a b) * (∑ c, ∑ d, E₂ c * E₃ d) := by
          rw [Finset.sum_mul_sum]
    _ = ∑ a, (∑ b, G a b) * (∑ c, ∑ d, E₂ c * E₃ d) := by rw [Finset.sum_mul]
    _ = ∑ a, ∑ b, G a b * (∑ c, ∑ d, E₂ c * E₃ d) := by
          refine Finset.sum_congr rfl (fun a _ => ?_); rw [Finset.sum_mul]
    _ = ∑ a, ∑ b, ∑ c, G a b * (∑ d, E₂ c * E₃ d) := by
          refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
          rw [Finset.mul_sum]
    _ = ∑ a, ∑ b, ∑ c, ∑ d, G a b * (E₂ c * E₃ d) := by
          refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
            Finset.sum_congr rfl (fun c _ => ?_)))
          rw [Finset.mul_sum]
    _ = ∑ a, ∑ b, ∑ c, ∑ d, G a b * E₂ c * E₃ d := by
          refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
            Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
          rw [mul_assoc]

/-! ### The congruence and the character on a fibre -/

/-- On a fibre, the congruence `p^m ∣ y² - a x²` is the congruence for the residues. -/
lemma cond_decomp {p j m : ℕ} (hp : p.Prime) [NeZero p] (hmj : m ≤ j) (a : ℤ)
    (x₀ y₀ : ZMod (p^m)) (u v : ZMod (p^(j-m))) :
    (((p^m : ℕ) : ℤ) ∣ ((deplift p j m y₀ v).val : ℤ)^2 - a * ((deplift p j m x₀ u).val : ℤ)^2)
      ↔ (((p^m : ℕ) : ℤ) ∣ (y₀.val : ℤ)^2 - a * (x₀.val : ℤ)^2) := by
  have hX : ((deplift p j m x₀ u).val : ℤ) = (x₀.val : ℤ) + ((p^m : ℕ) : ℤ) * (u.val : ℤ) := by
    rw [deplift_val hp hmj]; push_cast; ring
  have hY : ((deplift p j m y₀ v).val : ℤ) = (y₀.val : ℤ) + ((p^m : ℕ) : ℤ) * (v.val : ℤ) := by
    rw [deplift_val hp hmj]; push_cast; ring
  have hkey : ((deplift p j m y₀ v).val : ℤ)^2 - a * ((deplift p j m x₀ u).val : ℤ)^2
      = ((y₀.val : ℤ)^2 - a * (x₀.val : ℤ)^2)
        + ((p^m:ℕ):ℤ) * (2*(y₀.val:ℤ)*(v.val:ℤ) + ((p^m:ℕ):ℤ)*(v.val:ℤ)^2
                          - a*(2*(x₀.val:ℤ)*(u.val:ℤ) + ((p^m:ℕ):ℤ)*(u.val:ℤ)^2)) := by
    rw [hX, hY]; ring
  rw [hkey]
  exact Int.dvd_add_left (Int.dvd_mul_right _ _)

/-- The additive character splits on a fibre into the residue part and the two divided parts. -/
lemma E_decomp {p j m : ℕ} (hp : p.Prime) [NeZero p] (hmj : m ≤ j) (h1 h2 : ℤ)
    (x₀ y₀ : ZMod (p^m)) (u v : ZMod (p^(j-m))) :
    E (((((deplift p j m x₀ u).val : ℤ) * h1 + ((deplift p j m y₀ v).val : ℤ) * h2 : ℤ) : ℝ)
        / ((p^j : ℕ) : ℝ))
    = E ((((x₀.val : ℤ) * h1 + (y₀.val : ℤ) * h2 : ℤ) : ℝ) / ((p^j : ℕ) : ℝ))
      * E (((((u.val : ℤ) * h1 : ℤ) : ℝ) / ((p^(j-m) : ℕ) : ℝ)))
      * E (((((v.val : ℤ) * h2 : ℤ) : ℝ) / ((p^(j-m) : ℕ) : ℝ))) := by
  have hX : ((deplift p j m x₀ u).val : ℤ) = (x₀.val : ℤ) + ((p^m : ℕ) : ℤ) * (u.val : ℤ) := by
    rw [deplift_val hp hmj]; push_cast; ring
  have hY : ((deplift p j m y₀ v).val : ℤ) = (y₀.val : ℤ) + ((p^m : ℕ) : ℤ) * (v.val : ℤ) := by
    rw [deplift_val hp hmj]; push_cast; ring
  have key1 : ((((deplift p j m x₀ u).val : ℤ) * h1 + ((deplift p j m y₀ v).val : ℤ) * h2 : ℤ) : ℝ)
      = (((x₀.val : ℤ) * h1 + (y₀.val : ℤ) * h2 : ℤ) : ℝ)
        + ((p^m : ℕ) : ℝ) * ((((u.val : ℤ) * h1 + (v.val : ℤ) * h2 : ℤ)) : ℝ) := by
    rw [hX, hY]; push_cast; ring
  have hpq : ((p^j : ℕ) : ℝ) = ((p^m : ℕ) : ℝ) * ((p^(j-m) : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, ← pow_add, Nat.add_sub_cancel' hmj]
  have hm0 : (((p^m : ℕ) : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero m hp.ne_zero)
  have hC : (↑(((u.val : ℤ) * h1 + (v.val : ℤ) * h2) : ℤ) : ℝ)
      = ↑(((u.val : ℤ) * h1 : ℤ)) + ↑(((v.val : ℤ) * h2 : ℤ)) := by
    push_cast; ring
  have key2 : ((((x₀.val : ℤ) * h1 + (y₀.val : ℤ) * h2 : ℤ) : ℝ)
        + ((p^m : ℕ) : ℝ) * ((((u.val : ℤ) * h1 + (v.val : ℤ) * h2 : ℤ)) : ℝ))
        / (((p^m : ℕ) : ℝ) * ((p^(j-m) : ℕ) : ℝ))
      = (((x₀.val : ℤ) * h1 + (y₀.val : ℤ) * h2 : ℤ) : ℝ)
          / (((p^m : ℕ) : ℝ) * ((p^(j-m) : ℕ) : ℝ))
        + (((((u.val : ℤ) * h1 : ℤ) : ℝ)) / ((p^(j-m) : ℕ) : ℝ)
        + ((((v.val : ℤ) * h2 : ℤ) : ℝ)) / ((p^(j-m) : ℕ) : ℝ)) := by
    rw [add_div, mul_div_mul_left _ _ hm0, hC, add_div]
  rw [key1, hpq, key2, E_add, E_add, mul_assoc]

/-- The full summand rewrite on a fibre. -/
lemma summand_decomp {p j m : ℕ} (hp : p.Prime) [NeZero p] (hmj : m ≤ j) (a h1 h2 : ℤ)
    (x₀ y₀ : ZMod (p^m)) (u v : ZMod (p^(j-m))) :
    (if (((p^m : ℕ) : ℤ) ∣ ((deplift p j m y₀ v).val : ℤ)^2
          - a * ((deplift p j m x₀ u).val : ℤ)^2)
      then E (((((deplift p j m x₀ u).val : ℤ) * h1
            + ((deplift p j m y₀ v).val : ℤ) * h2 : ℤ) : ℝ) / ((p^j : ℕ) : ℝ))
      else 0)
    = (if (((p^m : ℕ) : ℤ) ∣ (y₀.val : ℤ)^2 - a * (x₀.val : ℤ)^2)
        then E ((((x₀.val : ℤ) * h1 + (y₀.val : ℤ) * h2 : ℤ) : ℝ) / ((p^j : ℕ) : ℝ))
        else 0)
      * E (((((u.val : ℤ) * h1 : ℤ) : ℝ) / ((p^(j-m) : ℕ) : ℝ)))
      * E (((((v.val : ℤ) * h2 : ℤ) : ℝ) / ((p^(j-m) : ℕ) : ℝ))) := by
  by_cases hc : (((p^m : ℕ) : ℤ) ∣ (y₀.val : ℤ)^2 - a * (x₀.val : ℤ)^2)
  · rw [if_pos ((cond_decomp hp hmj a x₀ y₀ u v).mpr hc), if_pos hc,
      E_decomp hp hmj h1 h2 x₀ y₀ u v]
  · rw [if_neg (fun h => hc ((cond_decomp hp hmj a x₀ y₀ u v).mp h)), if_neg hc, zero_mul,
      zero_mul]

/-! ### The inner sum equals `Tsum (p^m)` -/

/-- When `p^(j-m) ∣ h₁, h₂`, the residue part of the fibre sum is `Tsum (p^m)` with divided
characters. -/
lemma TsumD_inner {p j m : ℕ} (hp : p.Prime) [NeZero p] (hmj : m ≤ j) (a h1 h2 : ℤ)
    (hd1 : (((p^(j-m) : ℕ) : ℤ)) ∣ h1) (hd2 : (((p^(j-m) : ℕ) : ℤ)) ∣ h2) :
    (∑ x₀ : ZMod (p^m), ∑ y₀ : ZMod (p^m),
      (if (((p^m : ℕ) : ℤ) ∣ (y₀.val : ℤ)^2 - a * (x₀.val : ℤ)^2)
        then E ((((x₀.val : ℤ) * h1 + (y₀.val : ℤ) * h2 : ℤ) : ℝ) / ((p^j : ℕ) : ℝ))
        else 0))
    = Tsum (p^m) a (h1 / (((p^(j-m) : ℕ) : ℤ))) (h2 / (((p^(j-m) : ℕ) : ℤ))) := by
  rw [Tsum]
  refine Finset.sum_congr rfl (fun x₀ _ => Finset.sum_congr rfl (fun y₀ _ => ?_))
  by_cases h : (((p^m : ℕ) : ℤ) ∣ (y₀.val : ℤ)^2 - a * (x₀.val : ℤ)^2)
  · rw [if_pos h, if_pos ((zmod_cond_iff (p^m) a x₀ y₀).mp h)]
    set h1' : ℤ := h1 / (((p^(j-m) : ℕ) : ℤ)) with hh1'
    set h2' : ℤ := h2 / (((p^(j-m) : ℕ) : ℤ)) with hh2'
    have e1 : h1 = (((p^(j-m) : ℕ) : ℤ)) * h1' := by
      rw [hh1']; exact (Int.mul_ediv_cancel' hd1).symm
    have e2 : h2 = (((p^(j-m) : ℕ) : ℤ)) * h2' := by
      rw [hh2']; exact (Int.mul_ediv_cancel' hd2).symm
    have hQ : ((p^j : ℕ) : ℝ) = ((p^m : ℕ) : ℝ) * (((p^(j-m) : ℕ) : ℝ)) := by
      rw [← Nat.cast_mul, ← pow_add, Nat.add_sub_cancel' hmj]
    have hj0 : (((p^j : ℕ) : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero j hp.ne_zero)
    have hm0 : (((p^m : ℕ) : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero m hp.ne_zero)
    congr 1
    rw [div_eq_div_iff hj0 hm0, hQ, e1, e2]
    push_cast
    ring
  · rw [if_neg h, if_neg (fun hh => h ((zmod_cond_iff (p^m) a x₀ y₀).mpr hh))]

/-- **Separation.**  `TsumD p j m` factors as the residue sum times the two geometric sums. -/
lemma TsumD_step1 {p j m : ℕ} (hp : p.Prime) [NeZero p] (hmj : m ≤ j) (a h1 h2 : ℤ) :
    TsumD p j m a h1 h2
    = (∑ x₀ : ZMod (p^m), ∑ y₀ : ZMod (p^m),
        (if (((p^m : ℕ) : ℤ) ∣ (y₀.val : ℤ)^2 - a * (x₀.val : ℤ)^2)
          then E ((((x₀.val : ℤ) * h1 + (y₀.val : ℤ) * h2 : ℤ) : ℝ) / ((p^j : ℕ) : ℝ))
          else 0))
      * T (p^(j-m)) h1 * T (p^(j-m)) h2 := by
  haveI : NeZero (p^m) := inferInstance
  haveI : NeZero (p^(j-m)) := inferInstance
  let G : ZMod (p^m) → ZMod (p^m) → ℂ := fun x₀ y₀ =>
      (if (((p^m : ℕ) : ℤ) ∣ (y₀.val : ℤ)^2 - a * (x₀.val : ℤ)^2)
        then E ((((x₀.val : ℤ) * h1 + (y₀.val : ℤ) * h2 : ℤ) : ℝ) / ((p^j : ℕ) : ℝ))
        else 0)
  let E2 : ZMod (p^(j-m)) → ℂ := fun u => E (((((u.val : ℤ) * h1 : ℤ) : ℝ) / ((p^(j-m) : ℕ) : ℝ)))
  let E3 : ZMod (p^(j-m)) → ℂ := fun v => E (((((v.val : ℤ) * h2 : ℤ) : ℝ) / ((p^(j-m) : ℕ) : ℝ)))
  unfold TsumD
  simp only [sum_deplift hp hmj]
  simp only [summand_decomp hp hmj a h1 h2]
  rw [show (∑ x₀ : ZMod (p^m), ∑ u : ZMod (p^(j-m)), ∑ y₀ : ZMod (p^m),
          ∑ v : ZMod (p^(j-m)), G x₀ y₀ * E2 u * E3 v)
      = (∑ x₀ : ZMod (p^m), ∑ y₀ : ZMod (p^m), ∑ u : ZMod (p^(j-m)),
          ∑ v : ZMod (p^(j-m)), G x₀ y₀ * E2 u * E3 v) from by
        refine Finset.sum_congr rfl (fun x₀ _ => Finset.sum_comm)]
  rw [sum4_factor G E2 E3]
  have hE2 : (∑ u : ZMod (p^(j-m)), E2 u) = T (p^(j-m)) h1 := by
    rw [← sum_ZMod_E (N := p^(j-m)) (m := h1)]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    simp only [E2]
    congr 1
    push_cast; ring
  have hE3 : (∑ v : ZMod (p^(j-m)), E3 v) = T (p^(j-m)) h2 := by
    rw [← sum_ZMod_E (N := p^(j-m)) (m := h2)]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    simp only [E3]
    congr 1
    push_cast; ring
  rw [hE2, hE3]

/-! ### The target identity -/

theorem TsumD_lift (p j m : ℕ) (hp : p.Prime) [NeZero p] (hmj : m ≤ j) (a h1 h2 : ℤ) :
    TsumD p j m a h1 h2
      = ((p : ℂ) ^ (2 * (j - m))) *
          (if ((p ^ (j - m) : ℕ) : ℤ) ∣ h1 ∧ ((p ^ (j - m) : ℕ) : ℤ) ∣ h2 then
            Tsum (p ^ m) a (h1 / ((p ^ (j - m) : ℕ) : ℤ)) (h2 / ((p ^ (j - m) : ℕ) : ℤ))
           else 0) := by
  haveI : NeZero (p^m) := inferInstance
  haveI : NeZero (p^(j-m)) := inferInstance
  rw [TsumD_step1 hp hmj a h1 h2,
    T_eq (p^(j-m)) (Nat.one_le_pow (j-m) p hp.pos) h1,
    T_eq (p^(j-m)) (Nat.one_le_pow (j-m) p hp.pos) h2]
  by_cases hcd : (((p^(j-m) : ℕ) : ℤ)) ∣ h1 ∧ (((p^(j-m) : ℕ) : ℤ)) ∣ h2
  · rw [if_pos hcd.1, if_pos hcd.2, if_pos hcd, TsumD_inner hp hmj a h1 h2 hcd.1 hcd.2]
    have hKc : (((p^(j-m) : ℕ) : ℂ)) = (p : ℂ) ^ (j-m) := by push_cast; ring
    have hY : (p : ℂ) ^ (2 * (j - m)) = (p : ℂ) ^ (j - m) * (p : ℂ) ^ (j - m) := by
      rw [show 2 * (j - m) = (j - m) + (j - m) from by ring, pow_add]
    rw [hKc, hY]; ring
  · rw [if_neg hcd]
    rcases not_and_or.mp hcd with hh | hh
    · rw [if_neg hh]; ring
    · rw [if_neg hh]; ring

end

end Work.FIArea2
