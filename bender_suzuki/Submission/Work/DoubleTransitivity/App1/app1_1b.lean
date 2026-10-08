import Mathlib
import Submission.Work.DoubleTransitivity.App1.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi, Appendix I (1)(b): the elements of `X` inverted by an involution `t`

Peterfalvi, *Le théorème de Bender–Suzuki I*, Appendix I (1)(b): if `t` is an involution
(`orderOf t = 2`) of a finite group `G` and `X` is a subgroup of odd order normalised by `t`,
then, writing

* `K  = {[t,x] | x ∈ X} = {t⁻¹x⁻¹tx | x ∈ X}` (`commutatorSet t X`),
* `K₁ = {x ∈ X | x^t = x⁻¹} = J(X,t)` (`invertedBy X t`),
* `V  = C_X(t)` (`centralizerIn X t`),

one has `K = K₁` and `|X| = |V| · |K₁|`; indeed the map `(v,y) ↦ v·y` is a bijection
`V × K₁ ≃ X` (with `v ↦ v·y` the same for `(v,y) ↦ y·v`).

The proofs here are elementary and follow the paper:

* `K ⊆ K₁`: for `x ∈ X`, `[t,x]` lies in `X` and is inverted by `t`.
* The key point is that `|X|` is odd, so every element of `X` has a unique square root inside
  `X`: if `y^2 = z^2` then `y = y^{|X|+1} = (y^2)^{(|X|+1)/2} = (z^2)^{(|X|+1)/2} = z^{|X|+1} = z`.
  This gives `K₁ ⊆ K`: for `y ∈ K₁` and `k = (|X|+1)/2`, `[t, y^k] = y^{2k} = y^{|X|+1} = y`.
  It also gives injectivity of `(v,y) ↦ v·y` on `V × K₁` (as in the paper: from `v₁y₁ = v₂y₂`
  one gets `y₁² = y₂²`), and — with the canonical section `y ↦ y^k` — surjectivity.

The commutator is handled through the conjugation automorphism `MulAut.conj t` (a monoid
homomorphism `G →* MulAut G`): with `t` of order `2` one has `t⁻¹x⁻¹tx = (x^t)⁻¹x`, and the
computations `(x·y)^t = x^t·y^t`, `(y^n)^t = (y^t)^n`, `(x^t)^t = x` become `map_mul`,
`map_pow`, `map_mul ∘ map_mul`, avoiding any explicit word manipulation with `t*t = 1`.
-/

set_option autoImplicit false

open Submission.Blueprint

namespace Work.DoubleTransitivity.App1

variable {G : Type} [Group G]

/-! ## Elementary facts about an involution -/

lemma mul_self_eq_one_of_orderOf_eq_two {t : G} (ht : orderOf t = 2) : t * t = 1 := by
  rw [← pow_two, ← ht, pow_orderOf_eq_one]

lemma inv_eq_self_of_orderOf_eq_two {t : G} (ht : orderOf t = 2) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_left (mul_self_eq_one_of_orderOf_eq_two ht)

/-! ## The commutator `[t,x] = t⁻¹x⁻¹tx` through conjugation -/

/-- `[t,x] = t⁻¹x⁻¹tx`, written as `(x^t)⁻¹·x` for `x^t = t x t⁻¹`. -/
def commutatorElem (t x : G) : G := (MulAut.conj t x)⁻¹ * x

lemma inv_conj_apply (t x : G) : (MulAut.conj t x)⁻¹ = t * x⁻¹ * t⁻¹ := by
  rw [← map_inv, MulAut.conj_apply]

/-- For an involution, Peterfalvi's `[t,x]` is `(x^t)⁻¹x`. -/
lemma commutatorElem_eq {t : G} (ht : orderOf t = 2) (x : G) :
    t⁻¹ * x⁻¹ * t * x = commutatorElem t x := by
  rw [commutatorElem, inv_conj_apply, inv_eq_self_of_orderOf_eq_two ht]

/-- Conjugation by an involution is an involution of `G`. -/
lemma conj_conj_apply {t : G} (ht : orderOf t = 2) (x : G) :
    MulAut.conj t (MulAut.conj t x) = x := by
  have hsq : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two ht
  have h1 : MulAut.conj t * MulAut.conj t = 1 := by rw [← map_mul, hsq, map_one]
  calc MulAut.conj t (MulAut.conj t x) = (MulAut.conj t * MulAut.conj t) x := rfl
    _ = (1 : MulAut G) x := by rw [h1]
    _ = x := rfl

/-- `[t,x]` is inverted by `t`. -/
lemma conj_commutatorElem {t : G} (ht : orderOf t = 2) (x : G) :
    MulAut.conj t (commutatorElem t x) = (commutatorElem t x)⁻¹ := by
  unfold commutatorElem
  rw [map_mul, map_inv, conj_conj_apply ht, mul_inv_rev, inv_inv]

/-! ## Two readings of `J(X,t)` and of `C_X(t)` -/

lemma conj_eq_self_of_mem_centralizerIn {X : Subgroup G} {t v : G}
    (hv : v ∈ centralizerIn X t) : MulAut.conj t v = v :=
  (conj_eq_iff_mul_comm t v).mpr (Subgroup.mem_centralizer_singleton_iff.mp hv.2).symm

lemma conj_eq_inv_of_mem_invertedBy {X : Subgroup G} {t y : G}
    (hy : y ∈ invertedBy X t) : MulAut.conj t y = y⁻¹ := by
  simpa [MulAut.conj_apply] using hy.2

/-- Elements of `C_X(t)` do not change commutators with `t`. -/
lemma commutatorElem_mul_of_mem_centralizerIn {X : Subgroup G} {t v x : G}
    (hv : v ∈ centralizerIn X t) : commutatorElem t (v * x) = commutatorElem t x := by
  unfold commutatorElem
  rw [map_mul, conj_eq_self_of_mem_centralizerIn hv, mul_inv_rev]
  group

/-- `[t,yⁿ] = yⁿ·yⁿ` for `y ∈ J(X,t)`. -/
lemma commutatorElem_pow_of_mem_invertedBy {X : Subgroup G} {t y : G} (n : ℕ)
    (hy : y ∈ invertedBy X t) : commutatorElem t (y ^ n) = y ^ n * y ^ n := by
  unfold commutatorElem
  rw [map_pow, conj_eq_inv_of_mem_invertedBy hy, inv_pow, inv_inv]

/-! ## Odd order: extracting square roots -/

/-- In a subgroup of order `N`, the `N`-th power of any element is `1`. -/
lemma pow_natCard_eq_one_of_mem {X : Subgroup G} {y : G} (hy : y ∈ X) :
    y ^ Nat.card ↥X = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one]
  exact Subgroup.orderOf_dvd_natCard X hy

/-- If `2n = |X|+1` (e.g. `n = (|X|+1)/2`) and `y ∈ J(X,t)`, then `[t, yⁿ] = y`. -/
lemma commutatorElem_pow_eq_self {X : Subgroup G} {t y : G} {n : ℕ}
    (hy : y ∈ invertedBy X t) (h2n : 2 * n = Nat.card ↥X + 1) :
    commutatorElem t (y ^ n) = y := by
  rw [commutatorElem_pow_of_mem_invertedBy n hy, ← pow_add, ← two_mul, h2n, pow_succ,
    pow_natCard_eq_one_of_mem hy.1, one_mul]

/-- Equal commutators with `t` force `x x'⁻¹` to be centralised by `t`. -/
lemma conj_mul_inv_eq_of_commutatorElem_eq {t x x' : G}
    (h : commutatorElem t x = commutatorElem t x') :
    MulAut.conj t (x * x'⁻¹) = x * x'⁻¹ := by
  have h2 : MulAut.conj t x * ((MulAut.conj t x')⁻¹ * x') = x := by
    have hh := h
    simp only [commutatorElem] at hh
    calc MulAut.conj t x * ((MulAut.conj t x')⁻¹ * x')
        = MulAut.conj t x * ((MulAut.conj t x)⁻¹ * x) := by rw [hh]
      _ = x := by group
  have h1 : x * x'⁻¹ = MulAut.conj t x * (MulAut.conj t x')⁻¹ := by
    calc x * x'⁻¹ = (MulAut.conj t x * ((MulAut.conj t x')⁻¹ * x')) * x'⁻¹ := by rw [h2]
      _ = MulAut.conj t x * (MulAut.conj t x')⁻¹ := by group
  rw [map_mul, map_inv]
  exact h1.symm

/-! ## `K = K₁` -/

/-- For `x ∈ X`, `[t,x]` is an element of `X` inverted by `t`: `K ⊆ K₁`. -/
lemma commutatorSet_subset_invertedBy {X : Subgroup G} {t : G}
    (ht : orderOf t = 2) (hnorm : t ∈ Subgroup.normalizer (X : Set G)) :
    commutatorSet t X ⊆ invertedBy X t := by
  intro u hu
  rw [mem_commutatorSet] at hu
  obtain ⟨x, hx, rfl⟩ := hu
  rw [commutatorElem_eq ht]
  refine ⟨?_, ?_⟩
  · rw [commutatorElem]
    have hconj : MulAut.conj t x ∈ X := by
      simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp hnorm x).mp hx
    exact X.mul_mem (X.inv_mem hconj) hx
  · simpa [MulAut.conj_apply] using conj_commutatorElem ht x

/-- The converse inclusion: every element of `X` inverted by `t` is `[t, yⁿ]` for `n` with
`2n = |X|+1` (`|X|` odd), hence a commutator. -/
lemma invertedBy_subset_commutatorSet {X : Subgroup G} {t : G}
    (ht : orderOf t = 2) (hodd : Odd (Nat.card ↥X)) :
    invertedBy X t ⊆ commutatorSet t X := by
  intro y hy
  rw [mem_commutatorSet]
  have h2n : 2 * ((Nat.card ↥X + 1) / 2) = Nat.card ↥X + 1 := by
    rcases hodd with ⟨m, hm⟩
    omega
  exact ⟨y ^ ((Nat.card ↥X + 1) / 2), X.pow_mem hy.1 _,
    ((commutatorElem_eq ht _).trans (commutatorElem_pow_eq_self hy h2n)).symm⟩

/-! ## The bijection `V × K₁ ≃ X` and the product formula -/

/-- The exponent `(|X|+1)/2`, half of `|X|+1`; `y ↦ y^{(|X|+1)/2}` is the square root in `X`
when `|X|` is odd. -/
noncomputable def expo (X : Subgroup G) : ℕ := (Nat.card ↥X + 1) / 2

lemma two_mul_expo {X : Subgroup G} (hodd : Odd (Nat.card ↥X)) : 2 * expo X = Nat.card ↥X + 1 := by
  rw [expo]
  rcases hodd with ⟨m, hm⟩
  omega

/-- The map `(v,y) ↦ v·y^{(|X|+1)/2}` from `C_X(t) × J(X,t)` to `X` (Peterfalvi's bijection
`(x,y) ↦ xy` of `V × K` onto `X`, with the canonical choice `y ↦ y^{(|X|+1)/2}` of a square
root). -/
noncomputable def phiMap (X : Subgroup G) (t : G) :
    ↥(centralizerIn X t) × ↥(invertedBy X t) → ↥X :=
  fun p => ⟨(p.1 : G) * (p.2 : G) ^ expo X,
    X.mul_mem (Subgroup.mem_inf.mp (p.1).2).1 (X.pow_mem (p.2).2.1 (expo X))⟩

lemma phiMap_apply (X : Subgroup G) (t : G)
    (p : ↥(centralizerIn X t) × ↥(invertedBy X t)) :
    (phiMap X t p : G) = (p.1 : G) * (p.2 : G) ^ expo X := rfl

/-- Peterfalvi Appendix I (1)(b): `(x,y) ↦ xy` is a bijection of `C_X(t) × J(X,t)` onto `X`
(the canonical section `y ↦ y^{(|X|+1)/2}` makes both directions explicit). -/
lemma phiMap_bijective {X : Subgroup G} {t : G}
    (ht : orderOf t = 2) (hodd : Odd (Nat.card ↥X))
    (hnorm : t ∈ Subgroup.normalizer (X : Set G)) :
    Function.Bijective (phiMap X t) := by
  have h2n : 2 * expo X = Nat.card ↥X + 1 := two_mul_expo hodd
  constructor
  · rintro ⟨v₁, y₁⟩ ⟨v₂, y₂⟩ hpq
    -- `v₁·y₁^k = v₂·y₂^k` for `k = (|X|+1)/2`
    have hval : (v₁ : G) * (y₁ : G) ^ expo X = (v₂ : G) * (y₂ : G) ^ expo X := by
      have h := congrArg (fun z : ↥X => (z : G)) hpq
      rwa [phiMap_apply, phiMap_apply] at h
    -- applying `[t,·]` kills the `V`-parts (elements of `C_X(t)`) and returns `y`
    have hy : (y₁ : G) = (y₂ : G) := by
      have h1 : commutatorElem t ((v₁ : G) * (y₁ : G) ^ expo X)
          = commutatorElem t ((v₂ : G) * (y₂ : G) ^ expo X) := by rw [hval]
      rw [commutatorElem_mul_of_mem_centralizerIn v₁.2,
          commutatorElem_mul_of_mem_centralizerIn v₂.2,
          commutatorElem_pow_eq_self y₁.2 h2n,
          commutatorElem_pow_eq_self y₂.2 h2n] at h1
      exact h1
    have hv : (v₁ : G) = (v₂ : G) := by
      have h := hval
      rw [hy] at h
      exact mul_right_cancel h
    exact Prod.ext (Subtype.ext hv) (Subtype.ext hy)
  · intro z
    -- `y = [t,z] ∈ K₁` and `z = v·y^k` with `v = z·(y^k)⁻¹ ∈ C_X(t)`
    have hyK : commutatorElem t (z : G) ∈ invertedBy X t := by
      apply commutatorSet_subset_invertedBy ht hnorm
      rw [mem_commutatorSet]
      exact ⟨z, z.2, (commutatorElem_eq ht (z : G)).symm⟩
    have hpow : commutatorElem t ((commutatorElem t (z : G)) ^ expo X) = commutatorElem t (z : G) :=
      commutatorElem_pow_eq_self hyK h2n
    -- hence `z·(y^k)⁻¹` is centralised by `t`
    have hker : MulAut.conj t ((z : G) * ((commutatorElem t (z : G)) ^ expo X)⁻¹)
        = (z : G) * ((commutatorElem t (z : G)) ^ expo X)⁻¹ :=
      conj_mul_inv_eq_of_commutatorElem_eq (x := (z : G)) hpow.symm
    refine ⟨(⟨(z : G) * ((commutatorElem t (z : G)) ^ expo X)⁻¹, ?_⟩,
             ⟨commutatorElem t (z : G), hyK⟩), ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact X.mul_mem z.2 (X.inv_mem (X.pow_mem hyK.1 (expo X)))
      · exact Subgroup.mem_centralizer_singleton_iff.mpr ((conj_eq_iff_mul_comm t _).mp hker).symm
    · apply Subtype.ext
      rw [phiMap_apply]
      group

theorem app1_1b {G : Type} [Group G] [Finite G] {X : Subgroup G} {t : G}
    (ht : orderOf t = 2) (hodd : Odd (Nat.card ↥X))
    (hnorm : t ∈ Subgroup.normalizer (X : Set G)) :
    commutatorSet t X = Submission.Blueprint.invertedBy X t ∧
    Nat.card ↥X = Nat.card ↥(centralizerIn X t) * (Submission.Blueprint.invertedBy X t).ncard := by
  have hK : commutatorSet t X = Submission.Blueprint.invertedBy X t :=
    Set.Subset.antisymm (commutatorSet_subset_invertedBy ht hnorm)
      (invertedBy_subset_commutatorSet ht hodd)
  refine ⟨hK, ?_⟩
  have hbij : Function.Bijective (phiMap X t) := phiMap_bijective ht hodd hnorm
  have hcard := Nat.card_congr (Equiv.ofBijective (phiMap X t) hbij)
  rw [Nat.card_prod, Nat.card_coe_set_eq] at hcard
  exact hcard.symm

end Work.DoubleTransitivity.App1
