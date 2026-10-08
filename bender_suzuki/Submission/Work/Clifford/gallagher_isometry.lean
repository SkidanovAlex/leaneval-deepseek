import Mathlib
import Submission.Work.Clifford.Orbit
import Submission.Work.Clifford.coset_sum_char_norm
import Submission.Work.Clifford.sum_G_eq_sum_quotient_mul

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.gallagher_isometry`

Gallagher's isometry: if `N ⊴ G`, `θ ∈ Irr N` extends to `χ ∈ Irr G` (so that `χ|_N = θ`),
then for arbitrary functions `u v : G ⧸ N → ℂ` on the quotient,

`⟪χ · Inf u, χ · Inf v⟫_G = ⟪u, v⟫_{G ⧸ N}`.

The proof groups the sum over `G` into the sums over the `N`-cosets; the key input is that
`∑_{n ∈ N} |χ (g n)|² = |N|` for every `g : G` (`Work.Clifford.coset_sum_char_norm`),
a consequence of `χ|_N` being an irreducible character of `N`.
-/

noncomputable section

open Classical

namespace Work.Clifford

/-- The un-normalised isometry: the sum over `G` of `(χ · Inf u) * conj ((χ · Inf v))` equals
`|N|` times the corresponding sum over `G ⧸ N`. -/
theorem sum_mul_inflate_cfInner {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    [Fintype N] [Fintype (G ⧸ N)]
    {θ : N → ℂ} (hθ : θ ∈ Irr N) {χ : G → ℂ} (hχ : χ ∈ Irr G) (hext : Extends N χ θ)
    (u v : G ⧸ N → ℂ) :
    ∑ g : G, (χ * inflateFun N u) g * starRingEnd ℂ ((χ * inflateFun N v) g)
      = (Nat.card N : ℂ) * ∑ x : G ⧸ N, u x * starRingEnd ℂ (v x) := by
  have hclass : IsClassFun χ := IsClassFun.of_mem_Irr hχ
  have hterm : ∀ g : G, (χ * inflateFun N u) g * starRingEnd ℂ ((χ * inflateFun N v) g)
      = (χ g * starRingEnd ℂ (χ g))
        * (u (QuotientGroup.mk (s := N) g)
            * starRingEnd ℂ (v (QuotientGroup.mk (s := N) g))) := by
    intro g
    simp only [Pi.mul_apply, inflateFun, map_mul]
    ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g)]
  rw [sum_G_eq_sum_quotient_mul (N := N)
        (fun g => (χ g * starRingEnd ℂ (χ g))
          * (u (QuotientGroup.mk (s := N) g)
              * starRingEnd ℂ (v (QuotientGroup.mk (s := N) g))))]
  have hmk : ∀ (x : G ⧸ N) (n : N),
      QuotientGroup.mk (s := N) ((n : G) * Quotient.out x) = x := by
    intro x n
    rw [QuotientGroup.mk_mul]
    rw [(QuotientGroup.eq_one_iff (n : G)).mpr n.2, one_mul]
    exact Quotient.out_eq x
  have hconjterm : ∀ (x : G ⧸ N) (n : N),
      χ ((n : G) * Quotient.out x) = χ (Quotient.out x * (n : G)) := by
    intro x n
    have h := hclass (Quotient.out x * (n : G)) (Quotient.out x)⁻¹
    rw [show (Quotient.out x)⁻¹ * (Quotient.out x * (n : G)) * (Quotient.out x)⁻¹⁻¹
          = (n : G) * Quotient.out x by group] at h
    exact h
  have hinner : ∀ x : G ⧸ N,
      ∑ n : N, (χ ((n : G) * Quotient.out x) * starRingEnd ℂ (χ ((n : G) * Quotient.out x)))
          * (u (QuotientGroup.mk (s := N) ((n : G) * Quotient.out x))
              * starRingEnd ℂ (v (QuotientGroup.mk (s := N) ((n : G) * Quotient.out x))))
        = (Nat.card N : ℂ) * (u x * starRingEnd ℂ (v x)) := by
    intro x
    have hstep : ∀ n : N,
        (χ ((n : G) * Quotient.out x) * starRingEnd ℂ (χ ((n : G) * Quotient.out x)))
          * (u (QuotientGroup.mk (s := N) ((n : G) * Quotient.out x))
              * starRingEnd ℂ (v (QuotientGroup.mk (s := N) ((n : G) * Quotient.out x))))
        = (χ (Quotient.out x * (n : G)) * starRingEnd ℂ (χ (Quotient.out x * (n : G))))
          * (u x * starRingEnd ℂ (v x)) := by
      intro n
      rw [hmk x n, hconjterm x n]
    rw [Finset.sum_congr rfl (fun n _ => hstep n), ← Finset.sum_mul,
      coset_sum_char_norm hθ hχ hext (Quotient.out x)]
  rw [Finset.sum_congr rfl (fun x _ => hinner x), Finset.mul_sum]

theorem gallagher_isometry {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal] [Fintype N]
    [Fintype (G ⧸ N)]
    {θ : N → ℂ} (hθ : θ ∈ Work.Clifford.Irr N) {χ : G → ℂ} (hχ : χ ∈ Work.Clifford.Irr G)
    (hext : Work.Clifford.Extends N χ θ) (u v : G ⧸ N → ℂ) :
    Work.Clifford.cfInner (χ * Work.Clifford.inflateFun N u) (χ * Work.Clifford.inflateFun N v)
      = Work.Clifford.cfInner u v := by
  have hmain := sum_mul_inflate_cfInner hθ hχ hext u v
  rw [cfInner_apply, cfInner_apply, hmain, Nat.card_eq_fintype_card]
  have hcardnat : Nat.card ↥N * Nat.card (G ⧸ N) = Nat.card G := by
    rw [← Subgroup.card_mul_index N, Subgroup.index_eq_card N]
  have hcard : (Fintype.card G : ℂ) = (Fintype.card N : ℂ) * (Fintype.card (G ⧸ N) : ℂ) := by
    have h1 : Fintype.card G = Nat.card G := Fintype.card_eq_nat_card
    have h2 : Fintype.card N = Nat.card ↥N := Fintype.card_eq_nat_card
    have h3 : Fintype.card (G ⧸ N) = Nat.card (G ⧸ N) := Fintype.card_eq_nat_card
    rw [h1, h2, h3, ← hcardnat, Nat.cast_mul]
  have hNne : (Fintype.card N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hkey : (Fintype.card G : ℂ)⁻¹ * (Fintype.card N : ℂ)
      = (Fintype.card (G ⧸ N) : ℂ)⁻¹ := by
    rw [hcard, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hNne, mul_one]
  rw [← mul_assoc, hkey]

end Work.Clifford
