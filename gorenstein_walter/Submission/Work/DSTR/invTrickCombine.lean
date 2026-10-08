import Mathlib
import Submission.Work.DSTR.invTrickPre

namespace Work.DSTR

/-- **Combination step of the inversion trick.**

If an automorphism `ξ` of a finite group `G` fixes a subgroup `N` pointwise and maps every
`x` into the coset `x · N` (equivalently, acts trivially on `G ⧸ N`), and `orderOf ξ` is
coprime to `|N|`, then `ξ` is the identity.

The proof is the elementary "difference-map" argument.  Writing `u = ξ x * x⁻¹ ∈ N`, the
element `u` is fixed by `ξ`, so `ξ` kills the coset of `x` exactly by multiplying by `u`;
by induction `(ξ ^ k) x = u ^ k * x`.  Taking `k = orderOf ξ` gives `u ^ orderOf ξ = 1`, so
`orderOf u` divides both `orderOf ξ` and `|N|`, which are coprime; hence `u = 1` and `ξ x = x`. -/
theorem invTrickCombine {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    (ξ : MulAut G) (hNfix : ∀ y ∈ N, ξ y = y) (hN : ∀ x : G, ξ x * x⁻¹ ∈ N)
    (hcop : Nat.Coprime (orderOf ξ) (Nat.card ↥N)) : ξ = 1 := by
  apply MulEquiv.ext
  intro x
  simp only [MulAut.one_apply]
  -- the "difference" element, which lies in `N` and is therefore fixed by `ξ`
  set u : G := ξ x * x⁻¹ with hu
  have huN : u ∈ N := hN x
  have hufix : ξ u = u := hNfix u huN
  have hux : u * x = ξ x := by rw [hu]; group
  -- the key computation: `ξ ^ k` acts on `x` by multiplying by `u ^ k`
  have hpow : ∀ k : ℕ, (ξ ^ k) x = u ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hufix]
      rw [← hux, pow_succ, ← mul_assoc]
  -- hence `u` has order dividing `orderOf ξ`
  have hum : u ^ orderOf ξ = 1 := by
    have h1 := hpow (orderOf ξ)
    rw [pow_orderOf_eq_one, MulAut.one_apply] at h1
    have h2 : u ^ orderOf ξ * x = 1 * x := by rw [one_mul]; exact h1.symm
    exact mul_right_cancel h2
  -- `orderOf u` divides both `orderOf ξ` and `|N|`, which are coprime
  have hdvdξ : orderOf u ∣ orderOf ξ := orderOf_dvd_of_pow_eq_one hum
  have hcopu : Nat.Coprime (orderOf u) (Nat.card ↥N) :=
    Nat.Coprime.coprime_dvd_left hdvdξ hcop
  have hdvdN : orderOf u ∣ Nat.card ↥N := by
    have h := orderOf_dvd_natCard (⟨u, huN⟩ : ↥N)
    rwa [Subgroup.orderOf_mk] at h
  have hone : orderOf u = 1 := hcopu.eq_one_of_dvd hdvdN
  have hu1 : u = 1 := orderOf_eq_one_iff.mp hone
  rw [← hux, hu1, one_mul]

end Work.DSTR
