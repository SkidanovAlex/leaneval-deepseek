import Mathlib

namespace Work.CORE2A

/-- If `H ≤ K`, `K` normalizes `H`, and the relative index `[K : H]` is odd, then every
element of `K` whose order is a power of two already lies in `H`.

Proof: `H` is normal in `K`, so `K ⧸ H` is a group of order `[K : H]`, which is odd.
The image of `g` in `K ⧸ H` has order dividing both `orderOf g` (a power of two) and
the odd number `[K : H]`; hence its order is `1`, so `g` lies in the kernel `H`. -/
theorem c14_oddIndex {G : Type} [Group G] {H K : Subgroup G}
    (hHK : H ≤ K) (hnorm : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H) (hodd : Odd (H.relIndex K))
    {g : G} (hg : g ∈ K) {n : ℕ} (hpow : g ^ (2 ^ n) = 1) : g ∈ H := by
  -- `H`, viewed as a subgroup of `K`, is normal in `K`.
  let N : Subgroup K := H.subgroupOf K
  have hN : N.Normal := by
    refine Subgroup.Normal.mk ?_
    intro a ha b
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hnorm (b : G) b.2 (a : G) ha
  haveI := hN
  -- `g` as an element of `K`.
  let a : K := ⟨g, hg⟩
  have hpowK : a ^ (2 ^ n) = 1 := by
    apply Subtype.ext
    simp [a, hpow]
  -- The order of `a` divides `2 ^ n`.
  have hdvd1 : orderOf a ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hpowK
  -- The order of the image of `a` in `K ⧸ H` divides `orderOf a` ...
  have hdvd3 : orderOf ((QuotientGroup.mk' N) a) ∣ orderOf a := orderOf_map_dvd _ a
  -- ... and divides the order of the quotient, which is `[K : H]` (odd).
  have hdvd2 : orderOf ((QuotientGroup.mk' N) a) ∣ Nat.card (K ⧸ N) := orderOf_dvd_natCard _
  have hcard : Nat.card (K ⧸ N) = H.relIndex K := rfl
  have hcop : Nat.Coprime (2 ^ n) (H.relIndex K) := (hodd.coprime_two_right.symm).pow_left n
  have hone : orderOf ((QuotientGroup.mk' N) a) = 1 := by
    have hdiv : orderOf ((QuotientGroup.mk' N) a) ∣ Nat.gcd (2 ^ n) (H.relIndex K) :=
      Nat.dvd_gcd (hdvd3.trans hdvd1) (by rw [hcard] at hdvd2; exact hdvd2)
    rw [hcop.gcd_eq_one] at hdiv
    exact Nat.dvd_one.mp hdiv
  have ha1 : (QuotientGroup.mk' N) a = 1 := orderOf_eq_one_iff.mp hone
  have haN : a ∈ N := by
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
    exact ha1
  have hgH : (a : G) ∈ H := Subgroup.mem_subgroupOf.mp haN
  simpa [a] using hgH

end Work.CORE2A
