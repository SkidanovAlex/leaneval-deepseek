import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute.ExtChain

/-- Abstract Sylow reduction: let `x` in an additive commutative group satisfy `Nat.card G • x = 0`
and let `[G : P] • x = 0` for every Sylow `p`-subgroup `P ≤ G`. Then `x = 0`.

Proof: `d = addOrderOf x` divides `Nat.card G` and every Sylow index `[G : P]`; if `d ≠ 1`, pick a
prime `p ∣ d` (`Nat.exists_prime_and_dvd`), take a Sylow `p`-subgroup `P` (`Sylow.nonempty`, which
exists for every `p` as a maximal `p`-subgroup) and get `p ∣ [G : P]`, contradicting
`Sylow.not_dvd_index`. -/
theorem smul_eq_zero_of_sylow {G : Type} [Group G] [Fintype G] {A : Type} [AddCommGroup A]
    (x : A) (hcard : Nat.card G • x = 0)
    (hsyl : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G), (P : Subgroup G).index • x = 0) :
    x = 0 := by
  by_contra hx
  set d := addOrderOf x with hddef
  -- `Nat.card G • x = 0` gives `addOrderOf x ∣ Nat.card G`
  have hdG : d ∣ Nat.card G := (addOrderOf_dvd_iff_nsmul_eq_zero).mpr hcard
  -- If `d = 1` then `x = 0`, so `d ≠ 1`.
  have hd1 : d ≠ 1 := by
    intro h
    apply hx
    have h1 : (1 : ℕ) • x = 0 := by
      rw [← h, hddef]
      exact (addOrderOf_dvd_iff_nsmul_eq_zero (x := x)).mp (dvd_refl d)
    simpa using h1
  -- Pick a prime `p ∣ d`.
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
  haveI : Fact p.Prime := ⟨hp⟩
  -- Take a Sylow `p`-subgroup `P`.
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
  -- `[G : P] • x = 0` gives `d ∣ [G : P]`, hence `p ∣ [G : P]`.
  have hpidx : p ∣ (P : Subgroup G).index :=
    dvd_trans hpd ((addOrderOf_dvd_iff_nsmul_eq_zero (x := x)).mpr (hsyl p P))
  -- A `Subgroup` of a finite group has finite index.
  haveI : (P : Subgroup G).FiniteIndex := inferInstance
  -- But Sylow's theorem gives `¬ p ∣ [G : P]`.
  exact Sylow.not_dvd_index P hpidx

end Work.SSGRoute.ExtChain
