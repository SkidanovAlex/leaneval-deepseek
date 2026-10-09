import Mathlib
import Submission.NK.LocalInputs.Inputs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalInputs.PowerQuotient

/-- **The `p`-th power map on the units of a finite field of characteristic `p` is onto.**

In a finite field `F` of characteristic `p` the unit group `Fˣ` has cardinality `|F| - 1`,
and `|F| = p ^ n` is a power of `p`; since `p` is coprime to `p ^ n - 1`, the `p`-th power
endomorphism of `Fˣ` is surjective, so its cokernel `Fˣ ⧸ (powMonoidHom p).range` is trivial. -/
theorem natCard_units_quot_pow_eq_one_of_finite_field (F : Type*) [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (hchar : CharP F p) :
    Nat.card (Fˣ ⧸ (powMonoidHom p).range) = 1 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI hfin : Finite Fˣ := Finite.of_injective (Units.val : Fˣ → F) Units.val_injective
  haveI : IsCyclic Fˣ := inferInstance
  haveI : CharP F p := hchar
  rw [Commons.GroupTheory.SpecificGroups.Cyclic.card_quotient_powMonoidHom (G := Fˣ) p]
  obtain ⟨n, -, hcard⟩ := FiniteField.card F p
  have hcu : Fintype.card Fˣ = Fintype.card F - 1 := Fintype.card_units F
  rw [hcu, hcard]
  have hn0 : (n : ℕ) ≠ 0 := n.pos.ne'
  have hpos : 0 < p ^ (n : ℕ) := pow_pos hp.pos _
  have h1 : Nat.gcd p (p ^ (n : ℕ) - 1) ∣ p ^ (n : ℕ) :=
    (Nat.gcd_dvd_left p (p ^ (n : ℕ) - 1)).trans (dvd_pow_self p hn0)
  have h2 : Nat.gcd p (p ^ (n : ℕ) - 1) ∣ p ^ (n : ℕ) - 1 :=
    Nat.gcd_dvd_right p (p ^ (n : ℕ) - 1)
  have h3 : Nat.gcd p (p ^ (n : ℕ) - 1) ∣ p ^ (n : ℕ) - (p ^ (n : ℕ) - 1) :=
    Nat.dvd_sub h1 h2
  have hsub : p ^ (n : ℕ) - (p ^ (n : ℕ) - 1) = 1 := by omega
  rw [hsub] at h3
  exact Nat.dvd_one.mp h3

theorem natCard_residueUnits_quot_pow_eq_one {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hp : p.Prime) (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    Nat.card ((IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))ˣ ⧸
      (powMonoidHom p).range) = 1 := by
  haveI : Finite (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion K 𝔭
  exact natCard_units_quot_pow_eq_one_of_finite_field _ hp hchar

end NK.LocalInputs.PowerQuotient
