import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.TameStructureDeep.Tame.primeToPart_spec
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The prime-to-`p` part of a natural number at a place

For a number field `K`, a place `𝔭` with residue characteristic `p = resCharAt 𝔭` and a natural
number `m`, the *prime-to-`p` part* of `m` is

  `primeToPart 𝔭 m = m / p ^ (m.factorization p)`,

the largest divisor of `m` coprime to `p`.  It is the order of the tame inertia quotient
`Gal(κ^{ur}(π^{1/m})/κ^{ur}) = ℤ/primeToPart 𝔭 m` at the layer `m`, and hence the order of the
finite quotient of `I_κ/V_κ = Gal(κ^{tr}/κ^{ur})` cut out by the layer of `m`-th powers; this is
the form in which the chapter `Tame/` uses it.
-/
set_option linter.unusedVariables false

open scoped Classical

namespace NK.TameStructureDeep.Tame

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))

/-- **The prime-to-`p` part of `m` at the place `𝔭`**: the largest divisor of `m` coprime to the
residue characteristic `p = resCharAt 𝔭`. -/
def primeToPart (m : ℕ) : ℕ := m / (resCharAt 𝔭) ^ (m.factorization (resCharAt 𝔭))

/-- The defining property of the prime-to-`p` part: for `m ≠ 0` it divides `m`, is coprime to `p`,
and every divisor of `m` coprime to `p` divides it. -/
theorem primeToPart_spec' {m : ℕ} (hm : m ≠ 0) :
    (primeToPart 𝔭 m ∣ m) ∧ Nat.Coprime (primeToPart 𝔭 m) (resCharAt 𝔭) ∧
      ∀ g : ℕ, g ∣ m → ¬ resCharAt 𝔭 ∣ g → g ∣ primeToPart 𝔭 m :=
  primeToPart_spec 𝔭 m hm

/-- `d₀ = primeToPart 𝔭 m` divides `m`. -/
theorem primeToPart_dvd {m : ℕ} (hm : m ≠ 0) : primeToPart 𝔭 m ∣ m :=
  (primeToPart_spec' 𝔭 hm).1

/-- `d₀ = primeToPart 𝔭 m` is coprime to the residue characteristic. -/
theorem primeToPart_coprime {m : ℕ} (hm : m ≠ 0) : Nat.Coprime (primeToPart 𝔭 m) (resCharAt 𝔭) :=
  (primeToPart_spec' 𝔭 hm).2.1

/-- The residue characteristic does not divide `d₀ = primeToPart 𝔭 m`. -/
theorem not_dvd_primeToPart {m : ℕ} (hm : m ≠ 0) : ¬ resCharAt 𝔭 ∣ primeToPart 𝔭 m :=
  (Nat.Prime.coprime_iff_not_dvd (NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭)).mp
    (Nat.coprime_comm.mp (primeToPart_coprime 𝔭 hm))

/-- `d₀ = primeToPart 𝔭 m` is positive when `m > 0`. -/
theorem primeToPart_pos {m : ℕ} (hm : 0 < m) : 0 < primeToPart 𝔭 m :=
  Nat.pos_of_dvd_of_pos (primeToPart_dvd 𝔭 hm.ne') hm

/-- `d₀ = primeToPart 𝔭 m` is nonzero when `m > 0`. -/
theorem primeToPart_ne_zero {m : ℕ} (hm : 0 < m) : primeToPart 𝔭 m ≠ 0 :=
  (primeToPart_pos 𝔭 hm).ne'

end

end NK.TameStructureDeep.Tame
