import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS

/-- If an ideal `I` of `K[X₀,X₁,X₂]` (`K` a field) contains two relatively prime elements `f`, `g`,
then every minimal prime of `I` has height at least `2`.

The point is that a minimal prime `𝔭` of `I` is a prime containing `f` and `g`; and in the UFD
`K[X₀,X₁,X₂]`, a prime of height `≤ 1` is either `⊥` (it contains only `0`, so `f = g = 0`, which is
excluded by `IsRelPrime 0 0 ↔ IsUnit 0`), or principal `(x)` (Mathlib's
`UniqueFactorizationMonoid.isPrincipal_of_height_eq_one`), in which case `x ∣ f` and `x ∣ g` force
`IsUnit x`, whence `𝔭 = ⊤`, contradicting primeness. -/
theorem minimalPrimes_height_two_of_relPrime {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin 3) K)) (f g : MvPolynomial (Fin 3) K)
    (hf : f ∈ I) (hg : g ∈ I) (hcop : IsRelPrime f g) :
    ∀ 𝔭 ∈ I.minimalPrimes, 2 ≤ 𝔭.height := by
  intro 𝔭 h𝔭
  have hf𝔭 : f ∈ 𝔭 := h𝔭.le hf
  have hg𝔭 : g ∈ 𝔭 := h𝔭.le hg
  by_contra hcon
  rw [not_le] at hcon
  rw [ENat.lt_two_iff] at hcon
  rcases Order.le_one_iff.mp hcon with h0 | h1
  · -- height `0`: in a domain the prime is `⊥`, so `f = g = 0`, against `IsRelPrime f g`.
    have hbot : 𝔭 = ⊥ := Ideal.height_eq_zero_iff_eq_bot.mp h0
    have hf0 : f = 0 := by simpa [hbot] using hf𝔭
    have hg0 : g = 0 := by simpa [hbot] using hg𝔭
    rw [hf0, hg0] at hcop
    exact not_isUnit_zero (isRelPrime_self.mp hcop)
  · -- height `1`: a height-one prime of a UFD is principal, `𝔭 = (x)`; then `x` divides both `f`
    -- and `g`, so `x` is a unit, making `𝔭 = ⊤`, which a prime ideal is not.
    obtain ⟨x, hx⟩ :=
      (@UniqueFactorizationMonoid.isPrincipal_of_height_eq_one (MvPolynomial (Fin 3) K) _ _
        _ 𝔭 h𝔭.isPrime h1).principal
    have hxdvd : x ∣ f := by
      rw [hx] at hf𝔭
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hf𝔭
      exact ⟨a, by simpa [smul_eq_mul, mul_comm] using ha.symm⟩
    have hgdvd : x ∣ g := by
      rw [hx] at hg𝔭
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hg𝔭
      exact ⟨a, by simpa [smul_eq_mul, mul_comm] using ha.symm⟩
    have hunit : IsUnit x := hcop hxdvd hgdvd
    have hxmem : x ∈ 𝔭 := by
      rw [hx]
      exact Submodule.mem_span_singleton.mpr ⟨1, one_smul _ _⟩
    exact h𝔭.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem 𝔭 hxmem hunit)

end Work.MotAS
