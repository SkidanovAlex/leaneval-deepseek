import Mathlib
import Submission.Work.Tower.FrattiniLayer.Basic
import Submission.Work.Tower.FrattiniLayer.count_spanSingleton_eq_neg_log
import Submission.Work.Tower.FrattiniLayer.isPow_of_count_dvd

/-!
# A cube relation over an unramified extension forces the ideal to be a cube

Let `L ⊆ M` be an extension of number fields which is unramified at every finite prime, let
`α ∈ Lˣ` and `β ∈ M` with `β ^ 3 = α` (inside `M`).  Then the fractional ideal `(α)` of `𝓞 L` is
the cube of a fractional ideal of `𝓞 L`, i.e. `α` lies in `cubeIdealSubgroup L`.

The proof is local at every prime `𝔭` of `𝓞 L`.  Pick a prime `𝔓` of `𝓞 M` above `𝔭`; since
`M/L` is unramified, `𝔓` has ramification index `1` over `𝔭`, so for every `x ∈ L` the adic
valuation `v_𝔓 ∘ (L ↪ M)` equals `v_𝔭` (`valuation_algebraMap_eq_of_ramificationIdx_eq_one`).
Hence, writing `c_𝔭` for `count L 𝔭` (the exponent of `𝔭` in the factorization of `(α)`, which is
`-log (v_𝔭 α)`), we get

`c_𝔭 = -log (v_𝔓 α) = -log ((v_𝔓 β) ^ 3) = -3 · log (v_𝔓 β)`,

so `3 ∣ c_𝔭`.  Since a nonzero fractional ideal of a Dedekind domain is determined by the family
`(c_𝔭)`, and divisible exponents allow an integral cube root `(α) = 𝔞 ^ 3`, the conclusion
follows.
-/

set_option linter.style.haveILetI false

open NumberField
open scoped Classical nonZeroDivisors

namespace Work.Tower.FrattiniLayer

/-- **The valuation of a base element under an unramified prime.**  If `𝔓` lies over `𝔭` and the
ramification index of `𝔓` over `𝔭` is `1`, then the two adic valuations of `x ∈ L` agree (up to
the identification `L ↪ M`). -/
theorem valuation_algebraMap_eq_of_ramificationIdx_eq_one {L M : Type*} [Field L] [NumberField L]
    [Field M] [NumberField M] [Algebra L M] [FiniteDimensional L M]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (𝔓 : IsDedekindDomain.HeightOneSpectrum (𝓞 M))
    (hlie : 𝔓.asIdeal.LiesOver 𝔭.asIdeal)
    (hram : 𝔓.asIdeal.ramificationIdx (𝓞 L) = 1) (x : L) :
    𝔓.valuation M (algebraMap L M x) = 𝔭.valuation L x := by
  letI := hlie
  have h' : 𝔭.asIdeal.ramificationIdx' 𝔓.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx 𝔭.asIdeal 𝔓.asIdeal 𝔭.ne_bot, hram]
  have h2 := IsDedekindDomain.HeightOneSpectrum.valuation_liesOver (A := 𝓞 L) (B := 𝓞 M) M 𝔭 𝔓 x
  rw [h', pow_one] at h2
  exact h2.symm

theorem isCubeIdeal_of_unramified {L M : Type*} [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra L M] [FiniteDimensional L M] (α : Lˣ) (β : M)
    (hβ : β ^ 3 = algebraMap L M (α : L))
    (hunr : Work.Tower.FrattiniLayer.IsUnramifiedOver L M) :
    α ∈ Work.Tower.FrattiniLayer.cubeIdealSubgroup L := by
  set A : FractionalIdeal (𝓞 L)⁰ L := FractionalIdeal.spanSingleton (𝓞 L)⁰ (α : L) with hA
  have hA0 : A ≠ 0 := by
    rw [hA, FractionalIdeal.spanSingleton_ne_zero_iff]
    exact Units.ne_zero α
  -- the exponent of every prime in `(α)` is divisible by `3`
  have hdiv : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
      (3 : ℤ) ∣ FractionalIdeal.count L v A := by
    intro v
    obtain ⟨𝔓, h𝔓mem⟩ := (inferInstance : Nonempty ↑(v.asIdeal.primesOver (𝓞 M))).some
    have h𝔓prime : 𝔓.IsPrime := h𝔓mem.1
    have h𝔓lie : 𝔓.LiesOver v.asIdeal := h𝔓mem.2
    haveI := h𝔓prime
    haveI : Algebra.IsUnramifiedAt (𝓞 L) 𝔓 := hunr 𝔓
    have h𝔓nebot : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver v.ne_bot h𝔓mem
    let w : IsDedekindDomain.HeightOneSpectrum (𝓞 M) := ⟨𝔓, h𝔓prime, h𝔓nebot⟩
    have hram : 𝔓.ramificationIdx (𝓞 L) = 1 := Ideal.ramificationIdx_eq_one 𝔓 (𝓞 L)
    have hvaleq : w.valuation M (algebraMap L M (α : L)) = v.valuation L (α : L) :=
      valuation_algebraMap_eq_of_ramificationIdx_eq_one v w h𝔓lie hram (α : L)
    have hcount := count_spanSingleton_eq_neg_log (R := 𝓞 L) (K := L) v (α : L)
    rw [hA, hcount, ← hvaleq, ← hβ, Valuation.map_pow, WithZero.log_pow]
    exact ⟨-(w.valuation M β).log, by simp only [nsmul_eq_mul]; ring⟩
  obtain ⟨J, hJ⟩ := isPow_of_count_dvd 3 (by norm_num) hA0 hdiv
  have hJ0 : J ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at hJ
    exact hA0 hJ.symm
  exact ⟨Units.mk0 J hJ0, by rw [Units.val_mk0, hJ, hA]⟩

end Work.Tower.FrattiniLayer
