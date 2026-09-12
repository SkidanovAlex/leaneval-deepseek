import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.Maps

set_option linter.style.haveILetI false

namespace Commons.RingTheory.Ideal

/-- If `φ : A →+* B` is surjective and `q` is a minimal prime over `I ≤ B`, then the contraction
`q.comap φ` is a minimal prime over `I.comap φ`. -/
theorem minimalPrimes_comap_of_surjective {A B : Type*} [CommSemiring A] [CommSemiring B]
    (φ : A →+* B) (hφ : Function.Surjective φ) {I q : Ideal B} (hq : q ∈ I.minimalPrimes) :
    Ideal.comap φ q ∈ (I.comap φ).minimalPrimes := by
  haveI : q.IsPrime := hq.isPrime
  refine ⟨⟨inferInstance, Ideal.comap_mono hq.le⟩, ?_⟩
  intro r hr hle
  haveI : r.IsPrime := hr.1
  obtain ⟨r₀, hr₀, hr₀le⟩ := Ideal.exists_minimalPrimes_le (I := I.comap φ) (J := r) hr.2
  obtain ⟨q₀, hq₀, hq₀eq⟩ := Ideal.exists_minimalPrimes_comap_eq φ r₀ hr₀
  have hle₀ : q₀ ≤ q :=
    (Ideal.comap_le_comap_iff_of_surjective φ hφ q₀ q).1 (by rw [hq₀eq]; exact hr₀le.trans hle)
  have hge : q ≤ q₀ := hq.2 ⟨hq₀.isPrime, hq₀.le⟩ hle₀
  have hEq : r₀ = Ideal.comap φ q := by rw [← hq₀eq, le_antisymm hle₀ hge]
  rw [hEq] at hr₀le
  exact hr₀le

theorem card_minimalPrimes_comap_eq {A B : Type} [CommSemiring A] [CommSemiring B] (φ : A →+* B)
    (hφ : Function.Surjective φ) (I : Ideal B) :
    Nat.card {p : Ideal A // p ∈ (I.comap φ).minimalPrimes} =
      Nat.card {p : Ideal B // p ∈ I.minimalPrimes} := by
  refine Nat.card_congr ?_
  let fwd : {p : Ideal A // p ∈ (I.comap φ).minimalPrimes} →
      {p : Ideal B // p ∈ I.minimalPrimes} := fun p =>
    ⟨Classical.choose (Ideal.exists_minimalPrimes_comap_eq φ p.1 p.2),
      (Classical.choose_spec (Ideal.exists_minimalPrimes_comap_eq φ p.1 p.2)).1⟩
  have hfwd : ∀ p, Ideal.comap φ (fwd p).1 = p.1 := fun p =>
    (Classical.choose_spec (Ideal.exists_minimalPrimes_comap_eq φ p.1 p.2)).2
  refine
    { toFun := fwd
      invFun := fun q => ⟨Ideal.comap φ q.1, minimalPrimes_comap_of_surjective φ hφ q.2⟩
      left_inv := fun p => Subtype.ext (hfwd p)
      right_inv := ?_ }
  intro q
  apply Subtype.ext
  apply Ideal.comap_injective_of_surjective φ hφ
  rw [hfwd ⟨Ideal.comap φ q.1, minimalPrimes_comap_of_surjective φ hφ q.2⟩]

end Commons.RingTheory.Ideal
