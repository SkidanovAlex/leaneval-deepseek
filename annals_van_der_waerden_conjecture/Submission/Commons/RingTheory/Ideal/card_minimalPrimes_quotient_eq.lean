import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

namespace Commons.RingTheory.Ideal

theorem card_minimalPrimes_quotient_eq {R : Type*} [CommRing R] (I : Ideal R) :
    Nat.card {q : Ideal (R ⧸ I) // q ∈ Ideal.minimalPrimes (⊥ : Ideal (R ⧸ I))}
      = Nat.card {p : Ideal R // p ∈ I.minimalPrimes} := by
  let mk := Ideal.Quotient.mk I
  have hker : RingHom.ker mk = I := Ideal.mk_ker
  have hforward : ∀ p : Ideal R, p ∈ I.minimalPrimes →
      p.map mk ∈ Ideal.minimalPrimes (⊥ : Ideal (R ⧸ I)) := by
    intro p hp
    have hpprime : p.IsPrime := hp.isPrime
    have hple : I ≤ p := hp.le
    have hpmin : ∀ y : Ideal R, y.IsPrime → I ≤ y → y ≤ p → p ≤ y :=
      fun y hy hyI hyple => hp.2 ⟨hy, hyI⟩ hyple

    show (⊥ : Ideal (R ⧸ I)).IsMinimalPrime (p.map mk)
    refine ⟨⟨Ideal.isPrime_map_quotientMk_of_isPrime hple, bot_le⟩, ?_⟩
    intro q hq hle
    have hqprime : q.IsPrime := hq.1

    have hcomapprime : (q.comap mk).IsPrime := inferInstance
    have hIle : I ≤ q.comap mk :=
      le_trans (le_of_eq hker.symm) (Ideal.ker_le_comap mk)
    have hle' : q.comap mk ≤ p := by
      rw [← Ideal.comap_map_mk hple]
      exact Ideal.comap_mono hle
    have hpge : p ≤ q.comap mk := hpmin (q.comap mk) hcomapprime hIle hle'
    have heq : q.comap mk = p := le_antisymm hle' hpge
    have heq2 : p.map mk = q := by
      rw [← heq, Ideal.map_comap_of_surjective mk Ideal.Quotient.mk_surjective]
    exact le_of_eq heq2
  have hbackward : ∀ q : Ideal (R ⧸ I), q ∈ Ideal.minimalPrimes (⊥ : Ideal (R ⧸ I)) →
      q.comap mk ∈ I.minimalPrimes := by
    intro q hq
    have hqprime : q.IsPrime := hq.isPrime
    have hqmin : ∀ y : Ideal (R ⧸ I), y.IsPrime → y ≤ q → q ≤ y :=
      fun y hy hyq => hq.2 ⟨hy, bot_le⟩ hyq

    show I.IsMinimalPrime (q.comap mk)
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · exact le_trans (le_of_eq hker.symm) (Ideal.ker_le_comap mk)
    · intro r hr hle
      have hrprime : r.IsPrime := hr.1
      have hrI : I ≤ r := hr.2

      have hrmap : (r.map mk).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hrI
      have hle' : r.map mk ≤ q :=
        (Ideal.map_mono hle).trans
          (le_of_eq (Ideal.map_comap_of_surjective mk Ideal.Quotient.mk_surjective q))
      have hqle : q ≤ r.map mk := hqmin (r.map mk) hrmap hle'
      have heq : r.map mk = q := le_antisymm hle' hqle
      have heq2 : q.comap mk = r := by
        rw [← heq, Ideal.comap_map_mk hrI]
      exact le_of_eq heq2
  refine Nat.card_congr ?_
  refine
    { toFun := fun q => ⟨q.1.comap mk, hbackward q.1 q.2⟩
      invFun := fun p => ⟨p.1.map mk, hforward p.1 p.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro q
    exact Subtype.ext (Ideal.map_comap_of_surjective mk Ideal.Quotient.mk_surjective q.1)
  · intro p
    exact Subtype.ext (Ideal.comap_map_mk p.2.le)

end Commons.RingTheory.Ideal