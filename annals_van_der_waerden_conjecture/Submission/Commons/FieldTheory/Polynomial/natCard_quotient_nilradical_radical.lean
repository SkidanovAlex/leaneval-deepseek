import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Radical.Basic
import Mathlib.RingTheory.SimpleRing.Principal

open Polynomial

namespace Commons.FieldTheory.Polynomial

-- Component 1: quotient by nilradical of a quotient is the quotient by the radical.
noncomputable def nilradical_quotient_equiv (R : Type*) [CommRing R] (I : Ideal R) :
    (R ⧸ I) ⧸ nilradical (R ⧸ I) ≃+* R ⧸ I.radical := by
  let S : Type _ := R ⧸ I
  let N : Ideal S := nilradical S
  let ψ : R →+* S ⧸ N := (Ideal.Quotient.mk N).comp (Ideal.Quotient.mk I)
  have hsurj : Function.Surjective ψ := by
    dsimp [ψ]
    exact Function.Surjective.comp (Ideal.Quotient.mk_surjective (I := N))
      (Ideal.Quotient.mk_surjective (I := I))
  have hker : RingHom.ker ψ = I.radical := by
    ext x
    constructor
    · intro hx
      rw [Ideal.mem_radical_iff]
      have hx0 : (Ideal.Quotient.mk (nilradical (R ⧸ I))) ((Ideal.Quotient.mk I) x) = 0 := by
        dsimp [ψ, S, N] at hx
        exact hx
      have hm : (Ideal.Quotient.mk I) x ∈ nilradical (R ⧸ I) :=
        (Ideal.Quotient.eq_zero_iff_mem).mp hx0
      have hn : IsNilpotent ((Ideal.Quotient.mk I) x) := (mem_nilradical).mp hm
      rcases hn with ⟨n, hnpow⟩
      refine ⟨n, ?_⟩
      apply (Ideal.Quotient.eq_zero_iff_mem).mp
      rw [map_pow]
      exact hnpow
    · intro hx
      rw [Ideal.mem_radical_iff] at hx
      rcases hx with ⟨n, hn⟩
      dsimp [ψ, S, N]
      apply (Ideal.Quotient.eq_zero_iff_mem).mpr
      rw [mem_nilradical]
      refine ⟨n, ?_⟩
      rw [← map_pow]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr hn
  exact ((ψ.quotientKerEquivOfSurjective hsurj).symm).trans
    (Ideal.quotEquivOfEq (I := RingHom.ker ψ) (J := I.radical) hker)

-- Component 2: radical of the principal ideal (g) is the principal ideal of the element radical.
lemma radical_span_singleton {F : Type*} [Field F] [DecidableEq F] (g : F[X]) (hg : g ≠ 0) :
    (Ideal.span ({g} : Set (F[X]))).radical =
      Ideal.span ({UniqueFactorizationMonoid.radical g} : Set (F[X])) := by
  ext x
  constructor
  · intro hx
    rw [Ideal.mem_span_singleton]
    rw [Ideal.mem_radical_iff] at hx
    rcases hx with ⟨n, hn⟩
    have hdvd : g ∣ x ^ n := by simpa [Ideal.mem_span_singleton] using hn
    exact (UniqueFactorizationMonoid.exists_dvd_pow_iff_radical_dvd (a := g) (b := x) hg).mp ⟨n, hdvd⟩
  · intro hx
    rw [Ideal.mem_radical_iff]
    rw [Ideal.mem_span_singleton] at hx
    rcases (UniqueFactorizationMonoid.exists_dvd_pow_iff_radical_dvd (a := g) (b := x) hg).mpr hx with ⟨n, hdvd⟩
    refine ⟨n, ?_⟩
    simpa [Ideal.mem_span_singleton] using hdvd

-- Main theorem
theorem natCard_quotient_nilradical_radical {F : Type*} [Field F] [DecidableEq F] (g : F[X])
    (hg : g ≠ 0) :
    Nat.card ((F[X] ⧸ Ideal.span ({g} : Set (F[X]))) ⧸
      nilradical (F[X] ⧸ Ideal.span ({g} : Set (F[X])))) =
      Nat.card (F[X] ⧸ Ideal.span ({UniqueFactorizationMonoid.radical g} : Set (F[X]))) := by
  let I : Ideal F[X] := Ideal.span ({g} : Set F[X])
  have hrad : I.radical = Ideal.span ({UniqueFactorizationMonoid.radical g} : Set F[X]) := by
    dsimp [I]
    exact radical_span_singleton (F := F) g hg
  let e : ((F[X] ⧸ I) ⧸ nilradical (F[X] ⧸ I)) ≃+*
      (F[X] ⧸ Ideal.span ({UniqueFactorizationMonoid.radical g} : Set F[X])) :=
    (nilradical_quotient_equiv (F[X]) I).trans
      (Ideal.quotEquivOfEq (I := I.radical)
        (J := Ideal.span ({UniqueFactorizationMonoid.radical g} : Set F[X])) hrad)
  simpa [I] using (Nat.card_congr e)

end Commons.FieldTheory.Polynomial