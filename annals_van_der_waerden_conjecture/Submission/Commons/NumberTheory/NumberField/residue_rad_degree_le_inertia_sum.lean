import Mathlib
import Submission.Commons.FieldTheory.Polynomial.monic_index_ge_card_le
import Submission.Commons.FieldTheory.Polynomial.natCard_quotient_span_monic
import Submission.Commons.FieldTheory.Polynomial.natCard_quotient_nilradical_radical
import Submission.Commons.NumberTheory.NumberField.natCard_quotient_eq_pow_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.radical_map_eq_prod_primesOver
import Submission.Commons.NumberTheory.NumberField.natCard_quotient_prod_primesOver
import Submission.Commons.NumberTheory.NumberField.poly_reduced_card_le_radical_quotient

open scoped BigOperators NumberField
open Polynomial UniqueFactorizationMonoid

noncomputable section

namespace Commons.NumberTheory.NumberField

set_option autoImplicit false

variable {K : Type*} [Field K] [NumberField K]

/-- The residue-degree inequality. -/
theorem residue_rad_degree_le_inertia_sum {K : Type*} [Field K] [NumberField K]
    (θ : 𝓞 K) (p : ℕ) [Fact (Nat.Prime p)]
    (hdeg : 1 ≤ (minpoly ℤ θ).natDegree)
    (hgen : (minpoly ℤ θ).natDegree = Module.finrank ℚ K) :
    (UniqueFactorizationMonoid.radical ((minpoly ℤ θ).map (Int.castRingHom (ZMod p)))).natDegree ≤
      ∑ P ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K),
        P.inertiaDeg ℤ := by
  classical
  let Fp := ZMod p
  let fbar : Fp[X] := (minpoly ℤ θ).map (Int.castRingHom Fp)
  let r := UniqueFactorizationMonoid.radical fbar
  let pO : Ideal (𝓞 K) := (Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (𝓞 K))
  let S : Finset (Ideal (𝓞 K)) :=
    IsDedekindDomain.primesOverFinset (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K)
  have hp_lt : 1 < p := (Nat.Prime.one_lt (Fact.out : Nat.Prime p))
  have hfmonic : (minpoly ℤ θ).Monic := minpoly.monic (θ.isIntegral)
  have hfbar_monic : fbar.Monic := by
    simpa [fbar] using hfmonic.map (Int.castRingHom Fp)
  have hfbar_ne : fbar ≠ 0 := hfbar_monic.ne_zero
  have hr_monic : r.Monic := by
    simpa [r] using Commons.FieldTheory.Polynomial.radical_monic fbar hfbar_monic
  have hpow_le :
      p ^ r.natDegree ≤ Nat.card ((𝓞 K) ⧸ (pO.radical)) := by
    calc
      p ^ r.natDegree = Fintype.card Fp ^ r.natDegree := by
        rw [ZMod.card p]
      _ = Nat.card (Fp[X] ⧸ Ideal.span ({r} : Set (Fp[X]))) := by
        symm
        exact Commons.FieldTheory.Polynomial.natCard_quotient_span_monic (F := Fp) r hr_monic
      _ = Nat.card ((Fp[X] ⧸ Ideal.span ({fbar} : Set (Fp[X]))) ⧸
          nilradical (Fp[X] ⧸ Ideal.span ({fbar} : Set (Fp[X])))) := by
        symm
        exact Commons.FieldTheory.Polynomial.natCard_quotient_nilradical_radical (F := Fp) fbar hfbar_ne
      _ ≤ Nat.card ((𝓞 K) ⧸ (pO.radical)) := poly_reduced_card_le_radical_quotient θ p
  have hO_eq :
      Nat.card ((𝓞 K) ⧸ (pO.radical)) =
        p ^ (∑ P ∈ S, P.inertiaDeg ℤ) := by
    calc
      Nat.card ((𝓞 K) ⧸ (pO.radical)) =
          Nat.card ((𝓞 K) ⧸ (∏ P ∈ S, P)) := by
        dsimp [pO, S]
        change Nat.card ((𝓞 K) ⧸ (((Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (𝓞 K))).radical)) =
          Nat.card ((𝓞 K) ⧸ ∏ P ∈
            IsDedekindDomain.primesOverFinset (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K), P)
        rw [radical_map_eq_prod_primesOver (K := K) p]
      _ = ∏ P ∈ S, Nat.card ((𝓞 K) ⧸ P) := by
        exact natCard_quotient_prod_primesOver (K := K) p
      _ = ∏ P ∈ S, p ^ P.inertiaDeg ℤ := by
        apply Finset.prod_congr rfl
        intro P hP
        exact natCard_quotient_eq_pow_inertiaDeg (K := K) p P hP
      _ = p ^ (∑ P ∈ S, P.inertiaDeg ℤ) := by
        exact Finset.prod_pow_eq_pow_sum S (fun P : Ideal (𝓞 K) => P.inertiaDeg ℤ) p
  have hfin : r.natDegree ≤ ∑ P ∈ S, P.inertiaDeg ℤ := by
    exact (Nat.pow_le_pow_iff_right hp_lt).mp (by
      calc
        p ^ r.natDegree ≤ Nat.card ((𝓞 K) ⧸ (pO.radical)) := hpow_le
        _ = p ^ (∑ P ∈ S, P.inertiaDeg ℤ) := hO_eq)
  simpa [r, fbar, Fp, S] using hfin

end Commons.NumberTheory.NumberField
