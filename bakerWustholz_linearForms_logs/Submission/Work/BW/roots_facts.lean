import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial

/-- Elementary facts about the multiset of complex roots of a monic irreducible integer
polynomial of degree `> 1`: no root is `0`, the product of the roots is `(-1)^n P(0)`, and for
every `k ≥ 1` the product `∏_z (z^k - 1)` is a rational integer (it equals the resultant of `P`
and `X^k - 1`). -/
theorem roots_facts (P : Polynomial ℤ) (hP : P.Monic) (hirr : Irreducible P)
    (hdeg : 1 < P.natDegree) :
    (∀ z ∈ (P.map (Int.castRingHom ℂ)).roots, z ≠ 0)
    ∧ ((P.map (Int.castRingHom ℂ)).roots).prod
        = ((-1 : ℂ) ^ P.natDegree) * (P.coeff 0 : ℂ)
    ∧ (∀ k : ℕ, 1 ≤ k → ∃ m : ℤ,
        ((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ k - 1)).prod = (m : ℂ))
    ∧ P.coeff 0 ≠ 0 := by
  classical
  have hmonic : (P.map (Int.castRingHom ℂ)).Monic := hP.map _
  have hsplits : (P.map (Int.castRingHom ℂ)).Splits := IsAlgClosed.splits _
  have hn : (P.map (Int.castRingHom ℂ)).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _) P
  -- The constant coefficient does not vanish: otherwise `X ∣ P` and, `P` being irreducible,
  -- `P` would be associate to `X`, hence of degree `1`.
  have hc0 : P.coeff 0 ≠ 0 := by
    intro h0
    have hXnu : ¬ IsUnit (Polynomial.X : Polynomial ℤ) := by
      intro hu
      have hd : (Polynomial.X : Polynomial ℤ) ∣ (1 : Polynomial ℤ) := hu.dvd
      have hle := Polynomial.natDegree_le_of_dvd hd (one_ne_zero)
      rw [Polynomial.natDegree_X, Polynomial.natDegree_one] at hle
      omega
    obtain ⟨Q, hQ⟩ := Polynomial.X_dvd_iff.mpr h0
    rcases hirr.isUnit_or_isUnit hQ with hXu | hQu
    · exact hXnu hXu
    · have hQd : Q.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hQu
      have hPd : P.natDegree = 1 := by
        rw [hQ, Polynomial.natDegree_mul Polynomial.X_ne_zero hQu.ne_zero,
          Polynomial.natDegree_X, hQd]
      omega
  -- No root of the image of `P` in `ℂ[X]` is zero, again by the non-vanishing of the constant
  -- coefficient.
  have hroot : ∀ z ∈ (P.map (Int.castRingHom ℂ)).roots, z ≠ 0 := by
    intro z hz hz0
    subst hz0
    have hzr : (P.map (Int.castRingHom ℂ)).IsRoot 0 :=
      (Polynomial.mem_roots hmonic.ne_zero).mp hz
    have hc : (P.map (Int.castRingHom ℂ)).coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact Polynomial.IsRoot.def.mp hzr
    rw [Polynomial.coeff_map] at hc
    exact hc0 (Int.cast_eq_zero.mp hc)
  -- Vieta: for a monic split polynomial, `coeff 0 = (-1)^n * ∏ roots`.
  have hprod : ((P.map (Int.castRingHom ℂ)).roots).prod
      = ((-1 : ℂ) ^ P.natDegree) * (P.coeff 0 : ℂ) := by
    have h2 := hsplits.coeff_zero_eq_prod_roots_of_monic hmonic
    rw [Polynomial.coeff_map, hn] at h2
    simp only [Int.coe_castRingHom] at h2
    have hsign : (-1 : ℂ) ^ P.natDegree * (-1 : ℂ) ^ P.natDegree = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨P.natDegree, by ring⟩
    rw [h2, ← mul_assoc, hsign, one_mul]
  -- The product `∏_z (z^k - 1)` is the resultant `Res(P, X^k - 1)`, an integer.
  have hint : ∀ k : ℕ, 1 ≤ k → ∃ m : ℤ,
      ((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ k - 1)).prod = (m : ℂ) := by
    intro k _
    let R : Polynomial ℤ := Polynomial.X ^ k - 1
    have hRmap : R.map (Int.castRingHom ℂ) = (Polynomial.X : Polynomial ℂ) ^ k - 1 := by
      simp [R]
    refine ⟨P.resultant R (P.map (Int.castRingHom ℂ)).natDegree
      ((R.map (Int.castRingHom ℂ)).natDegree), ?_⟩
    have hres : (P.map (Int.castRingHom ℂ)).resultant (R.map (Int.castRingHom ℂ))
        = ((P.resultant R (P.map (Int.castRingHom ℂ)).natDegree
            ((R.map (Int.castRingHom ℂ)).natDegree) : ℤ) : ℂ) := by
      simpa using Polynomial.resultant_map_map P R (P.map (Int.castRingHom ℂ)).natDegree
        ((R.map (Int.castRingHom ℂ)).natDegree) (Int.castRingHom ℂ)
    rw [← hres, Polynomial.resultant_eq_prod_eval (P.map (Int.castRingHom ℂ))
      (R.map (Int.castRingHom ℂ)) _ le_rfl hsplits, hmonic.leadingCoeff, one_pow, one_mul]
    have heval : ∀ z : ℂ, (R.map (Int.castRingHom ℂ)).eval z = z ^ k - 1 := by
      intro z
      rw [hRmap]
      simp
    have hmap : ((P.map (Int.castRingHom ℂ)).roots).map (fun z => z ^ k - 1)
        = ((P.map (Int.castRingHom ℂ)).roots).map
            (fun x => Polynomial.eval x (R.map (Int.castRingHom ℂ))) :=
      Multiset.map_congr rfl (fun z _ => (heval z).symm)
    rw [hmap]
  exact ⟨hroot, hprod, hint, hc0⟩

end Work.BW
