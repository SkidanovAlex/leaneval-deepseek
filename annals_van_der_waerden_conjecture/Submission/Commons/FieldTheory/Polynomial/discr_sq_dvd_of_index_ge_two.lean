import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.Polynomial.Radical
import Submission.Commons.RingTheory.Polynomial.discr_map_of_natDegree
import Submission.Commons.FieldTheory.Polynomial.monic_index_ge_card_le
import Submission.Commons.RingTheory.Polynomial.sylvester_rank_le_of_common_divisor
import Submission.Commons.LinearAlgebra.Matrix.det_eq_zero_of_reduction_rank_le_sub_two

open Polynomial
open scoped BigOperators

set_option autoImplicit false

namespace Commons.FieldTheory.Polynomial

noncomputable section

-- ============================================================
-- Polynomial-side facts: radical / divRadical of a monic polynomial
-- ============================================================

/-- h = rad h * divRadical h -/
lemma h_eq_rad_mul_divRadical {F : Type*} [Field F] [DecidableEq F] (h : F[X]) :
    h = UniqueFactorizationMonoid.radical h * EuclideanDomain.divRadical h := by
  exact (EuclideanDomain.radical_mul_divRadical (a := h)).symm

/-- rad h is monic when h is monic -/
lemma radical_monic_of_monic {F : Type*} [Field F] [DecidableEq F] (h : F[X]) (hh : h.Monic) :
    (UniqueFactorizationMonoid.radical h).Monic :=
  Commons.FieldTheory.Polynomial.radical_monic h hh

/-- divRadical h is monic when h is monic -/
lemma divRadical_monic_of_monic {F : Type*} [Field F] [DecidableEq F] (h : F[X]) (hh : h.Monic) :
    (EuclideanDomain.divRadical h).Monic := by
  rw [Monic.def]
  have hlcmul : h.leadingCoeff =
      (UniqueFactorizationMonoid.radical h).leadingCoeff * (EuclideanDomain.divRadical h).leadingCoeff := by
    conv_lhs => rw [h_eq_rad_mul_divRadical h]
    exact Polynomial.leadingCoeff_mul (UniqueFactorizationMonoid.radical h) (EuclideanDomain.divRadical h)
  have hrc : (UniqueFactorizationMonoid.radical h).leadingCoeff * (EuclideanDomain.divRadical h).leadingCoeff = 1 := by
    rw [← hlcmul, hh.leadingCoeff]
  simpa [(radical_monic_of_monic h hh).leadingCoeff] using hrc

/-- natDegree h = natDegree(rad h) + natDegree(divRadical h) for monic h -/
lemma natDegree_h_eq_rad_add_divRadical {F : Type*} [Field F] [DecidableEq F] (h : F[X])
    (hh : h.Monic) :
    h.natDegree = (UniqueFactorizationMonoid.radical h).natDegree + (EuclideanDomain.divRadical h).natDegree := by
  have hrn : (UniqueFactorizationMonoid.radical h) ≠ 0 := UniqueFactorizationMonoid.radical_ne_zero
  have hdn : EuclideanDomain.divRadical h ≠ 0 := by
    intro hd
    apply hh.ne_zero
    rw [h_eq_rad_mul_divRadical h, hd, mul_zero]
  calc
    h.natDegree = (UniqueFactorizationMonoid.radical h * EuclideanDomain.divRadical h).natDegree := by
      conv_lhs => rw [h_eq_rad_mul_divRadical h]
    _ = (UniqueFactorizationMonoid.radical h).natDegree + (EuclideanDomain.divRadical h).natDegree :=
      Polynomial.natDegree_mul hrn hdn

/-- deg(divRadical h) = deg h - deg(rad h) -/
lemma natDegree_divRadical_eq_sub {F : Type*} [Field F] [DecidableEq F] (h : F[X])
    (hh : h.Monic) :
    (EuclideanDomain.divRadical h).natDegree = h.natDegree - (UniqueFactorizationMonoid.radical h).natDegree := by
  have hsum := natDegree_h_eq_rad_add_divRadical h hh
  omega

/-- A ring hom from `ℤ` to `ZMod p` composed with the cast `ℤ → ZMod (p^2)` is the direct cast. -/
lemma zmod_castHom_comp_intCast (p : ℕ) :
    (ZMod.castHom (show p ∣ p ^ 2 by exact ⟨p, by ring⟩) (ZMod p)).comp
      (Int.castRingHom (ZMod (p ^ 2))) = Int.castRingHom (ZMod p) := by
  apply RingHom.ext
  intro z
  exact eq_intCast
    (f := (ZMod.castHom (show p ∣ p ^ 2 by exact ⟨p, by ring⟩) (ZMod p)).comp
      (Int.castRingHom (ZMod (p ^ 2)))) z

-- ============================================================
-- Master lemma: index >= 2 forces p^2 | discr g.
-- ============================================================
theorem discr_sq_dvd_of_index_ge_two_aux (p : ℕ) [Fact (Nat.Prime p)] {n : ℕ} (hn : n < p)
    (g : ℤ[X]) (hg : g.Monic) (hdeg : g.natDegree = n)
    (hind : 2 ≤ (g.map (Int.castRingHom (ZMod p))).natDegree -
      (UniqueFactorizationMonoid.radical (g.map (Int.castRingHom (ZMod p)))).natDegree) :
    (p : ℤ) ^ 2 ∣ Polynomial.discr g := by
  classical
  haveI : Fact (1 < p ^ 2) := ⟨by
    have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    nlinarith⟩
  let Fp := ZMod p
  let φ : ℤ →+* Fp := Int.castRingHom Fp
  let h : Fp[X] := g.map φ
  have hh : h.Monic := by
    dsimp [h]
    exact hg.map φ
  have hhn : h.natDegree = n := by
    dsimp [h]
    rw [hg.natDegree_map φ, hdeg]
  have hradle : (UniqueFactorizationMonoid.radical h).natDegree ≤ h.natDegree :=
    Commons.FieldTheory.Polynomial.natDegree_radical_le h hh.ne_zero
  have hhind : 2 ≤ h.natDegree - (UniqueFactorizationMonoid.radical h).natDegree := by
    simpa [h] using hind
  have hn2 : 2 ≤ n := by
    have hsub : 2 ≤ n - (UniqueFactorizationMonoid.radical h).natDegree := by
      rwa [hhn] at hhind
    have hradle_n : (UniqueFactorizationMonoid.radical h).natDegree ≤ n := by
      rw [← hhn]
      exact hradle
    omega
  -- radical / divRadical of h
  let s : Fp[X] := EuclideanDomain.divRadical h
  let a : Fp[X] := UniqueFactorizationMonoid.radical h
  have hs2 : 2 ≤ s.natDegree := by
    dsimp [s]
    have hsub := natDegree_divRadical_eq_sub h hh
    rw [hsub]
    exact hhind
  have hs0 : s ≠ 0 := by
    intro hs0
    have : 2 ≤ (0 : Fp[X]).natDegree := by simpa [hs0] using hs2
    simp at this
  have hfs : h = s * a := by
    exact (h_eq_rad_mul_divRadical h).trans (mul_comm (UniqueFactorizationMonoid.radical h) (EuclideanDomain.divRadical h))
  have ha : a.natDegree + 2 ≤ n := by
    dsimp [a]
    have hsub : 2 ≤ n - (UniqueFactorizationMonoid.radical h).natDegree := by
      rwa [hhn] at hhind
    omega
  -- derivative of h is nonzero and its divRadical-quotient has the right degree
  have hder_le : h.derivative.natDegree ≤ n - 1 := by
    simpa [hhn] using (natDegree_derivative_le h)
  have hder_ne0 : h.derivative ≠ 0 := by
    intro hz
    have hcoeffn : h.coeff n = (1 : Fp) := by
      rw [← hhn]
      exact hh.coeff_natDegree
    have hc : (h.derivative).coeff (n - 1) = (n : Fp) := by
      rw [Polynomial.coeff_derivative]
      rw [show (n - 1) + 1 = n by omega]
      rw [hcoeffn]
      have hmult : ((↑(n - 1) : Fp) + 1) = (n : Fp) := by
        have hk : n - 1 + 1 = n := by omega
        rw [← hk]
        simp [Nat.cast_add]
      simp [hmult, one_mul, mul_one]
    rw [hz] at hc
    simp at hc
    have hnp : ¬ p ∣ n := by
      intro hpd
      by_cases hnz : n = 0
      · omega
      · have hp_le : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hnz) hpd
        omega
    have hnFp : (n : Fp) ≠ 0 := by
      intro hz0
      exact hnp ((ZMod.natCast_eq_zero_iff n p).mp hz0)
    exact hnFp hc.symm
  have hsdvd : s ∣ h.derivative := by
    dsimp [s]
    exact divRadical_dvd_derivative h
  let b : Fp[X] := Classical.choose hsdvd
  have hgs : h.derivative = s * b := by
    dsimp [b]
    exact Classical.choose_spec hsdvd
  have hb_ne0 : b ≠ 0 := by
    intro hb0
    apply hder_ne0
    rw [hgs, hb0, mul_zero]
  have hbnd : b.natDegree + 2 ≤ n - 1 := by
    have hs_le_der : s.natDegree ≤ h.derivative.natDegree :=
      Polynomial.natDegree_le_of_dvd hsdvd hder_ne0
    have hdeg_b : b.natDegree = h.derivative.natDegree - s.natDegree := by
      have hprod := Polynomial.natDegree_mul (p := s) (q := b) hs0 hb_ne0
      rw [hgs, hprod]
      omega
    omega
  -- rank bound for the Sylvester matrix over Fp (BB2)
  have hrank : Matrix.rank (Polynomial.sylvester h h.derivative n (n - 1)) ≤ n + (n - 1) - 2 := by
    exact Commons.RingTheory.Polynomial.sylvester_rank_le_of_common_divisor (K := Fp) h h.derivative s a b n (n - 1)
      (by rw [hhn])
      hder_le
      hfs hgs hs2 ha hbnd hh.ne_zero
  -- now work over ZMod (p^2)
  let Rp := ZMod (p ^ 2)
  let ψ : ℤ →+* Rp := Int.castRingHom Rp
  let g2 : Rp[X] := g.map ψ
  let ρ : Rp →+* Fp := ZMod.castHom (show p ∣ p ^ 2 by exact ⟨p, by ring⟩) Fp
  have hg2 : g2.Monic := by
    dsimp [g2]
    exact hg.map ψ
  have hg2n : g2.natDegree = n := by
    dsimp [g2]
    rw [hg.natDegree_map ψ, hdeg]
  -- discr commutes with reduction to ZMod (p^2)
  have hdisc_map : ((Polynomial.discr g : ℤ) : Rp) = Polynomial.discr g2 := by
    dsimp [g2]
    have hndg : (g.map ψ).natDegree = g.natDegree := hg.natDegree_map ψ
    have h := (Commons.RingTheory.Polynomial.discr_map_of_natDegree (R := ℤ) (S := Rp) ψ (p := g) hndg).symm
    simpa [Int.coe_castRingHom, ψ, Rp] using h.symm
  -- the discriminant is (up to sign) the resultant, which is the determinant of M
  let M : Matrix (Fin (n + (n - 1))) (Fin (n + (n - 1))) Rp :=
    Polynomial.sylvester g2 g2.derivative n (n - 1)
  have hdegpos : 0 < g2.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos]
    rw [hg2n]
    omega
  have hres := Polynomial.resultant_deriv (f := g2) hdegpos
  have hres_main : g2.resultant g2.derivative n (n - 1) =
      (-1 : Rp) ^ (n * (n - 1) / 2) * Polynomial.discr g2 := by
    have hrew := hres
    rw [hg2n] at hrew
    simpa [hg2.leadingCoeff] using hrew
  have hdet0 : M.det = 0 := by
    dsimp [M]
    refine Commons.LinearAlgebra.Matrix.det_eq_zero_of_reduction_rank_le_sub_two (p := p) (m := n + (n - 1)) (by omega)
      (A := Polynomial.sylvester g2 g2.derivative n (n - 1)) ?_
    have hred : (Polynomial.sylvester g2 g2.derivative n (n - 1)).map ρ =
        Polynomial.sylvester h h.derivative n (n - 1) := by
      rw [show (Polynomial.sylvester g2 g2.derivative n (n - 1)).map
            (ρ : Rp → Fp) =
          RingHom.mapMatrix ρ (Polynomial.sylvester g2 g2.derivative n (n - 1)) by
        ext i j
        rfl]
      rw [← Polynomial.sylvester_map_map (f := g2) (g := g2.derivative) (m := n) (n := n - 1) ρ]
      congr 1
      · dsimp [g2, h, ψ, φ]
        rw [Polynomial.map_map, zmod_castHom_comp_intCast p]
      · dsimp [g2, h, ψ, φ]
        rw [Polynomial.derivative_map, Polynomial.map_map, zmod_castHom_comp_intCast p]
        rw [← Polynomial.derivative_map]
    rw [hred]
    exact hrank
  have hsign : ∀ x : Rp, (-1 : Rp) ^ (n * (n - 1) / 2) * ((-1 : Rp) ^ (n * (n - 1) / 2) * x) = x := by
    intro x
    have hsq : (-1 : Rp) ^ (n * (n - 1) / 2) * (-1 : Rp) ^ (n * (n - 1) / 2) = 1 := by
      rw [← pow_add, ← two_mul]
      rw [pow_mul]
      norm_num
    rw [← mul_assoc, hsq, one_mul]
  have hmain : Polynomial.discr g2 = 0 := by
    calc
      Polynomial.discr g2 = (-1 : Rp) ^ (n * (n - 1) / 2) *
          ((-1 : Rp) ^ (n * (n - 1) / 2) * Polynomial.discr g2) := (hsign _).symm
      _ = (-1 : Rp) ^ (n * (n - 1) / 2) * (g2.resultant g2.derivative n (n - 1)) := by
        rw [hres_main]
      _ = (-1 : Rp) ^ (n * (n - 1) / 2) * M.det := by rfl
      _ = 0 := by rw [hdet0, mul_zero]
  have hd0 : ((Polynomial.discr g : ℤ) : Rp) = 0 := by
    rw [hdisc_map, hmain]
  have hdvd : ((p ^ 2 : ℕ) : ℤ) ∣ Polynomial.discr g := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (Polynomial.discr g) (p ^ 2)).mp hd0
  convert hdvd using 1
  norm_num

-- ============================================================
-- Final theorem
-- ============================================================
theorem discr_sq_dvd_of_index_ge_two (p : ℕ) [Fact (Nat.Prime p)] {n : ℕ} (hn : n < p)
    (f : ℤ[X]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hind : 2 ≤ (Polynomial.map (Int.castRingHom (ZMod p)) f).natDegree -
      (UniqueFactorizationMonoid.radical (Polynomial.map (Int.castRingHom (ZMod p)) f)).natDegree) :
    ∀ g : ℤ[X], g.Monic → g.natDegree = n →
      (∀ i < n, (g.coeff i : ZMod p) = (f.coeff i : ZMod p)) → (p : ℤ) ^ 2 ∣ Polynomial.discr g := by
  classical
  intro g hg hdeg' hcoeff
  refine discr_sq_dvd_of_index_ge_two_aux p hn g hg hdeg' ?_
  let φ : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  have hfφn : (f.map φ).natDegree = n := by
    rw [hf.natDegree_map φ, hdeg]
  have hfg : (f.map φ) = (g.map φ) := by
    apply Commons.FieldTheory.Polynomial.monic_ext (F := ZMod p)
    · exact hf.map φ
    · exact hg.map φ
    · rw [hf.natDegree_map φ, hdeg, hg.natDegree_map φ, hdeg']
    · intro i hi
      rw [Polynomial.coeff_map, Polynomial.coeff_map]
      exact (hcoeff i (by rwa [hfφn] at hi)).symm
  simpa [φ, hfg] using hind

end

end Commons.FieldTheory.Polynomial