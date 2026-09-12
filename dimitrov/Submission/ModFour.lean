import Mathlib.NumberTheory.NumberField.House
import Mathlib.Data.ZMod.Basic
import Submission.Powers
import Submission.PowersOdd
import Submission.RootCorr

/-!
# GOAL (Dimitrov's "mod 4" lemma, root-free)

For a monic `P : ℤ[X]`, with `P₂ := pow2 P` and `P₄ := pow2 (pow2 P)`
(from `Submission.Powers`), prove:

    pow4_sub_pow2_mod4 : ∀ n : ℕ, (4 : ℤ) ∣ (pow4 P).coeff n - (pow2 P).coeff n

i.e. `P₄ ≡ P₂ (mod 4)`.

## Proof structure

1. (mod 2) For every `P : ℤ[X]`: `pow2 P ≡ P (mod 2)` coefficient-wise.
   Over `ZMod 2`: `(-1) = 1`, `-X = X`, and `evenPart (Q*Q) = Q`
   (coefficient at `2n` of `Q*Q` is the single diagonal term `Q.coeff n`
   in characteristic 2; off-diagonal terms cancel in pairs), so
   `pow2 Q = Q` for every `Q : (ZMod 2)[X]`.  Map commutation
   (`pow2_map_zmod2`) transfers this back to ℤ as
   `two_dvd_pow2_sub_self`.
2. (mod 4) `pow2 P = P + 2Q` for some `Q` (`exists_eq_add_two_mul`).
   With `F := pow2 P` and `G := F*F(-X) - P*P(-X)`:
   `G = 2(R + R(-X)) + 4(Q*Q(-X))` where `R := P*(Q(-X))`, and at an even
   index `(R + R(-X)).coeff (2n) = 2 * R.coeff (2n)`, so every coefficient
   of `G` is divisible by 4.  Since
   `(pow2 F).coeff n = (-1)^d * (F*F(-X)).coeff (2n)` and
   `F.coeff n = (-1)^d * (P*P(-X)).coeff (2n)` (degrees agree because `P`
   is monic), `(pow2 F - F).coeff n` is divisible by 4.
-/

noncomputable section

open Polynomial
open scoped Polynomial

namespace Submission.ModFour

open Submission.Powers
open Submission.PowersOdd
open Submission.RootCorr

/-- Step 1 lemmas (mod 2). -/
lemma zmod2_neg_one_pow (k : ℕ) : (-1 : ZMod 2) ^ k = 1 := by
  have h1 : (-1 : ZMod 2) = 1 := by decide
  rw [h1, one_pow]

lemma zmod2_sq (x : ZMod 2) : x * x = x := by
  revert x; decide

lemma evenPart_map {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) (F : R[X]) :
    (evenPart F).map φ = evenPart (F.map φ) := by
  ext n
  rw [Polynomial.coeff_map, evenPart_coeff, evenPart_coeff, Polynomial.coeff_map]

lemma evenPart_mul_self_zmod2 (Q : (ZMod 2)[X]) : evenPart (Q * Q) = Q := by
  classical
  ext n
  rw [evenPart_coeff]
  rw [coeff_mul]
  change (∑ x ∈ Finset.antidiagonal (2 * n), Q.coeff x.1 * Q.coeff x.2) = Q.coeff n
  let S : Finset (ℕ × ℕ) := Finset.antidiagonal (2 * n)
  let f : ℕ × ℕ → ZMod 2 := fun x => Q.coeff x.1 * Q.coeff x.2
  have hmem : (n, n) ∈ S := by
    rw [Finset.mem_antidiagonal]
    omega
  have herased : (∑ x ∈ S.erase (n, n), f x) = 0 := by
    refine Finset.sum_involution (s := S.erase (n, n)) (f := f) (fun x _ => Prod.swap x) ?_ ?_ ?_ ?_
    · intro x hx
      rcases x with ⟨i, j⟩
      have h : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
      calc
        Q.coeff i * Q.coeff j + Q.coeff j * Q.coeff i = Q.coeff i * Q.coeff j + Q.coeff i * Q.coeff j := by
          rw [mul_comm (Q.coeff j) (Q.coeff i)]
        _ = 2 * (Q.coeff i * Q.coeff j) := by rw [two_mul]
        _ = 0 := by rw [h]; simp
    · intro x hx hf hfix
      have hxS0 : x ∈ S := (Finset.mem_erase.mp hx).2
      have hne0 : x ≠ (n, n) := (Finset.mem_erase.mp hx).1
      rcases x with ⟨i, j⟩
      have hij : i = j := by
        exact (congrArg Prod.fst hfix).symm
      have hsum : i + j = 2 * n := by
        simpa [S] using (Finset.mem_antidiagonal.mp hxS0)
      have hin : i = n := by omega
      have hxeq : (i, j) = (n, n) := by
        apply Prod.ext
        · exact hin
        · simpa [hij] using hin
      exact hne0 hxeq
    · intro x hx
      rcases x with ⟨i, j⟩
      have hxS : (i, j) ∈ S := (Finset.mem_erase.mp hx).2
      have hsum : i + j = 2 * n := by simpa [S] using (Finset.mem_antidiagonal.mp hxS)
      have hswap : (j, i) ∈ S := by
        rw [Finset.mem_antidiagonal]
        omega
      have hne : (j, i) ≠ (n, n) := by
        intro hji
        have hji' : (i, j) = (n, n) := by
          apply Prod.ext
          · exact congrArg Prod.snd hji
          · exact congrArg Prod.fst hji
        exact (Finset.mem_erase.mp hx).1 hji'
      exact Finset.mem_erase.mpr ⟨hne, hswap⟩
    · intro x hx
      simp
  calc
    (∑ x ∈ Finset.antidiagonal (2 * n), Q.coeff x.1 * Q.coeff x.2)
        = ∑ x ∈ S, f x := rfl
    _ = Q.coeff n := by
        rw [← Finset.sum_erase_add S f hmem, herased]
        simp [f, zmod2_sq]

lemma comp_neg_X_zmod2_self (Q : (ZMod 2)[X]) : Q.comp (-X) = Q := by
  ext n
  rw [Submission.PowersOdd.coeff_comp_neg_X]
  rw [zmod2_neg_one_pow]
  simp

lemma pow2_zmod2_evenPart (Q : (ZMod 2)[X]) : pow2 Q = evenPart (Q * Q.comp (-X)) := by
  unfold pow2
  rw [zmod2_neg_one_pow]
  simp

lemma pow2_zmod2_eq_self (Q : (ZMod 2)[X]) : pow2 Q = Q := by
  rw [pow2_zmod2_evenPart, comp_neg_X_zmod2_self Q]
  exact evenPart_mul_self_zmod2 Q

lemma pow2_map_zmod2 (P : ℤ[X]) :
    (pow2 P).map (Int.castRingHom (ZMod 2)) = pow2 (P.map (Int.castRingHom (ZMod 2))) := by
  classical
  let φ : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
  have hφpow : φ ((-1 : ℤ) ^ P.natDegree) = 1 := by
    calc
      φ ((-1 : ℤ) ^ P.natDegree) = (φ (-1 : ℤ)) ^ P.natDegree := by rw [map_pow]
      _ = (-1 : ZMod 2) ^ P.natDegree := by simp
      _ = 1 := zmod2_neg_one_pow P.natDegree
  have hsmul :
      φ ((-1 : ℤ) ^ P.natDegree) • (P * P.comp (-X)).map φ
        = (P.map φ) * (P.map φ).comp (-X) := by
    rw [hφpow]
    rw [one_smul]
    rw [Polynomial.map_mul]
    rw [Polynomial.map_comp]
    rw [Polynomial.map_neg]
    rw [Polynomial.map_X]
  calc
    (pow2 P).map φ = evenPart (map φ ((-1 : ℤ) ^ P.natDegree • (P * P.comp (-X)))) := by
        unfold pow2
        rw [evenPart_map]
    _ = evenPart (φ ((-1 : ℤ) ^ P.natDegree) • (P * P.comp (-X)).map φ) := by
        rw [Polynomial.map_smul]
    _ = evenPart ((P.map φ) * (P.map φ).comp (-X)) := by rw [hsmul]
    _ = pow2 (P.map φ) := by
        rw [pow2_zmod2_evenPart]

/-- Step 1: `pow2 P ≡ P (mod 2)` coefficient-wise. -/
lemma two_dvd_pow2_sub_self (P : ℤ[X]) (n : ℕ) : (2 : ℤ) ∣ (pow2 P).coeff n - P.coeff n := by
  classical
  let φ : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
  have hm : (pow2 P).map φ = P.map φ := by
    rw [pow2_map_zmod2]
    exact pow2_zmod2_eq_self (P.map (Int.castRingHom (ZMod 2)))
  have hc := congrArg (fun G : (ZMod 2)[X] => G.coeff n) hm
  have hc' : (((pow2 P).coeff n : ℤ) : ZMod 2) = ((P.coeff n : ℤ) : ZMod 2) := by
    simpa [φ] using hc
  have hzero : (((pow2 P).coeff n - P.coeff n : ℤ) : ZMod 2) = 0 := by
    rw [Int.cast_sub]
    exact sub_eq_zero.mpr hc'
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd ((pow2 P).coeff n - P.coeff n) 2).mp hzero

/-- If `A - B` has all coefficients even then `A = B + 2·Q` for some `Q`. -/
lemma exists_eq_add_two_mul {A B : ℤ[X]}
    (h : ∀ n : ℕ, (2 : ℤ) ∣ A.coeff n - B.coeff n) : ∃ Q : ℤ[X], A = B + (2 : ℤ[X]) * Q := by
  classical
  let k : ℕ → ℤ := fun n => Classical.choose (h n)
  let Q : ℤ[X] := (A - B).support.sum fun n => monomial n (k n)
  have hk : ∀ n, (A - B).coeff n = (2 : ℤ) * k n := by
    intro n
    dsimp [k]
    -- choose_spec (h n) : A.coeff n - B.coeff n = (2 : ℤ) * choose (h n)   (since Dvd: b = a*c)
    simpa [sub_eq_add_neg] using (Classical.choose_spec (h n))
  have hcQ : ∀ m, Q.coeff m = if m ∈ (A - B).support then k m else 0 := by
    intro m
    dsimp [Q]
    simp [Polynomial.coeff_monomial, Finset.sum_ite_eq']
  refine ⟨Q, ?_⟩
  apply Polynomial.ext
  intro m
  have hcq : ((2 : ℤ[X]) * Q).coeff m = 2 * Q.coeff m := by simp
  rw [coeff_add, hcq]
  by_cases hm : m ∈ (A - B).support
  · rw [hcQ m, if_pos hm]
    -- goal: A.coeff m = B.coeff m + 2 * k m
    have hmm : (A - B).coeff m = 2 * k m := hk m
    rw [← hmm] -- rewrite 2 * k m → (A-B).coeff m
    simp [coeff_sub]
  · rw [hcQ m, if_neg hm]
    have hz : (A - B).coeff m = 0 := by
      simpa [Polynomial.mem_support_iff] using hm
    -- goal A.coeff m = B.coeff m + 0
    rw [coeff_sub] at hz
    omega

/-- coefficient formula for `pow2`. -/
lemma pow2_coeff {R : Type*} [CommRing R] (G : R[X]) (n : ℕ) :
    (pow2 G).coeff n = (-1 : R) ^ G.natDegree * (G * G.comp (-X)).coeff (2 * n) := by
  unfold pow2
  rw [evenPart_coeff]
  simp [coeff_smul]

/-- Step 2: `pow2 (pow2 P) ≡ pow2 P (mod 4)` for monic `P`. -/
lemma four_dvd_pow2_pow2_sub (P : ℤ[X]) (hP : P.Monic) (n : ℕ) :
    (4 : ℤ) ∣ (pow2 (pow2 P)).coeff n - (pow2 P).coeff n := by
  classical
  let F : ℤ[X] := pow2 P
  have hdegF : F.natDegree = P.natDegree := by
    simpa [F] using pow2_natDegree P hP
  obtain ⟨Q, hFQ⟩ := exists_eq_add_two_mul (A := pow2 P) (B := P) (two_dvd_pow2_sub_self P)
  have hFQ' : F = P + (2 : ℤ[X]) * Q := by simpa [F] using hFQ
  have hFc : F.comp (-X) = P.comp (-X) + (2 : ℤ[X]) * Q.comp (-X) := by
    rw [hFQ']
    rw [add_comp]
    rw [mul_comp]
    simp
  let G : ℤ[X] := F * F.comp (-X) - P * P.comp (-X)
  let R : ℤ[X] := P * (Q.comp (-X))
  let S : ℤ[X] := Q * (Q.comp (-X))
  have hRc : (P * (Q.comp (-X))).comp (-X) = Q * P.comp (-X) := by
    calc
      (P * Q.comp (-X)).comp (-X) = P.comp (-X) * (Q.comp (-X)).comp (-X) := by rw [mul_comp]
      _ = P.comp (-X) * Q := by rw [comp_neg_X_comp_neg_X]
      _ = Q * P.comp (-X) := by rw [mul_comm]
  have hGid : G = (2 : ℤ[X]) * (R + R.comp (-X)) + (4 : ℤ[X]) * S := by
    dsimp [G]
    calc
      F * F.comp (-X) - P * P.comp (-X)
          = (P + (2 : ℤ[X]) * Q) * (P.comp (-X) + (2 : ℤ[X]) * Q.comp (-X)) - P * P.comp (-X) := by
              rw [hFc, hFQ']
      _ = (2 : ℤ[X]) * (P * (Q.comp (-X)) + (P * (Q.comp (-X))).comp (-X)) + (4 : ℤ[X]) * (Q * (Q.comp (-X))) := by
              rw [hRc]
              ring
  have h4G : (4 : ℤ) ∣ G.coeff (2 * n) := by
    rw [hGid]
    rw [coeff_add]
    have hRR : (R + R.comp (-X)).coeff (2 * n) = 2 * R.coeff (2 * n) := by
      rw [coeff_add, Submission.PowersOdd.coeff_comp_neg_X]
      have hpow : (-1 : ℤ) ^ (2 * n) = 1 := by simp [pow_mul]
      rw [hpow]
      ring
    have hcRR : ((2 : ℤ[X]) * (R + R.comp (-X))).coeff (2 * n) = 4 * R.coeff (2 * n) := by
      calc
        ((2 : ℤ[X]) * (R + R.comp (-X))).coeff (2 * n) = 2 * (R + R.comp (-X)).coeff (2 * n) := by simp
        _ = 2 * (2 * R.coeff (2 * n)) := by rw [hRR]
        _ = 4 * R.coeff (2 * n) := by ring
    have hcS : ((4 : ℤ[X]) * S).coeff (2 * n) = 4 * S.coeff (2 * n) := by simp
    rw [hcRR, hcS]
    exact ⟨R.coeff (2 * n) + S.coeff (2 * n), by ring⟩
  have hc1 : (pow2 F).coeff n = (-1 : ℤ) ^ P.natDegree * (F * F.comp (-X)).coeff (2 * n) := by
    calc
      (pow2 F).coeff n = (-1 : ℤ) ^ F.natDegree * (F * F.comp (-X)).coeff (2 * n) := pow2_coeff F n
      _ = (-1 : ℤ) ^ P.natDegree * (F * F.comp (-X)).coeff (2 * n) := by rw [hdegF]
  have hc2 : F.coeff n = (-1 : ℤ) ^ P.natDegree * (P * P.comp (-X)).coeff (2 * n) := by
    calc
      F.coeff n = (pow2 P).coeff n := by simp [F]
      _ = (-1 : ℤ) ^ P.natDegree * (P * P.comp (-X)).coeff (2 * n) := pow2_coeff P n
  have hmain : (pow2 F).coeff n - F.coeff n = (-1 : ℤ) ^ P.natDegree * G.coeff (2 * n) := by
    rw [hc1, hc2]
    simp [G]
    ring
  have h4main : (4 : ℤ) ∣ (pow2 F).coeff n - F.coeff n := by
    rw [hmain]
    rcases h4G with ⟨k, hk⟩
    refine ⟨(-1 : ℤ) ^ P.natDegree * k, ?_⟩
    rw [hk]
    ring
  simpa [F] using h4main


/-- The fourth-power polynomial `P₄ = (P₂)₂` is congruent to `P₂` modulo 4
coefficient-wise, for monic integer polynomials. -/
theorem pow4_sub_pow2_mod4 (P : ℤ[X]) (hP : P.Monic) (n : ℕ) :
    (4 : ℤ) ∣ (pow4 P).coeff n - (pow2 P).coeff n := by
  change (4 : ℤ) ∣ (pow2 (pow2 P)).coeff n - (pow2 P).coeff n
  exact four_dvd_pow2_pow2_sub P hP n

end Submission.ModFour

end
