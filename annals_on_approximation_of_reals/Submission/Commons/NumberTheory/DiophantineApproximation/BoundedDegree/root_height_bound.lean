import Mathlib.RingTheory.Polynomial.GaussLemma
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.minpoly_leading_coeff_eq_one
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_supNorm_one_le
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_natDegree_map_eq
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_factor_supNorm_le
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.finset_sup_nat_cast_le

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

open Polynomial
open scoped BigOperators

noncomputable section

/-! # root_height_bound

If `S ∈ ℤ[X]` is a non-zero polynomial of degree `≤ N` and `α ∈ ℂ` is a root of `S`,
then `α` is algebraic of degree `≤ N` and its naive height (the maximum of the integer
coefficients of `D · minpoly ℚ α`, where `D` is the lcm of the denominators of the
coefficients of the minimal polynomial) is `≤ C(N) · ‖S‖`, where `‖S‖` is the sup-norm
of the coefficients of `S`.

Structure of the proof:
 1. `α` is a root of the non-zero polynomial `Sℚ = S.map(algebraMap ℤ ℚ)`, hence
    algebraic; the minimal polynomial `p = minpoly ℚ α` divides `Sℚ`.
 2. Let `D` be the lcm of the denominators of the coefficients of `p`.  The polynomial
    `P := Σ i ∈ p.support, monomial i ((D * p.coeff i).num)` is a *primitive* integer
    polynomial (clear denominators; `p` is monic so the content is `1`), with
    `P.map(algebraMap ℤ ℚ) = D • p`, hence `P_ℚ | Sℚ`.
 3. By Gauss's lemma (Mathlib: `IsPrimitive.mul_map_mem_lifts_iff`), `P ∣ S` in `ℤ[X]`.
 4. Gelfond's factor lemma (`int_poly_factor_supNorm_le`) gives
    `‖P.map ℝ‖ ≤ 2^N · √(N+1) · ‖S.map ℝ‖`.
 5. The naive height of `α` is at most the sup over `p.support` of the coefficients of
    `P.map ℝ`, which is `≤ ‖P.map ℝ‖`.
-/

/-! ## 1. Roots of integer polynomials are algebraic of bounded degree -/

private lemma int_poly_aeval_zero_of_root_complex (S : Polynomial ℤ) (α : ℂ)
    (hroot : Polynomial.IsRoot (S.map (Int.castRingHom ℂ)) α) :
    aeval α (S.map (algebraMap ℤ ℚ)) = 0 := by
  rw [aeval_def, ← Polynomial.eval_map]
  rw [Polynomial.map_map]
  rw [show (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℂ from by
    ext n
    rfl]
  exact (Polynomial.IsRoot.def).mp hroot

private lemma isAlgebraic_of_root_int (S : Polynomial ℤ) (hS : S ≠ 0) (α : ℂ)
    (hroot : Polynomial.IsRoot (S.map (Int.castRingHom ℂ)) α) : IsAlgebraic ℚ α := by
  refine ⟨S.map (algebraMap ℤ ℚ), ?_, ?_⟩
  · exact (Polynomial.map_eq_zero_iff (f := algebraMap ℤ ℚ) Int.cast_injective).not.mpr hS
  · exact int_poly_aeval_zero_of_root_complex S α hroot

private lemma minpoly_dvd_int_poly (S : Polynomial ℤ) (α : ℂ)
    (hroot : Polynomial.IsRoot (S.map (Int.castRingHom ℂ)) α) :
    minpoly ℚ α ∣ S.map (algebraMap ℤ ℚ) := by
  exact minpoly.dvd ℚ α (int_poly_aeval_zero_of_root_complex S α hroot)

/-! ## 2. Clearing the denominators of a rational polynomial -/

/-- The lcm of the denominators of the (non-zero) coefficients of `p : ℚ[X]`. -/
private def lcmDen (p : Polynomial ℚ) : ℕ :=
  Multiset.lcm (Multiset.map (fun i : ℕ => (p.coeff i).den) p.support.val)

/-- `p` with denominators cleared: the integer polynomial whose `i`-th coefficient is the
numerator of `D * p.coeff i`. -/
private def clearPoly (p : Polynomial ℚ) (D : ℕ) : Polynomial ℤ :=
  p.support.sum fun i => Polynomial.monomial i ((D * p.coeff i).num)

private lemma coeff_finset_sum_int (s : Finset ℕ) (f : ℕ → Polynomial ℤ) (n : ℕ) :
    (s.sum f).coeff n = s.sum (fun i => (f i).coeff n) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s has ih
    rw [Finset.sum_insert has, Finset.sum_insert has]
    rw [Polynomial.coeff_add, ih]

private lemma den_dvd_lcmDen (p : Polynomial ℚ) {i : ℕ} (hi : i ∈ p.support) :
    (p.coeff i).den ∣ lcmDen p := by
  dsimp [lcmDen]
  exact Multiset.dvd_lcm (Multiset.mem_map.mpr ⟨i, hi, rfl⟩)

private lemma lcmDen_ne_zero (p : Polynomial ℚ) (_hp : p ≠ 0) : lcmDen p ≠ 0 := by
  dsimp [lcmDen]
  exact (Multiset.lcm_ne_zero_iff _).2 (by
    intro hz
    rw [Multiset.mem_map] at hz
    rcases hz with ⟨j, hj, hj0⟩
    have hpos : 0 < (p.coeff j).den := Rat.den_pos (p.coeff j)
    omega)

private lemma rat_mul_natCast_den_eq_one (q : ℚ) (D : ℕ) (hdiv : q.den ∣ D) :
    ((D : ℚ) * q).den = 1 := by
  by_cases hq : q = 0
  · simp [hq]
  let m : ℕ := D / q.den
  have hD : D = q.den * m := by
    dsimp [m]
    rw [Nat.mul_comm, Nat.div_mul_cancel hdiv]
  have hcoef : (D : ℚ) * q = ((m * q.num : ℤ) : ℚ) := by
    calc
      (D : ℚ) * q = ((q.den * m : ℕ) : ℚ) * q := by rw [hD]
      _ = ((q.den : ℚ) * (m : ℚ)) * q := by norm_num
      _ = (m : ℚ) * ((q.den : ℚ) * q) := by ring
      _ = (m : ℚ) * (q.num : ℚ) := by
        congr 1
        calc
          (q.den : ℚ) * q = (q.den : ℚ) * (↑q.num / ↑q.den) := by rw [Rat.num_div_den]
          _ = q.num := mul_div_cancel₀ (a := (q.num : ℚ)) (b := (q.den : ℚ))
            (by exact_mod_cast (Rat.den_nz q))
      _ = ((m * q.num : ℤ) : ℚ) := by norm_num
  rw [hcoef]
  rw [Rat.den_eq_one_iff]
  simp only [Rat.num_intCast]

private lemma clearPoly_coeff (p : Polynomial ℚ) (D : ℕ) :
    ∀ n : ℕ, (clearPoly p D).coeff n = (D * p.coeff n).num := by
  intro n
  dsimp [clearPoly]
  rw [coeff_finset_sum_int]
  -- each monomial contributes only at its own index
  have hterm : ∀ i : ℕ, (Polynomial.monomial i ((D * p.coeff i).num)).coeff n =
      if i = n then (D * p.coeff i).num else 0 := by
    intro i
    rw [Polynomial.coeff_monomial]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq']
  by_cases hn : n ∈ p.support
  · simp [hn]
  · simp [hn]
    have hp0 : p.coeff n = 0 := (Polynomial.notMem_support_iff.mp hn)
    simp [hp0]

private lemma clearPoly_coeff_rat (p : Polynomial ℚ) (D : ℕ) (hD : lcmDen p ∣ D)
    {i : ℕ} (hi : i ∈ p.support) :
    ((clearPoly p D).coeff i : ℚ) = (D : ℚ) * p.coeff i := by
  rw [clearPoly_coeff]
  have hdiv : (p.coeff i).den ∣ D := dvd_trans (den_dvd_lcmDen p hi) hD
  have hden : ((D : ℚ) * p.coeff i).den = 1 := rat_mul_natCast_den_eq_one (p.coeff i) D hdiv
  exact Rat.coe_int_num_of_den_eq_one hden

private lemma clearPoly_support (p : Polynomial ℚ) (D : ℕ) (hD : lcmDen p ∣ D)
    (hDpos : 0 < D) : (clearPoly p D).support = p.support := by
  ext n
  constructor
  · intro hnz
    rw [Polynomial.mem_support_iff] at hnz
    rw [clearPoly_coeff] at hnz
    by_contra hnot
    have hp0 : p.coeff n = 0 := (Polynomial.notMem_support_iff.mp hnot)
    exact hnz (by simp [hp0])
  · intro hmem
    rw [Polynomial.mem_support_iff]
    rw [clearPoly_coeff]
    have hdiv : (p.coeff n).den ∣ D := dvd_trans (den_dvd_lcmDen p hmem) hD
    have hprod_ne : (D : ℚ) * p.coeff n ≠ 0 := by
      exact mul_ne_zero (by positivity) (Polynomial.mem_support_iff.mp hmem)
    exact Rat.num_ne_zero.mpr hprod_ne

private lemma clearPoly_ne_zero (p : Polynomial ℚ) (D : ℕ) (hp : p ≠ 0)
    (_hD : lcmDen p ∣ D) (hDpos : 0 < D) : clearPoly p D ≠ 0 := by
  intro hP0
  apply hp
  ext n
  by_cases hn : n ∈ p.support
  · exfalso
    have hcoeffP : (clearPoly p D).coeff n = 0 := by simp [hP0]
    rw [clearPoly_coeff] at hcoeffP
    have hprod_ne : (D : ℚ) * p.coeff n ≠ 0 := by
      exact mul_ne_zero (by positivity) (Polynomial.mem_support_iff.mp hn)
    exact ((Rat.num_ne_zero.mpr hprod_ne) hcoeffP)
  · exact (Polynomial.notMem_support_iff.mp hn)

private lemma clearPoly_monic_natDegree_coeff (p : Polynomial ℚ) (D : ℕ) (hp : p.Monic) :
    (clearPoly p D).coeff p.natDegree = D := by
  rw [clearPoly_coeff]
  have h1 : p.coeff p.natDegree = 1 := by
    rw [Polynomial.coeff_natDegree]
    exact (Polynomial.Monic.leadingCoeff hp)
  rw [h1]
  simp
private lemma natAbs_clear (q : ℚ) (D : ℕ) (hdiv : q.den ∣ D) :
    ((D * q).num).natAbs * q.den = D * q.num.natAbs := by
  by_cases hq : q = 0
  · simp [hq]
  let m : ℕ := D / q.den
  have hD : D = q.den * m := by
    dsimp [m]
    rw [Nat.mul_comm, Nat.div_mul_cancel hdiv]
  have hcoef : (D : ℚ) * q = ((m * q.num : ℤ) : ℚ) := by
    calc
      (D : ℚ) * q = ((q.den * m : ℕ) : ℚ) * q := by rw [hD]
      _ = ((q.den : ℚ) * (m : ℚ)) * q := by norm_num
      _ = (m : ℚ) * ((q.den : ℚ) * q) := by ring
      _ = (m : ℚ) * (q.num : ℚ) := by
        congr 1
        calc
          (q.den : ℚ) * q = (q.den : ℚ) * (↑q.num / ↑q.den) := by rw [Rat.num_div_den]
          _ = q.num := mul_div_cancel₀ (a := (q.num : ℚ)) (b := (q.den : ℚ))
            (by exact_mod_cast (Rat.den_nz q))
      _ = ((m * q.num : ℤ) : ℚ) := by norm_num
  have hnum : (D * q).num = (m * q.num : ℤ) := by
    calc
      (D * q).num = ((m * q.num : ℤ) : ℚ).num := by rw [← hcoef]
      _ = m * q.num := Rat.num_intCast _
  calc
    ((D * q).num).natAbs * q.den = (m * q.num : ℤ).natAbs * q.den := by rw [hnum]
    _ = m * q.num.natAbs * q.den := by
      simp [Int.natAbs_mul]
    _ = D * q.num.natAbs := by
      rw [hD]
      ring

private lemma natAbs_dvd_of_dvd {r z : ℤ} (h : r ∣ z) : r.natAbs ∣ z.natAbs := by
  rcases h with ⟨c, hc⟩
  use c.natAbs
  rw [hc, Int.natAbs_mul]


private lemma coeff_C_dvd (P Q : Polynomial ℤ) (r : ℤ) (hQ : P = C r * Q) :
    ∀ i : ℕ, r ∣ P.coeff i := by
  intro i
  refine ⟨Q.coeff i, ?_⟩
  calc
    P.coeff i = (C r * Q).coeff i := by rw [hQ]
    _ = r * Q.coeff i := by rw [Polynomial.coeff_C_mul]

private lemma clearPoly_isPrimitive (p : Polynomial ℚ) (hp : p.Monic) :
    (clearPoly p (lcmDen p)).IsPrimitive := by
  intro r hCr
  by_cases hr : r = 0
  · exfalso
    rcases hCr with ⟨Q, hQ⟩
    have hP0 : clearPoly p (lcmDen p) = 0 := by simpa [hr] using hQ
    have hp_ne : p ≠ 0 := Polynomial.Monic.ne_zero hp
    exact clearPoly_ne_zero p (lcmDen p) hp_ne (by rfl) (Nat.pos_of_ne_zero (lcmDen_ne_zero p hp_ne)) hP0
  let D : ℕ := lcmDen p
  let n : ℕ := r.natAbs
  have hn_pos : 0 < n := Int.natAbs_pos.mpr hr
  have hdiv_coeff : ∀ i : ℕ, r ∣ (clearPoly p D).coeff i := by
    rcases hCr with ⟨Q, hQ⟩
    intro i
    exact coeff_C_dvd (clearPoly p D) Q r (by simpa [D] using hQ) i
  have hnd : ∀ i : ℕ, n ∣ ((clearPoly p D).coeff i).natAbs := by
    intro i
    dsimp [n]
    exact natAbs_dvd_of_dvd (hdiv_coeff i)
  have hp_ne : p ≠ 0 := Polynomial.Monic.ne_zero hp
  -- leading coefficient of P is D, so n | D
  have hlead_in : p.natDegree ∈ p.support := by
    rw [Polynomial.mem_support_iff]
    rw [Polynomial.coeff_natDegree]
    exact (Polynomial.Monic.leadingCoeff hp ▸ one_ne_zero)
  have hnD : n ∣ D := by
    have hlead := hnd p.natDegree
    have hcoeff_lead : (clearPoly p D).coeff p.natDegree = (D : ℤ) :=
      clearPoly_monic_natDegree_coeff p D hp
    rw [hcoeff_lead] at hlead
    simpa using hlead
  let D' : ℕ := D / n
  have hDdef : D = n * D' := by
    dsimp [D']
    rw [Nat.mul_comm, Nat.div_mul_cancel hnD]
  -- for every support index, the denominator divides D'
  have hden_dvd_D' : ∀ i : ℕ, i ∈ p.support → (p.coeff i).den ∣ D' := by
    intro i hi
    let d : ℕ := (p.coeff i).den
    let m : ℕ := (p.coeff i).num.natAbs
    have hdvdD : d ∣ D := by
      dsimp [d, D]
      exact den_dvd_lcmDen p hi
    have hcoeff : (clearPoly p D).coeff i = (D * p.coeff i).num := clearPoly_coeff p D i
    have heq : (((clearPoly p D).coeff i).natAbs) * d = D * m := by
      dsimp [d, m]
      rw [hcoeff]
      exact natAbs_clear (p.coeff i) D hdvdD
    -- from n | natAbs(P.coeff i) and n | D, and natAbs * d = D * m: get d | D'
    rcases (hnd i) with ⟨t, ht⟩
    have hmul : n * (t * d) = n * (D' * m) := by
      calc
        n * (t * d) = (((clearPoly p D).coeff i).natAbs) * d := by rw [ht, Nat.mul_assoc]
        _ = D * m := heq
        _ = (n * D') * m := by rw [hDdef]
        _ = n * (D' * m) := by ring
    have hcancel : t * d = D' * m := Nat.mul_left_cancel hn_pos hmul
    refine Nat.Coprime.dvd_of_dvd_mul_right (k := d) (n := m) (m := D') ?_ ?_
    · exact (p.coeff i).reduced.symm
    · exact ⟨t, by rw [← hcancel, mul_comm]⟩
  -- lcm over the support divides D'
  have hD_dvd : D ∣ D' := by
    dsimp [D, lcmDen]
    rw [Multiset.lcm_dvd]
    intro b hb
    rcases (Multiset.mem_map.mp hb) with ⟨j, hj, rfl⟩
    exact hden_dvd_D' j hj
  -- therefore n = 1
  have hD_ne : D ≠ 0 := by
    dsimp [D]
    exact lcmDen_ne_zero p hp_ne
  have hD'pos : 0 < D' := by
    by_contra h
    have hD'0 : D' = 0 := Nat.eq_zero_of_not_pos h
    exact hD_ne (by rw [hDdef, hD'0, mul_zero])
  have hdiv_le : n * D' ≤ D' := by
    have h' : (n * D') ∣ D' := by simpa [hDdef] using hD_dvd
    exact Nat.le_of_dvd hD'pos h'
  have hnle : n ≤ 1 := by
    exact Nat.le_of_mul_le_mul_right (a := n) (b := 1) (c := D')
      (by simpa [one_mul] using hdiv_le) hD'pos
  have hn1 : n = 1 := by omega
  have h_na : r.natAbs = 1 := by simpa [n] using hn1
  rw [Int.isUnit_iff]
  rcases (Int.natAbs_eq_iff.mp h_na) with h | h
  · exact Or.inl h
  · exact Or.inr h

private lemma int_natAbs_cast_abs (z : ℤ) : (z.natAbs : ℝ) = |(z : ℝ)| := by
  by_cases hz : 0 ≤ z
  · rw [abs_of_nonneg (by exact_mod_cast hz : (0 : ℝ) ≤ (z : ℝ))]
    have hn : ((z.natAbs : ℕ) : ℤ) = z := Int.natAbs_of_nonneg hz
    rw [← hn]
    norm_num
  · have hzlt : z < 0 := lt_of_not_ge hz
    rw [abs_of_neg (by exact_mod_cast hzlt : (z : ℝ) < 0)]
    have hz_eq : z = -((z.natAbs : ℕ) : ℤ) := by
      rcases Int.natAbs_eq z with h | h
      · have hzge : (0 : ℤ) ≤ z := by rw [h]; positivity
        omega
      · exact h
    rw [hz_eq]
    norm_num



/-- After clearing denominators the ℚ-map of `clearPoly p D` is `C (D : ℚ) * p`. -/
private lemma clearPoly_map_eq (p : Polynomial ℚ) (D : ℕ) (hD : lcmDen p ∣ D) :
    (clearPoly p D).map (algebraMap ℤ ℚ) = C (D : ℚ) * p := by
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_map, Polynomial.coeff_C_mul]
  by_cases hi : i ∈ p.support
  · simpa using (clearPoly_coeff_rat p D hD hi)
  · have hp0 : p.coeff i = 0 := (Polynomial.notMem_support_iff.mp hi)
    rw [clearPoly_coeff]
    simp [hp0]

/-- Gauss's lemma for the cleared polynomial: if a primitive integer `P` with
`P_ℚ = C (D : ℚ) * p` divides (over ℚ) an integer polynomial `S`, then `P` divides `S`
over ℤ. -/
private lemma primitive_dvd_of_dvd_rat (P : Polynomial ℤ) (hprim : P.IsPrimitive)
    (p : Polynomial ℚ) (D : ℕ) (hD0 : (D : ℚ) ≠ 0) (hmap : P.map (algebraMap ℤ ℚ) = C (D : ℚ) * p)
    {S : Polynomial ℤ} (hSdvd : p ∣ S.map (algebraMap ℤ ℚ)) : P ∣ S := by
  rcases hSdvd with ⟨q, hq⟩
  let Q : Polynomial ℚ := C (D : ℚ)⁻¹ * q
  have hQeq : Q * P.map (algebraMap ℤ ℚ) = S.map (algebraMap ℤ ℚ) := by
    calc
      Q * P.map (algebraMap ℤ ℚ) = (C (D : ℚ)⁻¹ * q) * (C (D : ℚ) * p) := by rw [hmap]
      _ = S.map (algebraMap ℤ ℚ) := by
        rw [hq]
        calc
          (C (D : ℚ)⁻¹ * q) * (C (D : ℚ) * p) = (C (D : ℚ) * (C (D : ℚ)⁻¹ * q)) * p := by ring
          _ = q * p := by
            have hC : C (D : ℚ) * (C (D : ℚ)⁻¹ * q) = q := by
              rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hD0, C_1, one_mul]
            rw [hC]
          _ = p * q := by ring
  have hiff : Q * P.map (algebraMap ℤ ℚ) ∈ Polynomial.lifts (algebraMap ℤ ℚ) ↔
      Q ∈ Polynomial.lifts (algebraMap ℤ ℚ) :=
    IsPrimitive.mul_map_mem_lifts_iff (R := ℤ) (K := ℚ) (f := P) hprim
  have hleft : Q * P.map (algebraMap ℤ ℚ) ∈ Polynomial.lifts (algebraMap ℤ ℚ) := by
    rw [hQeq]
    exact ⟨S, rfl⟩
  have hQmem : Q ∈ Polynomial.lifts (algebraMap ℤ ℚ) := (hiff.mp hleft)
  rcases hQmem with ⟨Q0, hQ0⟩
  have hQ0m : Q0.map (algebraMap ℤ ℚ) = Q := by simpa using hQ0
  have hpq0 : (P * Q0).map (algebraMap ℤ ℚ) = S.map (algebraMap ℤ ℚ) := by
    rw [Polynomial.map_mul]
    calc
      P.map (algebraMap ℤ ℚ) * Q0.map (algebraMap ℤ ℚ)
          = P.map (algebraMap ℤ ℚ) * Q := by rw [hQ0m]
      _ = S.map (algebraMap ℤ ℚ) := by
        rw [mul_comm]
        exact hQeq
  have hpq : P * Q0 = S := (Polynomial.map_injective (algebraMap ℤ ℚ) Int.cast_injective) hpq0
  exact ⟨Q0, hpq.symm⟩

/-- The denominators-cleared minimal polynomial divides `S` over ℤ. -/
private lemma clearDen_dvd (p : Polynomial ℚ) (hp : p.Monic) {S : Polynomial ℤ}
    (hSdvd : p ∣ S.map (algebraMap ℤ ℚ)) : clearPoly p (lcmDen p) ∣ S := by
  let P : Polynomial ℤ := clearPoly p (lcmDen p)
  have hprim : P.IsPrimitive := by
    dsimp [P]
    exact clearPoly_isPrimitive p hp
  have hD0 : ((lcmDen p : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (lcmDen_ne_zero p (Polynomial.Monic.ne_zero hp))
  have hmap : P.map (algebraMap ℤ ℚ) = C (lcmDen p : ℚ) * p := by
    dsimp [P]
    exact clearPoly_map_eq p (lcmDen p) (by rfl)
  exact primitive_dvd_of_dvd_rat P hprim p (lcmDen p) hD0 hmap hSdvd

/-- The degree of the denominators-cleared polynomial is at most that of the original. -/
private lemma clearPoly_natDegree_le (p : Polynomial ℚ) (D : ℕ) :
    (clearPoly p D).natDegree ≤ p.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [clearPoly_coeff]
  have hp0 : p.coeff m = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hm
  simp [hp0]

/-- The naive-height sup (over the support of `p`) is bounded by the sup-norm of the
denominators-cleared polynomial. -/
private lemma height_sup_le_clearNorm (p : Polynomial ℚ) (D : ℕ) :
    ((((p.support.sup (fun i => (D * p.coeff i).num.natAbs) : ℕ) : ℝ)) ≤
      ((clearPoly p D).map (Int.castRingHom ℝ)).supNorm) := by
  apply finset_sup_nat_cast_le
  · exact ((clearPoly p D).map (Int.castRingHom ℝ)).supNorm_nonneg
  · intro i hi
    calc
      ((D * p.coeff i).num.natAbs : ℝ) = |(((clearPoly p D).coeff i : ℤ) : ℝ)| := by
        rw [clearPoly_coeff]
        exact int_natAbs_cast_abs (D * p.coeff i).num
      _ = ‖(((clearPoly p D).map (Int.castRingHom ℝ)).coeff i)‖ := by
        rw [Polynomial.coeff_map]
        rfl
      _ ≤ ((clearPoly p D).map (Int.castRingHom ℝ)).supNorm := Polynomial.le_supNorm _ i

theorem root_height_bound (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (S : Polynomial ℤ) (α : ℂ),
      S ≠ 0 → S.natDegree ≤ N →
      Polynomial.IsRoot (S.map (Int.castRingHom ℂ)) α →
      IsAlgebraic ℚ α ∧
      Polynomial.natDegree (minpoly ℚ α) ≤ N ∧
      ((((let p := minpoly ℚ α;
          let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val);
          Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs) : ℕ) : ℝ)) ≤
        C * ((S.map (Int.castRingHom ℝ)).supNorm)) := by
  let C : ℝ := (2 : ℝ) ^ N * Real.sqrt (N + 1)
  refine ⟨C, ?_, ?_⟩
  · positivity
  · intro S α hS hdegS hroot
    have hAlg : IsAlgebraic ℚ α := isAlgebraic_of_root_int S hS α hroot
    have hdvd : minpoly ℚ α ∣ S.map (algebraMap ℤ ℚ) := minpoly_dvd_int_poly S α hroot
    have hSℚne : S.map (algebraMap ℤ ℚ) ≠ 0 := by
      exact (Polynomial.map_eq_zero_iff (f := algebraMap ℤ ℚ) Int.cast_injective).not.mpr hS
    have hdegmin_le : Polynomial.natDegree (minpoly ℚ α) ≤ N := by
      have hdegm : Polynomial.natDegree (minpoly ℚ α) ≤ (S.map (algebraMap ℤ ℚ)).natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd hSℚne
      have hdegSℚ : (S.map (algebraMap ℤ ℚ)).natDegree = S.natDegree := by
        exact Polynomial.natDegree_map_eq_of_injective (f := algebraMap ℤ ℚ) Int.cast_injective S
      exact le_trans hdegm (by
        rw [hdegSℚ]
        exact hdegS)
    refine ⟨hAlg, hdegmin_le, ?_⟩
    let p : Polynomial ℚ := minpoly ℚ α
    let D : ℕ := lcmDen p
    let P : Polynomial ℤ := clearPoly p D
    have hmonic : p.Monic := by
      dsimp [p]
      exact minpoly.monic (IsAlgebraic.isIntegral hAlg)
    have hp_ne : p ≠ 0 := Polynomial.Monic.ne_zero hmonic
    have hDpos : 0 < D := by
      dsimp [D]
      exact Nat.pos_of_ne_zero (lcmDen_ne_zero p hp_ne)
    have hPne : P ≠ 0 := by
      dsimp [P, D]
      exact clearPoly_ne_zero p D hp_ne (by rfl) hDpos
    have hPdiv : P ∣ S := by
      dsimp [P, D]
      exact clearDen_dvd p hmonic hdvd
    have hdegP : P.natDegree ≤ N := by
      have hdegP_le_p : P.natDegree ≤ p.natDegree := by
        dsimp [P]
        exact clearPoly_natDegree_le p D
      have hdegp_le : p.natDegree ≤ N := by
        dsimp [p]
        exact hdegmin_le
      exact le_trans hdegP_le_p hdegp_le
    have hfac := int_poly_factor_supNorm_le N (hP := hPne) (hQ := hS) hdegP hdegS hPdiv
    have hH1 : ((((p.support.sup (fun i => (D * p.coeff i).num.natAbs) : ℕ) : ℝ)) ≤
        ((clearPoly p D).map (Int.castRingHom ℝ)).supNorm) :=
      height_sup_le_clearNorm p D
    have hfac' : ((clearPoly p D).map (Int.castRingHom ℝ)).supNorm ≤
        C * ((S.map (Int.castRingHom ℝ)).supNorm) := by
      simpa [P, C] using hfac
    have hH2 : ((((p.support.sup (fun i => (D * p.coeff i).num.natAbs) : ℕ) : ℝ)) ≤
        C * ((S.map (Int.castRingHom ℝ)).supNorm)) :=
      le_trans hH1 hfac'
    simpa [p, D, lcmDen] using hH2