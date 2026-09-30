import Mathlib
import Submission.Work.BW.bm_base
import Submission.Work.BW.bm_eps_bounds
import Submission.Work.BW.bm_prod_norm_lt_one
import Submission.Work.BW.mahlerInversionClosed
import Submission.Work.BW.sigmaLessThanSumLog
import Submission.Work.BW.quadratic_case
import Submission.Work.BW.pow_eq_one_of_prod_roots_vanishes
import Submission.Work.BW.mahlerDefs
import Submission.Work.BW.roots_facts
import Submission.Work.BW.pair_decomposition

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial

/-! ## Blanksby–Montgomery, Theorem 1

Explicit lower bound for the Mahler measure of a non-cyclotomic algebraic integer
(P. E. Blanksby, H. L. Montgomery, *Algebraic integers near the unit circle*,
Acta Arith. **18** (1971), 355–369).

## Proof architecture

Let `P ∈ ℤ[X]` be monic irreducible of degree `n = 2N > 1` with Mahler measure
`M ≤ 1 + 1/(52 n log 6n)` and let `R = (P.map ℂ).roots`.

1. `quadratic_case` disposes of `n = 2`.
2. `mahlerInversionClosed` (reciprocity below the threshold, via the power-sum argument of
   `nonreciprocal_measure_gt`) shows that `R` is closed under `z ↦ z⁻¹`; with
   `root_inv_ne_self` (no root is `±1`) and separability, `multiset_map_inv_eq_self` turns this
   into `R.map (·⁻¹) = R`.
3. `pair_decomposition` writes `R` as the `N` inverse pairs `{w_j, w_j⁻¹}` with `‖w_j‖ ≤ 1`,
   `n = 2N`, and `prod_norm_eq_inv_mahler` gives `∏_j ‖w_j‖ = M⁻¹`.
4. With `ρ' = 1 - 1/(12N)`, `K = ⌊(54/5) N log 12N⌋`, `ε_j = min ρ' (‖w_j‖^K)`:
   `bm_eps_bounds` supplies `exp(-1/A0) ≤ ε_j ≤ ρ'` and `exp(-2/A0) ≤ ∏_j ε_j`;
   `sigmaLessThanSumLog` (Blanksby–Montgomery's Lemmas 2 and 3, using the Fejér moment
   inequalities `logMoment_le`, `logMoment_sq_ge_lin`, the pigeonhole `sigma_pigeonhole` and the
   explicit numerics `mahler_numeric`) produces `1 ≤ k ≤ K` with `σ_k < ∑_j log ε_j`.
5. `bm_prod_norm_lt_one` then gives `∏_{z ∈ R} ‖z^k - 1‖ < 1`; since
   `∏_{z ∈ R} (z^k - 1)` is a rational integer (`roots_facts`), it vanishes, and
   `pow_eq_one_of_prod_roots_vanishes` concludes `α^k = 1`.
-/

/-- Separability of the `ℂ`-image of a monic irreducible integer polynomial. -/
private lemma separable_map_int_roots (P : Polynomial ℤ) (hP : P.Monic) (hirr : Irreducible P)
    (hdeg : 1 < P.natDegree) : (P.map (Int.castRingHom ℂ)).Separable := by
  have heq : ((algebraMap ℤ ℚ : ℤ →+* ℚ)) = Int.castRingHom ℚ := by ext n; simp
  have hirrQ : Irreducible (P.map (Int.castRingHom ℚ)) := by
    have h := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
      (R := ℤ) (K := ℚ) hP).mp hirr
    rwa [heq] at h
  have hsepQ : (P.map (Int.castRingHom ℚ)).Separable := hirrQ.separable
  have hcomp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := by
    ext n; simp
  have hmap : (P.map (Int.castRingHom ℂ))
      = (P.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) := by
    rw [Polynomial.map_map, hcomp]
  rw [hmap]
  exact Separable.map hsepQ (f := algebraMap ℚ ℂ)

/-- Writing a nonzero complex number as `‖w‖ · exp (2π i θ)` with `θ = arg w / (2π)`. -/
private lemma theta_arg (w : ℂ) (hw : w ≠ 0) :
    w = (‖w‖ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((w.arg / (2 * Real.pi) : ℝ) : ℂ)) := by
  have h1 : w / ((‖w‖ : ℝ) : ℂ) = Complex.exp (((w.arg : ℂ)) * Complex.I) :=
    div_norm_eq_exp_arg w hw
  have harg : ((w.arg : ℂ)) * Complex.I
      = 2 * (Real.pi : ℂ) * Complex.I * (((w.arg / (2 * Real.pi) : ℝ)) : ℂ) := by
    push_cast
    field_simp
  have hne : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (norm_pos_iff.mpr hw))
  calc w = ((‖w‖ : ℝ) : ℂ) * (w / ((‖w‖ : ℝ) : ℂ)) := by
        rw [mul_div_cancel₀ w hne]
    _ = ((‖w‖ : ℝ) : ℂ) * Complex.exp (((w.arg : ℂ)) * Complex.I) := by rw [h1]
    _ = (‖w‖ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((w.arg / (2 * Real.pi) : ℝ) : ℂ)) := by
        rw [harg]

/-- **Blanksby–Montgomery (Acta Arith. 18 (1971), 355–369), Theorem 1** (an explicit lower bound
for the Mahler measure of a non-cyclotomic algebraic integer).

If `P ∈ ℤ[X]` is monic, irreducible, of degree `n > 1`, and its Mahler measure is at most
`1 + 1/(52 n log 6n)`, then every complex root of `P` is a root of unity. -/
theorem blanksby_montgomery (P : Polynomial ℤ) (hP : P.Monic) (hirr : Irreducible P)
    (hdeg : 1 < P.natDegree)
    (hM : (Polynomial.map (Int.castRingHom ℂ) P).mahlerMeasure ≤
      1 + 1 / (52 * (P.natDegree : ℝ) * Real.log (6 * (P.natDegree : ℝ))))
    {α : ℂ} (hα : (Polynomial.map (Int.castRingHom ℂ) P).IsRoot α) :
    ∃ k : ℕ, 0 < k ∧ α ^ k = 1 := by
  rcases eq_or_ne P.natDegree 2 with h2 | h2
  · -- degree `2`
    refine quadratic_case P hP hirr h2 ?_ hα
    rw [h2] at hM
    have h62 : (6 : ℝ) * ((2 : ℕ) : ℝ) = 12 := by norm_num
    rw [h62] at hM
    convert hM using 1 <;> norm_num
  · have hn3 : 3 ≤ P.natDegree := by omega
    set Q : ℂ[X] := P.map (Int.castRingHom ℂ) with hQ
    have hQne : Q ≠ 0 := (hP.map (Int.castRingHom ℂ)).ne_zero
    have hcardQ : Q.roots.card = P.natDegree := by
      have h1 : Q.roots.card = Q.natDegree :=
        (Polynomial.splits_iff_card_roots).mp (IsAlgClosed.splits Q)
      rw [h1, hQ,
        Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℂ)) P]
    have hroot_ne : ∀ z ∈ Q.roots, z ≠ 0 := by
      obtain ⟨h1, -, -, -⟩ := roots_facts P hP hirr hdeg
      intro z hz
      exact h1 z (by rwa [hQ] at hz)
    have hroot_fix : ∀ z ∈ Q.roots, z⁻¹ ≠ z := by
      intro z hz
      exact root_inv_ne_self P hP hirr hdeg ((Polynomial.mem_roots hQne).mp hz)
    have hinv : ∀ z ∈ Q.roots, z⁻¹ ∈ Q.roots := by
      intro z hz
      have hz' : (P.map (Int.castRingHom ℂ)).IsRoot z :=
        (Polynomial.mem_roots hQne).mp (by rwa [hQ] at hz)
      rw [hQ]
      exact (Polynomial.mem_roots (hP.map (Int.castRingHom ℂ)).ne_zero).mpr
        (mahlerInversionClosed P hP hirr hdeg hM hz')
    have hnodup : Q.roots.Nodup :=
      Polynomial.nodup_roots (separable_map_int_roots P hP hirr hdeg)
    have hmult : Q.roots.map (fun z => z⁻¹) = Q.roots :=
      multiset_map_inv_eq_self Q.roots hroot_ne hnodup hinv
    obtain ⟨N, w, hwnorm, hcardN, hR⟩ :=
      pair_decomposition Q.roots hroot_ne hmult hroot_fix
    have hdeg2N : P.natDegree = 2 * N := by rw [← hcardQ]; exact hcardN
    have hN2 : 2 ≤ N := by omega
    have hN1 : 1 ≤ N := by omega
    have hwmem : ∀ j : Fin N, w j ∈ Q.roots := by
      intro j
      rw [hR]
      exact Multiset.mem_add.mpr
        (Or.inl (Multiset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩))
    have hw0 : ∀ j, w j ≠ 0 := fun j => hroot_ne (w j) (hwmem j)
    have hprod : (∏ j, ‖w j‖)⁻¹ = Q.mahlerMeasure := by
      rw [hQ]
      exact prod_norm_eq_inv_mahler P hP hwnorm hw0 hR
    let θ : Fin N → ℝ := fun j => (w j).arg / (2 * Real.pi)
    have hwθ : ∀ j, w j = (‖w j‖ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (θ j)) := by
      intro j
      exact theta_arg (w j) (hw0 j)
    let ε : Fin N → ℝ := fun j => min (rhoP N) (‖w j‖ ^ (KK N))
    obtain ⟨hεlow, hεhigh, hεprod⟩ :=
      bm_eps_bounds P hP (by rw [← hQ]; exact hM) hN2 hdeg2N w hwnorm hprod
    have hε0 : ∀ j, 0 < ε j := fun j => lt_of_lt_of_le (Real.exp_pos _) (hεlow j)
    have hε1 : ∀ j, ε j < 1 := by
      intro j
      have h1 : rhoP N < 1 := by
        rw [rhoP]
        have h2 : (0 : ℝ) < 1 / (12 * (N : ℝ)) := by
          have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
          positivity
        linarith
      exact lt_of_le_of_lt (hεhigh j) h1
    obtain ⟨k, hkIcc, hσ⟩ := sigmaLessThanSumLog hN2 ε θ hε0 hε1 hεlow hεhigh hεprod
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hkIcc).1
    have hkK : k ≤ KK N := (Finset.mem_Icc.mp hkIcc).2
    have hprodlt : ((P.map (Int.castRingHom ℂ)).roots.map (fun u => ‖u ^ k - 1‖)).prod < 1 := by
      rw [← hQ]
      exact bm_prod_norm_lt_one P hP hN1 w θ hw0 hwnorm hwθ hR hk1 hkK hσ
    -- the product `∏_{z ∈ R} (z^k - 1)` is a rational integer of modulus `< 1`, hence vanishes
    obtain ⟨m, hm⟩ := (roots_facts P hP hirr hdeg).2.2.1 k hk1
    have hnorm_le : ‖((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ k - 1)).prod‖
        ≤ ((P.map (Int.castRingHom ℂ)).roots.map (fun z => ‖z ^ k - 1‖)).prod := by
      induction (P.map (Int.castRingHom ℂ)).roots using Multiset.induction_on with
      | empty => simp
      | cons a s ih =>
        simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
        exact mul_le_mul_of_nonneg_left ih (norm_nonneg _)
    have hm0 : m = 0 := by
      have h1 : ‖(m : ℂ)‖ < 1 := by
        rw [show (m : ℂ) = ((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ k - 1)).prod
          from hm.symm]
        exact lt_of_le_of_lt hnorm_le hprodlt
      have h2 : |(m : ℝ)| < 1 := by simpa using h1
      have h3 : ((m.natAbs : ℕ) : ℝ) < 1 := by simpa [Int.cast_abs] using h2
      have h3' : m.natAbs < 1 := by exact_mod_cast h3
      exact Int.natAbs_eq_zero.mp (Nat.lt_one_iff.mp h3')
    exact ⟨k, hk1, pow_eq_one_of_prod_roots_vanishes P hP hirr hdeg hα hk1
      (by rw [hm, hm0]; simp)⟩

end Work.BW
