import Mathlib
import Submission.Work.BW.roots_facts

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial

/-! ## Base layer for the Blanksby–Montgomery assembly

This module collects the elementary facts about a monic irreducible `P ∈ ℤ[X]` of degree `> 1`
that the main averaging argument uses, together with the geometric Lemma 4 of
Blanksby–Montgomery and the multiset bookkeeping.

It is deliberately stated in terms of a plain multiset `R`, so that it can be used both for the
root multiset `(P.map (Int.castRingHom ℂ)).roots` and for the `ℂ`-image of `P`.
-/

/-- For a monic integer polynomial the Mahler measure of its image in `ℂ[X]` is the product of
`max 1 ‖z‖` over the complex roots `z`. -/
lemma mahlerMeasure_map_int_eq (P : ℤ[X]) (hP : P.Monic) :
    (P.map (Int.castRingHom ℂ)).mahlerMeasure
      = ((P.map (Int.castRingHom ℂ)).roots.map (fun z => max 1 ‖z‖)).prod := by
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots,
    leadingCoeff_map_of_injective (Int.castRingHom ℂ).injective_int, hP.leadingCoeff, map_one,
    norm_one, one_mul]

/-- A root of a monic irreducible integer polynomial of degree `> 1` is nonzero. -/
lemma root_ne_zero_of_natDegree_gt_one (P : ℤ[X]) (hmon : P.Monic) (hirr : Irreducible P)
    (hdeg : 1 < P.natDegree) {α : ℂ} (hα : (P.map (Int.castRingHom ℂ)).IsRoot α) : α ≠ 0 := by
  intro h
  have hcoeff : P.coeff 0 = 0 := by
    have h1 : (P.map (Int.castRingHom ℂ)).coeff 0 = 0 := by
      rw [IsRoot.def, h] at hα
      rwa [← coeff_zero_eq_eval_zero] at hα
    have h2 : ((P.coeff 0 : ℤ) : ℂ) = 0 := by simpa [coeff_map] using h1
    exact_mod_cast h2
  obtain ⟨Q, hQ⟩ := X_dvd_iff.mpr hcoeff
  have hQne : Q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hQ
    exact hmon.ne_zero hQ
  have hdegQ : P.natDegree = 1 + Q.natDegree := by
    rw [hQ, natDegree_mul X_ne_zero hQne, natDegree_X]
  rcases hirr.isUnit_or_isUnit hQ with hunit | hunit
  · exact not_isUnit_X hunit
  · have := natDegree_eq_zero_of_isUnit hunit
    omega

/-- A real inequality underlying the geometric lemma. -/
private lemma annulus_aux {ρ r c : ℝ} (hρ0 : 0 < ρ) (_hρ1 : ρ ≤ 1) (hr : ρ ≤ r)
    (hr' : r ≤ ρ⁻¹) (hc : c ≤ 1) : (r - ρ⁻¹) * (r + ρ⁻¹ - 2 * c) ≤ 0 := by
  have h1 : r - ρ⁻¹ ≤ 0 := by linarith
  have h2 : 0 ≤ r + ρ⁻¹ - 2 * c := by
    have h2' : 2 ≤ ρ + ρ⁻¹ := by
      have : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hρ0)
      nlinarith [sq_nonneg (ρ - 1), hρ0, inv_pos.mpr hρ0]
    linarith
  exact mul_nonpos_of_nonpos_of_nonneg h1 h2

/-- **The geometric lemma of Blanksby–Montgomery** (their Lemma 4): for `0 < ρ ≤ 1` and
`ρ ≤ ‖z‖ ≤ ρ⁻¹` one has `‖z - 1‖ ≤ ρ⁻¹ * ‖ρ * (z / ‖z‖) - 1‖`. -/
lemma norm_sub_one_le_of_annulus {z : ℂ} {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hz : ρ ≤ ‖z‖) (hz' : ‖z‖ ≤ ρ⁻¹) :
    ‖z - 1‖ ≤ ρ⁻¹ * ‖(ρ : ℂ) * (z / (‖z‖ : ℂ)) - 1‖ := by
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hρ0 hz
  set u : ℂ := z / (‖z‖ : ℂ) with hu
  have hz0 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hzpos)
  have huz : (‖z‖ : ℂ) * u = z := by
    rw [hu]; exact mul_div_cancel₀ z hz0
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hzpos,
      div_self (ne_of_gt hzpos)]
  have hcsq : u.re ^ 2 + u.im ^ 2 = 1 := by
    have h : ‖u‖ ^ 2 = 1 := by rw [hun]; norm_num
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h
    nlinarith [h]
  have hu_re_le : u.re ≤ 1 := by nlinarith [hcsq, sq_nonneg u.im]
  have hkey := annulus_aux hρ0 hρ1 hz hz' hu_re_le
  have hρinv : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hρ0)
  have hzre : z.re = ‖z‖ * u.re := by
    conv_lhs => rw [← huz]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hzim : z.im = ‖z‖ * u.im := by
    conv_lhs => rw [← huz]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have e1 : ‖z - 1‖ ^ 2 = (‖z‖ * u.re - 1) ^ 2 + (‖z‖ * u.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, hzre, hzim]
    ring
  have e2 : ‖(ρ : ℂ) * u - 1‖ ^ 2 = (ρ * u.re - 1) ^ 2 + (ρ * u.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hsq : ‖z - 1‖ ^ 2 ≤ (ρ⁻¹ * ‖(ρ : ℂ) * u - 1‖) ^ 2 := by
    rw [e1]
    have hrr : (ρ⁻¹ * ‖(ρ : ℂ) * u - 1‖) ^ 2
        = ρ⁻¹ ^ 2 * ((ρ * u.re - 1) ^ 2 + (ρ * u.im) ^ 2) := by
      rw [mul_pow, e2]
    rw [hrr]
    have hL : (‖z‖ * u.re - 1) ^ 2 + (‖z‖ * u.im) ^ 2 = ‖z‖ ^ 2 - 2 * ‖z‖ * u.re + 1 := by
      have h : (‖z‖ * u.re - 1) ^ 2 + (‖z‖ * u.im) ^ 2
          = ‖z‖ ^ 2 * (u.re ^ 2 + u.im ^ 2) - 2 * ‖z‖ * u.re + 1 := by ring
      rw [h, hcsq]; ring
    have hR : ρ⁻¹ ^ 2 * ((ρ * u.re - 1) ^ 2 + (ρ * u.im) ^ 2)
        = ρ⁻¹ ^ 2 * (ρ ^ 2 - 2 * ρ * u.re + 1) := by
      have h : (ρ * u.re - 1) ^ 2 + (ρ * u.im) ^ 2
          = ρ ^ 2 * (u.re ^ 2 + u.im ^ 2) - 2 * ρ * u.re + 1 := by ring
      rw [h, hcsq]; ring
    rw [hL, hR]
    have hp2 : ρ⁻¹ ^ 2 * ρ ^ 2 = 1 := by
      rw [← mul_pow, mul_comm ρ⁻¹ ρ, hρinv, one_pow]
    have hid : ρ⁻¹ ^ 2 * (ρ ^ 2 - 2 * ρ * u.re + 1) - (‖z‖ ^ 2 - 2 * ‖z‖ * u.re + 1)
        = (ρ⁻¹ - ‖z‖) * (ρ⁻¹ + ‖z‖ - 2 * u.re) := by nlinarith [hp2]
    have hpos : 0 ≤ (ρ⁻¹ - ‖z‖) * (ρ⁻¹ + ‖z‖ - 2 * u.re) := by nlinarith [hkey]
    linarith [hid, hpos]
  have h3 : 0 ≤ ρ⁻¹ * ‖(ρ : ℂ) * u - 1‖ := by positivity
  have h4 := (sq_le_sq.mp hsq)
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg h3] at h4

/-- The modulus of the constant coefficient of a monic integer polynomial is at most the Mahler
measure of its image in `ℂ[X]` (via Mignotte's coefficient bound, Mathlib's
`norm_coeff_le_choose_mul_mahlerMeasure`). -/
lemma abs_coeff_zero_le_mahler (P : Polynomial ℤ) (hP : P.Monic) (hdeg : 1 < P.natDegree) :
    |((P.coeff 0 : ℤ) : ℝ)| ≤ (P.map (Int.castRingHom ℂ)).mahlerMeasure := by
  have h := norm_coeff_le_choose_mul_mahlerMeasure 0 (P.map (Int.castRingHom ℂ))
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul] at h
  have hc : (P.map (Int.castRingHom ℂ)).coeff 0 = ((P.coeff 0 : ℤ) : ℂ) := by
    rw [Polynomial.coeff_map]
    rfl
  rwa [hc, Complex.norm_intCast] at h

/-- The Mahler measure of a nonzero polynomial over `ℂ` is at least `1`. -/
lemma one_le_mahler (P : Polynomial ℤ) (hP : P.Monic) :
    1 ≤ (P.map (Int.castRingHom ℂ)).mahlerMeasure := by
  rw [mahlerMeasure_map_int_eq P hP]
  exact one_le_prod_max_one_norm_roots _

/-- A monic irreducible integer polynomial of degree `> 1` whose Mahler measure is at most
`1 + 1/(52 n log 6n)` has constant coefficient `±1`. -/
lemma coeff_zero_eq_one_or_neg_one (P : Polynomial ℤ) (hP : P.Monic) (hirr : Irreducible P)
    (hdeg : 1 < P.natDegree)
    (hM : (P.map (Int.castRingHom ℂ)).mahlerMeasure ≤
      1 + 1 / (52 * (P.natDegree : ℝ) * Real.log (6 * (P.natDegree : ℝ)))) :
    P.coeff 0 = 1 ∨ P.coeff 0 = -1 := by
  obtain ⟨-, -, -, hc0⟩ := roots_facts P hP hirr hdeg
  have hn2 : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hdeg
  have hlog : 0 < Real.log (6 * (P.natDegree : ℝ)) := by
    apply Real.log_pos
    nlinarith
  have hlog' : (22 : ℝ) / 13 ≤ Real.log (6 * (P.natDegree : ℝ)) := by
    have h11 : (0 : ℝ) ≤ 6 * (P.natDegree : ℝ) - 1 := by nlinarith
    have h := Real.le_log_one_add_of_nonneg h11
    have e1 : (1 : ℝ) + (6 * (P.natDegree : ℝ) - 1) = 6 * (P.natDegree : ℝ) := by ring
    rw [e1] at h
    have e2 : 6 * (P.natDegree : ℝ) - 1 + 2 = 6 * (P.natDegree : ℝ) + 1 := by ring
    rw [e2] at h
    have hmono : (22 : ℝ) / 13
        ≤ 2 * (6 * (P.natDegree : ℝ) - 1) / (6 * (P.natDegree : ℝ) + 1) := by
      rw [le_div_iff₀ (by nlinarith)]
      nlinarith
    linarith
  have hbig : 1 < 52 * (P.natDegree : ℝ) * Real.log (6 * (P.natDegree : ℝ)) := by nlinarith
  have hlt : |((P.coeff 0 : ℤ) : ℝ)| < 2 := by
    have h1 := abs_coeff_zero_le_mahler P hP hdeg
    have h2 : 1 / (52 * (P.natDegree : ℝ) * Real.log (6 * (P.natDegree : ℝ))) < 1 := by
      rw [div_lt_one (by positivity)]
      exact hbig
    linarith
  have hle1 : P.coeff 0 ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have h2 : (2 : ℤ) ≤ P.coeff 0 := by omega
    have h3 : (2 : ℝ) ≤ ((P.coeff 0 : ℤ) : ℝ) := by exact_mod_cast h2
    have h4 : |((P.coeff 0 : ℤ) : ℝ)| = ((P.coeff 0 : ℤ) : ℝ) := abs_of_pos (by linarith)
    linarith [h4]
  have hge1 : -1 ≤ P.coeff 0 := by
    by_contra hcon
    push_neg at hcon
    have h2 : P.coeff 0 ≤ -2 := by omega
    have h3 : ((P.coeff 0 : ℤ) : ℝ) ≤ -2 := by exact_mod_cast h2
    have h4 : |((P.coeff 0 : ℤ) : ℝ)| = -((P.coeff 0 : ℤ) : ℝ) := abs_of_neg (by linarith)
    linarith [h4]
  omega

/-- `w / ‖w‖ = exp(w.arg · I)` for `w ≠ 0`. -/
lemma div_norm_eq_exp_arg (w : ℂ) (hw : w ≠ 0) :
    w / ((‖w‖ : ℝ) : ℂ) = Complex.exp ((w.arg : ℂ) * Complex.I) := by
  have h := Complex.norm_mul_exp_arg_mul_I w
  have h' : ((‖w‖ : ℝ) : ℂ) * Complex.exp ((w.arg : ℂ) * Complex.I) = w := by
    simpa using h
  have hne : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by
    have hpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
    exact_mod_cast (ne_of_gt hpos)
  rw [div_eq_iff hne, mul_comm]
  exact h'.symm

/-- **Geometric step** (Blanksby–Montgomery's Lemma 4, in the form used here).  For a nonzero `w`
of modulus `≤ 1`, a level `ε ∈ (0,1]` with `ε ≤ ‖w‖^K`, and `1 ≤ k ≤ K`,
`‖w^k - 1‖ ≤ ε⁻¹ ‖ε·(w/‖w‖)^k - 1‖`. -/
lemma norm_pow_sub_one_le_of_trunc (w : ℂ) (hw : 0 < ‖w‖) (hw1 : ‖w‖ ≤ 1) {K k : ℕ}
    (hk : k ≤ K) (hk1 : 1 ≤ k) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hεK : ε ≤ ‖w‖ ^ K) :
    ‖w ^ k - 1‖ ≤ ε⁻¹ * ‖(ε : ℂ) * (w / ((‖w‖ : ℝ) : ℂ)) ^ k - 1‖ := by
  have hle : ε ≤ ‖w ^ k‖ := by
    rw [norm_pow]
    exact hεK.trans (pow_le_pow_of_le_one (norm_nonneg w) hw1 hk)
  have hone : ‖w‖ ^ k ≤ 1 := by
    simpa using pow_le_pow_of_le_one (norm_nonneg w) hw1 (Nat.zero_le k)
  have hann : ‖w ^ k‖ ≤ ε⁻¹ := by
    rw [norm_pow]
    exact hone.trans ((one_le_inv₀ hε0).mpr hε1)
  have h := norm_sub_one_le_of_annulus hε0 hε1 hle hann
  have hz : ((w ^ k) / ((‖w ^ k‖ : ℝ) : ℂ)) = (w / ((‖w‖ : ℝ) : ℂ)) ^ k := by
    rw [norm_pow, div_pow]
    norm_cast
  rwa [hz] at h

/-- `1` and `-1` are never roots of a monic irreducible integer polynomial of degree `> 1`. -/
lemma not_isRoot_one_or_neg_one (P : Polynomial ℤ) (hP : P.Monic) (hirr : Irreducible P)
    (hdeg : 1 < P.natDegree) {z : ℂ} (hz : (P.map (Int.castRingHom ℂ)).IsRoot z)
    (hzz : z * z = 1) : False := by
  have hzz' : z = 1 ∨ z = -1 := by
    have h : (z - 1) * (z + 1) = 0 := by linear_combination hzz
    rcases mul_eq_zero.mp h with h | h
    · left; exact sub_eq_zero.mp h
    · right; exact add_eq_zero_iff_eq_neg.mp h
  have hne : P.natDegree ≠ 1 := by omega
  rcases hzz' with h | h
  · subst h
    have hz1 : (P.map (Int.castRingHom ℂ)).IsRoot ((1 : ℤ) : ℂ) := by simpa using hz
    exact hirr.not_isRoot_of_natDegree_ne_one hne
      (hz1.of_map (Int.castRingHom ℂ).injective_int)
  · subst h
    have hz' : (P.map (Int.castRingHom ℂ)).IsRoot ((-1 : ℤ) : ℂ) := by simpa using hz
    exact hirr.not_isRoot_of_natDegree_ne_one hne
      (hz'.of_map (Int.castRingHom ℂ).injective_int)

/-- Roots of a monic irreducible polynomial of degree `> 1` are never their own inverses. -/
lemma root_inv_ne_self (P : Polynomial ℤ) (hP : P.Monic) (hirr : Irreducible P)
    (hdeg : 1 < P.natDegree) {z : ℂ} (hz : (P.map (Int.castRingHom ℂ)).IsRoot z) :
    z⁻¹ ≠ z := by
  intro h
  have hz0 : z ≠ 0 := root_ne_zero_of_natDegree_gt_one P hP hirr hdeg hz
  have h1 : z * z = 1 := by
    have h2 : z⁻¹ * z = z * z := congrArg (fun w => w * z) h
    rw [inv_mul_cancel₀ hz0] at h2
    exact h2.symm
  exact not_isRoot_one_or_neg_one P hP hirr hdeg hz h1

/-- The product identity produced by the pair decomposition. -/
lemma prod_pow_sub_one_eq (R : Multiset ℂ) {N : ℕ} (w : Fin N → ℂ) (k : ℕ)
    (hR : R = (Finset.univ : Finset (Fin N)).val.map w
            + (Finset.univ : Finset (Fin N)).val.map (fun j => (w j)⁻¹)) :
    (R.map (fun z => z ^ k - 1)).prod
      = (∏ j : Fin N, ((w j) ^ k - 1)) * (∏ j : Fin N, (((w j)⁻¹) ^ k - 1)) := by
  subst hR
  simp only [Multiset.map_add, Multiset.prod_add, Multiset.map_map,
    Finset.prod_eq_multiset_prod, Function.comp_apply]

/-- With the pair decomposition of an inversion-closed root multiset, the product of the norms of
the chosen representatives is the reciprocal of the Mahler measure. -/
lemma prod_norm_eq_inv_mahler (P : Polynomial ℤ) (hP : P.Monic) {N : ℕ} {w : Fin N → ℂ}
    (hw1 : ∀ j, ‖w j‖ ≤ 1) (hw0 : ∀ j, w j ≠ 0)
    (hR : (P.map (Int.castRingHom ℂ)).roots
            = (Finset.univ : Finset (Fin N)).val.map w
              + (Finset.univ : Finset (Fin N)).val.map (fun j => (w j)⁻¹)) :
    (∏ j : Fin N, ‖w j‖)⁻¹ = (P.map (Int.castRingHom ℂ)).mahlerMeasure := by
  rw [mahlerMeasure_map_int_eq P hP, hR, Multiset.map_add, Multiset.prod_add]
  have h1 : (Multiset.map (fun z => max 1 ‖z‖)
        ((Finset.univ : Finset (Fin N)).val.map w)).prod = 1 := by
    rw [Multiset.map_map, ← Finset.prod_eq_multiset_prod]
    exact Finset.prod_eq_one fun j _ => max_eq_left (hw1 j)
  have h2 : (Multiset.map (fun z => max 1 ‖z‖)
        ((Finset.univ : Finset (Fin N)).val.map (fun j => (w j)⁻¹))).prod
      = (∏ j : Fin N, ‖w j‖)⁻¹ := by
    rw [Multiset.map_map, ← Finset.prod_eq_multiset_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Function.comp_apply, norm_inv,
      max_eq_right ((one_le_inv₀ (norm_pos_iff.mpr (hw0 j))).mpr (hw1 j))]
  rw [h1, h2, one_mul]

/-! ## Multiset bookkeeping -/

/-- A multiset with no zeroes and with `z⁻¹ ∈ R` for every `z ∈ R` is invariant under
`z ↦ z⁻¹`.  (Multiplicities matter: the multiset `{a,a,a⁻¹}` with `a ≠ a⁻¹` satisfies the
pointwise condition but is not invariant, so the hypothesis `R.Nodup` is needed.) -/
lemma multiset_map_inv_eq_self (R : Multiset ℂ) (h0 : ∀ z ∈ R, z ≠ 0) (hnodup : R.Nodup)
    (hinv : ∀ z ∈ R, z⁻¹ ∈ R) : R.map (fun z => z⁻¹) = R := by
  classical
  have hnodup_map : (R.map (fun z => z⁻¹)).Nodup :=
    hnodup.map_on (fun x hx y hy hxy => by
      have hx0 : x ≠ 0 := h0 x hx
      calc x = (x⁻¹)⁻¹ := (inv_inv x).symm
        _ = (y⁻¹)⁻¹ := by rw [hxy]
        _ = y := inv_inv y)
  refine (Multiset.Nodup.ext hnodup_map hnodup).mpr fun a => ⟨?_, ?_⟩
  · intro ha
    obtain ⟨b, hb, hba⟩ := Multiset.mem_map.mp ha
    rw [← hba]
    exact hinv b hb
  · intro ha
    exact Multiset.mem_map.mpr ⟨a⁻¹, hinv a ha, inv_inv a⟩

end Work.BW
