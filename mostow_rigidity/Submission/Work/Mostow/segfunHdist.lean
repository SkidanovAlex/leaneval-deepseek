import Mathlib
import Submission.Work.Mostow.localIsomDefs

/-!
# Area L — the explicit geodesic segment `segfun` is arclength-parametrised

`segfun p q s` is the point at distance `s` from `p` on the unit-speed geodesic from `p` to `q`,
written in the hyperboloid chart `u ↦ (u, √(1+‖u‖²))`.  Here we prove the distance identity

`hdist (segfun p q s) (segfun p q s') = |s - s'|   for  s, s' ∈ [0, hdist p q]`.

The proof is pure chart algebra.  Writing `d = hdist p q`, `c(s) = segfun p q s` equals the
chart part of the ambient chord

`V(s) = (sinh (d - s)/sinh d) • hlift p + (sinh s/sinh d) • hlift q`,

and the whole content is the two hyperbolic-addition identities

`A A' + B B' + cosh d (A B' + B A') = cosh (s - s')`,   `A² + 2 A B cosh d + B² = 1`,

for `A = sinh (d - s)/sinh d`, `B = sinh s/sinh d` (both are instances of `coshPair` below,
by `Real.sinh_sub`, `Real.cosh_sub`, `Real.cosh_sq_sub_sinh_sq`).  The second one shows that
`tpart (A • p + B • q) = A tpart p + B tpart q`, and combining the two gives
`cdist (c s) (c s') = cosh (s - s')`; applying `Real.arcosh` yields the claim.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- Non-strict Cauchy–Schwarz bound: `1 ≤ cdist p q`. -/
private lemma one_le_cdist {n : ℕ} (p q : E n) : 1 ≤ cdist p q := by
  rw [cdist]
  have h1 : inner ℝ p q ≤ ‖p‖ * ‖q‖ := real_inner_le_norm p q
  have h2 : 1 + ‖p‖ * ‖q‖ ≤ tpart p * tpart q := by
    have ha : tpart p * tpart q = Real.sqrt ((1 + ‖p‖ ^ 2) * (1 + ‖q‖ ^ 2)) := by
      rw [tpart, tpart, Real.sqrt_mul (by positivity)]
    rw [ha]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (‖p‖ - ‖q‖)]
  linarith

/-- `cosh` of the hyperbolic distance is `cdist`. -/
private lemma cosh_hdist_cdist {n : ℕ} (p q : E n) : Real.cosh (hdist p q) = cdist p q := by
  rw [hdist]
  exact Real.cosh_arcosh (one_le_cdist p q)

/-- `cdist p q = 1` forces `p = q` (equality case of Cauchy–Schwarz). -/
private lemma cdist_ne_one {n : ℕ} (p q : E n) (hpq : p ≠ q) : cdist p q ≠ 1 := by
  intro h
  have h' : tpart p * tpart q = 1 + inner ℝ p q := by rw [cdist] at h; linarith
  have hsq : (tpart p * tpart q) ^ 2 = (1 + inner ℝ p q) ^ 2 := by rw [h']
  have hp := tpart_sq p
  have hq := tpart_sq q
  have hcs : (inner ℝ p q) ^ 2 ≤ (‖p‖ * ‖q‖) ^ 2 := by
    have h0 : |inner ℝ p q| ≤ ‖p‖ * ‖q‖ := abs_real_inner_le_norm p q
    have h0' : |inner ℝ p q| ^ 2 ≤ (‖p‖ * ‖q‖) ^ 2 := by
      have := mul_self_le_mul_self (abs_nonneg _) h0
      simpa [sq] using this
    rwa [sq_abs] at h0'
  have hns : ‖p - q‖ ^ 2 = ‖p‖ ^ 2 - 2 * inner ℝ p q + ‖q‖ ^ 2 := norm_sub_sq_real p q
  have hprod : (tpart p * tpart q) ^ 2 = (tpart p) ^ 2 * (tpart q) ^ 2 := by ring
  have hkey : ‖p - q‖ ^ 2 ≤ 0 := by rw [hns]; nlinarith [hsq, hp, hq, hcs, hprod]
  have hzero : ‖p - q‖ ^ 2 = 0 := le_antisymm hkey (sq_nonneg _)
  have hnorm : ‖p - q‖ = 0 := by nlinarith [hzero, norm_nonneg (p - q)]
  exact hpq (sub_eq_zero.mp (norm_eq_zero.mp hnorm))

/-- Distinct points are at positive hyperbolic distance. -/
private lemma hdist_pos_of_ne' {n : ℕ} (p q : E n) (hpq : p ≠ q) : 0 < hdist p q := by
  have hnn : 0 ≤ hdist p q := by rw [hdist]; exact Real.arcosh_nonneg (one_le_cdist p q)
  rcases lt_or_eq_of_le hnn with h | h
  · exact h
  · exfalso
    have : cdist p q = 1 := by rw [← cosh_hdist_cdist p q, ← h, Real.cosh_zero]
    exact cdist_ne_one p q hpq this

/-- The hyperbolic-addition identity in the chart: for `A = (Sh·cs - Ch·ss)/Sh`,
`B = ss/Sh`, `A' = (Sh·cs' - Ch·ss')/Sh`, `B' = ss'/Sh` with `Ch² - Sh² = 1`, `Sh ≠ 0`,
one has `A A' + B B' + Ch (A B' + B A') = cs cs' - ss ss'`. -/
private lemma coshPair (Sh Ch cs ss cs' ss' : ℝ) (hS : Sh ≠ 0) (h1 : Ch ^ 2 - Sh ^ 2 = 1) :
    ((Sh * cs - Ch * ss) / Sh) * ((Sh * cs' - Ch * ss') / Sh) + (ss / Sh) * (ss' / Sh) +
      Ch * (((Sh * cs - Ch * ss) / Sh) * (ss' / Sh) + (ss / Sh) * ((Sh * cs' - Ch * ss') / Sh))
      = cs * cs' - ss * ss' := by
  field_simp
  linear_combination (-(ss * ss')) * h1

/-- The time coordinate of the chord `A • p + B • q` in the hyperboloid chart, for `A, B ≥ 0`
and with the Minkowski self-pairing normalised to `-1`. -/
private lemma tpart_lincomb {n : ℕ} (p q : E n) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAB : A ^ 2 + 2 * A * B * (tpart p * tpart q - inner ℝ p q) + B ^ 2 = 1) :
    tpart (A • p + B • q) = A * tpart p + B * tpart q := by
  have hnorm : ‖A • p + B • q‖ ^ 2 = A^2 * ‖p‖^2 + 2*(A*B)*inner ℝ p q + B^2*‖q‖^2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      real_inner_smul_left, real_inner_smul_right]
    rw [mul_pow, mul_pow, sq_abs, sq_abs]
    ring
  have hsp := tpart_sq p
  have hsq := tpart_sq q
  have hkey : tpart (A • p + B • q)^2 = (A * tpart p + B * tpart q)^2 := by
    rw [tpart_sq, hnorm]
    nlinarith [hsp, hsq, hAB]
  have hnn : 0 ≤ A * tpart p + B * tpart q :=
    add_nonneg (mul_nonneg hA (le_of_lt (tpart_pos p))) (mul_nonneg hB (le_of_lt (tpart_pos q)))
  calc tpart (A • p + B • q)
      = Real.sqrt ((tpart (A • p + B • q))^2) := (Real.sqrt_sq (le_of_lt (tpart_pos _))).symm
    _ = Real.sqrt ((A * tpart p + B * tpart q)^2) := by rw [hkey]
    _ = A * tpart p + B * tpart q := Real.sqrt_sq hnn

/-- `cdist` of two chart chords, expanded into the four Minkowski pairings. -/
private lemma cdist_lincomb {n : ℕ} (p q : E n) (A B A' B' : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hA' : 0 ≤ A') (hB' : 0 ≤ B')
    (hAB : A^2 + 2*A*B*(tpart p*tpart q - inner ℝ p q) + B^2 = 1)
    (hAB' : A'^2 + 2*A'*B'*(tpart p*tpart q - inner ℝ p q) + B'^2 = 1) :
    cdist (A•p+B•q) (A'•p+B'•q) =
      A*A' + B*B' + (tpart p*tpart q - inner ℝ p q)*(A*B' + B*A') := by
  rw [cdist, tpart_lincomb p q A B hA hB hAB, tpart_lincomb p q A' B' hA' hB' hAB']
  have hinner : inner ℝ (A•p+B•q) (A'•p+B'•q) =
      A*A'*‖p‖^2 + A*B'*inner ℝ p q + B*A'*inner ℝ q p + B*B'*‖q‖^2 := by
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    ring
  rw [hinner]
  have hp : ‖p‖^2 = tpart p^2 - 1 := by have := tpart_sq p; linarith
  have hq : ‖q‖^2 = tpart q^2 - 1 := by have := tpart_sq q; linarith
  have hqp : inner ℝ q p = inner ℝ p q := real_inner_comm p q
  rw [hp, hq, hqp]
  ring

/-- Core computation: `cdist (segfun p q s) (segfun p q s') = cosh (s - s')` on the segment. -/
private lemma cdist_segfun {n : ℕ} (p q : E n) (hpq : p ≠ q) (s s' : ℝ)
    (hs : s ∈ Set.Icc 0 (hdist p q)) (hs' : s' ∈ Set.Icc 0 (hdist p q)) :
    cdist (segfun p q s) (segfun p q s') = Real.cosh (s - s') := by
  have hs0 : 0 ≤ s := hs.1
  have hshd : s ≤ hdist p q := hs.2
  have hs'0 : 0 ≤ s' := hs'.1
  have hs'hd : s' ≤ hdist p q := hs'.2
  have hC : Real.cosh (hdist p q) = cdist p q := cosh_hdist_cdist p q
  have hCd : tpart p * tpart q - inner ℝ p q = Real.cosh (hdist p q) := hC.symm
  have hSh_pos : 0 < Real.sinh (hdist p q) := Real.sinh_pos_iff.mpr (hdist_pos_of_ne' p q hpq)
  have hSh_ne : Real.sinh (hdist p q) ≠ 0 := ne_of_gt hSh_pos
  set A := Real.sinh (hdist p q - s) / Real.sinh (hdist p q) with hAdef
  set B := Real.sinh s / Real.sinh (hdist p q) with hBdef
  set A' := Real.sinh (hdist p q - s') / Real.sinh (hdist p q) with hA'def
  set B' := Real.sinh s' / Real.sinh (hdist p q) with hB'def
  have hA_nn : 0 ≤ A := by
    rw [hAdef]; apply div_nonneg
    · exact Real.sinh_nonneg_iff.mpr (by linarith [hshd])
    · exact le_of_lt hSh_pos
  have hB_nn : 0 ≤ B := by
    rw [hBdef]; apply div_nonneg
    · exact Real.sinh_nonneg_iff.mpr hs0
    · exact le_of_lt hSh_pos
  have hA'_nn : 0 ≤ A' := by
    rw [hA'def]; apply div_nonneg
    · exact Real.sinh_nonneg_iff.mpr (by linarith [hs'hd])
    · exact le_of_lt hSh_pos
  have hB'_nn : 0 ≤ B' := by
    rw [hB'def]; apply div_nonneg
    · exact Real.sinh_nonneg_iff.mpr hs'0
    · exact le_of_lt hSh_pos
  have hcs : Real.cosh s * Real.cosh s - Real.sinh s * Real.sinh s = 1 := by
    have := Real.cosh_sq_sub_sinh_sq s; nlinarith
  have hcs' : Real.cosh s' * Real.cosh s' - Real.sinh s' * Real.sinh s' = 1 := by
    have := Real.cosh_sq_sub_sinh_sq s'; nlinarith
  have hAB : A^2 + 2*A*B*(tpart p*tpart q - inner ℝ p q) + B^2 = 1 := by
    have key := coshPair (Real.sinh (hdist p q)) (Real.cosh (hdist p q))
      (Real.cosh s) (Real.sinh s) (Real.cosh s) (Real.sinh s) hSh_ne
      (Real.cosh_sq_sub_sinh_sq (hdist p q))
    rw [hcs] at key
    rw [hAdef, hBdef, Real.sinh_sub, hCd]
    linear_combination key
  have hAB' : A'^2 + 2*A'*B'*(tpart p*tpart q - inner ℝ p q) + B'^2 = 1 := by
    have key := coshPair (Real.sinh (hdist p q)) (Real.cosh (hdist p q))
      (Real.cosh s') (Real.sinh s') (Real.cosh s') (Real.sinh s') hSh_ne
      (Real.cosh_sq_sub_sinh_sq (hdist p q))
    rw [hcs'] at key
    rw [hA'def, hB'def, Real.sinh_sub, hCd]
    linear_combination key
  have hseg_s : segfun p q s = A • p + B • q := by rw [segfun, ← hAdef, ← hBdef]
  have hseg_s' : segfun p q s' = A' • p + B' • q := by rw [segfun, ← hA'def, ← hB'def]
  have hmain := cdist_lincomb p q A B A' B' hA_nn hB_nn hA'_nn hB'_nn hAB hAB'
  rw [hseg_s, hseg_s', hmain]
  have key := coshPair (Real.sinh (hdist p q)) (Real.cosh (hdist p q))
    (Real.cosh s) (Real.sinh s) (Real.cosh s') (Real.sinh s') hSh_ne
    (Real.cosh_sq_sub_sinh_sq (hdist p q))
  rw [hCd, hAdef, hBdef, hA'def, hB'def, Real.sinh_sub, Real.sinh_sub, Real.cosh_sub]
  exact key

/-- The explicit geodesic segment is arclength-parametrised: on `[0, hdist p q]` the
hyperbolic distance between `segfun p q s` and `segfun p q s'` is `|s - s'|`. -/
theorem segfunHdist {n : ℕ} (p q : E n) (hpq : p ≠ q) (s s' : ℝ)
    (hs : s ∈ Set.Icc 0 (hdist p q)) (hs' : s' ∈ Set.Icc 0 (hdist p q)) :
    hdist (segfun p q s) (segfun p q s') = |s - s'| := by
  have h := cdist_segfun p q hpq s s' hs hs'
  have hd : hdist (segfun p q s) (segfun p q s') =
      Real.arcosh (cdist (segfun p q s) (segfun p q s')) := rfl
  rw [hd, h, ← Real.cosh_abs]
  exact Real.arcosh_cosh (abs_nonneg _)

end

end Work.Mostow
