import Submission.ChebSerre
import Submission.DivLinear
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Adjusted (pruned) Chebyshev polynomials for the Serre interval

Single-interval instance of Smith's `lem:adjusted_Cheb` (adjust.tex): for
every `r ≥ 2` there is a real monic degree-`r` polynomial `T̃` (a *prune* of
the monic Chebyshev `T_{r+3}`: the product over the `r` interior roots) and a
sequence `y_0 > y_1 > … > y_r` of points of `[aSerre,bSerre]` (the extremal
points `extPoint (r+3) (k+1)`, `k = 0..r`) with all roots of `T̃` inside the
interval, sup-norm ≤ `(r+3)^6 κ^r`, alternating values ≥ `κ^r / 32`, and one
root between consecutive brackets.
-/

noncomputable section

open scoped Real
open Polynomial

namespace Submission.AdjustedCheb

open Submission.SerreExample
open Submission.ChebSerre
open Submission.DivLinear

set_option maxHeartbeats 800000

/-- The pruned polynomial: interior roots of `chebT (r+3)` kept
(`rootPoint (r+3) k` for `k.val+1 = 1..r`). -/
noncomputable def prunedPoly (r : ℕ) : Polynomial ℝ :=
  ∏ k : Fin r, (Polynomial.X - Polynomial.C (rootPoint (r + 3) (k.val + 1)))

/-- The bracket endpoints: `y i = extPoint (r+3) (i.val+1)`, decreasing. -/
noncomputable def bracketPoint (r : ℕ) (i : Fin (r + 1)) : ℝ :=
  extPoint (r + 3) (i.val + 1)

/-- The cubic of the three dropped roots (indices `0`, `r+1`, `r+2`). -/
noncomputable def droppedCubic (r : ℕ) : Polynomial ℝ :=
  (Polynomial.X - Polynomial.C (rootPoint (r + 3) 0)) *
    ((Polynomial.X - Polynomial.C (rootPoint (r + 3) (r + 1))) *
    (Polynomial.X - Polynomial.C (rootPoint (r + 3) (r + 2))))

/-! ## Basic facts about the interval, kappa, and Chebyshev points -/

lemma kappaC_pos : 0 < kappaC := by
  have h := kappaC_gt_one
  linarith

lemma kappaC_ne : kappaC ≠ 0 := ne_of_gt kappaC_pos

lemma bSerre_sub_aSerre_eq : bSerre - aSerre = 4 * kappaC := by
  unfold kappaC
  ring

lemma chebPoint_sub (u v : ℝ) : chebPoint u - chebPoint v = ((bSerre - aSerre) / 2) * (u - v) := by
  unfold chebPoint
  ring

lemma chebPoint_le_b {t : ℝ} (ht : t ≤ 1) : chebPoint t ≤ bSerre := by
  unfold chebPoint
  have hb : 0 ≤ (bSerre - aSerre) / 2 := by
    exact div_nonneg (le_of_lt (sub_pos.mpr a_lt_b)) (by norm_num)
  have hh : (bSerre - aSerre)/2 * t ≤ (bSerre - aSerre)/2 * 1 := mul_le_mul_of_nonneg_left ht hb
  nlinarith

lemma a_le_chebPoint {t : ℝ} (ht : -1 ≤ t) : aSerre ≤ chebPoint t := by
  unfold chebPoint
  have hb : 0 ≤ (bSerre - aSerre) / 2 := by
    exact div_nonneg (le_of_lt (sub_pos.mpr a_lt_b)) (by norm_num)
  have hh : (bSerre - aSerre)/2 * (-1) ≤ (bSerre - aSerre)/2 * t := mul_le_mul_of_nonneg_left ht hb
  nlinarith

/-- `extPoint N k` lies in the closed Serre interval (no bound on `k` needed). -/
lemma extPoint_mem_Icc (N k : ℕ) : extPoint N k ∈ Set.Icc aSerre bSerre := by
  unfold extPoint
  have hcos : Real.cos (extAngle N k) ∈ Set.Icc (-1) 1 := Real.cos_mem_Icc _
  exact ⟨a_le_chebPoint hcos.1, chebPoint_le_b hcos.2⟩

lemma rootPoint_mem_Icc {N k : ℕ} (hk : k < N) : rootPoint N k ∈ Set.Icc aSerre bSerre := by
  have hIoo := rootPoint_mem_Ioo (N := N) (k := k) (by omega) hk
  exact ⟨le_of_lt hIoo.1, le_of_lt hIoo.2⟩

lemma bracketPoint_mem_Icc (r : ℕ) (i : Fin (r + 1)) : bracketPoint r i ∈ Set.Icc aSerre bSerre := by
  unfold bracketPoint
  exact extPoint_mem_Icc (r + 3) (i.val + 1)

/-! ## Monicity, degrees, and the factorization `chebT (r+3) = droppedCubic · prunedPoly` -/

lemma prunedPoly_monic (r : ℕ) : (prunedPoly r).Monic := by
  unfold prunedPoly
  apply Polynomial.monic_prod_of_monic
  intro k hk
  exact monic_X_sub_C (rootPoint (r+3) (k.val+1))

lemma prunedPoly_natDegree (r : ℕ) : (prunedPoly r).natDegree = r := by
  unfold prunedPoly
  rw [Polynomial.natDegree_prod_of_monic]
  · simp
  · intro k hk
    exact monic_X_sub_C (rootPoint (r+3) (k.val+1))

lemma droppedCubic_monic (r : ℕ) : (droppedCubic r).Monic := by
  unfold droppedCubic
  exact Monic.mul (monic_X_sub_C _) (Monic.mul (monic_X_sub_C _) (monic_X_sub_C _))

lemma droppedCubic_natDegree (r : ℕ) : (droppedCubic r).natDegree = 3 := by
  unfold droppedCubic
  rw [Monic.natDegree_mul (monic_X_sub_C _) (Monic.mul (monic_X_sub_C _) (monic_X_sub_C _))]
  rw [Monic.natDegree_mul (monic_X_sub_C _) (monic_X_sub_C _)]
  simp

lemma droppedCubic_ne_zero (r : ℕ) : droppedCubic r ≠ 0 := (droppedCubic_monic r).ne_zero

/-- `droppedCubic` vanishes at each of the three dropped roots. -/
lemma cubic_eval_zero_at_dropped (r : ℕ) {d : ℕ} (hd : d = 0 ∨ d = r + 1 ∨ d = r + 2) :
    (droppedCubic r).eval (rootPoint (r + 3) d) = 0 := by
  unfold droppedCubic
  rw [eval_mul, eval_mul]
  rcases hd with hd0 | hd1 | hd2
  · have ha : (Polynomial.X - Polynomial.C (rootPoint (r+3) 0) : Polynomial ℝ).eval (rootPoint (r+3) d) = 0 := by
      simp [hd0]
    simp [ha]
  · have hb : (Polynomial.X - Polynomial.C (rootPoint (r+3) (r+1)) : Polynomial ℝ).eval (rootPoint (r+3) d) = 0 := by
      simp [hd1]
    simp [hb]
  · have hc : (Polynomial.X - Polynomial.C (rootPoint (r+3) (r+2)) : Polynomial ℝ).eval (rootPoint (r+3) d) = 0 := by
      simp [hd2]
    simp [hc]

/-- `prunedPoly` vanishes at each kept root `rootPoint (r+3) d`, `1 ≤ d ≤ r`. -/
lemma pruned_eval_zero_at_kept (r : ℕ) {d : ℕ} (hd1 : 1 ≤ d) (hdr : d ≤ r) :
    (prunedPoly r).eval (rootPoint (r + 3) d) = 0 := by
  let j : Fin r := ⟨d - 1, by omega⟩
  have hj : j.val + 1 = d := by
    dsimp [j]
    omega
  have hfac : (Polynomial.X - Polynomial.C (rootPoint (r+3) (j.val + 1)) : Polynomial ℝ).eval (rootPoint (r+3) d) = 0 := by
    rw [eval_sub, eval_X, eval_C, hj, sub_self]
  unfold prunedPoly
  rw [eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ j) hfac

/-- difference of two monic polynomials of equal degree has smaller degree -/
lemma natDegree_sub_lt_of_eq {f g : Polynomial ℝ} {n : ℕ}
    (hf : f.Monic) (hg : g.Monic) (hdegf : f.natDegree = n) (hdegg : g.natDegree = n)
    (hne : f ≠ g) : (f - g).natDegree < n := by
  have hle : (f - g).natDegree ≤ n := by
    rw [natDegree_sub_le_iff_left hdegg.le]
    exact hdegf.le
  have hzero : (f - g).coeff n = 0 := by
    rw [coeff_sub]
    have hcf : f.coeff n = 1 := by
      rw [← hdegf, coeff_natDegree, hf.leadingCoeff]
    have hcg : g.coeff n = 1 := by
      rw [← hdegg, coeff_natDegree, hg.leadingCoeff]
    rw [hcf, hcg, sub_self]
  have hne' : f - g ≠ 0 := sub_ne_zero.mpr hne
  by_contra hnot
  have hdegne : (f - g).natDegree ≠ n := by
    intro hdeg
    have hc : (f - g).coeff (f - g).natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact (leadingCoeff_ne_zero.mpr hne')
    rw [hdeg] at hc
    exact hc hzero
  have hle' : (f - g).natDegree = n := le_antisymm hle (le_of_not_gt hnot)
  exact hdegne hle'

/-- the root points of a fixed degree are pairwise distinct -/
lemma rootPoint_injective {N : ℕ} (hN : 1 ≤ N) : Function.Injective (fun k : Fin N => rootPoint N k.val) := by
  intro k l h
  have hroot : rootPoint N k.val = rootPoint N l.val := by simpa using h
  by_contra hne
  have hvne : k.val ≠ l.val := fun hv => hne (Fin.ext hv)
  rcases lt_or_gt_of_ne hvne with hkl | hlk
  · have hlt : rootPoint N l.val < rootPoint N k.val := rootPoint_antitone hN l.isLt hkl
    exact (ne_of_lt hlt hroot.symm)
  · have hlt : rootPoint N k.val < rootPoint N l.val := rootPoint_antitone hN k.isLt hlk
    exact (ne_of_lt hlt hroot)

/-- Main factorization: `chebT (r+3) = droppedCubic r * prunedPoly r`. -/
lemma chebT_eq_dropped_mul_pruned (r : ℕ) (hr : 2 ≤ r) :
    chebT (r + 3) = droppedCubic r * prunedPoly r := by
  let N : ℕ := r + 3
  have hN : 1 ≤ N := by omega
  let P : Polynomial ℝ := droppedCubic r * prunedPoly r
  let D : Polynomial ℝ := chebT N - P
  have hPmonic : P.Monic := (droppedCubic_monic r).mul (prunedPoly_monic r)
  have hdegP : P.natDegree = N := by
    dsimp [P]
    rw [Monic.natDegree_mul (droppedCubic_monic r) (prunedPoly_monic r)]
    rw [droppedCubic_natDegree r, prunedPoly_natDegree r]
    dsimp [N]
    omega
  have hDzero : D = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero (p := D) (ι := Fin N)
      (f := fun k : Fin N => rootPoint N k.val) (hf := rootPoint_injective hN)
    · intro k
      dsimp [D, P]
      rw [eval_sub, eval_mul]
      have hT : (chebT N).eval (rootPoint N k.val) = 0 :=
        chebT_eval_rootPoint N k.val hN k.isLt
      rw [hT, zero_sub]
      have h1 : (droppedCubic r).eval (rootPoint N k.val) = 0 ∨ (prunedPoly r).eval (rootPoint N k.val) = 0 := by
        by_cases hdrop : k.val = 0 ∨ k.val = r + 1 ∨ k.val = r + 2
        · left
          dsimp [N] at hdrop
          exact cubic_eval_zero_at_dropped r hdrop
        · right
          have hkept : 1 ≤ k.val ∧ k.val ≤ r := by
            have hlt : k.val < N := k.isLt
            dsimp [N] at hlt
            omega
          dsimp [N]
          exact pruned_eval_zero_at_kept r hkept.1 hkept.2
      rcases h1 with hC | hT
      · rw [hC]; simp
      · rw [hT]; simp
    · by_cases hne : chebT N ≠ P
      · have hdegT : (chebT N).natDegree = N := by dsimp [N]; exact chebT_natDegree (r+3) (by omega)
        have hmonT : (chebT N).Monic := by dsimp [N]; exact chebT_monic (r+3) (by omega)
        have hlt := natDegree_sub_lt_of_eq hmonT hPmonic hdegT hdegP hne
        simpa using hlt
      · have hP : P = chebT N := (not_ne_iff.mp hne).symm
        simp [D, hP]
        omega
  have hmain : chebT N = P := sub_eq_zero.mp hDzero
  change chebT (r + 3) = droppedCubic r * prunedPoly r
  simpa [P, N] using hmain

/-- `chebT (r+3)` vanishes at the three dropped roots. -/
lemma chebT_eval_zero_dropped (r : ℕ) {d : ℕ} (hd : d = 0 ∨ d = r + 1 ∨ d = r + 2) :
    (chebT (r + 3)).eval (rootPoint (r + 3) d) = 0 := by
  have hlt : d < r + 3 := by rcases hd with h0 | h1 | h2 <;> omega
  exact chebT_eval_rootPoint (r + 3) d (by omega) hlt

/-! ## Derivative (Markov) bound and Lipschitz estimates -/

/-- derivative bound for `chebT (r+3)` on the whole interval -/
lemma chebT_deriv_bound (r : ℕ) (x : ℝ) (hx : x ∈ Set.Icc aSerre bSerre) :
    |(chebT (r + 3)).derivative.eval x| ≤ (r + 3) ^ 2 * kappaC ^ (r + 2) := by
  have hN : 1 ≤ r + 3 := by omega
  have hdeg : (chebT (r+3)).natDegree ≤ r + 3 := (chebT_natDegree (r+3) hN).le
  have hM0 : 0 ≤ 2 * kappaC ^ (r + 3) := by
    exact mul_nonneg (by norm_num) (pow_nonneg (le_of_lt kappaC_pos) _)
  have hbd : ∀ y : ℝ, y ∈ Set.Icc aSerre bSerre → |(chebT (r+3)).eval y| ≤ 2 * kappaC ^ (r + 3) := by
    intro y hy
    exact chebT_bound (r+3) hN hy
  have hmain := Submission.MarkovInterval.markov_interval (P := chebT (r+3)) (n := r + 3) hdeg hM0 hbd x hx
  calc
    |(chebT (r+3)).derivative.eval x|
        ≤ (2 * (r + 3 : ℝ) ^ 2 / (bSerre - aSerre)) * (2 * kappaC ^ (r+3)) := by
          simpa using hmain
    _ = (r + 3 : ℝ) ^ 2 * kappaC ^ (r + 2) := by
      rw [bSerre_sub_aSerre_eq]
      field_simp [kappaC_ne]
      ring_nf

/-- Lipschitz bound: if `|P'| ≤ C` on the interval then
`|P.eval x - P.eval y| ≤ C * |x - y|`. -/
lemma poly_lipschitz {P : Polynomial ℝ} {x y : ℝ} {C : ℝ}
    (hxyx : x ∈ Set.Icc aSerre bSerre) (hxyy : y ∈ Set.Icc aSerre bSerre)
    (hC : ∀ z : ℝ, z ∈ Set.Icc aSerre bSerre → |P.derivative.eval z| ≤ C) :
    |P.eval x - P.eval y| ≤ C * |x - y| := by
  let f : ℝ → ℝ := fun z => P.eval z
  have hdiff : ∀ z ∈ Set.Icc aSerre bSerre, DifferentiableAt ℝ f z := by
    intro z hz
    dsimp [f]
    exact (Polynomial.hasDerivAt P z).differentiableAt
  have hbound : ∀ z ∈ Set.Icc aSerre bSerre, ‖deriv f z‖ ≤ C := by
    intro z hz
    dsimp [f]
    rw [Polynomial.deriv]
    have hz' : |P.derivative.eval z| ≤ C := hC z hz
    simpa [Real.norm_eq_abs] using hz'
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (G := ℝ) (f := f)
    (s := Set.Icc aSerre bSerre) (x := x) (y := y) (C := C) hdiff hbound
    (convex_Icc aSerre bSerre) hxyx hxyy
  dsimp [f] at hmain
  simpa [Real.norm_eq_abs, abs_sub_comm] using hmain

/-- Markov-type anchored bound: for a dropped root ρ and any x in the interval,
`|chebT(x)| ≤ (r+3)² · κ^{r+2} · |x−ρ|`. -/
lemma chebT_anchor_bound (r : ℕ) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) {d : ℕ}
    (hd : d = 0 ∨ d = r + 1 ∨ d = r + 2) :
    |(chebT (r + 3)).eval x| ≤ (r + 3) ^ 2 * kappaC ^ (r + 2) * |x - rootPoint (r + 3) d| := by
  let ρ : ℝ := rootPoint (r + 3) d
  have hρ : ρ ∈ Set.Icc aSerre bSerre := by
    dsimp [ρ]
    have hlt : d < r + 3 := by rcases hd with h0 | h1 | h2 <;> omega
    exact rootPoint_mem_Icc hlt
  have hC : ∀ z : ℝ, z ∈ Set.Icc aSerre bSerre →
      |(chebT (r+3)).derivative.eval z| ≤ (r + 3) ^ 2 * kappaC ^ (r + 2) := by
    intro z hz
    exact chebT_deriv_bound r z hz
  have hlp := poly_lipschitz (P := chebT (r+3)) (x := x) (y := ρ) (C := (r+3)^2 * kappaC^(r+2)) hx hρ hC
  have hroot : (chebT (r+3)).eval ρ = 0 := by
    dsimp [ρ]
    exact chebT_eval_zero_dropped r hd
  have hdiff : |(chebT (r+3)).eval x - (chebT (r+3)).eval ρ| = |(chebT (r+3)).eval x| := by
    rw [hroot, sub_zero]
  rw [hdiff] at hlp
  simpa [ρ] using hlp


/-! ## Trigonometric and geometric distance lemmas among the dropped roots -/

/-- `cos(π/2N) − cos(3π/2N) ≥ 4/N²` for N ≥ 2. -/
lemma cos_diff_ge {N : ℕ} (hN : 2 ≤ N) :
    (4 : ℝ) / (N : ℝ) ^ 2 ≤
      Real.cos (Real.pi / (2 * (N : ℝ))) - Real.cos ((3 : ℝ) * Real.pi / (2 * (N : ℝ))) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h1 : 1 ≤ N := by omega
    exact_mod_cast h1
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have h2Nne : (2 * (N : ℝ)) ≠ 0 := mul_ne_zero (by norm_num) hNne
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h1 : Real.cos (Real.pi / (2 * (N : ℝ))) - Real.cos ((3 : ℝ) * Real.pi / (2 * (N : ℝ)))
      = 2 * Real.sin (Real.pi / (N : ℝ)) * Real.sin (Real.pi / (2 * (N : ℝ))) := by
    rw [Real.cos_sub_cos]
    have hx : (Real.pi / (2 * (N : ℝ)) + 3 * Real.pi / (2 * (N : ℝ))) / 2 = Real.pi / (N : ℝ) := by
      ring_nf
    have hy : (Real.pi / (2 * (N : ℝ)) - 3 * Real.pi / (2 * (N : ℝ))) / 2 = -(Real.pi / (2 * (N : ℝ))) := by
      ring_nf
    rw [hx, hy, Real.sin_neg]
    ring
  rw [h1]
  have h0a : 0 ≤ Real.pi / (N : ℝ) := by positivity
  have hlea : Real.pi / (N : ℝ) ≤ Real.pi / 2 := by
    rw [div_le_iff₀ hNpos]
    nlinarith [Real.pi_pos, hN2]
  have hms1 := Real.mul_le_sin (x := Real.pi / (N : ℝ)) h0a hlea
  have hs1 : (2 / (N : ℝ)) ≤ Real.sin (Real.pi / (N : ℝ)) := by
    have hred : (2 / Real.pi) * (Real.pi / (N : ℝ)) = 2 / (N : ℝ) := by
      field_simp [Real.pi_ne_zero, hNne]
    rwa [← hred]
  have h0b : 0 ≤ Real.pi / (2 * (N : ℝ)) := by positivity
  have hleb : Real.pi / (2 * (N : ℝ)) ≤ Real.pi / 2 := by
    rw [div_le_iff₀ (by positivity : 0 < (2 * (N : ℝ)))]
    nlinarith [Real.pi_pos, hN2]
  have hms2 := Real.mul_le_sin (x := Real.pi / (2 * (N : ℝ))) h0b hleb
  have hs2 : (1 / (N : ℝ)) ≤ Real.sin (Real.pi / (2 * (N : ℝ))) := by
    have hred : (2 / Real.pi) * (Real.pi / (2 * (N : ℝ))) = 1 / (N : ℝ) := by
      field_simp [Real.pi_ne_zero, hNne, h2Nne]
    rwa [← hred]
  have hsin1nn : 0 ≤ Real.sin (Real.pi / (N : ℝ)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0a (by linarith [hlea, Real.pi_pos])
  have hsin2nn : 0 ≤ Real.sin (Real.pi / (2 * (N : ℝ))) :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0b (by linarith [hleb, Real.pi_pos])
  have hn1 : 0 ≤ (2 / (N : ℝ)) := by positivity
  have hn2 : 0 ≤ (1 / (N : ℝ)) := by positivity
  have hmul := mul_le_mul hs1 hs2 hn2 hsin1nn
  have hmul2 := mul_le_mul_of_nonneg_left hmul (by norm_num : 0 ≤ (2 : ℝ))
  rw [mul_assoc]
  rwa [show 2 * ((2 / (N : ℝ)) * (1 / (N : ℝ))) = (4 : ℝ) / (N : ℝ) ^ 2 by ring_nf] at hmul2

/-- angle of the (r+1)-st root of `chebT (r+3)`. -/
lemma rootAngle_dropped_one (r : ℕ) : rootAngle (r + 3) (r + 1) =
    Real.pi - (3 * Real.pi) / (2 * ((r + 3 : ℕ) : ℝ)) := by
  unfold rootAngle
  push_cast
  field_simp
  ring

/-- angle of the (r+2)-nd root of `chebT (r+3)`. -/
lemma rootAngle_dropped_two (r : ℕ) : rootAngle (r + 3) (r + 2) =
    Real.pi - Real.pi / (2 * ((r + 3 : ℕ) : ℝ)) := by
  unfold rootAngle
  push_cast
  field_simp
  ring

/-- angle of the 0-th root of `chebT (r+3)`. -/
lemma rootAngle_zero (r : ℕ) : rootAngle (r + 3) 0 = Real.pi / (2 * ((r + 3 : ℕ) : ℝ)) := by
  unfold rootAngle
  norm_num

/-- u-coordinate difference of the two leftmost dropped roots -/
lemma cos_rho1_sub_cos_rho2 (r : ℕ) :
    Real.cos (rootAngle (r + 3) (r + 1)) - Real.cos (rootAngle (r + 3) (r + 2)) =
      Real.cos (Real.pi / (2 * ((r + 3 : ℕ) : ℝ))) - Real.cos (3 * Real.pi / (2 * ((r + 3 : ℕ) : ℝ))) := by
  rw [rootAngle_dropped_one, rootAngle_dropped_two, Real.cos_pi_sub, Real.cos_pi_sub]
  ring

/-- lower bound on the gap ρ_{r+1} − ρ_{r+2}. -/
lemma dropped_distance_ge (r : ℕ) (hr : 2 ≤ r) :
    (8 * kappaC) / (r + 3 : ℝ) ^ 2 ≤ rootPoint (r + 3) (r + 1) - rootPoint (r + 3) (r + 2) := by
  have hN : 2 ≤ r + 3 := by omega
  have hd4 : (4 : ℝ) / (r + 3 : ℝ) ^ 2 ≤
      Real.cos (Real.pi / (2 * ((r + 3 : ℕ) : ℝ))) - Real.cos (3 * Real.pi / (2 * ((r + 3 : ℕ) : ℝ))) := by
    simpa using (cos_diff_ge (N := r + 3) hN)
  have hu : (4 : ℝ) / (r + 3 : ℝ) ^ 2 ≤
      Real.cos (rootAngle (r+3) (r+1)) - Real.cos (rootAngle (r+3) (r+2)) := by
    rw [cos_rho1_sub_cos_rho2]
    exact hd4
  have hρ : rootPoint (r+3) (r+1) - rootPoint (r+3) (r+2)
      = (2 * kappaC) * (Real.cos (rootAngle (r+3) (r+1)) - Real.cos (rootAngle (r+3) (r+2))) := by
    unfold rootPoint
    rw [chebPoint_sub]
    rw [bSerre_sub_aSerre_eq]
    ring
  rw [hρ]
  have hk : 0 ≤ 2 * kappaC := mul_nonneg (by norm_num) (le_of_lt kappaC_pos)
  have hm := mul_le_mul_of_nonneg_left hu hk
  have htarget : (8 * kappaC) / (r + 3 : ℝ) ^ 2 = (2 * kappaC) * ((4 : ℝ) / (r + 3 : ℝ) ^ 2) := by
    ring_nf
  rwa [htarget]

/-- gap ρ0 − ρ1 is at least the gap ρ1 − ρ2 (both in x-coordinates). -/
lemma dropped_gap01_ge_gap12 (r : ℕ) (hr : 2 ≤ r) :
    rootPoint (r + 3) 0 - rootPoint (r + 3) (r + 1) ≥
      rootPoint (r + 3) (r + 1) - rootPoint (r + 3) (r + 2) := by
  have hcos0 : Real.cos (rootAngle (r+3) 0) = Real.cos (Real.pi / (2 * ((r+3 : ℕ) : ℝ))) := by
    rw [rootAngle_zero]
  have hu0 : Real.cos (rootAngle (r+3) 0) - Real.cos (rootAngle (r+3) (r+1))
      ≥ Real.cos (rootAngle (r+3) (r+1)) - Real.cos (rootAngle (r+3) (r+2)) := by
    rw [rootAngle_dropped_one, rootAngle_dropped_two, Real.cos_pi_sub, Real.cos_pi_sub, hcos0]
    have hc : 0 ≤ Real.cos (3 * Real.pi / (2 * ((r+3 : ℕ) : ℝ))) := by
      apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      · have hp : 0 ≤ 3 * Real.pi / (2 * ((r+3:ℕ):ℝ)) := by positivity
        linarith [Real.pi_pos, hp]
      · rw [div_le_iff₀ (by positivity : 0 < 2 * ((r+3:ℕ):ℝ))]
        have hc2 : (3 : ℝ) ≤ ((r+3 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ r + 3)
        have hm := mul_le_mul_of_nonneg_right hc2 (le_of_lt Real.pi_pos)
        ring_nf
        simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hm
    nlinarith
  have hρ0 : rootPoint (r+3) 0 - rootPoint (r+3) (r+1) =
      (2 * kappaC) * (Real.cos (rootAngle (r+3) 0) - Real.cos (rootAngle (r+3) (r+1))) := by
    unfold rootPoint
    rw [chebPoint_sub, bSerre_sub_aSerre_eq]
    ring
  have hρ1 : rootPoint (r+3) (r+1) - rootPoint (r+3) (r+2) =
      (2 * kappaC) * (Real.cos (rootAngle (r+3) (r+1)) - Real.cos (rootAngle (r+3) (r+2))) := by
    unfold rootPoint
    rw [chebPoint_sub, bSerre_sub_aSerre_eq]
    ring
  rw [hρ0, hρ1]
  exact mul_le_mul_of_nonneg_left hu0 (by
    exact mul_nonneg (by norm_num) (le_of_lt kappaC_pos))

/-- the two gaps between consecutive dropped roots are positive and the second
is at least the first. -/
lemma dropped_roots_gaps (r : ℕ) (hr : 2 ≤ r) :
    0 < rootPoint (r+3) (r+1) - rootPoint (r+3) (r+2) ∧
    0 ≤ rootPoint (r+3) 0 - rootPoint (r+3) (r+1) := by
  have hN : 1 ≤ r + 3 := by omega
  constructor
  · have hlt : rootPoint (r+3) (r+2) < rootPoint (r+3) (r+1) := by
      exact rootPoint_antitone hN (by omega : r + 2 < r + 3) (by omega : r + 1 < r + 2)
    linarith
  · have hlt : rootPoint (r+3) (r+1) < rootPoint (r+3) 0 := by
      exact rootPoint_antitone hN (by omega : r + 1 < r + 3) (by omega : 0 < r + 1)
    linarith

/-! ## Auxiliary derivative facts -/

lemma deriv_eval_mul (f g : Polynomial ℝ) (x : ℝ) (hfx : f.eval x = 0) :
    (f * g).derivative.eval x = f.derivative.eval x * g.eval x := by
  rw [derivative_mul, eval_add, eval_mul, eval_mul]
  rw [hfx]
  simp

/-- closed formula for the derivative of the dropped cubic -/
lemma deriv_cubic_eval (r : ℕ) (x : ℝ) :
    (droppedCubic r).derivative.eval x =
      (x - rootPoint (r+3) (r+1)) * (x - rootPoint (r+3) (r+2)) +
        (x - rootPoint (r+3) 0) * ((x - rootPoint (r+3) (r+2)) + (x - rootPoint (r+3) (r+1))) := by
  unfold droppedCubic
  simp

lemma chebT_deriv_at_dropped_eq (r : ℕ) (hr : 2 ≤ r) {d : ℕ} (hd : d = 0 ∨ d = r + 1 ∨ d = r + 2) :
    (chebT (r + 3)).derivative.eval (rootPoint (r + 3) d) =
      (droppedCubic r).derivative.eval (rootPoint (r + 3) d) *
        (prunedPoly r).eval (rootPoint (r + 3) d) := by
  rw [chebT_eq_dropped_mul_pruned r hr]
  exact deriv_eval_mul (droppedCubic r) (prunedPoly r) (rootPoint (r + 3) d)
    (cubic_eval_zero_at_dropped r hd)

/-- the dropped roots satisfy ρ2 < ρ1 < ρ0. -/
lemma dropped_roots_order (r : ℕ) (hr : 2 ≤ r) :
    rootPoint (r+3) (r+2) < rootPoint (r+3) (r+1) ∧
    rootPoint (r+3) (r+1) < rootPoint (r+3) 0 := by
  have hN : 1 ≤ r + 3 := by omega
  constructor
  · exact rootPoint_antitone hN (by omega : r + 2 < r + 3) (by omega : r + 1 < r + 2)
  · exact rootPoint_antitone hN (by omega : r + 1 < r + 3) (by omega : 0 < r + 1)

/-- ρ0 − ρ2 ≥ ρ1 − ρ2. -/
lemma dropped_gap02_ge_gap12 (r : ℕ) (hr : 2 ≤ r) :
    rootPoint (r + 3) 0 - rootPoint (r + 3) (r + 2) ≥
      rootPoint (r + 3) (r + 1) - rootPoint (r + 3) (r + 2) := by
  have hlt : rootPoint (r+3) (r+1) < rootPoint (r+3) 0 := (dropped_roots_order r hr).2
  nlinarith

/-- |cubic'(ρ_d)| ≥ (ρ1−ρ2)² for each dropped root ρ_d -/
lemma cubic_deriv_abs_ge (r : ℕ) (hr : 2 ≤ r) {d : ℕ} (hd : d = 0 ∨ d = r + 1 ∨ d = r + 2) :
    (rootPoint (r + 3) (r + 1) - rootPoint (r + 3) (r + 2)) ^ 2 ≤
      |(droppedCubic r).derivative.eval (rootPoint (r + 3) d)| := by
  let P0 : ℝ := rootPoint (r + 3) 0
  let P1 : ℝ := rootPoint (r + 3) (r + 1)
  let P2 : ℝ := rootPoint (r + 3) (r + 2)
  have hg : 0 < P1 - P2 := by
    change 0 < rootPoint (r + 3) (r + 1) - rootPoint (r + 3) (r + 2)
    exact (dropped_roots_gaps r hr).1
  have h01ge : P0 - P1 ≥ P1 - P2 := by
    change rootPoint (r + 3) 0 - rootPoint (r + 3) (r + 1) ≥
      rootPoint (r + 3) (r + 1) - rootPoint (r + 3) (r + 2)
    exact dropped_gap01_ge_gap12 r hr
  have h02ge : P0 - P2 ≥ P1 - P2 := by
    change rootPoint (r + 3) 0 - rootPoint (r + 3) (r + 2) ≥
      rootPoint (r + 3) (r + 1) - rootPoint (r + 3) (r + 2)
    exact dropped_gap02_ge_gap12 r hr
  have hdnn : 0 ≤ P1 - P2 := by linarith
  have hp01 : 0 ≤ P0 - P1 := by linarith
  have hp02 : 0 ≤ P0 - P2 := by
    have hlt : rootPoint (r+3) (r+2) < rootPoint (r+3) 0 :=
      lt_trans (dropped_roots_order r hr).1 (dropped_roots_order r hr).2
    change 0 ≤ rootPoint (r + 3) 0 - rootPoint (r + 3) (r + 2)
    linarith
  rcases hd with hd0 | hd1 | hd2
  · subst d
    change (P1 - P2) ^ 2 ≤ |(droppedCubic r).derivative.eval P0|
    have hval : (droppedCubic r).derivative.eval P0 = (P0 - P1) * (P0 - P2) := by
      change (droppedCubic r).derivative.eval (rootPoint (r + 3) 0) =
        (rootPoint (r + 3) 0 - rootPoint (r + 3) (r + 1)) *
          (rootPoint (r + 3) 0 - rootPoint (r + 3) (r + 2))
      rw [deriv_cubic_eval]
      ring_nf
    have habs : |(droppedCubic r).derivative.eval P0| = (P0 - P1) * (P0 - P2) := by
      rw [hval]
      calc
        |(P0 - P1) * (P0 - P2)| = |P0 - P1| * |P0 - P2| := by rw [abs_mul]
        _ = (P0 - P1) * (P0 - P2) := by
          rw [abs_of_nonneg (by change 0 ≤ rootPoint (r+3) 0 - rootPoint (r+3) (r+1); linarith [h01ge]),
              abs_of_nonneg (by change 0 ≤ rootPoint (r+3) 0 - rootPoint (r+3) (r+2); linarith)]
    have hprod : (P1 - P2) ^ 2 ≤ (P0 - P1) * (P0 - P2) := by
      have hm := mul_le_mul (by linarith : P1 - P2 ≤ P0 - P1) (by linarith : P1 - P2 ≤ P0 - P2) hdnn hp01
      simpa [pow_two] using hm
    rwa [habs]
  · subst d
    change (P1 - P2) ^ 2 ≤ |(droppedCubic r).derivative.eval P1|
    have hval : (droppedCubic r).derivative.eval P1 = (P1 - P0) * (P1 - P2) := by
      change (droppedCubic r).derivative.eval (rootPoint (r + 3) (r + 1)) =
        (rootPoint (r + 3) (r + 1) - rootPoint (r + 3) 0) *
          (rootPoint (r + 3) (r + 1) - rootPoint (r + 3) (r + 2))
      rw [deriv_cubic_eval]
      ring_nf
    have hsub : |(P1 - P0) * (P1 - P2)| = (P0 - P1) * (P1 - P2) := by
      calc
        |(P1 - P0) * (P1 - P2)| = |P1 - P0| * |P1 - P2| := by rw [abs_mul]
        _ = (P0 - P1) * (P1 - P2) := by
          rw [abs_of_nonpos (by change P1 - P0 ≤ 0; linarith)]
          rw [abs_of_nonneg hdnn]
          ring
    have habs : |(droppedCubic r).derivative.eval P1| = (P0 - P1) * (P1 - P2) := by
      rw [hval, hsub]
    have hprod : (P1 - P2) ^ 2 ≤ (P0 - P1) * (P1 - P2) := by
      have h : P1 - P2 ≤ P0 - P1 := by linarith
      have hm := mul_le_mul h le_rfl hdnn hp01
      simpa [pow_two, mul_comm] using hm
    rwa [habs]
  · subst d
    change (P1 - P2) ^ 2 ≤ |(droppedCubic r).derivative.eval P2|
    have hval : (droppedCubic r).derivative.eval P2 = (P2 - P0) * (P2 - P1) := by
      change (droppedCubic r).derivative.eval (rootPoint (r + 3) (r + 2)) =
        (rootPoint (r + 3) (r + 2) - rootPoint (r + 3) 0) *
          (rootPoint (r + 3) (r + 2) - rootPoint (r + 3) (r + 1))
      rw [deriv_cubic_eval]
      ring_nf
    have hsub : |(P2 - P0) * (P2 - P1)| = (P0 - P2) * (P1 - P2) := by
      calc
        |(P2 - P0) * (P2 - P1)| = |P2 - P0| * |P2 - P1| := by rw [abs_mul]
        _ = (P0 - P2) * (P1 - P2) := by
          rw [abs_of_nonpos (by change P2 - P0 ≤ 0; linarith)]
          rw [abs_of_nonpos (by change P2 - P1 ≤ 0; linarith)]
          ring
    have habs : |(droppedCubic r).derivative.eval P2| = (P0 - P2) * (P1 - P2) := by
      rw [hval, hsub]
    have hprod : (P1 - P2) ^ 2 ≤ (P0 - P2) * (P1 - P2) := by
      have hm := mul_le_mul (by linarith : P1 - P2 ≤ P0 - P2) le_rfl hdnn hp02
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hm
    rwa [habs]

/-- value of the pruned polynomial at a dropped root: |Tpr(ρ_d)| ≤ (r+3)^6 · κ^r -/
lemma pruned_eval_dropped_le (r : ℕ) (hr : 2 ≤ r) {d : ℕ} (hd : d = 0 ∨ d = r + 1 ∨ d = r + 2) :
    |(prunedPoly r).eval (rootPoint (r + 3) d)| ≤ (r + 3) ^ 6 * kappaC ^ r := by
  let ρ0 : ℝ := rootPoint (r+3) 0
  let ρ1 : ℝ := rootPoint (r+3) (r+1)
  let ρ2 : ℝ := rootPoint (r+3) (r+2)
  have hgap : 0 < ρ1 - ρ2 := by
    change 0 < rootPoint (r + 3) (r + 1) - rootPoint (r + 3) (r + 2)
    exact (dropped_roots_gaps r hr).1
  have hgap2 : 0 < (ρ1 - ρ2) ^ 2 := sq_pos_of_pos hgap
  have hdv := chebT_deriv_at_dropped_eq r hr hd
  have hcub : (ρ1 - ρ2) ^ 2 ≤ |(droppedCubic r).derivative.eval (rootPoint (r+3) d)| := by
    change (rootPoint (r + 3) (r + 1) - rootPoint (r + 3) (r + 2)) ^ 2 ≤
      |(droppedCubic r).derivative.eval (rootPoint (r + 3) d)|
    exact cubic_deriv_abs_ge r hr hd
  have hcubpos : 0 < |(droppedCubic r).derivative.eval (rootPoint (r+3) d)| := by
    nlinarith [hcub, hgap2]
  have hρd : rootPoint (r + 3) d ∈ Set.Icc aSerre bSerre := by
    have hlt : d < r + 3 := by rcases hd with h0 | h1 | h2 <;> omega
    exact rootPoint_mem_Icc hlt
  have hM : |(chebT (r+3)).derivative.eval (rootPoint (r+3) d)| ≤
      (r + 3) ^ 2 * kappaC ^ (r + 2) := chebT_deriv_bound r (rootPoint (r+3) d) hρd
  have hdvabs : |(chebT (r+3)).derivative.eval (rootPoint (r+3) d)| =
      |(droppedCubic r).derivative.eval (rootPoint (r+3) d)| * |(prunedPoly r).eval (rootPoint (r+3) d)| := by
    rw [hdv, abs_mul]
  have hle' : |(droppedCubic r).derivative.eval (rootPoint (r+3) d)| *
        |(prunedPoly r).eval (rootPoint (r+3) d)| ≤
      (r + 3) ^ 2 * kappaC ^ (r + 2) := by
    rwa [← hdvabs]
  have hle : |(prunedPoly r).eval (rootPoint (r+3) d)| * |(droppedCubic r).derivative.eval (rootPoint (r+3) d)| ≤
      (r + 3) ^ 2 * kappaC ^ (r + 2) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hle'
  have hdiv : |(prunedPoly r).eval (rootPoint (r+3) d)| ≤
      (r + 3) ^ 2 * kappaC ^ (r + 2) / |(droppedCubic r).derivative.eval (rootPoint (r+3) d)| := by
    rwa [le_div_iff₀ hcubpos]
  have hM0 : 0 ≤ (r + 3) ^ 2 * kappaC ^ (r + 2) := by
    exact mul_nonneg (by positivity) (pow_nonneg (le_of_lt kappaC_pos) _)
  have hle2 : (r + 3) ^ 2 * kappaC ^ (r + 2) / |(droppedCubic r).derivative.eval (rootPoint (r+3) d)| ≤
      (r + 3) ^ 2 * kappaC ^ (r + 2) / (ρ1 - ρ2) ^ 2 :=
    div_le_div_of_nonneg_left hM0 hgap2 hcub
  have hmain : |(prunedPoly r).eval (rootPoint (r+3) d)| ≤
      (r + 3) ^ 2 * kappaC ^ (r + 2) / (ρ1 - ρ2) ^ 2 := by
    exact le_trans hdiv hle2
  have hd12ge : (8 * kappaC) / (r + 3 : ℝ) ^ 2 ≤ ρ1 - ρ2 := by
    change (8 * kappaC) / (r + 3 : ℝ) ^ 2 ≤ rootPoint (r + 3) (r + 1) - rootPoint (r + 3) (r + 2)
    exact dropped_distance_ge r hr
  have hfin : (r + 3) ^ 2 * kappaC ^ (r + 2) / (ρ1 - ρ2) ^ 2 ≤ (r + 3) ^ 6 * kappaC ^ r := by
    have hApos : 0 < (8 * kappaC) / (r + 3 : ℝ) ^ 2 := by
      exact div_pos (mul_pos (by norm_num) kappaC_pos) (by positivity)
    have hsq : ((8 * kappaC) / (r + 3 : ℝ) ^ 2) ^ 2 ≤ (ρ1 - ρ2) ^ 2 := by
      simpa [pow_two] using mul_le_mul hd12ge hd12ge (le_of_lt hApos) (le_of_lt hgap)
    have hA2pos : 0 < ((8 * kappaC) / (r + 3 : ℝ) ^ 2) ^ 2 := sq_pos_of_pos hApos
    have hden2 : (r + 3) ^ 2 * kappaC ^ (r + 2) / (ρ1 - ρ2) ^ 2 ≤
        (r + 3) ^ 2 * kappaC ^ (r + 2) / ((8 * kappaC) / (r + 3 : ℝ) ^ 2) ^ 2 :=
      div_le_div_of_nonneg_left hM0 hA2pos hsq
    have hnum : (r + 3) ^ 2 * kappaC ^ (r + 2) / ((8 * kappaC) / (r + 3 : ℝ) ^ 2) ^ 2 =
        (r + 3) ^ 6 * kappaC ^ r / 64 := by
      field_simp [kappaC_ne]
      ring_nf
    have h64 : (r + 3) ^ 6 * kappaC ^ r / 64 ≤ (r + 3) ^ 6 * kappaC ^ r := by
      have hnon : 0 ≤ (r + 3) ^ 6 * kappaC ^ r := by
        exact mul_nonneg (by positivity) (pow_nonneg (le_of_lt kappaC_pos) r)
      nlinarith
    calc
      (r + 3) ^ 2 * kappaC ^ (r + 2) / (ρ1 - ρ2) ^ 2 ≤
          (r + 3) ^ 2 * kappaC ^ (r + 2) / ((8 * kappaC) / (r + 3 : ℝ) ^ 2) ^ 2 := hden2
      _ = (r + 3) ^ 6 * kappaC ^ r / 64 := hnum
      _ ≤ (r + 3) ^ 6 * kappaC ^ r := h64

  change |(prunedPoly r).eval (rootPoint (r + 3) d)| ≤ (r + 3) ^ 6 * kappaC ^ r
  exact le_trans (by simpa [ρ1, ρ2] using hmain) hfin



/-- absolute value of the cubic at x is the product of the three distances -/
lemma cubic_eval_abs (r : ℕ) (x : ℝ) :
    |(droppedCubic r).eval x| =
      |x - rootPoint (r + 3) 0| * (|x - rootPoint (r + 3) (r + 1)| * |x - rootPoint (r + 3) (r + 2)|) := by
  unfold droppedCubic
  rw [eval_mul, eval_mul, abs_mul, abs_mul]
  simp

/-- |Tpr(x)| · |cubic(x)| = |chebT (r+3)(x)| -/
lemma pruned_eval_mul_cubic (r : ℕ) (hr : 2 ≤ r) (x : ℝ) :
    |(prunedPoly r).eval x| * |(droppedCubic r).eval x| = |(chebT (r + 3)).eval x| := by
  have hid : chebT (r + 3) = droppedCubic r * prunedPoly r := chebT_eq_dropped_mul_pruned r hr
  calc
    |(prunedPoly r).eval x| * |(droppedCubic r).eval x| =
        |(droppedCubic r).eval x * (prunedPoly r).eval x| := by
          rw [abs_mul, mul_comm]
    _ = |((droppedCubic r) * (prunedPoly r)).eval x| := by rw [eval_mul]
    _ = |(chebT (r + 3)).eval x| := by rw [hid]

/-- if `T·(δa·δb·δc) ≤ M·δc` and δa,δb ≥ d/2, then `T ≤ 4M/d²`. -/
lemma quot_by_two_distances {T δa δb δc M d : ℝ} (h : T * (δa * δb * δc) ≤ M * δc)
    (hδc : 0 < δc) (ha : d / 2 ≤ δa) (hb : d / 2 ≤ δb) (hd : 0 < d) (hM : 0 ≤ M) :
    T ≤ 4 * M / d ^ 2 := by
  have h1 : T * (δa * δb) ≤ M := by
    have h' : (T * (δa * δb)) * δc ≤ M * δc := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h
    exact le_of_mul_le_mul_right h' hδc
  have hd2 : 0 ≤ d / 2 := by linarith
  have hprod : (d / 2) * (d / 2) ≤ δa * δb := by
    have hδa : 0 ≤ δa := by linarith [hd2, ha]
    exact mul_le_mul ha hb hd2 hδa
  have h0 : 0 < d / 2 := by linarith
  have hposab : 0 < δa * δb := by
    have hδa : 0 < δa := lt_of_lt_of_le h0 ha
    have hδb : 0 < δb := lt_of_lt_of_le h0 hb
    positivity
  have hT : T ≤ M / (δa * δb) := by
    rwa [le_div_iff₀ hposab]
  have hbnd : M / (δa * δb) ≤ M / ((d / 2) * (d / 2)) := by
    apply div_le_div_of_nonneg_left hM (by positivity : 0 < (d / 2) * (d / 2)) hprod
  have hrew : M / ((d / 2) * (d / 2)) = 4 * M / d ^ 2 := by
    field_simp [hd.ne']
    ring
  calc
    T ≤ M / (δa * δb) := hT
    _ ≤ M / ((d / 2) * (d / 2)) := hbnd
    _ = 4 * M / d ^ 2 := hrew

/-- Main sup-norm bound on the whole interval: |Tpr(x)| ≤ (r+3)^6 · κ^r. -/
lemma prunedPoly_bound (r : ℕ) (hr : 2 ≤ r) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) :
    |(prunedPoly r).eval x| ≤ (r + 3) ^ 6 * kappaC ^ r := by
  let ρ0 : ℝ := rootPoint (r + 3) 0
  let ρ1 : ℝ := rootPoint (r + 3) (r + 1)
  let ρ2 : ℝ := rootPoint (r + 3) (r + 2)
  let d : ℝ := ρ1 - ρ2
  let M : ℝ := (r + 3) ^ 2 * kappaC ^ (r + 2)
  by_cases hxdrop : x = ρ0 ∨ x = ρ1 ∨ x = ρ2
  · rcases hxdrop with hx0 | hx1 | hx2
    · rw [hx0]
      change |(prunedPoly r).eval (rootPoint (r + 3) 0)| ≤ (r + 3) ^ 6 * kappaC ^ r
      exact pruned_eval_dropped_le r hr (Or.inl rfl)
    · rw [hx1]
      change |(prunedPoly r).eval (rootPoint (r + 3) (r + 1))| ≤ (r + 3) ^ 6 * kappaC ^ r
      exact pruned_eval_dropped_le r hr (Or.inr (Or.inl rfl))
    · rw [hx2]
      change |(prunedPoly r).eval (rootPoint (r + 3) (r + 2))| ≤ (r + 3) ^ 6 * kappaC ^ r
      exact pruned_eval_dropped_le r hr (Or.inr (Or.inr rfl))
  · -- x is not any of the dropped roots
    have hne0 : x ≠ ρ0 := by intro h; exact hxdrop (Or.inl h)
    have hne1 : x ≠ ρ1 := by intro h; exact hxdrop (Or.inr (Or.inl h))
    have hne2 : x ≠ ρ2 := by intro h; exact hxdrop (Or.inr (Or.inr h))
    let δ0 : ℝ := |x - ρ0|
    let δ1 : ℝ := |x - ρ1|
    let δ2 : ℝ := |x - ρ2|
    have hdpos : 0 < d := by
      dsimp [d, ρ1, ρ2]
      change 0 < rootPoint (r + 3) (r + 1) - rootPoint (r + 3) (r + 2)
      exact (dropped_roots_gaps r hr).1
    have hM0 : 0 ≤ M := by
      dsimp [M]
      exact mul_nonneg (by positivity) (pow_nonneg (le_of_lt kappaC_pos) _)
    have hδ0pos : 0 < δ0 := by
      dsimp [δ0]
      exact abs_pos.mpr (sub_ne_zero.mpr hne0)
    have hδ1pos : 0 < δ1 := by
      dsimp [δ1]
      exact abs_pos.mpr (sub_ne_zero.mpr hne1)
    have hδ2pos : 0 < δ2 := by
      dsimp [δ2]
      exact abs_pos.mpr (sub_ne_zero.mpr hne2)
    have hprod : |(prunedPoly r).eval x| * (δ0 * δ1 * δ2) = |(chebT (r + 3)).eval x| := by
      have h1 := pruned_eval_mul_cubic r hr x
      have h2 := cubic_eval_abs r x
      dsimp [δ0, δ1, δ2]
      rw [h2] at h1
      simpa [mul_assoc] using h1
    have hanchor0 : |(chebT (r+3)).eval x| ≤ M * δ0 := by
      have h := chebT_anchor_bound r hx (d := 0) (Or.inl rfl)
      dsimp [δ0, M]
      simpa using h
    have hanchor1 : |(chebT (r+3)).eval x| ≤ M * δ1 := by
      have h := chebT_anchor_bound r hx (d := r + 1) (Or.inr (Or.inl rfl))
      dsimp [δ1, M]
      simpa using h
    have hanchor2 : |(chebT (r+3)).eval x| ≤ M * δ2 := by
      have h := chebT_anchor_bound r hx (d := r + 2) (Or.inr (Or.inr rfl))
      dsimp [δ2, M]
      simpa using h
    have hc0 : |(prunedPoly r).eval x| * (δ0 * δ1 * δ2) ≤ M * δ0 := by
      rw [hprod]
      exact hanchor0
    have hc1 : |(prunedPoly r).eval x| * (δ0 * δ1 * δ2) ≤ M * δ1 := by
      rw [hprod]
      exact hanchor1
    have hc2 : |(prunedPoly r).eval x| * (δ0 * δ1 * δ2) ≤ M * δ2 := by
      rw [hprod]
      exact hanchor2
    -- regroup hc1 and hc0 for the two-distances lemma:
    have hc1' : |(prunedPoly r).eval x| * (δ0 * δ2 * δ1) ≤ M * δ1 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hc1
    have hc0' : |(prunedPoly r).eval x| * (δ1 * δ2 * δ0) ≤ M * δ0 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hc0
    have hTpr : |(prunedPoly r).eval x| ≤ 4 * M / d ^ 2 := by
      by_cases hbig0 : d / 2 ≤ δ0
      · by_cases hbig1 : d / 2 ≤ δ1
        · have hq := quot_by_two_distances (T := |(prunedPoly r).eval x|) (δa := δ0) (δb := δ1)
            (δc := δ2) (M := M) (d := d) hc2 hδ2pos hbig0 hbig1 hdpos hM0
          exact hq
        · have h1s : δ1 < d / 2 := by linarith
          have hbig2 : d / 2 ≤ δ2 := by
            by_contra hnot
            have h2s : δ2 < d / 2 := by linarith
            have htr : |ρ1 - ρ2| ≤ δ1 + δ2 := by
              dsimp [δ1, δ2]
              calc
                |ρ1 - ρ2| ≤ |ρ1 - x| + |x - ρ2| := by
                  calc
                    |ρ1 - ρ2| = |(ρ1 - x) + (x - ρ2)| := by ring_nf
                    _ ≤ |ρ1 - x| + |x - ρ2| := abs_add_le _ _
                _ = |x - ρ1| + |x - ρ2| := by rw [abs_sub_comm ρ1 x]
            have hlt : |ρ1 - ρ2| < d := by
              nlinarith
            have heq : |ρ1 - ρ2| = d := by
              dsimp [d]
              rw [abs_of_nonneg (le_of_lt hdpos)]
            rw [heq] at hlt
            exact (lt_irrefl d) hlt
          have hq := quot_by_two_distances (T := |(prunedPoly r).eval x|) (δa := δ0) (δb := δ2)
            (δc := δ1) (M := M) (d := d) hc1' hδ1pos hbig0 hbig2 hdpos hM0
          exact hq
      · have h0s : δ0 < d / 2 := by linarith
        have hbig1 : d / 2 ≤ δ1 := by
          by_contra hnot
          have h1s : δ1 < d / 2 := by linarith
          have htr : |ρ0 - ρ1| ≤ δ0 + δ1 := by
            dsimp [δ0, δ1]
            calc
              |ρ0 - ρ1| ≤ |ρ0 - x| + |x - ρ1| := by
                calc
                  |ρ0 - ρ1| = |(ρ0 - x) + (x - ρ1)| := by ring_nf
                  _ ≤ |ρ0 - x| + |x - ρ1| := abs_add_le _ _
              _ = |x - ρ0| + |x - ρ1| := by rw [abs_sub_comm ρ0 x]
          have hlt : |ρ0 - ρ1| < d := by
            nlinarith
          have hge : d ≤ |ρ0 - ρ1| := by
            dsimp [d]
            rw [abs_of_nonneg (by
              change 0 ≤ rootPoint (r+3) 0 - rootPoint (r+3) (r+1)
              have h01 : rootPoint (r+3) 0 - rootPoint (r+3) (r+1) ≥
                  rootPoint (r+3) (r+1) - rootPoint (r+3) (r+2) := dropped_gap01_ge_gap12 r hr
              have hg : 0 < rootPoint (r+3) (r+1) - rootPoint (r+3) (r+2) := (dropped_roots_gaps r hr).1
              linarith)]
            exact dropped_gap01_ge_gap12 r hr
          exact (not_le_of_gt hlt) hge
        have hbig2 : d / 2 ≤ δ2 := by
          by_contra hnot
          have h2s : δ2 < d / 2 := by linarith
          have htr : |ρ0 - ρ2| ≤ δ0 + δ2 := by
            dsimp [δ0, δ2]
            calc
              |ρ0 - ρ2| ≤ |ρ0 - x| + |x - ρ2| := by
                calc
                  |ρ0 - ρ2| = |(ρ0 - x) + (x - ρ2)| := by ring_nf
                  _ ≤ |ρ0 - x| + |x - ρ2| := abs_add_le _ _
              _ = |x - ρ0| + |x - ρ2| := by rw [abs_sub_comm ρ0 x]
          have hlt : |ρ0 - ρ2| < d := by
            nlinarith
          have hge : d ≤ |ρ0 - ρ2| := by
            dsimp [d]
            rw [abs_of_nonneg (by
              change 0 ≤ rootPoint (r+3) 0 - rootPoint (r+3) (r+2)
              have h02 : rootPoint (r+3) 0 - rootPoint (r+3) (r+2) ≥
                  rootPoint (r+3) (r+1) - rootPoint (r+3) (r+2) := dropped_gap02_ge_gap12 r hr
              have hg : 0 < rootPoint (r+3) (r+1) - rootPoint (r+3) (r+2) := (dropped_roots_gaps r hr).1
              linarith)]
            exact dropped_gap02_ge_gap12 r hr
          exact (not_le_of_gt hlt) hge
        have hq := quot_by_two_distances (T := |(prunedPoly r).eval x|) (δa := δ1) (δb := δ2)
          (δc := δ0) (M := M) (d := d) hc0' hδ0pos hbig1 hbig2 hdpos hM0
        exact hq
    have hfin : 4 * M / d ^ 2 ≤ (r + 3) ^ 6 * kappaC ^ r := by
      have hApos : 0 < (8 * kappaC) / (r + 3 : ℝ) ^ 2 := by
        exact div_pos (mul_pos (by norm_num) kappaC_pos) (by positivity)
      have hd12ge : (8 * kappaC) / (r + 3 : ℝ) ^ 2 ≤ d := by
        dsimp [d, ρ1, ρ2]
        change (8 * kappaC) / (r + 3 : ℝ) ^ 2 ≤ rootPoint (r + 3) (r + 1) - rootPoint (r + 3) (r + 2)
        exact dropped_distance_ge r hr
      have hsq : ((8 * kappaC) / (r + 3 : ℝ) ^ 2) ^ 2 ≤ d ^ 2 := by
        simpa [pow_two] using mul_le_mul hd12ge hd12ge (le_of_lt hApos) hdpos.le
      have hA2pos : 0 < ((8 * kappaC) / (r + 3 : ℝ) ^ 2) ^ 2 := sq_pos_of_pos hApos
      have hstep : M / d ^ 2 ≤ M / ((8 * kappaC) / (r + 3 : ℝ) ^ 2) ^ 2 :=
        div_le_div_of_nonneg_left hM0 hA2pos hsq
      have hmul := mul_le_mul_of_nonneg_left hstep (by norm_num : 0 ≤ (4 : ℝ))
      have hnum : 4 * M / ((8 * kappaC) / (r + 3 : ℝ) ^ 2) ^ 2 =
          (r + 3) ^ 6 * kappaC ^ r / 16 := by
        dsimp [M]
        field_simp [kappaC_ne]
        ring_nf
      have h16 : (r + 3) ^ 6 * kappaC ^ r / 16 ≤ (r + 3) ^ 6 * kappaC ^ r := by
        have hnon : 0 ≤ (r + 3) ^ 6 * kappaC ^ r := by
          exact mul_nonneg (by positivity) (pow_nonneg (le_of_lt kappaC_pos) r)
        nlinarith
      have hpart : 4 * (M / d ^ 2) = 4 * M / d ^ 2 := by rw [← mul_div_assoc]
      have hpart2 : 4 * (M / ((8 * kappaC) / (r + 3 : ℝ) ^ 2) ^ 2) = 4 * M / ((8 * kappaC) / (r + 3 : ℝ) ^ 2) ^ 2 := by rw [← mul_div_assoc]
      rw [← hpart]
      exact le_trans hmul (by
        calc
          4 * (M / ((8 * kappaC) / (r + 3 : ℝ) ^ 2) ^ 2) = 4 * M / ((8 * kappaC) / (r + 3 : ℝ) ^ 2) ^ 2 := hpart2
          _ = (r + 3) ^ 6 * kappaC ^ r / 16 := hnum
          _ ≤ (r + 3) ^ 6 * kappaC ^ r := h16)
    exact le_trans hTpr hfin



/-! ## Roots of the pruned polynomial and bracket values -/

/-- the roots of `prunedPoly r` are exactly the kept Chebyshev roots. -/
lemma pruned_eval_zero_iff_kept (r : ℕ) (x : ℝ) :
    (prunedPoly r).eval x = 0 ↔ ∃ j : Fin r, x = rootPoint (r + 3) (j.val + 1) := by
  constructor
  · intro h
    unfold prunedPoly at h
    rw [eval_prod] at h
    simp at h
    rcases (Finset.prod_eq_zero_iff.mp h) with ⟨j, hjmem, hjz⟩
    have hx : x - rootPoint (r+3) (j.val+1) = 0 := hjz
    exact ⟨j, by linarith⟩
  · rintro ⟨j, rfl⟩
    exact pruned_eval_zero_at_kept r (by omega : 1 ≤ j.val + 1) (by omega : j.val + 1 ≤ r)

/-- every root of `Tpr` lies in the open Serre interval. -/
lemma pruned_root_mem_Ioo (r : ℕ) {x : ℝ} (hx : (prunedPoly r).eval x = 0) :
    x ∈ Set.Ioo aSerre bSerre := by
  rcases (pruned_eval_zero_iff_kept r x).mp hx with ⟨j, rfl⟩
  exact rootPoint_mem_Ioo (N := r + 3) (k := j.val + 1) (by omega) (by omega : j.val + 1 < r + 3)

/-- `rootPoint N` is decreasing in its index (non-strict version). -/
lemma rootPoint_antitone_le {N : ℕ} (hN : 1 ≤ N) {k l : ℕ} (hk : l < N) (hkl : k ≤ l) :
    rootPoint N l ≤ rootPoint N k := by
  rcases lt_or_eq_of_le hkl with hlt | heq
  · exact le_of_lt (rootPoint_antitone hN hk hlt)
  · rw [heq]

/-- the leftmost bracket `y_r` is below every root of `Tpr`. -/
lemma bracket_left_below_root (r : ℕ) {j : Fin r} :
    bracketPoint r ⟨r, by omega⟩ < rootPoint (r + 3) (j.val + 1) := by
  have hN : 1 ≤ r + 3 := by omega
  have hy : bracketPoint r ⟨r, by omega⟩ < rootPoint (r+3) r := by
    unfold bracketPoint
    exact (extPoint_rootPoint_interleave (N := r + 3) (k := r) hN (by omega : r < r + 3)).1
  have hrootle : rootPoint (r+3) r ≤ rootPoint (r+3) (j.val + 1) :=
    rootPoint_antitone_le hN (by omega : r < r + 3) (by omega : j.val + 1 ≤ r)
  exact lt_of_lt_of_le hy hrootle

/-- the rightmost bracket `y_0` is above every root of `Tpr`. -/
lemma root_below_bracket_right (r : ℕ) {j : Fin r} :
    rootPoint (r + 3) (j.val + 1) < bracketPoint r ⟨0, by omega⟩ := by
  have hN : 1 ≤ r + 3 := by omega
  have hy : rootPoint (r+3) 1 < bracketPoint r ⟨0, by omega⟩ := by
    unfold bracketPoint
    exact (extPoint_rootPoint_interleave (N := r + 3) (k := 1) hN (by omega : 1 < r + 3)).2
  have hrootle : rootPoint (r+3) (j.val + 1) ≤ rootPoint (r+3) 1 :=
    rootPoint_antitone_le hN (by omega : j.val + 1 < r + 3) (by omega : 1 ≤ j.val + 1)
  exact lt_of_le_of_lt hrootle hy

/-- every root of `Tpr` lies between the extreme brackets `y_r` and `y_0`. -/
lemma pruned_root_mem_Ioo_brackets (r : ℕ) {x : ℝ} (hx : (prunedPoly r).eval x = 0) :
    x ∈ Set.Ioo (bracketPoint r ⟨r, by omega⟩) (bracketPoint r ⟨0, by omega⟩) := by
  rcases (pruned_eval_zero_iff_kept r x).mp hx with ⟨j, rfl⟩
  exact ⟨bracket_left_below_root r (j := j), root_below_bracket_right r (j := j)⟩

/-- two points of the interval are within `bSerre − aSerre`. -/
lemma abs_sub_le_interval {u v : ℝ} (hu : u ∈ Set.Icc aSerre bSerre)
    (hv : v ∈ Set.Icc aSerre bSerre) : |u - v| ≤ bSerre - aSerre := by
  apply abs_le.mpr
  constructor
  · nlinarith [hu.1, hv.2]
  · nlinarith [hu.2, hv.1]

/-- dropped-root distance from any bracket point is ≤ 4κ. -/
lemma bracket_dist_dropped_le (r : ℕ) (i : Fin (r + 1)) {d : ℕ}
    (hd : d = 0 ∨ d = r + 1 ∨ d = r + 2) :
    |bracketPoint r i - rootPoint (r + 3) d| ≤ 4 * kappaC := by
  have hlt : d < r + 3 := by rcases hd with h0 | h1 | h2 <;> omega
  have h1 := abs_sub_le_interval (bracketPoint_mem_Icc r i) (rootPoint_mem_Icc (N := r + 3) (k := d) hlt)
  rw [bSerre_sub_aSerre_eq] at h1
  exact h1

/-- value of `Tpr` at a bracket point is ≥ κ^r/32. -/
lemma pruned_bracket_lower (r : ℕ) (hr : 2 ≤ r) (i : Fin (r + 1)) :
    (kappaC ^ r) / 32 ≤ |(prunedPoly r).eval (bracketPoint r i)| := by
  let y : ℝ := bracketPoint r i
  have hN : 1 ≤ r + 3 := by omega
  have hv : (chebT (r + 3)).eval y = 2 * kappaC ^ (r + 3) * (-1) ^ (i.val + 1) := by
    dsimp [y]
    exact chebT_eval_extPoint (r + 3) (i.val + 1) hN (by omega : i.val + 1 ≤ r + 3)
  have hvpos : 0 ≤ 2 * kappaC ^ (r + 3) := by
    exact mul_nonneg (by norm_num) (pow_nonneg (le_of_lt kappaC_pos) _)
  have hvabs : |(chebT (r + 3)).eval y| = 2 * kappaC ^ (r + 3) := by
    rw [hv]
    rw [abs_mul]
    rw [abs_of_nonneg hvpos]
    have hpow : |((-1 : ℝ) ^ (i.val + 1))| = 1 := by simp
    rw [hpow]
    ring
  have hprod : |(prunedPoly r).eval y| * |(droppedCubic r).eval y| = 2 * kappaC ^ (r + 3) := by
    rw [pruned_eval_mul_cubic r hr y]
    exact hvabs
  have hb0 : |y - rootPoint (r + 3) 0| ≤ 4 * kappaC := by
    dsimp [y]
    exact bracket_dist_dropped_le r i (Or.inl rfl)
  have hb1 : |y - rootPoint (r + 3) (r + 1)| ≤ 4 * kappaC := by
    dsimp [y]
    exact bracket_dist_dropped_le r i (Or.inr (Or.inl rfl))
  have hb2 : |y - rootPoint (r + 3) (r + 2)| ≤ 4 * kappaC := by
    dsimp [y]
    exact bracket_dist_dropped_le r i (Or.inr (Or.inr rfl))
  have hk4 : 0 ≤ 4 * kappaC := mul_nonneg (by norm_num) (le_of_lt kappaC_pos)
  have hbnd : |(droppedCubic r).eval y| ≤ (4 * kappaC) ^ 3 := by
    rw [cubic_eval_abs]
    calc
      |y - rootPoint (r+3) 0| * (|y - rootPoint (r+3) (r+1)| * |y - rootPoint (r+3) (r+2)|)
          ≤ (4 * kappaC) * ((4 * kappaC) * (4 * kappaC)) := by
            have h12 : |y - rootPoint (r+3) (r+1)| * |y - rootPoint (r+3) (r+2)| ≤
                (4 * kappaC) * (4 * kappaC) :=
              mul_le_mul hb1 hb2 (abs_nonneg _) hk4
            have h01 : 0 ≤ |y - rootPoint (r+3) (r+1)| * |y - rootPoint (r+3) (r+2)| := by positivity
            exact mul_le_mul hb0 h12 h01 hk4
      _ = (4 * kappaC) ^ 3 := by
        rw [pow_three]
  let B : ℝ := (4 * kappaC) ^ 3
  have hBpos : 0 < B := by
    dsimp [B]
    exact pow_pos (mul_pos (by norm_num) kappaC_pos) 3
  have ha0 : 0 ≤ |(prunedPoly r).eval y| := abs_nonneg _
  have hh : |(prunedPoly r).eval y| * |(droppedCubic r).eval y| ≤ |(prunedPoly r).eval y| * B := by
    have hmm := mul_le_mul_of_nonneg_left hbnd ha0
    dsimp [B]
    simpa [mul_comm] using hmm
  have haB : |(prunedPoly r).eval y| * B ≥ 2 * kappaC ^ (r + 3) := by
    rw [hprod] at hh
    exact hh
  have hdiv : (2 * kappaC ^ (r + 3)) / B ≤ |(prunedPoly r).eval y| := by
    exact (div_le_iff₀ hBpos).mpr haB
  have hrew : (2 * kappaC ^ (r + 3)) / (4 * kappaC) ^ 3 = kappaC ^ r / 32 := by
    field_simp [kappaC_ne]
    ring_nf
  have hfin : kappaC ^ r / 32 ≤ |(prunedPoly r).eval y| := by
    dsimp [B] at hdiv
    rwa [hrew] at hdiv
  simpa [y] using hfin

/-- extrema are decreasing in their index: `bracketPoint` is decreasing. -/
lemma bracketPoint_decreasing (r : ℕ) {i j : Fin (r + 1)} (hij : i.val < j.val) :
    bracketPoint r j < bracketPoint r i := by
  have hN : 1 ≤ r + 3 := by omega
  unfold bracketPoint
  exact extPoint_antitone (N := r + 3) hN (by omega : j.val + 1 ≤ r + 3) (by omega)

/-- a root of `Tpr` sits between consecutive brackets. -/
lemma bracket_interleave_root (r : ℕ) (i : Fin r) :
    bracketPoint r ⟨i.val + 1, by omega⟩ < rootPoint (r + 3) (i.val + 1) ∧
      rootPoint (r + 3) (i.val + 1) < bracketPoint r ⟨i.val, by omega⟩ := by
  have hN : 1 ≤ r + 3 := by omega
  unfold bracketPoint
  exact extPoint_rootPoint_interleave (N := r + 3) (k := i.val + 1) hN (by omega)


/-- Main structure theorem for the pruned Chebyshev polynomial. -/
theorem pruned_cheb (r : ℕ) (hr : 2 ≤ r) :
    let Tpr := prunedPoly r
    Tpr.Monic ∧ Tpr.natDegree = r ∧
    (∀ x : ℝ, Tpr.eval x = 0 → x ∈ Set.Ioo aSerre bSerre) ∧
    (∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → |Tpr.eval x| ≤ (r + 3) ^ 6 * kappaC ^ r) ∧
    (∃ C : ℝ, 32 ≤ C ∧
      (∀ i : Fin (r + 1),
        bracketPoint r i ∈ Set.Icc aSerre bSerre ∧
        |Tpr.eval (bracketPoint r i)| ≥ C⁻¹ * kappaC ^ r) ∧
      (∀ i j : Fin (r + 1), i.val < j.val → bracketPoint r j < bracketPoint r i) ∧
      (∀ i : Fin r, bracketPoint r ⟨i.val + 1, by omega⟩ <
          rootPoint (r + 3) (i.val + 1) ∧
        rootPoint (r + 3) (i.val + 1) < bracketPoint r ⟨i.val, by omega⟩) ∧
      (∀ x : ℝ, Tpr.eval x = 0 → x ∈ Set.Ioo
          (bracketPoint r ⟨r, by omega⟩) (bracketPoint r ⟨0, by omega⟩))) := by
  dsimp
  refine ⟨prunedPoly_monic r, prunedPoly_natDegree r, ?_, ?_, ?_⟩
  · intro x hx
    exact pruned_root_mem_Ioo r hx
  · intro x hx
    exact prunedPoly_bound r hr hx
  · refine ⟨(32 : ℝ), by norm_num, ?_, ?_, ?_, ?_⟩
    · intro i
      constructor
      · exact bracketPoint_mem_Icc r i
      · have hb := pruned_bracket_lower r hr i
        have hc : (32 : ℝ)⁻¹ * kappaC ^ r = kappaC ^ r / 32 := by ring_nf
        rwa [hc]
    · intro i j hij
      exact bracketPoint_decreasing r hij
    · intro i
      exact bracket_interleave_root r i
    · intro x hx
      exact pruned_root_mem_Ioo_brackets r hx

end Submission.AdjustedCheb
