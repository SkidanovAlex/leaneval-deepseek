import Mathlib
import Submission.Work.Diff.L.Defs
import Submission.Work.Diff.L.Curv4K
import Submission.Work.Diff.L.exists_isONPair_secK_le_scalAlg_div

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Component bound for a pinching set

Every component `R i j k l` of a curvature array `R` in a pinching set `F` is bounded by a fixed
linear function `c * scalAlg R + C₀` of the scalar curvature, with a *positive* coefficient `c`.

The argument splits `F` into two classes (with `δ := 1/2`):

* `R ∈ F` that is `δ`-pinched.  Then
  (i) every sectional curvature of `R` is nonnegative (`IsPinchedAlg δ R` applied to the plane
  `(u,v)` twice gives `δ * secK R u v ≤ secK R u v`, and `δ < 1`), and
  (ii) for every orthonormal pair, `secK R u v ≤ scalAlg R / (δ n (n-1))`: if `(u₀,v₀)` is an
  orthonormal pair of sectional curvature at most the mean `scalAlg R / (n(n-1))`
  (`exists_isONPair_secK_le_scalAlg_div`), then `δ * secK R u v ≤ secK R u₀ v₀`.
  The polarization identity (`R4_eq_polarize`), applied to the standard basis, then bounds every
  component by `8 * scalAlg R / (δ n (n-1))` (`abs_R4_stdB_le_of_secK_bound`).
* the remaining elements of `F` are bounded (`IsPinchingSet`), so they contribute the additive
  constant `C₀`; their scalar curvature is bounded below by `- n² ‖R‖ ≥ -n² r`
  (`abs_scalAlg_le`), which is what makes the linear term absorb them.

## Naming note

This file (like `Work.Diff.L.Curv4K`) works with `Work.Diff.L.polU`/`polV` instead of
`Work.Diff.L.Psi`: the two combinations are the same (up to the naming of the four arguments), and
the modules `PinDefs` and `Curv4K` declare clashing names (`Work.Diff.L.dot_comm`,
`dot_self_nonneg`, `dot_self_eq_zero`, `dot_self_pos`), so no file may import both.
-/

namespace Work.Diff.L

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Work.Diff.Alg.PA

variable {n : ℕ}

/-! ## Elementary supplements -/

/-- The quartic form vanishes when its second argument is `0`. -/
lemma secK_zero_right (R : Curv4 n) (u : Fin n → ℝ) : secK R u 0 = 0 := by
  have h := secK_smul_smul R 1 0 u (0 : Fin n → ℝ)
  simpa using h

/-- The quartic form vanishes when its first argument is `0`. -/
lemma secK_zero_left (R : Curv4 n) (v : Fin n → ℝ) : secK R 0 v = 0 := by
  have h := secK_smul_smul R 0 1 (0 : Fin n → ℝ) v
  simpa using h

theorem dot_smul_left' (t : ℝ) (p q : Fin n → ℝ) : dot (t • p) q = t * dot p q := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dot_smul_right' (t : ℝ) (p q : Fin n → ℝ) : dot p (t • q) = t * dot p q := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dot_sub_left' (p p' q : Fin n → ℝ) : dot (p - p') q = dot p q - dot p' q := by
  simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem dot_sub_right' (p q q' : Fin n → ℝ) : dot p (q - q') = dot p q - dot p q' := by
  simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The four-term triangle inequality. -/
lemma abs_sub_sub_add_le (a b c d : ℝ) : |a - b - c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := le_abs_self a
  have h2 := neg_le_abs a
  have h3 := le_abs_self b
  have h4 := neg_le_abs b
  have h5 := le_abs_self c
  have h6 := neg_le_abs c
  have h7 := le_abs_self d
  have h8 := neg_le_abs d
  rw [abs_le]
  constructor <;> linarith

/-! ## The quartic form of an algebraic curvature tensor is controlled by its values on `dot`-orthonormal pairs -/

/-- **`secK` of an arbitrary pair is bounded by its values on orthonormal pairs, up to the area
factor.**  If `|secK R p q| ≤ S` for every orthonormal pair (`S ≥ 0`), then for *arbitrary*
vectors `u`, `v`,

`|secK R u v| ≤ dot u u * dot v v * S`.

Proof: `secK R u v = secK R u w` where `w = v - c • u` with `c = dot v u / dot u u` is the
component of `v` orthogonal to `u` (`secK_sub_smul_second`); normalising `u` and `w` to
`û = (√(dot u u))⁻¹ • u` and `ŵ = (√(dot w w))⁻¹ • w` gives an orthonormal pair with
`secK R u w = (dot u u) * (dot w w) * secK R û ŵ` (`secK_smul_smul`), while
`dot w w = dot v v - c² * dot u u ≤ dot v v`. -/
theorem abs_secK_le_of_isONPair_abs_le {R : Curv4 n} (hR : IsAlgCurv R) {S : ℝ} (hS : 0 ≤ S)
    (h : ∀ u v : Fin n → ℝ, IsONPair u v → |secK R u v| ≤ S) :
    ∀ u v : Fin n → ℝ, |secK R u v| ≤ dot u u * dot v v * S := by
  intro u v
  by_cases hu : u = 0
  · subst hu
    have hd : dot (0 : Fin n → ℝ) (0 : Fin n → ℝ) = 0 := by simp [dot]
    rw [secK_zero_left, abs_zero, hd, zero_mul, zero_mul]
  · have hduu : 0 < dot u u := dot_self_pos hu
    set c : ℝ := dot v u / dot u u with hc
    set w : Fin n → ℝ := v - c • u with hw
    have huw : dot u w = 0 := by
      rw [hw, dot_sub_right', dot_smul_right', hc, div_mul_cancel₀ _ hduu.ne', dot_comm u v]
      ring
    have hsecK : secK R u v = secK R u w := by
      rw [hw]
      exact (secK_sub_smul_second R hR u v c).symm
    by_cases hw0 : w = 0
    · rw [hsecK, hw0, secK_zero_right, abs_zero]
      exact mul_nonneg (mul_nonneg hduu.le (dot_self_nonneg v)) hS
    · have hdww : 0 < dot w w := dot_self_pos hw0
      have hsu : Real.sqrt (dot u u) ≠ 0 := (Real.sqrt_pos.mpr hduu).ne'
      have hsw : Real.sqrt (dot w w) ≠ 0 := (Real.sqrt_pos.mpr hdww).ne'
      set a : ℝ := (Real.sqrt (dot u u))⁻¹ with ha
      set b : ℝ := (Real.sqrt (dot w w))⁻¹ with hb
      have ha0 : a ≠ 0 := by rw [ha]; exact inv_ne_zero hsu
      have hb0 : b ≠ 0 := by rw [hb]; exact inv_ne_zero hsw
      have ha2 : a ^ 2 * dot u u = 1 := by
        rw [ha, inv_pow, Real.sq_sqrt hduu.le, inv_mul_cancel₀ hduu.ne']
      have hb2 : b ^ 2 * dot w w = 1 := by
        rw [hb, inv_pow, Real.sq_sqrt hdww.le, inv_mul_cancel₀ hdww.ne']
      have hainv : (a⁻¹) ^ 2 = dot u u := by
        have h' : a ^ 2 = (dot u u)⁻¹ := eq_inv_of_mul_eq_one_left ha2
        rw [inv_pow, h', inv_inv]
      have hbinv : (b⁻¹) ^ 2 = dot w w := by
        have h' : b ^ 2 = (dot w w)⁻¹ := eq_inv_of_mul_eq_one_left hb2
        rw [inv_pow, h', inv_inv]
      set uh : Fin n → ℝ := a • u with huh
      set wh : Fin n → ℝ := b • w with hwh
      have hON : IsONPair uh wh := by
        refine ⟨?_, ?_, ?_⟩
        · rw [huh, dot_smul_smul]
          simpa [sq] using ha2
        · rw [hwh, dot_smul_smul]
          simpa [sq] using hb2
        · rw [huh, hwh, dot_smul_smul, huw, mul_zero]
      have hkey : secK R u v = dot u u * dot w w * secK R uh wh := by
        have hu_eq : u = a⁻¹ • uh := by rw [huh, smul_smul, inv_mul_cancel₀ ha0, one_smul]
        have hw_eq : w = b⁻¹ • wh := by rw [hwh, smul_smul, inv_mul_cancel₀ hb0, one_smul]
        have h1 : secK R u w = (a⁻¹) ^ 2 * (b⁻¹) ^ 2 * secK R uh wh := by
          rw [hu_eq, hw_eq, secK_smul_smul]
        rw [hsecK, h1, hainv, hbinv]
      have hdww_le : dot w w ≤ dot v v := by
        have h1 : c * dot u u = dot v u := by rw [hc, div_mul_cancel₀ _ hduu.ne']
        have h4 : dot w w = dot v v - c ^ 2 * dot u u := by
          rw [hw, dot_sub_sub, dot_smul_right', dot_smul_left', dot_smul_smul, dot_comm u v,
            ← h1]
          ring
        have h3 : 0 ≤ c ^ 2 * dot u u := mul_nonneg (sq_nonneg c) hduu.le
        linarith [h4, h3]
      calc |secK R u v| = dot u u * dot w w * |secK R uh wh| := by
            rw [hkey, abs_mul, abs_mul, abs_of_pos hduu, abs_of_pos hdww]
        _ ≤ dot u u * dot w w * S :=
            mul_le_mul_of_nonneg_left (h uh wh hON) (mul_nonneg hduu.le hdww.le)
        _ ≤ dot u u * dot v v * S :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdww_le hduu.le) hS

/-- **Every component is at most eight times the sectional-curvature threshold.**  If
`|secK R u v| ≤ dot u u * dot v v * S` for all `u v` (`S ≥ 0`), then `|R i j k l| ≤ 8 * S`.

The polarization identity `R4_eq_polarize` expresses `R i j k l = R4 R (stdB i) (stdB j) (stdB k)
(stdB l)` through eight `secK`-values on pairs `(stdB ± stdB, stdB ± stdB)`, whose `dot`-squares are
at most `4`; each is therefore at most `16 * S`, and `|2 polU + polV| / 24 ≤ (2 * 64 + 64) S / 24
= 8 S`. -/
theorem abs_R4_stdB_le_of_secK_bound {R : Curv4 n} (hR : IsAlgCurv R) {S : ℝ} (hS : 0 ≤ S)
    (h : ∀ u v : Fin n → ℝ, |secK R u v| ≤ dot u u * dot v v * S) :
    ∀ i j k l : Fin n, |R i j k l| ≤ 8 * S := by
  intro i j k l
  have hterm : ∀ p q : Fin n → ℝ, dot p p ≤ 4 → dot q q ≤ 4 → |secK R p q| ≤ 16 * S := by
    intro p q hp hq
    have h1 := h p q
    have h2 : dot p p * dot q q ≤ 4 * 4 := by
      nlinarith [hp, hq, dot_self_nonneg p, dot_self_nonneg q]
    have h3 : dot p p * dot q q * S ≤ 16 * S := by nlinarith [h2, hS]
    linarith
  have hpolU : |polU R (stdB n i) (stdB n j) (stdB n k) (stdB n l)| ≤ 64 * S := by
    have t1 := hterm _ _ (dot_stdB_add_self_le i k) (dot_stdB_add_self_le j l)
    have t2 := hterm _ _ (dot_stdB_add_self_le i k) (dot_stdB_sub_self_le j l)
    have t3 := hterm _ _ (dot_stdB_sub_self_le i k) (dot_stdB_add_self_le j l)
    have t4 := hterm _ _ (dot_stdB_sub_self_le i k) (dot_stdB_sub_self_le j l)
    have h4 := abs_sub_sub_add_le
      (secK R (stdB n i + stdB n k) (stdB n j + stdB n l))
      (secK R (stdB n i + stdB n k) (stdB n j - stdB n l))
      (secK R (stdB n i - stdB n k) (stdB n j + stdB n l))
      (secK R (stdB n i - stdB n k) (stdB n j - stdB n l))
    simp only [polU]
    linarith
  have hpolV : |polV R (stdB n i) (stdB n j) (stdB n k) (stdB n l)| ≤ 64 * S := by
    have t1 := hterm _ _ (dot_stdB_add_self_le i j) (dot_stdB_add_self_le k l)
    have t2 := hterm _ _ (dot_stdB_add_self_le i j) (dot_stdB_sub_self_le k l)
    have t3 := hterm _ _ (dot_stdB_sub_self_le i j) (dot_stdB_add_self_le k l)
    have t4 := hterm _ _ (dot_stdB_sub_self_le i j) (dot_stdB_sub_self_le k l)
    have h4 := abs_sub_sub_add_le
      (secK R (stdB n i + stdB n j) (stdB n k + stdB n l))
      (secK R (stdB n i + stdB n j) (stdB n k - stdB n l))
      (secK R (stdB n i - stdB n j) (stdB n k + stdB n l))
      (secK R (stdB n i - stdB n j) (stdB n k - stdB n l))
    simp only [polV]
    linarith
  have hpolar := R4_eq_polarize R hR (stdB n i) (stdB n j) (stdB n k) (stdB n l)
  calc |R i j k l| = |R4 R (stdB n i) (stdB n j) (stdB n k) (stdB n l)| := by rw [R4_stdB]
    _ = |(2 * polU R (stdB n i) (stdB n j) (stdB n k) (stdB n l)
            + polV R (stdB n i) (stdB n j) (stdB n k) (stdB n l)) / 24| := by rw [hpolar]
    _ ≤ (2 * |polU R (stdB n i) (stdB n j) (stdB n k) (stdB n l)|
          + |polV R (stdB n i) (stdB n j) (stdB n k) (stdB n l)|) / 24 := by
        have h1 : |2 * polU R (stdB n i) (stdB n j) (stdB n k) (stdB n l)
              + polV R (stdB n i) (stdB n j) (stdB n k) (stdB n l)|
            ≤ 2 * |polU R (stdB n i) (stdB n j) (stdB n k) (stdB n l)|
              + |polV R (stdB n i) (stdB n j) (stdB n k) (stdB n l)| := by
          have h' := abs_add_le
            (2 * polU R (stdB n i) (stdB n j) (stdB n k) (stdB n l))
            (polV R (stdB n i) (stdB n j) (stdB n k) (stdB n l))
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h'
          simpa using h'
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 24)]
        linarith
    _ ≤ (2 * (64 * S) + 64 * S) / 24 := by
        have h1 : 2 * |polU R (stdB n i) (stdB n j) (stdB n k) (stdB n l)|
              + |polV R (stdB n i) (stdB n j) (stdB n k) (stdB n l)|
            ≤ 2 * (64 * S) + 64 * S := by linarith [hpolU, hpolV]
        have h2 := div_le_div_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 24)
        simpa using h2
    _ = 8 * S := by ring

/-! ## The component bound for a `δ`-pinched algebraic curvature tensor -/

/-- **The scalar curvature of a tensor with nonnegative sectional curvature is nonnegative.** -/
theorem scalAlg_nonneg_of_isONPair_nonneg {R : Curv4 n} (hR : IsAlgCurv R)
    (h : ∀ u v : Fin n → ℝ, IsONPair u v → 0 ≤ secK R u v) : 0 ≤ scalAlg R := by
  rw [← scalAlg_eq_sum_offDiag hR]
  refine Finset.sum_nonneg fun p hp => ?_
  have hpne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
  have h1 := h (stdB n p.1) (stdB n p.2) (isONPair_stdB hpne)
  rwa [secK_stdB] at h1

/-- **Component bound for a `δ`-pinched algebraic curvature tensor** (`0 < δ < 1`, `n ≥ 2`).

Every sectional curvature of such an `R` is nonnegative and at most
`scalAlg R / (δ n (n-1))`, and the polarization identity then gives
`|R i j k l| ≤ 8 scalAlg R / (δ n (n-1))` for every component. -/
theorem pinched_component_le {R : Curv4 n} (hn : 2 ≤ n) (hR : IsAlgCurv R) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hpin : IsPinchedAlg δ R) :
    0 ≤ scalAlg R ∧ ∀ i j k l : Fin n,
      |R i j k l| ≤ 8 / (δ * ((n : ℝ) * ((n : ℝ) - 1))) * scalAlg R := by
  have hD : 0 < (n : ℝ) * ((n : ℝ) - 1) := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hδD : 0 < δ * ((n : ℝ) * ((n : ℝ) - 1)) := mul_pos hδ hD
  -- every sectional curvature (of an orthonormal pair) is nonnegative
  have hnonneg : ∀ u v : Fin n → ℝ, IsONPair u v → 0 ≤ secK R u v := by
    intro u v huv
    have h := hpin u v u v huv huv
    nlinarith [h, hδ1]
  have hscal : 0 ≤ scalAlg R := scalAlg_nonneg_of_isONPair_nonneg hR hnonneg
  -- an orthonormal pair of minimal sectional curvature
  obtain ⟨u₀, v₀, hu₀v₀, hle₀⟩ := exists_isONPair_secK_le_scalAlg_div hn hR
  -- every orthonormal pair has sectional curvature in `[0, scalAlg R / (δ n (n-1))]`
  have hbound : ∀ u v : Fin n → ℝ, IsONPair u v →
      |secK R u v| ≤ scalAlg R / (δ * ((n : ℝ) * ((n : ℝ) - 1))) := by
    intro u v huv
    have h1 : δ * secK R u v ≤ secK R u₀ v₀ := hpin u₀ v₀ u v hu₀v₀ huv
    have h2 : δ * secK R u v * ((n : ℝ) * ((n : ℝ) - 1)) ≤ scalAlg R :=
      calc δ * secK R u v * ((n : ℝ) * ((n : ℝ) - 1))
          ≤ (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) * ((n : ℝ) * ((n : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_right (le_trans h1 hle₀) hD.le
        _ = scalAlg R := div_mul_cancel₀ _ hD.ne'
    rw [abs_of_nonneg (hnonneg u v huv), le_div_iff₀ hδD]
    nlinarith [h2]
  have habs := abs_secK_le_of_isONPair_abs_le hR (div_nonneg hscal hδD.le) hbound
  have hcomp := abs_R4_stdB_le_of_secK_bound hR (div_nonneg hscal hδD.le) habs
  refine ⟨hscal, fun i j k l => ?_⟩
  have h1 := hcomp i j k l
  have h2 : 8 * (scalAlg R / (δ * ((n : ℝ) * ((n : ℝ) - 1))))
      = 8 / (δ * ((n : ℝ) * ((n : ℝ) - 1))) * scalAlg R := by ring
  linarith [h1, h2]

/-! ## The component bound for a pinching set -/

/-- **Component bound for a pinching set.**  Every component of a curvature array in a pinching set is bounded by a fixed linear function of the scalar curvature.  This is a re-request of `Submission.Work.Diff.L.pinchingSet_component_bound`, whose prover never wrote a proof down.  (Route: `IsPinchingSet` bounds the non-`δ`-pinched part of `F`; `δ`-pinching with `δ < 1` forces all sectional curvatures to be nonnegative, and the polarization identity of `Submission.Work.Diff.L.PinDefs` — `R4 R x y z w = (2 * Psi R x y z w + Psi R y z x w)/24` with `Psi` a combination of sectional curvatures — bounds every component by a multiple of the maximal sectional curvature, which is at most `scalAlg/2`.  The bounded non-pinched part contributes the additive constant.) -/
theorem pinchingSet_component_bound_v2 {n : ℕ} {F : Set (Submission.Diff.Alg.Curv4 n)}
    (hF : Submission.Diff.Alg.IsPinchingSet F) :
    ∃ c C₀ : ℝ, 0 < c ∧ ∀ R ∈ F, ∀ i j k l : Fin n,
      |R i j k l| ≤ c * Submission.Diff.Alg.scalAlg R + C₀ := by
  classical
  by_cases hn : 2 ≤ n
  · -- the non-`δ`-pinched part of `F` is bounded (`δ = 1/2`)
    obtain ⟨r₀, hr₀⟩ := (isBounded_iff_subset_ball (0 : Curv4 n)).mp (hF.2 (1 / 2) (by norm_num))
    set r : ℝ := |r₀| with hrdef
    have hrnn : 0 ≤ r := abs_nonneg r₀
    have hr : ∀ R ∈ F, ¬ IsPinchedAlg (1 / 2) R → ‖R‖ < r := by
      intro R hRF hnp
      have h1 : dist R 0 < r₀ := hr₀ ⟨hRF, hnp⟩
      calc ‖R‖ = dist R 0 := by rw [dist_eq_norm]; simp
        _ < r₀ := h1
        _ ≤ r := le_abs_self r₀
    have hD : 0 < (n : ℝ) * ((n : ℝ) - 1) := by
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
    set K : ℝ := 8 / ((1 / 2) * ((n : ℝ) * ((n : ℝ) - 1))) with hKdef
    have hKpos : 0 < K := by rw [hKdef]; positivity
    set C₀ : ℝ := r + (K + 1) * ((n : ℝ) ^ 2 * r) with hC₀def
    have hC₀nn : 0 ≤ C₀ := by
      rw [hC₀def]
      have h1 : 0 ≤ (n : ℝ) ^ 2 * r := mul_nonneg (sq_nonneg _) hrnn
      nlinarith [hKpos, h1, hrnn]
    refine ⟨K + 1, C₀, by linarith, ?_⟩
    intro R hRF i j k l
    have hAlg : IsAlgCurv R := hF.1.2.2.1 R hRF
    by_cases hpin : IsPinchedAlg (1 / 2) R
    · -- `1/2`-pinched: the polarization bound, upgraded to the constant `K`
      obtain ⟨hscal, hcomp⟩ := pinched_component_le hn hAlg (by norm_num) (by norm_num) hpin
      have h1 : |R i j k l| ≤ K * scalAlg R := by
        rw [hKdef]
        exact hcomp i j k l
      calc |R i j k l| ≤ K * scalAlg R := h1
        _ ≤ (K + 1) * scalAlg R := by nlinarith [hscal]
        _ ≤ (K + 1) * scalAlg R + C₀ := by linarith [hC₀nn]
    · -- not `1/2`-pinched: bounded by `r`, absorbed by the additive constant
      have hRr : ‖R‖ < r := hr R hRF hpin
      have hscal_lower : -((n : ℝ) ^ 2 * r) ≤ scalAlg R := by
        have h1 : |scalAlg R| ≤ (n : ℝ) ^ 2 * ‖R‖ := abs_scalAlg_le R
        have h2 : (n : ℝ) ^ 2 * ‖R‖ ≤ (n : ℝ) ^ 2 * r :=
          mul_le_mul_of_nonneg_left (le_of_lt hRr) (sq_nonneg _)
        have h3 : -scalAlg R ≤ |scalAlg R| := neg_le_abs (scalAlg R)
        linarith
      calc |R i j k l| ≤ ‖R‖ := Curv4.abs_apply_le_norm R i j k l
        _ ≤ r := le_of_lt hRr
        _ = (K + 1) * (-((n : ℝ) ^ 2 * r)) + C₀ := by rw [hC₀def]; ring
        _ ≤ (K + 1) * scalAlg R + C₀ := by
            have h5 : 0 ≤ K + 1 := by linarith [hKpos]
            have h6 := mul_le_mul_of_nonneg_left hscal_lower h5
            linarith
  · -- `n ≤ 1`: every element of `F` is an algebraic curvature tensor in dimension at most one,
    -- hence vanishes
    have hn1 : n ≤ 1 := by omega
    refine ⟨1, 0, one_pos, ?_⟩
    intro R hRF i j k l
    have hAlg : IsAlgCurv R := hF.1.2.2.1 R hRF
    have hall : ∀ a b c d : Fin n, R a b c d = 0 := by
      intro a b c d
      have hab : a = b := by ext; omega
      have hac : a = c := by ext; omega
      have had : a = d := by ext; omega
      rw [← hab, ← hac, ← had]
      have h := hAlg.1 a a a a
      linarith
    have hscal : scalAlg R = 0 := by
      simp only [scalAlg]
      exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => hall a b a b
    rw [hall i j k l, abs_zero, hscal]
    norm_num

end Work.Diff.L
