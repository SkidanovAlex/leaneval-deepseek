import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

open Filter

/-- Triangle inequality in the form `|a - b| ≤ |a| + |b|`. -/
private lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]
  calc |a + -b| ≤ |a| + |-b| := abs_add_le _ _
    _ = |a| + |b| := by rw [abs_neg]

/-- Triangle inequality for a sum of three terms. -/
private lemma abs_add3_le (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
  calc |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
    _ ≤ (|a| + |b|) + |c| := by linarith [abs_add_le a b]

/-- If `|x| * |a| ≤ U`, `0 < δ` and `δ ≤ |a|`, then `|x| ≤ U / δ`. -/
private lemma abs_le_div_of_mul_abs_le {x U a δ : ℝ} (hδ : 0 < δ) (ha : δ ≤ |a|)
    (h : |x| * |a| ≤ U) : |x| ≤ U / δ := by
  rw [le_div_iff₀ hδ]
  exact le_trans (mul_le_mul_of_nonneg_left ha (abs_nonneg x)) h

/-- A list of length `≤ 2` is empty, a singleton, or a pair. -/
private lemma length_le_two_cases {d : ℕ} (l : List (Fin d)) (h : l.length ≤ 2) :
    l = [] ∨ (∃ p, l = [p]) ∨ (∃ q p, l = [q, p]) := by
  cases l with
  | nil => exact Or.inl rfl
  | cons p t =>
    cases t with
    | nil => exact Or.inr (Or.inl ⟨p, rfl⟩)
    | cons q t =>
      cases t with
      | nil => exact Or.inr (Or.inr ⟨p, q, rfl⟩)
      | cons s t =>
        simp only [List.length_cons] at h
        omega

/-- The pure arithmetic behind `pdRList_div_le`: with `B = S0 + S1 + S2` and
`D = r + (K1 + K2) r² + K1² r³` (all quantities nonnegative), the three quantities
`S0 r`, `S1 r + S0 K1 r²` and `S2 r + 2 S1 K1 r² + 2 S0 K1² r³ + S0 K2 r²` are all at most
`8 B D`. -/
private lemma div_arith {S0 S1 S2 K1 K2 r B D : ℝ}
    (hS0 : 0 ≤ S0) (hS1 : 0 ≤ S1) (hS2 : 0 ≤ S2) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hr : 0 ≤ r) (hB : B = S0 + S1 + S2) (hD : D = r + (K1 + K2) * r ^ 2 + K1 ^ 2 * r ^ 3) :
    S0 * r ≤ 8 * B * D ∧
    (S1 * r + S0 * K1 * r ^ 2 ≤ 8 * B * D) ∧
    (S2 * r + 2 * S1 * K1 * r ^ 2 + 2 * S0 * K1 ^ 2 * r ^ 3 + S0 * K2 * r ^ 2 ≤ 8 * B * D) := by
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; linarith
  have hr2 : (0 : ℝ) ≤ r ^ 2 := sq_nonneg r
  have hr3 : (0 : ℝ) ≤ r ^ 3 := by
    calc (0 : ℝ) ≤ r ^ 2 * r := mul_nonneg hr2 hr
      _ = r ^ 3 := by ring
  have hrD : r ≤ D := by
    rw [hD]
    nlinarith [mul_nonneg (add_nonneg hK1 hK2) hr2, mul_nonneg (sq_nonneg K1) hr3]
  have hS0B : S0 ≤ B := by rw [hB]; linarith
  have hS1B : S1 ≤ B := by rw [hB]; linarith
  have hS2B : S2 ≤ B := by rw [hB]; linarith
  have hK1rr : K1 * r ^ 2 ≤ D := by
    rw [hD]
    nlinarith [mul_nonneg hK2 hr2, mul_nonneg (sq_nonneg K1) hr3, hr, mul_nonneg hK1 hr2]
  have hK2rr : K2 * r ^ 2 ≤ D := by
    rw [hD]
    nlinarith [mul_nonneg hK1 hr2, mul_nonneg (sq_nonneg K1) hr3, hr, mul_nonneg hK2 hr2]
  have hK1r3 : K1 ^ 2 * r ^ 3 ≤ D := by
    rw [hD]
    nlinarith [mul_nonneg hK1 hr2, mul_nonneg hK2 hr2, hr, mul_nonneg (sq_nonneg K1) hr3]
  refine ⟨?_, ?_, ?_⟩
  · have h1 : S0 * r ≤ B * r := mul_le_mul_of_nonneg_right hS0B hr
    have h2 : B * r ≤ B * D := mul_le_mul_of_nonneg_left hrD hB0
    have h3 : (0 : ℝ) ≤ B * D := mul_nonneg hB0 hD0
    nlinarith
  · have h1 : S1 * r ≤ B * D :=
      le_trans (mul_le_mul_of_nonneg_right hS1B hr) (mul_le_mul_of_nonneg_left hrD hB0)
    have h2 : S0 * K1 * r ^ 2 ≤ B * D := by
      rw [mul_assoc]
      exact mul_le_mul hS0B hK1rr (mul_nonneg hK1 hr2) hB0
    have h3 : (0 : ℝ) ≤ B * D := mul_nonneg hB0 hD0
    nlinarith
  · have h3 : S2 * r ≤ B * D :=
      le_trans (mul_le_mul_of_nonneg_right hS2B hr) (mul_le_mul_of_nonneg_left hrD hB0)
    have h4 : S1 * K1 * r ^ 2 ≤ B * D := by
      rw [mul_assoc]
      exact mul_le_mul hS1B hK1rr (mul_nonneg hK1 hr2) hB0
    have h5 : S0 * K1 ^ 2 * r ^ 3 ≤ B * D := by
      rw [mul_assoc]
      exact mul_le_mul hS0B hK1r3 (mul_nonneg (sq_nonneg K1) hr3) hB0
    have h6 : S0 * K2 * r ^ 2 ≤ B * D := by
      rw [mul_assoc]
      exact mul_le_mul hS0B hK2rr (mul_nonneg hK2 hr2) hB0
    nlinarith [h3, h4, h5, h6, hD0, hB0]

/-- **First-order quotient identity.**  If `A` and `R` are `C²` at `y` and `A y ≠ 0`, then
differentiating the identity `A · (R/A) = R` gives
`A y * ∂_p (R/A) y + (R y / A y) * ∂_p A y = ∂_p R y`. -/
lemma pdR_div_mul_identity {d : ℕ} {A R : (Fin d → ℝ) → ℝ} {y : Fin d → ℝ}
    (hA : ContDiffAt ℝ 2 A y) (hR : ContDiffAt ℝ 2 R y) (hy : A y ≠ 0) (p : Fin d) :
    A y * Work.Diff.STE.pdR p (fun w => R w / A w) y + (R y / A y) * Work.Diff.STE.pdR p A y
      = Work.Diff.STE.pdR p R y := by
  have hdA : DifferentiableAt ℝ A y := hA.differentiableAt (by norm_num)
  have hdR : DifferentiableAt ℝ R y := hR.differentiableAt (by norm_num)
  have hdQ : DifferentiableAt ℝ (fun w => R w / A w) y :=
    (hR.div hA hy).differentiableAt (by norm_num)
  have hU : ∀ᶠ w in nhds y, A w ≠ 0 := hdA.continuousAt.eventually_ne hy
  have heq : (fun w => A w * (R w / A w)) =ᶠ[nhds y] R := by
    filter_upwards [hU] with w hw
    rw [mul_div_cancel₀ (R w) hw]
  have hmain : fderiv ℝ (fun w => A w * (R w / A w)) y = fderiv ℝ R y := heq.fderiv_eq
  rw [fderiv_fun_mul hdA hdQ] at hmain
  have h2 := congrArg (fun L : (Fin d → ℝ) →L[ℝ] ℝ => L (Pi.single p 1)) hmain
  simpa [Work.Diff.STE.pdR, smul_eq_mul] using h2

/-- **Second-order quotient identity.**  Differentiating the first-order identity of
`pdR_div_mul_identity` once more along the coordinate `q` gives the quotient rule for the second
partial derivatives of `R/A`:
`A z * ∂_q∂_p (R/A) z + ∂_p(R/A) z * ∂_q A z + (R z/A z) * ∂_q∂_p A z + ∂_p A z * ∂_q (R/A) z
 = ∂_q∂_p R z`. -/
lemma pdR2_div_identity {d : ℕ} {A R : (Fin d → ℝ) → ℝ} {z : Fin d → ℝ}
    (hA : ContDiffAt ℝ 2 A z) (hR : ContDiffAt ℝ 2 R z) (hz : A z ≠ 0) (q p : Fin d) :
    A z * Work.Diff.STE.pdR q (Work.Diff.STE.pdR p (fun w => R w / A w)) z
      + (Work.Diff.STE.pdR p (fun w => R w / A w) z) * Work.Diff.STE.pdR q A z
      + (R z / A z) * Work.Diff.STE.pdR q (Work.Diff.STE.pdR p A) z
      + (Work.Diff.STE.pdR p A z) * Work.Diff.STE.pdR q (fun w => R w / A w) z
      = Work.Diff.STE.pdR q (Work.Diff.STE.pdR p R) z := by
  have hQ2 : ContDiffAt ℝ 2 (fun w => R w / A w) z := hR.div hA hz
  have hdA : DifferentiableAt ℝ A z := hA.differentiableAt (by norm_num)
  have hdQ : DifferentiableAt ℝ (fun w => R w / A w) z := hQ2.differentiableAt (by norm_num)
  have hd2Q : DifferentiableAt ℝ (fderiv ℝ (fun w => R w / A w)) z :=
    (hQ2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd2A : DifferentiableAt ℝ (fderiv ℝ A) z :=
    (hA.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdPQ : DifferentiableAt ℝ (Work.Diff.STE.pdR p (fun w => R w / A w)) z := by
    have h :=
      (hd2Q.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single p (1:ℝ)) z)).differentiableAt
    show DifferentiableAt ℝ (fun y => fderiv ℝ (fun w => R w / A w) y (Pi.single p (1:ℝ))) z
    exact h
  have hdPA : DifferentiableAt ℝ (Work.Diff.STE.pdR p A) z := by
    have h :=
      (hd2A.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single p (1:ℝ)) z)).differentiableAt
    show DifferentiableAt ℝ (fun y => fderiv ℝ A y (Pi.single p (1:ℝ))) z
    exact h
  have hnev : ∀ᶠ y in nhds z, A y ≠ 0 := hdA.continuousAt.eventually_ne hz
  have hevA : ∀ᶠ y in nhds z, ContDiffAt ℝ 2 A y := hA.eventually (by norm_num)
  have hevR : ∀ᶠ y in nhds z, ContDiffAt ℝ 2 R y := hR.eventually (by norm_num)
  have hev : ((fun y => A y * Work.Diff.STE.pdR p (fun w => R w / A w) y)
      + (fun y => (R y / A y) * Work.Diff.STE.pdR p A y))
      =ᶠ[nhds z] (Work.Diff.STE.pdR p R) := by
    filter_upwards [hnev, hevA, hevR] with y hy hyA hyR
    exact pdR_div_mul_identity hyA hyR hy p
  have h1 : HasFDerivAt (fun y => A y * Work.Diff.STE.pdR p (fun w => R w / A w) y)
      (A z • fderiv ℝ (Work.Diff.STE.pdR p (fun w => R w / A w)) z
        + (Work.Diff.STE.pdR p (fun w => R w / A w) z) • fderiv ℝ A z) z :=
    hdA.hasFDerivAt.mul hdPQ.hasFDerivAt
  have h2 : HasFDerivAt (fun y => (R y / A y) * Work.Diff.STE.pdR p A y)
      ((R z / A z) • fderiv ℝ (Work.Diff.STE.pdR p A) z
        + (Work.Diff.STE.pdR p A z) • fderiv ℝ (fun w => R w / A w) z) z :=
    hdQ.hasFDerivAt.mul hdPA.hasFDerivAt
  have hsum : HasFDerivAt ((fun y => A y * Work.Diff.STE.pdR p (fun w => R w / A w) y)
      + (fun y => (R y / A y) * Work.Diff.STE.pdR p A y))
      ((A z • fderiv ℝ (Work.Diff.STE.pdR p (fun w => R w / A w)) z
        + (Work.Diff.STE.pdR p (fun w => R w / A w) z) • fderiv ℝ A z)
       + ((R z / A z) • fderiv ℝ (Work.Diff.STE.pdR p A) z
        + (Work.Diff.STE.pdR p A z) • fderiv ℝ (fun w => R w / A w) z)) z := h1.add h2
  have hfe : fderiv ℝ ((fun y => A y * Work.Diff.STE.pdR p (fun w => R w / A w) y)
      + (fun y => (R y / A y) * Work.Diff.STE.pdR p A y)) z
      = fderiv ℝ (Work.Diff.STE.pdR p R) z := hev.fderiv_eq
  have h3 := congrArg (fun L : (Fin d → ℝ) →L[ℝ] ℝ => L (Pi.single q 1)) hfe
  rw [hsum.fderiv] at h3
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at h3
  simpa only [Work.Diff.STE.pdR, add_assoc] using h3

/-- Division/Leibniz bound for the jets of order `≤ 2` of a quotient `R / A`.

If `A` and `R` are `C²` at `z`, `A z ≠ 0`, `K1, K2 ≥ 0` bound the first and the second directional
derivatives of `A` at `z`, and `δ > 0` bounds `|A z|` from below, then every iterated partial
derivative of `R / A` of order `≤ 2` at `z` is bounded by the corresponding derivatives of `R`
(up to order 2) times `1/δ + (K1+K2)/δ² + K1²/δ³`.

Route.  `R / A` is `C²` at `z` by `ContDiffAt.div`; the three cases `l = []`, `[p]`, `[q,p]` are
the quotient rules
`(R/A) = R/A`,
`∂_p (R/A) = (∂_p R · A - R · ∂_p A)/A²`,
`∂_q ∂_p (R/A) = (∂_q∂_p R)/A - (∂_p R ∂_q A + ∂_q R ∂_p A + R ∂_q∂_p A)/A² + 2 R ∂_p A ∂_q A/A³`.
Use `fderiv_div` (or `fderiv` of `f * (·)⁻¹` via `fderiv_mul`/`fderiv_inv`) and evaluate the
resulting linear maps at `Pi.single p 1`; bound each term with `|A z| ≥ δ`, `|∂A| ≤ K1`,
`|∂²A| ≤ K2` and `‖Pi.single p 1‖ = 1`.  Since `C` is existentially quantified (and may depend on
`d`), any numerical constant works. -/
theorem pdRList_div_le {d : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A R : (Fin d → ℝ) → ℝ) (z : Fin d → ℝ) (δ K1 K2 : ℝ),
      0 < δ → δ ≤ |A z| → 0 ≤ K1 → 0 ≤ K2 →
      (∀ p : Fin d, |Work.Diff.STE.pdR p A z| ≤ K1) →
      (∀ p q : Fin d, |Work.Diff.STE.pdR q (Work.Diff.STE.pdR p A) z| ≤ K2) →
      ContDiffAt ℝ 2 A z → ContDiffAt ℝ 2 R z →
      ∀ l : List (Fin d), l.length ≤ 2 →
        |Work.Diff.STE.pdRList l (fun y => R y / A y) z|
          ≤ C * (|R z| + ∑ p : Fin d, |Work.Diff.STE.pdR p R z|
              + ∑ p : Fin d, ∑ q : Fin d,
                  |Work.Diff.STE.pdR q (Work.Diff.STE.pdR p R) z|)
            * (1 / δ + (K1 + K2) / δ ^ 2 + K1 ^ 2 / δ ^ 3) := by
  refine ⟨8, by norm_num, ?_⟩
  intro A R z δ K1 K2 hδ hδA hK1 hK2 hbA hb2A hCA hCR l hl
  have hAz : A z ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hδA
    linarith
  set S0 : ℝ := |R z| with hS0
  set S1 : ℝ := ∑ p : Fin d, |Work.Diff.STE.pdR p R z| with hS1
  set S2 : ℝ := ∑ p : Fin d, ∑ q : Fin d,
    |Work.Diff.STE.pdR q (Work.Diff.STE.pdR p R) z| with hS2
  set r : ℝ := 1 / δ with hr
  have hDexp : r + (K1 + K2) / δ ^ 2 + K1 ^ 2 / δ ^ 3
      = r + (K1 + K2) * r ^ 2 + K1 ^ 2 * r ^ 3 := by
    rw [hr]
    field_simp
  rw [hDexp]
  set B : ℝ := S0 + S1 + S2 with hB
  set D : ℝ := r + (K1 + K2) * r ^ 2 + K1 ^ 2 * r ^ 3 with hD
  have hS0n : 0 ≤ S0 := by rw [hS0]; exact abs_nonneg _
  have hS1n : 0 ≤ S1 := by
    rw [hS1]; exact Finset.sum_nonneg (fun p _ => abs_nonneg _)
  have hS2n : 0 ≤ S2 := by
    rw [hS2]
    exact Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun q _ => abs_nonneg _))
  have hrn : 0 ≤ r := by rw [hr]; exact le_of_lt (one_div_pos.mpr hδ)
  have hR1 : ∀ p, |Work.Diff.STE.pdR p R z| ≤ S1 := by
    intro p
    rw [hS1]
    exact Finset.single_le_sum (f := fun i : Fin d => |Work.Diff.STE.pdR i R z|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ p)
  have hR2 : ∀ p q, |Work.Diff.STE.pdR q (Work.Diff.STE.pdR p R) z| ≤ S2 := by
    intro p q
    rw [hS2]
    refine le_trans (Finset.single_le_sum (f := fun q' : Fin d =>
        |Work.Diff.STE.pdR q' (Work.Diff.STE.pdR p R) z|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ q)) ?_
    exact Finset.single_le_sum (f := fun p' : Fin d => ∑ q' : Fin d,
        |Work.Diff.STE.pdR q' (Work.Diff.STE.pdR p' R) z|)
      (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) (Finset.mem_univ p)
  have harith := div_arith hS0n hS1n hS2n hK1 hK2 hrn hB hD
  -- first order
  have hQ0 : |(fun y => R y / A y) z| ≤ S0 * r := by
    have h1 : |(fun y => R y / A y) z| = |R z| * (1 / |A z|) := by
      rw [abs_div, one_div]
      ring
    rw [h1, hS0, hr]
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hδ hδA) hS0n
  have hQ1 : ∀ p, |Work.Diff.STE.pdR p (fun y => R y / A y) z|
      ≤ S1 * r + S0 * K1 * r ^ 2 := by
    intro p
    have hid := pdR_div_mul_identity hCA hCR hAz p
    have hPz : Work.Diff.STE.pdR p (fun y => R y / A y) z * A z
        = Work.Diff.STE.pdR p R z - (R z / A z) * Work.Diff.STE.pdR p A z := by
      nlinarith [hid]
    have hkey : |Work.Diff.STE.pdR p (fun y => R y / A y) z| * |A z|
        ≤ S1 + (S0 * r) * K1 := by
      rw [← abs_mul, hPz]
      refine le_trans (abs_sub_le_abs_add _ _) ?_
      rw [abs_mul]
      exact add_le_add (hR1 p) (mul_le_mul hQ0 (hbA p) (abs_nonneg _) (mul_nonneg hS0n hrn))
    have hstep := abs_le_div_of_mul_abs_le hδ hδA hkey
    have hconv : (S1 + (S0 * r) * K1) / δ = S1 * r + S0 * K1 * r ^ 2 := by
      rw [hr, div_eq_mul_inv, one_div]
      ring
    linarith [hstep, hconv]
  -- second order
  have hQ2b : ∀ p q, |Work.Diff.STE.pdR q (Work.Diff.STE.pdR p (fun y => R y / A y)) z|
      ≤ S2 * r + 2 * S1 * K1 * r ^ 2 + 2 * S0 * K1 ^ 2 * r ^ 3 + S0 * K2 * r ^ 2 := by
    intro p q
    have hid := pdR2_div_identity hCA hCR hAz q p
    have hPz : Work.Diff.STE.pdR q (Work.Diff.STE.pdR p (fun y => R y / A y)) z * A z
        = Work.Diff.STE.pdR q (Work.Diff.STE.pdR p R) z
          - ((Work.Diff.STE.pdR p (fun y => R y / A y) z) * (Work.Diff.STE.pdR q A z)
             + (R z / A z) * (Work.Diff.STE.pdR q (Work.Diff.STE.pdR p A) z)
             + (Work.Diff.STE.pdR p A z)
                * (Work.Diff.STE.pdR q (fun y => R y / A y) z)) := by
      nlinarith [hid]
    have hkey : |Work.Diff.STE.pdR q (Work.Diff.STE.pdR p (fun y => R y / A y)) z| * |A z|
        ≤ S2 + ((S1 * r + S0 * K1 * r ^ 2) * K1 + (S0 * r) * K2
            + K1 * (S1 * r + S0 * K1 * r ^ 2)) := by
      rw [← abs_mul, hPz]
      refine le_trans (abs_sub_le_abs_add _ _) ?_
      refine le_trans (add_le_add le_rfl (abs_add3_le _ _ _)) ?_
      rw [abs_mul, abs_mul, abs_mul]
      refine add_le_add (hR2 p q) ?_
      refine add_le_add (add_le_add ?_ ?_) ?_
      · exact mul_le_mul (hQ1 p) (hbA q) (abs_nonneg _)
          (add_nonneg (mul_nonneg hS1n hrn) (mul_nonneg (mul_nonneg hS0n hK1) (sq_nonneg r)))
      · exact mul_le_mul hQ0 (hb2A p q) (abs_nonneg _) (mul_nonneg hS0n hrn)
      · exact mul_le_mul (hbA p) (hQ1 q) (abs_nonneg _) hK1
    have hstep := abs_le_div_of_mul_abs_le hδ hδA hkey
    have hconv : (S2 + ((S1 * r + S0 * K1 * r ^ 2) * K1 + (S0 * r) * K2
          + K1 * (S1 * r + S0 * K1 * r ^ 2))) / δ
        = S2 * r + 2 * S1 * K1 * r ^ 2 + 2 * S0 * K1 ^ 2 * r ^ 3 + S0 * K2 * r ^ 2 := by
      rw [hr, div_eq_mul_inv, one_div]
      ring
    linarith [hstep, hconv]
  rcases length_le_two_cases l hl with rfl | ⟨p, rfl⟩ | ⟨q, p, rfl⟩
  · show |(fun y => R y / A y) z| ≤ 8 * B * D
    exact le_trans hQ0 harith.1
  · show |Work.Diff.STE.pdR p (fun y => R y / A y) z| ≤ 8 * B * D
    exact le_trans (hQ1 p) harith.2.1
  · show |Work.Diff.STE.pdR q (Work.Diff.STE.pdR p (fun y => R y / A y)) z| ≤ 8 * B * D
    exact le_trans (hQ2b p q) harith.2.2

end Work.Diff.STE.Lead
