import Mathlib
import Submission.Work.Mostow.mlDefs
import Submission.Work.Mostow.absCoshSubCoshLe

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## Elementary one-dimensional bounds for `sinh` and `cosh` -/

/-- `sinh` is `cosh M`-Lipschitz on `[0, M]`.  Same proof as `absCoshSubCoshLe`: the derivative
of `sinh` is `cosh`, which is monotone on `[0, ∞)`. -/
lemma absSinhSubSinhLe (M a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (haM : a ≤ M) (hbM : b ≤ M) :
    |Real.sinh a - Real.sinh b| ≤ Real.cosh M * |a - b| := by
  have hM : 0 ≤ M := le_trans ha haM
  have hbound : ∀ x ∈ Set.Icc (0 : ℝ) M, ‖deriv Real.sinh x‖ ≤ Real.cosh M := by
    intro x hx
    rw [Real.deriv_sinh, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (Real.cosh_pos x))]
    exact (Real.cosh_le_cosh).mpr (by
      rw [abs_of_nonneg hx.1, abs_of_nonneg hM]
      exact hx.2)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := Real.sinh) (s := Set.Icc (0 : ℝ) M) (C := Real.cosh M)
    (fun x _ => Real.differentiableAt_sinh) hbound (convex_Icc 0 M) ⟨hb, hbM⟩ ⟨ha, haM⟩
  simpa only [Real.norm_eq_abs] using h

/-- For `0 ≤ d ≤ 1` one has `cosh d - 1 ≤ cosh 1 * d ^ 2`. -/
lemma coshSubOneLeSq (d : ℝ) (h0 : 0 ≤ d) (h1 : d ≤ 1) :
    Real.cosh d - 1 ≤ Real.cosh 1 * d ^ 2 := by
  have hsinh : Real.sinh d ≤ Real.cosh 1 * d := by
    have h := absSinhSubSinhLe 1 d 0 h0 le_rfl h1 zero_le_one
    have h1' : |Real.sinh d - Real.sinh 0| = Real.sinh d := by
      rw [Real.sinh_zero, sub_zero, abs_of_nonneg (Real.sinh_nonneg_iff.mpr h0)]
    have h2' : |d - (0 : ℝ)| = d := by rw [sub_zero, abs_of_nonneg h0]
    rw [h1', h2'] at h
    exact h
  have hcosh : Real.cosh d - 1 ≤ Real.sinh d * d := by
    have h := absCoshSubCoshLe d d 0 h0 le_rfl le_rfl h0
    have h1' : |Real.cosh d - Real.cosh 0| = Real.cosh d - 1 := by
      rw [Real.cosh_zero, abs_of_nonneg (by linarith [Real.one_le_cosh d])]
    have h2' : |d - (0 : ℝ)| = d := by rw [sub_zero, abs_of_nonneg h0]
    rw [h1', h2'] at h
    exact h
  nlinarith [hcosh, hsinh, h0]

/-- Key exact identity: with `ρ = ‖v - u‖`, `Δ = tpart v - tpart u` and `d = hdist u v` one has
`ρ ^ 2 - Δ ^ 2 = 2 * (cosh d - 1)`.  Both sides are the Minkowski norm of `hlift v - hlift u`. -/
lemma chartCloseSqIdentity (u v : E n) :
    ‖v - u‖ ^ 2 - (tpart v - tpart u) ^ 2 = 2 * (Real.cosh (hdist u v) - 1) := by
  rw [cosh_hdist]
  rw [norm_sub_sq_real]
  have h2 := Hyper.sq_tpart u
  have h3 := Hyper.sq_tpart v
  have h4 : inner ℝ v u = inner ℝ u v := (real_inner_comm v u).symm
  nlinarith [h2, h3, h4]

/-! Explicit comparison between the hyperbolic distance and the chart (Euclidean) coordinates on a
bounded chart region.

Key facts to use (from `Submission.Work.Mostow.Hyper` and `BaryBase`):
* `cosh_hdist_zero : Real.cosh (hdist 0 u) = tpart u` (so `‖u‖ = Real.sinh (hdist 0 u)` with
  `Hyper.sq_tpart` and `Real.sinh_sq`);
* the triangle inequality of `HypIsometryProp`, giving `|hdist 0 v - hdist 0 u| ≤ hdist u v`;
* the exact identity: with `ρ := ‖v - u‖`, `p := tpart u`, `q := tpart v`, `Δ := q - p` and
  `d := hdist u v`, one has `ρ ^ 2 - Δ ^ 2 = 2 * (Real.cosh d - 1)` (both sides are the Minkowski
  norm of `hlift v - hlift u`: use `Hyper.mink_hlift_hlift`, `Hyper.mink_hlift_self`,
  `Hyper.mink_apply`, `Hyper.hdist_eq_cc`);
* a bound for `Δ`: `q = Real.cosh r_v`, `p = Real.cosh r_u` with `r_w := hdist 0 w`, `|r_v - r_u| ≤ d`
  and `r_u ≤ arcsinh K`, so `|Δ| ≤ d * Real.sinh (Real.arcsinh K + 1)` (mean value estimate for
  `cosh` on `[0, arcsinh K + 1]`: `|cosh a - cosh b| ≤ |a - b| * sinh (max a b)`).
Then `ρ ^ 2 = Δ ^ 2 + 2 * (cosh d - 1) ≤ C ^ 2 * d ^ 2` using `Real.cosh d - 1 ≤ C * d ^ 2` for `d ≤ 1`
(any finite constant works, e.g. `Real.cosh d - 1 ≤ d ^ 2 * Real.cosh 1` since `d ≤ 1`), and
`|v i - u i| ≤ ‖v - u‖ = ρ`. Coordinate bounds follow. -/
theorem chartClose (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n) (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : Submission.Mostow.E n, ‖u‖ ≤ K → Submission.Mostow.hdist u v ≤ 1 →
      (∀ i : Fin n, |v i - u i| ≤ C * Submission.Mostow.hdist u v) ∧
      |Submission.Mostow.tpart v - Submission.Mostow.tpart u| ≤ C * Submission.Mostow.hdist u v := by
  obtain ⟨hpos, hsym, -, htri, -⟩ := hI
  let K₀ : ℝ := max K 0
  let M : ℝ := Real.arsinh K₀ + 1
  let C : ℝ := Real.sqrt (Real.sinh M ^ 2 + 2 * Real.cosh 1)
  have hK₀eq : K₀ = max K 0 := rfl
  have hMeq : M = Real.arsinh K₀ + 1 := rfl
  have hCeq : C = Real.sqrt (Real.sinh M ^ 2 + 2 * Real.cosh 1) := rfl
  have hK₀_nn : 0 ≤ K₀ := by rw [hK₀eq]; exact le_max_right K 0
  have hM_ge : 0 ≤ M := by
    rw [hMeq]
    have := (Real.arsinh_nonneg_iff).mpr hK₀_nn
    linarith
  have hsinhM_nn : 0 ≤ Real.sinh M := Real.sinh_nonneg_iff.mpr hM_ge
  have hCpos : 0 < C := by
    rw [hCeq]
    exact Real.sqrt_pos.2 (by nlinarith [Real.cosh_pos 1, sq_nonneg (Real.sinh M)])
  have hC2 : C ^ 2 = Real.sinh M ^ 2 + 2 * Real.cosh 1 := by
    rw [hCeq]
    exact Real.sq_sqrt (by nlinarith [Real.cosh_pos 1, sq_nonneg (Real.sinh M)])
  have hsinhM_le_C : Real.sinh M ≤ C := by
    have h1 : Real.sinh M ≤ Real.sqrt (Real.sinh M ^ 2) := by
      rw [Real.sqrt_sq hsinhM_nn]
    have h2 : Real.sqrt (Real.sinh M ^ 2) ≤ Real.sqrt (Real.sinh M ^ 2 + 2 * Real.cosh 1) :=
      Real.sqrt_le_sqrt (by linarith [Real.cosh_pos 1])
    rw [hCeq]
    exact le_trans h1 h2
  refine ⟨C, hCpos, ?_⟩
  intro u v hu hd
  have huK₀ : ‖u‖ ≤ K₀ := by rw [hK₀eq]; exact le_trans hu (le_max_left K 0)
  have hdnn : 0 ≤ hdist u v := hpos u v
  have hru : hdist 0 u ≤ Real.arsinh K₀ := by
    rw [← Real.sinh_le_sinh, Real.sinh_arsinh, sinh_hdist_zero]
    exact huK₀
  have hrv : hdist 0 v ≤ M := by
    have h := htri 0 u v
    rw [hMeq]
    linarith
  have hru_le_M : hdist 0 u ≤ M := by rw [hMeq]; linarith
  have h0u : 0 ≤ hdist 0 u := hpos 0 u
  have h0v : 0 ≤ hdist 0 v := hpos 0 v
  have hDelta : |tpart v - tpart u| ≤ Real.sinh M * hdist u v := by
    have hv : tpart v = Real.cosh (hdist 0 v) := (cosh_hdist_zero v).symm
    have hu' : tpart u = Real.cosh (hdist 0 u) := (cosh_hdist_zero u).symm
    rw [hv, hu']
    have hb := absCoshSubCoshLe M (hdist 0 v) (hdist 0 u) h0v h0u hrv hru_le_M
    have hdiff : |hdist 0 v - hdist 0 u| ≤ hdist u v := by
      rw [abs_sub_le_iff]
      constructor
      · have h := htri 0 u v
        linarith
      · have h := htri 0 v u
        rw [hsym v u] at h
        linarith
    calc |Real.cosh (hdist 0 v) - Real.cosh (hdist 0 u)|
        ≤ Real.sinh M * |hdist 0 v - hdist 0 u| := hb
      _ ≤ Real.sinh M * hdist u v := mul_le_mul_of_nonneg_left hdiff hsinhM_nn
  have hDeltaSq : (tpart v - tpart u) ^ 2 ≤ (Real.sinh M * hdist u v) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (tpart v - tpart u)) hDelta 2
    simpa only [sq_abs] using h
  have hcoshB : Real.cosh (hdist u v) - 1 ≤ Real.cosh 1 * (hdist u v) ^ 2 :=
    coshSubOneLeSq (hdist u v) hdnn hd
  have hρ2 : ‖v - u‖ ^ 2 ≤ C ^ 2 * (hdist u v) ^ 2 := by
    have hkey := chartCloseSqIdentity u v
    have hmul : (Real.sinh M * hdist u v) ^ 2 = Real.sinh M ^ 2 * (hdist u v) ^ 2 := by ring
    rw [hC2]
    nlinarith [hkey, hDeltaSq, hcoshB, hmul]
  have hρ : ‖v - u‖ ≤ C * hdist u v := by
    have h2 : ‖v - u‖ ^ 2 ≤ (C * hdist u v) ^ 2 := by
      rw [mul_pow]
      exact hρ2
    have h := (sq_le_sq).mp h2
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (mul_nonneg (le_of_lt hCpos) hdnn)] at h
  refine ⟨?_, ?_⟩
  · intro i
    have h := PiLp.norm_apply_le (v - u) i
    have hc : |v i - u i| ≤ ‖v - u‖ := by simpa using h
    calc |v i - u i| ≤ ‖v - u‖ := hc
      _ ≤ C * hdist u v := hρ
  · calc |tpart v - tpart u| ≤ Real.sinh M * hdist u v := hDelta
      _ ≤ C * hdist u v := mul_le_mul_of_nonneg_right hsinhM_le_C hdnn

end

end Work.Mostow
