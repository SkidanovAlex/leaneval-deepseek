import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.saddleCollarFoot

-- NB: the original import list of this file also contained `levelSeparatingMap`,
-- `levelBoundsOfJourney` and `anchorModelFacts`; the proof below needs none of them (and
-- `levelSeparatingMap` was being edited by another agent while this file was written), so the
-- imports were trimmed to the modules the statement itself uses.
set_option maxHeartbeats 1600000

/-!
# The collar row of the saddle window

`Work.Drive.N2.saddleCollarRow`: for the model-adapted window flow `D.Φ` of a saddle, the
*backwards journey* of a collar point `x` (in the scaled chart coordinate `Z`, with
`Zs = lam0 * Z` the chart coordinate of the straightened chart `φ'`) to the anchor level
`f p - lam0 ^ 2 * η` lands exactly on that level and the model value `saddlePsi η δ (Z x)` is the
chart coordinate of the landing point.

The mathematics is:

* the *collar* bounds give `|Re (Z x)²| ≤ η` (so the anchor time `t = f p - lam0²η - f x ≤ 0` and
  `|t| ≤ 2 lam0² η`) and `|Im (Z x)²| ≥ 2 - 2δ > 1` (so along the journey the chart norm is bounded
  below by `lam0`, which puts the multiplier `chartMult lam0 (‖φ' ·‖²)` into its exact branch
  `1/(2‖φ' ·‖²)`, and above by `2 lam0`, which keeps the journey inside the ODE region);
* hence the journey cannot leave `C j` before time `t` (the classical exit argument: an exit point
  lies in `closure (C j) ⊆ φ'.source`, and there the invariants give the norm bound `≤ 2 lam0 < ρ j`,
  while `C j` contains the whole open ball of radius `ρ j`);
* on `[t,0]` the level law is then exact (the multiplier is `1/(2‖φ'‖²)`, so `Re (Z ·)²` moves at
  the rate `1/lam0²`), giving the landing, and the invariants `Im (Z ·)² = Im (Z x)²` and
  `Re (Z ·)² ∈ [-η, η]` put the whole journey in the collar;
* the model `saddlePsi η δ` is constant along the collar trajectory
  (`Work.Drive.N2.saddlePsi_collar_eq_of_continuousOn`) and is the identity on the anchor level
  (`Work.Drive.N2.saddleCollar_aux_saddlePsi_eq_self_of_re_sq_neg_eta`), so it converts the landing point back to
  `saddlePsi η δ (Z x)`.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Filter

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-! ## Elementary complex bookkeeping -/

lemma saddleCollar_aux_sq_re (z : ℂ) : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
  rw [pow_two, Complex.mul_re]; ring

lemma saddleCollar_aux_sq_im (z : ℂ) : (z ^ 2).im = 2 * z.re * z.im := by
  rw [pow_two, Complex.mul_im]; ring

lemma saddleCollar_aux_norm_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

lemma saddleCollar_aux_norm_four (w : ℂ) : ‖w‖ ^ 4 = (w ^ 2).re ^ 2 + (w ^ 2).im ^ 2 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← norm_pow w 2, Complex.sq_norm,
    Complex.normSq_apply]
  ring

lemma saddleCollar_aux_abs_im_sq_le (z : ℂ) : |(z ^ 2).im| ≤ ‖z‖ ^ 2 := by
  rw [saddleCollar_aux_sq_im, saddleCollar_aux_norm_sq, abs_mul, abs_mul, abs_two]
  nlinarith [abs_nonneg z.re, abs_nonneg z.im, sq_abs z.re, sq_abs z.im,
    sq_nonneg (|z.re| - |z.im|)]

lemma saddleCollar_aux_re_sq_smul (c : ℝ) (z : ℂ) : (((c : ℂ) * z) ^ 2).re = c ^ 2 * (z ^ 2).re := by
  rw [mul_pow, ← Complex.ofReal_pow c 2, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

lemma saddleCollar_aux_im_sq_smul (c : ℝ) (z : ℂ) : (((c : ℂ) * z) ^ 2).im = c ^ 2 * (z ^ 2).im := by
  rw [mul_pow, ← Complex.ofReal_pow c 2, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

lemma saddleCollar_aux_norm_ofReal_of_pos {c : ℝ} (hc : 0 < c) : ‖(c : ℂ)‖ = c := by
  have h : ‖(c : ℂ)‖ ^ 2 = c ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
  have h2 := (sq_eq_sq_iff_abs_eq_abs _ _).mp h
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (le_of_lt hc)] at h2

/-- The complex coordinate of a plane chart. -/
lemma saddleCollar_aux_re_chart (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (y : M) :
    (((φ y 0 : ℂ) + (φ y 1 : ℂ) * Complex.I)).re = φ y 0 := by simp

lemma saddleCollar_aux_im_chart (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (y : M) :
    (((φ y 0 : ℂ) + (φ y 1 : ℂ) * Complex.I)).im = φ y 1 := by simp

/-- The complex coordinate of a plane chart has the Euclidean norm of the chart value. -/
lemma saddleCollar_aux_norm_chart (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (y : M) :
    ‖((φ y 0 : ℂ) + (φ y 1 : ℂ) * Complex.I)‖ = ‖φ y‖ := by
  have h : ‖((φ y 0 : ℂ) + (φ y 1 : ℂ) * Complex.I)‖ ^ 2 = ‖φ y‖ ^ 2 := by
    rw [saddleCollar_aux_norm_sq, saddleCollar_aux_re_chart, saddleCollar_aux_im_chart, ← norm_uVec (φ y)]
  have h2 := (sq_eq_sq_iff_abs_eq_abs _ _).mp h
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h2

/-- Two charts with the same source and the same model balls have the same chart norm. -/
lemma saddleCollar_aux_norm_chart_eq {φ ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))}
    (hsrc : φ.source = ψ.source) (hball : ∀ r : ℝ, modelBall φ r = modelBall ψ r)
    {y : M} (hy : y ∈ φ.source) : ‖φ y‖ = ‖ψ y‖ := by
  have hlt : ∀ r : ℝ, ‖φ y‖ < r ↔ ‖ψ y‖ < r := by
    intro r
    constructor
    · intro h
      have hm : y ∈ modelBall φ r := ⟨hy, h⟩
      rw [hball r] at hm
      exact hm.2
    · intro h
      have hm : y ∈ modelBall ψ r := ⟨by rw [← hsrc]; exact hy, h⟩
      rw [← hball r] at hm
      exact hm.2
  refine le_antisymm ?_ ?_
  · by_contra hc
    rw [not_le] at hc
    obtain ⟨r, h1, h2⟩ := exists_between hc
    exact absurd ((hlt r).mpr h1) (not_lt.mpr h2.le)
  · by_contra hc
    rw [not_le] at hc
    obtain ⟨r, h1, h2⟩ := exists_between hc
    exact absurd ((hlt r).mp h1) (not_lt.mpr h2.le)

/-- The saddle model is the identity on the anchor level `Re z² = -η`. -/
lemma saddleCollar_aux_saddlePsi_eq_self_of_re_sq_neg_eta {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hδ₂ : δ < 1 / 2) {z : ℂ} (hz : (z ^ 2).re = -η) : saddlePsi η δ z = z := by
  have h2 : (0 : ℝ) ≤ 2 - 4 * δ := by linarith
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
    linarith
  have hphi : saddlePhi η δ (z ^ 2) = z ^ 2 := by
    rw [saddlePhi_eq_sub]
    simp [hz]
  have hr : saddleRatio η δ z = 1 := by
    have h := saddleRatio_mul_sq (η := η) (δ := δ) hδ h2 z
    rw [hphi] at h
    exact mul_right_cancel₀ (pow_ne_zero 2 hz0) (by rw [h, one_mul])
  rw [saddlePsi, hr, Complex.sqrt_one, mul_one]


theorem saddleCollarRow {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hsgn : D.s₁ D.j = - D.s₂ D.j)
    (φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (Zs Z : M → ℂ) (lam0 : ℝ)
    (hlam0 : lam0 = D.ρ D.j / 8)
    (hsrc : φ'.source = (D.φ D.j).source)
    (hball : ∀ r : ℝ, Work.Drive.N2.modelBall φ' r = Work.Drive.N2.modelBall (D.φ D.j) r)
    (hZs : ∀ y : M, Zs y = (φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I)
    (hZrel : ∀ y : M, Zs y = (lam0 : ℂ) * Z y)
    (hlev : ∀ y ∈ φ'.source, f y = f p + ((Zs y) ^ 2).re)
    (hODE : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      HasDerivAt (fun σ : ℝ => φ' (D.Φ (σ, y)) 0)
        (Work.Drive.N2.chartMult lam0 (‖φ' (D.Φ (t, y))‖ ^ 2) * ((1 : ℝ) * φ' (D.Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => φ' (D.Φ (σ, y)) 1)
        (Work.Drive.N2.chartMult lam0 (‖φ' (D.Φ (t, y))‖ ^ 2) * ((-1 : ℝ) * φ' (D.Φ (t, y)) 1)) t)
    (him : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      ((Zs (D.Φ (t, y))) ^ 2).im = ((Zs y) ^ 2).im)
    {η δ : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1 / 10)
    (hsep : (D.ρ D.j / 8) ^ 2 * η < 2 * D.ηd)
    {x : M} (hxsrc : x ∈ φ'.source) (hcol : Z x ∈ Work.Drive.N2.saddleCollar η δ) :
    D.Φ (f p - lam0 ^ 2 * η - f x, x) ∈ φ'.source ∧
    f (D.Φ (f p - lam0 ^ 2 * η - f x, x)) = f p - lam0 ^ 2 * η ∧
    Z (D.Φ (f p - lam0 ^ 2 * η - f x, x)) = Work.Drive.N2.saddlePsi η δ (Z x) := by
  classical
  -- ## 0. elementary bounds from the collar hypothesis
  have hρ : 0 < D.ρ D.j := D.hρ D.j
  have hlam0pos : 0 < lam0 := by rw [hlam0]; positivity
  have hlam0ne : lam0 ≠ 0 := ne_of_gt hlam0pos
  have hlam0C : (lam0 : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact hlam0ne
  have hη2 : η ^ 2 < 1 / 100 := by nlinarith [hη, hη']
  have h2δ : 0 < 2 - 2 * δ := by linarith
  have hsat : |((Z x) ^ 2).re| ≤ η ∧ 2 - 2 * δ ≤ |((Z x) ^ 2).im| ∧
      |((Z x) ^ 2).im| ≤ 2 := by
    simpa only [saddleCollar, Set.mem_setOf_eq] using hcol
  obtain ⟨hZre, hZimlo, hZimhi⟩ := hsat
  have hZre' : -η ≤ ((Z x) ^ 2).re := (abs_le.mp hZre).1
  have hZre'' : ((Z x) ^ 2).re ≤ η := (abs_le.mp hZre).2
  -- the transport time
  set t : ℝ := f p - lam0 ^ 2 * η - f x with ht_def
  have hfx : f x = f p + lam0 ^ 2 * ((Z x) ^ 2).re := by
    have h := hlev x hxsrc
    rw [hZrel x, saddleCollar_aux_re_sq_smul] at h
    exact h
  have ht_eq : t = -(lam0 ^ 2 * (((Z x) ^ 2).re + η)) := by
    rw [ht_def, hfx]; ring
  have ht0 : t ≤ 0 := by
    rw [ht_eq]; nlinarith [hlam0pos, hZre']
  have ht_low : -(2 * lam0 ^ 2 * η) ≤ t := by
    rw [ht_eq]; nlinarith [hlam0pos, hZre', hZre'']
  -- ## 1. the norm of the collar point
  have hZs_norm (y : M) : ‖Zs y‖ = ‖φ' y‖ := by
    rw [hZs y]; exact saddleCollar_aux_norm_chart φ' y
  have hZs_re (y : M) : ((Zs y) ^ 2).re = lam0 ^ 2 * ((Z y) ^ 2).re := by
    have h := saddleCollar_aux_re_sq_smul lam0 (Z y)
    rw [← hZrel y] at h
    exact h
  have hZs_im (y : M) : ((Zs y) ^ 2).im = lam0 ^ 2 * ((Z y) ^ 2).im := by
    have h := saddleCollar_aux_im_sq_smul lam0 (Z y)
    rw [← hZrel y] at h
    exact h
  have hZx_lt : ‖Z x‖ < 2 := by
    have h4 : ‖Z x‖ ^ 4 = ((Z x) ^ 2).re ^ 2 + ((Z x) ^ 2).im ^ 2 := saddleCollar_aux_norm_four _
    have hre2 : ((Z x) ^ 2).re ^ 2 ≤ η ^ 2 := by
      nlinarith [hZre', hZre'', sq_abs ((Z x) ^ 2).re, sq_nonneg η]
    have him2 : ((Z x) ^ 2).im ^ 2 ≤ 4 := by
      nlinarith [abs_le.mp hZimhi, sq_abs ((Z x) ^ 2).im]
    have hlt : ‖Z x‖ ^ 4 < (2 : ℝ) ^ 4 := by
      rw [h4]; norm_num
      nlinarith [hre2, him2, hη2]
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (4 : ℕ) ≠ 0)).mp hlt
  have hx_norm : ‖φ' x‖ < 2 * lam0 := by
    rw [← hZs_norm x]
    have h : ‖Zs x‖ = lam0 * ‖Z x‖ := by
      rw [hZrel x, Complex.norm_mul, saddleCollar_aux_norm_ofReal_of_pos hlam0pos]
    rw [h]; nlinarith [hZx_lt, hlam0pos]
  -- ## 2. the collar point lies in the closed ODE region
  have hxC : x ∈ D.C D.j := by
    refine D.hCop D.j ⟨?_, ?_⟩
    · rw [← hsrc]; exact hxsrc
    · rw [← saddleCollar_aux_norm_chart_eq hsrc hball hxsrc]
      have hρeq : D.ρ D.j = 8 * lam0 := by rw [hlam0]; ring
      rw [hρeq]; nlinarith [hx_norm]
  -- ## 3. the orbit invariants along an arbitrary confined trace
  have hnormLow : ∀ τ : ℝ, τ ≤ 0 → (∀ s ∈ Set.Icc τ 0, D.Φ (s, x) ∈ D.C D.j) →
      lam0 ^ 2 ≤ ‖φ' (D.Φ (τ, x))‖ ^ 2 := by
    intro τ hτ0 hconf
    have himτ := him x τ (by
      intro s hs
      rw [min_eq_right hτ0, max_eq_left hτ0] at hs
      exact hconf s hs)
    have h1 : |((Zs (D.Φ (τ, x))) ^ 2).im| ≤ ‖Zs (D.Φ (τ, x))‖ ^ 2 :=
      saddleCollar_aux_abs_im_sq_le _
    have h2 : |((Zs (D.Φ (τ, x))) ^ 2).im| = lam0 ^ 2 * |((Z x) ^ 2).im| := by
      rw [himτ, hZs_im x, abs_mul, abs_of_nonneg (sq_nonneg lam0)]
    have h3 : lam0 ^ 2 ≤ |((Zs (D.Φ (τ, x))) ^ 2).im| := by
      rw [h2]
      have h4 : lam0 ^ 2 * (2 - 2 * δ) ≤ lam0 ^ 2 * |((Z x) ^ 2).im| :=
        mul_le_mul_of_nonneg_left hZimlo (sq_nonneg lam0)
      nlinarith [h4, hlam0pos, h2δ]
    calc lam0 ^ 2 ≤ ‖Zs (D.Φ (τ, x))‖ ^ 2 := le_trans h3 h1
      _ = ‖φ' (D.Φ (τ, x))‖ ^ 2 := by rw [hZs_norm]
  have hderivRate : ∀ τ : ℝ, τ ≤ 0 → (∀ s ∈ Set.Icc τ 0, D.Φ (s, x) ∈ D.C D.j) →
      HasDerivAt (fun s : ℝ => ((Zs (D.Φ (s, x))) ^ 2).re) 1 τ := by
    intro τ hτ0 hconf
    obtain ⟨hd0, hd1⟩ := hODE x τ (by
      intro s hs
      rw [min_eq_right hτ0, max_eq_left hτ0] at hs
      exact hconf s hs)
    have hre_eq : ∀ s : ℝ, (Zs (D.Φ (s, x))).re = φ' (D.Φ (s, x)) 0 := by
      intro s; rw [hZs (D.Φ (s, x))]; exact saddleCollar_aux_re_chart φ' _
    have him_eq : ∀ s : ℝ, (Zs (D.Φ (s, x))).im = φ' (D.Φ (s, x)) 1 := by
      intro s; rw [hZs (D.Φ (s, x))]; exact saddleCollar_aux_im_chart φ' _
    have hu : HasDerivAt (fun s : ℝ => (Zs (D.Φ (s, x))).re)
        (chartMult lam0 (‖φ' (D.Φ (τ, x))‖ ^ 2) * (Zs (D.Φ (τ, x))).re) τ := by
      refine hd0.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
      · exact Filter.EventuallyEq.of_eq (funext fun s => hre_eq s)
      · rw [hre_eq τ, one_mul]
    have hv : HasDerivAt (fun s : ℝ => (Zs (D.Φ (s, x))).im)
        (chartMult lam0 (‖φ' (D.Φ (τ, x))‖ ^ 2) * (-(Zs (D.Φ (τ, x))).im)) τ := by
      refine hd1.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
      · exact Filter.EventuallyEq.of_eq (funext fun s => him_eq s)
      · rw [him_eq τ]; ring
    have hsq := (hu.pow 2).sub (hv.pow 2)
    have hnormeq : (Zs (D.Φ (τ, x))).re ^ 2 + (Zs (D.Φ (τ, x))).im ^ 2
        = ‖φ' (D.Φ (τ, x))‖ ^ 2 := by
      have h := norm_uVec (φ' (D.Φ (τ, x)))
      rw [← h]
      rw [hZs (D.Φ (τ, x))]; simp
    have hval : (2 : ℝ) * (Zs (D.Φ (τ, x))).re ^ (2 - 1)
          * (chartMult lam0 (‖φ' (D.Φ (τ, x))‖ ^ 2) * (Zs (D.Φ (τ, x))).re)
        - 2 * (Zs (D.Φ (τ, x))).im ^ (2 - 1)
          * (chartMult lam0 (‖φ' (D.Φ (τ, x))‖ ^ 2) * (-(Zs (D.Φ (τ, x))).im)) = 1 := by
      have hone : 2 * ‖φ' (D.Φ (τ, x))‖ ^ 2 * chartMult lam0 (‖φ' (D.Φ (τ, x))‖ ^ 2)
          = 1 := chartMult_mul hlam0pos (hnormLow τ hτ0 hconf)
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, pow_one]
      have h3 : 2 * (Zs (D.Φ (τ, x))).re
            * (chartMult lam0 (‖φ' (D.Φ (τ, x))‖ ^ 2) * (Zs (D.Φ (τ, x))).re)
          - 2 * (Zs (D.Φ (τ, x))).im
            * (chartMult lam0 (‖φ' (D.Φ (τ, x))‖ ^ 2) * (-(Zs (D.Φ (τ, x))).im))
          = 2 * chartMult lam0 (‖φ' (D.Φ (τ, x))‖ ^ 2)
            * ((Zs (D.Φ (τ, x))).re ^ 2 + (Zs (D.Φ (τ, x))).im ^ 2) := by ring
      rw [h3, hnormeq,
        show 2 * chartMult lam0 (‖φ' (D.Φ (τ, x))‖ ^ 2) * ‖φ' (D.Φ (τ, x))‖ ^ 2
          = 2 * ‖φ' (D.Φ (τ, x))‖ ^ 2 * chartMult lam0 (‖φ' (D.Φ (τ, x))‖ ^ 2) from by ring]
      exact hone
    refine hsq.congr_of_eventuallyEq ?_ |>.congr_deriv hval
    exact Filter.EventuallyEq.of_eq (funext fun s => saddleCollar_aux_sq_re (Zs (D.Φ (s, x))))
  have hrateOf : ∀ u : ℝ, u ≤ 0 → (∀ s ∈ Set.Icc u 0, D.Φ (s, x) ∈ D.C D.j) →
      ((Zs (D.Φ (u, x))) ^ 2).re = ((Zs x) ^ 2).re + u := by
    intro u hu0 hconf
    have hG' : ∀ s ∈ Set.Icc u 0,
        HasDerivAt (fun r : ℝ => ((Zs (D.Φ (r, x))) ^ 2).re - r) 0 s := by
      intro s hs
      have hconf' : ∀ r ∈ Set.Icc s 0, D.Φ (r, x) ∈ D.C D.j :=
        fun r hr => hconf r ⟨le_trans hs.1 hr.1, hr.2⟩
      have hd := hderivRate s hs.2 hconf'
      have hsub : HasDerivAt (fun r : ℝ => ((Zs (D.Φ (r, x))) ^ 2).re - r) (1 - 1) s :=
        hd.sub (hasDerivAt_id s)
      simpa using hsub
    have hdiff : ∀ s ∈ Set.Icc u 0,
        DifferentiableAt ℝ (fun r : ℝ => ((Zs (D.Φ (r, x))) ^ 2).re - r) s :=
      fun s hs => (hG' s hs).differentiableAt
    have hbound : ∀ s ∈ Set.Icc u 0,
        ‖deriv (fun r : ℝ => ((Zs (D.Φ (r, x))) ^ 2).re - r) s‖ ≤ 0 := by
      intro s hs
      rw [(hG' s hs).deriv, norm_zero]
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) hdiff hbound
      (convex_Icc u 0) ⟨le_rfl, hu0⟩ ⟨hu0, le_rfl⟩
    rw [zero_mul, norm_le_zero_iff] at h
    simp only [D.hΦ0 x] at h
    linarith
  -- ## 4. the confinement of the backwards journey
  set T : Set ℝ := {σ : ℝ | t ≤ σ ∧ σ ≤ 0 ∧
    ∀ u ∈ Set.Icc σ 0, D.Φ (u, x) ∈ D.C D.j} with hTdef
  have hTmem : ∀ σ : ℝ, σ ∈ T ↔ (t ≤ σ ∧ σ ≤ 0 ∧
      ∀ u ∈ Set.Icc σ 0, D.Φ (u, x) ∈ D.C D.j) := by
    intro σ; simp only [hTdef, Set.mem_setOf_eq]
  have h0T : (0 : ℝ) ∈ T := (hTmem 0).mpr ⟨ht0, le_rfl, by
    intro u hu
    rw [Set.Icc_self] at hu
    rw [hu, D.hΦ0 x]
    exact hxC⟩
  have hTne : T.Nonempty := ⟨0, h0T⟩
  have hTbdd : BddBelow T := ⟨t, fun b hb => ((hTmem b).mp hb).1⟩
  set β : ℝ := sInf T with hβdef
  have hβge : t ≤ β := le_csInf hTne (fun b hb => ((hTmem b).mp hb).1)
  have hβle : β ≤ 0 := csInf_le hTbdd h0T
  have hgtβ : ∀ u ∈ Set.Ioc β 0, D.Φ (u, x) ∈ D.C D.j := by
    intro u hu
    obtain ⟨v, hvT, hvu⟩ := (csInf_lt_iff hTbdd hTne).mp hu.1
    exact ((hTmem v).mp hvT).2.2 u ⟨le_of_lt hvu, hu.2⟩
  -- the norm bound along the confined part
  have hnormUpper : ∀ u ∈ Set.Ioc β 0, ‖φ' (D.Φ (u, x))‖ < 2 * lam0 := by
    intro u hu
    have hu0 : u ≤ 0 := hu.2
    have huI : u ∈ Set.Icc β 0 := ⟨hu.1.le, hu.2⟩
    have hrate := hrateOf u hu0 (fun s hs => hgtβ s ⟨lt_of_lt_of_le hu.1 hs.1, hs.2⟩)
    have himu : ((Zs (D.Φ (u, x))) ^ 2).im = ((Zs x) ^ 2).im := him x u (by
      intro s hs
      rw [min_eq_right hu0, max_eq_left hu0] at hs
      exact hgtβ s ⟨lt_of_lt_of_le hu.1 hs.1, hs.2⟩)
    have hre : |((Zs (D.Φ (u, x))) ^ 2).re| ≤ 3 * lam0 ^ 2 * η := by
      rw [hrate]
      have h1 : |((Zs x) ^ 2).re| ≤ lam0 ^ 2 * η := by
        rw [hZs_re x, abs_mul, abs_of_nonneg (sq_nonneg lam0)]
        exact mul_le_mul_of_nonneg_left hZre (sq_nonneg lam0)
      have h2 : |u| ≤ 2 * lam0 ^ 2 * η := by
        have htu : t ≤ u := le_of_lt (lt_of_le_of_lt hβge hu.1)
        rw [ht_eq] at htu
        rw [abs_of_nonpos hu0]
        nlinarith [htu, hZre', hZre'', hlam0pos]
      calc |((Zs x) ^ 2).re + u| ≤ |((Zs x) ^ 2).re| + |u| := abs_add_le _ _
        _ ≤ lam0 ^ 2 * η + 2 * lam0 ^ 2 * η := add_le_add h1 h2
        _ = 3 * lam0 ^ 2 * η := by ring
    have him2 : |((Zs (D.Φ (u, x))) ^ 2).im| ≤ 2 * lam0 ^ 2 := by
      have h : |((Zs (D.Φ (u, x))) ^ 2).im| ≤ lam0 ^ 2 * 2 := by
        rw [himu, hZs_im x, abs_mul, abs_of_nonneg (sq_nonneg lam0)]
        exact mul_le_mul_of_nonneg_left hZimhi (sq_nonneg lam0)
      linarith
    have hlt : ‖Zs (D.Φ (u, x))‖ ^ 4 < (2 * lam0) ^ 4 := by
      rw [saddleCollar_aux_norm_four]
      have hre2 : ((Zs (D.Φ (u, x))) ^ 2).re ^ 2 ≤ (3 * lam0 ^ 2 * η) ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * lam0 ^ 2 * η)]
        exact hre
      have him2' : ((Zs (D.Φ (u, x))) ^ 2).im ^ 2 ≤ (2 * lam0 ^ 2) ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * lam0 ^ 2)]
        exact him2
      have hlam4 : (0 : ℝ) < lam0 ^ 4 := by positivity
      have hA : (3 * lam0 ^ 2 * η) ^ 2 + (2 * lam0 ^ 2) ^ 2 < (2 * lam0) ^ 4 := by
        have h1 : (3 * lam0 ^ 2 * η) ^ 2 = 9 * lam0 ^ 4 * η ^ 2 := by ring
        have h2 : (2 * lam0 ^ 2) ^ 2 = 4 * lam0 ^ 4 := by ring
        have h3 : (2 * lam0) ^ 4 = 16 * lam0 ^ 4 := by ring
        rw [h1, h2, h3]
        nlinarith [hη2, hlam4]
      linarith [hre2, him2', hA]
    rw [← hZs_norm]
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * lam0)
      (by norm_num : (4 : ℕ) ≠ 0)).mp hlt
  -- the limit at `β`
  have hβcl : D.Φ (β, x) ∈ closure (D.C D.j) := by
    rcases eq_or_lt_of_le hβle with hβ0 | hβlt
    · rw [hβ0, D.hΦ0 x]; exact subset_closure hxC
    · have hcont : Continuous fun u : ℝ => D.Φ (u, x) := by
        have hp : Continuous fun u : ℝ => (u, x) := continuous_id.prodMk continuous_const
        exact D.hΦsm.continuous.comp hp
      have h1 : β ∈ closure (Set.Ioc β 0) := by
        rw [closure_Ioc (ne_of_lt hβlt)]; exact ⟨le_rfl, hβle⟩
      have h2 : closure (Set.Ioc β 0) ⊆ closure ((fun u : ℝ => D.Φ (u, x)) ⁻¹' D.C D.j) :=
        closure_mono fun u hu => hgtβ u hu
      have h3 : closure ((fun u : ℝ => D.Φ (u, x)) ⁻¹' D.C D.j) ⊆
          (fun u : ℝ => D.Φ (u, x)) ⁻¹' closure (D.C D.j) :=
        hcont.closure_preimage_subset _
      exact h3 (h2 h1)
  have hβsrc : D.Φ (β, x) ∈ φ'.source := by
    rw [hsrc]
    exact (D.hCcl D.j).2 hβcl
  have hβnorm : ‖φ' (D.Φ (β, x))‖ ≤ 2 * lam0 := by
    rcases eq_or_lt_of_le hβle with hβ0 | hβlt
    · rw [hβ0, D.hΦ0 x]; exact le_of_lt hx_norm
    · have hΦc : Continuous fun u : ℝ => D.Φ (u, x) := by
        have hp : Continuous fun u : ℝ => (u, x) := continuous_id.prodMk continuous_const
        exact D.hΦsm.continuous.comp hp
      have hφc : ContinuousAt (fun y : M => φ' y) (D.Φ (β, x)) :=
        φ'.continuousOn_toFun.continuousAt (φ'.open_source.mem_nhds hβsrc)
      have horbT : Tendsto (fun u : ℝ => D.Φ (u, x)) (𝓝[>] β) (𝓝 (D.Φ (β, x))) :=
        hΦc.continuousAt.mono_left nhdsWithin_le_nhds
      have htend : Tendsto (fun u : ℝ => ‖φ' (D.Φ (u, x))‖) (𝓝[>] β)
          (𝓝 ‖φ' (D.Φ (β, x))‖) :=
        (hφc.norm.tendsto).comp horbT
      refine le_of_tendsto htend ?_
      refine Filter.mem_of_superset (Ioc_mem_nhdsGT hβlt) ?_
      intro u hu
      exact (hnormUpper u hu).le
  have hβC : D.Φ (β, x) ∈ D.C D.j := by
    refine D.hCop D.j ⟨by rw [← hsrc]; exact hβsrc, ?_⟩
    rw [← saddleCollar_aux_norm_chart_eq hsrc hball hβsrc]
    have hρeq : D.ρ D.j = 8 * lam0 := by rw [hlam0]; ring
    rw [hρeq]; nlinarith [hβnorm, hlam0pos]
  have hβT : β ∈ T := (hTmem β).mpr ⟨hβge, hβle, fun u hu => by
    rcases eq_or_lt_of_le hu.1 with h | h
    · rw [← h]; exact hβC
    · exact hgtβ u ⟨h, hu.2⟩⟩
  -- ## 5. the infimum is the anchor time
  have hβeq : β = t := by
    by_contra hne
    have hlt : t < β := lt_of_le_of_ne hβge (Ne.symm hne)
    have hnhdC : {y : M | y ∈ φ'.source ∧ ‖φ' y‖ < D.ρ D.j} ⊆ D.C D.j := by
      intro y hy
      refine D.hCop D.j ⟨by rw [← hsrc]; exact hy.1, ?_⟩
      rw [← saddleCollar_aux_norm_chart_eq hsrc hball hy.1]
      exact hy.2
    have hnhd : {y : M | y ∈ φ'.source ∧ ‖φ' y‖ < D.ρ D.j} ∈ 𝓝 (D.Φ (β, x)) := by
      have hρeq : D.ρ D.j = 8 * lam0 := by rw [hlam0]; ring
      have hltn : ‖φ' (D.Φ (β, x))‖ < D.ρ D.j := by
        rw [hρeq]; nlinarith [hβnorm, hlam0pos]
      have hφc : ContinuousAt (fun y : M => φ' y) (D.Φ (β, x)) :=
        φ'.continuousOn_toFun.continuousAt (φ'.open_source.mem_nhds hβsrc)
      exact Filter.inter_mem (IsOpen.mem_nhds φ'.open_source hβsrc)
        (hφc.norm.preimage_mem_nhds (isOpen_Iio.mem_nhds hltn))
    have hΦc : Continuous fun u : ℝ => D.Φ (u, x) := by
      have hp : Continuous fun u : ℝ => (u, x) := continuous_id.prodMk continuous_const
      exact D.hΦsm.continuous.comp hp
    obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp (hΦc.continuousAt.preimage_mem_nhds hnhd)
    set δ : ℝ := min (ε / 2) ((β - t) / 2) with hδdef
    have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
    have hδ1 : δ ≤ ε / 2 := min_le_left _ _
    have hδ2 : δ ≤ (β - t) / 2 := min_le_right _ _
    have hmem : β - δ ∈ T := (hTmem _).mpr ⟨by linarith, by linarith, fun u hu => by
      rcases le_or_gt β u with h | h
      · exact ((hTmem β).mp hβT).2.2 u ⟨h, hu.2⟩
      · refine hnhdC (hε ?_)
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith [hu.1], by linarith [hu.1]⟩⟩
    have hle : β ≤ β - δ := csInf_le hTbdd hmem
    linarith
  have hconfT : ∀ s ∈ Set.Icc t 0, D.Φ (s, x) ∈ D.C D.j := by
    intro s hs
    exact ((hTmem β).mp hβT).2.2 s (by rw [hβeq]; exact hs)
  -- ## 6. the two orbit facts at the anchor time
  have hrateT : ((Zs (D.Φ (t, x))) ^ 2).re = ((Zs x) ^ 2).re + t :=
    hrateOf t ht0 hconfT
  have himT : ((Zs (D.Φ (t, x))) ^ 2).im = ((Zs x) ^ 2).im := by
    refine him x t ?_
    intro s hs
    rw [min_eq_right ht0, max_eq_left ht0] at hs
    exact hconfT s hs
  have hsrcT : D.Φ (t, x) ∈ φ'.source :=
    hsrc ▸ D.hCsub D.j (hconfT t ⟨le_rfl, ht0⟩)
  -- the anchor level in `Z`-coordinates
  have hZreT : ((Z (D.Φ (t, x))) ^ 2).re = -η := by
    have hkey : lam0 ^ 2 * ((Z (D.Φ (t, x))) ^ 2).re = lam0 ^ 2 * ((Z x) ^ 2).re + t := by
      rw [← hZs_re (D.Φ (t, x)), hrateT, hZs_re x]
    have h2 : lam0 ^ 2 * ((Z (D.Φ (t, x))) ^ 2).re = lam0 ^ 2 * (-η) := by
      rw [hkey, ht_def, hfx]; ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hlam0ne) h2
  -- ## 7. the model is constant along the journey
  have hchart : ContinuousOn (fun y : M => ((φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I))
      φ'.source := by
    have h0 : Continuous fun u : EuclideanSpace ℝ (Fin 2) => ((u 0 : ℝ) : ℂ) := by fun_prop
    have h1 : Continuous fun u : EuclideanSpace ℝ (Fin 2) => ((u 1 : ℝ) : ℂ) := by fun_prop
    exact (h0.add (h1.mul continuous_const)).comp_continuousOn φ'.continuousOn_toFun
  have hZcont : ContinuousOn (fun y : M => Z y) φ'.source := by
    have hEq : (fun y : M => Z y) = fun y : M => (lam0 : ℂ)⁻¹ *
        ((φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I) := by
      funext y
      have h : Z y = (lam0 : ℂ)⁻¹ * Zs y := by
        rw [hZrel y, ← mul_assoc, inv_mul_cancel₀ hlam0C, one_mul]
      rw [h, hZs y]
    rw [hEq]
    exact hchart.const_mul _
  set γ : ℝ → ℂ := fun s => Z (D.Φ (s * t, x)) with hγdef
  have hmemγ : ∀ s ∈ Set.Icc (0 : ℝ) 1, D.Φ (s * t, x) ∈ φ'.source := by
    intro s hs
    have hs' : s * t ∈ Set.Icc t 0 :=
      ⟨by nlinarith [hs.1, hs.2, ht0], by nlinarith [hs.1, hs.2, ht0]⟩
    rw [hsrc]
    exact D.hCsub D.j (hconfT (s * t) hs')
  have hγcont : ContinuousOn γ (Set.Icc (0 : ℝ) 1) := by
    have horb : Continuous fun s : ℝ => D.Φ (s * t, x) := by
      have hp : Continuous fun s : ℝ => (s * t, x) :=
        (continuous_id.mul continuous_const).prodMk continuous_const
      exact D.hΦsm.continuous.comp hp
    have hEq : γ = fun s : ℝ => (lam0 : ℂ)⁻¹ *
        ((φ' (D.Φ (s * t, x)) 0 : ℂ) + (φ' (D.Φ (s * t, x)) 1 : ℂ) * Complex.I) := by
      funext s
      show Z (D.Φ (s * t, x)) = (lam0 : ℂ)⁻¹ *
        ((φ' (D.Φ (s * t, x)) 0 : ℂ) + (φ' (D.Φ (s * t, x)) 1 : ℂ) * Complex.I)
      have h : Z (D.Φ (s * t, x)) = (lam0 : ℂ)⁻¹ * Zs (D.Φ (s * t, x)) := by
        rw [hZrel (D.Φ (s * t, x)), ← mul_assoc, inv_mul_cancel₀ hlam0C, one_mul]
      rw [h, hZs (D.Φ (s * t, x))]
    rw [hEq]
    exact (hchart.comp horb.continuousOn hmemγ).const_mul _
  have hγC : ∀ s ∈ Set.Icc (0 : ℝ) 1, γ s ∈ saddleCollar η δ := by
    intro s hs
    have hs' : s * t ∈ Set.Icc t 0 :=
      ⟨by nlinarith [hs.1, hs.2, ht0], by nlinarith [hs.1, hs.2, ht0]⟩
    have hrate := hrateOf (s * t) hs'.2 (fun r hr => hconfT r ⟨le_trans hs'.1 hr.1, hr.2⟩)
    have hims : ((Zs (D.Φ (s * t, x))) ^ 2).im = ((Zs x) ^ 2).im :=
      him x (s * t) (by
        intro r hr
        rw [min_eq_right hs'.2, max_eq_left hs'.2] at hr
        exact hconfT r ⟨le_trans hs'.1 hr.1, hr.2⟩)
    have hkey : lam0 ^ 2 * ((Z (D.Φ (s * t, x))) ^ 2).re = lam0 ^ 2 * ((Z x) ^ 2).re + s * t := by
      rw [← hZs_re (D.Φ (s * t, x)), hrate, hZs_re x]
    have habs : |((Z (D.Φ (s * t, x))) ^ 2).re| ≤ η := by
      have hb : |lam0 ^ 2 * ((Z (D.Φ (s * t, x))) ^ 2).re| ≤ lam0 ^ 2 * η := by
        rw [hkey, abs_le]
        constructor
        · nlinarith [hs'.1, ht_eq]
        · nlinarith [hs'.2, hZre'', sq_nonneg lam0]
      have h1 := abs_mul (lam0 ^ 2) ((Z (D.Φ (s * t, x))) ^ 2).re
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ lam0 ^ 2)] at h1
      rw [h1] at hb
      exact le_of_mul_le_mul_left hb (by positivity)
    have himabs : 2 - 2 * δ ≤ |((Z (D.Φ (s * t, x))) ^ 2).im| ∧
        |((Z (D.Φ (s * t, x))) ^ 2).im| ≤ 2 := by
      have h2 : ((Z (D.Φ (s * t, x))) ^ 2).im = ((Z x) ^ 2).im := by
        have h := hims
        rw [hZs_im, hZs_im] at h
        exact mul_left_cancel₀ (pow_ne_zero 2 hlam0ne) h
      rw [h2]; exact ⟨hZimlo, hZimhi⟩
    rw [hγdef]
    simpa only [saddleCollar, Set.mem_setOf_eq] using ⟨habs, himabs.1, himabs.2⟩
  have him0 : ∀ s ∈ Set.Icc (0 : ℝ) 1, ((γ s) ^ 2).im = ((γ 0) ^ 2).im := by
    intro s hs
    have hs' : s * t ∈ Set.Icc t 0 :=
      ⟨by nlinarith [hs.1, hs.2, ht0], by nlinarith [hs.1, hs.2, ht0]⟩
    have h0 : γ 0 = Z x := by
      simp only [hγdef]; simp [D.hΦ0 x]
    rw [h0]
    have h1 : ((Z (D.Φ (s * t, x))) ^ 2).im = ((Z x) ^ 2).im := by
      have h := him x (s * t) (by
        intro r hr
        rw [min_eq_right hs'.2, max_eq_left hs'.2] at hr
        exact hconfT r ⟨le_trans hs'.1 hr.1, hr.2⟩)
      rw [hZs_im, hZs_im] at h
      exact mul_left_cancel₀ (pow_ne_zero 2 hlam0ne) h
    rw [hγdef]
    simpa using h1
  have hΨconst : saddlePsi η δ (Z (D.Φ (t, x))) = saddlePsi η δ (Z x) := by
    have h := saddlePsi_collar_eq_of_continuousOn (γ := γ) hη hη' hδ hδ' hγcont hγC him0
    have h1 : γ 1 = Z (D.Φ (t, x)) := by
      simp only [hγdef]; simp
    have h0 : γ 0 = Z x := by
      simp only [hγdef]; simp [D.hΦ0 x]
    rwa [h1, h0] at h
  -- ## 8. conclusion
  have hself := saddleCollar_aux_saddlePsi_eq_self_of_re_sq_neg_eta hη hδ (by linarith : δ < 1 / 2) hZreT
  exact ⟨hsrcT,
    by
      calc f (D.Φ (t, x)) = f p + ((Zs (D.Φ (t, x))) ^ 2).re := hlev _ hsrcT
        _ = f p + (((Zs x) ^ 2).re + t) := by rw [hrateT]
        _ = f p - lam0 ^ 2 * η := by
          rw [hZs_re x, ht_def, hfx]; ring,
    by
      rw [← hself]
      exact hΨconst⟩


end Work.Drive.N2
