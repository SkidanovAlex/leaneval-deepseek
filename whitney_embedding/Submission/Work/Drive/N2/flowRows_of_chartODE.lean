import Mathlib
import Submission.Work.Drive.N2.modelFlowDefs
import Submission.Work.Drive.N2.im_sq_eq_of_flow_closedODE

namespace Work.Drive.N2

open Set

/-! ## Elementary algebra of the chart multiplier and of the scaled complex coordinate -/

/-- **The multiplier is never more than `1/(2σ)`**: `2 σ (chartMult r σ) ≤ 1` for all `σ`, `r`.
Below `r²/2` the multiplier vanishes; on the shell it is `(2σ)⁻¹`, and `smoothTransition ≤ 1`. -/
private lemma two_mul_chartMult_le_one (r σ : ℝ) : 2 * σ * chartMult r σ ≤ 1 := by
  by_cases hσ : σ ≤ 0
  · have h1 : 2 * σ / r ^ 2 - 1 ≤ 0 := by
      have : 2 * σ / r ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg r)
      linarith
    rw [chartMult, Real.smoothTransition.zero_of_nonpos h1]
    simp
  · push Not at hσ
    have h2 : (2 * σ) ≠ 0 := by positivity
    have key : 2 * σ * (2 * σ)⁻¹ = 1 := mul_inv_cancel₀ h2
    calc 2 * σ * chartMult r σ
        = Real.smoothTransition (2 * σ / r ^ 2 - 1) := by
          rw [chartMult]
          calc 2 * σ * (Real.smoothTransition (2 * σ / r ^ 2 - 1) * (2 * σ)⁻¹)
              = Real.smoothTransition (2 * σ / r ^ 2 - 1) * (2 * σ * (2 * σ)⁻¹) := by ring
            _ = Real.smoothTransition (2 * σ / r ^ 2 - 1) * 1 := by rw [key]
            _ = Real.smoothTransition (2 * σ / r ^ 2 - 1) := by ring
      _ ≤ 1 := Real.smoothTransition.le_one _

/-- The square of the complex coordinate of the chart: real part `a² - b²`. -/
private lemma re_sq_two (a b : ℝ) : ((((a : ℂ) + (b : ℂ) * Complex.I)) ^ 2).re = a ^ 2 - b ^ 2 := by
  simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]

/-- The square of the complex coordinate of the chart: imaginary part `2 a b`. -/
private lemma im_sq_two (a b : ℝ) : ((((a : ℂ) + (b : ℂ) * Complex.I)) ^ 2).im = 2 * a * b := by
  simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- Division by a real scalar scales the real part of the square. -/
private lemma re_sq_div (w : ℂ) (k : ℝ) : ((w / (k : ℂ)) ^ 2).re = (w ^ 2).re / k ^ 2 := by
  have h1 : w / (k : ℂ) = w * (((k⁻¹ : ℝ)) : ℂ) := by
    rw [div_eq_mul_inv, Complex.ofReal_inv]
  rw [h1, mul_pow, ← Complex.ofReal_pow]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Division by a real scalar scales the imaginary part of the square. -/
private lemma im_sq_div (w : ℂ) (k : ℝ) : ((w / (k : ℂ)) ^ 2).im = (w ^ 2).im / k ^ 2 := by
  have h1 : w / (k : ℂ) = w * (((k⁻¹ : ℝ)) : ℂ) := by
    rw [div_eq_mul_inv, Complex.ofReal_inv]
  rw [h1, mul_pow, ← Complex.ofReal_pow]
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The level law in the scaled coordinate**: for `lam = lam0²` the quantity `lam · Re (Z ·)²`
of the scaled chart coordinate is the level difference `a² - b²` of the two real chart coordinates. -/
private lemma lam_mul_re_scaled {lam lam0 : ℝ} (hlam0 : 0 < lam0) (hlam : lam = lam0 ^ 2)
    (a b : ℝ) :
    lam * (((((a : ℂ) + (b : ℂ) * Complex.I) / (lam0 : ℂ)) ^ 2).re) = a ^ 2 - b ^ 2 := by
  have h0 : lam0 ≠ 0 := ne_of_gt hlam0
  rw [re_sq_div, re_sq_two, hlam]
  field_simp

/-- **The fencing inequality**: a function on `[0, a]` with derivative `≤ 1` everywhere grows by at
most `a`.  (One-dimensional mean value theorem, `image_le_of_deriv_right_le_deriv_boundary` applied
to `G` and the reference function `σ ↦ G 0 + σ`.) -/
private lemma sub_le_of_hasDerivAt_le {G g' : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hG : ∀ σ ∈ Set.Icc 0 a, HasDerivAt G (g' σ) σ)
    (hbound : ∀ σ ∈ Set.Ico 0 a, g' σ ≤ 1) :
    G a - G 0 ≤ a := by
  have hmain := image_le_of_deriv_right_le_deriv_boundary
    (f := G) (f' := g') (a := 0) (b := a) (B := fun σ => G 0 + σ) (B' := fun _ => 1)
    (fun x hx => (hG x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hG x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
    (by simp)
    ((continuous_const.add continuous_id).continuousOn)
    (fun x _ => by
      have h := (hasDerivWithinAt_id (𝕜 := ℝ) x (Set.Ici x)).const_add (G 0)
      simpa using h)
    hbound
  have := hmain (Set.right_mem_Icc.mpr ha)
  linarith

/-- **The three flow rows that the model-adapted flow supplies on the closed chart region `C`**,
in the *scaled* chart coordinate `Z = (φ 0 + i φ 1)/lam0` (`f = c + lam * Re (Z ·)²`,
`lam = lam0²`): the `Im (Z ·)²`-invariance, the `f`-increment bound (`≤` elapsed time), and the
two-sided monotonicity of `f` along the orbits.  The chart ODE is the datum's, with the two saddle
signs `(1, -1)` and the multiplier `chartMult r (‖φ ·‖²)`; `C` is the closed chart region of the
datum (the ODE is only known on `C`).

SOLUTION SKETCH (both reviewers verified the three clauses and the arithmetic):
* clause 1 (`Im`-invariance): `Im (Z ·)² = 2 φ 0 φ 1 / lam0²` and the ODE gives
  `(φ 0 · φ 1)' = χ φ 0 φ 1 - χ φ 0 φ 1 = 0`.  (A sibling brick `im_sq_eq_of_flow_closedODE` has
  this clause in the *unscaled* coordinate; the scaling by `1/lam0` is just a factor `1/lam0²`.)
* clause 2 (`f`-increment `≤` elapsed time): with `χ = chartMult r (‖φ ·‖²)` and
  `σ = ‖φ ·‖²` one has `2 σ (chartMult r σ) = smoothTransition (2σ/r² - 1) ≤ 1` for all `σ, r`
  (`chartMult_eq_zero` below, `chartMult_mul` above), so along the orbit
  `d/dt (c + lam Re (Z ·)²) = lam * 2 χ ‖Z‖² = 2 χ ‖φ‖² ≤ 1`.  Restart at `y' = Φ (t₁, y)`
  (`hΦcomp`), apply `hODE` and `hlev` on the segment `[0, t₂ - t₁]` (contained in `C`), and use the
  mean value theorem / FTC.
* clause 3 (two-sided monotonicity): `hmono0` at `Φ (t₁, y)` plus `hΦ0`, `hΦcomp`. -/
theorem flowRows_of_chartODE {M : Type*} [TopologicalSpace M]
    (f : M → ℝ) {Φ : ℝ × M → M} (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    {c lam r lam0 : ℝ} (hlam0 : 0 < lam0) (hlam : lam = lam0 ^ 2)
    (Z : M → ℂ) (hZ : ∀ m : M, Z m = ((φ m 0 : ℂ) + (φ m 1 : ℂ) * Complex.I) / (lam0 : ℂ))
    {C : Set M}
    (hODE : ∀ (y : M) (τ : ℝ),
      (∀ u ∈ Set.Icc (min 0 τ) (max 0 τ), Φ (u, y) ∈ C) →
      HasDerivAt (fun σ : ℝ => φ (Φ (σ, y)) 0)
        (chartMult r (‖φ (Φ (τ, y))‖ ^ 2) * ((1 : ℝ) * φ (Φ (τ, y)) 0)) τ ∧
      HasDerivAt (fun σ : ℝ => φ (Φ (σ, y)) 1)
        (chartMult r (‖φ (Φ (τ, y))‖ ^ 2) * ((-1 : ℝ) * φ (Φ (τ, y)) 1)) τ)
    (hΦ0 : ∀ y : M, Φ (0, y) = y)
    (hΦcomp : ∀ (a b : ℝ) (y : M), Φ (a, Φ (b, y)) = Φ (a + b, y))
    (hlev : ∀ y ∈ C, f y = c + lam * ((Z y) ^ 2).re)
    (hmono0 : ∀ y : M, MonotoneOn (fun τ : ℝ => f (Φ (τ, y))) (Set.Ici 0)) :
    (∀ (y : M) (t : ℝ), (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∈ C) →
      ((Z (Φ (t, y))) ^ 2).im = ((Z y) ^ 2).im) ∧
    (∀ (y : M) (t₁ t₂ : ℝ), t₁ ≤ t₂ → (∀ u ∈ Set.Icc t₁ t₂, Φ (u, y) ∈ C) →
      f (Φ (t₂, y)) - f (Φ (t₁, y)) ≤ t₂ - t₁) ∧
    (∀ (y : M) (t₁ t₂ : ℝ), t₁ ≤ t₂ → f (Φ (t₁, y)) ≤ f (Φ (t₂, y))) := by
  refine ⟨?_, ?_, ?_⟩
  · -- ### clause 1: `Im (Z ·)²` is conserved, by the unscaled sibling brick and the scaling `1/lam0`
    intro y t hconf
    have hinv := im_sq_eq_of_flow_closedODE φ
      (fun m : M => (φ m 0 : ℂ) + (φ m 1 : ℂ) * Complex.I) (fun m => rfl) r hODE hΦ0 y t hconf
    have hinv' : (((φ (Φ (t, y)) 0 : ℂ) + (φ (Φ (t, y)) 1 : ℂ) * Complex.I) ^ 2).im
        = (((φ y 0 : ℂ) + (φ y 1 : ℂ) * Complex.I) ^ 2).im := by simpa using hinv
    rw [hZ (Φ (t, y)), hZ y, im_sq_div, im_sq_div, hinv']
  · -- ### clause 2: the increment is at most the elapsed time
    intro y t₁ t₂ htt hconf
    set y' : M := Φ (t₁, y) with hy'
    set a : ℝ := t₂ - t₁ with ha
    have ha0 : 0 ≤ a := by rw [ha]; linarith
    -- the restarted trace: `Φ (σ, y') = Φ (σ + t₁, y)`
    have hstep : ∀ σ : ℝ, Φ (σ, y') = Φ (σ + t₁, y) := by
      intro σ
      rw [hy']
      exact hΦcomp σ t₁ y
    have hCY : y' ∈ C := by
      rw [hy']
      exact hconf t₁ ⟨le_rfl, htt⟩
    have hconfC : ∀ σ ∈ Set.Icc 0 a, Φ (σ, y') ∈ C := by
      intro σ hσ
      rw [hstep σ]
      exact hconf _ ⟨by linarith [hσ.1],
        by rw [ha] at hσ; linarith [hσ.2]⟩
    -- the chart ODE along the restarted trace
    have hode : ∀ σ ∈ Set.Icc 0 a,
        HasDerivAt (fun s : ℝ => φ (Φ (s, y')) 0)
          (chartMult r (‖φ (Φ (σ, y'))‖ ^ 2) * ((1 : ℝ) * φ (Φ (σ, y')) 0)) σ ∧
        HasDerivAt (fun s : ℝ => φ (Φ (s, y')) 1)
          (chartMult r (‖φ (Φ (σ, y'))‖ ^ 2) * ((-1 : ℝ) * φ (Φ (σ, y')) 1)) σ := by
      intro σ hσ
      refine hODE y' σ (fun w hw => ?_)
      rw [min_eq_left hσ.1, max_eq_right hσ.1] at hw
      exact hconfC w ⟨hw.1, le_trans hw.2 hσ.2⟩
    -- the level of the trace, as a function of the elapsed time
    set G : ℝ → ℝ := fun σ => c + ((φ (Φ (σ, y')) 0) ^ 2 - (φ (Φ (σ, y')) 1) ^ 2) with hGdef
    have hGderiv : ∀ σ ∈ Set.Icc 0 a,
        HasDerivAt G (2 * ‖φ (Φ (σ, y'))‖ ^ 2 * chartMult r (‖φ (Φ (σ, y'))‖ ^ 2)) σ := by
      intro σ hσ
      obtain ⟨hd0, hd1⟩ := hode σ hσ
      rw [hGdef]
      refine (((hd0.pow 2).sub (hd1.pow 2)).const_add c).congr_deriv ?_
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, ← norm_uVec (φ (Φ (σ, y')))]
      ring
    have hbound : ∀ σ ∈ Set.Ico 0 a,
        2 * ‖φ (Φ (σ, y'))‖ ^ 2 * chartMult r (‖φ (Φ (σ, y'))‖ ^ 2) ≤ 1 :=
      fun σ _ => two_mul_chartMult_le_one r _
    have hmvt : G a - G 0 ≤ a := sub_le_of_hasDerivAt_le ha0 hGderiv hbound
    -- the two endpoints in terms of `G`
    have hG0 : f (Φ (t₁, y)) = G 0 := by
      have hlev' := hlev y' hCY
      rw [← hy', hGdef]
      simp only [hΦ0 y']
      rw [hlev', hZ y', lam_mul_re_scaled hlam0 hlam (φ y' 0) (φ y' 1)]
    have hGa : f (Φ (t₂, y)) = G a := by
      have hat : a + t₁ = t₂ := by rw [ha]; ring
      have h2 : Φ (t₂, y) = Φ (a, y') := by rw [← hat, ← hstep a]
      have hmem : Φ (a, y') ∈ C := hconfC a ⟨ha0, le_rfl⟩
      rw [hGdef, h2, hlev (Φ (a, y')) hmem, hZ (Φ (a, y')),
        lam_mul_re_scaled hlam0 hlam (φ (Φ (a, y')) 0) (φ (Φ (a, y')) 1)]
    rw [← hG0, ← hGa] at hmvt
    rw [ha] at hmvt
    exact hmvt
  · -- ### clause 3: two-sided monotonicity, by restarting the flow at `t₁`
    intro y t₁ t₂ htt
    have h1 : f (Φ (0, Φ (t₁, y))) ≤ f (Φ (t₂ - t₁, Φ (t₁, y))) :=
      hmono0 (Φ (t₁, y)) (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (sub_nonneg.mpr htt))
        (sub_nonneg.mpr htt)
    rw [hΦ0 (Φ (t₁, y))] at h1
    rw [hΦcomp (t₂ - t₁) t₁ y] at h1
    rw [show t₂ - t₁ + t₁ = t₂ by ring] at h1
    exact h1

end Work.Drive.N2
