import Mathlib

/-!
# Stabilising the direction datum of the plane chart at a prescribed level

`PLANE_CHART_FINAL.md` §9 (the plane chart's crux, sessions 4–5 of the agent owning
`exists_planeChart.lean`) reduces the last obligation of the capped-plane chart — the *vanishing*
`w z ≠ 0` of the blend `w z = α z * w_h z + (1 - α z) * w_a` — to the existence of a level `τ₁ < 0`
at which the *direction datum*

> `w_h (x,τ) := W (x,τ)/‖W (x,τ)‖ · conj (M (x,τ))/‖M (x,τ)‖`

of the descended chord data `(M, W)` is **constant in `x`** (then the modulus-mismatch criterion
`blend_ne_zero_of_norm_ne` applies at the level `α = |w_a|/(1+|w_a|)`, since a loop constant in `x`
avoids any prescribed `-w_a ≠` that constant).

§9.2 proposes to *produce* that constancy by a bump-supported modification of the pair `(M, W)`:

> `F (x,τ) := 1 + b τ · ζ x · (c · conj (w_h (x,τ₁)) − 1)`, `W_new := W · F`, `M_new := M · |F|`.

**That device, as sketched, has a gap.**  With `A := c · conj (w_h (x,τ))` (unit-valued) one has
`F = 1 + λ (A − 1)` with `λ = b τ ζ x`, so `F = 0` iff `λ = 1/(1 − A)`, and since `A` is unit this
forces `|λ| ≥ 1/2`, with equality exactly when `A = -1`.  The sketch controls `F` only by
`|F − 1| ≤ 1/2`, which *fails* on the set where `|λ| ≥ 1/2` — and that set is non-empty, because
`λ = 1` at `τ = τ₁`.  So `F` can vanish at an intermediate level, and `M_new = M·|F|` then need not
be smooth (and the pair need not be non-vanishing).  The sketch's own list of "niggles" does not
mention this case.

**The correction (this file).**  Use a *unit* factor instead of an affine blend: with `ψ` a real
argument of the loop `x ↦ c · conj (w_h (x,τ₁))` (such a `ψ` exists exactly because that loop has
*winding zero*, i.e. because `deg w_h = deg W − deg M = ε − m = 0` under `Work.Drive.WrapData` — the
condition §9.1 identifies as the one making the stabilisation possible), put

> `W_new (x,τ) := W (x,τ) · exp (i · b τ · ζ x · ψ x)`,   `M_new := M`.

Then

* `W_new` is smooth, `0 ≤ τ → W_new = W` (the bump vanishes for `τ ≥ 0`, so *all* value clauses of
  the descent at `τ ≥ 0` survive verbatim), `W_new ≠ 0` and `‖W_new‖ = ‖W‖` wherever `W ≠ 0`
  — hence `A = ‖M‖² + τ‖W‖²`, `D = M/√A` and the band inequality `‖M‖² ≥ 2|τ|‖W‖²` are *unchanged*;
* at `τ = τ₁` the factor is `exp (i ψ x) = c · conj (w_h (x,τ₁))`, and since `|w_h| = 1`
  this gives `w_h (x,τ₁) = w_h (x,τ₁) · c · conj (w_h (x,τ₁)) = c`: the direction datum is
  **constant**, with no vanishing issue at all (`exp` never vanishes, and `‖W_new‖ = ‖W‖` keeps every
  norm pinned).

This file states and proves that correction.  It is deliberately independent of the lane's files: the
only inputs are the smoothness and non-vanishing of `(M, W)` on the band `1/4 ≤ ‖x‖`, the level
`τ₁ < 0`, the unit constant `c`, and the argument `ψ` of the stabilising loop. -/

namespace Work.Drive

open scoped ContDiff

noncomputable section

/-- The **direction datum** of a pair `(M, W)` of descended chord data: for the plane chart this is
the `w_h` of `PLANE_CHART_FINAL.md` §9, `W/‖W‖ · conj M/‖M‖`.  (Junk where `M` or `W` vanishes; the
statements below always carry the relevant non-vanishing hypotheses.) -/
def dirDatum (M W : ℂ × ℝ → ℂ) (p : ℂ × ℝ) : ℂ :=
  (W p / ((‖W p‖ : ℝ) : ℂ)) * star (M p / ((‖M p‖ : ℝ) : ℂ))

/-- The direction datum has norm `1` where the data do not vanish. -/
lemma norm_dirDatum {M W : ℂ × ℝ → ℂ} {p : ℂ × ℝ} (hM : M p ≠ 0) (hW : W p ≠ 0) :
    ‖dirDatum M W p‖ = 1 := by
  rw [dirDatum, norm_mul, norm_star, norm_div, norm_div]
  have e1 : ‖(((‖W p‖ : ℝ)) : ℂ)‖ = ‖W p‖ := by
    rw [show ‖(((‖W p‖ : ℝ)) : ℂ)‖ = |‖W p‖| by simp, abs_of_nonneg (norm_nonneg _)]
  have e2 : ‖(((‖M p‖ : ℝ)) : ℂ)‖ = ‖M p‖ := by
    rw [show ‖(((‖M p‖ : ℝ)) : ℂ)‖ = |‖M p‖| by simp, abs_of_nonneg (norm_nonneg _)]
  rw [e1, e2, div_self (norm_ne_zero_iff.mpr hW), div_self (norm_ne_zero_iff.mpr hM), mul_one]

/-- Multiplying `W` by the unit factor `exp (i θ)` multiplies the direction datum by that same unit
factor.  (The norm `‖exp (i θ)‖ = 1` is what makes the modification preserve `A` and `D`.) -/
lemma dirDatum_mul_exp (M W : ℂ × ℝ → ℂ) (θ : ℂ × ℝ → ℝ) (p : ℂ × ℝ)
    (hM : M p ≠ 0) (hW : W p ≠ 0) :
    dirDatum M (fun q : ℂ × ℝ => W q * Complex.exp (((θ q : ℝ) : ℂ) * Complex.I)) p
      = dirDatum M W p * Complex.exp (((θ p : ℝ) : ℂ) * Complex.I) := by
  have hM' : ((‖M p‖ : ℝ) : ℂ) ≠ 0 := by
    simpa using (norm_ne_zero_iff.mpr hM)
  have hθre : (((θ p : ℝ) : ℂ) * Complex.I).re = 0 := by
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hnorm : ‖Complex.exp (((θ p : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp, hθre, Real.exp_zero]
  have hden : ‖W p * Complex.exp (((θ p : ℝ) : ℂ) * Complex.I)‖ = ‖W p‖ := by
    rw [norm_mul, hnorm, mul_one]
  rw [dirDatum, dirDatum, hden]
  have h1 : W p * Complex.exp (((θ p : ℝ) : ℂ) * Complex.I) / ((‖W p‖ : ℝ) : ℂ)
      = (W p / ((‖W p‖ : ℝ) : ℂ)) * Complex.exp (((θ p : ℝ) : ℂ) * Complex.I) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  rw [h1]
  ring

/-- **The correction of the stabilisation device of `PLANE_CHART_FINAL.md` §9.2.**

Let `(M, W)` be smooth complex data on the half-band `τ ≤ 0`, non-vanishing on the annulus
`1/4 ≤ ‖x‖` (the region the plane chart visits), let `τ₁ < 0`, let `c` be a unit constant, and let
`ψ` be a real argument of the stabilising loop: `exp (i ψ x) = c · conj (w_h (x,τ₁))` for `‖x‖ ≥ 1/2`
(existence of such a `ψ` is the winding-zero condition `deg w_h = 0` of §9.1, available under
`Work.Drive.WrapData`).

Then there is smooth `W'` with

* `0 ≤ τ → W' (x,τ) = W (x,τ)` — the modification is supported in `τ < 0`, so the descent's value
  clauses at `τ ≥ 0` are untouched;
* `W' ≠ 0` and `‖W' (x,τ)‖ = ‖W (x,τ)‖` on the annulus `τ ≤ 0`, `1/4 ≤ ‖x‖` — so `A`, `D` and the
  band inequality of the descent are unchanged, and `M` need not be modified at all;
* **`dirDatum M W' (x,τ₁) = c` for `‖x‖ ≥ 1/2`** — the direction datum is constant at the level
  `τ₁`.

Because `W'` is obtained from `W` by a *unit* factor, no vanishing can occur, which is exactly the
point the sketch of §9.2 misses. -/
theorem exists_directionStabilization
    (M W : ℂ × ℝ → ℂ) (hM : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hMne : ∀ p : ℂ × ℝ, p.2 ≤ 0 → 1 / 4 ≤ ‖p.1‖ → M p ≠ 0)
    (hWne : ∀ p : ℂ × ℝ, p.2 ≤ 0 → 1 / 4 ≤ ‖p.1‖ → W p ≠ 0)
    {τ₁ : ℝ} (hτ₁ : τ₁ < 0) (c : ℂ) (hc : ‖c‖ = 1)
    (ψ : ℂ → ℝ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hψspec : ∀ x : ℂ, 1 / 2 ≤ ‖x‖ →
      Complex.exp (((ψ x : ℝ) : ℂ) * Complex.I) = c * star (dirDatum M W (x, τ₁))) :
    ∃ W' : ℂ × ℝ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W' ∧
      (∀ p : ℂ × ℝ, 0 ≤ p.2 → W' p = W p) ∧
      (∀ p : ℂ × ℝ, p.2 ≤ 0 → 1 / 4 ≤ ‖p.1‖ → W' p ≠ 0) ∧
      (∀ p : ℂ × ℝ, p.2 ≤ 0 → 1 / 4 ≤ ‖p.1‖ → ‖W' p‖ = ‖W p‖) ∧
      (∀ x : ℂ, 1 / 2 ≤ ‖x‖ → dirDatum M W' (x, τ₁) = c) := by
  classical
  set b : ℝ → ℝ := fun τ => Real.smoothTransition (τ / τ₁) with hbdef
  set ζ : ℂ → ℝ := fun x => Real.smoothTransition ((Complex.normSq x - 1 / 16) / (3 / 16))
    with hζdef
  set W' : ℂ × ℝ → ℂ :=
    fun p => W p * Complex.exp ((((ζ p.1 * b p.2 * ψ p.1 : ℝ)) : ℂ) * Complex.I) with hW'def
  have hbsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    rw [hbdef]
    exact Real.smoothTransition.contDiff.comp (by fun_prop)
  have hns : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℂ => Complex.normSq x) := by
    have h : (fun x : ℂ => Complex.normSq x) = fun x : ℂ => x.re * x.re + x.im * x.im := by
      funext x; rw [Complex.normSq_apply]
    rw [h]
    exact ((Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff))
  have hζsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ := by
    rw [hζdef]
    exact Real.smoothTransition.contDiff.comp ((hns.sub contDiff_const).div_const _)
  refine ⟨W', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hW'def]
    refine ContDiff.mul hW ?_
    refine Complex.contDiff_exp.comp ?_
    refine (Complex.ofRealCLM.contDiff.comp ?_).mul contDiff_const
    exact ((hζsm.comp contDiff_fst).mul (hbsm.comp contDiff_snd)).mul (hψ.comp contDiff_fst)
  · intro p hp
    have hb0 : b p.2 = 0 := by
      rw [hbdef]
      exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonneg_of_nonpos hp hτ₁.le)
    show W p * Complex.exp ((((ζ p.1 * b p.2 * ψ p.1 : ℝ)) : ℂ) * Complex.I) = W p
    rw [hb0]
    simp
  · intro p hτ hx
    show W p * Complex.exp ((((ζ p.1 * b p.2 * ψ p.1 : ℝ)) : ℂ) * Complex.I) ≠ 0
    exact mul_ne_zero (hWne p hτ hx) (Complex.exp_ne_zero _)
  · intro p hτ hx
    show ‖W p * Complex.exp ((((ζ p.1 * b p.2 * ψ p.1 : ℝ)) : ℂ) * Complex.I)‖ = ‖W p‖
    rw [norm_mul]
    have hθre : (((((ζ p.1 * b p.2 * ψ p.1 : ℝ)) : ℂ) * Complex.I)).re = 0 := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    rw [Complex.norm_exp, hθre, Real.exp_zero, mul_one]
  · intro x hx
    have hx' : 1 / 4 ≤ ‖x‖ := by linarith
    have hMx : M (x, τ₁) ≠ 0 := hMne (x, τ₁) hτ₁.le hx'
    have hWx : W (x, τ₁) ≠ 0 := hWne (x, τ₁) hτ₁.le hx'
    have hζ1 : ζ x = 1 := by
      rw [hζdef]
      show Real.smoothTransition ((Complex.normSq x - 1 / 16) / (3 / 16)) = 1
      refine Real.smoothTransition.one_of_one_le ?_
      have hnsx : (1 / 4 : ℝ) ≤ Complex.normSq x := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [hx, norm_nonneg x]
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3 / 16)]
      linarith
    have hb1 : b τ₁ = 1 := by
      rw [hbdef]
      show Real.smoothTransition (τ₁ / τ₁) = 1
      rw [div_self (ne_of_lt hτ₁)]
      exact Real.smoothTransition.one_of_one_le le_rfl
    have hdir : dirDatum M W' (x, τ₁)
        = dirDatum M W (x, τ₁) * Complex.exp (((ψ x : ℝ) : ℂ) * Complex.I) := by
      show dirDatum M
          (fun q : ℂ × ℝ =>
            W q * Complex.exp ((((ζ q.1 * b q.2 * ψ q.1 : ℝ)) : ℂ) * Complex.I)) (x, τ₁) = _
      rw [dirDatum_mul_exp M W (fun q : ℂ × ℝ => ζ q.1 * b q.2 * ψ q.1) (x, τ₁) hMx hWx]
      have harg : ζ x * b τ₁ * ψ x = ψ x := by rw [hζ1, hb1]; ring
      rw [harg]
    rw [hdir, hψspec x hx]
    have hmul : dirDatum M W (x, τ₁) * star (dirDatum M W (x, τ₁)) = 1 := by
      have h1 : Complex.normSq (dirDatum M W (x, τ₁)) = 1 := by
        rw [Complex.normSq_eq_norm_sq, norm_dirDatum hMx hWx]
        norm_num
      have h2 := Complex.mul_conj (dirDatum M W (x, τ₁))
      rw [h1] at h2
      simpa using h2
    calc dirDatum M W (x, τ₁) * (c * star (dirDatum M W (x, τ₁)))
        = c * (dirDatum M W (x, τ₁) * star (dirDatum M W (x, τ₁))) := by ring
      _ = c * 1 := by rw [hmul]
      _ = c := by ring

end

end Work.Drive
