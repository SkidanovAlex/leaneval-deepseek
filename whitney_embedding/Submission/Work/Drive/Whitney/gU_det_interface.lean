import Mathlib
import Submission.Work.Drive.Whitney.det_gU_on_square
import Submission.Work.Drive.Whitney.gTheta_eq_inner_gChi
import Submission.Work.Drive.Whitney.glFamilyAux

/-!
# The determinant of `gU`: pointwise form, the `(α + Θ)/(1 + Θ)` form, and `IsUnit`

`Work.Drive.Whitney.det_gU_on_square` computes the determinant of the operator family
`gU φ u w ψ` on the unit square, under the *global* hypotheses `φ = 1` on the square and
`ψ ⊥ u` everywhere.  This file records the three refinements a consumer (the `glAuxCore`
construction) actually needs:

* `det_gU_pointwise`: only the values at the single point `p` matter — `φ p = 1`,
  `u p ≠ 0` and `inner ℝ (ψ p) (u p) = 0` at `p` suffice.  In particular `ψ` need only be
  orthogonal to `u` *on the square*, not everywhere (this is what makes the construction of `ψ`
  tractable: one may modify `ψ` far away from the square).
* `det_gU_eq_div`: on the square and where `gAm φ u p ≠ 0`, the determinant equals
  `(α + Θ)/(1 + Θ)` with `α = gAl + gC` and `Θ = gTheta ≥ 0` (because `gLam = (1 - α)/(1 + Θ)`).
  In particular the determinant is *nonzero* as soon as `α + Θ ≠ 0`, and *positive* as soon as
  `α + Θ > 0`; and on the edges of the square (`u = w`, where `α = 1`) the determinant is `1`.
* `isUnit_gU_iff`: for endomorphisms of `EuclideanSpace ℝ (Fin m)`,
  `IsUnit f ↔ LinearMap.det f.toLinearMap ≠ 0`.

**Warning (see `Submission/Work/Drive/Whitney/NOTES_det_gU_consumer.md` §5).**  The missing input of
the `gU`-construction of `glAuxCore` is an *existence* statement: a smooth `ψ`, orthogonal to `u`
on the square, with the scalar `α + Θ = (gAl + gC) + gTheta ≠ 0` there.  That statement is
**FALSE**: the scalar equals `coefA + ‖opT ψ‖²` in the notation of `twoFieldsDefs`, and this is
refuted by the machine-checked counterexample `Work.Drive.Whitney.no_z_counterexample`
(`opTSquare_refute.lean`) together with `exists_psi_of_coefA_refute.lean`.  The obstruction is
topological (a winding/degree argument on the disk `{coefA ≤ 0}`), not a formalisation gap, and it
does not disappear if the edge hypotheses `u p = w p` are added.  Consequently the plan
"`U := gU φ u w ψ`" cannot prove `glAuxCore`; a proof of `glAuxCore` must use the full `GL(E)`
freedom (or the low-dimensional families of `glAuxCoreLowDim.lean`).  The lemmas below remain valid
and are exactly what is needed to *test* any candidate `ψ` against that obstruction.
-/

namespace Work.Drive.Whitney

open scoped RealInnerProductSpace

variable {m : ℕ}

/-! ## The pointwise determinant identity -/

/-- **Pointwise form of `det_gU_on_square`.**  For `m ≥ 3`, if at the point `p` we have
`φ p = 1`, `u p ≠ 0` and `ψ p ⊥ u p`, then the determinant of `gU φ u w ψ p` is
`(gAl + gC) + gLam * gTheta` at `p`.  Neither smoothness of the data nor global orthogonality of
`ψ` and `u` is used: the identity is purely about the values at `p`. -/
theorem det_gU_pointwise {m : ℕ} (hm : 3 ≤ m) (φ : ℝ × ℝ → ℝ)
    (u w ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m)) (p : ℝ × ℝ)
    (hφp : φ p = 1) (hup : u p ≠ 0) (hzup : inner ℝ (ψ p) (u p) = 0) :
    LinearMap.det ((gU φ u w ψ p).toLinearMap) =
      (gAl φ u w p + gC φ u w p) + gLam φ u w ψ p * gTheta φ u w ψ p := by
  have hU2 : inner ℝ (u p) (u p) = ‖u p‖ ^ 2 := real_inner_self_eq_norm_sq (u p)
  have hAm_in : gAm φ u p = inner ℝ (u p) (u p) := by
    simp only [gAm, hφp, one_mul, sub_self, add_zero]
  have hup_ne : inner ℝ (u p) (u p) ≠ 0 := by
    rw [hU2]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hup)
  have hAm_ne : gAm φ u p ≠ 0 := by rw [hAm_in]; exact hup_ne
  have hAl : gAl φ u w p = inner ℝ (w p) (u p) / gAm φ u p := rfl
  have hAe : gAm φ u p = ‖u p‖ ^ 2 := hAm_in.trans hU2
  have hN : ‖gNn φ u w p‖ ^ 2 = gN φ u w p := by
    rw [gN, real_inner_self_eq_norm_sq]
  have hGZ : gZ φ u w ψ p = gLam φ u w ψ p • ψ p := rfl
  have hna : inner ℝ (gNn φ u w p) (u p) = 0 := by
    rw [gNn, gAl, inner_sub_left, real_inner_smul_left, hAm_in]
    rw [div_mul_cancel₀ _ hup_ne, sub_self]
  have hchi_u : inner ℝ (gChi φ u w ψ p) (u p) = 0 := by
    rw [gChi, inner_sub_left, real_inner_smul_left, real_inner_smul_left, hzup, hna]
    ring
  have hzu_z : inner ℝ (gZ φ u w ψ p) (u p) = 0 := by
    rw [hGZ, real_inner_smul_left, hzup, mul_zero]
  have hGU : gU φ u w ψ p = gUexp (u p) (w p) (gZ φ u w ψ p) (gChi φ u w ψ p) := by
    simp only [gU, gUexp, gCfam, gJ, gPu, gAl, gNn, gAm, hφp,
      real_inner_self_eq_norm_sq, one_div, one_smul, one_mul, sub_self, add_zero]
  rw [hGU]
  rw [det_gUexp hm (u p) (w p) (gZ φ u w ψ p) (gChi φ u w ψ p) hup hzu_z hchi_u]
  rw [← hAe, ← hAl, ← gNn, hN, hGZ, real_inner_smul_left, real_inner_smul_right]
  rw [det_alg (ψ := ψ p) (nn := gNn φ u w p) (χ := gChi φ u w ψ p)
    (A := gAm φ u p) (a := gAl φ u w p) (N := gN φ u w p) (lam := gLam φ u w ψ p)]
  rfl

/-! ## `gTheta` is a square, and the determinant in closed form -/

/-- `gTheta = ⟪χ, χ⟫ ≥ 0` wherever `gAm` does not vanish. -/
lemma gTheta_nonneg (φ : ℝ × ℝ → ℝ) (u w ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (p : ℝ × ℝ) (hAm : gAm φ u p ≠ 0) : 0 ≤ gTheta φ u w ψ p := by
  rw [gTheta_eq_inner_gChi u w ψ φ p hAm]
  exact real_inner_self_nonneg

/-- `1 + gTheta > 0` wherever `gAm` does not vanish (so that `gLam` is a regular function). -/
lemma one_add_gTheta_pos (φ : ℝ × ℝ → ℝ) (u w ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (p : ℝ × ℝ) (hAm : gAm φ u p ≠ 0) : 0 < 1 + gTheta φ u w ψ p := by
  have := gTheta_nonneg φ u w ψ p hAm
  linarith

/-- **The determinant on the square, in closed form.**  With `α = gAl + gC` and `Θ = gTheta ≥ 0`,
`det (gU φ u w ψ p) = (α + Θ)/(1 + Θ)` — this is `gLam = (1 - α)/(1 + Θ)` substituted into
`det = α + gLam * Θ`. -/
theorem det_gU_eq_div {m : ℕ} (hm : 3 ≤ m) (φ : ℝ × ℝ → ℝ)
    (u w ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m)) (p : ℝ × ℝ)
    (hφp : φ p = 1) (hup : u p ≠ 0) (hzup : inner ℝ (ψ p) (u p) = 0)
    (hAm : gAm φ u p ≠ 0) :
    LinearMap.det ((gU φ u w ψ p).toLinearMap) =
      ((gAl φ u w p + gC φ u w p) + gTheta φ u w ψ p) / (1 + gTheta φ u w ψ p) := by
  rw [det_gU_pointwise hm φ u w ψ p hφp hup hzup]
  have hne : 1 + gTheta φ u w ψ p ≠ 0 := ne_of_gt (one_add_gTheta_pos φ u w ψ p hAm)
  unfold gLam
  field_simp
  ring

/-- Nonvanishing of the determinant on the square, reduced to the scalar `α + Θ`. -/
theorem det_gU_ne_zero_iff {m : ℕ} (hm : 3 ≤ m) (φ : ℝ × ℝ → ℝ)
    (u w ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m)) (p : ℝ × ℝ)
    (hφp : φ p = 1) (hup : u p ≠ 0) (hzup : inner ℝ (ψ p) (u p) = 0)
    (hAm : gAm φ u p ≠ 0) :
    LinearMap.det ((gU φ u w ψ p).toLinearMap) ≠ 0 ↔
      (gAl φ u w p + gC φ u w p) + gTheta φ u w ψ p ≠ 0 := by
  rw [det_gU_eq_div hm φ u w ψ p hφp hup hzup hAm]
  have hne : 1 + gTheta φ u w ψ p ≠ 0 := ne_of_gt (one_add_gTheta_pos φ u w ψ p hAm)
  rw [div_ne_zero_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, hne⟩⟩

/-! ## `IsUnit` versus nonvanishing determinant -/

/-- For an endomorphism of `EuclideanSpace ℝ (Fin m)`, being a unit is the same as having
nonvanishing determinant. -/
theorem isUnit_clm_iff_det_ne_zero {m : ℕ}
    (f : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    IsUnit f ↔ LinearMap.det f.toLinearMap ≠ 0 := by
  have h1 : IsUnit f ↔ IsUnit f.toLinearMap := by
    rw [ContinuousLinearMap.isUnit_iff_bijective, Module.End.isUnit_iff]
    exact Iff.rfl
  rw [h1, LinearMap.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- **`IsUnit (gU φ u w ψ p)` on the square, reduced to the scalar `α + Θ`.** -/
theorem isUnit_gU_iff {m : ℕ} (hm : 3 ≤ m) (φ : ℝ × ℝ → ℝ)
    (u w ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m)) (p : ℝ × ℝ)
    (hφp : φ p = 1) (hup : u p ≠ 0) (hzup : inner ℝ (ψ p) (u p) = 0)
    (hAm : gAm φ u p ≠ 0) :
    IsUnit (gU φ u w ψ p) ↔
      (gAl φ u w p + gC φ u w p) + gTheta φ u w ψ p ≠ 0 := by
  rw [isUnit_clm_iff_det_ne_zero, det_gU_ne_zero_iff hm φ u w ψ p hφp hup hzup hAm]

/-- The forward direction of `isUnit_gU_iff`, in the form a construction uses: if the scalar
`α + Θ` is nonzero at `p` then `gU φ u w ψ p` is invertible. -/
theorem isUnit_gU_of_scalar_ne_zero {m : ℕ} (hm : 3 ≤ m) (φ : ℝ × ℝ → ℝ)
    (u w ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m)) (p : ℝ × ℝ)
    (hφp : φ p = 1) (hup : u p ≠ 0) (hzup : inner ℝ (ψ p) (u p) = 0)
    (hAm : gAm φ u p ≠ 0)
    (hsc : (gAl φ u w p + gC φ u w p) + gTheta φ u w ψ p ≠ 0) :
    IsUnit (gU φ u w ψ p) :=
  (isUnit_gU_iff hm φ u w ψ p hφp hup hzup hAm).mpr hsc


/-! ## The two action properties of `gU` on the square

These are the remaining conjuncts of `glAuxCore` for the specific family `U := gU φ u w ψ`: the
prescribed action `U p (u p) = w p` and the triviality `U p = 1` on the edges (where `u p = w p`).
Both are proved pointwise; the pointwise orthogonality `inner ℝ (ψ p) (u p) = 0` is needed only for
the first. -/

/-- `gU φ u w ψ p (u p) = w p` (at a point where `φ = 1`, `u p ≠ 0` and `ψ p ⊥ u p`). -/
theorem gU_apply_u {m : ℕ} (φ : ℝ × ℝ → ℝ) (u w ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (p : ℝ × ℝ) (hφp : φ p = 1) (hup : u p ≠ 0) (hzup : inner ℝ (ψ p) (u p) = 0) :
    gU φ u w ψ p (u p) = w p := by
  have hISL : ∀ x y : EuclideanSpace ℝ (Fin m), (innerSL ℝ x) y = inner ℝ x y := fun x y => rfl
  have hAm_in : gAm φ u p = inner ℝ (u p) (u p) := by
    simp only [gAm, hφp, one_mul, sub_self, add_zero]
  have hup_ne : inner ℝ (u p) (u p) ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hup)
  have hna : inner ℝ (gNn φ u w p) (u p) = 0 := by
    rw [gNn, gAl, inner_sub_left, real_inner_smul_left, hAm_in]
    rw [div_mul_cancel₀ _ hup_ne, sub_self]
  have hJ : gJ φ u w p (u p) = gNn φ u w p := by
    rw [gJ]
    simp only [smul_apply, sub_apply, ContinuousLinearMap.smulRight_apply, hISL]
    rw [hAm_in, hna, zero_smul, sub_zero, smul_smul, inv_mul_cancel₀ hup_ne, one_smul]
  have hPu : gPu φ u p (u p) = u p := by
    rw [gPu]
    simp only [smul_apply, ContinuousLinearMap.smulRight_apply, hISL]
    rw [hAm_in, smul_smul, inv_mul_cancel₀ hup_ne, one_smul]
  have hz : inner ℝ (gZ φ u w ψ p) (u p) = 0 := by
    rw [gZ, real_inner_smul_left, hzup, mul_zero]
  have hC : gCfam φ u w ψ p (u p) = 0 := by
    rw [gCfam]
    simp only [add_apply, sub_apply, one_apply_eq_self, ContinuousLinearMap.smulRight_apply, hISL]
    rw [hz, zero_smul, hPu, sub_self, add_zero]
  have h1mPu : u p - gPu φ u p (u p) = 0 := by rw [hPu, sub_self]
  have hC0 : gCfam φ u w ψ p (u p - gPu φ u p (u p))
      - gAl φ u w p • (u p - gPu φ u p (u p)) = 0 := by
    rw [h1mPu, smul_zero, map_zero, sub_zero]
  rw [gU]
  simp only [add_apply, smul_apply, mul_apply_eq_comp, sub_apply, one_apply_eq_self]
  rw [hC0, hJ, add_zero]
  rw [gNn]
  abel

/-- `gU φ u w ψ p = 1` at a point where `φ = 1` and `u p = w p ≠ 0` (the two edges). -/
theorem gU_eq_one_of_apply_eq {m : ℕ} (φ : ℝ × ℝ → ℝ)
    (u w ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m)) (p : ℝ × ℝ)
    (hφp : φ p = 1) (hup : u p ≠ 0) (huw : u p = w p) :
    gU φ u w ψ p = 1 := by
  have hAm_in : gAm φ u p = inner ℝ (u p) (u p) := by
    simp only [gAm, hφp, one_mul, sub_self, add_zero]
  have hup_ne : inner ℝ (u p) (u p) ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hup)
  have hww_ne : inner ℝ (w p) (w p) ≠ 0 := by rw [← huw]; exact hup_ne
  have hAl_one : gAl φ u w p = 1 := by
    rw [gAl, hAm_in, huw]
    exact div_self hww_ne
  have hNn_zero : gNn φ u w p = 0 := by
    rw [gNn, hAl_one, huw, one_smul, sub_self]
  have hN_zero : gN φ u w p = 0 := by rw [gN, hNn_zero]; simp
  have hC_zero : gC φ u w p = 0 := by rw [gC, hN_zero, zero_div]
  have hJ_zero : gJ φ u w p = 0 := by
    rw [gJ, hNn_zero]
    simp [ContinuousLinearMap.smulRight_zero, ContinuousLinearMap.zero_smulRight]
  have hLam_zero : gLam φ u w ψ p = 0 := by rw [gLam, hAl_one, hC_zero]; norm_num
  have hZ_zero : gZ φ u w ψ p = 0 := by rw [gZ, hLam_zero, zero_smul]
  have hCfam_eq : gCfam φ u w ψ p = 1 - gPu φ u p := by
    rw [gCfam, hZ_zero]
    have h0 : (innerSL ℝ (0 : EuclideanSpace ℝ (Fin m)) :
        EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) = 0 := by simp
    rw [h0, ContinuousLinearMap.zero_smulRight, add_zero]
  have hPu_idem : gPu φ u p * gPu φ u p = gPu φ u p := by
    have hISL : ∀ x y : EuclideanSpace ℝ (Fin m), (innerSL ℝ x) y = inner ℝ x y :=
      fun x y => rfl
    rw [gPu]
    apply ContinuousLinearMap.ext
    intro v
    simp only [mul_apply_eq_comp, smul_apply, ContinuousLinearMap.smulRight_apply, hISL,
      real_inner_smul_right]
    rw [hAm_in, smul_smul]
    rw [show (inner ℝ (u p) (u p))⁻¹ *
          ((inner ℝ (u p) (u p))⁻¹ * (inner ℝ (u p) v * inner ℝ (u p) (u p)))
        = (inner ℝ (u p) (u p))⁻¹ * inner ℝ (u p) v from by
      field_simp
      try ring]
    rw [← smul_smul]
  have hkey : (1 - gPu φ u p - 1) * (1 - gPu φ u p) = 0 := by
    rw [sub_mul, sub_mul, one_mul, mul_sub, mul_one, hPu_idem]
    abel
  rw [gU, hAl_one, hJ_zero, hCfam_eq, one_smul, hkey]
  simp

/-! ## The cutoff `φ`

`glAuxCore` needs a smooth `φ` which is `1` on the square and for which the modified scalar
`gAm φ u = φ * ⟪u,u⟫ + (1 - φ)` never vanishes (this is the standing hypothesis of `contDiff_gU`
and of the determinant identity of this file).  The construction is the box bump of
`glFamilyAux`: `φ p := sBump 1 p.1 * sBump 1 p.2`.  It is `1` exactly on the square, and its values
lie in `[0,1]`; hence `gAm φ u p = 1` where `φ p = 0`, and `gAm φ u p ≥ 1 - φ p > 0` where
`0 < φ p < 1`, while `φ p = 1` forces `p ∈ [0,1]²`, where `u p ≠ 0` makes
`gAm φ u p = ‖u p‖² > 0`.  (No compactness/thickening argument is needed: the only dangerous
configuration would be `φ p = 1` together with `u p = 0`.) -/

lemma sBump_nonneg' (ε : ℝ) (x : ℝ) : 0 ≤ sBump ε x := by
  simp only [sBump]
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma sBump_le_one' (ε : ℝ) (x : ℝ) : sBump ε x ≤ 1 := by
  have h1 : Real.smoothTransition ((x + ε) / ε) ≤ 1 := Real.smoothTransition.le_one _
  have h2 : Real.smoothTransition ((1 + ε - x) / ε) ≤ 1 := Real.smoothTransition.le_one _
  have h3 : 0 ≤ Real.smoothTransition ((x + ε) / ε) := Real.smoothTransition.nonneg _
  have h4 : 0 ≤ Real.smoothTransition ((1 + ε - x) / ε) := Real.smoothTransition.nonneg _
  simp only [sBump]
  nlinarith

/-- `sBump ε x = 1` forces `x ∈ [0,1]` (for `ε > 0`). -/
lemma sBump_eq_one_imp {ε : ℝ} (hε : 0 < ε) {x : ℝ} (h : sBump ε x = 1) :
    x ∈ Set.Icc (0:ℝ) 1 := by
  have hfac : sBump ε x = Real.smoothTransition ((x + ε) / ε) *
      Real.smoothTransition ((1 + ε - x) / ε) := rfl
  rw [hfac] at h
  have hf1 : Real.smoothTransition ((x + ε) / ε) = 1 := by
    have hle1 : Real.smoothTransition ((x + ε) / ε) ≤ 1 := Real.smoothTransition.le_one _
    have hnn1 : 0 ≤ Real.smoothTransition ((x + ε) / ε) := Real.smoothTransition.nonneg _
    have hle2 : Real.smoothTransition ((1 + ε - x) / ε) ≤ 1 := Real.smoothTransition.le_one _
    have hnn2 : 0 ≤ Real.smoothTransition ((1 + ε - x) / ε) := Real.smoothTransition.nonneg _
    nlinarith
  have hf2 : Real.smoothTransition ((1 + ε - x) / ε) = 1 := by
    have hle1 : Real.smoothTransition ((x + ε) / ε) ≤ 1 := Real.smoothTransition.le_one _
    have hnn1 : 0 ≤ Real.smoothTransition ((x + ε) / ε) := Real.smoothTransition.nonneg _
    have hle2 : Real.smoothTransition ((1 + ε - x) / ε) ≤ 1 := Real.smoothTransition.le_one _
    have hnn2 : 0 ≤ Real.smoothTransition ((1 + ε - x) / ε) := Real.smoothTransition.nonneg _
    nlinarith
  have h1 : 1 ≤ (x + ε) / ε := Real.smoothTransition.eq_one_iff_one_le.mp hf1
  have h2 : 1 ≤ (1 + ε - x) / ε := Real.smoothTransition.eq_one_iff_one_le.mp hf2
  rw [le_div_iff₀ hε] at h1 h2
  exact ⟨by linarith, by linarith⟩

/-- **The cutoff `φ` of the `gU` construction**: a smooth `φ` with values in `[0,1]`, equal to `1`
on the square `K = [0,1]²`, and with `gAm φ u` nowhere zero. -/
theorem exists_cutoff_gAm_pos {m : ℕ} (u : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (hune : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1, u p ≠ 0) :
    ∃ φ : ℝ × ℝ → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧
      (∀ p, 0 ≤ φ p ∧ φ p ≤ 1) ∧
      (∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1, φ p = 1) ∧
      (∀ p, 0 < gAm φ u p) := by
  have hpos : (0:ℝ) < 1 := one_pos
  set φ : ℝ × ℝ → ℝ := fun p => sBump 1 p.1 * sBump 1 p.2 with hφdef
  have hnn : ∀ p, 0 ≤ φ p := fun p => mul_nonneg (sBump_nonneg' 1 p.1) (sBump_nonneg' 1 p.2)
  have hle : ∀ p, φ p ≤ 1 := fun p => by
    have h1 := sBump_le_one' 1 p.1
    have h2 := sBump_le_one' 1 p.2
    have h3 := sBump_nonneg' 1 p.1
    have h4 := sBump_nonneg' 1 p.2
    show sBump 1 p.1 * sBump 1 p.2 ≤ 1
    nlinarith
  have hmem : ∀ p, φ p = 1 → p ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 := by
    intro p hp
    have hp' : sBump 1 p.1 * sBump 1 p.2 = 1 := hp
    have h1 : sBump 1 p.1 = 1 := by
      have hle1 := sBump_le_one' 1 p.1
      have hle2 := sBump_le_one' 1 p.2
      have hnn1 := sBump_nonneg' 1 p.1
      have hnn2 := sBump_nonneg' 1 p.2
      nlinarith
    have h2 : sBump 1 p.2 = 1 := by
      have hle1 := sBump_le_one' 1 p.1
      have hle2 := sBump_le_one' 1 p.2
      have hnn1 := sBump_nonneg' 1 p.1
      have hnn2 := sBump_nonneg' 1 p.2
      nlinarith
    exact ⟨sBump_eq_one_imp hpos h1, sBump_eq_one_imp hpos h2⟩
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · exact ((sBump_contDiff 1).comp contDiff_fst).mul ((sBump_contDiff 1).comp contDiff_snd)
  · exact fun p => ⟨hnn p, hle p⟩
  · intro p hp
    show sBump 1 p.1 * sBump 1 p.2 = 1
    rw [sBump_eq_one hpos hp.1, sBump_eq_one hpos hp.2, mul_one]
  · intro p
    rw [gAm]
    rcases eq_or_lt_of_le (hnn p) with h0 | h0
    · rw [← h0]; norm_num
    · by_cases h1 : φ p = 1
      · have hup : u p ≠ 0 := hune p (hmem p h1)
        rw [h1, one_mul, sub_self, add_zero, real_inner_self_eq_norm_sq]
        exact pow_pos (norm_pos_iff.mpr hup) 2
      · have hlt : φ p < 1 := lt_of_le_of_ne (hle p) h1
        have hnn2 : (0:ℝ) ≤ inner ℝ (u p) (u p) := real_inner_self_nonneg
        nlinarith

end Work.Drive.Whitney
