/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# A globally smooth model of the polar chart

`Work.NN.Final.polarChart n ρ j z = (z, log (ρ j / ‖z j‖))` is smooth only where `z j ≠ 0`.
For the composition estimate of the Hölder norms along the polar chart we need a *globally*
smooth map with globally bounded derivatives which agrees with `polarChart` on the annular
region `ε < ‖z j‖` where the chart is applied.

Here we build it out of the clamped logarithmic coordinate `ChartComp.tau0 (4 ε) j`, whose
clamping thresholds are `(4 ε)/8 = ε/2` and `(4 ε)/4 = ε`: it equals `log (4 ε) - log r` for
`r ≥ ε`, and is constant (`log 4`) for `r ≤ ε/2`.  Adding the constant
`log (ρ j / (4 ε))` therefore produces a function which equals `log (ρ j / r)` for `r ≥ ε`.

The interest of this construction is that the whole theory of the clamped coordinate
(`contDiff_tau0`, `exists_bound_Tfun`, `exists_bound_tau0`) is already available, so the
analytic work needed for the global bounds is bookkeeping.
-/
import Mathlib
import Submission.Work.NN.Final.ChartComp.holderNorm_comp_chartPoint

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Final

/-- The clamped logarithmic coordinate of the global model of the polar chart: the clamped
logarithm of the modulus `log (ρ j) - log ‖z j‖` for `‖z j‖ ≥ ε`, and a constant on the disc
`‖z j‖ ≤ ε / 2`. -/
def polarLogCoord (n : ℕ) (ρ : Fin n → ℝ) (j : Fin n) (ε : ℝ) (z : Fin n → ℂ) : ℝ :=
  Real.log (ρ j / (4 * ε)) + ChartComp.tau0 (fun _ : Fin n => 4 * ε) j (z j)

/-- The globally smooth model of the polar chart: the identity in the first coordinate and the
clamped logarithmic coordinate in the second. -/
def polarGlob (n : ℕ) (ρ : Fin n → ℝ) (j : Fin n) (ε : ℝ) :
    (Fin n → ℂ) → (Fin n → ℂ) × ℝ :=
  fun z => (z, polarLogCoord n ρ j ε z)

@[simp] lemma polarGlob_apply (n : ℕ) (ρ : Fin n → ℝ) (j : Fin n) (ε : ℝ)
    (z : Fin n → ℂ) : polarGlob n ρ j ε z = (z, polarLogCoord n ρ j ε z) := rfl

lemma polarGlob_fst (n : ℕ) (ρ : Fin n → ℝ) (j : Fin n) (ε : ℝ)
    (z : Fin n → ℂ) : (polarGlob n ρ j ε z).1 = z := rfl

lemma polarGlob_snd (n : ℕ) (ρ : Fin n → ℝ) (j : Fin n) (ε : ℝ)
    (z : Fin n → ℂ) : (polarGlob n ρ j ε z).2 = polarLogCoord n ρ j ε z := rfl

lemma polarLogCoord_apply (n : ℕ) (ρ : Fin n → ℝ) (j : Fin n) (ε : ℝ) (z : Fin n → ℂ) :
    polarLogCoord n ρ j ε z
      = Real.log (ρ j / (4 * ε)) + ChartComp.tau0 (fun _ : Fin n => 4 * ε) j (z j) := rfl

/-- The clamped logarithmic coordinate is `log (ρ j) - log ‖z j‖` as soon as `ε ≤ ‖z j‖`. -/
lemma polarLogCoord_eq_log {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} {ε : ℝ} (hε : 0 < ε)
    (hρ : 0 < ρ j) {z : Fin n → ℂ} (hz : ε ≤ ‖z j‖) :
    polarLogCoord n ρ j ε z = Real.log (ρ j) - Real.log ‖z j‖ := by
  have hr : 0 < ‖z j‖ := lt_of_lt_of_le hε hz
  have hstep : radialStep (((fun _ : Fin n => 4 * ε) j) / 8) (((fun _ : Fin n => 4 * ε) j) / 4)
      ‖z j‖ = 1 := by
    apply radialStep_of_ge
    · simp only; linarith
    · simp only; linarith
  have hT : ChartComp.Tfun (fun _ : Fin n => 4 * ε) j ‖z j‖
      = Real.log (4 * ε) - Real.log ‖z j‖ := by
    rw [ChartComp.Tfun, hstep]
    ring
  have hlog : Real.log (ρ j / (4 * ε)) = Real.log (ρ j) - Real.log (4 * ε) :=
    Real.log_div (ne_of_gt hρ) (by positivity)
  rw [polarLogCoord_apply, ChartComp.tau0_eq_Tfun, hT, hlog]
  ring

/-! ## Smoothness and global derivative bounds of the model -/

/-- The global model `polarGlob n ρ j ε` is smooth. -/
theorem contDiff_polarGlob {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (polarGlob n ρ j ε) := by
  have h4ε : (0 : ℝ) < 4 * ε := by linarith
  have hτc : ContDiff ℝ (⊤ : ℕ∞) (ChartComp.tau0 (fun _ : Fin n => 4 * ε) j) :=
    ChartComp.contDiff_tau0 h4ε
  have hproj : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Fin n → ℂ => ChartComp.tau0 (fun _ : Fin n => 4 * ε) j (z j)) :=
    hτc.comp (ContinuousLinearMap.proj (R := ℝ) j : (Fin n → ℂ) →L[ℝ] ℂ).contDiff
  have hconst : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : Fin n → ℂ => Real.log (ρ j / (4 * ε))) := contDiff_const
  have hsec : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℂ => polarLogCoord n ρ j ε z) := by
    simpa only [polarLogCoord_apply] using hconst.add hproj
  exact contDiff_id.prodMk hsec

lemma contDiff_polarLogCoord {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℂ => polarLogCoord n ρ j ε z) := by
  have h4ε : (0 : ℝ) < 4 * ε := by linarith
  have hτc : ContDiff ℝ (⊤ : ℕ∞) (ChartComp.tau0 (fun _ : Fin n => 4 * ε) j) :=
    ChartComp.contDiff_tau0 h4ε
  have hproj : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Fin n → ℂ => ChartComp.tau0 (fun _ : Fin n => 4 * ε) j (z j)) :=
    hτc.comp (ContinuousLinearMap.proj (R := ℝ) j : (Fin n → ℂ) →L[ℝ] ℂ).contDiff
  have hconst : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : Fin n → ℂ => Real.log (ρ j / (4 * ε))) := contDiff_const
  simpa only [polarLogCoord_apply] using hconst.add hproj

/-- The model has globally bounded derivatives of every positive order. -/
theorem exists_bound_iteratedFDeriv_polarGlob {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} {ε : ℝ}
    (hε : 0 < ε) :
    ∃ D : ℕ → ℝ, ∀ k : ℕ, 1 ≤ k → ∀ z : Fin n → ℂ,
      ‖iteratedFDeriv ℝ k (polarGlob n ρ j ε) z‖ ≤ D k := by
  have h4ε : (0 : ℝ) < 4 * ε := by linarith
  obtain ⟨Dτ, hDτ⟩ := ChartComp.exists_bound_tau0 (ρ := fun _ : Fin n => 4 * ε) (i := j) h4ε
  have hτc : ContDiff ℝ (⊤ : ℕ∞) (ChartComp.tau0 (fun _ : Fin n => 4 * ε) j) :=
    ChartComp.contDiff_tau0 h4ε
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℂ => polarLogCoord n ρ j ε z) :=
    contDiff_polarLogCoord hε
  refine ⟨fun k => 1 + Dτ k, fun k hk z => ?_⟩
  have hprod := iteratedFDeriv_prodMk (f := fun z : Fin n → ℂ => z)
    (g := fun z : Fin n → ℂ => polarLogCoord n ρ j ε z) (x := z)
    contDiff_id.contDiffAt (hg.contDiffAt) (ChartComp.natCast_le_top_nat k)
  have e : polarGlob n ρ j ε = fun z : Fin n → ℂ => (z, polarLogCoord n ρ j ε z) := rfl
  rw [e, hprod]
  refine le_trans (ChartComp.norm_prod_le _ _) ?_
  have h1 : ‖iteratedFDeriv ℝ k (fun z : Fin n → ℂ => z) z‖ ≤ 1 :=
    le_trans (ChartComp.norm_iteratedFDeriv_clm_le (ContinuousLinearMap.id ℝ (Fin n → ℂ)) k hk z)
      ContinuousLinearMap.norm_id_le
  have h2 : ‖iteratedFDeriv ℝ k (fun z : Fin n → ℂ => polarLogCoord n ρ j ε z) z‖ ≤ Dτ k := by
    have hsplit : (fun z : Fin n → ℂ => polarLogCoord n ρ j ε z)
        = (fun _ : Fin n → ℂ => Real.log (ρ j / (4 * ε)))
          + (fun z : Fin n → ℂ => ChartComp.tau0 (fun _ : Fin n => 4 * ε) j (z j)) := by
      funext w
      rw [polarLogCoord_apply, Pi.add_apply]
    have hAt : ContDiffAt ℝ ((k : ℕ∞) : WithTop ℕ∞)
        (fun z : Fin n → ℂ => ChartComp.tau0 (fun _ : Fin n => 4 * ε) j (z j)) z :=
      (hτc.contDiffAt.comp z ((ContinuousLinearMap.proj (R := ℝ) j :
        (Fin n → ℂ) →L[ℝ] ℂ).contDiff.contDiffAt)).of_le (ChartComp.natCast_le_top_nat k)
    have hAdd : iteratedFDeriv ℝ k (fun z : Fin n → ℂ => polarLogCoord n ρ j ε z) z
        = iteratedFDeriv ℝ k
            (fun z : Fin n → ℂ => ChartComp.tau0 (fun _ : Fin n => 4 * ε) j (z j)) z := by
      rw [hsplit, iteratedFDeriv_add_apply (contDiffAt_const) hAt,
        iteratedFDeriv_const_of_ne (𝕜 := ℝ) (by omega : k ≠ 0)]
      simp
    rw [hAdd]
    have hstep := ChartComp.norm_iteratedFDeriv_comp_clm_right
      (ContinuousLinearMap.proj (R := ℝ) j : (Fin n → ℂ) →L[ℝ] ℂ) hτc k z
    refine le_trans hstep ?_
    have h1' : ‖(ContinuousLinearMap.proj (R := ℝ) j : (Fin n → ℂ) →L[ℝ] ℂ)‖ ^ k ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (ChartComp.norm_proj_le j)
    calc ‖iteratedFDeriv ℝ k (ChartComp.tau0 (fun _ : Fin n => 4 * ε) j) (z j)‖
          * ‖(ContinuousLinearMap.proj (R := ℝ) j : (Fin n → ℂ) →L[ℝ] ℂ)‖ ^ k
        ≤ ‖iteratedFDeriv ℝ k (ChartComp.tau0 (fun _ : Fin n => 4 * ε) j) (z j)‖ * 1 :=
          mul_le_mul_of_nonneg_left h1' (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ k (ChartComp.tau0 (fun _ : Fin n => 4 * ε) j) (z j)‖ := mul_one _
      _ ≤ Dτ k := hDτ k hk (z j)
  linarith

/-- The model is globally Lipschitz. -/
theorem exists_lipschitz_polarGlob {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} {ε : ℝ} (_hε : 0 < ε)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) (polarGlob n ρ j ε)) (D : ℕ → ℝ)
    (hD : ∀ k : ℕ, 1 ≤ k → ∀ z : Fin n → ℂ,
      ‖iteratedFDeriv ℝ k (polarGlob n ρ j ε) z‖ ≤ D k) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : Fin n → ℂ,
      ‖polarGlob n ρ j ε x - polarGlob n ρ j ε y‖ ≤ L * ‖x - y‖ := by
  refine ⟨max (D 1) 0, le_max_right _ _, fun x y => ?_⟩
  have hdiff : ∀ z : Fin n → ℂ, DifferentiableAt ℝ (polarGlob n ρ j ε) z :=
    fun z => (hΨ.differentiable (by simp)).differentiableAt
  have hbound : ∀ z : Fin n → ℂ, ‖fderiv ℝ (polarGlob n ρ j ε) z‖ ≤ max (D 1) 0 := by
    intro z
    rw [← norm_iteratedFDeriv_one (polarGlob n ρ j ε)]
    exact le_trans (hD 1 le_rfl z) (le_max_left _ _)
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ)
    (f := polarGlob n ρ j ε) (C := max (D 1) 0) (fun z _ => hdiff z)
    (fun z _ => hbound z) convex_univ (Set.mem_univ x) (Set.mem_univ y)
  simpa only [norm_sub_rev] using h

/-- Every iterated derivative of the model is Hölder continuous of exponent `α < 1`. -/
theorem exists_holderE_polarGlob {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} {ε : ℝ} (_hε : 0 < ε)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) (polarGlob n ρ j ε)) (D : ℕ → ℝ)
    (hD : ∀ k : ℕ, 1 ≤ k → ∀ z : Fin n → ℂ,
      ‖iteratedFDeriv ℝ k (polarGlob n ρ j ε) z‖ ≤ D k) :
    ∃ E : ℕ → ℝ, ∀ k : ℕ, 1 ≤ k → ∀ x y : Fin n → ℂ,
      ‖iteratedFDeriv ℝ k (polarGlob n ρ j ε) x
        - iteratedFDeriv ℝ k (polarGlob n ρ j ε) y‖ ≤ E k * ‖x - y‖ ^ α := by
  refine ⟨fun k => max (D (k + 1)) (2 * D k), fun k hk x y => ?_⟩
  have hDk : 0 ≤ D k := le_trans (norm_nonneg _) (hD k hk 0)
  have hDk1 : 0 ≤ D (k + 1) := le_trans (norm_nonneg _) (hD (k + 1) (by omega) 0)
  rcases eq_or_ne x y with rfl | hne
  · simp [Real.zero_rpow hα0.ne']
  · have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    rcases lt_or_ge (1 : ℝ) ‖x - y‖ with hxy | hxy
    · have hone : (1 : ℝ) ≤ ‖x - y‖ ^ α := Real.one_le_rpow hxy.le hα0.le
      calc ‖iteratedFDeriv ℝ k (polarGlob n ρ j ε) x
            - iteratedFDeriv ℝ k (polarGlob n ρ j ε) y‖
          ≤ ‖iteratedFDeriv ℝ k (polarGlob n ρ j ε) x‖
            + ‖iteratedFDeriv ℝ k (polarGlob n ρ j ε) y‖ := norm_sub_le _ _
        _ ≤ D k + D k := add_le_add (hD k hk x) (hD k hk y)
        _ = 2 * D k := by ring
        _ ≤ 2 * D k * ‖x - y‖ ^ α := le_mul_of_one_le_right (by linarith) hone
        _ ≤ max (D (k + 1)) (2 * D k) * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right (le_max_right _ _)
              (Real.rpow_nonneg (norm_nonneg _) α)
    · have hle : ‖x - y‖ ≤ ‖x - y‖ ^ α := by
        have h1 : ‖x - y‖ ^ α * ‖x - y‖ ^ (1 - α) = ‖x - y‖ := by
          rw [← Real.rpow_add hpos, show α + (1 - α) = 1 by ring, Real.rpow_one]
        have h2 : ‖x - y‖ ^ (1 - α) ≤ 1 :=
          Real.rpow_le_one (norm_nonneg _) hxy (sub_nonneg.mpr hα1.le)
        calc ‖x - y‖ = ‖x - y‖ ^ α * ‖x - y‖ ^ (1 - α) := h1.symm
          _ ≤ ‖x - y‖ ^ α * 1 :=
              mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (norm_nonneg _) α)
          _ = ‖x - y‖ ^ α := mul_one _
      have hdiff : ∀ z : Fin n → ℂ,
          DifferentiableAt ℝ (fun w => iteratedFDeriv ℝ k (polarGlob n ρ j ε) w) z := by
        intro z
        have h1 : ContDiff ℝ (1 : WithTop ℕ∞)
            (fun w => iteratedFDeriv ℝ k (polarGlob n ρ j ε) w) :=
          hΨ.iteratedFDeriv_right (i := k) (WithTop.coe_le_coe.mpr le_top)
        exact (h1.differentiable (by simp)).differentiableAt
      have hbound : ∀ z : Fin n → ℂ,
          ‖fderiv ℝ (fun w => iteratedFDeriv ℝ k (polarGlob n ρ j ε) w) z‖ ≤ D (k + 1) := by
        intro z
        rw [norm_fderiv_iteratedFDeriv]
        exact hD (k + 1) (by omega) z
      have hmvt : ‖iteratedFDeriv ℝ k (polarGlob n ρ j ε) x
          - iteratedFDeriv ℝ k (polarGlob n ρ j ε) y‖ ≤ D (k + 1) * ‖x - y‖ := by
        have h := Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ)
          (f := fun w => iteratedFDeriv ℝ k (polarGlob n ρ j ε) w) (C := D (k + 1))
          (fun z _ => hdiff z) (fun z _ => hbound z) convex_univ
          (Set.mem_univ x) (Set.mem_univ y)
        simpa only [norm_sub_rev] using h
      refine le_trans hmvt ?_
      calc D (k + 1) * ‖x - y‖ ≤ D (k + 1) * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_left hle hDk1
        _ ≤ max (D (k + 1)) (2 * D k) * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right (le_max_left _ _)
              (Real.rpow_nonneg (norm_nonneg _) α)

end Work.NN.Final
