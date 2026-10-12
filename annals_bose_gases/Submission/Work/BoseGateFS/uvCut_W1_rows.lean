import ChallengeDeps
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.uvCut_W1_rows` — the rows of the UV-cut `Ŵ₁`

`BOSE_BOXFOCK_LEAD.md` §7 item 2 (`Submission/Work/BoseGateFS/README.md`): the honest
bundle of the §10 gate uses `Ŵ₁` **with a UV cut-off**, `W1f := ζ_Λ·Ŵ₁` with
`ζ_Λ(p) = f_u(‖p‖/Λ)` (`Work.BoseBoxFock.uvCut`), and needs the four analytic rows of
`W1f` (smoothness, the `Cw·a` bound, the decay row `|·|(1+‖p‖)² ≤ Cw·a`, the gradient row)
plus the normalisation `ζ_Λ = 1` on `‖p‖ ≤ Λ`, *derived from* the corresponding rows of
`Ŵ₁`.

This file proves exactly that inference.  The mathematical content is the analytic theory
of the radial cut-off:

* `ζ_Λ` is `C^∞`: its profile is constant `= 1` on the ball `‖p‖ < Λ` (where `‖·‖` is not
  differentiable), and off `0` it is a composition of smooth maps (`contDiff_radialCut`);
* `|deriv f_u| ≤ Cζ` makes the profile `Cζ`-Lipschitz (mean value theorem), hence `ζ_Λ`
  is `(Cζ/Λ)`-Lipschitz, hence its Fréchet derivative is bounded by `Cζ/Λ` at **every**
  point — including `0`, where the derivative vanishes (`lipschitz_radialCut`,
  `norm_fderiv_radialCut`);
* `0 ≤ f_u ≤ 1` (`abs_radialCut_le_one`).

The gradient row of the product then follows from the product rule
`fderiv (u·c) = u • fderiv c + c • fderiv u`, whose two terms cost
`Cw·a·(1+‖p‖)` and `(Cw·a)·(Cζ/Λ) ≤ (Cw·a)·(Cζ/Λ)·(1+‖p‖)` respectively.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Topology

namespace Work.BoseGateFS

/-- A `LowCut` profile is nonnegative and bounded by `1`
(`Work.BoseBoxFix.LowCut.nonneg`, `Work.BoseBoxFix.LowCut.le_one`); recorded here for the
radial cut-off. -/
theorem abs_radialCut_le_one {fu : Work.BoseBoxFix.LowCut} (Λ : ℝ)
    (p : EuclideanSpace ℝ (Fin 3)) : |fu.f (‖p‖ / Λ)| ≤ 1 := by
  rw [abs_of_nonneg (fu.nonneg _)]
  exact fu.le_one _

/-- **The radial cut-off is smooth.**  `p ↦ f_u(‖p‖/Λ)` is constant `1` on the ball of
radius `Λ` around `0` (the only point where `‖·‖` is not differentiable, and where the
composite is constantly `1` because `f_u = 1` on `(-∞,1]`), and elsewhere it is the
composition of `p ↦ ‖p‖/Λ` with the smooth profile. -/
theorem contDiff_radialCut {fu : Work.BoseBoxFix.LowCut} {Λ : ℝ} (hΛ : 0 < Λ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : EuclideanSpace ℝ (Fin 3) => fu.f (‖p‖ / Λ)) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  rcases eq_or_ne p 0 with rfl | hp
  · refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin 3)) hΛ] with x hx
    simp only [Metric.mem_ball, dist_zero_right] at hx
    exact fu.one _ ((div_le_one hΛ).mpr hx.le)
  · exact fu.smooth.contDiffAt.comp p ((contDiffAt_norm ℝ hp).div_const Λ)

/-- The profile `f_u` is `Cζ`-Lipschitz when `|deriv f_u| ≤ Cζ` (mean value theorem). -/
theorem abs_sub_le_of_deriv_le {f : ℝ → ℝ} (hdiff : ∀ x : ℝ, DifferentiableAt ℝ f x)
    {Cζ : ℝ} (hζ' : ∀ s : ℝ, |deriv f s| ≤ Cζ) (x y : ℝ) :
    |f x - f y| ≤ Cζ * |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := f) (s := Set.univ)
    (C := Cζ) (fun x _ => hdiff x) (fun x _ => by rw [Real.norm_eq_abs]; exact hζ' x)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using h

/-- The radial cut-off is `(Cζ/Λ)`-Lipschitz: the profile is `Cζ`-Lipschitz and
`‖·‖/Λ` is `(1/Λ)`-Lipschitz (reverse triangle inequality). -/
theorem lipschitz_radialCut {fu : Work.BoseBoxFix.LowCut} {Λ Cζ : ℝ} (hΛ : 0 < Λ)
    (hCζ : 0 ≤ Cζ) (hζ' : ∀ s : ℝ, |deriv fu.f s| ≤ Cζ) :
    LipschitzWith ⟨Cζ / Λ, div_nonneg hCζ hΛ.le⟩
      (fun p : EuclideanSpace ℝ (Fin 3) => fu.f (‖p‖ / Λ)) := by
  have hdiff : ∀ x : ℝ, DifferentiableAt ℝ fu.f x :=
    fun x => (fu.smooth.differentiable (by simp)) x
  have h1 : ∀ a b : ℝ, |fu.f a - fu.f b| ≤ Cζ * |a - b| :=
    fun a b => abs_sub_le_of_deriv_le hdiff hζ' a b
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have h3 : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
  calc dist (fu.f (‖x‖ / Λ)) (fu.f (‖y‖ / Λ))
      = |fu.f (‖x‖ / Λ) - fu.f (‖y‖ / Λ)| := Real.dist_eq _ _
    _ ≤ Cζ * |‖x‖ / Λ - ‖y‖ / Λ| := h1 _ _
    _ = Cζ * (|‖x‖ - ‖y‖| / Λ) := by rw [← sub_div, abs_div, abs_of_pos hΛ]
    _ ≤ Cζ * (‖x - y‖ / Λ) := by gcongr
    _ = (Cζ / Λ) * dist x y := by rw [dist_eq_norm, div_eq_mul_inv, div_eq_mul_inv]; ring

/-- **The derivative bound of the radial cut-off**, valid at *every* point (in particular
at `p = 0`, where the cut-off is locally constant): `‖fderiv (f_u(‖·‖/Λ)) p‖ ≤ Cζ/Λ`.
The converse mean value inequality applied to the Lipschitz estimate. -/
theorem norm_fderiv_radialCut {fu : Work.BoseBoxFix.LowCut} {Λ Cζ : ℝ} (hΛ : 0 < Λ)
    (hCζ : 0 ≤ Cζ) (hζ' : ∀ s : ℝ, |deriv fu.f s| ≤ Cζ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    ‖fderiv ℝ (fun q : EuclideanSpace ℝ (Fin 3) => fu.f (‖q‖ / Λ)) p‖ ≤ Cζ / Λ :=
  norm_fderiv_le_of_lipschitz (𝕜 := ℝ) (x₀ := p) (lipschitz_radialCut hΛ hCζ hζ')

set_option linter.unusedVariables false in
/-- **The rows of the UV-cut `Ŵ₁`** (`BOSE_BOXFOCK_LEAD.md` §7 item 2): the four analytic
rows of `W1f := ζ_Λ·Ŵ₁` and the normalisation `ζ_Λ = 1` on `‖p‖ ≤ Λ`, from the rows of
`Ŵ₁` (`hW1cd`, `hW1le`, `hW1decay`, `hW1grad`) and the profile bound `|deriv f_u| ≤ Cζ`.

The gradient row is the product rule `fderiv (u·c) p = u p • fderiv c p + c p • fderiv u p`:
the first term costs `Cw·a·(1+‖p‖)` and the second one `(Cw·a)·(Cζ/Λ)`, which is
`≤ (Cw·a)·(Cζ/Λ)·(1+‖p‖)` because `Cw·BoseGases.a v ≥ 0` (it dominates `|Ŵ₁|`, taken at
`p = 0`) and `1 ≤ 1+‖p‖`.  The `ζ_Λ` normalisation is `LowCut.one` below the cut-off. -/
theorem uvCut_W1_rows {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {ℓ Λ Cw : ℝ}
    (hℓ : 0 < ℓ) (hΛ : 1 ≤ Λ) (hCw : 0 ≤ Cw)
    (fu : Work.BoseBoxFix.LowCut) (Cζ : ℝ) (hCζ : 0 ≤ Cζ)
    (hζ' : ∀ s : ℝ, |deriv fu.f s| ≤ Cζ)
    (hW1cd : ContDiff ℝ 1 (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)))
    (hW1le : ∀ p : EuclideanSpace ℝ (Fin 3), |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| ≤ Cw * _root_.BoseGases.a v)
    (hW1decay : ∀ p : EuclideanSpace ℝ (Fin 3), |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| * (1 + ‖p‖) ^ 2 ≤ Cw * _root_.BoseGases.a v)
    (hW1grad : ∀ p : EuclideanSpace ℝ (Fin 3), ‖fderiv ℝ (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)) p‖ ≤ Cw * _root_.BoseGases.a v * (1 + ‖p‖)) :
    ContDiff ℝ 1 (fun p => Work.BoseBoxFock.uvCut fu Λ p * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p)
    ∧ (∀ p : EuclideanSpace ℝ (Fin 3), |Work.BoseBoxFock.uvCut fu Λ p * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| ≤ Cw * _root_.BoseGases.a v)
    ∧ (∀ p : EuclideanSpace ℝ (Fin 3), |Work.BoseBoxFock.uvCut fu Λ p * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| * (1 + ‖p‖) ^ 2 ≤ Cw * _root_.BoseGases.a v)
    ∧ (∀ p : EuclideanSpace ℝ (Fin 3), ‖fderiv ℝ (fun q => Work.BoseBoxFock.uvCut fu Λ q * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) p‖
        ≤ (Cw + Cw * Cζ / Λ) * _root_.BoseGases.a v * (1 + ‖p‖))
    ∧ (∀ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ≤ Λ → Work.BoseBoxFock.uvCut fu Λ p = 1) := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  -- `Ŵ₁` dominates the zero function, so `Cw * BoseGases.a v ≥ 0`
  have hCwa : 0 ≤ Cw * _root_.BoseGases.a v := le_trans (abs_nonneg _) (hW1le 0)
  have hB : 0 ≤ Cζ / Λ := div_nonneg hCζ hΛpos.le
  -- the radial cut-off rows
  have hu_cd : ContDiff ℝ (⊤ : ℕ∞) (fun p : EuclideanSpace ℝ (Fin 3) => fu.f (‖p‖ / Λ)) :=
    contDiff_radialCut hΛpos
  have hu_cd1 : ContDiff ℝ 1 (fun p : EuclideanSpace ℝ (Fin 3) => fu.f (‖p‖ / Λ)) :=
    hu_cd.of_le (by simp)
  have hu_fd : ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖fderiv ℝ (fun q : EuclideanSpace ℝ (Fin 3) => fu.f (‖q‖ / Λ)) p‖ ≤ Cζ / Λ :=
    fun p => norm_fderiv_radialCut hΛpos hCζ hζ' p
  have hu_abs : ∀ p : EuclideanSpace ℝ (Fin 3), |fu.f (‖p‖ / Λ)| ≤ 1 :=
    fun p => abs_radialCut_le_one Λ p
  have hudiff : ∀ p : EuclideanSpace ℝ (Fin 3),
      DifferentiableAt ℝ (fun q : EuclideanSpace ℝ (Fin 3) => fu.f (‖q‖ / Λ)) p :=
    fun p => hu_cd1.differentiable (by norm_num) p
  have hcdiff : ∀ p : EuclideanSpace ℝ (Fin 3),
      DifferentiableAt ℝ (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)) p :=
    fun p => hW1cd.differentiable (by norm_num) p
  simp only [Work.BoseBoxFock.uvCut]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness: product of two `C^1` functions
    exact hu_cd1.mul hW1cd
  · -- `|ζ_Λ·Ŵ₁| ≤ |Ŵ₁|`: the cut-off is bounded by `1`
    intro p
    rw [abs_mul]
    calc |fu.f (‖p‖ / Λ)| * |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p|
        ≤ |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| :=
          mul_le_of_le_one_left (abs_nonneg _) (hu_abs p)
      _ ≤ Cw * _root_.BoseGases.a v := hW1le p
  · -- the decay row: the same bound against `(1+‖p‖)²`
    intro p
    rw [abs_mul]
    calc |fu.f (‖p‖ / Λ)| * |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| * (1 + ‖p‖) ^ 2
        ≤ |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| * (1 + ‖p‖) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (show |fu.f (‖p‖ / Λ)| * |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p|
                ≤ |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| from
              mul_le_of_le_one_left (abs_nonneg _) (hu_abs p))
            (by positivity : (0 : ℝ) ≤ (1 + ‖p‖) ^ 2)
      _ ≤ Cw * _root_.BoseGases.a v := hW1decay p
  · -- the gradient row: product rule, then the two bounds
    intro p
    rw [fderiv_fun_mul (hudiff p) (hcdiff p)]
    have h1 : |fu.f (‖p‖ / Λ)| * ‖fderiv ℝ (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)) p‖
        ≤ 1 * (Cw * _root_.BoseGases.a v * (1 + ‖p‖)) :=
      mul_le_mul (hu_abs p) (hW1grad p) (norm_nonneg _) zero_le_one
    have h2 : |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| *
          ‖fderiv ℝ (fun q : EuclideanSpace ℝ (Fin 3) => fu.f (‖q‖ / Λ)) p‖
        ≤ (Cw * _root_.BoseGases.a v) * (Cζ / Λ) :=
      mul_le_mul (hW1le p) (hu_fd p) (norm_nonneg _) hCwa
    have hAB : 0 ≤ (Cw * _root_.BoseGases.a v) * (Cζ / Λ) := mul_nonneg hCwa hB
    have hT : (1 : ℝ) ≤ 1 + ‖p‖ := by linarith [norm_nonneg p]
    have h3 : (Cw * _root_.BoseGases.a v) * (Cζ / Λ)
        ≤ (Cw * _root_.BoseGases.a v) * (Cζ / Λ) * (1 + ‖p‖) := le_mul_of_one_le_right hAB hT
    calc ‖fu.f (‖p‖ / Λ) • fderiv ℝ (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)) p
            + Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p •
              fderiv ℝ (fun q : EuclideanSpace ℝ (Fin 3) => fu.f (‖q‖ / Λ)) p‖
        ≤ ‖fu.f (‖p‖ / Λ) • fderiv ℝ (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)) p‖
          + ‖Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p •
              fderiv ℝ (fun q : EuclideanSpace ℝ (Fin 3) => fu.f (‖q‖ / Λ)) p‖ :=
          norm_add_le _ _
      _ = |fu.f (‖p‖ / Λ)| * ‖fderiv ℝ (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)) p‖
          + |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| *
              ‖fderiv ℝ (fun q : EuclideanSpace ℝ (Fin 3) => fu.f (‖q‖ / Λ)) p‖ := by
          simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * (Cw * _root_.BoseGases.a v * (1 + ‖p‖))
          + (Cw * _root_.BoseGases.a v) * (Cζ / Λ) * (1 + ‖p‖) :=
          add_le_add h1 (le_trans h2 h3)
      _ = (Cw + Cw * Cζ / Λ) * _root_.BoseGases.a v * (1 + ‖p‖) := by ring
  · -- the normalisation `ζ_Λ = 1` below the cut-off
    intro p hp
    exact fu.one _ ((div_le_one hΛpos).mpr hp)

end Work.BoseGateFS
