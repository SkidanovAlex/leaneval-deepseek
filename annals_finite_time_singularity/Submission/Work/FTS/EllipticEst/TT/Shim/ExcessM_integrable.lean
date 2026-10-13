/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of the excess mixed term `EXM` of `HkIntegrand α k (D_z Ψ)`

`DzAux.EXM α Ψ k z θ = (D_z^k D_θΨ(z,θ) · Wt α z θ)²` is the second summand of
`HkIntegrand α k (D_z Ψ)` that is *not* a summand of `HkIntegrand α k Ψ` or of
`HkIntegrand α k (D_θΨ)` (needed only for `k ≥ 1`); here we prove that its `z`-slice
integrals are `z`-integrable.

## Route

Write `g := D_z^{k-1}D_θΨ` and, for a fixed angle `θ`, `h_θ(z) := sin(2θ)^{-γ/2}·g(z,θ)`
(`γ = gam α`).  Then, pointwise (a.e. in `z`),

* `DzAux.EXM α Ψ k z θ = w(z)²·(rDz h_θ z)²`,
* `DzAux.PM  α Ψ k z θ = w(z)²·(h_θ z)²`,
* `DzAux.ZM  α Ψ k z θ = w(z)²·(z² h_θ'' z)²`,

the first two for all `z`, the third for `z > 0` (where `z²h'' = rDz²h - rDz h`, and
`rDz²g - rDz g = D_z^{k+1}D_θΨ - D_z^kD_θΨ = mixed (k-1) 1 (z²∂_z²Ψ)`, cf.
`DzAux.mixed_slice_zsq`).  The one-dimensional weighted Agmon inequality (in its
unconditional `lintegral` form, with the finiteness of the middle integral, proved in
`Submission/Work/FTS/EllipticEst/TT/AgmonTT.lean` — a copy of `AgmonFts.LinAgmon` in a module
whose imports are compatible with `Cert.DzPsiAux`) applied to `h_θ` therefore gives, for every
`θ ∈ Iθ`,

`ofReal(α²)·∫⁻_z ofReal(EXM · θ) ≤ ofReal C·(∫⁻_z ofReal(PM · θ) + ofReal(α⁴)·∫⁻_z ofReal(ZM · θ))`.

Integrating this in `θ` (`lintegral_mono`), replacing the `θ`-integrals of `PM`, `ZM` by
`ofReal` of the honest slices (`hPMae`, `hZMae`) and using the finiteness hypotheses
`hPMlin`, `hZMlin` shows `∫⁻_θ ∫⁻_z ofReal(EXM) < ⊤`.  Tonelli
(`lintegral_lintegral_swap`, which uses `hEXMaesm`) identifies this with
`∫⁻_z ofReal(∫_θ EXM z θ)`, so the honest integral of the `θ`-slice is finite, and
`hEXMsl` together with `MeasureTheory.lintegral_ofReal_ne_top_iff_integrable` yields the
claim.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.TT.Shim.DzPsiAux
import Submission.Work.FTS.EllipticEst.TT.AgmonTT

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The angular slice to which the one-dimensional Agmon inequality is applied -/

/-- The `θ`-slice `h_θ(z) = sin(2θ)^{-γ/2}·D_z^{k-1}D_θΨ(z,θ)` of the radial Agmon estimate. -/
private def hslice (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ → ℝ :=
  fun z => Work.Spaces.wTheta α θ * Work.Spaces.DzIter (k - 1) (Work.Spaces.Dth Ψ) z θ

/-- The slice `h_θ` is `C^∞` (hence `smoothOrder`-smooth) on `(0,∞)` for every `θ ∈ Iθ`. -/
private lemma hslice_contDiffOn (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd Ψ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (hslice α k Ψ θ) (Set.Ioi 0) := by
  have hθ' : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hsm' : Work.Spaces.SmoothNbhd (Work.Spaces.DzIter (k - 1) (Work.Spaces.Dth Ψ)) :=
    Work.Spaces.SmoothNbhd.DzIter (Work.Spaces.SmoothNbhd.Dth hsm) (k - 1)
  have h1 : ContDiffOn ℝ ⊤ (fun z => Work.Spaces.DzIter (k - 1) (Work.Spaces.Dth Ψ) z θ)
      (Set.Ioi (-1)) := Work.FTS.EllipticEst.Cert.DzAux.contDiffOn_slice_nbh hsm' hθ'
  have h2 : ContDiffOn ℝ ⊤ (fun z => Work.Spaces.DzIter (k - 1) (Work.Spaces.Dth Ψ) z θ)
      (Set.Ioi 0) := h1.mono (fun z hz => by
        rw [Set.mem_Ioi] at hz ⊢; linarith)
  have h3 : ContDiffOn ℝ ⊤ (hslice α k Ψ θ) (Set.Ioi 0) :=
    (contDiffOn_const (c := Work.Spaces.wTheta α θ)).mul h2
  exact h3.of_le (by simp [Work.Stability.smoothOrder])

/-- `z²h'' = rDzIter 2 h - rDzIter 1 h` on `(0,∞)`. -/
private lemma rDzIter_two_sub_one {h : ℝ → ℝ} (hh : ContDiffOn ℝ 2 h (Set.Ioi 0)) {z : ℝ}
    (hz : 0 < z) :
    Work.FTS.EllipticEst.rDzIter 2 h z - Work.FTS.EllipticEst.rDzIter 1 h z
      = z ^ 2 * deriv (deriv h) z := by
  have hd1 : ContDiffOn ℝ 1 (deriv h) (Set.Ioi 0) := hh.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hdiff : DifferentiableAt ℝ (deriv h) z :=
    (hd1.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hprod : HasDerivAt (fun y : ℝ => y * deriv h y)
      (deriv h z + z * deriv (deriv h) z) z := by
    have h := (hasDerivAt_id z).mul hdiff.hasDerivAt
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  change z * deriv (fun y : ℝ => y * deriv h y) z - z * deriv h z = z ^ 2 * deriv (deriv h) z
  rw [hprod.deriv]
  ring

/-! ## Nonnegativity of the three integrands -/

private lemma EXM_nonneg (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Work.FTS.EllipticEst.Cert.DzAux.EXM α Ψ k z θ := by
  show (0 : ℝ) ≤ (Work.Spaces.DzIter k (Work.Spaces.Dth Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2
  exact sq_nonneg _

private lemma PM_nonneg (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Work.FTS.EllipticEst.Cert.DzAux.PM α Ψ k z θ := by
  show (0 : ℝ) ≤ (Work.Spaces.mixed (k - 1) 1 Ψ z θ * Work.Spaces.Wt α z θ) ^ 2
  exact sq_nonneg _

private lemma ZM_nonneg (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Work.FTS.EllipticEst.Cert.DzAux.ZM α Ψ k z θ := by
  show (0 : ℝ) ≤ (Work.Spaces.mixed (k - 1) 1
    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
  exact sq_nonneg _

/-! ## The three pointwise identities -/

/-- `EXM` is the square of the weighted `rDz`-derivative of the slice `h_θ`. -/
private lemma EXM_eq_rDz (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (hk : 1 ≤ k) (z θ : ℝ) :
    Work.FTS.EllipticEst.Cert.DzAux.EXM α Ψ k z θ
      = (Work.Spaces.w z) ^ 2 * (z * deriv (hslice α k Ψ θ) z) ^ 2 := by
  have hid : Work.FTS.EllipticEst.rDz
      (fun z => Work.Spaces.DzIter (k - 1) (Work.Spaces.Dth Ψ) z θ)
      = fun z => Work.Spaces.DzIter k (Work.Spaces.Dth Ψ) z θ :=
    Work.FTS.EllipticEst.Cert.DzAux.rDzIter_one_mixed_slice Ψ k hk θ
  have h2 : Work.FTS.EllipticEst.rDz (hslice α k Ψ θ)
      = fun z => Work.Spaces.wTheta α θ * Work.Spaces.DzIter k (Work.Spaces.Dth Ψ) z θ := by
    rw [show hslice α k Ψ θ = fun z => Work.Spaces.wTheta α θ *
        Work.Spaces.DzIter (k - 1) (Work.Spaces.Dth Ψ) z θ from rfl,
      Work.FTS.EllipticEst.rDz_const_mul, hid]
  have h3 : z * deriv (hslice α k Ψ θ) z
      = Work.Spaces.wTheta α θ * Work.Spaces.DzIter k (Work.Spaces.Dth Ψ) z θ := by
    have := congrFun h2 z
    simpa only [Work.FTS.EllipticEst.rDz] using this
  rw [h3]
  simp only [Work.FTS.EllipticEst.Cert.DzAux.EXM, Work.Spaces.Wt]
  ring

/-- `PM` is the square of the slice `h_θ` itself. -/
private lemma PM_eq_w_sq (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.EllipticEst.Cert.DzAux.PM α Ψ k z θ
      = (Work.Spaces.w z) ^ 2 * (hslice α k Ψ θ z) ^ 2 := by
  simp only [Work.FTS.EllipticEst.Cert.DzAux.PM, Work.Spaces.mixed, Work.Spaces.DthIter_zero,
    Work.Spaces.DthIter_succ, Work.Spaces.Wt, hslice]
  ring

/-- `ZM` is the square of the weighted second derivative `z²h_θ''` of the slice. -/
private lemma ZM_eq_w_sq (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hk : 1 ≤ k) {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.Cert.DzAux.ZM α Ψ k z θ
      = (Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv (hslice α k Ψ θ)) z) ^ 2 := by
  set g : ℝ → ℝ := fun z => Work.Spaces.DzIter (k - 1) (Work.Spaces.Dth Ψ) z θ with hg
  have hθ' : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hsm' : Work.Spaces.SmoothNbhd (Work.Spaces.DzIter (k - 1) (Work.Spaces.Dth Ψ)) :=
    Work.Spaces.SmoothNbhd.DzIter (Work.Spaces.SmoothNbhd.Dth hsm) (k - 1)
  have h1 : ContDiffOn ℝ ⊤ (fun z => Work.Spaces.DzIter (k - 1) (Work.Spaces.Dth Ψ) z θ)
      (Set.Ioi (-1)) := Work.FTS.EllipticEst.Cert.DzAux.contDiffOn_slice_nbh hsm' hθ'
  have hg2 : ContDiffOn ℝ 2 g (Set.Ioi 0) := (h1.of_le le_top).mono (fun y hy => by
    rw [Set.mem_Ioi] at hy ⊢; linarith)
  -- the slice is the constant multiple `sin(2θ)^{-γ/2}·g`
  have hA : deriv (deriv (hslice α k Ψ θ)) z = Work.Spaces.wTheta α θ * deriv (deriv g) z := by
    have hA1 : deriv (hslice α k Ψ θ) = fun y => Work.Spaces.wTheta α θ * deriv g y := by
      funext y
      rw [show hslice α k Ψ θ = fun z => Work.Spaces.wTheta α θ * g z from rfl]
      exact deriv_const_mul_field (Work.Spaces.wTheta α θ)
    rw [hA1]
    exact deriv_const_mul_field (Work.Spaces.wTheta α θ)
  -- `g`'s second derivative, in the `D_z` notation
  have hC : z ^ 2 * deriv (deriv g) z
      = Work.FTS.EllipticEst.rDzIter 2 g z - Work.FTS.EllipticEst.rDzIter 1 g z :=
    (rDzIter_two_sub_one hg2 hz).symm
  have hD : Work.FTS.EllipticEst.rDzIter 2 g
      = fun w => Work.Spaces.DzIter (k + 1) (Work.Spaces.Dth Ψ) w θ :=
    Work.FTS.EllipticEst.Cert.DzAux.rDzIter_two_mixed_slice Ψ k hk θ
  have hE : Work.FTS.EllipticEst.rDzIter 1 g
      = fun w => Work.Spaces.DzIter k (Work.Spaces.Dth Ψ) w θ :=
    Work.FTS.EllipticEst.Cert.DzAux.rDzIter_one_mixed_slice Ψ k hk θ
  have hF : Work.Spaces.DzIter (k + 1) (Work.Spaces.Dth Ψ) z θ
        - Work.Spaces.DzIter k (Work.Spaces.Dth Ψ) z θ
      = Work.Spaces.mixed (k - 1) 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ :=
    Work.FTS.EllipticEst.Cert.DzAux.mixed_slice_zsq Ψ hsm k hk
      (show z ∈ Work.Spaces.Iz from by
        rw [Work.Spaces.Iz, Set.mem_Ici]; linarith) hθ
  have hG : z ^ 2 * deriv (deriv (hslice α k Ψ θ)) z
      = Work.Spaces.wTheta α θ * Work.Spaces.mixed (k - 1) 1
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
    have h1' : z ^ 2 * deriv (deriv (hslice α k Ψ θ)) z
        = Work.Spaces.wTheta α θ * (z ^ 2 * deriv (deriv g) z) := by
      rw [hA]; ring
    rw [h1', hC, hD, hE, hF]
  rw [hG]
  simp only [Work.FTS.EllipticEst.Cert.DzAux.ZM, Work.Spaces.Wt]
  ring

/-! ## The pointwise-in-`θ` Agmon inequality for `EXM`, `PM`, `ZM` -/

/-- The one-dimensional Agmon inequality of `AgmonClean`, applied to the angular slice
`h_θ = sin(2θ)^{-γ/2}·D_z^{k-1}D_θΨ` and rewritten in terms of `EXM`, `PM`, `ZM`. -/
private theorem slice_agmon_bound (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (hα : 0 < α) (hα1 : α ≤ 1) (hk : 1 ≤ k)
    (C : ℝ) (hC : 0 < C)
    (hag : ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi 0) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (Work.Spaces.w z ^ 2 * (z * deriv h z) ^ 2))
        ≤ ENNReal.ofReal C * ((∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal (Work.Spaces.w z ^ 2 * h z ^ 2))
            + ENNReal.ofReal (α ^ 4) * (∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal (Work.Spaces.w z ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2)))) :
    ∀ θ ∈ Work.Spaces.Iθ,
      ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (Work.FTS.EllipticEst.Cert.DzAux.EXM α Ψ k z θ))
        ≤ ENNReal.ofReal C * ((∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal (Work.FTS.EllipticEst.Cert.DzAux.PM α Ψ k z θ))
            + ENNReal.ofReal (α ^ 4) * (∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal (Work.FTS.EllipticEst.Cert.DzAux.ZM α Ψ k z θ))) := by
  intro θ hθ
  have h1 := hag α (hslice α k Ψ θ) hα hα1 (hslice_contDiffOn α k Ψ hsm hθ)
  have hE : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (Work.Spaces.w z ^ 2 * (z * deriv (hslice α k Ψ θ) z) ^ 2))
      = (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (Work.FTS.EllipticEst.Cert.DzAux.EXM α Ψ k z θ)) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show ENNReal.ofReal (Work.Spaces.w z ^ 2 * (z * deriv (hslice α k Ψ θ) z) ^ 2)
      = ENNReal.ofReal (Work.FTS.EllipticEst.Cert.DzAux.EXM α Ψ k z θ)
    rw [EXM_eq_rDz α k Ψ hk z θ]
  have hP : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (Work.Spaces.w z ^ 2 * (hslice α k Ψ θ) z ^ 2))
      = (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (Work.FTS.EllipticEst.Cert.DzAux.PM α Ψ k z θ)) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show ENNReal.ofReal (Work.Spaces.w z ^ 2 * (hslice α k Ψ θ) z ^ 2)
      = ENNReal.ofReal (Work.FTS.EllipticEst.Cert.DzAux.PM α Ψ k z θ)
    rw [← PM_eq_w_sq α k Ψ z θ]
  have hZ : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (Work.Spaces.w z ^ 2 *
          (z ^ 2 * deriv (deriv (hslice α k Ψ θ)) z) ^ 2))
      = (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (Work.FTS.EllipticEst.Cert.DzAux.ZM α Ψ k z θ)) := by
    refine lintegral_congr_ae ?_
    rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    rw [← ZM_eq_w_sq α k Ψ hsm hk hz hθ]
  rw [hE, hP, hZ] at h1
  exact h1

/-! ## Two measure-theoretic steps -/

/-- The Tonelli chain turning `∫⁻_z ofReal(∫_θ F z θ)` into the iterated `lintegral`
`∫⁻_θ ∫⁻_z ofReal(F z θ)` over the product measure. -/
private theorem tonelli_swap_aux (F : ℝ → ℝ → ℝ) (hnn : ∀ z θ, 0 ≤ F z θ)
    (hsl : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => F z θ) Work.Spaces.Iθ)
    (haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, F z θ))
      = ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (F z θ) := by
  have hf : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (F p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable haesm.aemeasurable
  have h1 : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, F z θ))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (F z θ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hsl] with z hz
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hz
      (Filter.Eventually.of_forall (fun θ => hnn z θ))
  rw [h1]
  exact lintegral_lintegral_swap hf

/-- From a pointwise-in-`θ` Agmon estimate and finite `θ`-integrals of the two data terms,
the `θ`-integral of the middle term is finite. -/
private theorem theta_lt_top_aux (α C : ℝ) (hα : 0 < α) (hC : 0 < C)
    (A B D : ℝ → ENNReal)
    (hpt : ∀ θ ∈ Work.Spaces.Iθ,
      ENNReal.ofReal (α ^ 2) * A θ ≤ ENNReal.ofReal C * (B θ + ENNReal.ofReal (α ^ 4) * D θ))
    (hB : AEMeasurable B (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hBtop : (∫⁻ θ in Work.Spaces.Iθ, B θ) < ⊤)
    (hDtop : (∫⁻ θ in Work.Spaces.Iθ, D θ) < ⊤) :
    (∫⁻ θ in Work.Spaces.Iθ, A θ) < ⊤ := by
  have h2 : ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Work.Spaces.Iθ, A θ)
      ≤ ENNReal.ofReal C * ((∫⁻ θ in Work.Spaces.Iθ, B θ)
          + ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Work.Spaces.Iθ, D θ)) := by
    calc ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Work.Spaces.Iθ, A θ)
        = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (α ^ 2) * A θ :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal C * (B θ + ENNReal.ofReal (α ^ 4) * D θ) :=
          lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Icc hpt)
      _ = ENNReal.ofReal C * (∫⁻ θ in Work.Spaces.Iθ,
            (B θ + ENNReal.ofReal (α ^ 4) * D θ)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal C * ((∫⁻ θ in Work.Spaces.Iθ, B θ)
            + (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (α ^ 4) * D θ)) := by
          rw [lintegral_add_left' hB]
      _ = ENNReal.ofReal C * ((∫⁻ θ in Work.Spaces.Iθ, B θ)
            + ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Work.Spaces.Iθ, D θ)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hfin : ENNReal.ofReal C * ((∫⁻ θ in Work.Spaces.Iθ, B θ)
      + ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Work.Spaces.Iθ, D θ)) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.add_lt_top.mpr ⟨hBtop,
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDtop⟩)
  have h3 : ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Work.Spaces.Iθ, A θ) < ⊤ :=
    lt_of_le_of_lt h2 hfin
  rcases ENNReal.mul_lt_top_iff.mp h3 with ⟨-, hA⟩ | h0 | h0
  · exact hA
  · exact absurd h0 (ENNReal.ofReal_pos.mpr (pow_pos hα 2)).ne'
  · rw [h0]; exact ENNReal.zero_lt_top

/-! ## The certificate -/

theorem ExcessM_integrable (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (hα : 0 < α) (hα1 : α ≤ 1) (hk : 1 ≤ k)
    (hPMz : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.Cert.DzAux.PM α Ψ k z θ) Work.Spaces.Iz)
    (hPMae : Filter.Eventually (fun θ => MeasureTheory.IntegrableOn (fun z =>
      Work.FTS.EllipticEst.Cert.DzAux.PM α Ψ k z θ) Work.Spaces.Iz)
      (MeasureTheory.ae (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hPMlin : MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (fun θ => ENNReal.ofReal (∫ z in Work.Spaces.Iz,
        Work.FTS.EllipticEst.Cert.DzAux.PM α Ψ k z θ)) < ⊤)
    (hZMz : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.Cert.DzAux.ZM α Ψ k z θ) Work.Spaces.Iz)
    (hZMae : Filter.Eventually (fun θ => MeasureTheory.IntegrableOn (fun z =>
      Work.FTS.EllipticEst.Cert.DzAux.ZM α Ψ k z θ) Work.Spaces.Iz)
      (MeasureTheory.ae (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hZMlin : MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (fun θ => ENNReal.ofReal (∫ z in Work.Spaces.Iz,
        Work.FTS.EllipticEst.Cert.DzAux.ZM α Ψ k z θ)) < ⊤)
    (hEXMsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ =>
      Work.FTS.EllipticEst.Cert.DzAux.EXM α Ψ k z θ) Work.Spaces.Iθ)
    (hEXMaesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Cert.DzAux.EXM α Ψ k p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.Cert.DzAux.EXM α Ψ k z θ) Work.Spaces.Iz := by
  obtain ⟨C, hC, hag₀⟩ := Work.FTS.EllipticEst.TT.rDz_agmon_lintegral_tt
  have hag : ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi 0) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (Work.Spaces.w z ^ 2 * (z * deriv h z) ^ 2))
        ≤ ENNReal.ofReal C * ((∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal (Work.Spaces.w z ^ 2 * h z ^ 2))
            + ENNReal.ofReal (α ^ 4) * (∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal (Work.Spaces.w z ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2))) :=
    fun α h hα₀ hα₁ hcd => hag₀ α hα₀ hα₁ h hcd
  have hslice := slice_agmon_bound α k Ψ hsm hα hα1 hk C hC hag
  -- ## joint measurability of the `PM` integrand and of its `z`-integral in `θ`
  have hPMprod : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Cert.DzAux.PM α Ψ k p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_mixed_Wt_sq_prod α Ψ hsm (k - 1) 1
  have hBmeas : AEMeasurable
      (fun θ => ∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (Work.FTS.EllipticEst.Cert.DzAux.PM α Ψ k z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h : AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (Work.FTS.EllipticEst.Cert.DzAux.PM α Ψ k p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      ENNReal.measurable_ofReal.comp_aemeasurable hPMprod.aemeasurable
    exact h.lintegral_prod_left
  -- ## finiteness of the two `θ`-integrals of the data terms
  have hBeq : (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (Work.FTS.EllipticEst.Cert.DzAux.PM α Ψ k z θ))
      = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Cert.DzAux.PM α Ψ k z θ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hPMae] with θ hθ
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hθ
      (Filter.Eventually.of_forall (fun z => PM_nonneg α k Ψ z θ))).symm
  have hBfin : (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal (Work.FTS.EllipticEst.Cert.DzAux.PM α Ψ k z θ)) < ⊤ := by
    rw [hBeq]; exact hPMlin
  have hZeq : (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (Work.FTS.EllipticEst.Cert.DzAux.ZM α Ψ k z θ))
      = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Cert.DzAux.ZM α Ψ k z θ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hZMae] with θ hθ
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hθ
      (Filter.Eventually.of_forall (fun z => ZM_nonneg α k Ψ z θ))).symm
  have hDfin : (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal (Work.FTS.EllipticEst.Cert.DzAux.ZM α Ψ k z θ)) < ⊤ := by
    rw [hZeq]; exact hZMlin
  -- ## the `θ`-integral of the middle term is finite
  have hAfin : (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal (Work.FTS.EllipticEst.Cert.DzAux.EXM α Ψ k z θ)) < ⊤ :=
    theta_lt_top_aux α C hα hC _ _ _ hslice hBmeas hBfin hDfin
  -- ## Tonelli, and the final integrability
  have hsl : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.Cert.DzAux.EXM α Ψ k z θ)
        Work.Spaces.Iθ :=
    ae_restrict_of_forall_mem measurableSet_Ici hEXMsl
  have hton := tonelli_swap_aux (fun z θ => Work.FTS.EllipticEst.Cert.DzAux.EXM α Ψ k z θ)
    (fun z θ => EXM_nonneg α k Ψ z θ) hsl hEXMaesm
  have hfin : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Cert.DzAux.EXM α Ψ k z θ)) < ⊤ := by
    rw [hton]; exact hAfin
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hEXMaesm.integral_prod_right'
      (Filter.Eventually.of_forall
        (fun z => integral_nonneg (fun θ => EXM_nonneg α k Ψ z θ)))).mp (ne_of_lt hfin)

end Work.FTS.EllipticEst.TT
