import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.continuous_bsOneBody
import Submission.Work.BoseKinLoc.Kinetic.neuFrac_translate
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Sector.fsT_translate`

The localised kinetic word `fsT ℓ d s εT b u ψ` (FS `eq:DefT`, the one-body quadratic form
`𝒯_u` of `Work.BoseKinLoc.Defs`) is **invariant under translating the moving box by its
centre `ℓu`**, provided the one-body state is translated with the box:

    `fsT ℓ d s εT b u ψ = fsT ℓ d s εT b 0 (ψ(ℓu + ·))`.

`fsT` is the sum of the four pieces

* `neuWord ℓ d εT u ψ = ½ε_T(dℓ)⁻²·neuFrac ℓ (dℓ)⁻² u (Q_uψ)`,
* `gapWord ℓ b u ψ   = bℓ⁻²·∫_{Λ(u)}(Q_uψ)²`,
* `momWord ℓ d εT b u ψ = bε_T(dℓ)⁻²·(2π)⁻³∫_p 1_{‖p‖>(d²ℓ)⁻¹}‖kinFT(1_{Λ(u)}Q_uψ)‖²`,
* `mainWord ℓ d s εT u ψ = (1−ε_T)·bsOneBody ℓ F₁ u ψ + ε_T·bsOneBody ℓ F₂ u ψ`,

and each is transported by the substitution `z ↦ ℓu + z` on the box `Λ(u)`:

* the box `lamBox ℓ u = bsBox ℓ u` becomes `acube ℓ = lamBox ℓ 0` under `x ↦ x − ℓu`, so the
  set integrals over the moving box are those over the centred cube
  (`Gap.setIntegral_lamBox_eq_acube`);
* the box mean `bsMean ℓ u` is invariant (`bsMean ℓ u ψ = bsMean ℓ 0 (ψ(ℓu + ·))`), hence the
  mean-free part satisfies the *exact* pointwise identity
  `Q_uψ(ℓu + z) = Q_0(ψ(ℓu + ·)) z` (and likewise for `bsQ`, `Qfree = bsQ`);
* the window `bsWin ℓ u (ℓu + z) = χ(z/ℓ) = bsWin ℓ 0 z` and the indicator
  `indU ℓ u (ℓu + z) = indU ℓ 0 z` are exact;
* consequently the windowed state of the moving box is the *translate* by `ℓu` of the anchored
  windowed state, and the `p`-convention Fourier transform is translation covariant
  (`norm_kinFT_comp_add`: `kinFT (g(· + a)) p = e^{i⟪p,a⟫}·kinFT g p`), so the pointwise
  *norms* — and therefore every one-body form above — agree.

The Neumann fraction `neuFrac` is transported separately, by `Kinetic.neuFrac_translate`
(the trial-functional/infimum argument of that module), which is the only piece that is not a
straight change of variables in a `kinFT`-integral.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal Real

namespace Work.BoseKinLoc.Sector

open Work.BSKinetic Work.BSKinetic.Decomp

set_option linter.unusedVariables false

/-- The Euclidean space of the chapter, under a short local name for the helper lemmas below.
(The statement of `fsT_translate` itself is written with the corpus notation `ℝ³`.) -/
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The box mean, the mean-free part, the window and the indicator -/

/-- The box mean of the *anchored* box applied to the translated state is the box mean of the
moving box: both are `(ℓ³)⁻¹∫_{acube ℓ} ψ(ℓu + ·)`. -/
theorem fsTshift_bsMean (ℓ : ℝ) (u : E3) (ψ : E3 → ℝ) :
    Work.BSKinetic.bsMean ℓ 0 (fun w : E3 => ψ (ℓ • u + w)) = Work.BSKinetic.bsMean ℓ u ψ := by
  simp [Work.BSKinetic.bsMean]

/-- **The mean-free part transports exactly**: the mean-free part of `ψ` in the moving box,
evaluated at the shifted point `ℓu + z`, is the mean-free part of the translated state
`ψ(ℓu + ·)` in the anchored box, evaluated at `z`. -/
theorem fsTshift_bsQ (ℓ : ℝ) (u : E3) (ψ : E3 → ℝ) :
    (fun z : E3 => Work.BSKinetic.bsQ ℓ u ψ (ℓ • u + z))
      = Work.BSKinetic.bsQ ℓ 0 (fun w : E3 => ψ (ℓ • u + w)) := by
  funext z
  show ψ (ℓ • u + z) - Work.BSKinetic.bsMean ℓ u ψ
      = (fun w : E3 => ψ (ℓ • u + w)) z
        - Work.BSKinetic.bsMean ℓ 0 (fun w : E3 => ψ (ℓ • u + w))
  rw [fsTshift_bsMean]

/-- `Qfree = bsQ` in the same form as `fsTshift_bsQ`. -/
theorem fsTshift_Qfree (ℓ : ℝ) (u : E3) (ψ : E3 → ℝ) :
    (fun z : E3 => Work.BoseKinLoc.Qfree ℓ u ψ (ℓ • u + z))
      = Work.BoseKinLoc.Qfree ℓ 0 (fun w : E3 => ψ (ℓ • u + w)) :=
  fsTshift_bsQ ℓ u ψ

/-- The window of the moving box, evaluated at the shifted point `ℓu + z`, is the anchored
window at `z`. -/
theorem fsTshift_bsWin (ℓ : ℝ) (u : E3) (z : E3) :
    Work.BSKinetic.bsWin ℓ u (ℓ • u + z) = Work.BSKinetic.bsWin ℓ 0 z := by
  simp [Work.BSKinetic.bsWin]

/-- The indicator of the moving box, evaluated at the shifted point `ℓu + z`, is the indicator
of the anchored box at `z`. -/
theorem fsTshift_indU (ℓ : ℝ) (u : E3) (z : E3) :
    Work.BoseKinLoc.indU ℓ u (ℓ • u + z) = Work.BoseKinLoc.indU ℓ 0 z := by
  classical
  have hbox : Work.BSKinetic.bsBox ℓ (0 : E3) = Submission.BoseGases.acube ℓ := by
    ext x; simp [Work.BSKinetic.bsBox]
  unfold Work.BoseKinLoc.indU Work.BoseKinLoc.lamBox
  rw [Set.indicator_apply, Set.indicator_apply, hbox]
  by_cases hz : z ∈ Submission.BoseGases.acube ℓ
  · have hz' : ℓ • u + z ∈ Work.BSKinetic.bsBox ℓ u := by
      rw [Work.BSKinetic.bsBox, Set.mem_ofPred_eq]
      rwa [add_sub_cancel_left]
    simp only [hz', hz, ↓reduceIte]
  · have hz' : ℓ • u + z ∉ Work.BSKinetic.bsBox ℓ u := by
      rw [Work.BSKinetic.bsBox, Set.mem_ofPred_eq]
      rwa [add_sub_cancel_left]
    simp only [hz', hz, ↓reduceIte]

/-! ## 2. Translation covariance of the windowed `p`-modes -/

/-- `kinFT` covariance in the `addLeft` convention (`norm_kinFT_comp_add` is stated for
`z ↦ g (z + a)`). -/
theorem fsTshift_norm_kinFT_comp_add (g : E3 → ℂ) (a p : E3) :
    ‖Submission.BoseGases.kinFT (fun z : E3 => g (a + z)) p‖
      = ‖Submission.BoseGases.kinFT g p‖ := by
  have h : (fun z : E3 => g (a + z)) = fun z : E3 => g (z + a) := by
    funext z; rw [add_comm]
  rw [h, norm_kinFT_comp_add]

/-- **The windowed mode norms are translation invariant**: if the window and the state are both
translated by `ℓu`, the `p`-norm of the windowed Fourier transform is unchanged. -/
theorem fsTshift_norm_kinFT_window (ℓ : ℝ) (w f w' f' : E3 → ℝ) (u p : E3)
    (hw : ∀ z : E3, w (ℓ • u + z) = w' z) (hf : ∀ z : E3, f (ℓ • u + z) = f' z) :
    ‖Submission.BoseGases.kinFT (fun z : E3 => ((w z : ℝ) : ℂ) * ((f z : ℝ) : ℂ)) p‖
      = ‖Submission.BoseGases.kinFT (fun z : E3 => ((w' z : ℝ) : ℂ) * ((f' z : ℝ) : ℂ)) p‖ := by
  have hfun : (fun z : E3 => ((w (ℓ • u + z) : ℝ) : ℂ) * ((f (ℓ • u + z) : ℝ) : ℂ))
      = fun z : E3 => ((w' z : ℝ) : ℂ) * ((f' z : ℝ) : ℂ) := by
    funext z; rw [hw z, hf z]
  rw [← hfun]
  exact (fsTshift_norm_kinFT_comp_add
    (fun x : E3 => ((w x : ℝ) : ℂ) * ((f x : ℝ) : ℂ)) (ℓ • u) p).symm

/-! ## 3. The windowed one-body form (both `bsOneBody` and `momForm` are of this shape) -/

/-- **The generic windowed one-body form is translation invariant.**  Both
`bsOneBody ℓ F u ψ` (window `bsWin`, state `bsQ`) and `momForm ℓ d u ψ` (window `indU`, state
`Qfree`, symbol `momProj`) are the specialisation of

    `(2π)⁻³ ∫_p Fc p · ‖kinFT (w · f) p‖²`

to a window `w` and a mean-free state `f` that both transport to the anchored data by
`z ↦ ℓu + z`. -/
theorem fsTshift_windowedForm (ℓ : ℝ) (Fc : E3 → ℝ) (w f w' f' : E3 → ℝ) (u : E3)
    (hw : ∀ z : E3, w (ℓ • u + z) = w' z) (hf : ∀ z : E3, f (ℓ • u + z) = f' z) :
    ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : E3, Fc p * ‖Submission.BoseGases.kinFT
          (fun z : E3 => ((w z : ℝ) : ℂ) * ((f z : ℝ) : ℂ)) p‖ ^ 2)
      = ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : E3, Fc p * ‖Submission.BoseGases.kinFT
          (fun z : E3 => ((w' z : ℝ) : ℂ) * ((f' z : ℝ) : ℂ)) p‖ ^ 2) := by
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  dsimp only
  rw [fsTshift_norm_kinFT_window ℓ w f w' f' u p hw hf]

/-! ## 4. The four kinetic pieces -/

/-- `bsOneBody ℓ F u ψ` is the anchored `bsOneBody` of the translated state. -/
theorem fsTshift_bsOneBody (ℓ : ℝ) (F : ℝ → ℝ) (u : E3) (ψ : E3 → ℝ) :
    Work.BSKinetic.bsOneBody ℓ F u ψ
      = Work.BSKinetic.bsOneBody ℓ F 0 (fun z : E3 => ψ (ℓ • u + z)) := by
  rw [Work.BSKinetic.bsOneBody]
  exact fsTshift_windowedForm ℓ (fun p => F ‖p‖) (Work.BSKinetic.bsWin ℓ u)
    (Work.BSKinetic.bsQ ℓ u ψ) (Work.BSKinetic.bsWin ℓ 0)
    (Work.BSKinetic.bsQ ℓ 0 (fun z : E3 => ψ (ℓ • u + z))) u
    (fun z => fsTshift_bsWin ℓ u z) (fun z => congrFun (fsTshift_bsQ ℓ u ψ) z)

/-- `momForm ℓ d u ψ` is the anchored `momForm` of the translated state. -/
theorem fsTshift_momForm (ℓ d : ℝ) (u : E3) (ψ : E3 → ℝ) :
    Work.BoseKinLoc.momForm ℓ d u ψ
      = Work.BoseKinLoc.momForm ℓ d 0 (fun z : E3 => ψ (ℓ • u + z)) := by
  rw [Work.BoseKinLoc.momForm]
  exact fsTshift_windowedForm ℓ (Work.BoseKinLoc.momProj ℓ d) (Work.BoseKinLoc.indU ℓ u)
    (Work.BoseKinLoc.Qfree ℓ u ψ) (Work.BoseKinLoc.indU ℓ 0)
    (Work.BoseKinLoc.Qfree ℓ 0 (fun z : E3 => ψ (ℓ • u + z))) u
    (fun z => fsTshift_indU ℓ u z) (fun z => congrFun (fsTshift_Qfree ℓ u ψ) z)

/-- `gapBare ℓ u ψ = ∫_{Λ(u)}(Q_uψ)²` is the anchored `gapBare` of the translated state. -/
theorem fsTshift_gapBare (ℓ : ℝ) (u : E3) (ψ : E3 → ℝ) :
    Work.BoseKinLoc.gapBare ℓ u ψ
      = Work.BoseKinLoc.gapBare ℓ 0 (fun z : E3 => ψ (ℓ • u + z)) := by
  unfold Work.BoseKinLoc.gapBare
  rw [Work.BoseKinLoc.Gap.setIntegral_lamBox_eq_acube ℓ u
        (fun z => (Work.BoseKinLoc.Qfree ℓ u ψ z) ^ 2)]
  rw [Work.BoseKinLoc.Kinetic.lamBox_zero_eq_acube ℓ]
  refine setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ) (fun z _ => ?_)
  rw [congrFun (fsTshift_Qfree ℓ u ψ) z]

/-- `neuWord` transports: the Neumann-resolvent piece is handled by `neuFrac_translate`
(the trial-functional argument), together with the exact transport of `Q_u`. -/
theorem fsTshift_neuWord (ℓ d εT : ℝ) (u : E3) (ψ : E3 → ℝ) :
    Work.BoseKinLoc.neuWord ℓ d εT u ψ
      = Work.BoseKinLoc.neuWord ℓ d εT 0 (fun z : E3 => ψ (ℓ • u + z)) := by
  unfold Work.BoseKinLoc.neuWord
  rw [Work.BoseKinLoc.Kinetic.neuFrac_translate ℓ ((d * ℓ) ^ (-2 : ℤ)) u
    (Work.BoseKinLoc.Qfree ℓ u ψ)]
  rw [← fsTshift_Qfree ℓ u ψ]

/-- `gapWord` transports. -/
theorem fsTshift_gapWord (ℓ b : ℝ) (u : E3) (ψ : E3 → ℝ) :
    Work.BoseKinLoc.gapWord ℓ b u ψ
      = Work.BoseKinLoc.gapWord ℓ b 0 (fun z : E3 => ψ (ℓ • u + z)) := by
  unfold Work.BoseKinLoc.gapWord
  rw [fsTshift_gapBare ℓ u ψ]

/-- `momWord` transports. -/
theorem fsTshift_momWord (ℓ d εT b : ℝ) (u : E3) (ψ : E3 → ℝ) :
    Work.BoseKinLoc.momWord ℓ d εT b u ψ
      = Work.BoseKinLoc.momWord ℓ d εT b 0 (fun z : E3 => ψ (ℓ • u + z)) := by
  unfold Work.BoseKinLoc.momWord
  rw [fsTshift_momForm ℓ d u ψ]

/-- `mainWord` transports (both cut-offs at once). -/
theorem fsTshift_mainWord (ℓ d s εT : ℝ) (u : E3) (ψ : E3 → ℝ) :
    Work.BoseKinLoc.mainWord ℓ d s εT u ψ
      = Work.BoseKinLoc.mainWord ℓ d s εT 0 (fun z : E3 => ψ (ℓ • u + z)) := by
  unfold Work.BoseKinLoc.mainWord
  rw [fsTshift_bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ,
      fsTshift_bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ]

/-! ## 5. The requested statement -/

/-- The transported sum (the auxiliary form of `fsT_translate`, stated at the explicit type). -/
theorem fsT_translate_E3 (ℓ d s εT b : ℝ) (u : E3) (ψ : E3 → ℝ) :
    Work.BoseKinLoc.fsT ℓ d s εT b u ψ
      = Work.BoseKinLoc.fsT ℓ d s εT b 0 (fun z : E3 => ψ (ℓ • u + z)) := by
  unfold Work.BoseKinLoc.fsT
  rw [fsTshift_neuWord ℓ d εT u ψ, fsTshift_gapWord ℓ b u ψ, fsTshift_momWord ℓ d εT b u ψ,
      fsTshift_mainWord ℓ d s εT u ψ]

theorem fsT_translate (ℓ d s εT b : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    Work.BoseKinLoc.fsT ℓ d s εT b u ψ
      = Work.BoseKinLoc.fsT ℓ d s εT b 0 (fun z : ℝ³ => ψ (ℓ • u + z)) :=
  fsT_translate_E3 ℓ d s εT b u ψ

end Work.BoseKinLoc.Sector
