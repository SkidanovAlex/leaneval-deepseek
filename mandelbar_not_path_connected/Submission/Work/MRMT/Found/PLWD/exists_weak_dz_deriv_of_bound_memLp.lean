/-
Work.MRMT.Found.PLWD — the Riesz-representation step producing a weak `∂`-derivative from a
bounded pairing, in the form needed by the construction of the principal solution: the
representing function is an honest `L²` function.

If `φ` is locally integrable and the pairings `ψ ↦ ∫ φ · ∂ψ` against `C¹` test functions
supported in `B(0,R)` are bounded by `C · ‖ψ‖_{L²(B(0,R))}`, then — because the test functions
are dense in `L²(B(0,R))` — the pairing extends to a continuous linear functional of `L²`, and
the Riesz representation theorem produces `D ∈ L²(B(0,R))` (in the strong sense: `D` is
a.e. strongly measurable and square integrable) with

  `∫ z, D z * ψ z = -∫ z, φ z * ∂ψ z`   for every test function `ψ`.

The point of stating the conclusion as `MemLp D 2 (volume.restrict (ball 0 R))` rather than as
integrability of `‖D‖²` is that `MemLp` also records a.e. strong measurability, which the
downstream arguments about `μ D` and the weak `∂̄`-derivative genuinely need.
-/
import Mathlib
import Submission.Work.MRMT.Found.PLWD.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Topology ENNReal

namespace Work.MRMT.Found.PLWD

/-! ## Elementary properties of `∂` on test functions -/

/-- `∂ψ` is continuous when `ψ` is `C¹`. -/
private theorem continuous_dz_of_contDiff {ψ : ℂ → ℂ} (hψ : ContDiff ℝ 1 ψ) :
    Continuous (Work.MRMT.dz ψ) := by
  have hd : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by norm_num)
  unfold Work.MRMT.dz
  exact ((hd.clm_apply continuous_const).sub
    (continuous_const.mul (hd.clm_apply continuous_const))).div_const 2

/-- `∂ψ` has compact support when `ψ` does. -/
private theorem hasCompactSupport_dz_of_hasCompactSupport {ψ : ℂ → ℂ}
    (hψ : HasCompactSupport ψ) : HasCompactSupport (Work.MRMT.dz ψ) := by
  have h4 : HasCompactSupport
      (fun z : ℂ => fderiv ℝ ψ z (1 : ℂ) - Complex.I * fderiv ℝ ψ z Complex.I) := by
    have h1 : HasCompactSupport (fun z : ℂ => fderiv ℝ ψ z (1 : ℂ)) :=
      hψ.fderiv_apply ℝ (1 : ℂ)
    have h2 : HasCompactSupport (fun z : ℂ => fderiv ℝ ψ z Complex.I) :=
      hψ.fderiv_apply ℝ Complex.I
    have h3 : HasCompactSupport (fun z : ℂ => Complex.I * fderiv ℝ ψ z Complex.I) :=
      h2.comp_left (g := fun w : ℂ => Complex.I * w) (by simp)
    exact h1.sub h3
  have key : Work.MRMT.dz ψ = fun z : ℂ =>
      (fderiv ℝ ψ z (1 : ℂ) - Complex.I * fderiv ℝ ψ z Complex.I) / 2 := rfl
  rw [key]
  exact (h4.comp_left (g := fun w : ℂ => w / 2) (by simp)).comp_left (g := id) (by simp)

/-- `∂` is additive on `C¹` functions. -/
private theorem dz_add_of_contDiff {F G : ℂ → ℂ} (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) :
    Work.MRMT.dz (F + G) = Work.MRMT.dz F + Work.MRMT.dz G := by
  unfold Work.MRMT.dz
  funext z
  rw [show fderiv ℝ (F + G) z = fderiv ℝ F z + fderiv ℝ G z from
      fderiv_add ((hF.differentiable (by norm_num)).differentiableAt)
        ((hG.differentiable (by norm_num)).differentiableAt)]
  simp only [add_apply, Pi.add_apply]
  ring

/-- `∂` is `ℂ`-homogeneous on `C¹` functions. -/
private theorem dz_smul_of_contDiff (c : ℂ) {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) :
    Work.MRMT.dz (c • F) = c • Work.MRMT.dz F := by
  unfold Work.MRMT.dz
  funext z
  rw [show fderiv ℝ (c • F) z = c • fderiv ℝ F z from
      fderiv_const_smul ((hF.differentiable (by norm_num)).differentiableAt) c]
  simp only [smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ## The pairing `ψ ↦ -∫ φ · ∂ψ` on the test functions -/

/-- `φ · ∂ψ` is integrable for a locally integrable `φ` and a test function `ψ`. -/
private theorem integrable_mul_dz {φ : ℂ → ℂ} {R : ℝ}
    (hφ : LocallyIntegrable φ (volume : Measure ℂ)) {ψ : ℂ → ℂ} (hψ : ψ ∈ testSpace R) :
    Integrable (fun z => φ z * Work.MRMT.dz ψ z) (volume : Measure ℂ) := by
  have hc : Continuous (Work.MRMT.dz ψ) := continuous_dz_of_contDiff hψ.1
  have hcs : HasCompactSupport (Work.MRMT.dz ψ) :=
    hasCompactSupport_dz_of_hasCompactSupport hψ.2.1
  have h := hφ.integrable_smul_right_of_hasCompactSupport (μ := (volume : Measure ℂ)) hc hcs
  simpa only [smul_eq_mul] using h

/-- The linear functional `ψ ↦ -∫ φ · ∂ψ` on the `C¹` test functions supported in `B(0,R)`. -/
private def dzPairing (φ : ℂ → ℂ) (R : ℝ) (hφ : LocallyIntegrable φ (volume : Measure ℂ)) :
    testSpace R →ₗ[ℂ] ℂ where
  toFun ψ := -∫ z, φ z * Work.MRMT.dz (ψ : ℂ → ℂ) z
  map_add' ψ₁ ψ₂ := by
    have h1 : Integrable (fun z => φ z * Work.MRMT.dz (ψ₁ : ℂ → ℂ) z) (volume : Measure ℂ) :=
      integrable_mul_dz hφ ψ₁.2
    have h2 : Integrable (fun z => φ z * Work.MRMT.dz (ψ₂ : ℂ → ℂ) z) (volume : Measure ℂ) :=
      integrable_mul_dz hφ ψ₂.2
    show -∫ z, φ z * Work.MRMT.dz ((ψ₁ + ψ₂ : testSpace R) : ℂ → ℂ) z
        = (-∫ z, φ z * Work.MRMT.dz (ψ₁ : ℂ → ℂ) z)
          + (-∫ z, φ z * Work.MRMT.dz (ψ₂ : ℂ → ℂ) z)
    rw [← neg_add, ← integral_add h1 h2]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards with z
    rw [show Work.MRMT.dz ((ψ₁ + ψ₂ : testSpace R) : ℂ → ℂ) z
          = Work.MRMT.dz (ψ₁ : ℂ → ℂ) z + Work.MRMT.dz (ψ₂ : ℂ → ℂ) z from by
        rw [Submodule.coe_add, dz_add_of_contDiff ψ₁.2.1 ψ₂.2.1, Pi.add_apply]]
    ring
  map_smul' c ψ := by
    show -∫ z, φ z * Work.MRMT.dz ((c • ψ : testSpace R) : ℂ → ℂ) z
        = c • (-∫ z, φ z * Work.MRMT.dz (ψ : ℂ → ℂ) z)
    rw [smul_neg, ← integral_smul]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards with z
    rw [show Work.MRMT.dz ((c • ψ : testSpace R) : ℂ → ℂ) z
          = c * Work.MRMT.dz (ψ : ℂ → ℂ) z from by
        rw [Submodule.coe_smul, dz_smul_of_contDiff c ψ.2.1, Pi.smul_apply, smul_eq_mul]]
    ring

/-! ## The inner product of a test function against an `L²` class -/

/-- The `L²(B(0,R))`-inner product of `u` against the class of a test function, computed on the
whole plane: `⟪u, ψ⟫ = ∫ z, star (u z) · ψ z` (the integrand vanishes off `B(0,R)`). -/
private theorem inner_testLp_eq_integral_star_mul {R : ℝ}
    (u : Lp ℂ 2 ((volume : Measure ℂ).restrict (Metric.ball 0 R)))
    (ψ : testSpace R) :
    inner ℂ u (testLp R ψ) = ∫ z, star (u z) * (ψ : ℂ → ℂ) z := by
  rw [MeasureTheory.L2.inner_def]
  simp_rw [RCLike.inner_apply]
  simp only [starRingEnd_apply]
  have hcoe : ((↑↑(testLp R ψ) : ℂ → ℂ))
      =ᵐ[(volume : Measure ℂ).restrict (Metric.ball 0 R)] (ψ : ℂ → ℂ) := by
    rw [testLp_apply]
    exact MemLp.coeFn_toLp _
  have key : ∀ᵐ a ∂((volume : Measure ℂ).restrict (Metric.ball 0 R)),
      (↑↑(testLp R ψ) : ℂ → ℂ) a * star (u a) = (ψ : ℂ → ℂ) a * star (u a) := by
    filter_upwards [hcoe] with a ha
    rw [ha]
  rw [integral_congr_ae key]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := Metric.ball 0 R)
    (f := fun a => (ψ : ℂ → ℂ) a * star (u a)) (fun x hx => by
      have h0 : (ψ : ℂ → ℂ) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (ψ.2.2.2 h))
      rw [h0, zero_mul])]
  apply integral_congr_ae
  filter_upwards with z
  ring

theorem exists_weak_dz_deriv_of_bound_memLp {φ : ℂ → ℂ} {R : ℝ} {C : ℝ}
    (hφ : MeasureTheory.LocallyIntegrable φ (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hC : 0 ≤ C) (hdense : DenseRange (Work.MRMT.Found.testLp R))
    (hbd : ∀ ψ : Work.MRMT.Found.testSpace R,
      ‖∫ z, φ z * Work.MRMT.dz (ψ : ℂ → ℂ) z‖ ≤ C * ‖Work.MRMT.Found.testLp R ψ‖) :
    ∃ D : ℂ → ℂ,
      MeasureTheory.MemLp D 2 ((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict (Metric.ball 0 R)) ∧
      ∀ ψ : Work.MRMT.Found.testSpace R,
        ∫ z, D z * (ψ : ℂ → ℂ) z = -∫ z, φ z * Work.MRMT.dz (ψ : ℂ → ℂ) z := by
  have hLapply : ∀ ψ : testSpace R, dzPairing φ R hφ ψ
      = -∫ z, φ z * Work.MRMT.dz (ψ : ℂ → ℂ) z := fun ψ => rfl
  have hbound : ∀ ψ : testSpace R, ‖dzPairing φ R hφ ψ‖ ≤ C * ‖testLp R ψ‖ := by
    intro ψ
    rw [hLapply ψ]
    simpa using hbd ψ
  let Lext : Lp ℂ 2 ((volume : Measure ℂ).restrict (Metric.ball 0 R)) →L[ℂ] ℂ :=
    (dzPairing φ R hφ).extendOfNorm (testLp R)
  have hext : ∀ ψ : testSpace R, Lext (testLp R ψ) = dzPairing φ R hφ ψ :=
    fun ψ => LinearMap.extendOfNorm_eq hdense ⟨C, hbound⟩ ψ
  let u : Lp ℂ 2 ((volume : Measure ℂ).restrict (Metric.ball 0 R)) :=
    (InnerProductSpace.toDual ℂ (Lp ℂ 2 ((volume : Measure ℂ).restrict (Metric.ball 0 R)))).symm
      Lext
  have hu : ∀ ψ : testSpace R, dzPairing φ R hφ ψ = inner ℂ u (testLp R ψ) := by
    intro ψ
    rw [← hext ψ]
    exact (InnerProductSpace.toDual_symm_apply (x := testLp R ψ) (y := Lext)).symm
  refine ⟨fun z => star (u z), ?_, ?_⟩
  · have hmem : MemLp (u : ℂ → ℂ) 2 ((volume : Measure ℂ).restrict (Metric.ball 0 R)) :=
      Lp.memLp u
    exact hmem.star
  · intro ψ
    rw [← hLapply ψ, hu ψ, inner_testLp_eq_integral_star_mul u ψ]

end Work.MRMT.Found.PLWD
