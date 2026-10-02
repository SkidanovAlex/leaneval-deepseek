/-
Copyright: Work.MRMT (mandelbar) subproject.

# The weak (distributional) Leibniz rule for the Wirtinger derivatives

If `ψ : ℂ → ℂ` is smooth with compact support and `h` has weak (distributional) Wirtinger
derivatives `gz = ∂h` and `gzbar = ∂̄h` (`Work.MRMT.IsDzDeriv h gz`, `Work.MRMT.IsDbarDeriv h
gzbar`), then `ψ · h` has weak Wirtinger derivatives

`∂(ψ h) = ψ ∂h + h ∂ψ`,   `∂̄(ψ h) = ψ ∂̄h + h ∂̄ψ`.

The proof is the standard integration-by-parts argument.  For a test function `φ`, the product
`ψφ` is again a test function, so the defining identity of `IsDzDeriv h gz` applied to `ψφ` gives

`∫ h · ∂(ψφ) = -∫ gz · (ψφ)`,

and the pointwise Leibniz rule `∂(ψφ) = ψ ∂φ + φ ∂ψ`
(`Work.MRMT.QC.dz_mul`, `Work.MRMT.QC.dzbar_mul`) turns the left-hand side into
`∫ ψ h · ∂φ + ∫ h ∂ψ · φ`, which rearranges to the claim.

## The order parameter `⊤` in `ContDiff ℝ ⊤ ψ`

The statement that was requested has the hypothesis `ContDiff ℝ ⊤ ψ`.  In Lean's order
`ℕ∞ω = WithTop ℕ∞` for `ContDiff` the element `⊤` is `ω`, i.e. **real analyticity**, while
`C^∞` is `∞ = ((⊤ : ℕ∞) : ℕ∞ω)`.  So the requested statement is true but its hypothesis is
stronger than needed; in fact it forces `ψ = 0` as soon as `ψ` has compact support (see
`Work.MRMT.Sobolev.eq_zero_of_contDiff_omega_hasCompactSupport`).  We therefore prove the
statement carrying the actual content, with `ψ` smooth (`ContDiff ℝ ∞ ψ`), and derive the
requested statement from it, since analyticity implies smoothness (`∞ ≤ ω`).
-/
import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.QC.WirtingerCalc

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal ContDiff

namespace Work.MRMT.QC

/-- `∂f` is continuous as soon as `f` is `C^n` with `n ≠ 0`: `z ↦ fderiv ℝ f z` is continuous
and evaluation of a continuous linear map is continuous. -/
theorem continuous_dz_of_contDiff {f : ℂ → ℂ} {n : WithTop ℕ∞} (hn : n ≠ 0)
    (hc : ContDiff ℝ n f) : Continuous (dz f) := by
  have hd : Continuous (fderiv ℝ f) := hc.continuous_fderiv hn
  unfold dz
  exact ((hd.clm_apply continuous_const).sub
    (continuous_const.mul (hd.clm_apply continuous_const))).div_const 2

/-- `∂̄f` is continuous as soon as `f` is `C^n` with `n ≠ 0`. -/
theorem continuous_dzbar_of_contDiff {f : ℂ → ℂ} {n : WithTop ℕ∞} (hn : n ≠ 0)
    (hc : ContDiff ℝ n f) : Continuous (dzbar f) := by
  have hd : Continuous (fderiv ℝ f) := hc.continuous_fderiv hn
  unfold dzbar
  exact ((hd.clm_apply continuous_const).add
    (continuous_const.mul (hd.clm_apply continuous_const))).div_const 2

/-- The pointwise product of two test functions on `ℂ`, again a test function. -/
def testMul (ψ φ : TestFunction (⊤ : TopologicalSpace.Opens ℂ) ℂ ⊤) :
    TestFunction (⊤ : TopologicalSpace.Opens ℂ) ℂ ⊤ :=
  ⟨fun z => (ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z, ψ.contDiff.mul φ.contDiff,
    ψ.hasCompactSupport.mul_right, Set.subset_univ _⟩

@[simp] theorem testMul_coe (ψ φ : TestFunction (⊤ : TopologicalSpace.Opens ℂ) ℂ ⊤) :
    (testMul ψ φ : ℂ → ℂ) = fun z => (ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z := rfl

@[simp] theorem testMul_apply (ψ φ : TestFunction (⊤ : TopologicalSpace.Opens ℂ) ℂ ⊤) (z : ℂ) :
    (testMul ψ φ : ℂ → ℂ) z = (ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z := rfl

/-- **The weak `∂`-Leibniz rule**: multiplying a locally integrable function by a test function
`ψ` multiplies its weak `∂`-derivative data as claimed. -/
theorem isDzDeriv_mul_of_testFunction {h gz : ℂ → ℂ}
    (ψ : TestFunction (⊤ : TopologicalSpace.Opens ℂ) ℂ ⊤) (hz : IsDzDeriv h gz) :
    IsDzDeriv (fun z => ψ z * h z) (fun z => ψ z * gz z + h z * dz (ψ : ℂ → ℂ) z) := by
  obtain ⟨hh, hgz, hmain⟩ := hz
  have hψd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ : ℂ → ℂ) := ψ.contDiff
  have hψc : Continuous (ψ : ℂ → ℂ) := hψd.continuous
  have hdzψc : Continuous (dz (ψ : ℂ → ℂ)) := continuous_dz_of_contDiff (by simp) hψd
  refine ⟨?_, ?_, ?_⟩
  · -- `ψ · h` is locally integrable
    have h : (fun z => (ψ : ℂ → ℂ) z * h z) = fun z => h z * (ψ : ℂ → ℂ) z := by
      funext z; ring
    rw [h]
    exact hh.mul_continuous hψc
  · -- `ψ · gz + h · ∂ψ` is locally integrable
    have h1 : LocallyIntegrable (fun z => h z * dz (ψ : ℂ → ℂ) z) volume := hh.mul_continuous hdzψc
    have h2 : LocallyIntegrable (fun z => gz z * (ψ : ℂ → ℂ) z) volume := hgz.mul_continuous hψc
    have h : (fun z => (ψ : ℂ → ℂ) z * gz z + h z * dz (ψ : ℂ → ℂ) z)
        = fun z => h z * dz (ψ : ℂ → ℂ) z + gz z * (ψ : ℂ → ℂ) z := by
      funext z; ring
    rw [h]
    exact h1.add h2
  · intro φ
    have hcφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ : ℂ → ℂ) := φ.contDiff
    have hdzφc : Continuous (dz (φ : ℂ → ℂ)) := continuous_dz_of_contDiff (by simp) hcφ
    -- the defining identity for `h`, tested against the test function `ψ φ`
    obtain ⟨hInt1, hInt2, hEq⟩ := hmain (testMul ψ φ)
    -- the pointwise Leibniz rule, at every point
    have hpt : ∀ z, dz (testMul ψ φ : ℂ → ℂ) z
        = dz (ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z + (ψ : ℂ → ℂ) z * dz (φ : ℂ → ℂ) z := by
      intro z
      rw [testMul_coe]
      exact dz_mul ((hψd.differentiable (by simp)) z) ((hcφ.differentiable (by simp)) z)
    -- the three integrals appearing in the computation
    have hP : Integrable (fun z => h z * (dz (ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z)) := by
      have hcont : Continuous (fun z => dz (ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z) := hdzψc.mul φ.continuous
      have hcs : HasCompactSupport (fun z => dz (ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z) :=
        φ.hasCompactSupport.mul_left
      simpa only [smul_eq_mul] using hh.integrable_smul_right_of_hasCompactSupport hcont hcs
    have hQ : Integrable (fun z => h z * ((ψ : ℂ → ℂ) z * dz (φ : ℂ → ℂ) z)) := by
      have hcont : Continuous (fun z => (ψ : ℂ → ℂ) z * dz (φ : ℂ → ℂ) z) := hψc.mul hdzφc
      have hcs : HasCompactSupport (fun z => (ψ : ℂ → ℂ) z * dz (φ : ℂ → ℂ) z) :=
        ψ.hasCompactSupport.mul_right
      simpa only [smul_eq_mul] using hh.integrable_smul_right_of_hasCompactSupport hcont hcs
    have hR : Integrable (fun z => gz z * ((ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z)) := by
      simpa only [testMul_apply] using hInt2
    -- the defining identity, expanded with the Leibniz rule
    have hEqexp : ∫ z, h z * dz (testMul ψ φ : ℂ → ℂ) z
        = - ∫ z, gz z * ((ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z) := by
      have hc : (fun z => gz z * ((ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z))
          = fun z => gz z * (testMul ψ φ : ℂ → ℂ) z := by
        funext z; simp [testMul_apply]
      rw [hc, hEq]
    have hEq1 : ∫ z, (h z * (dz (ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z)
          + h z * ((ψ : ℂ → ℂ) z * dz (φ : ℂ → ℂ) z))
        = - ∫ z, gz z * ((ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z) := by
      rw [← hEqexp]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [hpt z]
      ring
    have hPQ : (∫ z, h z * (dz (ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z))
        + (∫ z, h z * ((ψ : ℂ → ℂ) z * dz (φ : ℂ → ℂ) z))
        = - ∫ z, gz z * ((ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z) := by
      rw [← integral_add hP hQ]
      exact hEq1
    refine ⟨?_, ?_, ?_⟩
    · have h : (fun z => (ψ : ℂ → ℂ) z * h z * dz (φ : ℂ → ℂ) z)
          = fun z => h z * ((ψ : ℂ → ℂ) z * dz (φ : ℂ → ℂ) z) := by funext z; ring
      rw [h]
      exact hQ
    · have h : (fun z => ((ψ : ℂ → ℂ) z * gz z + h z * dz (ψ : ℂ → ℂ) z) * (φ : ℂ → ℂ) z)
          = fun z => gz z * ((ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z)
              + h z * (dz (ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z) := by funext z; ring
      rw [h]
      exact hR.add hP
    · show ∫ z, ((ψ : ℂ → ℂ) z * h z) * dz (φ : ℂ → ℂ) z
          = - ∫ z, ((ψ : ℂ → ℂ) z * gz z + h z * dz (ψ : ℂ → ℂ) z) * (φ : ℂ → ℂ) z
      have hL : ∫ z, ((ψ : ℂ → ℂ) z * h z) * dz (φ : ℂ → ℂ) z
          = ∫ z, h z * ((ψ : ℂ → ℂ) z * dz (φ : ℂ → ℂ) z) :=
        integral_congr_ae (Eventually.of_forall fun z => by ring)
      have hRR : ∫ z, ((ψ : ℂ → ℂ) z * gz z + h z * dz (ψ : ℂ → ℂ) z) * (φ : ℂ → ℂ) z
          = (∫ z, gz z * ((ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z))
            + (∫ z, h z * (dz (ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z)) := by
        rw [← integral_add hR hP]
        exact integral_congr_ae (Eventually.of_forall fun z => by ring)
      rw [hL, hRR, eq_neg_iff_add_eq_zero]
      linear_combination hPQ

/-- **The weak `∂̄`-Leibniz rule**. -/
theorem isDbarDeriv_mul_of_testFunction {h gzbar : ℂ → ℂ}
    (ψ : TestFunction (⊤ : TopologicalSpace.Opens ℂ) ℂ ⊤) (hb : IsDbarDeriv h gzbar) :
    IsDbarDeriv (fun z => ψ z * h z) (fun z => ψ z * gzbar z + h z * dzbar (ψ : ℂ → ℂ) z) := by
  obtain ⟨hh, hgz, hmain⟩ := hb
  have hψd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ : ℂ → ℂ) := ψ.contDiff
  have hψc : Continuous (ψ : ℂ → ℂ) := hψd.continuous
  have hdzψc : Continuous (dzbar (ψ : ℂ → ℂ)) := continuous_dzbar_of_contDiff (by simp) hψd
  refine ⟨?_, ?_, ?_⟩
  · have h : (fun z => (ψ : ℂ → ℂ) z * h z) = fun z => h z * (ψ : ℂ → ℂ) z := by
      funext z; ring
    rw [h]
    exact hh.mul_continuous hψc
  · have h1 : LocallyIntegrable (fun z => h z * dzbar (ψ : ℂ → ℂ) z) volume :=
      hh.mul_continuous hdzψc
    have h2 : LocallyIntegrable (fun z => gzbar z * (ψ : ℂ → ℂ) z) volume := hgz.mul_continuous hψc
    have h : (fun z => (ψ : ℂ → ℂ) z * gzbar z + h z * dzbar (ψ : ℂ → ℂ) z)
        = fun z => h z * dzbar (ψ : ℂ → ℂ) z + gzbar z * (ψ : ℂ → ℂ) z := by
      funext z; ring
    rw [h]
    exact h1.add h2
  · intro φ
    have hcφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ : ℂ → ℂ) := φ.contDiff
    have hdzφc : Continuous (dzbar (φ : ℂ → ℂ)) := continuous_dzbar_of_contDiff (by simp) hcφ
    obtain ⟨hInt1, hInt2, hEq⟩ := hmain (testMul ψ φ)
    have hpt : ∀ z, dzbar (testMul ψ φ : ℂ → ℂ) z
        = dzbar (ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z + (ψ : ℂ → ℂ) z * dzbar (φ : ℂ → ℂ) z := by
      intro z
      rw [testMul_coe]
      exact dzbar_mul ((hψd.differentiable (by simp)) z) ((hcφ.differentiable (by simp)) z)
    have hP : Integrable (fun z => h z * ((φ : ℂ → ℂ) z * dzbar (ψ : ℂ → ℂ) z)) := by
      have hcont : Continuous (fun z => (φ : ℂ → ℂ) z * dzbar (ψ : ℂ → ℂ) z) :=
        φ.continuous.mul hdzψc
      have hcs : HasCompactSupport (fun z => (φ : ℂ → ℂ) z * dzbar (ψ : ℂ → ℂ) z) :=
        φ.hasCompactSupport.mul_right
      simpa only [smul_eq_mul] using hh.integrable_smul_right_of_hasCompactSupport hcont hcs
    have hQ : Integrable (fun z => h z * ((ψ : ℂ → ℂ) z * dzbar (φ : ℂ → ℂ) z)) := by
      have hcont : Continuous (fun z => (ψ : ℂ → ℂ) z * dzbar (φ : ℂ → ℂ) z) := hψc.mul hdzφc
      have hcs : HasCompactSupport (fun z => (ψ : ℂ → ℂ) z * dzbar (φ : ℂ → ℂ) z) :=
        ψ.hasCompactSupport.mul_right
      simpa only [smul_eq_mul] using hh.integrable_smul_right_of_hasCompactSupport hcont hcs
    have hR : Integrable (fun z => gzbar z * ((ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z)) := by
      simpa only [testMul_apply] using hInt2
    have hEqexp : ∫ z, h z * dzbar (testMul ψ φ : ℂ → ℂ) z
        = - ∫ z, gzbar z * ((ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z) := by
      have hc : (fun z => gzbar z * ((ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z))
          = fun z => gzbar z * (testMul ψ φ : ℂ → ℂ) z := by
        funext z; simp [testMul_apply]
      rw [hc, hEq]
    have hEq1 : ∫ z, (h z * ((φ : ℂ → ℂ) z * dzbar (ψ : ℂ → ℂ) z)
          + h z * ((ψ : ℂ → ℂ) z * dzbar (φ : ℂ → ℂ) z))
        = - ∫ z, gzbar z * ((ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z) := by
      rw [← hEqexp]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [hpt z]
      ring
    have hPQ : (∫ z, h z * ((φ : ℂ → ℂ) z * dzbar (ψ : ℂ → ℂ) z))
        + (∫ z, h z * ((ψ : ℂ → ℂ) z * dzbar (φ : ℂ → ℂ) z))
        = - ∫ z, gzbar z * ((ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z) := by
      rw [← integral_add hP hQ]
      exact hEq1
    refine ⟨?_, ?_, ?_⟩
    · have h : (fun z => (ψ : ℂ → ℂ) z * h z * dzbar (φ : ℂ → ℂ) z)
          = fun z => h z * ((ψ : ℂ → ℂ) z * dzbar (φ : ℂ → ℂ) z) := by funext z; ring
      rw [h]
      exact hQ
    · have h : (fun z => ((ψ : ℂ → ℂ) z * gzbar z + h z * dzbar (ψ : ℂ → ℂ) z) * (φ : ℂ → ℂ) z)
          = fun z => gzbar z * ((ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z)
              + h z * ((φ : ℂ → ℂ) z * dzbar (ψ : ℂ → ℂ) z) := by funext z; ring
      rw [h]
      exact hR.add hP
    · show ∫ z, ((ψ : ℂ → ℂ) z * h z) * dzbar (φ : ℂ → ℂ) z
          = - ∫ z, ((ψ : ℂ → ℂ) z * gzbar z + h z * dzbar (ψ : ℂ → ℂ) z) * (φ : ℂ → ℂ) z
      have hL : ∫ z, ((ψ : ℂ → ℂ) z * h z) * dzbar (φ : ℂ → ℂ) z
          = ∫ z, h z * ((ψ : ℂ → ℂ) z * dzbar (φ : ℂ → ℂ) z) :=
        integral_congr_ae (Eventually.of_forall fun z => by ring)
      have hRR : ∫ z, ((ψ : ℂ → ℂ) z * gzbar z + h z * dzbar (ψ : ℂ → ℂ) z) * (φ : ℂ → ℂ) z
          = (∫ z, gzbar z * ((ψ : ℂ → ℂ) z * (φ : ℂ → ℂ) z))
            + (∫ z, h z * ((φ : ℂ → ℂ) z * dzbar (ψ : ℂ → ℂ) z)) := by
        rw [← integral_add hR hP]
        exact integral_congr_ae (Eventually.of_forall fun z => by ring)
      rw [hL, hRR, eq_neg_iff_add_eq_zero]
      linear_combination hPQ

/-- The hypothesis of `isDzDeriv_mul_and_isDbarDeriv_mul_of_contDiff_infty` is neither
vacuous nor degenerate: a bump function is smooth, compactly supported and non-zero.
(Contrast the requested hypothesis `ContDiff ℝ ⊤ ψ = ContDiff ℝ ω ψ`, real analyticity, which
together with compact support forces `ψ = 0`; see
`Work.MRMT.Sobolev.eq_zero_of_contDiff_omega_hasCompactSupport`.) -/
theorem exists_ne_zero_contDiff_infty_hasCompactSupport :
    ∃ ψ : ℂ → ℂ, ψ ≠ 0 ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧ HasCompactSupport ψ := by
  obtain ⟨f⟩ := (inferInstance : Nonempty (ContDiffBump (0 : ℂ)))
  refine ⟨fun z => (f z : ℂ), ?_, ?_, ?_⟩
  · intro h
    have h1 : f 0 = 1 := f.one_of_mem_closedBall (Metric.mem_closedBall_self f.rIn_pos.le)
    have h2 : ((f 0 : ℝ) : ℂ) = 0 := congrFun h 0
    rw [h1] at h2
    exact one_ne_zero h2.symm.symm
  · exact Complex.ofRealCLM.contDiff.comp f.contDiff
  · exact f.hasCompactSupport.comp_left Complex.ofReal_zero

/-- **The weak Leibniz rule for the Wirtinger derivatives**, for `ψ` smooth with compact
support.  This is the statement carrying the mathematical content; see the module docstring on
the order parameter `⊤`. -/
theorem isDzDeriv_mul_and_isDbarDeriv_mul_of_contDiff_infty {h gz gzbar ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψs : HasCompactSupport ψ)
    (hz : IsDzDeriv h gz) (hb : IsDbarDeriv h gzbar) :
    IsDzDeriv (fun z => ψ z * h z) (fun z => ψ z * gz z + h z * dz ψ z) ∧
    IsDbarDeriv (fun z => ψ z * h z) (fun z => ψ z * gzbar z + h z * dzbar ψ z) := by
  have h1 := isDzDeriv_mul_of_testFunction
    (⟨ψ, hψ, hψs, Set.subset_univ _⟩ : TestFunction (⊤ : TopologicalSpace.Opens ℂ) ℂ ⊤) hz
  have h2 := isDbarDeriv_mul_of_testFunction
    (⟨ψ, hψ, hψs, Set.subset_univ _⟩ : TestFunction (⊤ : TopologicalSpace.Opens ℂ) ℂ ⊤) hb
  exact ⟨by simpa using h1, by simpa using h2⟩

/-- **The weak Leibniz rule for the Wirtinger derivatives**, as requested. -/
theorem isDzDeriv_mul_and_isDbarDeriv_mul {h gz gzbar ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ ⊤ ψ) (hψs : HasCompactSupport ψ)
    (hz : Work.MRMT.IsDzDeriv h gz) (hb : Work.MRMT.IsDbarDeriv h gzbar) :
    Work.MRMT.IsDzDeriv (fun z => ψ z * h z) (fun z => ψ z * gz z + h z * Work.MRMT.dz ψ z) ∧
    Work.MRMT.IsDbarDeriv (fun z => ψ z * h z)
      (fun z => ψ z * gzbar z + h z * Work.MRMT.dzbar ψ z) :=
  isDzDeriv_mul_and_isDbarDeriv_mul_of_contDiff_infty (hψ.of_le le_top) hψs hz hb

end Work.MRMT.QC
