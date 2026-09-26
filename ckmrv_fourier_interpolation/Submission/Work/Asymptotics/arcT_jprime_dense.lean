/-
# Density of the non-vanishing locus of `j'`

`Work.Residues.jprime = -2πi E₄²E₆/Δ` is holomorphic on `ℍ` and does not vanish identically
(it does not vanish near `2i`, by `Work.Asymptotics.exists_jprime_lower_near_imagAxis`).  Hence
by the identity theorem (`UpperHalfPlane.eq_zero_of_frequently`) its zero set has empty
interior: every point of `ℍ` has points with `j' ≠ 0` arbitrarily close by.

This is the clean (import-safe) replacement of `Work.Asymptotics.exists_jprime_ne_zero_near`,
whose transitive imports contain the clashing module `Work.Asymptotics.KPlusXiDefs`.
-/
import Mathlib
import Submission.Work.Residues.ResidueKernel
import Submission.Work.Asymptotics.exists_jprime_lower_near_imagAxis
import Submission.Work.Asymptotics.continuous_AfunFun
import Submission.Work.Asymptotics.KfunClear_vanish_of_phiPair
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.Graze.Vanishing

namespace Work.Asymptotics

open UpperHalfPlane
open scoped Manifold Topology

/-- `j' = -2πi E₄²E₆/Δ` is holomorphic on `ℍ`. -/
lemma mdifferentiable_jprime' :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Work.Residues.jprime := by
  have hE4 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Work.Kernels.E4Fun :=
    ModularFormClass.holo ModularForm.E₄
  have hE6 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Work.Kernels.E6Fun :=
    ModularFormClass.holo ModularForm.E₆
  have hD : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Work.Kernels.DeltaFun :=
    ModularFormClass.holo
      (CuspForm.discriminant :
        CuspForm (Matrix.SpecialLinearGroup.mapGL ℝ).range 12)
  have hnum : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun z : ℍ => -(2 * (Real.pi : ℂ) * Complex.I) *
        Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z) :=
    ((mdifferentiable_const.mul (hE4.pow 2))).mul hE6
  rw [show Work.Residues.jprime = (fun z : ℍ =>
      -(2 * (Real.pi : ℂ) * Complex.I) * Work.Kernels.E4Fun z ^ 2 *
        Work.Kernels.E6Fun z / Work.Kernels.DeltaFun z) from rfl]
  exact hnum.div hD (fun z => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z)

/-- There is a point of `ℍ` at which `j'` does not vanish. -/
lemma exists_jprime_ne_zero_point' :
    ∃ w : UpperHalfPlane, Work.Residues.jprime w ≠ 0 := by
  obtain ⟨η, c, hη, hc, hb⟩ :=
    exists_jprime_lower_near_imagAxis (s₀ := 2) (by norm_num) (by norm_num)
  refine ⟨Work.Kernels.imagAxis 2 (by norm_num), fun h => ?_⟩
  have hdist : ‖((Work.Kernels.imagAxis 2 (by norm_num) : UpperHalfPlane) : ℂ)
      - Complex.I * ((2 : ℝ) : ℂ)‖ = 0 := by
    rw [Work.Kernels.imagAxis]
    simp [Complex.ext_iff, Complex.mul_im, Complex.mul_re]
  have := hb (Work.Kernels.imagAxis 2 (by norm_num)) (by rw [hdist]; exact hη)
  rw [h, norm_zero] at this
  linarith

/-- **The non-vanishing locus of `j'` is dense.** -/
theorem exists_jprime_ne_zero_near' (τ : UpperHalfPlane) (ε : ℝ) (hε : 0 < ε) :
    ∃ τ' : UpperHalfPlane, dist τ τ' < ε ∧ Work.Residues.jprime τ' ≠ 0 := by
  by_contra h
  push_neg at h
  have hzero : Work.Residues.jprime = 0 := by
    refine UpperHalfPlane.eq_zero_of_frequently (τ := τ) mdifferentiable_jprime' ?_
    have hball : Metric.ball τ ε ∈ 𝓝 τ := Metric.ball_mem_nhds τ hε
    have hev : ∀ᶠ z in 𝓝[≠] τ, Work.Residues.jprime z = 0 := by
      filter_upwards [nhdsWithin_le_nhds hball] with z hz
      rw [Metric.mem_ball, dist_comm] at hz
      exact h z hz
    exact hev.frequently
  obtain ⟨w, hw⟩ := exists_jprime_ne_zero_point'
  exact hw (congrFun hzero w)

end Work.Asymptotics
