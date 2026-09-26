import Mathlib
import Submission.Work.Asymptotics.K24FZ
import Submission.Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Residues.ResidueTheorem
import Submission.Work.Asymptotics.KPlus_second_residue_at_crossed_zero

namespace Work.Asymptotics

open UpperHalfPlane Filter
open scoped Manifold Topology

/-- `j' = -2πi E₄²E₆/Δ` is holomorphic on `ℍ`. -/
private lemma mdifferentiable_jprime :
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

/-- There is a point of `ℍ` at which `j'` does not vanish (namely `3i`). -/
private lemma exists_jprime_ne_zero_point :
    ∃ w : UpperHalfPlane, Work.Residues.jprime w ≠ 0 := by
  refine ⟨Work.Kernels.imagAxis 3 (by norm_num : (0 : ℝ) < 3), ?_⟩
  refine jprime_ne_zero_of_three_le_im _ ?_
  simp [Work.Kernels.imagAxis]

/-- The set on which the holomorphic function `j'` does not vanish is dense: `j'` is not the
zero function, and a holomorphic function on the connected manifold `ℍ` which vanishes on an
open set vanishes identically. -/
theorem exists_jprime_ne_zero_near (τ : UpperHalfPlane) (ε : ℝ) (hε : 0 < ε) :
    ∃ τ' : UpperHalfPlane, dist τ τ' < ε ∧ Work.Residues.jprime τ' ≠ 0 := by
  by_contra h
  push Not at h
  have hzero : Work.Residues.jprime = 0 := by
    refine eq_zero_of_frequently (τ := τ) mdifferentiable_jprime ?_
    have hball : Metric.ball τ ε ∈ 𝓝 τ := Metric.ball_mem_nhds τ hε
    have hev : ∀ᶠ z in 𝓝[≠] τ, Work.Residues.jprime z = 0 := by
      filter_upwards [nhdsWithin_le_nhds hball] with z hz
      rw [Metric.mem_ball, dist_comm] at hz
      exact h z hz
    exact hev.frequently
  obtain ⟨w, hw⟩ := exists_jprime_ne_zero_point
  exact hw (congrFun hzero w)

end Work.Asymptotics
