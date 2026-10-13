import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Elliptic.contDiffOn_one_bounds
import Submission.Work.Elliptic.htU_interior_facts
import Submission.Work.Elliptic.htU_contDiffAt
import Submission.Work.Elliptic.htU_near_pi2
import Submission.Work.Elliptic.exists_bound_of_continuousOn_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- For `t ∈ [0, π/4]`, `t ≤ (π/4) sin(2t)` (the linear lower bound for `sin` on a quarter
period). -/
private lemma le_quarter_pi_mul_sin_two (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 4)) :
    t ≤ (Real.pi / 4) * Real.sin (2 * t) := by
  obtain ⟨ht0, ht1⟩ := ht
  have h2t0 : 0 ≤ 2 * t := by linarith
  have h2t1 : 2 * t ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h3 : 2 / Real.pi * (2 * t) ≤ Real.sin (2 * t) := Real.mul_le_sin h2t0 h2t1
  have h3' : (4 / Real.pi) * t ≤ Real.sin (2 * t) := by
    have : 2 / Real.pi * (2 * t) = (4 / Real.pi) * t := by ring
    linarith [h3, this]
  have h4 : (Real.pi / 4) * ((4 / Real.pi) * t) ≤ (Real.pi / 4) * Real.sin (2 * t) :=
    mul_le_mul_of_nonneg_left h3' (by positivity)
  have h5 : (Real.pi / 4) * ((4 / Real.pi) * t) = t := by
    have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp
  linarith [h4, h5]

/-- `min θ (π/2 - θ) ≤ (π/4) sin(2θ)` on `[0, π/2]`: the two-variable form of the linear
lower bound for `sin`. -/
private lemma min_le_quarter_pi_mul_sin_two (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    min θ (Real.pi / 2 - θ) ≤ (Real.pi / 4) * Real.sin (2 * θ) := by
  rcases le_total θ (Real.pi / 2 - θ) with hle | hle
  · rw [min_eq_left hle]
    exact le_quarter_pi_mul_sin_two θ ⟨hθ.1, by linarith [hle, hθ.2]⟩
  · rw [min_eq_right hle]
    have ht : Real.pi / 2 - θ ∈ Set.Icc (0 : ℝ) (Real.pi / 4) :=
      ⟨by linarith [hθ.2], by linarith [hle]⟩
    have h := le_quarter_pi_mul_sin_two (Real.pi / 2 - θ) ht
    have hsin : Real.sin (2 * (Real.pi / 2 - θ)) = Real.sin (2 * θ) := by
      rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
    rwa [hsin] at h

/-- The reflection `θ ↦ h (π/2 - θ)` of a smooth slice is again smooth of class `C²` on the
closed interval `[0, π/2]`. -/
private lemma flip_contDiffOn (h : ℝ → ℝ) (hm : SmoothSlice h) :
    ContDiffOn ℝ 2 (fun θ => h (Real.pi / 2 - θ)) (Set.Icc 0 (Real.pi / 2)) := by
  have hσ : ContDiffOn ℝ 2 (fun θ : ℝ => Real.pi / 2 - θ) (Set.Icc 0 (Real.pi / 2)) := by
    fun_prop
  have hg : ContDiffOn ℝ 2 h (Set.Ioo (-1) (Real.pi / 2 + 1)) := hm.of_le (by norm_num)
  have hmap : Set.MapsTo (fun θ : ℝ => Real.pi / 2 - θ) (Set.Icc 0 (Real.pi / 2))
      (Set.Ioo (-1) (Real.pi / 2 + 1)) := by
    intro x hx
    simp only [Set.mem_Ioo, Set.mem_Icc] at hx ⊢
    exact ⟨by linarith [hx.2, Real.pi_pos], by linarith [hx.1]⟩
  have := hg.comp hσ hmap
  simpa only [Function.comp_def] using this

/-- Reflection (oddness) of the derivative of the angular quotient:
`(h/sin 2θ)'(θ) = - (h(π/2 - ·)/sin 2·)'(π/2 - θ)`. -/
private lemma flip_deriv_SinQ (h : ℝ → ℝ) (hm : SmoothSlice h) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (SinQ h) θ
      = - deriv (SinQ (fun θ' => h (Real.pi / 2 - θ'))) (Real.pi / 2 - θ) := by
  have hflip : ContDiffOn ℝ 2 (fun θ' => h (Real.pi / 2 - θ')) (Set.Icc 0 (Real.pi / 2)) :=
    flip_contDiffOn h hm
  have hψ : Real.pi / 2 - θ ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hd : HasDerivAt (SinQ (fun θ' => h (Real.pi / 2 - θ')))
      (deriv (SinQ (fun θ' => h (Real.pi / 2 - θ'))) (Real.pi / 2 - θ)) (Real.pi / 2 - θ) := by
    have hcd : ContDiffAt ℝ 2 (SinQ (fun θ' => h (Real.pi / 2 - θ'))) (Real.pi / 2 - θ) := by
      rw [show SinQ (fun θ' => h (Real.pi / 2 - θ')) = htU (fun θ' => h (Real.pi / 2 - θ'))
        from rfl]
      exact htU_contDiffAt (fun θ' => h (Real.pi / 2 - θ')) hflip (Real.pi / 2 - θ) hψ
    exact (hcd.differentiableAt (by norm_num)).hasDerivAt
  have hσ : HasDerivAt (fun θ' : ℝ => Real.pi / 2 - θ') (-1) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => θ') (1 : ℝ) θ := hasDerivAt_id θ
    simpa using h1.const_sub (Real.pi / 2)
  have hcomp := hd.comp θ hσ
  have heq : SinQ h =ᶠ[𝓝 θ]
      ((SinQ (fun θ' => h (Real.pi / 2 - θ'))) ∘ (fun θ' : ℝ => Real.pi / 2 - θ')) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with x _
    have hx1 : Real.pi / 2 - (Real.pi / 2 - x) = x := by ring
    have hx2 : Real.sin (2 * (Real.pi / 2 - x)) = Real.sin (2 * x) := by
      rw [show 2 * (Real.pi / 2 - x) = Real.pi - 2 * x by ring, Real.sin_pi_sub]
    simp only [Function.comp_apply, SinQ, hx1, hx2]
  have hkey : deriv (SinQ h) θ
      = deriv ((SinQ (fun θ' => h (Real.pi / 2 - θ'))) ∘ (fun θ' : ℝ => Real.pi / 2 - θ')) θ :=
    heq.deriv_eq
  rw [hkey, hcomp.deriv]
  ring

theorem DivSinSmoothBounds (h : ℝ → ℝ) (hm : Work.Elliptic.SmoothSlice h) (h0 : h 0 = 0)
    (hπ : h (Real.pi / 2) = 0) :
    ∃ C : ℝ, 0 < C ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |h θ| ≤ C * Real.sin (2 * θ)) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv h θ| ≤ C) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |Work.Elliptic.SinQ h θ| ≤ C) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv (Work.Elliptic.SinQ h) θ| ≤ C) := by
  have hpi2pos : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hf2 : ContDiffOn ℝ 2 h (Set.Icc 0 (Real.pi / 2)) := (hm.mono hsub).of_le (by norm_num)
  have hf1 : ContDiffOn ℝ 1 h (Set.Icc 0 (Real.pi / 2)) := hf2.of_le (by norm_num)
  obtain ⟨-, hcomp1, hcomp2, hid1, hid2, -, hcontdU, -, -⟩ := htU_interior_facts h hf2
  obtain ⟨M, hMnn, hMad, hMder⟩ := contDiffOn_one_bounds hf1 h0 hπ
  -- (1) pointwise decay of `h` against `sin(2θ)`
  have hpart1 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |h θ| ≤ (M * (Real.pi / 4)) * Real.sin (2 * θ) := by
    intro θ hθ
    have hθIcc : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    calc |h θ| ≤ M * min θ (Real.pi / 2 - θ) := hMad θ hθIcc
      _ ≤ M * ((Real.pi / 4) * Real.sin (2 * θ)) :=
          mul_le_mul_of_nonneg_left (min_le_quarter_pi_mul_sin_two θ hθIcc) hMnn
      _ = (M * (Real.pi / 4)) * Real.sin (2 * θ) := by ring
  -- (2) bounded first derivative
  have hpart2 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv h θ| ≤ M := fun θ hθ => by
    simpa [Real.norm_eq_abs] using hMder θ hθ
  -- (3) bounded angular quotient
  have hpart3 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |SinQ h θ| ≤ M * (Real.pi / 4) := by
    intro θ hθ
    have hsinpos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    have h : |SinQ h θ| = |h θ| / Real.sin (2 * θ) := by
      simp only [SinQ, abs_div, abs_of_pos hsinpos]
    rw [h, div_le_iff₀ hsinpos]
    exact hpart1 θ hθ
  -- (4a) bounded derivative near the right endpoint
  obtain ⟨CR, δR, -, hδR, -, -, -, -, hdR, -⟩ :=
    htU_near_pi2 h hf2 hπ hcomp1 hcomp2 hid1 hid2
  -- (4b) bounded derivative near the left endpoint, via the reflection `θ ↦ π/2 - θ`
  have hflipCD : ContDiffOn ℝ 2 (fun θ' => h (Real.pi / 2 - θ')) (Set.Icc 0 (Real.pi / 2)) :=
    flip_contDiffOn h hm
  obtain ⟨-, hcomp1f, hcomp2f, hid1f, hid2f, -, -, -, -⟩ :=
    htU_interior_facts (fun θ' => h (Real.pi / 2 - θ')) hflipCD
  have hflip0 : (fun θ' => h (Real.pi / 2 - θ')) (Real.pi / 2) = 0 := by simpa using h0
  obtain ⟨CL, δL, -, hδL, -, -, -, -, hdL, -⟩ :=
    htU_near_pi2 (fun θ' => h (Real.pi / 2 - θ')) hflipCD hflip0 hcomp1f hcomp2f hid1f hid2f
  have hcont_dSinQ : ContinuousOn (fun x => deriv (SinQ h) x) (Set.Ioo 0 (Real.pi / 2)) := by
    rw [show SinQ h = htU h from rfl]
    exact hcontdU
  have hleft : ∃ C δ : ℝ, 0 < δ ∧ ∀ x ∈ Set.Ioo (0 : ℝ) (0 + δ), |deriv (SinQ h) x| ≤ C := by
    refine ⟨CL, min δL (Real.pi / 4), lt_min hδL (by linarith [Real.pi_pos]), ?_⟩
    intro x hx
    rw [zero_add] at hx
    have hxlt : x < Real.pi / 2 := by linarith [hx.2, min_le_right δL (Real.pi / 4), Real.pi_pos]
    have hxIoo : x ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hx.1, hxlt⟩
    have hψ : Real.pi / 2 - x ∈ Set.Ioo (Real.pi / 2 - δL) (Real.pi / 2) :=
      ⟨by linarith [hx.2, min_le_left δL (Real.pi / 4)], by linarith [hx.1]⟩
    rw [flip_deriv_SinQ h hm x hxIoo, abs_neg]
    exact hdL (Real.pi / 2 - x) hψ
  have hright : ∃ C δ : ℝ, 0 < δ ∧
      ∀ x ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), |deriv (SinQ h) x| ≤ C := by
    refine ⟨CR, min δR (Real.pi / 4), lt_min hδR (by linarith [Real.pi_pos]), ?_⟩
    intro x hx
    have hx' : x ∈ Set.Ioo (Real.pi / 2 - δR) (Real.pi / 2) :=
      ⟨by linarith [hx.1, min_le_left δR (Real.pi / 4)], hx.2⟩
    exact hdR x hx'
  obtain ⟨C4, hC4⟩ :=
    exists_bound_of_continuousOn_Ioo (a := 0) (b := Real.pi / 2) hpi2pos hcont_dSinQ hleft hright
  -- assemble the four constants
  set D : ℝ := max (M * (Real.pi / 4)) (max M (max C4 0)) with hD
  have hD1 : M * (Real.pi / 4) ≤ D := by rw [hD]; exact le_max_left _ _
  have hD2 : M ≤ D := by
    rw [hD]
    exact le_trans (le_max_left M (max C4 0)) (le_max_right (M * (Real.pi / 4)) _)
  have hD3 : C4 ≤ D := by
    rw [hD]
    exact le_trans (le_max_left C4 0)
      (le_trans (le_max_right M (max C4 0)) (le_max_right (M * (Real.pi / 4)) _))
  refine ⟨max 1 D, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_, ?_, ?_, ?_⟩
  · intro θ hθ
    have h1 := hpart1 θ hθ
    have hsin : 0 ≤ Real.sin (2 * θ) := by
      have hsp : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
      linarith
    calc |h θ| ≤ (M * (Real.pi / 4)) * Real.sin (2 * θ) := h1
      _ ≤ D * Real.sin (2 * θ) := mul_le_mul_of_nonneg_right hD1 hsin
      _ ≤ (max 1 D) * Real.sin (2 * θ) := mul_le_mul_of_nonneg_right (le_max_right 1 D) hsin
  · intro θ hθ
    exact le_trans (hpart2 θ hθ) (le_trans hD2 (le_max_right 1 D))
  · intro θ hθ
    exact le_trans (hpart3 θ hθ) (le_trans hD1 (le_max_right 1 D))
  · intro θ hθ
    exact le_trans (hC4 θ hθ) (le_trans hD3 (le_max_right 1 D))

end Work.Elliptic
