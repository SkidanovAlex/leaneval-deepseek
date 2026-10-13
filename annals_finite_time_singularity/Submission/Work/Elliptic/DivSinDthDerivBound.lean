/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise bound `|D_θ^m (h')| ≤ C sin(2θ)`, `m = 1,…,4`

This is the elementary boundary estimate underlying `DivisionBySin`: for a slice `h` that is
smooth on a neighbourhood of the closed interval `[0, π/2]`, each of the angular iterates
`D_θ^m (∂_θ h)` (`m = 1,…,4`, with `D_θ = sin(2θ) ∂_θ`) is `sin(2θ)` times a function that
is bounded on `[0, π/2]`; hence it is `O(sin 2θ)` as `θ` tends to the two endpoints.

The key structural observation (and the reason the estimate is stated with the weight
`sin(2θ)`) is that the iterates of `D_θ` applied to `deriv h` stay of the form
`D_θ^m (h') = sin(2θ) · g_m`, where `g_m` is obtained from `g_{m-1}` by the recursion
`g_m = 2 cos(2θ) · g_{m-1} + sin(2θ) · g_{m-1}'`.  Since `g_0 = h''` is smooth on the
neighbourhood and the recursion preserves smoothness, every `g_m` is continuous on the
compact interval `[0, π/2]`, hence bounded.

Neither the vanishing hypothesis `h 0 = 0` nor `h (π/2) = 0` is needed for this bound (it
is used elsewhere, in `DivSinSliceBdd`); it is kept in the statement for uniformity.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Structural form of the iterated angular derivatives of `h'`.**  For every `m ≥ 0` the
iterate `D_θ^{m+1}(∂_θ h)` is `sin(2θ)` times a function `g` that is `C^∞` on the open
neighbourhood `(-1, π/2+1)` of `[0, π/2]` on which `h` is smooth.

The recursion on the witnesses is
`g_{m+1} = 2 cos(2θ) · g_m + sin(2θ) · g_m'`, starting from `g_0 = h''`. -/
private lemma slice_dth1Iter_factor (h : ℝ → ℝ) (hm : SmoothSlice h) :
    ∀ m : ℕ, ∃ g : ℝ → ℝ,
      ContDiffOn ℝ ⊤ g (Set.Ioo (-1) (Real.pi / 2 + 1)) ∧
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        Dth1Iter (m + 1) (deriv h) θ = Real.sin (2 * θ) * g θ := by
  intro m
  induction m with
  | zero =>
      refine ⟨deriv (deriv h), ?_, ?_⟩
      · exact (hm.deriv_of_isOpen isOpen_Ioo le_top).deriv_of_isOpen isOpen_Ioo le_top
      · intro θ _; rfl
  | succ m ih =>
      obtain ⟨g, hgc, hg⟩ := ih
      refine ⟨fun θ => 2 * Real.cos (2 * θ) * g θ + Real.sin (2 * θ) * deriv g θ,
        ?_, ?_⟩
      · have h1 : ContDiffOn ℝ ⊤ (fun θ : ℝ => 2 * Real.cos (2 * θ))
            (Set.Ioo (-1) (Real.pi / 2 + 1)) := by fun_prop
        have h2 : ContDiffOn ℝ ⊤ (deriv g) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
          hgc.deriv_of_isOpen isOpen_Ioo le_top
        have h3 : ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ))
            (Set.Ioo (-1) (Real.pi / 2 + 1)) := by fun_prop
        exact (h1.mul hgc).add (h3.mul h2)
      · intro θ hθ
        have hθU : θ ∈ Set.Ioo (-1) (Real.pi / 2 + 1) :=
          ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
        have hdg : DifferentiableAt ℝ g θ :=
          (hgc.contDiffAt (isOpen_Ioo.mem_nhds hθU)).differentiableAt (by simp)
        -- `D_θ^{m+2} (h') = sin(2θ) · ∂_θ (D_θ^{m+1}(h'))`, and `D_θ^{m+1}(h')` agrees
        -- with `sin(2θ) · g` on a neighbourhood of `θ`.
        have hev : (fun θ' => Dth1Iter (m + 1) (deriv h) θ') =ᶠ[nhds θ]
            (fun θ' => Real.sin (2 * θ') * g θ') :=
          eventually_of_mem (isOpen_Ioo.mem_nhds hθ) (fun θ' hθ' => hg θ' hθ')
        have hsin2 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ := by
          have h2 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
            simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
          exact (Real.hasDerivAt_sin (2 * θ)).comp θ h2
        have hder : deriv (Dth1Iter (m + 1) (deriv h)) θ
            = (Real.cos (2 * θ) * 2) * g θ + Real.sin (2 * θ) * deriv g θ := by
          rw [hev.deriv_eq]
          exact (hsin2.mul hdg.hasDerivAt).deriv
        rw [Dth1Iter_succ, Dth1]
        rw [hder]
        ring

theorem DivSinDthDerivBound (h : ℝ → ℝ) (hm : Work.Elliptic.SmoothSlice h) (h0 : h 0 = 0)
    (hπ : h (Real.pi / 2) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ m ∈ Finset.Icc 1 4,
      |Work.Elliptic.Dth1Iter m (deriv h) θ| ≤ C * Real.sin (2 * θ) := by
  have hsinpos : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  obtain ⟨g1, hg1c, hg1⟩ := slice_dth1Iter_factor h hm 0
  obtain ⟨g2, hg2c, hg2⟩ := slice_dth1Iter_factor h hm 1
  obtain ⟨g3, hg3c, hg3⟩ := slice_dth1Iter_factor h hm 2
  obtain ⟨g4, hg4c, hg4⟩ := slice_dth1Iter_factor h hm 3
  have hsub : Set.Icc 0 (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg1c.continuousOn.mono hsub)
  obtain ⟨C2, hC2⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg2c.continuousOn.mono hsub)
  obtain ⟨C3, hC3⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg3c.continuousOn.mono hsub)
  obtain ⟨C4, hC4⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg4c.continuousOn.mono hsub)
  have hC1' : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |g1 θ| ≤ C1 := fun θ hθ => by
    have hh := hC1 θ hθ; rwa [Real.norm_eq_abs] at hh
  have hC2' : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |g2 θ| ≤ C2 := fun θ hθ => by
    have hh := hC2 θ hθ; rwa [Real.norm_eq_abs] at hh
  have hC3' : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |g3 θ| ≤ C3 := fun θ hθ => by
    have hh := hC3 θ hθ; rwa [Real.norm_eq_abs] at hh
  have hC4' : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |g4 θ| ≤ C4 := fun θ hθ => by
    have hh := hC4 θ hθ; rwa [Real.norm_eq_abs] at hh
  have hmem0 : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hC1nn : 0 ≤ C1 := by have hh := hC1' 0 hmem0; linarith [abs_nonneg (g1 0)]
  have hC2nn : 0 ≤ C2 := by have hh := hC2' 0 hmem0; linarith [abs_nonneg (g2 0)]
  have hC3nn : 0 ≤ C3 := by have hh := hC3' 0 hmem0; linarith [abs_nonneg (g3 0)]
  have hC4nn : 0 ≤ C4 := by have hh := hC4' 0 hmem0; linarith [abs_nonneg (g4 0)]
  refine ⟨C1 + C2 + C3 + C4 + 1, by linarith, ?_⟩
  intro θ hθ m hm
  obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
  have hsp := hsinpos θ hθ
  -- the general case: `|sin(2θ)·g| ≤ C sin(2θ)` on the interior
  have key : ∀ (M : ℕ) (g : ℝ → ℝ) (C : ℝ),
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Dth1Iter M (deriv h) θ = Real.sin (2 * θ) * g θ) →
      (∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |g θ| ≤ C) →
      |Dth1Iter M (deriv h) θ| ≤ C * Real.sin (2 * θ) := by
    intro M g C hg hC
    rw [hg θ hθ, abs_mul, abs_of_pos hsp]
    have hh := mul_le_mul_of_nonneg_left (hC θ ⟨hθ.1.le, hθ.2.le⟩) hsp.le
    simpa [mul_comm] using hh
  have hfin : ∀ C : ℝ, C ≤ C1 + C2 + C3 + C4 + 1 →
      C * Real.sin (2 * θ) ≤ (C1 + C2 + C3 + C4 + 1) * Real.sin (2 * θ) := by
    intro C hC; exact mul_le_mul_of_nonneg_right hC hsp.le
  interval_cases m
  · exact le_trans (key 1 g1 C1 hg1 hC1') (hfin C1 (by linarith))
  · exact le_trans (key 2 g2 C2 hg2 hC2') (hfin C2 (by linarith))
  · exact le_trans (key 3 g3 C3 hg3 hC3') (hfin C3 (by linarith))
  · exact le_trans (key 4 g4 C4 hg4 hC4') (hfin C4 (by linarith))

end Work.Elliptic
