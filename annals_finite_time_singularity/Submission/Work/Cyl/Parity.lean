import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.Cyl.FieldDeriv
import Submission.Work.Cyl.isOdd_cylField
import Submission.Work.Cyl.isOdd_of_reflZ_invariant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Parity in the axial variable

The `IsOdd` dictionary for axisymmetric no-swirl fields, for the stream-function field `psiField`,
and the derivative parity lemmas.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix Topology
open Filter
open Work.Cyl
open FiniteTimeSingularity

namespace Work.Cyl

/-! ## Derivatives of functions with a parity in the axial variable -/

theorem evenZ_pdZ_of_oddZ {ψ : ℝ → ℝ → ℝ} (h : OddZ ψ) : EvenZ (pdZ ψ) := by
  intro r z
  have key : deriv (fun x : ℝ => ψ r (-x)) (-z) = -deriv (fun x : ℝ => ψ r x) z := by
    have hc := deriv_comp_neg (fun x : ℝ => ψ r x) (-z)
    simpa using hc
  have key2 : deriv (fun x : ℝ => ψ r (-x)) (-z) = -deriv (fun x : ℝ => ψ r x) (-z) := by
    have hfun : (fun x : ℝ => ψ r (-x)) = fun x : ℝ => -(ψ r x) := by
      funext x; exact h r x
    rw [hfun]
    exact deriv.neg
  rw [pdZ, pdZ]
  linarith [key, key2]

theorem oddZ_pdR_of_oddZ {ψ : ℝ → ℝ → ℝ} (h : OddZ ψ) : OddZ (pdR ψ) := by
  intro r z
  rw [pdR, pdR]
  have hfun : (fun r' : ℝ => ψ r' (-z)) = fun r' : ℝ => -(ψ r' z) := by
    funext r'; exact h r' z
  rw [hfun]
  exact deriv.neg

theorem evenZ_pdR_of_evenZ {ψ : ℝ → ℝ → ℝ} (h : EvenZ ψ) : EvenZ (pdR ψ) := by
  intro r z
  rw [pdR, pdR]
  have hfun : (fun r' : ℝ => ψ r' (-z)) = fun r' : ℝ => ψ r' z := by
    funext r'; exact h r' z
  rw [hfun]

theorem oddZ_pdZ_of_evenZ {ψ : ℝ → ℝ → ℝ} (h : EvenZ ψ) : OddZ (pdZ ψ) := by
  intro r z
  have key : deriv (fun x : ℝ => ψ r (-x)) (-z) = -deriv (fun x : ℝ => ψ r x) z := by
    have hc := deriv_comp_neg (fun x : ℝ => ψ r x) (-z)
    simpa using hc
  have key2 : deriv (fun x : ℝ => ψ r (-x)) (-z) = deriv (fun x : ℝ => ψ r x) (-z) := by
    have hfun : (fun x : ℝ => ψ r (-x)) = fun x : ℝ => ψ r x := by
      funext x; exact h r x
    rw [hfun]
  rw [pdZ, pdZ]
  linarith [key, key2]

theorem isOdd_psiField_of_oddZ {ψ : ℝ → ℝ → ℝ} (h : OddZ ψ) : IsOdd (psiField ψ) := by
  rw [psiField, isOdd_cylField]
  refine ⟨?_, ?_⟩
  · intro r _ z
    exact evenZ_pdZ_of_oddZ h r z
  · intro r _ z
    show -(ψ r (-z) / r) - pdR ψ r (-z) = -(-(ψ r z / r) - pdR ψ r z)
    rw [h r z, oddZ_pdR_of_oddZ h r z]
    ring

/-! ## Propagation of the reflection symmetry -/

lemma flipZ_flipZ (v : R3) : flipZ (flipZ v) = v := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [flipZ, FiniteTimeSingularity.e]

/-- If a solution is unique in its class and the reflected field is again a solution with the same
initial data, then the solution is invariant under the reflection `reflZ`. -/
theorem reflZ_invariant_of_unique (p : R3 → ℝ → ℝ) (u₀ : R3 → R3) (T : ℝ)
    (u : R3 → ℝ → R3)
    (huniq : ∀ v : R3 → ℝ → R3, IsLocalEulerEquationSolution p u₀ T v → v = u)
    (href : IsLocalEulerEquationSolution p u₀ T (fun x t => flipZ (u (reflZ x) t))) :
    ∀ t x, u (reflZ x) t = flipZ (u x t) := by
  intro t x
  have h := huniq (fun x t => flipZ (u (reflZ x) t)) href
  have h2 : flipZ (u (reflZ x) t) = u x t := congrFun (congrFun h x) t
  rw [← h2, flipZ_flipZ]

/-- Reflection-symmetry propagation, hypothesis-level form: if `u` is axisymmetric without swirl
and is invariant under the reflection in the axis coordinate (this is what uniqueness of the
solution in the class gives, see `reflZ_invariant_of_unique`), then `u` is odd in the sense of
`IsOdd`. -/
theorem isOdd_solution_of_unique_reflection (p : R3 → ℝ → ℝ) (u₀ : R3 → R3) (T : ℝ)
    (u : R3 → ℝ → R3)
    (huniq : ∀ v : R3 → ℝ → R3, IsLocalEulerEquationSolution p u₀ T v → v = u)
    (href : IsLocalEulerEquationSolution p u₀ T (fun x t => flipZ (u (reflZ x) t)))
    (hax : ∀ t, IsAxiNoSwirl (u · t)) :
    ∀ t ∈ Set.Ico 0 T, IsOdd (u · t) := by
  intro t _
  exact isOdd_of_reflZ_invariant (u · t) (hax t)
    (fun x => reflZ_invariant_of_unique p u₀ T u huniq href t x)

/-! ## The converse: oddness of the field forces oddness of the stream function -/

/-- If `psiField ψ` is odd, `ψ` vanishes on `z = 0` and the slices `z ↦ ψ r z` are
differentiable, then `ψ` is odd in `z` on the half plane `r ≥ 0`. -/
theorem oddZnn_of_isOdd_psiField {ψ : ℝ → ℝ → ℝ} (hzero : ∀ r, ψ r 0 = 0)
    (hcont : ∀ z, ContinuousAt (fun r => ψ r z) 0)
    (hdiff : ∀ r z, DifferentiableAt ℝ (fun z' => ψ r z') z)
    (hodd : IsOdd (psiField ψ)) : OddZnn ψ := by
  rw [psiField, isOdd_cylField] at hodd
  obtain ⟨h1, _⟩ := hodd
  have key : ∀ r, 0 < r → ∀ z, ψ r (-z) = -ψ r z := by
    intro r hr
    have hF : Differentiable ℝ (fun z' : ℝ => ψ r z' + ψ r (-z')) := fun z' =>
      (hdiff r z').add ((hdiff r (-z')).comp z' differentiable_neg.differentiableAt)
    have hF' : ∀ z', deriv (fun z' : ℝ => ψ r z' + ψ r (-z')) z' = 0 := by
      intro z'
      have hd2 : DifferentiableAt ℝ (fun z'' : ℝ => ψ r (-z'')) z' :=
        (hdiff r (-z')).comp z' differentiable_neg.differentiableAt
      have e1 : deriv (fun z'' : ℝ => ψ r z'') z' = pdZ ψ r z' := rfl
      have e2 : deriv (fun z'' : ℝ => ψ r (-z'')) z' = -pdZ ψ r (-z') := by
        have hc := deriv_comp_neg (fun z'' : ℝ => ψ r z'') z'
        rw [hc, pdZ]
      have hsum : deriv (fun z'' : ℝ => ψ r z'' + ψ r (-z'')) z'
          = deriv (fun z'' : ℝ => ψ r z'') z' + deriv (fun z'' : ℝ => ψ r (-z'')) z' := by
        rw [show (fun z'' : ℝ => ψ r z'' + ψ r (-z'')) =
          (fun z'' : ℝ => ψ r z'') + fun z'' : ℝ => ψ r (-z'') from rfl]
        exact deriv_add (hdiff r z') hd2
      rw [hsum, e1, e2, h1 r hr z']
      ring
    intro z
    have hc := is_const_of_deriv_eq_zero hF hF' z 0
    rw [hzero r, neg_zero, hzero r] at hc
    linarith
  intro r hr z
  rcases lt_or_eq_of_le hr with hpos | h0
  · exact key r hpos z
  · subst h0
    have hlim1 : Tendsto (fun r' : ℝ => ψ r' z) (𝓝[>] (0 : ℝ)) (𝓝 (ψ 0 z)) :=
      (hcont z).tendsto.mono_left nhdsWithin_le_nhds
    have hlim2 : Tendsto (fun r' : ℝ => ψ r' (-z)) (𝓝[>] (0 : ℝ)) (𝓝 (ψ 0 (-z))) :=
      (hcont (-z)).tendsto.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ r' in 𝓝[>] (0 : ℝ), ψ r' z = -ψ r' (-z) := by
      filter_upwards [self_mem_nhdsWithin] with r' hr'
      have := key r' hr' z
      linarith
    have hlim3 : Tendsto (fun r' : ℝ => -ψ r' (-z)) (𝓝[>] (0 : ℝ)) (𝓝 (ψ 0 z)) :=
      hlim1.congr' hev
    have hu := tendsto_nhds_unique hlim3 hlim2.neg
    linarith

/-! ## Parity of the scalar vorticity -/

/-- If `ψ` is odd in `x₃`, then the scalar vorticity `ω^θ = ∂_z u_r - ∂_r u_z` of the
stream-function field is odd in `x₃` (the parity hypothesis of the paper's §Setup). -/
theorem oddZ_vortTheta_psiField {ψ : ℝ → ℝ → ℝ} (h : OddZ ψ) :
    OddZ (vortTheta (pdZ ψ) (fun r z => -(ψ r z / r) - pdR ψ r z)) := by
  have hZ : EvenZ (pdZ ψ) := evenZ_pdZ_of_oddZ h
  have huz : OddZ (fun r z => -(ψ r z / r) - pdR ψ r z) := by
    intro r z
    show -(ψ r (-z) / r) - pdR ψ r (-z) = -(-(ψ r z / r) - pdR ψ r z)
    rw [h r z, oddZ_pdR_of_oddZ h r z]
    ring
  intro r z
  show pdZ (pdZ ψ) r (-z) - pdR (fun r z => -(ψ r z / r) - pdR ψ r z) r (-z)
    = -(pdZ (pdZ ψ) r z - pdR (fun r z => -(ψ r z / r) - pdR ψ r z) r z)
  rw [oddZ_pdZ_of_evenZ hZ r z, oddZ_pdR_of_oddZ huz r z]
  ring

end Work.Cyl
