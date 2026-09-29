import Mathlib
import Submission.Work.A14D.setup
import Submission.Work.C17g.linear_ode_convex

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

noncomputable section

/-- The system matrix `sysA` is holomorphic on any open set on which `PZ` does not vanish. -/
private lemma differentiableOn_sysA {Ω : Set ℂ} (hP : ∀ z ∈ Ω, PZ z ≠ 0) :
    DifferentiableOn ℂ sysA Ω := by
  have hPZ : DifferentiableOn ℂ PZ Ω := by unfold PZ; fun_prop
  have hPZ' : DifferentiableOn ℂ PZ' Ω := by unfold PZ'; fun_prop
  have hRZ : DifferentiableOn ℂ RZ Ω := by unfold RZ; fun_prop
  have h0 : DifferentiableOn ℂ (fun z => -(RZ z / PZ z)) Ω := (hRZ.div hPZ hP).neg
  have h1 : DifferentiableOn ℂ (fun z => -(PZ' z / PZ z)) Ω := (hPZ'.div hPZ hP).neg
  refine differentiableOn_pi.mpr (fun i => ?_)
  refine differentiableOn_pi.mpr (fun j => ?_)
  fin_cases i <;> fin_cases j
  · simp [sysA]
  · simp [sysA]
  · simpa [sysA] using h0
  · simpa [sysA] using h1

/-- Existence of a solution of `LZ y = 0` on an open convex `Ω ⊆ {PZ ≠ 0}` with prescribed value
`a` and derivative `b` at a point `z₀ ∈ Ω`.  (Modules: `Submission.Work.A14D.setup` for `PZ`,
`LZ`, `sysA`, `sysb`, `toSol`, `hasDerivAt_toSol`, `LZ_of_hasDerivAt_toSol`.)

Proof route: `LZ y = 0` is equivalent to the first order system `(y, y')' = sysA z · (y, y')`
(`sum_sysA_zero`, `sum_sysA_one`); apply `Work.C17g.linear_ode_convex` with `A := sysA`,
`b := fun _ _ => 0`, `k = 2`, `Y₀ := ![a, b]` (the entries of `sysA` are holomorphic on `Ω`
because `PZ ≠ 0` there), and take `y := fun z => Y z 0`.  Then `deriv y = Y · 1` and
`LZ_of_hasDerivAt_toSol` gives `LZ y z = 0`. -/
theorem exists_sol_LZ_convex {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hP : ∀ z ∈ Ω, PZ z ≠ 0) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (a b : ℂ) :
    ∃ y : ℂ → ℂ, DifferentiableOn ℂ y Ω ∧ y z₀ = a ∧ deriv y z₀ = b ∧
      DifferentiableOn ℂ (deriv y) Ω ∧ ∀ z ∈ Ω, LZ y z = 0 := by
  have hA : DifferentiableOn ℂ sysA Ω := differentiableOn_sysA hP
  have hb : DifferentiableOn ℂ (fun _ : ℂ => (fun _ : Fin 2 => (0:ℂ))) Ω :=
    differentiableOn_const _
  obtain ⟨Y, hYdiff, hYz0, hYderiv⟩ :=
    Work.C17g.linear_ode_convex hΩc hΩo sysA (fun _ _ => (0:ℂ)) hA hb z₀ hz₀ (fun i => ![a, b] i)
  have hY0 : DifferentiableOn ℂ (fun z => Y z 0) Ω := (differentiableOn_pi.mp hYdiff) 0
  have hY1 : DifferentiableOn ℂ (fun z => Y z 1) Ω := (differentiableOn_pi.mp hYdiff) 1
  -- the first component of `Y` is the function, the second its derivative
  have hdY0 : ∀ w ∈ Ω, HasDerivAt (fun z => Y z 0) (Y w 1) w := by
    intro w hw
    have h := (hasDerivAt_pi.mp (hYderiv w hw)) 0
    have hv : (∑ j, sysA w 0 j * Y w j + 0) = Y w 1 := by
      simp only [Fin.sum_univ_two, sysA, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val']
      ring
    rwa [hv] at h
  have hderiv_eq : ∀ w ∈ Ω, deriv (fun z => Y z 0) w = Y w 1 := fun w hw => (hdY0 w hw).deriv
  have hdy : DifferentiableOn ℂ (deriv (fun z => Y z 0)) Ω :=
    hY1.congr (fun w hw => hderiv_eq w hw)
  -- `toSol` of the first component is `Y`
  have htoSol : ∀ w ∈ Ω, toSol (fun z => Y z 0) w = Y w := by
    intro w hw
    funext i
    fin_cases i <;> simp [toSol, hderiv_eq w hw]
  refine ⟨fun z => Y z 0, hY0, ?_, ?_, hdy, ?_⟩
  · have h := congr_fun hYz0 0
    simpa using h
  · have h := hderiv_eq z₀ hz₀
    rw [h]
    have h2 := congr_fun hYz0 1
    simpa using h2
  · intro z hz
    have hev : toSol (fun z => Y z 0) =ᶠ[𝓝 z] Y := by
      filter_upwards [hΩo.mem_nhds hz] with w hw
      exact htoSol w hw
    have h1 := (hYderiv z hz).congr_of_eventuallyEq hev
    have htarget : (fun i => ∑ j, sysA z i j * Y z j + 0)
        = fun i => ∑ j, sysA z i j * toSol (fun z => Y z 0) z j
            + sysb (fun _ => (0:ℂ)) z i := by
      funext i
      rw [htoSol z hz]
      fin_cases i <;> simp [sysb]
    rw [htarget] at h1
    exact LZ_of_hasDerivAt_toSol h1 (hdy.differentiableAt (hΩo.mem_nhds hz)) (hP z hz)

end

end Work.A14D
