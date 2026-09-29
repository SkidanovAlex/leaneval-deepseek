import Mathlib
import Submission.Work.A14D.setup
import Submission.Work.OdeCont.uniqueness

namespace Work.A14D

/-- Uniqueness for the second order operator `LZ`: two solutions of `LZ y = 0` on an open
preconnected `U ⊆ {PZ ≠ 0}` which agree in value and first derivative at one point of `U` agree
on all of `U`.  (Modules: `Submission.Work.A14D.setup` for `PZ`, `LZ`, `toSol`,
`hasDerivAt_toSol`; `Submission.Work.OdeCont.uniqueness`.)

Proof route: `toSol g = ![g, deriv g]` solves the first order system `Y' = sysA z · Y` on `U`
(`hasDerivAt_toSol` with `g := fun _ => 0`, using `LZ g = 0` and `PZ ≠ 0`); apply
`Work.OdeCont.uniqueness` to `toSol g₁`, `toSol g₂` (the entries of `sysA` are holomorphic on `U`
since `PZ ≠ 0` there) and read off the first component. -/
theorem eqOn_of_sol_LZ {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hP : ∀ z ∈ U, PZ z ≠ 0) {g₁ g₂ : ℂ → ℂ} (h₁ : DifferentiableOn ℂ g₁ U)
    (h₂ : DifferentiableOn ℂ g₂ U) (hL₁ : ∀ z ∈ U, LZ g₁ z = 0) (hL₂ : ∀ z ∈ U, LZ g₂ z = 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hv : g₁ z₀ = g₂ z₀) (hd : deriv g₁ z₀ = deriv g₂ z₀) :
    Set.EqOn g₁ g₂ U := by
  -- `deriv g` is holomorphic on the open set `U` whenever `g` is
  have hder₁ : DifferentiableOn ℂ (deriv g₁) U := h₁.deriv hUo
  have hder₂ : DifferentiableOn ℂ (deriv g₂) U := h₂.deriv hUo
  -- the vector valued functions `toSol g` are holomorphic on `U`
  have htoSol₁ : DifferentiableOn ℂ (toSol g₁) U := by
    rw [differentiableOn_pi]
    intro i
    fin_cases i
    · simpa [toSol] using h₁
    · simpa [toSol] using hder₁
  have htoSol₂ : DifferentiableOn ℂ (toSol g₂) U := by
    rw [differentiableOn_pi]
    intro i
    fin_cases i
    · simpa [toSol] using h₂
    · simpa [toSol] using hder₂
  -- and they solve the first order system `Y' = sysA z · Y` (the homogeneous one, `b = 0`)
  have hsys₁ : ∀ z ∈ U, HasDerivAt (toSol g₁)
      (fun i : Fin 2 => (∑ j, sysA z i j * toSol g₁ z j)
        + (fun _ : ℂ => (0 : Fin 2 → ℂ)) z i) z := by
    intro z hz
    have h := hasDerivAt_toSol (u := g₁) (g := (0 : ℂ → ℂ))
      (h₁.differentiableAt (hUo.mem_nhds hz)) (hder₁.differentiableAt (hUo.mem_nhds hz))
      (hP z hz) (by simpa using hL₁ z hz)
    refine h.congr_deriv ?_
    funext i
    fin_cases i <;> simp [sysb]
  have hsys₂ : ∀ z ∈ U, HasDerivAt (toSol g₂)
      (fun i : Fin 2 => (∑ j, sysA z i j * toSol g₂ z j)
        + (fun _ : ℂ => (0 : Fin 2 → ℂ)) z i) z := by
    intro z hz
    have h := hasDerivAt_toSol (u := g₂) (g := (0 : ℂ → ℂ))
      (h₂.differentiableAt (hUo.mem_nhds hz)) (hder₂.differentiableAt (hUo.mem_nhds hz))
      (hP z hz) (by simpa using hL₂ z hz)
    refine h.congr_deriv ?_
    funext i
    fin_cases i <;> simp [sysb]
  -- the coefficients of `sysA` are holomorphic on `U` because `PZ` does not vanish there
  have hA : ∀ i j : Fin 2, DifferentiableOn ℂ (fun z : ℂ => sysA z i j) U := by
    have hPZ : DifferentiableOn ℂ PZ U := by unfold PZ; fun_prop
    have hPZ' : DifferentiableOn ℂ PZ' U := by unfold PZ'; fun_prop
    have hRZ : DifferentiableOn ℂ RZ U := by unfold RZ; fun_prop
    have h10 : DifferentiableOn ℂ (fun z : ℂ => -(RZ z / PZ z)) U := (hRZ.div hPZ hP).neg
    have h11 : DifferentiableOn ℂ (fun z : ℂ => -(PZ' z / PZ z)) U := (hPZ'.div hPZ hP).neg
    intro i j
    fin_cases i
    · fin_cases j <;> simp [sysA]
    · fin_cases j
      · show DifferentiableOn ℂ (fun z : ℂ => -(RZ z / PZ z)) U
        exact h10
      · show DifferentiableOn ℂ (fun z : ℂ => -(PZ' z / PZ z)) U
        exact h11
  have hb : ∀ i : Fin 2, DifferentiableOn ℂ (fun z : ℂ =>
      (fun _ : ℂ => (0 : Fin 2 → ℂ)) z i) U :=
    fun _ => by simp
  -- the two vector solutions agree at `z₀`
  have hz₀eq : toSol g₁ z₀ = toSol g₂ z₀ := by
    funext i
    fin_cases i <;> simp [toSol, hv, hd]
  have hEq := Work.OdeCont.uniqueness (k := 2) (U := U) hUo hUc sysA
    (fun _ : ℂ => (0 : Fin 2 → ℂ)) hA hb (toSol g₁) (toSol g₂) htoSol₁ htoSol₂
    hsys₁ hsys₂ hz₀ hz₀eq
  -- read off the first component
  intro z hz
  have h := congrFun (hEq hz) 0
  simpa [toSol] using h

end Work.A14D
