import Mathlib
import Submission.Work.Induction.IndRepModel

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Induction.trace_indE`

The rank-one piece `indE V h g y = indIns V (h * y * g⁻¹) ∘ (V.ρ h ∘ indEval V y)` of the
operator `indT V g ∘ indQh V h` has trace `V.character h` when `h = y * g * y⁻¹` and trace
`0` otherwise.

The proof is the standard trace identity `tr (A ∘ B) = tr (B ∘ A)` applied to the factorisation
`indE V h g y = indIns V z ∘ ((V.ρ h) ∘ indEval V y)` with `z = h * y * g⁻¹`: the other cyclic
composite is the endomorphism of `V` sending `v` to `V.ρ h v` if `y = z` and to `0` otherwise.
-/

namespace Work.Induction

set_option linter.unusedSectionVars false

open Classical

variable {G : Type*} [Group G] [Fintype G] {H : Subgroup G}

/-- The composite `(V.ρ h ∘ eval_y) ∘ insert_z` on `V`: it is `V.ρ h` when `y = z` and `0`
otherwise. -/
lemma comp_indEval_indIns (V : FDRep ℂ H) (h : H) (y z : G) :
    ((V.ρ h).comp (indEval V y)).comp (indIns V z) = if y = z then V.ρ h else 0 := by
  by_cases hyz : y = z
  · rw [ite_eq_left hyz]
    ext v
    simp [hyz]
  · rw [ite_eq_right hyz]
    ext v
    simp [hyz]

/-- The trace of `indE V h g y` on the space `G → V` of all functions, in the form in which the
trace identity produces it. -/
lemma trace_indE_eq (V : FDRep ℂ H) (h : H) (g y : G) :
    LinearMap.trace ℂ (G → V) (indE V h g y)
      = if y = (h : G) * y * g⁻¹ then V.character h else 0 := by
  classical
  have htr : LinearMap.trace ℂ (G → V) (indE V h g y)
      = LinearMap.trace ℂ V
          (((V.ρ h).comp (indEval V y)).comp (indIns V ((h : G) * y * g⁻¹))) := by
    rw [show indE V h g y
        = (indIns V ((h : G) * y * g⁻¹)).comp ((V.ρ h).comp (indEval V y)) from rfl]
    exact LinearMap.trace_comp_comm' (M := G → V) (N := V)
      ((V.ρ h).comp (indEval V y)) (indIns V ((h : G) * y * g⁻¹))
  rw [htr, comp_indEval_indIns]
  by_cases hyz : y = (h : G) * y * g⁻¹
  · rw [ite_eq_left hyz, ite_eq_left hyz]
    rfl
  · rw [ite_eq_right hyz, ite_eq_right hyz]
    exact map_zero _

/-- `y = h * y * g⁻¹` is the same condition as `h = y * g * y⁻¹`. -/
lemma self_conj_iff (h g y : G) : (y = h * y * g⁻¹) ↔ (h = y * g * y⁻¹) := by
  constructor
  · intro hh
    have h1 : g = y⁻¹ * h * y := by
      have hc := congrArg (fun t : G => y⁻¹ * t * g) hh
      simpa [mul_assoc] using hc
    calc h = y * (y⁻¹ * h * y) * y⁻¹ := by group
      _ = y * g * y⁻¹ := by rw [h1]
  · intro hh
    have h1 : y⁻¹ * h * y = g := by
      have hc := congrArg (fun t : G => y⁻¹ * t * y) hh
      simpa [mul_assoc] using hc
    have h2 : h = y * g * y⁻¹ := by
      have hc := congrArg (fun t : G => y * t * y⁻¹) h1
      simpa [mul_assoc] using hc
    rw [h2]
    group

theorem trace_indE {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    (V : FDRep ℂ H) (h : H) (g y : G) :
    LinearMap.trace ℂ (G → V) (Work.Induction.indE V h g y)
      = if (h : G) = y * g * y⁻¹ then V.character h else 0 := by
  rw [trace_indE_eq]
  by_cases hyz : y = (h : G) * y * g⁻¹
  · rw [ite_eq_left hyz, ite_eq_left (self_conj_iff (h : G) g y |>.mp hyz)]
  · rw [ite_eq_right hyz,
      ite_eq_right (fun hh => hyz (self_conj_iff (h : G) g y |>.mpr hh))]

end Work.Induction
