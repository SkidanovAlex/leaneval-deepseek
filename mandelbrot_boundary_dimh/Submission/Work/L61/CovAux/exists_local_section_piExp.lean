import Mathlib
import Submission.Work.L61.Basic

namespace Work.L61.CovAux

open MandelDim

/-- `π(a + b) = π a · π b` for `π w = exp(2πiw)`. -/
theorem piExp_add' (a b : ℂ) : piExp (a + b) = piExp a * piExp b := by
  rw [piExp, piExp, piExp, ← Complex.exp_add]
  congr 1
  ring

/-- **Local section of `π w = exp(2πiw)` at a nonzero value.**  If `π w₀ = e₀ ≠ 0` then the
explicit lift `λ z = w₀ + log(z/e₀)/(2πi)` is continuous at `e₀`, takes the value `w₀` there, and
satisfies `π (λ z) = z` for every `z ≠ 0`. -/
theorem exists_local_section_piExp {e₀ w₀ : ℂ} (he : MandelDim.piExp w₀ = e₀) (h₀ : e₀ ≠ 0) :
    ∃ lam : ℂ → ℂ, ContinuousAt lam e₀ ∧ lam e₀ = w₀ ∧ ∀ z : ℂ, z ≠ 0 → MandelDim.piExp (lam z) = z := by
  refine ⟨fun z => w₀ + Complex.log (z / e₀) / (2 * Real.pi * Complex.I), ?_, ?_, ?_⟩
  · have hz : e₀ / e₀ ∈ Complex.slitPlane := by
      rw [div_self h₀]; exact Complex.one_mem_slitPlane
    have h1 : ContinuousAt (fun z : ℂ => Complex.log (z / e₀)) e₀ :=
      (continuousAt_id.div_const e₀).clog hz
    exact (h1.div_const (2 * Real.pi * Complex.I)).const_add w₀
  · show w₀ + Complex.log (e₀ / e₀) / (2 * Real.pi * Complex.I) = w₀
    rw [div_self h₀, Complex.log_one, zero_div, add_zero]
  · intro z hz
    show piExp (w₀ + Complex.log (z / e₀) / (2 * Real.pi * Complex.I)) = z
    rw [piExp_add', he, piExp_log_div (z / e₀) (div_ne_zero hz h₀)]
    exact mul_div_cancel₀ z h₀

end Work.L61.CovAux
