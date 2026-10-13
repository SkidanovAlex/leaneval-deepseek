import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SolutionDelivery.Scaling.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Oddness is preserved by the Euler rescaling of a datum

`rescaleDatum lam F = fun x => lam • F (lam • x)`.  The oddness class
`FiniteTimeSingularity.IsOdd` is the coordinatewise parity condition of the challenge: the `i`-th
component of `u` is odd in the `i`-th coordinate and even in the other two.  Multiplication by a
constant preserves oddness/evenness of a real function, and the linear change of variable
`x ↦ lam • x` sends the `i`-th coordinate to `lam * xᵢ` while keeping the other two coordinates
proportional to constants, so each component of `rescaleDatum lam F` has exactly the same parity
profile as the corresponding component of `F`.
-/

namespace Work.SolutionDelivery.Scaling

open FiniteTimeSingularity

/-- The `i`-th coordinate of `c • v`, for `v : R3`. -/
lemma ofLp_smul_fin3 (c : ℝ) (v : Work.SolutionDelivery.R3) (i : Fin 3) :
    (c • v).ofLp i = c * v.ofLp i := by
  rw [PiLp.smul_apply]
  rfl

/-- The coordinatewise description of a scalar multiple of `!₂[a,b,d]` in `ℝ³`. -/
lemma smul_vec3_fin3 (c a b d : ℝ) :
    (c • (!₂[a, b, d] : Work.SolutionDelivery.R3)) = !₂[c * a, c * b, c * d] := by
  rw [PiLp.ext_iff]
  intro i
  fin_cases i <;> simp

/-- `t ↦ c * g (c * t)` is odd when `g` is odd. -/
lemma odd_const_mul_comp {g : ℝ → ℝ} (hg : Function.Odd g) (c : ℝ) :
    Function.Odd (fun t => c * g (c * t)) := by
  intro t
  change c * g (c * (-t)) = -(c * g (c * t))
  have h : c * (-t) = -(c * t) := by ring
  rw [h, hg (c * t)]
  ring

/-- `t ↦ c * g (c * t)` is even when `g` is even. -/
lemma even_const_mul_comp {g : ℝ → ℝ} (hg : Function.Even g) (c : ℝ) :
    Function.Even (fun t => c * g (c * t)) := by
  intro t
  change c * g (c * (-t)) = c * g (c * t)
  have h : c * (-t) = -(c * t) := by ring
  rw [h, hg (c * t)]

theorem isOdd_rescaleDatum {lam : ℝ} {F : Work.SolutionDelivery.R3 → Work.SolutionDelivery.R3}
    (h : FiniteTimeSingularity.IsOdd F) :
    FiniteTimeSingularity.IsOdd (Work.SolutionDelivery.rescaleDatum lam F) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [FiniteTimeSingularity.IsOdd, Work.SolutionDelivery.rescaleDatum]
  refine ⟨?_, ?_, ?_⟩
  · intro x₁ x₂
    obtain ⟨ha, hb, hc⟩ := h1 (lam * x₁) (lam * x₂)
    refine ⟨?_, ?_, ?_⟩
    · have hfun : (fun x => (lam • F (lam • !₂[x, x₁, x₂])).ofLp 0)
          = (fun x => lam * (F !₂[lam * x, lam * x₁, lam * x₂]).ofLp 0) := by
        funext x
        rw [ofLp_smul_fin3, smul_vec3_fin3]
      rw [hfun]
      exact odd_const_mul_comp ha lam
    · have hfun : (fun x => (lam • F (lam • !₂[x, x₁, x₂])).ofLp 1)
          = (fun x => lam * (F !₂[lam * x, lam * x₁, lam * x₂]).ofLp 1) := by
        funext x
        rw [ofLp_smul_fin3, smul_vec3_fin3]
      rw [hfun]
      exact even_const_mul_comp hb lam
    · have hfun : (fun x => (lam • F (lam • !₂[x, x₁, x₂])).ofLp 2)
          = (fun x => lam * (F !₂[lam * x, lam * x₁, lam * x₂]).ofLp 2) := by
        funext x
        rw [ofLp_smul_fin3, smul_vec3_fin3]
      rw [hfun]
      exact even_const_mul_comp hc lam
  · intro x₀ x₂
    obtain ⟨ha, hb, hc⟩ := h2 (lam * x₀) (lam * x₂)
    refine ⟨?_, ?_, ?_⟩
    · have hfun : (fun x => (lam • F (lam • !₂[x₀, x, x₂])).ofLp 0)
          = (fun x => lam * (F !₂[lam * x₀, lam * x, lam * x₂]).ofLp 0) := by
        funext x
        rw [ofLp_smul_fin3, smul_vec3_fin3]
      rw [hfun]
      exact even_const_mul_comp ha lam
    · have hfun : (fun x => (lam • F (lam • !₂[x₀, x, x₂])).ofLp 1)
          = (fun x => lam * (F !₂[lam * x₀, lam * x, lam * x₂]).ofLp 1) := by
        funext x
        rw [ofLp_smul_fin3, smul_vec3_fin3]
      rw [hfun]
      exact odd_const_mul_comp hb lam
    · have hfun : (fun x => (lam • F (lam • !₂[x₀, x, x₂])).ofLp 2)
          = (fun x => lam * (F !₂[lam * x₀, lam * x, lam * x₂]).ofLp 2) := by
        funext x
        rw [ofLp_smul_fin3, smul_vec3_fin3]
      rw [hfun]
      exact even_const_mul_comp hc lam
  · intro x₀ x₁
    obtain ⟨ha, hb, hc⟩ := h3 (lam * x₀) (lam * x₁)
    refine ⟨?_, ?_, ?_⟩
    · have hfun : (fun x => (lam • F (lam • !₂[x₀, x₁, x])).ofLp 0)
          = (fun x => lam * (F !₂[lam * x₀, lam * x₁, lam * x]).ofLp 0) := by
        funext x
        rw [ofLp_smul_fin3, smul_vec3_fin3]
      rw [hfun]
      exact even_const_mul_comp ha lam
    · have hfun : (fun x => (lam • F (lam • !₂[x₀, x₁, x])).ofLp 1)
          = (fun x => lam * (F !₂[lam * x₀, lam * x₁, lam * x]).ofLp 1) := by
        funext x
        rw [ofLp_smul_fin3, smul_vec3_fin3]
      rw [hfun]
      exact even_const_mul_comp hb lam
    · have hfun : (fun x => (lam • F (lam • !₂[x₀, x₁, x])).ofLp 2)
          = (fun x => lam * (F !₂[lam * x₀, lam * x₁, lam * x]).ofLp 2) := by
        funext x
        rw [ofLp_smul_fin3, smul_vec3_fin3]
      rw [hfun]
      exact odd_const_mul_comp hc lam

end Work.SolutionDelivery.Scaling
