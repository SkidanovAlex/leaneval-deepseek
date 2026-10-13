import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.KernAux

/-- The first partial derivative `p ↦ ∂₁F p` of a smooth `F : ℝ × ℝ → ℝ` is smooth,
at every finite order. -/
theorem contDiff_partFst (F : ℝ × ℝ → ℝ) (hF : ∀ n : ℕ, ContDiff ℝ n F) :
    ∀ n : ℕ, ContDiff ℝ n (fun p : ℝ × ℝ => deriv (fun s : ℝ => F (s, p.2)) p.1) := by
  intro n
  -- `f p` is the slice `s ↦ F (s, p.2)`, whose uncurried form is `F` composed with the
  -- linear map `((x,y),s) ↦ (s,y)`; `g p = p.1` is the point at which it is evaluated
  -- and `k = 1` picks out the scalar derivative.
  have hf : ContDiff ℝ (n + 1) (Function.uncurry (fun (p : ℝ × ℝ) (s : ℝ) => F (s, p.2))) := by
    have h : Function.uncurry (fun (p : ℝ × ℝ) (s : ℝ) => F (s, p.2))
        = F ∘ (fun w : (ℝ × ℝ) × ℝ => (w.2, w.1.2)) := rfl
    rw [h]
    exact (hF (n + 1)).comp (by fun_prop)
  have hg : ContDiff ℝ n (fun p : ℝ × ℝ => p.1) := contDiff_fst
  have hk : ContDiff ℝ n (fun _ : ℝ × ℝ => (1 : ℝ)) := contDiff_const
  have hmain := ContDiff.fderiv_apply (𝕜 := ℝ) hf hg hk (le_refl ((n : WithTop ℕ∞) + 1))
  simpa only [fderiv_apply_one_eq_deriv] using hmain

/-- The second partial derivative `p ↦ ∂₂F p` of a smooth `F : ℝ × ℝ → ℝ` is smooth,
at every finite order. -/
theorem contDiff_partSnd (F : ℝ × ℝ → ℝ) (hF : ∀ n : ℕ, ContDiff ℝ n F) :
    ∀ n : ℕ, ContDiff ℝ n (fun p : ℝ × ℝ => deriv (fun t : ℝ => F (p.1, t)) p.2) := by
  intro n
  have hf : ContDiff ℝ (n + 1) (Function.uncurry (fun (p : ℝ × ℝ) (s : ℝ) => F (p.1, s))) := by
    have h : Function.uncurry (fun (p : ℝ × ℝ) (s : ℝ) => F (p.1, s))
        = F ∘ (fun w : (ℝ × ℝ) × ℝ => (w.1.1, w.2)) := rfl
    rw [h]
    exact (hF (n + 1)).comp (by fun_prop)
  have hg : ContDiff ℝ n (fun p : ℝ × ℝ => p.2) := contDiff_snd
  have hk : ContDiff ℝ n (fun _ : ℝ × ℝ => (1 : ℝ)) := contDiff_const
  have hmain := ContDiff.fderiv_apply (𝕜 := ℝ) hf hg hk (le_refl ((n : WithTop ℕ∞) + 1))
  simpa only [fderiv_apply_one_eq_deriv] using hmain

theorem contDiff_partFst_partSnd (F : ℝ × ℝ → ℝ) (hF : ∀ n : ℕ, ContDiff ℝ n F) :
    (∀ n : ℕ, ContDiff ℝ n (fun p : ℝ × ℝ => deriv (fun s : ℝ => F (s, p.2)) p.1)) ∧
    (∀ n : ℕ, ContDiff ℝ n (fun p : ℝ × ℝ => deriv (fun t : ℝ => F (p.1, t)) p.2)) :=
  ⟨contDiff_partFst F hF, contDiff_partSnd F hF⟩

end Work.FTS.StrongEps.KernAux
