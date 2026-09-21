import Mathlib

/-!
# Smoothness of a parametric interval integral

If `(s, t) ↦ F s t` is `C^N` on `ℝ × ℝ`, then for fixed real `a b` the function
`s ↦ ∫ t in a..b, F s t` is `C^N`.

The proof is an induction on `N`.  The base case is continuity of a parametric interval
integral.  For the inductive step we differentiate under the integral sign: the derivative of
`s ↦ ∫ t in a..b, F s t` is `s ↦ ∫ t in a..b, ∂₁F (s, t)`, where `∂₁F (s,t) = fderiv ℝ Φ (s,t) 1`
is the partial derivative of `Φ p = F p.1 p.2` in its first variable.  This partial derivative
is again `C^N` when `F` is `C^{N+1}`, so the induction hypothesis applies to it, and
`ContDiff ℝ (n+1) f ↔ Differentiable ℝ f ∧ ContDiff ℝ n (deriv f)` finishes the job.

The differentiation under the integral sign is licensed by
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`: we use as dominating
function a constant `C` bounding `‖∂₁F‖` on the compact box
`[x₀ - 1, x₀ + 1] × uIcc a b`, which exists by compactness.
-/

open MeasureTheory intervalIntegral Set Filter

namespace Work.Analysis.Calculus

/-- The partial derivative of `p ↦ F p.1 p.2` in the first variable, evaluated at `(s, t)`.
This is a (curried) function of two real variables. -/
private noncomputable def partialFst (F : ℝ → ℝ → ℝ) (s t : ℝ) : ℝ :=
  (fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2) (s, t)) (1, 0)

private theorem contDiff_partialFst {F : ℝ → ℝ → ℝ} {N : ℕ}
    (hF : ContDiff ℝ (N + 1) (fun p : ℝ × ℝ => F p.1 p.2)) :
    ContDiff ℝ N (fun p : ℝ × ℝ => partialFst F p.1 p.2) := by
  have : ContDiff ℝ N (fun p : ℝ × ℝ =>
      (fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2) p) (1, 0)) := by fun_prop
  simpa [partialFst] using this

private theorem hasDerivAt_partialFst {F : ℝ → ℝ → ℝ} {N : ℕ}
    (hF : ContDiff ℝ (N + 1) (fun p : ℝ × ℝ => F p.1 p.2)) (x t : ℝ) :
    HasDerivAt (fun u : ℝ => F u t) (partialFst F x t) x := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => F p.1 p.2)
      (fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2) (x, t)) (x, t) :=
    (hF.differentiable (by simp)).differentiableAt.hasFDerivAt
  have h2 : HasDerivAt (fun u : ℝ => ((u, t) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) x := by
    simpa using (hasDerivAt_id x).prodMk (hasDerivAt_const x t)
  exact h1.comp_hasDerivAt x h2

/-- **Smoothness of a parametric interval integral (fixed endpoints).**
If `(s, t) ↦ F s t` is `C^N` then `s ↦ ∫ t in a..b, F s t` is `C^N`. -/
theorem contDiff_intervalIntegral_fixed_aux :
    ∀ N : ℕ, ∀ (F : ℝ → ℝ → ℝ) (a b : ℝ),
      ContDiff ℝ N (fun p : ℝ × ℝ => F p.1 p.2) →
      ContDiff ℝ N (fun s : ℝ => ∫ t in a..b, F s t) := by
  intro N
  induction N with
  | zero =>
    intro F a b hF
    have hcont : Continuous (Function.uncurry fun s t => F s t) := hF.continuous
    have hbase := continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hcont a b
    exact contDiff_zero.mpr hbase
  | succ n ih =>
    intro F a b hF
    -- Differentiation under the integral sign, with a constant bound on a compact box.
    have hderiv : ∀ x₀ : ℝ, HasDerivAt (fun s : ℝ => ∫ t in a..b, F s t)
        (∫ t in a..b, partialFst F x₀ t) x₀ := by
      intro x₀
      have hcont_deriv : Continuous fun p : ℝ × ℝ => partialFst F p.1 p.2 := by
        have : Continuous fun p : ℝ × ℝ =>
            (fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2) p) (1, 0) :=
          (hF.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
        simpa [partialFst] using this
      obtain ⟨C, hC⟩ : ∃ C, ∀ p ∈ Set.Icc (x₀ - 1) (x₀ + 1) ×ˢ Set.uIcc a b,
          ‖partialFst F p.1 p.2‖ ≤ C := by
        obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn
          hcont_deriv.continuousOn
        exact ⟨C, fun p hp => hC p hp⟩
      have hd : ∀ x t : ℝ, HasDerivAt (fun u : ℝ => F u t) (partialFst F x t) x :=
        fun x t => hasDerivAt_partialFst hF x t
      have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (μ := volume) (a := a) (b := b) (bound := fun _ => C)
        (F := fun x t => F x t) (F' := fun x t => partialFst F x t)
        (x₀ := x₀) (s := Set.Icc (x₀ - 1) (x₀ + 1))
        (Icc_mem_nhds (by linarith) (by linarith))
        (Eventually.of_forall fun x =>
          (by fun_prop : Continuous fun t : ℝ => F x t).aestronglyMeasurable)
        ((by fun_prop : Continuous fun t : ℝ => F x₀ t).intervalIntegrable a b)
        ((by fun_prop : Continuous fun t : ℝ => partialFst F x₀ t).aestronglyMeasurable)
        (by
          filter_upwards with t ht
          intro x hx
          exact hC (x, t) ⟨hx, Set.uIoc_subset_uIcc ht⟩)
        intervalIntegrable_const
        (Eventually.of_forall fun t _ x _ => hd x t)
      exact h.2
    have hG : ContDiff ℝ n (fun p : ℝ × ℝ => partialFst F p.1 p.2) := contDiff_partialFst hF
    have hih : ContDiff ℝ n (fun s : ℝ => ∫ t in a..b, partialFst F s t) :=
      ih (fun x t => partialFst F x t) a b hG
    have hder : deriv (fun s : ℝ => ∫ t in a..b, F s t) =
        fun s => ∫ t in a..b, partialFst F s t := by
      funext x
      exact (hderiv x).deriv
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = ((n : WithTop ℕ∞) + 1) from by push_cast; rfl]
    refine contDiff_succ_iff_deriv.mpr ⟨?_, ?_, ?_⟩
    · exact fun x => (hderiv x).differentiableAt
    · intro h; exact absurd h (by simp)
    · rw [hder]; exact hih

theorem contDiff_intervalIntegral_fixed (N : ℕ) {F : ℝ → ℝ → ℝ} {a b : ℝ}
    (hF : ContDiff ℝ N (fun p : ℝ × ℝ => F p.1 p.2)) :
    ContDiff ℝ N (fun s : ℝ => ∫ t in a..b, F s t) :=
  contDiff_intervalIntegral_fixed_aux N F a b hF

end Work.Analysis.Calculus
