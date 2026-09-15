import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Calculus

/-- The second derivative of a `C²` function, evaluated on a doubled direction `h`, can be
computed as the derivative along a line: `fderiv (fun y ↦ fderiv f y h) z h` equals the second
iterated Fréchet derivative applied to `(h, h)`. -/
private lemma fderiv_fderiv_apply_eq_iteratedFDeriv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 2 f)
    (z h : E) :
    fderiv ℝ (fun y => fderiv ℝ f y h) z h = iteratedFDeriv ℝ 2 f z (fun _ : Fin 2 => h) := by
  have h1 : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 f) z :=
    (hf.differentiable_iteratedFDeriv (by norm_num)).differentiableAt
  have hfun : (fun y => fderiv ℝ f y h)
      = (fun y => (iteratedFDeriv ℝ 1 f y) (fun _ : Fin 1 => h)) := by
    ext y; rw [iteratedFDeriv_one_apply]
  rw [hfun]
  have key := DifferentiableAt.iteratedFDeriv_succ_apply_left' (f := f) (n := 1) (x := z)
      (m := fun _ : Fin 2 => h) h1
  rw [key]
  rfl

/-- **Second-order Taylor bound.**  If `f : E → F` is `C²` (over `ℝ`) and its second iterated
Fréchet derivative is bounded by `λ`, then the first-order Taylor remainder is bounded by
`λ‖h‖²`. -/
theorem norm_taylor_remainder_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {lam : ℝ} (hlam : 0 ≤ lam)
    (hf : ContDiff ℝ 2 f) (h2 : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ lam) (x h : E) :
    ‖f (x + h) - f x - fderiv ℝ f x h‖ ≤ lam * ‖h‖ ^ 2 := by
  have hfdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  set c : ℝ := lam * ‖h‖ ^ 2 with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact mul_nonneg hlam (sq_nonneg _)
  -- The two auxiliary functions, along the line through `x` in direction `h`.
  set Φ : ℝ → F := fun t => f (x + t • h) - f x - t • fderiv ℝ f x h with hΦ
  set Ψ : ℝ → F := fun t => fderiv ℝ f (x + t • h) h - fderiv ℝ f x h with hΨ
  have hgt : ∀ t, HasDerivAt (fun s : ℝ => x + s • h) h t := by
    intro t
    have hg0 : HasDerivAt (fun s : ℝ => s • h) h t := by
      simpa using (hasDerivAt_id t).smul_const h
    simpa using hg0.const_add x
  -- `Φ` has derivative `Ψ` everywhere.
  have hPhi' : ∀ t, HasDerivAt Φ (Ψ t) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => f (x + s • h)) (fderiv ℝ f (x + t • h) h) t :=
      ((hfdiff (x + t • h)).hasFDerivAt).comp_hasDerivAt t (hgt t)
    have h2 : HasDerivAt (fun _ : ℝ => f x) 0 t := hasDerivAt_const t (f x)
    have h3 : HasDerivAt (fun s : ℝ => s • fderiv ℝ f x h) (fderiv ℝ f x h) t := by
      simpa using (hasDerivAt_id t).smul_const (fderiv ℝ f x h)
    have hs := (h1.sub h2).sub h3
    rw [hΦ, hΨ]
    convert hs using 1
    · ext s; rfl
    · rw [sub_zero]
  -- `Ψ` has derivative the second iterated derivative.
  have hPsi' : ∀ t, HasDerivAt Ψ (iteratedFDeriv ℝ 2 f (x + t • h) (fun _ : Fin 2 => h)) t := by
    intro t
    have hH : HasFDerivAt (fun y => fderiv ℝ f y h)
        (fderiv ℝ (fun y => fderiv ℝ f y h) (x + t • h)) (x + t • h) :=
      (by fun_prop : DifferentiableAt ℝ (fun y => fderiv ℝ f y h) (x + t • h)).hasFDerivAt
    have hpt := hH.comp_hasDerivAt t (hgt t)
    rw [fderiv_fderiv_apply_eq_iteratedFDeriv hf (x + t • h) h] at hpt
    have h2 : HasDerivAt (fun _ : ℝ => fderiv ℝ f x h) 0 t := hasDerivAt_const t _
    have hs := hpt.sub h2
    rw [hΨ]
    convert hs using 1
    · ext s; rfl
    · rw [sub_zero]
  -- `Ψ` is continuous.
  have hPsi_cont : Continuous Ψ := by
    rw [hΨ]
    have hcc : Continuous (fun p : E × E => (fderiv ℝ f p.1) p.2) :=
      (hf.contDiff_fderiv_apply (m := 0) (by norm_num)).continuous
    have hinner : Continuous (fun s : ℝ => (x + s • h, h)) := by fun_prop
    exact (hcc.comp hinner).sub continuous_const
  -- Pointwise linear bound on `Ψ` on `[0, 1]`.
  have hPsi_bound : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖Ψ t‖ ≤ c * t := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := Ψ)
      (f' := fun t => iteratedFDeriv ℝ 2 f (x + t • h) (fun _ : Fin 2 => h))
      (a := 0) (b := 1) (B := fun t => c * t) (B' := fun _ => c)
      hPsi_cont.continuousOn ?_ ?_ (fun t => by simpa using (hasDerivAt_id t).const_mul c) ?_
    · intro t ht
      exact (hPsi' t).hasDerivWithinAt
    · rw [hΨ]; simp
    · intro t ht
      have hop : ‖iteratedFDeriv ℝ 2 f (x + t • h) (fun _ : Fin 2 => h)‖ ≤ c := by
        calc ‖iteratedFDeriv ℝ 2 f (x + t • h) (fun _ : Fin 2 => h)‖
            ≤ ‖iteratedFDeriv ℝ 2 f (x + t • h)‖ * ∏ i : Fin 2, ‖(fun _ : Fin 2 => h) i‖ :=
              ContinuousMultilinearMap.le_opNorm _ _
          _ = ‖iteratedFDeriv ℝ 2 f (x + t • h)‖ * ‖h‖ ^ 2 := by
              simp [Finset.prod_const, Fintype.card_fin]
          _ ≤ lam * ‖h‖ ^ 2 := mul_le_mul_of_nonneg_right (h2 (x + t • h)) (sq_nonneg _)
          _ = c := by rw [hc]
      exact hop
  -- Mean value inequality applied to `Φ`.
  have hmain : ‖Φ 1 - Φ 0‖ ≤ c := by
    refine norm_image_sub_le_of_norm_deriv_le_segment_01' (f := Φ) (f' := Ψ) ?_ ?_
    · intro t ht
      exact (hPhi' t).hasDerivWithinAt
    · intro t ht
      have ht1 : t ≤ 1 := le_of_lt ht.2
      have hb := hPsi_bound t ⟨ht.1, ht1⟩
      calc ‖Ψ t‖ ≤ c * t := hb
        _ ≤ c * 1 := mul_le_mul_of_nonneg_left ht1 hc0
        _ = c := by ring
  have hPhi0 : Φ 0 = 0 := by rw [hΦ]; simp
  have hPhi1 : Φ 1 = f (x + h) - f x - fderiv ℝ f x h := by rw [hΦ]; simp
  rw [hPhi0, sub_zero] at hmain
  rw [hPhi1] at hmain
  exact hmain

end Commons.Analysis.Calculus