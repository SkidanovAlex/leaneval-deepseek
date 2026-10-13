import Mathlib
import Submission.Work.WilE3.Taylor.Grad.lagrangeOfBoundaryMin
import Submission.Work.WilE3.Taylor.CaseII.aux_fderiv_mul_exp_sum_single
import Submission.Work.WilE3.Taylor.CaseII.aux_hasStrictFDerivAt_mul_exp_sum
import Submission.Work.WilE3.Taylor.CaseII.aux_coeff_eq_zero_of_minor_ne_zero

namespace Work.WilE3.Taylor.CaseII

open Classical

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / CaseII: **the Lagrange condition at a *boundary*
  minimum of the perturbed squared gradient norm `G · exp⟨v, ·- y⟩`.**

  The companion statement `pert_lagrange_interior` treats the level-set version; this file treats the
  case of a minimum which is additionally constrained to the sphere `∑ i, (z i - y i)² = const` about
  `y` — the situation at a point of the boundary of a level set inside a ball.  Two constraints are
  active, and the conclusion is that the gradient at `u` of the *perturbed* squared gradient norm
  `G := ∑ l (∂ₗ Φ)²` lies in the two-dimensional span of the two constraint gradients `∇Φ u` and
  `u - y`:

      `∇G u + G u • v = a • ∇Φ u + b • (u - y)`.

  The hypothesis `hloc` is only stated *eventually* near `u` (on the intersection of the two level
  sets), which is exactly what the Łojasiewicz argument supplies.  To consume it, the objective of the
  Lagrange argument is taken to be the *weighted* function

      `F z = (∑ l (∂ₗ Φ z)²) · exp (∑ i, v i (z i - y i))`,

  for which `∇F u = exp⟨v, u - y⟩ • (∇G u + G u • v)`; dividing the multiplier relation by the
  (non-zero) multipliers `Λ₀` and `exp⟨v, u - y⟩` yields the claim.  The independence of the two
  constraint gradients is exactly the hypothesis `hindep` (a non-vanishing `2 × 2` minor), and is what
  forces the multiplier `Λ₀` of the objective to be non-zero: if `Λ₀` vanished, the relation would
  read `Λ₀' • ∇Φ u + Λ₁' • (u - y) = 0`, contradicting the non-vanishing of that minor
  (`aux_coeff_eq_zero_of_minor_ne_zero`).
-/

theorem pert_lagrange_boundary {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {v y u : Fin k → ℝ}
    (hΦ : ∀ z, AnalyticAt ℝ Φ z)
    (hindep : ∃ i j : Fin k,
      Work.WilE3.Taylor.grad Φ u i * (u j - y j)
        - Work.WilE3.Taylor.grad Φ u j * (u i - y i) ≠ 0)
    (hloc : ∀ᶠ z in nhds u, Φ z = Φ u → (∑ i, (z i - y i) ^ 2) = (∑ i, (u i - y i) ^ 2) →
      (∑ l, (Work.WilE3.Taylor.grad Φ u l) ^ 2) * Real.exp (∑ i, v i * (u i - y i))
        ≤ (∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) * Real.exp (∑ i, v i * (z i - y i))) :
    ∃ a b : ℝ, ∀ i : Fin k,
      Work.WilE3.Taylor.grad (fun z => ∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) u i
        + (∑ l, (Work.WilE3.Taylor.grad Φ u l) ^ 2) * v i
        = a * Work.WilE3.Taylor.grad Φ u i + b * (u i - y i) := by
  classical
  -- Abbreviations: the sphere function `S`, the squared gradient norm `G`, the exponential weight
  -- `W`, the weighted objective `F`, its value `E` at `u`, and the family of constraints `f`.
  set S : (Fin k → ℝ) → ℝ := fun z => ∑ i, (z i - y i) ^ 2 with hS
  set G : (Fin k → ℝ) → ℝ := fun z => ∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2 with hG
  set W : (Fin k → ℝ) → ℝ := fun z => Real.exp (∑ i, v i * (z i - y i)) with hW
  set F : (Fin k → ℝ) → ℝ := fun z => G z * W z with hF
  set E : ℝ := Real.exp (∑ i, v i * (u i - y i)) with hE
  set f : Fin 2 → (Fin k → ℝ) → ℝ := ![Φ, S] with hf
  have hf0 : f 0 = Φ := by rw [hf]; simp
  have hf1 : f 1 = S := by rw [hf]; simp
  -- The weighted objective is analytic, hence strictly differentiable at `u`.
  have hGan : AnalyticAt ℝ G u := by
    rw [hG]; exact Work.WilE3.Taylor.Grad.analyticAt_grad_sqSum hΦ u
  have hFstrict : HasStrictFDerivAt F (fderiv ℝ F u) u := by
    have h := aux_hasStrictFDerivAt_mul_exp_sum (g := G) (v := v) (y := y) (u := u)
      hGan.contDiffAt
    simpa only [hF, hW] using h
  -- Strict differentiability of the two constraints.
  have hSstrict : HasStrictFDerivAt S (fderiv ℝ S u) u := by
    rw [hS]; exact Work.WilE3.Taylor.Grad.hasStrictFDerivAt_sphereSq y u
  have hf' : ∀ i : Fin 2, HasStrictFDerivAt (f i) (fderiv ℝ (f i) u) u := by
    intro i
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with h | h
    · rw [h, hf0]; exact (hΦ u).contDiffAt.hasStrictFDerivAt (n := 1) (by norm_num)
    · rw [h, hf1]; exact hSstrict
  -- `u` is a local minimum of `F` on the intersection of the two level sets: this is exactly
  -- the eventual hypothesis `hloc`.
  have hextr : IsLocalExtrOn F {z : Fin k → ℝ | ∀ i : Fin 2, f i z = f i u} u := by
    refine Or.inl ?_
    show ∀ᶠ z in nhdsWithin u {z : Fin k → ℝ | ∀ i : Fin 2, f i z = f i u}, F u ≤ F z
    filter_upwards [hloc.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hmem
    have h1 : Φ z = Φ u := by
      have h := hmem 0; rwa [hf0] at h
    have h2 : (∑ i, (z i - y i) ^ 2) = (∑ i, (u i - y i) ^ 2) := by
      have h := hmem 1; rw [hf1] at h; simpa only [hS] using h
    have h3 := hz h1 h2
    simpa only [hF, hG, hW, hE] using h3
  -- Lagrange multipliers for the two active constraints.
  obtain ⟨Λ, Λ₀, hΛne, hrel⟩ := hextr.exists_multipliers_of_hasStrictFDerivAt
    (f := f) (f' := fun i : Fin 2 => fderiv ℝ (f i) u) (φ := F) (φ' := fderiv ℝ F u)
    hf' hFstrict
  rw [Fin.sum_univ_two] at hrel
  -- The derivative of the weighted objective along the `l`-th coordinate vector.
  have hFderiv : ∀ l : Fin k, fderiv ℝ F u (Pi.single l 1)
      = (Work.WilE3.Taylor.grad G u l + G u * v l) * E := by
    intro l
    have h := aux_fderiv_mul_exp_sum_single (g := G) (v := v) (y := y) (u := u) (l := l)
      hGan.differentiableAt
    simpa only [hF, hW, Work.WilE3.Taylor.grad, ← hE] using h
  -- Evaluate the multiplier relation on each coordinate vector.
  have hpoint : ∀ l : Fin k,
      Λ 0 * Work.WilE3.Taylor.grad Φ u l + Λ 1 * (2 * (u l - y l))
        + Λ₀ * ((Work.WilE3.Taylor.grad G u l + G u * v l) * E) = 0 := by
    intro l
    have h := congrArg (fun (T : (Fin k → ℝ) →L[ℝ] ℝ) => T (Pi.single l 1)) hrel
    simp only [add_apply, smul_apply, zero_apply, smul_eq_mul] at h
    rw [hf0, hf1] at h
    have hSd : fderiv ℝ S u (Pi.single l 1) = 2 * (u l - y l) := by
      rw [hS]; exact Work.WilE3.Taylor.Grad.fderiv_sphereSq_single y u l
    rw [hSd, hFderiv l] at h
    simpa only [Work.WilE3.Taylor.grad] using h
  -- The multiplier of the objective cannot vanish: otherwise the two constraint gradients would be
  -- linearly dependent, contradicting the non-vanishing of the minor `hindep`.
  have hΛ₀ : Λ₀ ≠ 0 := by
    intro h0
    have hp0 : ∀ l : Fin k,
        Λ 0 * Work.WilE3.Taylor.grad Φ u l + (2 * Λ 1) * (u l - y l) = 0 := by
      intro l
      have h := hpoint l
      rw [h0, zero_mul, add_zero] at h
      linarith
    obtain ⟨hc, hd⟩ := aux_coeff_eq_zero_of_minor_ne_zero
      (g := fun l => Work.WilE3.Taylor.grad Φ u l) (w := fun l => u l - y l)
      (c := Λ 0) (d := 2 * Λ 1) hp0 hindep
    have hΛ1 : Λ 1 = 0 := by linarith
    have hΛ : Λ = 0 := by funext i; fin_cases i <;> simp [hc, hΛ1]
    exact hΛne (by rw [hΛ, h0]; rfl)
  have hEne : E ≠ 0 := by rw [hE]; exact Real.exp_ne_zero _
  have hprod : (Λ₀ * E) ≠ 0 := mul_ne_zero hΛ₀ hEne
  -- Solve the multiplier relation for `∇G u + G u • v`.
  refine ⟨-(Λ₀ * E)⁻¹ * Λ 0, -(Λ₀ * E)⁻¹ * (2 * Λ 1), fun i => ?_⟩
  have hGval : G u = ∑ l, (Work.WilE3.Taylor.grad Φ u l) ^ 2 := by rw [hG]
  rw [← hGval]
  have hfinal : Work.WilE3.Taylor.grad G u i + G u * v i
      = (-(Λ₀ * E)⁻¹ * Λ 0) * Work.WilE3.Taylor.grad Φ u i
        + (-(Λ₀ * E)⁻¹ * (2 * Λ 1)) * (u i - y i) := by
    have h1 : (Work.WilE3.Taylor.grad G u i + G u * v i) * (Λ₀ * E)
        = -(Λ 0 * Work.WilE3.Taylor.grad Φ u i + (2 * Λ 1) * (u i - y i)) := by
      have h := hpoint i
      linarith
    have h2 : Work.WilE3.Taylor.grad G u i + G u * v i
        = -(Λ₀ * E)⁻¹ * (Λ 0 * Work.WilE3.Taylor.grad Φ u i + (2 * Λ 1) * (u i - y i)) := by
      have h3 : (Work.WilE3.Taylor.grad G u i + G u * v i) * (Λ₀ * E)
          = (-(Λ₀ * E)⁻¹ * (Λ 0 * Work.WilE3.Taylor.grad Φ u i + (2 * Λ 1) * (u i - y i)))
              * (Λ₀ * E) := by
        rw [h1]
        field_simp
      exact mul_right_cancel₀ hprod h3
    rw [h2]
    ring
  exact hfinal

end Work.WilE3.Taylor.CaseII
