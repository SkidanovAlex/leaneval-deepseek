import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.Taylor.Polar.Basic
import Submission.Work.WilE3.Taylor.Polar.Lagrange
import Submission.Work.WilE3.Taylor.Grad.lagrangeOfInteriorMin

/-!
  annals_wilkies_conjecture, AREA E3: the Lagrange condition at a **boundary** minimum of the squared
  gradient norm.

  The Łojasiewicz/polar argument (`Submission/Work/WilE3/Taylor/Polar/`) routes the minimisers of
  `Φ` on the shells `{dist (·, Z) = ρ}` into the polar set by a Lagrange multiplier argument.  The
  companion file `lagrangeOfInteriorMin` treats the case of a minimum of
  `G := ∑ l (∂ₗ Φ)²` on the *level set* `{z | Φ z = Φ u}`: there `∇G u ∥ ∇Φ u`.  This file
  supplies the case in which the minimum is additionally constrained to a *sphere* about a point
  `y`, i.e. `u` minimises `G` on

      `{z | Φ z = Φ u}`  ∩  `{z | ∑ i (z i - y i)² = ∑ i (u i - y i)²}`.

  This is the situation at a point of the boundary of the level set inside a ball (a "boundary
  minimum"): two constraints are active, and the conclusion is that `∇G u` lies in the two
  dimensional span of the two constraint gradients `∇Φ u` and `u - y`:

      `∃ a b, ∇G u = a • ∇Φ u + b • (u - y)`.

  The proof is a direct application of Mathlib's Lagrange multiplier theorem
  (`IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt`, the version for a finite family of
  scalar constraints): with the two constraint functions `f₀ = Φ` and
  `f₁ = (fun z => ∑ i, (z i - y i)²)` (both strictly differentiable at `u` because analytic,
  respectively polynomial), the corollary of the theorem gives multipliers `Λ 0`, `Λ 1`, `Λ₀`
  with

      `Λ 0 • dΦ + Λ 1 • df₁ + Λ₀ • dG = 0`.

  The multiplier `Λ₀` of the objective cannot vanish: if it did, then `Λ 0 • dΦ + Λ 1 • df₁ = 0`
  would be a non-trivial linear dependence between `dΦ` and `df₁`, i.e. between the vectors
  `∇Φ u` and `u - y` (the derivative of `f₁` on the `l`-th coordinate vector is `2 (u l - y l)`),
  contradicting the hypothesis `hindep` — which is exactly the non-vanishing of a `2 × 2` minor of
  the pair `(∇Φ u, u - y)`, i.e. the linear independence of the two constraint gradients.  Dividing
  the relation by `Λ₀` and evaluating on coordinate vectors yields the claim, with
  `a = -(Λ₀⁻¹ * Λ 0)` and `b = -(Λ₀⁻¹ * (2 * Λ 1))`.

  Everything hinges on two elementary derivative computations collected at the top of the file:
  the derivative of `z ↦ ∑ i, (z i - y i)²` at `u` on a coordinate vector `eₗ` is `2 * (u l - y l)`
  (`fderiv_sphereSq_single`), and that function is strictly differentiable
  (`hasStrictFDerivAt_sphereSq`).  Both are proved from the chain rule for `HasFDerivAt` applied to
  the coordinate projections.
-/

namespace Work.WilE3.Taylor.Grad

open Classical Topology Filter

-- The hypothesis `hgu` (`∇Φ u ≠ 0`) of `lagrangeOfBoundaryMin` is redundant in the presence of
-- `hindep`: a nonzero `2 × 2` minor of `(∇Φ u, u - y)` already forces `∇Φ u ≠ 0`.  It is kept in
-- the statement (which must not be changed) so the linter is silenced locally.
set_option linter.unusedVariables false

/-- The Fréchet derivative of the squared distance `z ↦ ∑ i, (z i - y i)²` at `u`, evaluated on the
`l`-th coordinate unit vector, is `2 * (u l - y l)`. -/
theorem fderiv_sphereSq_single {k : ℕ} (y u : Fin k → ℝ) (l : Fin k) :
    fderiv ℝ (fun z : Fin k → ℝ => ∑ i, (z i - y i) ^ 2) u (Pi.single l 1)
      = 2 * (u l - y l) := by
  have h0 := HasFDerivAt.sum (u := Finset.univ) (A := fun i z => (z i - y i) ^ 2)
    (A' := fun i => (2 * (u i - y i)) • (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ))
    (fun i _ => by
      have h1 : HasFDerivAt (fun z : Fin k → ℝ => z i - y i)
          (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ) u := by
        simpa using
          ((ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).hasFDerivAt.sub_const (y i))
      have h2 := h1.pow 2
      simpa using h2)
  have hfun : (∑ i : Fin k, fun z : Fin k → ℝ => (z i - y i) ^ 2)
      = fun z => ∑ i, (z i - y i) ^ 2 := by
    funext z; simp [Finset.sum_apply]
  rw [hfun] at h0
  rw [h0.fderiv]
  rw [sum_apply]
  simp only [smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ l) h

/-- The squared distance `z ↦ ∑ i, (z i - y i)²` is strictly differentiable everywhere: it is a
polynomial function, hence `C^1`. -/
theorem hasStrictFDerivAt_sphereSq {k : ℕ} (y u : Fin k → ℝ) :
    HasStrictFDerivAt (fun z : Fin k → ℝ => ∑ i, (z i - y i) ^ 2)
      (fderiv ℝ (fun z : Fin k → ℝ => ∑ i, (z i - y i) ^ 2) u) u := by
  have hcd : ContDiffAt ℝ 1 (fun z : Fin k → ℝ => ∑ i, (z i - y i) ^ 2) u := by fun_prop
  exact hcd.hasStrictFDerivAt (by norm_num)

/-- **The Lagrange condition at a boundary minimum of the squared gradient norm.**

Let `Φ` be everywhere real-analytic, let `∇Φ u` and `u - y` be linearly independent (the hypothesis
`hindep`, the non-vanishing of a `2 × 2` minor of the pair), and suppose that `u` minimises the
squared gradient norm `G := ∑ l, (∂ₗ Φ)²` on the intersection of the level set `{z | Φ z = Φ u}` of
`Φ` with the sphere `{z | ∑ i (z i - y i)² = ∑ i (u i - y i)²}` about `y`.  Then the gradient of `G`
at `u` is a linear combination of the two constraint gradients `∇Φ u` and `u - y`:

  `∃ a b, ∇G u i = a * ∇Φ u i + b * (u i - y i)`  for all `i`.

This is the Lagrange multiplier theorem with the two active constraints `Φ` and the sphere; the
independence of the two constraints is exactly what forces the multiplier of the *objective* to be
non-zero, allowing the relation to be solved for `∇G u`. -/
theorem lagrangeOfBoundaryMin {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {u y : Fin k → ℝ}
    (hΦ : ∀ z, AnalyticAt ℝ Φ z)
    (hgu : Work.WilE3.Taylor.grad Φ u ≠ 0)
    (hindep : ∃ i j : Fin k,
      Work.WilE3.Taylor.grad Φ u i * (u j - y j)
        - Work.WilE3.Taylor.grad Φ u j * (u i - y i) ≠ 0)
    (hcrit : ∀ z : Fin k → ℝ, Φ z = Φ u →
      (∑ i, (z i - y i) ^ 2) = (∑ i, (u i - y i) ^ 2) →
      (∑ l, (Work.WilE3.Taylor.grad Φ u l) ^ 2) ≤ (∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2)) :
    ∃ a b : ℝ, ∀ i : Fin k,
      Work.WilE3.Taylor.grad (fun z => ∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) u i
        = a * Work.WilE3.Taylor.grad Φ u i + b * (u i - y i) := by
  classical
  -- Abbreviations: the sphere function `S`, the objective `G`, and the family of constraints.
  set S : (Fin k → ℝ) → ℝ := fun z => ∑ i, (z i - y i) ^ 2 with hS
  set G : (Fin k → ℝ) → ℝ := fun z => ∑ l, (grad Φ z l) ^ 2 with hG
  set f : Fin 2 → (Fin k → ℝ) → ℝ := ![Φ, S] with hf
  have hf0 : f 0 = Φ := by rw [hf]; simp
  have hf1 : f 1 = S := by rw [hf]; simp
  -- Strict differentiability of the objective and of the two constraints.
  have hG_strict : HasStrictFDerivAt G (fderiv ℝ G u) u := by
    rw [hG]
    exact (analyticAt_grad_sqSum hΦ u).contDiffAt.hasStrictFDerivAt (n := 1) (by norm_num)
  have hS_strict : HasStrictFDerivAt S (fderiv ℝ S u) u := by
    rw [hS]
    exact hasStrictFDerivAt_sphereSq y u
  have hf' : ∀ i : Fin 2, HasStrictFDerivAt (f i) (fderiv ℝ (f i) u) u := by
    intro i
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with h | h
    · rw [h, hf0]
      exact (hΦ u).contDiffAt.hasStrictFDerivAt (n := 1) (by norm_num)
    · rw [h, hf1]
      exact hS_strict
  -- `u` minimises `G` on the intersection of the two level sets of `f`.
  have hextr : IsLocalExtrOn G {z : Fin k → ℝ | ∀ i : Fin 2, f i z = f i u} u := by
    refine Or.inl ?_
    show ∀ᶠ z in 𝓝[{z : Fin k → ℝ | ∀ i : Fin 2, f i z = f i u}] u, G u ≤ G z
    filter_upwards [self_mem_nhdsWithin] with z hz
    have h1 : Φ z = Φ u := by
      have h := hz 0
      rwa [hf0] at h
    have h2 : (∑ i, (z i - y i) ^ 2) = (∑ i, (u i - y i) ^ 2) := by
      have h := hz 1
      rw [hf1] at h
      simpa only [hS] using h
    simpa only [hG] using hcrit z h1 h2
  -- Lagrange multipliers for the two constraints.
  obtain ⟨Λ, Λ₀, hΛne, hrel⟩ := hextr.exists_multipliers_of_hasStrictFDerivAt
    (f := f) (f' := fun i : Fin 2 => fderiv ℝ (f i) u) (φ := G) (φ' := fderiv ℝ G u)
    hf' hG_strict
  rw [Fin.sum_univ_two] at hrel
  -- Evaluate the multiplier relation on each coordinate unit vector.
  have hpoint : ∀ l : Fin k,
      Λ 0 * grad Φ u l + Λ 1 * (2 * (u l - y l)) + Λ₀ * grad G u l = 0 := by
    intro l
    have h := congrArg (fun (L : (Fin k → ℝ) →L[ℝ] ℝ) => L (Pi.single l 1)) hrel
    simp only [add_apply, smul_apply, zero_apply, smul_eq_mul] at h
    rw [hf0, hf1] at h
    have hSd : fderiv ℝ S u (Pi.single l 1) = 2 * (u l - y l) := by
      rw [hS]; exact fderiv_sphereSq_single y u l
    rw [hSd] at h
    simpa only [grad] using h
  -- The objective multiplier `Λ₀` cannot vanish: otherwise the two constraint gradients would be
  -- linearly dependent, contradicting `hindep`.
  have hΛ₀ : Λ₀ ≠ 0 := by
    intro h0
    have hp0 : ∀ l : Fin k, Λ 0 * grad Φ u l + Λ 1 * (2 * (u l - y l)) = 0 := by
      intro l
      have h := hpoint l
      rw [h0, zero_mul, add_zero] at h
      exact h
    obtain ⟨i, j, hij⟩ := hindep
    have e1 := hp0 i
    have e2 := hp0 j
    have hprod : Λ 0 * (grad Φ u i * (u j - y j) - grad Φ u j * (u i - y i)) = 0 := by
      linear_combination ((u j - y j)) * e1 - ((u i - y i)) * e2
    have hΛ0z : Λ 0 = 0 := by
      rcases mul_eq_zero.mp hprod with h | h
      · exact h
      · exact absurd h hij
    have hΛ1z : Λ 1 = 0 := by
      -- some coordinate of `u - y` is non-zero, else all the minors would vanish
      have hex : ∃ l : Fin k, u l - y l ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hij (by simp [hcon])
      obtain ⟨l, hl⟩ := hex
      have h := hp0 l
      rw [hΛ0z, zero_mul, zero_add] at h
      have h2 : (2 * (u l - y l)) ≠ 0 := by
        intro hc
        exact hl (by linarith)
      rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' h2
    refine hΛne ?_
    have hfun : Λ = 0 := by
      funext i
      fin_cases i <;> simp_all
    rw [hfun, h0]; rfl
  -- Solve the multiplier relation for `∇G u`.
  refine ⟨-(Λ₀⁻¹ * Λ 0), -(Λ₀⁻¹ * (2 * Λ 1)), fun i => ?_⟩
  show grad G u i = (-(Λ₀⁻¹ * Λ 0)) * grad Φ u i + (-(Λ₀⁻¹ * (2 * Λ 1))) * (u i - y i)
  have h1 := hpoint i
  have key : Λ₀ * grad G u i = -(Λ 0 * grad Φ u i + Λ 1 * (2 * (u i - y i))) := by linarith
  have h2 : grad G u i = Λ₀⁻¹ * (Λ₀ * grad G u i) := by
    rw [← mul_assoc, inv_mul_cancel₀ hΛ₀, one_mul]
  rw [h2, key]
  ring

end Work.WilE3.Taylor.Grad
