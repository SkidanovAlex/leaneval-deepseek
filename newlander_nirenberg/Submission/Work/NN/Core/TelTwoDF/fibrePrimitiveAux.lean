import Mathlib
import Submission.Work.CR.Flat.Cauchy.dbarC_mul
import Submission.Work.NN.Core.TelTwoDF.intervalIntegral_analyticOn
import Submission.Work.NN.Core.TelTwoDF.dbarC_intervalIntegral

set_option maxHeartbeats 2000000

namespace Work.NN.Core.TelTwoDF

open Set Metric MeasureTheory Filter
open scoped Topology

/-!
# Local real analytic `∂̄`-primitives in a fibre variable, from a holomorphic complexification

Given a real analytic function `E` on an open set `Ω ⊆ ℂⁿ × ℂ`, together with a *complexification*
`Φ` which is holomorphic in the fibre variables `(w, τ)` and satisfies
`Φ ((z,w), conj (w - c₀)) = E (z,w)` near a point `q = (z₀, c₀)`, we construct a real analytic
function `A` near `q` with

  `E (z,w) = ∂̄_w (A (z, ·)) w`.

The construction is the `τ`-antiderivative of the complexification along the anti-diagonal:
with `τ(w) = conj (w - c₀)`, we take

  `A (z,w) = τ(w) · ∫₀¹ Φ ((z,w), t · τ(w)) dt`.

Then `∂̄_w (τ(w) ∫₀¹ Φ(…, t τ(w)) dt) = ∫₀¹ Φ(…, t τ(w)) dt + τ(w) ∫₀¹ t ∂_τΦ(…, tτ(w)) dt`,
and the second term is `Φ(…, τ(w)) - ∫₀¹ Φ(…, t τ(w)) dt` by the fundamental theorem of calculus,
so the two `∫`-terms cancel and the sum is `Φ ((z,w), τ(w)) = E (z,w)`.
-/

/-- Chain rule for `∂̄` along a holomorphic map composed with a real differentiable curve:
if `G` is complex differentiable at `(w₀, σ w₀)` and `σ` is real differentiable at `w₀`, then
`∂̄ (w ↦ G (w, σ w)) w₀ = (∂₂G)(w₀, σ w₀) · ∂̄σ w₀`.  The `w`-dependence in the *first* slot is
holomorphic, hence contributes nothing to `∂̄`. -/
theorem dbarC_comp_prod {G : ℂ × ℂ → ℂ} {σ : ℂ → ℂ} {w₀ : ℂ}
    (hG : DifferentiableAt ℂ G (w₀, σ w₀)) (hσ : DifferentiableAt ℝ σ w₀) :
    Work.CR.Flat.dbarC (fun w => G (w, σ w)) w₀
      = (fderiv ℂ G (w₀, σ w₀)) (0, 1) * Work.CR.Flat.dbarC σ w₀ := by
  set D : ℂ × ℂ →L[ℂ] ℂ := fderiv ℂ G (w₀, σ w₀) with hD
  set T : ℂ →L[ℝ] ℂ := fderiv ℝ σ w₀ with hT
  have hpair : HasFDerivAt (fun w : ℂ => (w, σ w))
      ((ContinuousLinearMap.id ℝ ℂ).prod T) w₀ :=
    (hasFDerivAt_id w₀).prodMk hσ.hasFDerivAt
  have hcomp : HasFDerivAt (fun w : ℂ => G (w, σ w))
      ((D.restrictScalars ℝ).comp ((ContinuousLinearMap.id ℝ ℂ).prod T)) w₀ :=
    (hG.hasFDerivAt.restrictScalars ℝ).comp w₀ hpair
  have hL : fderiv ℝ (fun w : ℂ => G (w, σ w)) w₀
      = (D.restrictScalars ℝ).comp ((ContinuousLinearMap.id ℝ ℂ).prod T) := hcomp.fderiv
  have hDab : ∀ a b : ℂ, D (a, b) = a * D (1, 0) + b * D (0, 1) := by
    intro a b
    have hsplit : (a, b) = a • ((1:ℂ), (0:ℂ)) + b • ((0:ℂ), (1:ℂ)) := by
      ext <;> simp
    rw [hsplit, map_add, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul]
    simp [smul_eq_mul]
  have hL1 : ((D.restrictScalars ℝ).comp ((ContinuousLinearMap.id ℝ ℂ).prod T)) (1:ℂ)
      = D (1, 0) + (T 1) * D (0, 1) := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply]
    change D (1, T 1) = D (1, 0) + (T 1) * D (0, 1)
    rw [hDab]; ring
  have hLI : ((D.restrictScalars ℝ).comp ((ContinuousLinearMap.id ℝ ℂ).prod T)) (Complex.I)
      = Complex.I * D (1, 0) + (T Complex.I) * D (0, 1) := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply]
    change D (Complex.I, T Complex.I) = Complex.I * D (1, 0) + (T Complex.I) * D (0, 1)
    rw [hDab]
  rw [Work.CR.Flat.dbarC, hL, hL1, hLI, Work.CR.Flat.dbarC, ← hT]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `∂̄` of the anti-holomorphic affine function `w ↦ conj (w - c)` is `1`. -/
lemma dbarC_star_sub (c z : ℂ) :
    Work.CR.Flat.dbarC (fun w : ℂ => star (w - c)) z = 1 := by
  have h : HasFDerivAt (fun w : ℂ => star (w - c))
      ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) z := by
    have h1 : HasFDerivAt (fun w : ℂ => w - c) (ContinuousLinearMap.id ℝ ℂ) z :=
      (hasFDerivAt_id z).sub_const c
    have h2 : HasFDerivAt (star : ℂ → ℂ)
        (((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)) (z - c) :=
      ContinuousLinearMap.hasFDerivAt ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) (x := z - c)
    exact h2.comp z h1
  rw [Work.CR.Flat.dbarC, h.fderiv]
  simp [Complex.conj_I]
  norm_num

/-- `∂̄` of `w ↦ t * conj (w - c)` is `t`. -/
lemma dbarC_const_mul_star_sub (c t z : ℂ) :
    Work.CR.Flat.dbarC (fun w : ℂ => t * star (w - c)) z = t := by
  have hT : HasFDerivAt (fun w : ℂ => star (w - c))
      ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) z := by
    have h1 : HasFDerivAt (fun w : ℂ => w - c) (ContinuousLinearMap.id ℝ ℂ) z :=
      (hasFDerivAt_id z).sub_const c
    have h2 : HasFDerivAt (star : ℂ → ℂ)
        (((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)) (z - c) :=
      ContinuousLinearMap.hasFDerivAt ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) (x := z - c)
    exact h2.comp z h1
  have h2 : HasFDerivAt (fun w : ℂ => t * star (w - c))
      (t • ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)) z := hT.const_mul t
  rw [Work.CR.Flat.dbarC, h2.fderiv]
  simp only [smul_apply, smul_eq_mul]
  simp [Complex.conj_I]
  have hI : Complex.I * (t * Complex.I) = t * (Complex.I * Complex.I) := by ring
  rw [hI, Complex.I_mul_I]; ring



/-! ## The fibre `∂̄`-primitive of a holomorphic complexification -/

/-- The chain-rule derivative of `w ↦ Φ ((z,w), t * conj (w - c))`: the `ℂ`-derivative in the
second slot, restricted to `ℝ`, precomposed with `w ↦ (w, t * conj (w - c))`. -/
noncomputable def fibreH {n : ℕ} (Φ : ((Fin n → ℂ) × ℂ) × ℂ → ℂ) (z : Fin n → ℂ) (c : ℂ)
    (w : ℂ) (t : ℝ) : ℂ →L[ℝ] ℂ :=
  (fderiv ℝ (fun p : ℂ × ℂ => Φ ((z, p.1), p.2)) (w, (t : ℂ) * star (w - c))).comp
    ((ContinuousLinearMap.id ℝ ℂ).prod
      ((t : ℂ) • ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)))

@[simp] lemma fibreH_def {n : ℕ} (Φ : ((Fin n → ℂ) × ℂ) × ℂ → ℂ) (z : Fin n → ℂ) (c : ℂ)
    (w : ℂ) (t : ℝ) :
    fibreH Φ z c w t
      = (fderiv ℝ (fun p : ℂ × ℂ => Φ ((z, p.1), p.2)) (w, (t : ℂ) * star (w - c))).comp
        ((ContinuousLinearMap.id ℝ ℂ).prod
          ((t : ℂ) • ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ))) := rfl

/-- The real differential of the integrand `w ↦ conj (w - c) * Φ ((z,w), t * conj (w - c))`. -/
noncomputable def fibreG' {n : ℕ} (Φ : ((Fin n → ℂ) × ℂ) × ℂ → ℂ) (z : Fin n → ℂ) (c : ℂ)
    (w : ℂ) (t : ℝ) : ℂ →L[ℝ] ℂ :=
  star (w - c) • fibreH Φ z c w t + Φ ((z, w), (t : ℂ) * star (w - c)) •
    ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)

@[simp] lemma fibreG'_def {n : ℕ} (Φ : ((Fin n → ℂ) × ℂ) × ℂ → ℂ) (z : Fin n → ℂ) (c : ℂ)
    (w : ℂ) (t : ℝ) :
    fibreG' Φ z c w t
      = star (w - c) • fibreH Φ z c w t + Φ ((z, w), (t : ℂ) * star (w - c)) •
        ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) := rfl

theorem dbarC_fibrePrimitive {n : ℕ} {Φ : ((Fin n → ℂ) × ℂ) × ℂ → ℂ} {c : ℂ}
    {z : Fin n → ℂ} {w₀ : ℂ} {ρ : ℝ}
    (hΦhol : AnalyticOn ℂ (fun p : ℂ × ℂ => Φ ((z, p.1), p.2))
      (Metric.ball w₀ ρ ×ˢ Metric.ball (0 : ℂ) ρ))
    (hτ : ‖star (w₀ - c)‖ < ρ) :
    Work.CR.Flat.dbarC (fun w : ℂ => star (w - c) *
      ∫ t in (0:ℝ)..1, Φ ((z, w), t * star (w - c))) w₀
      = Φ ((z, w₀), star (w₀ - c)) := by
  classical
  rw [norm_star] at hτ
  set ε : ℝ := (ρ - ‖w₀ - c‖) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; have := norm_nonneg (w₀ - c); linarith
  have hερ : ε < ρ := by rw [hεdef]; have := norm_nonneg (w₀ - c); linarith
  set ρ₁ : ℝ := ε + ‖w₀ - c‖ with hρ₁def
  have hρ₁ρ : ρ₁ < ρ := by rw [hρ₁def, hεdef]; linarith
  have hρ₁nn : 0 ≤ ρ₁ := by rw [hρ₁def]; positivity
  -- the interval inclusions
  have hIoc : ∀ t : ℝ, t ∈ Set.uIoc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 := by
    intro t ht
    rw [Set.uIoc, min_eq_left (by norm_num : (0:ℝ) ≤ 1),
      max_eq_right (by norm_num : (0:ℝ) ≤ 1)] at ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  have hIcc : ∀ t : ℝ, t ∈ Set.uIcc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 := by
    intro t ht
    rw [Set.uIcc, min_eq_left (by norm_num : (0:ℝ) ≤ 1),
      max_eq_right (by norm_num : (0:ℝ) ≤ 1)] at ht
    exact ht
  -- ### differentiability of the anti-holomorphic affine map
  have hτfd : ∀ w : ℂ, HasFDerivAt (fun w' : ℂ => star (w' - c))
      ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) w := by
    intro w
    have h1 : HasFDerivAt (fun w' : ℂ => w' - c) (ContinuousLinearMap.id ℝ ℂ) w :=
      (hasFDerivAt_id w).sub_const c
    exact (ContinuousLinearMap.hasFDerivAt ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)
      (x := w - c)).comp w h1
  -- ### membership of the evaluation points in the polydisc
  have hmem : ∀ w ∈ Metric.ball w₀ ε, ∀ t ∈ Set.Icc (0:ℝ) 1,
      (w, (t:ℂ) * star (w - c)) ∈ Metric.ball w₀ ρ ×ˢ Metric.ball (0:ℂ) ρ := by
    intro w hw t ht
    have hw' : ‖w - w₀‖ < ε := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]; linarith
    · rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      have ht1 : ‖(t:ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [ht.1], ht.2⟩
      have hle : ‖w - c‖ ≤ ‖w - w₀‖ + ‖w₀ - c‖ := by
        calc ‖w - c‖ = ‖(w - w₀) + (w₀ - c)‖ := by ring_nf
          _ ≤ ‖w - w₀‖ + ‖w₀ - c‖ := norm_add_le _ _
      calc ‖(t:ℂ) * star (w - c)‖ = ‖(t:ℂ)‖ * ‖star (w - c)‖ := norm_mul _ _
        _ = ‖(t:ℂ)‖ * ‖w - c‖ := by rw [norm_star]
        _ ≤ 1 * ‖w - c‖ := mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
        _ = ‖w - c‖ := one_mul _
        _ ≤ ‖w - w₀‖ + ‖w₀ - c‖ := hle
        _ < ρ := by rw [hεdef] at hw'; linarith
  -- ### the chain rule for `w ↦ Φ ((z,w), t * star (w - c))`
  have hH : ∀ w ∈ Metric.ball w₀ ε, ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasFDerivAt (fun w' : ℂ => Φ ((z, w'), (t:ℂ) * star (w' - c)))
        (fibreH Φ z c w t) w := by
    intro w hw t ht
    have hmem' := hmem w hw t ht
    have hd : DifferentiableAt ℂ (fun p : ℂ × ℂ => Φ ((z, p.1), p.2))
        (w, (t:ℂ) * star (w - c)) :=
      hΦhol.differentiableOn.differentiableAt
        ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds hmem')
    have hinner : HasFDerivAt (fun w' : ℂ => (w', (t:ℂ) * star (w' - c)))
        ((ContinuousLinearMap.id ℝ ℂ).prod
          ((t:ℂ) • ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ))) w :=
      (hasFDerivAt_id w).prodMk ((hτfd w).const_mul (t:ℂ))
    have hcomp := (hd.hasFDerivAt.restrictScalars ℝ).comp w hinner
    have hfd : fderiv ℝ (fun p : ℂ × ℂ => Φ ((z, p.1), p.2)) (w, (t:ℂ)*star (w - c))
        = (fderiv ℂ (fun p : ℂ × ℂ => Φ ((z, p.1), p.2)) (w, (t:ℂ)*star (w - c))).restrictScalars ℝ :=
      (hd.hasFDerivAt.restrictScalars ℝ).fderiv
    rw [fibreH_def, hfd]
    exact hcomp
  -- ### the derivative of the integrand
  have hdiff : ∀ w ∈ Metric.ball w₀ ε, ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasFDerivAt (fun w' : ℂ => star (w' - c) * Φ ((z, w'), (t:ℂ) * star (w' - c)))
        (fibreG' Φ z c w t) w := by
    intro w hw t ht
    rw [fibreG'_def]
    exact (hτfd w).mul (hH w hw t ht)
  -- ### continuity of the derivatives on the polydisc
  have hVopen : IsOpen (Metric.ball w₀ ρ ×ˢ Metric.ball (0:ℂ) ρ) :=
    Metric.isOpen_ball.prod Metric.isOpen_ball
  have hcd : ContDiffOn ℂ (1 : WithTop ℕ∞) (fun p : ℂ × ℂ => Φ ((z, p.1), p.2))
      (Metric.ball w₀ ρ ×ˢ Metric.ball (0:ℂ) ρ) := hΦhol.contDiffOn hVopen.uniqueDiffOn
  have hfdcont : ContinuousOn (fun p : ℂ × ℂ => fderiv ℝ (fun p : ℂ × ℂ => Φ ((z, p.1), p.2)) p)
      (Metric.ball w₀ ρ ×ˢ Metric.ball (0:ℂ) ρ) :=
    ((hcd.restrict_scalars (𝕜 := ℝ)).continuousOn_fderiv_of_isOpen hVopen le_rfl)
  have hfdcontC : ContinuousOn (fun p : ℂ × ℂ => fderiv ℂ (fun p : ℂ × ℂ => Φ ((z, p.1), p.2)) p)
      (Metric.ball w₀ ρ ×ˢ Metric.ball (0:ℂ) ρ) :=
    hcd.continuousOn_fderiv_of_isOpen hVopen le_rfl
  -- ### bounds on a compact set
  set K : Set (ℂ × ℂ) := Metric.closedBall w₀ ε ×ˢ Metric.closedBall (0:ℂ) ρ₁ with hKdef
  have hKc : IsCompact K := (isCompact_closedBall w₀ ε).prod (isCompact_closedBall (0:ℂ) ρ₁)
  have hKV : K ⊆ Metric.ball w₀ ρ ×ˢ Metric.ball (0:ℂ) ρ := by
    intro p hp
    rw [hKdef] at hp
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have h1 := Metric.mem_closedBall.mp hp.1
      rw [dist_eq_norm] at h1
      linarith
    · rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      have h1 := Metric.mem_closedBall.mp hp.2
      rw [dist_eq_norm, sub_zero] at h1
      linarith
  obtain ⟨C₁, hC₁⟩ := hKc.exists_bound_of_continuousOn (hfdcont.mono hKV)
  obtain ⟨C₂, hC₂⟩ := hKc.exists_bound_of_continuousOn (hΦhol.continuousOn.mono hKV)
  -- ### the point `(w, t * star (w-c))` lies in `K`
  have hmemK : ∀ w ∈ Metric.ball w₀ ε, ∀ t ∈ Set.Icc (0:ℝ) 1,
      (w, (t:ℂ) * star (w - c)) ∈ K := by
    intro w hw t ht
    have hw' : ‖w - w₀‖ < ε := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    rw [hKdef]
    refine ⟨by rw [Metric.mem_closedBall, dist_eq_norm]; linarith, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have ht1 : ‖(t:ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [ht.1], ht.2⟩
    have hle : ‖w - c‖ ≤ ‖w - w₀‖ + ‖w₀ - c‖ := by
      calc ‖w - c‖ = ‖(w - w₀) + (w₀ - c)‖ := by ring_nf
        _ ≤ ‖w - w₀‖ + ‖w₀ - c‖ := norm_add_le _ _
    calc ‖(t:ℂ) * star (w - c)‖ = ‖(t:ℂ)‖ * ‖star (w - c)‖ := norm_mul _ _
      _ = ‖(t:ℂ)‖ * ‖w - c‖ := by rw [norm_star]
      _ ≤ 1 * ‖w - c‖ := mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
      _ = ‖w - c‖ := one_mul _
      _ ≤ ‖w - w₀‖ + ‖w₀ - c‖ := hle
      _ ≤ ρ₁ := by rw [hρ₁def, hεdef]; linarith
  have h0K : (w₀, (0:ℂ)) ∈ K := by
    rw [hKdef]
    exact ⟨by rw [Metric.mem_closedBall, dist_self]; exact hεpos.le,
      by rw [Metric.mem_closedBall, dist_self]; exact hρ₁nn⟩
  have hC₁nn : 0 ≤ C₁ := le_trans (norm_nonneg _) (hC₁ _ h0K)
  have hC₂nn : 0 ≤ C₂ := le_trans (norm_nonneg _) (hC₂ _ h0K)
  -- ### the bound on `‖fibreG'‖`
  have hbound : ∀ t ∈ Set.uIoc (0:ℝ) 1, ∀ w ∈ Metric.ball w₀ ε,
      ‖fibreG' Φ z c w t‖ ≤ ρ₁ * C₁ + C₂ := by
    intro t ht w hw
    have ht' := hIoc t ht
    rw [fibreG'_def]
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖star (w - c) • fibreH Φ z c w t‖
        = ‖star (w - c)‖ * ‖fibreH Φ z c w t‖ := norm_smul _ _
    have h2 : ‖Φ ((z, w), (t:ℂ) * star (w - c)) •
        ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)‖
        = ‖Φ ((z, w), (t:ℂ) * star (w - c))‖ * 1 := by
      rw [norm_smul, Complex.conjCLE_norm, mul_one]
    rw [h1, h2]
    have htw : ‖star (w - c)‖ ≤ ρ₁ := by
      rw [norm_star]
      have hw' : ‖w - w₀‖ < ε := by simpa [Metric.mem_ball, dist_eq_norm] using hw
      have hle : ‖w - c‖ ≤ ‖w - w₀‖ + ‖w₀ - c‖ := by
        calc ‖w - c‖ = ‖(w - w₀) + (w₀ - c)‖ := by ring_nf
          _ ≤ ‖w - w₀‖ + ‖w₀ - c‖ := norm_add_le _ _
      rw [hρ₁def, hεdef]; linarith
    have hHn : ‖fibreH Φ z c w t‖ ≤ C₁ := by
      rw [fibreH_def]
      refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
      have hD := hC₁ (w, (t:ℂ)*star (w - c)) (hmemK w hw t ht')
      have hL : ‖(ContinuousLinearMap.id ℝ ℂ).prod
          ((t:ℂ) • ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ))‖ ≤ 1 := by
        refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
        rw [ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.smul_apply, Prod.norm_def]
        refine max_le (by rw [one_mul]) ?_
        rw [norm_smul, one_mul]
        have ht1 : ‖(t:ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
          exact ⟨by linarith [ht'.1], ht'.2⟩
        calc ‖(t:ℂ)‖ * ‖((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) v‖
            ≤ 1 * (1 * ‖v‖) := mul_le_mul ht1
              (le_trans (ContinuousLinearMap.le_opNorm _ v)
                (le_of_eq (by rw [Complex.conjCLE_norm]))) (norm_nonneg _) (by norm_num)
          _ = ‖v‖ := by ring
      calc ‖fderiv ℝ (fun p : ℂ × ℂ => Φ ((z, p.1), p.2)) (w, (t:ℂ) * star (w - c))‖ *
            ‖(ContinuousLinearMap.id ℝ ℂ).prod
              ((t:ℂ) • ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ))‖
          ≤ C₁ * 1 := mul_le_mul hD hL (norm_nonneg _) hC₁nn
        _ = C₁ := mul_one _
    have hΦn : ‖Φ ((z, w), (t:ℂ) * star (w - c))‖ ≤ C₂ :=
      hC₂ (w, (t:ℂ)*star (w - c)) (hmemK w hw t ht')
    calc ‖star (w - c)‖ * ‖fibreH Φ z c w t‖ +
          ‖Φ ((z, w), (t:ℂ) * star (w - c))‖ * 1
        ≤ ρ₁ * C₁ + C₂ * 1 := add_le_add (mul_le_mul htw hHn (norm_nonneg _) hρ₁nn)
          (mul_le_mul_of_nonneg_right hΦn zero_le_one)
      _ = ρ₁ * C₁ + C₂ := by ring
  -- ### continuity of `fibreG' w₀` in `t`
  have hfdcont₂ : ContinuousOn (fun t : ℝ => fibreG' Φ z c w₀ t) (Set.uIoc (0:ℝ) 1) := by
    have hcurve : ContinuousOn (fun t : ℝ => (w₀, (t:ℂ) * star (w₀ - c))) (Set.uIoc (0:ℝ) 1) :=
      continuousOn_const.prodMk (ContinuousOn.mul Complex.continuous_ofReal.continuousOn
        continuousOn_const)
    have hD : ContinuousOn (fun t : ℝ => fderiv ℝ (fun p : ℂ × ℂ => Φ ((z, p.1), p.2))
        (w₀, (t:ℂ) * star (w₀ - c))) (Set.uIoc (0:ℝ) 1) :=
      hfdcont.comp hcurve (fun t ht => hmem w₀ (Metric.mem_ball_self hεpos) t (hIoc t ht))
    have hL : ContinuousOn (fun t : ℝ => (ContinuousLinearMap.id ℝ ℂ).prod
        ((t:ℂ) • ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ))) (Set.uIoc (0:ℝ) 1) := by
      have hEq : (fun t : ℝ => (ContinuousLinearMap.id ℝ ℂ).prod
          ((t:ℂ) • ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)))
          = fun t : ℝ => (ContinuousLinearMap.inl ℝ ℂ ℂ) + (t:ℂ) •
              ((ContinuousLinearMap.inr ℝ ℂ ℂ).comp
                ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)) := by
        funext t
        apply ContinuousLinearMap.ext
        intro v
        simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply, Prod.smul_mk, Prod.mk_add_mk]
        simp
      rw [hEq]
      exact ContinuousOn.add continuousOn_const
        (ContinuousOn.smul Complex.continuous_ofReal.continuousOn continuousOn_const)
    have hHc : ContinuousOn (fun t : ℝ => fibreH Φ z c w₀ t) (Set.uIoc (0:ℝ) 1) := by
      rw [show (fun t : ℝ => fibreH Φ z c w₀ t)
          = (fun t : ℝ => (fderiv ℝ (fun p : ℂ × ℂ => Φ ((z, p.1), p.2))
              (w₀, (t:ℂ) * star (w₀ - c))).comp ((ContinuousLinearMap.id ℝ ℂ).prod
                ((t:ℂ) • ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)))) from
        funext (fun t => fibreH_def Φ z c w₀ t)]
      exact hD.clm_comp hL
    have hΦc : ContinuousOn (fun t : ℝ => Φ ((z, w₀), (t:ℂ) * star (w₀ - c))) (Set.uIoc (0:ℝ) 1) :=
      hΦhol.continuousOn.comp hcurve
        (fun t ht => hmem w₀ (Metric.mem_ball_self hεpos) t (hIoc t ht))
    rw [show (fun t : ℝ => fibreG' Φ z c w₀ t)
        = fun t : ℝ => star (w₀ - c) • fibreH Φ z c w₀ t + Φ ((z, w₀), (t:ℂ) * star (w₀ - c)) •
            ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) from
      funext (fun t => fibreG'_def Φ z c w₀ t)]
    exact (hHc.const_smul (star (w₀ - c))).add (hΦc.smul
      (continuousOn_const (c := ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ))))
  -- ### applying differentiation under the integral
  have hkey : Work.CR.Flat.dbarC (fun w : ℂ => ∫ t in (0:ℝ)..1,
        star (w - c) * Φ ((z, w), (t:ℂ) * star (w - c))) w₀
      = ∫ t in (0:ℝ)..1, Work.CR.Flat.dbarC (fun w : ℂ =>
          star (w - c) * Φ ((z, w), (t:ℂ) * star (w - c))) w₀ := by
    refine dbarC_intervalIntegral (F := fun w t => star (w - c) * Φ ((z, w), (t:ℂ) * star (w - c)))
      (F' := fibreG' Φ z c) (bound := fun _ => ρ₁ * C₁ + C₂)
      (s := Metric.ball w₀ ε) (Metric.ball_mem_nhds w₀ hεpos) (Metric.mem_ball_self hεpos) ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [Metric.ball_mem_nhds w₀ hεpos] with w hw
      have hcurve : ContinuousOn (fun t : ℝ => (w, (t:ℂ) * star (w - c))) (Set.uIoc (0:ℝ) 1) :=
        continuousOn_const.prodMk (ContinuousOn.mul Complex.continuous_ofReal.continuousOn
          continuousOn_const)
      have hc : ContinuousOn (fun t : ℝ => Φ ((z, w), (t:ℂ) * star (w - c))) (Set.uIoc (0:ℝ) 1) :=
        hΦhol.continuousOn.comp hcurve (fun t ht => hmem w hw t (hIoc t ht))
      exact (continuousOn_const.mul hc).aestronglyMeasurable measurableSet_uIoc
    · have hcurve : ContinuousOn (fun t : ℝ => (w₀, (t:ℂ) * star (w₀ - c))) (Set.uIcc (0:ℝ) 1) :=
        continuousOn_const.prodMk (ContinuousOn.mul Complex.continuous_ofReal.continuousOn
          continuousOn_const)
      have hc : ContinuousOn (fun t : ℝ => Φ ((z, w₀), (t:ℂ) * star (w₀ - c))) (Set.uIcc (0:ℝ) 1) :=
        hΦhol.continuousOn.comp hcurve
          (fun t ht => hmem w₀ (Metric.mem_ball_self hεpos) t (hIcc t ht))
      exact (continuousOn_const.mul hc).intervalIntegrable
    · exact hfdcont₂.aestronglyMeasurable measurableSet_uIoc
    · filter_upwards with t ht w hw
      exact hbound t ht w hw
    · exact intervalIntegrable_const
    · filter_upwards with t ht w hw
      exact hdiff w hw t (hIoc t ht)
  -- ### the pointwise evaluation of the integrand
  have hpt : ∀ t ∈ Set.uIoc (0:ℝ) 1,
      Work.CR.Flat.dbarC (fun w : ℂ => star (w - c) * Φ ((z, w), (t:ℂ) * star (w - c))) w₀
        = Φ ((z, w₀), (t:ℂ) * star (w₀ - c))
          + star (w₀ - c) * ((t:ℂ) * ((fderiv ℂ (fun p : ℂ × ℂ => Φ ((z, p.1), p.2))
              (w₀, (t:ℂ) * star (w₀ - c))) (0, 1))) := by
    intro t ht
    have ht' := hIoc t ht
    have hgd : DifferentiableAt ℝ (fun w : ℂ => Φ ((z, w), (t:ℂ) * star (w - c))) w₀ :=
      (hH w₀ (Metric.mem_ball_self hεpos) t ht').differentiableAt
    have hσd : DifferentiableAt ℝ (fun w : ℂ => (t:ℂ) * star (w - c)) w₀ :=
      ((hτfd w₀).differentiableAt).const_mul (t:ℂ)
    have hΦd : DifferentiableAt ℂ (fun p : ℂ × ℂ => Φ ((z, p.1), p.2))
        (w₀, (t:ℂ) * star (w₀ - c)) :=
      hΦhol.differentiableOn.differentiableAt
        ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds
          (hmem w₀ (Metric.mem_ball_self hεpos) t ht'))
    rw [Work.CR.Flat.Cauchy.dbarC_mul (fun w : ℂ => star (w - c))
      (fun w : ℂ => Φ ((z, w), (t:ℂ) * star (w - c))) w₀
      ((hτfd w₀).differentiableAt) hgd, dbarC_star_sub]
    rw [dbarC_comp_prod hΦd hσd, dbarC_const_mul_star_sub]
    ring
  -- ### the fundamental theorem of calculus
  have hAcongr : (fun w : ℂ => star (w - c) * ∫ t in (0:ℝ)..1, Φ ((z, w), t * star (w - c)))
      = (fun w : ℂ => ∫ t in (0:ℝ)..1, star (w - c) * Φ ((z, w), (t:ℂ) * star (w - c))) := by
    funext w
    rw [intervalIntegral.integral_const_mul]
  rw [hAcongr, hkey,
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun t => hpt t))]
  set τ₀ : ℂ := star (w₀ - c) with hτ₀def
  set gg : ℝ → ℂ := fun t => (fderiv ℂ (fun p : ℂ × ℂ => Φ ((z, p.1), p.2))
      (w₀, (t:ℂ) * τ₀)) (0, 1) with hggdef
  set hh : ℝ → ℂ := fun t => Φ ((z, w₀), (t:ℂ) * τ₀) with hhdef
  have hcurveIcc : ContinuousOn (fun t : ℝ => (w₀, (t:ℂ) * τ₀)) (Set.uIcc (0:ℝ) 1) :=
    continuousOn_const.prodMk (ContinuousOn.mul Complex.continuous_ofReal.continuousOn
      continuousOn_const)
  have hggcont : ContinuousOn gg (Set.uIcc (0:ℝ) 1) := by
    rw [hggdef]
    refine ContinuousOn.clm_apply ?_ continuousOn_const
    refine hfdcontC.comp hcurveIcc ?_
    intro t ht
    rw [hτ₀def]
    exact hmem w₀ (Metric.mem_ball_self hεpos) t (hIcc t ht)
  -- ### derivative of `hh`
  have hhderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt hh (τ₀ * gg t) t := by
    intro t ht
    have ht' := hIcc t ht
    have hΦd : DifferentiableAt ℂ (fun p : ℂ × ℂ => Φ ((z, p.1), p.2)) (w₀, (t:ℂ) * τ₀) := by
      rw [hτ₀def]
      exact hΦhol.differentiableOn.differentiableAt
        ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds
          (hmem w₀ (Metric.mem_ball_self hεpos) t ht'))
    have h2 : HasDerivAt (fun s : ℝ => (s:ℂ)) (1:ℂ) t :=
      (ContinuousLinearMap.hasFDerivAt (Complex.ofRealCLM) (x := t)).hasDerivAt
    have h2' : HasDerivAt (fun s : ℝ => (s:ℂ) * τ₀) (1 * τ₀) t := h2.mul_const τ₀
    have hinner := (hasFDerivAt_const (x := t) w₀).prodMk h2'.hasFDerivAt
    have hcomp := (hΦd.hasFDerivAt.restrictScalars ℝ).comp (x := t)
      (f := fun s : ℝ => (w₀, (s:ℂ) * τ₀)) hinner
    have hdval : (((fderiv ℂ (fun p : ℂ × ℂ => Φ ((z, p.1), p.2)) (w₀, (t:ℂ)*τ₀)).restrictScalars ℝ).comp
        ((0 : ℝ →L[ℝ] ℂ).prod ((ContinuousLinearMap.smulRight (1:ℝ→L[ℝ]ℝ) ((1:ℂ)*τ₀))))) (1:ℝ)
        = τ₀ * gg t := by
      rw [ContinuousLinearMap.comp_apply]
      change (fderiv ℂ (fun p : ℂ × ℂ => Φ ((z, p.1), p.2)) (w₀, (t:ℂ)*τ₀))
        (((0 : ℝ →L[ℝ] ℂ).prod
          ((ContinuousLinearMap.smulRight (1:ℝ→L[ℝ]ℝ) ((1:ℂ)*τ₀)))) 1) = τ₀ * gg t
      rw [ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply,
        ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul, one_mul]
      rw [hggdef]
      have hsplit : ((0:ℂ), τ₀) = τ₀ • ((0:ℂ),(1:ℂ)) := by ext <;> simp
      rw [hsplit, ContinuousLinearMap.map_smul, smul_eq_mul]
    rw [hhdef]
    exact hcomp.hasDerivAt.congr_deriv hdval
  -- ### derivative of `t ↦ (t:ℂ) * hh t`
  have hGderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => (s:ℂ) * hh s) (hh t + (t:ℂ) * (τ₀ * gg t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => (s:ℂ)) (1:ℂ) t :=
      (ContinuousLinearMap.hasFDerivAt (Complex.ofRealCLM) (x := t)).hasDerivAt
    have h2 := h1.mul (hhderiv t ht)
    convert h2 using 1
    ring
  have hint : IntervalIntegrable (fun t : ℝ => hh t + (t:ℂ) * (τ₀ * gg t)) volume (0:ℝ) 1 := by
    have hcont : ContinuousOn (fun t : ℝ => hh t + (t:ℂ) * (τ₀ * gg t)) (Set.uIcc (0:ℝ) 1) := by
      have h1 : ContinuousOn hh (Set.uIcc (0:ℝ) 1) := by
        rw [hhdef]
        refine hΦhol.continuousOn.comp hcurveIcc ?_
        intro t ht
        rw [hτ₀def]
        exact hmem w₀ (Metric.mem_ball_self hεpos) t (hIcc t ht)
      refine ContinuousOn.add h1 ?_
      refine ContinuousOn.mul Complex.continuous_ofReal.continuousOn ?_
      exact continuousOn_const.mul hggcont
    exact hcont.intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hGderiv hint
  have hpt2 : ∀ t : ℝ, Φ ((z, w₀), (t:ℂ) * star (w₀ - c))
        + star (w₀ - c) * ((t:ℂ) * ((fderiv ℂ (fun p : ℂ × ℂ => Φ ((z, p.1), p.2))
            (w₀, (t:ℂ) * star (w₀ - c))) (0, 1)))
      = hh t + (t:ℂ) * (τ₀ * gg t) := by
    intro t
    simp only [hhdef, hggdef, hτ₀def]
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hpt2 t), hftc]
  have h1 : hh 1 = Φ ((z, w₀), τ₀) := by
    rw [hhdef]; simp
  rw [h1]; simp

end Work.NN.Core.TelTwoDF
