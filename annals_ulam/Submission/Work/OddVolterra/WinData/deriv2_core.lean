import Mathlib
import Submission.Work.OddVolterra.WinData.abel_weight
import Submission.Work.OddVolterra.WinData.thetaM_close_box
import Submission.Work.OddExistence.Manifest.thetaM_continuous
import Submission.Work.OddExistence.Manifest.hasDerivAt_G2M_apply

/-!
# The slope-derivative of the manifest odd kernel `𝚯M`

This file computes `deriv (fun u => ThetaM n h u σ z) s` in terms of the second `u`-derivative of
the Abel average `G2M`, and bounds the difference of two such derivatives by the corresponding
difference of the second `u`-derivative of the manifest Abel kernel `KvecM`.

* `iteratedDeriv_two_eq` — `iteratedDeriv 2 f = deriv (deriv f)`.
* `iteratedDeriv_two_G2M` — the second `u`-derivative of a component of `G2M` is the
  Abel-weighted average of `(1-τ)² ∂²KvecM`, obtained by applying
  `hasDerivAt_abelAvg_scalar` and `hasDerivAt_abelAvg_scalar_weight` in succession.
* `deriv_ThetaM_apply` — the components of `deriv (fun u => ThetaM n h u σ z) s`.
* `thetaM_deriv_close_of_KvecM` — the target estimate, from the three clauses of the KvecM
  second-derivative estimate.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.WinData

noncomputable section

open Work.OddVolterra Work.OddVolterra.KernelExt

set_option maxHeartbeats 800000

/-- `iteratedDeriv 2 f` is `deriv (deriv f)`. -/
lemma iteratedDeriv_two_eq (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-- **The second `u`-derivative of a component of `G2M`.**  With the second `u`-derivative of the
corresponding component of `KvecM` bounded on a neighbourhood of `s`, the second derivative of
`(G2M n h · σ z) j` at `s` is the Abel-weighted average of `(1-τ)² ∂²KvecM`. -/
lemma hasDerivAt_deriv_G2M {n : ℕ} {h : ℝ → ℝ} {σ s ε C : ℝ} (z : St) (j : Fin 2)
    (hε : 0 < ε) (hC : 0 ≤ C)
    (hKmeas : Measurable (fun a : ℝ => (KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) j))
    (hbd : ∀ x ∈ Set.Ioo (s - ε) (s + ε), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      ‖(KvecM n h (x + τ * (σ - x)) σ (z 0) (z 1) (z 2) (z 3)) j‖ ≤ C)
    (hdiff : ∀ x ∈ Set.Ioo (s - ε) (s + ε), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      DifferentiableAt ℝ (fun a : ℝ => (KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) j)
        (x + τ * (σ - x)))
    (hbd1 : ∀ x ∈ Set.Ioo (s - ε) (s + ε), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      ‖deriv (fun a : ℝ => (KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) j) (x + τ * (σ - x))‖
        ≤ C)
    (hdiff1 : ∀ x ∈ Set.Ioo (s - ε) (s + ε), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      DifferentiableAt ℝ (deriv (fun a : ℝ => (KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) j))
        (x + τ * (σ - x)))
    (hbd2 : ∀ x ∈ Set.Ioo (s - ε) (s + ε), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖(1 - τ) * deriv (deriv (fun a : ℝ => (KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) j))
        (x + τ * (σ - x))‖ ≤ C) :
    HasDerivAt (fun u : ℝ => deriv (fun v : ℝ =>
        (G2M n h v σ (z 0) (z 1) (z 2) (z 3)) j) u)
      (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) ^ 2 * deriv (deriv (fun a : ℝ =>
          (KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) j)) (s + τ * (σ - s)))) s := by
  set K : ℝ → ℝ := fun a => (KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) j with hK
  -- the Abel average of `K` is the corresponding component of `G2M`
  have hG2M : (fun u : ℝ => (G2M n h u σ (z 0) (z 1) (z 2) (z 3)) j)
      = fun u : ℝ => ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ * K (u + τ * (σ - u)) := by
    funext u
    simp only [G2M, hK, div_eq_inv_mul]
  -- the unweighted Abel lemma, applied at every point of a neighbourhood of `s`
  have hAbel : ∀ u : ℝ, |u - s| < ε / 2 →
      HasDerivAt (fun u' : ℝ => ∫ τ in (0 : ℝ)..1,
          (Real.sqrt (τ * (1 - τ)))⁻¹ * K (u' + τ * (σ - u')))
        (∫ τ in (0 : ℝ)..1,
          (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * deriv K (u + τ * (σ - u)))) u := by
    intro u hu
    have hsub : ∀ x : ℝ, x ∈ Set.Ioo (u - ε / 2) (u + ε / 2) → x ∈ Set.Ioo (s - ε) (s + ε) := by
      intro x hx
      rw [Set.mem_Ioo] at hx ⊢
      have h1 : |x - u| < ε / 2 := by
        rw [abs_lt]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have h3 : |x - s| < ε := by
        calc |x - s| = |(x - u) + (u - s)| := by ring_nf
          _ ≤ |x - u| + |u - s| := abs_add_le _ _
          _ < ε := by linarith
      rw [abs_lt] at h3
      exact ⟨by linarith [h3.1], by linarith [h3.2]⟩
    refine Work.OddExistence.Manifest.hasDerivAt_abelAvg_scalar (C := C) hKmeas
      (by linarith : (0:ℝ) < ε / 2) ?_ ?_ ?_
    · intro x hx τ hτ
      exact hbd x (hsub x hx) τ hτ
    · intro x hx τ hτ
      exact hdiff x (hsub x hx) τ hτ
    · intro x hx τ hτ
      rcases eq_or_lt_of_le hτ.2 with h1 | h1
      · rw [← h1, sub_self, zero_mul, norm_zero]; exact hC
      · have h2 := hbd1 x (hsub x hx) τ ⟨hτ.1, h1⟩
        rw [norm_mul]
        calc ‖(1 - τ)‖ * ‖deriv K (x + τ * (σ - x))‖ ≤ 1 * C := by
              refine mul_le_mul ?_ h2 (norm_nonneg _) (by norm_num)
              rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hτ.2] : (0:ℝ) ≤ 1 - τ)]
              linarith [hτ.1]
          _ = C := by ring
  -- `deriv (G2M ·)` agrees with the Abel average of `K`
  have hev : deriv (fun u : ℝ => (G2M n h u σ (z 0) (z 1) (z 2) (z 3)) j)
      =ᶠ[𝓝 s] fun u : ℝ => ∫ τ in (0 : ℝ)..1,
          (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * deriv K (u + τ * (σ - u))) := by
    have hmem : ∀ᶠ u in 𝓝 s, |u - s| < ε / 2 := by
      have h := Metric.ball_mem_nhds s (by linarith : (0:ℝ) < ε / 2)
      filter_upwards [h] with u hu
      simpa [Real.dist_eq] using hu
    filter_upwards [hmem] with u hu
    rw [hG2M]
    exact (hAbel u hu).deriv
  -- the weighted Abel lemma, at `s`
  have hAt : HasDerivAt (fun u : ℝ => ∫ τ in (0 : ℝ)..1,
        (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * deriv K (u + τ * (σ - u))))
      (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) ^ 2 * deriv (deriv K) (s + τ * (σ - s)))) s := by
    refine hasDerivAt_abelAvg_scalar_weight (C := C) (measurable_deriv (𝕜 := ℝ) K) hε ?_ ?_ ?_
    · intro x hx τ hτ
      exact hbd1 x hx τ hτ
    · intro x hx τ hτ
      exact hdiff1 x hx τ hτ
    · intro x hx τ hτ
      exact hbd2 x hx τ hτ
  exact (Filter.EventuallyEq.hasDerivAt_iff hev).mpr hAt


/-- **The second `u`-derivative of a component of `G2M`, as an equality.** -/
lemma iteratedDeriv_two_G2M {n : ℕ} {h : ℝ → ℝ} {σ s ε C : ℝ} (z : St) (j : Fin 2)
    (hε : 0 < ε) (hC : 0 ≤ C)
    (hKmeas : Measurable (fun a : ℝ => (KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) j))
    (hbd : ∀ x ∈ Set.Ioo (s - ε) (s + ε), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      ‖(KvecM n h (x + τ * (σ - x)) σ (z 0) (z 1) (z 2) (z 3)) j‖ ≤ C)
    (hdiff : ∀ x ∈ Set.Ioo (s - ε) (s + ε), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      DifferentiableAt ℝ (fun a : ℝ => (KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) j)
        (x + τ * (σ - x)))
    (hbd1 : ∀ x ∈ Set.Ioo (s - ε) (s + ε), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      ‖deriv (fun a : ℝ => (KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) j) (x + τ * (σ - x))‖
        ≤ C)
    (hdiff1 : ∀ x ∈ Set.Ioo (s - ε) (s + ε), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      DifferentiableAt ℝ (deriv (fun a : ℝ => (KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) j))
        (x + τ * (σ - x)))
    (hbd2 : ∀ x ∈ Set.Ioo (s - ε) (s + ε), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖(1 - τ) * deriv (deriv (fun a : ℝ => (KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) j))
        (x + τ * (σ - x))‖ ≤ C) :
    iteratedDeriv 2 (fun u : ℝ => (G2M n h u σ (z 0) (z 1) (z 2) (z 3)) j) s =
      ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) ^ 2 * deriv (deriv (fun a : ℝ =>
          (KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) j)) (s + τ * (σ - s))) := by
  rw [iteratedDeriv_two_eq]
  exact (hasDerivAt_deriv_G2M z j hε hC hKmeas hbd hdiff hbd1 hdiff1 hbd2).deriv

/-- **The components of `deriv (fun u => ThetaM n h u σ z) s`.** -/
lemma deriv_ThetaM_apply (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (s : ℝ)
    (h0 : DifferentiableAt ℝ (fun u : ℝ =>
      deriv (fun v : ℝ => (G2M n h v σ (z 0) (z 1) (z 2) (z 3)) 0) u) s)
    (h1 : DifferentiableAt ℝ (fun u : ℝ =>
      deriv (fun v : ℝ => (G2M n h v σ (z 0) (z 1) (z 2) (z 3)) 1) u) s) :
    deriv (fun u : ℝ => ThetaM n h u σ z) s =
      ![0, 0,
        -deriv (fun u : ℝ => deriv (fun v : ℝ =>
          (G2M n h v σ (z 0) (z 1) (z 2) (z 3)) 0) u) s,
        -deriv (fun u : ℝ => deriv (fun v : ℝ =>
          (G2M n h v σ (z 0) (z 1) (z 2) (z 3)) 1) u) s] := by
  have hcases : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    intro i; fin_cases i <;> simp
  have hd : ∀ i : Fin 4, DifferentiableAt ℝ (fun u : ℝ => ThetaM n h u σ z i) s := by
    intro i
    rcases hcases i with h | h | h | h
    · subst h; exact differentiableAt_const _
    · subst h; exact differentiableAt_const _
    · subst h
      have hfun : (fun u : ℝ => ThetaM n h u σ z 2)
          = fun u : ℝ => -deriv (fun v : ℝ =>
              (G2M n h v σ (z 0) (z 1) (z 2) (z 3)) 0) u := by
        funext u; simp [ThetaM]
      rw [hfun]; exact h0.neg
    · subst h
      have hfun : (fun u : ℝ => ThetaM n h u σ z 3)
          = fun u : ℝ => -deriv (fun v : ℝ =>
              (G2M n h v σ (z 0) (z 1) (z 2) (z 3)) 1) u := by
        funext u; simp [ThetaM]
      rw [hfun]; exact h1.neg
  rw [deriv_pi (𝕜 := ℝ) (x := s) (φ := fun u : ℝ => ThetaM n h u σ z) hd]
  funext i
  rcases hcases i with h | h | h | h <;> subst h <;> simp [ThetaM, deriv_neg]


/-! ## The moving point of the Abel average stays in the box -/

/-- For `x` in a small neighbourhood of `s ∈ [1/4,19/20]` and `τ ∈ [0,1)`, the moving point
`x + τ(σ-x)` lies in `[3/16, 1]`. -/
lemma moving_mem {s σ x τ : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20))
    (hσ : σ ∈ Set.Icc (1 / 4 : ℝ) 1)
    (hx : x ∈ Set.Ioo (s - 1 / 100) (s + 1 / 100)) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    x + τ * (σ - x) ∈ Set.Icc (3 / 16 : ℝ) 1 := by
  rw [Set.mem_Ioo] at hx
  have hpoint : x + τ * (σ - x) = (1 - τ) * x + τ * σ := by ring
  rw [hpoint]
  have h1 : (0 : ℝ) ≤ 1 - τ := by linarith [hτ.2]
  have h2 : (0 : ℝ) ≤ τ := hτ.1
  have hx16 : (3 / 16 : ℝ) ≤ x := by linarith [hs.1, hx.1]
  have hx1 : x ≤ 1 := by linarith [hs.2, hx.2]
  have hσ16 : (3 / 16 : ℝ) ≤ σ := by linarith [hσ.1]
  constructor
  · have ha : (1 - τ) * (3 / 16) ≤ (1 - τ) * x := mul_le_mul_of_nonneg_left hx16 h1
    have hb : τ * (3 / 16) ≤ τ * σ := mul_le_mul_of_nonneg_left hσ16 h2
    nlinarith [ha, hb]
  · have ha : (1 - τ) * x ≤ (1 - τ) * 1 := mul_le_mul_of_nonneg_left hx1 h1
    have hb : τ * σ ≤ τ * 1 := mul_le_mul_of_nonneg_left hσ.2 h2
    nlinarith [ha, hb]

end

end Work.OddVolterra.WinData
