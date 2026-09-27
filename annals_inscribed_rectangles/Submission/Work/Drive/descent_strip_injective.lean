import Mathlib
import Submission.Work.Drive.chordStrictWideDescent
import Submission.Work.Drive.planeChartDataAux
import Submission.Work.Drive.stripData
import Submission.Work.Drive.curve_deriv_ne_zero
import Submission.Work.Drive.curve_eq_iff
import Submission.Work.Drive.local_injective_of_fderiv_injective
import Submission.Work.Drive.dstripG_fderiv_injective
import Submission.Work.Drive.dstripG_eq_of_dstripA_dstripDc_eq
import Submission.Work.Drive.dstripU_boundary_val
import Submission.Work.Drive.dstripU_boundary_deriv
import Submission.Work.Drive.dstripG_boundary_injective
import Submission.Work.Drive.exists_strip_injective_of_local

/-!
# The pair `(pcA, pcDc)` separates the points of a thin descent strip

This file proves `Work.Drive.descent_strip_injective`.

## The mathematical content

For the band data `(M, W)` of a smooth embedded plane curve `γ` (avoiding `0`), the pair

`(α, τ) ↦ (A(α,τ), Dc(α,τ))`,  `A = ‖M (e^{iα}, τ)‖² + τ ‖W (e^{iα}, τ)‖²`,

is injective modulo the `2π`-periodicity of the angle, on a strip `τ ∈ [-c', 0]` for some `c' > 0`.

Two ingredients:

* **the boundary slice `τ = 0`**: `M (e^{iα}, 0) = symmC (curve γ α)` is the curve point, so
  `α ↦ (M, A)(α, 0)` is injective modulo `2π` (`dstripG_boundary_injective`);
* **the normal direction at the boundary**: the differential of
  `G := (α,τ) ↦ (M (e^{iα}, τ), A(α,τ))` at a boundary point `(α,0)` is *injective*.  Indeed, its two
  columns `u₁ = ∂_αG`, `u₂ = ∂_τG` satisfy `u₂.2 - λ u₁.2 = ‖W (e^{iα},0)‖² ≠ 0` whenever
  `u₂.1 = λ u₁.1`, and `u₁ ≠ 0` because `M (e^{iα}, τ)` at `τ = 0` is the curve, whose derivative
  does not vanish (immersion); this is `dstripG_fderiv_injective` together with
  `dstripU_boundary_deriv`.  By the inverse function theorem `G` is then locally injective at every
  boundary point, and the strip-width statement follows by compactness of the circle
  (`exists_strip_injective_of_local`).

Finally `(A, Dc)` determines `G`: `D = M/√A` is recovered from `Dc` by
`‖D‖² = 2 - ‖Dc‖²` (the band inequality gives `‖D‖² < 2`), hence `M = √A · D`
(`dstripG_eq_of_dstripA_dstripDc_eq`).
-/

namespace Work.Drive

open scoped ContDiff

noncomputable section

theorem descent_strip_injective (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0)
    (M W : ℂ × ℝ → ℂ) (c : ℝ)
    (hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (hc : 0 < c)
    (hMval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 →
      M (x, τ) = Neutral.dataMid γ x (Real.sqrt τ))
    (hWval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 →
      W (x, τ) = Neutral.dchW γ (x, Real.sqrt τ))
    (hband : ∀ x : ℂ, ∀ τ : ℝ, 1 / 8 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 →
      4 * |τ| * ‖W (x, τ)‖ ^ 2 < ‖M (x, τ)‖ ^ 2)
    (hWne : ∀ x : ℂ, ∀ τ : ℝ, 1 / 8 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 → W (x, τ) ≠ 0)
    (hM0 : ∀ x : ℂ, 1 / 8 ≤ ‖x‖ → ‖x‖ ≤ 1 → M (x, 0) ≠ 0)
    (hW0 : ∀ x : ℂ, 1 / 8 ≤ ‖x‖ → ‖x‖ ≤ 1 → W (x, 0) ≠ 0) :
    ∃ c' : ℝ, 0 < c' ∧ c' ≤ c ∧
      (∀ α α' τ τ' : ℝ, τ ∈ Set.Icc (-c') 0 → τ' ∈ Set.Icc (-c') 0 →
        pcA M W (fun _ : ℂ => Complex.exp ((α : ℂ) * Complex.I)) (fun _ : ℂ => τ) 0
          = pcA M W (fun _ : ℂ => Complex.exp ((α' : ℂ) * Complex.I)) (fun _ : ℂ => τ') 0 →
        pcDc M W (fun _ : ℂ => Complex.exp ((α : ℂ) * Complex.I)) (fun _ : ℂ => τ) 0
          = pcDc M W (fun _ : ℂ => Complex.exp ((α' : ℂ) * Complex.I)) (fun _ : ℂ => τ') 0 →
        (α - α') / (2 * Real.pi) ∈ Set.range ((↑) : ℤ → ℝ) ∧ τ = τ') := by
  classical
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dstripG M W) := contDiff_dstripG hMsm hWsm
  -- The boundary slice `τ = 0` is injective modulo `2π`.
  have hbd : ∀ α α' : ℝ, dstripG M W (α, 0) = dstripG M W (α', 0) →
      ∃ k : ℤ, α - α' = 2 * Real.pi * k := dstripG_boundary_injective hγ hMval
  -- Local injectivity at every boundary point.
  have hloc : ∀ α : ℝ, ∃ ρ : ℝ, 0 < ρ ∧
      ∀ x ∈ Metric.ball (α, 0) ρ, ∀ y ∈ Metric.ball (α, 0) ρ,
        dstripG M W x = dstripG M W y → x = y := by
    intro α
    have hv : fderiv ℝ (fun p : ℝ × ℝ => M (dstripU p.1, p.2)) (α, 0) (1, 0) ≠ 0 :=
      dstripU_boundary_deriv hγ hMval hMsm α
    have hW : W (dstripU α, 0) ≠ 0 :=
      hW0 (dstripU α) (by simp only [norm_dstripU]; norm_num)
        (by simp only [norm_dstripU]; norm_num)
    have hinj : Function.Injective (fderiv ℝ (dstripG M W) (α, 0)) :=
      dstripG_fderiv_injective hMsm hWsm hv hW
    exact local_injective_of_fderiv_injective hsm.contDiffAt
      ((hsm.contDiffAt.differentiableAt (by simp)).hasFDerivAt) hinj
  -- A thin strip on which `dstripG` is injective modulo `2π`.
  obtain ⟨c₀, hc₀pos, hstrip⟩ :=
    exists_strip_injective_of_local (dstripG M W) hsm.continuous (dstripG_periodic M W) hbd hloc
  refine ⟨min c₀ c, lt_min hc₀pos hc, min_le_right c₀ c, ?_⟩
  intro α α' τ τ' hτ hτ' hA hDc
  -- the band hypotheses with the constant `c`
  have hτc : τ ∈ Set.Icc (-c) 0 :=
    ⟨le_trans (neg_le_neg (min_le_right c₀ c)) hτ.1, hτ.2⟩
  have hτc' : τ' ∈ Set.Icc (-c) 0 :=
    ⟨le_trans (neg_le_neg (min_le_right c₀ c)) hτ'.1, hτ'.2⟩
  -- the same equalities in the `dstrip` notation
  have hA' : dstripA M W α τ = dstripA M W α' τ' := by
    simpa only [pcA, dstripA, dstripU] using hA
  have hDc' : dstripDc M W α τ = dstripDc M W α' τ' := by
    simpa only [pcDc, pcD, pcA, dstripDc, dstripD, dstripA, dstripU] using hDc
  -- `(A, Dc)` determines `(M, A)`
  have hG : dstripG M W (α, τ) = dstripG M W (α', τ') :=
    dstripG_eq_of_dstripA_dstripDc_eq hband hWne hM0 hτc hτc' hA' hDc'
  -- the strip injectivity
  have hτ₀ : τ ∈ Set.Icc (-c₀) 0 :=
    ⟨le_trans (neg_le_neg (min_le_left c₀ c)) hτ.1, hτ.2⟩
  have hτ₀' : τ' ∈ Set.Icc (-c₀) 0 :=
    ⟨le_trans (neg_le_neg (min_le_left c₀ c)) hτ'.1, hτ'.2⟩
  rcases hstrip α α' τ τ' hτ₀ hτ₀' hG with ⟨⟨k, hk⟩, hτeq⟩
  exact ⟨⟨k, by rw [hk]; field_simp⟩, hτeq⟩

end

end Work.Drive
