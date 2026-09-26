import Mathlib
import Submission.Work.Asymptotics.MiddleRange.exists_lambdaFun_lipschitz
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Residues.ResidueKernel
import Submission.Work.Residues.normalizedDeriv_jInvariantFun

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularForm
open scoped Topology Manifold

/-- The `j`-invariant is holomorphic on `ℍ`. -/
private lemma mdifferentiable_jInvariantFun :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Work.Kernels.jInvariantFun := by
  have hE4 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => Work.Kernels.E4Fun τ) :=
    ModularForm.holo' ModularForm.E₄
  have hΔ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => Work.Kernels.DeltaFun τ) :=
    CuspForm.holo' CuspForm.discriminant
  change MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
    (fun τ : ℍ => Work.Kernels.E4Fun τ ^ 3 / Work.Kernels.DeltaFun τ)
  exact (hE4.pow 3).div hΔ (fun z => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z)

/-- The lift `j ∘ ofComplex` is differentiable on the upper half plane. -/
private lemma differentiableOn_jInvariantFun_ofComplex :
    DifferentiableOn ℂ (Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex)
      {z : ℂ | 0 < z.im} :=
  UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_jInvariantFun

/-- The complex derivative of the lift `j ∘ ofComplex` at `ρ` is the paper's
`j' (ρ) = -2πi E₄²E₆/Δ (ρ)`. -/
private lemma deriv_jInvariantFun_ofComplex (ρ : ℍ) :
    deriv (Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex) (ρ : ℂ)
      = Work.Residues.jprime ρ := by
  have hD : Derivative.normalizedDerivOfComplex Work.Kernels.jInvariantFun ρ
      = -(Work.Kernels.E4Fun ρ ^ 2 * Work.Kernels.E6Fun ρ) / Work.Kernels.DeltaFun ρ :=
    congr_fun Work.Residues.normalizedDeriv_jInvariantFun ρ
  rw [Derivative.normalizedDerivOfComplex] at hD
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) *
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹
        * deriv (Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex) ↑ρ)
      = deriv (Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex) ↑ρ := by
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  rw [Work.Residues.jprime]
  rw [← h2, hD]
  ring

/-- **Two-point local linear lower bound for `j`.**  At a point `ρ₀` where `j' ≠ 0`, the
invariant `j` expands Euclidean distances on a small ball: there are `R, c > 0` with
`c ‖y - z‖ ≤ ‖j y - j z‖` for all `y, z` within `R` of `ρ₀`.  This is the analytic content
of the local bi-Lipschitzianity of `j`; `j` is analytic with nonzero derivative at `ρ₀`,
hence strictly differentiable, and `Work.Asymptotics.MiddleRange.exists_lipschitz_lower_bound_of_hasStrictDerivAt`
turns that into the lower bound. -/
private lemma exists_local_jDiff_lower_bound (ρ₀ : ℍ) (hne : Work.Residues.jprime ρ₀ ≠ 0) :
    ∃ R > 0, ∃ c > 0, ∀ y z : ℂ, ‖y - (ρ₀ : ℂ)‖ < R → ‖z - (ρ₀ : ℂ)‖ < R →
      c * ‖y - z‖ ≤ ‖(Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex) y
        - (Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex) z‖ := by
  have hAna : AnalyticAt ℂ (Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex) (ρ₀ : ℂ) :=
    differentiableOn_jInvariantFun_ofComplex.analyticAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds ρ₀.im_pos)
  have hStrict : HasStrictDerivAt (Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex)
      (Work.Residues.jprime ρ₀) (ρ₀ : ℂ) := by
    have h := hAna.hasStrictDerivAt
    rwa [deriv_jInvariantFun_ofComplex ρ₀] at h
  exact Work.Asymptotics.MiddleRange.exists_lipschitz_lower_bound_of_hasStrictDerivAt hStrict hne

/-- **A uniform linear lower bound for `j` near a compact set of non-degenerate points.**

If `K ⊆ ℍ` is compact and `j' ≠ 0` at every point of `K`, then there are `c, δ > 0` with
`c ‖z - ρ‖ ≤ ‖j z - j ρ‖` for every `ρ ∈ K` and every `z ∈ ℍ` with `‖z - ρ‖ ≤ δ`. -/
theorem tile_jDiff_linear_compact {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hj : ∀ ρ ∈ K, Work.Residues.jprime ρ ≠ 0) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ ρ ∈ K, ∀ z : UpperHalfPlane,
      ‖(z : ℂ) - (ρ : ℂ)‖ ≤ δ →
        c * ‖(z : ℂ) - (ρ : ℂ)‖ ≤
          ‖Work.Kernels.jInvariantFun z - Work.Kernels.jInvariantFun ρ‖ := by
  by_cases hKe : K = ∅
  · refine ⟨1, 1, one_pos, one_pos, fun ρ hρ => ?_⟩
    rw [hKe] at hρ
    exact absurd hρ (Set.notMem_empty ρ)
  · -- Each point of `K` carries a local ball and a local constant.
    have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKe
    have hlocal : ∀ i : K, ∃ R > 0, ∃ c > 0, ∀ y z : ℂ,
        ‖y - ((i : ℍ) : ℂ)‖ < R → ‖z - ((i : ℍ) : ℂ)‖ < R →
          c * ‖y - z‖ ≤ ‖(Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex) y
            - (Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex) z‖ :=
      fun i => exists_local_jDiff_lower_bound (i : ℍ) (hj (i : ℍ) i.2)
    choose R hRpos c hcpos hc using hlocal
    -- Cover the (compact) image of `K` in `ℂ` by the half-balls.
    have hcover : ((fun ρ : ℍ => (ρ : ℂ)) '' K) ⊆
        ⋃ i : K, Metric.ball (((i : ℍ) : ℂ)) (R i / 2) := by
      rintro w ⟨ρ, hρ, rfl⟩
      exact Set.mem_iUnion.mpr ⟨⟨ρ, hρ⟩, by
        rw [Metric.mem_ball, dist_self]; exact half_pos (hRpos ⟨ρ, hρ⟩)⟩
    obtain ⟨t, ht⟩ := (hK.image UpperHalfPlane.continuous_coe).elim_finite_subcover
      (fun i : K => Metric.ball (((i : ℍ) : ℂ)) (R i / 2))
      (fun _ => Metric.isOpen_ball) hcover
    have htne : t.Nonempty := by
      obtain ⟨ρ, hρ⟩ := hKne
      have hmem : (ρ : ℂ) ∈ ((fun ρ : ℍ => (ρ : ℂ)) '' K) := ⟨ρ, hρ, rfl⟩
      obtain ⟨i, hit, _⟩ := Set.mem_iUnion₂.mp (ht hmem)
      exact ⟨i, hit⟩
    -- Uniform constants: the minimum of the local constants and half the minimum radius.
    have hneR : (t.image R).Nonempty := htne.image R
    have hneC : (t.image c).Nonempty := htne.image c
    set D : ℝ := (t.image R).min' hneR with hD
    set Cf : ℝ := (t.image c).min' hneC with hCf
    have hDmem : D ∈ t.image R := by rw [hD]; exact Finset.min'_mem _ hneR
    obtain ⟨i₀, _, hRi₀⟩ := Finset.mem_image.mp hDmem
    have hDpos : 0 < D := by rw [← hRi₀]; exact hRpos i₀
    have hCmem : Cf ∈ t.image c := by rw [hCf]; exact Finset.min'_mem _ hneC
    obtain ⟨j₀, _, hCj₀⟩ := Finset.mem_image.mp hCmem
    have hCfpos : 0 < Cf := by rw [← hCj₀]; exact hcpos j₀
    refine ⟨Cf, D / 2, hCfpos, half_pos hDpos, fun ρ hρ z hz => ?_⟩
    -- Locate the ball of the cover containing `ρ`.
    have hmem : (ρ : ℂ) ∈ ((fun ρ : ℍ => (ρ : ℂ)) '' K) := ⟨ρ, hρ, rfl⟩
    obtain ⟨i, hit, hρU⟩ := Set.mem_iUnion₂.mp (ht hmem)
    have hρi : ‖(ρ : ℂ) - ((i : ℍ) : ℂ)‖ < R i / 2 := by
      have h := Metric.mem_ball.mp hρU
      rwa [dist_eq_norm] at h
    have hDi : D ≤ R i := by
      rw [hD]; exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, hit, rfl⟩)
    -- Both `ρ` and `z` lie in the ball of the local estimate at `i`.
    have hz_lt : ‖(z : ℂ) - ((i : ℍ) : ℂ)‖ < R i := by
      have h1 : ‖(z : ℂ) - ((i : ℍ) : ℂ)‖
          ≤ ‖(z : ℂ) - (ρ : ℂ)‖ + ‖(ρ : ℂ) - ((i : ℍ) : ℂ)‖ := by
        have := norm_add_le ((z : ℂ) - (ρ : ℂ)) ((ρ : ℂ) - ((i : ℍ) : ℂ))
        rwa [show ((z : ℂ) - (ρ : ℂ)) + ((ρ : ℂ) - ((i : ℍ) : ℂ))
              = (z : ℂ) - ((i : ℍ) : ℂ) by ring] at this
      linarith [h1, hρi, hz, hDi, hRpos i]
    have hρ_lt : ‖(ρ : ℂ) - ((i : ℍ) : ℂ)‖ < R i := by linarith [hρi, hRpos i]
    have happly := hc i (z : ℂ) (ρ : ℂ) hz_lt hρ_lt
    have hji : ‖(Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex) (z : ℂ)
        - (Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex) (ρ : ℂ)‖
        = ‖Work.Kernels.jInvariantFun z - Work.Kernels.jInvariantFun ρ‖ := by
      rw [UpperHalfPlane.comp_ofComplex, UpperHalfPlane.comp_ofComplex]
    have hCfle : Cf ≤ c i := by
      rw [hCf]; exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, hit, rfl⟩)
    calc Cf * ‖(z : ℂ) - (ρ : ℂ)‖ ≤ c i * ‖(z : ℂ) - (ρ : ℂ)‖ :=
          mul_le_mul_of_nonneg_right hCfle (norm_nonneg _)
      _ ≤ ‖Work.Kernels.jInvariantFun z - Work.Kernels.jInvariantFun ρ‖ := by
          rw [← hji]; exact happly

end Work.Asymptotics.Tile
