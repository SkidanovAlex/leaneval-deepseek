import Mathlib

namespace Work.Isotopy

open scoped Manifold ContDiff
open Topology Set Function

/-- Continuity of the partial derivative of a jointly `C¹` map in its second variable:
if `g : E × F → G` is `C¹`, then `p ↦ fderiv ℝ (fun z ↦ g (p.1, z)) p.2` is continuous. -/
lemma continuous_fderiv_curry {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : E × F → G} (hg : ContDiff ℝ 1 g) :
    Continuous fun p : E × F => fderiv ℝ (fun z : F => g (p.1, z)) p.2 := by
  set L : (E × F →L[ℝ] G) →L[ℝ] (F →L[ℝ] G) :=
    (ContinuousLinearMap.compL ℝ F (E × F) G).flip (ContinuousLinearMap.inr ℝ E F) with hL
  have key : (fun p : E × F => fderiv ℝ (fun z : F => g (p.1, z)) p.2)
      = fun p : E × F => L (fderiv ℝ g p) := by
    funext p
    change fderiv ℝ (g ∘ (fun z : F => (p.1, z))) p.2 = L (fderiv ℝ g p)
    rw [fderiv_comp (x := p.2) (f := fun z : F => (p.1, z)) (g := g)
      (hg.differentiable (by norm_num) _) (hasFDerivAt_prodMk_right p.1 p.2).differentiableAt]
    rw [(hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2).fderiv]
    rfl
  rw [key]
  exact (ContinuousLinearMap.continuous L).comp (hg.continuous_fderiv one_ne_zero)

/-- **Uniform smallness of `∂_z` of a "phase-corrected displacement".**
Fix a smooth family `Φ : ℝ → M → ℝ^N` of maps of a compact manifold into `ℝ^N`, globally smooth
maps `ρ_j : ℝ → ℝ^N → M`, and smooth cutoffs `ψ_j : ℝ × ℝ^N → ℝ` supported (in `z`) in a bounded
set.  Then for all phases `s, s'` that are sufficiently close the operator norm of the `z`-derivative
of the map `z ↦ ∑_j ψ_j(s,z) • (Φ s' (ρ_j s z) - Φ s (ρ_j s z))` is bounded by `1/2` everywhere. -/
theorem exists_estimate_small {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M]
    {ι : Type} [Fintype ι] {B : ι → Set (EuclideanSpace ℝ (Fin N))}
    {Φ : ℝ → M → EuclideanSpace ℝ (Fin N)}
    (hΦ : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 N) ∞ (Function.uncurry Φ))
    (ρ : ι → ℝ → EuclideanSpace ℝ (Fin N) → M)
    (hρ : ∀ j, ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓡 n) ∞ (Function.uncurry (ρ j)))
    (ψ : ι → ℝ → EuclideanSpace ℝ (Fin N) → ℝ)
    (hψ : ∀ j, ContDiff ℝ ∞ (Function.uncurry (ψ j)))
    (hBd : ∀ j, Bornology.IsBounded (B j))
    (hψsupp : ∀ j s z, ψ j s z ≠ 0 → z ∈ B j)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ η > 0, ∀ s ∈ Set.Icc a b, ∀ s' ∈ Set.Icc a b, |s' - s| ≤ η →
      ∀ y : EuclideanSpace ℝ (Fin N),
      ‖fderiv ℝ (fun z => ∑ j, ψ j s z • (Φ s' (ρ j s z) - Φ s (ρ j s z))) y‖ ≤ 1 / 2 := by
  -- The jointly smooth function whose `z`-derivative we control.
  set g : (ℝ × ℝ) × EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) :=
    fun q => ∑ j, ψ j q.1.1 q.2 • Φ q.1.2 (ρ j q.1.1 q.2) with hgdef
  have hg : ContDiff ℝ ∞ g := by
    rw [hgdef]
    refine ContDiff.sum (fun j _ => ?_)
    refine ContDiff.smul (𝕜' := ℝ) ?_ ?_
    · exact (hψ j).comp (show ContDiff ℝ ∞
        (fun q : (ℝ × ℝ) × EuclideanSpace ℝ (Fin N) => (q.1.1, q.2)) by fun_prop)
    · rw [← contMDiff_iff_contDiff]
      have h2 : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × EuclideanSpace ℝ (Fin N)) (𝓡 n) ∞
          (fun q : (ℝ × ℝ) × EuclideanSpace ℝ (Fin N) => ρ j q.1.1 q.2) := by
        have h1 : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × EuclideanSpace ℝ (Fin N)) 𝓘(ℝ,ℝ) ∞
            (fun q : (ℝ × ℝ) × EuclideanSpace ℝ (Fin N) => q.1.1) :=
          (show ContDiff ℝ ∞
            (fun q : (ℝ × ℝ) × EuclideanSpace ℝ (Fin N) => q.1.1) by fun_prop).contMDiff
        have h2b : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × EuclideanSpace ℝ (Fin N)) (𝓡 N) ∞
            (fun q : (ℝ × ℝ) × EuclideanSpace ℝ (Fin N) => q.2) :=
          (show ContDiff ℝ ∞
            (fun q : (ℝ × ℝ) × EuclideanSpace ℝ (Fin N) => q.2) by fun_prop).contMDiff
        intro q
        exact ContMDiffAt.comp₂ (M := (ℝ × ℝ) × EuclideanSpace ℝ (Fin N)) (M' := ℝ)
          (N' := EuclideanSpace ℝ (Fin N)) (N := M)
          (I := 𝓘(ℝ, (ℝ × ℝ) × EuclideanSpace ℝ (Fin N))) (I' := 𝓘(ℝ,ℝ))
          (J' := 𝓡 N) (J := 𝓡 n)
          (f := fun q : (ℝ × ℝ) × EuclideanSpace ℝ (Fin N) => q.1.1)
          (g := fun q : (ℝ × ℝ) × EuclideanSpace ℝ (Fin N) => q.2)
          ((hρ j) (q.1.1, q.2)) (h1 q) (h2b q)
      exact hΦ.comp (ContMDiff.prodMk
        ((show ContDiff ℝ ∞
          (fun q : (ℝ × ℝ) × EuclideanSpace ℝ (Fin N) => q.1.2) by fun_prop).contMDiff)
        h2)
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  -- A closed ball containing every `B j`.
  choose R hR using fun j => (hBd j).exists_norm_le
  set Rtot : ℝ := ∑ j, max (R j) 0 with hRtot
  have hRle : ∀ j, R j ≤ Rtot := by
    intro j
    have h2 : max (R j) 0 ≤ Rtot := by
      rw [hRtot]
      exact Finset.single_le_sum (fun i _ => le_max_right _ _) (Finset.mem_univ j)
    exact le_trans (le_max_left _ _) h2
  set K : Set (EuclideanSpace ℝ (Fin N)) := Metric.closedBall 0 Rtot with hKdef
  have hKcomp : IsCompact K := by
    rw [hKdef]; exact isCompact_closedBall 0 Rtot
  have hKclosed : IsClosed K := by
    rw [hKdef]; exact Metric.isClosed_closedBall
  have hBsub : ∀ j, B j ⊆ K := by
    intro j z hz
    rw [hKdef, Metric.mem_closedBall, dist_zero_right]
    exact le_trans (hR j z hz) (hRle j)
  -- The `z`-derivative as a function of all variables, and its continuity.
  set Q : ((ℝ × ℝ) × EuclideanSpace ℝ (Fin N)) →
      (EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
    fun r => fderiv ℝ (fun z => g (r.1, z)) r.2 with hQdef
  have hQcont : Continuous Q := by
    rw [hQdef]
    exact continuous_fderiv_curry hg1
  -- Uniform continuity on the compact set of admissible parameters and positions.
  set S : Set ((ℝ × ℝ) × EuclideanSpace ℝ (Fin N)) :=
    (Set.Icc a b ×ˢ Set.Icc a b) ×ˢ K with hSdef
  have hScomp : IsCompact S := by
    rw [hSdef]
    exact (isCompact_Icc.prod isCompact_Icc).prod hKcomp
  have hunif : UniformContinuousOn Q S :=
    hScomp.uniformContinuousOn_of_continuous hQcont.continuousOn
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff_le.1 hunif (1 / 4) (by norm_num)
  refine ⟨δ, hδpos, ?_⟩
  intro s hs s' hs' hss' y
  by_cases hy : y ∈ K
  · have hu : ((s, s'), y) ∈ S := by rw [hSdef]; exact ⟨⟨hs, hs'⟩, hy⟩
    have hv : ((s, s), y) ∈ S := by rw [hSdef]; exact ⟨⟨hs, hs⟩, hy⟩
    have hdist : dist ((s, s'), y) ((s, s), y) = |s' - s| := by
      rw [Prod.dist_eq, Prod.dist_eq, dist_self, Real.dist_eq, dist_self]
      simp
    have hb := hδ _ hu _ hv (by rw [hdist]; exact hss')
    rw [dist_eq_norm] at hb
    have hid : fderiv ℝ (fun z => ∑ j, ψ j s z • (Φ s' (ρ j s z) - Φ s (ρ j s z))) y
        = Q ((s, s'), y) - Q ((s, s), y) := by
      have hfun : (fun z => ∑ j, ψ j s z • (Φ s' (ρ j s z) - Φ s (ρ j s z)))
          = fun z => (∑ j, ψ j s z • Φ s' (ρ j s z))
              - (∑ j, ψ j s z • Φ s (ρ j s z)) := by
        funext z
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => by rw [smul_sub])
      have hd1 : DifferentiableAt ℝ (fun z => ∑ j, ψ j s z • Φ s' (ρ j s z)) y :=
        (hg1.differentiable (by norm_num) ((s, s'), y)).comp y
          (hasFDerivAt_prodMk_right (s, s') y).differentiableAt
      have hd2 : DifferentiableAt ℝ (fun z => ∑ j, ψ j s z • Φ s (ρ j s z)) y :=
        (hg1.differentiable (by norm_num) ((s, s), y)).comp y
          (hasFDerivAt_prodMk_right (s, s) y).differentiableAt
      rw [hfun]
      change fderiv ℝ ((fun z => ∑ j, ψ j s z • Φ s' (ρ j s z))
          - (fun z => ∑ j, ψ j s z • Φ s (ρ j s z))) y = Q ((s, s'), y) - Q ((s, s), y)
      rw [fderiv_sub hd1 hd2, hQdef]
    rw [hid]
    linarith
  · have hzero : (fun z => ∑ j, ψ j s z • (Φ s' (ρ j s z) - Φ s (ρ j s z))) =ᶠ[𝓝 y] 0 := by
      filter_upwards [hKclosed.isOpen_compl.mem_nhds hy] with z hz
      refine Finset.sum_eq_zero (fun j _ => ?_)
      have hzj : ψ j s z = 0 := by
        by_contra h
        exact hz (hBsub j (hψsupp j s z h))
      rw [hzj, zero_smul]
    have hf0 : fderiv ℝ (fun z => ∑ j, ψ j s z • (Φ s' (ρ j s z) - Φ s (ρ j s z))) y = 0 := by
      rw [hzero.fderiv_eq]
      simp
    rw [hf0, norm_zero]
    norm_num

end Work.Isotopy
