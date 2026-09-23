import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.LocalDiffeomorph

namespace Commons.Geometry.Manifold.LocalDiffeomorph

open scoped _root_.Manifold _root_.ContDiff
open Filter
open scoped Topology
open Set

/-- **Inverse function theorem, model space case, `C^∞` version with local smoothness.**
If `g : E → E'` is `C^∞` on a neighbourhood `u` of `a` and `fderiv 𝕜 g a` is invertible, then `g`
is a `C^∞` local diffeomorphism at `a`.  (Compare the existing `ω` version
`isLocalDiffeomorphAt_of_contDiffAt_of_isInvertible`, which uses analyticity at the point; here at
level `∞` one genuinely needs smoothness on a neighbourhood, since `ContDiffAt 𝕜 ∞ g a` only means
that `g` is `C^m` on some neighbourhood of `a` for each finite `m` separately.) -/
theorem isLocalDiffeomorphAt_infty_of_contDiffOn_of_isInvertible
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [CompleteSpace E']
    {g : E → E'} {a : E} {u : Set E} (hu : u ∈ 𝓝 a)
    (hg : ContDiffOn 𝕜 ((⊤ : ENat) : WithTop ENat) g u)
    (h : (fderiv 𝕜 g a).IsInvertible) :
    IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E') ((⊤ : ENat) : WithTop ENat) g a := by
  obtain ⟨B, hB⟩ := h
  -- An open neighbourhood `u₀` of `a` on which `g` is smooth.
  obtain ⟨u₀, hu₀_sub, hu₀_open, hu₀_mem⟩ := mem_nhds_iff.mp hu
  have hg_u₀ : ContDiffOn 𝕜 ((⊤ : ENat) : WithTop ENat) g u₀ := hg.mono hu₀_sub
  -- The local homeomorphism produced by the inverse function theorem at `a`.
  have hg1 : ContDiffAt 𝕜 (1 : ℕ∞ω) g a :=
    (hg_u₀.of_le (by simp)).contDiffAt (hu₀_open.mem_nhds hu₀_mem)
  have hf'a : HasFDerivAt g (B : E →L[𝕜] E') a := by
    rw [hB]
    exact (hg1.differentiableAt one_ne_zero).hasFDerivAt
  let Φ : OpenPartialHomeomorph E E' := hg1.toOpenPartialHomeomorph g hf'a one_ne_zero
  have hΦa : a ∈ Φ.source := hg1.mem_toOpenPartialHomeomorph_source hf'a one_ne_zero
  have hΦcoe : ⇑Φ = g := ContDiffAt.toOpenPartialHomeomorph_coe hg1 hf'a one_ne_zero
  -- An open neighbourhood of `a` on which `fderiv 𝕜 g` is invertible.
  have hcont : ContinuousAt (fderiv 𝕜 g) a := hg1.continuousAt_fderiv one_ne_zero
  have hmem_inv : {x | (fderiv 𝕜 g x).IsInvertible} ∈ 𝓝 a := by
    have hrange : Set.range ((↑) : (E ≃L[𝕜] E') → (E →L[𝕜] E')) ∈ 𝓝 (fderiv 𝕜 g a) :=
      hB ▸ ContinuousLinearEquiv.nhds B
    have hthis := hcont.preimage_mem_nhds hrange
    have hset : (fderiv 𝕜 g) ⁻¹' (Set.range ((↑) : (E ≃L[𝕜] E') → (E →L[𝕜] E')))
        = {x | (fderiv 𝕜 g x).IsInvertible} := by
      ext x
      simp [ContinuousLinearMap.IsInvertible, Set.mem_range]
    rwa [hset] at hthis
  obtain ⟨v, hv_sub, hv_open, hv_mem⟩ := mem_nhds_iff.mp hmem_inv
  -- The source of the local diffeomorphism: a small open neighbourhood of `a`, contained in
  -- `u₀`, in `Φ.source`, and where `fderiv 𝕜 g` is invertible.
  have hN : u₀ ∩ Φ.source ∩ v ∈ 𝓝 a :=
    inter_mem (inter_mem (hu₀_open.mem_nhds hu₀_mem) (Φ.open_source.mem_nhds hΦa))
      (hv_open.mem_nhds hv_mem)
  obtain ⟨s, hs_sub, hs_open, hs_mem⟩ := mem_nhds_iff.mp hN
  have hs_u₀ : s ⊆ u₀ := fun x hx => (hs_sub hx).1.1
  have hs_src : s ⊆ Φ.source := fun x hx => (hs_sub hx).1.2
  have hs_inv : ∀ x ∈ s, (fderiv 𝕜 g x).IsInvertible := fun x hx => hv_sub (hs_sub hx).2
  have ht_open : IsOpen (g '' s) := by
    rw [← hΦcoe]
    exact Φ.isOpen_image_of_subset_source hs_open hs_src
  -- Smoothness of the inverse of `Φ` on `g '' s`.  Note that `ContDiffOn 𝕜 ∞` at a point only
  -- gives a neighbourhood for each finite order separately, so we prove `ContDiffAt 𝕜 ∞` at each
  -- point by applying the finite-order inverse function theorem *at that point*.
  have ht_smooth : ContDiffOn 𝕜 ((⊤ : ENat) : WithTop ENat) (⇑Φ.symm) (g '' s) := by
    rw [IsOpen.contDiffOn_iff ht_open]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [contDiffAt_infty]
    intro m
    rcases Nat.eq_zero_or_pos m with hm | hm
    · -- order `0`: continuity of the inverse
      subst hm
      rw [Nat.cast_zero, contDiffAt_zero]
      refine ⟨Φ.target, Φ.open_target.mem_nhds ?_, Φ.continuousOn_invFun⟩
      rw [← hΦcoe]
      exact Φ.map_source (hs_src hx)
    · -- order `m > 0`: inverse function theorem at `x`
      have hne : ((m : ℕ∞ω)) ≠ 0 := by simp [hm.ne']
      have hgx : ContDiffAt 𝕜 (m : ℕ∞ω) g x :=
        ((contDiffOn_infty.mp hg_u₀) m).contDiffAt (hu₀_open.mem_nhds (hs_u₀ hx))
      obtain ⟨Bx, hBx⟩ := hs_inv x hx
      have hfx : HasFDerivAt g (Bx : E →L[𝕜] E') x := by
        rw [hBx]
        exact (hgx.differentiableAt hne).hasFDerivAt
      have hstr : HasStrictFDerivAt g (Bx : E →L[𝕜] E') x := hgx.hasStrictFDerivAt' hfx hne
      have huniq : ∀ᶠ z in 𝓝 x, (⇑Φ.symm) (g z) = z := by
        filter_upwards [Φ.open_source.mem_nhds (hs_src hx)] with z hz
        rw [← hΦcoe]
        exact Φ.left_inv hz
      have hkey := hstr.localInverse_unique huniq
      have hψ : ContDiffAt 𝕜 (m : ℕ∞ω)
          (HasStrictFDerivAt.localInverse g Bx x hstr) (g x) :=
        hgx.to_localInverse hfx hne
      exact hψ.congr_of_eventuallyEq hkey
  refine ⟨{ toPartialEquiv :=
              { toFun := g
                invFun := ⇑Φ.symm
                source := s
                target := g '' s
                map_source' := fun x hx => ⟨x, hx, rfl⟩
                map_target' := fun y hy => by
                  obtain ⟨x, hx, rfl⟩ := hy
                  have h1 : (⇑Φ.symm) (g x) = x := by
                    rw [← hΦcoe]
                    exact Φ.left_inv (hs_src hx)
                  rw [h1]
                  exact hx
                left_inv' := fun x hx => by
                  rw [← hΦcoe]
                  exact Φ.left_inv (hs_src hx)
                right_inv' := fun y hy => by
                  obtain ⟨x, hx, rfl⟩ := hy
                  have h1 : (⇑Φ.symm) (g x) = x := by
                    rw [← hΦcoe]
                    exact Φ.left_inv (hs_src hx)
                  rw [h1] },
            open_source := hs_open
            open_target := ht_open
            contMDiffOn_toFun := contMDiffOn_iff_contDiffOn.mpr (hg_u₀.mono hs_u₀)
            contMDiffOn_invFun := contMDiffOn_iff_contDiffOn.mpr ht_smooth },
    hs_mem, fun x _ => rfl⟩

end Commons.Geometry.Manifold.LocalDiffeomorph