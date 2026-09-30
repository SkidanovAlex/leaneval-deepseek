import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Submission.Work.RiemLib.Commons.Geometry.Manifold.LocalDiffeomorph.isLocalDiffeomorphAt_infty_of_contDiffOn_of_isInvertible

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Manifold ContDiff Topology
open Filter Set
open Commons.Geometry.Manifold.LocalDiffeomorph

namespace Commons.Analysis.Calculus

/-- If `u` and `v` are smooth curves in a finite-dimensional real normed space on an open set `V`
containing `t₀`, and `u' t₀ ≠ 0`, then `v` agrees, near `t₀`, with the composition of `u` with a
smooth function `F` defined on an open neighbourhood `W` of `u t₀`.

This is the open-set ("`ContDiffOn`") form of the local reparametrisation statement.  The proof
projects onto a linear functional `φ` that is non-degenerate on `u' t₀`, so that the scalar curve
`G = φ ∘ u` has nonzero derivative at `t₀`; the inverse function theorem at level `∞` (the commons
lemma `isLocalDiffeomorphAt_infty_of_contDiffOn_of_isInvertible`) then produces a genuinely smooth
local inverse `ψ` of `G` on an *open* neighbourhood of `G t₀`, and `F = v ∘ ψ ∘ φ` does the job. -/
theorem exists_contDiffOn_eqOn_of_deriv_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {u v : ℝ → E} {t₀ : ℝ} {V : Set ℝ} (hV : IsOpen V) (ht₀ : t₀ ∈ V)
    (hu : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) u V)
    (hv : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) v V)
    (hne : deriv u t₀ ≠ 0) :
    ∃ (F : E → E) (W : Set E), IsOpen W ∧ u t₀ ∈ W ∧
      ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) F W ∧
      (∀ᶠ t in nhds t₀, F (u t) = v t) := by
  have hn : (((⊤ : ENat) : WithTop ENat)) ≠ 0 := by simp
  -- A continuous linear functional equal to `1` on `deriv u t₀`.
  obtain ⟨g, -, hg2⟩ := exists_dual_vector ℝ (deriv u t₀) (by rwa [norm_ne_zero_iff])
  have hgw : g (deriv u t₀) = ‖deriv u t₀‖ := hg2
  let φ : E →L[ℝ] ℝ := (‖deriv u t₀‖)⁻¹ • g
  have hφ : φ (deriv u t₀) = 1 := by
    show (‖deriv u t₀‖)⁻¹ * (g (deriv u t₀)) = 1
    rw [hgw, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]
  have hφne : φ (deriv u t₀) ≠ 0 := by rw [hφ]; exact one_ne_zero
  -- The scalar curve `G = φ ∘ u`, smooth on `V` with nonzero derivative at `t₀`.
  let G : ℝ → ℝ := fun t => φ (u t)
  have hG_cd : ContDiffOn ℝ (((⊤ : ENat) : WithTop ENat)) G V := by
    have h := (φ.contDiff).comp_contDiffOn hu
    simpa [G, Function.comp_def] using h
  have hu_deriv : HasDerivAt u (deriv u t₀) t₀ :=
    ((hu.contDiffAt (hV.mem_nhds ht₀)).differentiableAt hn).hasDerivAt
  have hG_deriv : HasDerivAt (fun t => φ (u t)) (φ (deriv u t₀)) t₀ :=
    φ.hasFDerivAt.comp_hasDerivAt t₀ hu_deriv
  have hG_fderiv : HasFDerivAt G
      (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (φ (deriv u t₀)) hφne) :
        ℝ →L[ℝ] ℝ) t₀ :=
    hG_deriv.hasFDerivAt_equiv hφne
  have hG_inv : (fderiv ℝ G t₀).IsInvertible := by
    rw [hG_fderiv.fderiv]
    exact ContinuousLinearMap.isInvertible_equiv
  -- The inverse function theorem at level `∞`: `G` is a `C^∞` local diffeomorphism at `t₀`.
  have hG_ld : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (((⊤ : ENat) : WithTop ENat)) G t₀ :=
    isLocalDiffeomorphAt_infty_of_contDiffOn_of_isInvertible (hV.mem_nhds ht₀) hG_cd hG_inv
  -- A smooth local inverse `ψ` of `G` on an open neighbourhood of `G t₀`.
  let ψ : ℝ → ℝ := ⇑hG_ld.localInverse
  have hψ_smooth :
      ContDiffOn ℝ (((⊤ : ENat) : WithTop ENat)) ψ hG_ld.localInverse.source :=
    hG_ld.contmdiffOn_localInverse.contDiffOn
  have hψ_left : ∀ t ∈ hG_ld.localInverse.target, ψ (G t) = t :=
    fun t ht => hG_ld.localInverse_left_inv ht
  -- The set of `x : E` on which `φ x` lies in the source of `ψ`.
  let A : Set E := φ ⁻¹' hG_ld.localInverse.source
  have hA_open : IsOpen A := hG_ld.localInverse.open_source.preimage φ.continuous
  have hu₀A : u t₀ ∈ A := by
    simp only [A, Set.mem_preimage]
    simpa [G] using hG_ld.localInverse_mem_source
  -- The smooth function `h = ψ ∘ φ` on `A`, whose value at `u t₀` is `t₀`.
  let h : E → ℝ := fun x => ψ (φ x)
  have h_smooth_A : ContDiffOn ℝ (((⊤ : ENat) : WithTop ENat)) h A := by
    have hφ_A : ContDiffOn ℝ (((⊤ : ENat) : WithTop ENat)) (φ : E → ℝ) A :=
      φ.contDiff.contDiffOn.mono (subset_univ _)
    have hcomp := hψ_smooth.comp hφ_A (fun x hx => hx)
    simpa [h, Function.comp_def] using hcomp
  have hu₀_h : h (u t₀) = t₀ := by
    have := hψ_left t₀ hG_ld.localInverse_mem_target
    simpa [h, G] using this
  have hh_cont : ContinuousAt h (u t₀) :=
    h_smooth_A.continuousOn.continuousAt (hA_open.mem_nhds hu₀A)
  -- A neighbourhood of `u t₀` on which `h` takes values in `V`.
  have hVnhds : V ∈ 𝓝 (h (u t₀)) := by rw [hu₀_h]; exact hV.mem_nhds ht₀
  have hpre : h ⁻¹' V ∈ 𝓝 (u t₀) := hh_cont.preimage_mem_nhds hVnhds
  have hB_mem : A ∩ h ⁻¹' V ∈ 𝓝 (u t₀) :=
    inter_mem (hA_open.mem_nhds hu₀A) hpre
  obtain ⟨W, hWsub, hWopen, hu₀W⟩ := mem_nhds_iff.mp hB_mem
  -- The candidate function `F = v ∘ h`.
  let F : E → E := fun x => v (h x)
  refine ⟨F, W, hWopen, hu₀W, ?_, ?_⟩
  · -- `F` is smooth on `W`
    have hW_A : W ⊆ A := fun x hx => (hWsub hx).1
    have hW_V : ∀ x ∈ W, h x ∈ V := fun x hx => (hWsub hx).2
    have hcomp := hv.comp (h_smooth_A.mono hW_A) (fun x hx => hW_V x hx)
    simpa [F, Function.comp_def] using hcomp
  · -- `F (u t) = v t` for `t` near `t₀`
    filter_upwards [hG_ld.localInverse.open_target.mem_nhds hG_ld.localInverse_mem_target]
      with t ht
    have ht' : h (u t) = t := by
      have := hψ_left t ht
      simpa [h, G] using this
    show v (h (u t)) = v t
    rw [ht']

end Commons.Analysis.Calculus