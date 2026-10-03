import Mathlib
import Submission.Work.BasinSC.CoverDisc.exists_homeomorph_pow_of_isCoveringMap

/-!
# Preconnectedness of the preimage of a punctured disc under a covering of `𝔻*`

Let `q : Z → 𝔻*` be a covering map with `Z` path connected, and let `z₀` be a point of `Z` lying
over `u t₀`, where `u : U → 𝔻*` (`U = {Re > 0}`, `u t = exp (-t)`) is the universal covering of the
punctured disc.  Writing `baseLift : U → Z` for the lift of `u` through `q` with `baseLift t₀ = z₀`
(`Work.BasinSC.CoverDisc.baseLift`), we have

* `q ∘ baseLift = u` (`Work.BasinSC.CoverDisc.baseLift_mem`), and
* `baseLift` is surjective (`Work.BasinSC.CoverDisc.baseLift_surjective`, which uses only the path
  connectedness of `Z`).

Hence for any `S ⊆ 𝔻*`,
`q ⁻¹' S = baseLift '' (u ⁻¹' S)`, and the preimage of `S` is preconnected as soon as `u ⁻¹' S` is.
For `S = {w : 𝔻* | ‖w‖ < r}` with `0 < r` we have

`u ⁻¹' S = {t : U | -log r < t.re}`,

a half plane inside the convex set `U`, hence convex, hence preconnected.
-/

open Set Metric Filter Topology

namespace Work.Horn.HB

theorem preconnected_preimage_puncturedDisc_of_gamma_eq_bot {Z : Type*} [TopologicalSpace Z]
    [PathConnectedSpace Z] {q : Z → ↥Work.BasinSC.puncturedDisc} (hcov : IsCoveringMap q)
    {t₀ : ↥Work.BasinSC.CoverDisc.U} {z₀ : Z} (hz : q z₀ = Work.BasinSC.CoverDisc.u t₀)
    (hΓ : Work.BasinSC.CoverDisc.Gamma hcov t₀ z₀ hz = ⊥) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    IsPreconnected (q ⁻¹' {w : ↥Work.BasinSC.puncturedDisc | ‖(w : ℂ)‖ < r}) := by
  have hmem : ∀ t : ↥Work.BasinSC.CoverDisc.U,
      q ((Work.BasinSC.CoverDisc.baseLift hcov t₀ z₀ hz) t) = Work.BasinSC.CoverDisc.u t :=
    Work.BasinSC.CoverDisc.baseLift_mem hcov t₀ z₀ hz
  have hsurj : Function.Surjective (Work.BasinSC.CoverDisc.baseLift hcov t₀ z₀ hz) :=
    Work.BasinSC.CoverDisc.baseLift_surjective hcov t₀ z₀ hz
  -- the preimage of `S` under `q` is the image of the preimage of `S` under `u`, via the lift
  have hpre : q ⁻¹' {w : ↥Work.BasinSC.puncturedDisc | ‖(w : ℂ)‖ < r} =
      (Work.BasinSC.CoverDisc.baseLift hcov t₀ z₀ hz) ''
        (Work.BasinSC.CoverDisc.u ⁻¹' {w : ↥Work.BasinSC.puncturedDisc | ‖(w : ℂ)‖ < r}) := by
    ext z; constructor
    · intro hzS
      obtain ⟨t, ht⟩ := hsurj z
      refine ⟨t, ?_, ht⟩
      show Work.BasinSC.CoverDisc.u t ∈ {w : ↥Work.BasinSC.puncturedDisc | ‖(w : ℂ)‖ < r}
      rw [← hmem t, ht]
      exact hzS
    · rintro ⟨t, ht, rfl⟩
      show q ((Work.BasinSC.CoverDisc.baseLift hcov t₀ z₀ hz) t) ∈
        {w : ↥Work.BasinSC.puncturedDisc | ‖(w : ℂ)‖ < r}
      rw [hmem t]
      exact ht
  rw [hpre]
  refine IsPreconnected.image ?_ _
    (Work.BasinSC.CoverDisc.baseLift hcov t₀ z₀ hz).continuous.continuousOn
  -- it remains to see that `u ⁻¹' S` is preconnected
  have hset : (Work.BasinSC.CoverDisc.u ⁻¹'
        {w : ↥Work.BasinSC.puncturedDisc | ‖(w : ℂ)‖ < r} :
        Set ↥Work.BasinSC.CoverDisc.U) = Subtype.val ⁻¹' {z : ℂ | -Real.log r < z.re} := by
    ext t
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [Work.BasinSC.CoverDisc.u_val, Complex.norm_exp, Complex.neg_re,
      ← Real.lt_log_iff_exp_lt hr0]
    constructor <;> intro h <;> linarith
  rw [hset]
  -- `{z : ℂ | -log r < z.re}` is a half plane, hence convex
  have hA : {z : ℂ | -Real.log r < z.re} =
      (Complex.reCLM : ℂ →ₗ[ℝ] ℝ) ⁻¹' Set.Ioi (-Real.log r) := by
    ext z; simp [Complex.reCLM]
  have hconv : Convex ℝ (Work.BasinSC.CoverDisc.U ∩ {z : ℂ | -Real.log r < z.re}) :=
    Work.BasinSC.CoverDisc.U_convex.inter (by
      rw [hA]; exact (convex_Ioi _).linear_preimage _)
  have hpreU : PreconnectedSpace
      ↥(Work.BasinSC.CoverDisc.U ∩ {z : ℂ | -Real.log r < z.re}) :=
    isPreconnected_iff_preconnectedSpace.mp hconv.isPreconnected
  -- the preimage of the half plane in `↥U` is the image of `U` intersected with it
  let f : ↥(Work.BasinSC.CoverDisc.U ∩ {z : ℂ | -Real.log r < z.re}) →
      ↥Work.BasinSC.CoverDisc.U := fun x => ⟨x.1, x.2.1⟩
  have hf : Continuous f := by fun_prop
  have himg : f '' Set.univ =
      (Subtype.val ⁻¹' {z : ℂ | -Real.log r < z.re} : Set ↥Work.BasinSC.CoverDisc.U) := by
    ext t; constructor
    · rintro ⟨x, -, rfl⟩; exact x.2.2
    · intro ht; exact ⟨⟨(t : ℂ), t.2, ht⟩, Set.mem_univ _, Subtype.ext rfl⟩
  rw [← himg]
  exact IsPreconnected.image
    (isPreconnected_univ (α := ↥(Work.BasinSC.CoverDisc.U ∩ {z : ℂ | -Real.log r < z.re})))
    f hf.continuousOn

end Work.Horn.HB
