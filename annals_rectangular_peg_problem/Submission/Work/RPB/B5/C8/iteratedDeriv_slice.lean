import Mathlib

open scoped ContDiff Topology
open Filter

namespace Work.RPB.B5.C8

/-- **Smoothness of a slice of an iterated `σ`-derivative.**

If `Φ : (τ,σ) ↦ Ψ τ σ` is `C^{j+8}` on the product `s ×ˢ t`, where `0` is an interior point of `t`,
then for each `τ ∈ s` the slice `σ ↦ Ψ τ σ` is `C^{j+8}` at `0`, and the assignment
`τ ↦ iteratedDeriv j (fun σ => Ψ τ σ) 0` is `C^8` on `s`.

The value of the `j`-th `σ`-derivative at `0` is identified with the `j`-th iterated Fréchet
derivative of the joint map along the direction `(0,1)`, evaluated within the product `s ×ˢ t`
(this is the "fiber" identity `hfiber` below).  Smoothness in `τ` then follows from the Mathlib
lemma `ContDiffWithinAt.iteratedFDerivWithin_right`, which states that the `j`-th iterated
Fréchet derivative of a `C^{j+8}` function is `C^8` (in the point variable). -/
theorem iteratedDeriv_slice {s t : Set ℝ} (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (h0 : (0 : ℝ) ∈ interior t) (Ψ : ℝ → ℝ → ℝ) (j : ℕ)
    (hΨ : ContDiffOn ℝ (j + 8) (fun z : ℝ × ℝ => Ψ z.1 z.2) (s ×ˢ t)) :
    ContDiffOn ℝ 8 (fun τ : ℝ => iteratedDeriv j (fun σ : ℝ => Ψ τ σ) 0) s := by
  have h0t : (0 : ℝ) ∈ t := interior_subset h0
  have ht_nhds : t ∈ 𝓝 (0 : ℝ) :=
    mem_of_superset (isOpen_interior.mem_nhds h0) interior_subset
  -- Every slice is `C^{j+8}` at `0` (as a function on the whole line).
  have hslice : ∀ τ ∈ s, ContDiffAt ℝ (j + 8) (fun σ => Ψ τ σ) 0 := by
    intro τ hτ
    have hΦ : ContDiffWithinAt ℝ (j + 8) (fun z : ℝ × ℝ => Ψ z.1 z.2) (s ×ˢ t) (τ, 0) :=
      hΨ (τ, 0) ⟨hτ, h0t⟩
    have hsec : ContDiffWithinAt ℝ (j + 8) (fun σ : ℝ => (τ, σ)) t 0 :=
      (by fun_prop : ContDiff ℝ (j + 8) (fun σ : ℝ => (τ, σ))).contDiffWithinAt
    have hmap : Set.MapsTo (fun σ : ℝ => (τ, σ)) t (s ×ˢ t) := fun σ hσ => ⟨hτ, hσ⟩
    have hcomp := ContDiffWithinAt.comp (0 : ℝ) hΦ hsec hmap
    have hcomp' : ContDiffWithinAt ℝ (j + 8) (fun σ => Ψ τ σ) t 0 := by
      simpa only [Function.comp_def] using hcomp
    exact (contDiffWithinAt_iff_contDiffAt ht_nhds).mp hcomp'
  -- Fiber identity: the `j`-th `σ`-derivative within `t` is the iterated Fréchet derivative of
  -- the joint map along `(0,1)`, computed within the product `s ×ˢ t`.
  have hfiber : ∀ τ ∈ s, iteratedDerivWithin j (fun σ => Ψ τ σ) t 0
      = iteratedFDerivWithin ℝ j (fun z : ℝ × ℝ => Ψ z.1 z.2) (s ×ˢ t) (τ, 0)
          (fun _ => ((0 : ℝ), (1 : ℝ))) := by
    intro τ hτ
    have hFT := hΨ.ftaylorSeriesWithin (hs.prod ht)
    let h : ℝ →ᴬ[ℝ] ℝ × ℝ := ContinuousAffineMap.lineMap (τ, 0) (τ, 1)
    have hh : ∀ σ : ℝ, h σ = (τ, σ) := by
      intro σ
      rw [ContinuousAffineMap.coe_lineMap_eq]
      simp [AffineMap.lineMap_apply_module']
    have hL : h.contLinear 1 = ((0 : ℝ), (1 : ℝ)) := by
      have hh' := ContinuousAffineMap.contLinear_map_vsub h (1 : ℝ) 0
      simp only [vsub_eq_sub, sub_zero] at hh'
      rw [hh']
      simp only [hh]
      norm_num
    have hpre : h ⁻¹' (s ×ˢ t) = t := by
      ext σ
      rw [Set.mem_preimage, Set.mem_prod, hh]
      exact ⟨fun hh => hh.2, fun hσ => ⟨hτ, hσ⟩⟩
    have hcomp := hFT.comp_continuousAffineMap h
    rw [hpre] at hcomp
    have key := hcomp.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := j) (by norm_num) ht h0t
    have key2 := congrArg (fun (L : ℝ [×j]→L[ℝ] ℝ) => L (fun _ => (1 : ℝ))) key
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at key2
    rw [show (fun i : Fin j => h.contLinear 1) = (fun _ => ((0 : ℝ), (1 : ℝ))) from
        funext (fun i => hL)] at key2
    simp only [ftaylorSeriesWithin, hh] at key2
    have hΦh : ((fun z : ℝ × ℝ => Ψ z.1 z.2) ∘ ⇑h) = (fun σ => Ψ τ σ) := by
      funext σ; simp [hh]
    rw [hΦh] at key2
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin]
    exact key2.symm
  -- Replace the ordinary iterated derivative by the within-`t` one.
  have hderiv : ∀ τ ∈ s, iteratedDeriv j (fun σ => Ψ τ σ) 0
      = iteratedFDerivWithin ℝ j (fun z : ℝ × ℝ => Ψ z.1 z.2) (s ×ˢ t) (τ, 0)
          (fun _ => ((0 : ℝ), (1 : ℝ))) := by
    intro τ hτ
    rw [← iteratedDerivWithin_eq_iteratedDeriv ht ((hslice τ hτ).of_le (by norm_num)) h0t]
    exact hfiber τ hτ
  -- The candidate smooth function `G`.
  let G : ℝ → ℝ := fun τ => iteratedFDerivWithin ℝ j (fun z : ℝ × ℝ => Ψ z.1 z.2) (s ×ˢ t)
      (τ, 0) (fun _ => ((0 : ℝ), (1 : ℝ)))
  have hG : ContDiffOn ℝ 8 G s := by
    intro x hx
    have hx' : (x, 0) ∈ s ×ˢ t := ⟨hx, h0t⟩
    have hfd : ContDiffWithinAt ℝ 8 (iteratedFDerivWithin ℝ j (fun z : ℝ × ℝ => Ψ z.1 z.2)
        (s ×ˢ t)) (s ×ˢ t) (x, 0) :=
      ContDiffWithinAt.iteratedFDerivWithin_right (hΨ (x, 0) hx') (hs.prod ht)
        (by simp [add_comm]) hx'
    have h1 : ContDiffWithinAt ℝ 8
        (fun τ : ℝ => iteratedFDerivWithin ℝ j (fun z : ℝ × ℝ => Ψ z.1 z.2) (s ×ˢ t) (τ, 0))
        s x := by
      have hset : (ContinuousLinearMap.inl ℝ ℝ ℝ) ⁻¹' (s ×ˢ t) = s := by
        ext τ
        rw [Set.mem_preimage, Set.mem_prod, ContinuousLinearMap.inl_apply]
        exact ⟨fun h => h.1, fun h => ⟨h, h0t⟩⟩
      have hc := ContDiffWithinAt.comp_continuousLinearMap (ContinuousLinearMap.inl ℝ ℝ ℝ) hfd
      simpa only [Function.comp_def, ContinuousLinearMap.inl_apply, hset] using hc
    have h2 : ContDiffWithinAt ℝ 8 G s x := by
      have hc := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℝ × ℝ) ℝ
        (fun _ => ((0 : ℝ), (1 : ℝ)))).contDiff.comp_contDiffWithinAt h1
      simpa only [Function.comp_def, G, ContinuousMultilinearMap.apply_apply] using hc
    exact h2
  exact hG.congr (fun τ hτ => hderiv τ hτ)

end Work.RPB.B5.C8
