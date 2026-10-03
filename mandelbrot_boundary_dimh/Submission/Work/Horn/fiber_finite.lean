import Mathlib

/-!
# Finiteness of the fibre of a "proper" holomorphic map

`Work.Horn.fiber_finite`: if `B` is open and preconnected, `f` is holomorphic on `B` and is not
locally constant at some `c ∈ B`, and `f` is *proper* in the sense that the preimage (intersected
with `B`) of every compact subset `L ⊆ B` is compact, then the fibre `B ∩ f ⁻¹' {w}` over any
`w ∈ B` is finite.

The proof is the classical one: the fibre `S = B ∩ f ⁻¹' {w}` is compact by hypothesis, hence
closes; if `S` were infinite it would have an accumulation point `p ∈ S` (compactness), the
vanishing of `f - w` at that accumulation point forces `f = w` in a neighbourhood of `p`
(isolated zeros / `AnalyticAt.frequently_zero_iff_eventually_zero`), and the identity theorem on
the preconnected set `B` then forces `f ≡ w` on all of `B`, contradicting the non-local-constancy
of `f` at `c ∈ B`.

Note that `hprop` is *not* redundant: `f z = sin z` on `B = ℂ` has infinite (unbounded) fibres
over `0`, and its preimages of compacta `{0}` fail to be compact.
-/

namespace Work.Horn

theorem fiber_finite {B : Set ℂ} {f : ℂ → ℂ} {c w : ℂ}
    (hB : IsOpen B) (hpre : IsPreconnected B) (hf : DifferentiableOn ℂ f B)
    (hcB : c ∈ B) (hnc : ¬ ∀ᶠ z in nhds c, f z = f c)
    (hprop : ∀ L ⊆ B, IsCompact L → IsCompact (B ∩ f ⁻¹' L)) (hw : w ∈ B) :
    (B ∩ f ⁻¹' {w}).Finite := by
  -- the fibre is compact, by properness applied to the compact singleton `{w} ⊆ B`
  have hScomp : IsCompact (B ∩ f ⁻¹' {w}) :=
    hprop {w} (by rwa [Set.singleton_subset_iff]) isCompact_singleton
  by_contra hinf
  have hinfI : (B ∩ f ⁻¹' {w}).Infinite := hinf
  -- an infinite subset of a compact set has an accumulation point inside it
  obtain ⟨p, hpS, hpacc⟩ := hinfI.exists_accPt_of_subset_isCompact hScomp (subset_refl _)
  have hpB : p ∈ B := hpS.1
  -- `p` accumulates at points of the fibre of `w`
  have hfreq : ∃ᶠ y in nhds p, (Ne y p) ∧ y ∈ B ∩ f ⁻¹' {w} :=
    accPt_iff_frequently.mp hpacc
  have hfreq' : ∃ᶠ y in nhds p, (Ne y p) ∧ f y = w := by
    refine hfreq.mono ?_
    rintro y ⟨hy1, hy2, hy3⟩
    exact ⟨hy1, by simpa using hy3⟩
  have hfw : ∃ᶠ z in nhdsWithin p {p}ᶜ, f z = w := by
    rw [frequently_nhdsWithin_iff]
    exact hfreq'.mono (fun y hy => ⟨hy.2, hy.1⟩)
  -- so `f - w` vanishes frequently at `p`, and a holomorphic function with non-isolated zeros
  -- vanishes identically near that point
  have hgan : AnalyticAt ℂ (fun z => f z - w) p :=
    (hf.analyticAt (hB.mem_nhds hpB)).sub analyticAt_const
  have h0 : (fun z => f z - w) =ᶠ[nhds p] 0 :=
    (AnalyticAt.frequently_zero_iff_eventually_zero hgan).mp
      (hfw.mono (fun z hz => by simp [hz]))
  have hfw' : f =ᶠ[nhds p] (fun _ => w) := by
    filter_upwards [h0] with z hz
    simpa [sub_eq_zero] using hz
  -- identity theorem on the preconnected set `B`: `f ≡ w` on `B`
  have hEqOn : Set.EqOn f (fun _ => w) B :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hf.analyticOnNhd hB) analyticOnNhd_const
      hpre hpB hfw'
  -- which makes `f` locally constant at `c ∈ B`, contradiction
  exact hnc (by
    filter_upwards [hB.mem_nhds hcB] with z hz
    rw [hEqOn hz, hEqOn hcB])

end Work.Horn
