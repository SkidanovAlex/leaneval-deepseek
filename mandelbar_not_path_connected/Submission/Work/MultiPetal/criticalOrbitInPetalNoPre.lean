/-
# `Work.MultiPetal.criticalOrbitInPetalNoPre`

The statement `Work.SeedLimit.MultiPetal.criticalOrbitInPetal` (see
`Submission/Work/SeedLimit/MultiPetal/criticalOrbitInPetal.lean`) *without* the superfluous
hypothesis `IsPreconnected Pa`.  The hypothesis is genuinely unused by that proof: the petal
argument runs on the **saturation** `B = ⋃_n F^{-n}(Pa)` of the petal, which is open and bounded
and on which no connectedness of `Pa` is ever invoked (the only place a `Preconnected`-type
hypothesis could enter, the uniqueness of lifts on the overlap of two strips, is handled there by
the explicit pointwise agreement `X τ = Ψ₀ τ`).  Accordingly the very same proof establishes the
statement with the hypothesis removed, which is what this file records.

Indeed, if `B` contained no critical point then every iterate `F^[n] : B → B` would be a covering
map; lifting the inverse Fatou coordinate `Φ = φa⁻¹` of the petal through those coverings produces
a bounded entire function which is injective on a tail strip, contradicting Liouville.  The
critical point so found lies in `B`, i.e. some iterate of it lies in `Pa`.
-/
import Mathlib
import Submission.Work.SeedLimit.MultiPetal.criticalOrbitInPetal

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Set Filter
open scoped Topology

namespace Work.MultiPetal

theorem criticalOrbitInPetalNoPre (F : ℂ → ℂ)
    (hF : ∃ P : Polynomial ℂ, 2 ≤ P.natDegree ∧ ∀ z : ℂ, F z = P.eval z)
    (h0 : F 0 = 0) (h1 : deriv F 0 = 1)
    (Pa : Set ℂ) (φa : ℂ → ℂ)
    (hisOpen : IsOpen Pa) (hne : Pa.Nonempty) (hmap : Set.MapsTo F Pa Pa)
    (htend : ∀ z ∈ Pa, Filter.Tendsto (fun n : ℕ => (F^[n]) z) Filter.atTop (nhds 0))
    (hdiff : DifferentiableOn ℂ φa Pa) (hinj : Set.InjOn φa Pa)
    (habel : ∀ z ∈ Pa, φa (F z) = φa z + 1)
    (hstrip : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, ∀ τ : ℂ, C < τ.re → |τ.im| ≤ B →
      ∃ z ∈ Pa, φa z = τ) :
    ∃ w : ℂ, deriv F w = 0 ∧ ∃ K : ℕ, (F^[K]) w ∈ Pa := by
  have hFpoly : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F := hF
  have hFdiff : Differentiable ℂ F :=
    Work.FatouParabolic.Poly.isPolynomialMap_differentiable hFpoly
  have hesc : Work.FatouParabolic.BasinEscape F :=
    Work.FatouParabolic.Poly.isPolynomialMap_basinEscape hFpoly
  have hmapB : Set.MapsTo F (Work.SeedLimit.MultiPetal.satPa F Pa)
      (Work.SeedLimit.MultiPetal.satPa F Pa) :=
    Work.SeedLimit.MultiPetal.satPa_mapsTo hmap
  have hbdd : Bornology.IsBounded (Work.SeedLimit.MultiPetal.satPa F Pa) :=
    Work.SeedLimit.MultiPetal.satPa_isBounded htend hesc
  by_contra hcon
  -- the negation of the conclusion: no critical orbit enters `Pa`
  have hnocrit : ∀ w ∈ Work.SeedLimit.MultiPetal.satPa F Pa, deriv F w ≠ 0 := by
    intro w hw hdw
    obtain ⟨K, hK⟩ := Work.SeedLimit.MultiPetal.mem_satPa.mp hw
    exact hcon ⟨w, hdw, K, hK⟩
  -- every iterate is a covering of the saturation
  have hcover : ∀ n : ℕ, IsCoveringMap
      (Work.FatouParabolic.Core.immBasinIterate (Work.SeedLimit.MultiPetal.satPa F Pa) F hmapB n) :=
    fun n => Work.SeedLimit.MultiPetal.isCoveringMap_iterate_satPa hFpoly hisOpen hmapB n hnocrit
  -- the inverse Fatou coordinate of the petal on the tail of every horizontal strip
  have hpetal : ∃ Φ : ℂ → ℂ, ∀ H : ℝ, 0 < H → ∃ C : ℝ,
      Work.SeedLimit.MultiPetal.StripPropG (Work.SeedLimit.MultiPetal.satPa F Pa) F Φ C H ∧
      Set.InjOn Φ (Work.FatouParabolic.Core.tailStrip C H) := by
    refine ⟨Function.invFunOn φa Pa, fun H hH => ?_⟩
    obtain ⟨C, hC⟩ := hstrip H (le_of_lt hH)
    refine ⟨C, ?_, ?_⟩
    · intro τ hτre hτim
      have hex : ∃ z ∈ Pa, φa z = τ := hC τ hτre (le_of_lt hτim)
      have hmem : Function.invFunOn φa Pa τ ∈ Pa := Function.invFunOn_mem hex
      have hval : φa (Function.invFunOn φa Pa τ) = τ := Function.invFunOn_eq hex
      have hex1 : ∃ z ∈ Pa, φa z = τ + 1 :=
        hC (τ + 1) (by simp only [Complex.add_re, Complex.one_re]; linarith)
          (by simpa using le_of_lt hτim)
      have hmem1 : Function.invFunOn φa Pa (τ + 1) ∈ Pa := Function.invFunOn_mem hex1
      have hval1 : φa (Function.invFunOn φa Pa (τ + 1)) = τ + 1 := Function.invFunOn_eq hex1
      refine ⟨Work.SeedLimit.MultiPetal.mem_satPa.mpr ⟨0, by simpa using hmem⟩, ?_, ?_⟩
      · have hmaps : F (Function.invFunOn φa Pa τ) ∈ Pa := hmap hmem
        have habel' : φa (F (Function.invFunOn φa Pa τ))
            = φa (Function.invFunOn φa Pa τ) + 1 := habel _ hmem
        refine hinj hmaps hmem1 ?_
        rw [habel', hval, hval1]
      · have hmem_nhds : Pa ∈ 𝓝 (Function.invFunOn φa Pa τ) := hisOpen.mem_nhds hmem
        have han : AnalyticAt ℂ φa (Function.invFunOn φa Pa τ) :=
          (hdiff.analyticOn hisOpen).analyticAt hmem_nhds
        have hsd : HasStrictDerivAt φa (deriv φa (Function.invFunOn φa Pa τ))
            (Function.invFunOn φa Pa τ) := han.hasStrictDerivAt
        have hne : deriv φa (Function.invFunOn φa Pa τ) ≠ 0 :=
          Work.ELRig.deriv_ne_zero_of_injOn hdiff hisOpen hinj hmem
        have hev : ∀ᶠ x in 𝓝 (Function.invFunOn φa Pa τ),
            Function.invFunOn φa Pa (φa x) = x := by
          filter_upwards [hmem_nhds] with x hx
          have hex' : ∃ z ∈ Pa, φa z = φa x := ⟨x, hx, rfl⟩
          exact hinj (Function.invFunOn_mem hex') hx (Function.invFunOn_eq hex')
        have hsds := hsd.to_local_left_inverse hne hev
        have hd : DifferentiableAt ℂ (Function.invFunOn φa Pa)
            (φa (Function.invFunOn φa Pa τ)) := hsds.hasDerivAt.differentiableAt
        rwa [hval] at hd
    · intro τ₁ hτ₁ τ₂ hτ₂ heq
      have hex1 : ∃ z ∈ Pa, φa z = τ₁ := hC τ₁ hτ₁.1 (le_of_lt hτ₁.2)
      have hex2 : ∃ z ∈ Pa, φa z = τ₂ := hC τ₂ hτ₂.1 (le_of_lt hτ₂.2)
      have h1 : φa (Function.invFunOn φa Pa τ₁) = τ₁ := Function.invFunOn_eq hex1
      have h2 : φa (Function.invFunOn φa Pa τ₂) = τ₂ := Function.invFunOn_eq hex2
      calc τ₁ = φa (Function.invFunOn φa Pa τ₁) := h1.symm
        _ = φa (Function.invFunOn φa Pa τ₂) := by rw [heq]
        _ = τ₂ := h2
  exact Work.SeedLimit.MultiPetal.false_of_petalInverse_of_covering_general
    hFdiff hmapB hcover hbdd hnocrit hpetal

end Work.MultiPetal
