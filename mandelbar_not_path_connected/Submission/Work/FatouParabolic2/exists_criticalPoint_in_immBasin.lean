import Mathlib
import Submission.Work.FatouParabolic2.Defs
import Submission.Work.FatouParabolic2.pa_subset_immBasin
import Submission.Work.FatouParabolic2.mapsTo_immBasin
import Submission.Work.FatouParabolic2.petalInv_spec
import Submission.Work.FatouParabolic.Core.exists_isCriticalPoint_in_immBasin
import Submission.Work.FatouParabolic.Core.ImmBasin.false_of_petalInverse_of_covering
import Submission.Work.FatouParabolic.Poly.isPolynomialMap_differentiable
import Submission.Work.FatouParabolic.Core.ImmBasin.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Filter Set

namespace Work.FatouParabolic2

/-- **Fatou's result in the immediate basin, from petal data.**  A polynomial map `F` of degree
`≥ 2` with a fixed point `z₀` which carries petal data `pd` (an attracting petal with a
holomorphic injective Fatou coordinate whose image exhausts the tails of all horizontal strips)
has a critical point in the *immediate* basin of `z₀`, i.e. in the connected component of
`interior (basin F z₀)` through any petal point `p₀`.

This is the Liouville/covering step of the design, on the interface `PetalData` instead of the
flower.  The assembly replays the final proof of
`Work.FatouParabolic.Core.exists_isCriticalPoint_in_immBasin` with the three flower-specific
inputs replaced by `Work.FatouParabolic2.mapsTo_immBasin`, `Work.FatouParabolic2.pa_subset_immBasin`
and `Work.FatouParabolic2.petalInv_spec`:

* suppose no point of `Ω := immBasin F z₀ p₀` is critical;
* `hmap := mapsTo_immBasin hF pd hp₀`, `hopen := Core.exists_isOpen_immBasin F z₀ p₀`,
  `hbdd := Core.exists_isBounded_immBasin hF`, `hΩP := connectedComponentIn_subset _ _`,
  `hcl := Core.exists_immBasin_closed_in_interior F z₀ p₀`, and
  `Core.exists_isCoveringMap_immBasinIterate n hF hfix hopen hmap hΩP hcl hbdd hnocrit` give
  that every iterate `F^[n] : Ω → Ω` is a covering;
* `Core.ImmBasin.false_of_petalInverse_of_covering hFdiff hmap hcover hbdd hnocrit hpetal`
  yields the contradiction, with `hpetal := ⟨Function.invFunOn pd.φa pd.Pa, fun B hB => ...⟩`
  supplied by `petalInv_spec pd hFdiff hB` together with `pa_subset_immBasin pd hp₀` (to know that
  the values of the inverse coordinate lie in `Ω`). -/
theorem exists_criticalPoint_in_immBasin {F : ℂ → ℂ} {z₀ : ℂ}
    (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F) (hfix : F z₀ = z₀)
    (pd : PetalData F z₀) {p₀ : ℂ} (hp₀ : p₀ ∈ pd.Pa) :
    ∃ w ∈ Work.FatouParabolic.Core.immBasin F z₀ p₀, deriv F w = 0 := by
  by_contra hcon
  push_neg at hcon
  have hFdiff : Differentiable ℂ F := Work.FatouParabolic.Poly.isPolynomialMap_differentiable hF
  -- Q1: the structural facts about the immediate basin
  have hopen : IsOpen (Work.FatouParabolic.Core.immBasin F z₀ p₀) :=
    Work.FatouParabolic.Core.exists_isOpen_immBasin F z₀ p₀
  have hPa_sub : pd.Pa ⊆ Work.FatouParabolic.Core.immBasin F z₀ p₀ :=
    pa_subset_immBasin pd hp₀
  have hmap : Set.MapsTo F (Work.FatouParabolic.Core.immBasin F z₀ p₀)
      (Work.FatouParabolic.Core.immBasin F z₀ p₀) :=
    mapsTo_immBasin hF pd hp₀
  have hbdd : Bornology.IsBounded (Work.FatouParabolic.Core.immBasin F z₀ p₀) :=
    Work.FatouParabolic.Core.exists_isBounded_immBasin (z₀ := z₀) hF
  -- Q2: every iterate is a covering of the critical-point-free immediate basin
  have hcover : ∀ n : ℕ, IsCoveringMap
      (Work.FatouParabolic.Core.immBasinIterate
        (Work.FatouParabolic.Core.immBasin F z₀ p₀) F hmap n) :=
    fun n => Work.FatouParabolic.Core.exists_isCoveringMap_immBasinIterate n hF hfix hopen hmap
      (connectedComponentIn_subset _ _)
      (Work.FatouParabolic.Core.exists_immBasin_closed_in_interior F z₀ p₀) hbdd hcon
  -- Q3: the canonical petal inverse supplies the hypothesis of the strip-lifting argument
  have hpetal : ∃ Φ : ℂ → ℂ, ∀ B : ℝ, 0 < B → ∃ C : ℝ,
      (∀ τ : ℂ, C < τ.re → |τ.im| < B →
        Φ τ ∈ Work.FatouParabolic.Core.immBasin F z₀ p₀ ∧
        F (Φ τ) = Φ (τ + 1) ∧ DifferentiableAt ℂ Φ τ) ∧
      Set.InjOn Φ (Work.FatouParabolic.Core.tailStrip C B) := by
    refine ⟨Function.invFunOn pd.φa pd.Pa, fun B hB => ?_⟩
    obtain ⟨C, hC, hinj⟩ := petalInv_spec pd hFdiff hB
    refine ⟨C, fun τ h1 h2 => ?_, hinj⟩
    obtain ⟨hmem, -, hFτ, hdτ⟩ := hC τ h1 h2
    exact ⟨hPa_sub hmem, hFτ, hdτ⟩
  -- Q4–Q6: the bounded entire function obtained by lifting `Φ` contradicts Liouville
  exact Work.FatouParabolic.Core.ImmBasin.false_of_petalInverse_of_covering
    hFdiff hmap hcover hbdd hcon hpetal

end Work.FatouParabolic2
