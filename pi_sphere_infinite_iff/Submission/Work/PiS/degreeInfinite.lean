import Mathlib
import Submission.Work.PiS.Interfaces
import Submission.Work.Stems.hurewiczMapN_surjective
import Submission.Work.RatHurewicz.SphereConnectivity

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-! Guidance from the project lead (the requester):

AREA DEGREE (lead's guidance). π_n(Sⁿ) is infinite for n ≥ 2 because the Hurewicz map
π_n(Sⁿ) → H_n(Sⁿ;ℤ) ≅ ℤ is surjective.

* `Work.Stems.hurewiczMapN_surjective` — surjectivity of the Hurewicz map in the first
  non-vanishing degree (`Sⁿ` is `(n-1)`-connected, so the Hurewicz map is onto);
* `Work.RatHurewicz.sphereConnected` — `Sⁿ` is `(n-1)`-connected;
* `Work.Cohomology.sphereHomologyTop` — `H_n(Sⁿ;ℤ) ≅ ℤ`.

The map `πₙ(Sⁿ) → Hₙ(Sⁿ;ℤ) ≅ ℤ` is thus surjective onto an infinite type, and a surjection
onto an infinite type makes its source infinite.
-/

open CategoryTheory

namespace Work.PiS

noncomputable section

/-- `Hₙ(Sⁿ;ℤ)` is infinite for `n ≥ 1`: it is isomorphic to `ℤ`
(`Work.Cohomology.sphereHomologyTop`), and an isomorphism of `ℤ`-modules gives a bijection. -/
theorem infinite_HZ_sphere (n : ℕ) (hn : 1 ≤ n) : Infinite (HZ (Sph n) n) := by
  obtain ⟨e⟩ := Work.Cohomology.sphereHomologyTop n hn
  exact Infinite.of_injective (ModuleCat.Hom.hom e.inv)
    ((ModuleCat.mono_iff_injective e.inv).mp inferInstance)

/-- **Area DEGREE.** `πₙ(Sⁿ)` is infinite for `n ≥ 2`.

`Sⁿ` is `(n-1)`-connected (`Work.RatHurewicz.sphereConnected`), so by the first
non-vanishing degree Hurewicz theorem (`Work.Stems.hurewiczMapN_surjective`) the Hurewicz map
`πₙ(Sⁿ) → Hₙ(Sⁿ;ℤ)` is surjective; composing with the chosen identification
`Hₙ(Sⁿ;ℤ) ≅ ℤ` (`Work.Cohomology.sphereHomologyTop`) gives a surjection from `πₙ(Sⁿ)` onto the
infinite type `ℤ`.  A section of that surjection is then injective, so `πₙ(Sⁿ)` is infinite. -/
theorem degreeInfinite : Work.PiS.DegreeInfinite := by
  intro n hn
  have hn1 : 1 ≤ n := by omega
  -- `Sⁿ` is `(n-1)`-connected, hence the Hurewicz map is onto in degree `n`
  have hconn : ∀ i : ℕ, i < n → Subsingleton (HomotopyGroup (Fin i) (Sph n) (pt n)) :=
    Work.RatHurewicz.sphereConnected n hn1 (pt n)
  have hsurj : Function.Surjective (Work.Stems.hurewiczMapN n hn1 (pt n)) :=
    Work.Stems.hurewiczMapN_surjective n hn (pt n) hconn
  -- compose with the chosen identification `Hₙ(Sⁿ;ℤ) ≅ ℤ`
  obtain ⟨e⟩ := Work.Cohomology.sphereHomologyTop n hn1
  have hsurj_e : Function.Surjective (ModuleCat.Hom.hom e.hom) :=
    (ModuleCat.epi_iff_surjective e.hom).mp inferInstance
  set f : HomotopyGroup (Fin n) (Sph n) (pt n) → ℤ :=
    fun a => ModuleCat.Hom.hom e.hom (Work.Stems.hurewiczMapN n hn1 (pt n) a) with hf
  have hsurj' : Function.Surjective f := hsurj_e.comp hsurj
  change Infinite (HomotopyGroup (Fin n) (Sph n) (pt n))
  -- a section of a surjection onto `ℤ` is injective, so the source is infinite
  refine Infinite.of_injective (fun z : ℤ => Classical.choose (hsurj' z)) fun z w h => ?_
  have hz := Classical.choose_spec (hsurj' z)
  have hw := Classical.choose_spec (hsurj' w)
  exact hz.symm.trans ((congrArg f h).trans hw)

end

end Work.PiS
