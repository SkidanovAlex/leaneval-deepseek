import Mathlib
import Submission.Work.WingbergRoute.Main
import Submission.Work.WingbergRoute.TotallyReal
import Submission.Work.ShafarevichKoch.UnitHalf.kcProTwoPresentationInput_of_unitDuality

/-!
# `Work.WingbergRoute.UnitWall` -- the wall in its sharpest form: the *unit half* of Wingberg's duality

The deliverable of this area is the *single* arithmetic consequence of Wingberg's duality that the
benchmark needs, `df(G_∅) = d₂(E_K / N E_{K_∅}) ≤ d₂(O_K^×)`, in the cheapest available form.  This
module states that consequence in the sharpest form the workspace admits and wires the whole endgame
to it.

## What is already free, and what is not

For `Kc = ℚ(√-30030)` the chapter `Submission/Work/ShafarevichKoch/` proves **unconditionally** the
`H²`-half of the relation count,

`#(H²(G_∅,ℤ)/2H²(G_∅,ℤ)) ≤ 2^5`
(`Work.ShafarevichKoch.H2Half.natCard_H2Z_quot_two_le_pow_five_Kc`), and the `ℤ`-power sequence

`#H²(G_∅,𝔽₂) = #(H²(G_∅,ℤ)/2H²(G_∅,ℤ)) · #H³(G_∅,ℤ)[2]`

(`Work.ShafarevichKoch.natCard_H2_zmodTwo_eq`).  So *only* the `H³`-half remains, and it is
Wingberg's duality in degree `0`:

`H³(G_∅,ℤ)^∨ ≅  Ĥ⁰(G_∅, O_{K_∅}^×) = lim_{F} O_K^×/N_{F/K} O_F^×`  (universal norms of units),

which for `Kc` — whose units are `{±1}` — is a quotient of `{±1}`, i.e. `#H³(G_∅,ℤ)[2] ≤ 2`.
`Work.WingbergRoute.KcUnitDualityWall` below is exactly this input, in the form in which
`Work.ShafarevichKoch.UnitHalf.contH2DimLe_six_of_unitDuality` consumes it.  It is the
Theorem 8.8.1 of Neukirch--Schmidt--Wingberg, Ch. VIII §8 (with `S = T = ∅`, `c` the class of
finite `2`-groups, `A = ℤ`), quoted e.g. as `theo:wingberg` in Hajir--Maire--Ramakrishna,
arXiv:2103.09508 §"alternative proof"; its proof is global class field theory (the Tate/Artin theory
of the idèle class group of the tower) and is *not* available in this workspace.

## The sharp form and the slack

The classical theorem is sharper than what the benchmark needs.  Wingberg's duality gives
`df(G_∅) ≤ d₂(O_K^×) - dim_{𝔽_p} μ_p(K)` (the roots of unity are universal norms, since
`N_{F/K}(ζ) = ζ^{[F:K]} = 1` for `ζ ∈ μ_p(K)` and `[F:K]` a power of `p`).  For `Kc` this reads
`df ≤ 1 - 1 = 0`, i.e. `H³(G_∅,ℤ)` is *trivial* and `r = d = 5` — see
`Work.WingbergRoute.kcUnitDualityWall_of_h3_trivial`.  My walls only need `df ≤ 1`
(`KcWingbergWall`) resp. `df ≤ 2` (`gsFWingbergWall`), so they are *strictly weaker* than the
classical theorem: nothing here asks for more than the literature gives.

## Main declarations

* `Work.WingbergRoute.KcUnitDualityWall` (the wall, sharpest form);
* `Work.WingbergRoute.kcWingbergWall_of_unitDualityWall`;
* and the endgame transported to the sharp wall:
  `kcProTwoPresentationInput_of_unitDualityWall`, `hasProTwoPresentation_Kc_five_six_of_unitDualityWall`,
  `infiniteProTwoExtension_Kc_of_unitDualityWall`, `unramifiedPro2TowerWall_of_unitDualityWall`,
  `boundedRdTowerWall_of_unitDualityWall`, `exists_unramifiedLevel_rootDiscr_of_unitDualityWall`,
  with the `_seamFree` variants (Gaschütz's dictionary in the form
  `Work.AbstractDictionary.GaschutzPresentationExists`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped Classical
open NumberField

noncomputable section

namespace Work.WingbergRoute

open Work.ConCohomology Work.ShafarevichKoch Work.ClassFieldTower

/-- **The wall, in the sharpest form available: the unit half of Wingberg's duality.**

There is a maximal unramified pro-`2` extension `M` of `Kc = ℚ(√-30030)` for which `H²(G_∅,ℤ)` and
`H³(G_∅,ℤ)` are finite and the Pontryagin dual of `H³(G_∅,ℤ)` is a quotient of the units
`(𝓞 Kc)ˣ = {±1}`.  Equivalently (HMR, `theo:wingberg`): `H³(G_∅,ℤ)^∨ ≅ Ĥ⁰(G_∅, O_{K_∅}^×)`, the
universal norms of units.  Wingberg, *On the Fontaine--Mazur conjecture for CM-fields*, Compositio
Math. **131** (2002); Neukirch--Schmidt--Wingberg, Ch. VIII §8, Theorem 8.8.1 (with
`S = T = ∅`). -/
def KcUnitDualityWall : Prop :=
  ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
    Finite (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ) ∧
      Finite (Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ) ∧
        ∃ N : Subgroup (Work.ShafarevichKoch.RingUnit Kc),
          Nonempty (Work.ShafarevichKoch.PDual
              (Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ) ≃+
            Additive (Work.ShafarevichKoch.RingUnit Kc ⧸ N))

/-- **The sharp wall gives `KcWingbergWall`** (and hence everything in `Main.lean`). -/
theorem kcWingbergWall_of_unitDualityWall (h : KcUnitDualityWall) : KcWingbergWall := by
  obtain ⟨M, h2, h3, N, hN⟩ := h
  exact ⟨M, shafarevichBound_of_contH2DimLe_six M
    (Work.ShafarevichKoch.UnitHalf.contH2DimLe_six_of_unitDuality M h2 h3 ⟨N, hN⟩)⟩

/-! ## The endgame, transported to the sharp wall -/

/-- **The chapter's crux from the sharp wall** (Gaschütz's value theorem as input). -/
theorem kcProTwoPresentationInput_of_unitDualityWall
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : KcUnitDualityWall) : Work.ShafarevichKoch.KcProTwoPresentationInput :=
  kcProTwoPresentationInput_of_kcWingbergWall hdict (kcWingbergWall_of_unitDualityWall h)

/-- **`Work.ShafarevichKoch.HasProTwoPresentation Kc 5 6` from the sharp wall.** -/
theorem hasProTwoPresentation_Kc_five_six_of_unitDualityWall
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : KcUnitDualityWall) : Work.ShafarevichKoch.HasProTwoPresentation Kc 5 6 :=
  hasProTwoPresentation_Kc_five_six_of_kcWingbergWall hdict (kcWingbergWall_of_unitDualityWall h)

/-- **`Kc` has an infinite unramified pro-`2` tower, from the sharp wall.** -/
theorem infiniteProTwoExtension_Kc_of_unitDualityWall
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : KcUnitDualityWall) : Work.ClassFieldTower.InfiniteProTwoExtension Kc :=
  infiniteProTwoExtension_Kc_of_kcWingbergWall hdict (kcWingbergWall_of_unitDualityWall h)

/-- **The caller's `UnramifiedPro2TowerWall`, from the sharp wall.** -/
theorem unramifiedPro2TowerWall_of_unitDualityWall
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : KcUnitDualityWall) : Submission.NumberField.UnramifiedPro2TowerWall :=
  unramifiedPro2TowerWall_of_kcWingbergWall hdict (kcWingbergWall_of_unitDualityWall h)

/-- **The caller's `BoundedRdTowerWall`, from the sharp wall.** -/
theorem boundedRdTowerWall_of_unitDualityWall
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : KcUnitDualityWall) : Submission.NumberField.BoundedRdTowerWall :=
  boundedRdTowerWall_of_kcWingbergWall hdict (kcWingbergWall_of_unitDualityWall h)

/-- **Unramified levels of every prescribed degree with constant root discriminant, from the sharp
wall.** -/
theorem exists_unramifiedLevel_rootDiscr_of_unitDualityWall
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : KcUnitDualityWall) (N : ℕ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra Kc L)
      (_ : FiniteDimensional Kc L) (_ : IsGalois Kc L),
      N ≤ Module.finrank Kc L ∧ differentIdeal (𝓞 Kc) (𝓞 L) = ⊤ ∧
        NumberField.rootDiscr L = NumberField.rootDiscr Kc :=
  exists_unramifiedLevel_rootDiscr_of_kcWingbergWall hdict (kcWingbergWall_of_unitDualityWall h) N

/-! ## The seam-free variants (Gaschütz via `Work.AbstractDictionary`) -/

/-- **The chapter's crux from the sharp wall, seam-free.** -/
theorem kcProTwoPresentationInput_of_unitDualityWall_seamFree
    (hpres : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.AbstractDictionary.GaschutzPresentationExists (Work.ClassFieldTower.galoisGroup M))
    (h : KcUnitDualityWall) : Work.ShafarevichKoch.KcProTwoPresentationInput :=
  kcProTwoPresentationInput_of_kcWingbergWall_seamFree hpres (kcWingbergWall_of_unitDualityWall h)

/-- **`HasProTwoPresentation Kc 5 6` from the sharp wall, seam-free.** -/
theorem hasProTwoPresentation_Kc_five_six_of_unitDualityWall_seamFree
    (hpres : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.AbstractDictionary.GaschutzPresentationExists (Work.ClassFieldTower.galoisGroup M))
    (h : KcUnitDualityWall) : Work.ShafarevichKoch.HasProTwoPresentation Kc 5 6 :=
  hasProTwoPresentation_Kc_five_six_of_kcWingbergWall_seamFree hpres
    (kcWingbergWall_of_unitDualityWall h)

/-- **The caller's `BoundedRdTowerWall` from the sharp wall, seam-free.** -/
theorem boundedRdTowerWall_of_unitDualityWall_seamFree
    (hpres : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.AbstractDictionary.GaschutzPresentationExists (Work.ClassFieldTower.galoisGroup M))
    (h : KcUnitDualityWall) : Submission.NumberField.BoundedRdTowerWall :=
  boundedRdTowerWall_of_kcWingbergWall_seamFree hpres (kcWingbergWall_of_unitDualityWall h)

end Work.WingbergRoute
