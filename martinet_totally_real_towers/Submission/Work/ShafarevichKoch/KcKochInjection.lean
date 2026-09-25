import Mathlib
import Submission.Work.ShafarevichKoch.KcCohomology
import Submission.Work.ShafarevichKoch.contH2DimLe_six_of_kochInjection

/-!
# `Work.ShafarevichKoch.KcKochInjection` -- the classical Koch injection, and the crux

This module keeps the **single classical arithmetic statement** on which this chapter's crux
rests, in the sharpest form the workspace can state -- as a proposition about the objects of the
chapter -- and derives from it, in one step each, the chapter's crux and the walls.

## The statement

For `Kc = ℚ(√-30030)`, `G_∅ = Gal(Kc_∅/Kc)` and Koch's Kummer radical
`V_∅ = VTwo Kc = {x ∈ Kcˣ : (x) is a square fractional ideal}` (§4 of the README), the
classical theorem of Shafarevich (1963) and Koch (*Galois theory of `p`-extensions*, Ch. 11
Thm. 11.3) is the **injection**

`Sha_∅ = H²(G_∅, 𝔽₂)  ↪  (V_∅/Kc^{×2})^∨`,

where `H²` is *continuous* cohomology (`Work.RelatorRank.contH2`, built on
`Submission/Work/ConCohomology/`) and the codomain is the `𝔽₂`-dual of Koch's radical quotient.
`KochInjection M` below is exactly this injection; for `S = ∅` there are no local conditions, so
Koch's embedding is the whole theorem.  Its *numerical* consequence is the classical relation
bound `dim_{𝔽₂} H²(G_∅,𝔽₂) ≤ dim_{𝔽₂} V_∅/Kc^{×2} = 6`, i.e. `KcKochCohomologyBound` -- and the
dimension count that turns the injection into that numerical bound is
`Work.ShafarevichKoch.contH2DimLe_six_of_kochInjection` (delegated and proved in this session),
whose engine is the *proved* count

`Nat.card ((V_∅/Kc^{×2}) →* Multiplicative (ZMod 2)) = 64 = 2^6`
(`Work.ShafarevichKoch.natCard_dual_VTwoQuot_Kc`, from `card_vTwo_mod_squares`,
`classGroupTwoRank_Kc = 5`, `unitTwoRank Kc = 1`).

So the deliverable's item (2) is, in this workspace,

```
(∃ M, KochInjection M)                                   -- the classical arithmetic
  + (∀ M, GaschutzCohomologicalValue (galoisGroup M))    -- the shared group theory
  ⟹ KcProTwoPresentationInput                            -- this chapter's crux
  ⟹ InfiniteProTwoExtension Kc, BoundedRdTowerWall, ...
```

with every arrow proved here or in `KcCohomology.lean`.  The arithmetic input is *not* weakened by
being stated as an injection: because `dim_{𝔽₂} V_∅/Kc^{×2} = 6`, the injection is equivalent to
`dim_{𝔽₂} H²(G_∅,𝔽₂) ≤ 6` (for `H²` of finite dimension), which is exactly the classical
relation bound.

## Main declarations

* `Work.ShafarevichKoch.KochInjection` : the classical injection, as a proposition;
* `Work.ShafarevichKoch.kcKochCohomologyBound_of_kochInjection` :
  `(∃ M, KochInjection M) → KcKochCohomologyBound`;
* `Work.ShafarevichKoch.kcProTwoPresentationInput_of_kochInjection` : the crux, from the injection
  and Gaschütz's value theorem;
* `Work.ShafarevichKoch.infiniteProTwoExtension_Kc_of_kochInjection`,
  `Work.ShafarevichKoch.unramifiedPro2TowerWall_of_kochInjection`,
  `Work.ShafarevichKoch.boundedRdTowerWall_of_kochInjection`,
  `Work.ShafarevichKoch.exists_unramifiedLevel_rootDiscr_of_kochInjection` : the walls.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped Classical
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-- **The classical Shafarevich--Koch injection for `Kc`, as a proposition.**

`Sha_∅ = H²_cont(G_∅, 𝔽₂)` injects into the `𝔽₂`-dual of Koch's Kummer quotient
`V_∅/Kc^{×2}` (Koch, *Galois theory of `p`-extensions*, Ch. 11 Thm. 11.3; Shafarevich 1963).
For `S = ∅` there are no local conditions, so this embedding *is* the classical relation bound:
combined with `#(V_∅/Kc^{×2})^∨ = 2^6` it gives `dim_{𝔽₂} H²(G_∅,𝔽₂) ≤ 6`. -/
def KochInjection (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2) : Prop :=
  ∃ ι : Work.RelatorRank.contH2 (galoisGroup M) →+
      Additive ((↥(VTwo Kc) ⧸
          (Work.QuadraticFields.squareSubgroup Kcˣ).subgroupOf (VTwo Kc)) →*
        Multiplicative (ZMod 2)),
    Function.Injective ι

/-- **The arithmetic input in cohomological form, from the classical injection.** -/
theorem kcKochCohomologyBound_of_kochInjection
    (h : ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2, KochInjection M) :
    KcKochCohomologyBound := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M, contH2DimLe_six_of_kochInjection M hM⟩

/-- **The crux, from the two classical inputs**: the Koch injection and Gaschütz's value theorem
`r(Γ) = dim_{𝔽₂} H²(Γ,𝔽₂)` for `Γ = G_∅`. -/
theorem kcProTwoPresentationInput_of_kochInjection
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2, KochInjection M) :
    KcProTwoPresentationInput :=
  kcProTwoPresentationInput_of_kochCohomologyBound hdict
    (kcKochCohomologyBound_of_kochInjection h)

/-- **`Kc` has an infinite Hilbert `2`-class field tower**, from the two classical inputs. -/
theorem infiniteProTwoExtension_Kc_of_kochInjection
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2, KochInjection M) :
    Work.ClassFieldTower.InfiniteProTwoExtension Kc :=
  infiniteProTwoExtension_Kc_of_input (kcProTwoPresentationInput_of_kochInjection hdict h)

/-- **The caller's wall `Submission.NumberField.UnramifiedPro2TowerWall`**, from the two classical
inputs. -/
theorem unramifiedPro2TowerWall_of_kochInjection
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2, KochInjection M) :
    Submission.NumberField.UnramifiedPro2TowerWall :=
  unramifiedPro2TowerWall_of_input (kcProTwoPresentationInput_of_kochInjection hdict h)

/-- **The caller's wall `Submission.NumberField.BoundedRdTowerWall`**, from the two classical
inputs. -/
theorem boundedRdTowerWall_of_kochInjection
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2, KochInjection M) :
    Submission.NumberField.BoundedRdTowerWall :=
  boundedRdTowerWall_of_input (kcProTwoPresentationInput_of_kochInjection hdict h)

/-- **Unramified levels of every prescribed degree with constant root discriminant**, from the two
classical inputs. -/
theorem exists_unramifiedLevel_rootDiscr_of_kochInjection
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2, KochInjection M) (N : ℕ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra Kc L)
      (_ : FiniteDimensional Kc L) (_ : IsGalois Kc L),
      N ≤ Module.finrank Kc L ∧ differentIdeal (𝓞 Kc) (𝓞 L) = ⊤ ∧
        NumberField.rootDiscr L = NumberField.rootDiscr Kc :=
  exists_unramifiedLevel_rootDiscr_of_contH2DimLe
    _ (hdict _) (contH2DimLe_six_of_kochInjection _ (h.choose_spec)) N

end Work.ShafarevichKoch
