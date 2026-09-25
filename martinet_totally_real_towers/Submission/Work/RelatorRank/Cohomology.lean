import Submission.Work.RelatorRank.Bridge

/-!
# `Work.RelatorRank` -- the cohomological form of the relation bound

**Namespace** `Work.RelatorRank`; module `Submission.Work.RelatorRank.Cohomology`.

## The cohomological form, and what is missing

For a finitely generated pro-`2` group `Γ` the minimal number of relators of a presentation of `Γ`
on `d(Γ) = GeneratorRank Γ` generators is the *continuous* cohomology dimension

  `dim_{𝔽₂} H²(Γ, 𝔽₂) = minimal number of relators`

(Neukirch--Schmidt--Wingberg, *Cohomology of Number Fields*, I §4.3; Koch, *Galois theory of
`p`-extensions*, Ch. 11; the proof goes through the five-term exact sequence of
`1 → K → F → Γ → 1` with `F` the free pro-`p` group, together with Nakayama's lemma for the
`𝔽_p[[Γ]]`-module `K/Φ(K)`).  **This identification is not formalised in this workspace.**  Two
things are missing:

1. **Continuous cohomology of profinite groups.**  Mathlib has only the discrete/abstract theory
   (`Mathlib.RepresentationTheory.GroupCohomology.*`): group cohomology of a *discrete* group
   acting on a module.  That is not the theory that governs pro-`p` presentations: what is needed is
   continuous cohomology `H^n(Γ, M) = H^n` of the complex of continuous cochains
   `C^n(Γ, M) = {continuous maps Γ^n → M}` (inhomogeneous differential, `Γ` profinite, `M` a
   discrete `𝔽₂`-module), together with the five-term exact sequence of low-degree cohomology for
   `1 → K → F → Γ → 1`.  For instance the pro-`2` group `ℤ₂` has cohomological dimension `1`,
   so its continuous `H²` with `𝔽₂`-coefficients vanishes, and no statement about the *abstract*
   group cohomology of the underlying (uncountable, non-finitely-generated) group can recover this.
2. **The identification with presentations** (Hopf's formula / the transgression), which is what
   turns `dim H² ≤ r` into the *presentation* statement `RelatorRankLe Γ r` consumed here.

Because of this, the *statements* below are phrased in the presentation form -- but they are exactly
the interface an arithmetic theorem stated as `dim_{𝔽₂} H²(Γ, 𝔽₂) ≤ 6` needs: `H2DimLe Γ r` is the
cohomological bound in presentation shape, and `h2_le_six_of_relationRankLeSix` /
`relatorRankLe_of_h2_le_six` convert between the two shapes.

## Main declarations

* `relationRankDim Γ d` : the least number of relators of a presentation on `d` generators;
* `h2Dim Γ` : the same at the canonical generator count `GeneratorRank Γ`;
* `H2DimLe Γ r` : the cohomological bound `dim_{𝔽₂} H²(Γ, 𝔽₂) ≤ r`;
* `h2DimLe_iff_relatorRankLe` : the two shapes are equivalent;
* `h2_le_six_of_relationRankLeSix` : a presentation on five generators with six relators gives
 `dim_{𝔽₂} H²(Γ, 𝔽₂) ≤ 6`;
* `relatorRankLe_of_h2_le_six` : and conversely, a cohomological bound `dim H² ≤ 6` at
  `GeneratorRank Γ = 5` gives the canonical relation-rank bound.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace Work.RelatorRank

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- **The relation-rank dimension `r(Γ; d)`**: the least number of relators of a presentation of `Γ`
on `d` generators (`sInf`, hence `0` when no finite presentation on `d` generators exists).  At
`d = GeneratorRank Γ` this is the relation rank `RelatorRank Γ`, and for a finitely generated
pro-`2` group it equals the continuous cohomology dimension `dim_{𝔽₂} H²(Γ, 𝔽₂)`. -/
noncomputable def relationRankDim (Γ : Type*) [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] (d : ℕ) : ℕ :=
  sInf {r : ℕ | HasProP2Presentation Γ d r}

/-- **`h2Dim Γ`**: `dim_{𝔽₂} H²(Γ, 𝔽₂)` in the presentation form -- the relation-rank dimension at
the canonical generator count. -/
noncomputable def h2Dim (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] : ℕ :=
  relationRankDim Γ (GeneratorRank Γ)

/-- **The cohomological relation bound `dim_{𝔽₂} H²(Γ, 𝔽₂) ≤ r`**, stated in the presentation form
(the identification of the two is the classical theorem recorded in the module docstring; it is not
formalised, so this predicate *is* the cohomological bound in this workspace). -/
def H2DimLe (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (r : ℕ) : Prop :=
  ∃ r' : ℕ, r' ≤ r ∧ RelatorRankLe Γ r'

/-- `H2DimLe` is monotone in `r`. -/
theorem H2DimLe.mono {r r' : ℕ} (h : H2DimLe Γ r) (hr : r ≤ r') : H2DimLe Γ r' := by
  obtain ⟨r'', hr'', hle⟩ := h
  exact ⟨r'', le_trans hr'' hr, hle⟩

/-- **The two shapes are equivalent**: `dim_{𝔽₂} H²(Γ, 𝔽₂) ≤ r` is the canonical relation-rank
bound. -/
theorem h2DimLe_iff_relatorRankLe {r : ℕ} : H2DimLe Γ r ↔ RelatorRankLe Γ r := by
  constructor
  · rintro ⟨r', hr', hle⟩
    exact hle.mono hr'
  · intro h
    exact ⟨r, le_rfl, h⟩

/-- The relation rank is the relation-rank dimension at the canonical generator count. -/
theorem relatorRank_eq_relationRankDim : RelatorRank Γ = relationRankDim Γ (GeneratorRank Γ) := by
  simp only [RelatorRank, relationRankDim, RelatorRankLe]

/-- **A presentation on five generators with six relators gives `dim_{𝔽₂} H²(Γ, 𝔽₂) ≤ 6`.**

The minimality hypothesis identifies the generator number `5` with `GeneratorRank Γ`, so the given
presentation is the canonical relation-rank bound. -/
theorem h2_le_six_of_relationRankLeSix (hmin : NoSmallerGeneratingFamily Γ 5)
    (h : HasProP2Presentation Γ 5 6) : H2DimLe Γ 6 :=
  ⟨6, le_rfl, (relatorRankLeSix_iff_hasProP2Presentation hmin h.to_hasDenseGeneratingFamily).mpr h⟩

/-- The general-`d`, general-`r` form of `h2_le_six_of_relationRankLeSix`. -/
theorem h2DimLe_of_hasProP2Presentation {d r : ℕ} (hmin : NoSmallerGeneratingFamily Γ d)
    (h : HasProP2Presentation Γ d r) : H2DimLe Γ r :=
  ⟨r, le_rfl, (relatorRankLe_iff_hasProP2Presentation hmin h.to_hasDenseGeneratingFamily).mpr h⟩

/-- **The converse direction**, which is the one an arithmetic hypothesis stated as
`dim_{𝔽₂} H²(Γ, 𝔽₂) ≤ 6` is consumed through: at `GeneratorRank Γ = 5` the cohomological bound
gives the canonical relation-rank bound `RelatorRankLe Γ 6`. -/
theorem relatorRankLe_of_h2_le_six (hmin : NoSmallerGeneratingFamily Γ 5) (h : H2DimLe Γ 6) :
    RelatorRankLe Γ 6 :=
  h2DimLe_iff_relatorRankLe.mp h

/-- The general-`r` form of `relatorRankLe_of_h2_le_six`. -/
theorem relatorRankLe_of_h2DimLe {r : ℕ} (h : H2DimLe Γ r) : RelatorRankLe Γ r :=
  h2DimLe_iff_relatorRankLe.mp h

/-- **Cohomological form of the bridge.**  If the arithmetic input is stated cohomologically
(`dim_{𝔽₂} H²(Γ, 𝔽₂) ≤ 6`), then -- together with the *generator* half
`HasDenseGeneratingFamily Γ 5` (the workspace's `GeneratorHalf`) and the minimality of five-element
generating families -- and with the missing invariance of the relation count
(`RelationRankInvariant Γ 5 6`) -- every dense generating five-element family of `Γ` admits at most
six relators.

The minimality and generator hypotheses identify `GeneratorRank Γ` with `5`, so the cohomological
bound is compatible with five generators. -/
theorem relator_half_of_h2_le_six (hmin : NoSmallerGeneratingFamily Γ 5)
    (hex : HasDenseGeneratingFamily Γ 5)
    (hinv : RelationRankInvariant Γ 5 6) (h : H2DimLe Γ 6) :
    ∀ gen : Fin 5 → Γ, DenseGenerating gen →
      ∃ rel : Finset (FreeGroup (Fin 5)), rel.card ≤ 6 ∧
        MonoidHom.ker (FreeGroup.lift gen) = Subgroup.normalClosure (rel : Set (FreeGroup (Fin 5))) :=
  hinv ((relatorRankLeSix_iff_hasProP2Presentation hmin hex).mp (relatorRankLe_of_h2_le_six hmin h))

end Work.RelatorRank
