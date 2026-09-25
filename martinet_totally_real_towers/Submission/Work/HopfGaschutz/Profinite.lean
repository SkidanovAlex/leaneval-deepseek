import Mathlib
import Submission.Work.HopfGaschutz.Defs
import Submission.Work.RelatorRank.CohomologyH2
import Submission.Work.RelatorRank.GeneratorRank.hasDenseGeneratingFamily_of_continuous_surjective

/-!
# `Work.HopfGaschutz.Profinite` -- the profinite gap, as named bridges

**Namespace** `Work.HopfGaschutz`; module `Submission.Work.HopfGaschutz.Profinite`.

This module records the *exact* statements that separate the **finite** dictionary proved in this
chapter (`CohomologicalDictionary.lean`) from the profinite statements consumed by the arithmetic
chapters (`Work.TameSalle.SalleTameRelationBound`,
`Work.RelatorRank.GaschutzCohomologicalValue`, `Work.HopfGaschutz.GaschutzDictionary`).  It is
imported by `All.lean` so that a reader of the area cannot miss it.

## The two categories

* **pro-`p`.**  A presentation of a pro-`p` group `Γ` means a continuous surjection `F̂_d ↠ Γ` from
  the free pro-`p` group on `d` generators whose kernel is the *closed normal closure* of `r`
  elements.  This is the category in which the classical theorem
  `r(Γ) = dim_{𝔽_p} H²_cont(Γ, 𝔽_p)` lives (Gaschütz 1953; Koch, *Galois theory of `p`-extensions*,
  Ch. 11; Neukirch--Schmidt--Wingberg I §4.3), and the one in which Salle's relation bound
  (`r − d ≤ dim_{𝔽₂} B_S/ℚ^{×2} = 1`, Hajir--Maire--Ramakrishna arXiv:2103.09508 §1) is proved.
* **discrete.**  A presentation in the workspace's sense
  (`Work.TameArithmetic.TamePro2Presentation`, `Work.RelatorRank.HasProP2Presentation`) is a family
  `gen : Fin d → Γ` with *dense* image and a finite `rel ⊆ FreeGroup (Fin d)` (the *discrete* free
  group) with `ker (FreeGroup.lift gen) = Subgroup.normalClosure rel`.

The two normalisations differ by the *engine* (`K = ⟨S⟩^F · K^p[K,F] → K = ⟨S⟩^F`), which needs the
defect `K ⧸ ⟨S⟩^F` to have no prime-to-`p`-quotients (equivalently: the abstract group presented by
the relators must be *residually a finite `p`-group*, i.e. equal to its pro-`p` completion):

* in the pro-`p` category the defect is a compact pro-`p` group and Nakayama for compact modules over
  the completed group algebra `𝔽_p[[Γ]]` applies -- classical, and *not formalisable here*, since
  Mathlib has neither free pro-`p` groups nor `𝔽_p[[Γ]]`;
* for a **finite** `p`-group the defect is a finite `p`-group and the engine is a theorem of this
  chapter (`le_normalClosure_of_le_sup_relFrattini`,
  `normalGeneratorNumber_eq_relFrattiniDim_of_finite_pgroup`) -- and at the finite level residual
  `p`-finiteness is automatic, so what remains there is exactly *efficiency* of the finite `p`-group
  (`GaschutzDictionary p`, `README.md` §3);
* for the **discrete** free group of rank one the naive criterion is *false*: `K = 2ℤ ⊴ ℤ` and
  `S = {6}` satisfy `K = ⟨S⟩^F · K^p[K,F]` while `⟨S⟩^F = 6ℤ ≠ 2ℤ` -- `Counterexample.lean`.

## What this chapter proves (finite level)

`CohomologicalDictionary.card_contH2_eq_card_relFrattiniQuotient` identifies `H²(Q,𝔽₂)` (`Q`
finite, discrete) with the relation-Frattini quotient `K ⧸ K²[K,F]` of any *minimal* presentation of
`Q`, and `h2DimOf_eq_log_card_contH2` reads this as `h2DimOf 2 α Q gen = dim_{𝔽₂} H²(Q,𝔽₂)`.  Hence

* `log_card_contH2_le_card_of_presentation`: every presentation has `dim H² ≤ #relators`;
* what is left of the dictionary at the finite level is exactly *efficiency* of finite `p`-groups.

## The bridges, and a warning

Both bridges below move information *upwards*, from the finite quotients to `Γ`, which is the
direction in which such information can flow.

**Warning (a correction of the naive statement).**  It is tempting to say that
`dim_{𝔽₂} H²(Γ,𝔽₂) = sup_{U ◁ₒ Γ} dim_{𝔽₂} H²(Γ/U, 𝔽₂)`.  **This is false in general.**  The
cochain complexes really are the filtered colimit of those of the quotients
(`CochainFactorization` below), and *filtered colimits of complexes are exact*, so

  `H²(Γ,𝔽₂) = colim_U H²(Γ/U,𝔽₂)`  -- a colimit, with the *inflation* maps as transitions;

and those transition maps need not be injective: for `Γ = ℤₚ` the inflation
`H²(ℤ/p^n,𝔽ₚ) → H²(ℤ/p^{n+1},𝔽ₚ)` is the **zero** map for every `n ≥ 1` (it is the transgression of
the five term sequence of `1 → ℤ/p → ℤ/p^{n+1} → ℤ/p^n → 1`, and `H¹(ℤ/p^{n+1}) → H¹(ℤ/p)` is onto
because both groups are `𝔽ₚ`), while `H²(ℤ/p^n,𝔽ₚ) ≅ 𝔽ₚ` for every `n ≥ 1`.  Hence
`H²(ℤₚ,𝔽ₚ) = 0 = colim`, which agrees with `cd(ℤₚ) = 1`, but
`sup_n dim H²(ℤ/p^n,𝔽ₚ) = 1 ≠ 0`.  So a bound on `Γ` does **not** bound the individual finite
quotients; what transfers upwards is a *uniform* bound on the quotients
(`ContH2UniformBoundBridge`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.HopfGaschutz

/-- **The cochain factorisation**: for a profinite group `Γ` (i.e. `Γ` compact and Hausdorff with a
neighbourhood basis of `1` consisting of open subgroups, which holds for a compact totally
disconnected topological group), every locally constant `2`-cochain on `Γ × Γ` factors through
`Γ/U × Γ/U` for some open normal `U ◁ₒ Γ`.  Equivalently: the complex of continuous cochains on `Γ`
is the filtered colimit of those of its finite quotients.

This is the concrete ingredient of every comparison between `H*(Γ,𝔽ₚ)` and the cohomology of the
finite quotients; *it is provable with what the workspace has* (compactness of `Γ × Γ` to get a
finite subcover of neighbourhoods, then the neighbourhood basis of open subgroups to take the
intersection), but it is not formalised here.  Reference: Serre, *Cohomologie galoisienne*, I §2.2. -/
def CochainFactorization (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] : Prop :=
  ∀ (M : Type) [AddCommGroup M] (f : LocallyConstant (Γ × Γ) M),
    ∃ U : OpenNormalSubgroup Γ, ∃ g : (Γ ⧸ U.toSubgroup) × (Γ ⧸ U.toSubgroup) → M,
      ⇑f = fun p => g (QuotientGroup.mk' U.toSubgroup p.1, QuotientGroup.mk' U.toSubgroup p.2)

/-- **Bridge 1 (the useful direction).**  A *uniform* bound on the finite quotients of `Γ` gives the
same bound on `Γ`: if for some `U ◁ₒ Γ` every finite quotient `Γ/V` with `V ≤ U` has
`dim_{𝔽₂} H²(Γ/V,𝔽₂) ≤ r` (in the finite-dimension form `ContH2DimLe`), then
`dim_{𝔽₂} H²(Γ,𝔽₂) ≤ r`.

This is the direction in which the arithmetic bounds travel: Salle's theorem produces bounds at the
finite levels, and this bridge puts them on `Γ`.  The converse direction is false -- see the warning
in the module docstring.  Proof ingredients: `CochainFactorization` (so that `H²(Γ)` is the colimit
of the `H²(Γ/V)`) and the elementary fact that the `𝔽₂`-dimension of a filtered colimit of vector
spaces of dimension `≤ r` is at most `r`. -/
def ContH2UniformBoundBridge (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] :
    Prop :=
  ∀ r : ℕ, (∃ U : OpenNormalSubgroup Γ, ∀ V : OpenNormalSubgroup Γ, V ≤ U →
      Work.RelatorRank.ContH2DimLe (Γ ⧸ V.toSubgroup) r) →
    Work.RelatorRank.ContH2DimLe Γ r

/-- **Bridge 2.**  A *uniform* family of presentations of the finite quotients of `Γ` (the same
number `d` of generators, the same bound `r` on the relators, for all quotients below some open
normal `U`) produces a presentation of `Γ` on `d` generators with at most `r` relators.

This is the classical "inverse limit of the presentations" construction of a pro-`p` presentation
(Koch, *Galois theory of `p`-extensions*, Ch. 11; Neukirch--Schmidt--Wingberg I §4.3): the relation
kernels of the finite quotients are the images of the relation kernel of `Γ`, their intersection
over the cofinal system is that kernel, and the uniformity is what makes a single relator set
suffice.  In the *pro-`p* category this is where the completed group algebra `𝔽_p[[Γ]]` and the free
pro-`p` group are used, neither of which is available here; the finite index/multiplicative
structures the workspace *does* have (`Work.ShafarevichKoch.ProTwoClosed`) are the closest
formalisation of the "closed" normalisation, together with the residual-`p`-finiteness needed to
pass to the discrete normalisation of `HasProP2Presentation`. -/
def RelatorRankUniformBridge (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] :
    Prop :=
  ∀ (d r : ℕ), Work.RelatorRank.HasDenseGeneratingFamily Γ d →
    (∃ U : OpenNormalSubgroup Γ, ∀ V : OpenNormalSubgroup Γ, V ≤ U →
      Work.RelatorRank.HasProP2Presentation (Γ ⧸ V.toSubgroup) d r) →
    Work.RelatorRank.HasProP2Presentation Γ d r

/-- **The composition.**  If the two bridges hold for `Γ`, and the finite-level dictionary holds for
every finite quotient of `Γ` (that is: for every finite quotient `Q = Γ ⧸ V` on `d` generators,
`dim_{𝔽₂} H²(Q,𝔽₂) ≤ r` produces a presentation of `Q` on `d` generators with at most `r`
relators -- the `∃`-direction of `GaschutzDictionary`, at the finite level), then the *uniform*
cohomological bound on the finite quotients produces a presentation of `Γ`.

This two-line consequence is recorded so that a consumer sees precisely which three inputs are
needed; the proof is by the definitions, and it uses no `sorry`. -/
theorem hasProP2Presentation_of_uniform_quotient_bounds {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] (hsup : RelatorRankUniformBridge Γ)
    (hfinite : ∀ (V : OpenNormalSubgroup Γ) (d r : ℕ),
      Work.RelatorRank.HasDenseGeneratingFamily (Γ ⧸ V.toSubgroup) d →
      Work.RelatorRank.ContH2DimLe (Γ ⧸ V.toSubgroup) r →
        Work.RelatorRank.HasProP2Presentation (Γ ⧸ V.toSubgroup) d r)
    {d r : ℕ} (hd : Work.RelatorRank.HasDenseGeneratingFamily Γ d)
    (h : ∃ U : OpenNormalSubgroup Γ, ∀ V : OpenNormalSubgroup Γ, V ≤ U →
      Work.RelatorRank.ContH2DimLe (Γ ⧸ V.toSubgroup) r) :
    Work.RelatorRank.HasProP2Presentation Γ d r := by
  obtain ⟨U, hU⟩ := h
  refine hsup d r hd ⟨U, fun V hV => ?_⟩
  refine hfinite V d r ?_ (hU V hV)
  exact Work.RelatorRank.GeneratorRank.hasDenseGeneratingFamily_of_continuous_surjective
    (QuotientGroup.mk' V.toSubgroup) continuous_quotient_mk' (QuotientGroup.mk'_surjective _) hd

end Work.HopfGaschutz
