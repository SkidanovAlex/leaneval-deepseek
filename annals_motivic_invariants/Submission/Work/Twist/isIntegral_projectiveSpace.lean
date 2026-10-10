import Mathlib
import Submission.Work.Twist.Defs
import Submission.Work.Twist.away_chart_mvPolynomial_X

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open CategoryTheory AlgebraicGeometry
open Work.Twist

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

noncomputable section

open MvPolynomial HomogeneousLocalization

/-! ## `ℙⁿ_𝕜` is integral

The projective space `ℙⁿ_𝕜 = Proj 𝕜[X₀,…,Xₙ]` (standard grading) is irreducible and reduced,
hence integral.

The two components are proved directly.

* **Reducedness** is a *local* property and does not need the chart isomorphisms at all: for any
  graded ring `A` that is reduced, `Proj 𝒜` is reduced, because the stalk at a point `x` is
  `(A_x)_0` (`Proj.stalkIso`), a subring of the localization of `A` at the prime `x`
  (`HomogeneousLocalization.val_injective`), and a localization of a reduced ring is reduced.

* **Irreducibility** uses the generic point: since `A` is a domain, the zero ideal `(0)` is a
  homogeneous *relevant* prime (relevant because `X₀` is a nonzero element of the irrelevant
  ideal), and it lies in every nonempty basic open `D₊(f)` (`D₊(f) ≠ ∅ ↔ f ≠ 0`). Hence every
  nonempty open contains `(0)`, which makes the space irreducible. -/

/-- **`Proj` of a reduced graded ring is reduced.**  The stalk of `Proj 𝒜` at a point `x` is the
degree-zero part `(A_x)_0` of the localization of `A` at the prime `x` (`Proj.stalkIso`), which is
reduced because it embeds (via `HomogeneousLocalization.val`) into the localization `A_x`, and a
localization of a reduced ring is reduced. -/
theorem isReduced_proj_of_isReduced {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] [hred : _root_.IsReduced A] :
    IsReduced (Proj 𝒜) := by
  have hAtPrime : ∀ (p : Ideal A) [hp : p.IsPrime],
      _root_.IsReduced (HomogeneousLocalization.AtPrime 𝒜 p) := by
    intro p hp
    exact isReduced_of_injective (algebraMap _ _) (by
      rw [show (⇑(algebraMap (HomogeneousLocalization.AtPrime 𝒜 p) (Localization p.primeCompl)))
          = HomogeneousLocalization.val from
          funext (fun y => HomogeneousLocalization.algebraMap_apply y)]
      exact HomogeneousLocalization.val_injective _)
  haveI : ∀ x : ↥(Proj 𝒜), _root_.IsReduced ↑((Proj 𝒜).presheaf.stalk x) := by
    intro x
    haveI hp : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
    exact isReduced_of_injective
      ((Proj.stalkIso 𝒜 x).commRingCatIsoToRingEquiv.toRingHom)
      (Proj.stalkIso 𝒜 x).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _

/-- **`Proj` of a graded domain with nonzero irrelevant ideal is irreducible.**  The zero ideal is a
relevant homogeneous prime, and it lies in every nonempty basic open: `f` is in `(0)` only if
`f = 0`, and `D₊(0) = ∅`.  So every nonempty open contains `(0)` and any two nonempty opens
meet. -/
theorem irreducibleSpace_proj_of_isDomain {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] [IsDomain A]
    (hirr : ¬ (HomogeneousIdeal.irrelevant 𝒜 ≤ (⊥ : HomogeneousIdeal 𝒜))) :
    IrreducibleSpace (Proj 𝒜) := by
  -- the generic point: the zero ideal
  let q : ↥(Proj 𝒜) :=
    ⟨⊥, by rw [HomogeneousIdeal.toIdeal_bot]; exact Ideal.isPrime_bot, hirr⟩
  have hqmem : ∀ f : A, f ≠ 0 → q ∈ Proj.basicOpen 𝒜 f := by
    intro f hf
    rw [Proj.mem_basicOpen]
    intro hcon
    apply hf
    have h3 : f ∈ (⊥ : Ideal A) := hcon
    simpa using h3
  have key : ∀ U : (Proj 𝒜).Opens, U.1.Nonempty → q ∈ U := by
    intro U hU
    obtain ⟨x, hxU⟩ := hU
    obtain ⟨U', hU', hxU', hU'U⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Proj.isBasis_basicOpen 𝒜)) hxU
    obtain ⟨f, rfl⟩ := hU'
    have hfnz : f ≠ 0 := by
      intro hf
      rw [hf, Proj.basicOpen_zero] at hxU'
      simpa using hxU'
    exact hU'U (hqmem f hfnz)
  haveI : PreirreducibleSpace (Proj 𝒜) :=
    PreirreducibleSpace.of_forall_nonempty_inter (by
      intro U V hU hV hUne hVne
      exact ⟨q, key ⟨U, hU⟩ hUne, key ⟨V, hV⟩ hVne⟩)
  exact ⟨⟨q⟩⟩

/-- The standard graded polynomial ring `𝕜[X₀,…,Xₙ]` has nonzero irrelevant ideal: `X₀` is a
nonzero element of degree one. -/
theorem irrelevant_homogeneousSubmodule_ne_bot (𝕜 : Type) [CommRing 𝕜] [Nontrivial 𝕜] (n : ℕ) :
    ¬ (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜) ≤
        (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜))) := by
  intro h
  have hmem := HomogeneousIdeal.mem_irrelevant_of_mem
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜) (show 0 < 1 by norm_num)
    (MvPolynomial.isHomogeneous_X 𝕜 (0 : Fin (n + 1)))
  have h2 := h hmem
  have h3 : MvPolynomial.X (0 : Fin (n + 1)) ∈
      (⊥ : Ideal (MvPolynomial (Fin (n + 1)) 𝕜)) := h2
  exact MvPolynomial.X_ne_zero (0 : Fin (n + 1)) h3

theorem irreducibleSpace_projectiveSpace (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    IrreducibleSpace (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)) :=
  irreducibleSpace_proj_of_isDomain _ (irrelevant_homogeneousSubmodule_ne_bot 𝕜 n)

theorem isReduced_projectiveSpace (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    IsReduced (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)) :=
  isReduced_proj_of_isReduced _

/-- **`ℙⁿ_𝕜` is integral** (irreducible and reduced).  This is the remaining field of
`MotivicInvariants.Variety` for `projectiveSpace 𝕜 n` whose other fields are already available
(`Work.PointlessIndexFive.Model`: `IsProper`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`,
together with the `Over` instance `projectiveSpaceOver`), so it yields an unconditional
`Variety 𝕜 (ℙⁿ)` and removes the hypothesis `GeometricallyIntegral` from
`Work.PointlessIndexFive.variety_projectiveSpace` at this level.

Route: `IsIntegral X ↔ IrreducibleSpace X ∧ IsReduced X`; the charts `D₊(X_i)` cover `ℙⁿ`
(`Proj.iSup_basicOpen_eq_top`), each is `Spec (Away 𝒜 X_i) ≅ Spec 𝕜[y₁,…,yₙ]`
(`Twist.away_chart_mvPolynomial_X`), i.e. an integral affine scheme, and any two charts meet
(`D₊(X_i) ∩ D₊(X_j) ≠ ∅`).

* irreducibility: a space covered by irreducible opens with pairwise non-empty intersections is
  irreducible (`Spec` of a domain is irreducible, and the generic point `(0)` lies in every chart of
  `ℙⁿ`);
* reducedness: `isReduced_of_isReduced_stalk` (`AlgebraicGeometry/Properties.lean`), every stalk of
  `ℙⁿ` being the stalk of a chart at a point, i.e. a localization of the domain `𝕜[y₁,…,yₙ]`.

For `n = 0` the single chart `D₊(X_0)` is all of `Proj 𝕜[X₀] ≅ Spec 𝕜`. -/
theorem isIntegral_projectiveSpace (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    IsIntegral (Work.PointlessIndexFive.projectiveSpace 𝕜 n) := by
  change IsIntegral (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜))
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  exact ⟨irreducibleSpace_projectiveSpace 𝕜 n, isReduced_projectiveSpace 𝕜 n⟩

end

end Work.Twist
