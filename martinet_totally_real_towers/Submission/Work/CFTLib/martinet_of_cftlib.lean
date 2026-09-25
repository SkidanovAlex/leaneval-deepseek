import Mathlib
import Submission.CFTLib.Interfaces
import Submission.Work.WingbergEndgame.Defs
import Submission.Work.WingbergEndgame.certificate_quotient_six
import Submission.Work.WingbergEndgame.isPGroup_of_finite_galoisGroup
import Submission.Work.WingbergEndgame.Endgame
import Submission.NumberField.UnramifiedPro2Assembly
import Submission.Work.ProPGS.Unconditional
import Submission.Work.ProPDeficiency.Specialisations
import Submission.Work.RelatorRank.CohomologyH2
import Submission.Work.HopfGaschutz.CohomologicalDictionary
import Submission.Work.QuadraticFields.CertificateRealSummary
import Submission.Work.CFTLib.finrank_groupCohomology_one_le_dGens
import Submission.Work.CFTLib.finrank_groupCohomology_two_eq_log_card_contH2
import Submission.Work.CFTLib.shafBound_eval_gsF

/-!
# Martinet's asymptotically good totally real towers, from the shared CFT interfaces

**Namespace** `Work.CFTLib`; module `Submission.Work.CFTLib.martinet_of_cftlib`.

We prove

`Work.CFTLib.martinet_of_cftlib (h1 : CFTLib.ShafBound) (h2 : CFTLib.MaximalClassCond) : Benchmark`,

i.e. Martinet's theorem (`Submission.exists_totallyReal_discr_le`) with the two shared
class-field-theory inputs of `Submission/CFTLib/Interfaces.lean` assumed as hypotheses.

## The route

Let `F = gsF = ℚ(√(5·13·17·29·37·41·53))`, the totally real quadratic field of
`Work.QuadraticFields`, and let `E` be the **wide** maximal pro-`2` extension of `F`, i.e. the
maximal pro-`2` Galois extension unramified at every place, finite and infinite
(`Work.WingbergEndgame.UnramifiedProTwoExtension F`, whose existence needs no class field theory:
`Work.WingbergEndgame.exists_unramifiedProTwoExtension`).  Write `Γ = Gal(E.K/F)`.

* If `Γ` were finite, then `E.K/F` would be a finite Galois extension, `E.K` a number field,
  `Γ` a finite `2`-group, `E.K/F` unramified at every place (finite and infinite), and `E.K/F`
  maximal among such (`E.universal`).  So `h2 : MaximalClassCond` gives the class condition and
  `h1 : ShafBound` gives
  `dim H²(Γ,𝔽₂) ≤ dim H¹(Γ,𝔽₂) + (r₁ + r₂ - 1) + δ₂(F) + 0 = dim H¹(Γ,𝔽₂) + 2`
  (`r₁ = 2`, `r₂ = 0` for the real quadratic field `F`, and `δ₂(F) = 1` since `-1` is a primitive
  square root of unity in `F`); see `shafBound_eval_gsF`.

* The genus certificate `gsM/gsF` (`Work.QuadraticFields.gs_certificate`) is an everywhere
  unramified Galois extension of `F` of degree `2 ^ 6` with `Gal(gsM/F) = (ℤ/2)^6`
  (`Work.WingbergEndgame.certificate_quotient_six`), so `Γ` has a continuous surjection onto
  `(ℤ/2)^6` and hence at least `6` generators
  (`Work.ProPDeficiency.le_dGens_of_surjective_zmod_two`).

* The finite `2`-group Golod--Shafarevich inequality
  (`Work.ProPGS.proPGolodShafarevich`) says `4 · dim H²(Γ,𝔽₂) > d(Γ)²` for the minimal number
  `d(Γ)` of generators, where `dim H²(Γ,𝔽₂)` is the workspace's continuous cohomology
  (`Work.RelatorRank.contH2`) read through the relation-rank dictionary
  (`Work.HopfGaschutz.h2DimOf_eq_log_card_contH2`).  Since `4 (d + 2) ≤ d²` for `d ≥ 6`, this
  contradicts the bound above (`false_of_finite_twoGroup_cohomology`).  The bridge from Mathlib's
  abstract group cohomology -- the language of `CFTLib.ShafBound` -- to the workspace's is
  `finrank_groupCohomology_two_eq_log_card_contH2` and `finrank_groupCohomology_one_le_dGens`
  (for a *finite* group the abstract and the continuous theory agree: every cochain is locally
  constant).

* Hence `Γ` is infinite and
  `Submission.NumberField.exists_totallyReal_discr_le_of_infinite_unramified_protwo`
  (`Work.WingbergEndgame.exists_totallyReal_discr_le_of_infinite`) produces the required family of
  totally real fields with bounded root discriminant.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Classical
open NumberField

namespace Work.CFTLib

noncomputable section

/-! ## 1. From a minimal generating finset to a minimal generating family -/

/-- A minimal generating finset `S` of a group `Q` gives a minimal generating family indexed by
`Fin S.card` (`Work.ProPGS.IsMinimalGeneratingFamily`, the input of the pro-`p`
Golod--Shafarevich inequality). -/
theorem exists_isMinimalGeneratingFamily_fin {Q : Type*} [Group Q] (S : Finset Q)
    (hS : Work.ProPDeficiency.IsMinimalGeneratingSet S) :
    ∃ gen : Fin S.card → Q, Work.ProPGS.IsMinimalGeneratingFamily gen := by
  classical
  refine ⟨fun i => ((Finset.equivFin S).symm i : Q), ?_, ?_⟩
  · have hrange : Set.range (fun i : Fin S.card => ((Finset.equivFin S).symm i : Q))
        = (S : Set Q) := by
      ext q
      constructor
      · rintro ⟨i, rfl⟩
        exact ((Finset.equivFin S).symm i).2
      · intro hq
        exact ⟨Finset.equivFin S ⟨q, hq⟩, by simp⟩
    rw [hrange]
    exact hS.1
  · intro T hT
    rw [Fintype.card_fin]
    exact hS.2 T hT

/-! ## 2. The finite `2`-group endgame -/

/-- **No finite `2`-group satisfies the Shafarevich bound with `δ + r₁ + r₂ - 1 + |T| = 2` and
has at least six generators.**

Let `Γ` be a finite `2`-group (discrete topology) whose second group cohomology with trivial
`𝔽₂`-coefficients is at most `dim H¹ + 2` dimensional (the conclusion of `CFTLib.ShafBound` at
`gsF`, `p = 2`, `T = ∅`).  If `Γ` has at least `6` generators, then we get a contradiction:

* Mathlib's abstract `H²(Γ,𝔽₂)` is the workspace's continuous `H²(Γ,𝔽₂)`
  (`finrank_groupCohomology_two_eq_log_card_contH2`), which is the relation rank of a minimal
  presentation (`Work.HopfGaschutz.h2DimOf_eq_log_card_contH2`), whence Golod--Shafarevich
  (`Work.ProPGS.proPGolodShafarevich`) gives `4 · dim H²(Γ,𝔽₂) > d²` for `d = dGens Γ`;
* `dim H¹(Γ,𝔽₂) ≤ d` (`finrank_groupCohomology_one_le_dGens`);
* so `d² < 4 (d + 2)`, while `6 ≤ d` gives `4 (d + 2) ≤ d²`. -/
theorem false_of_finite_twoGroup_cohomology (Γ : Type) [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [DiscreteTopology Γ] [Fintype Γ] [Nontrivial Γ]
    (hpg : IsPGroup 2 Γ) (h6 : 6 ≤ Work.ProPDeficiency.dGens Γ)
    (hb : Module.finrank (ZMod 2)
        (groupCohomology (Rep.trivial (ZMod 2) Γ (ZMod 2)) 2) ≤
      Module.finrank (ZMod 2)
        (groupCohomology (Rep.trivial (ZMod 2) Γ (ZMod 2)) 1) + 2) :
    False := by
  classical
  -- a minimal generating finset, and the induced minimal generating family
  obtain ⟨S, hSmin, hScard⟩ :=
    Work.ProPDeficiency.exists_minimalGeneratingSet (G := Γ) (Group.fg_of_finite)
  obtain ⟨gen, hgen⟩ := exists_isMinimalGeneratingFamily_fin S hSmin
  -- the free group carries the discrete topology, so that the workspace's cohomology applies
  letI : TopologicalSpace (FreeGroup (Fin S.card)) := ⊥
  haveI : DiscreteTopology (FreeGroup (Fin S.card)) := ⟨rfl⟩
  -- Golod--Shafarevich
  have hgs := Work.ProPGS.proPGolodShafarevich 2 (Fin S.card) Γ hpg gen hgen
  simp only [Fintype.card_fin] at hgs
  -- the relation rank is the dimension of `H²`
  have hmin' : Work.HopfGaschutz.presKernel gen ≤ Work.HopfGaschutz.relFrattini 2 ⊤ :=
    Work.HopfGaschutz.le_relFrattini_of_minimal_generating hpg gen hgen.1
      (fun T hT => by simpa using hgen.2 T hT)
  have hval := Work.HopfGaschutz.h2DimOf_eq_log_card_contH2 gen hgen.1 hmin'
  -- the cohomological bound on `H¹`
  have hH1 : Module.finrank (ZMod 2)
      (groupCohomology (Rep.trivial (ZMod 2) Γ (ZMod 2)) 1) ≤ S.card := by
    have h := finrank_groupCohomology_one_le_dGens Γ
    rw [← hScard] at h
    exact h
  -- Golod--Shafarevich in the language of `dim H²`
  have hGS : S.card ^ 2 < 4 * Module.finrank (ZMod 2)
      (groupCohomology (Rep.trivial (ZMod 2) Γ (ZMod 2)) 2) := by
    have h := hgs
    rw [hval, ← finrank_groupCohomology_two_eq_log_card_contH2 Γ] at h
    exact h
  have hbound : 4 * Module.finrank (ZMod 2)
      (groupCohomology (Rep.trivial (ZMod 2) Γ (ZMod 2)) 2) ≤ 4 * (S.card + 2) := by
    omega
  have h6' : 6 ≤ S.card := by omega
  have hle : 4 * (S.card + 2) ≤ S.card ^ 2 := by
    nlinarith [sq_nonneg ((S.card : ℤ) - 6)]
  omega

/-! ## 3. Martinet's theorem from the shared CFT interfaces -/

/-- **Martinet's asymptotically good totally real towers**, from the two shared class-field-theory
interfaces `CFTLib.ShafBound` and `CFTLib.MaximalClassCond`.

There is `C > 0` such that for every `N` there is a totally real number field `K` of degree `≥ N`
with `|disc K| ≤ C ^ [K : ℚ]`. -/
theorem martinet_of_cftlib (h1 : CFTLib.ShafBound) (h2 : CFTLib.MaximalClassCond) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d := by
  -- the wide maximal pro-`2` extension of the totally real quadratic field `gsF`
  obtain ⟨E⟩ :=
    Work.WingbergEndgame.exists_unramifiedProTwoExtension Work.WingbergEndgame.gsF
  refine Work.WingbergEndgame.exists_totallyReal_discr_le_of_infinite E ?_
  -- suppose `Γ = Gal(E.K/F)` were finite
  by_contra hcon
  haveI hfin : Finite (Work.WingbergEndgame.galoisGroup E) := not_infinite_iff_finite.mp hcon
  haveI : Fintype (Work.WingbergEndgame.galoisGroup E) := Fintype.ofFinite _
  haveI hfd : FiniteDimensional ↥Work.QuadraticFields.gsF E.K :=
    IsGalois.finiteDimensional_of_finite ↥Work.QuadraticFields.gsF E.K
  -- `Γ` is a `2`-group and has at least six generators, by the genus certificate `gsM/gsF`
  have hpg : IsPGroup 2 (Work.WingbergEndgame.galoisGroup E) :=
    Work.WingbergEndgame.isPGroup_of_finite_galoisGroup E hfin
  obtain ⟨φ, hφsurj, -⟩ := Work.WingbergEndgame.certificate_quotient_six E
  haveI : Nontrivial (Work.WingbergEndgame.galoisGroup E) := hφsurj.nontrivial
  have h6 : 6 ≤ Work.ProPDeficiency.dGens (Work.WingbergEndgame.galoisGroup E) :=
    Work.ProPDeficiency.le_dGens_of_surjective_zmod_two φ hφsurj
  -- the Shafarevich bound, evaluated at `gsF`, `p = 2`, `T = ∅`
  exact false_of_finite_twoGroup_cohomology (Work.WingbergEndgame.galoisGroup E) hpg h6
    (shafBound_eval_gsF h1 h2 E hfin)

end

end Work.CFTLib
