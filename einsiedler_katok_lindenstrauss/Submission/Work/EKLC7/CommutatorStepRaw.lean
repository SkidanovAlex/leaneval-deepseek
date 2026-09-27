import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLC7.Defs
import Submission.Work.EKLC7.HeisMul
import Submission.Work.EKLC7.HeisShift
import Submission.Work.EKLC7.Horo
import Submission.Work.EKLC7.HeisFactor
import Submission.Work.EKLC7.ProductInstances
import Submission.Work.EKLC7.ProductTriple
import Submission.Work.EKLC7.CoordTest
import Submission.Work.EKLC7.CoordTrip
import Submission.Work.EKLC7.SepL2c
import Submission.Work.EKLC7.SupportFacts
import Submission.Work.EKLC7.SuppSmall
import Submission.Work.EKLC7.SuppSmallDerive
import Submission.Work.EKLC7.FiberRel
import Submission.Work.EKLC7.PerSub
import Submission.Work.EKLC7.RootSupp
import Submission.Work.EKLC7.FiberRelIter
import Submission.Work.EKLC7.PeriodSmallIter
import Submission.Work.EKLContract.Lemmas.Uij_range
import Submission.Work.EKLContract.Lemmas.Box1_Uij
import Submission.Work.EKLContract.Lemmas.isHoro_Uij

/-!
# C7, the commutator lemma: the assembly

EKL Lemma 3.3 (= Einsiedler–Katok, Lemma 6.1; Pisa 9.11): if `μ` is an `A`-ergodic probability
measure on `X₃ = SL₃(ℝ)/SL₃(ℤ)` and neither `U_ij` nor `U_jk` is a `μ`-cross-section, then `μ` is
`U_ik`-invariant.

The proof is the one written out in `ROUTE_LEAD.md` §C7:

1. `P_Leafwise` gives leafwise measures `ν^{ij}`, `ν^{jk}`, `ν^{ik}`, `ν^N`, `ν^{U_jk U_ik}`,
   `ν^{U_ij U_ik}` for the six groups of the Heisenberg configuration `⟨U_ij, U_jk, U_ik⟩`, and
   their clauses (U3)–(U8);
2. `P_Product` (C5b) gives the two product formulae `TripleA`, `TripleB` for `ν^N`
   (`ProductTriple`); comparing them over the product measure `ν^{ij} ⊗ ν^{jk}` yields the
   translation identity `ν^{ik} · [z₁,z₂] = c · ν^{ik}` (`FiberRel`);
3. (U5) turns proportionality into invariance, and `PeriodSmall` shows that the periods contain
   non-zero elements of arbitrarily small modulus;
4. a subgroup of `ℝ` containing such elements is all of `ℝ` (`PerSub`), so the leafwise measure
   `ν^{ik}` is invariant under every right translation by `U_ik`;
5. (U4) converts a.e. invariance of the leafwise measures into `U_ik`-invariance of `μ`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

namespace Work.EKLC7

open Work.EKLC7

/-- **C7, assembled from the leafwise-measure input in split form.**

* `hEx` is the existence half of C5 (`Work.EKLC7.P_LeafwiseEx`, proved as
  `Work.EKLC7.LeafwiseHoro`): every horospherical subgroup of an `A`-invariant probability
  measure carries leafwise measures;
* `hPr` is the clause list (U3)–(U8) for the one-dimensional root groups
  (`Work.EKLC7.P_RootProps`, proved as `Work.EKLC7.RootPropsC7`);
* `hProd` is C5b (`P_Product`), the product structure of leafwise measures;
* `hPS` is `Work.EKLC7.PeriodSmallIter`, the extraction of arbitrarily small non-trivial
  periods from the commutator-translation identity.

Together with `Work.EKLC7.SuppSmall`/`RootSupp`, `ProductTriple`, `FiberRelIter`, `PerSub` and
the Heisenberg algebra files, this proves `P_Commutator`. -/
theorem commutator_step_raw (hEx : P_LeafwiseEx) (hPr : P_RootProps) (hProd : P_Product)
    (hPS : ∀ {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
      (νij νjk νik : SLm) (c : ℝ),
      νij (Uij hij)ᶜ = 0 → νjk (Uij hjk)ᶜ = 0 →
      CommRel2 νij νjk νik c →
      (∀ u ∈ Uij hik, ∀ c' : ℝ≥0∞, (νik).map (fun g => g * u) = c' • νik →
        (νik).map (fun g => g * u) = νik) →
      (∀ ε : ℝ, 0 < ε → ∃ p : ℝ, p ≠ 0 ∧ |p| ≤ ε ∧ uij hij p ∈ (νij).support) →
      (∃ r : ℝ, r ≠ 0 ∧ uij hjk r ∈ (νjk).support) →
      SmallPeriods hik νik) :
    Work.EKLContract.P_Commutator := by
  intro μ hprob hErg i j k hij hjk hik hnc1 hnc2
  have hAinv : IsAInvariant μ := hErg.1
  -- the horospherical subgroups of the Heisenberg configuration
  have hHij : IsHoro (Uij hij) := Work.EKLContract.Lemmas.isHoro_Uij hij
  have hHjk : IsHoro (Uij hjk) := Work.EKLContract.Lemmas.isHoro_Uij hjk
  have hHik : IsHoro (Uij hik) := Work.EKLContract.Lemmas.isHoro_Uij hik
  have hH := Horo hij hjk hik
  -- the six leafwise systems (existence half of C5)
  obtain ⟨νij, Xij, hLij⟩ := hEx μ hAinv (Uij hij) hHij
  obtain ⟨νjk, Xjk, hLjk⟩ := hEx μ hAinv (Uij hjk) hHjk
  obtain ⟨νik, Xik, hLik⟩ := hEx μ hAinv (Uij hik) hHik
  obtain ⟨νN, XN, hLN⟩ := hEx μ hAinv (Heis3 hij hjk hik) hH.1
  obtain ⟨νV1, XV1, hLV1⟩ := hEx μ hAinv (VjkIk hjk hik) hH.2.1
  obtain ⟨νV2, XV2, hLV2⟩ := hEx μ hAinv (VijIk hij hik) hH.2.2
  -- clauses (U3)-(U8) for `ν^{ik}` (the root-group part of C5's clause list)
  obtain ⟨-, hU4, hU5, -, -⟩ := hPr μ hErg hik νik Xik hLik
  -- the conull domains and the leafwise properties, a.e.
  have hXij : ∀ᵐ x ∂μ, x ∈ Xij := by
    rw [MeasureTheory.ae_iff]; show μ Xijᶜ = 0; exact hLij.conull
  have hXjk : ∀ᵐ x ∂μ, x ∈ Xjk := by
    rw [MeasureTheory.ae_iff]; show μ Xjkᶜ = 0; exact hLjk.conull
  have hXik : ∀ᵐ x ∂μ, x ∈ Xik := by
    rw [MeasureTheory.ae_iff]; show μ Xikᶜ = 0; exact hLik.conull
  have hcar_ij : ∀ᵐ x ∂μ, νij x (Uij hij)ᶜ = 0 := hXij.mono fun x hx => hLij.carried x hx
  have hcar_jk : ∀ᵐ x ∂μ, νjk x (Uij hjk)ᶜ = 0 := hXjk.mono fun x hx => hLjk.carried x hx
  have hfin_ij : ∀ᵐ x ∂μ, IsFiniteMeasureOnCompacts (νij x) := hXij.mono fun x hx => hLij.radon x hx
  have hfin_jk : ∀ᵐ x ∂μ, IsFiniteMeasureOnCompacts (νjk x) := hXjk.mono fun x hx => hLjk.radon x hx
  have hfin_ik : ∀ᵐ x ∂μ, IsFiniteMeasureOnCompacts (νik x) := hXik.mono fun x hx => hLik.radon x hx
  -- the two product formulae (C5b)
  have htriple := ProductTriple hProd μ hAinv hij hjk hik νij νjk νik νN νV1 νV2
    Xij Xjk Xik XN XV1 XV2 hLij hLjk hLik hLN hLV1 hLV2
  -- the small-support descrition of `ν^{ij}` and `ν^{jk}`
  have hsup_ij := RootSupp hPr μ hErg hij νij Xij hLij hnc1
  have hsup_jk := RootSupp hPr μ hErg hjk νjk Xjk hLjk hnc2
  -- the a.e. invariance of `ν^{ik}` under `U_ik`
  have key : ∀ᵐ x ∂μ, ∀ u ∈ Uij hik, (νik x).map (fun g => g * u) = νik x := by
    filter_upwards [htriple, hsup_ij, hsup_jk, hcar_ij, hcar_jk, hfin_ij, hfin_jk, hfin_ik,
      hU5, hXik] with x hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10
    obtain ⟨cA, hcA, cB, hcB, hA, hB⟩ := hx1
    obtain ⟨hne, hball, hno, hsupp⟩ := hx2
    obtain ⟨hne', hball', hno', hsupp'⟩ := hx3
    have hcarik : νik x (Uij hik)ᶜ = 0 := hLik.carried x hx10
    -- step 2: the commutator-translation identity
    have hfib : CommRel2 (νij x) (νjk x) (νik x) (cB / cA) :=
      FiberRelIter hij hjk hik (νij x) (νjk x) (νik x) (νN x) cA cB hx6 hx7 hx8 hx4 hx5 hcarik
        hcA hcB hA hB
    -- step 3: the periods are arbitrarily small
    have hsm : ∀ ε : ℝ, 0 < ε → ∃ p : ℝ, p ≠ 0 ∧ |p| ≤ ε ∧ uij hij p ∈ (νij x).support :=
      exists_small_support hij (νij x) hball hno
    have hps : SmallPeriods hik (νik x) :=
      hPS hij hjk hik (νij x) (νjk x) (νik x) (cB / cA) hx4 hx5 hfib hx9 hsm hsupp'
    -- step 4: all translations preserve `ν^{ik}`
    have hall : ∀ t : ℝ, (νik x).map (fun g => g * uij hik t) = νik x :=
      PerSub hik (νik x) hx8 hps
    -- step 5: translate back to the root group
    intro u hu
    obtain ⟨t, ht⟩ : ∃ t : ℝ, uij hik t = u := (Work.EKLContract.Lemmas.mem_Uij_iff hik u).mp hu
    rw [← ht]
    exact hall t
  -- clause (U4) converts a.e. invariance into `U_ik`-invariance of `μ`
  exact hU4 key

end Work.EKLC7
