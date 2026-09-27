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

/-- The commutator lemma, given the two leafwise hypotheses and the period-density input.

`hPS` is `Work.EKLC7.PeriodSmall`, stated here as a hypothesis so that the assembly can be
checked independently of the (long) product-formula comparison. -/
theorem commutator_step (h5 : Work.EKLContract.P_Leafwise) (h5b : Work.EKLContract.P_Product)
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
  obtain ⟨t0ij, ht0ij⟩ := hHij.2.2
  obtain ⟨t0jk, ht0jk⟩ := hHjk.2.2
  obtain ⟨t0ik, ht0ik⟩ := hHik.2.2
  obtain ⟨t0N, ht0N⟩ := hH.1.2.2
  obtain ⟨t0V1, ht0V1⟩ := hH.2.1.2.2
  obtain ⟨t0V2, ht0V2⟩ := hH.2.2.2.2
  -- the six leafwise systems (C5 existence)
  obtain ⟨⟨νij, Xij, hLij⟩, hPij⟩ := h5 μ (Uij hij) hHij t0ij (hAinv t0ij) ht0ij
  obtain ⟨⟨νjk, Xjk, hLjk⟩, hPjk⟩ := h5 μ (Uij hjk) hHjk t0jk (hAinv t0jk) ht0jk
  obtain ⟨⟨νik, Xik, hLik⟩, hPik⟩ := h5 μ (Uij hik) hHik t0ik (hAinv t0ik) ht0ik
  obtain ⟨⟨νN, XN, hLN⟩, _⟩ := h5 μ (Heis3 hij hjk hik) hH.1 t0N (hAinv t0N) ht0N
  obtain ⟨⟨νV1, XV1, hLV1⟩, _⟩ := h5 μ (VjkIk hjk hik) hH.2.1 t0V1 (hAinv t0V1) ht0V1
  obtain ⟨⟨νV2, XV2, hLV2⟩, _⟩ := h5 μ (VijIk hij hik) hH.2.2 t0V2 (hAinv t0V2) ht0V2
  -- clauses (U4) and (U5) for `ν^{ik}`
  obtain ⟨-, -, -, hU4, hU5, -, -, -, -⟩ := hPik νik Xik hLik
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
  have htriple := ProductTriple h5b μ hAinv hij hjk hik νij νjk νik νN νV1 νV2
    Xij Xjk Xik XN XV1 XV2 hLij hLjk hLik hLN hLV1 hLV2
  -- the small-support descrition of `ν^{ij}` and `ν^{jk}`
  have hsup_ij := SuppSmall h5 μ hErg hij νij Xij hLij hnc1
  have hsup_jk := SuppSmall h5 μ hErg hjk νjk Xjk hLjk hnc2
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
  exact hU4.mpr key

end Work.EKLC7
