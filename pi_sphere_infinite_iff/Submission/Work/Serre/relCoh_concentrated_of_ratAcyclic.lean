import Mathlib
import Submission.Work.Serre.Defs
import Submission.Work.Serre.EulerFibreRoot
import Submission.Work.Serre.ratCoh_ratH_iso_rat
import Submission.Work.Serre.pathConnectedSpace_of_ratAcyclic
import Submission.Work.Thom.Cohomology
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.diskPairCohomologyTop
import Submission.Work.Cohomology.epi_singularCohomologyMap_zero
import Submission.Work.Cohomology.isZeroRelCohomologyZero
import Submission.Work.Serre.epi_singularCohomologyMap_zero_rat
import Submission.Work.Serre.isZeroRelCohomologyZero_rat

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-!
# The rational relative cohomology of a rationally acyclic space modulo a rational sphere

The long exact sequence of the pair `(P,Q)` together with the rational acyclicity of `P` shows
that the rational relative cohomology `H^j(P,Q;ℚ)` is concentrated in degree `r+1` (through degree
`N+1`), where `H_*(Q;ℚ)` is concentrated (through degree `N`).  This is the "geometric input" of
subproject SERRE (`Work.Serre.ratHypotheses`).

The proof is the long exact sequence of the pair, in the three degree ranges:

* degree `0`: `H⁰(P,Q;ℚ) = 0` because `P` is path connected (it is rationally acyclic) and `Q` is
  nonempty (`isZeroRelCohomologyZero_rat`);
* degree `1`: `H¹(P,Q;ℚ)` is the cokernel of the restriction `H⁰(P;ℚ) → H⁰(Q;ℚ)`
  (`relCohomologyOne_iso_coker_rat`), which vanishes because `Q` is path connected
  (`epi_singularCohomologyMap_zero_rat`);
* degrees `j ≥ 2` and `j = r+1`: the connecting map `H^{j-1}(Q;ℚ) → H^j(P,Q;ℚ)` is an isomorphism
  (`pairδ_isIso_rat`) since `H^*(P;ℚ)` vanishes in positive degrees; the source vanishes for
  `j ≤ N+1`, `j ≠ r+1` (rational universal coefficients), and is a line for `j = r+1`.
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## The connecting map of the pair when the outer terms vanish -/

/-- **The connecting map of the pair is an isomorphism when the outer terms vanish** (rational
coefficients): if `H^{m+1}(X;ℚ) = H^m(X;ℚ) = 0` then
`pairδ : H^m(A;ℚ) ⟶ H^{m+1}(X,A;ℚ)` is an isomorphism.  The rational version of
`Work.Cohomology.pairδ_isIso`. -/
theorem pairδ_isIso_rat (X : TopCat) (A : Set X) (m : ℕ)
    (h1 : IsZero (Work.Cohomology.singularCohomology ℚ (m + 1) X))
    (h2 : IsZero (Work.Cohomology.singularCohomology ℚ m X)) :
    IsIso (Work.Cohomology.pairδ ℚ X A m) := by
  have hmono : Mono (Work.Cohomology.pairδ ℚ X A m) := by
    have hf : (ShortComplex.mk (HomologicalComplex.homologyMap (Work.Cohomology.restr ℚ X A) m)
        (Work.Cohomology.pairδ ℚ X A m) (Work.Cohomology.pair_comp_δ ℚ X A m)).f = 0 :=
      h2.eq_of_src _ 0
    exact (ShortComplex.exact_iff_mono _ hf).mp (Work.Cohomology.pair_exact₃ ℚ X A m)
  have hepi : Epi (Work.Cohomology.pairδ ℚ X A m) := by
    have hg : (ShortComplex.mk (Work.Cohomology.pairδ ℚ X A m)
        (HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℚ X A) (m + 1))
        (Work.Cohomology.pairδ_comp ℚ X A m)).g = 0 := h1.eq_of_tgt _ 0
    exact (ShortComplex.exact_iff_epi _ hg).mp (Work.Cohomology.pair_exact₁ ℚ X A m)
  exact isIso_of_mono_of_epi _

/-! ## Degree one: the relative group as a cokernel -/

/-- **`H¹(X,A;ℚ)` is the cokernel of the restriction `H⁰(X;ℚ) ⟶ H⁰(A;ℚ)`** when
`H¹(X;ℚ) = 0`.  The rational version of `Work.Cohomology.relCohomologyOne_iso_coker`. -/
theorem relCohomologyOne_iso_coker_rat (X : TopCat) (A : Set X)
    (h : IsZero (Work.Cohomology.singularCohomology ℚ 1 X)) :
    Nonempty ((Work.Cohomology.relComplex ℚ X A).homology 1 ≅
      cokernel (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of A) X
        (Work.Cohomology.subtypeIncl X A) 0)) := by
  have hδepi : Epi (Work.Cohomology.pairδ ℚ X A 0) := by
    have hg : (ShortComplex.mk (Work.Cohomology.pairδ ℚ X A 0)
        (HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℚ X A) 1)
        (Work.Cohomology.pairδ_comp ℚ X A 0)).g = 0 := h.eq_of_tgt _ 0
    exact (ShortComplex.exact_iff_epi _ hg).mp (Work.Cohomology.pair_exact₁ ℚ X A 0)
  have hsurj : Function.Surjective (ModuleCat.Hom.hom (Work.Cohomology.pairδ ℚ X A 0)) :=
    (ModuleCat.epi_iff_surjective _).mp hδepi
  have hrange : (ModuleCat.Hom.hom
        (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of A) X
          (Work.Cohomology.subtypeIncl X A) 0)).range
      = (ModuleCat.Hom.hom (Work.Cohomology.pairδ ℚ X A 0)).ker :=
    ShortComplex.Exact.moduleCat_range_eq_ker (Work.Cohomology.pair_exact₃ ℚ X A 0)
  have hex : Function.Exact
      (ModuleCat.Hom.hom (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of A) X
        (Work.Cohomology.subtypeIncl X A) 0))
      (ModuleCat.Hom.hom (Work.Cohomology.pairδ ℚ X A 0)) :=
    LinearMap.exact_iff.mpr hrange.symm
  exact ⟨IsColimit.coconePointUniqueUpToIso
    (ModuleCat.isColimitCokernelCofork
      (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of A) X
        (Work.Cohomology.subtypeIncl X A) 0) (Work.Cohomology.pairδ ℚ X A 0) hex hsurj)
    (colimit.isColimit _)⟩

/-! ## The main theorem -/

theorem relCoh_concentrated_of_ratAcyclic {P : Type} [TopologicalSpace P] (Q : Set P)
    (r N : ℕ) (hr : 1 ≤ r) (hP : Work.Serre.RatAcyclic P) (hQ : PathConnectedSpace ↥Q)
    (hvan : ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N → CategoryTheory.Limits.IsZero
      (Work.Serre.ratH (TopCat.of ↥Q) t))
    (hgen : Nonempty (Work.Serre.ratH (TopCat.of ↥Q) r ≅ ModuleCat.of ℚ ℚ)) :
    (∀ j : ℕ, j ≤ N + 1 → j ≠ r + 1 →
      CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j P Q)) ∧
    Nonempty (Work.Thom.RelCoh ℚ (r + 1) P Q ≅ ModuleCat.of ℚ ℚ) := by
  haveI hpcP : PathConnectedSpace P := pathConnectedSpace_of_ratAcyclic hP
  have hQne : Q.Nonempty := by
    obtain ⟨x⟩ := (PathConnectedSpace.nonempty (X := ↥Q))
    exact ⟨x.1, x.2⟩
  -- rational cohomology of `P` vanishes in positive degrees
  have hPcoh : ∀ n : ℕ, 0 < n →
      IsZero (Work.Cohomology.singularCohomology ℚ n (TopCat.of P)) :=
    fun n hn => isZero_coh_of_ratAcyclic hP hn
  -- rational cohomology of `Q` vanishes in the range (universal coefficients)
  have hQcoh : ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      IsZero (Work.Cohomology.singularCohomology ℚ t (TopCat.of ↥Q)) :=
    fun t ht htr htN => isZero_ratCoh_of_isZero_ratH (hvan t ht htr htN)
  -- and is a line in degree `r`
  have hQline : Nonempty (Work.Cohomology.singularCohomology ℚ r (TopCat.of ↥Q) ≅
      ModuleCat.of ℚ ℚ) :=
    (ratCoh_ratH_iso_rat (TopCat.of ↥Q) r).mpr hgen
  -- degrees `≥ 2`: the connecting map identifies `H^{n+1}(P,Q)` with `H^n(Q)`
  have hstep : ∀ n : ℕ, 1 ≤ n → n + 1 ≤ N + 1 → n + 1 ≠ r + 1 →
      IsZero (Work.Thom.RelCoh ℚ (n + 1) P Q) := by
    intro n hn hnN hnr
    haveI : IsIso (Work.Cohomology.pairδ ℚ (TopCat.of P) Q n) :=
      pairδ_isIso_rat (TopCat.of P) Q n (hPcoh (n + 1) (by omega)) (hPcoh n (by omega))
    have hz : IsZero (Work.Cohomology.singularCohomology ℚ n (TopCat.of ↥Q)) :=
      hQcoh n (by omega) (by omega) (by omega)
    exact IsZero.of_iso hz (asIso (Work.Cohomology.pairδ ℚ (TopCat.of P) Q n)).symm
  -- degree one: `H¹(P,Q)` is the cokernel of `H⁰(P) → H⁰(Q)`, which vanishes
  have hone : IsZero (Work.Thom.RelCoh ℚ 1 P Q) := by
    obtain ⟨e⟩ := relCohomologyOne_iso_coker_rat (TopCat.of P) Q (hPcoh 1 (by omega))
    haveI : PathConnectedSpace (TopCat.of ↥Q) := hQ
    haveI : Epi (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of ↥Q) (TopCat.of P)
        (Work.Cohomology.subtypeIncl (TopCat.of P) Q) 0) :=
      epi_singularCohomologyMap_zero_rat (Work.Cohomology.subtypeIncl (TopCat.of P) Q)
    exact IsZero.of_iso (isZero_cokernel_of_epi (Work.Cohomology.singularCohomologyMap ℚ
      (TopCat.of ↥Q) (TopCat.of P) (Work.Cohomology.subtypeIncl (TopCat.of P) Q) 0)) e
  -- degree zero
  have hzero : IsZero (Work.Thom.RelCoh ℚ 0 P Q) :=
    isZeroRelCohomologyZero_rat (TopCat.of P) Q hQne
  -- degree `r+1`
  have htop : Nonempty (Work.Thom.RelCoh ℚ (r + 1) P Q ≅ ModuleCat.of ℚ ℚ) := by
    haveI : IsIso (Work.Cohomology.pairδ ℚ (TopCat.of P) Q r) :=
      pairδ_isIso_rat (TopCat.of P) Q r (hPcoh (r + 1) (by omega)) (hPcoh r (by omega))
    exact ⟨(asIso (Work.Cohomology.pairδ ℚ (TopCat.of P) Q r)).symm ≪≫ (Classical.choice hQline)⟩
  refine ⟨?_, htop⟩
  intro j hjN hjr
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0; exact hzero
  · rcases eq_or_lt_of_le (show 1 ≤ j from hpos) with h1 | h2
    · subst h1; exact hone
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      exact hstep n (by omega) hjN hjr

end

end Work.Serre
