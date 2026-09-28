import Mathlib
import Submission.Work.Rat.s1Full
import Submission.Work.Rat.s1Sphere
import Submission.Work.Serre.ratSerrePairComparison
import Submission.Work.Stems.HurewiczFirstDegree
import Submission.Work.Stems.HurewiczSphere
import Submission.Work.Stems.Hurewicz
import Submission.Work.StemsB.PiMap
import Submission.Work.Rat.fibreAcyclicOfTwoColumn
import Submission.Work.Rat.truncationComparison
import Submission.Work.Stems.rankOneOddFree_of_serreE3b
import Submission.Work.StemsB.rangeModel_ratH_iso
import Submission.Work.Rat.U.C3
import Submission.Work.Serre.E3aModel
import Submission.Work.Serre.serreE0Range
import Submission.Work.Stems.fibreOfHomeomorphLoopSpace
import Submission.Work.Stems.isHurewiczFibration_homotopyFibreFst
import Submission.Work.StemsB.contractible_pathSpace
import Submission.Work.StemsB.isSerreFibration_evalOne
import Submission.Work.Rat.finitePiRatHVanishing
import Submission.Work.Stems.product_ratH_vanishing
import Submission.Work.Serre.serreS2OfC0C2oddS1

/-!
# `Work.Rat.torsionAboveHoleE3b`

This is `Work.Rat.torsionAboveHole` with the Gysin-periodicity slot replaced by Serre's Euler-class
statement `Work.Serre.SerreE3b`, which is a *hypothesis* of the area contract.  The cell-comparison
content of Serre's E3(b) (`Rat/Neut/*`, `Rat/Cap/*`, `Serre/CellCrux/*`, `Serre/gysinTowerPeriodic`,
`Serre/gysinPeriodicityHom`, `Stems/ThomCellStep/*`) is not imported at all: the whole slot is the
single proved term

  `Work.Rat.rangeModelAcyclicOddUnbounded_of_rankOne (Work.Stems.rankOneOddFree_of_serreE3b hE3b)`.

Everything else is a verbatim copy of the proof of `Work.Rat.torsionAboveHole`.
-/

namespace Work.Rat

open CategoryTheory CategoryTheory.Limits

/-- **Bounded form of "an acyclic base forces an acyclic fibre".**  If `p : E → B` is a Serre
fibration over a simply connected base `B` (trivial `πᵢ` for `i < b`), `E` is rationally acyclic
and `B` is rationally acyclic up to degree `Nc`, then the fibre of `p` is rationally acyclic up to
degree `Nc - 1`.  Verbatim copy of the private helper of `Work.Rat.torsionAboveHole`. -/
private theorem acyclic_fibre_range
    (hcell : Work.Serre.RatCellStepSharp) (hpb : Work.Serre.RatPullbackComparison)
    (htow : Work.Serre.RatTowerComparison)
    {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (hp : Work.StemsB.IsSerreFibration p) (b₀ : B) (b : ℕ) (hb : 2 ≤ b)
    [PathConnectedSpace E] [PathConnectedSpace B]
    [PathConnectedSpace (Work.StemsB.fibre p b₀)]
    (hconn : ∀ i : ℕ, i < b → Subsingleton (HomotopyGroup (Fin i) B b₀))
    (Nc : ℕ)
    (hEac : ∀ i : ℕ, 0 < i → IsZero (Work.Serre.ratH (TopCat.of E) i))
    (hBac : ∀ i : ℕ, 0 < i → i ≤ Nc → IsZero (Work.Serre.ratH (TopCat.of B) i)) :
    ∀ j : ℕ, 0 < j → j + 1 ≤ Nc →
      IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hjNc
    have hfib : ∀ i : ℕ, 0 < i → i < j →
        IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) i) :=
      fun i hi hij => ih i hij hi (by omega)
    have hcmp := (Work.Serre.ratSerrePairComparison_of_inputs hcell hpb htow p hp b₀ b j hb hj
      (inferInstance) (inferInstance) hconn (inferInstance) hfib).1 (j + 1) (by omega)
    have hBrel : IsZero
        ((Work.StemsB.relChainsR ℚ (TopCat.of B) ({b₀} : Set B)).homology (j + 1)) :=
      Work.StemsB.isZero_relChainsR_homology_succ_of_isIso ℚ (TopCat.of B) ({b₀} : Set B) j
        (IsZero.isIso (Work.Cohomology.homologyContractible_ring ℚ
          (X := TopCat.of ↥({b₀} : Set B)) (j + 1) (by omega)) (hBac (j + 1) (by omega) hjNc) _)
        (IsZero.isIso (Work.Cohomology.homologyContractible_ring ℚ
          (X := TopCat.of ↥({b₀} : Set B)) j hj) (hBac j hj (by omega)) _)
    have hrel : IsZero
        ((Work.StemsB.relChainsR ℚ (TopCat.of E) (p ⁻¹' {b₀})).homology (j + 1)) :=
      IsZero.of_iso hBrel hcmp.some
    have hS := Work.StemsB.relChainsR_exact₁ ℚ (TopCat.of E) (p ⁻¹' {b₀}) j
    exact hS.isZero_X₂ (IsZero.eq_zero_of_src hrel _) (IsZero.eq_zero_of_tgt (hEac j hj) _)



/-- Finiteness of a homotopy group transported along an equality of the indices. -/
private theorem fintype_of_index_eq {X : Type} [TopologicalSpace X] {x : X} {a b : ℕ} (h : a = b)
    (H : Nonempty (Fintype (HomotopyGroup (Fin a) X x))) :
    Nonempty (Fintype (HomotopyGroup (Fin b) X x)) := by
  subst h; exact H


/-! ## The E3(b)-powered range-model vanishing

The whole Gysin-periodicity slot of `Work.Rat.torsionAboveHole` is replaced by the single proved
term built from `Work.Stems.rankOneOddFree_of_serreE3b` and the Postnikov truncation comparison
`Work.Rat.truncationComparison`.  The assembly `rangeModelAcyclicOddUnbounded_of` is restated here
so that we do not depend on the module `Submission.Work.Rat.rangeModelAcyclicOddUnbounded`, which
imports a sorry-carrying file owned by a live agent. -/

/-- **The rank-one range-model vanishing, assembled from the rank-one `K(A,·)` computation.**  This
is a verbatim restatement of `Work.Rat.rangeModelAcyclicOddUnbounded_of` (the composition of the
rank-one computation with the Postnikov truncation comparison `Work.Rat.truncationComparison`),
inlined so that the module `Rat/rangeModelAcyclicOddUnbounded.lean` need not be imported. -/
private theorem rankOneRangeModelVanishing (hrank : Work.Rat.RankOneOddFree 1)
    {d M : ℕ} (hd : 3 ≤ d) (hodd : Odd d) {Z : Type} [TopologicalSpace Z] (z₀ : Z)
    (hZ : ∀ j : ℕ, j ≤ M + 1 → j ≠ d → Subsingleton (HomotopyGroup (Fin j) Z z₀))
    (hgen : Nonempty (Work.Serre.ratH (TopCat.of Z) d ≅ ModuleCat.of ℚ ℚ)) :
    ∀ j : ℕ, d < j → j ≤ M + 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of Z) j) := by
  intro j hdj hjM
  have hlt : d < M + 1 := lt_of_lt_of_le hdj hjM
  obtain ⟨P, tP, p₀, hPmod, hPgen, hcmp⟩ :=
    Work.Rat.truncationComparison hd (by omega) z₀ hZ hgen
  have hzeroP : CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of P) j) :=
    hrank d (M + 1 + d) hd hodd p₀ hPmod hPgen j hdj (by omega)
  obtain ⟨e⟩ := hcmp j hjM
  exact CategoryTheory.Limits.IsZero.of_iso hzeroP e

/-- The rank-one range-model vanishing from Serre's Euler-class statement `E3(b)` alone. -/
private theorem rangeModelVanishingLocal (hE3b : Work.Serre.SerreE3b) {d M : ℕ} (hd : 3 ≤ d)
    (hodd : Odd d) {Z : Type} [TopologicalSpace Z] (z₀ : Z)
    (hZ : ∀ j : ℕ, j ≤ M + 1 → j ≠ d → Subsingleton (HomotopyGroup (Fin j) Z z₀))
    (hgen : Nonempty (Work.Serre.ratH (TopCat.of Z) d ≅ ModuleCat.of ℚ ℚ)) :
    ∀ j : ℕ, d < j → j ≤ M + 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of Z) j) :=
  rankOneRangeModelVanishing (Work.Stems.rankOneOddFree_of_serreE3b hE3b) hd hodd z₀ hZ hgen

/-- **The `(d-1)`-connected case of `torsionAboveHoleE3b`.**  A `(d-1)`-connected space `X`
(`d ≥ 3` odd) whose rational homology is that of `S^d` in degrees `≤ M` has torsion homotopy groups
above the hole.  Verbatim copy of the private helper of `Work.Rat.torsionAboveHole`, with `hE3b`
threaded to the range-model vanishing. -/
private theorem connectedCaseOdd (hE3b : Work.Serre.SerreE3b) {d M : ℕ} (hd : 3 ≤ d) (hodd : Odd d)
    {X : Type} [TopologicalSpace X] (x₀ : X)
    (hconn : ∀ i : ℕ, i < d → Subsingleton (HomotopyGroup (Fin i) X x₀))
    (hSph : ∀ y₀ : Work.Serre.Sph d, Work.Serre.PiTorsion (Work.Serre.Sph d) y₀ d)
    (hfg : ∀ (a : ℕ) [Nonempty (Fin a)], a ≤ M → Group.FG (HomotopyGroup (Fin a) X x₀))
    (hvan : ∀ i : ℕ, 0 < i → i ≤ M → i ≠ d →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) i))
    (hgen : Nonempty (Work.Serre.ratH (TopCat.of X) d ≅ ModuleCat.of ℚ ℚ)) :
    ∀ j : ℕ, d < j → j ≤ M → Work.Serre.PiTorsion X x₀ (j - 1) := by
  intro j hj hjM
  -- the `d`-truncation of `X` through degree `M + 2`
  obtain ⟨P, tP, g, hg1, hg2⟩ := Work.Serre.serrePostnikovTower d (M + 2) X x₀ (by omega)
  letI : TopologicalSpace P := tP
  haveI hXpc : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x₀ (hconn 0 (by omega))
  -- `P` is `(d-1)`-connected at `g x₀`
  have hconnP : ∀ i : ℕ, i < d → Subsingleton (HomotopyGroup (Fin i) P (g x₀)) := by
    intro i hi
    exact subsingleton_of_surjective_aux (hconn i hi) (Work.Serre.piMapN g i x₀)
      (hg1 i (le_of_lt hi)).2
  haveI hPpc : PathConnectedSpace P :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero (g x₀) (hconnP 0 (by omega))
  -- `F := homotopyFibre g x₀` is `d`-connected, with `π_i(F) ≅ π_i(X)` for `d < i < M + 2`
  obtain ⟨hcov1, hcov2⟩ :=
    Work.Serre.serreConnectedCover d (M + 2) (by omega) (by omega) X x₀ P g hg1 hg2
  -- `H_d(P;ℚ) ≅ ℚ`: `X` and `P` are range models of the same type through degree `d`
  have hPgen : Nonempty (Work.Serre.ratH (TopCat.of P) d ≅ ModuleCat.of ℚ ℚ) := by
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by omega⟩
    have hXM : Work.Serre.IsEMSpaceUpTo (Additive (HomotopyGroup (Fin (d' + 2)) X x₀))
        (d' + 2) (by omega) (d' + 2) X x₀ :=
      ⟨⟨MulEquiv.refl _⟩, fun i hi hmem => by
        rcases hmem with hlt | hle
        · exact hconn i hlt
        · exact hconn i (lt_of_le_of_ne hle hi)⟩
    have hPN : Work.Serre.IsEMSpaceUpTo (Additive (HomotopyGroup (Fin (d' + 2)) X x₀))
        (d' + 2) (by omega) (d' + 2) P (g x₀) :=
      ⟨⟨(MulEquiv.ofBijective (Work.StemsB.πmap g (d' + 1) x₀) (hg1 (d' + 2) le_rfl)).symm⟩,
        fun i hi hmem => by
        rcases hmem with hlt | hle
        · exact hconnP i hlt
        · exact hconnP i (lt_of_le_of_ne hle hi)⟩
    obtain ⟨e⟩ := Work.StemsB.rangeModel_ratH_iso
      (Additive (HomotopyGroup (Fin (d' + 2)) X x₀))
      (d' + 2) (d' + 2) (by omega) X x₀ hXM P (g x₀) hPN (d' + 2) le_rfl
    exact ⟨e.symm ≪≫ hgen.some⟩
  -- the base `P` has vanishing rational homology in degrees `0 < i ≤ M+1`, `i ≠ d`
  have hPvan : ∀ i : ℕ, 0 < i → i ≤ M + 1 → i ≠ d →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of P) i) := by
    intro i hi0 hiM hid
    rcases lt_or_ge i d with hlt | hge
    · exact Work.Serre.serreE0Range P (g x₀) (d - 1)
        (fun k hk => hconnP k (by omega)) i hi0 (by omega)
    · have hdlt : d < i := lt_of_le_of_ne hge (Ne.symm hid)
      exact rangeModelVanishingLocal hE3b hd hodd (g x₀)
        (fun k hk hkd => by
          by_cases hkd' : k < d
          · exact hconnP k hkd'
          · exact hg2 k (by omega) (by omega) (g x₀))
        hPgen i hdlt (by omega)
  -- the two-column fibre acyclicity
  have hFvan : ∀ i : ℕ, d < i → i ≤ M →
      IsZero (Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre g x₀)) i) :=
    Work.Rat.fibreAcyclicOfTwoColumn g x₀ (g x₀) rfl d M (by omega) hconnP
      (fun i hi => hcov1 i hi) hPvan hPgen hvan hgen
  -- finite generation of the homotopy groups of `F`
  have hFfg : ∀ (a : ℕ) [Nonempty (Fin a)], a ≤ M →
      Group.FG (HomotopyGroup (Fin a) (Work.RatHurewicz.homotopyFibre g x₀)
        (Work.RatHurewicz.homotopyFibreBasepoint g x₀)) := by
    intro a _ haM
    by_cases ha : a ≤ d
    · haveI : Subsingleton (HomotopyGroup (Fin a) (Work.RatHurewicz.homotopyFibre g x₀)
          (Work.RatHurewicz.homotopyFibreBasepoint g x₀)) := hcov1 a ha
      haveI : Finite (HomotopyGroup (Fin a) (Work.RatHurewicz.homotopyFibre g x₀)
          (Work.RatHurewicz.homotopyFibreBasepoint g x₀)) := Finite.of_subsingleton
      exact Group.fg_iff_monoid_fg.mpr Monoid.fg_of_finite
    · have hlt : d < a := Nat.lt_of_not_le ha
      have hbij := hcov2 a hlt (by omega)
      haveI : Nonempty (Fin ((a - 1) + 1)) := ⟨⟨0, by omega⟩⟩
      haveI : Group.FG (HomotopyGroup (Fin ((a - 1) + 1)) X x₀) :=
        fg_of_index_eq (X := X) (x := x₀) (by omega) (hfg a haM)
      let e : HomotopyGroup (Fin ((a - 1) + 1)) (Work.RatHurewicz.homotopyFibre g x₀)
            (Work.RatHurewicz.homotopyFibreBasepoint g x₀) ≃*
          HomotopyGroup (Fin ((a - 1) + 1)) X x₀ :=
        MulEquiv.ofBijective _ hbij
      have hmid : Group.FG (HomotopyGroup (Fin ((a - 1) + 1))
          (Work.RatHurewicz.homotopyFibre g x₀)
          (Work.RatHurewicz.homotopyFibreBasepoint g x₀)) :=
        Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
      exact fg_of_index_eq (X := Work.RatHurewicz.homotopyFibre g x₀)
        (x := Work.RatHurewicz.homotopyFibreBasepoint g x₀) (by omega) hmid
  -- the vanishing Hurewicz theorem on `F`
  have hFtor : ∀ j : ℕ, d < j → j ≤ M →
      Work.Serre.PiTorsion (Work.RatHurewicz.homotopyFibre g x₀)
        (Work.RatHurewicz.homotopyFibreBasepoint g x₀) (j - 1) :=
    Work.Rat.piTorsion_of_ratH_vanishing_full' Work.Serre.serreE3a (d + 1) (by omega)
      (Work.RatHurewicz.homotopyFibre g x₀) (Work.RatHurewicz.homotopyFibreBasepoint g x₀) M
      (fun i hi => hcov1 i (by omega)) hFfg
      (fun i hi _ => hFvan i hi (by omega))
  -- transfer along `π_j(F) ≅ π_j(X)`
  exact Work.Serre.piTorsion_of_surjective_hom
    (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst g x₀) (j - 1)
      (Work.RatHurewicz.homotopyFibreBasepoint g x₀))
    (hcov2 j (by omega) (by omega)).2 (hFtor j hj hjM)


theorem torsionAboveHoleE3b (hE3b : Work.Serre.SerreE3b) {d M : ℕ} (hd : 3 ≤ d) (hodd : Odd d)
    {X : Type} [TopologicalSpace X] (x₀ : X)
    (h01 : Subsingleton (HomotopyGroup (Fin 0) X x₀))
    (h1 : Subsingleton (HomotopyGroup (Fin 1) X x₀))
    (htors : ∀ i : ℕ, 2 ≤ i → i < d → Work.Serre.PiTorsion X x₀ (i - 1))
    (hSph : ∀ y₀ : Work.Serre.Sph d, Work.Serre.PiTorsion (Work.Serre.Sph d) y₀ d)
    (hfg : ∀ (a : ℕ) [Nonempty (Fin a)], a ≤ M → Group.FG (HomotopyGroup (Fin a) X x₀))
    (hvan : ∀ i : ℕ, 0 < i → i ≤ M → i ≠ d →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) i))
    (hgen : Nonempty (Work.Serre.ratH (TopCat.of X) d ≅ ModuleCat.of ℚ ℚ)) :
    ∀ j : ℕ, d < j → j ≤ M → Work.Serre.PiTorsion X x₀ (j - 1) := by
  by_cases hMd : M ≤ d
  · intro j hj hjM; omega
  have hdM : d < M := Nat.lt_of_not_le hMd
  set N : ℕ := M + 10 with hNdef
  have hdN : d - 1 ≤ N := by omega
  obtain ⟨P, tP, g, hg1, hg2⟩ := Work.Serre.serrePostnikovTower (d - 1) N X x₀ hdN
  letI : TopologicalSpace P := tP
  have hP0 : Subsingleton (HomotopyGroup (Fin 0) P (g x₀)) :=
    subsingleton_of_surjective_aux h01 (Work.Serre.piMapN g 0 x₀) (hg1 0 (by omega)).2
  have hP1 : Subsingleton (HomotopyGroup (Fin 1) P (g x₀)) :=
    subsingleton_of_surjective_aux h1 (Work.Serre.piMapN g 1 x₀) (hg1 1 (by omega)).2
  obtain ⟨hcov1, hcov2⟩ :=
    Work.Serre.serreConnectedCover (d - 1) N (by omega) (by omega) X x₀ P g hg1 hg2
  have hfinP : ∀ i : ℕ, 2 ≤ i → i ≤ N →
      Nonempty (Fintype (HomotopyGroup (Fin i) P (g x₀))) := by
    intro i hi2 hiN
    by_cases hid : i ≤ d - 1
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
      haveI : Nonempty (Fin (i' + 2)) := ⟨⟨0, by omega⟩⟩
      have hbij := hg1 (i' + 2) hid
      haveI : Group.FG (HomotopyGroup (Fin (i' + 2)) X x₀) := hfg (i' + 2) (by omega)
      have htor : IsMulTorsion (HomotopyGroup (Fin (i' + 2)) X x₀) := fun a =>
        isOfFinOrder_iff_pow_eq_one.mpr (htors (i' + 2) (by omega) (by omega) a)
      haveI hfinX : Finite (HomotopyGroup (Fin (i' + 2)) X x₀) :=
        CommGroup.finite_of_fg_isMulTorsion _ htor
      exact Work.Rat.fintype_of_bijective_piMapN g (i' + 2) x₀ hbij ⟨Fintype.ofFinite _⟩
    · have hle : d - 1 < i := Nat.lt_of_not_le hid
      haveI : Subsingleton (HomotopyGroup (Fin i) P (g x₀)) := hg2 i hle hiN (g x₀)
      exact ⟨Fintype.ofFinite _⟩
  have hPac : ∀ j : ℕ, 0 < j → j ≤ N → IsZero (Work.Serre.ratH (TopCat.of P) j) :=
    Work.Rat.finitePiRatHVanishing (Work.Rat.rangeEMVanAllFin_reproved Work.Serre.serreE3a)
      P (g x₀) N hP0 hP1 hfinP
  haveI hPpc : PathConnectedSpace P :=
    Work.Serre.serreAux_pathConnected_of_subsingleton_pi_zero (g x₀) hP0
  -- `Ω P` is rationally acyclic
  have hLoopAcyc : ∀ j : ℕ, 0 < j → j ≤ M + 1 →
      IsZero (Work.Serre.ratH (TopCat.of (Path (g x₀) (g x₀))) j) := by
    intro j hj hjM
    haveI : ContractibleSpace (Work.StemsB.PathSpace P (g x₀)) :=
      Work.StemsB.contractible_pathSpace P (g x₀)
    have hEac : ∀ i : ℕ, 0 < i →
        IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.PathSpace P (g x₀))) i) :=
      fun i hi => Work.Cohomology.homologyContractible_ring ℚ
        (X := TopCat.of (Work.StemsB.PathSpace P (g x₀))) i hi
    have hLpc : PathConnectedSpace (Path (g x₀) (g x₀)) :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero (Path.refl (g x₀))
        (Work.Serre.subsingleton_pi0_loopSpace_of_pi1 (g x₀) hP1)
    haveI hFpc : PathConnectedSpace (Work.StemsB.fibre (Work.StemsB.evalOne P (g x₀)) (g x₀)) := by
      refine ⟨⟨(Work.StemsB.fibreEvalOneHomeo P (g x₀)).symm (Path.refl (g x₀))⟩, fun a b => ?_⟩
      obtain ⟨γ⟩ := hLpc.joined ((Work.StemsB.fibreEvalOneHomeo P (g x₀)) a)
        ((Work.StemsB.fibreEvalOneHomeo P (g x₀)) b)
      exact ⟨γ.map (Work.StemsB.fibreEvalOneHomeo P (g x₀)).symm.continuous⟩
    have hconnP : ∀ i : ℕ, i < 2 → Subsingleton (HomotopyGroup (Fin i) P (g x₀)) := by
      intro i hi
      interval_cases i
      · exact hP0
      · exact hP1
    have hres := Work.Rat.acyclic_fibre_range Work.Serre.cellStepSharp
      Work.Serre.ratPullbackComparison Work.Serre.ratTowerComparison
      (Work.StemsB.evalOne P (g x₀)) (Work.StemsB.isSerreFibration_evalOne P (g x₀))
      (g x₀) 2 (by norm_num) hconnP (M + 2) hEac
      (fun i hi hiN => hPac i hi (by omega)) j hj (by omega)
    exact Work.Stems.isZero_ratH_of_homeomorph
      (Work.StemsB.fibreEvalOneHomeo P (g x₀)).symm j hres
  -- E3a: the cover projection `Y' → X` is a rational homology isomorphism up to `M`
  have hIso : ∀ i : ℕ, i ≤ M →
      IsIso (Work.Serre.ratHomologyMap (Work.RatHurewicz.homotopyFibreFst g x₀) i) := by
    intro i hi
    refine Work.Serre.E3aModel.serreE3aFibreAcyclic
      (Work.RatHurewicz.homotopyFibre g x₀) X (Work.RatHurewicz.homotopyFibreFst g x₀) x₀
      (M + 1) ?_ ?_ ?_ ?_ i (by omega)
    · exact (Work.Stems.isHurewiczFibration_homotopyFibreFst g x₀).isSerreFibration
    · exact Work.Serre.serreAux_pathConnected_of_subsingleton_pi_zero x₀ h01
    · intro t ht htle
      obtain ⟨e⟩ := Work.Stems.fibreOfHomeomorphLoopSpace g x₀
      exact Work.Stems.isZero_ratH_of_homeomorph e t (hLoopAcyc t ht (by omega))
    · obtain ⟨e⟩ := Work.Stems.fibreOfHomeomorphLoopSpace g x₀
      haveI : IsIso (Work.Serre.ratHomologyMap e.toHomotopyEquiv.toFun 0) :=
        Work.Serre.IsRatHomologyIso.of_homotopyEquiv e.toHomotopyEquiv 0
      haveI : PathConnectedSpace (Path (g x₀) (g x₀)) :=
        Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero (Path.refl (g x₀))
          (Work.Serre.subsingleton_pi0_loopSpace_of_pi1 (g x₀) hP1)
      exact ⟨(asIso (Work.Serre.ratHomologyMap e.toHomotopyEquiv.toFun 0)).trans
        (Work.Serre.ratH_zero_of_pathConnected (Path (g x₀) (g x₀))).some⟩
  -- assemble the hypotheses for the `(d-1)`-connected case and transfer
  intro j hj hjM
  have hconnY : ∀ i : ℕ, i < d → Subsingleton (HomotopyGroup (Fin i)
      (Work.RatHurewicz.homotopyFibre g x₀) (Work.RatHurewicz.homotopyFibreBasepoint g x₀)) :=
    fun i hi => hcov1 i (by omega)
  have hfgY : ∀ (a : ℕ) [Nonempty (Fin a)], a ≤ M → Group.FG (HomotopyGroup (Fin a)
      (Work.RatHurewicz.homotopyFibre g x₀) (Work.RatHurewicz.homotopyFibreBasepoint g x₀)) := by
    intro a _ haM
    by_cases hle : a ≤ d - 1
    · haveI : Subsingleton (HomotopyGroup (Fin a)
          (Work.RatHurewicz.homotopyFibre g x₀) (Work.RatHurewicz.homotopyFibreBasepoint g x₀)) :=
        hcov1 a hle
      haveI : Finite (HomotopyGroup (Fin a)
          (Work.RatHurewicz.homotopyFibre g x₀) (Work.RatHurewicz.homotopyFibreBasepoint g x₀)) :=
        Finite.of_subsingleton
      exact Group.fg_iff_monoid_fg.mpr Monoid.fg_of_finite
    · have hlt : d - 1 < a := Nat.lt_of_not_le hle
      have hbij := hcov2 a hlt (by omega)
      haveI : Nonempty (Fin ((a - 1) + 1)) := ⟨⟨0, by omega⟩⟩
      haveI : Group.FG (HomotopyGroup (Fin ((a - 1) + 1)) X x₀) :=
        fg_of_index_eq (X := X) (x := x₀) (by omega) (hfg a haM)
      let e : HomotopyGroup (Fin ((a - 1) + 1))
            (Work.RatHurewicz.homotopyFibre g x₀)
            (Work.RatHurewicz.homotopyFibreBasepoint g x₀) ≃*
          HomotopyGroup (Fin ((a - 1) + 1)) X x₀ :=
        MulEquiv.ofBijective _ hbij
      have hmid : Group.FG (HomotopyGroup (Fin ((a - 1) + 1))
          (Work.RatHurewicz.homotopyFibre g x₀)
          (Work.RatHurewicz.homotopyFibreBasepoint g x₀)) :=
        Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
      exact fg_of_index_eq (X := Work.RatHurewicz.homotopyFibre g x₀)
        (x := Work.RatHurewicz.homotopyFibreBasepoint g x₀) (by omega) hmid
  have hvanY : ∀ i : ℕ, 0 < i → i ≤ M → i ≠ d → IsZero (Work.Serre.ratH
      (TopCat.of (Work.RatHurewicz.homotopyFibre g x₀)) i) := by
    intro i hi0 hiM hid
    rcases lt_or_ge i d with hlt | hge
    · exact (Work.Serre.serreE0Range (Work.RatHurewicz.homotopyFibre g x₀)
        (Work.RatHurewicz.homotopyFibreBasepoint g x₀) (d - 1)
        (fun i hi => hcov1 i hi)) i hi0 (by omega)
    · have hdlt : d < i := lt_of_le_of_ne hge (Ne.symm hid)
      haveI : IsIso (Work.Serre.ratHomologyMap (Work.RatHurewicz.homotopyFibreFst g x₀) i) :=
        hIso i (by omega)
      exact IsZero.of_iso (hvan i hi0 hiM hid)
        (asIso (Work.Serre.ratHomologyMap (Work.RatHurewicz.homotopyFibreFst g x₀) i))
  have hgenY : Nonempty (Work.Serre.ratH
      (TopCat.of (Work.RatHurewicz.homotopyFibre g x₀)) d ≅ ModuleCat.of ℚ ℚ) := by
    haveI : IsIso (Work.Serre.ratHomologyMap (Work.RatHurewicz.homotopyFibreFst g x₀) d) :=
      hIso d (by omega)
    exact ⟨(asIso (Work.Serre.ratHomologyMap (Work.RatHurewicz.homotopyFibreFst g x₀) d)).trans
      hgen.some⟩
  have hmain := connectedCaseOdd hE3b hd hodd (Work.RatHurewicz.homotopyFibreBasepoint g x₀)
    hconnY hSph hfgY hvanY hgenY j hj hjM
  exact Work.Serre.piTorsion_of_surjective_hom
    (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst g x₀) (j - 1)
      (Work.RatHurewicz.homotopyFibreBasepoint g x₀))
    (hcov2 j (by omega) (by omega)).2 hmain

end Work.Rat
