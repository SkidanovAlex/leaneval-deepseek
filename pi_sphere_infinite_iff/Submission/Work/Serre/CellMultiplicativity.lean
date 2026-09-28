import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.MixedCup
import Submission.Work.Cohomology.relCupHNatural
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Serre.ModelThomRatPairNeutral
import Submission.Work.Serre.thomCylBaseCase

/-!
# The multiplicative (cup-product) side of the cell step: infrastructure

The additive cell step (`Work.Serre.CsrSharp.Cell.perCellSharp`, `Work.Serre.DiscPair.discCellStep`,
…) is complete.  What the cellular step `Work.Serre.thomCylCellStepAlt` still needs is the
*multiplicative* content: that the mixed cup product behaves naturally under the comparisons used
there.  This file collects that infrastructure.

The first two results are the coefficient-generic (in particular `ℚ`-valued) versions of
`Work.Thom.mixedCupC_pairNatural` and of its chain-level input `Work.Thom.relMapLM_cup`
(`Submission/Work/Thom/mixedCupC_pairNatural.lean`, currently stated over `ℤ` only): the cell step
works over `ℚ`, and every consumer of the naturality there needs the `ℚ` case.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **Chain-level naturality of the mixed Alexander–Whitney product** (arbitrary commutative
coefficients).  Pulling back the product `a ⌣ b` of an absolute cochain `a` with a relative cochain
`b` is the product of the pullbacks. -/
theorem relMapLM_cup_R (R : Type) [CommRing R] {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : ∀ x ∈ A, f x ∈ B) (m n : ℕ)
    (a : Work.Cohomology.Cochain R (TopCat.toSSet.obj (TopCat.of Y)) m)
    (b : Work.Cohomology.relKern R (TopCat.of Y) B n)
    (hmem : Work.Cohomology.cup R (TopCat.toSSet.obj (TopCat.of Y)) a
        (b.1 : Work.Cohomology.Cochain R (TopCat.toSSet.obj (TopCat.of Y)) n) ∈
      Work.Cohomology.relKern R (TopCat.of Y) B (m + n)) :
    (((Work.Cohomology.relMapLM R A B (TopCat.ofHom f) hf (m + n)
        ⟨Work.Cohomology.cup R (TopCat.toSSet.obj (TopCat.of Y)) a
            (b.1 : Work.Cohomology.Cochain R (TopCat.toSSet.obj (TopCat.of Y)) n), hmem⟩))).1 =
      Work.Cohomology.cup R (TopCat.toSSet.obj (TopCat.of X))
        (((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
            (ModuleCat.of R R)).f m).hom.dualMap a)
        (((Work.Cohomology.relMapLM R A B (TopCat.ofHom f) hf n b))).1 := by
  rw [Work.Cohomology.relMapLM_coe, Work.Cohomology.relMapLM_coe]
  simp only [Work.Cohomology.dualChainMap_f_hom, Work.Cohomology.chainMap_f_eq]
  exact (Work.Cohomology.cupNatural R (TopCat.toSSet.map (TopCat.ofHom f)) a b.1).symm

/-- **Naturality of the mixed cup product** (arbitrary commutative coefficients).  For a continuous
map `f : X → Y` carrying `A ⊆ X` into `B ⊆ Y`, an absolute class `x ∈ H^m(Y;R)` and a relative
class `z ∈ H^n(Y,B;R)`, `f^*(x ⌣ z) = (f^*x) ⌣ (f^*z)`; both sides live in `H^{m+n}(X,A;R)`. -/
theorem mixedCupC_pairNatural_R (R : Type) [CommRing R] {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : ∀ x ∈ A, f x ∈ B)
    (m n : ℕ) (x : Work.Thom.Coh R m Y) (z : Work.Thom.RelCoh R n Y B) :
    (Work.Thom.relCohMap f A B hf R (m + n)).hom ((Work.Thom.mixedCupC R B m n) x z)
      = (Work.Thom.mixedCupC R A m n) ((Work.Thom.CohMap f R m).hom x)
          ((Work.Thom.relCohMap f A B hf R n).hom z) := by
  obtain ⟨a, ha, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf R
    (TopCat.toSSet.obj (TopCat.of Y)) m x
  obtain ⟨b, hb, rfl⟩ := Work.Cohomology.exists_relClassOf R (TopCat.of Y) B n z
  obtain ⟨hmemY, hcocY, hcupY⟩ :=
    Work.Serre.mixedCupC_apply R B m n a b ha hb
  have hCoh : (Work.Thom.CohMap f R m).hom
        (Work.Cohomology.cohomologyClassOf R (TopCat.toSSet.obj (TopCat.of Y)) a ha) =
      Work.Cohomology.cohomologyClassOf R (TopCat.toSSet.obj (TopCat.of X))
        (((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
            (ModuleCat.of R R)).f m).hom.dualMap a)
        (Work.Cohomology.cochainDiff_dualMap_chainComplexMap R
          (TopCat.toSSet.map (TopCat.ofHom f)) a ha) :=
    Work.Cohomology.singularCohomologyMap_classOf R (TopCat.ofHom f) a ha
  have hRel := @Work.Cohomology.homologyMap_relComplexMap_relClassOf R _ (TopCat.of X)
    (TopCat.of Y) A B (TopCat.ofHom f) hf n b hb
  obtain ⟨hmemX, hcocX, hcupX⟩ := Work.Serre.mixedCupC_apply R A m n
    (((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
        (ModuleCat.of R R)).f m).hom.dualMap a)
    (@Work.Cohomology.relMapLM R _ (TopCat.of X) (TopCat.of Y) A B (TopCat.ofHom f) hf n b)
    (Work.Cohomology.cochainDiff_dualMap_chainComplexMap R
      (TopCat.toSSet.map (TopCat.ofHom f)) a ha)
    (@Work.Cohomology.relDiffLM_relMapLM R _ (TopCat.of X) (TopCat.of Y) A B
      (TopCat.ofHom f) hf n b hb)
  have hL1 := @Work.Cohomology.homologyMap_relComplexMap_relClassOf R _ (TopCat.of X)
    (TopCat.of Y) A B (TopCat.ofHom f) hf (m + n)
    ⟨Work.Cohomology.cup R (TopCat.toSSet.obj (TopCat.of Y)) a b.1, hmemY⟩ hcocY
  have heq : (@Work.Cohomology.relMapLM R _ (TopCat.of X) (TopCat.of Y) A B (TopCat.ofHom f)
        hf (m + n)
        ⟨Work.Cohomology.cup R (TopCat.toSSet.obj (TopCat.of Y)) a b.1, hmemY⟩)
      = ⟨Work.Cohomology.cup R (TopCat.toSSet.obj (TopCat.of X))
          (((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
              (ModuleCat.of R R)).f m).hom.dualMap a)
          ((@Work.Cohomology.relMapLM R _ (TopCat.of X) (TopCat.of Y) A B (TopCat.ofHom f)
            hf n b).1), hmemX⟩ := by
    apply Subtype.ext
    exact relMapLM_cup_R R f A B hf m n a b hmemY
  rw [hcupY, hL1, hCoh, hRel, hcupX]
  exact Work.Cohomology.relClassOf_congr R (TopCat.of X) A _ _ heq

/-- **The Thom isomorphism over an acyclic base.**

Let `p : E → B` be a Serre fibration, `A = Set.range (cylIncl p)` the bottom copy of the source in
the mapping cylinder, and suppose

* the base is rationally acyclic in positive degrees (`H^n(B;ℚ) = 0` for `0 < n`) with
  `H^0(B;ℚ) ≅ ℚ`;
* the bottom copy has the rational cohomology of the fibre over a point `b₀` (`hAiso`);
* the fibre over `b₀` is path connected and rationally an `r`-sphere through degree `N`.

Then there is `U ∈ H^{r+1}(cyl p, A;ℚ)` whose mixed cup product with the pullback along
`cylRetract p` is an isomorphism in the range `m + r + 1 ≤ N + 1`.

This is the `Work.Serre.thomCylBaseCase` argument (which is the case `B = PUnit`) with the two
uses of "the base is a point" replaced by the explicit hypotheses: `H^n(B) = 0` for `n > 0`
(giving `H^n(cyl p) = 0` for `n > 0` through the pullback isomorphism along `cylInr p`) and
`hAiso` (giving both `H^r(A) ≅ ℚ` and the vanishing of `H^{m+r}(A)` for `m ≥ 1`). -/
theorem thomCylAcyclicBase (r N : ℕ) (hr : 1 ≤ r) {B : Type} [TopologicalSpace B]
    {E : Type} [TopologicalSpace E] (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B)
    (hBvan : ∀ n : ℕ, 0 < n → CategoryTheory.Limits.IsZero (Work.Thom.Coh ℚ n B))
    (hB0 : Nonempty (Work.Thom.Coh ℚ 0 B ≅ ModuleCat.of ℚ ℚ))
    (hAiso : ∀ n : ℕ, Nonempty (Work.Thom.Coh ℚ n ↥(Set.range (Work.Serre.cylIncl p)) ≅
      Work.Thom.Coh ℚ n (Work.StemsB.fibre p b₀)))
    (hfib0 : PathConnectedSpace (Work.StemsB.fibre p b₀))
    (hvan : ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N → CategoryTheory.Limits.IsZero
      (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) t))
    (hgen : Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) r ≅ ModuleCat.of ℚ ℚ)) :
    ∃ U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl p) (Set.range (Work.Serre.cylIncl p)),
      ∀ m : ℕ, m + r + 1 ≤ N + 1 → CategoryTheory.IsIso (ModuleCat.ofHom
        (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl p)) m (r + 1))).flip U ∘ₗ
          (Work.Thom.CohMap (Work.Serre.cylRetract p) ℚ m).hom)) := by
  classical
  set A : Set (Work.Serre.cyl p) := Set.range (Work.Serre.cylIncl p) with hA
  -- ### 1. The cylinder has the cohomology of the base (which is acyclic in positive degrees)
  have hMvan : ∀ n : ℕ, 0 < n → IsZero (Work.Thom.Coh ℚ n (Work.Serre.cyl p)) := by
    intro n hn
    haveI := isIso_cohMap_cylInr p n
    exact IsZero.of_iso (hBvan n hn) (asIso (Work.Thom.CohMap (Work.Serre.cylInr p) ℚ n))
  -- ### 2. The connecting map `δ_r` is bijective
  have hδ : Function.Bijective (Work.StemsB.pairδCR ℚ A r).hom :=
    tcbPairDelta_bijective A r
      (ModuleCat.isZero_iff_subsingleton.mp (hMvan r (by omega)))
      (ModuleCat.isZero_iff_subsingleton.mp (hMvan (r + 1) (by omega)))
  -- ### 3. A generator of `H^r` of the bottom copy
  have hAr : Nonempty (Work.Thom.Coh ℚ r ↥A ≅ ModuleCat.of ℚ ℚ) := by
    obtain ⟨eF⟩ := hgen
    obtain ⟨eAa⟩ := hAiso r
    exact ⟨eAa ≪≫ (Work.StemsB.ratDualUCT
        (Work.Serre.ratChains (TopCat.of (Work.StemsB.fibre p b₀))) r).some
      ≪≫ ratCupAux_dualIsoRat eF⟩
  obtain ⟨eA'⟩ := hAr
  set gen : Work.Thom.Coh ℚ r ↥A := (eA'.inv).hom 1 with hgen_def
  have hgen_ne : gen ≠ 0 := by
    intro h0
    have hinj : Function.Injective (eA'.inv).hom :=
      ((CategoryTheory.ConcreteCategory.isIso_iff_bijective eA'.inv).mp inferInstance).1
    have h1 : (eA'.inv).hom (1 : ℚ) = (eA'.inv).hom 0 := by
      rw [hgen_def] at h0
      rw [h0, map_zero]
    exact one_ne_zero (hinj h1)
  -- ### 4. The class `U`
  set U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl p) A :=
    (Work.StemsB.pairδCR ℚ A r).hom gen with hU_def
  have hUne : U ≠ 0 := by
    intro h0
    rw [hU_def] at h0
    exact hgen_ne (hδ.1 (by rw [h0, map_zero]))
  -- ### 5. Isomorphisms identifying the two sides with `ℚ`
  obtain ⟨e1⟩ := hB0
  have hδIso : IsIso (Work.StemsB.pairδCR ℚ A r) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr hδ
  let δIso : Work.Thom.Coh ℚ r ↥A ≅ Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl p) A :=
    asIso (Work.StemsB.pairδCR ℚ A r)
  let e2' : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl p) A ≅ ModuleCat.of ℚ ℚ :=
    δIso.symm ≪≫ eA'
  let e0 : Work.Thom.RelCoh ℚ (0 + (r + 1)) (Work.Serre.cyl p) A ≅
      Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl p) A :=
    eqToIso (congrArg (fun t => Work.Thom.RelCoh ℚ t (Work.Serre.cyl p) A) (Nat.zero_add (r + 1)))
  let e2 : Work.Thom.RelCoh ℚ (0 + (r + 1)) (Work.Serre.cyl p) A ≅ ModuleCat.of ℚ ℚ :=
    e0 ≪≫ e2'
  -- ### 6. Assembly
  refine ⟨U, fun m hm => ?_⟩
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- ## The case `m = 0`
    subst hm0
    set φ0 : Work.Thom.Coh ℚ 0 B →ₗ[ℚ]
        Work.Thom.RelCoh ℚ (0 + (r + 1)) (Work.Serre.cyl p) A :=
      ((Work.Thom.mixedCupC ℚ A 0 (r + 1))).flip U ∘ₗ
        (Work.Thom.CohMap (Work.Serre.cylRetract p) ℚ 0).hom with hφ0_def
    have hαiso : IsIso (Work.Thom.CohMap (Work.Serre.cylRetract p) ℚ 0) :=
      tcbIsIso_cohMap_cylRetract p 0
    let α : Work.Thom.Coh ℚ 0 B ≅ Work.Thom.Coh ℚ 0 (Work.Serre.cyl p) :=
      asIso (Work.Thom.CohMap (Work.Serre.cylRetract p) ℚ 0)
    set u : Work.Thom.Coh ℚ 0 (Work.Serre.cyl p) :=
      Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of (Work.Serre.cyl p))) with hu_def
    have hxu : (Work.Thom.CohMap (Work.Serre.cylRetract p) ℚ 0).hom (α.inv.hom u) = u := by
      change α.hom.hom (α.inv.hom u) = u
      exact tcbModuleIso_hom_inv_apply α u
    have hunit : (Work.Thom.mixedCupC ℚ A 0 (r + 1)) u U = e0.inv.hom U := by
      rw [Work.StemsB.Rat.mixedCupC_oneH_zeroQ A (r + 1) U]
      exact (tcbRelCohEqToIso_inv_apply A (Nat.zero_add (r + 1)) U).symm
    have hU0ne : e0.inv.hom U ≠ 0 := by
      intro hcon
      have h2 : e0.hom.hom (e0.inv.hom U) = e0.hom.hom 0 :=
        congrArg (fun z => e0.hom.hom z) hcon
      rw [tcbModuleIso_hom_inv_apply e0 U, map_zero] at h2
      exact hUne h2
    have hφ0ne : φ0 ≠ 0 := by
      intro hzero
      have hx : φ0 (α.inv.hom u) = 0 := by
        have hx' := LinearMap.congr_fun hzero (α.inv.hom u)
        simpa using hx'
      have hval : φ0 (α.inv.hom u) = e0.inv.hom U := by
        show (Work.Thom.mixedCupC ℚ A 0 (r + 1))
            ((Work.Thom.CohMap (Work.Serre.cylRetract p) ℚ 0).hom (α.inv.hom u)) U
          = e0.inv.hom U
        rw [hxu, hunit]
      rw [hval] at hx
      exact hU0ne hx
    have hg1 : (e1.inv ≫ (ModuleCat.ofHom φ0 ≫ e2.hom)).hom 1 ≠ 0 := by
      intro h1
      have hg0 : (e1.inv ≫ (ModuleCat.ofHom φ0 ≫ e2.hom)).hom = 0 := by
        apply LinearMap.ext
        intro x
        have hx : (e1.inv ≫ (ModuleCat.ofHom φ0 ≫ e2.hom)).hom x
            = x * ((e1.inv ≫ (ModuleCat.ofHom φ0 ≫ e2.hom)).hom 1) := by
          simpa using map_smul ((e1.inv ≫ (ModuleCat.ofHom φ0 ≫ e2.hom)).hom) x (1 : ℚ)
        rw [hx, h1, mul_zero]
        rfl
      apply hφ0ne
      exact tcbConj_eq_zero φ0 e1 e2 hg0
    have hGeq : e1.inv ≫ (ModuleCat.ofHom φ0 ≫ e2.hom)
        = ModuleCat.ofHom ((e1.inv ≫ (ModuleCat.ofHom φ0 ≫ e2.hom)).hom) :=
      ModuleCat.hom_ext (by rw [ModuleCat.hom_ofHom])
    have hconjIso : IsIso (ModuleCat.ofHom ((e1.inv ≫ (ModuleCat.ofHom φ0 ≫ e2.hom)).hom)) :=
      ratCupAux_isIso_ofHom_rat_ne_zero _
        (ratCupAux_ratEnd_ne_zero_of_apply_one_ne_zero hg1)
    exact ratCupAux_isIso_of_iso_conj_rat (u := e1) (v := e2) (hGeq ▸ hconjIso)
  · -- ## The case `m ≥ 1`
    haveI hdom : Subsingleton ↥(Work.Thom.Coh ℚ m B) :=
      ModuleCat.isZero_iff_subsingleton.mp (hBvan m hmpos)
    haveI hcod : Subsingleton ↥(Work.Thom.RelCoh ℚ (m + (r + 1)) (Work.Serre.cyl p) A) := by
      have hk : 0 < m + r := by omega
      have hkn : m + r ≠ r := by omega
      have hkle : m + r ≤ N := by omega
      have h1 : IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) (m + r)) :=
        hvan (m + r) hk hkn hkle
      have h2 : IsZero (Work.Thom.Coh ℚ (m + r) (Work.StemsB.fibre p b₀)) :=
        isZero_ratCoh_of_isZero_ratH h1
      have h3 : IsZero (Work.Thom.Coh ℚ (m + r) ↥A) :=
        IsZero.of_iso h2 (hAiso (m + r)).some
      have hδk : Function.Bijective (Work.StemsB.pairδCR ℚ A (m + r)).hom :=
        tcbPairDelta_bijective A (m + r)
          (ModuleCat.isZero_iff_subsingleton.mp (hMvan (m + r) (by omega)))
          (ModuleCat.isZero_iff_subsingleton.mp (hMvan (m + r + 1) (by omega)))
      haveI : IsIso (Work.StemsB.pairδCR ℚ A (m + r)) :=
        (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr hδk
      have h4 : IsZero (Work.Thom.RelCoh ℚ (m + r + 1) (Work.Serre.cyl p) A) :=
        IsZero.of_iso h3 (asIso (Work.StemsB.pairδCR ℚ A (m + r))).symm
      have h5 : IsZero (Work.Thom.RelCoh ℚ (m + (r + 1)) (Work.Serre.cyl p) A) := by
        rw [← Nat.add_assoc m r 1]
        exact h4
      exact ModuleCat.isZero_iff_subsingleton.mp h5
    refine (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, ?_⟩
    · intro a b _
      exact Subsingleton.elim a b
    · intro y
      exact ⟨0, Subsingleton.elim _ _⟩


end

end Work.Serre
