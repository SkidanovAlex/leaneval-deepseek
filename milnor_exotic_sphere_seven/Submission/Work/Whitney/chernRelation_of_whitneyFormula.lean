import Mathlib
import Submission.Work.LerayHirsch.SplitLines
import Submission.Work.LerayHirsch.SplitsOverProj
import Submission.Work.LerayHirsch.LH
import Submission.Work.LerayHirsch.paracompactSpace_projSpace
import Submission.Work.LerayHirsch.t2Space_projSpace
import Submission.Work.Whitney.ChernProduct
import Submission.Work.Whitney.ChernRelDefs
import Submission.Work.Thom.chernClass_eq_zero_of_lt
import Submission.Work.LerayHirsch.whitneySumFormulaOfLerayHirsch
import Submission.Work.Whitney.convSeries_twoTerm_geo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## The Chern series of the tautological line bundle -/

/-- The Chern series of a complex line bundle is the two-term series `1 + z t` with `z = c₁`. -/
theorem chernSeries_tautLine_eq_twoTermSeries {m' : ℕ} {ι : Type} [Fintype ι]
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m' + 1))) ι) :
    Work.LerayHirsch.chernSeries (Work.LerayHirsch.tautLine E)
      = ChernRel.twoTermSeries (Work.LerayHirsch.zeta E) := by
  funext i
  rcases i with _ | _ | i
  · rw [show Work.LerayHirsch.chernSeries (Work.LerayHirsch.tautLine E) 0
        = Work.Thom.chernClass 1 0 (Work.LerayHirsch.tautLine E) from rfl,
      Work.Thom.chernClass_zero_eq_oneH, ChernRel.twoTermSeries_zero]
  · rw [ChernRel.twoTermSeries_one]
    show Work.Thom.chernClass 1 1 (Work.LerayHirsch.tautLine E) = Work.LerayHirsch.zeta E
    rw [Work.LerayHirsch.zeta_eq_chernClass]
    exact (ChernRel.cohTransport_self _ _).symm
  · rw [show Work.LerayHirsch.chernSeries (Work.LerayHirsch.tautLine E) (i + 2)
        = Work.Thom.chernClass 1 (i + 2) (Work.LerayHirsch.tautLine E) from rfl,
      Work.Thom.chernClass_eq_zero_of_lt _ (by omega),
      ChernRel.twoTermSeries_of_two_le _ (by omega)]

/-! ## The bridge: the Chern relation is a convolution with the geometric series -/

/-- General version of the componentwise input of the bridge. -/
theorem cohTransport_zsmul {n n' : ℕ} (h : n = n') (c : ℤ) (x : Coh ℤ n B) :
    cohTransport h (c • x) = c • cohTransport h x := map_zsmul _ c x

/-- The graded cup product is `ZSMul`-linear in its second variable. -/
theorem cupH_zsmul (a b : ℕ) (c : ℤ) (x : Coh ℤ (2 * a) B) (y : Coh ℤ (2 * b) B) :
    Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b) x (c • y)
      = c • Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b) x y :=
  map_zsmul _ c y

/-- The graded cup product is `ZSMul`-linear in its first variable. -/
theorem cupH_zsmul_left (a b : ℕ) (c : ℤ) (x : Coh ℤ (2 * a) B) (y : Coh ℤ (2 * b) B) :
    Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b) (c • x) y
      = c • Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b) x y :=
  LinearMap.congr_fun (map_zsmul (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b)) c x) y

/-- Graded commutativity of `cupH'` in even degrees, with the sign `(-1)^{4ab} = 1`. -/
theorem cupH_comm_even (a b : ℕ) (x : Coh ℤ (2 * a) B) (y : Coh ℤ (2 * b) B) :
    Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b) x y
      = (Nat.add_comm (2 * a) (2 * b)).symm ▸
          (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * b) (2 * a) y x) := by
  have h2 : (-1 : ℤ) ^ ((2 * a) * (2 * b)) = 1 := by
    rw [show (2 * a) * (2 * b) = 2 * (2 * (a * b)) by ring]
    exact Even.neg_one_pow ⟨2 * (a * b), by ring⟩
  have hg := Work.Cohomology.gradedComm ℤ (Work.Whitney.ssB B) (2 * a) (2 * b) x y
  rw [h2, one_smul] at hg
  have key : cohTransport (Nat.add_comm (2 * a) (2 * b))
      (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b) x y)
      = Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * b) (2 * a) y x := by
    rw [← Work.LerayHirsch.eqRec_eq_cohTransport]; exact hg
  calc Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b) x y
      = cohTransport ((Nat.add_comm (2 * a) (2 * b)).trans
          (Nat.add_comm (2 * a) (2 * b)).symm)
          (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b) x y) :=
        (ChernRel.cohTransport_self _ _).symm
    _ = cohTransport ((Nat.add_comm (2 * a) (2 * b)).symm)
          (cohTransport (Nat.add_comm (2 * a) (2 * b))
            (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b) x y)) :=
        (Work.Whitney.cohTransport_trans _ _ _).symm
    _ = cohTransport ((Nat.add_comm (2 * a) (2 * b)).symm)
          (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * b) (2 * a) y x) := by rw [key]
    _ = (Nat.add_comm (2 * a) (2 * b)).symm ▸
          (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * b) (2 * a) y x) :=
        (Work.LerayHirsch.eqRec_eq_cohTransport _ _).symm

/-- **The bridge, term by term.**  The `j`-th summand of the Chern relation is the `j`-th
`convTerm`-summand of `convSeries (geoSeriesOf ζ) (chernSeries π^*E)` at `m`. -/
theorem chernRel_bridge_term {m' : ℕ} {ι : Type} [Fintype ι]
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m' + 1))) ι) (j : Fin (m' + 1 + 1)) :
    Work.Thom.cohTransport
        (by have h := (j : ℕ); omega :
          2 * (((m' + 1) - (j : ℕ)) + (j : ℕ)) = 2 * (m' + 1))
        (((-1 : ℤ) ^ (j : ℕ)) • Work.Whitney.cupChern ((m' + 1) - (j : ℕ)) (j : ℕ)
          ((Work.Thom.CohMap (Work.LerayHirsch.projMap E) ℤ (2 * ((m' + 1) - (j : ℕ)))).hom
            (Work.Thom.chernClass (m' + 1) ((m' + 1) - (j : ℕ)) E))
          (Work.LerayHirsch.zetaPow E (j : ℕ)))
      = Work.LerayHirsch.convTerm
          (ChernRel.geoSeriesOf (Work.LerayHirsch.zeta E))
          (fun i => (Work.Thom.CohMap (Work.LerayHirsch.projMap E) ℤ (2 * i)).hom
            (Work.Thom.chernClass (m' + 1) i E))
          (m' + 1) (j : ℕ) := by
  rw [Work.LerayHirsch.convTerm_pos (by omega : (j : ℕ) ≤ m' + 1)]
  rw [ChernRel.geoSeriesOf_eq_smul, ← ChernRel.zetaPow_eq_zPow E]
  rw [cupH_zsmul_left, cohTransport_zsmul, cohTransport_zsmul]
  rw [Work.Whitney.cupChern_def]
  rw [cupH_comm_even (j : ℕ) ((m' + 1) - (j : ℕ)), Work.LerayHirsch.eqRec_eq_cohTransport]
  repeat rw [Work.Whitney.cohTransport_trans]

/-- **The bridge: the sum of the Chern relation is a `convSeries` coefficient.** -/
theorem chernRel_bridgeSum {m' : ℕ} {ι : Type} [Fintype ι]
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m' + 1))) ι) :
    (Finset.univ : Finset (Fin (m' + 1 + 1))).sum
      (fun j : Fin (m' + 1 + 1) =>
        Work.Thom.cohTransport
          (by have h := (j : ℕ); omega :
            2 * (((m' + 1) - (j : ℕ)) + (j : ℕ)) = 2 * (m' + 1))
          (((-1 : ℤ) ^ (j : ℕ)) • Work.Whitney.cupChern ((m' + 1) - (j : ℕ)) (j : ℕ)
            ((Work.Thom.CohMap (Work.LerayHirsch.projMap E) ℤ (2 * ((m' + 1) - (j : ℕ)))).hom
              (Work.Thom.chernClass (m' + 1) ((m' + 1) - (j : ℕ)) E))
            (Work.LerayHirsch.zetaPow E (j : ℕ))))
      = Work.LerayHirsch.convSeries
          (ChernRel.geoSeriesOf (Work.LerayHirsch.zeta E))
          (fun i => (Work.Thom.CohMap (Work.LerayHirsch.projMap E) ℤ (2 * i)).hom
            (Work.Thom.chernClass (m' + 1) i E))
          (m' + 1) := by
  rw [Finset.sum_congr rfl (fun j _ => chernRel_bridge_term E j)]
  exact Fin.sum_univ_eq_sum_range
      (fun i => Work.LerayHirsch.convTerm
        (ChernRel.geoSeriesOf (Work.LerayHirsch.zeta E))
        (fun i => (Work.Thom.CohMap (Work.LerayHirsch.projMap E) ℤ (2 * i)).hom
          (Work.Thom.chernClass (m' + 1) i E)) (m' + 1) i) (m' + 1 + 1)

/-! ## The target -/

theorem chernRelation_of_whitneyFormula {m : ℕ} (hm : 1 ≤ m)
    (IH : ∀ {m₁ m₂ : ℕ}, m₁ + m₂ ≤ m → ∀ {B : Type} [TopologicalSpace B] [ParacompactSpace B]
      [T2Space B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
      (W₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
      (W₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) (j : ℕ),
      Work.Thom.chernClass (m₁ + m₂) j (Work.Whitney.whitneySum W₁ W₂)
        = Work.Whitney.chernProductSum W₁ W₂ j)
    {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B] {ι : Type} [Fintype ι]
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    (Finset.univ : Finset (Fin (m + 1))).sum
      (fun j : Fin (m + 1) =>
        Work.Thom.cohTransport
          (by have h := (j : ℕ); omega : 2 * ((m - (j : ℕ)) + (j : ℕ)) = 2 * m)
          (((-1 : ℤ) ^ (j : ℕ)) • Work.Whitney.cupChern (m - (j : ℕ)) (j : ℕ)
            ((Work.Thom.CohMap (Work.LerayHirsch.projMap E) ℤ (2 * (m - (j : ℕ)))).hom
              (Work.Thom.chernClass m (m - (j : ℕ)) E))
            (Work.LerayHirsch.zetaPow E (j : ℕ))))
      = 0 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  haveI : ParacompactSpace (Work.LerayHirsch.ProjSpace E) :=
    Work.LerayHirsch.paracompactSpace_projSpace E
  haveI : T2Space (Work.LerayHirsch.ProjSpace E) := Work.LerayHirsch.t2Space_projSpace E
  obtain ⟨Q, ⟨e⟩⟩ := Work.LerayHirsch.splitsOverProj_of_paracompact (m' := m') E
  -- the recursion: the Chern series of `π^*E` is the convolution of `1 + ζt` and that of `Q`
  have hrec : ∀ i, (Work.Thom.CohMap (Work.LerayHirsch.projMap E) ℤ (2 * i)).hom
        (Work.Thom.chernClass (m' + 1) i E)
      = Work.LerayHirsch.convSeries (ChernRel.twoTermSeries (Work.LerayHirsch.zeta E))
          (Work.LerayHirsch.chernSeries Q) i := by
    intro k
    rw [← Work.Thom.chernClass_comap E (Work.LerayHirsch.projMap E)]
    have h1 := Work.Whitney.chernClass_BundleIso_of_eq (by omega : m' + 1 = 1 + m')
      (Work.Thom.bundleComap E (Work.LerayHirsch.projMap E))
      (Work.Whitney.whitneySum (Work.LerayHirsch.tautLine E) Q) e k
    have h2 : Work.Thom.chernClass (1 + m') k
        (Work.Whitney.whitneySum (Work.LerayHirsch.tautLine E) Q)
        = Work.Whitney.chernProductSum (Work.LerayHirsch.tautLine E) Q k :=
      IH (m₁ := 1) (m₂ := m') (by omega) (Work.LerayHirsch.tautLine E) Q k
    have h3 : Work.Whitney.chernProductSum (Work.LerayHirsch.tautLine E) Q k
        = Work.LerayHirsch.convSeries
            (Work.LerayHirsch.chernSeries (Work.LerayHirsch.tautLine E))
            (Work.LerayHirsch.chernSeries Q) k :=
      Work.LerayHirsch.chernProductSum_eq_convSeries (Work.LerayHirsch.tautLine E) Q k
    have h4 : Work.LerayHirsch.chernSeries (Work.LerayHirsch.tautLine E)
        = ChernRel.twoTermSeries (Work.LerayHirsch.zeta E) :=
      chernSeries_tautLine_eq_twoTermSeries E
    rw [h1, h2, h3, h4]
  -- the bridge, then the telescoping of the geometric series
  refine (chernRel_bridgeSum E).trans ?_
  rw [show (fun i => (Work.Thom.CohMap (Work.LerayHirsch.projMap E) ℤ (2 * i)).hom
        (Work.Thom.chernClass (m' + 1) i E))
      = Work.LerayHirsch.convSeries (ChernRel.twoTermSeries (Work.LerayHirsch.zeta E))
          (Work.LerayHirsch.chernSeries Q) from funext hrec]
  rw [← Work.LerayHirsch.convSeries_assoc (ChernRel.geoSeriesOf (Work.LerayHirsch.zeta E))
    (ChernRel.twoTermSeries (Work.LerayHirsch.zeta E)) (Work.LerayHirsch.chernSeries Q) (m' + 1)]
  rw [Work.Whitney.convSeries_comm
      (Work.LerayHirsch.convSeries (ChernRel.geoSeriesOf (Work.LerayHirsch.zeta E))
        (ChernRel.twoTermSeries (Work.LerayHirsch.zeta E)))
      (Work.LerayHirsch.chernSeries Q) (m' + 1),
    ← Work.LerayHirsch.convSeries_assoc (Work.LerayHirsch.chernSeries Q)
      (ChernRel.geoSeriesOf (Work.LerayHirsch.zeta E))
      (ChernRel.twoTermSeries (Work.LerayHirsch.zeta E)) (m' + 1),
    Work.Whitney.convSeries_comm
      (Work.LerayHirsch.convSeries (Work.LerayHirsch.chernSeries Q)
        (ChernRel.geoSeriesOf (Work.LerayHirsch.zeta E)))
      (ChernRel.twoTermSeries (Work.LerayHirsch.zeta E)) (m' + 1),
    Work.Whitney.convSeries_twoTerm_geo (Work.LerayHirsch.zeta E)
      (Work.LerayHirsch.chernSeries Q) m']
  exact Work.Thom.chernClass_eq_zero_of_lt Q (by omega)

end
end Work.Whitney
