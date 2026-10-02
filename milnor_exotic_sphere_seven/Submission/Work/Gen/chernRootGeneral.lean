import Mathlib
import Submission.Work.Gen.chernRootDefs
import Submission.Work.Gen.chernRootTwistTop
import Submission.Work.Whitney.convSeries_comm
import Submission.Work.Whitney.convSeries_unit_right
import Submission.Work.Kunneth.PointTopValue

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-!
# The bookkeeping lemmas of the Chern-root relation

The general facts used in the proof of `Work.Gen.chernRoot_split`:

* `Work.Gen.lhMap_eq_range_sum` — the Leray–Hirsch sum over the index type
  `{i : Fin m // i ≤ m}` as a sum over `Finset.range m`;
* `Work.Gen.lhTerm_def'` — `lhTerm` at the index `k` in `cupChern`-normal form;
* `Work.Gen.convTerm_geo_eq` — the `k`-th term of the convolution with the geometric series in
  `cupChern`-normal form;
* `Work.Gen.CohMap_eSym_eq` — `π^*` of the elementary symmetric class of a family of line bundles;
* `Work.Gen.lhTerm_split_term` — the comparison of the Leray–Hirsch term with the convolution term;
* `Work.Gen.convTerm_geo_top_eSymC` — the top term of the convolution is `(-1)^n ζ^n`;
* `Work.Gen.chernRoot_twistTop_one` — the vanishing of the top Chern class of the twist in rank one.
-/

namespace Work.Gen

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]

/-- The Leray-Hirsch sum over a rank-`n` bundle, as a sum over `range n`. -/
theorem lhMap_eq_range_sum {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (xf : (i : {i : Fin m // (i:ℕ) ≤ m}) → Coh ℤ (2*(m - (i:ℕ))) B) :
    Work.LerayHirsch.lhMap Z m xf
      = ∑ j ∈ Finset.range m,
          (if h : j < m then Work.LerayHirsch.lhTerm Z m ⟨⟨j, h⟩, by omega⟩
            (xf ⟨⟨j, h⟩, by omega⟩) else 0) := by
  rw [Work.LerayHirsch.lhMap_apply]
  rw [show (∑ j ∈ Finset.range m,
        (if h : j < m then Work.LerayHirsch.lhTerm Z m ⟨⟨j, h⟩, by omega⟩
          (xf ⟨⟨j, h⟩, by omega⟩) else 0))
      = ∑ j : Fin m, (fun j' : ℕ => if h : j' < m then Work.LerayHirsch.lhTerm Z m ⟨⟨j', h⟩, by omega⟩
          (xf ⟨⟨j', h⟩, by omega⟩) else 0) ↑j from
    (Fin.sum_univ_eq_sum_range (fun j' : ℕ => if h : j' < m then
      Work.LerayHirsch.lhTerm Z m ⟨⟨j', h⟩, by omega⟩
        (xf ⟨⟨j', h⟩, by omega⟩) else 0) m).symm]
  rw [← Fintype.sum_equiv (Equiv.subtypeUnivEquiv (p := fun i : Fin m => (i:ℕ) ≤ m) (fun i => by omega))
    (fun i : {i : Fin m // (i:ℕ) ≤ m} => Work.LerayHirsch.lhTerm Z m i (xf i))
    (fun j : Fin m => (fun j' : ℕ => if h : j' < m then Work.LerayHirsch.lhTerm Z m ⟨⟨j', h⟩, by omega⟩
        (xf ⟨⟨j', h⟩, by omega⟩) else 0) ↑j)]
  · intro i
    rw [Equiv.subtypeUnivEquiv_apply]
    simp only [dif_pos i.1.isLt]


/-- `lhTerm` at the index `k`, in `cupChern`-normal form. -/
theorem lhTerm_def' {n k : ℕ} (hk : k < n) {ιW : Type} [Fintype ιW]
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ιW) (x : Coh ℤ (2*(n-k)) B) :
    Work.LerayHirsch.lhTerm W n ⟨⟨k, hk⟩, by omega⟩ x
      = cohTransport (by omega : 2 * ((n - k) + k) = 2 * n)
          (Work.Whitney.cupChern (n - k) k
            ((CohMap (Work.LerayHirsch.projMap W) ℤ (2 * (n - k))).hom x)
            ((Work.Whitney.ChernRel.zPow (Work.LerayHirsch.zeta W)) k)) := by
  rw [Work.LerayHirsch.lhTerm_def, Work.Whitney.ChernRel.zetaPow_eq_zPow]

/-- The `k`-th term of the convolution with the geometric series, in `cupChern`-normal form. -/
theorem convTerm_geo_eq {P : Type} [TopologicalSpace P] {n k : ℕ} (hk : k ≤ n)
    (E : (j : ℕ) → Coh ℤ (2*j) P) (z : Coh ℤ 2 P) :
    Work.LerayHirsch.convTerm (Work.Whitney.ChernRel.geoSeriesOf z) E n k
      = (-1 : ℤ) ^ k • cohTransport (by omega : 2 * ((n - k) + k) = 2 * n)
          (Work.Whitney.cupChern (n - k) k (E (n - k))
            ((Work.Whitney.ChernRel.zPow z) k)) := by
  have hG : Work.Whitney.ChernRel.geoSeriesOf z k = (-1 : ℤ) ^ k • (Work.Whitney.ChernRel.zPow z) k :=
    Work.Whitney.ChernRel.geoSeriesOf_eq_smul z k
  rw [Work.Whitney.ChernRel.convTerm_eq_cupChern hk]
  rw [hG, Work.Kunneth.cupChern_zsmul_left]
  rw [Work.Thom.cohTransport_zsmul]
  rw [Work.Whitney.ChernRel.cupChern_comm]
  rw [Work.Whitney.cohTransport_trans]
  try rw [Work.LerayHirsch.cohTransport_congr_proof _ (by omega : 2 * ((n - k) + k) = 2 * n)]

/-- `π^*` of the elementary symmetric class of a family of line bundles is the `eSymC` of the
pulled-back first Chern classes. -/
theorem CohMap_eSym_eq {n m : ℕ} {ιM : Type} [Fintype ιM] {P : Type} [TopologicalSpace P]
    (π : C(P, B)) (L : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιM) :
    (CohMap π ℤ (2*m)).hom (Work.Gen.eSym n L m)
      = eSymC (P := P) n (fun i => (CohMap π ℤ 2).hom (Work.Thom.chernClass 1 1 (L i))) m :=
  (congrArg (fun y => (CohMap π ℤ (2*m)).hom y) (eSym_eq_eSymC L m)).trans
    (eSymC_CohMap (P := P) (Q := B) π (fun i => Work.Thom.chernClass 1 1 (L i)) m).symm

end

end Work.Gen

namespace Work.Gen

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]

/-- **The term of the Leray–Hirsch sum at index `k`**, compared with the `k`-th term of the
convolution of the geometric series with the elementary symmetric class. -/
theorem lhTerm_split_term {n : ℕ} (hn : 1 ≤ n) {ιW : Type} [Fintype ιW]
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ιW)
    (M : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (k : ℕ) (hk : k < n) :
    Work.LerayHirsch.lhTerm W n ⟨⟨k, hk⟩, by omega⟩
        ((fun i : {i : Fin n // (i:ℕ) ≤ n} =>
            ((-1 : ℤ) ^ (n + 1 + (i:ℕ))) • Work.Gen.eSym n M (n - (i:ℕ))) ⟨⟨k, hk⟩, by omega⟩)
      = (-1 : ℤ) ^ (n + 1) •
        Work.LerayHirsch.convTerm
          (Work.Whitney.ChernRel.geoSeriesOf (Work.LerayHirsch.zeta W))
          (fun j => eSymC (P := Work.LerayHirsch.ProjSpace W) n
            (fun i => (CohMap (Work.LerayHirsch.projMap W) ℤ 2).hom
              (Work.Thom.chernClass 1 1 (M i))) j)
          n k := by
  have hG : Work.Whitney.ChernRel.geoSeriesOf (Work.LerayHirsch.zeta W) k
      = (-1 : ℤ) ^ k • (Work.Whitney.ChernRel.zPow (Work.LerayHirsch.zeta W)) k :=
    Work.Whitney.ChernRel.geoSeriesOf_eq_smul (Work.LerayHirsch.zeta W) k
  rw [show ((fun i : {i : Fin n // (i:ℕ) ≤ n} =>
        ((-1 : ℤ) ^ (n + 1 + (i:ℕ))) • Work.Gen.eSym n M (n - (i:ℕ))) ⟨⟨k, hk⟩, by omega⟩)
      = ((-1 : ℤ) ^ (n + 1 + k)) • Work.Gen.eSym n M (n - k) from rfl]
  rw [Work.Kunneth.lhTerm_zsmul]
  rw [lhTerm_def' hk W (Work.Gen.eSym n M (n - k))]
  rw [CohMap_eSym_eq (Work.LerayHirsch.projMap W) M]
  rw [convTerm_geo_eq (Nat.le_of_lt hk)
    (fun j => eSymC (P := Work.LerayHirsch.ProjSpace W) n
      (fun i => (CohMap (Work.LerayHirsch.projMap W) ℤ 2).hom
        (Work.Thom.chernClass 1 1 (M i))) j)
    (Work.LerayHirsch.zeta W)]
  rw [smul_smul]
  congr 1
  rw [← pow_add]


/-- The `k`-th term of the convolution with the geometric series is `(-1)^k ζ^k` at the top index. -/
theorem convTerm_geo_top_eSymC {P : Type} [TopologicalSpace P] {n : ℕ}
    (t : Fin n → Coh ℤ 2 P) (z : Coh ℤ 2 P) :
    Work.LerayHirsch.convTerm (Work.Whitney.ChernRel.geoSeriesOf z)
        (fun k => eSymC (P := P) n t k) n n = (-1 : ℤ) ^ n • (Work.Whitney.ChernRel.zPow z) n := by
  have hE0 : eSymC (P := P) n t 0 = Work.Cohomology.oneH ℤ (Work.Whitney.ssB P) := by
    rw [eSymC_zero_index]
    exact (Work.LerayHirsch.cohTransport_congr_proof _ (by omega : 0 = 2 * 0)).trans
      (Work.Thom.cohTransport_rfl _)
  have hnn : n - n = 0 := Nat.sub_self n
  have hser : eSymC (P := P) n t (n - n)
      = cohTransport (congrArg (fun t : ℕ => 2 * t) hnn.symm)
          (eSymC (P := P) n t 0) :=
    (Work.Whitney.cohTransport_congrArg_series hnn.symm (fun k => eSymC (P := P) n t k)).symm
  rw [convTerm_geo_eq (le_refl n)]
  congr 1
  rw [hser, hE0]
  rw [Work.Kunneth.cupChern_cohTransport_left (h := congrArg (fun t : ℕ => 2 * t) hnn.symm)
    (x := Work.Cohomology.oneH ℤ (Work.Whitney.ssB P))
    (y := (Work.Whitney.ChernRel.zPow z) n)]
  rw [Work.Whitney.cohTransport_trans]
  rw [Work.LerayHirsch.cohTransport_congr_proof _ (by omega : 2 * (0 + n) = 2 * n)]
  exact Work.LerayHirsch.cohTransport_cupChern_one_left n ((Work.Whitney.ChernRel.zPow z) n)

/-- The top Chern class of the twist vanishes in rank one as well. -/
theorem chernRoot_twistTop_one {B : Type} [TopologicalSpace B] {ιW : Type} [Fintype ιW]
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιW) :
    Work.Thom.chernClass 1 1 (twistTautTop W) = 0 := by
  obtain ⟨σ, hσ1, _⟩ := Work.LerayHirsch.exists_tautSection (m := 0) W
  rw [show twistTautTop W = Work.LerayHirsch.tautTwist W from rfl]
  rw [Work.Whitney.chernClass_eq_of_nowhereZeroSection (Work.LerayHirsch.tautTwist W) σ hσ1 1]
  exact Work.Thom.chernClass_eq_zero_of_lt _ (by omega)

end

end Work.Gen
