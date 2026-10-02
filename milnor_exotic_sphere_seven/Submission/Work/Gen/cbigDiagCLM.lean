import Mathlib
import Submission.Work.Gen.EulerModel
import Submission.Work.Gen.Cbig_inv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The diagonal transition of `eulerTarget` is the conjugate of the diagonal scalars

`Work.Gen.cbigDiagCLM`: the transition function of the five-fold sum `eulerTarget` of `ℂ ⊗ O(1)`
from the diagonal index over the chart `i` to the diagonal index over the chart `j` is the
conjugate, by the copy-order shuffle `Work.Gen.CbigCLM`, of the block-diagonal scaling
`diag(z_i/z_j, …, z_j/z_i, …)`.

The proof splits into two halves:

* the *nested* computation: `eulerTarget.coordChange` at the diagonal index is `sumShuffle`-conjugate
  to the nested block-diagonal `T × (T × (T × (T × T)))` where `T = (lineC 4).coordChange (i,i) (j,j)`
  (`conj_prodCongr` is the single-step, purely linear-algebraic identity that drives the induction);
* the *pairing* computation: `pairing`-conjugating the block scaling of `ℂ⁵ × ℂ⁵` gives exactly that
  nested block-diagonal (`pairing_comp_D`).
-/

namespace Work.Gen

open Work.Projective Work.Whitney

noncomputable section

/-! ## The general linear-algebra step: conjugating a product with a nested one -/

/-- **Pushing a product of maps through the splitting.**  For a continuous linear equivalence
`s : A × B ≃L C`, a map `L : A →L A` and a map `M : B' →L B'` glued into `B` along `e₂`, the
conjugate of `L × (e₂ ∘ M ∘ e₂⁻¹)` by `s` is the conjugate of `L × M` by the nested splitting
`(refl × e₂) ≫ s`.  This is the one inductive step of the nested computation. -/
theorem conj_prodCongr {A B B' C : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup B'] [NormedSpace ℂ B']
    [NormedAddCommGroup C] [NormedSpace ℂ C]
    (s : (A × B) ≃L[ℂ] C) (e₂ : B' ≃L[ℂ] B) (L : A →L[ℂ] A) (M : B' →L[ℂ] B') :
    s.toContinuousLinearMap.comp
        ((L.prodMap (e₂.toContinuousLinearMap.comp (M.comp e₂.symm.toContinuousLinearMap))).comp
          s.symm.toContinuousLinearMap)
      = ((((ContinuousLinearEquiv.refl ℂ A).prodCongr e₂).trans s).toContinuousLinearMap).comp
          ((L.prodMap M).comp
            (((((ContinuousLinearEquiv.refl ℂ A).prodCongr e₂).trans s).symm).toContinuousLinearMap)) := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := s.surjective x
  obtain ⟨a, b⟩ := y
  simp [ContinuousLinearMap.comp_apply]

/-! ## The block transition of `lineC 4` -/

/-- The transition function of `lineC 4 = O(1) ⊕ O(-1)` at the diagonal index `(i,i) → (j,j)`. -/
def Tdiag (i j : Fin 5) (b : CP 4) : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (lineC 4).coordChange (i, i) (j, j) b

/-- The `O(1)`-scalar `z_i/z_j`. -/
def hc1 (i j : Fin 5) (b : CP 4) : ℂ := homCoord 4 j i b

/-- The `O(-1)`-scalar `z_j/z_i`. -/
def hc2 (i j : Fin 5) (b : CP 4) : ℂ := homCoord 4 i j b

theorem lineC_coordChange_diag (i j : Fin 5) (b : CP 4) :
    Tdiag i j b = (sumFibreC 1 1).toContinuousLinearMap.comp
      ((((hc1 i j b) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))).prodMap
        ((hc2 i j b) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))).comp
          (sumFibreC 1 1).symm.toContinuousLinearMap) := by
  simp only [Tdiag, hc1, hc2, lineC, whitneySum, sumCore_coordChange,
    tautDual_coordChange, tautLine_coordChange]

/-- The nested splitting `ℂ² × ℂ² → ℂ⁴`. -/
def Y2 : (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)) ≃L[ℂ]
    EuclideanSpace ℂ (Fin (2 + 2)) :=
  sumFibreC 2 2

/-- The nested splitting `ℂ² × (ℂ² × ℂ²) → ℂ⁶`. -/
def Y3 : (EuclideanSpace ℂ (Fin 2) × (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2))) ≃L[ℂ]
    EuclideanSpace ℂ (Fin (2 + (2 + 2))) :=
  (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin 2))) Y2).trans
    (sumFibreC 2 (2 + 2))

/-- The nested splitting `ℂ² × (ℂ² × (ℂ² × ℂ²)) → ℂ⁸`. -/
def Y4 : (EuclideanSpace ℂ (Fin 2) ×
      (EuclideanSpace ℂ (Fin 2) × (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)))) ≃L[ℂ]
    EuclideanSpace ℂ (Fin (2 + (2 + (2 + 2)))) :=
  (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin 2))) Y3).trans
    (sumFibreC 2 (2 + (2 + 2)))

/-- The nested splitting `Nested5 → ℂ¹⁰`; it is the copy-order shuffle `sumShuffle`. -/
def Y5 : Nested5 ≃L[ℂ] EuclideanSpace ℂ (Fin (2 + (2 + (2 + (2 + 2))))) :=
  (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin 2))) Y4).trans
    (sumFibreC 2 (2 + (2 + (2 + 2))))

theorem Y5_eq_sumShuffle : Y5 = sumShuffle := rfl

/-! ## The nested block-diagonal of `Tdiag` -/

def Tprod2 (i j : Fin 5) (b : CP 4) :
    (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)) →L[ℂ]
      (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)) :=
  (Tdiag i j b).prodMap (Tdiag i j b)

def Tprod3 (i j : Fin 5) (b : CP 4) :
    (EuclideanSpace ℂ (Fin 2) × (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2))) →L[ℂ]
      (EuclideanSpace ℂ (Fin 2) × (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2))) :=
  (Tdiag i j b).prodMap (Tprod2 i j b)

def Tprod4 (i j : Fin 5) (b : CP 4) :
    (EuclideanSpace ℂ (Fin 2) ×
      (EuclideanSpace ℂ (Fin 2) × (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)))) →L[ℂ]
      (EuclideanSpace ℂ (Fin 2) ×
      (EuclideanSpace ℂ (Fin 2) × (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)))) :=
  (Tdiag i j b).prodMap (Tprod3 i j b)

def Tprod5 (i j : Fin 5) (b : CP 4) : Nested5 →L[ℂ] Nested5 :=
  (Tdiag i j b).prodMap (Tprod4 i j b)

/-- The `k`-th `ℂ²`-component of the nested block-diagonal is the block itself. -/
theorem nestK_Tprod5 (i j : Fin 5) (b : CP 4) (y : Nested5) (k : Fin 5) :
    nestK k (Tprod5 i j b y) = Tdiag i j b (nestK k y) := by
  fin_cases k <;> simp [Tprod5, Tprod4, Tprod3, Tprod2, nestK]

/-! ## The nested bundles and their diagonal transitions -/

def Eb2 : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin (2 + 2))) (lineIdx × lineIdx) :=
  whitneySum (lineC 4) (lineC 4)

def Eb3 : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin (2 + (2 + 2))))
    (lineIdx × (lineIdx × lineIdx)) :=
  whitneySum (lineC 4) Eb2

def Eb4 : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin (2 + (2 + (2 + 2)))))
    (lineIdx × (lineIdx × (lineIdx × lineIdx))) :=
  whitneySum (lineC 4) Eb3

theorem Eb2_coordChange_diag (i j : Fin 5) (b : CP 4) :
    Eb2.coordChange ((i, i), (i, i)) ((j, j), (j, j)) b =
      Y2.toContinuousLinearMap.comp ((Tprod2 i j b).comp Y2.symm.toContinuousLinearMap) := by
  simp only [Eb2, Y2, Tprod2, Tdiag, whitneySum_coordChange]

theorem Eb3_coordChange_diag (i j : Fin 5) (b : CP 4) :
    Eb3.coordChange ((i, i), ((i, i), (i, i))) ((j, j), ((j, j), (j, j))) b =
      Y3.toContinuousLinearMap.comp ((Tprod3 i j b).comp Y3.symm.toContinuousLinearMap) := by
  rw [Eb3, whitneySum_coordChange, Eb2_coordChange_diag]
  simp only [Y3, Tprod3]
  exact conj_prodCongr (sumFibreC 2 (2 + 2)) Y2 (Tdiag i j b) (Tprod2 i j b)

theorem Eb4_coordChange_diag (i j : Fin 5) (b : CP 4) :
    Eb4.coordChange ((i, i), ((i, i), ((i, i), (i, i))))
        ((j, j), ((j, j), ((j, j), (j, j)))) b =
      Y4.toContinuousLinearMap.comp ((Tprod4 i j b).comp Y4.symm.toContinuousLinearMap) := by
  rw [Eb4, whitneySum_coordChange, Eb3_coordChange_diag]
  simp only [Y4, Tprod4]
  exact conj_prodCongr (sumFibreC 2 (2 + (2 + 2))) Y3 (Tdiag i j b) (Tprod3 i j b)

theorem eulerTarget_coordChange_diag (i j : Fin 5) (b : CP 4) :
    eulerTarget.coordChange (diagIdx i) (diagIdx j) b =
      sumShuffle.toContinuousLinearMap.comp
        ((Tprod5 i j b).comp sumShuffle.symm.toContinuousLinearMap) := by
  have hY : eulerTarget.coordChange (diagIdx i) (diagIdx j) b =
      Y5.toContinuousLinearMap.comp ((Tprod5 i j b).comp Y5.symm.toContinuousLinearMap) := by
    change (whitneySum (lineC 4) Eb4).coordChange
        ((i, i), ((i, i), ((i, i), ((i, i), (i, i)))))
        ((j, j), ((j, j), ((j, j), ((j, j), (j, j))))) b =
      Y5.toContinuousLinearMap.comp ((Tprod5 i j b).comp Y5.symm.toContinuousLinearMap)
    rw [whitneySum_coordChange, Eb4_coordChange_diag]
    simp only [Y5, Tprod5]
    exact conj_prodCongr (sumFibreC 2 (2 + (2 + (2 + 2)))) Y4 (Tdiag i j b) (Tprod4 i j b)
  rw [hY, Y5_eq_sumShuffle]

/-! ## The pairing identity -/

/-- The block scaling `(h₁ • id) × (h₂ • id)` on `ℂ⁵ × ℂ⁵`. -/
def Dmap (i j : Fin 5) (b : CP 4) :
    (EuclideanSpace ℂ (Fin 5) × EuclideanSpace ℂ (Fin 5)) →L[ℂ]
      (EuclideanSpace ℂ (Fin 5) × EuclideanSpace ℂ (Fin 5)) :=
  (((homCoord 4 j i b) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 5))).prodMap
    ((homCoord 4 i j b) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 5))))

theorem pairK_smul (k : Fin 5) (c d : ℂ) (u v : EuclideanSpace ℂ (Fin 5)) :
    pairK k (c • u, d • v) =
      (sumFibreC 1 1).toContinuousLinearMap
        (c • (toC1 : ℂ →L[ℂ] EuclideanSpace ℂ (Fin 1)) (coord5 k u),
         d • (toC1 : ℂ →L[ℂ] EuclideanSpace ℂ (Fin 1)) (coord5 k v)) := by
  simp only [pairK, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
  simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  congr 1

theorem pairK_apply' (k : Fin 5) (u v : EuclideanSpace ℂ (Fin 5)) :
    pairK k (u, v) =
      (sumFibreC 1 1).toContinuousLinearMap
        ((toC1 : ℂ →L[ℂ] EuclideanSpace ℂ (Fin 1)) (coord5 k u),
         (toC1 : ℂ →L[ℂ] EuclideanSpace ℂ (Fin 1)) (coord5 k v)) := by
  simp [pairK]

theorem Tdiag_s1 (i j : Fin 5) (b : CP 4)
    (a c : EuclideanSpace ℂ (Fin 1)) :
    Tdiag i j b ((sumFibreC 1 1).toContinuousLinearMap (a, c)) =
      (sumFibreC 1 1).toContinuousLinearMap (hc1 i j b • a, hc2 i j b • c) := by
  rw [lineC_coordChange_diag]
  simp

theorem Dmap_apply (i j : Fin 5) (b : CP 4) (u v : EuclideanSpace ℂ (Fin 5)) :
    Dmap i j b (u, v) = (homCoord 4 j i b • u, homCoord 4 i j b • v) := by
  simp [Dmap]

theorem pairing_comp_Dmap (i j : Fin 5) (b : CP 4) :
    pairing.comp (Dmap i j b) = (Tprod5 i j b).comp pairing := by
  apply ContinuousLinearMap.ext
  intro w
  obtain ⟨u, v⟩ := w
  simp only [ContinuousLinearMap.comp_apply]
  apply cbig_nested_ext
  intro k
  rw [Dmap_apply, cbig_nestK_pairing, nestK_Tprod5, cbig_nestK_pairing,
      pairK_smul, pairK_apply', Tdiag_s1]
  simp only [hc1, hc2]

theorem cbig_conj (i j : Fin 5) (b : CP 4) :
    sumShuffle.toContinuousLinearMap.comp
        ((Tprod5 i j b).comp sumShuffle.symm.toContinuousLinearMap)
      = CbigCLM.comp ((Dmap i j b).comp CbigInv) := by
  have hpair : pairing.comp ((Dmap i j b).comp pairingInv) = Tprod5 i j b := by
    rw [← ContinuousLinearMap.comp_assoc, pairing_comp_Dmap, ContinuousLinearMap.comp_assoc,
      cbig_pairing_comp_pairingInv]
    show Tprod5 i j b ∘SL ContinuousLinearMap.id ℂ Nested5 = Tprod5 i j b
    rw [ContinuousLinearMap.comp_id]
  rw [CbigCLM, CbigInv, ← hpair]
  simp only [ContinuousLinearMap.comp_assoc]

/-! ## The target -/

theorem cbigDiagCLM :
    ∀ (i j : Fin 5) (b : Work.Projective.CP 4),
      b ∈ Work.Projective.chartSet i ∩ Work.Projective.chartSet j →
      Work.Gen.eulerTarget.coordChange (Work.Gen.diagIdx i) (Work.Gen.diagIdx j) b =
        Work.Gen.CbigCLM.comp
          ((((Work.Gen.homCoord 4 j i b) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 5))).prodMap
            ((Work.Gen.homCoord 4 i j b) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 5)))).comp
              Work.Gen.CbigInv) := by
  intro i j b _
  rw [eulerTarget_coordChange_diag]
  exact cbig_conj i j b

end

end Work.Gen
