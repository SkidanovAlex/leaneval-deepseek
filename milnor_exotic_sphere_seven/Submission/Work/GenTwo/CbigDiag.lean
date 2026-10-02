import Mathlib
import Submission.Work.GenTwo.Model
import Submission.Work.Gen.cbigDiagCLM

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
# The diagonal transition of `Tgt = (ℂ ⊗ O(1))³` is the conjugate of the block scalings

The `n = 2` instance of `Submission/Work/Gen/cbigDiagCLM.lean`: the `CbigCLM`-conjugate of the
block scaling `diag(z_i/z_j, z_j/z_i)` of `ℂ³ × ℂ³` is the transition function of `Tgt` between the
diagonal indices of the charts `i` and `j`.
-/

namespace Work.Gen.E2

open Work.Projective Work.Whitney

noncomputable section

/-! ## The block transition of `lineC 2` -/

/-- The transition function of `lineC 2 = O(1) ⊕ O(-1)` at the diagonal index `(i,i) → (j,j)`. -/
def Tdiag (i j : Fin 3) (b : CP 2) : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (lineC 2).coordChange (i, i) (j, j) b

/-- The `O(1)`-scalar `z_i/z_j`. -/
def hc1 (i j : Fin 3) (b : CP 2) : ℂ := homCoord 2 j i b

/-- The `O(-1)`-scalar `z_j/z_i`. -/
def hc2 (i j : Fin 3) (b : CP 2) : ℂ := homCoord 2 i j b

theorem lineC_coordChange_diag (i j : Fin 3) (b : CP 2) :
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

/-! ## The nested block-diagonal of `Tdiag` -/

def Tprod2 (i j : Fin 3) (b : CP 2) :
    (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)) →L[ℂ]
      (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)) :=
  (Tdiag i j b).prodMap (Tdiag i j b)

def Tprod3 (i j : Fin 3) (b : CP 2) : Nested3 →L[ℂ] Nested3 :=
  (Tdiag i j b).prodMap (Tprod2 i j b)

/-- The `k`-th `ℂ²`-component of the nested block-diagonal is the block itself. -/
theorem nestK_Tprod3 (i j : Fin 3) (b : CP 2) (y : Nested3) (k : Fin 3) :
    nestK k (Tprod3 i j b y) = Tdiag i j b (nestK k y) := by
  fin_cases k <;> simp [Tprod3, Tprod2, nestK]

/-! ## The nested bundles and their diagonal transitions -/

def Eb2 : VectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin (2 + 2))) (Idx2 × Idx2) :=
  whitneySum (lineC 2) (lineC 2)

theorem Eb2_coordChange_diag (i j : Fin 3) (b : CP 2) :
    Eb2.coordChange ((i, i), (i, i)) ((j, j), (j, j)) b =
      Y2.toContinuousLinearMap.comp ((Tprod2 i j b).comp Y2.symm.toContinuousLinearMap) := by
  simp only [Eb2, Y2, Tprod2, Tdiag, whitneySum_coordChange]

theorem Tgt_coordChange_diag (i j : Fin 3) (b : CP 2) :
    Tgt.coordChange (diagIdx i) (diagIdx j) b =
      sumShuffle.toContinuousLinearMap.comp
        ((Tprod3 i j b).comp sumShuffle.symm.toContinuousLinearMap) := by
  have hY : Tgt.coordChange (diagIdx i) (diagIdx j) b =
      sumShuffle.toContinuousLinearMap.comp
        ((Tprod3 i j b).comp sumShuffle.symm.toContinuousLinearMap) := by
    change (whitneySum (lineC 2) Eb2).coordChange
        ((i, i), ((i, i), (i, i)))
        ((j, j), ((j, j), (j, j))) b =
      sumShuffle.toContinuousLinearMap.comp
        ((Tprod3 i j b).comp sumShuffle.symm.toContinuousLinearMap)
    rw [whitneySum_coordChange, Eb2_coordChange_diag]
    simp only [sumShuffle, Tprod3]
    exact Work.Gen.conj_prodCongr (sumFibreC 2 (2 + 2)) Y2 (Tdiag i j b) (Tprod2 i j b)
  exact hY

/-! ## The pairing identity -/

/-- The block scaling `(h₁ • id) × (h₂ • id)` on `ℂ³ × ℂ³`. -/
def Dmap (i j : Fin 3) (b : CP 2) :
    (EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)) →L[ℂ]
      (EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)) :=
  (((homCoord 2 j i b) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 3))).prodMap
    ((homCoord 2 i j b) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 3))))

theorem pairK_smul (k : Fin 3) (c d : ℂ) (u v : EuclideanSpace ℂ (Fin 3)) :
    pairK k (c • u, d • v) =
      (sumFibreC 1 1).toContinuousLinearMap
        (c • (toC1 : ℂ →L[ℂ] EuclideanSpace ℂ (Fin 1)) (coord3 k u),
         d • (toC1 : ℂ →L[ℂ] EuclideanSpace ℂ (Fin 1)) (coord3 k v)) := by
  simp only [pairK, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
  simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  congr 1

theorem pairK_apply' (k : Fin 3) (u v : EuclideanSpace ℂ (Fin 3)) :
    pairK k (u, v) =
      (sumFibreC 1 1).toContinuousLinearMap
        ((toC1 : ℂ →L[ℂ] EuclideanSpace ℂ (Fin 1)) (coord3 k u),
         (toC1 : ℂ →L[ℂ] EuclideanSpace ℂ (Fin 1)) (coord3 k v)) := by
  simp [pairK]

theorem Tdiag_s1 (i j : Fin 3) (b : CP 2)
    (a c : EuclideanSpace ℂ (Fin 1)) :
    Tdiag i j b ((sumFibreC 1 1).toContinuousLinearMap (a, c)) =
      (sumFibreC 1 1).toContinuousLinearMap (hc1 i j b • a, hc2 i j b • c) := by
  rw [lineC_coordChange_diag]
  simp

theorem Dmap_apply (i j : Fin 3) (b : CP 2) (u v : EuclideanSpace ℂ (Fin 3)) :
    Dmap i j b (u, v) = (homCoord 2 j i b • u, homCoord 2 i j b • v) := by
  simp [Dmap]

theorem pairing_comp_Dmap (i j : Fin 3) (b : CP 2) :
    pairing.comp (Dmap i j b) = (Tprod3 i j b).comp pairing := by
  apply ContinuousLinearMap.ext
  intro w
  obtain ⟨u, v⟩ := w
  simp only [ContinuousLinearMap.comp_apply]
  apply cbig_nested_ext
  intro k
  rw [Dmap_apply, cbig_nestK_pairing, nestK_Tprod3, cbig_nestK_pairing,
      pairK_smul, pairK_apply', Tdiag_s1]
  simp only [hc1, hc2]

theorem cbig_conj (i j : Fin 3) (b : CP 2) :
    sumShuffle.toContinuousLinearMap.comp
        ((Tprod3 i j b).comp sumShuffle.symm.toContinuousLinearMap)
      = CbigCLM.comp ((Dmap i j b).comp CbigInv) := by
  have hpair : pairing.comp ((Dmap i j b).comp pairingInv) = Tprod3 i j b := by
    rw [← ContinuousLinearMap.comp_assoc, pairing_comp_Dmap, ContinuousLinearMap.comp_assoc,
      cbig_pairing_comp_pairingInv]
    show Tprod3 i j b ∘SL ContinuousLinearMap.id ℂ Nested3 = Tprod3 i j b
    rw [ContinuousLinearMap.comp_id]
  rw [CbigCLM, CbigInv, ← hpair]
  simp only [ContinuousLinearMap.comp_assoc]

/-! ## The target -/

theorem cbigDiagCLM :
    ∀ (i j : Fin 3) (b : Work.Projective.CP 2),
      b ∈ Work.Projective.chartSet i ∩ Work.Projective.chartSet j →
      Work.Gen.E2.Tgt.coordChange (Work.Gen.E2.diagIdx i) (Work.Gen.E2.diagIdx j) b =
        Work.Gen.E2.CbigCLM.comp
          ((((Work.Gen.homCoord 2 j i b) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 3))).prodMap
            ((Work.Gen.homCoord 2 i j b) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 3)))).comp
              Work.Gen.E2.CbigInv) := by
  intro i j b _
  rw [Tgt_coordChange_diag]
  exact cbig_conj i j b

end

end Work.Gen.E2
