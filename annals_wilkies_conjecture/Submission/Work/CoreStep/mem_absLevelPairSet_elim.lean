import Mathlib
import Submission.Work.WilE7.CoreStep.GermDefs

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep

namespace Work.CoreStep

/-- The point of the pair space `Fin (0 + pPair n m) → ℝ` un-indexed to `Fin (pPair n m) → ℝ`
along the `0 + ·` bookkeeping.  This is the same function as `MainDesign.absPt`, but written in
the equivalence `finEquiv` used by `SemiPf.reindex` in the definition of `absLevelPairSet`. -/
private def idxPt {n m : ℕ} (z : Fin (0 + Work.WilE7.CoreStep.pPair n m) → ℝ) :
    Fin (Work.WilE7.CoreStep.pPair n m) → ℝ :=
  fun i => z ((Work.WilE7.finEquiv (Nat.zero_add (Work.WilE7.CoreStep.pPair n m))).symm i)

/-- `idxPt` is `absPt`: both cast the index set along `0 + pPair n m = pPair n m`. -/
private theorem absPt_idxPt {n m : ℕ} (z : Fin (0 + Work.WilE7.CoreStep.pPair n m) → ℝ) :
    Work.WilE7.MainDesign.absPt z = idxPt z := by
  funext i
  show z (Fin.cast (Nat.zero_add (Work.WilE7.CoreStep.pPair n m)).symm i)
      = z ((Work.WilE7.finEquiv (Nat.zero_add (Work.WilE7.CoreStep.pPair n m))).symm i)
  congr 1

/-- `absPtUp` really is a section of `absPt` (it is `absPtInv`). -/
private theorem absPt_absPtUp {n m : ℕ} (u : Fin (n + (m + 1)) → ℝ) :
    Work.WilE7.MainDesign.absPt (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) u) = u :=
  Work.WilE7.CoreStep.absPtInv_absPtUp u

theorem mem_absLevelPairSet_elim {n m : ℕ} (T T' : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    {z : Fin (0 + Work.WilE7.CoreStep.pPair n m) → ℝ}
    (hz : z ∈ (Work.WilE7.CoreStep.absLevelPairSet T T').set) :
    WilkiesDesign.E.projFirst (n + (m + 1)) (n + (m + 1)) (Work.WilE7.MainDesign.absPt z)
        ∈ Work.WilE7.MainDesign.absSet T ∧
    WilkiesDesign.E.projSnd (n + (m + 1)) (n + (m + 1)) (Work.WilE7.MainDesign.absPt z)
        ∈ Work.WilE7.MainDesign.absSet T' ∧
    WilkiesDesign.E.projFirst n (m + 1)
        (WilkiesDesign.E.projFirst (n + (m + 1)) (n + (m + 1)) (Work.WilE7.MainDesign.absPt z))
      = WilkiesDesign.E.projFirst n (m + 1)
        (WilkiesDesign.E.projSnd (n + (m + 1)) (n + (m + 1)) (Work.WilE7.MainDesign.absPt z)) ∧
    (WilkiesDesign.E.projSnd n (m + 1)
        (WilkiesDesign.E.projFirst (n + (m + 1)) (n + (m + 1))
          (Work.WilE7.MainDesign.absPt z))) ⟨m, by omega⟩
      = (WilkiesDesign.E.projSnd n (m + 1)
        (WilkiesDesign.E.projSnd (n + (m + 1)) (n + (m + 1))
          (Work.WilE7.MainDesign.absPt z))) ⟨m, by omega⟩ ∧
    z = Work.WilE7.CoreStep.pairPtUp
          (Work.WilE7.CoreStep.absPtUp (n := n) (m := m)
            (WilkiesDesign.E.projFirst (n + (m + 1)) (n + (m + 1)) (Work.WilE7.MainDesign.absPt z)))
          (Work.WilE7.CoreStep.absPtUp (n := n) (m := m)
            (WilkiesDesign.E.projSnd (n + (m + 1)) (n + (m + 1))
              (Work.WilE7.MainDesign.absPt z))) := by
  -- Reindex the membership along the `finEquiv` used in the definition of `absLevelPairSet`.
  have hmem : idxPt z ∈ (Work.WilE7.levelGlue (absReindex T) (absReindex T')).set :=
    (Work.WilE7.sp_reindex_mem ((Work.WilE7.finEquiv (Nat.zero_add (pPair n m))).symm)
      (Work.WilE7.levelGlue (absReindex T) (absReindex T')) z).mp hz
  rw [Work.WilE7.levelGlue_set] at hmem
  have h1 := hmem.1
  have h2 := hmem.2.1
  have h3 := hmem.2.2.1
  have h4 := hmem.2.2.2
  -- `levelGlue` glues the two reindexed pieces, so the two halves land in `absSet T`, `absSet T'`.
  have hs1 : absPtUp (n := n) (m := m) (projFirst (n + (m + 1)) (n + (m + 1)) (idxPt z))
      ∈ T.X.set := (mem_absReindex T _).mp h1
  have hs2 : absPtUp (n := n) (m := m) (projSnd (n + (m + 1)) (n + (m + 1)) (idxPt z))
      ∈ T'.X.set := (mem_absReindex T' _).mp h2
  have habs : absPt z = idxPt z := absPt_idxPt z
  -- The pair point of the two halves of `absPt z` is `absPt z` itself.
  have hpt : pairPt (absPtUp (n := n) (m := m)
        (projFirst (n + (m + 1)) (n + (m + 1)) (absPt z)))
      (absPtUp (n := n) (m := m)
        (projSnd (n + (m + 1)) (n + (m + 1)) (absPt z))) = absPt z := by
    rw [pairPt, absPtInv_absPtUp, absPtInv_absPtUp]
    exact Work.WilE7.append_projFirst_projSnd (absPt z)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show projFirst (n + (m + 1)) (n + (m + 1)) (absPt z) ∈ absSet T
    rw [absSet, habs]
    exact ⟨_, hs1, absPt_absPtUp _⟩
  · show projSnd (n + (m + 1)) (n + (m + 1)) (absPt z) ∈ absSet T'
    rw [absSet, habs]
    exact ⟨_, hs2, absPt_absPtUp _⟩
  · simpa only [habs] using h3
  · simpa only [habs] using h4
  · funext j
    show z j = pairPtUp _ _ j
    show z j = pairPt _ _ (Fin.cast (Nat.zero_add (pPair n m)) j)
    rw [hpt]
    show z j = absPt z (Fin.cast (Nat.zero_add (pPair n m)) j)
    rfl

end Work.CoreStep
