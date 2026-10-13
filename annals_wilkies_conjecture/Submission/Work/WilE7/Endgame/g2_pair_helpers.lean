import Mathlib
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.WilE7.CoreStep.fiber_empty_of_good_of_vertical
import Submission.Work.CoreStep.CrossDefs
import Submission.Work.WilE7.DimAPI.ProjRankAux

namespace Work.WilE7.Endgame

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt)

/-- The base projection of an `absPtUp`-point. -/
theorem g2_basePrLin_absPtUp {n m : ℕ} (z : Fin (n + (m + 1)) → ℝ) :
    Work.WilE7.MainDesign.basePrLin n (m + 1) (absPtUp (n := n) (m := m) z)
      = projFirst n (m + 1) z := by
  rw [← Work.WilE7.CoreStep.projFirst_absPt (absPtUp (n := n) (m := m) z)]
  exact congrArg (projFirst n (m + 1)) (Work.WilE7.DimAPI.absPt_absPtInv (n + (m + 1)) z)

/-- The base projection `pairBaseLin` is the base projection of the first block. -/
theorem g2_pairBaseLin_block {n m : ℕ} (w : Fin (0 + pPair n m) → ℝ) :
    pairBaseLin n m w
      = Work.WilE7.MainDesign.basePrLin n (m + 1) (Work.CoreStep.blockFirstCLM n m w) := by
  funext i
  rw [Work.CoreStep.blockFirstCLM_apply]
  rfl

/-- `pairBase` is `pairBaseLin`. -/
theorem g2_pairBase_eq_pairBaseLin {n m : ℕ} (w : Fin (0 + pPair n m) → ℝ) :
    Work.CoreStep.pairBase n m w = pairBaseLin n m w := by
  funext i
  exact congrArg w (Fin.ext rfl)

/-- The diagonal (base-agreement) condition of the two-piece pair set `absPairSet2 R T`, together
with the membership of the two components in `R` and `T`. -/
theorem g2_mem_absPairSet2_elim {n m : ℕ} (R T : Stratum 0 (n + (m + 1)))
    {y : Fin (0 + pPair n m) → ℝ} (hy : y ∈ (absPairSet2 R T).set) :
    (∀ i : Fin n, Work.WilE7.MainDesign.basePrLin n (m + 1) (Work.CoreStep.blockFirstCLM n m y) i
        = Work.WilE7.MainDesign.basePrLin n (m + 1) (Work.CoreStep.blockSndCLM n m y) i) ∧
      Work.CoreStep.blockFirstCLM n m y ∈ R.X.set ∧
      Work.CoreStep.blockSndCLM n m y ∈ T.X.set := by
  classical
  have hz : (fun i : Fin (pPair n m) =>
        y ((Work.WilE7.finEquiv (Nat.zero_add (pPair n m))).symm i))
      = Work.WilE7.MainDesign.absPt y := by
    funext i
    exact congrArg y (Fin.ext rfl)
  rw [absPairSet2, Work.WilE7.sp_reindex_set] at hy
  simp only [Set.mem_ofPred_eq] at hy
  rw [hz, Work.WilE7.fiberProdZ_set] at hy
  obtain ⟨h1, h2, h3⟩ := hy
  have hbf : Work.CoreStep.blockFirstCLM n m y
      = absPtUp (n := n) (m := m)
          (projFirst (n + (m + 1)) (n + (m + 1)) (Work.WilE7.MainDesign.absPt y)) := rfl
  have hbs : Work.CoreStep.blockSndCLM n m y
      = absPtUp (n := n) (m := m)
          (projSnd (n + (m + 1)) (n + (m + 1)) (Work.WilE7.MainDesign.absPt y)) := rfl
  have hR : Work.CoreStep.blockFirstCLM n m y ∈ R.X.set := by
    rw [hbf]
    exact (Work.WilE7.CoreStep.mem_absReindex R _).mp h1
  have hT : Work.CoreStep.blockSndCLM n m y ∈ T.X.set := by
    rw [hbs]
    exact (Work.WilE7.CoreStep.mem_absReindex T _).mp h2
  refine ⟨?_, hR, hT⟩
  intro i
  rw [hbf, hbs, g2_basePrLin_absPtUp, g2_basePrLin_absPtUp]
  exact congrFun h3 i

/-- Membership in the two-piece pair set from its two components and base agreement. -/
theorem g2_mem_absPairSet2_of {n m : ℕ} (R T : Stratum 0 (n + (m + 1)))
    (u v : Fin (pDim n m) → ℝ) (hu : u ∈ R.X.set) (hv : v ∈ T.X.set)
    (hbase : ∀ i : Fin n,
      Work.WilE7.MainDesign.basePrLin n (m + 1) u i = Work.WilE7.MainDesign.basePrLin n (m + 1) v i) :
    pairPtUp u v ∈ (absPairSet2 R T).set := by
  classical
  have hz : (fun i : Fin (pPair n m) =>
        pairPtUp u v ((Work.WilE7.finEquiv (Nat.zero_add (pPair n m))).symm i))
      = Work.WilE7.MainDesign.absPt (pairPtUp u v) := by
    funext i
    exact congrArg (pairPtUp u v) (Fin.ext rfl)
  rw [absPairSet2, Work.WilE7.sp_reindex_set]
  simp only [Set.mem_ofPred_eq]
  rw [hz, Work.WilE7.fiberProdZ_set]
  have hbf : Work.CoreStep.blockFirstCLM n m (pairPtUp u v) = u :=
    Work.CoreStep.blockFirst_pairPtUp u v
  have hbs : Work.CoreStep.blockSndCLM n m (pairPtUp u v) = v :=
    Work.CoreStep.blockSnd_pairPtUp u v
  have h1 : projFirst (n + (m + 1)) (n + (m + 1))
      (Work.WilE7.MainDesign.absPt (pairPtUp u v)) ∈ (absReindex R).set := by
    rw [Work.WilE7.CoreStep.mem_absReindex]
    rw [show absPtUp (n := n) (m := m)
          (projFirst (n + (m + 1)) (n + (m + 1))
            (Work.WilE7.MainDesign.absPt (pairPtUp u v)))
        = Work.CoreStep.blockFirstCLM n m (pairPtUp u v) from rfl, hbf]
    exact hu
  have h2 : projSnd (n + (m + 1)) (n + (m + 1))
      (Work.WilE7.MainDesign.absPt (pairPtUp u v)) ∈ (absReindex T).set := by
    rw [Work.WilE7.CoreStep.mem_absReindex]
    rw [show absPtUp (n := n) (m := m)
          (projSnd (n + (m + 1)) (n + (m + 1))
            (Work.WilE7.MainDesign.absPt (pairPtUp u v)))
        = Work.CoreStep.blockSndCLM n m (pairPtUp u v) from rfl, hbs]
    exact hv
  refine ⟨h1, h2, ?_⟩
  show projFirst n (m + 1)
      (projFirst (n + (m + 1)) (n + (m + 1)) (Work.WilE7.MainDesign.absPt (pairPtUp u v)))
    = projFirst n (m + 1)
      (projSnd (n + (m + 1)) (n + (m + 1)) (Work.WilE7.MainDesign.absPt (pairPtUp u v)))
  rw [Work.CoreStep.Cross_absPt_pairPtUp]
  rw [show projFirst (n + (m + 1)) (n + (m + 1))
        (Fin.append (Work.WilE7.MainDesign.absPt u) (Work.WilE7.MainDesign.absPt v))
      = Work.WilE7.MainDesign.absPt u from funext fun i => Fin.append_left _ _ i]
  rw [show projSnd (n + (m + 1)) (n + (m + 1))
        (Fin.append (Work.WilE7.MainDesign.absPt u) (Work.WilE7.MainDesign.absPt v))
      = Work.WilE7.MainDesign.absPt v from funext fun i => Fin.append_right _ _ i]
  exact funext (fun i => hbase i)


end

end Work.WilE7.Endgame
