import Mathlib
import Submission.Work.PTCert.Checks.C2All
import Submission.Work.PTCert.Cert2.Setup
import Submission.Work.PTCert.Cert2.symHypC2
import Submission.Work.PTCert.Cert2.rowCheckC2
import Submission.Work.PTCert.Cert2.ldlDataC2
import Submission.Work.PTCert.Cert2.classEqC2
import Submission.Work.PTCert.Cert2.resC2

namespace Work.PTCert

open OnPropertyT Submission.FreeGroupAut Submission.RouteB
open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.D2 Submission.PTCert.C2K
open scoped BigOperators

set_option maxRecDepth 400000

/-- **The `C2` certificate**: the assembly of the kernel-checked data of the second certificate
(`q = qC2`, `μ = 7/25`, common denominator `200`, `SC = 2^80`, residual bound `(23/100)·2^80·200`)
into `SAut5Adj2OpCert`, i.e. `∃ μ > 0, Adj₅ + 2·Op₅ − μ·Δ₅ ∈ Σ²`.

The hypotheses are the semantic Props of `Glue3.lean` (`PsdAssembly`, `RowTabSound`, `FinalStep`,
`ClassSem`, `KleinSem`) together with the target identity `hT2`; the data hypotheses of those Props
are discharged in the companion files of `Submission/Work/PTCert/Cert2/` from the kernel checks
`Checks/C2/`. -/
theorem cert2Final (hPA : PsdAssembly) (hRT : RowTabSound) (hFS : FinalStep) (hC : ClassSem)
    (hK : ∀ k ≤ 5, KleinSem k) (hT2 : targetSum qC2 200 = gramL 5 (QAdjOp 5 2 (7 / 25))) :
    Submission.RouteB.Edge.SAut5Adj2OpCert := by
  -- (1) the symmetry of the value table (kernel checks `sym_ok{r}_{j}`)
  have hSym : SymHyp Cert2.valZ := Cert2.symHypC2
  -- (2) the row tables (kernel checks `rw_ok{r}_{j}`, through `RowTabSound`)
  have hRowTab : RowTabHyp Cert2.valZ rowTs := hRT valT rowTs Cert2.rowCheckC2
  -- (3) the LDL data of the five base characters (kernel checks `ldl_ok{k}_{j}`)
  have hLDL : ∀ k ≤ 4, LdlData rowTs k := Cert2.ldlDataC2
  -- (4) hence `Pmat` is positive semidefinite
  have hPSD : (Pmat Cert2.valZ).PosSemidef := hPA Cert2.valZ rowTs hSym hRowTab hLDL
  -- (5) the target: `T = Adj₅ + 2·Op₅ − (1/20)·Δ₅`
  let T : MonoidAlgebra ℝ G5 := targetSum Cert2.qZ 200 + (23 / 100 : ℝ) • Edge.deltaSub 5 5
  have hTeq : T = Edge.AdjPair 5 5 + (2 : ℝ) • Edge.OpPair 5 5
      - (1 / 20 : ℝ) • Edge.deltaSub 5 5 := by
    show targetSum Cert2.qZ 200 + (23 / 100 : ℝ) • Edge.deltaSub 5 5 =
      Edge.AdjPair 5 5 + (2 : ℝ) • Edge.OpPair 5 5 - (1 / 20 : ℝ) • Edge.deltaSub 5 5
    have hA := (Work.PTCert.targetExpansions 5).2 (2 : ℚ) (7 / 25)
    rw [Cert2.targetSum_qZ_eq, hT2, ← hA]
    module
  -- (6) `T` is invariant under conjugation by the signed permutations
  have hinv : ∀ σ ∈ Sg, MonoidAlgebra.of ℝ G5 σ * T * MonoidAlgebra.of ℝ G5 σ⁻¹ = T := by
    intro σ hσ
    rw [hTeq]
    obtain ⟨hd, ha, ho⟩ := (Work.PTCert.targetInvariance 5) σ hσ
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
    rw [ha, ho, hd]
  -- (7) the final step: PSD + exact class sums + absorbed residual give `T ∈ Σ²`
  have hSOS : IsSOS T :=
    hFS Cert2.valZ Cert2.qZ Cert2.resZ Cert2.denZ Cert2.scZ T (23 / 100) Cert2.denZ_pos
      Cert2.scZ_pos hPSD Cert2.classEqC2 Cert2.resC2.1 Cert2.resC2.2.1 Cert2.resC2.2.2 hinv rfl
  rw [hTeq] at hSOS
  exact ⟨1 / 20, by norm_num, hSOS⟩

end Work.PTCert
