import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.SQASM.connHomology
import Submission.Work.Serre.serrePostnikovTower
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.Pi6.HALG

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **Range inputs for the fibration `mpathQ g₄`** (area HALG): the integral homology of `Y` vanishes
in degrees 1–4, `Y` is path connected, and the Postnikov section `P₄` has trivial homotopy below
degree 4. Write `Submission/Work/Pi6/HALG/rangeInputsY.lean`, module
`Submission.Work.Pi6.HALG.rangeInputsY`, namespace `Work.Pi6.HALG`, importing
`Submission.Work.Pi6.Interfaces` and `Submission.Work.Pi6.SQASM.connHomology`.

Route. `hT` (instantiated at the given tower data) gives `∀ i ≤ 4, Subsingleton (π_i Y)` at `y0`, and
at `e0 g3` for `E`; apply `Work.Pi6.SQASM.connHomology` (already proved:
connectivity at one point gives `IsZero (HR ℤ X i)` for `0 < i ≤ n`) with `n = 4`, resp. `n = 3`.
For the third conjunct: `h4` makes `Work.Serre.piMapN g4 i (e0 g3)` bijective for `i ≤ 4`, so
`π_i P4 ≅ π_i E = 0` for `i ≤ 3`. -/
theorem rangeInputsY (hT : Work.Pi6.TowerPi)
    (P3 : Type) [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3))
    (h3 : Work.Pi6.PostnikovData 3 12 g3 Work.Pi6.s3)
    (P4 : Type) [TopologicalSpace P4] (g4 : C(Work.Pi6.Ecov g3, P4))
    (h4 : Work.Pi6.PostnikovData 4 12 g4 (Work.Pi6.e0 g3)) :
    (∀ j : ℕ, 0 < j → j ≤ 4 → CategoryTheory.Limits.IsZero (Work.Pi6.HR ℤ (Work.Pi6.Ycov g3 g4) j)) ∧
    Subsingleton (HomotopyGroup (Fin 0) (Work.Pi6.Ycov g3 g4) (Work.Pi6.y0 g3 g4)) ∧
    (∀ i : ℕ, i < 4 → Subsingleton (HomotopyGroup (Fin i) P4 (g4 (Work.Pi6.e0 g3)))) := by
  -- a stage-5 Postnikov section of `Y`, needed only to instantiate `TowerPi`
  obtain ⟨P5, _, g5, h5a, h5b, -⟩ :=
    Work.Serre.serrePostnikovTower_strong (12 - 5) 5 12 (Work.Pi6.Ycov g3 g4) rfl (by norm_num)
  have h5 : Work.Pi6.PostnikovData 5 12 g5 (Work.Pi6.y0 g3 g4) :=
    ⟨fun i hi y => h5a i hi y, h5b⟩
  obtain ⟨-, hE, hY, -, -⟩ := hT P3 g3 h3 P4 g4 h4 P5 g5 h5
  refine ⟨?_, hY 0 (by omega), ?_⟩
  · -- `Y` is `4`-connected at `y₀`, hence its integral homology vanishes in degrees `1 – 4`
    intro j hj hj4
    exact Work.Pi6.SQASM.connHomology (Work.Pi6.y0 g3 g4) 4 j (fun i hi => hY i hi) hj hj4
  · -- `π_i(P₄)`, `i < 4`, is a quotient of `π_i(E)`, which vanishes since `E` is `3`-connected
    intro i hi
    haveI : Subsingleton (HomotopyGroup (Fin i) (Work.Pi6.Ecov g3) (Work.Pi6.e0 g3)) :=
      hE i (by omega)
    exact (h4.1 i (by omega) (Work.Pi6.e0 g3)).surjective.subsingleton

end

end Work.Pi6.HALG
