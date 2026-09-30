import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.SQASM.connHomology
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.HALG

/-- **Range inputs for the fibration `mpathQ g₅`** (area HALG): the integral homology of `Z` vanishes
in degrees 1–5, `Z` is path connected, and the Postnikov section `P₅` has trivial homotopy below
degree 5. Write `Submission/Work/Pi6/HALG/rangeInputsZ.lean`, module
`Submission.Work.Pi6.HALG.rangeInputsZ`, namespace `Work.Pi6.HALG`, importing
`Submission.Work.Pi6.Interfaces` and `Submission.Work.Pi6.SQASM.connHomology`.

Route. `hT` (instantiated at the given tower data) gives `∀ i ≤ 5, Subsingleton (π_i Z)` at the
homotopy-fibre base point, so `Work.Pi6.SQASM.connHomology` (already proved) with `n = 5` gives the
first conjunct; the second is the `i = 0` instance. For the third: `h5` makes
`Work.Serre.piMapN g5 i (y0 g3 g4)` bijective for `i ≤ 5`, and `hT` gives `π_i Y = 0` for `i ≤ 4`,
so `π_i P5 = 0` for `i ≤ 4`. -/
theorem rangeInputsZ (hT : Work.Pi6.TowerPi)
    (P3 : Type) [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3))
    (h3 : Work.Pi6.PostnikovData 3 12 g3 Work.Pi6.s3)
    (P4 : Type) [TopologicalSpace P4] (g4 : C(Work.Pi6.Ecov g3, P4))
    (h4 : Work.Pi6.PostnikovData 4 12 g4 (Work.Pi6.e0 g3))
    (P5 : Type) [TopologicalSpace P5] (g5 : C(Work.Pi6.Ycov g3 g4, P5))
    (h5 : Work.Pi6.PostnikovData 5 12 g5 (Work.Pi6.y0 g3 g4)) :
    (∀ j : ℕ, 0 < j → j ≤ 5 → CategoryTheory.Limits.IsZero (Work.Pi6.HR ℤ (Work.Pi6.Zcov g3 g4 g5) j)) ∧
    Subsingleton (HomotopyGroup (Fin 0) (Work.Pi6.Zcov g3 g4 g5)
      (Work.RatHurewicz.homotopyFibreBasepoint g5 (Work.Pi6.y0 g3 g4))) ∧
    (∀ i : ℕ, i < 5 → Subsingleton (HomotopyGroup (Fin i) P5 (g5 (Work.Pi6.y0 g3 g4)))) := by
  obtain ⟨-, -, hYconn, hZconn, -, -⟩ := hT P3 g3 h3 P4 g4 h4 P5 g5 h5
  refine ⟨fun j hj hj5 => ?_, hZconn 0 (by norm_num), fun i hi => ?_⟩
  · exact Work.Pi6.SQASM.connHomology
      (Work.RatHurewicz.homotopyFibreBasepoint g5 (Work.Pi6.y0 g3 g4)) 5 j hZconn hj hj5
  · haveI : Subsingleton
        (HomotopyGroup (Fin i) (Work.Pi6.Ycov g3 g4) (Work.Pi6.y0 g3 g4)) :=
      hYconn i (by omega)
    have hsurj : Function.Surjective (Work.Serre.piMapN g5 i (Work.Pi6.y0 g3 g4)) :=
      (h5.1 i (by omega) (Work.Pi6.y0 g3 g4)).2
    exact ⟨fun a b => by
      obtain ⟨a', ha'⟩ := hsurj a
      obtain ⟨b', hb'⟩ := hsurj b
      rw [← ha', ← hb', Subsingleton.elim a' b']⟩

end Work.Pi6.HALG
