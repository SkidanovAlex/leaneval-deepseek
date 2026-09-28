import Mathlib
import Submission.Work.Serre.RangeEMVanFinDefs
import Submission.Work.Serre.serrePostnikovTower
import Submission.Work.Serre.serreConnectedCover
import Submission.Work.Serre.serreE3a
import Submission.Work.Serre.serreE0Range
import Submission.Work.Stems.isHurewiczFibration_homotopyFibreFst
import Submission.Work.Rat.finiteHomotopyRatAcyclic

namespace Work.Rat

open CategoryTheory CategoryTheory.Limits
open scoped Topology Topology.Homotopy unitInterval

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

noncomputable section

/-- **Bounded finiteness gives bounded rational acyclicity.**

If `X` is path-connected and simply connected (`π_0`, `π_1` trivial) with `π_i(X)` finite for
`2 ≤ i ≤ m`, then `H_j(X;ℚ) = 0` for every `1 ≤ j ≤ m`.

This is the bounded form of `Work.Rat.isZero_ratH_of_finite_homotopy`: its proof never uses
finiteness above the target degree `j ≤ m`.  Indeed, we replace `X` by the Postnikov stage
`P` of `serrePostnikovTower_strong`,` which is a `π_i`-isomorphism for `i ≤ j` and has
`π_i(P) = 0` for `j < i ≤ 3j + 5`; the `j`-stage Postnikov theorem `serreK2Proved` gives
`H_j(X;ℚ) ≅ H_j(P;ℚ)`, and the range form of the Serre `E3(a)` mapping theorem
(`ratVanishing_of_finite_homotopy_aux`) gives `H_j(P;ℚ) = 0` because `j ≤ 3j + 5 - 2j - 1`. -/
theorem isZero_ratH_of_finite_homotopy_le (hEM : Work.Serre.RangeEMVanAllFin)
    (X : Type) [TopologicalSpace X] (x₀ : X) (m : ℕ)
    (h0 : Subsingleton (HomotopyGroup (Fin 0) X x₀))
    (h1 : Subsingleton (HomotopyGroup (Fin 1) X x₀))
    (hfin : ∀ i : ℕ, 2 ≤ i → i ≤ m → Nonempty (Fintype (HomotopyGroup (Fin i) X x₀)))
    (j : ℕ) (hj : 0 < j) (hjm : j ≤ m) :
    IsZero (Work.Serre.ratH (TopCat.of X) j) := by
  haveI : Nonempty X := ⟨x₀⟩
  obtain ⟨P, tP, g, hg1, hg2, -⟩ :=
    Work.Serre.serrePostnikovTower_strong (3 * j + 5 - j) j (3 * j + 5) X rfl (by omega)
  letI : TopologicalSpace P := tP
  -- `H_j(X;ℚ) ≅ H_j(P;ℚ)`: `g` is a `π_i`-isomorphism for `i ≤ j` (`serreK2Proved`).
  haveI hg : IsIso (Work.Serre.ratHomologyMap g j) :=
    Work.Serre.serreK2Proved X P g (j + 1) (fun i hi x => hg1 i (by omega) x) j (by omega)
  -- `P` satisfies the hypotheses of the range theorem, with `n = j`.
  have h0P : Subsingleton (HomotopyGroup (Fin 0) P (g x₀)) :=
    subsingleton_of_surjective_aux h0 (Work.Serre.piMapN g 0 x₀) (hg1 0 (by omega) x₀).2
  have h1P : Subsingleton (HomotopyGroup (Fin 1) P (g x₀)) :=
    subsingleton_of_surjective_aux h1 (Work.Serre.piMapN g 1 x₀) (hg1 1 (by omega) x₀).2
  have hfinP : ∀ i : ℕ, 2 ≤ i → i ≤ j →
      Nonempty (Fintype (HomotopyGroup (Fin i) P (g x₀))) := by
    intro i hi2 hij
    exact fintype_of_bijective_piMapN g i x₀ (hg1 i hij x₀) (hfin i hi2 (le_trans hij hjm))
  have hzeroP : ∀ i : ℕ, j < i → i ≤ 3 * j + 5 →
      Subsingleton (HomotopyGroup (Fin i) P (g x₀)) :=
    fun i hi hiN => hg2 i hi hiN (g x₀)
  have hP : IsZero (Work.Serre.ratH (TopCat.of P) j) :=
    ratVanishing_of_finite_homotopy_aux hEM j (3 * j + 5) P (g x₀) (by omega) (by omega)
      h0P h1P hfinP hzeroP j hj (by omega)
  exact IsZero.of_iso hP (asIso (Work.Serre.ratHomologyMap g j))

/-- **Finitely many homotopy classes in degrees `≤ M` force rational homology to vanish in
degrees `≤ M`.**  If `X` is path-connected and simply connected with `π_i(X)` finite for
`2 ≤ i ≤ M`, then `H_j(X;ℚ) = 0` for every `1 ≤ j ≤ M`. -/
theorem finitePiRatHVanishing (hEM : Work.Serre.RangeEMVanAllFin)
    (X : Type) [TopologicalSpace X] (x₀ : X) (M : ℕ)
    (h0 : Subsingleton (HomotopyGroup (Fin 0) X x₀))
    (h1 : Subsingleton (HomotopyGroup (Fin 1) X x₀))
    (hfin : ∀ i : ℕ, 2 ≤ i → i ≤ M → Nonempty (Fintype (HomotopyGroup (Fin i) X x₀))) :
    ∀ j : ℕ, 1 ≤ j → j ≤ M →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) j) := by
  intro j hj hjM
  exact isZero_ratH_of_finite_homotopy_le hEM X x₀ M h0 h1 hfin j hj hjM

end

end Work.Rat
