/-
  Subproject WilE9G — the bridge from the symbolic derivative `eaD` to the honest Fréchet
  derivative, in the two matrix shapes that the construction uses.

  `Work.WilE5.Strat.fderiv_eaEval_apply_single` already gives, for a single `EAPoly`,
  `(fderiv (fun z => eaEval c Q z) x) (Pi.single i 1) = eaEval c (eaD c i Q) x`.
  The lemmas here are its matrix form: the `(1+m) x (1+m)` block of symbolic derivatives of an
  `EffStratum` is the block of an honest differential, and likewise for the `j x N` matrix of an
  `AmbStratum`.
-/
import Submission.Work.WilE9G.Amb
import Submission.Work.WilE5.Strat.flatConormalTools

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G
open WilkiesDesign WilkiesDesign.E Work.WilE9.Sharp

/-- The fibre block of an `EffStratum`'s symbolic Jacobian is the corresponding block of the
honest Fréchet differential of the tuple of equations. -/
theorem EffStratum_jac_eq_fderiv {n m : ℕ} (E : EffStratum n m)
    (z : Fin (n + (1 + m)) → ℝ) :
    (Matrix.of fun (a : Fin (1 + m)) (l : Fin (1 + m)) =>
        eaEval E.X.c (eaD E.X.c (Fin.natAdd n l) (E.h a)) z)
      = Matrix.of fun (a : Fin (1 + m)) (l : Fin (1 + m)) =>
          (fderiv ℝ (fun z' : Fin (n + (1 + m)) → ℝ => eaEval E.X.c (E.h a) z') z)
            (Pi.single (Fin.natAdd n l) 1) := by
  ext a l
  exact (Work.WilE5.Strat.fderiv_eaEval_apply_single E.X.c (E.h a) z (Fin.natAdd n l)).symm

/-- The `j x N` matrix of an `AmbStratum`'s symbolic Jacobian is the corresponding matrix of the
honest Fréchet differential of the tuple of equations. -/
theorem AmbStratum_jac_eq_fderiv {N : ℕ} (S : AmbStratum N) (z : Fin N → ℝ) :
    (Matrix.of fun (a : Fin S.j) (l : Fin N) => eaEval S.X.c (eaD S.X.c l (S.h a)) z)
      = Matrix.of fun (a : Fin S.j) (l : Fin N) =>
          (fderiv ℝ (fun z' : Fin N → ℝ => eaEval S.X.c (S.h a) z') z) (Pi.single l 1) := by
  ext a l
  exact (Work.WilE5.Strat.fderiv_eaEval_apply_single S.X.c (S.h a) z l).symm

end Work.WilE9G
