/-
  annals_wilkies_conjecture, AREA E3K: the set of non-submersion values of the remaining system
  is closed.

  For `E : ETData N (rt+1) n re`, the remaining system `E.psiMap` (`Elim.lean`) is the system map
  with the eliminated arctan row deleted, a map `ℝ^{N+1} → ℝ^N`.  We prove that

    `{y | ¬ E.ETSubmersion y}`

  — the set of values at which some point of the level set `{psiMap = y}` has dependent derivative
  functionals — is closed, provided `E.psiMap` is proper.

  The argument is the E2 one (`Work.WilE2.khoSubm_bad_closed`), with the continuity input supplied
  here:

  * `E.psiMap` is `C²`: each row of `E.map` is either an arctan equation
    (`Real.arctan ∘ proj - affine`) or an exp-affine equation (`E.evP i = eaEval E.toChain (E.G i)`,
    smooth by `Work.WilE9.EaD.eaEval_contDiff`); the rows of `E.psiMap` are rows of `E.map`;
  * hence the generalised cross product `Work.WilE2.crossField E.psiMap` of the `N` gradients is
    continuous (`Work.WilE2.contDiff_crossField`), so its zero set is closed;
  * the derivative functionals of the rows of `E.psiMap` are dependent at `z` exactly when that
    cross product vanishes (`Work.WilE2.not_linearIndependent_iff_crossField_eq_zero`), so
    `{y | ¬ E.ETSubmersion y} = E.psiMap '' {z | crossField E.psiMap z = 0}`;
  * a proper map is closed, so that image is closed.
-/
import Mathlib
import Submission.Work.WilE3K.Elim
import Submission.Work.WilE2.tangentField_exists
import Submission.Work.WilE2.khoSubm_bad_closed
import Submission.Work.WilE3K.ContAux
import Submission.Work.WilE9.EaD.eaEval_contDiff

set_option autoImplicit false
noncomputable section
open Classical Topology Filter

namespace Work.WilE3K

namespace ETData

variable {N rt n re : ℕ}

/-! ## §1. The remaining system is `C²` -/

/-- The affine part `E.lin j` of an arctan equation is smooth: it is a finite sum of coordinate
projections plus a constant. -/
private theorem contDiff_lin_aux (E : ETData N rt n re) (j : Fin rt) :
    ContDiff ℝ ⊤ (E.lin j) := by
  rw [show E.lin j = fun z : Fin (N + 1) → ℝ =>
      (∑ i : Fin n, E.lam j i * z (E.freeCoord i)) + E.mu j from by
    funext z; rw [ETData.lin]]
  exact (ContDiff.sum (fun i _ => contDiff_const.mul (contDiff_apply ℝ ℝ (E.freeCoord i)))).add
    contDiff_const

/-- Every arctan equation is smooth: `arctan` is, and so is the affine function subtracted from
it. -/
private theorem contDiff_tanFun_aux (E : ETData N rt n re) (j : Fin rt) :
    ContDiff ℝ ⊤ (E.tanFun j) :=
  (Real.contDiff_arctan.comp (contDiff_apply ℝ ℝ (E.tanCoord j))).sub (contDiff_lin_aux E j)

/-- Every exp-affine equation is smooth: `E.evP i` is the EA evaluation `eaEval E.toChain (E.G i)`
of `E.toChain` (`Work.WilE3K.ETData.evalPoly_eq_eaEval`), which is smooth. -/
private theorem contDiff_evP_aux (E : ETData N rt n re) (i : Fin n) :
    ContDiff ℝ ⊤ (E.evP i) := by
  rw [show E.evP i = fun z : Fin (N + 1) → ℝ => WilkiesDesign.E.eaEval E.toChain (E.G i) z from by
    funext z; exact E.evalPoly_eq_eaEval (E.G i) z]
  exact Work.WilE9.EaD.eaEval_contDiff E.toChain (E.G i)

/-- The system map of a lifted system is `C²`: row by row it is either an arctan equation or an
exp-affine equation. -/
private theorem contDiff_map_aux (E : ETData N rt n re) : ContDiff ℝ 2 E.map := by
  rw [contDiff_pi]
  intro i
  by_cases hi : (i : ℕ) < rt
  · have hfun : (fun z => E.map z i) = E.tanFun (E.tanIndex i hi) := by
      funext z; simp only [ETData.map, dite_eq_left hi]
    rw [hfun]
    exact (contDiff_tanFun_aux E (E.tanIndex i hi)).of_le le_top
  · have hfun : (fun z => E.map z i) = E.evP (E.freeIndex i (not_lt.mp hi)) := by
      funext z; simp only [ETData.map, dite_eq_right hi]
    rw [hfun]
    exact (contDiff_evP_aux E (E.freeIndex i (not_lt.mp hi))).of_le le_top

/-- **The remaining system is `C²`.**  `E.psiMap` is `E.map` with the rows re-indexed by
`Fin.succAbove E.lastRow`, so its rows are rows of `E.map`. -/
theorem contDiff_psiMap (E : ETData N (rt + 1) n re) : ContDiff ℝ 2 E.psiMap := by
  rw [contDiff_pi]
  intro i
  have h : ContDiff ℝ 2 (fun w : Fin (N + 1) → ℝ => E.map w (Fin.succAbove E.lastRow i)) :=
    (contDiff_pi.mp (contDiff_map_aux E)) _
  simpa only [ETData.psiMap] using h

end ETData

/-! ## §2. Closedness of the set of non-submersion values -/

/-- The values at which the remaining system `E.psiMap` is not a submersion form a closed set. `E.ETSubmersion y` unfolds to `∀ z, E.psiMap z = y → LinearIndependent ℝ (fun a => fderiv ℝ (fun w => E.psiMap w a) z)`, so `¬ E.ETSubmersion y` iff `y` is the image of a point where the generalised cross product `Work.WilE2.crossField E.psiMap` vanishes (`Work.WilE2.not_linearIndependent_iff_crossField_eq_zero`); the image under the proper map `E.psiMap` of that (closed) zero set is closed. Needed: `ContDiff ℝ 2 E.psiMap` (from `Work.WilE3K.ContAux` + `Work.WilE9.EaD.eaEval_contDiff`) and continuity of the cross product (`Work.WilE2.contDiff_crossField`). -/
theorem ETSubm_bad_closed {N rt n re : ℕ} (E : Work.WilE3K.ETData N (rt + 1) n re)
    (hproper : IsProperMap E.psiMap) :
    IsClosed {y : Fin N → ℝ | ¬ E.ETSubmersion y} := by
  -- The cross-product field of the `N` gradients of the rows of `psiMap` is continuous.
  have hcont : Continuous (Work.WilE2.crossField E.psiMap) :=
    (Work.WilE2.contDiff_crossField E.psiMap E.contDiff_psiMap).continuous
  -- Its zero set is closed.
  have hC : IsClosed {z : Fin (N + 1) → ℝ | Work.WilE2.crossField E.psiMap z = 0} :=
    isClosed_eq hcont continuous_const
  -- A proper map is closed, so the image of the zero set is closed.
  have himg : IsClosed
      (E.psiMap '' {z : Fin (N + 1) → ℝ | Work.WilE2.crossField E.psiMap z = 0}) :=
    hproper.isClosedMap _ hC
  -- The image of the zero set is exactly the set of non-submersion values.
  convert himg using 1
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro hy
    rw [Work.WilE3K.ETData.ETSubmersion] at hy
    push Not at hy
    obtain ⟨z, hz, hli⟩ := hy
    exact ⟨z, (Work.WilE2.not_linearIndependent_iff_crossField_eq_zero E.psiMap z).mp hli, hz⟩
  · rintro ⟨z, hz, rfl⟩ hy
    exact (Work.WilE2.not_linearIndependent_iff_crossField_eq_zero E.psiMap z).mpr hz (hy z rfl)

end Work.WilE3K
