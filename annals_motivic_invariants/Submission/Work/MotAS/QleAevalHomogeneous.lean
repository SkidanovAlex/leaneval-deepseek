import Mathlib
import Submission.Work.MotK.TwRuling.KleinKerDefs
import Submission.Work.MotK.TwRuling.SdWNdeg
import Submission.Work.MotK.TwRuling.quinticTw_notMem_kernel

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.Q_le_aeval_homogeneous_v2` — the `hD.spans` span of products, recompiled

`Work.MotK.TwRuling.Q_le_aeval_homogeneousSubmodule`
(`Submission/Work/MotK/TwRuling/Q_le_aeval_homogeneousSubmodule.lean`) currently does **not**
elaborate (two `rw` failures in a proof that was written against a different simp normal form of
`Algebra.smul_def`).  This module carries the same statement with a repaired proof, so that the
`Work.MotAS` branch (node `kerAevalKleinPAS`, the chart of the AS twisted Klein curve) does not
depend on the broken file.  Nothing here is new mathematics: the argument is
`hD.spans L` + `prodSpanN_le` + `aeval_X`, exactly as in the sibling file.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Work.MotAS

open MvPolynomial

/-- **The span of the `n`-fold products of the Klein coordinates contains `Five.Q`.**  Same
statement and proof as `Work.MotK.TwRuling.Q_le_aeval_homogeneousSubmodule`, with the
`Algebra.smul_def` rewrites repaired. -/
theorem Q_le_aeval_homogeneous_v2 (K : Type) [Field K] (D : Work.MotV.KleinData K)
    (hD : D.Good) (L : Type) [Field L] [Algebra K L] (n : ℕ) :
    Work.MotK.TwRuling.Five.Q (D.E.baseChange L) n ≤
      Submodule.map (MvPolynomial.aeval (Work.MotV.kleinCoord D L)).toLinearMap
        (MvPolynomial.homogeneousSubmodule (Fin 5) L n) := by
  obtain ⟨e, he⟩ := hD.spans
  -- Every basis element `sdBas (D.E.baseChange L) m = kleinBas D L m` is an `L`-linear combination
  -- of the Klein coordinates `kleinCoord D L i`.
  have hsd : ∀ m : Fin 5, Work.MotK.TwRuling.sdBas (D.E.baseChange L) m ∈
      Submodule.span L (Set.range (Work.MotV.kleinCoord D L)) := by
    intro m
    rw [show Work.MotK.TwRuling.sdBas (D.E.baseChange L) = Work.MotV.kleinBas D L from rfl,
      he L m]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ (algebraMap K L (e m i))
      (Submodule.subset_span (Set.mem_range_self i))
  -- hence the spans of the `n`-fold products are nested
  have hA : Work.MotK.TwRuling.prodSpanN L (Work.MotK.TwRuling.sdBas (D.E.baseChange L)) n ≤
      Work.MotK.TwRuling.prodSpanN L (Work.MotV.kleinCoord D L) n :=
    Work.MotK.TwRuling.prodSpanN_le L n hsd
  -- and every `n`-fold product of Klein coordinates is the image of the corresponding monomial
  have hB : Work.MotK.TwRuling.prodSpanN L (Work.MotV.kleinCoord D L) n ≤
      Submodule.map (MvPolynomial.aeval (Work.MotV.kleinCoord D L)).toLinearMap
        (MvPolynomial.homogeneousSubmodule (Fin 5) L n) := by
    rw [Work.MotK.TwRuling.prodSpanN, Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    show (∏ i : Fin n, Work.MotV.kleinCoord D L (p i)) ∈
      Submodule.map (MvPolynomial.aeval (Work.MotV.kleinCoord D L)).toLinearMap
        (MvPolynomial.homogeneousSubmodule (Fin 5) L n)
    rw [Submodule.mem_map]
    refine ⟨∏ i : Fin n, MvPolynomial.X (p i), ?_, ?_⟩
    · have h := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin n))
        (fun i : Fin n => MvPolynomial.X (p i)) (fun _ => 1)
        (fun i _ => MvPolynomial.isHomogeneous_X L (p i))
      simpa using h
    · show MvPolynomial.aeval (Work.MotV.kleinCoord D L)
          (∏ i : Fin n, MvPolynomial.X (p i))
        = ∏ i : Fin n, Work.MotV.kleinCoord D L (p i)
      rw [map_prod]
      exact Finset.prod_congr rfl fun i _ => MvPolynomial.aeval_X _ (p i)
  exact hA.trans hB

end Work.MotAS
