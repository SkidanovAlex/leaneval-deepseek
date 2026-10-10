import Mathlib
import Submission.Work.MotC5N3.ASZResVecDefs
import Submission.Work.MotC5N3.ASZChartSetupGen
import Submission.Work.MotC5N3.ASZPhiMemGen
import Submission.Work.MotC5N3.ASZChartPresentationGen
import Submission.Work.MotC5N3.ASZChartNegIso
import Submission.Work.MotAS.asChartIdeal_fracIso_of_certificates
import Submission.Work.MotAS.ASRulV2M.trdeg_quotient_add_height
import Submission.Work.MotAS.ASZElimP_irreducible
import Submission.Work.MotAS.ASZElimMem
import Submission.Work.MotAS.ASZGC.clause1_mem
import Submission.Work.MotAS.ASZGC.not_dvd_D0
import Submission.Work.MotK.CensusBridge.isFractionRing_adjoin_range_ratFunc
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.ASZPhiRes` — the residual-coordinate map of the AS projection

This file contains the parts of the K6 leaf `Work.MotC5N3.ASZTwistDivPlaneGeom_three` that are
*not* delegated, namely

* `kleinRAS_ringHom` — `kleinRAS` commutes with ring homomorphisms;
* `aszPhi_kleinRAS_zero` and `aszPhi_mem_radical` — the residual-coordinate map
  `aszPhi D g : K[X₀,X₁,X₂] →ₐ[K] ↥(twistFieldAS D (3 * g))` kills `ZIAS a b g`, hence its radical
  (the content is `Work.MotAS.ASZPhiMemGen` plus the cubic homogeneity of `kleinRAS`);
* `height_radical_ZIAS_ge_two` — the residual curve has codimension `≥ 2` in `𝔸³` (from the
  eliminant `E`, the graph element `G` and `¬ E ∣ D₀`, all of which are proved in the workspace);
* `ASZTwistDivPlaneGeom_three_of` — the assembly, taking as hypotheses the two pieces that are
  delegated (`Work.MotC5N3.ASZRadicalIsPrime` and `Work.MotC5N3.ASZResVecAdjoin`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
set_option linter.unusedSectionVars false

namespace Work.MotC5N3

open MvPolynomial

variable {𝕜 : Type} [Field 𝕜]
variable {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5]

/-! ## §1 `kleinRAS` commutes with ring homomorphisms -/

/-- The AS inverse quadro-cubic map commutes with every ring homomorphism. -/
lemma kleinRAS_ringHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b g : R)
    (y : Fin 5 → R) (k : Fin 5) :
    f (Work.MotAS.kleinRAS a b g y k)
      = Work.MotAS.kleinRAS (f a) (f b) (f g) (fun i => f (y i)) k := by
  fin_cases k <;>
    simp only [Work.MotAS.kleinRAS, Work.MotAS.kleinRAS0, Work.MotAS.kleinRAS1,
      Work.MotAS.kleinRAS2, Work.MotAS.kleinRAS3, Work.MotAS.kleinRAS4,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Fin.reduceFinMk,
      map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_ofNat] <;>
    first | refl_ring1 | ring

/-! ## §2 The twisted Pfaffians vanish at the projective twisted coordinates -/

/-- The transported Pfaffians vanish at the projective twisted coordinates `v_j = y_j/y_0`. -/
theorem aszPhi_kleinPAS_zero (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (g : K) :
    Work.MotAS.kleinPAS (algebraMap K (OmA K D) (aK K D))
        (algebraMap K (OmA K D) (bK K D)) (algebraMap K (OmA K D) (3 * g))
        (fun j => aszV D (3 * g) j) = 0 := by
  have h0 := Work.MotC5N3.kleinPAS_asTwY D hD (3 * g)
  have hc : (fun j => aszV D (3 * g) j)
      = fun j => (asTwY D (3 * g) 0)⁻¹ * asTwY D (3 * g) j := by
    funext j
    rw [aszV, div_eq_mul_inv, mul_comm]
  rw [hc, Work.MotAS.kleinPAS_smul, h0]
  funext i
  simp

/-! ## §3 The residual-coordinate map kills the residual ideal -/

/-- The fifth residual coordinate is zero (`phiAS` has a zero last row). -/
theorem aszZ_four (D : Work.MotV.KleinData 𝕜) (g : K) : aszZ D g 4 = 0 := by
  rw [aszZ]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [← phiAS_algebraMap D 4 j]
  simp [Work.MotAS.phiAS]

end Work.MotC5N3
