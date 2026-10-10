import Mathlib
import Submission.Work.MotC5N3.Ruling
import Submission.Work.MotC5N3.RhoCert.asCoeff6_notMem_gen
import Submission.Work.MotC5N3.Work.asRho_ne_zero_general_ne

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.asRho_ne_zero` — the chart-2 rho input (unnormalised form)

The inverse AS quadro-cubic map `kleinRAS` does not vanish on the *unnormalised* ruling point
`asW2 D g` of the corrected chart-2 presentation over the generic point of the AS-twisted Klein
curve, for an arbitrary `𝕜`-algebra field `K` of characteristic `5` and arbitrary `g : K`.

## Route

Everything needed is already in the workspace:

* `Work.MotC5N3.RhoC.asPhi2_rho_ne_zero_gen` — the *normalised* non-vanishing
  `kleinRAS (as2a) (as2b) (as2g) (fun j => asW2 D g j / asW2 D g 0) ≠ 0`, proved from the
  self-contained `ring`-only certificate `Work.MotC5N3.RhoC.main`;
* `Work.MotC5N3.asPhi2_denom` — the normalising coordinate `asW2 D g 0` is nonzero;
* `Work.MotAS.kleinRAS_smul` — degree-`3` homogeneity of `kleinRAS`, which rescales the
  normalised point back: `kleinRAS (fun i => c * v i) = fun i => c ^ 3 * kleinRAS v i`.

Hence `kleinRAS (as2a) (as2b) (as2g) (asW2 D g) ≠ 0` as a *vector*, i.e. one of its five
components is nonzero.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Work.MotC5N3

open MvPolynomial

variable {𝕜 : Type} [Field 𝕜]

/-- The normalised ruling point is the ruling point rescaled by `(asW2 D g 0)⁻¹`. -/
theorem asW2_div_eq_inv_mul {K : Type} [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜]
    [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) (g : K) :
    (fun j => Work.MotC5N3.asW2 D g j / Work.MotC5N3.asW2 D g 0)
      = (fun j => (Work.MotC5N3.asW2 D g 0)⁻¹ * Work.MotC5N3.asW2 D g j) := by
  funext j
  rw [div_eq_mul_inv, mul_comm]

/-- **The unnormalised non-vanishing of `kleinRAS` on the ruling point**: the vector
`kleinRAS (as2a) (as2b) (as2g) (asW2 D g)` is nonzero. -/
theorem asRho_ne_zero_vec {K : Type} [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜] [Algebra 𝕜 K]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K) :
    Work.MotAS.kleinRAS (Work.MotC5N3.as2a D g) (Work.MotC5N3.as2b D g)
      (Work.MotC5N3.as2g D g) (Work.MotC5N3.asW2 D g) ≠ 0 := by
  intro h
  obtain ⟨i, hi⟩ := Work.MotC5N3.Work.asRho_of_certificate K D hD g
    (Work.MotC5N3.RhoCert.asCoeff6_notMem_gen K (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g
      (Work.MotC5N3.aK_ne_zero (K := K) D hD) (Work.MotC5N3.bK_ne_zero (K := K) D hD)
      (Work.MotC5N3.aK_sq_sub_ne (K := K) D hD))
  exact hi (by rw [h]; rfl)

theorem asRho_ne_zero (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜] [Algebra 𝕜 K]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K) :
    ∃ i : Fin 5, Work.MotAS.kleinRAS
        (algebraMap 𝕜 (RatFunc ↥(Work.MotC5N3.twistFieldAS D g)) D.a)
        (algebraMap 𝕜 (RatFunc ↥(Work.MotC5N3.twistFieldAS D g)) D.b)
        (algebraMap K (RatFunc ↥(Work.MotC5N3.twistFieldAS D g)) g)
        (Work.MotC5N3.asW2 D g) i ≠ 0 := by
  have hV := asRho_ne_zero_vec (K := K) D hD g
  by_contra hcon
  push_neg at hcon
  exact hV (funext hcon)

end Work.MotC5N3
