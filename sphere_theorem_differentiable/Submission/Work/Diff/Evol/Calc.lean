import Mathlib
import Submission.Diff.Alg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Curvature-array algebra for Hamilton's evolution equation (definitions)

This module fixes the finite-dimensional algebra that appears in the derivation of Hamilton's
curvature evolution equation `∂ₜR = ΔR + Q(R)` (in the Uhlenbeck frame) and, more precisely, in its
*fixed-vector* form

  `∂ₜ (⟨R(a,b)d,c⟩) = (ΔR)(a,b,c,d) - Q̂(R)(a,b,c,d) + ricact(R)(a,b,c,d)`

that we use as an intermediate step.  All the objects are arrays `Curv4 n = Fin n → … → ℝ` of
curvature components in an orthonormal frame, with the workspace convention
`R i j k l = ⟨R(eᵢ,eⱼ)e_l, e_k⟩` (`Submission/Diff/Alg.lean`).

* `ricArr R i j = ∑ a, R a i a j` is the Ricci tensor of the array (the trace of the curvature);
* `Qhat R` is the quadratic term obtained from the differential Bianchi identity, the Ricci identity
  and the contracted Bianchi identity: with `[∇_m,∇_i]T = -∑_s T(…,R(e_m,e_i)a_s,…)`,

    `Q̂_{ijkl} = ∑_m ∑_a ( R_{miaj}R_{amkl} + R_{miam}R_{jakl} + R_{miak}R_{jmal} + R_{mial}R_{jmka}
                          + R_{mjam}R_{aikl} + R_{mjai}R_{makl} + R_{mjak}R_{mial} + R_{mjal}R_{mika} )`

  which is exactly `-∑_m ( [∇_m,∇_i]R_{jmkl} + [∇_m,∇_j]R_{mikl} )`;
* `ricact R` collects the two Ricci terms `-∑_a R_{ijal}Ric_{ak} + ∑_a R_{ijak}Ric_{la}` left over
  from the Ricci identity applied to `Ric` itself;
* `Xact R_{ijkl} = ∑_p (Ric_{ip}R_{pjkl} + Ric_{jp}R_{ipkl} + Ric_{kp}R_{ijpl} + Ric_{lp}R_{ijkp})` is
  the contribution of the moving orthonormal frame (the Uhlenbeck correction).

The key algebraic input (`Work.Diff.Evol.Qhat_identity`, proved in
`Submission/Work/Diff/Evol/Qhat_identity.lean`) is

  `-Q̂ + Xact + ricact = Q`  for every algebraic curvature tensor `R` (`IsAlgCurv R`),

which is exactly what converts the fixed-vector evolution equation into the Uhlenbeck-frame
statement `∂ₜ R = ΔR + Q(R)`: `Xact` are precisely the terms that `-Q̂ + ricact` is missing.
-/

namespace Work.Diff.Evol

open Submission.Diff.Alg
open Finset

variable {n : ℕ}

/-- The Ricci tensor of a curvature array: `ricArr R i j = ∑ a, R a i a j`. -/
noncomputable def ricArr (R : Curv4 n) : Fin n → Fin n → ℝ := fun i j => ∑ a, R a i a j

/-- The quadratic term `Q̂` of the expansion of `ΔR` in terms of `∇²Ric` and quadratic curvature
terms (from the differential Bianchi identity, the Ricci identity and the contracted Bianchi
identity). -/
noncomputable def Qhat (R : Curv4 n) : Curv4 n := fun i j k l =>
  ∑ m, ∑ a,
    (R m i a j * R a m k l + R m i a m * R j a k l + R m i a k * R j m a l + R m i a l * R j m k a
      + R m j a m * R a i k l + R m j a i * R m a k l + R m j a k * R m i a l + R m j a l * R m i k a)

/-- The two Ricci terms of the fixed-vector evolution equation that are left after the Ricci
identity is applied to `Ric`: `-∑_a R_{ijal}Ric_{ak} + ∑_a R_{ijak}Ric_{la}`. -/
noncomputable def ricact (R : Curv4 n) : Curv4 n := fun i j k l =>
  -∑ a, R i j a l * ricArr R a k + ∑ a, R i j a k * ricArr R l a

/-- The Uhlenbeck-frame correction: the four Ricci-action terms produced by the motion of the
orthonormal frame, `∑_p (Ric_{ip}R_{pjkl} + Ric_{jp}R_{ipkl} + Ric_{kp}R_{ijpl} + Ric_{lp}R_{ijkp})`. -/
noncomputable def Xact (R : Curv4 n) : Curv4 n := fun i j k l =>
  ∑ p, (ricArr R i p * R p j k l + ricArr R j p * R i p k l
        + ricArr R k p * R i j p l + ricArr R l p * R i j k p)

end Work.Diff.Evol
