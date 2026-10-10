import Mathlib
import Submission.Work.MotAS.ASData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASRul.Matrices` — the AS Klein matrix and the AS ruling matrix

The characteristic-`5` (Artin–Schreier) analogues of the T-route's `Work.MotK.kleinTwM` and
`Work.MotK.TwCensus.Amat` (see `ASRULINGMAINNEW_STATE.md` and `MotK/TGen/NOTE_STRulingDiv.md`).

`kleinMAS a b g y` is the `5 × 5` skew matrix, **linear in `y`**, obtained by transporting the
split Klein matrix `Work.MotK.kleinM` along the AS coordinate changes
`x = asM w · y` (source) and `z = asN w · ẑ` (target):

  `kleinMAS a b g y = (asN w)ᵀ · kleinM a b (asM w · y) · (asN w)`,  `w⁵ = w + g`, `5 = 0`,

reduced modulo `(w⁵ − w − g, 5)`.  In characteristic `5` this matrix is `w`-free (every coefficient
of `wᵏ`, `k ≥ 1`, of the reduction is divisible by `5`), and it satisfies

  `kleinMAS a b g y *ᵥ kleinPAS a b g y = 0`

(verified symbolically over 𝔽₅), i.e. it is the AS analogue of `kleinTwM ·ᵥ kleinTwP = 0`.  Its
kernel over a target point `c` is the fibre of the AS quadro map `kleinPAS` over `[c]`, so the
matrix `AmatAS a b g c = ∂(kleinMAS · c)/∂y` — the AS analogue of `Amat` — has, on the residual
curve `V(ZIAS)`, rank `3` and kernel the ruling line (verified numerically over 𝔽₅ at all four
`𝔽₅`-points of `V(ZIAS)`, `(a,b,g) = (1,1,1)`).

Both definitions are *bare data*: the accompanying identities are stated in the sibling files.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotAS.ASRul

variable {R : Type*} [CommRing R]

/-- **The AS Klein matrix** `MAS(y)`, linear in `y` and skew.  Its Pfaffian vector is *not*
`kleinPAS` (the Pfaffian vector of a skew matrix is congruence-equivariant, while `kleinPAS` is the
contragredient transport of `kleinP`), but `MAS(y) *ᵥ kleinPAS y = 0` — which is what the ruling
needs. -/
def kleinMAS (a b g : R) (y : Fin 5 → R) : Matrix (Fin 5) (Fin 5) R :=
  !![0, (-2)*a*(y 4) + b*(y 4), a*(y 3) + (2)*b*(y 3), -a*(y 2) + (-2)*a*(y 4) + (-2)*b*(y 2) - b*(y 4), (2)*a*(y 1) + (2)*a*(y 3) - b*(y 1) + b*(y 3);
      -((-2)*a*(y 4) + b*(y 4)), 0, (-2)*a*(y 2) + (2)*a*(y 4) + b*(y 2) + b*(y 4), a*(y 1) - a*(y 3) + (2)*b*(y 1) + (2)*b*(y 3), -a*(y 0) - a*(y 2) + a*(y 4) + (-2)*b*(y 0) + (2)*b*(y 2) + (2)*b*(y 4);
      -(a*(y 3) + (2)*b*(y 3)), -((-2)*a*(y 2) + (2)*a*(y 4) + b*(y 2) + b*(y 4)), 0, (-2)*a*(y 0) - a*(y 2) + a*(y 4) + b*(y 0) + (2)*b*(y 2) + (2)*b*(y 4), a*g*(y 4) + (-2)*a*(y 1) + (2)*a*(y 3) + (2)*b*g*(y 4) - b*(y 1) - b*(y 3);
      -(-a*(y 2) + (-2)*a*(y 4) + (-2)*b*(y 2) - b*(y 4)), -(a*(y 1) - a*(y 3) + (2)*b*(y 1) + (2)*b*(y 3)), -((-2)*a*(y 0) - a*(y 2) + a*(y 4) + b*(y 0) + (2)*b*(y 2) + (2)*b*(y 4)), 0, (-2)*a*g*(y 3) + a*(y 0) + (2)*a*(y 2) + (-2)*a*(y 4) + b*g*(y 3) + (-2)*b*(y 0) - b*(y 2) - b*(y 4);
      -((2)*a*(y 1) + (2)*a*(y 3) - b*(y 1) + b*(y 3)), -(-a*(y 0) - a*(y 2) + a*(y 4) + (-2)*b*(y 0) + (2)*b*(y 2) + (2)*b*(y 4)), -(a*g*(y 4) + (-2)*a*(y 1) + (2)*a*(y 3) + (2)*b*g*(y 4) - b*(y 1) - b*(y 3)), -((-2)*a*g*(y 3) + a*(y 0) + (2)*a*(y 2) + (-2)*a*(y 4) + b*g*(y 3) + (-2)*b*(y 0) - b*(y 2) - b*(y 4)), 0]

/-- **The AS ruling matrix**, the coefficient matrix of `y ↦ kleinMAS a b g y *ᵥ c`: the linear
system whose kernel is the fibre of `kleinPAS` over `[c]`.  Entries are linear in `c`. -/
def AmatAS (a b g : R) (c : Fin 5 → R) : Matrix (Fin 5) (Fin 5) R :=
  !![0, (2)*a*(c 4) - b*(c 4), -a*(c 3) + (-2)*b*(c 3), a*(c 2) + (2)*a*(c 4) + (2)*b*(c 2) + b*(c 4), (-2)*a*(c 1) + (-2)*a*(c 3) + b*(c 1) - b*(c 3);
      -a*(c 4) + (-2)*b*(c 4), a*(c 3) + (2)*b*(c 3), (-2)*a*(c 2) - a*(c 4) + b*(c 2) + (2)*b*(c 4), -a*(c 3) + (2)*b*(c 3), (2)*a*(c 0) + (2)*a*(c 2) + a*(c 4) - b*(c 0) + b*(c 2) + (2)*b*(c 4);
      (-2)*a*(c 3) + b*(c 3), (-2)*a*(c 4) - b*(c 4), (2)*a*(c 1) - a*(c 3) - b*(c 1) + (2)*b*(c 3), -a*(c 0) + (2)*a*(c 4) + (-2)*b*(c 0) - b*(c 4), a*g*(c 4) + (-2)*a*(c 1) + a*(c 3) + (2)*b*g*(c 4) - b*(c 1) + (2)*b*(c 3);
      (2)*a*(c 2) + a*(c 4) - b*(c 2) + (-2)*b*(c 4), -a*(c 1) + (-2)*b*(c 1), a*(c 0) + a*(c 2) + (2)*a*(c 4) + (2)*b*(c 0) + (-2)*b*(c 2) - b*(c 4), (-2)*a*g*(c 4) + a*(c 1) + b*g*(c 4) + (-2)*b*(c 1), (2)*a*(c 0) - a*(c 2) + (-2)*a*(c 4) + b*(c 0) + (-2)*b*(c 2) - b*(c 4);
      a*(c 1) - a*(c 3) + (2)*b*(c 1) + (2)*b*(c 3), (-2)*a*(c 0) + (2)*a*(c 2) + b*(c 0) + b*(c 2), a*(c 1) + (-2)*a*(c 3) + (-2)*b*(c 1) + b*(c 3), (2)*a*g*(c 3) + (-2)*a*(c 0) + (-2)*a*(c 2) - b*g*(c 3) - b*(c 0) + b*(c 2), -a*g*(c 2) - a*(c 1) + (2)*a*(c 3) + (-2)*b*g*(c 2) + (-2)*b*(c 1) + b*(c 3)]

end Work.MotAS.ASRul
