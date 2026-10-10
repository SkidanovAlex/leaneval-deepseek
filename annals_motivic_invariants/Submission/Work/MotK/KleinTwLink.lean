/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.KleinTwI1
import Submission.Work.MotK.TwDataMod5
import Submission.Work.MotK.LinkTwData
import Submission.Work.MotK.KleinTwQ_stereo
import Submission.Work.MotK.KleinTwBilinStereo
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The T-twisted Crauder--Katz link data: the corrected target-side dual secant quintic

`Work.MotK.kleinTwSDual` is the *plain* Kummer twist `z_i = w^i z_i` (`w^5 = h`) of the dual
secant quintic `s' = kleinSecDual`; `Work.MotK.kleinTwR` is the *inverse* twist
`z_i = w^{4i} z_i` of the inverse quadro-cubic map `R`.  Those two conventions are the ones
under which the twisted inverse relation

  `kleinTwR (kleinTwP y) = kleinTwS y • y`   (`KleinTwI1`)

holds, and they are *not* the same convention: consequently the naive twisted forms of the
identities I2, I3, I4 of `Submission.Work.MotK.KleinIdents` are **false** for `h ≠ 1`
(the audit `AUDIT_LinkCertT.md` records the counterexample).

The correct target-side object is the **inverse** (reduced-exponent) twist of `s'`:

* `kleinTwSDualInv a b h y := s'(a, b, fun i => w ^ (4 * i % 5) * y_i)` collected in `h = w^5`
  (a polynomial in `h` and `y`, index-degree zero, of `h`-degree `≤ 16`);

with it the twisted link identities read

* `KleinTwI2inv`: `kleinTwP (kleinTwR z) = kleinTwSDualInv z • z`   (twisted I2),
* `KleinTwI3inv`: `kleinTwSDualInv (kleinTwP y) = kleinTwS y ^ 2`   (twisted I3),

and the link unit condition (`KleinTwLinkUnit`) is

  `b(p, kleinTwR (kleinTwP (y(v)))) * kleinTwSDualInv (kleinTwP (y(v)))
     = -(kleinTwS (y(v)))^2 * b(p,v) * (b(p,v) * kleinTwS (y(v)))`

for `y(v) = kleinTwStereo a b h p v` the inverse stereographic projection from a point `p` of
the T-invariant quadric `{kleinTwQ = 0}`.  This is the `T`-twist (`K3_T` / `T8`) input of the
K-route deliverable `Work.MotK.LinkCertT`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

namespace Work.MotK

variable {R : Type*} [CommRing R]

/-- **The `T`-twisted dual secant quintic in the inverse Kummer twist**
`z_i = w ^ (4 * i % 5) * y_i`, collected in `h = w ^ 5`.  It is the target-side equation of the
twisted Crauder--Katz link: the object `s'` of the split data has to be replaced by it, because
the target-side coordinates of the twisted link are the inverse twist of the split ones. -/
def kleinTwSDualInv (a b h : R) (y : Fin 5 → R) : R :=
  2*a^(3:ℕ)*b^(7:ℕ)*h*(y 0)^(3:ℕ)*(y 2)*(y 3)
    + 2*a^(3:ℕ)*b^(7:ℕ)*h^(3:ℕ)*(y 1)^(3:ℕ)*(y 3)*(y 4)
    + 2*a^(3:ℕ)*b^(7:ℕ)*h^(2:ℕ)*(y 0)*(y 2)^(3:ℕ)*(y 4)
    + 2*a^(3:ℕ)*b^(7:ℕ)*h^(2:ℕ)*(y 0)*(y 1)*(y 3)^(3:ℕ)
    + 2*a^(3:ℕ)*b^(7:ℕ)*h^(2:ℕ)*(y 1)*(y 2)*(y 4)^(3:ℕ)
    + 2*a^(7:ℕ)*b^(3:ℕ)*h*(y 0)^(3:ℕ)*(y 1)*(y 4)
    + 2*a^(7:ℕ)*b^(3:ℕ)*h^(3:ℕ)*(y 0)*(y 1)^(3:ℕ)*(y 2)
    + 2*a^(7:ℕ)*b^(3:ℕ)*h^(3:ℕ)*(y 1)*(y 2)^(3:ℕ)*(y 3)
    + 2*a^(7:ℕ)*b^(3:ℕ)*h*(y 0)*(y 3)*(y 4)^(3:ℕ)
    + 2*a^(7:ℕ)*b^(3:ℕ)*h^(2:ℕ)*(y 2)*(y 3)^(3:ℕ)*(y 4)
    + 3*a^(4:ℕ)*b^(6:ℕ)*h^(2:ℕ)*(y 0)^(2:ℕ)*(y 1)*(y 2)^(2:ℕ)
    + 3*a^(4:ℕ)*b^(6:ℕ)*h*(y 0)^(2:ℕ)*(y 3)^(2:ℕ)*(y 4)
    + 3*a^(4:ℕ)*b^(6:ℕ)*h^(3:ℕ)*(y 1)^(2:ℕ)*(y 2)*(y 3)^(2:ℕ)
    + 3*a^(4:ℕ)*b^(6:ℕ)*h^(2:ℕ)*(y 0)*(y 1)^(2:ℕ)*(y 4)^(2:ℕ)
    + 3*a^(4:ℕ)*b^(6:ℕ)*h^(2:ℕ)*(y 2)^(2:ℕ)*(y 3)*(y 4)^(2:ℕ)
    - 3*a^(6:ℕ)*b^(4:ℕ)*h^(2:ℕ)*(y 0)^(2:ℕ)*(y 1)^(2:ℕ)*(y 3)
    - 3*a^(6:ℕ)*b^(4:ℕ)*h*(y 0)^(2:ℕ)*(y 2)*(y 4)^(2:ℕ)
    - 3*a^(6:ℕ)*b^(4:ℕ)*h^(3:ℕ)*(y 1)^(2:ℕ)*(y 2)^(2:ℕ)*(y 4)
    - 3*a^(6:ℕ)*b^(4:ℕ)*h^(2:ℕ)*(y 0)*(y 2)^(2:ℕ)*(y 3)^(2:ℕ)
    - 3*a^(6:ℕ)*b^(4:ℕ)*h^(2:ℕ)*(y 1)*(y 3)^(2:ℕ)*(y 4)^(2:ℕ)
    - 6*a^(5:ℕ)*b^(5:ℕ)*h^(2:ℕ)*(y 0)*(y 1)*(y 2)*(y 3)*(y 4)
    - a*b^(9:ℕ)*h^(2:ℕ)*(y 0)^(2:ℕ)*(y 1)^(2:ℕ)*(y 3)
    - a*b^(9:ℕ)*h*(y 0)^(2:ℕ)*(y 2)*(y 4)^(2:ℕ)
    - a*b^(9:ℕ)*h^(3:ℕ)*(y 1)^(2:ℕ)*(y 2)^(2:ℕ)*(y 4)
    - a*b^(9:ℕ)*h^(2:ℕ)*(y 0)*(y 2)^(2:ℕ)*(y 3)^(2:ℕ)
    - a*b^(9:ℕ)*h^(2:ℕ)*(y 1)*(y 3)^(2:ℕ)*(y 4)^(2:ℕ)
    + a^(10:ℕ)*h^(2:ℕ)*(y 0)*(y 1)*(y 2)*(y 3)*(y 4)
    - a^(2:ℕ)*b^(8:ℕ)*h*(y 0)^(3:ℕ)*(y 1)*(y 4)
    - a^(2:ℕ)*b^(8:ℕ)*h^(3:ℕ)*(y 0)*(y 1)^(3:ℕ)*(y 2)
    - a^(2:ℕ)*b^(8:ℕ)*h^(3:ℕ)*(y 1)*(y 2)^(3:ℕ)*(y 3)
    - a^(2:ℕ)*b^(8:ℕ)*h*(y 0)*(y 3)*(y 4)^(3:ℕ)
    - a^(2:ℕ)*b^(8:ℕ)*h^(2:ℕ)*(y 2)*(y 3)^(3:ℕ)*(y 4)
    - a^(5:ℕ)*b^(5:ℕ)*(y 0)^(5:ℕ)
    - a^(5:ℕ)*b^(5:ℕ)*h^(4:ℕ)*(y 1)^(5:ℕ)
    - a^(5:ℕ)*b^(5:ℕ)*h^(3:ℕ)*(y 2)^(5:ℕ)
    - a^(5:ℕ)*b^(5:ℕ)*h^(2:ℕ)*(y 3)^(5:ℕ)
    - a^(5:ℕ)*b^(5:ℕ)*h*(y 4)^(5:ℕ)
    + a^(8:ℕ)*b^(2:ℕ)*h*(y 0)^(3:ℕ)*(y 2)*(y 3)
    + a^(8:ℕ)*b^(2:ℕ)*h^(3:ℕ)*(y 1)^(3:ℕ)*(y 3)*(y 4)
    + a^(8:ℕ)*b^(2:ℕ)*h^(2:ℕ)*(y 0)*(y 2)^(3:ℕ)*(y 4)
    + a^(8:ℕ)*b^(2:ℕ)*h^(2:ℕ)*(y 0)*(y 1)*(y 3)^(3:ℕ)
    + a^(8:ℕ)*b^(2:ℕ)*h^(2:ℕ)*(y 1)*(y 2)*(y 4)^(3:ℕ)
    - a^(9:ℕ)*b*h^(2:ℕ)*(y 0)^(2:ℕ)*(y 1)*(y 2)^(2:ℕ)
    - a^(9:ℕ)*b*h*(y 0)^(2:ℕ)*(y 3)^(2:ℕ)*(y 4)
    - a^(9:ℕ)*b*h^(3:ℕ)*(y 1)^(2:ℕ)*(y 2)*(y 3)^(2:ℕ)
    - a^(9:ℕ)*b*h^(2:ℕ)*(y 0)*(y 1)^(2:ℕ)*(y 4)^(2:ℕ)
    - a^(9:ℕ)*b*h^(2:ℕ)*(y 2)^(2:ℕ)*(y 3)*(y 4)^(2:ℕ)
    - b^(10:ℕ)*h^(2:ℕ)*(y 0)*(y 1)*(y 2)*(y 3)*(y 4)

/-- The inverse Kummer twist of the dual secant quintic: substituting `z_i = w ^ (4 * i % 5) * y_i`
into `s'` gives `kleinTwSDualInv` at `h = w ^ 5`. -/
theorem KleinSecDualInvTwist (a b w : R) (y : Fin 5 → R) :
    kleinSecDual a b (fun i => w ^ ((4 * (i : ℕ)) % 5) * y i)
      = kleinTwSDualInv a b (w ^(5:ℕ)) y := by
  simp only [kleinSecDual, kleinTwSDualInv]
  norm_num
  refl_ring1

/-! ## Index normalization and component read-off lemmas

`fin_cases` replaces the index `k` by a `Fin.mk` with an opaque bound proof, while the definitions
use the `OfNat` literals; the following `rfl`-lemmas rewrite both forms to the literal, and the
`'`-versions of the component read-off lemmas of `Submission.Work.MotK.KleinTwI1` are the
`Fin.mk`-indexed forms which `fin_cases` produces. -/

theorem fin5_zero (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
theorem fin5_one (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
theorem fin5_two (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
theorem fin5_three (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
theorem fin5_four (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl

theorem kleinTwP_zero' (a b h : R) (y : Fin 5 → R) (h0 : 0 < 5) :
    kleinTwP a b h y ⟨0, h0⟩ = kleinTwP0 a b h y := rfl
theorem kleinTwP_one' (a b h : R) (y : Fin 5 → R) (h0 : 1 < 5) :
    kleinTwP a b h y ⟨1, h0⟩ = kleinTwP1 a b h y := rfl
theorem kleinTwP_two' (a b h : R) (y : Fin 5 → R) (h0 : 2 < 5) :
    kleinTwP a b h y ⟨2, h0⟩ = kleinTwP2 a b h y := rfl
theorem kleinTwP_three' (a b h : R) (y : Fin 5 → R) (h0 : 3 < 5) :
    kleinTwP a b h y ⟨3, h0⟩ = kleinTwP3 a b h y := rfl
theorem kleinTwP_four' (a b h : R) (y : Fin 5 → R) (h0 : 4 < 5) :
    kleinTwP a b h y ⟨4, h0⟩ = kleinTwP4 a b h y := rfl

theorem kleinTwR_zero' (a b h : R) (y : Fin 5 → R) (h0 : 0 < 5) :
    kleinTwR a b h y ⟨0, h0⟩ = kleinTwR0 a b h y := rfl
theorem kleinTwR_one' (a b h : R) (y : Fin 5 → R) (h0 : 1 < 5) :
    kleinTwR a b h y ⟨1, h0⟩ = kleinTwR1 a b h y := rfl
theorem kleinTwR_two' (a b h : R) (y : Fin 5 → R) (h0 : 2 < 5) :
    kleinTwR a b h y ⟨2, h0⟩ = kleinTwR2 a b h y := rfl
theorem kleinTwR_three' (a b h : R) (y : Fin 5 → R) (h0 : 3 < 5) :
    kleinTwR a b h y ⟨3, h0⟩ = kleinTwR3 a b h y := rfl
theorem kleinTwR_four' (a b h : R) (y : Fin 5 → R) (h0 : 4 < 5) :
    kleinTwR a b h y ⟨4, h0⟩ = kleinTwR4 a b h y := rfl

/-- **The twisted inverse relation I2** (the corrected form of the naive `I2'`, which is false):
`kleinTwP (kleinTwR z) = kleinTwSDualInv z • z`. -/
theorem KleinTwI2inv (a b h : R) (z : Fin 5 → R) (k : Fin 5) :
    kleinTwP a b h (kleinTwR a b h z) k = kleinTwSDualInv a b h z * z k := by
  fin_cases k <;>
    simp only [fin5_zero, fin5_one, fin5_two, fin5_three, fin5_four,
      kleinTwP_zero', kleinTwP_one', kleinTwP_two', kleinTwP_three', kleinTwP_four',
      kleinTwP_zero, kleinTwP_one, kleinTwP_two, kleinTwP_three, kleinTwP_four,
      kleinTwR_zero', kleinTwR_one', kleinTwR_two', kleinTwR_three', kleinTwR_four',
      kleinTwR_zero, kleinTwR_one, kleinTwR_two, kleinTwR_three, kleinTwR_four,
      kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4,
      kleinTwR0, kleinTwR1, kleinTwR2, kleinTwR3, kleinTwR4, kleinTwSDualInv] <;>
    refl_ring1

/-- **The twisted secant relation I3** (the corrected form of the naive `I3'`, which is false):
`kleinTwSDualInv (kleinTwP y) = (kleinTwS y) ^ 2`. -/
theorem KleinTwI3inv (a b h : R) (y : Fin 5 → R) :
    kleinTwSDualInv a b h (kleinTwP a b h y) = kleinTwS a b h y ^(2:ℕ) := by
  simp only [kleinTwSDualInv, kleinTwP_zero, kleinTwP_one, kleinTwP_two, kleinTwP_three,
    kleinTwP_four, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4, kleinTwS]
  norm_num
  refl_ring1

/-- The polar form of the T-twisted quadric is linear in its second argument. -/
theorem kleinTwBilin_smul_right' (a b h : R) (u v : Fin 5 → R) (c : R) :
    kleinTwBilin a b h u (fun i => c * v i) = c * kleinTwBilin a b h u v := by
  simp only [kleinTwBilin, kleinTwQ, kleinTwP0, Pi.add_apply]
  refl_ring1

/-- **The unit condition of the T-twisted link** (`K3_T` / node `T8`).

With `y(v) = kleinTwStereo a b h p v` the inverse stereographic projection from a point `p` of the
T-invariant quadric `{kleinTwQ = 0}` and `f = kleinTwP ∘ kleinTwStereo` the Cremona map of the
twisted Crauder--Katz link, pulling back the target equation
`G_hom(w) = kleinTwBilin a b h p (kleinTwR w) * kleinTwSDualInv w` along `f` gives

  `-s(y(v))^2 * b(p,v) * F_hom(v)`,   `F_hom(v) = b(p,v) * s(y(v))`,

so that `G_hom ∘ f = -(s(y)) * F_hom ^ 2` is a unit multiple of a power of `F_hom` in the
localisation `K[v]_F`, which is the unit condition making `f^*` an isomorphism of the two charts.
The proof is the chain

  `b(p, R(P(y))) * s'(P(y)) = b(p, s(y)·y) * s(y)^2 = s(y)·b(p,y)·s(y)^2 = -s(y)^3 b(p,v)^2`,

using `KleinTwI1` (`R(P y) = s(y)·y`), `KleinTwI3inv` (`s'(P y) = s(y)^2`), the linearity of `b`
in its second argument, and `KleinTwBilinStereo` together with `kleinTwQ p = 0`. -/
theorem KleinTwLinkUnit (a b h : R) (p v : Fin 5 → R) (hp : kleinTwQ a b h p = 0) :
    kleinTwBilin a b h p (kleinTwR a b h (kleinTwP a b h (kleinTwStereo a b h p v)))
        * kleinTwSDualInv a b h (kleinTwP a b h (kleinTwStereo a b h p v))
      = -(kleinTwS a b h (kleinTwStereo a b h p v)) ^(2:ℕ) * kleinTwBilin a b h p v
        * (kleinTwBilin a b h p v * kleinTwS a b h (kleinTwStereo a b h p v)) := by
  set y : Fin 5 → R := kleinTwStereo a b h p v with hy
  have hI1 : kleinTwR a b h (kleinTwP a b h y)
      = fun i => kleinTwS a b h y * y i := funext fun i => KleinTwI1 a b h y i
  have hsm : kleinTwBilin a b h p (fun i => kleinTwS a b h y * y i)
      = kleinTwS a b h y * kleinTwBilin a b h p y :=
    kleinTwBilin_smul_right' a b h p y (kleinTwS a b h y)
  have hst : kleinTwBilin a b h p y = -(kleinTwBilin a b h p v) ^(2:ℕ) := by
    rw [hy, KleinTwBilinStereo a b h p v, hp]
    refl_ring1
  have hI3 : kleinTwSDualInv a b h (kleinTwP a b h y) = (kleinTwS a b h y) ^(2:ℕ) :=
    KleinTwI3inv a b h y
  rw [hI1, hsm, hI3, hst]
  refl_ring1

/-- The extended stereographic map: taking `v = x - x_0 * p` puts `v` on the line through `p` and
`x` with `v_0 = 0` (the affine chart of `ℙ³ ≅ Q̃` used by the link). -/
def kleinTwPi {R : Type*} [CommRing R] (p x : Fin 5 → R) : Fin 5 → R :=
  fun i => x i - x 0 * p i

/-- The unconditional form of the inverse-stereographic identity: the stereographic
parametrisation at `v = x - x_0 p` is `q(x)p - b(p,x)x`, corrected by the `q(p)`-terms. -/
theorem KleinTwStereo_pi_aux {R : Type*} [CommRing R] (a b h : R) (p x : Fin 5 → R) :
    kleinTwStereo a b h p (kleinTwPi p x)
      = fun i => kleinTwQ a b h x * p i - kleinTwBilin a b h p x * x i
          - kleinTwQ a b h p * (x 0) ^(2:ℕ) * p i + 2 * kleinTwQ a b h p * x 0 * x i := by
  funext i
  simp only [kleinTwPi, kleinTwStereo, kleinTwBilin, kleinTwQ, kleinTwP0, Pi.add_apply,
    Pi.sub_apply]
  refl_ring1

/-- **The inverse-stereographic identity.**  For `p` on the quadric (`kleinTwQ p = 0`), the
stereographic parametrisation at the point `v = x - x_0 p` of the line through `p` and `x` is

  `y(x - x_0 p) = q(x)·p - b(p,x)·x`,

in particular `y(x - x_0 p) = -b(p,x)·x` for `x` on the quadric.  This is the inverse of the
parametrisation `kleinTwStereo` used by the link: it makes `f = P ∘ y` invertible on the chart
`v_0 = 0`, with `π(x) = x - x_0 p` the (polynomial) projection from `p`. -/
theorem KleinTwStereo_pi {R : Type*} [CommRing R] (a b h : R) (p x : Fin 5 → R)
    (hp : kleinTwQ a b h p = 0) :
    kleinTwStereo a b h p (kleinTwPi p x)
      = fun i => kleinTwQ a b h x * p i - kleinTwBilin a b h p x * x i := by
  rw [KleinTwStereo_pi_aux, hp]
  funext i
  refl_ring1

/-! ## The two unit conditions in the cancellation-free and divided forms, and I4'

`Submission.Work.MotK.TwDataMod5` provides the corrected target-side data (`kleinTwSDualV`, the
same polynomial as `kleinTwSDualInv`, together with the identities I2', I3', I4' and the
homogeneity lemmas).  Here we record the I4' in the form the link uses and assemble the second
unit condition of the link. -/

/-- The corrected target-side dual secant quintic of `TwDataMod5` is the polynomial
`kleinTwSDualInv`. -/
theorem kleinTwSDualInv_eq_kleinTwSDualV (a b h : R) (y : Fin 5 → R) :
    kleinTwSDualInv a b h y = Work.MotK.kleinTwSDualV a b h y := by
  simp only [kleinTwSDualInv, Work.MotK.kleinTwSDualV]
  refl_ring1

/-- **I4' in multiplied form** (no cancellation, every component): composing `KleinTwI1` with
`KleinTwI2inv` and the cube-homogeneity of `kleinTwR`. -/
theorem kleinTwI4_mul (a b h : R) (z : Fin 5 → R) (k : Fin 5) :
    kleinTwR a b h z k * kleinTwS a b h (kleinTwR a b h z)
      = kleinTwR a b h z k * kleinTwSDualInv a b h z ^(3:ℕ) := by
  have h1 : kleinTwR a b h (kleinTwP a b h (kleinTwR a b h z))
      = fun i => kleinTwS a b h (kleinTwR a b h z) * kleinTwR a b h z i :=
    funext fun i => KleinTwI1 a b h (kleinTwR a b h z) i
  have h2 : kleinTwP a b h (kleinTwR a b h z) = fun i => kleinTwSDualInv a b h z * z i :=
    funext fun i => KleinTwI2inv a b h z i
  rw [h2, Work.MotK.kleinTwR_homog (lam := kleinTwSDualInv a b h z)] at h1
  have h0 := congrFun h1 k
  rw [mul_comm (kleinTwSDualInv a b h z ^(3:ℕ)),
    mul_comm (kleinTwS a b h (kleinTwR a b h z))] at h0
  exact h0.symm

/-- **I4'**: `s(R z) = kleinTwSDualInv z ^ 3`, whenever `kleinTwR z ≠ 0` (in a domain). -/
theorem KleinTwI4inv (a b h : R) [IsDomain R] (z : Fin 5 → R)
    (hz : ∃ k, kleinTwR a b h z k ≠ 0) :
    kleinTwS a b h (kleinTwR a b h z) = kleinTwSDualInv a b h z ^(3:ℕ) := by
  obtain ⟨k, hk⟩ := hz
  exact mul_left_cancel₀ hk (kleinTwI4_mul a b h z k)

/-- The polar form at `(p, p)`: `b(p,p) = 2 q(p)`. -/
theorem kleinTwBilin_self' (a b h : R) (v : Fin 5 → R) :
    kleinTwBilin a b h v v = 2 * kleinTwQ a b h v :=
  Work.MotK.kleinTwBilin_self a b h v

/-- The polar form of the projection: `b(p, x - x_0 p) = b(p,x) - x_0·b(p,p)`. -/
theorem kleinTwBilin_pi (a b h : R) (p x : Fin 5 → R) :
    kleinTwBilin a b h p (kleinTwPi p x)
      = kleinTwBilin a b h p x - x 0 * kleinTwBilin a b h p p := by
  simp only [kleinTwPi, kleinTwBilin, kleinTwQ, kleinTwP0, Pi.add_apply, Pi.sub_apply]
  refl_ring1

/-- For `p` on the quadric the polar form is unchanged by the projection: `b(p, x - x_0 p) = b(p,x)`. -/
theorem kleinTwBilin_pi_eq (a b h : R) (p x : Fin 5 → R) (hp : kleinTwQ a b h p = 0) :
    kleinTwBilin a b h p (kleinTwPi p x) = kleinTwBilin a b h p x := by
  rw [kleinTwBilin_pi, kleinTwBilin_self', hp]
  refl_ring1

/-- The corrected target equation of the T-twisted link: `G_hom(w) = b(p, R w) · s'(w)`. -/
def kleinTwGhom' (a b h : R) (p w : Fin 5 → R) : R :=
  kleinTwBilin a b h p (kleinTwR a b h w) * kleinTwSDualInv a b h w

/-- **The second unit condition of the T-twisted link.**

With `F_hom(v) = b(p,v)·s(y(v))` the source equation, `G_hom(w) = b(p,R w)·s'(w)` the corrected
target equation, and `π(x) = x - x_0·p` the polynomial projection from `p`, pulling `F_hom` back
along `g = π ∘ R` gives

  `F_hom(g(w)) = -b(p,R w)^3 · G_hom(w)^3`,

a unit multiple of `G_hom^3` in `K[w]_{G_hom}` (`b(p,R w) | G_hom`).  This is the inverse of
`KleinTwLinkUnit` and, together with it, gives the chart isomorphism of the twisted link. -/
theorem KleinTwLinkUnitInv (a b h : R) [IsDomain R] (p w : Fin 5 → R)
    (hp : kleinTwQ a b h p = 0) (hw : w 0 = 0)
    (hR : ∃ k, kleinTwR a b h w k ≠ 0) :
    kleinTwFhom a b h p (kleinTwPi p (kleinTwR a b h w))
      = -(kleinTwBilin a b h p (kleinTwR a b h w)) ^(3:ℕ) * kleinTwGhom' a b h p w ^(3:ℕ) := by
  -- `R(w)` lies on the quadric because `w_0 = 0` and `P(R w) = s'(w) w`
  have hx0 : kleinTwQ a b h (kleinTwR a b h w) = 0 := by
    rw [show kleinTwQ a b h (kleinTwR a b h w) = kleinTwP a b h (kleinTwR a b h w) 0 from rfl,
      KleinTwI2inv, hw, mul_zero]
  -- the stereographic parametrisation at the projection of `R(w)`
  have hpi : kleinTwStereo a b h p (kleinTwPi p (kleinTwR a b h w))
      = fun i => -(kleinTwBilin a b h p (kleinTwR a b h w)) * kleinTwR a b h w i := by
    rw [KleinTwStereo_pi a b h p (kleinTwR a b h w) hp, hx0]
    funext i
    refl_ring1
  have hbpi : kleinTwBilin a b h p (kleinTwPi p (kleinTwR a b h w))
      = kleinTwBilin a b h p (kleinTwR a b h w) :=
    kleinTwBilin_pi_eq a b h p (kleinTwR a b h w) hp
  have hS : kleinTwS a b h (kleinTwStereo a b h p (kleinTwPi p (kleinTwR a b h w)))
      = (-(kleinTwBilin a b h p (kleinTwR a b h w))) ^(5:ℕ) * kleinTwS a b h (kleinTwR a b h w) := by
    rw [hpi]
    exact Work.MotK.kleinTwS_homog a b h (-(kleinTwBilin a b h p (kleinTwR a b h w)))
      (kleinTwR a b h w)
  have hI4 : kleinTwS a b h (kleinTwR a b h w) = kleinTwSDualInv a b h w ^(3:ℕ) :=
    KleinTwI4inv a b h w hR
  rw [kleinTwFhom, hbpi, hS, hI4, kleinTwGhom']
  refl_ring1

/-! ## Assembly of a chart isomorphism from two homomorphisms -/

/-- A `K`-algebra homomorphism whose two composites with a second `K`-algebra homomorphism are
bijective is an isomorphism.  This is the last step of the chart isomorphism of the link: the two
pullbacks `f^*` and `g^*` are mutually inverse up to automorphisms (the homotheties given by
`KleinTwLinkComp1`/`KleinTwLinkComp2`), which is exactly the hypothesis used here. -/
theorem algEquiv_of_comp_bijective {K A B : Type*} [CommSemiring K] [Semiring A] [Semiring B]
    [Algebra K A] [Algebra K B] (φ : A →ₐ[K] B) (ψ : B →ₐ[K] A)
    (h₁ : Function.Bijective (ψ.comp φ)) (h₂ : Function.Bijective (φ.comp ψ)) :
    Nonempty (A ≃ₐ[K] B) := by
  have hinj : Function.Injective φ := fun a₁ a₂ h => h₁.1 (by simpa using congrArg ψ h)
  have hsurj : Function.Surjective φ := by
    intro b
    obtain ⟨a, ha⟩ := h₂.2 b
    exact ⟨ψ a, by simpa using ha⟩
  exact ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

/-! ## The affine chart of the twisted link

The source `ℙ³` of the link is the hyperplane `{v₀ = 0}` of `ℙ⁴` (every line through the point `p`
with `p₀ = 1` meets it in exactly one point), with affine coordinates `(x₀,x₁,x₂)` on the chart
`v₁ = 1`; the target is the hyperplane `{z₀ = 0}` with the same coordinates.  Dehomogenising the
two (homogeneous, equal-degree) link equations gives the affine polynomials the certificate
`Work.MotV.LinkCert` consumes. -/

/-- The affine chart `v₀ = 0, v₁ = 1` of `ℙ⁴`, in graded-`MvPolynomial` form. -/
noncomputable def affPt (R : Type*) [CommRing R] : Fin 5 → MvPolynomial (Fin 3) R :=
  ![0, 1, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2]

/-- The affine source equation `F = F̃(v₀ = 0, v₁ = 1, x₀, x₁, x₂)`. -/
noncomputable def kleinTwFaff (R : Type*) [CommRing R] (a b h : R) (p : Fin 5 → R) :
    MvPolynomial (Fin 3) R :=
  kleinTwFhom (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (fun i => MvPolynomial.C (p i)) (affPt R)

/-- The affine target equation `G = G̃(z₀ = 0, z₁ = 1, x₀, x₁, x₂)`, with the corrected
target-side dual secant quintic `kleinTwSDualInv`. -/
noncomputable def kleinTwGaff (R : Type*) [CommRing R] (a b h : R) (p : Fin 5 → R) :
    MvPolynomial (Fin 3) R :=
  kleinTwGhom' (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (fun i => MvPolynomial.C (p i)) (affPt R)

end Work.MotK
