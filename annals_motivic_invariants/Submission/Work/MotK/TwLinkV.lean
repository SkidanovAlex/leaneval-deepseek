/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Submission.Work.MotK.TwDataMod5
import Submission.Work.MotK.KleinTwBilinStereo
import Submission.Work.MotK.KleinTwQ_stereo
import Submission.Work.MotK.LinkTwData
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The T-twisted link equations and their **unit conditions**

The quadro-cubic link of the T-twist is the map `f = kleinTwP ∘ kleinTwStereo` from the source
chart (the twisted quadric `{q = 0}`, `q = kleinTwQ = kleinTwP0`) to the target chart (the
hyperplane `H = {z_0 = 0}`); its inverse is `π_p ∘ kleinTwR`.  The two equations whose divisors
are counted in the census are

* the **source** equation `kleinTwFhom a b h p v = b(p, v) · kleinTwS (kleinTwStereo p v)`
  (`LinkTwData`, *unchanged* by the correction of the target data);
* the **target** equation `kleinTwGhomV a b h p w = b(p, kleinTwR w) · kleinTwSDualV w`, using the
  Kummer-inverse twist `kleinTwSDualV` of the dual secant quintic (`TwDataMod5`).

The *first* unit condition is

  `kleinTwGhomV p (f v) = - kleinTwS(y)^2 · b(p,v) · kleinTwFhom p v`,   `y = kleinTwStereo p v`,

which makes `f^*` send `Localization.Away F_hom` isomorphically onto `Localization.Away G_hom` in
the direction "source to target".  Its proof is *verbatim* the split one
(`Work.MotK.KleinLinkUnit`): I1' (`KleinTwI1`), I3' (`kleinTwSDualV_kleinTwP`), the bilinearity of
the polar form, and the stereographic identity `KleinTwBilinStereo` together with `q(p) = 0`.

The *second* unit condition (the inverse direction) is
`kelinTwFhom p (π_p (kleinTwR w)) = (unit) · kleinTwGhomV p w`; it uses I2' and I4' and the
projection `π_p`, and is stated separately (see `KleinTwLinkUnitInvV` below).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotK

variable {R : Type*} [CommRing R]

/-- The polar form of the twisted quadric is linear in its second argument. -/
theorem kleinTwBilin_smul_rightV (a b h : R) (u v : Fin 5 → R) (c : R) :
    kleinTwBilin a b h u (fun i => c * v i) = c * kleinTwBilin a b h u v := by
  simp only [kleinTwBilin, kleinTwQ, kleinTwP0, Pi.add_apply]
  first | refl_ring1 | ring

/-- The polar form of the twisted quadric is symmetric. -/
theorem kleinTwBilin_commV (a b h : R) (u v : Fin 5 → R) :
    kleinTwBilin a b h u v = kleinTwBilin a b h v u := by
  simp only [kleinTwBilin, kleinTwQ, kleinTwP0, Pi.add_apply]
  first | refl_ring1 | ring

/-- **The target equation of the corrected T-twisted link**: `b(p, R w) · s'(w)` with the
Kummer-inverse twist `kleinTwSDualV` of the dual secant quintic. -/
def kleinTwGhomV (a b h : R) (p w : Fin 5 → R) : R :=
  kleinTwBilin a b h p (kleinTwR a b h w) * kleinTwSDualV a b h w

/-- **The first unit condition of the T-twisted link** (audit node K3_T): pulling back the target
equation `kleinTwGhomV` along the Cremona map `f = kleinTwP ∘ kleinTwStereo` from a point `p` of
the twisted quadric `{q = 0}` gives `-s(y)^2 · b(p,v) · kleinTwFhom`, so `G_hom ∘ f` and `F_hom`
differ by a unit of the localisation. -/
theorem kleinTwLinkUnitV (a b h : R) (p v : Fin 5 → R) (hp : kleinTwQ a b h p = 0) :
    kleinTwGhomV a b h p (kleinTwP a b h (kleinTwStereo a b h p v))
      = -(kleinTwS a b h (kleinTwStereo a b h p v)) ^ 2 * kleinTwBilin a b h p v
          * kleinTwFhom a b h p v := by
  set y : Fin 5 → R := kleinTwStereo a b h p v with hy
  -- I1': `R(P(y)) = s(y)·y`
  have hI1 : kleinTwR a b h (kleinTwP a b h y) = fun i => kleinTwS a b h y * y i :=
    funext fun i => KleinTwI1 a b h y i
  -- I3': `s'(P(y)) = s(y)^2`
  have hI3 : kleinTwSDualV a b h (kleinTwP a b h y) = kleinTwS a b h y ^ 2 :=
    kleinTwSDualV_kleinTwP a b h y
  -- the stereographic polar identity, specialised by `q(p) = 0`
  have hst : kleinTwBilin a b h p y = -(kleinTwBilin a b h p v) ^ 2 := by
    rw [hy, KleinTwBilinStereo a b h p v, hp]
    first | refl_ring1 | ring
  -- bilinearity of `b` in the second argument
  have hsm : kleinTwBilin a b h p (fun i => kleinTwS a b h y * y i)
      = kleinTwS a b h y * kleinTwBilin a b h p y :=
    kleinTwBilin_smul_rightV a b h p y (kleinTwS a b h y)
  rw [kleinTwGhomV, kleinTwFhom, hI1, hI3, hsm, hst]
  first | refl_ring1 | ring

/-! ## The inverse map on the hyperplane `H = {w 0 = 0}`

The target chart of the link is the hyperplane `H = {w 0 = 0}` (the map `f = kleinTwP ∘ y`
lands in it: `KleinTwQ_stereo`).  On `H` the inverse of `f` is the *inverse quadro-cubic map*
`kleinTwR` itself: `kleinTwR` maps `H` into the twisted quadric `{q = 0}`
(`kleinTwQ_kleinTwR_of_zero`), and on `Q` the stereographic map fixes the projective points
(`kleinTwStereo p x = -b(p,x)·x` for `q(x) = 0`), so `kleinTwStereo p (kleinTwR w) = -b(p,Rw)·Rw`
and `P(kleinTwStereo p (kleinTwR w)) ∝ P(Rw) ∝ w`. -/

/-- **`kleinTwR` maps the hyperplane `{w 0 = 0}` into the twisted quadric.** -/
theorem kleinTwQ_kleinTwR_of_zero (a b h : R) (w : Fin 5 → R) (hw : w 0 = 0) :
    kleinTwQ a b h (kleinTwR a b h w) = 0 := by
  simp only [kleinTwQ, kleinTwP0, kleinTwR_zero, kleinTwR_one, kleinTwR_two, kleinTwR_three,
    kleinTwR_four, kleinTwR0, kleinTwR1, kleinTwR2, kleinTwR3, kleinTwR4]
  rw [show w 0 = 0 from hw]
  first | refl_ring1 | ring

/-- **The second unit condition of the T-twisted link**: on the hyperplane `{w 0 = 0}` (where the
inverse of `f` is `kleinTwR`), the source equation `kleinTwFhom` pulled back is a unit multiple of
the target equation `kleinTwGhomV`:

  `kleinTwFhom p (R w) = -b(p, Rw)^5 · s'(w)^2 · kleinTwGhomV p w`,

the unit being `-b(p,Rw)^5·s'(w)^2` (both `b(p,Rw)` and `s'(w)` divide the target equation, hence
are units of the localisation `A_{G_hom}`). -/
theorem kleinTwFhom_kleinTwR (a b h : R) [IsDomain R] (p w : Fin 5 → R)
    (hx : kleinTwQ a b h (kleinTwR a b h w) = 0)
    (hw : kleinTwR a b h w 0 ≠ 0) :
    kleinTwFhom a b h p (kleinTwR a b h w)
      = -(kleinTwBilin a b h p (kleinTwR a b h w)) ^ 5
          * (kleinTwSDualV a b h w) ^ 2 * kleinTwGhomV a b h p w := by
  set x : Fin 5 → R := kleinTwR a b h w with hxdef
  -- on the quadric, the stereographic map is the scalar map `x ↦ -b(p,x)·x`
  have hst : kleinTwStereo a b h p x = fun i => -kleinTwBilin a b h p x * x i := by
    funext i
    simp only [kleinTwStereo, Pi.sub_apply, hx]
    first | refl_ring1 | ring
  -- homogeneity of `s`
  have hhom : kleinTwS a b h (fun i => -kleinTwBilin a b h p x * x i)
      = (-kleinTwBilin a b h p x) ^ 5 * kleinTwS a b h x := by
    have h := kleinTwS_homog a b h (-(kleinTwBilin a b h p x)) x
    simpa using h
  -- I4' on the hyperplane
  have hI4 : kleinTwS a b h x = kleinTwSDualV a b h w ^ 3 :=
    kleinTwSec_kleinTwR a b h w hw
  rw [kleinTwFhom, hst, hhom, hI4, hxdef, kleinTwGhomV]
  first | refl_ring1 | ring

end Work.MotK
