import Mathlib
import Submission.Work.MotAS.ASLink
import Submission.Work.MotAS.ASData
import Submission.Work.MotK.KleinLinkUnit
import Submission.Work.MotAS.AsTransportSstage
import Submission.Work.MotAS.SDKeyF2

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The unit condition of the AS link (`KleinLinkUnitAS`)

The characteristic-5 (Artin–Schreier) branch of the Crauder–Katz chart of
H.-Y. Lin, E. Shinder, *Motivic invariants of birational maps*, Ann. of Math. **199** (2024).

The statement is the `AS`-transported form of `Work.MotK.KleinLinkUnit` (the split unit
condition): with `x = asM w · ·` the source Galois-coordinate substitution and `z = asN w · ·`
the target one, the split identity evaluated at `p' = asM w · p`, `x = asM w · v` becomes the
AS statement once every ingredient is transported:

* `kleinQ a b (asM w · y) = kleinQAS a b y` (`Work.MotAS.asTransportQ`),
* `kleinP a b (asM w · y) = asN w · kleinPAS a b g y` (`Work.MotAS.asTransportP`),
* `kleinR a b (asN w · z) = asM w · kleinRAS a b g z` (`Work.MotAS.asTransportR`),
* `kleinSec a b (asM w · y) = kleinSecAS a b g y` (source quintic transport),
* `kleinSecDual a b (asN w · z) = kleinSecDualAS a b g z` (target quintic transport),
* bilinearity of `kleinQ` / `kleinQAS` turns the transport of `kleinBilin` and of the
  stereographic parametrisation into a rewriting.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotAS

variable {R : Type*} [CommRing R]

/-- The polar bilinear form transports: `b(asM w · u, asM w · z) = b^AS(u, z)`. -/
theorem kleinBilin_asTransport (a b g w : R) (h5 : (5 : R) = 0) (hw : w ^ 5 = w + g)
    (u z : Fin 5 → R) :
    Work.MotK.kleinBilin a b (fun i => ∑ j, asM w i j * u j)
        (fun i => ∑ j, asM w i j * z j)
      = kleinBilinAS a b u z := by
  have hadd : (fun i => ∑ j, asM w i j * u j) + (fun i => ∑ j, asM w i j * z j)
      = fun i => ∑ j, asM w i j * (u + z) j := by
    funext i
    change (∑ j, asM w i j * u j) + (∑ j, asM w i j * z j) = ∑ j, asM w i j * (u + z) j
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [Pi.add_apply]; ring
  simp only [Work.MotK.kleinBilin, kleinBilinAS, hadd,
    asTransportQ a b g w h5 hw (u + z), asTransportQ a b g w h5 hw u,
    asTransportQ a b g w h5 hw z]

/-- The stereographic parametrisation transports:
`y_{asM w·p}(asM w·v) = asM w · y^AS_p(v)`. -/
theorem kleinStereo_asTransport (a b g w : R) (h5 : (5 : R) = 0) (hw : w ^ 5 = w + g)
    (p v : Fin 5 → R) :
    Work.MotK.kleinStereo a b (fun i => ∑ j, asM w i j * p j)
        (fun i => ∑ j, asM w i j * v j)
      = fun i => ∑ j, asM w i j * kleinStereoAS a b p v j := by
  funext i
  simp only [Work.MotK.kleinStereo, kleinStereoAS, Pi.add_apply]
  rw [asTransportQ a b g w h5 hw v, kleinBilin_asTransport a b g w h5 hw p v]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The unit condition of the link (audit node K3), transported to AS Galois coordinates: with
`x = asM w · ·` the source substitution and `z = asN w · ·` the target one, the split unit
condition `Work.MotK.KleinLinkUnit` evaluated at `x = asM w · v` reads
`G^AS_hom(P^AS(y(v))) = -s^AS(y(v))^2 · b^AS(p,v) · F^AS_hom(v)`. -/
theorem KleinLinkUnitAS {R : Type*} [CommRing R] (a b g w : R) (h5 : (5 : R) = 0)
    (hw : w ^ 5 = w + g) (p v : Fin 5 → R) (hp : kleinQAS a b p = 0) :
    kleinGhomAS a b g p (kleinPAS a b g (kleinStereoAS a b p v))
      = -(kleinSecAS a b g (kleinStereoAS a b p v)) ^ 2 * kleinBilinAS a b p v
          * kleinFhomAS a b g p v := by
  -- the source-side and target-side quintic transports (proved in the sibling modules)
  have hS : ∀ y : Fin 5 → R,
      Work.MotK.kleinSec a b (fun i => ∑ j, asM w i j * y j) = kleinSecAS a b g y :=
    fun y => AsTransportSstage a b g w h5 hw y
  have hSD : ∀ z : Fin 5 → R,
      Work.MotK.kleinSecDual a b (fun k => ∑ j, asN w k j * z j) = kleinSecDualAS a b g z :=
    fun z => Work.MotAS.SDF2.AsTransportSDKey a b g w h5 hw z
  -- setup
  set P' : Fin 5 → R := fun i => ∑ j, asM w i j * p j with hP'
  set V' : Fin 5 → R := fun i => ∑ j, asM w i j * v j with hV'
  set Y : Fin 5 → R := kleinStereoAS a b p v with hY
  have hQ : Work.MotK.kleinQ a b P' = 0 := by
    rw [hP', asTransportQ a b g w h5 hw p, hp]
  have hst : Work.MotK.kleinStereo a b P' V' = fun i => ∑ j, asM w i j * Y j := by
    rw [hP', hV', hY]; exact kleinStereo_asTransport a b g w h5 hw p v
  have hP : Work.MotK.kleinP a b (fun i => ∑ j, asM w i j * Y j)
      = (asN w).mulVec (kleinPAS a b g Y) := asTransportP a b g w h5 hw Y
  -- the split unit condition at the substituted data
  have hlink := Work.MotK.KleinLinkUnit a b P' V' hQ
  rw [hst, hP] at hlink
  -- rewrite the ingredients of the split identity into their AS counterparts
  have hR : Work.MotK.kleinR a b ((asN w).mulVec (kleinPAS a b g Y))
      = fun i => ∑ j, asM w i j * kleinRAS a b g (kleinPAS a b g Y) j :=
    asTransportR a b g w h5 hw (kleinPAS a b g Y)
  have hSD' : Work.MotK.kleinSecDual a b ((asN w).mulVec (kleinPAS a b g Y))
      = kleinSecDualAS a b g (kleinPAS a b g Y) := hSD (kleinPAS a b g Y)
  have hbil : Work.MotK.kleinBilin a b P'
        (fun i => ∑ j, asM w i j * kleinRAS a b g (kleinPAS a b g Y) j)
      = kleinBilinAS a b p (kleinRAS a b g (kleinPAS a b g Y)) := by
    rw [hP']
    exact kleinBilin_asTransport a b g w h5 hw p (kleinRAS a b g (kleinPAS a b g Y))
  have hY' : Work.MotK.kleinSec a b (fun i => ∑ j, asM w i j * Y j) = kleinSecAS a b g Y := hS Y
  have hbilv : Work.MotK.kleinBilin a b P' V' = kleinBilinAS a b p v := by
    rw [hP', hV']; exact kleinBilin_asTransport a b g w h5 hw p v
  rw [Work.MotK.kleinGhom, Work.MotK.kleinFhom] at hlink
  rw [hR, hbil, hSD', hY', hst, hY', hbilv] at hlink
  simp only [kleinGhomAS, kleinFhomAS]
  exact hlink

end Work.MotAS

