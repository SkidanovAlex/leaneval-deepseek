/-
  annals_wilkies_conjecture, AREA E3, frame-step vocabulary.

  This file fixes the objects of the *frame step* of `E3_identity` (GV Cor. 4.7):
  the tangential multi-indices, the `opMono` words indexed by them, the first-order operator `Vdir`
  of differentiation along the tangential frame vector of `Vcoef.lean`, and its iterated words
  `Vword`.

  The main algebraic facts about them (proved elsewhere or delegated) are
  * `Vdir_prepend`: `V_l (Vword m F) = Vword (m + e_l) F` when `l` is below all the active indices
    of `m`,
  * `opMono_prepend`: `detOp c h ι l (opMono (extend m) f) = opMono (extend (m + e_l)) f` under the
    same condition,
  and together with `eaEvalC_detOp_eq` (`Vcoef.lean`) they give the triangularity
  `Vword m (f) ∈ span{C^ω · (opMono ν f) : ν ≤ m}` which is the frame step: every iterated
  tangential derivative of `f` at `x` is a combination of the *ordered* reduced derivatives
  appearing in the hypothesis of `E3_identity`.
-/
import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.API.opMono_basic
import Submission.Work.WilE3.Frame.Vcoef

namespace Work.WilE3.Frame

set_option autoImplicit false
noncomputable section
open Classical Topology Matrix
open WilkiesDesign.E
open Work.WilE3 (jacDet)

variable {k r j : ℕ}

/-! ## §1. Tangential multi-indices and the coordinate map -/

/-- The `ι`-complement ("tangential") index type: the coordinates complementary to `ι`. -/
abbrev U (k : ℕ) {j : ℕ} (ι : Fin j → Fin k) : Type := {i : Fin k // i ∉ Set.range ι}

/-- Extension of a tangential multi-index by zero on the `ι`-coordinates. -/
def extend {k j : ℕ} (ι : Fin j → Fin k) (m : U k ι → ℕ) : Fin k → ℕ :=
  fun i => if h : i ∈ Set.range ι then 0 else m ⟨i, h⟩

/-- The `opMono` word attached to a tangential multi-index. -/
def Dop (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k) (f : EAPoly k r)
    (m : U k ι → ℕ) : EAPoly k r :=
  opMono c h ι (extend ι m) f

/-- The `ι`-complement coordinates of a complex point. -/
def uCoord (k : ℕ) {j : ℕ} (ι : Fin j → Fin k) (z : Fin k → ℂ) : U k ι → ℂ := fun i => z i.1

/-- The coordinate map `Φ = (ι^c-coordinates, h)`, whose local inverse straightens `{h = 0}`. -/
def PhiC (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k) :
    (Fin k → ℂ) → ((U k ι → ℂ) × (Fin j → ℂ)) :=
  fun z => (uCoord k ι z, fun a => eaEvalC c (h a) z)

/-- A real point, viewed as a complex point. -/
def toC {k : ℕ} (x : Fin k → ℝ) : Fin k → ℂ := fun i => (x i : ℂ)

/-! ## §2. Differentiation along the tangential frame -/

/-- The directional derivative of a complex function in the direction of the frame vector `V_l`. -/
def Vdir (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k) (l : Fin k)
    (F : (Fin k → ℂ) → ℂ) : (Fin k → ℂ) → ℂ :=
  fun z => ∑ i, VcoefC c h ι l z i * fderiv ℂ F z (Pi.single i 1)

/-- The directional derivative of a function of the curve parameter in the direction `e_l`
(the `l`-th coordinate direction of the parametrising space `Fin k → ℂ`). -/
def edir (l : Fin k) (G : (Fin k → ℂ) → ℂ) : (Fin k → ℂ) → ℂ :=
  fun u => deriv (fun t : ℂ => G (u + t • Pi.single l 1)) 0

/-- The iterated frame derivative `V_{k-1}^{m (k-1)} ⋯ V_0^{m 0}` applied to a function. -/
def Vword (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k) (m : Fin k → ℕ)
    (F : (Fin k → ℂ) → ℂ) : (Fin k → ℂ) → ℂ :=
  (List.finRange k).foldr (fun i G => (Vdir c h ι i)^[m i] G) F

end

end Work.WilE3.Frame
