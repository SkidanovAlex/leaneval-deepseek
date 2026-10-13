/-
  WilC5 — the *real constants* of an `LRc`-structure.

  `LRc = (ring.sum rexpL)[[ℝ]]` has a constant symbol for every real number, so every `LRc`-structure
  `M` carries a canonical map `ℝ → M`, `r ↦ realConst M r`.  In a model of `TR` this map is a ring
  embedding onto a copy of `ℝ` (the standard part map of the standard real valuation of vdDMM (1.1)
  has image exactly the constants), and this is what makes vdDMM's decomposition

      `w = z (1 + ε)`   with `z ∈ F`, `v(ε) > 0`

  of Lemma 4.2 available: given `v(w) = v(z)`, the quotient `w / z` is a *unit*, so it is
  infinitesimally close to a standard real `r`, i.e. `w / z = r (1 + ε)`.

  This module only fixes the map; the standard part theorem
  (`Work.WilC5.stdPart`, that every element of finite value differs from a real constant by an
  infinitesimal) is requested from the fleet as `WilC5/stdPart`.
-/
import Mathlib
import Submission.Work.WilC5.LRcReduct

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- The element of an `LRc`-structure interpreting the constant symbol attached to `r : ℝ`. -/
def realConst (M : Type) [LRc.Structure M] (r : ℝ) : M :=
  @Structure.funMap (constantsOn ℝ) M (lrcConstReduct M) 0 r ![]

@[simp] theorem realConst_eq_funMap (M : Type) [LRc.Structure M] (r : ℝ) :
    realConst M r = @Structure.funMap (constantsOn ℝ) M (lrcConstReduct M) 0 r ![] := rfl

end Work.WilC5
