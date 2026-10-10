import Mathlib
import Submission.Work.MotV5.WtDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

open Polynomial

/-- In a ring of characteristic `5`, every natural number is fixed by the Frobenius
`x ↦ x ^ 5`.  This is `ZMod.pow_card` (`x ^ p = x` in `ZMod p`) transported along the
canonical ring homomorphism `ZMod 5 →+* L`. -/
lemma natCast_pow_five {L : Type*} [Ring L] [CharP L 5] (n : ℕ) :
    ((n : ℕ) : L) ^ 5 = ((n : ℕ) : L) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h1 : (ZMod.castHom (dvd_refl 5) L) (n : ZMod 5) = (n : L) := by simp
  have h3 := congrArg (ZMod.castHom (dvd_refl 5) L) (ZMod.pow_card (n : ZMod 5))
  rw [map_pow, h1] at h3
  exact h3

/-- The Artin–Schreier polynomial `T⁵ - T - g` (mapped into `L`) vanishes at `w + i` for
`i ∈ {0,1,2,3,4}`, whenever `w` is a root, i.e. `w⁵ - w = g`.  Additivity of the Frobenius
in characteristic `5` gives `(w+i)⁵ = w⁵ + i⁵ = w⁵ + i`, and `i` is fixed by Frobenius. -/
theorem asPolyF_root {F L : Type*} [Field F] [Field L] [Algebra F L] [CharP F 5]
    (w : L) (g : F) (hw : w ^ 5 - w = algebraMap F L g) (i : Fin 5) :
    ((Work.MotV5.asPolyF g).map (algebraMap F L)).eval (w + ((i:ℕ):L)) = 0 := by
  haveI : CharP L 5 := charP_of_injective_algebraMap (algebraMap F L).injective 5
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hc : ((i : ℕ) : L) ^ 5 = ((i : ℕ) : L) := natCast_pow_five _
  have heval : ((Work.MotV5.asPolyF g).map (algebraMap F L)).eval (w + ((i:ℕ):L))
      = (w + ((i:ℕ):L)) ^ 5 - (w + ((i:ℕ):L)) - algebraMap F L g := by
    simp [Work.MotV5.asPolyF]
  rw [heval, add_pow_char w ((i:ℕ):L) 5, hc]
  linear_combination (norm := first | refl_ring1 | ring1) hw

end Work.MotV5
