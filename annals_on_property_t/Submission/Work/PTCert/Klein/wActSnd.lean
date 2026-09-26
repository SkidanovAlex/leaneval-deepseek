import Mathlib
import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.twistedFourierCriterion

/-!
# Second-argument equivariance of the untwisted Fourier block

`fourierW act M S x y = ∑_a χ_S(a) · M x (act a y)` where `act` is an action of the
elementary abelian 2-group `(Fin m → ZMod 2)` on `ι` and `χ_S = chiS S` is the sign
character attached to a finite set `S ⊆ Fin m`.

Since `(Fin m → ZMod 2)` has exponent two (`v + v = 0`) and `χ_S` is a character
(`chiS_add`), translating the summation index by `ν` in the second variable of
`fourierW` produces exactly the factor `χ_S ν`:

  `fourierW act M S u (act ν v) = χ_S ν · fourierW act M S u v`.

Unlike the first-argument version this needs no invariance of `M` and no unit law
`act 0 x = x`: only the associativity law `act (a+b) x = act a (act b x)` of the action.
-/

namespace Work.PTCert.Klein

open Submission.PTCert
open scoped BigOperators

set_option autoImplicit false

/-- `(Fin m → ZMod 2)` has exponent two. -/
private lemma zmod2_vec_add_self {m : ℕ} (v : Fin m → ZMod 2) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

theorem wActSnd {m : ℕ} {ι : Type} (act : (Fin m → ZMod 2) → ι → ι) (M : Matrix ι ι ℝ)
    (S : Finset (Fin m))
    (hact : ∀ a b x, act (a + b) x = act a (act b x))
    (ν : Fin m → ZMod 2) (u v : ι) :
    Submission.PTCert.fourierW act M S u (act ν v)
      = Submission.PTCert.chiS S ν * Submission.PTCert.fourierW act M S u v := by
  -- Unfold the action on the shifted variable: `act c (act ν v) = act (c + ν) v`.
  have hstep1 : (∑ c, chiS S c * M u (act c (act ν v)))
      = ∑ c, chiS S c * M u (act (c + ν) v) :=
    Finset.sum_congr rfl (fun c _ => by rw [hact c ν v])
  -- Compensate by multiplying with `χ_S(c)` rewritten as `χ_S((c + ν) + ν)` (using `ν + ν = 0`).
  have hcong : (∑ c, chiS S c * M u (act (c + ν) v))
      = ∑ c, chiS S ((c + ν) + ν) * M u (act (c + ν) v) := by
    apply Finset.sum_congr rfl
    intro c _
    rw [show (c + ν) + ν = c from by rw [add_assoc, zmod2_vec_add_self ν, add_zero]]
  -- Reindex the sum by `c ↦ c + ν` and pull out the factor `χ_S ν`.
  have hstep2 : (∑ c, chiS S c * M u (act (c + ν) v))
      = ∑ c, chiS S (c + ν) * M u (act c v) := by
    rw [hcong]
    simpa only [Equiv.coe_addRight] using
      (Equiv.sum_comp (Equiv.addRight ν) (fun c => chiS S (c + ν) * M u (act c v)))
  have hstep3 : (∑ c, chiS S (c + ν) * M u (act c v))
      = chiS S ν * ∑ c, chiS S c * M u (act c v) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [chiS_add]
    ring
  simpa [fourierW] using hstep1.trans (hstep2.trans hstep3)

end Work.PTCert.Klein
