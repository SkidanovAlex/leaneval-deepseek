import Mathlib
import Submission.Work.PTCert.fourierTransport.Common

/-!
# Equivariance of the untwisted Fourier block `fourierW`

`fourierW act M S x y = ∑_a χ_S(a) · M x (act a y)`, where `χ_S = chiS S` is the sign
character of `(ℤ/2)^m` attached to a finite set `S ⊆ Fin m` and `act` is an action of
`(ℤ/2)^m` on the index type `ι` for which the matrix `M` is invariant
(`M (act a x) (act a y) = M x y`).

This is the `sgn = 1` special case of `Work.PTCert.Fourier.WSfunAct`, proved here directly:
the action is by involutions (`act_neg`, since `(ℤ/2)^m` has exponent two) and `χ_S` is a
character (`chiS_add`), so translating the summation index by `a` (resp. `b`) turns each
variable of `fourierW` into a factor `χ_S a` (resp. `χ_S b`).
-/

namespace Work.PTCert

open Submission.PTCert
open scoped BigOperators

set_option autoImplicit false

/-- `(Fin m → ZMod 2)` has exponent two. -/
private lemma zmod2_vec_add_self {m : ℕ} (v : Fin m → ZMod 2) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

/-- First-argument equivariance of the untwisted Fourier block:
`fourierW (act a x) z = χ_S a · fourierW x z`. -/
private lemma fourierW_fst {m : ℕ} {ι : Type} (act : (Fin m → ZMod 2) → ι → ι)
    (hact_add : ∀ a b x, act (a + b) x = act a (act b x)) (hact_zero : ∀ x, act 0 x = x)
    (M : Matrix ι ι ℝ) (hM : ∀ a x y, M (act a x) (act a y) = M x y)
    (S : Finset (Fin m)) (a : Fin m → ZMod 2) (x z : ι) :
    fourierW act M S (act a x) z = chiS S a * fourierW act M S x z := by
  have hself : ∀ w : ι, act a (act a w) = w := fun w => act_neg act hact_add hact_zero a w
  -- `M` is invariant, and `act a ∘ act a = id`: move the action on the first variable across.
  have key : ∀ c : Fin m → ZMod 2, M (act a x) (act c z) = M x (act (a + c) z) := by
    intro c
    have h := hM a x (act a (act c z))
    rw [hself (act c z)] at h
    rw [h, hact_add a c z]
  have hstep1 : (∑ c, chiS S c * M (act a x) (act c z))
      = ∑ c, chiS S c * M x (act (a + c) z) :=
    Finset.sum_congr rfl (fun c _ => by rw [key c])
  have hcong : (∑ c, chiS S c * M x (act (a + c) z))
      = ∑ c, chiS S (a + (a + c)) * M x (act (a + c) z) := by
    apply Finset.sum_congr rfl
    intro c _
    rw [show a + (a + c) = c from by rw [← add_assoc, zmod2_vec_add_self a, zero_add]]
  -- Reindex the sum by `c ↦ a + c` and pull out `χ_S a`.
  have hstep2 : (∑ c, chiS S c * M x (act (a + c) z))
      = ∑ c, chiS S (a + c) * M x (act c z) := by
    rw [hcong]
    simpa only [Equiv.coe_addLeft] using
      (Equiv.sum_comp (Equiv.addLeft a) (fun c => chiS S (a + c) * M x (act c z)))
  have hstep3 : (∑ c, chiS S (a + c) * M x (act c z))
      = chiS S a * ∑ c, chiS S c * M x (act c z) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [chiS_add]
    ring
  have hchain := hstep1.trans (hstep2.trans hstep3)
  simpa [fourierW] using hchain

/-- Second-argument equivariance of the untwisted Fourier block:
`fourierW x (act b y) = χ_S b · fourierW x y`. -/
private lemma fourierW_snd {m : ℕ} {ι : Type} (act : (Fin m → ZMod 2) → ι → ι)
    (hact_add : ∀ a b x, act (a + b) x = act a (act b x))
    (M : Matrix ι ι ℝ) (S : Finset (Fin m)) (b : Fin m → ZMod 2) (x y : ι) :
    fourierW act M S x (act b y) = chiS S b * fourierW act M S x y := by
  have hstep1 : (∑ c, chiS S c * M x (act c (act b y)))
      = ∑ c, chiS S c * M x (act (c + b) y) :=
    Finset.sum_congr rfl (fun c _ => by rw [hact_add c b y])
  have hcong : (∑ c, chiS S c * M x (act (c + b) y))
      = ∑ c, chiS S ((c + b) + b) * M x (act (c + b) y) := by
    apply Finset.sum_congr rfl
    intro c _
    rw [show (c + b) + b = c from by rw [add_assoc, zmod2_vec_add_self b, add_zero]]
  -- Reindex the sum by `c ↦ c + b` and pull out `χ_S b`.
  have hstep2 : (∑ c, chiS S c * M x (act (c + b) y))
      = ∑ c, chiS S (c + b) * M x (act c y) := by
    rw [hcong]
    simpa only [Equiv.coe_addRight] using
      (Equiv.sum_comp (Equiv.addRight b) (fun c => chiS S (c + b) * M x (act c y)))
  have hstep3 : (∑ c, chiS S (c + b) * M x (act c y))
      = chiS S b * ∑ c, chiS S c * M x (act c y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [chiS_add]
    ring
  have hchain := hstep1.trans (hstep2.trans hstep3)
  simpa [fourierW] using hchain

theorem fourierWAct {m : ℕ} {ι : Type} (act : (Fin m → ZMod 2) → ι → ι)
    (hact_add : ∀ a b x, act (a + b) x = act a (act b x)) (hact_zero : ∀ x, act 0 x = x)
    (M : Matrix ι ι ℝ) (hM : ∀ a x y, M (act a x) (act a y) = M x y)
    (S : Finset (Fin m)) (a b : Fin m → ZMod 2) (x y : ι) :
    Submission.PTCert.fourierW act M S (act a x) (act b y) =
      Submission.PTCert.chiS S a * Submission.PTCert.chiS S b *
        Submission.PTCert.fourierW act M S x y := by
  rw [fourierW_fst act hact_add hact_zero M hM S a x (act b y)]
  rw [fourierW_snd act hact_add M S b x y]
  ring

end Work.PTCert
