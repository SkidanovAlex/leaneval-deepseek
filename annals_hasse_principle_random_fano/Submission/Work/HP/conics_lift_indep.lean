import Mathlib
import Submission.Work.HP.ConicsLiftDefs

/-!
# `qf A` is constant on the lifts of a radical vector `v`

Let `p` be a prime, `ā` a conic mod `p`, `A` a lift of `ā` mod `p²`, and `v` a vector mod `p`
lying in the radical of the polar form of `ā`, i.e. `pol ā v y = 0` for all `y`.  If `v₁` and
`v₂` are two vectors mod `p²` reducing to `v`, then `qf A v₁ = qf A v₂`.

Indeed `v₂ - v₁ = p • w` for some `w` (the kernel of the reduction consists of the multiples of
`p`), so by `Conics.qf_add_smul`

`qf A v₂ = qf A v₁ + p · pol A v₁ w + p² · qf A w`.

The last term vanishes because `p² = 0` in `ZMod (p²)`.  For the middle term,
`red (pol A v₁ w) = pol ā v (red ∘ w) = 0` by the radical hypothesis, and any element of
`ZMod (p²)` reducing to `0` is killed by `p` (`Conics.p_mul_eq_p_mul_lif_red`).

This is the `lift_indep` helper announced in `Submission/Work/HP/conics_lift.lean`: it says that,
for a sharp `ā` on the line `⟨v⟩`, the truth value of `Conics.II p A v`
(i.e. `qf A` not vanishing on the lifts of `v`) is independent of the chosen lift.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset

namespace Work.HP

/-- In `ZMod (p²)`, any element whose reduction mod `p` vanishes is killed by `p`. -/
theorem p_mul_eq_zero_of_red_eq_zero (p : ℕ) [Fact p.Prime] (z : ZMod (p ^ 2))
    (hz : Work.HP.Conics.red p z = 0) : (p : ZMod (p ^ 2)) * z = 0 := by
  rw [Work.HP.Conics.p_mul_eq_p_mul_lif_red p z, hz]
  simp [Work.HP.Conics.lif]

/-- `p² = 0` in `ZMod (p²)`. -/
theorem p_sq_eq_zero (p : ℕ) : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
  have h : ((p ^ 2 : ℕ) : ZMod (p ^ 2)) = 0 := ZMod.natCast_self (p ^ 2)
  simpa [pow_two, Nat.cast_mul] using h

theorem conics_lift_indep (p : ℕ) [Fact p.Prime] (ā : Work.HP.Mon 2 2 → ZMod p)
    (v : Fin 3 → ZMod p) (hrad : ∀ y : Fin 3 → ZMod p, Work.HP.Conics.pol ā v y = 0)
    (A : Work.HP.Mon 2 2 → ZMod (p ^ 2)) (hA : Work.HP.Conics.redC p A = ā)
    (v₁ v₂ : Fin 3 → ZMod (p ^ 2)) (h₁ : Work.HP.Conics.IsLift p v₁ v)
    (h₂ : Work.HP.Conics.IsLift p v₂ v) :
    Work.HP.Conics.qf A v₁ = Work.HP.Conics.qf A v₂ := by
  -- The difference of two lifts of `v` is `p` times *something*.
  have hwit : ∀ i, ∃ t : ZMod p,
      v₂ i - v₁ i = (p : ZMod (p ^ 2)) * Work.HP.Conics.lif p t := by
    intro i
    exact (Work.HP.Conics.red_eq_zero_iff_exists_lif p (v₂ i - v₁ i)).mp (by
      rw [map_sub, h₂ i, h₁ i, sub_self])
  choose t ht using hwit
  set w : Fin 3 → ZMod (p ^ 2) := fun i => Work.HP.Conics.lif p (t i) with hw
  have hv2 : v₂ = v₁ + (p : ZMod (p ^ 2)) • w := by
    funext i
    rw [hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact sub_eq_iff_eq_add'.mp (ht i)
  -- The polar term is killed by `p`, since `v` is in the radical mod `p`.
  have hred_pol : Work.HP.Conics.red p (Work.HP.Conics.pol A v₁ w) = 0 := by
    rw [Work.HP.Conics.red_pol, hA]
    have hv1red : (fun i => Work.HP.Conics.red p (v₁ i)) = v := funext h₁
    rw [hv1red]
    exact hrad _
  have hpol : (p : ZMod (p ^ 2)) * Work.HP.Conics.pol A v₁ w = 0 :=
    p_mul_eq_zero_of_red_eq_zero p _ hred_pol
  -- Assemble: the perturbation by `p • w` changes nothing.
  have hmain : Work.HP.Conics.qf A (v₁ + (p : ZMod (p ^ 2)) • w) = Work.HP.Conics.qf A v₁ := by
    rw [Work.HP.Conics.qf_add_smul, hpol, p_sq_eq_zero, zero_mul, add_zero, add_zero]
  rw [hv2]
  exact hmain.symm

end Work.HP
