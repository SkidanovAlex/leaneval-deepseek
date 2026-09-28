import Mathlib
import Submission.Work.HP.ConicsLiftDefs

/-!
# `qf (Phi p ā B) (vecLift p v)` splits off the mod-`p` part

For a prime `p`, a coefficient vector `ā` mod `p`, a vector `v` mod `p` and a perturbation
`B` mod `p`, the quadratic form evaluated at any lift of `ā` has
```
qf (Phi p ā B) (vecLift p v) = qf (coefLift p ā) (vecLift p v) + p · lif (qf B v)  mod p².
```
Indeed `Phi p ā B = coefLift p ā + p · (lif ∘ B)` coefficientwise, so the difference of the two
values is `p · ∑_m lif (B m) · ν(vecLift v)_m`; the reduction mod `p` of the bracketed sum is
`qf B v`, and `p · z = p · lif (red z)` for every `z` mod `p²`.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset

namespace Work.HP

namespace Conics

/-- Splitting a quadratic form whose coefficient vector is perturbed coefficientwise by `c • C`:
the perturbation contributes `c` times the pairing of `C` with the monomials of `x`. -/
lemma qf_coeff_add {R : Type*} [CommSemiring R] (A C : Mon 2 2 → R) (x : Fin 3 → R) (c : R) :
    qf (fun m => A m + c * C m) x = qf A x + c * ∑ m, C m * ∏ i, x i ^ (m.1 i : ℕ) := by
  simp only [qf]
  rw [show (∑ m, (A m + c * C m) * ∏ i, x i ^ (m.1 i : ℕ))
        = ∑ m, ((A m * ∏ i, x i ^ (m.1 i : ℕ)) + c * (C m * ∏ i, x i ^ (m.1 i : ℕ))) from
      Finset.sum_congr rfl (fun m _ => by rw [add_mul]; ring)]
  rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- The reduction mod `p` of the lifted monomial sum `∑_m lif (B m) · ν(vecLift v)_m` is
`qf B v`. -/
lemma red_sum_lif_vecLift (p : ℕ) [Fact p.Prime] (B : Mon 2 2 → ZMod p) (v : Fin 3 → ZMod p) :
    red p (∑ m, lif p (B m) * ∏ i, (vecLift p v i) ^ (m.1 i : ℕ)) = qf B v := by
  simp only [vecLift]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [map_mul, red_lif, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [map_pow, red_lif]

end Conics

theorem conics_lift_qfPhi (p : ℕ) [Fact p.Prime] (ā : Work.HP.Mon 2 2 → ZMod p)
    (v : Fin 3 → ZMod p) (B : Work.HP.Mon 2 2 → ZMod p) :
    Work.HP.Conics.qf (Work.HP.Conics.Phi p ā B) (Work.HP.Conics.vecLift p v)
      = Work.HP.Conics.qf (Work.HP.Conics.coefLift p ā) (Work.HP.Conics.vecLift p v)
        + (p : ZMod (p ^ 2)) * Work.HP.Conics.lif p (Work.HP.Conics.qf B v) := by
  change Work.HP.Conics.qf
      (fun m => Work.HP.Conics.coefLift p ā m + (p : ZMod (p ^ 2)) * Work.HP.Conics.lif p (B m))
      (Work.HP.Conics.vecLift p v) = _
  rw [Work.HP.Conics.qf_coeff_add]
  have h : (p : ZMod (p ^ 2)) * (∑ m, Work.HP.Conics.lif p (B m)
        * ∏ i, (Work.HP.Conics.vecLift p v i) ^ (m.1 i : ℕ))
      = (p : ZMod (p ^ 2)) * Work.HP.Conics.lif p (Work.HP.Conics.qf B v) := by
    calc (p : ZMod (p ^ 2)) * (∑ m, Work.HP.Conics.lif p (B m)
            * ∏ i, (Work.HP.Conics.vecLift p v i) ^ (m.1 i : ℕ))
        = (p : ZMod (p ^ 2)) * Work.HP.Conics.lif p (Work.HP.Conics.red p (∑ m,
            Work.HP.Conics.lif p (B m) * ∏ i, (Work.HP.Conics.vecLift p v i) ^ (m.1 i : ℕ))) :=
          Work.HP.Conics.p_mul_eq_p_mul_lif_red p _
      _ = (p : ZMod (p ^ 2)) * Work.HP.Conics.lif p (Work.HP.Conics.qf B v) := by
          rw [Work.HP.Conics.red_sum_lif_vecLift]
  rw [h]

end Work.HP
