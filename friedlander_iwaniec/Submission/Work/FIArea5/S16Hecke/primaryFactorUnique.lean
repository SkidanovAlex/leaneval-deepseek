import Mathlib
import Submission.Work.FIArea5.S16Hecke.primaryAux
import Submission.Commons.NumberTheory.GaussianInt.fibre_associated_of_norm_coprime

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea5.S16Hecke

open Work.FIPlan

/-- The third primary condition, stated as an equality in `ZMod 4`. -/
theorem isPrimary_cast_im {z : GaussianInt} (h : IsPrimary z) :
    (z.im : ZMod 4) = (z.re : ZMod 4) - 1 := by
  obtain ⟨_, _, hc⟩ := h
  have h2 := (ZMod.intCast_eq_intCast_iff z.im (z.re - 1) 4).mpr hc
  push_cast at h2 ⊢
  exact h2

/-- **Uniqueness of the primary factorisation along coprime norms.**

If `z1 * z2 = z1' * z2'` with `z1, z2, z1', z2'` primary and
`‖z1‖ = ‖z1'‖ = m`, `‖z2‖ = ‖z2'‖ = n` for coprime `m, n > 0`, then `z1 = z1'`.

Two facts combine: the norm fibres over coprime values are single associate classes
(`fibre_associated_of_norm_coprime`), so `z1` and `z1'` differ by a unit; and the only
primary unit (with respect to the primary normalisation) is `1`
(`unit_eq_one_of_primary`). -/
theorem primaryFactorUnique {z1 z2 z1' z2' : GaussianInt} {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hcop : Nat.Coprime m n)
    (h1 : Work.FIPlan.IsPrimary z1) (h2 : Work.FIPlan.IsPrimary z2)
    (h1' : Work.FIPlan.IsPrimary z1') (h2' : Work.FIPlan.IsPrimary z2')
    (hg1 : Work.FIPlan.gnorm z1 = m) (hg1' : Work.FIPlan.gnorm z1' = m)
    (hg2 : Work.FIPlan.gnorm z2 = n) (hg2' : Work.FIPlan.gnorm z2' = n)
    (h : z1 * z2 = z1' * z2') : z1 = z1' := by
  have hassoc : Associated z1 z1' :=
    Commons.NumberTheory.GaussianInt.fibre_associated_of_norm_coprime hcop
      (show z1.norm.natAbs = m from hg1) (show z1'.norm.natAbs = m from hg1')
      (show z2.norm.natAbs = n from hg2) (show z2'.norm.natAbs = n from hg2') h
  obtain ⟨u, hu⟩ := hassoc
  have hu1 : (↑u : GaussianInt) = 1 :=
    Commons.NumberTheory.GaussianInt.unit_eq_one_of_primary h1.1 h1.2.1 (isPrimary_cast_im h1)
      (by rw [hu]; exact h1'.1)
      (by rw [hu]; exact isPrimary_cast_im h1')
  rw [← hu, hu1, mul_one]

end Work.FIArea5.S16Hecke
