import Mathlib
import Submission.Work.Maximal.mstWideLat_defs
import Submission.Work.BourgainPlan.Maximal.level_l2_mst_large_n

/-!
# `Q`-periodicity in the shift of the modulated sequence `mstModSeq`

`mstArc G E t = Σ_{β ∈ E} G β · e_t(β)` is a linear combination of the characters `e_t`, so if
every `β ∈ E` is a `Q`-torsion point of the circle (`e_Q(β) = 1`) then `t ↦ mstArc G E t` is
`Q`-periodic.  Consequently the modulated input `mstModSeq G E f x k = mstArc G E (k - x) · f k`
only depends on the residue class of `x` modulo `Q`:

`mstModSeq G E f y = mstModSeq G E f (y % Q)`.

This is the reduction that lets the freezing/averaging argument of MST run over the finite set of
residues mod `Q`.
-/

open Work.BourgainPlan.IonescuWainger

namespace Work.Maximal

/-- Multiplicativity of the character `fourier` in its index: `e_{m·n} = (e_m)^n`. -/
lemma fourier_mul_zpow {m n : ℤ} {β : Work.BourgainPlan.IonescuWainger.Circle} :
    fourier (m * n) β = (fourier m β) ^ n := by
  rw [fourier_apply, fourier_apply]
  rw [show (m * n) • β = n • (m • β) from by rw [mul_smul, smul_comm]]
  rw [AddCircle.toCircle_zsmul, Circle.coe_zpow]

/-- If `fourier Q β = 1` then `fourier (·) β` is `Q`-periodic in the second-variable sense used
here: `fourier (a - y) β = fourier (a - y % Q) β`. -/
lemma fourier_sub_emod {Q : ℕ} {β : Work.BourgainPlan.IonescuWainger.Circle}
    (hQ : fourier (Q : ℤ) β = 1) (a y : ℤ) :
    fourier (a - y) β = fourier (a - y % (Q : ℤ)) β := by
  have h : a - y % (Q : ℤ) = (a - y) + (Q : ℤ) * (y / (Q : ℤ)) := by
    have := Int.mul_ediv_add_emod y (Q : ℤ)
    omega
  rw [h, fourier_add, fourier_mul_zpow, hQ, one_zpow, mul_one]

theorem mstModSeq_period_emod {G : Work.BourgainPlan.IonescuWainger.Circle → ℂ}
    {E : Finset Work.BourgainPlan.IonescuWainger.Circle} {Q : ℕ} (hQpos : 0 < Q)
    (hQ : ∀ β ∈ E, fourier (Q : ℤ) β = 1) (f : ℤ → ℂ) (y : ℤ) :
    Work.BourgainPlan.Maximal.mstModSeq G E f y
      = Work.BourgainPlan.Maximal.mstModSeq G E f (y % (Q : ℤ)) := by
  have _hQpos := hQpos
  funext k
  simp only [Work.BourgainPlan.Maximal.mstModSeq_apply]
  have harc : Work.BourgainPlan.Maximal.mstArc G E (k - y)
      = Work.BourgainPlan.Maximal.mstArc G E (k - y % (Q : ℤ)) := by
    unfold Work.BourgainPlan.Maximal.mstArc
    exact Finset.sum_congr rfl fun β hβ => by rw [fourier_sub_emod (hQ β hβ) k y]
  rw [harc]

end Work.Maximal
