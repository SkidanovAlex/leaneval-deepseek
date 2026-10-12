import ChallengeDeps
import Submission.Work.BoseSym.Perm.integral_sq_symAvgF_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseSym.Bridge.integral_symAvgF_mul_sq_eq`

The symmetrisation average `symAvgF N V x = (N!)⁻¹ · ∑_σ V (actPerm σ x)` may be
replaced by `V` inside the weighted integral

`∫_{box N L} (symAvgF N V) · f² = ∫_{box N L} V · f²`

whenever `f` is permutation invariant almost everywhere (`hinv`).  This is the
averaging identity behind the bosonic reduction of the potential energy: since
the box and Lebesgue measure are invariant under relabelling the particles, each
individual term `∫_{box} V (actPerm σ x) f x²` equals the full integral (the
weight `f x² = f (actPerm σ x)²` is invariant, and the change of variables
`x ↦ actPerm σ x` leaves the integral over the box unchanged), so the average of
the `N!` equal terms is again the same integral.

## Proof outline

* `ae_restrict_of_ae` transports the a.e. invariance of `f` from Lebesgue
  measure to Lebesgue measure restricted to the box;
* `IntegralSqSymAvg.integrableOn_actPerm_box_iff` gives integrability of the
  relabelled weight `(V·f²) ∘ actPerm σ`, and the a.e. invariance of `f` turns it
  into integrability of `V (actPerm σ ·) · f²`;
* `IntegralSqSymAvg.integral_actPerm_box` shows each term of the average equals
  the target integral;
* assembly expands `symAvgF` as `(N!)⁻¹ ∑_σ`, pulls the constant and the finite
  sum out of the integral (`integral_const_mul`, `integral_finsetSum`), and
  evaluates the resulting constant sum.
-/

namespace Work.BoseSym.Bridge

open MeasureTheory Filter
open scoped Topology Real

theorem integral_symAvgF_mul_sq_eq {N : ℕ} {L : ℝ} {V f : Work.BoseSym.Conf N → ℝ}
    (hV0 : 0 ≤ V) (hVint : Work.BoseSym.IntOnBox N L V)
    (hint : MeasureTheory.IntegrableOn (fun x => V x * (f x) ^ 2) (BoseGases.box N L)
      MeasureTheory.volume)
    (hinv : ∀ᵐ x ∂(Work.BoseSym.volC N), ∀ σ : Equiv.Perm (Fin N),
      f (Submission.BoseGases.actPerm N σ x) = f x) :
    ∫ x in BoseGases.box N L, (Work.BoseSym.symAvgF N V) x * (f x) ^ 2 =
      ∫ x in BoseGases.box N L, V x * (f x) ^ 2 := by
  classical
  have hae : ∀ᵐ x ∂(volume.restrict (BoseGases.box N L)),
      ∀ σ : Equiv.Perm (Fin N), f (Submission.BoseGases.actPerm N σ x) = f x :=
    MeasureTheory.ae_restrict_of_ae hinv
  have hσ : ∀ σ : Equiv.Perm (Fin N),
      MeasureTheory.Integrable (fun x => V (Submission.BoseGases.actPerm N σ x) * (f x) ^ 2)
        (volume.restrict (BoseGases.box N L)) := by
    intro σ
    have hcomp : MeasureTheory.Integrable
        (fun x => V (Submission.BoseGases.actPerm N σ x) *
          (f (Submission.BoseGases.actPerm N σ x)) ^ 2)
        (volume.restrict (BoseGases.box N L)) :=
      (Work.BoseSym.Perm.IntegralSqSymAvg.integrableOn_actPerm_box_iff L σ
        (fun y => V y * (f y) ^ 2)).mpr hint
    exact hcomp.congr (hae.mono (fun x hx => by simp only [hx σ]))
  have hIσ : ∀ σ : Equiv.Perm (Fin N),
      ∫ x in BoseGases.box N L, V (Submission.BoseGases.actPerm N σ x) * (f x) ^ 2
        = ∫ x in BoseGases.box N L, V x * (f x) ^ 2 := by
    intro σ
    rw [← Work.BoseSym.Perm.IntegralSqSymAvg.integral_actPerm_box L σ (fun y => V y * (f y)^2)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx σ]
  calc ∫ x in BoseGases.box N L, (Work.BoseSym.symAvgF N V) x * (f x) ^ 2
      = ∫ x in BoseGases.box N L, (1 / (Nat.factorial N : ℝ)) *
          (∑ σ : Equiv.Perm (Fin N), V (Submission.BoseGases.actPerm N σ x) * (f x) ^ 2) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        simp only [Work.BoseSym.symAvgF, Submission.BoseGases.symAvg]
        rw [mul_assoc, Finset.sum_mul]
    _ = (1 / (Nat.factorial N : ℝ)) * ∫ x in BoseGases.box N L,
          ∑ σ : Equiv.Perm (Fin N), V (Submission.BoseGases.actPerm N σ x) * (f x) ^ 2 := by
        rw [MeasureTheory.integral_const_mul]
    _ = (1 / (Nat.factorial N : ℝ)) * ∑ σ : Equiv.Perm (Fin N),
          ∫ x in BoseGases.box N L, V (Submission.BoseGases.actPerm N σ x) * (f x) ^ 2 := by
        rw [MeasureTheory.integral_finsetSum _ (fun σ _ => hσ σ)]
    _ = (1 / (Nat.factorial N : ℝ)) * ∑ σ : Equiv.Perm (Fin N),
          ∫ x in BoseGases.box N L, V x * (f x) ^ 2 := by
        rw [Finset.sum_congr rfl (fun σ _ => hIσ σ)]
    _ = ∫ x in BoseGases.box N L, V x * (f x) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
        have hfac : (Nat.factorial N : ℝ) ≠ 0 := by positivity
        field_simp

end Work.BoseSym.Bridge
