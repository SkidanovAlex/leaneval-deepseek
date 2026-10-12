import ChallengeDeps
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseSym.Perm.integral_sq_symAvgF_le`

The symmetrisation average

`symAvgF N u x = (N!)⁻¹ · ∑_σ u (actPerm σ x)`

is an `L²` contraction on the box `box N L = ([0,L]³)^N`:

`∫_{box N L} (symAvgF N u)² ≤ ∫_{box N L} u²`.

This is the "symmetrisation does not increase the `L²` norm" fact underlying the
bosonic (Perron–Frobenius) reduction: averaging a trial function over the
symmetric group is a convex combination of its relabellings, hence Jensen's
inequality applies pointwise, and the box (with Lebesgue measure) is invariant
under relabelling, so the average of the relabelled squares has the same
integral as the original square.

## Proof outline

* `sq_symAvgF_le_symAvgF_sq` : the pointwise Jensen step,
  `(symAvgF N u x)² ≤ symAvgF N (u²) x`, obtained from Cauchy–Schwarz
  (`sq_sum_le_card_mul_sum_sq`) on the finite group `Equiv.Perm (Fin N)`.
* `measurePreserving_tauPerm_box` / `integral_actPerm_box` /
  `integrableOn_actPerm_box_iff` : relabelling the particles preserves Lebesgue
  measure restricted to the box, hence integrals and integrability.
* Assembly: `∫ (symAvgF N (u²)) = (N!)⁻¹ ∑_σ ∫ (u² ∘ σ) = ∫ u²`, and
  `integral_mono_of_nonneg` applied to the pointwise Jensen inequality.
-/

namespace Work.BoseSym.Perm

open MeasureTheory Filter
open scoped Topology Real

namespace IntegralSqSymAvg

/-- The particle permutation `tauPerm N σ` is a measurable embedding (it is the
forward map of the measurable equivalence `MeasurableEquiv.piCongrLeft`). -/
lemma measurableEmbedding_tauPerm (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    MeasurableEmbedding (tauPerm N σ) := by
  have hfun : ((MeasurableEquiv.piCongrLeft (fun _ : Fin N => E3) σ.symm :
      Conf N ≃ᵐ Conf N) : Conf N → Conf N) = tauPerm N σ := by
    funext x i
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, tauPerm]
  rw [← hfun]
  exact (MeasurableEquiv.piCongrLeft (fun _ : Fin N => E3) σ.symm).measurableEmbedding

/-- Lebesgue measure restricted to the box is invariant under the relabelling
`tauPerm σ` of the particles. -/
lemma measurePreserving_tauPerm_box {N : ℕ} (L : ℝ) (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (tauPerm N σ)
      ((volume : Measure (Conf N)).restrict (BoseGases.box N L))
      ((volume : Measure (Conf N)).restrict (BoseGases.box N L)) := by
  have hmeas : Measurable (tauPerm N σ) := tauPerm_measurable N σ
  have hpre : (tauPerm N σ) ⁻¹' (BoseGases.box N L) = BoseGases.box N L :=
    Set.ext (fun x => Submission.BoseGases.actPerm_mem_box_iff σ x)
  refine ⟨hmeas, ?_⟩
  have h1 := Measure.restrict_map (μ := (volume : Measure (Conf N)))
    (f := tauPerm N σ) hmeas (s := BoseGases.box N L)
    (Submission.BoseGases.box_measurable N L)
  rw [MeasurePreserving.map_eq (measurePreserving_tauPerm N σ), hpre] at h1
  exact h1.symm

/-- Change of variables in the integral over the box: relabelling the particles
does not change the integral. -/
lemma integral_actPerm_box {N : ℕ} (L : ℝ) (σ : Equiv.Perm (Fin N)) (g : Conf N → ℝ) :
    (∫ x in BoseGases.box N L, g (Submission.BoseGases.actPerm N σ x))
      = ∫ x in BoseGases.box N L, g x :=
  MeasurePreserving.integral_comp (measurePreserving_tauPerm_box L σ)
    (measurableEmbedding_tauPerm N σ) g

/-- Integrability on the box is preserved by relabelling the particles. -/
lemma integrableOn_actPerm_box_iff {N : ℕ} (L : ℝ) (σ : Equiv.Perm (Fin N))
    (g : Conf N → ℝ) :
    IntegrableOn (fun x => g (Submission.BoseGases.actPerm N σ x)) (BoseGases.box N L) volume
      ↔ IntegrableOn g (BoseGases.box N L) volume :=
  MeasurePreserving.integrable_comp_emb (measurePreserving_tauPerm_box L σ)
    (measurableEmbedding_tauPerm N σ)

/-- Pointwise Jensen inequality for the symmetrisation average: the square of
the average is at most the average of the squares. -/
lemma sq_symAvgF_le_symAvgF_sq {N : ℕ} (u : Conf N → ℝ) (x : Conf N) :
    (symAvgF N u x) ^ 2 ≤ symAvgF N (fun y => (u y) ^ 2) x := by
  simp only [symAvgF, Submission.BoseGases.symAvg]
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Equiv.Perm (Fin N))))
    (f := fun σ : Equiv.Perm (Fin N) => u (Submission.BoseGases.actPerm N σ x))
  have hcast : (↑((Finset.univ : Finset (Equiv.Perm (Fin N))).card) : ℝ)
      = (Nat.factorial N : ℝ) := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  calc ((1 / (Nat.factorial N : ℝ)) * ∑ σ : Equiv.Perm (Fin N),
          u (Submission.BoseGases.actPerm N σ x)) ^ 2
      = (1 / (Nat.factorial N : ℝ)) ^ 2 *
          (∑ σ : Equiv.Perm (Fin N), u (Submission.BoseGases.actPerm N σ x)) ^ 2 := by ring
    _ ≤ (1 / (Nat.factorial N : ℝ)) ^ 2 *
          ((Nat.factorial N : ℝ) * ∑ σ : Equiv.Perm (Fin N),
            (u (Submission.BoseGases.actPerm N σ x)) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        rwa [hcast] at hcs
    _ = (1 / (Nat.factorial N : ℝ)) * ∑ σ : Equiv.Perm (Fin N),
          (u (Submission.BoseGases.actPerm N σ x)) ^ 2 := by
        field_simp

end IntegralSqSymAvg

theorem integral_sq_symAvgF_le {N : ℕ} {L : ℝ} (hL : 0 < L) {u : Work.BoseSym.Conf N → ℝ}
    (hu : MeasureTheory.IntegrableOn (fun x => (u x) ^ 2) (BoseGases.box N L) MeasureTheory.volume) :
    ∫ x in BoseGases.box N L, (Work.BoseSym.symAvgF N u x) ^ 2 ≤ ∫ x in BoseGases.box N L, (u x) ^ 2 := by
  classical
  have hIntσ : ∀ σ : Equiv.Perm (Fin N),
      Integrable (fun x => (u (Submission.BoseGases.actPerm N σ x)) ^ 2)
        (volume.restrict (BoseGases.box N L)) :=
    fun σ => (IntegralSqSymAvg.integrableOn_actPerm_box_iff L σ (fun y => (u y) ^ 2)).mpr hu
  have hintσ : ∀ σ : Equiv.Perm (Fin N),
      ∫ x in BoseGases.box N L, (u (Submission.BoseGases.actPerm N σ x)) ^ 2
        = ∫ x in BoseGases.box N L, (u x) ^ 2 :=
    fun σ => IntegralSqSymAvg.integral_actPerm_box L σ (fun y => (u y) ^ 2)
  have hsum_int : Integrable (fun x => ∑ σ : Equiv.Perm (Fin N),
        (u (Submission.BoseGases.actPerm N σ x)) ^ 2) (volume.restrict (BoseGases.box N L)) := by
    have aux : ∀ t : Finset (Equiv.Perm (Fin N)), Integrable (fun x =>
        ∑ σ ∈ t, (u (Submission.BoseGases.actPerm N σ x)) ^ 2)
        (volume.restrict (BoseGases.box N L)) := by
      intro t
      induction t using Finset.induction with
      | empty => simp
      | insert a t hat ih =>
          have key : (fun x => ∑ σ ∈ insert a t,
                (u (Submission.BoseGases.actPerm N σ x)) ^ 2)
              = fun x => (u (Submission.BoseGases.actPerm N a x)) ^ 2
                  + ∑ σ ∈ t, (u (Submission.BoseGases.actPerm N σ x)) ^ 2 := by
            funext x
            rw [Finset.sum_insert hat]
          rw [key]
          exact ((hIntσ a).add ih).congr
            (Eventually.of_forall fun x => by simp [Pi.add_apply])
    exact aux Finset.univ
  have hTint : Integrable (fun x => Work.BoseSym.symAvgF N (fun y => (u y) ^ 2) x)
      (volume.restrict (BoseGases.box N L)) := by
    have := hsum_int.const_mul (1 / (Nat.factorial N : ℝ))
    simpa only [Work.BoseSym.symAvgF, Submission.BoseGases.symAvg] using this
  have hmono : ∫ x in BoseGases.box N L, (Work.BoseSym.symAvgF N u x) ^ 2
      ≤ ∫ x in BoseGases.box N L, Work.BoseSym.symAvgF N (fun y => (u y) ^ 2) x :=
    integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hTint
      (Eventually.of_forall fun x => IntegralSqSymAvg.sq_symAvgF_le_symAvgF_sq u x)
  have hTeq : ∫ x in BoseGases.box N L, Work.BoseSym.symAvgF N (fun y => (u y) ^ 2) x
      = ∫ x in BoseGases.box N L, (u x) ^ 2 := by
    have h1 : ∫ x in BoseGases.box N L, Work.BoseSym.symAvgF N (fun y => (u y) ^ 2) x
        = (1 / (Nat.factorial N : ℝ)) * ∑ σ : Equiv.Perm (Fin N),
            ∫ x in BoseGases.box N L, (u (Submission.BoseGases.actPerm N σ x)) ^ 2 := by
      simp only [Work.BoseSym.symAvgF, Submission.BoseGases.symAvg]
      rw [integral_const_mul, integral_finsetSum _ (fun σ _ => hIntσ σ)]
    have h2 : (∑ σ : Equiv.Perm (Fin N),
          ∫ x in BoseGases.box N L, (u (Submission.BoseGases.actPerm N σ x)) ^ 2)
        = (Nat.factorial N : ℝ) * ∫ x in BoseGases.box N L, (u x) ^ 2 := by
      rw [Finset.sum_congr rfl (fun σ _ => hintσ σ)]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    have h3 : (1 / (Nat.factorial N : ℝ)) * ((Nat.factorial N : ℝ) *
          ∫ x in BoseGases.box N L, (u x) ^ 2) = ∫ x in BoseGases.box N L, (u x) ^ 2 := by
      have hnfac : (Nat.factorial N : ℝ) ≠ 0 := by positivity
      field_simp
    calc ∫ x in BoseGases.box N L, Work.BoseSym.symAvgF N (fun y => (u y) ^ 2) x
        = (1 / (Nat.factorial N : ℝ)) * ∑ σ : Equiv.Perm (Fin N),
            ∫ x in BoseGases.box N L, (u (Submission.BoseGases.actPerm N σ x)) ^ 2 := h1
      _ = (1 / (Nat.factorial N : ℝ)) * ((Nat.factorial N : ℝ) *
            ∫ x in BoseGases.box N L, (u x) ^ 2) := by rw [h2]
      _ = ∫ x in BoseGases.box N L, (u x) ^ 2 := h3
  linarith

end Work.BoseSym.Perm
