import ChallengeDeps
import Submission.Work.BoseSym.Perm.integral_sq_symAvgF_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseSym.Bridge.integral_symAvgF_mul_eq`

**Self-adjointness of the symmetrisation average.**

`symAvgF N f = (N!)⁻¹ · ∑_σ f ∘ actPerm σ` is the average of the relabellings of
`f`; regarded as an operator on functions on the box it is the orthogonal
projection onto the permutation invariant (bosonic) functions.  Here we prove
the *adjointness* identity

`∫_{box N L} (symAvgF N V) · g = ∫_{box N L} V · (symAvgF N g)`

for every `V` integrable on the box and every `g` which is almost everywhere
strongly measurable and bounded (`|g| ≤ D`) on the box.  Note that `g` is *not*
assumed symmetric: the average on the right-hand side is the pointwise average
of the relabellings of `g`.

The identity is the standard "average the relabelling" computation.  Writing
`T_σ f = f ∘ actPerm σ`, the left-hand side expands as
`(N!)⁻¹ ∑_σ ∫ (T_σ V) g`, and each summand is computed by the change of
variables `x ↦ actPerm σ x` (which preserves both the box and Lebesgue measure
on it, `IntegralSqSymAvg.integral_actPerm_box`):

`∫ (T_σ V) · g = ∫ V · (T_{σ⁻¹} g)`.

Summing over `σ` and using that `σ ↦ σ⁻¹` is a bijection of `Equiv.Perm (Fin N)`
produces `(N!)⁻¹ ∑_σ ∫ V · (T_σ g)`, which is precisely the expansion of the
right-hand side.

The only analytic input is that the summands are integrable: since `|g| ≤ D`,
`|V · (g ∘ actPerm σ)| ≤ D · |V ∘ actPerm σ|`, and `|V|` is integrable on the box
(as is each relabelling of it, `IntegralSqSymAvg.integrableOn_actPerm_box_iff`),
so `Integrable.mono'` applies.

## Contents

* `integrable_mul_actPerm_left`, `integrable_mul_actPerm_right` — integrability
  of the two families of summands;
* `integral_symAvgF_mul_eq` — the adjointness identity.
-/

namespace Work.BoseSym.Bridge

open MeasureTheory Filter
open scoped Topology Real

set_option autoImplicit false

/-- **Integrability of the summands (left side).**  If `V` is integrable on the
box and `g` is bounded by `D`, then `x ↦ V x · g (actPerm σ x)` is integrable on
the box: it is a.e. strongly measurable and dominated by `D · |V|`, which is
integrable. -/
lemma integrable_mul_actPerm_left {N : ℕ} {L : ℝ} {V g : Work.BoseSym.Conf N → ℝ}
    (hV : Work.BoseSym.IntOnBox N L V)
    (hgm : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict (BoseGases.box N L)))
    {D : ℝ} (hgD : ∀ x, |g x| ≤ D) (σ : Equiv.Perm (Fin N)) :
    MeasureTheory.Integrable
      (fun x => V x * g (Submission.BoseGases.actPerm N σ x))
      (MeasureTheory.volume.restrict (BoseGases.box N L)) := by
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun x => g (Submission.BoseGases.actPerm N σ x))
      (MeasureTheory.volume.restrict (BoseGases.box N L)) :=
    (MeasureTheory.MeasurePreserving.aestronglyMeasurable_comp_iff
      (Work.BoseSym.Perm.IntegralSqSymAvg.measurePreserving_tauPerm_box L σ)
      (Work.BoseSym.Perm.IntegralSqSymAvg.measurableEmbedding_tauPerm N σ)).mpr hgm
  refine (hV.abs.mul_const D).mono' (hV.aestronglyMeasurable.mul haesm) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hgD _) (abs_nonneg _)

/-- **Integrability of the summands (right side).**  The relabelled integrand
`x ↦ V (actPerm σ x) · g x` is integrable on the box, dominated by
`D · |V ∘ actPerm σ|`. -/
lemma integrable_mul_actPerm_right {N : ℕ} {L : ℝ} {V g : Work.BoseSym.Conf N → ℝ}
    (hV : Work.BoseSym.IntOnBox N L V)
    (hgm : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict (BoseGases.box N L)))
    {D : ℝ} (hgD : ∀ x, |g x| ≤ D) (σ : Equiv.Perm (Fin N)) :
    MeasureTheory.Integrable
      (fun x => V (Submission.BoseGases.actPerm N σ x) * g x)
      (MeasureTheory.volume.restrict (BoseGases.box N L)) := by
  have hVσ : MeasureTheory.Integrable
      (fun x => V (Submission.BoseGases.actPerm N σ x))
      (MeasureTheory.volume.restrict (BoseGases.box N L)) :=
    (Work.BoseSym.Perm.IntegralSqSymAvg.integrableOn_actPerm_box_iff L σ V).mpr hV
  have hb : MeasureTheory.Integrable
      (fun x => |V (Submission.BoseGases.actPerm N σ x)| * D)
      (MeasureTheory.volume.restrict (BoseGases.box N L)) :=
    ((Work.BoseSym.Perm.IntegralSqSymAvg.integrableOn_actPerm_box_iff L σ
      (fun x => |V x|)).mpr hV.abs).mul_const D
  refine hb.mono' (hVσ.aestronglyMeasurable.mul hgm) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hgD x) (abs_nonneg _)

theorem integral_symAvgF_mul_eq {N : ℕ} {L : ℝ} {V g : Work.BoseSym.Conf N → ℝ}
    (hV : Work.BoseSym.IntOnBox N L V)
    (hgm : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict (BoseGases.box N L)))
    {D : ℝ} (hD : 0 ≤ D) (hgD : ∀ x, |g x| ≤ D) :
    ∫ x in BoseGases.box N L, (Work.BoseSym.symAvgF N V) x * g x =
      ∫ x in BoseGases.box N L, V x * (Work.BoseSym.symAvgF N g) x := by
  classical
  have hI1 : ∀ σ : Equiv.Perm (Fin N), MeasureTheory.Integrable
      (fun x => V x * g (Submission.BoseGases.actPerm N σ x))
      (MeasureTheory.volume.restrict (BoseGases.box N L)) :=
    fun σ => integrable_mul_actPerm_left hV hgm hgD σ
  have hI2 : ∀ σ : Equiv.Perm (Fin N), MeasureTheory.Integrable
      (fun x => V (Submission.BoseGases.actPerm N σ x) * g x)
      (MeasureTheory.volume.restrict (BoseGases.box N L)) :=
    fun σ => integrable_mul_actPerm_right hV hgm hgD σ
  -- the permutation inverse cancels the action
  have hcancel : ∀ (σ : Equiv.Perm (Fin N)) (x : Work.BoseSym.Conf N),
      Submission.BoseGases.actPerm N σ⁻¹ (Submission.BoseGases.actPerm N σ x) = x := by
    intro σ x
    funext i
    simp [Submission.BoseGases.actPerm]
  -- change of variables: `∫ (V ∘ σ) · g = ∫ V · (g ∘ σ⁻¹)`
  have hcv : ∀ σ : Equiv.Perm (Fin N),
      ∫ x in BoseGases.box N L, V (Submission.BoseGases.actPerm N σ x) * g x
        = ∫ x in BoseGases.box N L, V x * g (Submission.BoseGases.actPerm N σ⁻¹ x) := by
    intro σ
    have h1 : (∫ x in BoseGases.box N L, V (Submission.BoseGases.actPerm N σ x) * g x)
        = ∫ x in BoseGases.box N L,
            (fun y : Work.BoseSym.Conf N =>
              V y * g (Submission.BoseGases.actPerm N σ⁻¹ y))
              (Submission.BoseGases.actPerm N σ x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hcancel σ x]
    rw [h1, Work.BoseSym.Perm.IntegralSqSymAvg.integral_actPerm_box L σ
      (fun y : Work.BoseSym.Conf N => V y * g (Submission.BoseGases.actPerm N σ⁻¹ y))]
  -- pointwise expansion of the left-hand side
  have hsymL : ∀ x : Work.BoseSym.Conf N, (Work.BoseSym.symAvgF N V) x * g x
      = (1 / (Nat.factorial N : ℝ)) * ∑ σ : Equiv.Perm (Fin N),
          (V (Submission.BoseGases.actPerm N σ x) * g x) := by
    intro x
    simp only [Work.BoseSym.symAvgF, Submission.BoseGases.symAvg]
    rw [mul_assoc, Finset.sum_mul]
  -- pointwise expansion of the right-hand side
  have hsymR : ∀ x : Work.BoseSym.Conf N, V x * (Work.BoseSym.symAvgF N g) x
      = (1 / (Nat.factorial N : ℝ)) * ∑ σ : Equiv.Perm (Fin N),
          (V x * g (Submission.BoseGases.actPerm N σ x)) := by
    intro x
    simp only [Work.BoseSym.symAvgF, Submission.BoseGases.symAvg]
    have h1 : V x * ((1 / (Nat.factorial N : ℝ)) * ∑ σ : Equiv.Perm (Fin N),
        g (Submission.BoseGases.actPerm N σ x))
      = (1 / (Nat.factorial N : ℝ)) * (V x * ∑ σ : Equiv.Perm (Fin N),
        g (Submission.BoseGases.actPerm N σ x)) := by ring
    rw [h1, Finset.mul_sum]
  -- the right-hand side, expanded as a sum of integrals
  have hRHS : ∫ x in BoseGases.box N L, V x * (Work.BoseSym.symAvgF N g) x
      = (1 / (Nat.factorial N : ℝ)) * ∑ σ : Equiv.Perm (Fin N),
          ∫ x in BoseGases.box N L, V x * g (Submission.BoseGases.actPerm N σ x) := by
    calc ∫ x in BoseGases.box N L, V x * (Work.BoseSym.symAvgF N g) x
        = ∫ x in BoseGases.box N L, (1 / (Nat.factorial N : ℝ)) *
            ∑ σ : Equiv.Perm (Fin N),
              (V x * g (Submission.BoseGases.actPerm N σ x)) :=
          integral_congr_ae (Filter.Eventually.of_forall hsymR)
      _ = (1 / (Nat.factorial N : ℝ)) * ∫ x in BoseGases.box N L,
            ∑ σ : Equiv.Perm (Fin N),
              (V x * g (Submission.BoseGases.actPerm N σ x)) :=
          integral_const_mul _ _
      _ = (1 / (Nat.factorial N : ℝ)) * ∑ σ : Equiv.Perm (Fin N),
            ∫ x in BoseGases.box N L, V x * g (Submission.BoseGases.actPerm N σ x) := by
          rw [integral_finsetSum _ (fun σ _ => hI1 σ)]
  -- reindexing the group by the inversion bijection
  have hre : (∑ σ : Equiv.Perm (Fin N),
        ∫ x in BoseGases.box N L, V x * g (Submission.BoseGases.actPerm N σ⁻¹ x))
      = ∑ σ : Equiv.Perm (Fin N),
        ∫ x in BoseGases.box N L, V x * g (Submission.BoseGases.actPerm N σ x) := by
    simpa using Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin N)))
      (fun τ : Equiv.Perm (Fin N) =>
        ∫ x in BoseGases.box N L, V x * g (Submission.BoseGases.actPerm N τ x))
  calc ∫ x in BoseGases.box N L, (Work.BoseSym.symAvgF N V) x * g x
      = ∫ x in BoseGases.box N L, (1 / (Nat.factorial N : ℝ)) *
          ∑ σ : Equiv.Perm (Fin N),
            (V (Submission.BoseGases.actPerm N σ x) * g x) :=
        integral_congr_ae (Filter.Eventually.of_forall hsymL)
    _ = (1 / (Nat.factorial N : ℝ)) * ∫ x in BoseGases.box N L,
          ∑ σ : Equiv.Perm (Fin N),
            (V (Submission.BoseGases.actPerm N σ x) * g x) :=
        integral_const_mul _ _
    _ = (1 / (Nat.factorial N : ℝ)) * ∑ σ : Equiv.Perm (Fin N),
          ∫ x in BoseGases.box N L, V (Submission.BoseGases.actPerm N σ x) * g x := by
        rw [integral_finsetSum _ (fun σ _ => hI2 σ)]
    _ = (1 / (Nat.factorial N : ℝ)) * ∑ σ : Equiv.Perm (Fin N),
          ∫ x in BoseGases.box N L, V x * g (Submission.BoseGases.actPerm N σ⁻¹ x) := by
        rw [Finset.sum_congr rfl (fun σ _ => hcv σ)]
    _ = (1 / (Nat.factorial N : ℝ)) * ∑ σ : Equiv.Perm (Fin N),
          ∫ x in BoseGases.box N L, V x * g (Submission.BoseGases.actPerm N σ x) := by
        rw [hre]
    _ = ∫ x in BoseGases.box N L, V x * (Work.BoseSym.symAvgF N g) x := hRHS.symm

end Work.BoseSym.Bridge
