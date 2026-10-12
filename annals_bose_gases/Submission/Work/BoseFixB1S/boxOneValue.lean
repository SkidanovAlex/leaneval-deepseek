import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1S.BoxPIndFlat
import Submission.Work.BoseFixB1S.BoxQIndCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxOneValue` — the one-body value collapse at the sliding box

FS `thm:smallbox`'s `q₀` has a *one-body* line: the expectation of the one-body potential
`−μ Σᵢ w₁(xᵢ)` in the box-projected state `P_{B,i}Φ`.  Since FS's box projection carries the box
indicator, `P_{B,i}Φ` is constant in the slot `i` up to that indicator, so the *slot* integral of
`(P_{B,i}Φ)²` weighted by any slot function collapses to the mean over the box:

    Σ_i ∫_{abox N ℓ} (P_{B,i}Φ)²·(∫_{acube ℓ} f (x i) y) dy
      = |B|⁻¹·(∫_{B × acube ℓ} f) · Σ_i ∫_{abox N ℓ} (P_{B,i}Φ)² ,

with `B = dlBox ℓ d u` and `|B| = boxMass ℓ d u = ∫ 1_B`.  The constant `|B|⁻¹` in front of the
fibre integral is exactly the `(1/volA)` of `boxPInd`, and the `Σ_i ∫ (P_{B,i}Φ)²` on the right is
what the neighbouring box identities (`boxQ0Square`) also produce.

## The proof is unconditional in the state

The statement carries *no* hypothesis on `Φ` (in particular no continuity) and no integrability
of the collapsed integrands: `|B|` may even vanish.  Two facts make this possible:

* `Work.BoseFixB1S.Q0C.abox_peel_transport` — the measure preserving change of variables
  `kcInsN m i : kcE3 × X m ≃ᵐ X (m+1)`, stated for an **arbitrary** function;
* `MeasureTheory.setIntegral_prod_mul` — the product factorization of the Bochner integral over a
  product measure, which Mathlib proves **unconditionally** (the non-integrable case being handled
  by the `integral_undef` convention `∫ = 0`).

Together they give the peel of any *product* integrand, and `boxPInd` squares into a product
(`Work.BoseFixB1S.Q0C.boxPInd_sq_kcInsN`).  The only extra input is Fubini for the fibre
(which needs, and gets, the hypothesis `hf`), and the degenerate case `boxMass = 0`, in which
`boxPInd` vanishes identically because `(0:ℝ)⁻¹ = 0`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

-- NOTE: `ℝ³` is the *global* `notation "ℝ³" => EuclideanSpace ℝ (Fin 3)` of
-- `Submission.Work.BoseKinLoc.Defs` (in the import cone here); a `local notation` for the same
-- token would be ambiguous, so the global one is used.

open Submission.BoseGases

set_option maxHeartbeats 800000

/-- The restricted volume on `acube ℓ ×ˢ abox m ℓ` is the product of the restricted volumes. -/
theorem volume_restrict_acube_prod_abox (m : ℕ) (ℓ : ℝ) :
    (((volume : Measure ℝ³).restrict (acube ℓ)).prod
        ((volume : Measure (X m)).restrict (abox m ℓ)))
      = (volume : Measure (ℝ³ × X m)).restrict (acube ℓ ×ˢ abox m ℓ) :=
  Measure.prod_restrict _ _

/-- **Peel of a one-slot product integrand.**  If `F` factorises on the image of the insertion
`kcInsN m i` as `F (kcInsN m i (t,r)) = Q t * P r`, then its integral over the `(m+1)`-box is
the product of the two one-slot integrals over `acube ℓ` and `abox m ℓ`.  No regularity hypothesis
is needed: the change of variables is measure preserving and the product factorization of the
integral holds unconditionally (with the `∫ = 0` convention). -/
theorem integral_abox_peel_prod {m : ℕ} {ℓ : ℝ} (i : Fin (m + 1))
    {F : X (m + 1) → ℝ} {P : X m → ℝ} {Q : ℝ³ → ℝ}
    (hF : ∀ (t : ℝ³) (r : X m), F (kcInsN m i (t, r)) = Q t * P r) :
    (∫ x in abox (m + 1) ℓ, F x)
      = (∫ t in acube ℓ, Q t) * (∫ r in abox m ℓ, P r) := by
  rw [Q0C.abox_peel_transport (n := m) (ℓ := ℓ) i F]
  have hstep : (∫ q : ℝ³ × X m, F (kcInsN m i q)
        ∂(((volume : Measure ℝ³).restrict (acube ℓ)).prod
          ((volume : Measure (X m)).restrict (abox m ℓ))))
      = ∫ q : ℝ³ × X m, Q q.1 * P q.2
        ∂(((volume : Measure ℝ³).restrict (acube ℓ)).prod
          ((volume : Measure (X m)).restrict (abox m ℓ))) :=
    integral_congr_ae (Filter.Eventually.of_forall (fun q => by
      obtain ⟨t, r⟩ := q
      simpa using hF t r))
  rw [hstep, volume_restrict_acube_prod_abox]
  exact setIntegral_prod_mul Q P (acube ℓ) (abox m ℓ)

/-- **The peel of the box projection.**  Squaring `boxPInd` and multiplying by a slot weight `Q`
makes the peeled integrand a product of a function of the inserted slot and a function of the
remaining coordinates, so the `(m+1)`-box integral factors. -/
theorem boxPInd_peel {m : ℕ} {ℓ vA : ℝ} {A : Set ℝ³} (i : Fin (m + 1))
    (Φ : X (m + 1) → ℝ) (Q : ℝ³ → ℝ) :
    (∫ x in abox (m + 1) ℓ, (UBBInputs8.boxPInd vA A i Φ x) ^ 2 * Q (x i))
      = (∫ t in acube ℓ, A.indicator (fun _ => (1 : ℝ)) t * Q t)
        * (∫ r in abox m ℓ, (Q0C.oneRest vA A i Φ r) ^ 2) := by
  refine integral_abox_peel_prod (ℓ := ℓ) i
    (P := fun r => (Q0C.oneRest vA A i Φ r) ^ 2)
    (Q := fun t => A.indicator (fun _ => (1 : ℝ)) t * Q t) ?_
  intro t r
  rw [Q0C.boxPInd_sq_kcInsN, kc_insN_apply_same]
  ring

/-- **The self value of the box projection.**  With the constant slot weight, the same peel gives
the squared norm of `P_{B,i}Φ` as the box volume times the peeled fibre square integral. -/
theorem boxPInd_self {m : ℕ} {ℓ vA : ℝ} {A : Set ℝ³} (hA : MeasurableSet A)
    (i : Fin (m + 1)) (Φ : X (m + 1) → ℝ) :
    (∫ x in abox (m + 1) ℓ, (UBBInputs8.boxPInd vA A i Φ x) ^ 2)
      = (∫ t in acube ℓ, A.indicator (fun _ => (1 : ℝ)) t)
        * (∫ r in abox m ℓ, (Q0C.oneRest vA A i Φ r) ^ 2) := by
  have h1 : (∫ x in abox (m + 1) ℓ, (UBBInputs8.boxPInd vA A i Φ x) ^ 2)
      = ∫ x in abox (m + 1) ℓ,
          (UBBInputs8.boxPInd vA A i Φ x) ^ 2 * A.indicator (fun _ => (1 : ℝ)) (x i) := by
    apply setIntegral_congr_fun (abox_measurable (m + 1) ℓ)
    intro x _
    show (UBBInputs8.boxPInd vA A i Φ x) ^ 2
      = (UBBInputs8.boxPInd vA A i Φ x) ^ 2 * A.indicator (fun _ => (1 : ℝ)) (x i)
    by_cases hx : x i ∈ A
    · rw [Set.indicator_of_mem hx, mul_one]
    · rw [Set.indicator_of_notMem hx, mul_zero]
      have hzero : UBBInputs8.boxPInd vA A i Φ x = 0 := by
        simp only [UBBInputs8.boxPInd]
        rw [Set.indicator_of_notMem hx, mul_zero]
      rw [hzero]
      ring
  have h2 : (∫ t in acube ℓ, A.indicator (fun _ => (1 : ℝ)) t * A.indicator (fun _ => (1 : ℝ)) t)
      = ∫ t in acube ℓ, A.indicator (fun _ => (1 : ℝ)) t := by
    apply setIntegral_congr_fun (acube_measurable ℓ)
    intro t _
    by_cases ht : t ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, ht]
  rw [h1, boxPInd_peel i Φ (fun t => A.indicator (fun _ => (1 : ℝ)) t), h2]

/-- **Fubini for the fibre form.**  The box-indicator weighted slot integral of the fibre
`t ↦ ∫_{acube ℓ} f t y` is the box-product integral of `f`. -/
theorem setIntegral_fibre_eq_prod {ℓ : ℝ} {A : Set ℝ³} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) {f : ℝ³ → ℝ³ → ℝ}
    (hf : IntegrableOn (fun q : ℝ³ × ℝ³ => f q.1 q.2) (A ×ˢ acube ℓ) volume) :
    (∫ t in acube ℓ, A.indicator (fun _ => (1 : ℝ)) t * (∫ y in acube ℓ, f t y))
      = ∫ q in A ×ˢ acube ℓ, f q.1 q.2 := by
  rw [setIntegral_indicator_one_mul hA hAc]
  have hf' : IntegrableOn (fun q : ℝ³ × ℝ³ => f q.1 q.2) (A ×ˢ acube ℓ)
      (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using hf
  rw [← setIntegral_prod (fun q : ℝ³ × ℝ³ => f q.1 q.2) hf']
  rw [Measure.volume_eq_prod ℝ³ ℝ³]

/-- **The one-body value collapse** (the box analogue of `AeValue.sumOne_value_ae`): the
per-slot integral of the squared box projection against the fibre of `f` collapses onto the
box average. -/
theorem boxOneValue {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ)
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (u : EuclideanSpace ℝ (Fin 3)) (Φ : Submission.BoseGases.X n → ℝ)
    (hf : MeasureTheory.IntegrableOn
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => f q.1 q.2)
      (Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.acube ℓ) MeasureTheory.volume) :
    (∑ i : Fin n,
        ∫ x in Submission.BoseGases.abox n ℓ,
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
          * (∫ y in Submission.BoseGases.acube ℓ, f (x i) y))
      = (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹
          * (∫ q in Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.acube ℓ,
              f q.1 q.2)
          * (∑ i : Fin n,
              ∫ x in Submission.BoseGases.abox n ℓ,
                (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2) := by
  have hA : MeasurableSet (dlBox ℓ d u) := Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : dlBox ℓ d u ⊆ acube ℓ := Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hvoldef : Work.SmallBoxSliding.boxMass ℓ d u = (volume : Measure ℝ³).real (dlBox ℓ d u) :=
    Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u
  -- the fibre integral is the box-product integral
  have hFub : (∫ t in acube ℓ,
        (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) t * (∫ y in acube ℓ, f t y))
      = ∫ q in dlBox ℓ d u ×ˢ acube ℓ, f q.1 q.2 :=
    setIntegral_fibre_eq_prod hA hAc hf
  -- the box volume is the slot integral of the box indicator
  have hvol_eq : (∫ t in acube ℓ, (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) t)
      = Work.SmallBoxSliding.boxMass ℓ d u := by
    have h1 : (∫ t in acube ℓ, (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) t * (1 : ℝ))
        = Work.SmallBoxSliding.boxMass ℓ d u := by
      rw [setIntegral_indicator_one_mul hA hAc (fun _ => (1 : ℝ)),
        MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
      exact hvoldef.symm
    have h2 : (∫ t in acube ℓ, (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) t * (1 : ℝ))
        = ∫ t in acube ℓ, (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) t := by
      apply setIntegral_congr_fun (acube_measurable ℓ)
      intro t _
      simp only [mul_one]
    rw [← h2]
    exact h1
  cases n with
  | zero => simp
  | succ m =>
    by_cases hv : Work.SmallBoxSliding.boxMass ℓ d u = 0
    · -- degenerate case: `boxMass = 0` makes the box projection vanish identically
      have hzero : ∀ (i : Fin (m + 1)) (x : X (m + 1)),
          UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u) i Φ x = 0 := by
        intro i x
        simp only [UBBInputs8.boxPInd, hv]
        simp
      have hL : (∑ i : Fin (m + 1), ∫ x in abox (m + 1) ℓ,
            (UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (dlBox ℓ d u) i Φ x) ^ 2 * (∫ y in acube ℓ, f (x i) y)) = 0 := by
        simp [hzero]
      have hR : (∑ i : Fin (m + 1), ∫ x in abox (m + 1) ℓ,
            (UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (dlBox ℓ d u) i Φ x) ^ 2) = 0 := by
        simp [hzero]
      rw [hL, hR, hv]
      simp
    · -- the per-slot value identity
      have hself : ∀ i : Fin (m + 1),
          (∫ x in abox (m + 1) ℓ,
              (UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (dlBox ℓ d u) i Φ x) ^ 2)
            = (∫ t in acube ℓ, (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) t)
              * (∫ r in abox m ℓ,
                  (Q0C.oneRest (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u) i Φ r) ^ 2) :=
        fun i => boxPInd_self hA i Φ
      have hkey : ∀ i : Fin (m + 1),
          (∫ x in abox (m + 1) ℓ,
              (UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (dlBox ℓ d u) i Φ x) ^ 2 * (∫ y in acube ℓ, f (x i) y))
            = (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹
                * (∫ q in dlBox ℓ d u ×ˢ acube ℓ, f q.1 q.2)
                * (∫ x in abox (m + 1) ℓ,
                    (UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                      (dlBox ℓ d u) i Φ x) ^ 2) := by
        intro i
        rw [boxPInd_peel (ℓ := ℓ) (vA := Work.SmallBoxSliding.boxMass ℓ d u)
          (A := dlBox ℓ d u) i Φ (fun t => ∫ y in acube ℓ, f t y)]
        rw [hFub, hself i, hvol_eq]
        have hAlg : (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹
              * (∫ q in dlBox ℓ d u ×ˢ acube ℓ, f q.1 q.2)
              * (Work.SmallBoxSliding.boxMass ℓ d u
                * ∫ r in abox m ℓ,
                    (Q0C.oneRest (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u) i Φ r) ^ 2)
            = (∫ q in dlBox ℓ d u ×ˢ acube ℓ, f q.1 q.2)
              * (∫ r in abox m ℓ,
                  (Q0C.oneRest (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u) i Φ r) ^ 2) := by
          calc (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹
                * (∫ q in dlBox ℓ d u ×ˢ acube ℓ, f q.1 q.2)
                * (Work.SmallBoxSliding.boxMass ℓ d u
                  * ∫ r in abox m ℓ,
                      (Q0C.oneRest (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u) i Φ r) ^ 2)
              = ((Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ * Work.SmallBoxSliding.boxMass ℓ d u)
                * ((∫ q in dlBox ℓ d u ×ˢ acube ℓ, f q.1 q.2)
                  * ∫ r in abox m ℓ,
                      (Q0C.oneRest (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u) i Φ r) ^ 2) := by
                ring
            _ = (∫ q in dlBox ℓ d u ×ˢ acube ℓ, f q.1 q.2)
                  * (∫ r in abox m ℓ,
                      (Q0C.oneRest (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u) i Φ r) ^ 2) := by
                rw [inv_mul_cancel₀ hv, one_mul]
        exact hAlg.symm
      have hsum : (∑ i : Fin (m + 1), ∫ x in abox (m + 1) ℓ,
            (UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (dlBox ℓ d u) i Φ x) ^ 2 * (∫ y in acube ℓ, f (x i) y))
          = (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹
              * (∫ q in dlBox ℓ d u ×ˢ acube ℓ, f q.1 q.2)
              * (∑ i : Fin (m + 1), ∫ x in abox (m + 1) ℓ,
                  (UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (dlBox ℓ d u) i Φ x) ^ 2) := by
        rw [Finset.sum_congr rfl (fun i _ => hkey i), Finset.mul_sum]
      exact hsum

end Work.BoseFixB1S
