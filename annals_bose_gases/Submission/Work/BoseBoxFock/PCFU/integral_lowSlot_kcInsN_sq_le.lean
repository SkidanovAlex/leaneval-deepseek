import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PCFU.chDimg_le
import Submission.Work.BoseBoxFock.PCFU.dirichletPeel
import Submission.Work.BoseBoxFock.PCFU.lowSlot_aQ_aP_sq_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.integral_lowSlot_kcInsN_sq_le`

The slice bound for the low-momentum slot of the pair operator `aQ ℓ j ∘ aP ℓ i`: with
`ℓ = ellH v μ`, `κ = chKappa v μ` and `Γ := lowSlot fc κ ℓ j (aQ ℓ j (aP ℓ i (boxRestrictR ℓ Φ)))`,

    ∫_{abox m ℓ} (Γ (kcInsN m i (0, r)))² dr  ≤  4·normB v μ (m+1) Φ / ℓ³ ,

and the integrand on the left is integrable on the box.

## The argument

The state `Γ` is **constant in the slot `i`**: `aP ℓ i Θ` already averages the `i`-th slot away
(`aP_update_self`), so `aQ ℓ j (aP ℓ i Θ)` does not see it either (`aP_aP_update_inner` +
`aQ_aP_update_invariant`), and `lowSlot fc κ ℓ j (·)` only ever reads the slots different from `i`
(`lowSlot_const_of_update_eq`).  Therefore the peel of the `i`-th coordinate
(`Submission.BoseGases.abox_integral_peel`) factorises the box integral of `Γ²`:

    ∫_{abox (m+1) ℓ} Γ² = ℓ³·∫_{abox m ℓ} (Γ (kcInsN m i (0, r)))² dr         (`lowSlot_aQ_aP_sq_peel`)

(the inner `y`-integral is over a constant).  Combining this with the `L²`-contraction
`PCFU.lowSlot_aQ_aP_sq_le` (the fibre `Q_L,j` and the pair `Q_jP_i` are both contractions,
constant `4` in the frozen statement) gives

    ℓ³·∫_{abox m ℓ} Γ(0,·)² = ∫_{abox (m+1) ℓ} Γ²
        ≤ 4·∫_{abox (m+1) ℓ} (boxRestrictR ℓ Φ)² = 4·‖Φ‖²_{L²(abox (m+1) ℓ)} = 4·normB v μ (m+1) Φ ,

and `ℓ > 0` (`ellH_pos`) yields the claim after division by `ℓ³`.

## Pieces used

* `PCFU.lowSlot_aQ_aP_sq_le` (PROVED) — the `L²`-contraction with constant `4`;
* `PCFU.lowSlot_aQ_aP_measurable_bounded` (PROVED) — measurability and uniform boundedness of `Γ`
  for a measurable, globally bounded state (needed by the peel);
* `PCFU.aQ_aP_update_invariant` (PROVED) — `aQ ℓ j (aP ℓ i Θ)` does not see the slot `i`.

Everything in this file is `sorry`-free.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-! ## 1. Two bookkeeping facts about the box -/

/-- **`boxRestrictR ℓ Φ` is measurable and globally bounded** for a continuous `Φ`: it is the
product of `Φ` with the indicator of the (measurable) box, and any bound of `|Φ|` on the compact
box bounds the restriction everywhere (the indicator is `0` outside). -/
lemma boxRestrictR_measurable_globally_bounded {n : ℕ} {ℓ : ℝ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    Measurable (Work.BoseBoxFock.boxRestrictR ℓ Φ)
      ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |Work.BoseBoxFock.boxRestrictR ℓ Φ x| ≤ C := by
  constructor
  · unfold Work.BoseBoxFock.boxRestrictR
    exact hΦ.measurable.mul
      (measurable_const.indicator (Submission.BoseGases.abox_measurable n ℓ))
  · obtain ⟨C, hC⟩ :=
      (Work.UBBInputs9.B.abox_isCompact n ℓ).exists_bound_of_continuousOn hΦ.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
    rw [Work.BoseBoxFock.boxRestrictR]
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · rw [Set.indicator_of_mem hx, mul_one]
      exact le_trans (by simpa [Real.norm_eq_abs] using hC x hx) (le_max_left _ _)
    · rw [Set.indicator_of_notMem hx, mul_zero, abs_zero]
      exact le_max_right _ _

/-- **`normB` at the honest box side**: `normB v μ n Φ = ∫_{abox n (ellH v μ)} Φ²`. -/
lemma normB_eq_integral_ellH (v : E3 → ℝ) {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v)
    (n : ℕ) (Φ : Submission.BoseGases.X n → ℝ) :
    Work.BoseBoxFix.normB v μ n Φ
      = ∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ), (Φ x) ^ 2 := by
  have hside : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  simp only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, Work.BoseBoxFock.ellH,
    if_pos hside]

/-- On the box, the square of the box restriction of `Φ` integrates to the square of `Φ`. -/
lemma boxRestrictR_sq_integral_eq {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ) :
    (∫ x in Submission.BoseGases.abox n ℓ, (Work.BoseBoxFock.boxRestrictR ℓ Φ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)]
    with x hx
  rw [Work.BoseBoxFock.boxRestrictR, Set.indicator_of_mem hx, mul_one]

/-! ## 2. `kcInsN` inserts by a slot update -/

/-- The inserted configuration is the `i`-slot update of the `y = 0` configuration. -/
lemma kcInsN_eq_update_of_zero {n : ℕ} (i : Fin (n + 1)) (r : Submission.BoseGases.X n)
    (y : E3) :
    Submission.BoseGases.kcInsN n i (y, r)
      = Function.update (Submission.BoseGases.kcInsN n i ((0 : E3), r)) i y := by
  funext k
  by_cases hk : k = i
  · subst hk
    rw [Submission.BoseGases.kc_insN_apply_same, Function.update_self]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    simp only [Submission.BoseGases.kc_insN_apply_succ, Function.update_apply,
      Fin.succAbove_ne i j, if_false]

/-! ## 3. The constancy of `Γ` in the peeled slot -/

/-- A slot-`j` low-momentum lift is constant in the slot `i` (`i ≠ j`) whenever its argument is:
`lowMult` only reads the slot `j` and the slots left untouched by the `i`-update. -/
lemma lowSlot_const_of_update_eq {n : ℕ} (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ)
    {i j : Fin n} (hij : i ≠ j) {Ψ : Submission.BoseGases.X n → ℝ}
    (hΨ : ∀ y z, Ψ (Function.update y i z) = Ψ y) (x : Submission.BoseGases.X n) (z : E3) :
    Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ (Function.update x i z)
      = Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ x := by
  have hkey : (fun y : E3 => Ψ (Function.update (Function.update x i z) j y))
      = fun y : E3 => Ψ (Function.update x j y) := by
    funext y
    rw [Function.update_comm hij z y x]
    exact hΨ (Function.update x j y) z
  simp only [Work.BoseBoxFix.lowSlot]
  rw [Function.update_of_ne (Ne.symm hij) z x, hkey]

/-- The pair operator `aQ ℓ j (aP ℓ i Θ)` does not see the slot `i` (`i ≠ j`). -/
lemma lowSlot_aQ_aP_const_in_coord_update {n : ℕ} (i j : Fin (n + 1)) (hij : i ≠ j)
    (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) (Θ : Submission.BoseGases.X (n + 1) → ℝ)
    (x : Submission.BoseGases.X (n + 1)) (z : E3) :
    Work.BoseBoxFix.lowSlot fc κ ℓ j
        (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) (Function.update x i z)
      = Work.BoseBoxFix.lowSlot fc κ ℓ j
          (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) x :=
  lowSlot_const_of_update_eq fc κ ℓ hij (fun y w => aQ_aP_update_invariant hij y w) x z

/-! ## 4. The peel of `Γ²` over the inserted slot -/

/-- **The peel of the `Γ`-square**: since `Γ = lowSlot fc κ ℓ j (aQ ℓ j (aP ℓ i (boxRestrictR ℓ Φ)))`
is constant in the slot `i`, its square integral over the box is `ℓ³` times the integral of its
values on the peeled configurations. -/
lemma lowSlot_aQ_aP_sq_peel {m : ℕ} (i j : Fin (m + 1)) (hij : i ≠ j)
    (fc : Work.BoseBoxFix.LowCut) {ℓ κ D : ℝ} (hℓ : 0 < ℓ) (hD : 0 ≤ D)
    {Φ : Submission.BoseGases.X (m + 1) → ℝ}
    (hΓm : Measurable (fun x => Work.BoseBoxFix.lowSlot fc κ ℓ j
      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i
        (Work.BoseBoxFock.boxRestrictR ℓ Φ))) x))
    (hΓb : ∀ x, |Work.BoseBoxFix.lowSlot fc κ ℓ j
      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i
        (Work.BoseBoxFock.boxRestrictR ℓ Φ))) x| ≤ D) :
    (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
        (Work.BoseBoxFix.lowSlot fc κ ℓ j (Submission.BoseGases.aQ ℓ j
          (Submission.BoseGases.aP ℓ i (Work.BoseBoxFock.boxRestrictR ℓ Φ))) x) ^ 2)
      = ℓ ^ 3 * ∫ r in Submission.BoseGases.abox m ℓ,
          (Work.BoseBoxFix.lowSlot fc κ ℓ j (Submission.BoseGases.aQ ℓ j
            (Submission.BoseGases.aP ℓ i (Work.BoseBoxFock.boxRestrictR ℓ Φ)))
              (Submission.BoseGases.kcInsN m i ((0 : E3), r))) ^ 2 := by
  have hInt : IntegrableOn (fun x : Submission.BoseGases.X (m + 1) =>
      (Work.BoseBoxFix.lowSlot fc κ ℓ j (Submission.BoseGases.aQ ℓ j
        (Submission.BoseGases.aP ℓ i (Work.BoseBoxFock.boxRestrictR ℓ Φ))) x) ^ 2)
      (Submission.BoseGases.abox (m + 1) ℓ) := by
    refine IntegrableOn.of_bound ((Work.UBBInputs9.B.abox_isCompact (m + 1) ℓ).measure_lt_top)
      (hΓm.pow_const 2).aestronglyMeasurable (D ^ 2) ?_
    filter_upwards with x
    have h := hΓb x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [Submission.BoseGases.abox_integral_peel i _ hInt,
    ← MeasureTheory.integral_const_mul (ℓ ^ 3)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with r
  have hconst : ∀ y : E3,
      (Work.BoseBoxFix.lowSlot fc κ ℓ j (Submission.BoseGases.aQ ℓ j
        (Submission.BoseGases.aP ℓ i (Work.BoseBoxFock.boxRestrictR ℓ Φ)))
          (Submission.BoseGases.kcInsN m i (y, r))) ^ 2
        = (Work.BoseBoxFix.lowSlot fc κ ℓ j (Submission.BoseGases.aQ ℓ j
          (Submission.BoseGases.aP ℓ i (Work.BoseBoxFock.boxRestrictR ℓ Φ)))
            (Submission.BoseGases.kcInsN m i ((0 : E3), r))) ^ 2 := by
    intro y
    rw [kcInsN_eq_update_of_zero i r y,
      lowSlot_aQ_aP_const_in_coord_update i j hij fc κ ℓ (Work.BoseBoxFock.boxRestrictR ℓ Φ)
        (Submission.BoseGases.kcInsN m i ((0 : E3), r)) y]
  rw [funext hconst, MeasureTheory.integral_const, MeasureTheory.Measure.real,
    MeasureTheory.Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le,
    ENNReal.toReal_ofReal (by positivity)]
  simp [smul_eq_mul]

/-! ## 5. The target -/

theorem integral_lowSlot_kcInsN_sq_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < BoseGases.a v) {m : ℕ} {Φ : Submission.BoseGases.X (m + 1) → ℝ}
    (hΦ : Continuous Φ) (fc : Work.BoseBoxFix.LowCut) (i j : Fin (m + 1)) (hij : i ≠ j) :
    MeasureTheory.Integrable (fun r : Submission.BoseGases.X m =>
        (Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ)
            (Work.BoseBoxFock.ellH v μ) j
            (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
              (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
                (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ)))
            (Submission.BoseGases.kcInsN m i ((0 : EuclideanSpace ℝ (Fin 3)), r))) ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
        (Submission.BoseGases.abox m (Work.BoseBoxFock.ellH v μ)))
    ∧ (∫ r in Submission.BoseGases.abox m (Work.BoseBoxFock.ellH v μ),
        (Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ)
            (Work.BoseBoxFock.ellH v μ) j
            (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
              (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
                (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ)))
            (Submission.BoseGases.kcInsN m i ((0 : EuclideanSpace ℝ (Fin 3)), r))) ^ 2)
      ≤ 4 * Work.BoseBoxFix.normB v μ (m + 1) Φ / (Work.BoseBoxFock.ellH v μ) ^ 3 := by
  have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hκ : 0 < Work.BoseBoxFock.PCFU.chKappa v μ := chKappa_pos v hμ hav
  -- the state data used by the peel
  obtain ⟨hΘm, C, hC0, hΘb⟩ := boxRestrictR_measurable_globally_bounded (Φ := Φ) hΦ
  obtain ⟨hΓm, D, hD0, hΓb⟩ :=
    lowSlot_aQ_aP_measurable_bounded (fc := fc) (μ := μ) (ℓ := Work.BoseBoxFock.ellH v μ)
      (κ := Work.BoseBoxFock.PCFU.chKappa v μ) hℓ hκ hC0 hΘm hΘb
  -- the peel of the inserted slot
  have hpeel :=
    lowSlot_aQ_aP_sq_peel (m := m) i j hij fc hℓ hD0 hΓm hΓb
  -- the `L²`-contraction, with the frozen constant `4`
  have hcontr := lowSlot_aQ_aP_sq_le (n := m + 1) (ℓ := Work.BoseBoxFock.ellH v μ)
    (κ := Work.BoseBoxFock.PCFU.chKappa v μ) hℓ i j hij fc hκ hΦ
  -- the identification of the right-hand side with `normB`
  have hbox := boxRestrictR_sq_integral_eq (Work.BoseBoxFock.ellH v μ) Φ
  have hnorm := (normB_eq_integral_ellH v hμ hav (m + 1) Φ).symm
  -- the chain `ℓ³·A ≤ 4·normB`
  have hchain :
      (Work.BoseBoxFock.ellH v μ) ^ 3 *
          (∫ r in Submission.BoseGases.abox m (Work.BoseBoxFock.ellH v μ),
            (Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ)
                (Work.BoseBoxFock.ellH v μ) j
                (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                  (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
                    (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ)))
                (Submission.BoseGases.kcInsN m i ((0 : E3), r))) ^ 2)
        ≤ 4 * Work.BoseBoxFix.normB v μ (m + 1) Φ := by
    rw [← hpeel]
    calc (∫ x in Submission.BoseGases.abox (m + 1) (Work.BoseBoxFock.ellH v μ),
          (Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ)
              (Work.BoseBoxFock.ellH v μ) j
              (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
                  (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ))) x) ^ 2)
        ≤ 4 * ∫ x in Submission.BoseGases.abox (m + 1) (Work.BoseBoxFock.ellH v μ),
            (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ x) ^ 2 := hcontr
      _ = 4 * ∫ x in Submission.BoseGases.abox (m + 1) (Work.BoseBoxFock.ellH v μ),
            (Φ x) ^ 2 := by rw [hbox]
      _ = 4 * Work.BoseBoxFix.normB v μ (m + 1) Φ := by rw [hnorm]
  refine ⟨?_, ?_⟩
  · -- integrability of the squared slice
    have hmeas : Measurable (fun r : Submission.BoseGases.X m =>
        Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ)
          (Work.BoseBoxFock.ellH v μ) j
          (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
            (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
              (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ)))
          (Submission.BoseGases.kcInsN m i ((0 : E3), r))) :=
      hΓm.comp (((Submission.BoseGases.kcInsN m i).measurable).comp
        (by fun_prop : Measurable fun r : Submission.BoseGases.X m => ((0 : E3), r)))
    refine IntegrableOn.of_bound
      ((Work.UBBInputs9.B.abox_isCompact m (Work.BoseBoxFock.ellH v μ)).measure_lt_top)
      (hmeas.pow_const 2).aestronglyMeasurable (D ^ 2) ?_
    filter_upwards with r
    have h := hΓb (Submission.BoseGases.kcInsN m i ((0 : E3), r))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  · -- the slice bound
    have h3 : 0 < (Work.BoseBoxFock.ellH v μ) ^ 3 := by positivity
    rw [le_div_iff₀ h3]
    calc (∫ r in Submission.BoseGases.abox m (Work.BoseBoxFock.ellH v μ),
            (Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ)
                (Work.BoseBoxFock.ellH v μ) j
                (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                  (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
                    (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ)))
                (Submission.BoseGases.kcInsN m i ((0 : E3), r))) ^ 2)
            * (Work.BoseBoxFock.ellH v μ) ^ 3
        = (Work.BoseBoxFock.ellH v μ) ^ 3 *
            (∫ r in Submission.BoseGases.abox m (Work.BoseBoxFock.ellH v μ),
              (Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ)
                  (Work.BoseBoxFock.ellH v μ) j
                  (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                    (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
                      (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ)))
                  (Submission.BoseGases.kcInsN m i ((0 : E3), r))) ^ 2) := by ring
      _ ≤ 4 * Work.BoseBoxFix.normB v μ (m + 1) Φ := hchain

end Work.BoseBoxFock.PCFU
