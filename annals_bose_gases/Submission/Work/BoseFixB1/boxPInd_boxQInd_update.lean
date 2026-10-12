import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Q1FormDefs
import Submission.Work.BoseFixB1S.integrableOn_boxFragments
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxPInd_boxQInd_update`

The `(B)`-pattern update identity for FS's box projections
`P_i = UBBInputs8.boxPInd V A i` and `Q_i = UBBInputs8.boxQInd V A i = 1_A(x_i)·Φ − P_i`
(FS `eq:HBU`): the configuration `x` with its `s`-th slot set to `u`, evaluated against
`P_s Q_t Φ` (`s ≠ t`).

Because `P_s` only sees the box indicator in the `s`-th slot and the `s`-slot mean, and an
`s`-update leaves the `t`-th coordinate alone (`s ≠ t`), the result is

  `1_A(u)·1_A(x_t)·( V⁻¹∫_A Φ(x[s↦z]) − V⁻¹·(V⁻¹∫_A∫_A Φ(x[s↦z][t↦w])) )`,

i.e. the box indicators times the difference of the `s`-slot mean of `Φ` and the normalised
`s`-then-`t` double mean of `Φ` — the `P_{B,s}Q_{B,t}` shape FS use in `eq:Q1n0`.

The proof is the pointwise identity
`Q_tΦ(x[s↦z]) = 1_A(x_t)·(Φ(x[s↦z]) − V⁻¹∫_A Φ(x[s↦z][t↦w]))`
(pure algebra in the definitions), followed by the two slot-integral manipulations
`∫_A 1_A(x_t)·(f z − V⁻¹·∫_A g z w) = 1_A(x_t)·(∫_A f − V⁻¹·∫_A∫_A g)`:
the constant `1_A(x_t)` is pulled out (`integral_const_mul`, which needs no integrability) and
the difference is split with `integral_sub`, whose side conditions are the slot integrability of
`z ↦ Φ(x[s↦z])` and of `z ↦ ∫_A Φ(x[s↦z][t↦w])`. Both follow from the continuity of `Φ` and
`A ⊆ acube ℓ` (the box is bounded, and the `s`- and `t`-updates stay in the analysis box).

No positivity of `V` is used: the identity is polynomial in `V⁻¹` and the two slot means.
-/

noncomputable section

namespace Work.BoseFixB1

open MeasureTheory

/-! ## Slot integrability -/

/-- The `i`-slot integral `z ↦ f (x[i↦z])` of a function bounded on the analysis box is
integrable over `A ⊆ acube ℓ` (for `x` in the box). -/
private theorem integrableOn_slot {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hA : MeasurableSet A) (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {x : Submission.BoseGases.X N} (hx : x ∈ Submission.BoseGases.abox N ℓ)
    {f : Submission.BoseGases.X N → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ y ∈ Submission.BoseGases.abox N ℓ, |f y| ≤ C) :
    IntegrableOn (fun z : E3 => f (Function.update x i z)) A volume := by
  have hfin : (volume : Measure E3) A < ⊤ := Work.BoseFixB1S.Q0C.volume_A_lt_top hℓ hAc
  refine MeasureTheory.IntegrableOn.of_bound hfin ?_ C ?_
  · exact (hf.comp (by fun_prop : Measurable (fun z : E3 => Function.update x i z))).aestronglyMeasurable
  · rw [MeasureTheory.ae_restrict_iff' hA]
    exact Filter.Eventually.of_forall fun z hz => by
      rw [Real.norm_eq_abs]
      exact hC _ (Work.BoseFixB1S.Q0C.update_mem_abox hAc hx i hz)

/-- The `(i,j)`-slot double mean `z ↦ ∫_A Φ (x[i↦z][j↦w])` is integrable over `A ⊆ acube ℓ`
(for `x` in the analysis box). -/
private theorem integrableOn_slotInner {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hA : MeasurableSet A) (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i j : Fin N)
    {x : Submission.BoseGases.X N} (hx : x ∈ Submission.BoseGases.abox N ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) {C : ℝ}
    (hC : ∀ y ∈ Submission.BoseGases.abox N ℓ, |Φ y| ≤ C) :
    IntegrableOn (fun z : E3 => ∫ w in A, Φ (Function.update (Function.update x i z) j w))
      A volume := by
  have hfin : (volume : Measure E3) A < ⊤ := Work.BoseFixB1S.Q0C.volume_A_lt_top hℓ hAc
  refine MeasureTheory.IntegrableOn.of_bound hfin ?_ (C * (volume : Measure E3).real A) ?_
  · exact ((Work.BoseFixB1S.measurable_fibreMean A hA j hΦc.measurable).comp
      (by fun_prop : Measurable (fun z : E3 => Function.update x i z))).aestronglyMeasurable
  · rw [MeasureTheory.ae_restrict_iff' hA]
    exact Filter.Eventually.of_forall fun z hz =>
      MeasureTheory.norm_setIntegral_le_of_norm_le_const hfin fun w hw => by
        rw [Real.norm_eq_abs]
        exact hC _ (Work.BoseFixB1S.Q0C.update_mem_abox hAc
          (Work.BoseFixB1S.Q0C.update_mem_abox hAc hx i hz) j hw)

/-! ## The identity -/

theorem boxPInd_boxQInd_update {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ)
    {A : Set Work.BoseFixB1.E3} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {s t : Fin N} (hst : s ≠ t) {x : Submission.BoseGases.X N}
    (hx : x ∈ Submission.BoseGases.abox N ℓ) (u : Work.BoseFixB1.E3) :
    Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxQInd V A t Φ) (Function.update x s u)
      = A.indicator (fun _ => (1 : ℝ)) u * A.indicator (fun _ => (1 : ℝ)) (x t)
        * ((1 / V) * (∫ z in A, Φ (Function.update x s z))
          - (1 / V) * ((1 / V) * ∫ z in A, ∫ w in A,
              Φ (Function.update (Function.update x s z) t w))) := by
  -- a uniform bound for `Φ` on the analysis box
  obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox N ℓ) (f := Φ) hΦc.continuousOn
  have hB' : ∀ y ∈ Submission.BoseGases.abox N ℓ, |Φ y| ≤ B := fun y hy => by
    simpa [Real.norm_eq_abs] using hB y hy
  -- pointwise form of `Q_tΦ` at `x[s↦z]`
  have hpt : ∀ z : E3, Work.UBBInputs8.boxQInd V A t Φ (Function.update x s z)
      = A.indicator (fun _ => (1 : ℝ)) (x t)
        * (Φ (Function.update x s z)
            - (1 / V) * ∫ w in A, Φ (Function.update (Function.update x s z) t w)) := by
    intro z
    rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
    have h1 : (Function.update x s z) t = x t :=
      Function.update_of_ne (fun h => hst h.symm) z x
    rw [h1]
    ring
  -- the `s`-slot integral of `Q_tΦ`
  have hInt : (∫ z in A, Work.UBBInputs8.boxQInd V A t Φ (Function.update x s z))
      = A.indicator (fun _ => (1 : ℝ)) (x t)
        * ((∫ z in A, Φ (Function.update x s z))
            - (1 / V) * ∫ z in A, ∫ w in A,
                Φ (Function.update (Function.update x s z) t w)) := by
    rw [show (∫ z in A, Work.UBBInputs8.boxQInd V A t Φ (Function.update x s z))
        = ∫ z in A, A.indicator (fun _ => (1 : ℝ)) (x t)
            * (Φ (Function.update x s z)
              - (1 / V) * ∫ w in A, Φ (Function.update (Function.update x s z) t w))
        from MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_sub
      (integrableOn_slot hℓ hA hAc s hx hΦc.measurable hB')
      (MeasureTheory.Integrable.const_mul
        (integrableOn_slotInner hℓ hA hAc s t hx hΦc hB') (1 / V))]
    rw [MeasureTheory.integral_const_mul]
  -- the `s`-slot projection at `x[s↦u]`
  have hL : Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxQInd V A t Φ) (Function.update x s u)
      = (1 / V) * (∫ z in A, Work.UBBInputs8.boxQInd V A t Φ (Function.update x s z))
        * A.indicator (fun _ => (1 : ℝ)) u :=
    Work.BoseFixB1S.Q0C.boxPInd_update_self V A s (Work.UBBInputs8.boxQInd V A t Φ) x u
  rw [hL, hInt]
  ring

end Work.BoseFixB1
