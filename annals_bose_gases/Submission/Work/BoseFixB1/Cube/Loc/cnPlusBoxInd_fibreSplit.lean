import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Cube.Loc.cnPlusBoxInd_eq_zero_of_vanishes_on_tubes
import Submission.Work.BoseFixB1.Cube.Loc.subsectorSupp_slice_snd
import Submission.Work.BoseFixB1B.cnPlusBoxInd_slice_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Cube.Loc.cnPlusBoxInd_fibreSplit`

The **excited-count slot** of the Step-Loc fibre formula (`DESIGN_stepLoc.md` §1(iii)): the
FS-faithful excited-particle count `n₊(B) = cnPlusBoxInd a A V Φ` (`Work.UBBInputs8.cnPlusBoxInd`,
FS `eq:HBU`) splits as the integral, over the **out-of-box** configurations
`Dloc m a A = (acube a \ A)^m`, of the count of the **in-box fibre** `fibre k m Φ y`:

    cnPlusBoxInd a A V Φ = ∫ y in Dloc m a A, cnPlusBoxInd a A V (fibre k m Φ y) ,

for every continuous `Φ` on the `(k+m)`-particle box supported a.e. on the subsector where the
first `k` particles lie in `A` and the last `m` outside it (`SubsectorSupp`).

## Proof

The count is a sum of one-slot terms, so the proved block split
`Work.BoseFixB1B.cns_split_gen` (the general form of `cnPlusBoxInd_slice_split`) writes

    cnPlusBoxInd a A V Φ = (∫ w in abox m a, cnPlusBoxInd a A V (fibre k m Φ w))
                             + ∫ y in abox k a, cnPlusBoxInd a A V (slice y) .

Two reductions finish:

* **the second term vanishes.**  By `subsectorSupp_merge` + Fubini, for a.e. `y` the slice
  `w ↦ Φ (merge (y,w))` vanishes a.e. on each slot-tube `{w | w j ∈ A}`; the count of such a
  state is zero (`cnPlusBoxInd_eq_zero_of_vanishes_on_tubes`).
* **the first term localises to `Dloc`.**  For a.e. `w` with some slot in `A` the fibre
  `fibre k m Φ w` vanishes a.e. on the box (the support condition forces `w j ∉ A` for all `j`),
  so its count is zero (`cnPlusBoxInd_eq_zero_of_ae_eq_zero`); hence the integrand of the first
  term vanishes a.e. off `Dloc m a A` and the two set integrals agree.

Nothing here is analytic: every step is an a.e. support statement plus the pointwise vanishing of
a sum of squares of `L²`-norms.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1.Cube.Loc

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Pointwise shape of the box projection -/

/-- FS's mean-free box projection, in the shape used below: the box indicator in the slot times
the deviation of the state from its slot mean over the box. -/
lemma boxQInd_eq_indicator_mul_sub_mean {m : ℕ} {V : ℝ} {A : Set E3} (i : Fin m)
    (Ψ : X m → ℝ) (x : X m) :
    Work.UBBInputs8.boxQInd V A i Ψ x
      = A.indicator (fun _ => (1 : ℝ)) (x i)
        * (Ψ x - (1 / V) * ∫ z in A, Ψ (Function.update x i z)) := by
  simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
  ring

/-! ## 2. The slot mean of an a.e.-vanishing state -/

/-- The product of the slot mean with the box indicator vanishes a.e. when the state does.

This is the `volA = (volume A).toReal` case of the proved
`Work.BoseFixB1S.boxPInd_ae_eq_zero_of_ae_eq_zero` (`|B| > 0`), together with the (trivial) case
of a null box, where the slot mean is identically zero. -/
theorem mean_mul_indicator_ae_eq_zero_of_ae_eq_zero {m : ℕ} {a : ℝ} (ha : 0 < a)
    {A : Set E3} (hA : MeasurableSet A) (hAc : A ⊆ acube a) (i : Fin m)
    {Ψ : X m → ℝ} (hΨm : Measurable Ψ)
    (hΨ : Ψ =ᵐ[(volume : Measure (X m)).restrict (abox m a)] 0) :
    (fun x : X m => A.indicator (fun _ => (1 : ℝ)) (x i) *
        (∫ z in A, Ψ (Function.update x i z)))
      =ᵐ[(volume : Measure (X m)).restrict (abox m a)] 0 := by
  by_cases hpos : 0 < (volume A).toReal
  · have hP := Work.BoseFixB1S.boxPInd_ae_eq_zero_of_ae_eq_zero (N := m) (ℓ := a)
      (volA := (volume A).toReal) ha hpos hA rfl hAc i hΨm hΨ
    have hv : (volume A).toReal ≠ 0 := ne_of_gt hpos
    refine hP.mono (fun x hx => ?_)
    simp only [Work.UBBInputs8.boxPInd, Pi.zero_apply] at hx ⊢
    have h5 : (1 / (volume A).toReal) * (A.indicator (fun _ => (1 : ℝ)) (x i)
        * (∫ z in A, Ψ (Function.update x i z))) = 0 := by
      rw [← hx]
      ring
    have h6 : A.indicator (fun _ => (1 : ℝ)) (x i) * (∫ z in A, Ψ (Function.update x i z))
        = (volume A).toReal * ((1 / (volume A).toReal)
            * (A.indicator (fun _ => (1 : ℝ)) (x i)
              * (∫ z in A, Ψ (Function.update x i z)))) := by
      rw [one_div, mul_inv_cancel_left₀ hv]
    rw [h6, h5, mul_zero]
  · have hto0 : (volume A).toReal = 0 :=
      le_antisymm (not_lt.mp hpos) (ENNReal.toReal_nonneg)
    have hvol0 : (volume : Measure E3) A = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).mp hto0 with h | h
      · exact h
      · exact absurd h (ne_of_lt (lt_of_le_of_lt (measure_mono hAc) (acube_lt_top a ha.le)))
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp only [setIntegral_measure_zero (fun z : E3 => Ψ (Function.update x i z)) hvol0,
      mul_zero, Pi.zero_apply]

/-! ## 3. The vanishing of the excited count -/

/-- A state vanishing a.e. on the box has vanishing excited count. -/
theorem cnPlusBoxInd_eq_zero_of_ae_eq_zero {m : ℕ} {a V : ℝ} (ha : 0 < a)
    {A : Set E3} (hA : MeasurableSet A) (hAc : A ⊆ acube a)
    {Ψ : X m → ℝ} (hΨm : Measurable Ψ)
    (hΨ : Ψ =ᵐ[(volume : Measure (X m)).restrict (abox m a)] 0) :
    Work.UBBInputs8.cnPlusBoxInd a A V Ψ = 0 := by
  have hQ : ∀ i : Fin m, Work.UBBInputs8.boxQInd V A i Ψ
      =ᵐ[(volume : Measure (X m)).restrict (abox m a)] 0 := by
    intro i
    have h1 : (fun x : X m => A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x)
        =ᵐ[(volume : Measure (X m)).restrict (abox m a)] 0 :=
      hΨ.mono (fun x hx => by
        simp only [Pi.zero_apply] at hx ⊢
        rw [hx, mul_zero])
    have h2 := mean_mul_indicator_ae_eq_zero_of_ae_eq_zero ha hA hAc i hΨm hΨ
    have h2' : (fun x : X m => (1 / V) * (A.indicator (fun _ => (1 : ℝ)) (x i)
          * (∫ z in A, Ψ (Function.update x i z))))
        =ᵐ[(volume : Measure (X m)).restrict (abox m a)] 0 :=
      h2.mono (fun x hx => by
        simp only [Pi.zero_apply] at hx ⊢
        rw [hx, mul_zero])
    have h3 : (fun x : X m => A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
          - (1 / V) * (A.indicator (fun _ => (1 : ℝ)) (x i)
              * (∫ z in A, Ψ (Function.update x i z))))
        =ᵐ[(volume : Measure (X m)).restrict (abox m a)] 0 := by
      filter_upwards [h1, h2'] with x hx1 hx2
      simp only [Pi.zero_apply] at hx1 hx2 ⊢
      rw [hx1, hx2, sub_zero]
    exact h3.mono (fun x hx => by
      simp only [Pi.zero_apply] at hx ⊢
      rw [boxQInd_eq_indicator_mul_sub_mean i Ψ x, ← hx]
      ring)
  rw [Work.UBBInputs8.cnPlusBoxInd]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  refine integral_eq_zero_of_ae ?_
  exact (hQ i).mono (fun x hx => by
    simp only [Pi.zero_apply] at hx ⊢
    rw [hx]
    norm_num)

/-! ## 4. The a.e. support, sliced -/

/-- The a.e. support condition, with the **in-box** block first (outer). -/
lemma subsectorSupp_slice_fst {k m : ℕ} {a : ℝ} {A : Set E3} {Φ : X (k + m) → ℝ}
    (hsupp : SubsectorSupp k m a A Φ) :
    ∀ᵐ y ∂((volume : Measure (X k)).restrict (abox k a)),
      ∀ᵐ w ∂((volume : Measure (X m)).restrict (abox m a)),
        Φ (mergeBlock k m (y, w)) ≠ 0 →
          (∀ i : Fin k, y i ∈ A) ∧ (∀ j : Fin m, w j ∉ A) :=
  Measure.ae_ae_of_ae_prod (subsectorSupp_merge hsupp)

/-! ## 5. The target -/

theorem cnPlusBoxInd_fibreSplit {k m : ℕ} {a : ℝ} (ha : 0 < a) (hk : 0 < k)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a) (V : ℝ)
    {Φ : Submission.BoseGases.X (k + m) → ℝ} (hΦc : Continuous Φ)
    (hsupp : Work.BoseFixB1.Cube.Loc.SubsectorSupp k m a A Φ) :
    Work.UBBInputs8.cnPlusBoxInd a A V Φ
      = ∫ y in Work.BoseFixB1.Cube.Loc.Dloc m a A,
          Work.UBBInputs8.cnPlusBoxInd a A V (Work.BoseFixB1.Cube.Loc.fibre k m Φ y) := by
  -- ### the block split of the count
  have hsplit := Work.BoseFixB1B.cns_split_gen (N1 := k) (N2 := m) (ℓ := a) (V := V)
    ha hA hAc hΦc
  -- ### the first block identifies with the fibre
  have hfib : ∀ w : X m, (fun y : X k => Φ (mergeBlock k m (y, w))) = fibre k m Φ w := by
    intro w
    funext z
    simp only [fibre, mkSlot_eq_mergeBlock]
  have hT1 : (∫ w in abox m a, Work.UBBInputs8.cnPlusBoxInd a A V
        fun y => Φ (mergeBlock k m (y, w)))
      = ∫ w in abox m a, Work.UBBInputs8.cnPlusBoxInd a A V (fibre k m Φ w) := by
    refine integral_congr_ae ?_
    filter_upwards with w
    rw [hfib w]
  -- ### the second block's count vanishes
  have hT2 : (∫ y in abox k a, Work.UBBInputs8.cnPlusBoxInd a A V
        fun w => Φ (mergeBlock k m (y, w))) = 0 := by
    refine integral_eq_zero_of_ae ?_
    refine (subsectorSupp_slice_fst hsupp).mono (fun y hy => ?_)
    refine cnPlusBoxInd_eq_zero_of_vanishes_on_tubes ha hA hAc ?_ ?_
    · exact (hΦc.comp
        (Work.BoseFixB1B.cns_split_continuous_mergeBlock_snd (N1 := k) (N2 := m) y)).measurable
    · intro j
      have hmeas : MeasurableSet {w : X m | w j ∈ A} := (measurable_pi_apply j) hA
      filter_upwards [hy.filter_mono
          (ae_mono (Measure.restrict_le_self (s := {w : X m | w j ∈ A}))),
        ae_restrict_mem hmeas] with w h1 h2
      simp only [Pi.zero_apply]
      by_contra hne
      exact (h1 hne).2 j h2
  -- ### the first block's integrand localises to `Dloc`
  have hD : (∫ w in abox m a, Work.UBBInputs8.cnPlusBoxInd a A V (fibre k m Φ w))
      = ∫ w in Dloc m a A, Work.UBBInputs8.cnPlusBoxInd a A V (fibre k m Φ w) := by
    have hmeasD : MeasurableSet (abox m a \ Dloc m a A) :=
      (abox_measurable m a).diff (measurableSet_Dloc m hA)
    -- the integrand vanishes a.e. off `Dloc`
    have hzero : (fun w : X m => Work.UBBInputs8.cnPlusBoxInd a A V (fibre k m Φ w))
        =ᵐ[(volume : Measure (X m)).restrict (abox m a \ Dloc m a A)] 0 := by
      have hslice := (subsectorSupp_slice_snd hsupp).filter_mono
        (ae_mono (Measure.restrict_le_self (s := abox m a \ Dloc m a A)))
      rw [Measure.restrict_restrict_of_subset (s := abox m a \ Dloc m a A)
        (t := abox m a) Set.sdiff_subset] at hslice
      filter_upwards [hslice, ae_restrict_mem hmeasD] with w hw hwmem
      obtain ⟨j, hj⟩ := exists_mem_A_of_mem_abox_not_mem_Dloc hwmem.1 hwmem.2
      refine cnPlusBoxInd_eq_zero_of_ae_eq_zero ha hA hAc ?_ ?_
      · have hm : Measurable (fun y : X k => Φ (mergeBlock k m (y, w))) :=
          (hΦc.comp (Work.BoseFixB1B.cns_split_continuous_mergeBlock_fst
            (N1 := k) (N2 := m) w)).measurable
        rwa [hfib w] at hm
      · refine hw.mono (fun y hy => ?_)
        simp only [fibre, mkSlot_eq_mergeBlock]
        by_contra hne
        exact (hy hne).2 j hj
    -- hence the two indicator integrands agree a.e.
    have hS : (volume : Measure (X m))
        {x : X m | (abox m a).indicator
              (fun w => Work.UBBInputs8.cnPlusBoxInd a A V (fibre k m Φ w)) x
            ≠ (Dloc m a A).indicator
              (fun w => Work.UBBInputs8.cnPlusBoxInd a A V (fibre k m Φ w)) x} = 0 := by
      have hsub : {x : X m | (abox m a).indicator
              (fun w => Work.UBBInputs8.cnPlusBoxInd a A V (fibre k m Φ w)) x
            ≠ (Dloc m a A).indicator
              (fun w => Work.UBBInputs8.cnPlusBoxInd a A V (fibre k m Φ w)) x}
          ⊆ {x : X m | Work.UBBInputs8.cnPlusBoxInd a A V (fibre k m Φ x) ≠ 0}
            ∩ (abox m a \ Dloc m a A) := by
        intro x hx
        by_cases hxa : x ∈ abox m a
        · have h1 : (abox m a).indicator
              (fun w => Work.UBBInputs8.cnPlusBoxInd a A V (fibre k m Φ w)) x
              = Work.UBBInputs8.cnPlusBoxInd a A V (fibre k m Φ x) :=
            Set.indicator_of_mem hxa _
          by_cases hxd : x ∈ Dloc m a A
          · exact absurd (by rw [h1, Set.indicator_of_mem hxd]) hx
          · refine ⟨?_, ⟨hxa, hxd⟩⟩
            intro hF
            exact hx (by rw [h1, Set.indicator_of_notMem hxd, hF])
        · have h1 : (abox m a).indicator
              (fun w => Work.UBBInputs8.cnPlusBoxInd a A V (fibre k m Φ w)) x = 0 :=
            Set.indicator_of_notMem hxa _
          have h2 : (Dloc m a A).indicator
              (fun w => Work.UBBInputs8.cnPlusBoxInd a A V (fibre k m Φ w)) x = 0 :=
            Set.indicator_of_notMem (fun hxd => hxa (Dloc_subset_abox m a A hxd)) _
          exact absurd (by rw [h1, h2]) hx
      have hae : (volume : Measure (X m))
          ({x : X m | Work.UBBInputs8.cnPlusBoxInd a A V (fibre k m Φ x) ≠ 0}
            ∩ (abox m a \ Dloc m a A)) = 0 := by
        rw [← Measure.restrict_apply' hmeasD]
        exact ae_iff.mp hzero
      exact measure_mono_null hsub hae
    rw [← MeasureTheory.integral_indicator (μ := (volume : Measure (X m)))
          (abox_measurable m a)
          (f := fun w => Work.UBBInputs8.cnPlusBoxInd a A V (fibre k m Φ w)),
      ← MeasureTheory.integral_indicator (μ := (volume : Measure (X m)))
          (measurableSet_Dloc m hA)
          (f := fun w => Work.UBBInputs8.cnPlusBoxInd a A V (fibre k m Φ w))]
    exact integral_congr_ae hS
  rw [hsplit, hT1, hT2, add_zero, ← hD]

end Work.BoseFixB1.Cube.Loc
