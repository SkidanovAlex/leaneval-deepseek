import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Cube.Loc.subsectorSupp_slice_snd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1.Cube.Loc

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# `Work.BoseFixB1.Cube.Loc.qLHSword_fibreSplit_of_integrable`

The **potential slot** of the Step-Loc fibre formula (`DESIGN_stepLoc.md` §1(iii)), in the
integrability-corrected form recorded in `FINDING_sbWordCube_fibreSplit.md` §5: the potential word
`qLHSword (N := k+m) a μ w w1 Φ = ∫_{abox (k+m) a} Φ² · qLHSden (k+m) a μ w w1` of a state
supported a.e. on the sub-sector where the first `k` slots lie in `A` and the last `m` avoid it
equals the integral, over the out-of-box configurations `Dloc m a A = (acube a \ A)^m`, of the
`k`-particle potential word of the in-box fibre `fibre k m Φ y`.

## Proof

Three steps, exactly the corpus's own `qLHSden1_expect_eq_slice` plus two a.e. reductions.

* **the density collapses to block 1** (`qLHSden_eq_qLHSden1_of_subsector`).  On the sub-sector the
  block-2 and cross-block rows of `qLHSden` vanish: the one-body kernel `w1Fibre` and the *first*
  argument of `w` vanish off `A`.  Hence a.e. `Φ² · qLHSden = Φ² · qLHSden1` on the box, and in
  particular the integrand of `hint` is a.e. the block-1 integrand.
* **the block-1 Fubini identity**: `qLHSden1_expect_eq_slice` (the corpus's proved
  `SmallBoxSuperadd` lemma), applied with the integrability just transported.
* **the outer domain localises to `Dloc`**: for a.e. `y` in `abox m a` with a slot in `A`, the fibre
  `fibre k m Φ y` vanishes a.e. (the sub-sector support of `Φ` forces every out-of-box coordinate
  of a non-zero configuration to avoid `A`), so its `qLHSword` is `0`; the two indicator integrands
  therefore agree a.e.

Nothing in the proof is analytic; every ingredient is an a.e. support statement plus the
pointwise vanishing of the two dropped rows of the pair density and the corpus's restricted
Fubini.
-/

/-- **The potential density on the sub-sector.**  Where the first `k` slots of `x` lie in `A` and
the last `m` avoid it, the `(k+m)`-particle potential density `qLHSden` collapses onto its block-1
part `qLHSden1`: the block-2 row (`-μ Σ w1Fibre` and the pairs of out-of-box slots) and the
cross-block row both vanish because the one-body kernel `w1Fibre` and the *first* argument of the
two-body kernel `w` vanish off `A`. -/
theorem qLHSden_eq_qLHSden1_of_subsector {k m : ℕ} {a μ : ℝ}
    {A : Set E3} {w w1 : E3 → E3 → ℝ}
    (hw : ∀ x y, x ∉ A → w x y = 0) (hw' : ∀ x y, y ∉ A → w x y = 0)
    (hw1 : ∀ x, x ∉ A → w1Fibre a w1 x = 0)
    {x : X (k + m)}
    (hx : (∀ i : Fin k, x (Fin.castAdd m i) ∈ A) ∧
          (∀ j : Fin m, x (Fin.natAdd k j) ∉ A)) :
    qLHSden (k + m) a μ w w1 x = qLHSden1 (N1 := k) (N2 := m) a μ w w1 x := by
  have hsp := qLHSden_split (N1 := k) (N2 := m) a μ w w1 x
  have h2 : qLHSden2 (N1 := k) (N2 := m) a μ w w1 x = 0 := by
    rw [qLHSden2]
    have hA : (∑ j : Fin m, w1Fibre a w1 (x (Fin.natAdd k j))) = 0 :=
      Finset.sum_eq_zero (fun j _ => hw1 _ (hx.2 j))
    have hB : (∑ p ∈ pairSet m, w (x (Fin.natAdd k p.1)) (x (Fin.natAdd k p.2))) = 0 :=
      Finset.sum_eq_zero (fun p _ => hw _ _ (hx.2 p.1))
    rw [hA, hB]
    ring
  have h3 : qLHSdenCross (N1 := k) (N2 := m) w x = 0 := by
    rw [qLHSdenCross]
    have hC : (∑ i₁ : Fin k, ∑ j₂ : Fin m, (w (x (Fin.castAdd m i₁)) (x (Fin.natAdd k j₂))
        + w (x (Fin.natAdd k j₂)) (x (Fin.castAdd m i₁)))) = 0 := by
      refine Finset.sum_eq_zero (fun i₁ _ => Finset.sum_eq_zero (fun j₂ _ => ?_))
      rw [hw' _ _ (hx.2 j₂), hw _ _ (hx.2 j₂)]
      ring
    rw [hC]
    ring
  linarith [hsp, h2, h3]

theorem qLHSword_fibreSplit_of_integrable {k m : ℕ} {a μ : ℝ} (ha : 0 < a) (hk : 0 < k)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    {w w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw : ∀ x y, x ∉ A → w x y = 0) (hw' : ∀ x y, y ∉ A → w x y = 0)
    (hw1 : ∀ x, x ∉ A → Submission.BoseGases.w1Fibre a w1 x = 0)
    {Φ : Submission.BoseGases.X (k + m) → ℝ} (hΦm : Measurable Φ)
    (hsupp : Work.BoseFixB1.Cube.Loc.SubsectorSupp k m a A Φ)
    (hint : MeasureTheory.IntegrableOn (fun x => (Φ x) ^ 2 *
        Submission.BoseGases.qLHSden (k + m) a μ w w1 x)
        (Submission.BoseGases.abox (k + m) a) MeasureTheory.volume) :
    Submission.BoseGases.qLHSword (N := k + m) a μ w w1 Φ
      = ∫ y in Work.BoseFixB1.Cube.Loc.Dloc m a A,
          Submission.BoseGases.qLHSword (N := k) a μ w w1 (Work.BoseFixB1.Cube.Loc.fibre k m Φ y) := by
  -- ### the density agrees a.e. with its block-1 part
  have hden : (fun x : X (k + m) => (Φ x) ^ 2 * qLHSden (k + m) a μ w w1 x)
      =ᵐ[(volume : Measure (X (k + m))).restrict (abox (k + m) a)]
      (fun x : X (k + m) => (Φ x) ^ 2 * qLHSden1 (N1 := k) (N2 := m) a μ w w1 x) := by
    filter_upwards [hsupp] with x hx
    by_cases h : Φ x = 0
    · rw [h]
      ring
    · rw [qLHSden_eq_qLHSden1_of_subsector hw hw' hw1 (hx h)]
  -- ### the block-1 integrability
  have hint1 : IntegrableOn (fun x : X (k + m) => (Φ x) ^ 2 *
      qLHSden1 (N1 := k) (N2 := m) a μ w w1 x) (abox (k + m) a) volume :=
    hint.congr hden
  -- ### the block-1 Fubini identity
  have hC := qLHSden1_expect_eq_slice (N1 := k) (N2 := m) (s := a) (μ := μ) w w1 Φ hint1
  -- ### the `k`-particle word of the fibre vanishes a.e. off `Dloc`
  have hzero : (fun y : X m => qLHSword (N := k) a μ w w1 (fibre k m Φ y))
      =ᵐ[(volume : Measure (X m)).restrict (abox m a \ Dloc m a A)] 0 := by
    have hmeasS : MeasurableSet (abox m a \ Dloc m a A) :=
      (abox_measurable m a).diff (measurableSet_Dloc m hA)
    have hslice : ∀ᵐ y ∂((volume : Measure (X m)).restrict (abox m a \ Dloc m a A)),
        ∀ᵐ z ∂((volume : Measure (X k)).restrict (abox k a)),
          Φ (mergeBlock k m (z, y)) ≠ 0 →
            (∀ i : Fin k, z i ∈ A) ∧ (∀ j : Fin m, y j ∉ A) :=
      Filter.Eventually.filter_mono
        (ae_mono (Measure.restrict_mono Set.sdiff_subset le_rfl))
        (subsectorSupp_slice_snd hsupp)
    filter_upwards [hslice, ae_restrict_mem hmeasS] with y hy hymem
    obtain ⟨j, hj⟩ := exists_mem_A_of_mem_abox_not_mem_Dloc hymem.1 hymem.2
    have hfib0 : ∀ᵐ z ∂((volume : Measure (X k)).restrict (abox k a)), fibre k m Φ y z = 0 := by
      refine hy.mono (fun z hz => ?_)
      by_contra hne
      exact (hz (by simpa [fibre, mkSlot_eq_mergeBlock] using hne)).2 j hj
    rw [qLHSword_eq_integral_qLHSden]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hfib0] with z hz
    show fibre k m Φ y z ^ 2 * qLHSden k a μ w w1 z = 0
    rw [hz]
    ring
  -- ### hence the two set integrals over `abox m a` and `Dloc m a A` agree
  have hD : (∫ y in abox m a, qLHSword (N := k) a μ w w1 (fibre k m Φ y))
      = ∫ y in Dloc m a A, qLHSword (N := k) a μ w w1 (fibre k m Φ y) := by
    have hmeasS : MeasurableSet (abox m a \ Dloc m a A) :=
      (abox_measurable m a).diff (measurableSet_Dloc m hA)
    have hae : (volume : Measure (X m))
        ({y : X m | qLHSword (N := k) a μ w w1 (fibre k m Φ y) ≠ 0}
          ∩ (abox m a \ Dloc m a A)) = 0 := by
      rw [← Measure.restrict_apply' hmeasS]
      exact ae_iff.mp hzero
    have hS : (volume : Measure (X m))
        {y : X m | (abox m a).indicator
              (fun y => qLHSword (N := k) a μ w w1 (fibre k m Φ y)) y
            ≠ (Dloc m a A).indicator
              (fun y => qLHSword (N := k) a μ w w1 (fibre k m Φ y)) y} = 0 := by
      refine measure_mono_null ?_ hae
      intro y hy
      by_cases hya : y ∈ abox m a
      · have h1 : (abox m a).indicator
            (fun y => qLHSword (N := k) a μ w w1 (fibre k m Φ y)) y
            = qLHSword (N := k) a μ w w1 (fibre k m Φ y) :=
          Set.indicator_of_mem hya _
        by_cases hyd : y ∈ Dloc m a A
        · exact absurd (by rw [h1, Set.indicator_of_mem hyd]) hy
        · refine ⟨?_, hya, hyd⟩
          intro hF
          exact hy (by rw [h1, Set.indicator_of_notMem hyd, hF])
      · have h1 : (abox m a).indicator
            (fun y => qLHSword (N := k) a μ w w1 (fibre k m Φ y)) y = 0 :=
          Set.indicator_of_notMem hya _
        have h2 : (Dloc m a A).indicator
            (fun y => qLHSword (N := k) a μ w w1 (fibre k m Φ y)) y = 0 :=
          Set.indicator_of_notMem (fun hd => hya (Dloc_subset_abox m a A hd)) _
        exact absurd (by rw [h1, h2]) hy
    rw [← MeasureTheory.integral_indicator (μ := (volume : Measure (X m)))
          (abox_measurable m a)
          (f := fun y => qLHSword (N := k) a μ w w1 (fibre k m Φ y)),
        ← MeasureTheory.integral_indicator (μ := (volume : Measure (X m)))
          (measurableSet_Dloc m hA)
          (f := fun y => qLHSword (N := k) a μ w w1 (fibre k m Φ y))]
    exact integral_congr_ae ((ae_iff (μ := (volume : Measure (X m)))).mpr hS)
  -- ### assembly
  have hA1 : qLHSword (N := k + m) a μ w w1 Φ
      = ∫ x in abox (k + m) a, (Φ x) ^ 2 * qLHSden1 (N1 := k) (N2 := m) a μ w w1 x := by
    rw [qLHSword_eq_integral_qLHSden]
    exact integral_congr_ae hden
  have hC' : (∫ x in abox (k + m) a, (Φ x) ^ 2 *
        qLHSden1 (N1 := k) (N2 := m) a μ w w1 x)
      = ∫ y in abox m a, qLHSword (N := k) a μ w w1 (fibre k m Φ y) := by
    rw [hC]
    refine integral_congr_ae ?_
    filter_upwards with y
    exact congrArg (fun ψ => qLHSword (N := k) a μ w w1 ψ) (fibre_eq_sbs_slice k m Φ y).symm
  exact hA1.trans (hC'.trans hD)

end Work.BoseFixB1.Cube.Loc
