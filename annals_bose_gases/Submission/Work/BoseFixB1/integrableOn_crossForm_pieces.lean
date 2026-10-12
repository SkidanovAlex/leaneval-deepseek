import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.PairBlockCore
import Submission.Work.BoseFixB1.boxProjBoundsReal
import Submission.Work.BoseFixB1.integrableOn_slot_wSmallPair
import Submission.Work.SlotWord.measurable_boxQInd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

/-!
# `Work.BoseFixB1.integrableOn_crossForm_pieces`

The three pieces of the pointwise identity `Work.BoseFixB1.boxPairBlock_pointwise` — the
cross-form decomposition of the pair-block word — are `IntegrableOn` the analysis box
`abox N ℓ`:

* `(1_A(x_p)·(1_A(x_q)·Φ(x)))² · w(x_p, x_q)` with numerator `v`,
* `P_p(P_q Φ)² · w(x_p, x_q)` with numerator `g₂ = v(1−w₀)(1+w₀)`,
* `Q_q(Q_p Φ) · P_p(P_q Φ) · w₁(x_p, x_q)` with `w₁ = wSmallPair (g₀)`, `g₀ = v(1−w₀)`.

Each integrand factors as `S · wSmallPair M ℓ d u (numerator) (x_p) (x_q)` where

* the numerator (`v`, `g₂`, `g₀`) is integrable and supported in `‖z‖ ≤ R0` (the diluteness
  scale `R0 ≤ ℓd/16`), and
* the prefactor `S` is measurable and bounded on the compact box `abox N ℓ`: it is either a
  product of a *set indicator* (bounded by `1`) with `Φ` (`Φ` bounded on the compact box by
  compactness of `abox` and continuity of `Φ`), or a product of box projections/box
  fluctuations of `Φ`, which satisfy the `L^∞` bounds of `Work.BoseFixB1.boxProjBoundsReal`
  (`P` preserves the bound, `Q` at most doubles it, so `QQ` costs a factor `4`).

The slot kernel is then handled by the general lemma
`Work.BoseFixB1.integrableOn_slot_wSmallPair`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

theorem integrableOn_crossForm_pieces {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3))
    (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {p : Fin N × Fin N} (hp : p ∈ Submission.BoseGases.pairSet N) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        ((Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.1)
            * ((Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2
          * (Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
    ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.1
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x) ^ 2
          * (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) (x p.1) (x p.2)))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
    ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.2
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.1 Φ) x)
          * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.1
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x)
          * (Submission.BoseGases.wSmall1Pair h M ℓ d u (x p.1) (x p.2)))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
  classical
  -- the small box, its measurability, and its containment in the big box
  have hA : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  -- the pair index consists of distinct slots
  have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
  -- `Φ` is bounded on the compact analysis box
  obtain ⟨Bf, hBf⟩ := (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox N ℓ) (f := Φ) hΦc.continuousOn
  have hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ |Bf| := by
    intro x hx
    have hh := hBf x hx
    rw [Real.norm_eq_abs] at hh
    exact le_trans hh (le_abs_self Bf)
  have hΦm : Measurable Φ := hΦc.measurable
  -- the arithmetic volume is the (real) measure of the small box
  have hVeq : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real
          (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u
  -- promote a bound valid everywhere on the box to an a.e. bound on the box
  have ae_abox : ∀ {q : Submission.BoseGases.X N → Prop},
      (∀ x ∈ Submission.BoseGases.abox N ℓ, q x) →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)), q x :=
    fun hq => (MeasureTheory.ae_restrict_iff'
      (Submission.BoseGases.abox_measurable N ℓ)).mpr (Filter.Eventually.of_forall hq)
  -- the three numerators: integrable, supported in `‖z‖ ≤ R0`
  have hvZero : ∀ z : EuclideanSpace ℝ (Fin 3), R0 ≤ ‖z‖ → v z = 0 := by
    intro z hz
    refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
    have h1 : dist z (0 : EuclideanSpace ℝ (Fin 3)) < R0 := Metric.mem_ball.mp (hv_supp hmem)
    rw [dist_eq_norm, sub_zero] at h1
    exact absurd h1 (not_lt.mpr hz)
  have hvInt : MeasureTheory.Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
  have hg0Int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  have hg0Zero : ∀ z : EuclideanSpace ℝ (Fin 3), R0 ≤ ‖z‖ →
      Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  have hg2Int : MeasureTheory.Integrable (Submission.BoseGases.g2 v h) :=
    Submission.BoseGases.g2_integrable hR0 hv hvrad hv_supp h
  have hg2Zero : ∀ z : EuclideanSpace ℝ (Fin 3), R0 ≤ ‖z‖ →
      Submission.BoseGases.g2 v h z = 0 :=
    fun z hz => Submission.BoseGases.g2_zero_of_norm_ge hv_supp hz h
  -- the `L^∞` bounds of the box projections on the analysis box
  have hbd : ∀ i j : Fin N,
      (∀ x ∈ Submission.BoseGases.abox N ℓ,
          |Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x| ≤ |Bf|)
      ∧ (∀ x ∈ Submission.BoseGases.abox N ℓ,
          |Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x| ≤ 2 * |Bf|)
      ∧ (∀ x ∈ Submission.BoseGases.abox N ℓ,
          |Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) j Φ) x| ≤ |Bf|)
      ∧ (∀ x ∈ Submission.BoseGases.abox N ℓ,
          |Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) j Φ) x| ≤ 2 * |Bf|)
      ∧ (∀ x ∈ Submission.BoseGases.abox N ℓ,
          |Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) j Φ) x| ≤ 2 * |Bf|)
      ∧ (∀ x ∈ Submission.BoseGases.abox N ℓ,
          |Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) j Φ) x| ≤ 4 * |Bf|) := by
    intro i j
    simpa only [← hVeq] using boxProjBoundsReal (N := N) hℓ hA hAc hΦb i j
  -- the indicator of the small box, in the two slots
  have hind1m : Measurable (fun x : Submission.BoseGases.X N =>
      (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.1)) :=
    (measurable_const.indicator hA).comp (measurable_pi_apply p.1)
  have hind2m : Measurable (fun x : Submission.BoseGases.X N =>
      (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.2)) :=
    (measurable_const.indicator hA).comp (measurable_pi_apply p.2)
  have hind1_le : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |(Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.1)| ≤ 1 := by
    intro x _
    by_cases h1 : x p.1 ∈ Submission.BoseGases.dlBox ℓ d u <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1]
  have hind2_le : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |(Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.2)| ≤ 1 := by
    intro x _
    by_cases h2 : x p.2 ∈ Submission.BoseGases.dlBox ℓ d u <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h2]
  -- ## Piece 1: the square of the doubly-indicated state, against the `v`-kernel
  have hS1m : Measurable (fun x : Submission.BoseGases.X N =>
      ((Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.1)
        * ((Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2) :=
    (hind1m.mul (hind2m.mul hΦm)).pow_const 2
  have hS1b : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |((Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.1)
        * ((Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2|
        ≤ |Bf| ^ 2 := by
    intro x hx
    rw [abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    rw [abs_mul, abs_mul]
    calc |(Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.1)|
            * (|(Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.2)|
                * |Φ x|)
          ≤ 1 * (1 * |Bf|) :=
        mul_le_mul (hind1_le x hx)
          (mul_le_mul (hind2_le x hx) (hΦb x hx) (abs_nonneg _) zero_le_one)
          (by positivity) zero_le_one
      _ = |Bf| := by ring
  -- ## Piece 2: the square of the doubly-projected state, against the `g₂`-kernel
  have hP2m : Measurable (fun x : Submission.BoseGases.X N =>
      Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) p.1
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x) :=
    Work.BoseFixB1S.measurable_boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
      (Submission.BoseGases.dlBox ℓ d u) hA p.1
      (Work.BoseFixB1S.measurable_boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) hA p.2 hΦm)
  have hS2m : Measurable (fun x : Submission.BoseGases.X N =>
      (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) p.1
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x) ^ 2) := hP2m.pow_const 2
  have hS2b : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |(Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) p.1
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x) ^ 2| ≤ |Bf| ^ 2 := by
    intro x hx
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) ((hbd p.1 p.2).2.2.1 x hx) 2
  -- ## Piece 3: double fluctuation times double projection, against the `w₁`-kernel
  have hQ3m : Measurable (fun x : Submission.BoseGases.X N =>
      Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) p.2
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) p.1 Φ) x) :=
    Work.SlotWord.measurable_boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
      (Submission.BoseGases.dlBox ℓ d u) hA p.2
      (Work.SlotWord.measurable_boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) hA p.1 hΦm)
  have hS3m : Measurable (fun x : Submission.BoseGases.X N =>
      (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) p.2
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) p.1 Φ) x)
        * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) p.1
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x)) := hQ3m.mul hP2m
  have hS3b : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |(Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) p.2
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) p.1 Φ) x)
        * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) p.1
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x)| ≤ 4 * |Bf| * |Bf| := by
    intro x hx
    rw [abs_mul]
    calc |Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) p.2
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.1 Φ) x|
          * |Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.1
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x|
          ≤ (4 * |Bf|) * |Bf| :=
        mul_le_mul ((hbd p.2 p.1).2.2.2.2.2 x hx) ((hbd p.1 p.2).2.2.1 x hx)
          (abs_nonneg _) (by positivity)
      _ = 4 * |Bf| * |Bf| := by ring
  refine ⟨?_, ?_, ?_⟩
  · have hmain := integrableOn_slot_wSmallPair (N := N) (ℓ := ℓ) (d := d) (R := R0)
      hℓ hd hvInt hvZero hM hR hRχ u hpne
      (S := fun x : Submission.BoseGases.X N =>
        ((Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.1)
          * ((Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2)
      hS1m.aestronglyMeasurable (B := |Bf| ^ 2) (sq_nonneg _) (ae_abox hS1b)
    exact hmain
  · have hmain := integrableOn_slot_wSmallPair (N := N) (ℓ := ℓ) (d := d) (R := R0)
      hℓ hd hg2Int hg2Zero hM hR hRχ u hpne
      (S := fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) p.1
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x) ^ 2)
      hS2m.aestronglyMeasurable (B := |Bf| ^ 2) (sq_nonneg _) (ae_abox hS2b)
    exact hmain
  · have hmain := integrableOn_slot_wSmallPair (N := N) (ℓ := ℓ) (d := d) (R := R0)
      hℓ hd hg0Int hg0Zero hM hR hRχ u hpne
      (S := fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) p.2
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) p.1 Φ) x)
          * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.1
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x))
      hS3m.aestronglyMeasurable (B := 4 * |Bf| * |Bf|) (by positivity) (ae_abox hS3b)
    simpa only [Submission.BoseGases.wSmall1Pair] using hmain

end

end Work.BoseFixB1
