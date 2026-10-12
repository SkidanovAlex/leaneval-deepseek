import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.a0A2QJointEdgeAtomFix
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.SectorAux.measEdgeAtomSharpGoodState` — the per-edge sharp hop atom, `GoodState`
form

The target (statement below, unchanged) is the `GoodState` version of the corpus's per-edge atom
(see `Submission/Work/BoseFixB1S/a0A2QJointEdgeAtomSharp.lean`,
`Work.BoseFixB1S.a0A2QJointEdgeAtomSharpFixed`): for the pair `p ∈ hopPairSet i` and the two joint
components

    F := boxCompT V A (p.1.erase i) (insert i p.2) Φ ,   G := boxCompT V A p.1 p.2 Φ ,

the scalar identity is the **pointwise perfect square** `Work.BoseFixB1S.atomA0A2Q`
(with `t := |p.1|`, `m := μV`, `X := (√(|p.1|+1) + √(μV))²`)

    2xy(t−1−m) ≥ −8Xx² − ((t−1−m)²/(8X))y²   (all reals x, y),

multiplied by the **nonnegative** weight `fib (x i) ≥ 0` and integrated over the box
(an `AM–GM`/completion of squares; no Cauchy–Schwarz is involved).  Dividing by two gives

    (t−1−m)·∫F·fib·G + 4X·∫F²·fib + ((t−1−m)²/(16X))·∫G²·fib ≥ 0 .

The only analytic input is integrability of the three products, which holds because `F` and `G`
are `GoodState`s (`Work.BoseFixB1S.goodState_boxCompT`, so measurable and bounded on `abox N ℓ`)
and `fib` is a.e. strongly measurable and bounded on the cube: those a.e. facts transfer to the
slot `i` over the box by `Submission.BoseGases.aem_comp_coord'` plus the coordinate membership
`Submission.BoseGases.mem_abox_iff`.  This is exactly the relaxation `Continuous Φ ↦ GoodState ℓ Φ`
needed by the sector assembly.
-/

namespace Work.BoseFixB1.SectorAux

open MeasureTheory
open scoped BigOperators

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-! ## 1. Bounded integrability on a finite measure space -/

/-- `x ↦ A x ^ 2 * φ x` is integrable on a finite measure space when `A` is measurable and
a.e. bounded and `φ` is a.e. strongly measurable and a.e. bounded. -/
private theorem integrable_sq_mul_fibre {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {A φ : α → ℝ} {CA Cφ : ℝ}
    (hAm : Measurable A) (hAb : ∀ᵐ x ∂μ, |A x| ≤ CA)
    (hφm : AEStronglyMeasurable φ μ) (hφb : ∀ᵐ x ∂μ, |φ x| ≤ Cφ) :
    Integrable (fun x => (A x) ^ 2 * φ x) μ := by
  refine Integrable.of_bound ((hAm.pow_const 2).aestronglyMeasurable.mul hφm)
    (max CA 0 ^ 2 * max Cφ 0) ?_
  filter_upwards [hAb, hφb] with x hA hφ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (A x))]
  have hA' : |A x| ≤ max CA 0 := le_trans hA (le_max_left _ _)
  have hφ' : |φ x| ≤ max Cφ 0 := le_trans hφ (le_max_left _ _)
  have hsq : (A x) ^ 2 ≤ (max CA 0) ^ 2 := by
    rw [abs_le] at hA'
    have hpos : 0 ≤ (max CA 0 - A x) * (max CA 0 + A x) :=
      mul_nonneg (by linarith [hA'.2]) (by linarith [hA'.1])
    nlinarith [hpos]
  exact mul_le_mul hsq hφ' (abs_nonneg _) (sq_nonneg _)

/-- `x ↦ F x * φ x * G x` is integrable on a finite measure space when `F, G` are measurable
and a.e. bounded and `φ` is a.e. strongly measurable and a.e. bounded. -/
private theorem integrable_mul_fibre {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {F G φ : α → ℝ} {CF CG Cφ : ℝ}
    (hFm : Measurable F) (hFb : ∀ᵐ x ∂μ, |F x| ≤ CF)
    (hGm : Measurable G) (hGb : ∀ᵐ x ∂μ, |G x| ≤ CG)
    (hφm : AEStronglyMeasurable φ μ) (hφb : ∀ᵐ x ∂μ, |φ x| ≤ Cφ) :
    Integrable (fun x => F x * φ x * G x) μ := by
  refine Integrable.of_bound ((hFm.aestronglyMeasurable.mul hφm).mul hGm.aestronglyMeasurable)
    (max CF 0 * max Cφ 0 * max CG 0) ?_
  filter_upwards [hFb, hφb, hGb] with x hF hφ hG
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  have hF' : |F x| ≤ max CF 0 := le_trans hF (le_max_left _ _)
  have hφ' : |φ x| ≤ max Cφ 0 := le_trans hφ (le_max_left _ _)
  have hG' : |G x| ≤ max CG 0 := le_trans hG (le_max_left _ _)
  exact mul_le_mul (mul_le_mul hF' hφ' (abs_nonneg _) (le_max_right _ _)) hG' (abs_nonneg _)
    (mul_nonneg (le_max_right _ _) (le_max_right _ _))

/-! ## 2. The integrated atom -/

/-- Integrating the pointwise perfect square `Work.BoseFixB1S.atomA0A2Q` against a nonnegative
weight `φ`: for `t, m ≥ 0` and integrable `F²φ`, `G²φ`, `FφG`,

    (t−1−m)·∫F·φ·G + 4X·∫F²·φ + ((t−1−m)²/(16X))·∫G²·φ ≥ 0 ,   X := (√(t+1)+√m)² . -/
private theorem integral_atom_engine {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F G φ : α → ℝ} {t m : ℝ} (ht : 0 ≤ t) (hm : 0 ≤ m) (hφnn : ∀ᵐ x ∂μ, 0 ≤ φ x)
    (hIntF2 : Integrable (fun x => (F x) ^ 2 * φ x) μ)
    (hIntG2 : Integrable (fun x => (G x) ^ 2 * φ x) μ)
    (hIntFG : Integrable (fun x => F x * φ x * G x) μ) :
    0 ≤ (t - 1 - m) * (∫ x, F x * φ x * G x ∂μ)
      + 4 * (Real.sqrt (t + 1) + Real.sqrt m) ^ 2 * (∫ x, (F x) ^ 2 * φ x ∂μ)
      + (((t - 1 - m) ^ 2 / (16 * (Real.sqrt (t + 1) + Real.sqrt m) ^ 2))
          * (∫ x, (G x) ^ 2 * φ x ∂μ)) := by
  set Z : ℝ := (Real.sqrt (t + 1) + Real.sqrt m) ^ 2 with hZdef
  have hZne : Z ≠ 0 := by
    rw [hZdef]
    exact ne_of_gt (Work.BoseFixB1S.sqrtSumSq_pos ht hm)
  have hpt : ∀ᵐ x ∂μ,
      -(4 * Z) * ((F x) ^ 2 * φ x) - (((t - 1 - m) ^ 2 / (16 * Z)) * ((G x) ^ 2 * φ x))
        ≤ (t - 1 - m) * (F x * φ x * G x) := by
    filter_upwards [hφnn] with x hx
    have h0 := Work.BoseFixB1S.atomA0A2Q (t := t) (m := m) (x := F x) (y := G x) ht hm
    rw [← hZdef] at h0
    have h1 := mul_le_mul_of_nonneg_left h0 hx
    have e1 : 2 * ((t - 1 - m) * (F x * φ x * G x))
        = φ x * (2 * F x * G x * (t - 1 - m)) := by ring
    have e2 : 2 * (-(4 * Z) * ((F x) ^ 2 * φ x)
          - (((t - 1 - m) ^ 2 / (16 * Z)) * ((G x) ^ 2 * φ x)))
        = φ x * (-(8 * Z) * (F x) ^ 2 - (((t - 1 - m) ^ 2 / (8 * Z)) * (G x) ^ 2)) := by
      field_simp
      ring
    rw [← e1, ← e2] at h1
    linarith [h1]
  have hIntR : Integrable (fun x =>
      -(4 * Z) * ((F x) ^ 2 * φ x) - (((t - 1 - m) ^ 2 / (16 * Z)) * ((G x) ^ 2 * φ x))) μ :=
    (hIntF2.const_mul _).sub (hIntG2.const_mul _)
  have hIntL : Integrable (fun x => (t - 1 - m) * (F x * φ x * G x)) μ := hIntFG.const_mul _
  have hmono := integral_mono_ae hIntR hIntL hpt
  have hsplit : (∫ x, (-(4 * Z) * ((F x) ^ 2 * φ x)
        - (((t - 1 - m) ^ 2 / (16 * Z)) * ((G x) ^ 2 * φ x))) ∂μ)
      = -(4 * Z) * (∫ x, (F x) ^ 2 * φ x ∂μ)
        - (((t - 1 - m) ^ 2 / (16 * Z)) * (∫ x, (G x) ^ 2 * φ x ∂μ)) := by
    rw [integral_sub (hIntF2.const_mul _) (hIntG2.const_mul _), integral_const_mul,
      integral_const_mul]
  have hlhs : (∫ x, (t - 1 - m) * (F x * φ x * G x) ∂μ)
      = (t - 1 - m) * (∫ x, F x * φ x * G x ∂μ) := integral_const_mul _ _
  rw [hsplit, hlhs] at hmono
  rw [hZdef] at hmono
  linarith [hmono]

/-! ## 3. The target -/

theorem measEdgeAtomSharpGoodState {N : ℕ} {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    (hμv : 1 ≤ μ * Work.SmallBoxSliding.boxMass ℓ d u)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : Work.SmallBoxSliding.boxMass ℓ d u = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hfibm : MeasureTheory.AEStronglyMeasurable fib
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    (hfibnn : ∀ z ∈ Submission.BoseGases.acube ℓ, 0 ≤ fib z)
    {Cf : ℝ} (hfibb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ Cf)
    {M1 : ℝ} (hM1 : M1 = ∫ z in A, fib z)
    (hM1nn : 0 ≤ M1)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦg : Work.BoseFixB1S.GoodState ℓ Φ)
    (i : Fin N) (p : Finset (Fin N) × Finset (Fin N)) (hp : p ∈ Work.BoseFixB1S.hopPairSet i) :
    0 ≤ (((p.1.card : ℝ) - 1 - μ * Work.SmallBoxSliding.boxMass ℓ d u) *
          (∫ x in Submission.BoseGases.abox N ℓ,
            Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u) A
                (p.1.erase i) (insert i p.2) Φ x
              * fib (x i)
              * Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u) A p.1 p.2 Φ x)
        + 4 * (Real.sqrt ((p.1.card : ℝ) + 1)
            + Real.sqrt (μ * Work.SmallBoxSliding.boxMass ℓ d u)) ^ 2 *
          (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u) A
                (p.1.erase i) (insert i p.2) Φ x) ^ 2 * fib (x i))
        + ((((p.1.card : ℝ) - 1 - μ * Work.SmallBoxSliding.boxMass ℓ d u) ^ 2
              / (16 * (Real.sqrt ((p.1.card : ℝ) + 1)
                  + Real.sqrt (μ * Work.SmallBoxSliding.boxMass ℓ d u)) ^ 2)) *
            (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u) A p.1 p.2 Φ x) ^ 2
                * fib (x i)))) := by
  -- ## abbreviations for the two joint components
  set F : Submission.BoseGases.X N → ℝ :=
    Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u) A
      (p.1.erase i) (insert i p.2) Φ with hFdef
  set G : Submission.BoseGases.X N → ℝ :=
    Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u) A p.1 p.2 Φ with hGdef
  -- ## the two components are `GoodState`s
  have hgsF : Work.BoseFixB1S.GoodState ℓ F := by
    rw [hFdef]
    exact Work.BoseFixB1S.goodState_boxCompT hℓ hvol hA hVeq hAc (p.1.erase i) (insert i p.2) hΦg
  obtain ⟨hFm, CF, hFb⟩ := hgsF
  have hgsG : Work.BoseFixB1S.GoodState ℓ G := by
    rw [hGdef]
    exact Work.BoseFixB1S.goodState_boxCompT hℓ hvol hA hVeq hAc p.1 p.2 hΦg
  obtain ⟨hGm, CG, hGb⟩ := hgsG
  -- ## the box carries a finite measure
  haveI hfin : IsFiniteMeasure
      ((MeasureTheory.volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.abox_lt_top N ℓ hℓ.le⟩
  -- ## the fibre facts on the slot `i`, over the box
  have hfibslot : AEStronglyMeasurable (fun x : Submission.BoseGases.X N => fib (x i))
      ((MeasureTheory.volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) :=
    Submission.BoseGases.aem_comp_coord' i hfibm
  have hFb' : ∀ᵐ x ∂((MeasureTheory.volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)), |F x| ≤ CF :=
    (MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)).mpr
      (Filter.Eventually.of_forall (fun x hx => hFb x hx))
  have hGb' : ∀ᵐ x ∂((MeasureTheory.volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)), |G x| ≤ CG :=
    (MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)).mpr
      (Filter.Eventually.of_forall (fun x hx => hGb x hx))
  have hfibslotb : ∀ᵐ x ∂((MeasureTheory.volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)), |fib (x i)| ≤ Cf :=
    (MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)).mpr
      (Filter.Eventually.of_forall (fun x hx =>
        hfibb (x i) ((Submission.BoseGases.mem_abox_iff N ℓ x).mp hx i)))
  have hfibslotnn : ∀ᵐ x ∂((MeasureTheory.volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)), 0 ≤ fib (x i) :=
    (MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)).mpr
      (Filter.Eventually.of_forall (fun x hx =>
        hfibnn (x i) ((Submission.BoseGases.mem_abox_iff N ℓ x).mp hx i)))
  -- ## integrability of the three products on the box
  have hIntF2 : Integrable (fun x : Submission.BoseGases.X N => (F x) ^ 2 * fib (x i))
      ((MeasureTheory.volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) :=
    integrable_sq_mul_fibre
      (μ := (MeasureTheory.volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ))
      (A := F) (φ := fun x : Submission.BoseGases.X N => fib (x i)) (CA := CF) (Cφ := Cf)
      hFm hFb' hfibslot hfibslotb
  have hIntG2 : Integrable (fun x : Submission.BoseGases.X N => (G x) ^ 2 * fib (x i))
      ((MeasureTheory.volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) :=
    integrable_sq_mul_fibre
      (μ := (MeasureTheory.volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ))
      (A := G) (φ := fun x : Submission.BoseGases.X N => fib (x i)) (CA := CG) (Cφ := Cf)
      hGm hGb' hfibslot hfibslotb
  have hIntFG : Integrable (fun x : Submission.BoseGases.X N => F x * fib (x i) * G x)
      ((MeasureTheory.volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) :=
    integrable_mul_fibre
      (μ := (MeasureTheory.volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ))
      (F := F) (G := G) (φ := fun x : Submission.BoseGases.X N => fib (x i))
      (CF := CF) (CG := CG) (Cφ := Cf) hFm hFb' hGm hGb' hfibslot hfibslotb
  -- ## the integrated atom
  have hm0 : (0 : ℝ) ≤ μ * Work.SmallBoxSliding.boxMass ℓ d u := le_trans zero_le_one hμv
  have hmain := integral_atom_engine
    (μ := (MeasureTheory.volume : Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N ℓ))
    (F := F) (G := G) (φ := fun x : Submission.BoseGases.X N => fib (x i))
    (t := (p.1.card : ℝ)) (m := μ * Work.SmallBoxSliding.boxMass ℓ d u)
    (Nat.cast_nonneg _) hm0 hfibslotnn hIntF2 hIntG2 hIntFG
  exact hmain

end Work.BoseFixB1.SectorAux
