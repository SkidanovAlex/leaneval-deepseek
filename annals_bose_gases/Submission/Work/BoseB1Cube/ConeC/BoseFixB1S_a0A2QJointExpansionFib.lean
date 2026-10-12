import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_boxCrossExpansionB1S
import Submission.Work.BoseFixB1S.Gen.exists_measurable_clip_ae_eq
import Submission.Work.BoseFixB1S.hopSlotOrth
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.a0A2QJointExpansionFib` — the *uncentred* hopping expansion

`Work.BoseFixB1S.boxCrossExpansionB1S` writes the crossing term of the sliding box as the hopping
edge sum with the **centred** fibre `fib(xᵢ) − κ`, `κ = M₁/V`.  The present lemma is the same
statement with the **uncentred** fibre `fib(xᵢ)` on the right-hand side — the form the payment
estimates use.

The two right-hand sums differ by `κ · Σᵢ Σ_{p∋i} (|p.1|−1−μV)·∫ ψ_{c_i(p)}·ψ_p`, and every
inner integral vanishes: the child `c_i(p) = (p.1.erase i, insert i p.2)` and its parent
`p = (p.1, p.2)` have different slot types in the slot `i` itself, so the components are
orthogonal by `orth_of_mem_S` (the `P`-slot case of `boxCompT_orth`).  This is exactly where the
uncentred statement is *easier* than the centred one: the correction pairs two components with a
**constant** weight, and is killed by the unweighted orthogonality of the corpus.

As a by-product the file proves the weighted orthogonality `hopCompTWeightedOrthAe` of the joint
components for a weight that is only *a.e. strongly measurable* and bounded on `acube ℓ` (all the
corpus supplies for `w1Fibre ℓ (wSmall1Pair …)`): transporting the a.e. equality along the slot
projection reduces it to the proved measurable version `Work.BoseFixB1S.hopSlotOrth`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. A.e. pullback of an a.e. equivalence along a slot -/

/-- If two one-slot weights agree a.e. on `acube ℓ`, then their slot-`i` readings agree a.e. on
the box (peel with `abox_peel_mp`, then project to the first factor). -/
private theorem ae_eq_slot {ℓ : ℝ} (_hℓ : 0 < ℓ) {fib g : E3 → ℝ}
    (h : ∀ᵐ z ∂(volume.restrict (Submission.BoseGases.acube ℓ)), fib z = g z)
    {N : ℕ} (i : Fin N) :
    ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox N ℓ)), fib (x i) = g (x i) := by
  cases N with
  | zero => exact absurd i.isLt (Nat.not_lt_zero _)
  | succ n =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E3) i
    have hmp : MeasurePreserving (⇑e)
        ((volume : Measure (Submission.BoseGases.X (n + 1))).restrict
          (Submission.BoseGases.abox (n + 1) ℓ))
        (((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
          ((volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ))) :=
      Submission.BoseGases.abox_peel_mp n ℓ i
    have hfst : Measure.QuasiMeasurePreserving Prod.fst
        (((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
          ((volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ)))
        ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
      Measure.quasiMeasurePreserving_fst
    have h2 := (hfst.comp hmp.quasiMeasurePreserving).ae h
    have hfe : ∀ x : Submission.BoseGases.X (n + 1), (e x).1 = x i := fun x => rfl
    filter_upwards [h2] with x hx
    simpa only [Function.comp_apply, hfe] using hx

/-! ## 2. Weighted orthogonality for an a.e.-strongly-measurable weight -/

/-- **Weighted orthogonality of the three-way joint components**, for a weight `g` that is only
a.e. strongly measurable (and bounded) on `acube ℓ`.  If the slot types of the two disjoint pairs
differ in a slot `j ≠ i`, then the pairing against the slot-`i` weight `g(xᵢ)` vanishes.

The bounded a.e.-strongly-measurable weight is replaced by the clipped measurable representative
of `Gen.exists_measurable_clip_ae_eq`, which agrees with `g` a.e. on `acube ℓ`; that equality
pulls back to the box along the slot projection (`ae_eq_slot`), and the measurable version is the
proved `Work.BoseFixB1S.hopSlotOrth`. -/
theorem hopCompTWeightedOrthAe {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hgm : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {Bg : ℝ} (hgb : ∀ z ∈ Submission.BoseGases.acube ℓ, |g z| ≤ Bg)
    {i j : Fin N} (hij : j ≠ i)
    {S T S' T' : Finset (Fin N)} (hST : Disjoint S T) (hST' : Disjoint S' T')
    (hdif : Work.BoseFixB1S.orthSlotType S T j ≠ Work.BoseFixB1S.orthSlotType S' T' j)
    {Φ Ψ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (hΨc : Continuous Ψ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A S T Φ x * g (x i)
          * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x) = 0 := by
  obtain ⟨f, hfm, hfbd, hgae⟩ :=
    Gen.exists_measurable_clip_ae_eq (ℓ := ℓ) (fib := g) (C := Bg) hgm hgb
  have haef : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      g (x i) = f (x i) := ae_eq_slot hℓ hgae i
  have hred : (∫ x in Submission.BoseGases.abox N ℓ,
      Work.BoseFixB1S.boxCompT volA A S T Φ x * f (x i)
        * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x) = 0 :=
    hopSlotOrth (g := f) hℓ hvol hA hvolA hAc hfm (Bg := max Bg 0)
      (fun z _ => hfbd z) hij hST hST' hdif hΦc hΨc
  have hge : (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.boxCompT volA A S T Φ x * g (x i)
          * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
      (fun x => Work.BoseFixB1S.boxCompT volA A S T Φ x * f (x i)
          * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x) := by
    filter_upwards [haef] with x hx
    rw [hx]
  rw [integral_congr_ae hge, hred]

/-! ## 3. The child component is orthogonal to its parent -/

/-- The joint component of the child `c_i(p) = (p.1.erase i, insert i p.2)` is orthogonal to the
component of the parent `p = (p.1, p.2)`: the slot `i` is a `Q`-slot of the child and a `P`-slot
of the parent, so `orth_of_mem_S` applies. -/
theorem hopChild_orth {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {i : Fin N} {p : Finset (Fin N) × Finset (Fin N)} (hp : p ∈ hopPairSet i) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x
          * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) = 0 := by
  have hpi : i ∈ p.1 := (mem_hopPairSet.mp hp).2
  have h1 : (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
          * Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x) = 0 :=
    orth_of_mem_S (S := p.1) (T := p.2) (S' := p.1.erase i) (T' := insert i p.2) (j := i)
      hℓ hvol hA hvolA hAc hpi (Finset.notMem_erase i p.1) hΦc hΦc
  have h2 : (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x
          * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
          * Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x := by
    refine MeasureTheory.setIntegral_congr_fun
      (Submission.BoseGases.abox_measurable N ℓ) (fun x _ => ?_)
    ring
  rw [h2, h1]

/-! ## 4. Replacing the centred fibre by the fibre in one edge term -/

/-- **The per-edge correction.**  For an edge `p ∈ hopPairSet i` and a slot-`i` weight `fib`, the
integrand with the centred weight `fib(xᵢ) − κ` has the same integral as the one with `fib(xᵢ)`:
the two differ by `κ·ψ_{c_i(p)}·ψ_p`, whose integral vanishes by `hopChild_orth`. -/
theorem integral_child_sub_kappa {N : ℕ} {ℓ volA κ : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hfibm : MeasureTheory.AEStronglyMeasurable fib
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {Cf : ℝ} (hfibb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ Cf)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {i : Fin N} {p : Finset (Fin N) × Finset (Fin N)} (hp : p ∈ hopPairSet i) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x
          * (fib (x i) - κ) * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x
          * fib (x i) * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x := by
  obtain ⟨hm1, C1, hb1⟩ :=
    goodState_boxCompT hℓ hvol hA hvolA hAc (p.1.erase i) (insert i p.2)
      (goodState_of_continuous hℓ hΦc)
  obtain ⟨hm2, C2, hb2⟩ :=
    goodState_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 (goodState_of_continuous hℓ hΦc)
  -- integrability of the two pieces
  have hI1 : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x
          * fib (x i) * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
    refine integrableOn_abox_of_bound_aesm (C := max C1 0 * max Cf 0 * max C2 0) hℓ ?_ ?_
    · exact ((hm1.aestronglyMeasurable.mul
        (Submission.BoseGases.aem_comp_coord' i hfibm)).mul hm2.aestronglyMeasurable)
    · intro x hx
      have hxi : x i ∈ Submission.BoseGases.acube ℓ :=
        (Submission.BoseGases.mem_abox_iff N ℓ x).mp hx i
      have h1 : |Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x|
          ≤ max C1 0 := le_trans (hb1 x hx) (le_max_left _ _)
      have h2 : |fib (x i)| ≤ max Cf 0 := le_trans (hfibb (x i) hxi) (le_max_left _ _)
      have h3 : |Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x| ≤ max C2 0 :=
        le_trans (hb2 x hx) (le_max_left _ _)
      have h10 : (0 : ℝ) ≤ max C1 0 := le_max_right _ _
      have h20 : (0 : ℝ) ≤ max Cf 0 := le_max_right _ _
      have h30 : (0 : ℝ) ≤ max C2 0 := le_max_right _ _
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) h10) h3 (abs_nonneg _)
        (mul_nonneg h10 h20)
  have hI2 : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        κ * (Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x
          * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    (integrableOn_mul_of_bound hℓ hm1 hm2 hb1 hb2).const_mul κ
  -- the two integrands differ pointwise by `κ·ψ_{c_i(p)}·ψ_p`
  have hpt : ∀ x : Submission.BoseGases.X N,
      Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x
          * (fib (x i) - κ) * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
        = (Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x
              * fib (x i) * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
            - κ * (Work.BoseFixB1S.boxCompT volA A (p.1.erase i) (insert i p.2) Φ x
              * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x)) := by
    intro x
    ring
  rw [MeasureTheory.setIntegral_congr_fun
    (Submission.BoseGases.abox_measurable N ℓ) (fun x _ => hpt x)]
  rw [MeasureTheory.integral_sub hI1 hI2, MeasureTheory.integral_const_mul,
    hopChild_orth hℓ hvol hA hvolA hAc hΦc hp, mul_zero, sub_zero]

/-! ## 5. The target -/

theorem a0A2QJointExpansionFib {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) :
    ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
      (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
      (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
      {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ),
      (Work.SmallBoxSliding.boxMass ℓ d u / 2) *
        (Work.BoseFixB1.boxCrossPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
          - 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x)
                * Submission.BoseGases.w1Fibre ℓ
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)
                * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) i Φ x)))
      = ∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
          (((p.1.card : ℝ) - 1 - μ * Work.SmallBoxSliding.boxMass ℓ d u)
            * ∫ x in Submission.BoseGases.abox N ℓ,
                Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) (p.1.erase i) (insert i p.2) Φ x
                  * Submission.BoseGases.w1Fibre ℓ
                      (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)
                  * Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
                      (Submission.BoseGases.dlBox ℓ d u) p.1 p.2 Φ x) := by
  intro ℓ d μ hℓ hd hR hRχ u hvol N Φ hΦc
  -- ## the regularity of the localised fibre
  obtain ⟨-, ⟨hFibAesm, Cf, hCfnn, hCfb⟩⟩ :=
    Work.BoseFixB1.q1Fib_aem_bound (v := v) (R0 := R0) hv_supp hR0 hv hvrad h (M := M) hM
      hℓ hd hR hRχ u
  have hFibAesm' : MeasureTheory.AEStronglyMeasurable
      (Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u))
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)) := by
    simpa only [Work.BoseFixB1.q1Fib1] using hFibAesm
  have hCfb' : ∀ z ∈ Submission.BoseGases.acube ℓ,
      |Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z| ≤ Cf :=
    fun z _ => by simpa only [Work.BoseFixB1.q1Fib1] using hCfb z
  -- ## box data
  have hAmeas : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hVeq : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ d u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  -- ## the weighted orthogonality at the centred fibre weight
  have horth : ∀ (i : Fin N) (S T S' T' : Finset (Fin N)), Disjoint S T → Disjoint S' T' →
      ∀ j : Fin N, j ≠ i →
        Work.BoseFixB1S.orthSlotType S T j ≠ Work.BoseFixB1S.orthSlotType S' T' j →
      (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) S T Φ x
          * (Submission.BoseGases.w1Fibre ℓ
                (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)
              - Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                  (Submission.BoseGases.wSmall1Pair h M ℓ d u)
                / Work.SmallBoxSliding.boxMass ℓ d u)
          * Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) S' T' Φ x) = 0 := by
    intro i S T S' T' hST hST' j hj hdif
    have hδaesm : MeasureTheory.AEStronglyMeasurable
        (fun z : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z
            - Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmall1Pair h M ℓ d u)
              / Work.SmallBoxSliding.boxMass ℓ d u)
        (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)) :=
      hFibAesm'.sub aestronglyMeasurable_const
    have hδb : ∀ z ∈ Submission.BoseGases.acube ℓ,
        |Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z
            - Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmall1Pair h M ℓ d u)
              / Work.SmallBoxSliding.boxMass ℓ d u|
          ≤ Cf + |Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            / Work.SmallBoxSliding.boxMass ℓ d u| :=
      fun z hz => le_trans (abs_sub _ _) (add_le_add (hCfb' z hz) le_rfl)
    exact hopCompTWeightedOrthAe (volA := Work.SmallBoxSliding.boxMass ℓ d u)
      (A := Submission.BoseGases.dlBox ℓ d u)
      (g := fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z
          - Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            / Work.SmallBoxSliding.boxMass ℓ d u)
      hℓ hvol hAmeas hVeq hAc hδaesm
      (Bg := Cf + |Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u)
        / Work.SmallBoxSliding.boxMass ℓ d u|) hδb hj hST hST' hdif hΦc hΦc
  -- ## the centred expansion of the corpus
  have hexp := boxCrossExpansionB1S (v := v) (R0 := R0) hv_supp hR0 hv hvrad hv1 h (M := M) hM
    (μ := μ) hℓ hd hR hRχ u hvol hΦc horth
  rw [hexp]
  -- ## the only difference is the centring, which vanishes edge by edge
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun p hp => ?_))
  rw [integral_child_sub_kappa (volA := Work.SmallBoxSliding.boxMass ℓ d u)
      (κ := Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u)
        / Work.SmallBoxSliding.boxMass ℓ d u)
      (A := Submission.BoseGases.dlBox ℓ d u)
      (fib := Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u))
      (Cf := Cf) hℓ hvol hAmeas hVeq hAc hFibAesm' hCfb' hΦc hp]

end Work.BoseFixB1S
