import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_hopQIndDecomp
import Submission.Work.BoseFixB1S.abox_integral_mul_finset_sum
import Submission.Work.BoseFixB1S.boxCrossCentredB1S
import Submission.Work.BoseFixB1S.boxCrossHoppingSharpLowAux
import Submission.Work.BoseFixB1S.hopBracketDecomp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.boxCrossExpansionB1S` — the cross part as the hopping edge sum

The sliding-box cross part of the localised `g₀`-kernel, with
`V = boxMass ℓ d u`, `A = dlBox ℓ d u`, `w₁ = wSmall1Pair h M ℓ d u`,
`fib = w1Fibre ℓ w₁`, `δ z = fib z − boxM1 ℓ A w₁ / V` (so `⦵_A δ = 0`), is

  `(V/2)·(boxCrossPart V ℓ A w₁ Φ − 2μ·Σᵢ∫ (QᵢΦ)·fib(xᵢ)·(PᵢΦ))
     = Σᵢ Σ_{p ∈ hopPairSet i} (|p.1| − 1 − μV)·∫_{abox} ψ_{c_i(p)}·δ(xᵢ)·ψ_p`

with `ψ_{S,T} = boxCompT V A S T Φ` and `c_i(p) = (p.1.erase i, insert i p.2)`.

The proof is the assembly of the corpus's `boxCrossPart_centred` (the fibre-centred identity,
copied cycle-free as `boxCrossPartCentredB1S`), `hopBracketDecomp` (the FS `eq:Q1n0` bracket),
`hopQIndDecomp` (`QᵢΦ` in the joint components), the linearity of the box integral over finite
sums (`abox_integral_mul_finset_sum`, `abox_integral_sum_mul`) and the collapse of the `Q`-sum
onto the child `hopCollapseGen` (whose only input is the weighted orthogonality `horth` of the
statement, supplied downstream by `Work.BoseFixB1S.hopOrthAeB1S`).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- The core of the expansion: everything except the source of the centred identity (which is
passed as `hcent`) and of the weighted orthogonality (passed as `horth`). -/
private theorem expansionCore {N : ℕ} {ℓ V μ : ℝ} {A : Set E3} {w₁ : E3 → E3 → ℝ}
    {Φ : Submission.BoseGases.X N → ℝ} {fib : E3 → ℝ} {Cf : ℝ}
    (hℓ : 0 < ℓ) (hVpos : 0 < V) (hAmeas : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hΦc : Continuous Φ)
    (hfibaesm : MeasureTheory.AEStronglyMeasurable fib
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    (hfibb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ Cf)
    (hcent : Work.BoseFixB1.boxCrossPart V ℓ A w₁ Φ
        - 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
              * (Work.UBBInputs8.boxPInd V A i Φ x))
      = (2 / V) * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x)
              * (fib (x i) - Work.BoseFixB1S.boxM1 ℓ A w₁ / V)
              * ((Work.UBBInputs8.boxPInd V A i (Work.BoseFixB1.rungF V A Φ) x)
                  - (1 + μ * V) * (Work.UBBInputs8.boxPInd V A i Φ x))))
    (horth : ∀ (i : Fin N) (S T S' T' : Finset (Fin N)), Disjoint S T → Disjoint S' T' →
      ∀ j : Fin N, j ≠ i → orthSlotType S T j ≠ orthSlotType S' T' j →
      (∫ x in Submission.BoseGases.abox N ℓ,
        boxCompT V A S T Φ x * (fib (x i) - Work.BoseFixB1S.boxM1 ℓ A w₁ / V)
          * boxCompT V A S' T' Φ x) = 0) :
    (V / 2) * (Work.BoseFixB1.boxCrossPart V ℓ A w₁ Φ
        - 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
              * (Work.UBBInputs8.boxPInd V A i Φ x)))
      = ∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
          (((p.1.card : ℝ) - 1 - μ * V)
            * ∫ x in Submission.BoseGases.abox N ℓ,
                boxCompT V A (p.1.erase i) (insert i p.2) Φ x
                  * (fib (x i) - Work.BoseFixB1S.boxM1 ℓ A w₁ / V)
                  * boxCompT V A p.1 p.2 Φ x) := by
  classical
  set δ : E3 → ℝ := fun z => fib z - Work.BoseFixB1S.boxM1 ℓ A w₁ / V with hδ
  -- ## box data and fibre bounds
  have hCube0 : (0 : E3) ∈ Submission.BoseGases.acube ℓ := by
    rw [Submission.BoseGases.mem_acube_iff]
    intro m
    change (0 : ℝ) ∈ Set.Icc (-ℓ / 2) (ℓ / 2)
    exact ⟨by linarith [hℓ], by linarith [hℓ]⟩
  have hCfn : 0 ≤ Cf := le_trans (abs_nonneg (fib 0)) (hfibb 0 hCube0)
  have hδb : ∀ (i : Fin N) (x : Submission.BoseGases.X N),
      x ∈ Submission.BoseGases.abox N ℓ →
      |δ (x i)| ≤ Cf + |Work.BoseFixB1S.boxM1 ℓ A w₁ / V| := by
    intro i x hx
    have hxi : x i ∈ Submission.BoseGases.acube ℓ := (mem_abox_iff N ℓ x).mp hx i
    calc |δ (x i)| = |fib (x i) - Work.BoseFixB1S.boxM1 ℓ A w₁ / V| := by simp only [hδ]
      _ ≤ |fib (x i)| + |Work.BoseFixB1S.boxM1 ℓ A w₁ / V| := abs_sub _ _
      _ ≤ Cf + |Work.BoseFixB1S.boxM1 ℓ A w₁ / V| :=
          add_le_add (hfibb (x i) hxi) (le_refl _)
  have hδAESM : ∀ i : Fin N, MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N => δ (x i))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) := by
    intro i
    have h1 : MeasureTheory.AEStronglyMeasurable (fun x : Submission.BoseGases.X N => fib (x i))
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ)) := Submission.BoseGases.aem_comp_coord' i hfibaesm
    have h2 := h1.sub (MeasureTheory.aestronglyMeasurable_const :
      MeasureTheory.AEStronglyMeasurable
        (fun _ : Submission.BoseGases.X N => Work.BoseFixB1S.boxM1 ℓ A w₁ / V) _)
    have h3 : (fun x : Submission.BoseGases.X N => δ (x i))
        = (fun x : Submission.BoseGases.X N => fib (x i))
          - (fun _ : Submission.BoseGases.X N => Work.BoseFixB1S.boxM1 ℓ A w₁ / V) := by
      funext x
      simp only [hδ, Pi.sub_apply]
    rw [h3]
    exact h2
  -- ## component bounds and measurability
  have hG : ∀ c : Finset (Fin N) × Finset (Fin N), GoodState ℓ (boxCompT V A c.1 c.2 Φ) :=
    fun c => goodState_boxCompT hℓ hVpos hAmeas hVeq hAc c.1 c.2
      (goodState_of_continuous hℓ hΦc)
  have hGb : ∀ c : Finset (Fin N) × Finset (Fin N), ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Submission.BoseGases.abox N ℓ, |boxCompT V A c.1 c.2 Φ x| ≤ C := by
    intro c
    obtain ⟨hm, C, hb⟩ := hG c
    exact ⟨max C 0, le_max_right _ _, fun x hx => le_trans (hb x hx) (le_max_left _ _)⟩
  set K : Finset (Fin N) × Finset (Fin N) → ℝ := fun c => Classical.choose (hGb c) with hK
  have hKnn : ∀ c : Finset (Fin N) × Finset (Fin N), 0 ≤ K c :=
    fun c => (Classical.choose_spec (hGb c)).1
  have hKb : ∀ (c : Finset (Fin N) × Finset (Fin N)) (x : Submission.BoseGases.X N),
      x ∈ Submission.BoseGases.abox N ℓ → |boxCompT V A c.1 c.2 Φ x| ≤ K c :=
    fun c x hx => (Classical.choose_spec (hGb c)).2 x hx
  have hKm : ∀ c : Finset (Fin N) × Finset (Fin N), Measurable (boxCompT V A c.1 c.2 Φ) :=
    fun c => (hG c).1
  -- ## the per-slot identity
  have hslot : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd V A i Φ x) * δ (x i)
            * ((Work.UBBInputs8.boxPInd V A i (Work.BoseFixB1.rungF V A Φ) x)
                - (1 + μ * V) * (Work.UBBInputs8.boxPInd V A i Φ x)))
        = ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
            (((p.1.card : ℝ) - 1 - μ * V)
              * ∫ x in Submission.BoseGases.abox N ℓ,
                  boxCompT V A (p.1.erase i) (insert i p.2) Φ x * δ (x i)
                    * boxCompT V A p.1 p.2 Φ x) := by
    intro i
    set Qs : Finset (Finset (Fin N) × Finset (Fin N)) :=
      (Work.BoseFixB1.disjPairs N).filter (fun q => i ∈ q.2) with hQs
    have hQ : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxQInd V A i Φ x = ∑ q ∈ Qs, boxCompT V A q.1 q.2 Φ x :=
      fun x hx => hopQIndDecomp hℓ hVpos hAmeas hVeq hAc hΦc i x hx
    have hβ : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxPInd V A i (Work.BoseFixB1.rungF V A Φ) x
            - (1 + μ * V) * (Work.UBBInputs8.boxPInd V A i Φ x)
          = ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
              ((p.1.card : ℝ) - 1 - μ * V) * boxCompT V A p.1 p.2 Φ x :=
      fun x hx => hopBracketDecomp hℓ hVpos hAmeas hVeq hAc hΦc i x hx
    -- measurability of the `Q`-sum
    have hQm : Measurable (fun x : Submission.BoseGases.X N =>
        ∑ q ∈ Qs, boxCompT V A q.1 q.2 Φ x) :=
      Finset.measurable_sum _ (fun q _ => hKm q)
    -- integrability of the `p`-summands
    have hB : ∀ p ∈ Work.BoseFixB1S.hopPairSet i, MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          ((∑ q ∈ Qs, boxCompT V A q.1 q.2 Φ x) * δ (x i)) * boxCompT V A p.1 p.2 Φ x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
      intro p hp
      refine integrableOn_abox_of_bound_aesm
        (C := (∑ q ∈ Qs, K q) * (Cf + |Work.BoseFixB1S.boxM1 ℓ A w₁ / V|) * K p) hℓ ?_ ?_
      · exact (hQm.aestronglyMeasurable.mul (hδAESM i)).mul (hKm p).aestronglyMeasurable
      · intro x hx
        have h1 : |∑ q ∈ Qs, boxCompT V A q.1 q.2 Φ x| ≤ ∑ q ∈ Qs, K q :=
          le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun q _ => hKb q x hx))
        have h2 : 0 ≤ ∑ q ∈ Qs, K q := Finset.sum_nonneg (fun q _ => hKnn q)
        have h3 : 0 ≤ Cf + |Work.BoseFixB1S.boxM1 ℓ A w₁ / V| :=
          add_nonneg hCfn (abs_nonneg _)
        calc |((∑ q ∈ Qs, boxCompT V A q.1 q.2 Φ x) * δ (x i)) * boxCompT V A p.1 p.2 Φ x|
            = |∑ q ∈ Qs, boxCompT V A q.1 q.2 Φ x| * |δ (x i)|
                * |boxCompT V A p.1 p.2 Φ x| := by rw [abs_mul, abs_mul]
          _ ≤ (∑ q ∈ Qs, K q) * (Cf + |Work.BoseFixB1S.boxM1 ℓ A w₁ / V|) * K p := by
              refine mul_le_mul (mul_le_mul h1 (hδb i x hx) (abs_nonneg _) h2)
                (hKb p x hx) (abs_nonneg _) (mul_nonneg h2 h3)
    -- the inner distribution, and the collapse
    have hInner1 : ∀ p ∈ Work.BoseFixB1S.hopPairSet i,
        (∫ x in Submission.BoseGases.abox N ℓ,
            ((∑ q ∈ Qs, boxCompT V A q.1 q.2 Φ x) * δ (x i))
              * boxCompT V A p.1 p.2 Φ x)
          = ∑ q ∈ Qs, ∫ x in Submission.BoseGases.abox N ℓ,
              boxCompT V A q.1 q.2 Φ x * δ (x i) * boxCompT V A p.1 p.2 Φ x := by
      intro p hp
      have hsum_eq : (∫ x in Submission.BoseGases.abox N ℓ,
            ((∑ q ∈ Qs, boxCompT V A q.1 q.2 Φ x) * δ (x i)) * boxCompT V A p.1 p.2 Φ x)
          = ∫ x in Submission.BoseGases.abox N ℓ,
              (∑ q ∈ Qs, boxCompT V A q.1 q.2 Φ x * δ (x i))
                * boxCompT V A p.1 p.2 Φ x := by
        refine MeasureTheory.setIntegral_congr_fun
          (Submission.BoseGases.abox_measurable N ℓ) (fun x _ => ?_)
        rw [Finset.sum_mul]
      rw [hsum_eq]
      refine abox_integral_sum_mul Qs
        (fun q x => boxCompT V A q.1 q.2 Φ x * δ (x i))
        (fun x => boxCompT V A p.1 p.2 Φ x) ?_
      intro q hq
      refine integrableOn_abox_of_bound_aesm
        (C := K q * (Cf + |Work.BoseFixB1S.boxM1 ℓ A w₁ / V|) * K p) hℓ ?_ ?_
      · exact ((hKm q).aestronglyMeasurable.mul (hδAESM i)).mul (hKm p).aestronglyMeasurable
      · intro x hx
        have h3 : 0 ≤ Cf + |Work.BoseFixB1S.boxM1 ℓ A w₁ / V| :=
          add_nonneg hCfn (abs_nonneg _)
        calc |(boxCompT V A q.1 q.2 Φ x * δ (x i)) * boxCompT V A p.1 p.2 Φ x|
            = |boxCompT V A q.1 q.2 Φ x| * |δ (x i)| * |boxCompT V A p.1 p.2 Φ x| := by
              rw [abs_mul, abs_mul]
          _ ≤ K q * (Cf + |Work.BoseFixB1S.boxM1 ℓ A w₁ / V|) * K p :=
              mul_le_mul (mul_le_mul (hKb q x hx) (hδb i x hx) (abs_nonneg _) (hKnn q))
                (hKb p x hx) (abs_nonneg _) (mul_nonneg (hKnn q) h3)
    have hInner2 : ∀ p ∈ Work.BoseFixB1S.hopPairSet i,
        (∑ q ∈ Qs, ∫ x in Submission.BoseGases.abox N ℓ,
            boxCompT V A q.1 q.2 Φ x * δ (x i) * boxCompT V A p.1 p.2 Φ x)
          = ∫ x in Submission.BoseGases.abox N ℓ,
              boxCompT V A (p.1.erase i) (insert i p.2) Φ x * δ (x i)
                * boxCompT V A p.1 p.2 Φ x := by
      intro p hp
      have hpd : p ∈ Work.BoseFixB1.disjPairs N := (mem_hopPairSet.mp hp).1
      have hpi : i ∈ p.1 := (mem_hopPairSet.mp hp).2
      exact hopCollapseGen (ℓ := ℓ) (volA := V) (A := A) (g := δ) (Φ := Φ) hpd hpi
        (fun S T S' T' hST hST' j hj hdif => horth i S T S' T' hST hST' j hj hdif)
    calc (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd V A i Φ x) * δ (x i)
            * ((Work.UBBInputs8.boxPInd V A i (Work.BoseFixB1.rungF V A Φ) x)
                - (1 + μ * V) * (Work.UBBInputs8.boxPInd V A i Φ x)))
        = ∫ x in Submission.BoseGases.abox N ℓ,
            (∑ q ∈ Qs, boxCompT V A q.1 q.2 Φ x) * δ (x i)
              * (∑ p ∈ Work.BoseFixB1S.hopPairSet i,
                  ((p.1.card : ℝ) - 1 - μ * V) * boxCompT V A p.1 p.2 Φ x) := by
          refine MeasureTheory.setIntegral_congr_fun
            (Submission.BoseGases.abox_measurable N ℓ) (fun x hx => ?_)
          rw [hQ x hx, hβ x hx]
      _ = ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
            ((p.1.card : ℝ) - 1 - μ * V)
              * ∫ x in Submission.BoseGases.abox N ℓ,
                  ((∑ q ∈ Qs, boxCompT V A q.1 q.2 Φ x) * δ (x i))
                    * boxCompT V A p.1 p.2 Φ x :=
          abox_integral_mul_finset_sum (Work.BoseFixB1S.hopPairSet i)
            (fun x => (∑ q ∈ Qs, boxCompT V A q.1 q.2 Φ x) * δ (x i))
            (fun p => (p.1.card : ℝ) - 1 - μ * V)
            (fun p x => boxCompT V A p.1 p.2 Φ x) hB
      _ = ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
            ((p.1.card : ℝ) - 1 - μ * V)
              * ∑ q ∈ Qs, ∫ x in Submission.BoseGases.abox N ℓ,
                  boxCompT V A q.1 q.2 Φ x * δ (x i) * boxCompT V A p.1 p.2 Φ x := by
          refine Finset.sum_congr rfl (fun p hp => ?_)
          rw [hInner1 p hp]
      _ = ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
            ((p.1.card : ℝ) - 1 - μ * V)
              * ∫ x in Submission.BoseGases.abox N ℓ,
                  boxCompT V A (p.1.erase i) (insert i p.2) Φ x * δ (x i)
                    * boxCompT V A p.1 p.2 Φ x := by
          refine Finset.sum_congr rfl (fun p hp => ?_)
          rw [hInner2 p hp]
  -- ## the assembly
  have hVne : V ≠ 0 := ne_of_gt hVpos
  calc (V / 2) * (Work.BoseFixB1.boxCrossPart V ℓ A w₁ Φ
        - 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
              * (Work.UBBInputs8.boxPInd V A i Φ x)))
      = ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd V A i Φ x) * δ (x i)
            * ((Work.UBBInputs8.boxPInd V A i (Work.BoseFixB1.rungF V A Φ) x)
                - (1 + μ * V) * (Work.UBBInputs8.boxPInd V A i Φ x)) := by
        rw [hcent]
        have harith : V / 2 * (2 / V) = 1 := by field_simp
        rw [← mul_assoc, harith, one_mul]
    _ = ∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
          (((p.1.card : ℝ) - 1 - μ * V)
            * ∫ x in Submission.BoseGases.abox N ℓ,
                boxCompT V A (p.1.erase i) (insert i p.2) Φ x * δ (x i)
                  * boxCompT V A p.1 p.2 Φ x) :=
        Finset.sum_congr rfl (fun i _ => hslot i)

/-! ## The public statement -/

theorem boxCrossExpansionB1S {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) :
    ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
      (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
      (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
      {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
      (horth : ∀ (i : Fin N) (S T S' T' : Finset (Fin N)), Disjoint S T → Disjoint S' T' →
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
                (Submission.BoseGases.dlBox ℓ d u) S' T' Φ x) = 0),
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
                  * (Submission.BoseGases.w1Fibre ℓ
                        (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)
                      - Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                          (Submission.BoseGases.wSmall1Pair h M ℓ d u)
                        / Work.SmallBoxSliding.boxMass ℓ d u)
                  * Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
                      (Submission.BoseGases.dlBox ℓ d u) p.1 p.2 Φ x) := by
  intro ℓ d μ hℓ hd hR hRχ u hvol N Φ hΦc horth
  -- the fibre facts for the localised `g₀`-fibre
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
  -- the centred identity of the corpus (cycle-free copy)
  have hcent := Work.BoseFixB1S.boxCrossPartCentredB1S (v := v) (R0 := R0) (μ := μ)
    hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u hvol hΦc
  -- box data
  have hAmeas : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hVeq : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ d u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  exact expansionCore (fib := Submission.BoseGases.w1Fibre ℓ
      (Submission.BoseGases.wSmall1Pair h M ℓ d u)) (Cf := Cf)
    hℓ hvol hAmeas hVeq hAc hΦc hFibAesm' hCfb' hcent horth

end Work.BoseFixB1S
