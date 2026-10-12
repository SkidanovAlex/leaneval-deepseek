import ChallengeDeps
import Submission.Work.BoseFixB1.boxCrossPart_sub_twoMuP_eq_operatorB1
import Submission.Work.BoseFixB1S.n0FunOp_affineB1_of_continuous
import Submission.Work.BoseFixB1S.qSideLossB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxCrossPartZsplitB1`

The sliding-box cross part `boxCrossPart` of the localised `g₀`-kernel `w₁ = wSmall1Pair h M ℓ d u`
splits, along the `μ`-line, into the **`n₀`-functional-calculus form** of FS's completion of
squares (`final_v2.tex`, `lm:appinteractionestimate`):

`boxCrossPart − 2μ·Σᵢ∫(QᵢΦ)·fib₁(xᵢ)·(PᵢΦ)
   = (2/V)·[ Σᵢ∫(QᵢΦ)·fib₁(xᵢ)·(g(n₀)PᵢΦ) − 2·Σᵢ∫(QᵢΦ)·fib₁(xᵢ)·(PᵢΦ) ]`,

with `V = |B(u)| = boxMass ℓ d u`, `g = (· + 1 − μV)`, `Pᵢ = boxPInd V A i`, `Qᵢ = boxQInd V A i`,
`A = dlBox ℓ d u`, `fib₁ = w1Fibre ℓ w₁`.

## Proof

The operator form of the same identity is *proved*
(`Work.BoseFixB1.boxCrossPart_sub_twoMuP_eq_operatorB1`):

`boxCrossPart − 2μ·Σᵢ∫(QᵢΦ)·fib₁(xᵢ)·(PᵢΦ)
   = (2/V)·Σᵢ∫(QᵢΦ)·fib₁(xᵢ)·[(ΣⱼPⱼPᵢΦ) − (1+μV)·(PᵢΦ)]`.

So it suffices to identify, slot by slot, the two bracket integrands.  The `n₀`-calculus identity
(`Work.BoseFixB1S.n0FunOp_affineB1_of_goodState`, `n0Op` being *defined* as `ΣⱼPⱼ`)

`g(n₀)Ψ = n₀Ψ + (1 − μV)Ψ = ΣⱼPⱼΨ + (1 − μV)Ψ`   a.e. on the box,

for `Ψ = PᵢΦ` (`GoodState`, since `Φ` is continuous hence bounded on the compact box), turns
`g(n₀)PᵢΦ − 2PᵢΦ` into `ΣⱼPⱼPᵢΦ − (1 + μV)PᵢΦ` pointwise a.e.; and both sides are integrable
against the fibre weight (every factor is measurable and bounded on the finite-measure box, the
fibre `fib₁` being a.e. strongly measurable and bounded on `acube ℓ`), so the Bochner integrals
agree.  `zsplit_slot` is this slot statement; summing it over `i` and multiplying by `2/V` gives
the claim.
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- **Integrability interface.**  A slot-fibre weight `fib(xᵢ)` (`fib` a.e. strongly measurable and
bounded on `acube ℓ`) times two states that are measurable and bounded on the box is integrable on
the (finite-measure) analysis box. -/
private theorem integrableOn_mul_fib_mul {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {fib : E3 → ℝ}
    (hfm : MeasureTheory.AEStronglyMeasurable fib
      ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict (Submission.BoseGases.acube ℓ)))
    {Cf : ℝ} (hfibb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ Cf)
    (i : Fin N) {F G : Submission.BoseGases.X N → ℝ} (hF : GoodState ℓ F)
    (hG : GoodState ℓ G) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => F x * fib (x i) * G x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
  obtain ⟨hFm, CF, hFb⟩ := hF
  obtain ⟨hGm, CG, hGb⟩ := hG
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N => F x * fib (x i) * G x)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) :=
    (hFm.aestronglyMeasurable.mul
      (Submission.BoseGases.aem_comp_coord' (ℓ := ℓ) i hfm)).mul hGm.aestronglyMeasurable
  refine MeasureTheory.IntegrableOn.of_bound
    (Submission.BoseGases.abox_lt_top N ℓ hℓ.le) haesm (max CF 0 * Cf * max CG 0) ?_
  rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
  refine Filter.Eventually.of_forall (fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  have hFx : |F x| ≤ max CF 0 := le_trans (hFb x hx) (le_max_left _ _)
  have hGx : |G x| ≤ max CG 0 := le_trans (hGb x hx) (le_max_left _ _)
  have hfibx : |fib (x i)| ≤ Cf := hfibb (x i) (hx i)
  have hCF0 : 0 ≤ max CF 0 := le_max_right _ _
  have hCG0 : 0 ≤ max CG 0 := le_max_right _ _
  have hCf0 : 0 ≤ Cf := le_trans (abs_nonneg _) hfibx
  calc |F x| * |fib (x i)| * |G x|
      ≤ (max CF 0 * Cf) * max CG 0 :=
        mul_le_mul (mul_le_mul hFx hfibx (abs_nonneg _) hCF0) hGx (abs_nonneg _)
          (mul_nonneg hCF0 hCf0)
    _ = max CF 0 * Cf * max CG 0 := by ring

/-- **The slot-level `n₀`-split.**  For a continuous state `Φ`, a box `A ⊆ acube ℓ` of volume `V`,
a fibre weight `fib` a.e. strongly measurable and bounded on `acube ℓ`, and a slot `i`:

`∫ (QᵢΦ)·fib(xᵢ)·(g(n₀)PᵢΦ) − 2∫ (QᵢΦ)·fib(xᵢ)·(PᵢΦ)
   = ∫ (QᵢΦ)·fib(xᵢ)·[(ΣⱼPⱼPᵢΦ) − (1+μV)(PᵢΦ)]`,  `g = (· + 1 − μV)`. -/
private theorem zsplit_slot {N : ℕ} {ℓ V μ : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume : MeasureTheory.Measure E3).real A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {fib : E3 → ℝ}
    (hfm : MeasureTheory.AEStronglyMeasurable fib
      ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict (Submission.BoseGases.acube ℓ)))
    {Cf : ℝ} (hfibb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ Cf)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (i : Fin N) :
    (∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
        * (n0FunOp V A (fun r : ℝ => r + 1 - μ * V)
            (Work.UBBInputs8.boxPInd V A i Φ)) x)
      - 2 * (∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x)
          * fib (x i) * (Work.UBBInputs8.boxPInd V A i Φ x))
      = ∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
          * ((∑ j : Fin N, Work.UBBInputs8.boxPInd V A j
                (Work.UBBInputs8.boxPInd V A i Φ) x)
              - (1 + μ * V) * (Work.UBBInputs8.boxPInd V A i Φ x)) := by
  classical
  set P : Submission.BoseGases.X N → ℝ := Work.UBBInputs8.boxPInd V A i Φ with hP
  set Q : Submission.BoseGases.X N → ℝ := Work.UBBInputs8.boxQInd V A i Φ with hQ
  have hVeq' : V = ((MeasureTheory.volume : MeasureTheory.Measure E3) A).toReal := by
    rw [hVeq, MeasureTheory.Measure.real_def]
  -- the states are measurable and bounded on the compact box
  have hΦG : GoodState ℓ Φ := by
    obtain ⟨C, _, hCb⟩ := exists_abox_bound hℓ hΦc
    exact ⟨hΦc.measurable, C, hCb⟩
  have hPG : GoodState ℓ P := by
    rw [hP]
    exact goodState_boxPInd hℓ hV hA hVeq' hAc i hΦG
  have hQG : GoodState ℓ Q := by
    rw [hQ]
    exact goodState_boxQInd hℓ hV hA hVeq' hAc i hΦG
  have hn0G : GoodState ℓ (n0FunOp V A (fun r : ℝ => r + 1 - μ * V) P) :=
    goodState_n0FunOpQSide hℓ hV hA hVeq hAc _ hPG
  -- the affine `n₀`-calculus identity
  have haff := n0FunOp_affineB1_of_goodState (N := N) hℓ hV hA hVeq' hAc (μ * V) hPG
  -- integrability of the two slot integrals
  have hIntA : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Q x * fib (x i)
      * (n0FunOp V A (fun r : ℝ => r + 1 - μ * V) P) x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    integrableOn_mul_fib_mul hℓ hfm hfibb i hQG hn0G
  have hIntB : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Q x * fib (x i) * P x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    integrableOn_mul_fib_mul hℓ hfm hfibb i hQG hPG
  -- split `∫A − 2∫B` into a single integral
  have h1 : (∫ x in Submission.BoseGases.abox N ℓ, Q x * fib (x i)
        * (n0FunOp V A (fun r : ℝ => r + 1 - μ * V) P) x)
      - 2 * (∫ x in Submission.BoseGases.abox N ℓ, Q x * fib (x i) * P x)
      = ∫ x in Submission.BoseGases.abox N ℓ, (Q x * fib (x i)
            * (n0FunOp V A (fun r : ℝ => r + 1 - μ * V) P) x
          - 2 * (Q x * fib (x i) * P x)) := by
    rw [MeasureTheory.integral_sub hIntA (hIntB.const_mul 2), MeasureTheory.integral_const_mul]
  -- rewrite the single integrand twice: pointwise algebra, then the a.e. identity
  have h2 : (∫ x in Submission.BoseGases.abox N ℓ, (Q x * fib (x i)
          * (n0FunOp V A (fun r : ℝ => r + 1 - μ * V) P) x
          - 2 * (Q x * fib (x i) * P x)))
      = ∫ x in Submission.BoseGases.abox N ℓ, Q x * fib (x i)
          * ((n0FunOp V A (fun r : ℝ => r + 1 - μ * V) P) x - 2 * P x) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
  have h3 : (∫ x in Submission.BoseGases.abox N ℓ, Q x * fib (x i)
          * ((n0FunOp V A (fun r : ℝ => r + 1 - μ * V) P) x - 2 * P x))
      = ∫ x in Submission.BoseGases.abox N ℓ, Q x * fib (x i)
          * ((n0Op V A P x + (1 - μ * V) * P x) - 2 * P x) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [haff] with x hx
    rw [hx]
  have h4 : (∫ x in Submission.BoseGases.abox N ℓ, Q x * fib (x i)
          * ((n0Op V A P x + (1 - μ * V) * P x) - 2 * P x))
      = ∫ x in Submission.BoseGases.abox N ℓ, Q x * fib (x i)
          * ((∑ j : Fin N, Work.UBBInputs8.boxPInd V A j P x) - (1 + μ * V) * P x) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by
      simp only [n0Op]
      ring))
  rw [h1, h2, h3, h4]

theorem boxCrossPartZsplitB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    Work.BoseFixB1.boxCrossPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
        (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
      - 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ x)
            * Submission.BoseGases.w1Fibre ℓ
                (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)
            * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) i Φ x))
      = (2 / Work.SmallBoxSliding.boxMass ℓ d u)
        * ((∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x)
                * Submission.BoseGases.w1Fibre ℓ
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)
                * (Work.BoseFixB1S.n0FunOp (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u)
                    (fun r : ℝ => r + 1 - μ * Work.SmallBoxSliding.boxMass ℓ d u)
                    (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                      (Submission.BoseGases.dlBox ℓ d u) i Φ)) x)
          - 2 * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x)
                * Submission.BoseGases.w1Fibre ℓ
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)
                * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) i Φ x))) := by
  classical
  set V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
  set A : Set E3 := Submission.BoseGases.dlBox ℓ d u with hAdef
  set W : E3 → E3 → ℝ := Submission.BoseGases.wSmall1Pair h M ℓ d u with hWdef
  set fib : E3 → ℝ := Submission.BoseGases.w1Fibre ℓ W with hfibdef
  have hVpos : 0 < V := by rw [hVdef]; exact hvol
  have hAmeas : MeasurableSet A := by
    rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := by
    rw [hAdef]; exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hVeq : V = (MeasureTheory.volume : MeasureTheory.Measure E3).real A := by
    rw [hVdef, hAdef]; exact Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u
  -- the localised fibre, unfolded
  have hfib_eq : fib = fun z : E3 => ∫ y in Submission.BoseGases.acube ℓ,
      Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y := by
    funext z
    rw [hfibdef, hWdef]
    rfl
  have hfm : MeasureTheory.AEStronglyMeasurable fib
      ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
        (Submission.BoseGases.acube ℓ)) := by
    rw [hfib_eq]
    exact Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre M u
      (Submission.BoseGases.g0_integrable hR0 hv_supp h).aemeasurable
  have hfibb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤
      Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M *
        (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          / Work.SmallBoxSliding.smallConvLower M * (8 * Real.pi * _root_.BoseGases.a v)) := by
    intro z _
    rw [hfib_eq]
    exact Work.BoseFixB1.wSmall1Pair_fibre_abs_le hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u z
  -- the operator form of the identity (already proved)
  have hcross : Work.BoseFixB1.boxCrossPart V ℓ A W Φ
      - 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
            * (Work.UBBInputs8.boxPInd V A i Φ x))
      = (2 / V) * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
            * ((∑ j : Fin N, Work.UBBInputs8.boxPInd V A j
                  (Work.UBBInputs8.boxPInd V A i Φ) x)
                - (1 + μ * V) * (Work.UBBInputs8.boxPInd V A i Φ x))) := by
    rw [hVdef, hAdef, hfibdef, hWdef]
    exact Work.BoseFixB1.boxCrossPart_sub_twoMuP_eq_operatorB1 (v := v) (R0 := R0) hv_supp hR0
      hv hvrad hv1 h (M := M) hM hℓ hd hR hRχ u hvol (Φ := Φ) hΦc
  -- the slot-wise `n₀`-split, summed
  have hsum : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
          * (n0FunOp V A (fun r : ℝ => r + 1 - μ * V)
              (Work.UBBInputs8.boxPInd V A i Φ)) x)
      - 2 * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
          * (Work.UBBInputs8.boxPInd V A i Φ x))
      = (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
          * ((∑ j : Fin N, Work.UBBInputs8.boxPInd V A j
                (Work.UBBInputs8.boxPInd V A i Φ) x)
              - (1 + μ * V) * (Work.UBBInputs8.boxPInd V A i Φ x))) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl
      (fun i _ => zsplit_slot hℓ hVpos hAmeas hVeq hAc hfm hfibb hΦc i)
  rw [hcross, ← hsum]

end Work.BoseFixB1S
