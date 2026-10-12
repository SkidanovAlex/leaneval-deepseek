import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB3.CS.Pieces.aP_abs_le_of_bound
import Submission.Work.BoseFixB3.CS.Pieces.aP_sq_le_of_bound
import Submission.Work.BoseFixB3.CS.Pieces.highSlot_aP_comm
import Submission.Work.BoseFixB3.CS.Pieces.peel_const_le
import Submission.Work.BoseFixB3.CS.highSlot_bound_of_pos
import Submission.Work.BoseFixB3.HighMass.measurable_highSlot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.Fmass_le_highMass_pos`

The `fMass`-bound of the `CS` chapter (the FS `eq:BQwQleq`-shape mass estimate for the
`Q̄_L`-part of the `3Q` word), in the `0 < κ` form in which it is used:

`Σ_{p∈pairSet} ∫_{abox}(Q̄_{L,p.2} P_{p.1} Q_{p.2}Φ)²·|w₁(x_{p.1},x_{p.2})|
  ≤ C·(ℓ³)⁻¹·N·highMass fc κ ℓ Φ`,

with `highMass fc κ ℓ Φ = Σ_i ∫_{abox}(Q̄_{L,i}Q_iΦ)²` the `Q̄_L`-mass of FS
`eq:QLs_giveNplusH` and `w₁ = wLoc ℓ (g₀ v h) 0`.

The constant is `C = chiSup²·2·(8π·a v)`, the coarse `|w₁|`-fibre bound.

## Route

* `highSlot_aP_comm` (`i ≠ j`, `κ > 0`): `Q̄_{L,j}P_i = P_iQ̄_{L,j}` on the box.
* Jensen for the box mean: `(P_i Ψ x)² ≤ P_i(Ψ²) x`, and `∫_{abox}P_iΨ = ∫_{abox}Ψ`.
* the one-slot peel: with `A` invariant in the slot `i` and `k` with
  `∫_{acube}k(·,b) ≤ C`, `∫_{abox}A·k(x_i,x_j) ≤ C(ℓ³)⁻¹∫_{abox}A`.
* the pair count: `Σ_{p∈pairSet}g(p.2) = (N−1)Σ_j g(j)`.

The `κ > 0` hypothesis is essential (for `κ ≤ 0` the statement is false; see
`Pieces/FINDING_Fmass_le_highMass_kappa_nonpos.md`).
-/

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators

namespace Work.BoseFixB3.CS.Pieces

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

/-! ## 1. The weight `wLoc ℓ h 0` is the pair kernel `wPair ℓ h` -/

/-- The corpus's localised kernel at `u = 0` is the pair kernel:
`wLoc ℓ h 0 = wPair ℓ h`. -/
lemma wLoc_zero_eq_wPair (ℓ : ℝ) (g : E3 → ℝ) (a b : E3) :
    Submission.BoseGases.wLoc ℓ g 0 a b = Submission.BoseGases.wPair ℓ g a b := by
  simp [Submission.BoseGases.wLoc, Submission.BoseGases.wPair, Submission.BoseGases.wScaled,
    Submission.BoseGases.chiU, Submission.BoseGases.chiScale]

/-! ## 2. Slot invariance of the box mean (no continuity needed) -/

/-- `aP ℓ i Ξ` does not depend on the value of the slot-`i` coordinate.  Only
`Function.update_idem` is used, so no regularity of `Ξ` is required. -/
lemma aP_update_eq_self {N : ℕ} {ℓ : ℝ} (i : Fin N) (Ξ : Submission.BoseGases.X N → ℝ)
    (x : Submission.BoseGases.X N) (z : E3) :
    Submission.BoseGases.aP ℓ i Ξ (Function.update x i z) = Submission.BoseGases.aP ℓ i Ξ x := by
  simp only [Submission.BoseGases.aP]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  rw [Function.update_idem]

/-- The square of a box mean is invariant in the slot of the mean. -/
lemma aP_sq_update_eq_self {N : ℕ} {ℓ : ℝ} (i : Fin N) (Ξ : Submission.BoseGases.X N → ℝ)
    (x : Submission.BoseGases.X N) (z : E3) :
    (Submission.BoseGases.aP ℓ i Ξ (Function.update x i z)) ^ 2
      = (Submission.BoseGases.aP ℓ i Ξ x) ^ 2 := by
  rw [aP_update_eq_self]

/-- `aP ℓ i Ξ` is a.e. strongly measurable on the box for a merely measurable `Ξ`
(the slot average of a measurable function of the two variables). -/
lemma aP_aestronglyMeasurable_of_measurable {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {Ξ : Submission.BoseGases.X N → ℝ} (hΞm : Measurable Ξ) :
    AEStronglyMeasurable (Submission.BoseGases.aP ℓ i Ξ)
      (volume.restrict (Submission.BoseGases.abox N ℓ)) := by
  have hupd : Continuous
      (fun p : Submission.BoseGases.X N × E3 => Function.update p.1 i p.2) := by fun_prop
  have hf : AEStronglyMeasurable
      (fun p : Submission.BoseGases.X N × E3 => Ξ (Function.update p.1 i p.2))
      ((volume : Measure (Submission.BoseGases.X N)).prod
        ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
    (hΞm.comp hupd.measurable).aestronglyMeasurable
  haveI : SigmaFinite ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
    inferInstance
  have hA : AEStronglyMeasurable (fun x : Submission.BoseGases.X N =>
      ∫ y : E3, Ξ (Function.update x i y)
        ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)))
      (volume : Measure (Submission.BoseGases.X N)) := hf.integral_prod_right'
  change AEStronglyMeasurable (fun x : Submission.BoseGases.X N =>
      (1 / ℓ ^ 3) * (∫ y : E3 in Submission.BoseGases.acube ℓ, Ξ (Function.update x i y)))
      (volume.restrict (Submission.BoseGases.abox N ℓ))
  exact (hA.const_mul (1 / ℓ ^ 3)).restrict

/-! ## 3. The `|w₁|`-fibre bound in the orientation used by the peel -/

/-- **Transposed `|w₁|`-fibre bound.**  For the chosen branch, the `acube`-fibre integral of
`|w₁| = |wPair(g₀)|` in its *first* variable is bounded by
`chiSup²·2·(8π·a v)` uniformly in the second variable.  (`wPair(g₀)` is symmetric by
`wPairC_g0_sym`, so this is `w1abs_fibre_acube_abs_le` with the orientation reversed.) -/
lemma wPair_g0_fibre_bound {v : E3 → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (h : ∃ w : E3 → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    ∀ b : E3, (∫ a in Submission.BoseGases.acube ℓ,
        |Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) a b|)
      ≤ Submission.BoseGases.chiSup ^ 2 * 2 * (8 * π * _root_.BoseGases.a v) := by
  intro b
  have hsym : (∫ a in Submission.BoseGases.acube ℓ,
        |Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) a b|)
      = ∫ a in Submission.BoseGases.acube ℓ,
          |Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) b a| := by
    apply integral_congr_ae
    filter_upwards with a
    have hw : Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) a b
        = Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) b a :=
      Submission.BoseGases.wPairC_g0_sym hvrad h ℓ a b
    rw [hw]
  rw [hsym]
  have h2 := Submission.BoseGases.w1abs_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ b
  have h3 : 0 ≤ ∫ a in Submission.BoseGases.acube ℓ,
      |Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) b a| :=
    integral_nonneg (fun a => abs_nonneg _)
  rw [abs_of_nonneg h3] at h2
  exact h2

/-! ## 4. The `highMass` summand -/

/-- `highMass` is the sum of its slot summands (definitional). -/
lemma highMass_eq_sum (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) {N : ℕ}
    (Φ : Submission.BoseGases.X N → ℝ) :
    Work.BoseFixB3.highMass fc κ ℓ Φ
      = ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB3.highSlot fc κ ℓ j (Submission.BoseGases.aQ ℓ j Φ) x) ^ 2 := rfl

theorem Fmass_le_highMass_pos {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) (R : ℝ) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hav : 0 < BoseGases.a v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (ℓ : ℝ) (hℓ : 0 < ℓ) (fc : Work.BoseBoxFix.LowCut) (κ : ℝ)
      (hκ : 0 < κ) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) {Φ : Submission.BoseGases.X N → ℝ}
      (hΦc : Continuous Φ),
      (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB3.highSlot fc κ ℓ p.2
            (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ)) x) ^ 2 *
          |Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x p.1) (x p.2)|)
      ≤ C * (ℓ ^ 3)⁻¹ * (N : ℝ) * Work.BoseFixB3.highMass fc κ ℓ Φ := by
  classical
  -- The constant: the coarse `|w₁|`-fibre bound.
  let C0 : ℝ := Submission.BoseGases.chiSup ^ 2 * 2 * (8 * π * BoseGases.a v)
  have hC0 : 0 ≤ C0 := by
    have hav0 : 0 ≤ BoseGases.a v := le_of_lt hav
    have hchi : (0 : ℝ) ≤ Submission.BoseGases.chiSup ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
    have h8pi : (0 : ℝ) ≤ 8 * π := by positivity
    exact mul_nonneg (mul_nonneg hchi h2) (mul_nonneg h8pi hav0)
  refine ⟨C0, hC0, ?_⟩
  intro N ℓ hℓ fc κ hκ hRℓ Φ hΦc
  -- the transposed `|w₁|`-fibre bound
  have hfib : ∀ b : E3, (∫ a in Submission.BoseGases.acube ℓ,
      |Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) a b|) ≤ C0 :=
    wPair_g0_fibre_bound hR hv hvrad hv_supp h hℓ hRℓ
  -- per-pair bound: commutation + peel + contraction
  have hstep : ∀ p ∈ Submission.BoseGases.pairSet N,
      (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB3.highSlot fc κ ℓ p.2
            (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ)) x) ^ 2 *
          |Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x p.1) (x p.2)|)
      ≤ C0 * (ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB3.highSlot fc κ ℓ p.2 (Submission.BoseGases.aQ ℓ p.2 Φ) x) ^ 2) := by
    intro p hp
    have hne : p.1 ≠ p.2 := by simpa [Submission.BoseGases.pairSet] using hp
    have hΨc : Continuous (Submission.BoseGases.aQ ℓ p.2 Φ) :=
      Submission.BoseGases.aQ_continuous hℓ p.2 hΦc
    let η : Submission.BoseGases.X N → ℝ :=
      Work.BoseFixB3.highSlot fc κ ℓ p.2 (Submission.BoseGases.aQ ℓ p.2 Φ)
    have hηm : Measurable η :=
      Work.BoseFixB3.HighMass.measurable_highSlot (fc := fc) (κ := κ) (ℓ := ℓ) p.2
        (Φ := Submission.BoseGases.aQ ℓ p.2 Φ) hΨc
    obtain ⟨B, hB0, hBb⟩ := Work.BoseFixB3.CS.highSlot_bound_of_pos (fc := fc) (κ := κ) (ℓ := ℓ)
      hκ hℓ p.2 (Ψ := Submission.BoseGases.aQ ℓ p.2 Φ) hΨc
    -- the bound and measurability of `A = (P_{p.1} η)²`
    have hAabs : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |(Submission.BoseGases.aP ℓ p.1 η x) ^ 2| ≤ B ^ 2 := by
      intro x hx
      have hP : |Submission.BoseGases.aP ℓ p.1 η x| ≤ B :=
        aP_abs_le_of_bound (N := N) (ℓ := ℓ) hℓ p.1 (Ξ := η) hB0 hηm hBb x hx
      calc |(Submission.BoseGases.aP ℓ p.1 η x) ^ 2|
          = |Submission.BoseGases.aP ℓ p.1 η x| ^ 2 := by rw [abs_pow]
        _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hP 2
    have hAae : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox N ℓ)),
        |(Submission.BoseGases.aP ℓ p.1 η x) ^ 2| ≤ B ^ 2 := by
      rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
      exact ae_of_all volume (fun x hx => hAabs x hx)
    have hAnorm : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox N ℓ)),
        ‖(Submission.BoseGases.aP ℓ p.1 η x) ^ 2‖ ≤ B ^ 2 := by
      filter_upwards [hAae] with x hx
      rwa [Real.norm_eq_abs]
    have hAmeas : AEStronglyMeasurable
        (fun x : Submission.BoseGases.X N => (Submission.BoseGases.aP ℓ p.1 η x) ^ 2)
        (volume.restrict (Submission.BoseGases.abox N ℓ)) :=
      (aP_aestronglyMeasurable_of_measurable (N := N) (ℓ := ℓ) hℓ p.1 hηm).pow 2
    have hAint : IntegrableOn
        (fun x : Submission.BoseGases.X N => (Submission.BoseGases.aP ℓ p.1 η x) ^ 2)
        (Submission.BoseGases.abox N ℓ) volume :=
      IntegrableOn.of_bound (s := Submission.BoseGases.abox N ℓ)
        (f := fun x : Submission.BoseGases.X N => (Submission.BoseGases.aP ℓ p.1 η x) ^ 2)
        (Submission.BoseGases.abox_compact N hℓ).measure_lt_top hAmeas
        (B ^ 2) hAnorm
    -- integrability of the weighted integrand
    have hkint : IntegrableOn
        (fun x : Submission.BoseGases.X N => (Submission.BoseGases.aP ℓ p.1 η x) ^ 2 *
          |Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) (x p.1) (x p.2)|)
        (Submission.BoseGases.abox N ℓ) volume := by
      have hg_int : Integrable (fun z : E3 => |Submission.BoseGases.g0 v h z|) :=
        (Submission.BoseGases.g0_integrable hR hv_supp h).abs
      have hg_supp : ∀ z : E3, R ≤ ‖z‖ → |Submission.BoseGases.g0 v h z| = 0 := by
        intro z hz
        rw [Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h, abs_zero]
      have hbase := Submission.BoseGases.integrableOn_bounded_mul_wPair_sub_abox
        (N := N) (ℓ := ℓ) (R := R) hℓ
        (g := fun x : Submission.BoseGases.X N => (Submission.BoseGases.aP ℓ p.1 η x) ^ 2)
        (h := fun z : E3 => |Submission.BoseGases.g0 v h z|) hg_int hg_supp hRℓ p.1 p.2 hne
        hAmeas (sq_nonneg B) hAae
      refine hbase.integrable.congr ?_
      filter_upwards with x
      show (Submission.BoseGases.aP ℓ p.1 η x) ^ 2 *
            Submission.BoseGases.wPair ℓ (fun z : E3 => |Submission.BoseGases.g0 v h z|)
              (x p.1) (x p.2)
          = (Submission.BoseGases.aP ℓ p.1 η x) ^ 2 *
              |Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) (x p.1) (x p.2)|
      rw [← Submission.BoseGases.wPair_abs_eq]
    -- the peel
    have hpeel := peel_const_le (N := N) (ℓ := ℓ) hℓ (i := p.1) (j := p.2) hne
      (A := fun x : Submission.BoseGases.X N => (Submission.BoseGases.aP ℓ p.1 η x) ^ 2)
      (fun x z => aP_sq_update_eq_self p.1 η x z)
      (fun x _ => sq_nonneg _) hAint
      (k := fun a b : E3 => |Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) a b|)
      (C := C0) hkint hfib
    -- the contraction of the box mean
    have hcontract := aP_sq_le_of_bound (N := N) (ℓ := ℓ) hℓ p.1 (Ξ := η) hB0 hηm hBb
    calc (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB3.highSlot fc κ ℓ p.2
              (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ)) x) ^ 2 *
            |Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x p.1) (x p.2)|)
        = ∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aP ℓ p.1 η x) ^ 2 *
            |Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) (x p.1) (x p.2)| := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          show Work.BoseFixB3.highSlot fc κ ℓ p.2
                (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ)) x ^ 2 *
              |Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x p.1) (x p.2)|
            = (Submission.BoseGases.aP ℓ p.1 η x) ^ 2 *
              |Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) (x p.1) (x p.2)|
          have hcomm := highSlot_aP_comm fc κ ℓ hκ hℓ hne hΨc x
          rw [show Work.BoseFixB3.highSlot fc κ ℓ p.2
                (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ)) x
              = Submission.BoseGases.aP ℓ p.1 η x from hcomm,
            wLoc_zero_eq_wPair]
      _ ≤ C0 * (ℓ ^ 3)⁻¹ *
            (∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aP ℓ p.1 η x) ^ 2) :=
          hpeel
      _ ≤ C0 * (ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox N ℓ, (η x) ^ 2) :=
          mul_le_mul_of_nonneg_left hcontract (mul_nonneg hC0 (by positivity))
      _ = C0 * (ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB3.highSlot fc κ ℓ p.2 (Submission.BoseGases.aQ ℓ p.2 Φ) x) ^ 2) := rfl
  -- sum over the ordered pairs and count
  calc (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB3.highSlot fc κ ℓ p.2
            (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ)) x) ^ 2 *
          |Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x p.1) (x p.2)|)
      ≤ ∑ p ∈ Submission.BoseGases.pairSet N, C0 * (ℓ ^ 3)⁻¹ *
          (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB3.highSlot fc κ ℓ p.2 (Submission.BoseGases.aQ ℓ p.2 Φ) x) ^ 2) :=
        Finset.sum_le_sum (fun p hp => hstep p hp)
    _ = C0 * (ℓ ^ 3)⁻¹ * (∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB3.highSlot fc κ ℓ p.2 (Submission.BoseGases.aQ ℓ p.2 Φ) x) ^ 2) := by
        rw [Finset.mul_sum]
    _ = C0 * (ℓ ^ 3)⁻¹ * (((N : ℝ) - 1) * Work.BoseFixB3.highMass fc κ ℓ Φ) := by
        have hcnt : (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.BoseFixB3.highSlot fc κ ℓ p.2 (Submission.BoseGases.aQ ℓ p.2 Φ) x) ^ 2)
            = ((N : ℝ) - 1) * Work.BoseFixB3.highMass fc κ ℓ Φ := by
          rw [highMass_eq_sum (fc := fc) (κ := κ) (ℓ := ℓ) (Φ := Φ)]
          exact Submission.BoseGases.sum_pairSet_second_eq N
            (fun j : Fin N => ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.BoseFixB3.highSlot fc κ ℓ j (Submission.BoseGases.aQ ℓ j Φ) x) ^ 2)
        rw [hcnt]
    _ ≤ C0 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * Work.BoseFixB3.highMass fc κ ℓ Φ) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0 (by positivity))
        have hM : 0 ≤ Work.BoseFixB3.highMass fc κ ℓ Φ := by
          rw [highMass_eq_sum (fc := fc) (κ := κ) (ℓ := ℓ) (Φ := Φ)]
          exact Finset.sum_nonneg (fun j _ => integral_nonneg (fun x => sq_nonneg _))
        have hle : ((N : ℝ) - 1) ≤ (N : ℝ) := by linarith
        exact mul_le_mul_of_nonneg_right hle hM
    _ = C0 * (ℓ ^ 3)⁻¹ * (N : ℝ) * Work.BoseFixB3.highMass fc κ ℓ Φ := by ring

end Work.BoseFixB3.CS.Pieces
