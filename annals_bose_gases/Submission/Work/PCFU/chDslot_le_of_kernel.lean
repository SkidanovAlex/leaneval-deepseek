import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBoxFock.PCFU.ChWordChains
import Submission.Work.PCFU.aP_aeStronglyMeasurable
import Submission.Work.PCFU.aP_lintegral_contraction
import Submission.Work.PCFU.aemeasurable_fibre_lintegral_cube
import Submission.Work.PCFU.chiLam_pairing_le
import Submission.Work.PCFU.fibre_mean_removal_le
import Submission.Work.PCFU.lowMult_eq_zero_of_not_integrable
import Submission.Work.PCFU.lowMult_lintegral_sq_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.PCFU.chDslot_le_of_kernel` — the state-side reduction of the `(D)`-slot

With `ℓ = ellH v μ`, `κ = chKappa v μ = (d²ℓ)⁻¹`, `χ_ℓ = chiLam ℓ` and the alias kernel
`F = KχfrU v h μ fu N − chDC h ℓ`, the `(D)`-slot pairs `χ_ℓ·F` against the low-momentum
"slot" `lowSlot fc κ ℓ j Ψ (x[j↦z])`.  This module proves that a **pointwise kernel bound**
`∀ z, ‖χ_ℓ(z)·F(z)‖ ≤ K` bounds the slot by `K·ℓ³·normB v μ n Φ`.

Route: pointwise in `x`, Cauchy–Schwarz in `z` (the kernel side is controlled by
`√(vol Λ) = √(ℓ³)` and the slot side by Plancherel, `|f| ≤ 1`); the fibre of
`Ψ = aQ_j aP_i Θ` is the mean-free part of the fibre of `aP_iΘ`, whose `L²`-mass is at most
that of the fibre of `V = aP_i|Θ|` (`|aP_iΘ| ≤ aP_i|Θ|`); and for the `x`-integral,
Cauchy–Schwarz against `‖Θ‖₂ = √normB`, the peel
`∫_{abox}∫_ΛF(x[j↦u]) = ℓ³∫_{abox}F` and the contraction `‖aP_i|Θ|‖₂ ≤ ‖Θ‖₂`.

The three geometric/measure-theoretic inputs of this file are delegated and PROVED in sibling
modules of `Submission/Work/PCFU/`:

* `Work.PCFU.abox_cube_peel` (`abox_cube_peel.lean`) — the peel of one coordinate;
* `Work.PCFU.lowMult_lintegral_sq_le`, `Work.PCFU.lowMult_eq_zero_of_not_integrable`,
  `Work.PCFU.fibre_mean_removal_le`, `Work.PCFU.chiLam_pairing_le` — the Plancherel,
  junk-case and mean-removal steps of the per-`x` bound;
* `Work.PCFU.aP_aeStronglyMeasurable`, `Work.PCFU.aemeasurable_fibre_lintegral_cube`,
  `Work.PCFU.aP_lintegral_contraction` — measurability and the `L²`-contraction of `aP`.
-/

noncomputable section

set_option maxHeartbeats 1600000

open MeasureTheory

namespace Work.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The low-momentum cut-off of the `(D)`-slot is positive**:
`chKappa v μ = ((paramsAt μ (a v)).d²·sideAt μ (a v))⁻¹`. -/
lemma chKappa_pos {v : E3 → ℝ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    0 < Work.BoseBoxFock.PCFU.chKappa v μ := by
  rw [Work.BoseBoxFock.PCFU.chKappa]
  have hu : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
  have hd : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).d := by
    rw [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_pos hu
  have hs : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  positivity

/-- `lowSlot` at an updated configuration is the low-momentum multiplier of the fibre. -/
lemma lowSlot_update_eq_lowMult {n : ℕ} (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) (j : Fin n)
    (Ψ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) (z : E3) :
    Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ (Function.update x j z)
      = Work.BoseBoxFix.lowMult fc κ ℓ (fun u => Ψ (Function.update x j u)) z := by
  simp only [Work.BoseBoxFix.lowSlot, Function.update_idem, Function.update_self]

/-- The slot-`j` mean of `aP ℓ i Θ` along the `j`-fibre is the cube mean of the fibre. -/
lemma aP_j_aP_i_update {n : ℕ} {ℓ : ℝ} (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ)
    (x : Submission.BoseGases.X n) (u : E3) :
    Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ) (Function.update x j u)
      = (1 / ℓ ^ 3) * ∫ v in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.aP ℓ i Θ (Function.update x j v) := by
  simp only [Submission.BoseGases.aP, Function.update_idem]

/-- The pointwise domination of the slot mean by the mean of the absolute value. -/
lemma abs_aP_le_aP_abs {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    (Θ : Submission.BoseGases.X n → ℝ) (y : Submission.BoseGases.X n) :
    |Submission.BoseGases.aP ℓ i Θ y|
      ≤ Submission.BoseGases.aP ℓ i (fun y => |Θ y|) y := by
  show |(1 / ℓ ^ 3) * ∫ z in Submission.BoseGases.acube ℓ, Θ (Function.update y i z)|
    ≤ (1 / ℓ ^ 3) * ∫ z in Submission.BoseGases.acube ℓ, |Θ (Function.update y i z)|
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / ℓ ^ 3)]
  exact mul_le_mul_of_nonneg_left
    (MeasureTheory.abs_integral_le_integral_abs
      (μ := (volume : MeasureTheory.Measure E3).restrict (Submission.BoseGases.acube ℓ))
      (f := fun z : E3 => Θ (Function.update y i z))) (by positivity)

/-- **`lowMult` depends only on the a.e. class of its argument.** -/
lemma lowMult_congr_ae {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} {ψ ψ' : E3 → ℝ}
    (h : ψ =ᵐ[volume] ψ') (z : E3) :
    Work.BoseBoxFix.lowMult fc κ ℓ ψ z = Work.BoseBoxFix.lowMult fc κ ℓ ψ' z := by
  have hk : ∀ p : E3, Submission.BoseGases.kinFT
      (fun y : E3 => (((Submission.BoseGases.acube ℓ).indicator ψ y : ℝ) : ℂ)) p
      = Submission.BoseGases.kinFT
        (fun y : E3 => (((Submission.BoseGases.acube ℓ).indicator ψ' y : ℝ) : ℂ)) p := by
    intro p
    rw [Submission.BoseGases.kinFT, Submission.BoseGases.kinFT]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [h] with y hy
    have hind : ((Submission.BoseGases.acube ℓ).indicator ψ y)
        = ((Submission.BoseGases.acube ℓ).indicator ψ' y) := by
      by_cases hy' : y ∈ Submission.BoseGases.acube ℓ
      · rw [Set.indicator_of_mem hy', Set.indicator_of_mem hy', hy]
      · rw [Set.indicator_of_notMem hy', Set.indicator_of_notMem hy']
    rw [hind]
  simp only [Work.BoseBoxFix.lowMult]
  rw [funext hk]

/-- **`lowMult` depends on its argument only through the cube-restricted a.e. class.** -/
lemma lowMult_congr_ae_indicator {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} {ψ ψ' : E3 → ℝ}
    (h : ∀ᵐ u ∂volume, (Submission.BoseGases.acube ℓ).indicator ψ u
      = (Submission.BoseGases.acube ℓ).indicator ψ' u) (z : E3) :
    Work.BoseBoxFix.lowMult fc κ ℓ ψ z = Work.BoseBoxFix.lowMult fc κ ℓ ψ' z := by
  have hk : ∀ p : E3, Submission.BoseGases.kinFT
      (fun y : E3 => (((Submission.BoseGases.acube ℓ).indicator ψ y : ℝ) : ℂ)) p
      = Submission.BoseGases.kinFT
        (fun y : E3 => (((Submission.BoseGases.acube ℓ).indicator ψ' y : ℝ) : ℂ)) p := by
    intro p
    rw [Submission.BoseGases.kinFT, Submission.BoseGases.kinFT]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [h] with y hy
    have hy' : (((Submission.BoseGases.acube ℓ).indicator ψ y : ℝ) : ℂ)
        = (((Submission.BoseGases.acube ℓ).indicator ψ' y : ℝ) : ℂ) :=
      congrArg (fun r : ℝ => (r : ℂ)) hy
    rw [hy']
  simp only [Work.BoseBoxFix.lowMult]
  rw [funext hk]

/-- **Strong measurability of the low-momentum multiplier** for a profile that is
a.e.-measurable after restriction to the cube. -/
lemma aestronglyMeasurable_lowMult_of_aemeasurable {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ}
    {ψ : E3 → ℝ}
    (hψ : AEMeasurable (fun u : E3 => (Submission.BoseGases.acube ℓ).indicator ψ u) volume) :
    MeasureTheory.AEStronglyMeasurable (fun z => Work.BoseBoxFix.lowMult fc κ ℓ ψ z)
      volume := by
  classical
  obtain ⟨g, hgm, hgeq⟩ := hψ
  have h1 : MeasureTheory.AEStronglyMeasurable (fun z => Work.BoseBoxFix.lowMult fc κ ℓ g z)
      volume := (Work.BoseFixB3.Conv.stronglyMeasurable_lowMult hgm).aestronglyMeasurable
  refine h1.congr ?_
  filter_upwards with z
  refine lowMult_congr_ae_indicator (fc := fc) (κ := κ) (ℓ := ℓ) (ψ := g) (ψ' := ψ) ?_ z
  filter_upwards [hgeq] with u hu
  by_cases hu' : u ∈ Submission.BoseGases.acube ℓ
  · rw [Set.indicator_of_mem hu', Set.indicator_of_mem hu']
    rw [show ψ u = g u from by rw [← hu, Set.indicator_of_mem hu']]
  · rw [Set.indicator_of_notMem hu', Set.indicator_of_notMem hu']

/-- **Extending an a.e.-measurable-on-`s` function by `0` off `s`.** -/
lemma aemeasurable_indicator_of_restrict {n : ℕ} {s : Set (Submission.BoseGases.X n)}
    (hsm : MeasurableSet s) {f : Submission.BoseGases.X n → ℝ}
    (hf : AEMeasurable f ((volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict s)) :
    AEMeasurable (s.indicator f) (volume : MeasureTheory.Measure (Submission.BoseGases.X n)) := by
  classical
  obtain ⟨g, hgm, hgeq⟩ := hf
  have hge : ∀ᵐ x ∂(volume : MeasureTheory.Measure (Submission.BoseGases.X n)),
      x ∈ s → f x = g x := (MeasureTheory.ae_restrict_iff' hsm).mp hgeq
  refine ⟨s.indicator g, hgm.indicator hsm, ?_⟩
  show ∀ᵐ x ∂(volume : MeasureTheory.Measure (Submission.BoseGases.X n)),
    s.indicator f x = s.indicator g x
  filter_upwards [hge] with x hx
  by_cases hxs : x ∈ s
  · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hxs]
    exact hx hxs
  · rw [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxs]

/-- **The square of the `enorm` of a real number seen in `ℂ`.** -/
lemma enorm_ofReal_sq (r : ℝ) :
    ‖((r : ℝ) : ℂ)‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (r ^ 2) := by
  have h1 : ‖((r : ℝ) : ℂ)‖ₑ = ENNReal.ofReal |r| := by
    rw [← ofReal_norm (x := ((r : ℝ) : ℂ))]
    congr 1
    exact RCLike.norm_ofReal r
  have h2 : |r| ^ (2 : ℝ) = r ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [h1, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg r) (by norm_num : (0:ℝ) ≤ 2), h2]

/-- **The `enorm` of a real number seen in `ℂ` equals that of the real number.** -/
lemma enorm_ofReal_complex (r : ℝ) : ‖((r : ℝ) : ℂ)‖ₑ = ‖r‖ₑ := by
  have h : ‖((r : ℝ) : ℂ)‖ = |r| := RCLike.norm_ofReal r
  rw [← ofReal_norm (x := ((r : ℝ) : ℂ)), h, ← Real.enorm_eq_ofReal_abs]

/-- **The per-`x` bound of the `(D)`-slot.**  The pointwise kernel bound `|χ_ℓ·F| ≤ K`
bounds the `z`-pairing against the slot function of the mean-free slot fibre, by
`√(vol Λ) = √(ℓ³)` times the `L²`-mass of the fibre of the dominating function `aP ℓ i |Θ|`. -/
lemma chDslot_fibre_le {n : ℕ} (fc : Work.BoseBoxFix.LowCut) {κ ℓ K : ℝ} (hκ : 0 < κ)
    (hℓ : 0 < ℓ) (hK : 0 ≤ K) {Θ : Submission.BoseGases.X n → ℝ} {F : E3 → ℂ}
    (hKer : ∀ z : E3, ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) * F z‖ ≤ K)
    (i j : Fin n) (x : Submission.BoseGases.X n) :
    ‖(∫ z, (((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) * F z
        * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
              (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
              (Function.update x j z) : ℝ) : ℂ))‖ₑ
      ≤ ENNReal.ofReal (K * Real.sqrt (ℓ ^ 3))
        * (∫⁻ u in Submission.BoseGases.acube ℓ,
            ENNReal.ofReal ((Submission.BoseGases.aP ℓ i (fun y => |Θ y|)
              (Function.update x j u)) ^ 2)) ^ (1 / 2 : ℝ) := by
  classical
  set ψf : E3 → ℝ := fun u => Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
      (Function.update x j u) with hψf
  set fh : E3 → ℝ := fun u => Submission.BoseGases.aP ℓ i Θ (Function.update x j u) with hfh
  have hΓeq : ∀ z : E3, ((Work.BoseBoxFix.lowSlot fc κ ℓ j
        (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
        (Function.update x j z) : ℝ) : ℂ)
      = ((Work.BoseBoxFix.lowMult fc κ ℓ ψf z : ℝ) : ℂ) := by
    intro z
    rw [lowSlot_update_eq_lowMult]
  by_cases hInt : MeasureTheory.Integrable
      (fun u : E3 => (Submission.BoseGases.acube ℓ).indicator ψf u)
  · have hΓm : MeasureTheory.AEStronglyMeasurable
        (fun z : E3 => ((Work.BoseBoxFix.lowMult fc κ ℓ ψf z : ℝ) : ℂ)) volume :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable
        (aestronglyMeasurable_lowMult_of_aemeasurable (fc := fc) (κ := κ) (ℓ := ℓ)
          hInt.aestronglyMeasurable.aemeasurable)
    -- DELEGATED (PCFU/chiLam_pairing_le)
    have hpair : ‖(∫ z, (((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) * F z
          * ((Work.BoseBoxFix.lowMult fc κ ℓ ψf z : ℝ) : ℂ))‖ₑ
        ≤ ENNReal.ofReal (K * Real.sqrt (ℓ ^ 3))
          * (∫⁻ z, ‖((Work.BoseBoxFix.lowMult fc κ ℓ ψf z : ℝ) : ℂ)‖ₑ ^ (2 : ℝ))
              ^ (1 / 2 : ℝ) :=
      chiLam_pairing_le (ℓ := ℓ) (K := K) (F := F)
        (Γ := fun z : E3 => ((Work.BoseBoxFix.lowMult fc κ ℓ ψf z : ℝ) : ℂ))
        hℓ hK hKer hΓm
    -- DELEGATED (PCFU/lowMult_lintegral_sq_le)
    have hplan : (∫⁻ z, ENNReal.ofReal ((Work.BoseBoxFix.lowMult fc κ ℓ ψf z) ^ 2))
        ≤ ∫⁻ u, ENNReal.ofReal
            (((Submission.BoseGases.acube ℓ).indicator ψf u) ^ 2) :=
      lowMult_lintegral_sq_le hκ hℓ hInt
    -- DELEGATED (PCFU/fibre_mean_removal_le)
    have hmean : (∫⁻ u, ENNReal.ofReal
          (((Submission.BoseGases.acube ℓ).indicator ψf u) ^ 2))
        ≤ ∫⁻ u, ENNReal.ofReal
            (((Submission.BoseGases.acube ℓ).indicator fh u) ^ 2) := by
      have hfib : ∀ u : E3, ψf u
          = fh u - (1 / ℓ ^ 3) * ∫ v in Submission.BoseGases.acube ℓ, fh v := by
        intro u
        rw [hψf, hfh]
        simp only [Submission.BoseGases.aQ]
        rw [aP_j_aP_i_update]
      have hpt : ∀ u : E3, ((Submission.BoseGases.acube ℓ).indicator ψf u)
          = ((Submission.BoseGases.acube ℓ).indicator
              (fun u => fh u - (1 / ℓ ^ 3) * ∫ v in Submission.BoseGases.acube ℓ,
                fh v) u) := by
        intro u; rw [Set.indicator_apply, Set.indicator_apply, hfib u]
      rw [lintegral_congr (fun u => by rw [hpt u])]
      exact fibre_mean_removal_le (ℓ := ℓ) hℓ (ψ := fh)
    have hdom : (∫⁻ u, ENNReal.ofReal
          (((Submission.BoseGases.acube ℓ).indicator fh u) ^ 2))
        ≤ ∫⁻ u in Submission.BoseGases.acube ℓ,
            ENNReal.ofReal ((Submission.BoseGases.aP ℓ i (fun y => |Θ y|)
              (Function.update x j u)) ^ 2) := by
      have h1 : (∫⁻ u, ENNReal.ofReal
            (((Submission.BoseGases.acube ℓ).indicator fh u) ^ 2))
          = ∫⁻ u in Submission.BoseGases.acube ℓ, ENNReal.ofReal ((fh u) ^ 2) := by
        rw [← MeasureTheory.lintegral_indicator (Submission.BoseGases.acube_measurable ℓ)
          (fun u : E3 => ENNReal.ofReal ((fh u) ^ 2))]
        apply lintegral_congr
        intro u
        rw [Set.indicator_apply, Set.indicator_apply]
        by_cases hu : u ∈ Submission.BoseGases.acube ℓ
        · rw [if_pos hu, if_pos hu]
        · rw [if_neg hu, if_neg hu]; simp
      rw [h1]
      apply lintegral_mono
      intro u
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 : |fh u| ≤ Submission.BoseGases.aP ℓ i (fun y => |Θ y|)
          (Function.update x j u) := by
        rw [hfh]
        exact abs_aP_le_aP_abs hℓ i Θ (Function.update x j u)
      calc (fh u) ^ 2 = |fh u| ^ 2 := by rw [sq_abs]
        _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) h2 2
    calc ‖(∫ z, (((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) * F z
          * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                (Function.update x j z) : ℝ) : ℂ))‖ₑ
        = ‖(∫ z, (((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) * F z
            * ((Work.BoseBoxFix.lowMult fc κ ℓ ψf z : ℝ) : ℂ))‖ₑ := by
          congr 1
          refine MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall (fun z => ?_))
          simp only [hΓeq z]
      _ ≤ ENNReal.ofReal (K * Real.sqrt (ℓ ^ 3))
            * (∫⁻ z, ‖((Work.BoseBoxFix.lowMult fc κ ℓ ψf z : ℝ) : ℂ)‖ₑ ^ (2 : ℝ))
                ^ (1 / 2 : ℝ) := hpair
      _ = ENNReal.ofReal (K * Real.sqrt (ℓ ^ 3))
            * (∫⁻ z, ENNReal.ofReal ((Work.BoseBoxFix.lowMult fc κ ℓ ψf z) ^ 2))
                ^ (1 / 2 : ℝ) := by
          congr 1
          apply congrArg (fun t => t ^ (1 / 2 : ℝ))
          apply lintegral_congr
          intro z
          exact enorm_ofReal_sq (Work.BoseBoxFix.lowMult fc κ ℓ ψf z)
      _ ≤ ENNReal.ofReal (K * Real.sqrt (ℓ ^ 3))
            * (∫⁻ u, ENNReal.ofReal
                (((Submission.BoseGases.acube ℓ).indicator ψf u) ^ 2)) ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hplan (by norm_num)) zero_le
      _ ≤ ENNReal.ofReal (K * Real.sqrt (ℓ ^ 3))
            * (∫⁻ u, ENNReal.ofReal
                (((Submission.BoseGases.acube ℓ).indicator fh u) ^ 2)) ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hmean (by norm_num)) zero_le
      _ ≤ ENNReal.ofReal (K * Real.sqrt (ℓ ^ 3))
            * (∫⁻ u in Submission.BoseGases.acube ℓ,
                ENNReal.ofReal ((Submission.BoseGases.aP ℓ i (fun y => |Θ y|)
                  (Function.update x j u)) ^ 2)) ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hdom (by norm_num)) zero_le
  · have hzero : Work.BoseBoxFix.lowMult fc κ ℓ ψf = 0 :=
      lowMult_eq_zero_of_not_integrable hℓ hInt
    have hfun : (fun z : E3 => (((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) * F z
          * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                (Function.update x j z) : ℝ) : ℂ))
        = fun _ : E3 => 0 := by
      funext z
      rw [hΓeq z, hzero]; simp
    rw [hfun]
    simp

theorem chDslot_le_of_kernel {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} (hav : 0 < BoseGases.a v)
    {μ : ℝ} (hμ : 0 < μ) (fc fu : Work.BoseBoxFix.LowCut) (N : ℕ) {K : ℝ} (hK0 : 0 ≤ K)
    {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : MeasureTheory.IntegrableOn (fun x => (Φ x) ^ 2)
      (Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)))
    (hKer : ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖(((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) z : ℝ)) : ℂ)
        * (Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
            - Work.BoseBoxFock.PCFU.chDC h (Work.BoseBoxFock.ellH v μ) z)‖ ≤ K) :
    ‖Work.BoseBoxFock.PCFU.chDslot v h fc fu μ N i j
        (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ)‖
      ≤ K * (Work.BoseBoxFock.ellH v μ) ^ 3 * Work.BoseBoxFix.normB v μ n Φ := by
  classical
  have hsidepos : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have hκ : 0 < Work.BoseBoxFock.PCFU.chKappa v μ := chKappa_pos hμ hav
  set ℓ : ℝ := Work.BoseBoxFock.ellH v μ with hℓ
  have hℓpos : 0 < ℓ := Work.BoseBoxFock.ellH_pos v μ
  set Θ : Submission.BoseGases.X n → ℝ := Work.BoseBoxFock.boxRestrictR ℓ Φ with hΘ
  set V : Submission.BoseGases.X n → ℝ
      := Submission.BoseGases.aP ℓ i (fun x => |Θ x|) with hV
  set s : Set (Submission.BoseGases.X n) := Submission.BoseGases.abox n ℓ with hs
  have hsm : MeasurableSet s := by rw [hs]; exact Submission.BoseGases.abox_measurable n ℓ
  have hΦs : MeasureTheory.IntegrableOn (fun x => (Φ x) ^ 2) s := by
    rw [hs, hℓ]; exact hΦ
  have hKerg : ∀ z : E3, ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)
      * (Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
          - Work.BoseBoxFock.PCFU.chDC h ℓ z)‖ ≤ K := by
    intro z; rw [hℓ]; exact hKer z
  have hnormB : Work.BoseBoxFix.normB v μ n Φ
      = ∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ), (Φ x) ^ 2 := by
    rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB,
      show Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) from by
        rw [Work.BoseBoxFock.ellH, if_pos hsidepos]]
  have hΘabs : AEMeasurable (fun x : Submission.BoseGases.X n => |Θ x|)
      (volume : MeasureTheory.Measure (Submission.BoseGases.X n)) := by
    have hΦ2 : AEMeasurable (fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
        ((volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict s) :=
      hΦs.aestronglyMeasurable.aemeasurable
    have habs : AEMeasurable (fun x : Submission.BoseGases.X n => |Φ x|)
        ((volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict s) := by
      have h1 : AEMeasurable (fun x : Submission.BoseGases.X n => Real.sqrt ((Φ x) ^ 2))
          ((volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict s) :=
        Real.continuous_sqrt.measurable.comp_aemeasurable hΦ2
      refine h1.congr ?_
      filter_upwards with x
      rw [Real.sqrt_sq_eq_abs]
    have h2 := aemeasurable_indicator_of_restrict hsm habs
    refine h2.congr ?_
    filter_upwards with x
    by_cases hx : x ∈ s
    · have hx' : x ∈ Submission.BoseGases.abox n ℓ := by rwa [hs] at hx
      rw [Set.indicator_of_mem hx, hΘ, Work.BoseBoxFock.boxRestrictR,
        Set.indicator_of_mem hx', abs_mul, abs_one, mul_one]
    · have hx' : x ∉ Submission.BoseGases.abox n ℓ := by rwa [hs] at hx
      rw [Set.indicator_of_notMem hx, hΘ, Work.BoseBoxFock.boxRestrictR,
        Set.indicator_of_notMem hx', mul_zero, abs_zero]
  have hVae : AEMeasurable V (volume : MeasureTheory.Measure (Submission.BoseGases.X n)) := by
    rw [hV]
    exact (aP_aeStronglyMeasurable hℓpos i hΘabs).aemeasurable
  have hGae : AEMeasurable (fun x : Submission.BoseGases.X n =>
      (∫⁻ u in Submission.BoseGases.acube ℓ,
        ENNReal.ofReal ((V (Function.update x j u)) ^ 2)) ^ (1 / 2 : ℝ))
      (volume : MeasureTheory.Measure (Submission.BoseGases.X n)) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (aemeasurable_fibre_lintegral_cube j hVae)
  have hN0 : 0 ≤ ∫ x in s, (Φ x) ^ 2 := integral_nonneg (fun x => sq_nonneg _)
  have hbound : (∫⁻ x in s, ENNReal.ofReal ((Θ x) ^ 2))
      = ENNReal.ofReal (∫ x in s, (Φ x) ^ 2) := by
    have hint : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n => (Θ x) ^ 2)
        (volume.restrict s) := by
      refine hΦs.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hsm] with x hx
      rw [hΘ, Work.BoseBoxFock.boxRestrictR, Set.indicator_of_mem hx, mul_one]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))]
    congr 1
    exact MeasureTheory.setIntegral_congr_fun hsm (fun x hx => by
      rw [hΘ, Work.BoseBoxFock.boxRestrictR, Set.indicator_of_mem hx, mul_one])
  -- per-x bound
  have hperx : ∀ x : Submission.BoseGases.X n,
      ‖(∫ z, (((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)
          * (Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
              - Work.BoseBoxFock.PCFU.chDC h ℓ z)
          * ((Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ) ℓ j
                (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                (Function.update x j z) : ℝ) : ℂ))‖ₑ
        ≤ ENNReal.ofReal (K * Real.sqrt (ℓ ^ 3))
          * (∫⁻ u in Submission.BoseGases.acube ℓ,
              ENNReal.ofReal ((V (Function.update x j u)) ^ 2)) ^ (1 / 2 : ℝ) :=
    fun x => chDslot_fibre_le fc hκ hℓpos hK0 hKerg i j x
  have hsupp : ∀ x : Submission.BoseGases.X n, x ∉ s → ‖Θ x‖ₑ = 0 := by
    intro x hx
    rw [hs] at hx
    have h0 : Θ x = 0 := by
      rw [hΘ, Work.BoseBoxFock.boxRestrictR, Set.indicator_of_notMem hx, mul_zero]
    rw [h0]; simp
  have hkey : ‖Work.BoseBoxFock.PCFU.chDslot v h fc fu μ N i j Θ‖ₑ
      ≤ ENNReal.ofReal (K * ℓ ^ 3 * ∫ x in s, (Φ x) ^ 2) := by
    have hsplit : Work.BoseBoxFock.PCFU.chDslot v h fc fu μ N i j Θ
        = ∫ x, (Θ x : ℂ) * (∫ z, (((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)
            * (Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
                - Work.BoseBoxFock.PCFU.chDC h ℓ z)
            * ((Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ) ℓ j
                  (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                  (Function.update x j z) : ℝ) : ℂ)) := by
      rw [hΘ, hℓ]
      simp only [Work.BoseBoxFock.PCFU.chDslot, Work.BoseBoxFock.PCFU.chDC]
    have step1 : ‖Work.BoseBoxFock.PCFU.chDslot v h fc fu μ N i j Θ‖ₑ
        ≤ ∫⁻ x, ‖Θ x‖ₑ * ‖(∫ z, (((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)
            * (Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
                - Work.BoseBoxFock.PCFU.chDC h ℓ z)
            * ((Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ) ℓ j
                  (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                  (Function.update x j z) : ℝ) : ℂ))‖ₑ := by
      rw [hsplit]
      refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
      exact lintegral_mono (fun x => le_of_eq (by
        rw [enorm_mul, enorm_ofReal_complex]))
    have step2 : (∫⁻ x, ‖Θ x‖ₑ * ‖(∫ z, (((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)
            * (Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
                - Work.BoseBoxFock.PCFU.chDC h ℓ z)
            * ((Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ) ℓ j
                  (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                  (Function.update x j z) : ℝ) : ℂ))‖ₑ)
        ≤ ENNReal.ofReal (K * Real.sqrt (ℓ ^ 3))
          * ∫⁻ x, ‖Θ x‖ₑ * (∫⁻ u in Submission.BoseGases.acube ℓ,
              ENNReal.ofReal ((V (Function.update x j u)) ^ 2)) ^ (1 / 2 : ℝ) := by
      rw [← MeasureTheory.lintegral_const_mul' _ _
        (ENNReal.ofReal_ne_top)]
      apply lintegral_mono
      intro x
      calc ‖Θ x‖ₑ * ‖(∫ z, (((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)
              * (Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
                  - Work.BoseBoxFock.PCFU.chDC h ℓ z)
              * ((Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ) ℓ j
                    (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                    (Function.update x j z) : ℝ) : ℂ))‖ₑ
          ≤ ‖Θ x‖ₑ * (ENNReal.ofReal (K * Real.sqrt (ℓ ^ 3))
              * (∫⁻ u in Submission.BoseGases.acube ℓ,
                  ENNReal.ofReal ((V (Function.update x j u)) ^ 2)) ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left (hperx x) zero_le
        _ = ENNReal.ofReal (K * Real.sqrt (ℓ ^ 3)) * (‖Θ x‖ₑ
              * (∫⁻ u in Submission.BoseGases.acube ℓ,
                  ENNReal.ofReal ((V (Function.update x j u)) ^ 2)) ^ (1 / 2 : ℝ)) := by
            ring
    have hHolder : (∫⁻ x, ‖Θ x‖ₑ * (∫⁻ u in Submission.BoseGases.acube ℓ,
          ENNReal.ofReal ((V (Function.update x j u)) ^ 2)) ^ (1 / 2 : ℝ))
        ≤ (ENNReal.ofReal (∫ x in s, (Φ x) ^ 2)) ^ (1 / 2 : ℝ)
          * (ENNReal.ofReal (ℓ ^ 3 * ∫ x in s, (Φ x) ^ 2)) ^ (1 / 2 : ℝ) := by
      have hbox : (∫⁻ x, ‖Θ x‖ₑ * (∫⁻ u in Submission.BoseGases.acube ℓ,
            ENNReal.ofReal ((V (Function.update x j u)) ^ 2)) ^ (1 / 2 : ℝ))
          = ∫⁻ x in s, ‖Θ x‖ₑ * (∫⁻ u in Submission.BoseGases.acube ℓ,
            ENNReal.ofReal ((V (Function.update x j u)) ^ 2)) ^ (1 / 2 : ℝ) := by
        rw [← MeasureTheory.lintegral_indicator hsm (fun x => ‖Θ x‖ₑ
          * (∫⁻ u in Submission.BoseGases.acube ℓ,
              ENNReal.ofReal ((V (Function.update x j u)) ^ 2)) ^ (1 / 2 : ℝ))]
        apply lintegral_congr
        intro x
        by_cases hx : x ∈ s
        · rw [Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx, hsupp x hx]; simp
      rw [hbox]
      have hf : AEMeasurable (fun x : Submission.BoseGases.X n => ‖Θ x‖ₑ)
          (volume.restrict s) := by
        have h1 : AEMeasurable (fun x : Submission.BoseGases.X n => ENNReal.ofReal |Θ x|)
            (volume.restrict s) := hΘabs.restrict.ennreal_ofReal
        refine h1.congr ?_
        filter_upwards with x
        rw [Real.enorm_eq_ofReal_abs]
      have hg : AEMeasurable (fun x : Submission.BoseGases.X n =>
          (∫⁻ u in Submission.BoseGases.acube ℓ,
            ENNReal.ofReal ((V (Function.update x j u)) ^ 2)) ^ (1 / 2 : ℝ))
          (volume.restrict s) := hGae.restrict
      refine le_trans (ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict s)
        (show (2:ℝ).HolderConjugate 2 from ⟨by norm_num, by norm_num, by norm_num⟩)
        hf hg) ?_
      refine mul_le_mul ?_ ?_ zero_le zero_le
      · refine le_of_eq ?_
        have hpt : ∀ x : Submission.BoseGases.X n,
            ‖Θ x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal ((Θ x) ^ 2) := by
          intro x
          rw [Real.enorm_eq_ofReal_abs,
            ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)]
          congr 1
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
        rw [lintegral_congr (fun x => hpt x), hbound]
      · have hpt : ∀ x : Submission.BoseGases.X n,
            ((∫⁻ u in Submission.BoseGases.acube ℓ,
              ENNReal.ofReal ((V (Function.update x j u)) ^ 2)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ)
              = ∫⁻ u in Submission.BoseGases.acube ℓ,
                  ENNReal.ofReal ((V (Function.update x j u)) ^ 2) := by
          intro x
          rw [← ENNReal.rpow_mul]
          norm_num
        rw [lintegral_congr (fun x => hpt x)]
        have hFae : AEMeasurable (fun x : Submission.BoseGases.X n =>
            ENNReal.ofReal ((V x) ^ 2)) (volume.restrict s) :=
          (hVae.restrict.pow_const 2).ennreal_ofReal
        rw [show (∫⁻ x in s, ∫⁻ u in Submission.BoseGases.acube ℓ,
              ENNReal.ofReal ((V (Function.update x j u)) ^ 2))
            = ∫⁻ x in Submission.BoseGases.abox n ℓ, ∫⁻ u in Submission.BoseGases.acube ℓ,
                ENNReal.ofReal ((V (Function.update x j u)) ^ 2) from by rw [hs]]
        rw [abox_cube_peel hℓpos j (fun x => ENNReal.ofReal ((V x) ^ 2)) hFae]
        rw [← hs]
        have hcontr : (∫⁻ x in s, ENNReal.ofReal ((V x) ^ 2))
            ≤ ∫⁻ x in s, ENNReal.ofReal ((Θ x) ^ 2) := by
          rw [hs, hV]
          refine le_trans (aP_lintegral_contraction hℓpos i hΘabs) ?_
          apply lintegral_mono
          intro x
          show ENNReal.ofReal (|Θ x| ^ 2) ≤ ENNReal.ofReal ((Θ x) ^ 2)
          rw [sq_abs]
        have h1 : (∫⁻ x in s, ENNReal.ofReal ((V x) ^ 2))
            ≤ ENNReal.ofReal (∫ x in s, (Φ x) ^ 2) := le_trans hcontr (le_of_eq hbound)
        have h2 : ENNReal.ofReal (ℓ ^ 3) * ∫⁻ x in s, ENNReal.ofReal ((V x) ^ 2)
            ≤ ENNReal.ofReal (ℓ ^ 3 * ∫ x in s, (Φ x) ^ 2) := by
          calc ENNReal.ofReal (ℓ ^ 3) * ∫⁻ x in s, ENNReal.ofReal ((V x) ^ 2)
              ≤ ENNReal.ofReal (ℓ ^ 3) * ENNReal.ofReal (∫ x in s, (Φ x) ^ 2) :=
                mul_le_mul_of_nonneg_left h1 zero_le
            _ = ENNReal.ofReal (ℓ ^ 3 * ∫ x in s, (Φ x) ^ 2) := by
                rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ℓ ^ 3)]
        exact ENNReal.rpow_le_rpow h2 (by norm_num)
    calc ‖Work.BoseBoxFock.PCFU.chDslot v h fc fu μ N i j Θ‖ₑ
        ≤ ∫⁻ x, ‖Θ x‖ₑ * ‖(∫ z, (((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)
            * (Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
                - Work.BoseBoxFock.PCFU.chDC h ℓ z)
            * ((Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ) ℓ j
                  (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                  (Function.update x j z) : ℝ) : ℂ))‖ₑ := step1
      _ ≤ ENNReal.ofReal (K * Real.sqrt (ℓ ^ 3))
          * ∫⁻ x, ‖Θ x‖ₑ * (∫⁻ u in Submission.BoseGases.acube ℓ,
              ENNReal.ofReal ((V (Function.update x j u)) ^ 2)) ^ (1 / 2 : ℝ) := step2
      _ ≤ ENNReal.ofReal (K * Real.sqrt (ℓ ^ 3))
          * ((ENNReal.ofReal (∫ x in s, (Φ x) ^ 2)) ^ (1 / 2 : ℝ)
            * (ENNReal.ofReal (ℓ ^ 3 * ∫ x in s, (Φ x) ^ 2)) ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hHolder zero_le
      _ = ENNReal.ofReal (K * ℓ ^ 3 * ∫ x in s, (Φ x) ^ 2) := by
        rw [show (ENNReal.ofReal (∫ x in s, (Φ x) ^ 2)) ^ (1 / 2 : ℝ)
              = ENNReal.ofReal (Real.sqrt (∫ x in s, (Φ x) ^ 2)) from by
            rw [ENNReal.ofReal_rpow_of_nonneg hN0 (by norm_num : (0:ℝ) ≤ 1 / 2),
              ← Real.sqrt_eq_rpow]]
        rw [show (ENNReal.ofReal (ℓ ^ 3 * ∫ x in s, (Φ x) ^ 2)) ^ (1 / 2 : ℝ)
              = ENNReal.ofReal (Real.sqrt (ℓ ^ 3 * ∫ x in s, (Φ x) ^ 2)) from by
            rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0:ℝ) ≤ 1 / 2),
              ← Real.sqrt_eq_rpow]]
        rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg (∫ x in s, (Φ x) ^ 2)),
          ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ K * Real.sqrt (ℓ ^ 3))]
        congr 1
        have hsqℓ : Real.sqrt (ℓ ^ 3) * Real.sqrt (ℓ ^ 3) = ℓ ^ 3 := by
          rw [← sq]; exact Real.sq_sqrt (by positivity)
        have hsqN : Real.sqrt (∫ x in s, (Φ x) ^ 2) * Real.sqrt (∫ x in s, (Φ x) ^ 2)
            = ∫ x in s, (Φ x) ^ 2 := by
          rw [← sq]; exact Real.sq_sqrt hN0
        rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ ℓ ^ 3) (∫ x in s, (Φ x) ^ 2)]
        rw [show K * Real.sqrt (ℓ ^ 3) * (Real.sqrt (∫ x in s, (Φ x) ^ 2)
              * (Real.sqrt (ℓ ^ 3) * Real.sqrt (∫ x in s, (Φ x) ^ 2)))
            = K * (Real.sqrt (ℓ ^ 3) * Real.sqrt (ℓ ^ 3))
              * (Real.sqrt (∫ x in s, (Φ x) ^ 2)
                * Real.sqrt (∫ x in s, (Φ x) ^ 2)) from by ring]
        rw [hsqℓ, hsqN]
  have hfin : ‖Work.BoseBoxFock.PCFU.chDslot v h fc fu μ N i j Θ‖
      ≤ K * ℓ ^ 3 * ∫ x in s, (Φ x) ^ 2 := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hkey
    rw [ENNReal.toReal_ofReal (by positivity)] at h1
    rwa [← ofReal_norm (x := Work.BoseBoxFock.PCFU.chDslot v h fc fu μ N i j Θ),
      ENNReal.toReal_ofReal (norm_nonneg _)] at h1
  calc ‖Work.BoseBoxFock.PCFU.chDslot v h fc fu μ N i j
        (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ)‖
      = ‖Work.BoseBoxFock.PCFU.chDslot v h fc fu μ N i j Θ‖ := by
        rw [hℓ.symm, hΘ.symm]
    _ ≤ K * ℓ ^ 3 * ∫ x in s, (Φ x) ^ 2 := hfin
    _ = K * (Work.BoseBoxFock.ellH v μ) ^ 3 * Work.BoseBoxFix.normB v μ n Φ := by
        rw [hnormB, hℓ.symm]

end Work.PCFU
