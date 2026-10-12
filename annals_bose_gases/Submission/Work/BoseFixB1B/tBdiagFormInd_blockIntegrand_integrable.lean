import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1B.tBamp_amplitude_box_fubini
import Submission.Work.BoseFixB1B.tBamp_boxQInd_uniform_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Joint `(p,w)`-integrability of the block-split `tBamp` amplitude integrand

This is the input that licenses the exchange of `∫_p` with `∫_w` in the block split of
`Work.UBBInputs8.tBdiagFormInd` (`Work.BoseFixB1B.tBdiagFormInd_slice_split_box`).

**The mathematics.**  The windowed amplitude `tBamp χ p (Q_{B,i}Ψ) i x` is the `p`-Fourier
transform of a compactly supported smooth fibre, so it decays like `(1+‖p‖)⁻³`
(`Work.BoseFixB1B.tBamp_boxQInd_uniform_decay`, applied to the *big* state `Φ` on the box
`abox (N₁+N₂) a`).  Because the amplitude of a block slot at a merged configuration is exactly the
amplitude of the corresponding slot of the slice (`tBamp_boxQInd_merge_castAdd`, resp.
`tBamp_boxQInd_merge_natAdd`), this decay is *uniform* in the frozen block `w ∈ abox N₂ a` as
well.  Hence, with `F` obeying the growth bound `|F r| ≤ K(1+r)^d`, `d < 3`,

    ‖F‖p‖ · ((a³)⁻¹∫_{abox N₁ a}‖tBamp χ p (Q_j slice_w) j u‖²)‖ ≤ M·(1+‖p‖)^(d-6),

and `d - 6 < -3 = -dim ℝ³` makes the right-hand side integrable against
`volume.prod (volume.restrict (abox N₂ a))` (`integrable_one_add_norm` + `Integrable.comp_fst`).

**The formal points.**  (i) The inner `u`-integral is bounded with
`norm_setIntegral_le_of_norm_le_const`, the box `abox N₁ a` having finite measure.  (ii) Joint
measurability of the integrand in `(p, w)` — needed for `Integrable.mono'` — comes from
`Work.BoseFixB1.measurable_tBamp_boxQInd_pair` (joint measurability of `(p,x) ↦ ‖amp‖²` for a
*fixed* state) composed with the measurable map `(p,w,u) ↦ (p, mergeBlock (u,w))`, rewritten along
the merge identity, and finally integrated over `u` by
`MeasureTheory.StronglyMeasurable.integral_prod_right'` (no integrability needed).  (iii) The
pointwise bound on the `u`-integral only holds for `w ∈ abox N₂ a`, so the domination is an
`∀ᵐ` statement (`ae_iff` + `Measure.prod_prod`).
-/

noncomputable section

open MeasureTheory
open scoped Real ENNReal Topology
open Submission.BoseGases

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1.  Auxiliary measurability of the block concatenation -/

/-- The block concatenation `mergeBlock N₁ N₂ : X N₁ × X N₂ → X (N₁+N₂)` is continuous
(each coordinate is one of the two block coordinates). -/
private lemma continuous_mergeBlock_pair (N1 N2 : ℕ) :
    Continuous (Submission.BoseGases.mergeBlock N1 N2) := by
  rw [continuous_pi_iff]
  intro k
  by_cases h : (k : ℕ) < N1
  · let i : Fin N1 := ⟨k.val, h⟩
    have hk : k = Fin.castAdd N2 i := by ext; simp [i]
    rw [hk]
    have hfun : (fun p : Submission.BoseGases.X N1 × Submission.BoseGases.X N2 =>
        Submission.BoseGases.mergeBlock N1 N2 p (Fin.castAdd N2 i)) = fun p => p.1 i := by
      funext p; simp [Submission.BoseGases.mergeBlock]
    rw [hfun]
    exact (continuous_apply i).comp continuous_fst
  · push Not at h
    let j : Fin N2 := ⟨k.val - N1, by omega⟩
    have hkN : k = Fin.natAdd N1 j := by ext; simp [j]; omega
    rw [hkN]
    have hfun : (fun p : Submission.BoseGases.X N1 × Submission.BoseGases.X N2 =>
        Submission.BoseGases.mergeBlock N1 N2 p (Fin.natAdd N1 j)) = fun p => p.2 j := by
      funext p; simp [Submission.BoseGases.mergeBlock]
    rw [hfun]
    exact (continuous_apply j).comp continuous_snd

/-! ## 2.  Joint measurability of the block-slot amplitude in `(p, w, u)` -/

/-- Joint measurability of `(p, w, u) ↦ ‖tBamp χ p (Q_{A,j} (w-slice)) j u‖²`, first-block side.
The slice amplitude is the amplitude of the *big* box slot at the merged configuration
(`tBamp_boxQInd_merge_castAdd`), which is jointly measurable in `(p, ·)` by
`Work.BoseFixB1.measurable_tBamp_boxQInd_pair`. -/
private lemma measurable_blockAmp_sq_left {N1 N2 : ℕ} {V : ℝ} {A : Set E3}
    (hA : MeasurableSet A) {χ : E3 → ℝ} (hχ : Continuous χ)
    {Φ : Submission.BoseGases.X (N1 + N2) → ℝ} (hΦm : Measurable Φ) (j : Fin N1) :
    Measurable (fun q : (E3 × Submission.BoseGases.X N2) × Submission.BoseGases.X N1 =>
      ‖Work.SmallBoxTBWord.tBamp χ q.1.1
        (Work.UBBInputs8.boxQInd V A j
          (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, q.1.2)))) j q.2‖ ^ 2) := by
  have hmB := continuous_mergeBlock_pair N1 N2
  have hmtB := Work.BoseFixB1.measurable_tBamp_boxQInd_pair (n := N1 + N2) (A := A) (χ := χ)
    (volA := V) (Ψ := Φ) hA hχ hΦm (Fin.castAdd N2 j)
  have hpair : Measurable (fun q : (E3 × Submission.BoseGases.X N2) ×
      Submission.BoseGases.X N1 =>
      (q.1.1, Submission.BoseGases.mergeBlock N1 N2 (q.2, q.1.2))) :=
    (measurable_fst.comp measurable_fst).prodMk
      (hmB.measurable.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  have hcomp := hmtB.comp hpair
  change Measurable (fun q : (E3 × Submission.BoseGases.X N2) × Submission.BoseGases.X N1 =>
      ‖Work.SmallBoxTBWord.tBamp χ q.1.1 (Work.UBBInputs8.boxQInd V A (Fin.castAdd N2 j) Φ)
        (Fin.castAdd N2 j) (Submission.BoseGases.mergeBlock N1 N2 (q.2, q.1.2))‖ ^ 2) at hcomp
  have heq : (fun q : (E3 × Submission.BoseGases.X N2) × Submission.BoseGases.X N1 =>
        ‖Work.SmallBoxTBWord.tBamp χ q.1.1 (Work.UBBInputs8.boxQInd V A (Fin.castAdd N2 j) Φ)
          (Fin.castAdd N2 j) (Submission.BoseGases.mergeBlock N1 N2 (q.2, q.1.2))‖ ^ 2)
      = (fun q : (E3 × Submission.BoseGases.X N2) × Submission.BoseGases.X N1 =>
        ‖Work.SmallBoxTBWord.tBamp χ q.1.1
          (Work.UBBInputs8.boxQInd V A j
            (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, q.1.2)))) j q.2‖ ^ 2) := by
    funext q
    rw [tBamp_boxQInd_merge_castAdd Φ j q.2 q.1.2]
  rwa [heq] at hcomp

/-- Joint measurability of `(p, y, w) ↦ ‖tBamp χ p (Q_{A,j} (y-slice)) j w‖²`, second-block
side. -/
private lemma measurable_blockAmp_sq_right {N1 N2 : ℕ} {V : ℝ} {A : Set E3}
    (hA : MeasurableSet A) {χ : E3 → ℝ} (hχ : Continuous χ)
    {Φ : Submission.BoseGases.X (N1 + N2) → ℝ} (hΦm : Measurable Φ) (j : Fin N2) :
    Measurable (fun q : (E3 × Submission.BoseGases.X N1) × Submission.BoseGases.X N2 =>
      ‖Work.SmallBoxTBWord.tBamp χ q.1.1
        (Work.UBBInputs8.boxQInd V A j
          (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (q.1.2, y)))) j q.2‖ ^ 2) := by
  have hmB := continuous_mergeBlock_pair N1 N2
  have hmtB := Work.BoseFixB1.measurable_tBamp_boxQInd_pair (n := N1 + N2) (A := A) (χ := χ)
    (volA := V) (Ψ := Φ) hA hχ hΦm (Fin.natAdd N1 j)
  have hpair : Measurable (fun q : (E3 × Submission.BoseGases.X N1) ×
      Submission.BoseGases.X N2 =>
      (q.1.1, Submission.BoseGases.mergeBlock N1 N2 (q.1.2, q.2))) :=
    (measurable_fst.comp measurable_fst).prodMk
      (hmB.measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hcomp := hmtB.comp hpair
  change Measurable (fun q : (E3 × Submission.BoseGases.X N1) × Submission.BoseGases.X N2 =>
      ‖Work.SmallBoxTBWord.tBamp χ q.1.1 (Work.UBBInputs8.boxQInd V A (Fin.natAdd N1 j) Φ)
        (Fin.natAdd N1 j) (Submission.BoseGases.mergeBlock N1 N2 (q.1.2, q.2))‖ ^ 2) at hcomp
  have heq : (fun q : (E3 × Submission.BoseGases.X N1) × Submission.BoseGases.X N2 =>
        ‖Work.SmallBoxTBWord.tBamp χ q.1.1 (Work.UBBInputs8.boxQInd V A (Fin.natAdd N1 j) Φ)
          (Fin.natAdd N1 j) (Submission.BoseGases.mergeBlock N1 N2 (q.1.2, q.2))‖ ^ 2)
      = (fun q : (E3 × Submission.BoseGases.X N1) × Submission.BoseGases.X N2 =>
        ‖Work.SmallBoxTBWord.tBamp χ q.1.1
          (Work.UBBInputs8.boxQInd V A j
            (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (q.1.2, y)))) j q.2‖ ^ 2) := by
    funext q
    rw [tBamp_boxQInd_merge_natAdd Φ j q.1.2 q.2]
  rwa [heq] at hcomp

/-! ## 3.  The generic integrability lemma -/

/-- **Integrability of `F‖p‖ · (a³)⁻¹·I(p,w)` on the product measure.**  If the inner functional
`I` is measurable, nonnegative, and bounded by `(C/(1+‖p‖)³)²·Vbox` on the `w`-box, then the
weighted integrand is `L¹` for `volume.prod (volume.restrict (abox M a))`, because
`|F r| ≤ K(1+r)^d` with `d < 3` turns the bound into `(1+‖p‖)^(d-6)`, integrable in dimension
three. -/
private lemma integrable_blockIntegrand {M : ℕ} {a Vbox : ℝ} (ha : 0 < a) (hVbox : 0 ≤ Vbox)
    {K d C : ℝ} (hK : 0 ≤ K) (hd : d < 3) (hC0 : 0 ≤ C)
    {F : ℝ → ℝ} (hFm : Measurable F)
    (hFd : ∀ r : ℝ, 0 ≤ r → |F r| ≤ K * (1 + r) ^ d)
    {I : E3 × Submission.BoseGases.X M → ℝ} (hIm : Measurable I) (hI0 : ∀ q, 0 ≤ I q)
    (hIbd : ∀ q, q.2 ∈ Submission.BoseGases.abox M a →
      I q ≤ (C / (1 + ‖q.1‖) ^ 3) ^ 2 * Vbox) :
    MeasureTheory.Integrable
      (fun q : E3 × Submission.BoseGases.X M => F ‖q.1‖ * ((a ^ 3)⁻¹ * I q))
      ((MeasureTheory.volume : Measure E3).prod
        ((MeasureTheory.volume : Measure (Submission.BoseGases.X M)).restrict
          (Submission.BoseGases.abox M a))) := by
  have hFIN : IsFiniteMeasure
      ((volume : Measure (Submission.BoseGases.X M)).restrict (Submission.BoseGases.abox M a)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (Submission.BoseGases.abox_lt_top M a ha.le).ne
  have hfin : (Module.finrank ℝ E3 : ℝ) < 6 - d := by
    rw [finrank_euclideanSpace_fin]
    simp
    linarith
  have hbase : Integrable (fun p : E3 => (1 + ‖p‖) ^ (-(6 - d))) (volume : Measure E3) :=
    integrable_one_add_norm (μ := (volume : Measure E3)) hfin
  have hbase' : Integrable (fun p : E3 => (1 + ‖p‖) ^ (d - 6)) (volume : Measure E3) := by
    simpa only [show -(6 - d) = d - 6 by ring] using hbase
  have hdom : Integrable (fun q : E3 × Submission.BoseGases.X M =>
      (K * C ^ 2 * (a ^ 3)⁻¹ * Vbox) * (1 + ‖q.1‖) ^ (d - 6))
      ((volume : Measure E3).prod
        ((volume : Measure (Submission.BoseGases.X M)).restrict
          (Submission.BoseGases.abox M a))) :=
    (hbase'.const_mul (K * C ^ 2 * (a ^ 3)⁻¹ * Vbox)).comp_fst _
  refine hdom.mono' ?_ ?_
  · exact ((hFm.comp ((continuous_norm.comp continuous_fst).measurable)).mul
      (measurable_const.mul hIm)).aestronglyMeasurable
  · have hae : ∀ᵐ q ∂((volume : Measure E3).prod
        ((volume : Measure (Submission.BoseGases.X M)).restrict
          (Submission.BoseGases.abox M a))), q.2 ∈ Submission.BoseGases.abox M a := by
      rw [MeasureTheory.ae_iff]
      rw [show {q : E3 × Submission.BoseGases.X M |
            ¬ q.2 ∈ Submission.BoseGases.abox M a}
          = Set.univ ×ˢ (Submission.BoseGases.abox M a)ᶜ by ext q; simp]
      rw [Measure.prod_prod]
      have hc : ((volume : Measure (Submission.BoseGases.X M)).restrict
          (Submission.BoseGases.abox M a)) (Submission.BoseGases.abox M a)ᶜ = 0 := by
        rw [Measure.restrict_apply (Submission.BoseGases.abox_measurable M a).compl,
          Set.compl_inter_self, measure_empty]
      rw [hc, mul_zero]
    filter_upwards [hae] with q hq
    have hr : 0 < 1 + ‖q.1‖ := by positivity
    have ha3 : 0 < (a ^ 3)⁻¹ := inv_pos_of_pos (pow_pos ha 3)
    have hI' : 0 ≤ (a ^ 3)⁻¹ * I q := mul_nonneg ha3.le (hI0 q)
    have hFb : |F ‖q.1‖| ≤ K * (1 + ‖q.1‖) ^ d := hFd ‖q.1‖ (norm_nonneg _)
    have hIq : I q ≤ (C / (1 + ‖q.1‖) ^ 3) ^ 2 * Vbox := hIbd q hq
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg hI']
    calc |F ‖q.1‖| * ((a ^ 3)⁻¹ * I q)
        ≤ (K * (1 + ‖q.1‖) ^ d) *
            ((a ^ 3)⁻¹ * ((C / (1 + ‖q.1‖) ^ 3) ^ 2 * Vbox)) := by
          refine mul_le_mul hFb (mul_le_mul_of_nonneg_left hIq ha3.le) hI' ?_
          exact mul_nonneg hK (Real.rpow_nonneg (by positivity) d)
      _ = (K * C ^ 2 * (a ^ 3)⁻¹ * Vbox) * (1 + ‖q.1‖) ^ (d - 6) := by
          have hinv : ((1 + ‖q.1‖) ^ 6 : ℝ)⁻¹ = (1 + ‖q.1‖) ^ (-(6:ℝ)) := by
            rw [← Real.rpow_natCast (1 + ‖q.1‖) 6]
            exact (Real.rpow_neg (by positivity) 6).symm
          have h1 : (C / (1 + ‖q.1‖) ^ 3) ^ 2
              = C ^ 2 * (1 + ‖q.1‖) ^ (-(6:ℝ)) := by
            rw [div_pow, show ((1 + ‖q.1‖) ^ 3) ^ 2 = (1 + ‖q.1‖) ^ 6 by ring,
              div_eq_mul_inv, hinv]
          have hpow : (1 + ‖q.1‖) ^ d * (1 + ‖q.1‖) ^ (-(6:ℝ))
              = (1 + ‖q.1‖) ^ (d - 6) := by
            rw [← Real.rpow_add hr d (-(6:ℝ))]
            congr 1
          rw [h1, ← hpow]
          ring

/-! ## 4.  The target -/

theorem tBdiagFormInd_blockIntegrand_integrable {N1 N2 : ℕ} {a V : ℝ} (ha : 0 < a)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχs : HasCompactSupport χ) (hχA : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ A → χ z = 0)
    {Φ : Submission.BoseGases.X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {F : ℝ → ℝ} (hFm : Measurable F) {K d : ℝ} (hK : 0 ≤ K) (hd : d < 3)
    (hFd : ∀ r : ℝ, 0 ≤ r → |F r| ≤ K * (1 + r) ^ d) :
    (∀ j : Fin N1,
        MeasureTheory.Integrable
          (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N2 =>
            F ‖q.1‖ * ((a ^ 3)⁻¹ * (∫ u in Submission.BoseGases.abox N1 a,
              ‖Work.SmallBoxTBWord.tBamp χ q.1
                (Work.UBBInputs8.boxQInd V A j
                  (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, q.2)))) j u‖ ^ 2)))
          (MeasureTheory.volume.prod
            (MeasureTheory.volume.restrict (Submission.BoseGases.abox N2 a))))
    ∧ (∀ j : Fin N2,
        MeasureTheory.Integrable
          (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N1 =>
            F ‖q.1‖ * ((a ^ 3)⁻¹ * (∫ w in Submission.BoseGases.abox N2 a,
              ‖Work.SmallBoxTBWord.tBamp χ q.1
                (Work.UBBInputs8.boxQInd V A j
                  (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (q.2, y)))) j w‖ ^ 2)))
          (MeasureTheory.volume.prod
            (MeasureTheory.volume.restrict (Submission.BoseGases.abox N1 a)))) := by
  classical
  -- the window vanishes off the box
  have hχsupp : Function.support χ ⊆ A := by
    intro z hz
    by_contra hzA
    exact hz (hχA z hzA)
  -- the state is bounded on the big box
  obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact (N1 + N2) ha).exists_bound_of_continuousOn
    (f := Φ) hΦ.continuous.continuousOn
  have hB0 : 0 ≤ B :=
    le_trans (norm_nonneg (Φ 0)) (hB 0 (Submission.BoseGases.zero_mem_abox ha.le))
  have hΦb : ∀ x ∈ Submission.BoseGases.abox (N1 + N2) a, |Φ x| ≤ B :=
    fun x hx => by simpa [Real.norm_eq_abs] using hB x hx
  -- the uniform decay of the box-projected amplitude
  obtain ⟨C, hC0, hCd⟩ := tBamp_boxQInd_uniform_decay (N := N1 + N2) (a := a) (volA := V) (B := B)
    ha hB0 hA hAc hχ hχs hχsupp hΦ hΦb
  have hΦm : Measurable Φ := hΦ.continuous.measurable
  constructor
  · -- ## first block
    intro j
    have hslice : ∀ (u : Submission.BoseGases.X N1) (w : Submission.BoseGases.X N2),
        u ∈ Submission.BoseGases.abox N1 a → w ∈ Submission.BoseGases.abox N2 a →
        ∀ p : E3,
        ‖Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd V A j
            (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w)))) j u‖
          ≤ C / (1 + ‖p‖) ^ 3 := by
      intro u w hu hw p
      rw [← tBamp_boxQInd_merge_castAdd Φ j u w]
      exact hCd (Submission.BoseGases.mergeBlock N1 N2 (u, w))
        (cns_split_mergeBlock_mem_abox hu hw) (Fin.castAdd N2 j) p
    have hIm : Measurable (fun q : E3 × Submission.BoseGases.X N2 =>
        ∫ u in Submission.BoseGases.abox N1 a,
          ‖Work.SmallBoxTBWord.tBamp χ q.1
            (Work.UBBInputs8.boxQInd V A j
              (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, q.2)))) j u‖ ^ 2) := by
      have h := (measurable_blockAmp_sq_left (N1 := N1) (N2 := N2) (V := V) (A := A)
        hA hχ.continuous hΦm j).stronglyMeasurable.integral_prod_right'
        (ν := (volume : Measure (Submission.BoseGases.X N1)).restrict
          (Submission.BoseGases.abox N1 a))
      simpa only using h.measurable
    refine integrable_blockIntegrand (M := N2) (a := a) (Vbox :=
        (volume : Measure (Submission.BoseGases.X N1)).real (Submission.BoseGases.abox N1 a))
      ha measureReal_nonneg hK hd hC0 hFm hFd hIm
      (fun q => integral_nonneg (fun u => sq_nonneg _)) ?_
    intro q hq
    have hstep : ∀ u ∈ Submission.BoseGases.abox N1 a,
        ‖Work.SmallBoxTBWord.tBamp χ q.1
          (Work.UBBInputs8.boxQInd V A j
            (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, q.2)))) j u‖ ^ 2
          ≤ (C / (1 + ‖q.1‖) ^ 3) ^ 2 :=
      fun u hu => pow_le_pow_left₀ (norm_nonneg _) (hslice u q.2 hu hq q.1) 2
    have h1 := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure (Submission.BoseGases.X N1)))
      (s := Submission.BoseGases.abox N1 a)
      (f := fun u : Submission.BoseGases.X N1 =>
        ‖Work.SmallBoxTBWord.tBamp χ q.1
          (Work.UBBInputs8.boxQInd V A j
            (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, q.2)))) j u‖ ^ 2)
      (C := (C / (1 + ‖q.1‖) ^ 3) ^ 2)
      (Submission.BoseGases.abox_lt_top N1 a ha.le)
      (fun u hu => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hstep u hu)
    rwa [Real.norm_of_nonneg (integral_nonneg (fun u => sq_nonneg _))] at h1
  · -- ## second block
    intro j
    have hslice : ∀ (u : Submission.BoseGases.X N1) (w : Submission.BoseGases.X N2),
        u ∈ Submission.BoseGases.abox N1 a → w ∈ Submission.BoseGases.abox N2 a →
        ∀ p : E3,
        ‖Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd V A j
            (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, y)))) j w‖
          ≤ C / (1 + ‖p‖) ^ 3 := by
      intro u w hu hw p
      rw [← tBamp_boxQInd_merge_natAdd Φ j u w]
      exact hCd (Submission.BoseGases.mergeBlock N1 N2 (u, w))
        (cns_split_mergeBlock_mem_abox hu hw) (Fin.natAdd N1 j) p
    have hIm : Measurable (fun q : E3 × Submission.BoseGases.X N1 =>
        ∫ w in Submission.BoseGases.abox N2 a,
          ‖Work.SmallBoxTBWord.tBamp χ q.1
            (Work.UBBInputs8.boxQInd V A j
              (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (q.2, y)))) j w‖ ^ 2) := by
      have h := (measurable_blockAmp_sq_right (N1 := N1) (N2 := N2) (V := V) (A := A)
        hA hχ.continuous hΦm j).stronglyMeasurable.integral_prod_right'
        (ν := (volume : Measure (Submission.BoseGases.X N2)).restrict
          (Submission.BoseGases.abox N2 a))
      simpa only using h.measurable
    refine integrable_blockIntegrand (M := N1) (a := a) (Vbox :=
        (volume : Measure (Submission.BoseGases.X N2)).real (Submission.BoseGases.abox N2 a))
      ha measureReal_nonneg hK hd hC0 hFm hFd hIm
      (fun q => integral_nonneg (fun w => sq_nonneg _)) ?_
    intro q hq
    have hstep : ∀ w ∈ Submission.BoseGases.abox N2 a,
        ‖Work.SmallBoxTBWord.tBamp χ q.1
          (Work.UBBInputs8.boxQInd V A j
            (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (q.2, y)))) j w‖ ^ 2
          ≤ (C / (1 + ‖q.1‖) ^ 3) ^ 2 :=
      fun w hw => pow_le_pow_left₀ (norm_nonneg _) (hslice q.2 w hq hw q.1) 2
    have h1 := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure (Submission.BoseGases.X N2)))
      (s := Submission.BoseGases.abox N2 a)
      (f := fun w : Submission.BoseGases.X N2 =>
        ‖Work.SmallBoxTBWord.tBamp χ q.1
          (Work.UBBInputs8.boxQInd V A j
            (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (q.2, y)))) j w‖ ^ 2)
      (C := (C / (1 + ‖q.1‖) ^ 3) ^ 2)
      (Submission.BoseGases.abox_lt_top N2 a ha.le)
      (fun w hw => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hstep w hw)
    rwa [Real.norm_of_nonneg (integral_nonneg (fun w => sq_nonneg _))] at h1

end Work.BoseFixB1B
