import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1B.chiSmallB_tBamp_decay_uniform
import Submission.Work.BoseFixB1S.chiSmallB_bounds3
import Submission.Work.BoseFixB1S.win.chiSmallB_windowIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.cubeAmpEnergyJoint`

**Joint `(p, x)`-integrability of the `p`-density of FS's box-projected spectral slot at the
cube-supported sliding cutoff.**

The target is that

    (p, x) ↦ fsKinCoeff c ‖p‖ · ((ℓ³)⁻¹ · ‖tBamp χ p (Q_{B(u),i}Ψ) i x‖²) ,
      χ = chiSmallB M ℓ d u ,  B(u) = dlBox ℓ d u ,  Q_{B,i} = boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i

is `Integrable` against `volume.prod (volume ↾ abox n ℓ)`.  This is the hypothesis under which the
`p`-integral of the slot density may be exchanged with the `x`-integral (Tonelli/Fubini), which is
what the slot-additivity of the sliding cube spectral word needs.

## Route

The *quantitative* input is the uniform Fourier decay of the box-projected amplitude at the cube
cutoff:

    ∃ C ≥ 0, ∀ x ∈ abox n ℓ, ∀ i p,  ‖tBamp (chiSmallB M ℓ d u) p (Q_{B(u),i}Ψ) i x‖ ≤ C (1+‖p‖)⁻³

(`boxQIndAmpDecayCube` below; the mirror of the private lemma of
`Work.BoseFixB1S.integrable_bandSlotTampCube` at `chiSmallB`, whose regularity `3` is exactly what
`M ≥ 4` gives).  Squaring and multiplying by `fsKinCoeff c ‖p‖ ≤ (1+|c|)²(1+‖p‖)²` produces the
pointwise domination of the joint integrand by the **`x`-independent** profile

    (ℓ³)⁻¹ · fsKinCoeff c ‖p‖ · (C/(1+‖p‖)³)² `` ≤ `` (ℓ³)⁻¹ C²(1+|c|)² (1+‖p‖)⁻⁴ ,

which is integrable on `ℝ³` by `integrable_fsKinCoeff_decayProfile`; pulling it back to the product
measure is `Integrable.comp_fst` (the second factor is the *finite* measure `volume ↾ abox n ℓ`),
and `Integrable.mono'` closes once the joint integrand is a.e.-strongly measurable
(`Work.BoseFixB1.measurable_tBamp_boxQInd_pair`, transported through the continuous factor
`p ↦ fsKinCoeff c ‖p‖`).  The a.e. statement `q.2 ∈ abox n ℓ` is
`Measure.ae_prod_iff_ae_ae` + `ae_restrict_mem`.  This last step is
`integrable_cubeAmpEnergy_of_decay`, stated for an abstract window, so that the analytic content
(decay) is cleanly separated from the measure-theoretic glue.

Nothing here uses `hc : 0 ≤ c` (the domination is by `(|c|+1)²`, and `fsKinCoeff` is a square), and
the degenerate `boxMass ℓ d u = 0` case is harmless: then `boxP = (1/0)·∫ = 0` and the bound
`|boxP| ≤ |1/volA|·(B·|A|) = 0` is still valid.
-/

namespace Work.BoseB1Cube

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The `fsKinCoeff`-weighted decay profile is integrable -/

/-- **The `fsKinCoeff`-weighted decay profile.**  For every `c, C : ℝ` the function

    `p ↦ fsKinCoeff c ‖p‖ · (C/(1+‖p‖)³)²`

is integrable on `ℝ³`: `fsKinCoeff c r = (max (r−c) 0)² ≤ (1+|c|)²(1+r)²` reduces it to a multiple
of `(1+‖·‖)⁻⁴`, and `(1+‖·‖)⁻⁴` is integrable in dimension three. -/
private theorem integrable_fsKinCoeff_decayProfile (c C : ℝ) :
    Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2) := by
  have hbase : Integrable (fun p : E3 => (1 + ‖p‖) ^ (-(4 : ℝ))) :=
    integrable_one_add_norm (μ := volume) (r := (4 : ℝ))
      (by rw [finrank_euclideanSpace_fin]; norm_num)
  have hg : Integrable (fun p : E3 => (C ^ 2 * (1 + |c|) ^ 2) * (1 + ‖p‖) ^ (-(4 : ℝ))) :=
    hbase.const_mul _
  refine hg.mono' ?_ ?_
  · have h1 : Continuous (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖) := by
      unfold Submission.BoseGases.fsKinCoeff
      exact (((continuous_id.sub continuous_const).max continuous_const).pow 2).comp continuous_norm
    have h2 : Continuous (fun p : E3 => (C / (1 + ‖p‖) ^ 3) ^ 2) := by
      refine ((continuous_const.div ((continuous_const.add continuous_norm).pow 3) ?_)).pow 2
      intro p
      exact pow_ne_zero 3 (ne_of_gt (by positivity : (0 : ℝ) < 1 + ‖p‖))
    exact (h1.mul h2).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_of_nonneg (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg _ _) (sq_nonneg _))]
    have hden : (0 : ℝ) < 1 + ‖p‖ := by positivity
    have hmax : (0 : ℝ) ≤ max (‖p‖ - c) 0 := le_max_right _ _
    have hle : max (‖p‖ - c) 0 ≤ (1 + |c|) * (1 + ‖p‖) := by
      have h2 : max (‖p‖ - c) 0 ≤ ‖p‖ + |c| := by
        refine max_le (by linarith [neg_le_abs c]) (by positivity)
      have h3 : ‖p‖ + |c| ≤ (1 + |c|) * (1 + ‖p‖) := by
        nlinarith [norm_nonneg p, abs_nonneg c, mul_nonneg (abs_nonneg c) (norm_nonneg p)]
      linarith
    have hsq : (max (‖p‖ - c) 0) ^ 2 ≤ ((1 + |c|) * (1 + ‖p‖)) ^ 2 :=
      pow_le_pow_left₀ hmax hle 2
    have hrpow : (1 + ‖p‖) ^ (-(4 : ℝ)) = ((1 + ‖p‖) ^ 4)⁻¹ := by
      rw [show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hden.le,
        Real.rpow_natCast]
    unfold Submission.BoseGases.fsKinCoeff
    rw [hrpow]
    calc (max (‖p‖ - c) 0) ^ 2 * (C / (1 + ‖p‖) ^ 3) ^ 2
        ≤ ((1 + |c|) * (1 + ‖p‖)) ^ 2 * (C / (1 + ‖p‖) ^ 3) ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ = (C ^ 2 * (1 + |c|) ^ 2) * ((1 + ‖p‖) ^ 4)⁻¹ := by field_simp

/-! ## 2. The uniform decay of the box-projected amplitude at the cube cutoff -/

/-- **Uniform `(1+‖p‖)⁻³` decay of the amplitude of FS's box projection at `chiSmallB`.**

The window `chiSmallB M ℓ d u` is `C^{M−1}` and `M ≥ 4` makes it `C³`, the regularity at which the
three-fold integration by parts behind `Work.BoseFixB1S.win.tBamp_decay_three` is legitimate.  The
box projection is split exactly (`Work.BoseBox.tBamp_boxQInd_eq_sub`):

  `tBamp χ p (Q_{B,i}Ψ) i x = tBamp χ p Ψ i x − boxP(Ψ)(x)·tBamp χ p 1 i x`,

the window vanishing off the box `B = dlBox ℓ d u`; both amplitudes decay at `(1+‖p‖)⁻³` and the
box mean is bounded on the box by `|1/volA|·(B₀·|B|)`, `B₀` a sup bound for `Ψ` on `abox n ℓ`. -/
private theorem boxQIndAmpDecayCube {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {M : ℕ}
    (hM : 4 ≤ M) (u : E3) {Ψ : X n → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Submission.BoseGases.abox n ℓ, ∀ (i : Fin n) (p : E3),
      ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Ψ) i x‖ ≤ C / (1 + ‖p‖) ^ 3 := by
  classical
  set A : Set E3 := Submission.BoseGases.dlBox ℓ d u with hAdef
  set volA : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hvoldef
  set χ : E3 → ℝ := Submission.BoseGases.chiSmallB M ℓ d u with hχdef
  have hM1 : 1 ≤ M := by omega
  -- ### the three pieces of window data
  have hχd : ContDiff ℝ 3 χ :=
    Work.BoseFixB1S.win.contDiff_chiSmallB 3 M (by omega) (ne_of_gt hℓ) (ne_of_gt hd) u
  have hχs : HasCompactSupport χ := by
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : E3) (ℓ / 2)) ?_
    intro z hz
    rw [Function.mem_support] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact Work.BoseFixB1S.chiSmallB3_support_radius (M := M) hM1 hℓ hd u
      (by simpa [hχdef] using hz)
  have hχsupp : ∀ z : E3, z ∉ A → χ z = 0 := by
    intro z hz
    exact Work.BoseFixB1S.win.chiSmallB_eq_zero_of_not_mem_dlBox (M := M) hM1 hℓ hd u z
      (by simpa [hAdef] using hz)
  -- ### the two Fourier-decay constants (the state `Ψ` and the constant state `1`)
  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    Work.BoseFixB1S.win.tBamp_decay_three (N := n) (a := ℓ) hℓ hχd hχs hΨ
  obtain ⟨C₂, hC₂0, hC₂⟩ := Work.BoseFixB1S.win.tBamp_decay_three (N := n) (a := ℓ) hℓ hχd hχs
    (Φ := fun _ : X n => (1 : ℝ)) contDiff_const
  -- ### the box mean bound on the box
  obtain ⟨B, hB0, hBb⟩ :=
    Work.BoseFixB1.exists_bound_abox_pos (N := n) (ℓ := ℓ) hℓ (Ψ := Ψ) hΨ.continuous
  have hfinA : (volume : Measure E3) A < ⊤ :=
    lt_of_le_of_lt (measure_mono (by
        intro z hz
        exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u (by simpa [hAdef] using hz)))
      (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
  have hint : ∀ (i : Fin n) (x : X n), x ∈ Submission.BoseGases.abox n ℓ →
      |∫ z in A, Ψ (Function.update x i z)| ≤ B * (volume : Measure E3).real A := by
    intro i x hx
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := volume) (s := A) (f := fun z : E3 => Ψ (Function.update x i z)) (C := B)
      hfinA (fun z hz => by
        rw [Real.norm_eq_abs]
        exact hBb _ (Submission.BoseGases.update_mem_abox i hx
          (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u (by simpa [hAdef] using hz))))
    rwa [Real.norm_eq_abs] at h
  set Mb : ℝ := |1 / volA| * (B * (volume : Measure E3).real A) with hMbdef
  have hMb0 : 0 ≤ Mb := by
    rw [hMbdef]
    have hreal : 0 ≤ (volume : Measure E3).real A := measureReal_nonneg
    positivity
  have hboxP_le : ∀ (i : Fin n) (x : X n), x ∈ Submission.BoseGases.abox n ℓ →
      |Work.SmallBoxTBWord.boxP volA A i Ψ (Function.update x i 0)| ≤ Mb := by
    intro i x hx
    have hEq : Work.SmallBoxTBWord.boxP volA A i Ψ (Function.update x i 0)
        = (1 / volA) * ∫ z in A, Ψ (Function.update x i z) := by
      rw [Work.SmallBoxTBWord.boxP]
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      rw [Function.update_idem]
    rw [hEq, abs_mul, hMbdef]
    exact mul_le_mul_of_nonneg_left (hint i x hx) (abs_nonneg _)
  -- ### the triangle inequality
  refine ⟨C₁ + Mb * C₂, add_nonneg hC₁0 (mul_nonneg hMb0 hC₂0), ?_⟩
  intro x hx i p
  rw [Work.BoseBox.tBamp_boxQInd_eq_sub (volA := volA) (A := A) (χ := χ) (N := n)
    Ψ i p x 0 hχsupp hχd.continuous hχs hΨ.continuous]
  have h1 : ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖ ≤ C₁ / (1 + ‖p‖) ^ 3 := hC₁ x hx i p
  have h2 : ‖Work.SmallBoxTBWord.tBamp χ p (fun _ : X n => (1 : ℝ)) i x‖
      ≤ C₂ / (1 + ‖p‖) ^ 3 := hC₂ x hx i p
  have h3 : |Work.SmallBoxTBWord.boxP volA A i Ψ (Function.update x i 0)| ≤ Mb := hboxP_le i x hx
  have h4 : |Work.SmallBoxTBWord.boxP volA A i Ψ (Function.update x i 0)|
      * ‖Work.SmallBoxTBWord.tBamp χ p (fun _ : X n => (1 : ℝ)) i x‖
      ≤ Mb * (C₂ / (1 + ‖p‖) ^ 3) :=
    mul_le_mul h3 h2 (norm_nonneg _) hMb0
  calc ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x
        - ((Work.SmallBoxTBWord.boxP volA A i Ψ (Function.update x i 0) : ℝ) : ℂ)
          * Work.SmallBoxTBWord.tBamp χ p (fun _ : X n => (1 : ℝ)) i x‖
      ≤ ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖
        + ‖((Work.SmallBoxTBWord.boxP volA A i Ψ (Function.update x i 0) : ℝ) : ℂ)
          * Work.SmallBoxTBWord.tBamp χ p (fun _ : X n => (1 : ℝ)) i x‖ :=
        norm_sub_le _ _
    _ = ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖
        + |Work.SmallBoxTBWord.boxP volA A i Ψ (Function.update x i 0)|
          * ‖Work.SmallBoxTBWord.tBamp χ p (fun _ : X n => (1 : ℝ)) i x‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ C₁ / (1 + ‖p‖) ^ 3 + Mb * (C₂ / (1 + ‖p‖) ^ 3) := add_le_add h1 h4
    _ = (C₁ + Mb * C₂) / (1 + ‖p‖) ^ 3 := by
        rw [← mul_div_assoc, ← add_div]

/-! ## 3. The measure-theoretic assembly: decay ⟹ joint integrability -/

/-- **The joint integrability of the `fsKinCoeff`-weighted slot density from a uniform decay
bound.**  For an abstract measurable box `A`, a continuous window `χ`, a measurable state `Ψ` and a
uniform bound `‖tBamp χ p (Q_{A,i}Ψ) i x‖ ≤ C(1+‖p‖)⁻³` on the box `abox n a`, the pair `(p, x)`
integrand `fsKinCoeff c ‖p‖·((a³)⁻¹‖tBamp χ p (Q_{A,i}Ψ) i x‖²)` is integrable against
`volume.prod (volume ↾ abox n a)`.

The domination is by the `x`-independent profile `(a³)⁻¹·fsKinCoeff c ‖p‖·(C/(1+‖p‖)³)²`, whose
integrability is `integrable_fsKinCoeff_decayProfile`; `Integrable.comp_fst` lifts it to the product
(using finiteness of `volume ↾ abox n a`), and `Integrable.mono'` finishes with the a.e.-strong
measurability of the integrand and the a.e. bound `q.2 ∈ abox n a`
(`Measure.ae_prod_iff_ae_ae`). -/
private theorem integrable_cubeAmpEnergy_of_decay {n : ℕ} {a volA c : ℝ} (ha : 0 < a)
    {A : Set E3} (hA : MeasurableSet A) {χ : E3 → ℝ} (hχ : Continuous χ)
    {Ψ : X n → ℝ} (hΨ : Measurable Ψ) {C : ℝ}
    (hdec : ∀ x ∈ Submission.BoseGases.abox n a, ∀ (i : Fin n) (p : E3),
      ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖
        ≤ C / (1 + ‖p‖) ^ 3) (i : Fin n) :
    Integrable (fun q : E3 × X n =>
        Submission.BoseGases.fsKinCoeff c ‖q.1‖ *
          ((a ^ 3)⁻¹ * ‖Work.SmallBoxTBWord.tBamp χ q.1
            (Work.UBBInputs8.boxQInd volA A i Ψ) i q.2‖ ^ 2))
      ((volume : Measure E3).prod
        ((volume : Measure (X n)).restrict (Submission.BoseGases.abox n a))) := by
  classical
  haveI : IsFiniteMeasure ((volume : Measure (X n)).restrict (Submission.BoseGases.abox n a)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.abox_lt_top n a ha.le⟩
  -- the dominating profile, pulled back from `p` to the pair `(p, x)`
  have hG : Integrable (fun p : E3 =>
      (a ^ 3)⁻¹ * (Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2)) :=
    (integrable_fsKinCoeff_decayProfile c C).const_mul _
  have hdom := hG.comp_fst ((volume : Measure (X n)).restrict (Submission.BoseGases.abox n a))
  refine hdom.mono' ?_ ?_
  · -- a.e.-strong measurability of the integrand
    have hmeas : Measurable (fun q : E3 × X n =>
        ‖Work.SmallBoxTBWord.tBamp χ q.1 (Work.UBBInputs8.boxQInd volA A i Ψ) i q.2‖ ^ 2) :=
      Work.BoseFixB1.measurable_tBamp_boxQInd_pair hA hχ hΨ i
    have hfs : Continuous (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖) := by
      unfold Submission.BoseGases.fsKinCoeff
      exact (((continuous_id.sub continuous_const).max continuous_const).pow 2).comp continuous_norm
    exact ((hfs.comp continuous_fst).measurable.mul (hmeas.const_mul (a ^ 3)⁻¹)).aestronglyMeasurable
  · -- the a.e. pointwise domination
    have hae : ∀ᵐ q ∂((volume : Measure E3).prod
        ((volume : Measure (X n)).restrict (Submission.BoseGases.abox n a))),
        q.2 ∈ Submission.BoseGases.abox n a := by
      rw [Measure.ae_prod_iff_ae_ae
        ((Submission.BoseGases.abox_measurable n a).preimage measurable_snd)]
      filter_upwards with p
      exact ae_restrict_mem (Submission.BoseGases.abox_measurable n a)
    filter_upwards [hae] with q hq
    have hfnn : 0 ≤ Submission.BoseGases.fsKinCoeff c ‖q.1‖ *
        ((a ^ 3)⁻¹ * ‖Work.SmallBoxTBWord.tBamp χ q.1
          (Work.UBBInputs8.boxQInd volA A i Ψ) i q.2‖ ^ 2) :=
      mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg _ _)
        (mul_nonneg (by positivity) (sq_nonneg _))
    rw [Real.norm_of_nonneg hfnn]
    calc Submission.BoseGases.fsKinCoeff c ‖q.1‖ *
          ((a ^ 3)⁻¹ * ‖Work.SmallBoxTBWord.tBamp χ q.1
            (Work.UBBInputs8.boxQInd volA A i Ψ) i q.2‖ ^ 2)
        ≤ Submission.BoseGases.fsKinCoeff c ‖q.1‖ *
          ((a ^ 3)⁻¹ * (C / (1 + ‖q.1‖) ^ 3) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (Submission.BoseGases.fsKinCoeff_nonneg _ _)
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (hdec q.2 hq i q.1) 2) (by positivity)
      _ = (a ^ 3)⁻¹ * (Submission.BoseGases.fsKinCoeff c ‖q.1‖ * (C / (1 + ‖q.1‖) ^ 3) ^ 2) := by
          ring

/-! ## 4. The target -/

theorem cubeAmpEnergyJoint {n : ℕ} {ℓ d c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {M : ℕ} (hM : 4 ≤ M)
    (u : EuclideanSpace ℝ (Fin 3)) (hc : 0 ≤ c) {Ψ : Submission.BoseGases.X n → ℝ}
    (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) (i : Fin n) :
    MeasureTheory.Integrable
      (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Submission.BoseGases.fsKinCoeff c ‖q.1‖ *
          ((ℓ ^ 3)⁻¹ *
            ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) q.1
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) i Ψ) i q.2‖ ^ 2))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))) := by
  obtain ⟨C, _hC0, hdec⟩ := boxQIndAmpDecayCube (n := n) hℓ hd hM u hΨ
  exact integrable_cubeAmpEnergy_of_decay (a := ℓ) (volA := Work.SmallBoxSliding.boxMass ℓ d u)
    (A := Submission.BoseGases.dlBox ℓ d u) (χ := Submission.BoseGases.chiSmallB M ℓ d u)
    (c := c) hℓ (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)
    ((Work.BoseFixB1S.win.contDiff_chiSmallB 3 M (by omega) (ne_of_gt hℓ) (ne_of_gt hd) u).continuous)
    hΨ.continuous.measurable hdec i

end

end Work.BoseB1Cube
