import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixB1S.chiSmallB_bounds3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.cubeSpectral_uniformBound`

The `u`-uniform bound on the matched sliding **cube** spectral form

    u ↦ `tBwordKinInd ℓ (dlBox ℓ d u) (boxMass ℓ d u) (chiSmallB M ℓ d u) c Φ`

for a fixed smooth many-body state `Φ`.  The box family is the sliding family
`B(u) = acube ℓ ∩ ((ℓd)•u + acube (ℓd))` and the window is the cube-supported cutoff
`chiSmallB M ℓ d u`; the ambient box is `abox N ℓ`.

## Route

1. **Uniform decay.**  For a *family* `χ : E3 → E3 → ℝ` of windows which are `C³`, supported in a
   fixed ball of radius `R`, and whose iterated derivatives up to order `3` are bounded by a
   `u`-independent sequence `G`, the windowed amplitude `tBamp (χ u) p Ψ i x` decays like
   `C (1+‖p‖)⁻³` with `C` independent of `u` (and of `x`, `i`), for any *fixed* `C³` state `Ψ`
   with `u`-independent derivative bounds `Mb` on the box.  This is `tBamp_decay_fam`, the
   uniform-in-`u` form of `Commons.Analysis.Fourier.fourier_decay_mul_update`; the window
   certificate `chiSmallB_bounds3` supplies `(hχc, R, G)` for `chiSmallB M ℓ d u`.

2. **The box projection.**  `boxQInd` carries FS's box indicator while the decay estimate applies
   to the plain smooth state.  On the support of the cube cutoff the indicator is `1`, so the two
   amplitudes agree: `tBamp` of `boxQInd` equals `tBamp` of `boxQ V A i Φ`, and the latter is
   smooth (`boxQ_contDiff_of_compact`, the box being compact) with compact-support window data.

3. **Integration.**  The pointwise `(1+‖p‖)⁻³` bound (together with `fsKinCoeff c r ≤ (1+|c|)²(1+r)²`)
   dominates the `p`-integrand by `const·(1+‖p‖)⁻⁴`, which is integrable in `ℝ³`; the `x`-integral
   gives the volume `(ℓ³)^N` of `abox N ℓ`.  Summing over the `N` slots produces the uniform `K`.
-/

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 1. Elementary estimates -/

/-- A vector of `E3` all of whose coordinates are bounded by `C` has norm at most `√3·C`. -/
private lemma norm_le_of_coord_abs_le {C : ℝ} (hC : 0 ≤ C) {y : E3}
    (hy : ∀ k : Fin 3, |y k| ≤ C) : ‖y‖ ≤ Real.sqrt 3 * C := by
  have hb : 0 ≤ Real.sqrt 3 * C := by positivity
  apply le_of_sq_le_sq
  · rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ k : Fin 3, (y k) ^ 2 ≤ ∑ _k : Fin 3, C ^ 2 := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          exact sq_le_sq.mpr (by simpa [abs_of_nonneg hC] using hy k)
      _ = 3 * C ^ 2 := by norm_num
      _ = (Real.sqrt 3 * C) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  · exact hb

/-- Every coordinate of a configuration of `abox N a` is bounded by `3a`. -/
private lemma norm_coord_abox {N : ℕ} {a : ℝ} (ha : 0 < a) {x : X N}
    (hx : x ∈ Submission.BoseGases.abox N a) (j : Fin N) : ‖x j‖ ≤ 3 * a := by
  have hmem : x j ∈ Submission.BoseGases.acube a := hx j
  rw [Submission.BoseGases.mem_acube_iff] at hmem
  have habs : ∀ k : Fin 3, |(x j) k| ≤ a / 2 := by
    intro k
    rw [abs_le]
    exact ⟨by linarith [(hmem k).1], (hmem k).2⟩
  have h1 : ‖x j‖ ≤ Real.sqrt 3 * (a / 2) := norm_le_of_coord_abs_le (by positivity) habs
  have h2 : Real.sqrt 3 * (a / 2) ≤ 3 * a := by
    have hs : Real.sqrt 3 ≤ 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
    nlinarith
  linarith

/-- Replacing one slot of a configuration of `abox N a` by a point of a set contained in
`acube a` keeps it in `abox N a`. -/
private lemma update_mem_abox {N : ℕ} {a : ℝ} {A : Set E3}
    (hAsub : A ⊆ Submission.BoseGases.acube a) {x : X N}
    (hx : x ∈ Submission.BoseGases.abox N a) {z : E3} (hz : z ∈ A) (i : Fin N) :
    Function.update x i z ∈ Submission.BoseGases.abox N a := by
  intro j
  by_cases hj : j = i
  · subst hj; rw [Function.update_self]; exact hAsub hz
  · rw [Function.update_of_ne hj]; exact hx j

/-- The sliding box `B(u) = acube ℓ ∩ ((ℓd)•u + acube (ℓd))` is compact. -/
private lemma isCompact_dlBox_priv {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) :
    IsCompact (Submission.BoseGases.dlBox ℓ d u) := by
  have hpre : IsClosed ((fun x : E3 => x - (ℓ * d) • u) ⁻¹'
      Submission.BoseGases.acube (ℓ * d)) :=
    (Submission.BoseGases.acube_isClosed (ℓ * d)).preimage (by fun_prop)
  refine (Submission.BoseGases.acube_compact hℓ).of_isClosed_subset ?_ ?_
  · unfold Submission.BoseGases.dlBox
    exact (Submission.BoseGases.acube_isClosed ℓ).inter hpre
  · intro x hx
    exact (Submission.BoseGases.mem_dlBox_iff ℓ d u x).mp hx |>.1

/-- The modulus of the Fourier phase is `1`. -/
private lemma norm_exp_neg_inner (p z : E3) :
    ‖Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))‖ = 1 := by
  have hrew : -(Complex.I * ((inner ℝ p z : ℝ) : ℂ))
      = (((-(inner ℝ p z)) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hrew, Complex.norm_exp_ofReal_mul_I]

/-- Continuity of the Fourier phase. -/
private lemma continuous_exp_neg_inner (p : E3) :
    Continuous (fun z : E3 => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))) :=
  Complex.continuous_exp.comp
    (((continuous_const : Continuous fun _ : E3 => Complex.I).mul
      (Complex.continuous_ofReal.comp (continuous_inner.comp
        (continuous_const.prodMk continuous_id)))).neg)

/-- The windowed amplitude of an integrable state is integrable. -/
private lemma integrable_exp_mul {f : E3 → ℂ} (hf : Continuous f)
    (hfs : HasCompactSupport f) (p : E3) :
    Integrable (fun z : E3 => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z) :=
  (hf.integrable_of_hasCompactSupport hfs).bdd_mul
    (continuous_exp_neg_inner p).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => le_of_eq (norm_exp_neg_inner p z)))

/-- The norm of a complexified real number. -/
private lemma norm_ofReal_eq_abs (r : ℝ) : ‖(((r : ℝ)) : ℂ)‖ = |r| := RCLike.norm_ofReal r

/-- `[r−c]₊² ≤ (1+|c|)²(1+r)²` for `r ≥ 0`. -/
private lemma fsKinCoeff_le_mul_sq (c : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    Submission.BoseGases.fsKinCoeff c r ≤ (1 + |c|) ^ 2 * (1 + r) ^ 2 := by
  have h1 : max (r - c) 0 ≤ (1 + |c|) * (1 + r) := by
    refine max_le ?_ ?_
    · have h3 : r + |c| ≤ (1 + |c|) * (1 + r) := by nlinarith [abs_nonneg c, hr]
      have h4 : r - c ≤ r + |c| := by
        have := neg_le_abs c; linarith
      linarith
    · have : (0 : ℝ) ≤ (1 + |c|) * (1 + r) := by positivity
      linarith
  calc Submission.BoseGases.fsKinCoeff c r = (max (r - c) 0) ^ 2 := rfl
    _ ≤ ((1 + |c|) * (1 + r)) ^ 2 := pow_le_pow_left₀ (le_max_right _ _) h1 2
    _ = (1 + |c|) ^ 2 * (1 + r) ^ 2 := by ring

/-- `r^{-6}·r² = r^{-4}`. -/
private lemma rpow_six_mul_sq {r : ℝ} (hr : 0 < r) :
    r ^ (-(6 : ℝ)) * r ^ 2 = r ^ (-(4 : ℝ)) := by
  rw [show r ^ 2 = r ^ (2 : ℝ) by rw [Real.rpow_ofNat]]
  rw [← Real.rpow_add hr]
  norm_num

/-- `(D/r³)² = D²·r^{-6}`. -/
private lemma div_cube_sq_eq_rpow (D r : ℝ) (hr : 0 < r) :
    (D / r ^ 3) ^ 2 = D ^ 2 * r ^ (-(6 : ℝ)) := by
  rw [Real.rpow_neg hr.le, Real.rpow_ofNat, div_pow, div_eq_mul_inv]
  ring

/-- `(2π)⁻³·((2π)³·Y) = Y`. -/
private lemma inv_two_pi_cube_mul (Y : ℝ) :
    (((2 * Real.pi) ^ 3 : ℝ))⁻¹ * ((2 * Real.pi) ^ 3 * Y) = Y := by
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- Absorption of the `(2π)` scaling of the Fourier variable:
`K·(1+r/c)⁻³ ≤ K·c³/(1+r)³` for `K ≥ 0`, `c ≥ 1`, `r ≥ 0`. -/
private lemma zpow_neg_three_le (K c r : ℝ) (hK : 0 ≤ K) (hc : 1 ≤ c) (hr : 0 ≤ r) :
    K * (1 + r / c) ^ (-(3:ℤ)) ≤ K * c ^ 3 / (1 + r) ^ 3 := by
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  have h1r : 0 ≤ 1 + r := by linarith
  have hbase : 0 < 1 + r / c := by positivity
  have hdiv : 1 + r / c = (c + r) / c := by field_simp
  have hexp : (1 + r / c) ^ 3 = (c + r) ^ 3 / c ^ 3 := by rw [hdiv, div_pow]
  have hle : (1 + r) ^ 3 / c ^ 3 ≤ (1 + r / c) ^ 3 := by
    rw [hexp]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ h1r (by linarith) 3) (by positivity)
  have hpos1 : 0 < (1 + r / c) ^ 3 := pow_pos hbase 3
  have hpos2 : 0 < (1 + r) ^ 3 / c ^ 3 := by positivity
  have hinv : ((1 + r / c) ^ 3)⁻¹ ≤ c ^ 3 / (1 + r) ^ 3 := by
    have h := (inv_le_inv₀ hpos1 hpos2).mpr hle
    rwa [inv_div] at h
  have hzpow : (1 + r / c) ^ (-(3:ℤ)) = ((1 + r / c) ^ 3)⁻¹ := by simp [zpow_neg]
  rw [hzpow]
  simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hinv hK

/-! ## 2. The uniform decay of the windowed amplitude -/

/-- **Uniform-in-`u` `(1+‖p‖)⁻³` decay of the windowed amplitude** for a family of windows whose
`C³` data is `u`-independent and a fixed `C³` state with `u`-independent derivative bounds on the
box.  The decay constant is the explicit `C = Cd·(1+Σ|G k|)(1+Σ|Mb k|)(2π)³` of
`Commons.Analysis.Fourier.fourier_decay_mul_update`, hence uniform in `u`. -/
private theorem tBamp_decay_fam {N : ℕ} {a R S : ℝ} (hR : 0 < R) (hRS : R ≤ S)
    (hboxS : ∀ x : X N, x ∈ Submission.BoseGases.abox N a → ∀ j : Fin N, ‖x j‖ ≤ S)
    {χ : E3 → E3 → ℝ} (hχc : ∀ u : E3, ContDiff ℝ 3 (fun z : E3 => (χ u z : ℂ)))
    (hχsupp : ∀ (u z : E3), χ u z ≠ 0 → ‖z‖ ≤ R)
    {G : ℕ → ℝ} (hG : ∀ (u : E3) (k : ℕ), k ≤ 3 → ∀ z : E3,
      ‖iteratedFDeriv ℝ k (fun z : E3 => (χ u z : ℂ)) z‖ ≤ G k)
    {Ψ : X N → ℝ} (hΨc : ContDiff ℝ 3 (fun y : X N => (Ψ y : ℂ)))
    {Mb : ℕ → ℝ} (hMb : ∀ k : ℕ, k ≤ 3 → ∀ y : X N, (∀ j : Fin N, ‖y j‖ ≤ S) →
      ‖iteratedFDeriv ℝ k (fun y : X N => (Ψ y : ℂ)) y‖ ≤ Mb k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : E3) (x : X N), x ∈ Submission.BoseGases.abox N a →
      ∀ (i : Fin N) (p : E3),
      ‖Work.SmallBoxTBWord.tBamp (χ u) p Ψ i x‖ ≤ C / (1 + ‖p‖) ^ 3 := by
  obtain ⟨Cd, hCd0, hCd⟩ := Commons.Analysis.Fourier.fourier_decay_mul_update N R S hR hRS
  have hS1 : 0 ≤ 1 + ∑ k ∈ Finset.range 4, |G k| :=
    add_nonneg zero_le_one (Finset.sum_nonneg fun k _ => abs_nonneg _)
  have hS2 : 0 ≤ 1 + ∑ k ∈ Finset.range 4, |Mb k| :=
    add_nonneg zero_le_one (Finset.sum_nonneg fun k _ => abs_nonneg _)
  refine ⟨Cd * (1 + ∑ k ∈ Finset.range 4, |G k|) * (1 + ∑ k ∈ Finset.range 4, |Mb k|)
      * (2 * Real.pi) ^ 3, by positivity, ?_⟩
  intro u x hx i p
  have hxS : ∀ j : Fin N, ‖x j‖ ≤ S := hboxS x hx
  have hgsupp : ∀ z : E3, (fun z : E3 => (χ u z : ℂ)) z ≠ 0 → ‖z‖ ≤ R := by
    intro z hz; exact hχsupp u z (by simpa using hz)
  have hdec := hCd (fun z : E3 => (χ u z : ℂ)) G (hχc u) hgsupp (hG u)
    (fun y : X N => (Ψ y : ℂ)) Mb hΨc hMb x hxS i ((2 * Real.pi)⁻¹ • p)
  have hconv : Work.SmallBoxTBWord.tBamp (χ u) p Ψ i x
      = Submission.BoseGases.kinFT
          (fun z : E3 => (χ u z : ℂ) * (Ψ (Function.update x i z) : ℂ)) p := by
    rw [Work.SmallBoxTBWord.tBamp, Submission.BoseGases.kinFT]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  rw [hconv, Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
  refine hdec.trans ?_
  have hnorm_xi : ‖(2 * Real.pi)⁻¹ • p‖ = ‖p‖ / (2 * Real.pi) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹),
      inv_mul_eq_div]
  rw [hnorm_xi]
  have hK : 0 ≤ Cd * (1 + ∑ k ∈ Finset.range 4, |G k|) * (1 + ∑ k ∈ Finset.range 4, |Mb k|) :=
    mul_nonneg (mul_nonneg hCd0 hS1) hS2
  have hfin := zpow_neg_three_le
    (Cd * (1 + ∑ k ∈ Finset.range 4, |G k|) * (1 + ∑ k ∈ Finset.range 4, |Mb k|))
    (2 * Real.pi) ‖p‖ hK (by linarith [Real.pi_gt_three]) (norm_nonneg p)
  simpa using hfin

/-! ## 3. Amplitude conversions -/

/-- The windowed amplitude as the Fourier transform of the windowed slot function (the
multiplication form, matching `Commons`' Fourier decay estimate). -/
private lemma tBamp_eq_kinFT_mul {N : ℕ} (χ : E3 → ℝ) (p : E3) (Ψ : X N → ℝ) (i : Fin N)
    (x : X N) :
    Work.SmallBoxTBWord.tBamp χ p Ψ i x
      = Submission.BoseGases.kinFT
          (fun z : E3 => (χ z : ℂ) * (Ψ (Function.update x i z) : ℂ)) p := by
  rw [Work.SmallBoxTBWord.tBamp, Submission.BoseGases.kinFT]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  ring

/-- `kinFT` is additive on integrable states. -/
private lemma kinFT_sub_of_integrable {f g : E3 → ℂ} (hf : Integrable f) (hg : Integrable g)
    (p : E3) :
    Submission.BoseGases.kinFT (f - g) p
      = Submission.BoseGases.kinFT f p - Submission.BoseGases.kinFT g p := by
  have hbdd : ∀ᵐ z ∂(volume : Measure E3),
      ‖Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))‖ ≤ 1 :=
    Filter.Eventually.of_forall fun z => le_of_eq (norm_exp_neg_inner p z)
  have h1 : Integrable (fun z : E3 => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z) :=
    hf.bdd_mul (continuous_exp_neg_inner p).aestronglyMeasurable hbdd
  have h2 : Integrable (fun z : E3 => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * g z) :=
    hg.bdd_mul (continuous_exp_neg_inner p).aestronglyMeasurable hbdd
  rw [Submission.BoseGases.kinFT, Submission.BoseGases.kinFT, Submission.BoseGases.kinFT,
    ← MeasureTheory.integral_sub h1 h2]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.sub_apply]
  ring

/-- `kinFT` is homogeneous in the scalar. -/
private lemma kinFT_const_mul (c : ℂ) (f : E3 → ℂ) (p : E3) :
    Submission.BoseGases.kinFT (fun z : E3 => c * f z) p
      = c * Submission.BoseGases.kinFT f p := by
  rw [Submission.BoseGases.kinFT, Submission.BoseGases.kinFT]
  rw [show (fun z : E3 => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (c * f z))
      = fun z : E3 => c * (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * f z) from by
        funext z; ring]
  rw [MeasureTheory.integral_const_mul]

/-! ## 4. The uniform decay for FS's box projection -/

/-- The box mean does not depend on the slot-`i` coordinate. -/
private lemma boxP_update_eq {N : ℕ} (V : ℝ) (A : Set E3) (i : Fin N) (Φ : X N → ℝ)
    (x : X N) (z : E3) :
    Work.SmallBoxTBWord.boxP V A i Φ (Function.update x i z)
      = Work.SmallBoxTBWord.boxP V A i Φ x := by
  rw [Work.SmallBoxTBWord.boxP, Work.SmallBoxTBWord.boxP]
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with w
  rw [Function.update_idem]

/-- **Uniform-in-`u` decay of the amplitude of FS's box projection.**  The window is the sliding
cube cutoff `chiSmallB M ℓ d u`, the state is `Q_{B(u),i}Φ` with the box indicator (`boxQInd`).
The constant is uniform in `u`. -/
private lemma tBamp_boxQInd_decay {M : ℕ} (hM : 4 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {N : ℕ} {Φ : X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : E3) (x : X N), x ∈ Submission.BoseGases.abox N ℓ →
      ∀ (i : Fin N) (p : E3),
      ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ≤ C / (1 + ‖p‖) ^ 3 := by
  obtain ⟨hχc, R, G, hRpos, hGnn, hχsupp, hG⟩ := chiSmallB_bounds3 (M := M) hM hℓ hd
  have hSnn : 0 ≤ max R (3 * ℓ) := le_trans (le_of_lt hRpos) (le_max_left _ _)
  have hboxS : ∀ x : X N, x ∈ Submission.BoseGases.abox N ℓ →
      ∀ j : Fin N, ‖x j‖ ≤ max R (3 * ℓ) :=
    fun x hx j => le_trans (norm_coord_abox hℓ hx j) (le_max_right _ _)
  -- the state `Φ`
  have hΦc : ContDiff ℝ 3 (fun y : X N => (Φ y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hΦ.of_le (WithTop.coe_le_coe.mpr le_top))
  obtain ⟨Mb, hMbnn, hMb⟩ :=
    Work.SmallBoxTBWord.complexified_iteratedFDeriv_bound (N := N) (S := max R (3 * ℓ)) hSnn hΦ
  obtain ⟨CΦ, hCΦ0, hCΦ⟩ := tBamp_decay_fam (a := ℓ) (R := R) (S := max R (3 * ℓ))
    hRpos (le_max_left _ _) hboxS hχc hχsupp hG hΦc hMb
  -- the constant state
  have h1c : ContDiff ℝ 3 (fun y : X N => (((1 : ℝ)) : ℂ)) := contDiff_const
  obtain ⟨M1, hM1nn, hM1⟩ :=
    Work.SmallBoxTBWord.complexified_iteratedFDeriv_bound (N := N) (S := max R (3 * ℓ)) hSnn
      (Φ := fun _ : X N => (1 : ℝ)) contDiff_const
  obtain ⟨C1, hC10, hC1⟩ := tBamp_decay_fam (a := ℓ) (R := R) (S := max R (3 * ℓ))
    hRpos (le_max_left _ _) hboxS hχc hχsupp hG h1c hM1
  -- the box mean is bounded by a bound on the state
  obtain ⟨MΦ, hMΦ0, hMΦ⟩ := Work.BoseFixB1.exists_bound_abox_pos (N := N) (ℓ := ℓ) hℓ hΦ.continuous
  refine ⟨CΦ + MΦ * C1, by positivity, fun u x hx i p => ?_⟩
  set V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
  set A : Set E3 := Submission.BoseGases.dlBox ℓ d u with hAdef
  set m : ℝ := Work.SmallBoxTBWord.boxP V A i Φ x with hmdef
  have hχsupp' : ∀ z : E3, z ∉ A → Submission.BoseGases.chiSmallB M ℓ d u z = 0 :=
    fun z hz =>
      Work.BoseFixB1S.win.chiSmallB_eq_zero_of_not_mem_dlBox (M := M) (by omega) hℓ hd u z hz
  -- ## the mean bound
  have hVnn : 0 ≤ V := by
    rw [hVdef, Work.SmallBoxSliding.boxMass_eq_measureReal]
    exact MeasureTheory.measureReal_nonneg
  have hVreal : V = (volume : Measure E3).real A := by
    rw [hVdef, hAdef, Work.SmallBoxSliding.boxMass_eq_measureReal]
  have hAsub : A ⊆ Submission.BoseGases.acube ℓ := by
    rw [hAdef]; exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hmeanz : |m| ≤ MΦ := by
    have hfin : (volume : Measure E3) A < ⊤ :=
      lt_of_le_of_lt (measure_mono hAsub) (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
    have hI : |∫ z in A, Φ (Function.update x i z)| ≤ MΦ * V := by
      have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (f := fun z : E3 => Φ (Function.update x i z)) (C := MΦ) hfin
        (fun z hz => by
          rw [Real.norm_eq_abs]
          exact hMΦ _ (update_mem_abox hAsub hx hz i))
      rwa [← hVreal] at h
    have hm_eq : m = (1 / V) * ∫ z in A, Φ (Function.update x i z) := by
      rw [hmdef, Work.SmallBoxTBWord.boxP]
    calc |m| = |(1 / V) * ∫ z in A, Φ (Function.update x i z)| := by rw [hm_eq]
      _ = |(1 / V)| * |∫ z in A, Φ (Function.update x i z)| := by rw [abs_mul]
      _ ≤ |(1 / V)| * (MΦ * V) := mul_le_mul_of_nonneg_left hI (abs_nonneg _)
      _ = (|(1 / V)| * V) * MΦ := by ring
      _ ≤ 1 * MΦ := by
          refine mul_le_mul_of_nonneg_right ?_ hMΦ0
          rcases eq_or_lt_of_le hVnn with h | h
          · rw [← h]; norm_num
          · rw [abs_of_pos (by positivity)]
            field_simp
            exact le_refl 1
      _ = MΦ := one_mul _
  -- ## the splitting of the amplitude
  have hχcs : HasCompactSupport (Submission.BoseGases.chiSmallB M ℓ d u) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : E3) (ℓ / 2)) ?_
    intro z hz
    rw [Function.mem_support] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact chiSmallB3_support_radius (M := M) (by omega) hℓ hd u hz
  have hχcont : Continuous (Submission.BoseGases.chiSmallB M ℓ d u) := by
    have h1 : Continuous (Submission.BoseGases.chiScale ℓ) :=
      Submission.BoseGases.chi_contDiff.continuous.comp (by fun_prop)
    have h2 : Continuous
        (fun x : E3 => Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) :=
      (Submission.BoseGases.chiSmall_continuous (by omega)).comp (by fun_prop)
    exact h1.mul h2
  have hFcont : Continuous (fun z : E3 =>
      (Submission.BoseGases.chiSmallB M ℓ d u z : ℂ) * (Φ (Function.update x i z) : ℂ)) :=
    (Complex.continuous_ofReal.comp hχcont).mul
      (Complex.continuous_ofReal.comp
        (hΦ.continuous.comp (continuous_const.update i continuous_id)))
  have hFcs : HasCompactSupport (fun z : E3 =>
      (Submission.BoseGases.chiSmallB M ℓ d u z : ℂ) * (Φ (Function.update x i z) : ℂ)) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : E3) (ℓ / 2)) ?_
    intro z hz
    rw [Function.mem_support] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hcon
    have hz0 : Submission.BoseGases.chiSmallB M ℓ d u z = 0 := by
      by_contra hne
      exact hcon (chiSmallB3_support_radius (M := M) (by omega) hℓ hd u hne)
    exact hz (by rw [hz0]; simp)
  have hFi : Integrable (fun z : E3 =>
      (Submission.BoseGases.chiSmallB M ℓ d u z : ℂ) * (Φ (Function.update x i z) : ℂ)) :=
    hFcont.integrable_of_hasCompactSupport hFcs
  have hGcont : Continuous (fun z : E3 =>
      ((m : ℝ) : ℂ) * ((Submission.BoseGases.chiSmallB M ℓ d u z : ℂ) * ((1 : ℝ) : ℂ))) :=
    continuous_const.mul
      ((Complex.continuous_ofReal.comp hχcont).mul continuous_const)
  have hGcs : HasCompactSupport (fun z : E3 =>
      ((m : ℝ) : ℂ) * ((Submission.BoseGases.chiSmallB M ℓ d u z : ℂ) * ((1 : ℝ) : ℂ))) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : E3) (ℓ / 2)) ?_
    intro z hz
    rw [Function.mem_support] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hcon
    have hz0 : Submission.BoseGases.chiSmallB M ℓ d u z = 0 := by
      by_contra hne
      exact hcon (chiSmallB3_support_radius (M := M) (by omega) hℓ hd u hne)
    exact hz (by rw [hz0]; simp)
  have hGi : Integrable (fun z : E3 =>
      ((m : ℝ) : ℂ) * ((Submission.BoseGases.chiSmallB M ℓ d u z : ℂ) * ((1 : ℝ) : ℂ))) :=
    hGcont.integrable_of_hasCompactSupport hGcs
  have hkey : Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
        (Work.UBBInputs8.boxQInd V A i Φ) i x
      = Submission.BoseGases.kinFT (fun z : E3 =>
          (Submission.BoseGases.chiSmallB M ℓ d u z : ℂ) * ((Φ (Function.update x i z) - m : ℝ) : ℂ)) p := by
    rw [Work.BoseFixB1.SectorAux.tBamp_boxQInd_eq_kinFT_boxQ (V := V) (A := A) hχsupp' i Φ p x]
    congr 1
    funext z
    rw [Work.SmallBoxTBWord.boxQ, boxP_update_eq V A i Φ x z]
    simp only [← hmdef, Complex.ofReal_mul, Complex.ofReal_sub]
  have hsplit : Submission.BoseGases.kinFT (fun z : E3 =>
        (Submission.BoseGases.chiSmallB M ℓ d u z : ℂ) * ((Φ (Function.update x i z) - m : ℝ) : ℂ)) p
      = Submission.BoseGases.kinFT (fun z : E3 =>
          (Submission.BoseGases.chiSmallB M ℓ d u z : ℂ) * (Φ (Function.update x i z) : ℂ)) p
        - ((m : ℝ) : ℂ) * Submission.BoseGases.kinFT (fun z : E3 =>
            (Submission.BoseGases.chiSmallB M ℓ d u z : ℂ) * ((1 : ℝ) : ℂ)) p := by
    have heq : (fun z : E3 =>
          (Submission.BoseGases.chiSmallB M ℓ d u z : ℂ) * ((Φ (Function.update x i z) - m : ℝ) : ℂ))
        = (fun z : E3 =>
            (Submission.BoseGases.chiSmallB M ℓ d u z : ℂ) * (Φ (Function.update x i z) : ℂ))
          - (fun z : E3 =>
              ((m : ℝ) : ℂ) * ((Submission.BoseGases.chiSmallB M ℓ d u z : ℂ) * ((1 : ℝ) : ℂ))) := by
      funext z
      simp only [Pi.sub_apply]
      push_cast
      ring
    rw [heq, kinFT_sub_of_integrable hFi hGi p, kinFT_const_mul]
  -- ## the conclusion
  have hf1 : ‖Submission.BoseGases.kinFT (fun z : E3 =>
        (Submission.BoseGases.chiSmallB M ℓ d u z : ℂ) * (Φ (Function.update x i z) : ℂ)) p‖
      ≤ CΦ / (1 + ‖p‖) ^ 3 := by
    rw [← tBamp_eq_kinFT_mul (Submission.BoseGases.chiSmallB M ℓ d u) p Φ i x]
    exact hCΦ u x hx i p
  have hf2 : ‖Submission.BoseGases.kinFT (fun z : E3 =>
        (Submission.BoseGases.chiSmallB M ℓ d u z : ℂ) * ((1 : ℝ) : ℂ)) p‖
      ≤ C1 / (1 + ‖p‖) ^ 3 := by
    rw [← tBamp_eq_kinFT_mul (Submission.BoseGases.chiSmallB M ℓ d u) p
      (fun _ : X N => (1 : ℝ)) i x]
    exact hC1 u x hx i p
  have hden : 0 < (1 + ‖p‖) ^ 3 := by positivity
  calc ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
          (Work.UBBInputs8.boxQInd V A i Φ) i x‖
      = ‖Submission.BoseGases.kinFT (fun z : E3 =>
          (Submission.BoseGases.chiSmallB M ℓ d u z : ℂ) * ((Φ (Function.update x i z) - m : ℝ) : ℂ)) p‖ := by
        rw [hkey]
    _ = ‖Submission.BoseGases.kinFT (fun z : E3 =>
          (Submission.BoseGases.chiSmallB M ℓ d u z : ℂ) * (Φ (Function.update x i z) : ℂ)) p
        - ((m : ℝ) : ℂ) * Submission.BoseGases.kinFT (fun z : E3 =>
            (Submission.BoseGases.chiSmallB M ℓ d u z : ℂ) * ((1 : ℝ) : ℂ)) p‖ := by
        rw [hsplit]
    _ ≤ CΦ / (1 + ‖p‖) ^ 3 + |m| * (C1 / (1 + ‖p‖) ^ 3) := by
        refine (norm_sub_le _ _).trans ?_
        refine add_le_add hf1 ?_
        rw [norm_mul, norm_ofReal_eq_abs]
        exact mul_le_mul_of_nonneg_left hf2 (abs_nonneg _)
    _ ≤ CΦ / (1 + ‖p‖) ^ 3 + MΦ * (C1 / (1 + ‖p‖) ^ 3) := by
        have hC1d : 0 ≤ C1 / (1 + ‖p‖) ^ 3 := div_nonneg hC10 hden.le
        exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hmeanz hC1d)
    _ = (CΦ + MΦ * C1) / (1 + ‖p‖) ^ 3 := by
        rw [← mul_div_assoc]
        exact (add_div CΦ (MΦ * C1) ((1 + ‖p‖) ^ 3)).symm

/-! ## 5. The arithmetic of the `p`-integral -/

/-- **The per-slot bound.**  Given the uniform `(1+‖p‖)⁻³` decay of the box-projected amplitude
(with constant `C`), the `p`-integral of one slot of the sliding cube spectral form is bounded by
`(2π)³·(1+|c|)²C²(ℓ³)⁻¹(ℓ³)^N·∫(1+‖p‖)⁻⁴`. -/
private lemma slot_bound {M : ℕ} {ℓ d c : ℝ} (hℓ : 0 < ℓ)
    {N : ℕ} {Φ : X N → ℝ} {C : ℝ}
    (hC : ∀ (u : E3) (x : X N), x ∈ Submission.BoseGases.abox N ℓ → ∀ (i : Fin N) (p : E3),
      ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ≤ C / (1 + ‖p‖) ^ 3)
    (u : E3) (i : Fin N) :
    ∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2)
      ≤ (2 * Real.pi) ^ 3 * (((1 + |c|) ^ 2 * C ^ 2 * (ℓ ^ 3)⁻¹ * (ℓ ^ 3) ^ N)
          * ∫ p : E3, (1 + ‖p‖) ^ (-(4 : ℝ))) := by
  classical
  haveI : IsFiniteMeasure ((volume : Measure (X N)).restrict (Submission.BoseGases.abox N ℓ)) :=
    ⟨by
      rw [Measure.restrict_apply_univ, Submission.BoseGases.abox_volume N ℓ hℓ.le]
      exact ENNReal.ofReal_lt_top⟩
  have hvol : (volume : Measure (X N)).real (Submission.BoseGases.abox N ℓ) = (ℓ ^ 3) ^ N := by
    rw [Measure.real_def, Submission.BoseGases.abox_volume N ℓ hℓ.le, ENNReal.toReal_ofReal]
    positivity
  have hℓ3 : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
  -- ## step 1: the `x`-integral
  have hxin : ∀ p : E3, ∫ x in Submission.BoseGases.abox N ℓ,
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2
      ≤ (C / (1 + ‖p‖) ^ 3) ^ 2 * (ℓ ^ 3) ^ N := by
    intro p
    have h1 : ∫ x in Submission.BoseGases.abox N ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2
        ≤ ∫ _x in Submission.BoseGases.abox N ℓ, (C / (1 + ‖p‖) ^ 3) ^ 2 := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
        (integrable_const _) ?_
      have hae : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox N ℓ)),
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2 ≤ (C / (1 + ‖p‖) ^ 3) ^ 2 := by
        rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
        exact Filter.Eventually.of_forall fun x hx =>
          pow_le_pow_left₀ (norm_nonneg _) (hC u x hx i p) 2
      exact hae
    refine h1.trans (le_of_eq ?_)
    rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul]
    ring
  -- ## step 2: the `p`-integrand
  have hpbound : ∀ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2)
      ≤ ((1 + |c|) ^ 2 * C ^ 2 * (ℓ ^ 3)⁻¹ * (ℓ ^ 3) ^ N) * (1 + ‖p‖) ^ (-(4 : ℝ)) := by
    intro p
    have h1 : Submission.BoseGases.fsKinCoeff c ‖p‖ ≤ (1 + |c|) ^ 2 * (1 + ‖p‖) ^ 2 :=
      fsKinCoeff_le_mul_sq c (norm_nonneg p)
    have h2 : ∫ x in Submission.BoseGases.abox N ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2
        ≤ C ^ 2 * (1 + ‖p‖) ^ (-(6 : ℝ)) * (ℓ ^ 3) ^ N := by
      have h := hxin p
      rwa [div_cube_sq_eq_rpow C (1 + ‖p‖) (by positivity)] at h
    have h3 : 0 ≤ ∫ x in Submission.BoseGases.abox N ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2 :=
      integral_nonneg fun x => sq_nonneg _
    calc Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N ℓ,
            ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2)
        ≤ ((1 + |c|) ^ 2 * (1 + ‖p‖) ^ 2) *
            ((ℓ ^ 3)⁻¹ * (C ^ 2 * (1 + ‖p‖) ^ (-(6 : ℝ)) * (ℓ ^ 3) ^ N)) := by
          refine mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hℓ3)
            (mul_nonneg hℓ3 h3) (by positivity)
      _ = ((1 + |c|) ^ 2 * C ^ 2 * (ℓ ^ 3)⁻¹ * (ℓ ^ 3) ^ N) * (1 + ‖p‖) ^ (-(4 : ℝ)) := by
          rw [← rpow_six_mul_sq (r := 1 + ‖p‖) (by positivity)]
          ring
  -- ## step 3: the `p`-integral
  have hKc : 0 ≤ ((1 + |c|) ^ 2 * C ^ 2 * (ℓ ^ 3)⁻¹ * (ℓ ^ 3) ^ N) *
      ∫ p : E3, (1 + ‖p‖) ^ (-(4 : ℝ)) := by
    refine mul_nonneg ?_ (integral_nonneg fun p => Real.rpow_nonneg (by positivity) _)
    positivity
  have hintg : Integrable (fun p : E3 =>
      ((1 + |c|) ^ 2 * C ^ 2 * (ℓ ^ 3)⁻¹ * (ℓ ^ 3) ^ N) * (1 + ‖p‖) ^ (-(4 : ℝ))) :=
    (integrable_one_add_norm (E := E3) (μ := volume) (r := 4)
      (by rw [finrank_euclideanSpace, Fintype.card_fin]; norm_num)).const_mul _
  have hmain := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun p =>
      mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖)
        (mul_nonneg hℓ3 (integral_nonneg fun x => sq_nonneg _)))
    hintg (Filter.Eventually.of_forall hpbound)
  have h2pi : (1 : ℝ) ≤ (2 * Real.pi) ^ 3 := by
    have h1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    calc (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ (2 * Real.pi) ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
  calc ∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2)
      ≤ ∫ p : E3, ((1 + |c|) ^ 2 * C ^ 2 * (ℓ ^ 3)⁻¹ * (ℓ ^ 3) ^ N)
          * (1 + ‖p‖) ^ (-(4 : ℝ)) := hmain
    _ = ((1 + |c|) ^ 2 * C ^ 2 * (ℓ ^ 3)⁻¹ * (ℓ ^ 3) ^ N)
          * ∫ p : E3, (1 + ‖p‖) ^ (-(4 : ℝ)) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ (2 * Real.pi) ^ 3 * (((1 + |c|) ^ 2 * C ^ 2 * (ℓ ^ 3)⁻¹ * (ℓ ^ 3) ^ N)
          * ∫ p : E3, (1 + ‖p‖) ^ (-(4 : ℝ))) := le_mul_of_one_le_left hKc h2pi

/-! ## 6. The target -/

theorem cubeSpectral_uniformBound {M : ℕ} (hM : 4 ≤ M) {ℓ d c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : EuclideanSpace ℝ (Fin 3),
      Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u) c Φ
        ≤ K := by
  obtain ⟨C, hC0, hC⟩ := tBamp_boxQInd_decay (M := M) hM hℓ hd (N := N) (Φ := Φ) hΦ
  refine ⟨max 0 ((N : ℝ) * (((1 + |c|) ^ 2 * C ^ 2 * (ℓ ^ 3)⁻¹ * (ℓ ^ 3) ^ N)
      * ∫ p : E3, (1 + ‖p‖) ^ (-(4 : ℝ)))), le_max_left _ _, ?_⟩
  intro u
  rw [Work.UBBInputs8.tBwordKinInd, Work.UBBInputs8.tBdiagFormInd]
  calc ∑ i : Fin N, ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2)
      ≤ ∑ _i : Fin N, ((2 * Real.pi) ^ 3)⁻¹ * ((2 * Real.pi) ^ 3 *
          (((1 + |c|) ^ 2 * C ^ 2 * (ℓ ^ 3)⁻¹ * (ℓ ^ 3) ^ N)
            * ∫ p : E3, (1 + ‖p‖) ^ (-(4 : ℝ)))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_left (slot_bound hℓ hC u i) (by positivity)
    _ = (N : ℝ) * (((1 + |c|) ^ 2 * C ^ 2 * (ℓ ^ 3)⁻¹ * (ℓ ^ 3) ^ N)
          * ∫ p : E3, (1 + ‖p‖) ^ (-(4 : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          inv_two_pi_cube_mul]
    _ ≤ max 0 ((N : ℝ) * (((1 + |c|) ^ 2 * C ^ 2 * (ℓ ^ 3)⁻¹ * (ℓ ^ 3) ^ N)
          * ∫ p : E3, (1 + ‖p‖) ^ (-(4 : ℝ)))) := le_max_right _ _

end

end Work.BoseFixB1S
