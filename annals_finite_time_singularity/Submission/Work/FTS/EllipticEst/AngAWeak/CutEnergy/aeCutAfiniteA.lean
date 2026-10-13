import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemGradUD

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak.AeCutA

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

/-!
# `AeCutAfinite` — finiteness of the cut-off radial `L²`-norm of `∂_z u`

For a datum `AeData α u G` of the almost-everywhere class of the level-`0` elliptic estimate
and a cut-off `φ ∈ C²` with compact support contained in `(0,∞)` and `0 ≤ φ ≤ 1`, the
hypothesis

`∫⁻ z in Iz, ofReal (φ z * w z ^ 2) * (∫⁻ θ in Iθ, ofReal (u z θ ^ 2)) ≠ ⊤`

is turned into

`∫⁻ z in Iz, ofReal (φ z * w z ^ 2 * z ^ 2) * (∫⁻ θ in Iθ, ofReal ((∂_z u z θ) ^ 2)) ≠ ⊤`,

i.e. the *radial first derivative* of `u` is square-integrable against `φ w² z²`.

## Route

The work is done by the radial Agmon–Nirenberg interpolation of the tree,
`Work.FTS.EllipticEst.H2W.Ae.hkMem_gradU`: for `AeData α u G` the level-`0` `ℋ`-membership
`HkMem α 0 (D_z u)` of `D_z u = z ∂_z u` holds.  Unfolding `HkMem` at `k = 0` it says
exactly that

`A z := ∫_θ (z ∂_z u z θ * w z / sin(2θ)^{η/2})²`

is integrable in `z`, which by `ofReal_integral_eq_lintegral_ofReal` makes
`∫⁻ z, ofReal (A z) ≠ ⊤`.

The desired integral is dominated by this one: the only point is the *pointwise* bound (for
`θ ∈ (0,π/2)`, where `0 < sin(2θ) ≤ 1`)

`φ z * w z ² * z ² * (∂_z u z θ)² ≤ (z ∂_z u z θ * w z / sin(2θ)^{η/2})²`,

which is `φ z ≤ sin(2θ)^{-η}` multiplied by the nonnegative factor `w z ² * z ² *
(∂_z u z θ)²` (`φ z ≤ 1 ≤ sin(2θ)^{-η}`, and `sin(2θ)^{-η}` is exactly the square of the
angular part of the `ℋ⁰`-weight).  Pulling the constant `ofReal (φ z w z ² z ²)` inside the
`θ`-lintegral (`lintegral_const_mul'`, `ofReal_mul`) and integrating the resulting a.e.
pointwise bound over `θ` gives the claim.
-/

/-- The square of the angular factor `w / sin(2θ)^{η/2}` of the `ℋ⁰`-weight, written with a
single `rpow`: `(w / s^{η/2})² = w² s^{-η}` for `s ≥ 0`. -/
private lemma sinRpow_div_sq (w s : ℝ) (hs : 0 ≤ s) (η : ℝ) :
    (w / s ^ (η / 2)) ^ 2 = w ^ 2 * s ^ (-η) := by
  have h2 : (s ^ (η / 2)) ^ 2 = s ^ η := by
    rw [← Real.rpow_natCast (x := s ^ (η / 2)) (n := 2)]
    rw [← Real.rpow_mul (x := s) hs (η / 2) ((2 : ℕ) : ℝ)]
    norm_num
  rw [div_pow, h2, Real.rpow_neg hs]
  ring

/-- Almost every `θ ∈ Iθ = [0,π/2]` lies in the *open* interval `(0,π/2)` (the complement is
the two-point set `{0, π/2}`). -/
private lemma ae_mem_Ioo_of_Iθ_restrict :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  change ∀ᵐ θ ∂(volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))),
    θ ∈ Set.Ioo 0 (Real.pi / 2)
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  rw [MeasureTheory.ae_iff]
  have hsub : {θ : ℝ | ¬ (θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) →
      θ ∈ Set.Ioo 0 (Real.pi / 2))} ⊆ ({0, Real.pi / 2} : Set ℝ) := by
    intro θ hθ
    obtain ⟨h1, h2⟩ := not_imp.mp hθ
    rw [Set.mem_Icc] at h1
    rw [Set.mem_Ioo] at h2
    have hθeq : θ = 0 ∨ θ = Real.pi / 2 := by
      by_cases h : θ ≤ 0
      · exact Or.inl (le_antisymm h h1.1)
      · refine Or.inr (le_antisymm h1.2 ?_)
        by_contra hge
        exact h2 ⟨lt_of_not_ge h, lt_of_not_ge hge⟩
    rcases hθeq with h | h <;> simp [h]
  refine measure_mono_null hsub ?_
  exact (Set.Finite.insert 0 (Set.finite_singleton (Real.pi / 2))).measure_zero volume

/-- The pointwise domination of the cut-off radial integrand by the `ℋ⁰`-integrand of
`D_z u = z ∂_z u`, on the *open* angular interval: for `0 ≤ φ ≤ 1` and
`θ ∈ (0,π/2)`,

`φ z * w z ² * z ² * (∂_z u z θ)² ≤ (z ∂_z u z θ * w z / sin(2θ)^{η/2})²`
`  = HkIntegrand α 0 (grad u) z θ`.

(`HkIntegrand α 0 f z θ` is the single term `(f z θ * w z / sin(2θ)^{η/2})²`.) -/
private lemma hkIntegrand_weight_le (φ : ℝ → ℝ) (hφ1 : ∀ z, φ z ≤ 1) (u : ℝ → ℝ → ℝ)
    (α z θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    φ z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsr : 1 ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
    have h : (1 : ℝ) ^ (-Work.Spaces.eta) ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
      Real.rpow_le_rpow_of_nonpos hs hs1 (by have := Work.Spaces.eta_pos; linarith)
    simpa using h
  have hhk : Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
      = ((z * Work.Spaces.pz u z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    simp [Work.Spaces.HkIntegrand, Work.FTS.EllipticEst.H2W.Ae.grad]
  rw [hhk, mul_pow,
    sinRpow_div_sq (Work.Spaces.w z) (Real.sin (2 * θ)) hs.le Work.Spaces.eta]
  have hX : 0 ≤ (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2 := by positivity
  calc φ z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2
      = φ z * ((Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2) := by ring
    _ ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
          * ((Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2) :=
        mul_le_mul_of_nonneg_right (le_trans (hφ1 z) hsr) hX
    _ = (z * Work.Spaces.pz u z θ) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by ring

theorem aeCutAfiniteA (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (φ : ℝ → ℝ) (hφsm : ContDiff ℝ 2 φ) (hcpt : HasCompactSupport φ)
    (hφ0 : ∀ z : ℝ, z ≤ 0 → φ z = 0) (hφnn : ∀ z : ℝ, 0 ≤ φ z) (hφ1 : ∀ z : ℝ, φ z ≤ 1)
    (hM : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))) ≠ ⊤) :
    (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2))) ≠ ⊤ := by
  -- The radial Agmon--Nirenberg certificate: `D_z u = z ∂_z u` is `ℋ⁰`, i.e. the weighted
  -- square of `z ∂_z u` is jointly integrable.
  obtain ⟨hsl, hzint⟩ := Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h
  -- The desired lintegral is dominated by the (finite) `ℋ⁰`-lintegral of `grad u`.
  have hKey : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2)))
      ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
            (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    have hAz : MeasureTheory.Integrable
        (fun θ => Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ)
        (volume.restrict Work.Spaces.Iθ) := (hsl z hz).integrable
    have hA0 : 0 ≤ φ z * (Work.Spaces.w z) ^ 2 * z ^ 2 :=
      mul_nonneg (mul_nonneg (hφnn z) (sq_nonneg _)) (sq_nonneg _)
    calc ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2))
        = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)
            * ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2) := by
          rw [← MeasureTheory.lintegral_const_mul'
            (ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2 * z ^ 2))
            (fun θ => ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2)) ENNReal.ofReal_ne_top]
      _ = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
            (φ z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2) := by
          refine MeasureTheory.lintegral_congr (fun θ => ?_)
          rw [← ENNReal.ofReal_mul hA0]
      _ ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
            (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ) := by
          refine MeasureTheory.lintegral_mono_ae ?_
          filter_upwards [ae_mem_Ioo_of_Iθ_restrict] with θ hθ
          exact ENNReal.ofReal_le_ofReal (hkIntegrand_weight_le φ hφ1 u α z θ hθ)
      _ = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
            (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ) := by
          rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            (μ := volume.restrict Work.Spaces.Iθ) hAz
            (Filter.Eventually.of_forall fun θ =>
              Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)]
  refine ne_top_of_le_ne_top ?_ hKey
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hzint.integrable)
      (Filter.Eventually.of_forall fun z => integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)]
  exact ENNReal.ofReal_ne_top

end Work.FTS.EllipticEst.AngAWeak.AeCutA
