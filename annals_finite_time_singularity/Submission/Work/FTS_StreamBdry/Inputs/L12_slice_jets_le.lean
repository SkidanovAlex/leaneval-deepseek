import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_StreamBdry.Inputs

set_option maxHeartbeats 800000

/-! ## Auxiliary bounds for `L12_slice_jets_le`

The target is the *uniform* bound, for all `z > 0`, on the iterated radial jets
`D_z^k (L₁₂ h)(z)`, `k ≤ 3`, of a datum `h` which is `C⁴` on the open quadrant, obeys the
standing pointwise bound `JetBnd Cw h` (`|mixed b a h| ≤ Cw · z^{3/2}/(1+z)²`, `a + b ≤ 2`)
and whose radial majorant `∫_{s>z} s^{1/2}/(1+s)²` is bounded by `Cmaj`.

The proof uses the *angular-moment tower* of `RXT.L12Iter` / `RXT.Slots.v2_Mine`:

* `D_z^j (L₁₂ h)(z) = L12jet h j z`, which is `L₁₂ h z` for `j = 0` and `-Qang h (j-1) z`
  for `j ≥ 1`, `Qang h k z = ∫_θ K(θ) D_z^k h (z,θ) dθ`;
* `|Qang h k z| ≤ 3 (π/2) (Cw · Rwt z)` for `k ≤ 2` (the `θ`-integral of the pointwise
  bound, with `K ≤ 3` and `λ(Iθ) = π/2`);
* `|L₁₂ h z| ≤ ∫_{s>z} |L12dens h s| ≤ 3 (π/2) Cw ∫_{s>z} s^{1/2}/(1+s)² ≤ 3 (π/2) Cw Cmaj`.

Since `Rwt z ≤ 1` for `z ≥ 0`, the four jets are uniformly bounded by
`3 (π/2) Cw · max Cmaj 1`. -/

/-- The radial weight `Rwt z = z^{3/2}/(1+z)²` of the standing bound is `≤ 1` for `z ≥ 0`. -/
private theorem Rwt_le_one {z : ℝ} (hz : 0 ≤ z) :
    Work.FTS_RegExport.RXT.L12Iter.Rwt z ≤ 1 := by
  rw [Work.FTS_RegExport.RXT.L12Iter.Rwt, div_le_one (by positivity)]
  calc z ^ ((3 : ℝ) / 2) ≤ (1 + z) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow hz (by linarith) (by norm_num)
    _ ≤ (1 + z) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ = (1 + z) ^ 2 := by rw [Real.rpow_two]

/-- The angular moment at level `k ≤ 2`, bounded by the `θ`-integral of the standing bound
(`K ≤ 3` pointwise and `λ(Iθ) = π/2`). -/
private theorem abs_Qang_le_two {C0 : ℝ} (hC0 : 0 ≤ C0) {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * Work.FTS_RegExport.RXT.L12Iter.Rwt z)
    {k : ℕ} (hk : k ≤ 2) {z : ℝ} (hz : 0 < z) :
    |Work.Elliptic.Qang f k z| ≤ 3 * (Real.pi / 2) * (C0 * Work.FTS_RegExport.RXT.L12Iter.Rwt z) := by
  have hint := Work.FTS_RegExport.RXT.L12Iter.integrable_Ktheta_mul_DzIter hC0 h4 hbd hk hz
  have hbnd := Work.FTS_RegExport.RXT.L12Iter.abs_Ktheta_mul_DzIter_le hC0 hbd hk hz
  have h1 : ‖Work.Elliptic.Qang f k z‖
      ≤ ∫ θ in Work.Spaces.Iθ, ‖Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f z θ‖ := by
    rw [Work.Elliptic.Qang]
    exact MeasureTheory.norm_integral_le_integral_norm _
  have h2 : (∫ θ in Work.Spaces.Iθ, ‖Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f z θ‖)
      ≤ ∫ θ in Work.Spaces.Iθ, (3 * (C0 * Work.FTS_RegExport.RXT.L12Iter.Rwt z)) :=
    MeasureTheory.integral_mono_ae hint.norm (MeasureTheory.integrable_const _) hbnd
  have h3 : (∫ θ in Work.Spaces.Iθ, (3 * (C0 * Work.FTS_RegExport.RXT.L12Iter.Rwt z)))
      = 3 * (Real.pi / 2) * (C0 * Work.FTS_RegExport.RXT.L12Iter.Rwt z) := by
    rw [Work.Elliptic.integral_Iθ_eq_interval, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  rw [Real.norm_eq_abs] at h1
  linarith [h1, h2, le_of_eq h3]

/-- The base jet: `|L₁₂ h z| ≤ 3 (π/2) Cw Cmaj`, by dominated convergence in the radial
variable against the majorant `s^{1/2}/(1+s)²`. -/
private theorem abs_L12_le {C0 Cmaj : ℝ} (hC0 : 0 ≤ C0) {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * Work.FTS_RegExport.RXT.L12Iter.Rwt z)
    (hmaj : ∀ z : ℝ, 0 < z →
      ∫ s in Set.Ioi z, s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 ≤ Cmaj)
    {z : ℝ} (hz : 0 < z) :
    |Work.Construction.L12 f z| ≤ 3 * (Real.pi / 2) * C0 * Cmaj := by
  have hint : Integrable (Work.FM.L12dens Work.Spaces.K f) (volume.restrict (Set.Ioi z)) :=
    Work.FTS_RegExport.RXT.L12Iter.L12dens_integrableOn hC0 h4 hbd hz
  have h1 : ‖Work.Construction.L12 f z‖
      ≤ ∫ s in Set.Ioi z, ‖Work.FM.L12dens Work.Spaces.K f s‖ := by
    show ‖∫ s in Set.Ioi z, Work.FM.L12dens Work.Spaces.K f s‖ ≤ _
    exact MeasureTheory.norm_integral_le_integral_norm _
  have h2 : (∫ s in Set.Ioi z, ‖Work.FM.L12dens Work.Spaces.K f s‖)
      ≤ ∫ s in Set.Ioi z, 3 * (Real.pi / 2) * C0
          * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) := by
    refine MeasureTheory.integral_mono_ae hint.norm
      ((Work.FTS_RegExport.RXT.L12Iter.integrable_majorant hz).const_mul _) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs]
    exact Work.FTS_RegExport.RXT.L12Iter.abs_L12dens_le hC0 h4 hbd (lt_trans hz hs)
  have h3 : (∫ s in Set.Ioi z, 3 * (Real.pi / 2) * C0
        * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2))
      = 3 * (Real.pi / 2) * C0 * ∫ s in Set.Ioi z, s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 :=
    MeasureTheory.integral_const_mul _ _
  have h4' : 3 * (Real.pi / 2) * C0 * ∫ s in Set.Ioi z, s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2
      ≤ 3 * (Real.pi / 2) * C0 * Cmaj :=
    mul_le_mul_of_nonneg_left (hmaj z hz) (by positivity)
  rw [Real.norm_eq_abs] at h1
  linarith [h1, h2, le_of_eq h3, h4']

/-- **The angular-moment tower specialised to a `JetBnd` datum.**  For `k ≤ 3` and `z > 0`
the radial jet `D_z^k (L₁₂ h)(z)` (with the `θ`-variable set to `0`, as in the statement)
equals `L12jet h k z`. -/
private theorem DzIter_L12_eq_L12jet {Cw : ℝ} (hCw : 0 ≤ Cw) {h : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    (hJet : Work.FTS_RegExport.RXT.Slots.JetBnd Cw h)
    (hcontD : ContinuousOn (fun s => Work.Elliptic.L12dens h s) (Set.Ioi 0))
    {j : ℕ} (hj : j ≤ 3) {z : ℝ} (hz : 0 < z) :
    Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 h z) z 0
      = Work.FTS_RegExport.RXT.Slots.L12jet h j z := by
  rw [Work.Elliptic.DzIter_rad (fun z => Work.Construction.L12 h z) j z 0]
  exact Work.FTS_RegExport.RXT.Slots.dzdIter_L12_jet hCw h4 hJet
    (fun w hw => Work.FTS_RegExport.RXT.Slots.QangZeroDeriv_jet hCw h4 hJet hw)
    (fun w hw => Work.FTS_RegExport.RXT.Slots.QangOneDeriv_jet hCw h4 hJet hw)
    (fun w hw => Work.FTS_RegExport.RXT.Slots.Construction_L12_hasDerivAt_jet hCw hJet hcontD hw)
    hj hz

theorem L12_slice_jets_le {Cw Cmaj : ℝ} (hCw : 0 ≤ Cw) (hCmaj : 0 ≤ Cmaj)
    {h : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    (hJet : Work.FTS_RegExport.RXT.Slots.JetBnd Cw h)
    (hmaj : ∀ z : ℝ, 0 < z →
      ∫ s in Set.Ioi z, s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 ≤ Cmaj) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      |Work.Spaces.DzIter k (fun z _ => Work.Construction.L12 h z) z 0| ≤ C := by
  -- the standing bound, in the form used by the `L12Iter` toolkit
  have hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k h z θ| ≤ Cw * Work.FTS_RegExport.RXT.L12Iter.Rwt z := by
    intro k hk z θ hz h0 h1
    simpa only [Work.Spaces.mixed_zero_right, Work.FTS_RegExport.RXT.L12Iter.Rwt]
      using hJet k 0 (by omega : 0 + k ≤ 2) z θ hz h0 h1
  -- continuity of the `L₁₂`-density
  have hcontD : ContinuousOn (fun s => Work.Elliptic.L12dens h s) (Set.Ioi 0) := by
    refine ContinuousOn.congr (s := Set.Ioi 0) (f := fun s => Work.Elliptic.Qang h 0 s / s)
      (g := fun s => Work.Elliptic.L12dens h s) ?_ ?_
    · intro s hs
      exact ((Work.FTS_RegExport.RXT.Slots.QangZeroDeriv_jet hCw h4 hJet hs).continuousAt.div
        continuousAt_id (ne_of_gt hs)).continuousWithinAt
    · intro s _
      exact Work.Elliptic.L12dens_eq_Qang_div h s
  have hkey : ∀ (j : ℕ), j ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 h z) z 0
        = Work.FTS_RegExport.RXT.Slots.L12jet h j z :=
    fun j hj z hz => DzIter_L12_eq_L12jet hCw h4 hJet hcontD hj hz
  have hCn : 0 ≤ 3 * (Real.pi / 2) * Cw * max Cmaj 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hCw)
      (le_trans zero_le_one (le_max_right Cmaj 1))
  refine ⟨3 * (Real.pi / 2) * Cw * max Cmaj 1 + 1,
    lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left hCn), ?_⟩
  intro k hk z hz
  rw [hkey k hk z hz]
  have hc : 0 ≤ 3 * (Real.pi / 2) * Cw := mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hCw
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `k = 0`: the radial majorant
    subst hk0
    rw [Work.FTS_RegExport.RXT.Slots.L12jet_zero]
    have hL12 := abs_L12_le hCw h4 hbd hmaj hz
    calc |Work.Construction.L12 h z| ≤ 3 * (Real.pi / 2) * Cw * Cmaj := hL12
      _ ≤ 3 * (Real.pi / 2) * Cw * max Cmaj 1 :=
          mul_le_mul_of_nonneg_left (le_max_left Cmaj 1) hc
      _ ≤ 3 * (Real.pi / 2) * Cw * max Cmaj 1 + 1 := by linarith
  · -- `k = m + 1 ≥ 1`: the angular moment at level `m ≤ 2`
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkpos.ne'
    rw [Work.FTS_RegExport.RXT.Slots.L12jet_succ]
    have hm2 : m ≤ 2 := by omega
    have hq := abs_Qang_le_two hCw h4 hbd hm2 hz
    have hR : Work.FTS_RegExport.RXT.L12Iter.Rwt z ≤ 1 := Rwt_le_one hz.le
    have hstep : 3 * (Real.pi / 2) * (Cw * Work.FTS_RegExport.RXT.L12Iter.Rwt z)
        ≤ 3 * (Real.pi / 2) * Cw := by
      have h1 : Cw * Work.FTS_RegExport.RXT.L12Iter.Rwt z ≤ Cw * 1 :=
        mul_le_mul_of_nonneg_left hR hCw
      have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 3 * (Real.pi / 2))
      linarith [h2]
    have hstep2 : 3 * (Real.pi / 2) * Cw ≤ 3 * (Real.pi / 2) * Cw * max Cmaj 1 := by
      have h2 := mul_le_mul_of_nonneg_left (le_max_right Cmaj 1) hc
      linarith [h2]
    calc |-(Work.Elliptic.Qang h m z)| = |Work.Elliptic.Qang h m z| := abs_neg _
      _ ≤ 3 * (Real.pi / 2) * (Cw * Work.FTS_RegExport.RXT.L12Iter.Rwt z) := hq
      _ ≤ 3 * (Real.pi / 2) * Cw := hstep
      _ ≤ 3 * (Real.pi / 2) * Cw * max Cmaj 1 := hstep2
      _ ≤ 3 * (Real.pi / 2) * Cw * max Cmaj 1 + 1 := by linarith

end Work.FTS_StreamBdry.Inputs
