import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.Trunc.PassAux2
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.Stability.mul_rpow_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT.uTrAone

open MeasureTheory Set
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-- The integrand of the conclusion: `(∂_t phiTr N · Gc N b u)² · wE`. -/
abbrev GPhi (N b : ℝ) (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (deriv (phiTr N) p.1 * Gc N b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2

/-- The integrand of the reference slot: `(L_b u)² · wE`. -/
abbrev GSlot (b : ℝ) (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2

theorem measurableSet_suppPhi (N : ℝ) :
    MeasurableSet (Set.Icc (-(8192 * N)) (8192 * N)) := measurableSet_Icc

/-! ## Derivative facts for the cutoff `phiTr` -/

theorem deriv_phiTr_eq (N t : ℝ) :
    deriv (phiTr N) t = deriv Work.FTS.EllSol.Trunc.tk (t / (4096 * N)) / (4096 * N) :=
  Work.FTS.EllSol.Trunc.deriv_chi_eq (4096 * N) t

theorem abs_deriv_phiTr_le (N K : ℝ) (hN : 0 < N)
    (hK : ∀ t : ℝ, |deriv Work.FTS.EllSol.Trunc.tk t| ≤ K) (t : ℝ) :
    |deriv (phiTr N) t| ≤ K / (4096 * N) := by
  rw [deriv_phiTr_eq, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4096 * N)]
  exact div_le_div_of_nonneg_right (hK _) (by positivity)

theorem deriv_phiTr_eq_zero_of_gt (N t : ℝ) (hN : 0 < N) (ht : 8192 * N < |t|) :
    deriv (phiTr N) t = 0 :=
  Work.FTS.EllSol.Trunc.deriv_chi_eq_zero_of_gt (N := 4096 * N) (by positivity)
    (by linarith)

theorem deriv_phiTr_eq_zero_of_lt (N t : ℝ) (hN : 0 < N) (ht : |t| < 4096 * N) :
    deriv (phiTr N) t = 0 := by
  have hev : (phiTr N) =ᶠ[𝓝 t] (fun _ : ℝ => (1 : ℝ)) := by
    have hopen : IsOpen {s : ℝ | |s| < 4096 * N} := isOpen_lt continuous_abs continuous_const
    filter_upwards [hopen.mem_nhds ht] with s hs
    exact Work.FTS.EllSol.Trunc.chi_eq_one (by positivity) (le_of_lt hs)
  rw [hev.deriv_eq, deriv_const]

/-! ## Pointwise domination of the integrand -/

/-- Pointwise bound: outside `[-8192N, 8192N]` the derivative of `phiTr N` vanishes, and inside
it either the derivative vanishes (for `|t| < 4096N`) or `|Gc|` is controlled by the shifted slot
through the hypothesis `hbd`. The angular weight is an arbitrary nonnegative `w`. -/
theorem GPhi_le (N b K : ℝ) (u : ℝ → ℝ → ℝ) (hN : 2 ≤ N)
    (hK : ∀ t : ℝ, |deriv Work.FTS.EllSol.Trunc.tk t| ≤ K)
    (hbd : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → 2 * N ≤ |t| →
      |Gc N b u t θ| ≤ ∫ s in (-(2 * N))..(2 * N), |Work.Spaces.pz u s θ - b * u s θ|)
    (w : ℝ) (hw : 0 ≤ w) (t θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (deriv (phiTr N) t * Gc N b u t θ) ^ 2 * w
      ≤ (K / (4096 * N)) ^ 2
          * (∫ s in (-(2 * N))..(2 * N), |Work.Spaces.pz u s θ - b * u s θ|) ^ 2
          * w
        * (Set.Icc (-(8192 * N)) (8192 * N)).indicator (fun _ => (1 : ℝ)) t := by
  have hNpos : 0 < N := by linarith
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0)
  have hmems0 : t ∈ Set.Icc (-(8192 * N)) (8192 * N) ↔ |t| ≤ 8192 * N := by
    rw [Set.mem_Icc, abs_le]
  by_cases ht : t ∈ Set.Icc (-(8192 * N)) (8192 * N)
  · rw [Set.indicator_of_mem ht, mul_one]
    by_cases hlt : |t| < 4096 * N
    · rw [deriv_phiTr_eq_zero_of_lt N t hNpos hlt, zero_mul, zero_pow (by norm_num), zero_mul]
      positivity
    · push_neg at hlt
      have hbdt := hbd t θ hθ (by linarith)
      have hdb : |deriv (phiTr N) t| ≤ K / (4096 * N) := abs_deriv_phiTr_le N K hNpos hK t
      have hd2 : (deriv (phiTr N) t) ^ 2 ≤ (K / (4096 * N)) ^ 2 := by
        rw [show (deriv (phiTr N) t) ^ 2 = |deriv (phiTr N) t| ^ 2 from (sq_abs _).symm]
        exact pow_le_pow_left₀ (abs_nonneg _) hdb 2
      have hG2 : (Gc N b u t θ) ^ 2
          ≤ (∫ s in (-(2 * N))..(2 * N), |Work.Spaces.pz u s θ - b * u s θ|) ^ 2 := by
        rw [show (Gc N b u t θ) ^ 2 = |Gc N b u t θ| ^ 2 from (sq_abs _).symm]
        exact pow_le_pow_left₀ (abs_nonneg _) hbdt 2
      have hC2 : 0 ≤ (∫ s in (-(2 * N))..(2 * N), |Work.Spaces.pz u s θ - b * u s θ|) ^ 2 :=
        sq_nonneg _
      have hKM : 0 ≤ (K / (4096 * N)) ^ 2 := sq_nonneg _
      calc (deriv (phiTr N) t * Gc N b u t θ) ^ 2 * w
          = (deriv (phiTr N) t) ^ 2 * (Gc N b u t θ) ^ 2 * w := by ring
        _ ≤ (K / (4096 * N)) ^ 2
              * (∫ s in (-(2 * N))..(2 * N), |Work.Spaces.pz u s θ - b * u s θ|) ^ 2
              * w :=
            mul_le_mul (mul_le_mul hd2 hG2 (sq_nonneg _) hKM) le_rfl hw (mul_nonneg hKM hC2)
  · rw [Set.indicator_of_notMem ht, mul_zero]
    have hgt : 8192 * N < |t| := lt_of_not_ge (fun hle => ht (hmems0.mpr hle))
    rw [deriv_phiTr_eq_zero_of_gt N t hNpos hgt, zero_mul, zero_pow (by norm_num), zero_mul]

/-! ## Cauchy–Schwarz on the interval `[-2N, 2N]` -/

theorem C_sq_le (N b : ℝ) (u : ℝ → ℝ → ℝ) (hN : 0 < N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ENNReal.ofReal ((∫ s in (-(2 * N))..(2 * N), |Work.Spaces.pz u s θ - b * u s θ|) ^ 2)
      ≤ ENNReal.ofReal (4 * N)
        * ∫⁻ t, ENNReal.ofReal ((Work.Spaces.pz u t θ - b * u t θ) ^ 2) := by
  have hN0 : (0 : ℝ) ≤ N := le_of_lt hN
  have hab : -(2 * N) ≤ 2 * N := by linarith
  have hcont : Continuous (fun s : ℝ => Work.Spaces.pz u s θ - b * u s θ) :=
    (Work.FTS.EllSol.Trunc.continuous_pz_zslice hu hθ).sub
      (continuous_const.mul (Work.FTS.EllSol.Trunc.continuous_zslice hu hθ))
  have hcs := Work.FTS.StrongEps.LocUnif.ofReal_interval_integral_sq_le hab
    (fun s : ℝ => |Work.Spaces.pz u s θ - b * u s θ|) hcont.abs.aestronglyMeasurable
  refine hcs.trans ?_
  have hba : (2 * N) - (-(2 * N)) = 4 * N := by ring
  rw [hba]
  refine mul_le_mul le_rfl ?_ ?_ ?_
  · exact le_trans (setLIntegral_le_lintegral _ _) (le_of_eq (lintegral_congr (fun t => by
      rw [sq_abs])))
  · positivity
  · positivity

/-! ## The slice estimate -/

/-- The slice estimate with a general nonnegative angular weight `w`: the numerical factor is
`(K/(4096N))^2 · (2·8192N) · 4N = K^2/256`. -/
theorem slice_aux (N b K : ℝ) (u : ℝ → ℝ → ℝ) (hN : 2 ≤ N)
    (hK : ∀ t : ℝ, |deriv Work.FTS.EllSol.Trunc.tk t| ≤ K)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hbd : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → 2 * N ≤ |t| →
      |Gc N b u t θ| ≤ ∫ s in (-(2 * N))..(2 * N), |Work.Spaces.pz u s θ - b * u s θ|)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (w : ℝ) (hw : 0 ≤ w) :
    ∫⁻ t, ENNReal.ofReal ((deriv (phiTr N) t * Gc N b u t θ) ^ 2 * w)
      ≤ ENNReal.ofReal (K ^ 2 / 256)
        * ∫⁻ t, ENNReal.ofReal ((Work.Spaces.pz u t θ - b * u t θ) ^ 2 * w) := by
  have hNpos : 0 < N := by linarith
  set C : ℝ := ∫ s in (-(2 * N))..(2 * N), |Work.Spaces.pz u s θ - b * u s θ| with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
    exact intervalIntegral.integral_nonneg (by linarith) (fun s _ => abs_nonneg _)
  have hle_pt : ∀ t, t ∈ Set.Icc (-(8192 * N)) (8192 * N) →
      ENNReal.ofReal ((deriv (phiTr N) t * Gc N b u t θ) ^ 2 * w)
        ≤ ENNReal.ofReal ((K / (4096 * N)) ^ 2 * C ^ 2 * w) := by
    intro t ht
    have h := GPhi_le N b K u hN hK hbd w hw t θ hθ
    rw [Set.indicator_of_mem ht, mul_one, ← hC] at h
    exact ENNReal.ofReal_le_ofReal h
  have hzero_pt : ∀ t, t ∉ Set.Icc (-(8192 * N)) (8192 * N) →
      ENNReal.ofReal ((deriv (phiTr N) t * Gc N b u t θ) ^ 2 * w) = 0 := by
    intro t ht
    have h := GPhi_le N b K u hN hK hbd w hw t θ hθ
    rw [Set.indicator_of_notMem ht, mul_zero] at h
    have hnn : 0 ≤ (deriv (phiTr N) t * Gc N b u t θ) ^ 2 * w :=
      mul_nonneg (sq_nonneg _) hw
    rw [le_antisymm h hnn, ENNReal.ofReal_zero]
  have hA : ∫⁻ t, ENNReal.ofReal ((deriv (phiTr N) t * Gc N b u t θ) ^ 2 * w)
      ≤ ENNReal.ofReal ((K / (4096 * N)) ^ 2 * C ^ 2 * w)
        * ENNReal.ofReal (2 * (8192 * N)) := by
    have h1 : ∫⁻ t, ENNReal.ofReal ((deriv (phiTr N) t * Gc N b u t θ) ^ 2 * w)
        = ∫⁻ t in Set.Icc (-(8192 * N)) (8192 * N), ENNReal.ofReal ((deriv (phiTr N) t * Gc N b u t θ) ^ 2 * w) := by
      rw [← lintegral_indicator (measurableSet_suppPhi N)]
      exact lintegral_congr (fun t => by
        by_cases ht : t ∈ Set.Icc (-(8192 * N)) (8192 * N)
        · rw [Set.indicator_of_mem ht]
        · rw [Set.indicator_of_notMem ht, hzero_pt t ht])
    rw [h1]
    refine (setLIntegral_mono' (measurableSet_suppPhi N) (fun t ht => hle_pt t ht)).trans
      (le_of_eq ?_)
    rw [setLIntegral_const, Real.volume_Icc,
      show (8192 : ℝ) * N - (-(8192 * N)) = 2 * (8192 * N) from by ring]
  have hB : ENNReal.ofReal (C ^ 2)
      ≤ ENNReal.ofReal (4 * N)
        * ∫⁻ t, ENNReal.ofReal ((Work.Spaces.pz u t θ - b * u t θ) ^ 2) := by
    have h := C_sq_le N b u hNpos hu θ hθ
    rwa [← hC] at h
  have hA1 : ENNReal.ofReal ((K / (4096 * N)) ^ 2 * C ^ 2 * w)
      = (ENNReal.ofReal ((K / (4096 * N)) ^ 2) * ENNReal.ofReal (C ^ 2))
        * ENNReal.ofReal w := by
    rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
      ENNReal.ofReal_mul (sq_nonneg _)]
  have hA2 : ENNReal.ofReal ((K / (4096 * N)) ^ 2) * ENNReal.ofReal (4 * N)
      * ENNReal.ofReal (2 * (8192 * N)) = ENNReal.ofReal (K ^ 2 / 256) := by
    rw [← ENNReal.ofReal_mul (sq_nonneg (K / (4096 * N))),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (K / (4096 * N)) ^ 2 * (4 * N))]
    congr 1
    field_simp
    ring
  calc ∫⁻ t, ENNReal.ofReal ((deriv (phiTr N) t * Gc N b u t θ) ^ 2 * w)
      ≤ ENNReal.ofReal ((K / (4096 * N)) ^ 2 * C ^ 2 * w)
        * ENNReal.ofReal (2 * (8192 * N)) := hA
    _ = (ENNReal.ofReal ((K / (4096 * N)) ^ 2) * ENNReal.ofReal (C ^ 2)
          * ENNReal.ofReal w) * ENNReal.ofReal (2 * (8192 * N)) := by rw [hA1]
    _ ≤ (ENNReal.ofReal ((K / (4096 * N)) ^ 2)
            * (ENNReal.ofReal (4 * N)
              * ∫⁻ t, ENNReal.ofReal ((Work.Spaces.pz u t θ - b * u t θ) ^ 2))
          * ENNReal.ofReal w) * ENNReal.ofReal (2 * (8192 * N)) :=
          mul_le_mul_left (mul_le_mul_left (mul_le_mul_right hB _) _) _
    _ = ENNReal.ofReal (K ^ 2 / 256)
          * (ENNReal.ofReal w
              * ∫⁻ t, ENNReal.ofReal ((Work.Spaces.pz u t θ - b * u t θ) ^ 2)) := by
          rw [← hA2]; ac_rfl
    _ = ENNReal.ofReal (K ^ 2 / 256)
          * ∫⁻ t, ENNReal.ofReal (w * (Work.Spaces.pz u t θ - b * u t θ) ^ 2) := by
          congr 1
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact lintegral_congr (fun t => (ENNReal.ofReal_mul hw).symm)
    _ = ENNReal.ofReal (K ^ 2 / 256)
          * ∫⁻ t, ENNReal.ofReal ((Work.Spaces.pz u t θ - b * u t θ) ^ 2 * w) := by
          congr 1
          exact lintegral_congr (fun t => by rw [mul_comm])

/-- The slice estimate for the angular weight `wE`. -/
theorem slice_lintegral_le (N b K : ℝ) (u : ℝ → ℝ → ℝ) (hN : 2 ≤ N)
    (hK : ∀ t : ℝ, |deriv Work.FTS.EllSol.Trunc.tk t| ≤ K)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hbd : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → 2 * N ≤ |t| →
      |Gc N b u t θ| ≤ ∫ s in (-(2 * N))..(2 * N), |Work.Spaces.pz u s θ - b * u s θ|)
    (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    ∫⁻ t, ENNReal.ofReal
        ((deriv (phiTr N) t * Gc N b u t θ) ^ 2 * Work.FTS.EllSol.FlatFT.wE θ)
      ≤ ENNReal.ofReal (K ^ 2 / 256)
        * ∫⁻ t, ENNReal.ofReal
            ((Work.Spaces.pz u t θ - b * u t θ) ^ 2 * Work.FTS.EllSol.FlatFT.wE θ) := by
  by_cases hIoo : θ ∈ Set.Ioo 0 (Real.pi / 2)
  · exact slice_aux N b K u hN hK hu hbd θ hIoo (Work.FTS.EllSol.FlatFT.wE θ)
      (Work.FTS.EllSol.FlatFT.wE_nonneg hθ)
  · have hz : Work.FTS.EllSol.FlatFT.wE θ = 0 := by
      rcases hθ with ⟨h0, h1⟩
      rcases lt_or_eq_of_le h0 with h | h
      · have hp : θ = Real.pi / 2 := by
          by_contra hne
          exact hIoo ⟨h, lt_of_le_of_ne h1 hne⟩
        rw [hp]; exact Work.FTS.EllSol.Trunc.wE_pi_div_two
      · rw [← h]; exact Work.FTS.EllSol.Trunc.wE_zero
    have hfun : (fun t => ENNReal.ofReal
        ((deriv (phiTr N) t * Gc N b u t θ) ^ 2 * Work.FTS.EllSol.FlatFT.wE θ))
        = fun _ => 0 := by
      funext t
      rw [hz, mul_zero, ENNReal.ofReal_zero]
    rw [hfun, lintegral_zero]
    exact bot_le

/-! ## The bridge from the product integral to the iterated one -/

theorem setLIntegral_strip_eq_iterated {f : ℝ → ℝ → ℝ}
    (hf : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (f p.1 p.2))
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ))) :
    ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal (f p.1 p.2)
      = ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ t, ENNReal.ofReal (f t θ) := by
  have hf' : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (f p.1 p.2))
      ((volume.prod volume).restrict (Set.univ ×ˢ Work.Spaces.Iθ)) := by
    rw [← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact hf
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  simpa only [Measure.restrict_univ] using
    MeasureTheory.setLIntegral_prod_symm (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
      (s := (Set.univ : Set ℝ)) (t := Work.Spaces.Iθ)
      (fun p : ℝ × ℝ => ENNReal.ofReal (f p.1 p.2)) hf'

theorem derivPhiTrGcLe (N b K : ℝ) (u : ℝ → ℝ → ℝ) (hN : 2 ≤ N)
    (hK : ∀ t : ℝ, |deriv Work.FTS.EllSol.Trunc.tk t| ≤ K)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hI : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ))
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.EllSol.ShiftFT.Gc N b u p.1 p.2)
      (MeasureTheory.volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)))
    (hbd : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → 2 * N ≤ |t| →
      |Work.FTS.EllSol.ShiftFT.Gc N b u t θ|
        ≤ ∫ s in (-(2 * N))..(2 * N), |Work.Spaces.pz u s θ - b * u s θ|) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (deriv (Work.FTS.EllSol.ShiftFT.phiTr N) p.1
          * Work.FTS.EllSol.ShiftFT.Gc N b u p.1 p.2) ^ 2
          * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) ∧
    (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        (deriv (Work.FTS.EllSol.ShiftFT.phiTr N) p.1
          * Work.FTS.EllSol.ShiftFT.Gc N b u p.1 p.2) ^ 2
          * Work.FTS.EllSol.FlatFT.wE p.2)
      ≤ K ^ 2 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2
            * Work.FTS.EllSol.FlatFT.wE p.2) := by
  have hNpos : 0 < N := by linarith
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0)
  have hmeasθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hSI_meas : MeasurableSet (Set.univ ×ˢ Work.Spaces.Iθ) :=
    (MeasurableSet.univ (α := ℝ)).prod hmeasθ
  show MeasureTheory.IntegrableOn (GPhi N b u) (Set.univ ×ˢ Work.Spaces.Iθ) ∧
    (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, GPhi N b u p)
      ≤ K ^ 2 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, GSlot b u p)
  -- ## measurability of the two integrands
  have hdphi : Continuous (deriv (phiTr N)) :=
    ((phiTr_contDiff 1 N).continuous_deriv (by simp))
  have hAESM_phi : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => deriv (phiTr N) p.1)
      (MeasureTheory.volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
    (hdphi.measurable.comp measurable_fst).aestronglyMeasurable
  have hAESM_wE : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.EllSol.FlatFT.wE p.2)
      (MeasureTheory.volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
    Work.FTS.EllSol.Trunc.aesm_strip Work.FTS.EllSol.Trunc.continuousOn_wE_comp
  have hAESM_GPhi : MeasureTheory.AEStronglyMeasurable (GPhi N b u)
      (MeasureTheory.volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
    (((hAESM_phi.mul hmeas).pow 2).mul hAESM_wE)
  have hAESM_pz : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
      (MeasureTheory.volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
    Work.FTS.EllSol.Trunc.aesm_strip
      (Work.FTS.EllSol.Trunc.continuousOn_uncurry_pz hu)
  have hAESM_u : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => u p.1 p.2)
      (MeasureTheory.volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
    Work.FTS.EllSol.Trunc.aesm_strip hu.continuousOn
  have hAESM_GSlot : MeasureTheory.AEStronglyMeasurable (GSlot b u)
      (MeasureTheory.volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
    (((hAESM_pz.sub (hAESM_u.const_mul b)).pow 2).mul hAESM_wE)
  -- ## a.e. nonnegativity
  have hGPhi_pos : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)]
      GPhi N b u := by
    filter_upwards [MeasureTheory.ae_restrict_mem hSI_meas] with p hp
    exact mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.FlatFT.wE_nonneg hp.2)
  have hGSlot_pos : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)]
      GSlot b u := by
    filter_upwards [MeasureTheory.ae_restrict_mem hSI_meas] with p hp
    exact mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.FlatFT.wE_nonneg hp.2)
  -- ## the lintegral estimate
  have hLHS : ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal (GPhi N b u p)
      = ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ t, ENNReal.ofReal (GPhi N b u (t, θ)) :=
    setLIntegral_strip_eq_iterated (f := fun t θ => GPhi N b u (t, θ))
      (ENNReal.measurable_ofReal.comp_aemeasurable hAESM_GPhi.aemeasurable)
  have hRHS : ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal (GSlot b u p)
      = ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ t, ENNReal.ofReal (GSlot b u (t, θ)) :=
    setLIntegral_strip_eq_iterated (f := fun t θ => GSlot b u (t, θ))
      (ENNReal.measurable_ofReal.comp_aemeasurable hAESM_GSlot.aemeasurable)
  have hslice : ∀ θ ∈ Work.Spaces.Iθ,
      ∫⁻ t, ENNReal.ofReal (GPhi N b u (t, θ))
        ≤ ENNReal.ofReal (K ^ 2 / 256) * ∫⁻ t, ENNReal.ofReal (GSlot b u (t, θ)) :=
    fun θ hθ => slice_lintegral_le N b K u hN hK hu hbd θ hθ
  have hfin256 : ENNReal.ofReal (K ^ 2 / 256) ≤ ENNReal.ofReal (K ^ 2) :=
    ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg K])
  have hlin : ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal (GPhi N b u p)
      ≤ ENNReal.ofReal (K ^ 2) * ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ,
          ENNReal.ofReal (GSlot b u p) := by
    rw [hLHS, hRHS]
    calc ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ t, ENNReal.ofReal (GPhi N b u (t, θ))
        ≤ ∫⁻ θ in Work.Spaces.Iθ, (ENNReal.ofReal (K ^ 2 / 256)
            * ∫⁻ t, ENNReal.ofReal (GSlot b u (t, θ))) :=
          setLIntegral_mono' hmeasθ hslice
      _ = ENNReal.ofReal (K ^ 2 / 256)
            * ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ t, ENNReal.ofReal (GSlot b u (t, θ)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (K ^ 2)
            * ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ t, ENNReal.ofReal (GSlot b u (t, θ)) :=
          mul_le_mul_left hfin256 _
  -- ## finiteness of the reference lintegral
  have hGSlot_fin : ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal (GSlot b u p) < ⊤ :=
    (MeasureTheory.hasFiniteIntegral_iff_ofReal hGSlot_pos).mp hI.2
  have hGSlot_ne : ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal (GSlot b u p) ≠ ⊤ :=
    ne_of_lt hGSlot_fin
  have hG_eq : ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal (GSlot b u p)
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, GSlot b u p) := by
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hGSlot_pos hAESM_GSlot]
    exact (ENNReal.ofReal_toReal hGSlot_ne).symm
  have hbound : ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal (GPhi N b u p)
      ≤ ENNReal.ofReal (K ^ 2 * ∫ p in Set.univ ×ˢ Work.Spaces.Iθ, GSlot b u p) := by
    refine hlin.trans (le_of_eq ?_)
    rw [hG_eq, ← ENNReal.ofReal_mul (sq_nonneg K)]
  -- ## conclusion
  have hGSlot_int_nonneg : 0 ≤ ∫ p in Set.univ ×ˢ Work.Spaces.Iθ, GSlot b u p :=
    MeasureTheory.integral_nonneg_of_ae hGSlot_pos
  have hineq : ∫ p in Set.univ ×ˢ Work.Spaces.Iθ, GPhi N b u p
      ≤ K ^ 2 * ∫ p in Set.univ ×ˢ Work.Spaces.Iθ, GSlot b u p :=
    Work.FTS.EllSol.Trunc.integral_le_of_lintegral_le hGPhi_pos
      (mul_nonneg (sq_nonneg K) hGSlot_int_nonneg) hbound
  have hInt : MeasureTheory.IntegrableOn (GPhi N b u) (Set.univ ×ˢ Work.Spaces.Iθ) :=
    ⟨hAESM_GPhi,
      (MeasureTheory.hasFiniteIntegral_iff_ofReal hGPhi_pos).mpr
        (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top)⟩
  exact ⟨hInt, hineq⟩

end

end Work.FTS.EllSol.ShiftFT.uTrAone
