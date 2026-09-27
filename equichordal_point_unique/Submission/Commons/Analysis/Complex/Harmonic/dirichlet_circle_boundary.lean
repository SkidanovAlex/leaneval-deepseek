import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

noncomputable section
open Complex InnerProductSpace Metric Real
open scoped Topology Real

namespace Commons.Analysis.Complex.Harmonic

/-- Poisson integral (radius r, center 0). -/
noncomputable def poissonInt (g : ℂ → ℝ) (r : ℝ) (w : ℂ) : ℝ :=
  Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * g z) 0 r

lemma poissonKernel_circle_r {w z : ℂ} {r : ℝ} (_hw : ‖w‖ < r) (hz : ‖z‖ = r) :
    poissonKernel 0 w z = (r ^ 2 - ‖w‖ ^ 2) / ‖z - w‖ ^ 2 := by
  rw [poissonKernel_def]
  simp [hz]

lemma poissonKernel_pos_r {w z : ℂ} {r : ℝ} (hw : ‖w‖ < r) (hz : ‖z‖ = r) :
    0 ≤ poissonKernel 0 w z := by
  rw [poissonKernel_circle_r hw hz]
  have hnum : 0 ≤ r ^ 2 - ‖w‖ ^ 2 := by
    have hr : 0 ≤ r := (norm_nonneg w).trans hw.le
    have hw2 : ‖w‖ ^ 2 ≤ r ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg w) hr).2 hw.le
    nlinarith
  exact div_nonneg hnum (sq_nonneg ‖z - w‖)

lemma poisson_total_mass_r {w : ℂ} {r : ℝ} (_hr : 0 < r) (hw : ‖w‖ < r) :
    Real.circleAverage (fun z : ℂ => poissonKernel 0 w z) 0 r = 1 := by
  have hconst : InnerProductSpace.HarmonicContOnCl (fun _ : ℂ => (1 : ℝ)) (ball (0 : ℂ) r) := by
    exact InnerProductSpace.harmonicContOnCl_const
  have hwball : w ∈ ball (0 : ℂ) r := by
    simpa [mem_ball, dist_eq_norm] using hw
  have h := InnerProductSpace.HarmonicContOnCl.circleAverage_poissonKernel_smul
    (f := fun _ : ℂ => (1 : ℝ)) (c := (0 : ℂ)) (R := r) hconst hwball
  have hsmul : (poissonKernel 0 w • (fun _ : ℂ => (1 : ℝ))) = fun z : ℂ => poissonKernel 0 w z := by
    funext z
    simp
  rw [hsmul] at h
  exact h

lemma continuousOn_poissonKernel_sphere_r {w : ℂ} {r : ℝ} (hw : ‖w‖ < r) :
    ContinuousOn (fun z : ℂ => poissonKernel 0 w z) (sphere (0 : ℂ) r) := by
  refine ContinuousOn.congr (f := fun u : ℂ => (r ^ 2 - ‖w‖ ^ 2) / ‖u - w‖ ^ 2)
    (g := fun z : ℂ => poissonKernel 0 w z) ?h ?h'
  · refine ContinuousOn.div ?hnum ?hden ?hden_ne
    · fun_prop
    · fun_prop
    · intro z hz
      have hzr : ‖z‖ = r := by simpa using (mem_sphere_iff_norm.mp hz)
      have hne : z - w ≠ 0 := by
        intro h
        have : ‖w‖ = r := by simpa [sub_eq_zero.mp h] using hzr
        linarith
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
  · intro z hz
    have hzr : ‖z‖ = r := by simpa using (mem_sphere_iff_norm.mp hz)
    change poissonKernel 0 w z = (r ^ 2 - ‖w‖ ^ 2) / ‖z - w‖ ^ 2
    exact poissonKernel_circle_r hw hzr

lemma circleIntegrable_poisson_mul (g : ℂ → ℝ) {r : ℝ} (hr : 0 < r)
    (hg : ContinuousOn g (sphere 0 r)) {w : ℂ} (hw : ‖w‖ < r) :
    CircleIntegrable (fun z : ℂ => poissonKernel 0 w z * g z) 0 r := by
  have hk : ContinuousOn (fun z : ℂ => poissonKernel 0 w z) (sphere 0 |r|) := by
    simpa [abs_of_pos hr] using continuousOn_poissonKernel_sphere_r hw
  have hg' : ContinuousOn g (sphere 0 |r|) := by
    simpa [abs_of_pos hr] using hg
  exact (hk.mul hg').circleIntegrable'

lemma poissonInt_sub (g : ℂ → ℝ) {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (sphere 0 r))
    {w x : ℂ} (hw : ‖w‖ < r) (_hx : ‖x‖ = r) :
    poissonInt g r w - g x =
      Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * (g z - g x)) 0 r := by
  let k : ℂ → ℝ := fun z => poissonKernel 0 w z
  let fA : ℂ → ℝ := fun z => k z * g z
  let fC : ℂ → ℝ := fun z => k z * g x
  have hkcont : ContinuousOn k (sphere 0 r) := continuousOn_poissonKernel_sphere_r hw
  have hAcont : ContinuousOn fA (sphere 0 r) := by
    intro z hz
    exact (hkcont z hz).mul (hg z hz)
  have hCcont : ContinuousOn fC (sphere 0 r) := by
    intro z hz
    exact (hkcont z hz).mul_const (g x)
  have hAcont' : ContinuousOn fA (sphere 0 |r|) := by
    simpa [abs_of_pos hr] using hAcont
  have hCcont' : ContinuousOn fC (sphere 0 |r|) := by
    simpa [abs_of_pos hr] using hCcont
  have hAint : CircleIntegrable fA 0 r := hAcont'.circleIntegrable'
  have hCint : CircleIntegrable fC 0 r := hCcont'.circleIntegrable'
  -- circle average of fC equals g x
  have hC : Real.circleAverage fC 0 r = g x := by
    have hsmul : Real.circleAverage (fun z : ℂ => (g x) • k z) 0 r =
        (g x) • Real.circleAverage k 0 r := by
      exact Real.circleAverage_fun_smul (a := g x) (f := k)
    have hcon : (fun z : ℂ => (g x) • k z) = fC := by
      funext z
      simp [fC, k, smul_eq_mul, mul_comm]
    have hmass : Real.circleAverage k 0 r = 1 := by
      simpa [k] using poisson_total_mass_r hr hw
    calc
      Real.circleAverage fC 0 r = Real.circleAverage (fun z : ℂ => (g x) • k z) 0 r := by
        rw [hcon.symm]
      _ = (g x) • Real.circleAverage k 0 r := hsmul
      _ = g x := by simp [hmass]
  calc
    poissonInt g r w - g x = Real.circleAverage fA 0 r - g x := by rfl
    _ = Real.circleAverage fA 0 r - Real.circleAverage fC 0 r := by rw [hC]
    _ = Real.circleAverage (fun z : ℂ => fA z - fC z) 0 r :=
        (Real.circleAverage_fun_sub hAint hCint).symm
    _ = Real.circleAverage (fun z : ℂ => k z * (g z - g x)) 0 r := by
      congr 1
      funext z
      simp [fA, fC, mul_sub]
    _ = Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * (g z - g x)) 0 r := by
      simp [k]

end Commons.Analysis.Complex.Harmonic

namespace Commons.Analysis.Complex.Harmonic

lemma norm_add_sub_triangle (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; abel
    _ ≤ ‖a - b‖ + ‖b - c‖ := norm_add_le _ _

/-- Poisson kernel at radius r, upper bound off an arc. -/
lemma poissonKernel_offArc_bound {w x z : ℂ} {r θ : ℝ} (hw : ‖w‖ < r) (hθ : 0 < θ)
    (hwx : ‖w - x‖ ≤ θ / 2) (hx : ‖x‖ = r) (hzx : θ ≤ ‖z - x‖) (hz : ‖z‖ = r) :
    poissonKernel 0 w z ≤ (8 * r * ‖w - x‖) / θ ^ 2 := by
  rw [poissonKernel_circle_r hw hz]
  have htri : ‖z - x‖ ≤ ‖z - w‖ + ‖w - x‖ := norm_add_sub_triangle z w x
  have hzw_ge : θ / 2 ≤ ‖z - w‖ := by nlinarith [hzx, hwx, htri]
  have hnum : 0 ≤ r ^ 2 - ‖w‖ ^ 2 := by
    have hr : 0 ≤ r := (norm_nonneg w).trans hw.le
    have hw2 : ‖w‖ ^ 2 ≤ r ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg w) hr).2 hw.le
    nlinarith
  have hθ2pos : 0 < (θ / 2) ^ 2 := sq_pos_of_pos (by positivity)
  have hden_le : (θ / 2) ^ 2 ≤ ‖z - w‖ ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 hzw_ge
  have h1 : (r ^ 2 - ‖w‖ ^ 2) / ‖z - w‖ ^ 2 ≤ (r ^ 2 - ‖w‖ ^ 2) / (θ / 2) ^ 2 :=
    div_le_div_of_nonneg_left hnum hθ2pos hden_le
  have htri2 : ‖x‖ ≤ ‖x - w‖ + ‖w‖ := by
    calc ‖x‖ = ‖(x - w) + w‖ := by congr 1; abel
      _ ≤ ‖x - w‖ + ‖w‖ := norm_add_le _ _
  have hxw_le : r - ‖w‖ ≤ ‖w - x‖ := by
    have h1' : ‖x‖ - ‖w‖ ≤ ‖x - w‖ := by linarith
    rw [hx] at h1'
    rw [norm_sub_rev x w] at h1'
    exact h1'
  have hr : 0 ≤ r := (norm_nonneg w).trans hw.le
  have hsum_le : r + ‖w‖ ≤ 2 * r := by nlinarith [hw.le]
  have hnum_le : r ^ 2 - ‖w‖ ^ 2 ≤ 2 * r * ‖w - x‖ := by
    calc
      r ^ 2 - ‖w‖ ^ 2 = (r - ‖w‖) * (r + ‖w‖) := by ring
      _ ≤ ‖w - x‖ * (r + ‖w‖) := by
        have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
        have hnon : 0 ≤ r + ‖w‖ := by nlinarith
        exact mul_le_mul_of_nonneg_right hxw_le hnon
      _ ≤ ‖w - x‖ * (2 * r) := by
        have hwx0 : 0 ≤ ‖w - x‖ := norm_nonneg _
        exact mul_le_mul_of_nonneg_left hsum_le hwx0
      _ = 2 * r * ‖w - x‖ := by ring
  have h2 : (r ^ 2 - ‖w‖ ^ 2) / (θ / 2) ^ 2 ≤ (2 * r * ‖w - x‖) / (θ / 2) ^ 2 :=
    div_le_div_of_nonneg_right hnum_le (sq_nonneg (θ / 2))
  have h3 : (2 * r * ‖w - x‖) / (θ / 2) ^ 2 = (8 * r * ‖w - x‖) / θ ^ 2 := by
    field_simp [hθ.ne']
    ring
  calc
    (r ^ 2 - ‖w‖ ^ 2) / ‖z - w‖ ^ 2 ≤ (r ^ 2 - ‖w‖ ^ 2) / (θ / 2) ^ 2 := h1
    _ ≤ (2 * r * ‖w - x‖) / (θ / 2) ^ 2 := h2
    _ = (8 * r * ‖w - x‖) / θ ^ 2 := h3

/-- Bounded oscillation of g on the sphere. -/
lemma sphere_osc_bound (g : ℂ → ℝ) {r : ℝ} (hr : 0 < r)
    (hg : ContinuousOn g (sphere 0 r)) (x : ℂ) (hx : ‖x‖ = r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, ‖z‖ = r → |g z - g x| ≤ M := by
  obtain ⟨B, hB⟩ := (isCompact_sphere (0 : ℂ) r).exists_bound_of_continuousOn hg
  have hne : (sphere (0 : ℂ) r).Nonempty := by
    refine ⟨(r : ℂ), ?_⟩
    simp [mem_sphere_iff_norm, abs_of_pos hr]
  rcases hne with ⟨y, hy⟩
  have hBy0 : 0 ≤ B := le_trans (norm_nonneg (g y)) (hB y hy)
  refine ⟨2 * B, by nlinarith, ?_⟩
  intro z hz
  have hBz : ‖g z‖ ≤ B := hB z (by simpa [mem_sphere_iff_norm] using hz)
  have hBx : ‖g x‖ ≤ B := hB x (by simpa [mem_sphere_iff_norm] using hx)
  have hBz' : |g z| ≤ B := by simpa [Real.norm_eq_abs] using hBz
  have hBx' : |g x| ≤ B := by simpa [Real.norm_eq_abs] using hBx
  have h1 : |g z - g x| ≤ |g z| + |g x| := by
    simpa [Real.norm_eq_abs] using (norm_sub_le (g z) (g x))
  linarith

end Commons.Analysis.Complex.Harmonic
namespace Commons.Analysis.Complex.Harmonic

/-- Bounding |poissonInt w − g x| by oscillation arc + off-arc kernel estimate. -/
lemma poissonInt_bound (g : ℂ → ℝ) {r : ℝ} (hr : 0 < r)
    (hg : ContinuousOn g (sphere 0 r)) {w x : ℂ} (hw : ‖w‖ < r) (hx : ‖x‖ = r)
    {η M θ : ℝ} (hη : 0 ≤ η) (hM0 : 0 ≤ M)
    (hM : ∀ z : ℂ, ‖z‖ = r → |g z - g x| ≤ M)
    (hθ : 0 < θ)
    (harc : ∀ z : ℂ, ‖z‖ = r → ‖z - x‖ < θ → |g z - g x| ≤ η)
    (hwx : ‖w - x‖ ≤ θ / 2) :
    |poissonInt g r w - g x| ≤ η + M * (8 * r * ‖w - x‖) / θ ^ 2 := by
  let B0 : ℝ := (8 * r * ‖w - x‖) / θ ^ 2
  let k : ℂ → ℝ := fun z => poissonKernel 0 w z
  have hB0pos : 0 ≤ B0 := by
    have hr0 : 0 ≤ r := (norm_nonneg w).trans hw.le
    exact div_nonneg (mul_nonneg (by positivity) (norm_nonneg _)) (sq_pos_of_pos hθ).le
  -- pointwise bound on the sphere
  have hpoint : ∀ z ∈ sphere 0 r,
      poissonKernel 0 w z * |g z - g x| ≤ η * poissonKernel 0 w z + M * B0 := by
    intro z hz
    have hzr : ‖z‖ = r := by simpa [mem_sphere_iff_norm] using hz
    have he0 : 0 ≤ |g z - g x| := abs_nonneg _
    by_cases hnear : ‖z - x‖ < θ
    · have he : |g z - g x| ≤ η := harc z hzr hnear
      have hk0 : 0 ≤ poissonKernel 0 w z := poissonKernel_pos_r hw hzr
      have hmul : poissonKernel 0 w z * |g z - g x| ≤ poissonKernel 0 w z * η :=
        mul_le_mul_of_nonneg_left he hk0
      have hMB0 : 0 ≤ M * B0 := mul_nonneg hM0 hB0pos
      calc
        poissonKernel 0 w z * |g z - g x| ≤ poissonKernel 0 w z * η := hmul
        _ = η * poissonKernel 0 w z := by ring
        _ ≤ η * poissonKernel 0 w z + M * B0 := by
          simpa [add_comm] using (le_add_of_nonneg_left hMB0 : η * poissonKernel 0 w z ≤ M * B0 + η * poissonKernel 0 w z)
    · have hfar : θ ≤ ‖z - x‖ := le_of_not_gt hnear
      have hk_le : poissonKernel 0 w z ≤ B0 := by
        simpa [B0] using poissonKernel_offArc_bound hw hθ hwx hx hfar hzr
      have hmul1 : poissonKernel 0 w z * |g z - g x| ≤ B0 * |g z - g x| := by
        exact mul_le_mul_of_nonneg_right hk_le he0
      have hB00 : 0 ≤ B0 := hB0pos
      have heM : |g z - g x| ≤ M := hM z hzr
      have hmul2 : B0 * |g z - g x| ≤ B0 * M := mul_le_mul_of_nonneg_left heM hB00
      have hηk0 : 0 ≤ η * poissonKernel 0 w z := mul_nonneg hη (poissonKernel_pos_r hw hzr)
      have hMle : B0 * M = M * B0 := by ring
      calc
        poissonKernel 0 w z * |g z - g x| ≤ B0 * |g z - g x| := hmul1
        _ ≤ B0 * M := hmul2
        _ ≤ η * poissonKernel 0 w z + B0 * M := le_add_of_nonneg_left hηk0
        _ = η * poissonKernel 0 w z + M * B0 := by rw [hMle]
  -- circle-average machinery
  have hkcont : ContinuousOn k (sphere 0 r) := continuousOn_poissonKernel_sphere_r hw
  have hLcont : ContinuousOn (fun z : ℂ => poissonKernel 0 w z * |g z - g x|) (sphere 0 r) := by
    intro z hz
    have hgsub : ContinuousWithinAt (fun z : ℂ => g z - g x) (sphere 0 r) z :=
      (hg z hz).sub continuousWithinAt_const
    exact (hkcont z hz).mul hgsub.abs
  have hRcont : ContinuousOn (fun z : ℂ => η * poissonKernel 0 w z + M * B0) (sphere 0 r) := by
    intro z hz
    exact ((hkcont z hz).const_mul η).add (continuousWithinAt_const : ContinuousWithinAt (fun _ : ℂ => M * B0) (sphere 0 r) z)
  have hLint : CircleIntegrable (fun z : ℂ => poissonKernel 0 w z * |g z - g x|) 0 r := by
    apply (show ContinuousOn (fun z : ℂ => poissonKernel 0 w z * |g z - g x|) (sphere 0 |r|)
      from by simpa [abs_of_pos hr] using hLcont).circleIntegrable'
  have hRint : CircleIntegrable (fun z : ℂ => η * poissonKernel 0 w z + M * B0) 0 r := by
    apply (show ContinuousOn (fun z : ℂ => η * poissonKernel 0 w z + M * B0) (sphere 0 |r|)
      from by simpa [abs_of_pos hr] using hRcont).circleIntegrable'
  have hmono : Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * |g z - g x|) 0 r
      ≤ Real.circleAverage (fun z : ℂ => η * poissonKernel 0 w z + M * B0) 0 r := by
    refine Real.circleAverage_mono hLint hRint ?_
    intro z hz
    exact hpoint z (by simpa [abs_of_pos hr] using hz)
  have hRavg : Real.circleAverage (fun z : ℂ => η * poissonKernel 0 w z + M * B0) 0 r
      = η + M * B0 := by
    have hsmul : Real.circleAverage (fun z : ℂ => η • k z) 0 r = η • Real.circleAverage k 0 r :=
      Real.circleAverage_fun_smul (a := η) (f := k)
    have hkcont' : ContinuousOn k (sphere 0 |r|) := by
      simpa [abs_of_pos hr] using hkcont
    have hηk_int : CircleIntegrable (fun z : ℂ => η • k z) 0 r := by
      apply ContinuousOn.circleIntegrable'
      simpa [Pi.smul_apply, smul_eq_mul] using hkcont'.const_mul η
    have hcst_int : CircleIntegrable (fun _ : ℂ => M * B0) 0 r := circleIntegrable_const _ _ _
    have hsum : Real.circleAverage (fun z : ℂ => η • k z + (fun _ : ℂ => M * B0) z) 0 r
        = Real.circleAverage (fun z : ℂ => η • k z) 0 r + Real.circleAverage (fun _ : ℂ => M * B0) 0 r :=
      Real.circleAverage_fun_add hηk_int hcst_int
    have hcst : Real.circleAverage (fun _ : ℂ => M * B0) 0 r = M * B0 := Real.circleAverage_const _ _ _
    calc
      Real.circleAverage (fun z : ℂ => η * poissonKernel 0 w z + M * B0) 0 r
          = Real.circleAverage (fun z : ℂ => η • k z + (fun _ : ℂ => M * B0) z) 0 r := by
            apply congrArg (fun F : ℂ → ℝ => Real.circleAverage F 0 r)
            funext z
            simp [k, smul_eq_mul]
      _ = Real.circleAverage (fun z : ℂ => η • k z) 0 r + Real.circleAverage (fun _ : ℂ => M * B0) 0 r := hsum
      _ = η • Real.circleAverage k 0 r + M * B0 := by rw [hsmul, hcst]
      _ = η + M * B0 := by
        have hmass : Real.circleAverage k 0 r = 1 := by simpa [k] using poisson_total_mass_r hr hw
        simp [hmass]
  have habs := abs_circleAverage_le_circleAverage_abs (f := fun z : ℂ => poissonKernel 0 w z * (g z - g x))
      (c := (0 : ℂ)) (R := r)
  have hsub := poissonInt_sub g hr hg hw hx
  -- |fun z => k z * (g z - g x)| = fun z => k z * |g z - g x| on the sphere
  have hfun : Set.EqOn (fun z : ℂ => |poissonKernel 0 w z * (g z - g x)|)
      (fun z : ℂ => poissonKernel 0 w z * |g z - g x|) (sphere 0 r) := by
    intro z hz
    have hzr : ‖z‖ = r := by simpa [mem_sphere_iff_norm] using hz
    change |poissonKernel 0 w z * (g z - g x)| = poissonKernel 0 w z * |g z - g x|
    rw [abs_mul, abs_of_nonneg (poissonKernel_pos_r hw hzr)]
  have hc1 : Real.circleAverage (fun z : ℂ => |poissonKernel 0 w z * (g z - g x)|) 0 r
      = Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * |g z - g x|) 0 r := by
    refine Real.circleAverage_congr_sphere ?_
    intro z hz
    exact hfun (by simpa [abs_of_pos hr] using hz)
  calc
    |poissonInt g r w - g x| = |Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * (g z - g x)) 0 r| := by
        rw [poissonInt_sub g hr hg hw hx]
    _ ≤ Real.circleAverage (fun z : ℂ => |poissonKernel 0 w z * (g z - g x)|) 0 r := habs
    _ = Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * |g z - g x|) 0 r := hc1
    _ ≤ Real.circleAverage (fun z : ℂ => η * poissonKernel 0 w z + M * B0) 0 r := hmono
    _ = η + M * B0 := hRavg
    _ = η + M * (8 * r * ‖w - x‖) / θ ^ 2 := by
      dsimp [B0]
      ring_nf

/-- poissonInt is harmonic inside the ball. -/
lemma poissonInt_harmonicOnNhd (g : ℂ → ℝ) {r : ℝ} (hr : 0 < r)
    (hg : ContinuousOn g (sphere 0 r)) :
    HarmonicOnNhd (poissonInt g r) (ball 0 r) := by
  intro x hx
  let G : ℂ → ℂ := fun z => (g z : ℂ)
  have hg_int : CircleIntegrable g 0 r :=
    (show ContinuousOn g (sphere 0 |r|) from by simpa [abs_of_pos hr] using hg).circleIntegrable'
  have hG_int : CircleIntegrable G 0 r := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hg_int ⊢
    exact Complex.ofRealCLM.integrable_comp hg_int
  let F : ℂ → ℂ := fun w => Real.circleAverage (fun z : ℂ => herglotzRieszKernel 0 w z • G z) 0 r
  have hF_analytic : AnalyticOnNhd ℂ F (ball 0 r) :=
    (analyticOnNhd_circleAverage_herglotzRieszKernel_smul (f := G) (R := r) hG_int).mono
      (fun w hw hs => by
        rw [Metric.mem_sphere, dist_zero_right] at hs
        rw [Metric.mem_ball, dist_zero_right] at hw
        linarith [le_abs_self r])
  have hFx : AnalyticAt ℂ F x := hF_analytic x hx
  have hRe : HarmonicAt (fun w : ℂ => (F w).re) x := AnalyticAt.harmonicAt_re hFx
  have h_eq : (fun w : ℂ => (F w).re) =ᶠ[𝓝 x] poissonInt g r := by
    filter_upwards [isOpen_ball.mem_nhds hx] with w hw
    calc
      (F w).re = Real.circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w) • g) 0 r := by
        exact re_circleAverage_herglotzRieszKernel_smul hg_int (fun hs => by
          rw [Metric.mem_sphere, dist_zero_right] at hs
          rw [Metric.mem_ball, dist_zero_right] at hw
          linarith [le_abs_self r])
      _ = Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * g z) 0 r := by
        congr 1
        funext z
        simp [← poissonKernel_eq_re_herglotzRieszKernel (c := (0 : ℂ)) (w := w)]
      _ = poissonInt g r w := by rfl
  exact (harmonicAt_congr_nhds h_eq.symm).mpr hRe

/-- The candidate extension. -/
noncomputable def candidate (g : ℂ → ℝ) (r : ℝ) (w : ℂ) : ℝ :=
  if ‖w‖ < r then poissonInt g r w else g w

/-- Interior continuity of the candidate. -/
lemma candidate_continuousAt_interior (g : ℂ → ℝ) {r : ℝ} (hr : 0 < r)
    (hg : ContinuousOn g (sphere 0 r)) {x : ℂ} (hx : ‖x‖ < r) :
    ContinuousAt (candidate g r) x := by
  have hxball : x ∈ ball 0 r := by simpa [mem_ball, dist_eq_norm] using hx
  have hPFcont : ContinuousAt (poissonInt g r) x :=
    (poissonInt_harmonicOnNhd g hr hg x hxball).1.continuousAt
  have hEq : candidate g r =ᶠ[𝓝 x] poissonInt g r := by
    filter_upwards [isOpen_ball.mem_nhds hxball] with w hw
    have hwlt : ‖w‖ < r := by simpa [mem_ball, dist_eq_norm] using hw
    simp [candidate, hwlt]
  exact hPFcont.congr_of_eventuallyEq hEq

/-- Boundary ε-δ estimate at a boundary point x. -/
lemma candidate_boundary_est (g : ℂ → ℝ) {r : ℝ} (hr : 0 < r)
    (hg : ContinuousOn g (sphere 0 r)) {x : ℂ} (hx : ‖x‖ = r) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, ‖w‖ ≤ r → ‖w - x‖ < δ →
      |candidate g r w - g x| < ε := by
  intro ε hε
  obtain ⟨M, hM0, hM⟩ := sphere_osc_bound g hr hg x hx
  have hxSph : x ∈ sphere 0 r := by simpa [mem_sphere_iff_norm] using hx
  let η : ℝ := ε / 4
  have hηpos : 0 < η := by dsimp [η]; positivity
  obtain ⟨θ0, hθ0, hθ0arc⟩ := (Metric.continuousWithinAt_iff.mp (hg x hxSph)) η hηpos
  have harc : ∀ z : ℂ, ‖z‖ = r → ‖z - x‖ < θ0 → |g z - g x| ≤ η := by
    intro z hz hd
    have hzSph : z ∈ sphere 0 r := by simpa [mem_sphere_iff_norm] using hz
    have h1 := hθ0arc hzSph (by simpa [dist_eq_norm] using hd)
    have : dist (g z) (g x) = |g z - g x| := by simp [dist_eq_norm]
    rw [this] at h1
    exact le_of_lt h1
  -- delta0 := min (θ0/2) (ε * θ0^2 / (24 * r * max M 1))
  let D : ℝ := ε * θ0 ^ 2 / (24 * r * max M 1)
  have hθ02pos : 0 < θ0 ^ 2 := sq_pos_of_pos hθ0
  have hrmaxpos : 0 < 24 * r * max M 1 := by positivity
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  let δ : ℝ := min (θ0 / 2) D
  have hθ0half : 0 < θ0 / 2 := by positivity
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min hθ0half hDpos
  refine ⟨δ, hδpos, ?_⟩
  intro w hwle hwδ
  have hwδle : ‖w - x‖ ≤ δ := le_of_lt hwδ
  have hwx_half : ‖w - x‖ ≤ θ0 / 2 := le_trans hwδle (min_le_left _ _)
  have hwx_D : ‖w - x‖ ≤ D := le_trans hwδle (min_le_right _ _)
  by_cases hwlt : ‖w‖ < r
  · have hmain : M * (8 * r * ‖w - x‖) / θ0 ^ 2 ≤ ε / 3 := by
      have hrpos : 0 < r := lt_of_le_of_lt (norm_nonneg w) hwlt
      have hmaxM : M ≤ max M 1 := le_max_left M 1
      have hmaxpos : 0 < 24 * r * max M 1 := by positivity
      have hA0 : 0 ≤ ‖w - x‖ := norm_nonneg _
      have hB0 : 0 ≤ 24 * r * ‖w - x‖ := by positivity
      have hDdiv : ‖w - x‖ ≤ ε * θ0 ^ 2 / (24 * r * max M 1) := by
        simpa [D] using hwx_D
      have hmm0 : ‖w - x‖ * (24 * r * max M 1) ≤ ε * θ0 ^ 2 :=
        (le_div_iff₀ hmaxpos).mp hDdiv
      have hmm : 24 * r * (max M 1) * ‖w - x‖ ≤ ε * θ0 ^ 2 := by
        nlinarith [hmm0]
      have hchain : 24 * M * r * ‖w - x‖ ≤ 24 * (max M 1) * r * ‖w - x‖ := by
        calc 24 * M * r * ‖w - x‖ = M * (24 * r * ‖w - x‖) := by ring
          _ ≤ (max M 1) * (24 * r * ‖w - x‖) := mul_le_mul_of_nonneg_right hmaxM hB0
          _ = 24 * (max M 1) * r * ‖w - x‖ := by ring
      rw [div_le_iff₀ (sq_pos_of_pos hθ0)]
      rw [show (ε / 3) * θ0 ^ 2 = ε * θ0 ^ 2 / 3 by ring]
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
      nlinarith [hchain, hmm]
    have hbound := poissonInt_bound g hr hg hwlt hx (by dsimp [η]; positivity) hM0 hM hθ0 harc hwx_half
    have hc : candidate g r w = poissonInt g r w := by simp [candidate, hwlt]
    have h1 : |candidate g r w - g x| < ε := by
      rw [hc]
      have hb : |poissonInt g r w - g x| ≤ η + M * (8 * r * ‖w - x‖) / θ0 ^ 2 := hbound
      have hb' : η + M * (8 * r * ‖w - x‖) / θ0 ^ 2 ≤ ε / 4 + ε / 3 := by
        dsimp [η]
        linarith
      have h3 : ε / 4 + ε / 3 < ε := by nlinarith [hε]
      exact lt_of_le_of_lt (le_trans hb hb') h3
    exact h1
  · have hwnorm : ‖w‖ = r := le_antisymm hwle (le_of_not_gt hwlt)
    have hwSph : w ∈ sphere 0 r := by simpa [mem_sphere_iff_norm] using hwnorm
    have hwδ_θ : ‖w - x‖ < θ0 := by
      have h1 : δ ≤ θ0 / 2 := by dsimp [δ]; exact min_le_left _ _
      have h2 : θ0 / 2 < θ0 := by exact half_lt_self hθ0
      exact lt_of_le_of_lt (le_trans (le_of_lt hwδ) h1) h2
    have hdist : dist (g w) (g x) < η := by
      exact hθ0arc hwSph (by simpa [dist_eq_norm] using hwδ_θ)
    have hc : candidate g r w = g w := by simp [candidate, hwlt]
    have hgx : |g w - g x| < ε := by
      have hdg : dist (g w) (g x) = |g w - g x| := by simp [dist_eq_norm]
      have hηε : η < ε := by dsimp [η]; nlinarith
      exact lt_of_le_of_lt (le_of_lt (by simpa [hdg] using hdist)) hηε
    simpa [hc] using hgx


/-- Candidate is continuous on the closed ball. -/
lemma candidate_continuousOn_closedBall (g : ℂ → ℝ) {r : ℝ} (hr : 0 < r)
    (hg : ContinuousOn g (sphere 0 r)) :
    ContinuousOn (candidate g r) (closedBall 0 r) := by
  intro x hx
  have hxnorm : ‖x‖ ≤ r := by simpa [mem_closedBall_iff_norm] using hx
  by_cases hlt : ‖x‖ < r
  · exact (candidate_continuousAt_interior g hr hg hlt).continuousWithinAt
  · have hxr : ‖x‖ = r := le_antisymm hxnorm (le_of_not_gt hlt)
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδprop⟩ := candidate_boundary_est g hr hg hxr ε hε
    refine ⟨δ, hδ, ?_⟩
    intro w hwS hwd
    have hwle : ‖w‖ ≤ r := by simpa [mem_closedBall_iff_norm] using hwS
    have hwxn : ‖w - x‖ < δ := by simpa [dist_eq_norm] using hwd
    have h := hδprop w hwle hwxn
    have hcx : candidate g r x = g x := by
      simp [candidate, hlt]
    simpa [hcx, dist_eq_norm] using h

/-- Candidate is harmonic on the open ball. -/
lemma candidate_harmonicOnNhd (g : ℂ → ℝ) {r : ℝ} (hr : 0 < r)
    (hg : ContinuousOn g (sphere 0 r)) :
    HarmonicOnNhd (candidate g r) (ball 0 r) := by
  intro x hx
  have hPFx : HarmonicAt (poissonInt g r) x := poissonInt_harmonicOnNhd g hr hg x hx
  have hEq : candidate g r =ᶠ[𝓝 x] poissonInt g r := by
    filter_upwards [isOpen_ball.mem_nhds hx] with w hw
    have hwlt : ‖w‖ < r := by simpa [mem_ball, dist_eq_norm] using hw
    simp [candidate, hwlt]
  exact (harmonicAt_congr_nhds hEq).mpr hPFx

/-- **Dirichlet problem on a circle with continuous boundary data.**
Given a continuous real function `g` on the circle `sphere (0:ℂ) r` (center `0`,
radius `r > 0`), there exists `P : ℂ → ℝ` which is harmonic on the open ball
`ball 0 r`, continuous on the closure `closedBall 0 r`, and agrees with `g` on
the circle.  (Standard Poisson-integral solution: reduce by rotation/scaling to
`r = 1`; define
`P w := Real.circleAverage (fun z ↦ poissonKernel 0 w z • g z) 0 1`
for `w ∈ ball 0 1`; harmonicity on the ball via
`analyticOnNhd_circleAverage_herglotzRieszKernel_smul`
(`Mathlib/Analysis/Complex/Poisson.lean`) applied to `fun z ↦ (g z : ℂ)` +
`poissonKernel_eq_re_herglotzRieszKernel` + `AnalyticAt.harmonicAt_re`
(`Mathlib/Analysis/InnerProductSpace/Harmonic/Constructions.lean`) +
`harmonicAt_congr_nhds`; boundary values: approximate-identity argument
splitting the circle average near the boundary point (kernel mass → 1, kernel
bounded by `(1+‖w‖)/(1-‖w‖)`, kernel uniformly small off the approach arc via
`Commons.Analysis.Complex.poissonKernel_offArc_le`, `poissonKernel_pos`,
`poissonKernel_bound`, total mass 1 via
`InnerProductSpace.HarmonicContOnCl.circleAverage_poissonKernel_smul`
applied to the constant function `1`).  -/
theorem dirichlet_circle_boundary {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r)
    (hg : ContinuousOn g (sphere (0 : ℂ) r)) :
    ∃ P : ℂ → ℝ,
      InnerProductSpace.HarmonicContOnCl P (ball (0 : ℂ) r) ∧
        (∀ z : ℂ, ‖z‖ = r → P z = g z) := by
  refine ⟨candidate g r, ?_, ?_⟩
  · constructor
    · exact candidate_harmonicOnNhd g hr hg
    · have hcc := candidate_continuousOn_closedBall g hr hg
      rw [closure_ball (0 : ℂ) hr.ne']
      exact hcc
  · intro z hz
    have hnotlt : ¬‖z‖ < r := by linarith
    simp [candidate, hnotlt]

end Commons.Analysis.Complex.Harmonic