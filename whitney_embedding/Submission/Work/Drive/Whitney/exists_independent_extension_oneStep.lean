import Mathlib
import Submission.Work.Drive.Whitney.marchingTransport3
import Submission.Work.Drive.Whitney.uniformCloseness_clampedShell
import Submission.Work.Drive.Whitney.smooth_kernelProjection_twoParam

/-!
# One-step independent extension

`Work.Drive.Whitney.exists_independent_extension_oneStep`: given a smooth family
`b : ℝ → ℝ → (Fin k → ℝ^m)` of pointwise linearly independent `k`-tuples with `k < m`, there is a
smooth `w : ℝ → ℝ → ℝ^m` with `Fin.snoc (b s t) (w s t)` pointwise independent.

The proof constructs a smooth nonvanishing section of the complement bundle
`W x = (span (b x))ᵖ` over the plane `ℝ²`, by the radial-shell marching transport
(`Work.Drive.Whitney.marchingTransport_gen`): the plane `x = (0,0)` is a single point, and the
transport of a fixed vector along the shell `[a n, a n + 1]` gives a section there; consecutive
shells are chained at their common inner sphere and glued with a radial partition of unity.

This file contains the infrastructure: normalisation, the clamping function `ψ` used as transverse
parameter of the shell families, and the radial partition of unity.
-/

set_option maxHeartbeats 4000000

namespace Work.Drive.Whitney

open scoped ContDiff Topology
open Set Metric Filter

noncomputable section

/-! ## 1. Normalisation of a vector -/

/-- The normalisation `v ⧸ ‖v‖` of a vector. -/
def nz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : E) : E := ‖v‖⁻¹ • v

theorem nz_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    nz (0 : E) = 0 := by
  simp [nz]

theorem norm_nz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) (hv : v ≠ 0) : ‖nz v‖ = 1 := by
  rw [nz, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

theorem nz_ne_zero_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v : E} : nz v ≠ 0 ↔ v ≠ 0 := by
  constructor
  · intro h hv
    rw [hv, nz_zero] at h
    exact h rfl
  · intro hv h
    have h1 := norm_nz v hv
    rw [h, norm_zero] at h1
    exact one_ne_zero h1.symm

theorem nz_eq_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v : E} (hv : ‖v‖ = 1) : nz v = v := by
  rw [nz, hv, inv_one, one_smul]

theorem nz_smul_of_pos {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ℝ) (hc : 0 < c) (v : E) : nz (c • v) = nz v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [nz]
  · have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    rw [nz, nz, norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul]
    congr 1
    field_simp

theorem contDiffOn_nz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : E => nz v) ({0}ᶜ : Set E) := by
  have hnorm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : E => ‖v‖) ({0}ᶜ : Set E) :=
    (contDiffOn_id (𝕜 := ℝ)).norm ℝ (fun x hx => hx)
  have hinv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : E => (‖v‖)⁻¹) ({0}ᶜ : Set E) :=
    hnorm.inv (fun x hx => norm_ne_zero_iff.mpr hx)
  have hfin : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : E => (fun w : E => (‖w‖)⁻¹) v • (id : E → E) v) ({0}ᶜ : Set E) :=
    hinv.smul (contDiffOn_id (𝕜 := ℝ) (E := E))
  simpa only [nz, id_eq] using hfin

/-- A convex combination of two unit vectors with inner product at least `1/2` is bounded away
from zero. -/
theorem norm_convex_combination_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (h : (1 / 2 : ℝ) ≤ inner ℝ u v)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (3 / 4 : ℝ) ≤ ‖(1 - t) • u + t • v‖ ^ 2 := by
  have h1 : ‖(1 - t) • u + t • v‖ ^ 2
      = (1 - t) ^ 2 * ‖u‖ ^ 2 + 2 * ((1 - t) * t) * inner ℝ u v + t ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
    ring
  rw [h1, hu, hv]
  have ht : 0 ≤ 2 * ((1 - t) * t) := by nlinarith
  have h2 : 2 * ((1 - t) * t) * (1 / 2) ≤ 2 * ((1 - t) * t) * inner ℝ u v :=
    mul_le_mul_of_nonneg_left h ht
  nlinarith [h2, sq_nonneg (t - 1 / 2)]

/-! ## 2. The clamp factor -/

/-- A smooth clamp factor: `1` for `t ≤ 1`, `1 ⧸ t` for `t ≥ 2`. -/
def clampC (t : ℝ) : ℝ := (1 + Real.smoothTransition (t - 1) * (t - 1))⁻¹

theorem clampC_pos (t : ℝ) : 0 < clampC t := by
  rw [clampC, inv_pos]
  rcases le_total t 1 with h | h
  · have h0 : Real.smoothTransition (t - 1) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by linarith)
    rw [h0, zero_mul]
    norm_num
  · have h1 : 0 ≤ Real.smoothTransition (t - 1) * (t - 1) :=
      mul_nonneg (Real.smoothTransition.nonneg _) (by linarith)
    linarith

theorem clampC_eq_one {t : ℝ} (ht : t ≤ 1) : clampC t = 1 := by
  rw [clampC, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul, add_zero, inv_one]

theorem clampC_eq_inv {t : ℝ} (ht : 2 ≤ t) : clampC t = t⁻¹ := by
  have h1 : 1 ≤ t - 1 := by linarith
  rw [clampC, Real.smoothTransition.one_of_one_le h1, one_mul]
  congr 1
  ring

theorem clampC_le_one {t : ℝ} (ht : 1 ≤ t) : clampC t ≤ 1 := by
  have h2 : 0 ≤ Real.smoothTransition (t - 1) * (t - 1) :=
    mul_nonneg (Real.smoothTransition.nonneg _) (by linarith)
  rw [clampC, inv_le_one₀ (by linarith)]
  linarith

theorem clampC_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) clampC := by
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun t : ℝ => (1 + Real.smoothTransition (t - 1) * (t - 1))⁻¹)
  refine ContDiff.inv (by fun_prop) (fun t => ?_)
  have h := clampC_pos t
  rw [clampC] at h
  exact ne_of_gt (inv_pos.mp h)

theorem clampC_nonneg (t : ℝ) : 0 ≤ clampC t := le_of_lt (clampC_pos t)

/-! ## 3. The Euclidean radius on `ℝ × ℝ` -/

/-- The Euclidean radius of a point of `ℝ × ℝ` (the product type carries only the sup norm, so we
use the Euclidean radius explicitly). -/
def rad2 (x : ℝ × ℝ) : ℝ := Real.sqrt (x.1 ^ 2 + x.2 ^ 2)

theorem rad2_sq (x : ℝ × ℝ) : rad2 x ^ 2 = x.1 ^ 2 + x.2 ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem rad2_nonneg (x : ℝ × ℝ) : 0 ≤ rad2 x := Real.sqrt_nonneg _

theorem rad2_pos {x : ℝ × ℝ} (hx : x ≠ 0) : 0 < rad2 x := by
  rw [rad2, Real.sqrt_pos]
  have h : x.1 ≠ 0 ∨ x.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (Prod.ext h.1 h.2)
  rcases h with h | h
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg x.2]
  · nlinarith [sq_nonneg x.1, sq_pos_of_ne_zero h]

theorem rad2_eq_zero_iff {x : ℝ × ℝ} : rad2 x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h2 : x.1 ^ 2 + x.2 ^ 2 = 0 := by
      have h' : Real.sqrt (x.1 ^ 2 + x.2 ^ 2) = 0 := by rw [← rad2]; exact h
      have h3 : x.1 ^ 2 + x.2 ^ 2 ≤ 0 := Real.sqrt_eq_zero'.mp h'
      exact le_antisymm h3 (by positivity)
    have h1 : x.1 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
    have h3 : x.2 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
    exact Prod.ext h1 h3
  · intro h
    subst h
    simp [rad2]

theorem rad2_smul (c : ℝ) (u : ℝ × ℝ) : rad2 (c • u) = |c| * rad2 u := by
  have h : (c • u).1 ^ 2 + (c • u).2 ^ 2 = c ^ 2 * (u.1 ^ 2 + u.2 ^ 2) := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [rad2, h, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, rad2]

theorem le_rad2 (u : ℝ × ℝ) : ‖u‖ ≤ rad2 u := by
  have key : max |u.1| |u.2| ≤ rad2 u := by
    rw [rad2, Real.le_sqrt (by positivity) (by positivity)]
    rcases le_total |u.1| |u.2| with h | h
    · rw [max_eq_right h]; nlinarith [sq_abs u.2, sq_nonneg u.1]
    · rw [max_eq_left h]; nlinarith [sq_abs u.1, sq_nonneg u.2]
  calc ‖u‖ = max ‖u.1‖ ‖u.2‖ := Prod.norm_def u
    _ = max |u.1| |u.2| := by simp only [Real.norm_eq_abs]
    _ ≤ rad2 u := key

theorem rad2_contDiffAt {x : ℝ × ℝ} (hx : x ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) rad2 x := by
  have hpos : x.1 ^ 2 + x.2 ^ 2 ≠ 0 := by
    intro h
    exact hx (rad2_eq_zero_iff.mp (by rw [rad2, h, Real.sqrt_zero]))
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × ℝ => x.1 ^ 2 + x.2 ^ 2) x := by
    fun_prop
  exact (Real.contDiffAt_sqrt hpos).comp x h1

theorem contDiff_comp_rad2 {c : ℝ → ℝ} (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) {ε : ℝ}
    (hε : 0 < ε) (hc0 : ∀ t, t ≤ ε → c t = c 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × ℝ => c (rad2 x)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    refine (contDiffAt_const (c := c 0)).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ × ℝ) (by positivity : (0 : ℝ) < ε / 2)] with y hy
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def] at hy
    have h1 : rad2 y ≤ ε := by
      rw [rad2, Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have h2 : max ‖y.1‖ ‖y.2‖ < ε / 2 := by rw [← Prod.norm_def]; exact hy
      have h3 : ‖y.1‖ < ε / 2 := lt_of_le_of_lt (le_max_left _ _) h2
      have h4 : ‖y.2‖ < ε / 2 := lt_of_le_of_lt (le_max_right _ _) h2
      nlinarith [abs_lt.mp h3, abs_lt.mp h4, sq_nonneg (y.1), sq_nonneg (y.2)]
    exact hc0 _ h1
  · exact hc.contDiffAt.comp x (rad2_contDiffAt hx)

/-! ## 4. The clamped direction -/

/-- The scalar clamp function of the radius. -/
def clampFun (η : ℝ) (t : ℝ) : ℝ := η⁻¹ * clampC (t / η)

/-- The clamped direction: `u ⧸ η` for `rad2 u ≤ η`, `u ⧸ rad2 u` for `rad2 u ≥ 2η`. -/
def psiFun (η : ℝ) (u : ℝ × ℝ) : ℝ × ℝ := clampFun η (rad2 u) • u

theorem clampFun_contDiff {η : ℝ} (hη : 0 < η) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (clampFun η) := by
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => η⁻¹ * clampC (t / η))
  exact contDiff_const.mul (clampC_contDiff.comp (contDiff_id.div_const η))

theorem clampFun_eq_inv {η : ℝ} (hη : 0 < η) {t : ℝ} (ht : 2 * η ≤ t) :
    clampFun η t = t⁻¹ := by
  show η⁻¹ * clampC (t / η) = t⁻¹
  rw [clampC_eq_inv (by rw [le_div_iff₀ hη]; linarith)]
  field_simp

theorem clampFun_eq {η : ℝ} (hη : 0 < η) {t : ℝ} (ht : t ≤ η) : clampFun η t = η⁻¹ := by
  show η⁻¹ * clampC (t / η) = η⁻¹
  rw [clampC_eq_one (by rw [div_le_one hη]; exact ht), mul_one]

theorem clampFun_nonneg {η : ℝ} (hη : 0 < η) (t : ℝ) : 0 ≤ clampFun η t :=
  mul_nonneg (inv_nonneg.mpr hη.le) (clampC_nonneg _)

theorem clampFun_mul_le_two {η : ℝ} (hη : 0 < η) {t : ℝ} (ht : 0 ≤ t) :
    t * clampFun η t ≤ 2 := by
  show t * (η⁻¹ * clampC (t / η)) ≤ 2
  rcases le_total t η with h | h
  · have h1 : clampC (t / η) = 1 := clampC_eq_one (by rw [div_le_one hη]; exact h)
    rw [h1, mul_one, ← div_eq_mul_inv, div_le_iff₀ hη]
    linarith
  · have htη : (1 : ℝ) ≤ t / η := by rw [le_div_iff₀ hη]; linarith
    rcases le_total t (2 * η) with h2 | h2
    · have h3 : clampC (t / η) ≤ 1 := clampC_le_one htη
      have h4 : 0 ≤ t * η⁻¹ := mul_nonneg ht (inv_nonneg.mpr hη.le)
      calc t * (η⁻¹ * clampC (t / η)) = (t * η⁻¹) * clampC (t / η) := by ring
        _ ≤ (t * η⁻¹) * 1 := mul_le_mul_of_nonneg_left h3 h4
        _ = t / η := by rw [mul_one, div_eq_mul_inv]
        _ ≤ 2 := by rw [div_le_iff₀ hη]; linarith
    · have htpos : 0 < t := lt_of_lt_of_le hη h
      have h3 : clampC (t / η) = (t / η)⁻¹ := by
        rw [clampC_eq_inv (by rw [le_div_iff₀ hη]; linarith)]
      rw [h3, div_eq_mul_inv, mul_inv]
      field_simp
      linarith

theorem psiFun_contDiff {η : ℝ} (hη : 0 < η) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (psiFun η) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ × ℝ => clampFun η (rad2 u)) := by
    refine contDiff_comp_rad2 (clampFun_contDiff hη) hη (fun t ht => ?_)
    rw [clampFun_eq hη ht, clampFun_eq hη (by positivity : (0 : ℝ) ≤ η)]
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ × ℝ => clampFun η (rad2 u) • u)
  exact h1.smul contDiff_id

theorem psiFun_bound {η : ℝ} (hη : 0 < η) (u : ℝ × ℝ) : ‖psiFun η u‖ ≤ 2 := by
  have h1 : ‖psiFun η u‖ ≤ rad2 (psiFun η u) := le_rad2 _
  have h2 : rad2 (psiFun η u) = clampFun η (rad2 u) * rad2 u := by
    rw [psiFun, rad2_smul, abs_of_nonneg (clampFun_nonneg hη _)]
  have h3 : rad2 u * clampFun η (rad2 u) ≤ 2 := clampFun_mul_le_two hη (rad2_nonneg u)
  rw [h2] at h1
  linarith

/-- The clamped direction agrees with the honest one outside the clamp ball. -/
theorem psiFun_eq_dir {η : ℝ} (hη : 0 < η) {u : ℝ × ℝ} (hu : 2 * η ≤ rad2 u) :
    psiFun η u = (rad2 u)⁻¹ • u := by
  rw [psiFun, clampFun_eq_inv hη hu]

/-- Multiplication by the radius undoes the clamped direction. -/
theorem smul_psiFun_self {η : ℝ} (hη : 0 < η) {u : ℝ × ℝ} (hu : 2 * η ≤ rad2 u) :
    rad2 u • psiFun η u = u := by
  rw [psiFun_eq_dir hη hu, smul_smul, mul_inv_cancel₀ (ne_of_gt (lt_of_lt_of_le (by linarith) hu)),
    one_smul]


theorem rad2_le_sqrt_two_mul_norm (y : ℝ × ℝ) : rad2 y ≤ Real.sqrt 2 * ‖y‖ := by
  have hnorm : ‖y‖ = max |y.1| |y.2| := by
    rw [Prod.norm_def]
    simp only [Real.norm_eq_abs]
  have hkey : y.1 ^ 2 + y.2 ^ 2 ≤ (Real.sqrt 2 * ‖y‖) ^ 2 := by
    rw [hnorm, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [le_max_left |y.1| |y.2|, le_max_right |y.1| |y.2|,
      sq_abs y.1, sq_abs y.2, abs_nonneg y.1, abs_nonneg y.2]
  have h2 : 0 ≤ Real.sqrt 2 * ‖y‖ := by positivity
  calc rad2 y = Real.sqrt (rad2 y ^ 2) := (Real.sqrt_sq (rad2_nonneg y)).symm
    _ = Real.sqrt (y.1 ^ 2 + y.2 ^ 2) := by rw [rad2_sq]
    _ ≤ Real.sqrt ((Real.sqrt 2 * ‖y‖) ^ 2) := Real.sqrt_le_sqrt hkey
    _ = Real.sqrt 2 * ‖y‖ := Real.sqrt_sq h2

theorem sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

theorem continuous_rad2 : Continuous rad2 := by
  show Continuous fun x : ℝ × ℝ => Real.sqrt (x.1 ^ 2 + x.2 ^ 2)
  fun_prop

/-! ## 6. The radial shells and the partition of unity -/

/-- The inner radii of the shells: `a n = R₀ + n / 2`. -/
def aSeq (R₀ : ℝ) (n : ℕ) : ℝ := R₀ + (n : ℝ) / 2

theorem aSeq_mono (R₀ : ℝ) : Monotone (aSeq R₀) := by
  intro m n h
  simp only [aSeq]
  have h' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  linarith

theorem aSeq_succ (R₀ : ℝ) (n : ℕ) : aSeq R₀ (n + 1) = aSeq R₀ n + 1 / 2 := by
  simp only [aSeq]; push_cast; ring

theorem aSeq_nonneg {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (n : ℕ) : 0 ≤ aSeq R₀ n := by
  simp only [aSeq]; positivity

theorem le_aSeq (R₀ : ℝ) (n : ℕ) : R₀ ≤ aSeq R₀ n := by
  simp only [aSeq]
  have : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
  linarith

theorem aSeq_lt_succ {R₀ : ℝ} (n : ℕ) : aSeq R₀ n < aSeq R₀ (n + 1) := by
  have h := aSeq_succ R₀ n
  linarith

/-- The bump of the radial partition of unity. -/
def Theta (R₀ : ℝ) (w : ℕ → ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  Real.smoothTransition ((r - aSeq R₀ n) / w n)

/-- The radial partition of unity. -/
def Chi (R₀ : ℝ) (w : ℕ → ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  Theta R₀ w n r - Theta R₀ w (n + 1) r

/-- The truncation index: `Nat.floor ((rad2 x - R₀) * 2) + 2`. -/
def Nidx (R₀ : ℝ) (x : ℝ × ℝ) : ℕ := Nat.floor ((rad2 x - R₀) * 2) + 2

theorem Theta_contDiff (R₀ : ℝ) (w : ℕ → ℝ) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Theta R₀ w n) := by
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun r : ℝ => Real.smoothTransition ((r - aSeq R₀ n) / w n))
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem Chi_contDiff (R₀ : ℝ) (w : ℕ → ℝ) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Chi R₀ w n) :=
  (Theta_contDiff R₀ w n).sub (Theta_contDiff R₀ w (n + 1))

theorem Theta_nonneg (R₀ : ℝ) (w : ℕ → ℝ) (n : ℕ) (r : ℝ) : 0 ≤ Theta R₀ w n r :=
  Real.smoothTransition.nonneg _

theorem Theta_le_one (R₀ : ℝ) (w : ℕ → ℝ) (n : ℕ) (r : ℝ) : Theta R₀ w n r ≤ 1 :=
  Real.smoothTransition.le_one _

theorem Theta_zero_of_le {R₀ : ℝ} {w : ℕ → ℝ} {n : ℕ} (hw : 0 < w n) {r : ℝ}
    (h : r ≤ aSeq R₀ n) : Theta R₀ w n r = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le

theorem Theta_one_of_le {R₀ : ℝ} {w : ℕ → ℝ} {n : ℕ} (hw : 0 < w n) {r : ℝ}
    (h : aSeq R₀ n + w n ≤ r) : Theta R₀ w n r = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  rw [le_div_iff₀ hw]
  linarith

theorem Theta_lt_one {R₀ : ℝ} {w : ℕ → ℝ} {n : ℕ} (hw : 0 < w n) {r : ℝ}
    (h : r < aSeq R₀ n + w n) : Theta R₀ w n r < 1 := by
  refine Real.smoothTransition.lt_one_of_lt_one ?_
  rw [div_lt_one hw]
  linarith

theorem Theta_pos {R₀ : ℝ} {w : ℕ → ℝ} {n : ℕ} (hw : 0 < w n) {r : ℝ}
    (h : aSeq R₀ n < r) : 0 < Theta R₀ w n r := by
  refine Real.smoothTransition.pos_of_pos ?_
  exact div_pos (by linarith) hw

theorem Theta_eq_zero_iff {R₀ : ℝ} {w : ℕ → ℝ} {n : ℕ} (hw : 0 < w n) (r : ℝ) :
    Theta R₀ w n r = 0 ↔ r ≤ aSeq R₀ n := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact absurd h (ne_of_gt (Theta_pos hw hc))
  · exact Theta_zero_of_le hw

theorem Theta_eq_one_iff {R₀ : ℝ} {w : ℕ → ℝ} {n : ℕ} (hw : 0 < w n) (r : ℝ) :
    Theta R₀ w n r = 1 ↔ aSeq R₀ n + w n ≤ r := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have h1 := Theta_lt_one hw hc
    rw [h] at h1
    exact lt_irrefl 1 h1
  · exact Theta_one_of_le hw

theorem Chi_nonneg {R₀ : ℝ} {w : ℕ → ℝ} (hw : ∀ n, 0 < w n)
    (hgap : ∀ n, aSeq R₀ n + w n ≤ aSeq R₀ (n + 1)) (n : ℕ) (r : ℝ) :
    0 ≤ Chi R₀ w n r := by
  rw [Chi]
  by_cases h1 : r ≤ aSeq R₀ n
  · rw [Theta_zero_of_le (hw n) h1,
      Theta_zero_of_le (hw (n + 1)) (le_trans h1 (le_of_lt (aSeq_lt_succ n))), sub_zero]
  · push Not at h1
    rcases le_total r (aSeq R₀ n + w n) with h2 | h2
    · rw [Theta_zero_of_le (hw (n + 1)) (le_trans h2 (hgap n)), sub_zero]
      exact Theta_nonneg _ _ _ _
    · rw [Theta_one_of_le (hw n) h2]
      linarith [Theta_le_one R₀ w (n + 1) r]

theorem Chi_sum_range {R₀ : ℝ} {w : ℕ → ℝ} (N : ℕ) (r : ℝ) :
    ∑ n ∈ Finset.range N, Chi R₀ w n r = Theta R₀ w 0 r - Theta R₀ w N r := by
  simp only [Chi]
  exact Finset.sum_range_sub' (fun n => Theta R₀ w n r) N

theorem Chi_support {R₀ : ℝ} {w : ℕ → ℝ} (hw : ∀ n, 0 < w n)
    (hgap : ∀ n, aSeq R₀ n + w n ≤ aSeq R₀ (n + 1)) {n : ℕ} {r : ℝ}
    (h : Chi R₀ w n r ≠ 0) :
    aSeq R₀ n < r ∧ r < aSeq R₀ (n + 1) + w (n + 1) := by
  have hne : Theta R₀ w n r ≠ Theta R₀ w (n + 1) r := by
    intro hc
    exact h (by rw [Chi, hc, sub_self])
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : 0 < Theta R₀ w (n + 1) r := lt_of_le_of_lt (Theta_nonneg _ _ _ _) hlt
    have h2 : aSeq R₀ (n + 1) < r := by
      by_contra hc
      push Not at hc
      rw [Theta_eq_zero_iff (hw (n + 1)) r |>.mpr hc] at h1
      exact lt_irrefl 0 h1
    have h3 : r < aSeq R₀ n + w n := by
      by_contra hc
      push Not at hc
      have h4 : Theta R₀ w n r = 1 := Theta_eq_one_iff (hw n) r |>.mpr hc
      have h5 : Theta R₀ w (n + 1) r ≤ 1 := Theta_le_one _ _ _ _
      linarith
    exact ⟨lt_trans (aSeq_lt_succ n) h2, by linarith [hgap n, hw (n + 1)]⟩
  · have h1 : 0 < Theta R₀ w n r := lt_of_le_of_lt (Theta_nonneg _ _ _ _) hgt
    have h2 : aSeq R₀ n < r := by
      by_contra hc
      push Not at hc
      rw [Theta_eq_zero_iff (hw n) r |>.mpr hc] at h1
      exact lt_irrefl 0 h1
    have h3 : r < aSeq R₀ (n + 1) + w (n + 1) := by
      by_contra hc
      push Not at hc
      have h4 : Theta R₀ w (n + 1) r = 1 := Theta_eq_one_iff (hw (n + 1)) r |>.mpr hc
      have h5 : Theta R₀ w n r ≤ 1 := Theta_le_one _ _ _ _
      linarith
    exact ⟨h2, h3⟩

theorem Chi_eq_zero_of_le {R₀ : ℝ} {w : ℕ → ℝ} (hw : ∀ n, 0 < w n) {n : ℕ} {r : ℝ}
    (h : r ≤ aSeq R₀ n) : Chi R₀ w n r = 0 := by
  rw [Chi, Theta_zero_of_le (hw n) h,
    Theta_zero_of_le (hw (n + 1)) (le_trans h (le_of_lt (aSeq_lt_succ n))), sub_self]

/-- The truncation index is beyond `rad2 x`. -/
theorem rad2_lt_aSeq_Nidx_succ {R₀ : ℝ} (x : ℝ × ℝ) :
    rad2 x < aSeq R₀ (Nidx R₀ x + 1) := by
  have h1 : (rad2 x - R₀) * 2 < (Nat.floor ((rad2 x - R₀) * 2) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  rw [Nidx]
  simp only [aSeq]
  push_cast
  linarith

theorem aSeq_le_Nidx {R₀ : ℝ} (x : ℝ × ℝ) : rad2 x ≤ aSeq R₀ (Nidx R₀ x + 1) :=
  le_of_lt (rad2_lt_aSeq_Nidx_succ x)

/-- A full step of slack: `rad2 x + 1` is still below the truncation shell. -/
theorem rad2_add_one_le_aSeq_Nidx_succ {R₀ : ℝ} (x : ℝ × ℝ) :
    rad2 x + 1 ≤ aSeq R₀ (Nidx R₀ x + 1) := by
  have h1 : (rad2 x - R₀) * 2 < (Nat.floor ((rad2 x - R₀) * 2) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  rw [Nidx]
  simp only [aSeq]
  push_cast
  linarith

/-- Two distinct active indices are consecutive. -/
theorem Chi_active_consec {R₀ : ℝ} {w : ℕ → ℝ} (hw : ∀ n, 0 < w n)
    (hgap : ∀ n, aSeq R₀ n + w n ≤ aSeq R₀ (n + 1)) (hwle : ∀ n, w n ≤ 1 / 2)
    {n m : ℕ} {r : ℝ} (hn : Chi R₀ w n r ≠ 0) (hm : Chi R₀ w m r ≠ 0) (hnm : n < m) :
    m = n + 1 := by
  obtain ⟨h1n, h2n⟩ := Chi_support hw hgap hn
  obtain ⟨h1m, h2m⟩ := Chi_support hw hgap hm
  by_contra hc
  have hm2 : n + 2 ≤ m := by omega
  have h3 : aSeq R₀ (n + 1) + 1 / 2 ≤ aSeq R₀ m := by
    have hm' : aSeq R₀ (n + 2) ≤ aSeq R₀ m := aSeq_mono R₀ hm2
    have hs : aSeq R₀ (n + 2) = aSeq R₀ (n + 1) + 1 / 2 := aSeq_succ R₀ (n + 1)
    linarith [hm']
  linarith [h2n, h1m, h3, hwle (n + 1)]

/-! ## 7. Smoothness of the radial sum -/

theorem contDiff_chi_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R₀ : ℝ} (hR₀ : 0 < R₀) {w : ℕ → ℝ} (hw : ∀ n, 0 < w n)
    (u : ℕ → ℝ × ℝ → E)
    (hu : ∀ n, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u n) {x : ℝ × ℝ | x ≠ 0}) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × ℝ => ∑ n ∈ Finset.range (Nidx R₀ x + 1), Chi R₀ w n (rad2 x) • u n x) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro x₀
  by_cases hx₀ : x₀ = 0
  · subst hx₀
    refine (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ × ℝ) (show (0 : ℝ) < R₀ / 2 by positivity)] with y hy
    have hy' : rad2 y < R₀ := by
      have h2 : ‖y‖ < R₀ / 2 := by rwa [Metric.mem_ball, dist_zero_right] at hy
      have h3 := rad2_le_sqrt_two_mul_norm y
      have h4 : Real.sqrt 2 * ‖y‖ < Real.sqrt 2 * (R₀ / 2) :=
        mul_lt_mul_of_pos_left h2 (Real.sqrt_pos.mpr (by norm_num))
      have h5 : Real.sqrt 2 * (R₀ / 2) < 2 * (R₀ / 2) :=
        mul_lt_mul_of_pos_right sqrt_two_lt_two (by linarith)
      linarith
    have hzero : ∑ n ∈ Finset.range (Nidx R₀ y + 1), Chi R₀ w n (rad2 y) • u n y = 0 := by
      refine Finset.sum_eq_zero (fun n hn => ?_)
      rw [Chi_eq_zero_of_le hw (le_of_lt (lt_of_lt_of_le hy' (le_aSeq R₀ n))), zero_smul]
    rw [hzero]
  · set M := Nidx R₀ x₀ with hM
    have hMval : rad2 x₀ < aSeq R₀ (M + 1) := rad2_lt_aSeq_Nidx_succ x₀
    have hopen : IsOpen {y : ℝ × ℝ | rad2 y < rad2 x₀ + 1} :=
      isOpen_lt continuous_rad2 continuous_const
    have hmem : x₀ ∈ {y : ℝ × ℝ | rad2 y < rad2 x₀ + 1} := by
      simp only [mem_setOf_eq]
      linarith [rad2_nonneg x₀]
    have hfixed : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : ℝ × ℝ => ∑ n ∈ Finset.range (M + 1), Chi R₀ w n (rad2 y) • u n y) x₀ := by
      refine ContDiffAt.sum (fun n hn => ?_)
      have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : ℝ × ℝ => Chi R₀ w n (rad2 y)) x₀ :=
        (Chi_contDiff R₀ w n).contDiffAt.comp x₀ (rad2_contDiffAt hx₀)
      have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u n) x₀ := by
        exact (hu n).contDiffAt ((isOpen_compl_singleton).mem_nhds (by simpa using hx₀))
      exact h1.smul h2
    refine hfixed.congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hmem] with y hy
    have key : ∀ n, Nidx R₀ y + 1 ≤ n ∨ M + 1 ≤ n → Chi R₀ w n (rad2 y) • u n y = 0 := by
      intro n hn
      rcases hn with hn | hn
      · rw [Chi_eq_zero_of_le hw (le_of_lt (lt_of_lt_of_le (rad2_lt_aSeq_Nidx_succ y)
          (aSeq_mono R₀ hn))), zero_smul]
      · rw [Chi_eq_zero_of_le hw (le_of_lt (lt_of_lt_of_le hy (le_trans
          (rad2_add_one_le_aSeq_Nidx_succ x₀) (aSeq_mono R₀ hn)))), zero_smul]
    have h1 : (∑ n ∈ Finset.range (Nidx R₀ y + 1), Chi R₀ w n (rad2 y) • u n y)
        = ∑ n ∈ Finset.range (max (Nidx R₀ y + 1) (M + 1)), Chi R₀ w n (rad2 y) • u n y := by
      refine Finset.sum_subset (Finset.range_mono (le_max_left _ _)) ?_
      intro n hn hn'
      exact key n (Or.inl (Nat.le_of_not_lt (by simpa [Finset.mem_range] using hn')))
    have h2 : (∑ n ∈ Finset.range (M + 1), Chi R₀ w n (rad2 y) • u n y)
        = ∑ n ∈ Finset.range (max (Nidx R₀ y + 1) (M + 1)), Chi R₀ w n (rad2 y) • u n y := by
      refine Finset.sum_subset (Finset.range_mono (le_max_right _ _)) ?_
      intro n hn hn'
      exact key n (Or.inr (Nat.le_of_not_lt (by simpa [Finset.mem_range] using hn')))
    rw [h1, h2]

/-! ## 8. The two-term analysis of the radial sum -/

theorem Theta_zero_of_lt_one {R₀ : ℝ} {w : ℕ → ℝ} {n : ℕ} (hw : 0 < w n) {r : ℝ}
    (h : Theta R₀ w n r < 1) : r < aSeq R₀ n + w n := by
  by_contra hc
  push Not at hc
  have h1 := Theta_one_of_le hw hc
  linarith

theorem Theta_pos_of_ne_zero {R₀ : ℝ} {w : ℕ → ℝ} {n : ℕ} (hw : 0 < w n) {r : ℝ}
    (h : Theta R₀ w n r ≠ 0) : aSeq R₀ n < r := by
  by_contra hc
  push Not at hc
  exact h (Theta_zero_of_le hw hc)

/-- The packaged analysis of the radial sum: at any point beyond the first shell the sum of the
partition of unity reduces to two consecutive terms, with the two coefficients summing to `1`. -/
theorem chi_analysis {R₀ : ℝ} {w : ℕ → ℝ} (hw : ∀ n, 0 < w n)
    (hgap : ∀ n, aSeq R₀ n + w n ≤ aSeq R₀ (n + 1)) (hwle : ∀ n, w n ≤ 1 / 2)
    {x : ℝ × ℝ} (hx : aSeq R₀ 0 + w 0 ≤ rad2 x) :
    ∃ n₀ : ℕ, Chi R₀ w n₀ (rad2 x) ≠ 0 ∧
      Chi R₀ w n₀ (rad2 x) + Chi R₀ w (n₀ + 1) (rad2 x) = 1 ∧
      0 ≤ Chi R₀ w (n₀ + 1) (rad2 x) ∧
      (Chi R₀ w (n₀ + 1) (rad2 x) ≠ 0 → aSeq R₀ (n₀ + 1) < rad2 x) ∧
      (Chi R₀ w (n₀ + 1) (rad2 x) ≠ 0 → rad2 x < aSeq R₀ (n₀ + 1) + w (n₀ + 1)) ∧
      (∀ (M : Type) [AddCommMonoid M] [Module ℝ M] (f : ℕ → M),
        (∑ n ∈ Finset.range (Nidx R₀ x + 1), Chi R₀ w n (rad2 x) • f n)
          = Chi R₀ w n₀ (rad2 x) • f n₀ + Chi R₀ w (n₀ + 1) (rad2 x) • f (n₀ + 1)) := by
  classical
  set r := rad2 x with hr
  have hsum1 : ∑ n ∈ Finset.range (Nidx R₀ x + 1), Chi R₀ w n r = 1 := by
    rw [Chi_sum_range]
    have h0 : Theta R₀ w 0 r = 1 := Theta_one_of_le (hw 0) (by simpa [aSeq] using hx)
    have hN : Theta R₀ w (Nidx R₀ x + 1) r = 0 :=
      Theta_zero_of_le (hw _) (le_of_lt (rad2_lt_aSeq_Nidx_succ x))
    rw [h0, hN, sub_zero]
  have hex : ∃ n, n ∈ Finset.range (Nidx R₀ x + 1) ∧ Chi R₀ w n r ≠ 0 := by
    by_contra h
    push Not at h
    exact one_ne_zero (by rw [← hsum1]; exact Finset.sum_eq_zero fun n hn => h n hn)
  set n₀ := Nat.find hex with hn₀
  have hn₀spec : n₀ ∈ Finset.range (Nidx R₀ x + 1) ∧ Chi R₀ w n₀ r ≠ 0 := Nat.find_spec hex
  have hvan : ∀ n ∈ Finset.range (Nidx R₀ x + 1), n ≠ n₀ → n ≠ n₀ + 1 → Chi R₀ w n r = 0 := by
    intro n hn hn0 hn1
    rcases lt_trichotomy n n₀ with h | h | h
    · by_contra hc
      exact Nat.find_min hex h ⟨hn, hc⟩
    · exact absurd h hn0
    · by_contra hc
      exact hn1 (Chi_active_consec hw hgap hwle hn₀spec.2 hc h)
  have hred : ∀ (M : Type) [AddCommMonoid M] [Module ℝ M] (f : ℕ → M),
      (∑ n ∈ Finset.range (Nidx R₀ x + 1), Chi R₀ w n r • f n)
        = Chi R₀ w n₀ r • f n₀ + Chi R₀ w (n₀ + 1) r • f (n₀ + 1) := by
    intro M _ _ f
    have h1 : (∑ n ∈ Finset.range (Nidx R₀ x + 1), Chi R₀ w n r • f n)
        = ∑ n ∈ (Finset.range (Nidx R₀ x + 1) ∪ ({n₀, n₀ + 1} : Finset ℕ)),
            Chi R₀ w n r • f n := by
      refine Finset.sum_subset Finset.subset_union_left ?_
      intro n hn hn'
      rcases Finset.mem_union.mp hn with h | h
      · exact absurd h hn'
      · rcases Finset.mem_insert.mp h with h2 | h2
        · exact absurd (h2 ▸ hn₀spec.1) hn'
        · have h3 : n = n₀ + 1 := Finset.mem_singleton.mp h2
          have hle : Nidx R₀ x + 1 ≤ n₀ + 1 := by
            rw [h3] at hn'
            simpa [Finset.mem_range] using hn'
          rw [h3, Chi_eq_zero_of_le hw (le_of_lt (lt_of_lt_of_le (rad2_lt_aSeq_Nidx_succ x)
            (aSeq_mono R₀ hle))), zero_smul]
    have h2 : (∑ n ∈ ({n₀, n₀ + 1} : Finset ℕ), Chi R₀ w n r • f n)
        = ∑ n ∈ (Finset.range (Nidx R₀ x + 1) ∪ ({n₀, n₀ + 1} : Finset ℕ)),
            Chi R₀ w n r • f n := by
      refine Finset.sum_subset Finset.subset_union_right ?_
      intro n hn hn'
      have hnr : n ∈ Finset.range (Nidx R₀ x + 1) := by
        rcases Finset.mem_union.mp hn with h | h
        · exact h
        · exact absurd h hn'
      rw [hvan n hnr (fun h => hn' (by simp [h])) (fun h => hn' (by simp [h])), zero_smul]
    rw [h1, ← h2, Finset.sum_pair (by omega)]
  refine ⟨n₀, hn₀spec.2, ?_, ?_, ?_, ?_, hred⟩
  · have h : (∑ n ∈ Finset.range (Nidx R₀ x + 1), Chi R₀ w n r)
        = Chi R₀ w n₀ r + Chi R₀ w (n₀ + 1) r := by
      simpa using hred ℝ (fun _ => (1 : ℝ))
    rw [← h]
    exact hsum1
  · exact Chi_nonneg hw hgap (n₀ + 1) r
  · intro h
    exact (Chi_support hw hgap (n := n₀ + 1) h).1
  · intro h
    exact (Chi_support hw hgap hn₀spec.2).2

/-! ## 9. The radial sum is nonvanishing -/

theorem chi_sum_ne_zero {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R₀ : ℝ} {w : ℕ → ℝ} (hw : ∀ n, 0 < w n) (hwle : ∀ n, w n ≤ 1 / 2)
    (hgap : ∀ n, aSeq R₀ n + w n ≤ aSeq R₀ (n + 1))
    (u : ℕ → ℝ × ℝ → E) (hunit : ∀ n x, ‖u n x‖ = 1)
    (hclose : ∀ n x, aSeq R₀ (n + 1) ≤ rad2 x → rad2 x ≤ aSeq R₀ (n + 1) + w (n + 1) →
      1 / 2 ≤ inner ℝ (u n x) (u (n + 1) x))
    {x : ℝ × ℝ} (hx : aSeq R₀ 0 + w 0 ≤ rad2 x) :
    (∑ n ∈ Finset.range (Nidx R₀ x + 1), Chi R₀ w n (rad2 x) • u n x) ≠ 0 := by
  obtain ⟨n₀, hn₀ne, hst, htnn, ht1, ht2, hred⟩ := chi_analysis hw hgap hwle hx
  have hred' : (∑ n ∈ Finset.range (Nidx R₀ x + 1), Chi R₀ w n (rad2 x) • u n x)
      = Chi R₀ w n₀ (rad2 x) • u n₀ x + Chi R₀ w (n₀ + 1) (rad2 x) • u (n₀ + 1) x :=
    hred E (fun n => u n x)
  rw [hred']
  set s := Chi R₀ w n₀ (rad2 x) with hs
  set t := Chi R₀ w (n₀ + 1) (rad2 x) with ht
  have hsne : s ≠ 0 := hn₀ne
  have hspos : 0 < s := lt_of_le_of_ne (Chi_nonneg hw hgap n₀ _) (Ne.symm hsne)
  by_cases ht0 : t = 0
  · rw [ht0, zero_smul, add_zero]
    have hs1 : s = 1 := by rw [← hst, ht0, add_zero]
    rw [hs1, one_smul]
    intro h
    have hh := hunit n₀ x
    rw [h, norm_zero] at hh
    exact one_ne_zero hh.symm
  · have htpos : 0 < t := lt_of_le_of_ne htnn (Ne.symm ht0)
    have h1 : aSeq R₀ (n₀ + 1) < rad2 x := ht1 ht0
    have h2 : rad2 x ≤ aSeq R₀ (n₀ + 1) + w (n₀ + 1) := le_of_lt (ht2 ht0)
    have hcl := hclose n₀ x (le_of_lt h1) h2
    have hs_eq : s = 1 - t := by linarith [hst]
    have hbound := norm_convex_combination_sq (hunit n₀ x) (hunit (n₀ + 1) x) hcl
      (le_of_lt htpos) (by linarith [hst, hspos])
    intro hzero
    rw [hs_eq] at hzero
    have h0 : ‖(1 - t) • u n₀ x + t • u (n₀ + 1) x‖ ^ 2 = 0 := by rw [hzero]; simp
    linarith

/-! ## 10. The radial transition function -/

/-- The radial transition between the radii `a` and `b` (`a < b`): `0` below `a`, `1` above `b`. -/
def lamFun (a b : ℝ) (r : ℝ) : ℝ := Real.smoothTransition ((r - a) / (b - a))

theorem lamFun_contDiff (a b : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lamFun a b) := by
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun r : ℝ => Real.smoothTransition ((r - a) / (b - a)))
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem lamFun_zero {a b r : ℝ} (hab : a < b) (h : r ≤ a) : lamFun a b r = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

theorem lamFun_one {a b r : ℝ} (hab : a < b) (h : b ≤ r) : lamFun a b r = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem lamFun_nonneg (a b r : ℝ) : 0 ≤ lamFun a b r := Real.smoothTransition.nonneg _

theorem lamFun_le_one (a b r : ℝ) : lamFun a b r ≤ 1 := Real.smoothTransition.le_one _

theorem contDiff_lamFun_rad2 {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × ℝ => lamFun a b (rad2 x)) := by
  have hconst : ∀ t : ℝ, t ≤ a → lamFun a b t = lamFun a b 0 := by
    intro t ht
    rw [lamFun_zero hab ht, lamFun_zero hab (le_of_lt ha)]
  exact contDiff_comp_rad2 (lamFun_contDiff a b) ha hconst

theorem assemble_section {m : ℕ} {R₀ ε : ℝ} (hR₀ : 0 < R₀) (hε0 : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    {w : ℕ → ℝ} (hw : ∀ n, 0 < w n) (hwle : ∀ n, w n ≤ 1 / 2)
    (hgap : ∀ n, aSeq R₀ n + w n ≤ aSeq R₀ (n + 1)) (hw0 : w 0 < ε)
    (W : ℝ × ℝ → Submodule ℝ (EuclideanSpace ℝ (Fin m)))
    (u₁ : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (hu₁sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u₁ {x : ℝ × ℝ | rad2 x < R₀ + 2 * ε})
    (hu₁unit : ∀ x, rad2 x ≤ R₀ + ε → ‖u₁ x‖ = 1)
    (hu₁mem : ∀ x, rad2 x ≤ R₀ + ε → u₁ x ∈ W x)
    (u : ℕ → ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (husm : ∀ n, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u n) {x : ℝ × ℝ | x ≠ 0})
    (huunit : ∀ n x, ‖u n x‖ = 1)
    (humem : ∀ n x, aSeq R₀ n ≤ rad2 x → rad2 x ≤ aSeq R₀ n + 1 → u n x ∈ W x)
    (hclose : ∀ n x, aSeq R₀ (n + 1) ≤ rad2 x → rad2 x ≤ aSeq R₀ (n + 1) + w (n + 1) →
      1 / 2 ≤ inner ℝ (u n x) (u (n + 1) x))
    (hclose₀ : ∀ x, R₀ ≤ rad2 x → rad2 x ≤ R₀ + ε → 1 / 2 ≤ inner ℝ (u₁ x) (u 0 x)) :
    ∃ v : ℝ × ℝ → EuclideanSpace ℝ (Fin m),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v ∧ (∀ x, v x ≠ 0) ∧ (∀ x, v x ∈ W x) := by
  classical
  set S : ℝ × ℝ → EuclideanSpace ℝ (Fin m) :=
    fun x => ∑ n ∈ Finset.range (Nidx R₀ x + 1), Chi R₀ w n (rad2 x) • u n x with hS
  have hSsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S := contDiff_chi_sum hR₀ hw u husm
  set L : ℝ × ℝ → ℝ := fun x => lamFun (R₀ + w 0) (R₀ + ε) (rad2 x) with hL
  have hLsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L :=
    contDiff_lamFun_rad2 (by have := hw 0; linarith) (by linarith)
  -- `S` agrees with `u 0` in the transition region
  have hSmid : ∀ x, R₀ + w 0 ≤ rad2 x → rad2 x ≤ R₀ + ε → S x = u 0 x := by
    intro x hx1 hx2
    have hχ0 : Chi R₀ w 0 (rad2 x) = 1 := by
      rw [Chi, Theta_one_of_le (hw 0) (by simpa [aSeq] using hx1)]
      have h1 : Theta R₀ w 1 (rad2 x) = 0 := by
        refine Theta_zero_of_le (hw 1) ?_
        have h2 : aSeq R₀ 1 = R₀ + 1 / 2 := by rw [aSeq_succ]; simp [aSeq]
        linarith
      rw [h1, sub_zero]
    change (∑ n ∈ Finset.range (Nidx R₀ x + 1), Chi R₀ w n (rad2 x) • u n x) = u 0 x
    have hsingle : (∑ n ∈ Finset.range (Nidx R₀ x + 1), Chi R₀ w n (rad2 x) • u n x)
        = Chi R₀ w 0 (rad2 x) • u 0 x := by
      refine Finset.sum_eq_single 0 ?_ ?_
      · intro n hn hn0
        have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        have h1 : Chi R₀ w n (rad2 x) = 0 := by
          refine Chi_eq_zero_of_le hw ?_
          have h2 : aSeq R₀ 1 ≤ aSeq R₀ n := aSeq_mono R₀ hn1
          have h3 : aSeq R₀ 1 = R₀ + 1 / 2 := by rw [aSeq_succ]; simp [aSeq]
          linarith
        rw [h1, zero_smul]
      · intro h
        simp at h
    rw [hsingle, hχ0, one_smul]
  refine ⟨fun x => (1 - L x) • u₁ x + L x • S x, ?_, ?_, ?_⟩
  · -- smoothness
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : rad2 x < R₀ + 2 * ε
    · have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u₁ x :=
        hu₁sm.contDiffAt ((isOpen_lt continuous_rad2 continuous_const).mem_nhds hx)
      exact ((contDiffAt_const.sub hLsm.contDiffAt).smul h1).add
        (hLsm.contDiffAt.smul hSsm.contDiffAt)
    · push Not at hx
      refine (hSsm.contDiffAt).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_const continuous_rad2).mem_nhds
        (by linarith : R₀ + ε < rad2 x)] with y hy
      have h1 : L y = 1 := by
        rw [hL]
        exact lamFun_one (by linarith : R₀ + w 0 < R₀ + ε) (by linarith)
      rw [h1, sub_self, zero_smul, zero_add, one_smul]
  · -- nonvanishing
    intro x
    change (1 - L x) • u₁ x + L x • S x ≠ 0
    by_cases hx1 : rad2 x ≤ R₀ + w 0
    · have h1 : L x = 0 := by
        rw [hL]; exact lamFun_zero (by linarith : R₀ + w 0 < R₀ + ε) hx1
      simp only [h1, sub_zero, one_smul, zero_smul, add_zero]
      intro h
      have hh := hu₁unit x (by linarith)
      rw [h, norm_zero] at hh
      exact one_ne_zero hh.symm
    · push Not at hx1
      by_cases hx2 : rad2 x ≤ R₀ + ε
      · have hLnn : 0 ≤ L x := lamFun_nonneg _ _ _
        have hLle : L x ≤ 1 := lamFun_le_one _ _ _
        have hcl := hclose₀ x (by have := hw 0; linarith) hx2
        rw [hSmid x (le_of_lt hx1) hx2]
        have hpos := norm_convex_combination_sq (hu₁unit x hx2) (huunit 0 x) hcl hLnn hLle
        intro hzero
        have h0 : ‖(1 - L x) • u₁ x + L x • u 0 x‖ ^ 2 = 0 := by rw [hzero]; simp
        linarith
      · push Not at hx2
        have h1 : L x = 1 := by
          rw [hL]; exact lamFun_one (by linarith : R₀ + w 0 < R₀ + ε) (by linarith)
        simp only [h1, sub_self, zero_smul, zero_add, one_smul]
        exact chi_sum_ne_zero hw hwle hgap u huunit hclose (by rw [aSeq]; simp; linarith [hw0])
  · -- membership in the vertical subbundle
    intro x
    change (1 - L x) • u₁ x + L x • S x ∈ W x
    by_cases hx1 : rad2 x ≤ R₀ + w 0
    · have h1 : L x = 0 := by
        rw [hL]; exact lamFun_zero (by linarith : R₀ + w 0 < R₀ + ε) hx1
      simp only [h1, sub_zero, one_smul, zero_smul, add_zero]
      exact hu₁mem x (by linarith)
    · push Not at hx1
      by_cases hx2 : rad2 x ≤ R₀ + ε
      · rw [hSmid x (le_of_lt hx1) hx2]
        have h4 : aSeq R₀ 0 = R₀ := by simp [aSeq]
        have h0lo : aSeq R₀ 0 ≤ rad2 x := by
          rw [h4]
          exact le_of_lt (lt_of_le_of_lt (le_add_of_nonneg_right (le_of_lt (hw 0))) hx1)
        have h0hi : rad2 x ≤ aSeq R₀ 0 + 1 := by
          rw [h4]
          have h5 : ε ≤ 1 := le_trans hεhalf (by norm_num)
          linarith
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hu₁mem x (by linarith)))
          (Submodule.smul_mem _ _ (humem 0 x h0lo h0hi))
      · push Not at hx2
        have h1 : L x = 1 := by
          rw [hL]; exact lamFun_one (by linarith : R₀ + w 0 < R₀ + ε) (by linarith)
        simp only [h1, sub_self, zero_smul, zero_add, one_smul]
        obtain ⟨n₀, hn₀ne, hst, htnn, ht1, ht2, hred⟩ :=
          chi_analysis hw hgap hwle (by rw [aSeq]; simp; linarith [hw0])
        have hSsplit := hred (EuclideanSpace ℝ (Fin m)) (fun n => u n x)
        change (∑ n ∈ Finset.range (Nidx R₀ x + 1), Chi R₀ w n (rad2 x) • u n x) ∈ W x
        rw [hSsplit]
        have hbound1 : aSeq R₀ n₀ ≤ rad2 x := le_of_lt (Chi_support hw hgap hn₀ne).1
        have hbound2 : rad2 x ≤ aSeq R₀ n₀ + 1 := by
          have h2 := (Chi_support hw hgap hn₀ne).2
          have h3 : aSeq R₀ (n₀ + 1) = aSeq R₀ n₀ + 1 / 2 := aSeq_succ R₀ n₀
          linarith [hw (n₀ + 1), hwle (n₀ + 1)]
        by_cases ht0 : Chi R₀ w (n₀ + 1) (rad2 x) = 0
        · rw [ht0, zero_smul, add_zero]
          have hs1 : Chi R₀ w n₀ (rad2 x) = 1 := by rw [← hst, ht0, add_zero]
          rw [hs1, one_smul]
          exact humem n₀ x hbound1 hbound2
        · have hb1 : aSeq R₀ (n₀ + 1) ≤ rad2 x := le_of_lt (ht1 ht0)
          have hb2 : rad2 x ≤ aSeq R₀ (n₀ + 1) + w (n₀ + 1) := le_of_lt (ht2 ht0)
          refine Submodule.add_mem _ (Submodule.smul_mem _ _ (humem n₀ x hbound1 hbound2)) ?_
          refine Submodule.smul_mem _ _ (humem (n₀ + 1) x hb1 ?_)
          linarith [hwle (n₀ + 1), aSeq_succ R₀ n₀]



/-! ## 12. The uniform closeness radius -/

/-- **A uniform closeness radius.**  If a continuous function is `≥ 1/2` on the sphere of radius
`a > 0`, it is `≥ 1/4` on the annulus `[a, a + δ]` for some `δ > 0`. -/
theorem exists_closeness_radius {F : ℝ × ℝ → ℝ} (hF : Continuous F) {a : ℝ} (ha : 0 < a)
    (hsphere : ∀ x : ℝ × ℝ, rad2 x = a → 1 / 2 ≤ F x) :
    ∃ δ > 0, ∀ x : ℝ × ℝ, a ≤ rad2 x → rad2 x ≤ a + δ → 1 / 4 ≤ F x := by
  have hsub : {x : ℝ × ℝ | a ≤ rad2 x ∧ rad2 x ≤ a + 1} ⊆ closedBall (0 : ℝ × ℝ) (a + 1) := by
    intro x hx
    rw [mem_closedBall, dist_zero_right]
    exact le_trans (le_rad2 x) hx.2
  have hclosed : IsClosed {x : ℝ × ℝ | a ≤ rad2 x ∧ rad2 x ≤ a + 1} :=
    IsClosed.inter (isClosed_le continuous_const continuous_rad2)
      (isClosed_le continuous_rad2 continuous_const)
  have hA : IsCompact {x : ℝ × ℝ | a ≤ rad2 x ∧ rad2 x ≤ a + 1} :=
    IsCompact.of_isClosed_subset (isCompact_closedBall 0 (a + 1)) hclosed hsub
  obtain ⟨δ', hδ'pos, hδ'⟩ := Metric.uniformContinuousOn_iff.mp
    (hA.uniformContinuousOn_of_continuous hF.continuousOn) (1 / 4) (by norm_num)
  refine ⟨min (1 / 2) δ' / 2, by positivity, ?_⟩
  intro x hx1 hx2
  have hx2' : rad2 x ≤ a + 1 := by
    have h3 : min (1 / 2 : ℝ) δ' ≤ 1 / 2 := min_le_left _ _
    have h4 : min (1 / 2 : ℝ) δ' / 2 ≤ 1 := by linarith
    linarith
  have hxA : x ∈ {x : ℝ × ℝ | a ≤ rad2 x ∧ rad2 x ≤ a + 1} := ⟨hx1, hx2'⟩
  have hrx : 0 < rad2 x := lt_of_lt_of_le ha hx1
  set y : ℝ × ℝ := (a / rad2 x) • x with hy
  have h1y : rad2 y = a := by
    rw [hy, rad2_smul, abs_of_pos (div_pos ha hrx)]
    field_simp
  have hyA : y ∈ {x : ℝ × ℝ | a ≤ rad2 x ∧ rad2 x ≤ a + 1} :=
    ⟨by rw [h1y], by rw [h1y]; linarith⟩
  have hdist : dist x y < δ' := by
    have h1 : dist x y ≤ rad2 (x - y) := by
      rw [dist_eq_norm]
      exact le_rad2 _
    have heq : x - y = (1 - a / rad2 x) • x := by
      rw [hy]; module
    have h2 : rad2 (x - y) = rad2 x - a := by
      rw [heq, rad2_smul, abs_of_nonneg (by
        rw [sub_nonneg, div_le_one hrx]
        exact hx1)]
      field_simp
    have h3 : rad2 x - a ≤ min (1 / 2) δ' / 2 := sub_le_iff_le_add'.mpr hx2
    have h4 : min (1 / 2 : ℝ) δ' ≤ δ' := min_le_right _ _
    linarith
  have hres := hδ' x hxA y hyA hdist
  have hFy : 1 / 2 ≤ F y := hsphere y (by
    rw [hy, rad2_smul, abs_of_pos (div_pos ha hrx)]
    field_simp)
  rw [Real.dist_eq] at hres
  have hres2 : -(1 / 4) < F x - F y := (abs_lt.mp hres).1
  linarith

/-! ## 13b. Auxiliary facts about the clamped direction and the closeness radius -/

theorem psiFun_eq_zero_iff {η : ℝ} (hη : 0 < η) (x : ℝ × ℝ) :
    psiFun η x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h' : clampFun η (rad2 x) • x = 0 := by
      simpa only [psiFun] using h
    rcases smul_eq_zero.mp h' with h1 | h1
    · exact absurd h1 (mul_ne_zero (inv_ne_zero (ne_of_gt hη)) (ne_of_gt (clampC_pos _)))
    · exact h1
  · rintro rfl
    simp [psiFun]

theorem rad2_psiFun_le_two {η : ℝ} (hη : 0 < η) (u : ℝ × ℝ) : rad2 (psiFun η u) ≤ 2 := by
  rw [psiFun, rad2_smul, abs_of_nonneg (clampFun_nonneg hη _), mul_comm]
  exact clampFun_mul_le_two hη (rad2_nonneg u)

theorem rad2_smul_psiFun_le {η : ℝ} (hη : 0 < η) {c : ℝ} (hc : 0 ≤ c) (u : ℝ × ℝ) :
    rad2 (c • psiFun η u) ≤ 2 * c := by
  calc rad2 (c • psiFun η u) = c * rad2 (psiFun η u) := by rw [rad2_smul, abs_of_nonneg hc]
    _ ≤ c * 2 := mul_le_mul_of_nonneg_left (rad2_psiFun_le_two hη u) hc
    _ = 2 * c := by ring

theorem rad2_psiFun_eq_one {η : ℝ} (hη : 0 < η) {u : ℝ × ℝ} (hu : 2 * η ≤ rad2 u) :
    rad2 (psiFun η u) = 1 := by
  have hu0 : 0 < rad2 u := lt_of_lt_of_le (by linarith) hu
  rw [psiFun_eq_dir hη hu, rad2_smul, abs_of_pos (inv_pos.mpr hu0),
    inv_mul_cancel₀ (ne_of_gt hu0)]

/-- **A uniform closeness radius, in the form used for the shell gluing.**  If `F` is continuous on
the annulus `[a, a + L]` and takes the value `1` on the inner sphere, then `F ≥ 1/2` on
`[a, a + δ]` for some `0 < δ ≤ L`. -/
theorem exists_closeness_radius_eq_one {F : ℝ × ℝ → ℝ} {a L : ℝ} (ha : 0 < a) (hL : 0 < L)
    (hcont : ContinuousOn F {x : ℝ × ℝ | a ≤ rad2 x ∧ rad2 x ≤ a + L})
    (hsphere : ∀ x : ℝ × ℝ, rad2 x = a → F x = 1) :
    ∃ δ > 0, δ ≤ L ∧ ∀ x : ℝ × ℝ, a ≤ rad2 x → rad2 x ≤ a + δ → 1 / 2 ≤ F x := by
  have hsub : {x : ℝ × ℝ | a ≤ rad2 x ∧ rad2 x ≤ a + L} ⊆ closedBall (0 : ℝ × ℝ) (a + L) := by
    intro x hx
    rw [mem_closedBall, dist_zero_right]
    exact le_trans (le_rad2 x) hx.2
  have hclosed : IsClosed {x : ℝ × ℝ | a ≤ rad2 x ∧ rad2 x ≤ a + L} :=
    IsClosed.inter (isClosed_le continuous_const continuous_rad2)
      (isClosed_le continuous_rad2 continuous_const)
  have hA : IsCompact {x : ℝ × ℝ | a ≤ rad2 x ∧ rad2 x ≤ a + L} :=
    IsCompact.of_isClosed_subset (isCompact_closedBall 0 (a + L)) hclosed hsub
  obtain ⟨δ', hδ'pos, hδ'⟩ := Metric.uniformContinuousOn_iff.mp
    (hA.uniformContinuousOn_of_continuous hcont) (1 / 2) (by norm_num)
  refine ⟨min L δ' / 2, by positivity, ?_, ?_⟩
  · have h1 : min L δ' ≤ L := min_le_left _ _
    linarith
  · intro x hx1 hx2
    have hx2' : rad2 x ≤ a + L := by
      have h3 : min L δ' ≤ L := min_le_left _ _
      have h4 : min L δ' / 2 ≤ L := by linarith
      linarith
    have hxA : x ∈ {x : ℝ × ℝ | a ≤ rad2 x ∧ rad2 x ≤ a + L} := ⟨hx1, hx2'⟩
    have hrx : 0 < rad2 x := lt_of_lt_of_le ha hx1
    set y : ℝ × ℝ := (a / rad2 x) • x with hy
    have h1y : rad2 y = a := by
      rw [hy, rad2_smul, abs_of_pos (div_pos ha hrx)]
      field_simp
    have hyA : y ∈ {x : ℝ × ℝ | a ≤ rad2 x ∧ rad2 x ≤ a + L} :=
      ⟨by rw [h1y], by rw [h1y]; linarith⟩
    have hdist : dist x y < δ' := by
      have h1 : dist x y ≤ rad2 (x - y) := by
        rw [dist_eq_norm]
        exact le_rad2 _
      have heq : x - y = (1 - a / rad2 x) • x := by
        rw [hy]; module
      have h2 : rad2 (x - y) = rad2 x - a := by
        rw [heq, rad2_smul, abs_of_nonneg (by
          rw [sub_nonneg, div_le_one hrx]
          exact hx1)]
        field_simp
      have h3 : rad2 x - a ≤ min L δ' / 2 := sub_le_iff_le_add'.mpr hx2
      have h4 : min L δ' ≤ δ' := min_le_right _ _
      linarith
    have hres := hδ' x hxA y hyA hdist
    have hFy : F y = 1 := hsphere y h1y
    rw [Real.dist_eq, hFy] at hres
    have hres2 : -(1 / 2) < F x - 1 := (abs_lt.mp hres).1
    linarith

/-! ## 13. The shell sections -/

/-- The `n`-th shell section, transported from the inner sphere by the normalised transport `trN`. -/
noncomputable def sectOf {m : ℕ} (η R₀ : ℝ) (u₁ : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (trN : ℕ → ℝ → (ℝ × ℝ) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    ℕ → ℝ × ℝ → EuclideanSpace ℝ (Fin m)
  | 0 => fun x => nz (trN 0 (rad2 x - aSeq R₀ 0) x (nz (u₁ (aSeq R₀ 0 • psiFun η x))))
  | (n + 1) => fun x => nz (trN (n + 1) (rad2 x - aSeq R₀ (n + 1)) x
      (nz (sectOf η R₀ u₁ trN n (aSeq R₀ (n + 1) • psiFun η x))))

/-! ## 14. The global section of a smooth projection family -/

theorem exists_global_section {m k : ℕ} (hkm : k < m)
    (P : ℝ × ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hPsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (ℝ × ℝ) × EuclideanSpace ℝ (Fin m) => P p.1 p.2))
    (hPidem : ∀ x, P x * P x = P x)
    (hPrank : ∀ x, Module.finrank ℝ (LinearMap.range (P x).toLinearMap) = m - k) :
    ∃ v : ℝ × ℝ → EuclideanSpace ℝ (Fin m),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v ∧ (∀ x, v x ≠ 0) ∧
      (∀ x, v x ∈ LinearMap.range (P x).toLinearMap) := by
  classical
  have hEP : Type := ℝ × ℝ
  -- (1) a nonzero reference vector in the value at the origin
  have hr : 0 < m - k := by omega
  have hne : (LinearMap.range (P 0).toLinearMap) ≠ ⊥ := by
    intro h
    have := hPrank 0
    rw [h, finrank_bot] at this
    omega
  obtain ⟨v₀, hv₀mem, hv₀ne⟩ := (Submodule.ne_bot_iff _).mp hne
  have hP0v₀ : P 0 v₀ = v₀ := by
    obtain ⟨w, hw⟩ := hv₀mem
    rw [← hw]
    have h := congrArg (fun f : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) => f w)
      (hPidem 0)
    simpa using h
  -- (2) continuity gives a radius on which `P · v₀` does not vanish
  have hfam : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × ℝ => P x) := by
    rw [contDiff_clm_apply_iff]
    intro y
    exact hPsm.comp (contDiff_id.prodMk contDiff_const)
  have hcont : Continuous fun x : ℝ × ℝ => P x v₀ := hfam.continuous.clm_apply continuous_const
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.continuousAt_iff.mp hcont.continuousAt (‖v₀‖ / 2) (by positivity)
  set ρ : ℝ := δ / 2 with hρdef
  have hρpos : 0 < ρ := by positivity
  have hgood : ∀ x : ℝ × ℝ, rad2 x ≤ ρ → P x v₀ ≠ 0 := by
    intro x hx hzero
    have h1 : dist x 0 < δ := by
      rw [dist_zero_right]
      exact lt_of_le_of_lt (le_trans (le_rad2 x) hx) (by linarith)
    have h2 := hδ h1
    rw [dist_eq_norm] at h2
    have h3 : P 0 v₀ = v₀ := hP0v₀
    rw [h3] at h2
    rw [hzero, zero_sub, norm_neg] at h2
    have h4 : 0 < ‖v₀‖ := norm_pos_iff.mpr hv₀ne
    linarith
  -- (3) the constants
  set R₀ : ℝ := ρ / 8 with hR₀def
  have hR₀pos : 0 < R₀ := by positivity
  set η : ℝ := R₀ / 4 with hηdef
  have hηpos : 0 < η := by positivity
  have hR₀ρ : 2 * R₀ ≤ ρ := by rw [hR₀def]; linarith
  -- (4) the disc section
  set u₁ : ℝ × ℝ → EuclideanSpace ℝ (Fin m) := fun x => nz (P x v₀) with hu₁def
  have hu₁sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u₁ {x : ℝ × ℝ | rad2 x < ρ} := by
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × ℝ => P x v₀)
        {x : ℝ × ℝ | rad2 x < ρ} :=
      (hfam.clm_apply contDiff_const).contDiffOn
    exact contDiffOn_nz.comp h1 (fun x hx => hgood x (le_of_lt hx))
  have hu₁unit : ∀ x : ℝ × ℝ, rad2 x ≤ ρ → ‖u₁ x‖ = 1 := by
    intro x hx
    rw [hu₁def]
    exact norm_nz _ (hgood x hx)
  have hu₁mem : ∀ x : ℝ × ℝ, rad2 x ≤ ρ → u₁ x ∈ LinearMap.range (P x).toLinearMap := by
    intro x hx
    rw [hu₁def]
    refine Submodule.smul_mem _ _ (LinearMap.mem_range.mpr ⟨P x v₀, ?_⟩)
    have h := congrArg
      (fun f : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) => f v₀) (hPidem x)
    simpa [ContinuousLinearMap.mul_apply] using h
  -- (5) the shell families and their transports
  let prF : ℕ → ℝ → (ℝ × ℝ) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    fun n s u => P ((aSeq R₀ n + s) • psiFun η u)
  have hshell : ∀ n : ℕ, ∃ (Λ Λinv : ℝ → (ℝ × ℝ) →
        EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : (ℝ × (ℝ × ℝ)) × EuclideanSpace ℝ (Fin m) =>
        Λ p.1.1 p.1.2 p.2) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : (ℝ × (ℝ × ℝ)) × EuclideanSpace ℝ (Fin m) =>
        Λinv p.1.1 p.1.2 p.2) ∧
      (∀ t z y, Λinv t z (Λ t z y) = y) ∧ (∀ t z y, Λ t z (Λinv t z y) = y) ∧
      (∀ z : ℝ × ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        LinearMap.range ((Λ t z).toLinearMap.comp ((prF n t z).toLinearMap))
          = LinearMap.range ((prF n 0 z).toLinearMap)) := by
    intro n
    refine marchingTransport_gen (Z := ℝ × ℝ) (E := EuclideanSpace ℝ (Fin m))
      (k := m - k) (pr := prF n) ?_ ?_ ?_ ?_
    · have hmap : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : (ℝ × (ℝ × ℝ)) × EuclideanSpace ℝ (Fin m) =>
            (((aSeq R₀ n + (p.1.1 : ℝ)) • psiFun η (p.1.2 : ℝ × ℝ)), p.2)) := by
        refine ContDiff.prodMk ?_ contDiff_snd
        have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun p : (ℝ × (ℝ × ℝ)) × EuclideanSpace ℝ (Fin m) =>
              psiFun η (p.1.2 : ℝ × ℝ)) :=
          (psiFun_contDiff hηpos).comp (contDiff_fst.snd)
        have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun p : (ℝ × (ℝ × ℝ)) × EuclideanSpace ℝ (Fin m) => aSeq R₀ n + (p.1.1 : ℝ)) :=
          contDiff_const.add (contDiff_fst.fst)
        exact h2.smul h1
      have hres := hPsm.comp hmap
      convert hres using 1
      funext p
      rfl
    · intro s u; exact hPidem _
    · intro s u; exact hPrank _
    · exact uniformCloseness_clampedShell (E := EuclideanSpace ℝ (Fin m)) P hPsm (aSeq R₀ n)
        (psiFun η) (psiFun_contDiff hηpos) (fun u => psiFun_bound hηpos u)
  choose Λ Λinv hΛsm hΛinvsm hinv1 hinv2 hrange using hshell
  let trN : ℕ → ℝ → (ℝ × ℝ) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    fun n s u => (Λinv n s u).comp (Λ n 0 u)
  have htrN0 : ∀ n u, trN n 0 u = 1 := by
    intro n u
    refine ContinuousLinearMap.ext (fun y => ?_)
    simp only [trN, ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]
    exact hinv1 n 0 u y
  have hprF_pt : ∀ n x, 2 * η ≤ rad2 x → prF n (rad2 x - aSeq R₀ n) x = P x := by
    intro n x hx
    simp only [prF]
    have h1 : aSeq R₀ n + (rad2 x - aSeq R₀ n) = rad2 x := by ring
    rw [h1, smul_psiFun_self hηpos hx]
  have htrN_mem : ∀ n s u, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y : EuclideanSpace ℝ (Fin m),
      y ∈ LinearMap.range ((prF n 0 u).toLinearMap) →
      trN n s u y ∈ LinearMap.range ((prF n s u).toLinearMap) := by
    intro n s u hs y hy
    obtain ⟨w, hw⟩ := hy
    have h2 := hrange n u 0 (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    have h3 : Λ n 0 u y ∈ LinearMap.range ((prF n 0 u).toLinearMap) := by
      rw [← h2]
      refine ⟨w, ?_⟩
      show ((Λ n 0 u).toLinearMap.comp ((prF n 0 u).toLinearMap)) w
        = ((Λ n 0 u).toLinearMap) y
      rw [LinearMap.comp_apply, hw]
    obtain ⟨v, hv⟩ := h3
    have h4 := hrange n u s hs
    have h5 : Λ n 0 u y ∈ LinearMap.range
        ((Λ n s u).toLinearMap.comp ((prF n s u).toLinearMap)) := by
      rw [h4]
      exact ⟨v, by simpa only [LinearMap.comp_apply] using hv⟩
    obtain ⟨x, hx⟩ := h5
    refine ⟨prF n s u x, ?_⟩
    have hidem' : (prF n s u) ((prF n s u) x) = prF n s u x := by
      have h := congrArg (fun f : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) => f x)
        (hPidem ((aSeq R₀ n + s) • psiFun η u))
      simpa only [prF, ContinuousLinearMap.mul_apply] using h
    change (prF n s u) ((prF n s u) x) = trN n s u y
    rw [hidem']
    change prF n s u x = (Λinv n s u) ((Λ n 0 u) y)
    rw [← hx]
    exact (hinv1 n s u (prF n s u x)).symm
  -- (6) the shell sections
  let sect : ℕ → ℝ × ℝ → EuclideanSpace ℝ (Fin m) := sectOf η R₀ u₁ trN
  have htrN_sm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (ℝ × (ℝ × ℝ)) × EuclideanSpace ℝ (Fin m) => trN n p.1.1 p.1.2 p.2) := by
    intro n
    have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : (ℝ × (ℝ × ℝ)) × EuclideanSpace ℝ (Fin m) => Λinv n p.1.1 p.1.2) := by
      rw [contDiff_clm_apply_iff]
      intro y
      exact (hΛinvsm n).comp (ContDiff.prodMk contDiff_fst contDiff_const)
    have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : (ℝ × (ℝ × ℝ)) × EuclideanSpace ℝ (Fin m) => Λ n 0 p.1.2) := by
      rw [contDiff_clm_apply_iff]
      intro y
      exact (hΛsm n).comp (ContDiff.prodMk
        (ContDiff.prodMk contDiff_const contDiff_fst.snd) contDiff_const)
    have hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : (ℝ × (ℝ × ℝ)) × EuclideanSpace ℝ (Fin m) => (Λ n 0 p.1.2) p.2) :=
      hB.clm_apply contDiff_snd
    have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : (ℝ × (ℝ × ℝ)) × EuclideanSpace ℝ (Fin m) =>
          (Λinv n p.1.1 p.1.2) ((Λ n 0 p.1.2) p.2)) := hA.clm_apply hC
    simpa only [trN, ContinuousLinearMap.comp_apply] using hD

  -- (7) smoothness of the joint transport, in linear-map form
  have htrN_sm' : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × ℝ) => trN n q.1 q.2) := by
    intro n
    rw [contDiff_clm_apply_iff]
    intro y
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (ℝ × ℝ) =>
          (((q.1, q.2), y) : (ℝ × (ℝ × ℝ)) × EuclideanSpace ℝ (Fin m))) :=
      (contDiff_fst.prodMk contDiff_snd).prodMk contDiff_const
    exact (htrN_sm n).comp h2
  have hrad2On : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × ℝ => rad2 x)
      {x : ℝ × ℝ | x ≠ 0} :=
    isOpen_ne.contDiffOn_iff.mpr (fun x hx => rad2_contDiffAt hx)
  have htrN_inj : ∀ n s u, Function.Injective (trN n s u) := by
    intro n s u y z hyz
    have h4 : (Λinv n s u) ((Λ n 0 u) y) = (Λinv n s u) ((Λ n 0 u) z) := by
      simpa only [trN, ContinuousLinearMap.comp_apply] using hyz
    have h5 : (Λ n 0 u) y = (Λ n 0 u) z := by
      have h6 : (Λ n s u) ((Λinv n s u) ((Λ n 0 u) y))
          = (Λ n s u) ((Λinv n s u) ((Λ n 0 u) z)) := congrArg (Λ n s u) h4
      simpa only [hinv2 n s u] using h6
    have h7 : (Λinv n 0 u) ((Λ n 0 u) y) = (Λinv n 0 u) ((Λ n 0 u) z) :=
      congrArg (Λinv n 0 u) h5
    simpa only [hinv1 n 0 u] using h7
  have htrN_nz : ∀ n s u (y : EuclideanSpace ℝ (Fin m)), y ≠ 0 → trN n s u y ≠ 0 := by
    intro n s u y hy h
    exact hy (htrN_inj n s u (by rw [h, map_zero]))
  have hR₀0 : aSeq R₀ 0 = R₀ := by simp [aSeq]
  have htwo : 2 * η ≤ R₀ := by rw [hηdef]; linarith
  have hR₀ρ' : 2 * R₀ < ρ := by linarith
  have hu₁ne : ∀ y : ℝ × ℝ, rad2 y ≤ ρ → u₁ y ≠ 0 := by
    intro y hy h
    have h1 := hu₁unit y hy
    rw [h, norm_zero] at h1
    exact one_ne_zero h1.symm
  have harglt : ∀ x : ℝ × ℝ, rad2 (aSeq R₀ 0 • psiFun η x) < ρ := by
    intro x
    rw [hR₀0]
    exact lt_of_le_of_lt (rad2_smul_psiFun_le hηpos hR₀pos.le x) hR₀ρ'
  -- (8) the shell section is never zero
  have hsect_ne : ∀ n : ℕ, ∀ x : ℝ × ℝ, sect n x ≠ 0 := by
    intro n
    induction n with
    | zero =>
      intro x
      show nz (trN 0 (rad2 x - aSeq R₀ 0) x (nz (u₁ (aSeq R₀ 0 • psiFun η x)))) ≠ 0
      rw [nz_ne_zero_iff]
      exact htrN_nz 0 (rad2 x - aSeq R₀ 0) x (nz (u₁ (aSeq R₀ 0 • psiFun η x)))
        (by rw [nz_ne_zero_iff]; exact hu₁ne _ (le_of_lt (harglt x)))
    | succ n ih =>
      intro x
      show nz (trN (n + 1) (rad2 x - aSeq R₀ (n + 1)) x
        (nz (sect n (aSeq R₀ (n + 1) • psiFun η x)))) ≠ 0
      rw [nz_ne_zero_iff]
      exact htrN_nz (n + 1) (rad2 x - aSeq R₀ (n + 1)) x
        (nz (sect n (aSeq R₀ (n + 1) • psiFun η x)))
        (by rw [nz_ne_zero_iff]; exact ih _)
  -- (9) the shell section has unit norm
  have hsect_unit : ∀ n x, ‖sect n x‖ = 1 := by
    intro n x
    cases n with
    | zero =>
      show ‖nz (trN 0 (rad2 x - aSeq R₀ 0) x (nz (u₁ (aSeq R₀ 0 • psiFun η x))))‖ = 1
      refine norm_nz _ ?_
      rw [← nz_ne_zero_iff]
      exact hsect_ne 0 x
    | succ n =>
      show ‖nz (trN (n + 1) (rad2 x - aSeq R₀ (n + 1)) x
        (nz (sect n (aSeq R₀ (n + 1) • psiFun η x))))‖ = 1
      refine norm_nz _ ?_
      rw [← nz_ne_zero_iff]
      exact hsect_ne (n + 1) x
  -- (10) smoothness of the shell section off the origin
  have hpsi_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ × ℝ => psiFun η u) :=
    psiFun_contDiff hηpos
  have hsect_sm : ∀ n, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sect n)
      {x : ℝ × ℝ | x ≠ 0} := by
    intro n
    induction n with
    | zero =>
      show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ × ℝ => nz (trN 0 (rad2 x - aSeq R₀ 0) x
          (nz (u₁ (aSeq R₀ 0 • psiFun η x))))) {x : ℝ × ℝ | x ≠ 0}
      have hA : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : ℝ × ℝ => aSeq R₀ 0 • psiFun η x) {x : ℝ × ℝ | x ≠ 0} :=
        (hpsi_sm.const_smul (aSeq R₀ 0)).contDiffOn
      have hA' : Set.MapsTo (fun x : ℝ × ℝ => aSeq R₀ 0 • psiFun η x) {x : ℝ × ℝ | x ≠ 0}
          {y : ℝ × ℝ | rad2 y < ρ} := fun x _ => harglt x
      have hB : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : ℝ × ℝ => u₁ (aSeq R₀ 0 • psiFun η x)) {x : ℝ × ℝ | x ≠ 0} :=
        hu₁sm.comp hA hA'
      have hC : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : ℝ × ℝ => nz (u₁ (aSeq R₀ 0 • psiFun η x))) {x : ℝ × ℝ | x ≠ 0} :=
        (contDiffOn_nz (E := EuclideanSpace ℝ (Fin m))).comp hB
          (fun x _ => hu₁ne _ (le_of_lt (harglt x)))
      have hD : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : ℝ × ℝ => trN 0 (rad2 x - aSeq R₀ 0) x) {x : ℝ × ℝ | x ≠ 0} :=
        (htrN_sm' 0).comp_contDiffOn
          ((hrad2On.sub contDiffOn_const).prodMk contDiffOn_id)
      have hE : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : ℝ × ℝ => trN 0 (rad2 x - aSeq R₀ 0) x
            (nz (u₁ (aSeq R₀ 0 • psiFun η x)))) {x : ℝ × ℝ | x ≠ 0} := hD.clm_apply hC
      exact (contDiffOn_nz (E := EuclideanSpace ℝ (Fin m))).comp hE
        (fun x _ => nz_ne_zero_iff.mp (hsect_ne 0 x))
    | succ n ih =>
      show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ × ℝ => nz (trN (n + 1) (rad2 x - aSeq R₀ (n + 1)) x
          (nz (sect n (aSeq R₀ (n + 1) • psiFun η x))))) {x : ℝ × ℝ | x ≠ 0}
      have hc0 : 0 < aSeq R₀ (n + 1) := lt_of_lt_of_le hR₀pos (le_aSeq R₀ (n + 1))
      have hA : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : ℝ × ℝ => aSeq R₀ (n + 1) • psiFun η x) {x : ℝ × ℝ | x ≠ 0} :=
        (hpsi_sm.const_smul (aSeq R₀ (n + 1))).contDiffOn
      have hA' : Set.MapsTo (fun x : ℝ × ℝ => aSeq R₀ (n + 1) • psiFun η x) {x : ℝ × ℝ | x ≠ 0}
          {y : ℝ × ℝ | y ≠ 0} := by
        intro x hx h
        rcases smul_eq_zero.mp h with h1 | h1
        · exact absurd h1 hc0.ne'
        · exact hx ((psiFun_eq_zero_iff hηpos x).mp h1)
      have hB : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : ℝ × ℝ => sect n (aSeq R₀ (n + 1) • psiFun η x)) {x : ℝ × ℝ | x ≠ 0} :=
        ih.comp hA hA'
      have hC : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : ℝ × ℝ => nz (sect n (aSeq R₀ (n + 1) • psiFun η x))) {x : ℝ × ℝ | x ≠ 0} :=
        (contDiffOn_nz (E := EuclideanSpace ℝ (Fin m))).comp hB (fun x _ => hsect_ne n _)
      have hD : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : ℝ × ℝ => trN (n + 1) (rad2 x - aSeq R₀ (n + 1)) x) {x : ℝ × ℝ | x ≠ 0} :=
        (htrN_sm' (n + 1)).comp_contDiffOn
          ((hrad2On.sub contDiffOn_const).prodMk contDiffOn_id)
      exact (contDiffOn_nz (E := EuclideanSpace ℝ (Fin m))).comp (hD.clm_apply hC)
        (fun x _ => nz_ne_zero_iff.mp (hsect_ne (n + 1) x))
  -- (11) the shell section lies in the transported bundle
  have hsect_mem : ∀ n x, aSeq R₀ n ≤ rad2 x → rad2 x ≤ aSeq R₀ n + 1 →
      sect n x ∈ LinearMap.range (P x).toLinearMap := by
    intro n
    induction n with
    | zero =>
      intro x h1 h2
      show nz (trN 0 (rad2 x - aSeq R₀ 0) x (nz (u₁ (aSeq R₀ 0 • psiFun η x))))
        ∈ LinearMap.range (P x).toLinearMap
      have hxη : 2 * η ≤ rad2 x := le_trans htwo (le_trans (le_aSeq R₀ 0) h1)
      have hmem1 : u₁ (aSeq R₀ 0 • psiFun η x) ∈ LinearMap.range (prF 0 0 x).toLinearMap := by
        have h4 := hu₁mem _ (le_of_lt (harglt x))
        simpa only [prF, add_zero] using h4
      have hmem2 : nz (u₁ (aSeq R₀ 0 • psiFun η x))
          ∈ LinearMap.range (prF 0 0 x).toLinearMap := Submodule.smul_mem _ _ hmem1
      have hs : (rad2 x - aSeq R₀ 0) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
      have hmem3 := htrN_mem 0 (rad2 x - aSeq R₀ 0) x hs _ hmem2
      have h5 : prF 0 (rad2 x - aSeq R₀ 0) x = P x := hprF_pt 0 x hxη
      rw [h5] at hmem3
      exact Submodule.smul_mem _ _ hmem3
    | succ n ih =>
      intro x h1 h2
      show nz (trN (n + 1) (rad2 x - aSeq R₀ (n + 1)) x
        (nz (sect n (aSeq R₀ (n + 1) • psiFun η x)))) ∈ LinearMap.range (P x).toLinearMap
      have hxη : 2 * η ≤ rad2 x := le_trans htwo (le_trans (le_aSeq R₀ (n + 1)) h1)
      have hc0 : 0 < aSeq R₀ (n + 1) := lt_of_lt_of_le hR₀pos (le_aSeq R₀ (n + 1))
      have hz : rad2 (aSeq R₀ (n + 1) • psiFun η x) = aSeq R₀ (n + 1) := by
        rw [rad2_smul, abs_of_nonneg (le_of_lt hc0), rad2_psiFun_eq_one hηpos hxη, mul_one]
      have hz1 : aSeq R₀ n ≤ rad2 (aSeq R₀ (n + 1) • psiFun η x) := by
        rw [hz]; exact le_of_lt (aSeq_lt_succ (R₀ := R₀) n)
      have hz2 : rad2 (aSeq R₀ (n + 1) • psiFun η x) ≤ aSeq R₀ n + 1 := by
        rw [hz, aSeq_succ]; linarith
      have hmem1 : sect n (aSeq R₀ (n + 1) • psiFun η x)
          ∈ LinearMap.range (prF (n + 1) 0 x).toLinearMap := by
        have h4 := ih _ hz1 hz2
        simpa only [prF, add_zero] using h4
      have hmem2 : nz (sect n (aSeq R₀ (n + 1) • psiFun η x))
          ∈ LinearMap.range (prF (n + 1) 0 x).toLinearMap := Submodule.smul_mem _ _ hmem1
      have hs : (rad2 x - aSeq R₀ (n + 1)) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
      have hmem3 := htrN_mem (n + 1) (rad2 x - aSeq R₀ (n + 1)) x hs _ hmem2
      have h5 : prF (n + 1) (rad2 x - aSeq R₀ (n + 1)) x = P x := hprF_pt (n + 1) x hxη
      rw [h5] at hmem3
      exact Submodule.smul_mem _ _ hmem3
  -- (12) the shell sections agree on the common spheres
  have hsect_agree : ∀ n x, rad2 x = aSeq R₀ (n + 1) → sect (n + 1) x = sect n x := by
    intro n x hx
    have hxη : 2 * η ≤ rad2 x := by rw [hx]; exact le_trans htwo (le_aSeq R₀ (n + 1))
    show nz (trN (n + 1) (rad2 x - aSeq R₀ (n + 1)) x
      (nz (sect n (aSeq R₀ (n + 1) • psiFun η x)))) = sect n x
    have h0 : rad2 x - aSeq R₀ (n + 1) = 0 := by rw [hx]; ring
    have hz : aSeq R₀ (n + 1) • psiFun η x = x := by
      rw [← hx]; exact smul_psiFun_self hηpos hxη
    rw [h0, hz, htrN0]
    simp only [ContinuousLinearMap.one_apply]
    simp only [nz_eq_self (hsect_unit n x)]
  have hsect_agree_zero : ∀ x, rad2 x = R₀ → sect 0 x = u₁ x := by
    intro x hx
    have hxη : 2 * η ≤ rad2 x := by rw [hx]; exact htwo
    show nz (trN 0 (rad2 x - aSeq R₀ 0) x (nz (u₁ (aSeq R₀ 0 • psiFun η x)))) = u₁ x
    have h0 : rad2 x - aSeq R₀ 0 = 0 := by rw [hR₀0, hx]; ring
    have hz : aSeq R₀ 0 • psiFun η x = x := by
      rw [hR₀0, ← hx]; exact smul_psiFun_self hηpos hxη
    have hu : ‖u₁ x‖ = 1 := hu₁unit x (by rw [hx]; linarith)
    rw [h0, hz, htrN0]
    simp only [ContinuousLinearMap.one_apply]
    simp only [nz_eq_self hu]
  -- (13) the closeness radii of the successive shells
  have hcont0 : ContinuousOn (fun x : ℝ × ℝ => inner ℝ (u₁ x) (sect 0 x))
      {x : ℝ × ℝ | R₀ ≤ rad2 x ∧ rad2 x ≤ R₀ + ρ / 2} := by
    have hmono1 : {x : ℝ × ℝ | R₀ ≤ rad2 x ∧ rad2 x ≤ R₀ + ρ / 2} ⊆ {x : ℝ × ℝ | rad2 x < ρ} := by
      intro x hx
      have h : R₀ + ρ / 2 < ρ := by rw [hR₀def]; linarith
      have hx2 : rad2 x ≤ R₀ + ρ / 2 := hx.2
      show rad2 x < ρ
      linarith
    have h1 : ContinuousOn u₁ {x : ℝ × ℝ | R₀ ≤ rad2 x ∧ rad2 x ≤ R₀ + ρ / 2} :=
      hu₁sm.continuousOn.mono hmono1
    have hmono2 : {x : ℝ × ℝ | R₀ ≤ rad2 x ∧ rad2 x ≤ R₀ + ρ / 2} ⊆ {x : ℝ × ℝ | x ≠ 0} := by
      intro x hx h
      have hx1 : R₀ ≤ rad2 x := hx.1
      rw [h] at hx1
      have hz : rad2 (0 : ℝ × ℝ) = 0 := by simp [rad2]
      rw [hz] at hx1
      linarith
    have h2 : ContinuousOn (sect 0) {x : ℝ × ℝ | R₀ ≤ rad2 x ∧ rad2 x ≤ R₀ + ρ / 2} :=
      (hsect_sm 0).continuousOn.mono hmono2
    exact h1.inner h2
  obtain ⟨δ₀, hδ₀pos, hδ₀le, hδ₀⟩ := exists_closeness_radius_eq_one
    (F := fun x : ℝ × ℝ => inner ℝ (u₁ x) (sect 0 x)) hR₀pos
    (by positivity : (0 : ℝ) < ρ / 2) hcont0 (fun x hx => by
      rw [hsect_agree_zero x hx, real_inner_self_eq_norm_sq,
        hu₁unit x (by rw [hx]; linarith)]
      norm_num)
  have hcontn : ∀ n : ℕ, ContinuousOn (fun x : ℝ × ℝ => inner ℝ (sect n x) (sect (n + 1) x))
      {x : ℝ × ℝ | aSeq R₀ (n + 1) ≤ rad2 x ∧ rad2 x ≤ aSeq R₀ (n + 1) + 1} := by
    intro n
    have hc0 : 0 < aSeq R₀ (n + 1) := lt_of_lt_of_le hR₀pos (le_aSeq R₀ (n + 1))
    have hmono : {x : ℝ × ℝ | aSeq R₀ (n + 1) ≤ rad2 x ∧ rad2 x ≤ aSeq R₀ (n + 1) + 1}
        ⊆ {x : ℝ × ℝ | x ≠ 0} := by
      intro x hx h
      have hx1 : aSeq R₀ (n + 1) ≤ rad2 x := hx.1
      rw [h] at hx1
      have hz : rad2 (0 : ℝ × ℝ) = 0 := by simp [rad2]
      rw [hz] at hx1
      linarith
    exact ((hsect_sm n).continuousOn.mono hmono).inner ((hsect_sm (n + 1)).continuousOn.mono hmono)
  choose δn hδn using fun n : ℕ => exists_closeness_radius_eq_one
    (F := fun x : ℝ × ℝ => inner ℝ (sect n x) (sect (n + 1) x))
    (a := aSeq R₀ (n + 1)) (L := 1) (lt_of_lt_of_le hR₀pos (le_aSeq R₀ (n + 1))) (by norm_num)
    (hcontn n) (fun x hx => by
      rw [hsect_agree n x hx, real_inner_self_eq_norm_sq, hsect_unit n x]
      norm_num)
  -- (14) the widths
  set ε : ℝ := min (1 / 4) (min (R₀ / 8) (δ₀ / 2)) with hεdef
  have hεpos : 0 < ε := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hεle : ε ≤ 1 / 4 := min_le_left _ _
  have hεR₀ : ε ≤ R₀ / 8 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεδ₀ : ε < δ₀ := by
    have h1 : ε ≤ δ₀ / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  let c : ℕ → ℝ := Nat.rec (ε / 2) (fun k _ => δn k / 2)
  let w : ℕ → ℝ := fun n => min (1 / 8) (c n)
  have hc0 : c 0 = ε / 2 := rfl
  have hcs : ∀ n, c (n + 1) = δn n / 2 := fun n => rfl
  have hcpos : ∀ n, 0 < c n := by
    intro n
    induction n with
    | zero => rw [hc0]; linarith [hεpos]
    | succ n ih => rw [hcs n]; linarith [(hδn n).1]
  have hw : ∀ n, 0 < w n := fun n => lt_min (by norm_num) (hcpos n)
  have hwle : ∀ n, w n ≤ 1 / 8 := fun n => min_le_left _ _
  have hwle2 : ∀ n, w n ≤ 1 / 2 := fun n => le_trans (hwle n) (by norm_num)
  have hw0 : w 0 < ε := by
    have h1 : w 0 ≤ c 0 := min_le_right _ _
    rw [hc0] at h1
    linarith [hεpos]
  have hwsucc : ∀ n, w (n + 1) ≤ δn n := by
    intro n
    have h1 : w (n + 1) ≤ c (n + 1) := min_le_right _ _
    rw [hcs n] at h1
    linarith [(hδn n).1]
  have hgap : ∀ n, aSeq R₀ n + w n ≤ aSeq R₀ (n + 1) := by
    intro n
    rw [aSeq_succ]
    linarith [hwle n]
  -- (15) the radii fit inside the transition zone
  have hεR₀' : 2 * ε ≤ R₀ / 4 := by linarith [hεR₀, hR₀pos]
  have hlt1 : R₀ + 2 * ε < ρ := by
    have h2 : R₀ = ρ / 8 := hR₀def
    linarith [hρpos]
  have hlt2 : R₀ + ε < ρ := by
    have h2 : R₀ = ρ / 8 := hR₀def
    linarith [hρpos]
  -- (16) the assembled section
  obtain ⟨v, hvsm, hvne, hvmem⟩ := assemble_section (m := m) hR₀pos hεpos
    (le_trans hεle (by norm_num)) hw hwle2 hgap hw0
    (fun x => LinearMap.range (P x).toLinearMap) u₁
    (hu₁sm.mono (fun x hx => by
      have hx' : rad2 x < R₀ + 2 * ε := by simpa only [Set.mem_setOf_eq] using hx
      show rad2 x < ρ
      linarith))
    (fun x hx => hu₁unit x (by linarith [hx]))
    (fun x hx => hu₁mem x (by linarith [hx]))
    sect hsect_sm hsect_unit hsect_mem
    (fun n x h1 h2 => (hδn n).2.2 x h1 (by linarith [hwsucc n]))
    (fun x h1 h2 => hδ₀ x h1 (by linarith [hεδ₀]))
  exact ⟨v, hvsm, hvne, hvmem⟩

/-! ## 15. The one-step independent extension -/

/-- **One-step independent extension.**  Given a smooth family of pointwise linearly independent
`k`-frames in `ℝ^m` with `k < m`, there is a smooth field `w` such that `(b, w)` is pointwise
independent. -/
theorem exists_independent_extension_oneStep {m k : ℕ} (hkm : k < m)
    (b : ℝ → ℝ → (Fin k → EuclideanSpace ℝ (Fin m)))
    (hb : ∀ i : Fin k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => b p.1 p.2 i))
    (hind : ∀ p : ℝ × ℝ, LinearIndependent ℝ (b p.1 p.2)) :
    ∃ w : ℝ → ℝ → EuclideanSpace ℝ (Fin m),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => w p.1 p.2) ∧
      (∀ p : ℝ × ℝ, LinearIndependent ℝ (Fin.snoc (b p.1 p.2) (w p.1 p.2))) := by
  obtain ⟨P, hPsm, hPidem, hPadj, hPrank, hPrange⟩ :=
    smooth_kernelProjection_twoParam (fun p : ℝ × ℝ => b p.1 p.2) hb hind
  obtain ⟨v, hvsm, hvne, hvmem⟩ := exists_global_section hkm P hPsm hPidem hPrank
  refine ⟨fun s t => v (s, t), ?_, ?_⟩
  · exact hvsm
  · intro p
    refine LinearIndependent.finSnoc (hind p) ?_
    intro hmem
    have h1 : v p ∈ (Submodule.span ℝ (Set.range (b p.1 p.2)))ᗮ := by
      rw [← hPrange p]
      exact hvmem p
    rw [Submodule.mem_orthogonal] at h1
    have h2 : inner ℝ (v p) (v p) = 0 := h1 (v p) hmem
    have h3 : ‖v p‖ ^ 2 = 0 := by rw [← real_inner_self_eq_norm_sq]; exact h2
    have h4 : v p = 0 := by
      rw [pow_two, mul_self_eq_zero] at h3
      exact norm_eq_zero.mp h3
    exact hvne p h4
