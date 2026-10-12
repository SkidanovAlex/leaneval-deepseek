import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.FRKDefs
import Submission.Work.BoseBoxFock.chiLam_le_cubic_flat
import Submission.Work.BoseBoxFock.kinRow_lattice_tauPhi
import Submission.Work.BoseBoxFock.summable_one_add_norm_latVec_pow_inv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.WinAuxDefs` — vocabulary for the *image-sum* leaf of the W-route

The design `LEAD_DESIGN_formrowkin.md` §3 splits the W-route into

* W0 `chiLam_le_cubic_flat` (cubic flatness of the window `χ_Λ` at the sphere — PROVED),
* W1 `lattice_symbol_eq_alias` (the polarised Parseval identity, which exhibits the aliasing
  defect as the *image sum* `Σ_{m ≠ 0} Re ∫ conj(g x)·symOp σ g (x + ℓ•m)`),
* W2 `norm_symOp_le_of_dist` (the kernel decay estimate, a *hypothesis* here),
* W3 `windowAlias_le` (the image sum is paid by the reserve `‖D⁶σ‖₁ ℓ⁻³ gapBare`).

This file fixes the two auxiliary objects with which the position-space image sum is estimated:

* `winD ℓ x = max 0 (ℓ/2 − ‖x‖)`, the distance of `x` to the boundary of the ℓ-ball, which
  controls both the window `χ_Λ(x) ≤ C (winD ℓ x/ℓ)³` and the separation
  `‖x + ℓ•m − y‖ ≥ ℓ(‖m‖−1) + winD ℓ x + winD ℓ y`;
* `winW ℓ ψ = 1_{Λ} |Q_Λψ|`, the localised mean-free state as a *nonnegative* weight, whose
  `L¹`-norm is controlled by `gapBare ℓ 0 ψ = ∫_Λ (Q_Λψ)²` through Cauchy–Schwarz, and which
  bounds the bridge state `winState ℓ ψ = χ_Λ·Q_Λψ` pointwise.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The distance of `x` to the boundary of the window ball: `winD ℓ x = max 0 (ℓ/2 − ‖x‖)`. -/
noncomputable def winD (ℓ : ℝ) (x : E3) : ℝ := max 0 (ℓ / 2 - ‖x‖)

/-- The localised mean-free state of the box `Λ = acube ℓ`, as a nonnegative weight:
`winW ℓ ψ = 1_Λ·|Q_Λψ|` with `Q_Λψ = Qfree ℓ 0 ψ`. -/
noncomputable def winW (ℓ : ℝ) (ψ : E3 → ℝ) : E3 → ℝ :=
  (Submission.BoseGases.acube ℓ).indicator (fun z => |Work.BoseKinLoc.Qfree ℓ 0 ψ z|)

lemma winD_nonneg (ℓ : ℝ) (x : E3) : 0 ≤ winD ℓ x := le_max_left _ _

lemma winD_le_half {ℓ : ℝ} (hℓ : 0 < ℓ) (x : E3) : winD ℓ x ≤ ℓ / 2 := by
  rw [winD]
  exact max_le (by linarith) (sub_le_self _ (norm_nonneg x))

lemma winD_pos_iff {ℓ : ℝ} (hℓ : 0 < ℓ) (x : E3) : 0 < winD ℓ x ↔ ‖x‖ < ℓ / 2 := by
  rw [winD]
  constructor
  · intro h
    by_contra h'
    rw [max_eq_left (by linarith : ℓ / 2 - ‖x‖ ≤ 0)] at h
    exact lt_irrefl 0 h
  · intro h
    exact lt_max_of_lt_right (by linarith)

lemma mem_acube_of_winD_pos {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3} (h : 0 < winD ℓ x) :
    x ∈ Submission.BoseGases.acube ℓ :=
  Submission.BoseGases.mem_acube_of_norm_le hℓ.le (le_of_lt ((winD_pos_iff hℓ x).mp h))

lemma winW_nonneg (ℓ : ℝ) (ψ : E3 → ℝ) (z : E3) : 0 ≤ winW ℓ ψ z :=
  Set.indicator_nonneg (fun _ _ => abs_nonneg _) _

lemma winW_of_mem {ℓ : ℝ} {ψ : E3 → ℝ} {z : E3}
    (hz : z ∈ Submission.BoseGases.acube ℓ) :
    winW ℓ ψ z = |Work.BoseKinLoc.Qfree ℓ 0 ψ z| :=
  Set.indicator_of_mem hz _

lemma winW_of_notMem {ℓ : ℝ} {ψ : E3 → ℝ} {z : E3}
    (hz : z ∉ Submission.BoseGases.acube ℓ) : winW ℓ ψ z = 0 :=
  Set.indicator_of_notMem hz _

lemma winW_support_subset (ℓ : ℝ) (ψ : E3 → ℝ) :
    Function.support (winW ℓ ψ) ⊆ Submission.BoseGases.acube ℓ := by
  intro z hz
  by_contra hmem
  exact hz (winW_of_notMem hmem)

lemma winW_sq_eq (ℓ : ℝ) (ψ : E3 → ℝ) (z : E3) :
    winW ℓ ψ z ^ 2 = (Submission.BoseGases.acube ℓ).indicator
      (fun z => (Work.BoseKinLoc.Qfree ℓ 0 ψ z) ^ 2) z := by
  rw [winW]
  by_cases hz : z ∈ Submission.BoseGases.acube ℓ
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, sq_abs]
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
    ring

/-- `‖(r : ℂ)‖ = |r|`. -/
lemma winNorm_ofReal (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  have h1 : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
  calc ‖((r : ℝ) : ℂ)‖ = Real.sqrt (‖((r : ℝ) : ℂ)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (r ^ 2) := by rw [h1]
    _ = |r| := Real.sqrt_sq_eq_abs r

/-! ## The window factor `χ_Λ` -/

lemma chiLam_nonneg (ℓ : ℝ) (x : E3) : 0 ≤ Work.BoseK15.corpusBox.chiLam ℓ x := by
  have h : Work.BoseK15.corpusBox.chiLam ℓ x = Submission.BoseGases.chiScale ℓ x := rfl
  rw [h]
  exact Submission.BoseGases.chiScale_nonneg ℓ x

/-- **The window vanishes at and beyond the sphere**: `χ_Λ x = 0` for `ℓ/2 ≤ ‖x‖`.

This is the *strict* form of the support statement: `chiScale` is an `rOut = 1/2` bump, so its
support is the open ball.  It is what makes `x + ℓ•m` fall off `tsupport (winState ℓ ψ)` whenever
`winState ℓ ψ x ≠ 0` and `m ≠ 0`. -/
lemma chiLam_eq_zero_of_half_le {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3} (hx : ℓ / 2 ≤ ‖x‖) :
    Work.BoseK15.corpusBox.chiLam ℓ x = 0 := by
  obtain ⟨C, _hC0, hC⟩ := chiLam_le_cubic_flat hℓ
  have hmax : max 0 (ℓ / 2 - ‖x‖) = 0 := max_eq_left (by linarith)
  have h := hC x
  rw [hmax, zero_div, zero_pow (by norm_num : (3 : ℕ) ≠ 0), mul_zero] at h
  exact le_antisymm h (chiLam_nonneg ℓ x)

/-- `chiScale ℓ z = 0` at and beyond the sphere (same statement as `chiLam_eq_zero_of_half_le`,
`chiScale` and `chiLam` being definitionally equal). -/
lemma chiScale_eq_zero_of_half_le {ℓ : ℝ} (hℓ : 0 < ℓ) {z : E3} (h : ℓ / 2 ≤ ‖z‖) :
    Submission.BoseGases.chiScale ℓ z = 0 := by
  have h1 : Work.BoseK15.corpusBox.chiLam ℓ z = Submission.BoseGases.chiScale ℓ z := rfl
  rw [← h1]
  exact chiLam_eq_zero_of_half_le hℓ h

/-- `chiScale ℓ z ≠ 0` forces `‖z‖ < ℓ/2`, strictly. -/
lemma chiScale_norm_lt_half {ℓ : ℝ} (hℓ : 0 < ℓ) {z : E3}
    (hz : Submission.BoseGases.chiScale ℓ z ≠ 0) : ‖z‖ < ℓ / 2 := by
  by_contra h
  exact hz (chiScale_eq_zero_of_half_le hℓ (le_of_not_gt h))

/-! ## The bridge state as `χ_Λ·(Q_Λψ)` -/

/-- **`winState` is the window times the localised mean-free state** (definitionally). -/
lemma winState_apply (ℓ : ℝ) (ψ : E3 → ℝ) (z : E3) :
    winState ℓ ψ z
      = ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) *
        ((Work.BoseKinLoc.Qfree ℓ 0 ψ z : ℝ) : ℂ) := by
  rw [show winState ℓ ψ z = ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) *
      (((ψ z - (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.acube ℓ, ψ x) : ℝ) : ℂ) from rfl]
  congr 2
  simp [Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ, Work.BSKinetic.bsMean]

/-- The pointwise bound of the bridge state by the weight `winW`: outside the box both sides
vanish, inside it is the flat-decay bound of W0. -/
lemma winState_norm_le_of {ℓ C : ℝ} (hℓ : 0 < ℓ) (hC0 : 0 ≤ C)
    (hC : ∀ x : E3, Work.BoseK15.corpusBox.chiLam ℓ x ≤ C * (winD ℓ x / ℓ) ^ 3)
    (ψ : E3 → ℝ) (x : E3) :
    ‖winState ℓ ψ x‖ ≤ C * (winD ℓ x / ℓ) ^ 3 * winW ℓ ψ x := by
  have hpow : 0 ≤ (winD ℓ x / ℓ) ^ 3 := by
    have : 0 ≤ winD ℓ x / ℓ := div_nonneg (winD_nonneg ℓ x) hℓ.le
    positivity
  by_cases hχ : Work.BoseK15.corpusBox.chiLam ℓ x = 0
  · rw [winState_apply, hχ, Complex.ofReal_zero, zero_mul, norm_zero]
    exact mul_nonneg (mul_nonneg hC0 hpow) (winW_nonneg ℓ ψ x)
  · have hmemic : x ∈ Submission.BoseGases.acube ℓ := by
      have h3 : Work.BoseK15.corpusBox.chiLam ℓ x = Submission.BoseGases.chiScale ℓ x := rfl
      exact Submission.BoseGases.chiScale_mem_acube hℓ (by rwa [h3] at hχ)
    rw [winState_apply, norm_mul, winNorm_ofReal, winNorm_ofReal,
      abs_of_nonneg (chiLam_nonneg ℓ x), winW_of_mem hmemic]
    exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)

/-- **The bridge state vanishes off the open ball of radius `ℓ/2`.** -/
lemma winState_eq_zero_of_half_le_norm {ℓ : ℝ} (hℓ : 0 < ℓ) (ψ : E3 → ℝ) {x : E3}
    (hx : ℓ / 2 ≤ ‖x‖) : winState ℓ ψ x = 0 := by
  rw [winState_apply, chiLam_eq_zero_of_half_le hℓ hx, Complex.ofReal_zero, zero_mul]

/-- `winState ℓ ψ x ≠ 0` forces `‖x‖ < ℓ/2`, strictly.  (Used to place the shifted argument
`x + ℓ•m` outside `tsupport (winState ℓ ψ)`.) -/
lemma norm_lt_half_of_winState_ne_zero {ℓ : ℝ} (hℓ : 0 < ℓ) (ψ : E3 → ℝ) {x : E3}
    (hx : winState ℓ ψ x ≠ 0) : ‖x‖ < ℓ / 2 := by
  by_contra h
  exact hx (winState_eq_zero_of_half_le_norm hℓ ψ (le_of_not_gt h))

/-- A non-zero lattice vector has norm at least `1`. -/
lemma norm_latVec_ge_one {m : Fin 3 → ℤ} (hm : m ≠ 0) : 1 ≤ ‖latVec m‖ := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := Function.ne_iff.mp hm
  have h1 : (1 : ℝ) ≤ |((m i : ℤ) : ℝ)| := by
    have h2 : (1 : ℤ) ≤ |m i| := Int.one_le_abs hi
    exact_mod_cast h2
  have h2 : ‖(latVec m).ofLp i‖ = |((m i : ℤ) : ℝ)| := by
    rw [latVec_apply, Real.norm_eq_abs]
  calc (1 : ℝ) ≤ ‖(latVec m).ofLp i‖ := by rw [h2]; exact h1
    _ ≤ ‖latVec m‖ := PiLp.norm_apply_le (latVec m) i

end Work.BoseBoxFock
