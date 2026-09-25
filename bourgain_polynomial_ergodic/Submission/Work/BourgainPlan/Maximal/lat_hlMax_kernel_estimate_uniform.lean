/-
# The uniform lattice–kernel estimate for the Hardy–Littlewood maximal function

Let `ψ` be a Schwartz window on `ℝ` whose Fourier transform equals `1` on `[-1/4, 1/4]` and
vanishes off `[-1/2, 1/2]`, and let `H : ℝ → ℂ` be continuous, integrable, band-limited to
`|ξ| ≤ 1/4`.  Then `H` is reproduced from its integer samples,
`H y = ∑'_j ψ (y - j) · H j` (`lat_sampling_reproduce`), and the Hardy–Littlewood maximal
function of `‖H‖` is dominated by *discrete* data:

`mstHlMax (ofReal ‖H‖) t ≤ C · (latDiscMaxC (‖H ·‖ₑ) ⌊t⌋ + ∑'_j ‖H j‖ₑ · latKernel (t - j))`,

where `latDiscMaxC` is the centred discrete Hardy–Littlewood maximal function of the sampled
values and `latKernel u = ofReal ((1+|u|)^{-2})` is the summable far-field kernel.  The constant
`C` depends on `ψ` only through `‖ψ‖₁` and the Schwartz decay constant `psiDecay ψ`.

The proof splits the lattice sum according to the geometry of the averaging interval `[a₀,b₀] ∋ t`
of length `L = b₀ - a₀`:

* `L ≤ 1`: every term is at distance `≥ |t-j| - 1` from the interval, so the sampling kernel is
  dominated by `4 (1+|t-j|)^{-2}`; this is the far-field regime.
* `L > 1`: the terms with `|t-j| ≲ L` (at most `3L+1` of them, all inside
  `Finset.Icc (⌊t⌋-N) (⌊t⌋+N)` with `N = ⌈3L⌉₊`) are bounded by the *joint* average
  `N⁻¹ ∑_{|n-⌊t⌋|≤N} ‖H n‖ₑ`, which is at most the discrete maximal function `latDiscMaxC`; the
  remaining terms are at distance `> 2L` and fall under the summable kernel `latKernel`.

The use of the joint (maximal) average — rather than the sum of the per-`j` suprema of the sampling
kernel — is essential: the per-`j` supremum kernel behaves like `1/|j|` and convolution with it is
unbounded on `ℓʳ` (see `LATTICE_PRINCIPLE_STATUS.md`, §4).
-/
import Mathlib
import Submission.Work.BourgainPlan.Maximal.subtwoLatDefs
import Submission.Work.BourgainPlan.Maximal.lat_sampling_reproduce
import Submission.Work.BourgainPlan.Maximal.hlMaxBasicFacts
import Submission.Work.Maximal.mstWide_defs

namespace Work.BourgainPlan.Maximal

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

/-! ## The two constants attached to the window `ψ` -/

/-- Schwartz decay constant of `ψ`: `‖ψ u‖ ≤ psiDecay ψ * (1 + |u|)^{-2}` for every `u`. -/
def psiDecay (ψ : SchwartzMap ℝ ℂ) : ℝ :=
  4 * (SchwartzMap.seminorm ℂ 0 0 ψ) + 4 * (SchwartzMap.seminorm ℂ 2 0 ψ)

lemma psiDecay_nonneg (ψ : SchwartzMap ℝ ℂ) : 0 ≤ psiDecay ψ := by
  have h1 : (0:ℝ) ≤ (SchwartzMap.seminorm ℂ 0 0 ψ) := by positivity
  have h2 : (0:ℝ) ≤ (SchwartzMap.seminorm ℂ 2 0 ψ) := by positivity
  unfold psiDecay; linarith

/-- The Schwartz decay of the window: `‖ψ u‖ ≤ psiDecay ψ * (1 + |u|)^{-2}`. -/
lemma psi_norm_le (ψ : SchwartzMap ℝ ℂ) (u : ℝ) :
    ‖ψ u‖ ≤ psiDecay ψ * (1 + |u|) ^ (-2 : ℝ) := by
  have hS0 : (0:ℝ) ≤ (SchwartzMap.seminorm ℂ 0 0 ψ) := by positivity
  have hS2 : (0:ℝ) ≤ (SchwartzMap.seminorm ℂ 2 0 ψ) := by positivity
  have h0 : ‖ψ u‖ ≤ (SchwartzMap.seminorm ℂ 0 0 ψ) := SchwartzMap.norm_le_seminorm ℂ ψ u
  have h2 : |u| ^ 2 * ‖ψ u‖ ≤ (SchwartzMap.seminorm ℂ 2 0 ψ) := by
    have h := SchwartzMap.norm_pow_mul_le_seminorm ℂ ψ 2 u
    rw [Real.norm_eq_abs] at h
    simpa using h
  have hu : (0:ℝ) < 1 + |u| := by positivity
  rw [show (1 + |u|) ^ (-2 : ℝ) = ((1 + |u|) ^ 2)⁻¹ by
        rw [Real.rpow_neg (le_of_lt hu), Real.rpow_two]]
  rw [le_mul_inv_iff₀ (by positivity : (0:ℝ) < (1 + |u|) ^ 2)]
  rcases le_total |u| 1 with hu1 | hu1
  · calc ‖ψ u‖ * (1 + |u|) ^ 2 ≤ (SchwartzMap.seminorm ℂ 0 0 ψ) * 4 := by
          refine mul_le_mul h0 ?_ (by positivity) hS0
          nlinarith [abs_nonneg u]
      _ ≤ psiDecay ψ := by unfold psiDecay; linarith
  · have h4 : (1 + |u|) ^ 2 ≤ 4 * |u| ^ 2 := by nlinarith [abs_nonneg u, hu1]
    calc ‖ψ u‖ * (1 + |u|) ^ 2 ≤ ‖ψ u‖ * (4 * |u| ^ 2) :=
          mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
      _ = 4 * (|u| ^ 2 * ‖ψ u‖) := by ring
      _ ≤ 4 * (SchwartzMap.seminorm ℂ 2 0 ψ) :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ psiDecay ψ := by unfold psiDecay; linarith

/-- The `L¹` mass of the window `ψ`. -/
def psiMass (ψ : SchwartzMap ℝ ℂ) : ℝ := ∫ u, ‖ψ u‖

lemma psiMass_nonneg (ψ : SchwartzMap ℝ ℂ) : 0 ≤ psiMass ψ :=
  integral_nonneg fun u => norm_nonneg _

/-- The set integral of the modulus of the shifted window is at most the `L¹` mass. -/
lemma lintegral_psi_sub_le (ψ : SchwartzMap ℝ ℂ) (a b : ℝ) (j : ℤ) :
    ∫⁻ y in Set.Icc a b, ‖ψ (y - (j:ℝ))‖ₑ ≤ ENNReal.ofReal (psiMass ψ) := by
  have hint : MeasureTheory.Integrable (fun y : ℝ => ‖ψ y‖) := ψ.integrable.norm
  have hmain : (∫⁻ y : ℝ, ENNReal.ofReal ‖ψ y‖) = ENNReal.ofReal (∫ y : ℝ, ‖ψ y‖) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (f := fun y : ℝ => ‖ψ y‖) hint
      (Filter.Eventually.of_forall fun y => norm_nonneg _)).symm
  calc ∫⁻ y in Set.Icc a b, ‖ψ (y - (j:ℝ))‖ₑ
      ≤ ∫⁻ y : ℝ, ‖ψ (y - (j:ℝ))‖ₑ := by
        simpa using lintegral_mono_set (Set.subset_univ (Set.Icc a b))
    _ = ∫⁻ y : ℝ, ‖ψ y‖ₑ := lintegral_sub_right_eq_self (fun y => ‖ψ y‖ₑ) (j:ℝ)
    _ = ENNReal.ofReal (∫ y : ℝ, ‖ψ y‖) := by
        rw [← hmain]
        exact lintegral_congr fun y => by simp
    _ = ENNReal.ofReal (psiMass ψ) := rfl

/-- The normalised sampling kernel of the window `ψ` over the interval `[a₀,b₀]`:
`latSampKernel ψ a₀ b₀ j = (b₀-a₀)⁻¹ ∫_{a₀}^{b₀} ‖ψ (y - j)‖ dy`. -/
def latSampKernel (ψ : SchwartzMap ℝ ℂ) (a₀ b₀ : ℝ) : ℤ → ENNReal :=
  fun j => ENNReal.ofReal (b₀ - a₀)⁻¹ * ∫⁻ y in Set.Icc a₀ b₀, ‖ψ (y - (j:ℝ))‖ₑ

@[simp] lemma latSampKernel_apply (ψ : SchwartzMap ℝ ℂ) (a₀ b₀ : ℝ) (j : ℤ) :
    latSampKernel ψ a₀ b₀ j
      = ENNReal.ofReal (b₀ - a₀)⁻¹ * ∫⁻ y in Set.Icc a₀ b₀, ‖ψ (y - (j:ℝ))‖ₑ := rfl

/-! ## The three regimes for the sampling kernel -/

lemma kernel_mass_bound (ψ : SchwartzMap ℝ ℂ) {a₀ b₀ : ℝ} (hL : 0 < b₀ - a₀) (j : ℤ) :
    latSampKernel ψ a₀ b₀ j ≤ ENNReal.ofReal ((b₀ - a₀)⁻¹ * psiMass ψ) := by
  rw [latSampKernel_apply]
  calc ENNReal.ofReal (b₀ - a₀)⁻¹ * ∫⁻ y in Set.Icc a₀ b₀, ‖ψ (y - (j:ℝ))‖ₑ
      ≤ ENNReal.ofReal (b₀ - a₀)⁻¹ * ENNReal.ofReal (psiMass ψ) :=
        mul_le_mul_right (lintegral_psi_sub_le ψ a₀ b₀ j) _
    _ = ENNReal.ofReal ((b₀ - a₀)⁻¹ * psiMass ψ) := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hL.le)]

lemma kernel_sup_bound (ψ : SchwartzMap ℝ ℂ) {a₀ b₀ : ℝ} (hL : 0 < b₀ - a₀) (j : ℤ) :
    latSampKernel ψ a₀ b₀ j ≤ ENNReal.ofReal (psiDecay ψ) := by
  have hA : 0 ≤ psiDecay ψ := psiDecay_nonneg ψ
  have hpt : ∀ y : ℝ, ‖ψ (y - (j:ℝ))‖ₑ ≤ ENNReal.ofReal (psiDecay ψ) := by
    intro y
    rw [show ‖ψ (y - (j:ℝ))‖ₑ = ENNReal.ofReal ‖ψ (y - (j:ℝ))‖ by simp]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖ψ (y - (j:ℝ))‖ ≤ psiDecay ψ * (1 + |y - (j:ℝ)|) ^ (-2 : ℝ) := psi_norm_le ψ _
      _ ≤ psiDecay ψ * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ hA
          rw [Real.rpow_neg (by positivity), Real.rpow_two]
          exact inv_le_one_of_one_le₀ (by nlinarith [abs_nonneg (y - (j:ℝ))])
      _ = psiDecay ψ := mul_one _
  rw [latSampKernel_apply]
  have hvol : ∫⁻ y in Set.Icc a₀ b₀, ENNReal.ofReal (psiDecay ψ)
      = ENNReal.ofReal (psiDecay ψ) * ENNReal.ofReal (b₀ - a₀) := by
    rw [setLIntegral_const, Real.volume_Icc]
  calc ENNReal.ofReal (b₀ - a₀)⁻¹ * ∫⁻ y in Set.Icc a₀ b₀, ‖ψ (y - (j:ℝ))‖ₑ
      ≤ ENNReal.ofReal (b₀ - a₀)⁻¹ * ∫⁻ y in Set.Icc a₀ b₀, ENNReal.ofReal (psiDecay ψ) :=
        mul_le_mul_right (lintegral_mono fun y => hpt y) _
    _ = ENNReal.ofReal (b₀ - a₀)⁻¹ *
          (ENNReal.ofReal (psiDecay ψ) * ENNReal.ofReal (b₀ - a₀)) := by rw [hvol]
    _ = ENNReal.ofReal (psiDecay ψ) *
          (ENNReal.ofReal (b₀ - a₀)⁻¹ * ENNReal.ofReal (b₀ - a₀)) := by ring
    _ ≤ ENNReal.ofReal (psiDecay ψ) * 1 :=
        mul_le_mul_right (ofReal_inv_mul_ofReal_le_one (b₀ - a₀)) _
    _ = ENNReal.ofReal (psiDecay ψ) := mul_one _

/-- Elementary: `(1 + c/2)^{-2} ≤ 4 (1 + c)^{-2}` for `c ≥ 0`. -/
lemma rpow_neg_two_half_le (c : ℝ) (hc : 0 ≤ c) :
    (1 + c/2) ^ (-2 : ℝ) ≤ 4 * (1 + c) ^ (-2 : ℝ) := by
  have hA : (0:ℝ) < (1+c)/2 := by linarith
  have hB : (1+c)/2 ≤ 1 + c/2 := by linarith
  calc (1 + c/2) ^ (-2 : ℝ) ≤ ((1+c)/2) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hA hB (by norm_num)
    _ = 4 * (1 + c) ^ (-2 : ℝ) := by
        simp only [Real.rpow_neg (by positivity : (0:ℝ) ≤ (1+c)/2),
          Real.rpow_neg (by linarith : (0:ℝ) ≤ 1+c), Real.rpow_two]
        rw [div_pow]
        norm_num
        rw [div_eq_mul_inv]

/-- Far-field decay of the sampling kernel: if the lattice point `j` is at distance at least `2`
from `t` and the averaging interval is at most half that far, then the normalised window average
decays like `latKernel`. -/
lemma kernel_far_bound (ψ : SchwartzMap ℝ ℂ) {a₀ b₀ t : ℝ} (hL : 0 < b₀ - a₀)
    (ha₀ : a₀ ≤ t) (hb₀ : t ≤ b₀) {j : ℤ}
    (h2 : 2 ≤ |t - (j:ℝ)|) (hL2 : b₀ - a₀ ≤ |t - (j:ℝ)| / 2) :
    latSampKernel ψ a₀ b₀ j ≤ ENNReal.ofReal (4 * psiDecay ψ) * latKernel (t - (j:ℝ)) := by
  have hA : 0 ≤ psiDecay ψ := psiDecay_nonneg ψ
  set c : ℝ := |t - (j:ℝ)| with hc
  have hc2 : 2 ≤ c := h2
  have hLc : b₀ - a₀ ≤ c / 2 := hL2
  rw [latSampKernel_apply]
  -- pointwise bound on the interval
  have hpt : ∀ y ∈ Set.Icc a₀ b₀,
      ‖ψ (y - (j:ℝ))‖ₑ ≤ ENNReal.ofReal (4 * psiDecay ψ) * latKernel (t - (j:ℝ)) := by
    intro y hy
    have hyt : |t - y| ≤ b₀ - a₀ := by
      rw [abs_le]; exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have hsplit : c ≤ |t - y| + |y - (j:ℝ)| := by
      calc c = |t - (j:ℝ)| := hc
        _ = |(t - y) + (y - (j:ℝ))| := by ring_nf
        _ ≤ |t - y| + |y - (j:ℝ)| := abs_add_le _ _
    have hyj : c / 2 ≤ |y - (j:ℝ)| := by
      have : |t - y| ≤ c / 2 := le_trans hyt hLc
      linarith
    have hmono : (1 + |y - (j:ℝ)|) ^ (-2 : ℝ) ≤ (1 + c/2) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
    have hnorm : ‖ψ (y - (j:ℝ))‖ ≤ psiDecay ψ * (4 * (1 + c) ^ (-2 : ℝ)) := by
      calc ‖ψ (y - (j:ℝ))‖ ≤ psiDecay ψ * (1 + |y - (j:ℝ)|) ^ (-2 : ℝ) := psi_norm_le ψ _
        _ ≤ psiDecay ψ * (1 + c/2) ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left hmono hA
        _ ≤ psiDecay ψ * (4 * (1 + c) ^ (-2 : ℝ)) :=
            mul_le_mul_of_nonneg_left (rpow_neg_two_half_le c (by linarith)) hA
    rw [show ‖ψ (y - (j:ℝ))‖ₑ = ENNReal.ofReal ‖ψ (y - (j:ℝ))‖ by simp]
    calc ENNReal.ofReal ‖ψ (y - (j:ℝ))‖
        ≤ ENNReal.ofReal (psiDecay ψ * (4 * (1 + c) ^ (-2 : ℝ))) :=
          ENNReal.ofReal_le_ofReal hnorm
      _ = ENNReal.ofReal (4 * psiDecay ψ) * latKernel (t - (j:ℝ)) := by
          rw [latKernel, ← hc, ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hA)]
          congr 1
          ring
  have hvol : ∫⁻ y in Set.Icc a₀ b₀,
        ENNReal.ofReal (4 * psiDecay ψ) * latKernel (t - (j:ℝ))
      = (ENNReal.ofReal (4 * psiDecay ψ) * latKernel (t - (j:ℝ))) * ENNReal.ofReal (b₀ - a₀) := by
    rw [setLIntegral_const, Real.volume_Icc]
  calc ENNReal.ofReal (b₀ - a₀)⁻¹ * ∫⁻ y in Set.Icc a₀ b₀, ‖ψ (y - (j:ℝ))‖ₑ
      ≤ ENNReal.ofReal (b₀ - a₀)⁻¹ * ∫⁻ y in Set.Icc a₀ b₀,
          ENNReal.ofReal (4 * psiDecay ψ) * latKernel (t - (j:ℝ)) :=
        mul_le_mul_right (setLIntegral_mono' measurableSet_Icc (fun y hy => hpt y hy)) _
    _ = ENNReal.ofReal (b₀ - a₀)⁻¹ *
          ((ENNReal.ofReal (4 * psiDecay ψ) * latKernel (t - (j:ℝ))) *
            ENNReal.ofReal (b₀ - a₀)) := by rw [hvol]
    _ = (ENNReal.ofReal (4 * psiDecay ψ) * latKernel (t - (j:ℝ))) *
          (ENNReal.ofReal (b₀ - a₀)⁻¹ * ENNReal.ofReal (b₀ - a₀)) := by ring
    _ ≤ (ENNReal.ofReal (4 * psiDecay ψ) * latKernel (t - (j:ℝ))) * 1 :=
        mul_le_mul_right (ofReal_inv_mul_ofReal_le_one (b₀ - a₀)) _
    _ = ENNReal.ofReal (4 * psiDecay ψ) * latKernel (t - (j:ℝ)) := mul_one _

/-- Near-field bound: for `|t - j| ≤ 2`, the trivial `L^∞` bound of the window is still dominated
by `16 ‖ψ‖_∞ latKernel (t-j)`, because `latKernel (t-j) ≥ 1/9` there. -/
lemma kernel_sup_le_kernel {ψ : SchwartzMap ℝ ℂ} {t : ℝ} {j : ℤ}
    (h : |t - (j:ℝ)| ≤ 2) :
    ENNReal.ofReal (psiDecay ψ) ≤ ENNReal.ofReal (16 * psiDecay ψ) * latKernel (t - (j:ℝ)) := by
  have hA : 0 ≤ psiDecay ψ := psiDecay_nonneg ψ
  have h9 : (1:ℝ)/9 ≤ (1 + |t - (j:ℝ)|) ^ (-2 : ℝ) := by
    have h3 : 1 + |t - (j:ℝ)| ≤ 3 := by linarith [abs_nonneg (t - (j:ℝ))]
    have h3' : (3:ℝ) ^ (-2:ℝ) = 1/9 := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num
    rw [← h3']
    exact Real.rpow_le_rpow_of_nonpos (by positivity) h3 (by norm_num)
  calc ENNReal.ofReal (psiDecay ψ)
      ≤ ENNReal.ofReal (16 * psiDecay ψ) * ENNReal.ofReal ((1:ℝ)/9) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 16 * psiDecay ψ)]
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [hA]
    _ ≤ ENNReal.ofReal (16 * psiDecay ψ) * latKernel (t - (j:ℝ)) :=
        mul_le_mul_right (ENNReal.ofReal_le_ofReal h9) _

/-! ## The per-`j` bound of the maximal average -/

/-- **The lattice–kernel estimate for one averaging interval.**  For an interval `[a₀,b₀]`
containing `t` (of positive length `L`), the sum over the lattice of the sampled values `a j`
weighted by the normalised window average `latSampKernel ψ a₀ b₀ j` is at most a constant
(depending on `ψ`) times the discrete maximal function of `a` at `⌊t⌋` plus the far-field
convolution with `latKernel`. -/
lemma core_estimate (ψ : SchwartzMap ℝ ℂ) (a : ℤ → ENNReal) {a₀ b₀ t : ℝ}
    (ha₀ : a₀ ≤ t) (hb₀ : t ≤ b₀) (hL : 0 < b₀ - a₀) :
    (∑' j : ℤ, a j * latSampKernel ψ a₀ b₀ j)
      ≤ ENNReal.ofReal (4 * psiMass ψ + 16 * psiDecay ψ) *
          (latDiscMaxC a ⌊t⌋ + ∑' j : ℤ, a j * latKernel (t - (j:ℝ))) := by
  have hM : 0 ≤ psiMass ψ := psiMass_nonneg ψ
  have hA : 0 ≤ psiDecay ψ := psiDecay_nonneg ψ
  rcases le_total (b₀ - a₀) 1 with hsmall | hbig
  · -- small interval: everything is in the far-field regime
    have hstep : ∀ j : ℤ, a j * latSampKernel ψ a₀ b₀ j
        ≤ a j * (ENNReal.ofReal (16 * psiDecay ψ) * latKernel (t - (j:ℝ))) := by
      intro j
      refine mul_le_mul_right ?_ (a j)
      rcases le_total (2:ℝ) |t - (j:ℝ)| with hfar | hnear
      · refine (kernel_far_bound ψ hL ha₀ hb₀ hfar (by linarith)).trans ?_
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _
      · exact (kernel_sup_bound ψ hL j).trans (kernel_sup_le_kernel hnear)
    calc (∑' j : ℤ, a j * latSampKernel ψ a₀ b₀ j)
        ≤ ∑' j : ℤ, a j * (ENNReal.ofReal (16 * psiDecay ψ) * latKernel (t - (j:ℝ))) :=
          ENNReal.tsum_le_tsum hstep
      _ = ENNReal.ofReal (16 * psiDecay ψ) * ∑' j : ℤ, a j * latKernel (t - (j:ℝ)) := by
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun j => by ring
      _ ≤ ENNReal.ofReal (4 * psiMass ψ + 16 * psiDecay ψ) *
            (latDiscMaxC a ⌊t⌋ + ∑' j : ℤ, a j * latKernel (t - (j:ℝ))) := by
          have h16 : ENNReal.ofReal (16 * psiDecay ψ)
              ≤ ENNReal.ofReal (4 * psiMass ψ + 16 * psiDecay ψ) :=
            ENNReal.ofReal_le_ofReal (by linarith)
          have hG : (∑' j : ℤ, a j * latKernel (t - (j:ℝ)))
              ≤ latDiscMaxC a ⌊t⌋ + ∑' j : ℤ, a j * latKernel (t - (j:ℝ)) := le_add_left le_rfl
          refine le_trans (mul_le_mul_left h16 (∑' j : ℤ, a j * latKernel (t - (j:ℝ)))) ?_
          exact mul_le_mul_right hG (ENNReal.ofReal (4 * psiMass ψ + 16 * psiDecay ψ))
  · -- large interval: split at the discrete maximal function
    have hL1 : 1 ≤ b₀ - a₀ := hbig
    set N : ℕ := ⌈3 * (b₀ - a₀)⌉₊ with hN
    have hN3 : 3 * (b₀ - a₀) ≤ (N : ℝ) := by rw [hN]; exact Nat.le_ceil _
    have hNpos : 0 < N := by rw [hN]; exact Nat.ceil_pos.mpr (by linarith)
    have hN4 : (N : ℝ) ≤ 4 * (b₀ - a₀) := by
      have hlt : ((N:ℝ)) < 3 * (b₀ - a₀) + 1 := by
        rw [hN]; exact Nat.ceil_lt_add_one (by linarith)
      linarith
    set S : Finset ℤ := Finset.Icc (⌊t⌋ - (N:ℤ)) (⌊t⌋ + (N:ℤ)) with hS
    have hsplit : (∑' j : ℤ, a j * latSampKernel ψ a₀ b₀ j)
        ≤ (∑' j : ℤ, if j ∈ S then a j * latSampKernel ψ a₀ b₀ j else 0)
          + ∑' j : ℤ, if j ∈ S then 0 else a j * latSampKernel ψ a₀ b₀ j := by
      rw [show (∑' j : ℤ, a j * latSampKernel ψ a₀ b₀ j)
          = ∑' j : ℤ, ((if j ∈ S then a j * latSampKernel ψ a₀ b₀ j else 0)
              + (if j ∈ S then 0 else a j * latSampKernel ψ a₀ b₀ j)) from
        tsum_congr fun j => by by_cases h : j ∈ S <;> simp [h]]
      rw [ENNReal.tsum_add]
    -- the near part is controlled by the discrete maximal function
    have hnear : (∑' j : ℤ, if j ∈ S then a j * latSampKernel ψ a₀ b₀ j else 0)
        ≤ ENNReal.ofReal (4 * psiMass ψ) * latDiscMaxC a ⌊t⌋ := by
      have h1 : (∑' j : ℤ, if j ∈ S then a j * latSampKernel ψ a₀ b₀ j else 0)
          ≤ ∑' j : ℤ,
              if j ∈ S then a j * ENNReal.ofReal ((b₀ - a₀)⁻¹ * psiMass ψ) else 0 := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        by_cases h : j ∈ S
        · simp only [h, if_true]
          exact mul_le_mul_right (kernel_mass_bound ψ hL j) (a j)
        · simp only [h, if_false]; exact bot_le
      have h2 : (∑' j : ℤ,
            if j ∈ S then a j * ENNReal.ofReal ((b₀ - a₀)⁻¹ * psiMass ψ) else 0)
          = ENNReal.ofReal ((b₀ - a₀)⁻¹ * psiMass ψ) *
              ∑' j : ℤ, if j ∈ S then a j else 0 := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun j => by by_cases h : j ∈ S <;> simp [h, mul_comm]
      have h3 : (∑' j : ℤ, if j ∈ S then a j else 0) ≤ ∑ j ∈ S, a j := by
        rw [ENNReal.tsum_eq_iSup_sum]
        refine iSup_le fun s => ?_
        rw [← Finset.sum_filter]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => bot_le)
        intro x hx
        rw [Finset.mem_filter] at hx
        exact hx.2
      have h4 : (∑ j ∈ S, a j) ≤ (N : ENNReal) * latDiscMaxC a ⌊t⌋ := by
        have hNne : (N : ENNReal) ≠ 0 := by
          rw [← ENNReal.ofReal_natCast]
          exact (ENNReal.ofReal_pos.mpr (by exact_mod_cast hNpos)).ne'
        have hle : ((N : ENNReal))⁻¹ * (∑ j ∈ S, a j) ≤ latDiscMaxC a ⌊t⌋ := by
          rw [latDiscMaxC, hS]
          exact le_iSup_of_le N (le_iSup_of_le hNpos le_rfl)
        calc (∑ j ∈ S, a j) = (N : ENNReal) * (((N : ENNReal))⁻¹ * ∑ j ∈ S, a j) := by
              rw [← mul_assoc, ENNReal.mul_inv_cancel hNne (by simp), one_mul]
          _ ≤ (N : ENNReal) * latDiscMaxC a ⌊t⌋ := mul_le_mul_right hle _
      have h5 : ENNReal.ofReal ((b₀ - a₀)⁻¹ * psiMass ψ) * ((N : ENNReal) * latDiscMaxC a ⌊t⌋)
          ≤ ENNReal.ofReal (4 * psiMass ψ) * latDiscMaxC a ⌊t⌋ := by
        have hkey : ENNReal.ofReal ((b₀ - a₀)⁻¹ * psiMass ψ) * (N : ENNReal)
            ≤ ENNReal.ofReal (4 * psiMass ψ) := by
          have hcast : ((N : ℕ) : ENNReal) = ENNReal.ofReal ((N : ℕ) : ℝ) :=
            (ENNReal.ofReal_natCast N).symm
          rw [hcast, ← ENNReal.ofReal_mul (p := (b₀ - a₀)⁻¹ * psiMass ψ)
            (q := ((N : ℕ) : ℝ)) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hNL : (b₀ - a₀)⁻¹ * ((N : ℕ) : ℝ) ≤ 4 := by
            rw [mul_comm, mul_inv_le_iff₀ hL]
            exact hN4
          calc (b₀ - a₀)⁻¹ * psiMass ψ * ((N : ℕ) : ℝ)
              = ((b₀ - a₀)⁻¹ * ((N : ℕ) : ℝ)) * psiMass ψ := by ring
            _ ≤ 4 * psiMass ψ := mul_le_mul hNL le_rfl hM (by norm_num)
        calc ENNReal.ofReal ((b₀ - a₀)⁻¹ * psiMass ψ) * ((N : ENNReal) * latDiscMaxC a ⌊t⌋)
            = (ENNReal.ofReal ((b₀ - a₀)⁻¹ * psiMass ψ) * (N : ENNReal)) *
                latDiscMaxC a ⌊t⌋ := by rw [mul_assoc]
          _ ≤ ENNReal.ofReal (4 * psiMass ψ) * latDiscMaxC a ⌊t⌋ := mul_le_mul_left hkey _
      calc (∑' j : ℤ, if j ∈ S then a j * latSampKernel ψ a₀ b₀ j else 0)
          ≤ ∑' j : ℤ,
              if j ∈ S then a j * ENNReal.ofReal ((b₀ - a₀)⁻¹ * psiMass ψ) else 0 := h1
        _ = ENNReal.ofReal ((b₀ - a₀)⁻¹ * psiMass ψ) *
              ∑' j : ℤ, if j ∈ S then a j else 0 := h2
        _ ≤ ENNReal.ofReal ((b₀ - a₀)⁻¹ * psiMass ψ) * (∑ j ∈ S, a j) :=
            mul_le_mul_right h3 _
        _ ≤ ENNReal.ofReal ((b₀ - a₀)⁻¹ * psiMass ψ) * ((N : ENNReal) * latDiscMaxC a ⌊t⌋) :=
            mul_le_mul_right h4 _
        _ ≤ ENNReal.ofReal (4 * psiMass ψ) * latDiscMaxC a ⌊t⌋ := h5
    -- the far part is controlled by the summable kernel
    have hfarpart : (∑' j : ℤ, if j ∈ S then 0 else a j * latSampKernel ψ a₀ b₀ j)
        ≤ ENNReal.ofReal (4 * psiDecay ψ) * ∑' j : ℤ, a j * latKernel (t - (j:ℝ)) := by
      have h1 : (∑' j : ℤ, if j ∈ S then 0 else a j * latSampKernel ψ a₀ b₀ j)
          ≤ ∑' j : ℤ, if j ∈ S then 0 else
              a j * (ENNReal.ofReal (4 * psiDecay ψ) * latKernel (t - (j:ℝ))) := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        by_cases h : j ∈ S
        · simp only [h, if_true]; exact bot_le
        · simp only [h, if_false]
          refine mul_le_mul_right ?_ (a j)
          rw [Finset.mem_Icc] at h
          have hdis : j < ⌊t⌋ - (N:ℤ) ∨ ⌊t⌋ + (N:ℤ) < j := by
            by_contra hcon
            push_neg at hcon
            exact h ⟨hcon.1, hcon.2⟩
          rcases hdis with hlt | hgt
          · -- j < ⌊t⌋ - N
            have hjint : j ≤ ⌊t⌋ - (N:ℤ) - 1 := by omega
            have hjreal : ((j:ℤ):ℝ) ≤ ((⌊t⌋ - (N:ℤ) - 1 : ℤ):ℝ) := by exact_mod_cast hjint
            have hjN : (N:ℝ) ≤ t - (j:ℝ) := by
              have h2 : ((⌊t⌋:ℤ):ℝ) ≤ t := Int.floor_le t
              push_cast at hjreal
              linarith
            have habs : (N:ℝ) ≤ |t - (j:ℝ)| := by
              rw [abs_of_nonneg (by linarith)]
              exact hjN
            exact kernel_far_bound ψ hL ha₀ hb₀ (le_trans (by linarith) habs)
              (by linarith [habs, hN3, hL1])
          · -- ⌊t⌋ + N < j
            have hjint : ⌊t⌋ + (N:ℤ) + 1 ≤ j := by omega
            have hjreal : ((⌊t⌋ + (N:ℤ) + 1 : ℤ):ℝ) ≤ ((j:ℤ):ℝ) := by exact_mod_cast hjint
            have hjN : (N:ℝ) ≤ (j:ℝ) - t := by
              have h2 : t < ((⌊t⌋:ℤ):ℝ) + 1 := Int.lt_floor_add_one t
              push_cast at hjreal
              linarith
            have habs : (N:ℝ) ≤ |t - (j:ℝ)| := by
              rw [abs_of_nonpos (by linarith)]
              linarith
            exact kernel_far_bound ψ hL ha₀ hb₀ (le_trans (by linarith) habs)
              (by linarith [habs, hN3, hL1])
      have h2 : (∑' j : ℤ, if j ∈ S then 0 else
            a j * (ENNReal.ofReal (4 * psiDecay ψ) * latKernel (t - (j:ℝ))))
          ≤ ∑' j : ℤ, a j * (ENNReal.ofReal (4 * psiDecay ψ) * latKernel (t - (j:ℝ))) := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        by_cases h : j ∈ S
        · simp only [h, if_true]; exact bot_le
        · simp only [h, if_false]; exact le_rfl
      have h3 : (∑' j : ℤ, a j * (ENNReal.ofReal (4 * psiDecay ψ) * latKernel (t - (j:ℝ))))
          = ENNReal.ofReal (4 * psiDecay ψ) * ∑' j : ℤ, a j * latKernel (t - (j:ℝ)) := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun j => by ring
      calc (∑' j : ℤ, if j ∈ S then 0 else a j * latSampKernel ψ a₀ b₀ j)
          ≤ _ := h1
        _ ≤ _ := h2
        _ = ENNReal.ofReal (4 * psiDecay ψ) * ∑' j : ℤ, a j * latKernel (t - (j:ℝ)) := h3
    calc (∑' j : ℤ, a j * latSampKernel ψ a₀ b₀ j)
        ≤ (∑' j : ℤ, if j ∈ S then a j * latSampKernel ψ a₀ b₀ j else 0)
          + ∑' j : ℤ, if j ∈ S then 0 else a j * latSampKernel ψ a₀ b₀ j := hsplit
      _ ≤ ENNReal.ofReal (4 * psiMass ψ) * latDiscMaxC a ⌊t⌋
          + ENNReal.ofReal (4 * psiDecay ψ) * ∑' j : ℤ, a j * latKernel (t - (j:ℝ)) :=
          add_le_add hnear hfarpart
      _ ≤ ENNReal.ofReal (4 * psiMass ψ + 16 * psiDecay ψ) * latDiscMaxC a ⌊t⌋
          + ENNReal.ofReal (4 * psiMass ψ + 16 * psiDecay ψ) *
              ∑' j : ℤ, a j * latKernel (t - (j:ℝ)) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _
          · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _
      _ = ENNReal.ofReal (4 * psiMass ψ + 16 * psiDecay ψ) *
            (latDiscMaxC a ⌊t⌋ + ∑' j : ℤ, a j * latKernel (t - (j:ℝ))) := by rw [mul_add]

theorem lat_hlMax_kernel_estimate_uniform {ψ : SchwartzMap ℝ ℂ}
    (hψ1 : ∀ ξ ∈ Set.Icc (-(1 / 4) : ℝ) (1 / 4), FourierTransform.fourier (⇑ψ) ξ = 1)
    (hψ0 : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → FourierTransform.fourier (⇑ψ) ξ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℝ → ℂ), Continuous H → MeasureTheory.Integrable H →
      (∀ ξ : ℝ, 1 / 4 < |ξ| → FourierTransform.fourier H ξ = 0) → ∀ t : ℝ,
      Work.Maximal.mstHlMax (fun y : ℝ => ENNReal.ofReal ‖H y‖) t
        ≤ ENNReal.ofReal C *
            (Work.BourgainPlan.Maximal.latDiscMaxC (fun j : ℤ => ‖H (j : ℝ)‖ₑ) ⌊t⌋
              + ∑' j : ℤ, ‖H (j : ℝ)‖ₑ * Work.BourgainPlan.Maximal.latKernel (t - (j : ℝ))) := by
  refine ⟨4 * psiMass ψ + 16 * psiDecay ψ + 1,
    by linarith [psiMass_nonneg ψ, psiDecay_nonneg ψ], ?_⟩
  intro H hHc hH1 hband t
  have hsam : ∀ y : ℝ, H y = ∑' j : ℤ, ψ (y - (j:ℝ)) * H (j:ℝ) :=
    lat_sampling_reproduce hHc hH1 hband hψ1 hψ0
  -- pointwise domination of `‖H‖` by the sampled values
  have hpt : ∀ y : ℝ, ‖H y‖ₑ ≤ ∑' j : ℤ, ‖ψ (y - (j:ℝ))‖ₑ * ‖H (j:ℝ)‖ₑ := by
    intro y
    rw [hsam y]
    calc ‖∑' j : ℤ, ψ (y - (j:ℝ)) * H (j:ℝ)‖ₑ
        ≤ ∑' j : ℤ, ‖ψ (y - (j:ℝ)) * H (j:ℝ)‖ₑ := enorm_tsum_le_tsum_enorm
      _ = ∑' j : ℤ, ‖ψ (y - (j:ℝ))‖ₑ * ‖H (j:ℝ)‖ₑ := tsum_congr fun j => enorm_mul _ _
  have hmeas : ∀ j : ℤ, AEMeasurable
      (fun y : ℝ => ‖ψ (y - (j:ℝ))‖ₑ * ‖H (j:ℝ)‖ₑ) volume :=
    fun j => (((SchwartzMap.continuous ψ).measurable.comp
      (measurable_id.sub_const (j:ℝ))).enorm.mul_const _).aemeasurable
  rw [Work.Maximal.mstHlMax_apply, Commons.Analysis.Maximal.hlMax]
  refine iSup_le fun a₀ => iSup_le fun b₀ => iSup_le fun hab => ?_
  obtain ⟨ha₀, hb₀⟩ := hab
  rcases eq_or_lt_of_le (sub_nonneg.mpr (ha₀.trans hb₀)) with h0 | hpos
  · rw [← h0]; simp
  · have hK : ENNReal.ofReal (b₀ - a₀)⁻¹ * ∫⁻ y in Set.Icc a₀ b₀, ENNReal.ofReal ‖H y‖
        ≤ ∑' j : ℤ, ‖H (j:ℝ)‖ₑ * latSampKernel ψ a₀ b₀ j := by
      calc ENNReal.ofReal (b₀ - a₀)⁻¹ * ∫⁻ y in Set.Icc a₀ b₀, ENNReal.ofReal ‖H y‖
          = ENNReal.ofReal (b₀ - a₀)⁻¹ * ∫⁻ y in Set.Icc a₀ b₀, ‖H y‖ₑ := by
            congr 1
            exact lintegral_congr fun y => (by simp : ‖H y‖ₑ = ENNReal.ofReal ‖H y‖).symm
        _ ≤ ENNReal.ofReal (b₀ - a₀)⁻¹ *
              ∫⁻ y in Set.Icc a₀ b₀, ∑' j : ℤ, ‖ψ (y - (j:ℝ))‖ₑ * ‖H (j:ℝ)‖ₑ :=
            mul_le_mul_right (lintegral_mono fun y => hpt y) _
        _ = ENNReal.ofReal (b₀ - a₀)⁻¹ *
              ∑' j : ℤ, ∫⁻ y in Set.Icc a₀ b₀, ‖ψ (y - (j:ℝ))‖ₑ * ‖H (j:ℝ)‖ₑ := by
            congr 1
            exact lintegral_tsum (fun j => (hmeas j).mono_measure Measure.restrict_le_self)
        _ = ENNReal.ofReal (b₀ - a₀)⁻¹ *
              ∑' j : ℤ, (‖H (j:ℝ)‖ₑ * ∫⁻ y in Set.Icc a₀ b₀, ‖ψ (y - (j:ℝ))‖ₑ) := by
            congr 1
            exact tsum_congr fun j =>
              (lintegral_congr fun y => mul_comm _ _).trans
                (lintegral_const_mul' _ _ (by simp))
        _ = ∑' j : ℤ, ‖H (j:ℝ)‖ₑ * latSampKernel ψ a₀ b₀ j := by
            simp only [latSampKernel_apply]
            rw [← ENNReal.tsum_mul_left]
            exact tsum_congr fun j => by ring
    calc ENNReal.ofReal (b₀ - a₀)⁻¹ * ∫⁻ y in Set.Icc a₀ b₀, ENNReal.ofReal ‖H y‖
        ≤ ∑' j : ℤ, ‖H (j:ℝ)‖ₑ * latSampKernel ψ a₀ b₀ j := hK
      _ ≤ ENNReal.ofReal (4 * psiMass ψ + 16 * psiDecay ψ) *
            (latDiscMaxC (fun j : ℤ => ‖H (j:ℝ)‖ₑ) ⌊t⌋
              + ∑' j : ℤ, ‖H (j:ℝ)‖ₑ * latKernel (t - (j:ℝ))) :=
          core_estimate ψ (fun j : ℤ => ‖H (j:ℝ)‖ₑ) ha₀ hb₀ hpos
      _ ≤ ENNReal.ofReal (4 * psiMass ψ + 16 * psiDecay ψ + 1) *
            (latDiscMaxC (fun j : ℤ => ‖H (j:ℝ)‖ₑ) ⌊t⌋
              + ∑' j : ℤ, ‖H (j:ℝ)‖ₑ * latKernel (t - (j:ℝ))) :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal
            (by linarith [psiMass_nonneg ψ, psiDecay_nonneg ψ]))
            (latDiscMaxC (fun j : ℤ => ‖H (j:ℝ)‖ₑ) ⌊t⌋
              + ∑' j : ℤ, ‖H (j:ℝ)‖ₑ * latKernel (t - (j:ℝ)))

end

end Work.BourgainPlan.Maximal
