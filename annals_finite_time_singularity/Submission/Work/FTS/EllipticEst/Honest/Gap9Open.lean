import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Auxiliary.Slice9PoincareGap

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-!
## `Gap9Open`: the constrained slice Poincaré inequality for `C²`-in-the-open functions

The target statement (`Work.FTS.EllipticEst.Honest.Gap9Open`) is

`9 ∫_{Iθ} f² ≤ ∫_{Iθ} (f')²`

for `f : ℝ → ℝ` which is `C²` on the *open* interval `(0,π/2)`, continuous on `[0,π/2]`,
vanishes at both endpoints, with `(f')²` integrable on `[0,π/2]` and `∫_{Iθ} f · sinθcos²θ = 0`.

The proof goes by *squeezing*: `θ ↦ δ + c(δ)·θ` maps `[0,π/2]` onto `[δ, π/2-δ]` with
`c(δ) = 1 - 2δ/(π/2)`, and for small `δ` the function

`g_δ(θ) = f(δ + c(δ)θ) - (f(δ) + ((f(π/2-δ) - f(δ))/(π/2))·θ)`

is `C²` on the *closed* interval (its arguments stay in the compact `[δ, π/2-δ] ⊂ (0,π/2)`),
vanishes at both endpoints, and converges to `f` in `L¹(Iθ)` as `δ → 0`.  Correcting the
second moment by a multiple of `sin 2θ` makes it satisfy the solvability condition, so the
already-proved strong version `Work.FTS.EllipticEst.P9.slicePoincare9_fts` applies.  The
estimates are the exact dilation identity
`∫ (f(δ+cθ)')² = c ∫_δ^{π/2-δ} (f')² - (f(π/2-δ) - f(δ))²/(π/2) ≤ ∫ (f')²`,
the two `L¹` bounds following from `|g_δ| ≤ 4M` (`M` a bound for `|f|`), and the limit
`∫ |g_δ - f| → 0` supplied by dominated convergence.
-/

/-! ### The squeeze parameters -/

/-- `δ n = 1/(n+2)`, the squeezing parameter. -/
def gapDelta (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

/-- The dilation factor `c(δ) = 1 - 2δ/(π/2)`: the map `θ ↦ δ + c(δ)θ` sends `[0,π/2]`
onto `[δ, π/2 - δ]`. -/
def gapDC (δ : ℝ) : ℝ := 1 - 2 * δ / (Real.pi / 2)

/-- `Δ(δ) = f(π/2 - δ) - f δ`. -/
def gapDD (f : ℝ → ℝ) (δ : ℝ) : ℝ := f (Real.pi / 2 - δ) - f δ

/-- `c n = c(δ n)`. -/
def gapC (n : ℕ) : ℝ := gapDC (gapDelta n)

/-- `Δ n = Δ(δ n)`. -/
def gapD (f : ℝ → ℝ) (n : ℕ) : ℝ := gapDD f (gapDelta n)

/-- The affine correction `m_n(θ) = f(δ n) + (Δ n/(π/2))·θ`. -/
def gapM (f : ℝ → ℝ) (n : ℕ) (θ : ℝ) : ℝ := f (gapDelta n) + gapD f n / (Real.pi / 2) * θ

/-- The squeezed function `g_n(θ) = f(δ n + c n·θ) - m_n(θ)`. -/
def gapG (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  fun θ => f (gapDelta n + gapC n * θ) - gapM f n θ

/-- The coefficient of the correction making the second moment vanish:
`a_n = (15/4) ∫_{Iθ} g_n θ · sinθcos²θ`. -/
def gapA (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  (15 / 4) * ∫ θ in Work.Spaces.Iθ, gapG f n θ * Work.Elliptic.sinCos2 θ

/-- The corrected function `F_n = g_n - a_n · sin 2θ`, which satisfies all hypotheses of the
strong slice Poincaré inequality. -/
def gapF (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  fun θ => gapG f n θ - gapA f n * Real.sin (2 * θ)

/-! ### Elementary facts about the parameters -/

section Basic

variable {f : ℝ → ℝ}

theorem gapDelta_pos (n : ℕ) : 0 < gapDelta n := by
  unfold gapDelta; positivity

theorem gapDelta_nonneg (n : ℕ) : 0 ≤ gapDelta n := (gapDelta_pos n).le

theorem gapDelta_le_half' (n : ℕ) : gapDelta n ≤ 1 / 2 := by
  unfold gapDelta
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)

theorem gapDelta_le_one (n : ℕ) : gapDelta n ≤ 1 := by
  linarith [gapDelta_le_half' n]

/-- `δ n ≤ π/4 = (π/2)/2`. -/
theorem gapDelta_le_half (n : ℕ) : gapDelta n ≤ Real.pi / 4 := by
  have h1 := gapDelta_le_half' n
  have h2 : (1 : ℝ) / 2 ≤ Real.pi / 4 := by nlinarith [Real.pi_gt_three]
  linarith

theorem tendsto_gapDelta : Tendsto gapDelta atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 (tendsto_natCast_atTop_atTop (R := ℝ))
  have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h1
  have hg : gapDelta = fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2) := rfl
  rw [hg]
  exact h2

theorem eventually_gapDelta_lt_eighth : ∀ᶠ n in atTop, gapDelta n < Real.pi / 8 := by
  filter_upwards [eventually_ge_atTop 3] with n hn
  have h1 : gapDelta n ≤ 1 / 5 := by
    unfold gapDelta
    refine div_le_div_of_nonneg_left (by norm_num) (by norm_num) ?_
    have hn' : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h2 : (1 : ℝ) / 5 < Real.pi / 8 := by nlinarith [Real.pi_gt_three]
  linarith

theorem gapC_mul_pi (n : ℕ) : gapC n * (Real.pi / 2) = Real.pi / 2 - 2 * gapDelta n := by
  unfold gapC gapDC
  field_simp

theorem gapC_nonneg (n : ℕ) : 0 ≤ gapC n := by
  have hL : (0 : ℝ) < Real.pi / 2 := by positivity
  have h1 : 2 * gapDelta n / (Real.pi / 2) ≤ 1 := by
    rw [div_le_one hL]; linarith [gapDelta_le_half n]
  unfold gapC gapDC
  linarith

theorem gapC_le_one (n : ℕ) : gapC n ≤ 1 := by
  have h1 : 0 ≤ 2 * gapDelta n / (Real.pi / 2) :=
    div_nonneg (by linarith [gapDelta_nonneg n]) (by positivity)
  unfold gapC gapDC
  linarith

theorem gapC_pos {n : ℕ} (h : gapDelta n < Real.pi / 8) : 0 < gapC n := by
  have hL : (0 : ℝ) < Real.pi / 2 := by positivity
  have h1 : 2 * gapDelta n / (Real.pi / 2) < 1 := by
    rw [div_lt_one hL]; linarith
  unfold gapC gapDC
  linarith

/-- The squeeze map sends `Iθ` into `Iθ`. -/
theorem gap_shift_mem_Icc (n : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    gapDelta n + gapC n * θ ∈ Set.Icc 0 (Real.pi / 2) := by
  have hc0 := gapC_nonneg n
  have hcl := gapC_mul_pi n
  have h1 : gapDelta n ≤ Real.pi / 2 := by linarith [gapDelta_le_half n, Real.pi_pos]
  constructor
  · have h2 : 0 ≤ gapC n * θ := mul_nonneg hc0 hθ.1
    linarith [gapDelta_nonneg n]
  · have h2 : gapC n * θ ≤ gapC n * (Real.pi / 2) := mul_le_mul_of_nonneg_left hθ.2 hc0
    have h3 : (0:ℝ) < gapDelta n := gapDelta_pos n
    linarith [hcl ▸ h2]

/-- For `δ < π/8` the squeeze map sends `Iθ` into the *open* interval. -/
theorem gap_shift_mem_Ioo {n : ℕ} (h : gapDelta n < Real.pi / 8) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    gapDelta n + gapC n * θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have hc0 := (gapC_pos h).le
  have hcl := gapC_mul_pi n
  have hδ := gapDelta_pos n
  constructor
  · have h2 : 0 ≤ gapC n * θ := mul_nonneg hc0 hθ.1
    linarith
  · have h2 : gapC n * θ ≤ gapC n * (Real.pi / 2) := mul_le_mul_of_nonneg_left hθ.2 hc0
    have h3 : gapDelta n < Real.pi / 2 := by linarith [Real.pi_pos]
    linarith [hcl ▸ h2]

end Basic

/-! ### Smoothness of the squeezed family -/

section Smooth

variable {f : ℝ → ℝ}

theorem gapG_contDiffOn (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) {n : ℕ}
    (h : gapDelta n < Real.pi / 8) :
    ContDiffOn ℝ 2 (gapG f n) (Set.Icc 0 (Real.pi / 2)) := by
  have hmap : MapsTo (fun θ : ℝ => gapDelta n + gapC n * θ) (Set.Icc 0 (Real.pi / 2))
      (Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => gap_shift_mem_Ioo h hθ
  have hcomp : ContDiffOn ℝ 2 (fun θ : ℝ => f (gapDelta n + gapC n * θ))
      (Set.Icc 0 (Real.pi / 2)) := ContDiffOn.comp hf2 (by fun_prop) hmap
  have haff : ContDiffOn ℝ 2 (gapM f n) (Set.Icc 0 (Real.pi / 2)) := by
    unfold gapM; fun_prop
  exact (hcomp.sub haff).congr (fun θ _ => rfl)

theorem gapF_contDiffOn (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) {n : ℕ}
    (h : gapDelta n < Real.pi / 8) :
    ContDiffOn ℝ 2 (gapF f n) (Set.Icc 0 (Real.pi / 2)) := by
  have hG := gapG_contDiffOn hf2 h
  have hsin : ContDiffOn ℝ 2 (fun θ : ℝ => gapA f n * Real.sin (2 * θ))
      (Set.Icc 0 (Real.pi / 2)) := by fun_prop
  exact (hG.sub hsin).congr (fun θ _ => rfl)

theorem gapG_zero (n : ℕ) : gapG f n 0 = 0 := by
  simp [gapG, gapM]

theorem gapG_pi (n : ℕ) : gapG f n (Real.pi / 2) = 0 := by
  have hcl := gapC_mul_pi n
  have h1 : gapDelta n + gapC n * (Real.pi / 2) = Real.pi / 2 - gapDelta n := by linarith
  have h2 : gapM f n (Real.pi / 2) = f (Real.pi / 2 - gapDelta n) := by
    unfold gapM gapD gapDD
    rw [div_mul_cancel₀ _ (by positivity : (Real.pi / 2) ≠ 0)]
    ring
  simp only [gapG, h1, h2]
  ring

theorem gapF_zero (n : ℕ) : gapF f n 0 = 0 := by
  simp [gapF, gapG_zero]

theorem gapF_pi (n : ℕ) : gapF f n (Real.pi / 2) = 0 := by
  have h2 : Real.sin (2 * (Real.pi / 2)) = 0 := by
    rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  simp [gapF, gapG_pi, h2]

end Smooth

/-! ### The derivative of the squeezed family on the open interval -/

section Deriv

variable {f : ℝ → ℝ}

theorem deriv_gapG (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) {n : ℕ}
    (h : gapDelta n < Real.pi / 8) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (gapG f n) θ
      = gapC n * deriv f (gapDelta n + gapC n * θ) - gapD f n / (Real.pi / 2) := by
  have hx : gapDelta n + gapC n * θ ∈ Set.Ioo 0 (Real.pi / 2) :=
    gap_shift_mem_Ioo h ⟨hθ.1.le, hθ.2.le⟩
  have h2 : HasDerivAt f (deriv f (gapDelta n + gapC n * θ)) (gapDelta n + gapC n * θ) :=
    ((hf2.contDiffAt (Ioo_mem_nhds hx.1 hx.2)).differentiableAt (by norm_num)).hasDerivAt
  have h1 : HasDerivAt (fun θ : ℝ => gapDelta n + gapC n * θ) (gapC n) θ := by
    simpa using ((hasDerivAt_id θ).const_mul (gapC n)).const_add (gapDelta n)
  have h3 : HasDerivAt (fun θ : ℝ => f (gapDelta n + gapC n * θ))
      (gapC n * deriv f (gapDelta n + gapC n * θ)) θ := by
    have h3' := (h2.comp θ h1).congr_deriv (by rw [mul_comm])
    simpa [Function.comp_def] using h3'
  have h4 : HasDerivAt (gapM f n) (gapD f n / (Real.pi / 2)) θ := by
    have hmm : gapM f n
        = fun y : ℝ => f (gapDelta n) + (gapD f n / (Real.pi / 2)) * y := rfl
    rw [hmm]
    have hb : HasDerivAt (fun y : ℝ => (gapD f n / (Real.pi / 2)) * y)
        (gapD f n / (Real.pi / 2)) θ := by
      simpa using (hasDerivAt_id θ).const_mul (gapD f n / (Real.pi / 2))
    exact hb.const_add (f (gapDelta n))
  have h5 : HasDerivAt (gapG f n)
      (gapC n * deriv f (gapDelta n + gapC n * θ) - gapD f n / (Real.pi / 2)) θ := by
    have hmm : gapG f n
        = fun y : ℝ => f (gapDelta n + gapC n * y) - gapM f n y := rfl
    rw [hmm]
    exact h3.sub h4
  exact h5.deriv

theorem deriv_gapF (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) {n : ℕ}
    (h : gapDelta n < Real.pi / 8) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (gapF f n) θ = deriv (gapG f n) θ - gapA f n * (2 * Real.cos (2 * θ)) := by
  have hx : gapDelta n + gapC n * θ ∈ Set.Ioo 0 (Real.pi / 2) :=
    gap_shift_mem_Ioo h ⟨hθ.1.le, hθ.2.le⟩
  have h2 : HasDerivAt f (deriv f (gapDelta n + gapC n * θ)) (gapDelta n + gapC n * θ) :=
    ((hf2.contDiffAt (Ioo_mem_nhds hx.1 hx.2)).differentiableAt (by norm_num)).hasDerivAt
  have h1 : HasDerivAt (fun θ : ℝ => gapDelta n + gapC n * θ) (gapC n) θ := by
    simpa using ((hasDerivAt_id θ).const_mul (gapC n)).const_add (gapDelta n)
  have hG : HasDerivAt (gapG f n)
      (gapC n * deriv f (gapDelta n + gapC n * θ) - gapD f n / (Real.pi / 2)) θ := by
    have h3 : HasDerivAt (fun θ : ℝ => f (gapDelta n + gapC n * θ))
        (gapC n * deriv f (gapDelta n + gapC n * θ)) θ := by
      have h3' := (h2.comp θ h1).congr_deriv (by rw [mul_comm])
      simpa [Function.comp_def] using h3'
    have h4 : HasDerivAt (gapM f n) (gapD f n / (Real.pi / 2)) θ := by
      have hmm : gapM f n
          = fun y : ℝ => f (gapDelta n) + (gapD f n / (Real.pi / 2)) * y := rfl
      rw [hmm]
      have hb : HasDerivAt (fun y : ℝ => (gapD f n / (Real.pi / 2)) * y)
          (gapD f n / (Real.pi / 2)) θ := by
        simpa using (hasDerivAt_id θ).const_mul (gapD f n / (Real.pi / 2))
      exact hb.const_add (f (gapDelta n))
    have hmm : gapG f n
        = fun y : ℝ => f (gapDelta n + gapC n * y) - gapM f n y := rfl
    rw [hmm]
    exact h3.sub h4
  have hsin : HasDerivAt (fun θ : ℝ => gapA f n * Real.sin (2 * θ))
      (gapA f n * (2 * Real.cos (2 * θ))) θ := by
    have hinner : HasDerivAt (fun θ : ℝ => (2 : ℝ) * θ) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have hs : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (Real.cos (2 * θ) * 2) θ :=
      (Real.hasDerivAt_sin (2 * θ)).comp θ hinner
    exact (hs.const_mul (gapA f n)).congr_deriv (by ring)
  have hmain : HasDerivAt (gapF f n)
      (deriv (gapG f n) θ - gapA f n * (2 * Real.cos (2 * θ))) θ := by
    have hmm : gapF f n
        = fun y : ℝ => gapG f n y - gapA f n * Real.sin (2 * y) := rfl
    rw [hmm]
    have hG' : HasDerivAt (gapG f n) (deriv (gapG f n) θ) θ :=
      hG.differentiableAt.hasDerivAt
    exact hG'.sub hsin
  exact hmain.deriv

end Deriv

/-! ### Bounds on the squeezed family -/

section Bounds

variable {f : ℝ → ℝ}

theorem gapM_bound {M : ℝ} (hM : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |f θ| ≤ M) (hMnn : 0 ≤ M)
    (n : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) : |gapM f n θ| ≤ 3 * M := by
  have hL : (0 : ℝ) < Real.pi / 2 := by positivity
  have h1 : |f (gapDelta n)| ≤ M := hM _ (Set.mem_Icc.mpr ⟨gapDelta_nonneg n, by
    linarith [gapDelta_le_half n, Real.pi_pos]⟩)
  have h2 : |f (Real.pi / 2 - gapDelta n)| ≤ M := hM _ (Set.mem_Icc.mpr ⟨by
    linarith [gapDelta_le_half n, Real.pi_pos], by linarith [gapDelta_nonneg n]⟩)
  have h3 : |gapD f n| ≤ 2 * M := by
    have hgd : gapD f n = f (Real.pi / 2 - gapDelta n) - f (gapDelta n) := rfl
    rw [hgd]
    calc |f (Real.pi / 2 - gapDelta n) - f (gapDelta n)|
        ≤ |f (Real.pi / 2 - gapDelta n)| + |f (gapDelta n)| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  have h4 : |gapD f n / (Real.pi / 2) * θ| ≤ 2 * M := by
    rw [abs_mul, abs_div, abs_of_pos hL]
    have hθ' : |θ| ≤ Real.pi / 2 := by
      rw [abs_of_nonneg hθ.1]; exact hθ.2
    have h5 : |gapD f n| / (Real.pi / 2) * |θ| ≤ (2 * M) / (Real.pi / 2) * (Real.pi / 2) :=
      mul_le_mul (div_le_div_of_nonneg_right h3 hL.le) hθ' (abs_nonneg _) (by positivity)
    calc |gapD f n| / (Real.pi / 2) * |θ| ≤ (2 * M) / (Real.pi / 2) * (Real.pi / 2) := h5
      _ = 2 * M := by field_simp
  have hmain : |gapM f n θ| ≤ |f (gapDelta n)| + |gapD f n / (Real.pi / 2) * θ| := by
    unfold gapM
    exact abs_add_le _ _
  linarith

theorem gapG_bound {M : ℝ} (hM : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |f θ| ≤ M) (hMnn : 0 ≤ M)
    (n : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) : |gapG f n θ| ≤ 4 * M := by
  have h1 : |f (gapDelta n + gapC n * θ)| ≤ M := hM _ (gap_shift_mem_Icc n hθ)
  have h2 := gapM_bound hM hMnn n hθ
  have hgg : gapG f n θ = f (gapDelta n + gapC n * θ) - gapM f n θ := rfl
  rw [hgg]
  calc |f (gapDelta n + gapC n * θ) - gapM f n θ|
      ≤ |f (gapDelta n + gapC n * θ)| + |gapM f n θ| := abs_sub _ _
    _ ≤ 4 * M := by linarith

theorem gapG_sub_f_bound {M : ℝ} (hM : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |f θ| ≤ M)
    (hMnn : 0 ≤ M) (n : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    |gapG f n θ - f θ| ≤ 5 * M := by
  have h1 := gapG_bound hM hMnn n hθ
  have h2 : |f θ| ≤ M := hM θ hθ
  calc |gapG f n θ - f θ| ≤ |gapG f n θ| + |f θ| := abs_sub _ _
    _ ≤ 5 * M := by linarith


end Bounds

/-! ### Continuity and integrability of the squeezed family -/

section ContInt

variable {f : ℝ → ℝ}

theorem continuousOn_gapG (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2))) (n : ℕ) :
    ContinuousOn (gapG f n) (Set.Icc 0 (Real.pi / 2)) := by
  have hshift : Continuous (fun θ : ℝ => gapDelta n + gapC n * θ) := by fun_prop
  have h1 : ContinuousOn ((f) ∘ fun θ : ℝ => gapDelta n + gapC n * θ)
      (Set.Icc 0 (Real.pi / 2)) :=
    ContinuousOn.comp hcont hshift.continuousOn (fun θ hθ => gap_shift_mem_Icc n hθ)
  have h1' : ContinuousOn (fun θ : ℝ => f (gapDelta n + gapC n * θ))
      (Set.Icc 0 (Real.pi / 2)) := by
    simpa only [Function.comp_def] using h1
  have h2 : ContinuousOn (gapM f n) (Set.Icc 0 (Real.pi / 2)) := by
    unfold gapM; fun_prop
  have h3 := h1'.sub h2
  have hgg : gapG f n = fun θ : ℝ => f (gapDelta n + gapC n * θ) - gapM f n θ := rfl
  rw [hgg]
  exact h3

theorem continuousOn_gapF (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2))) (n : ℕ) :
    ContinuousOn (gapF f n) (Set.Icc 0 (Real.pi / 2)) := by
  have h1 := continuousOn_gapG hcont n
  have h2 : ContinuousOn (fun θ : ℝ => gapA f n * Real.sin (2 * θ))
      (Set.Icc 0 (Real.pi / 2)) := by fun_prop
  have h3 := h1.sub h2
  have hgg : gapF f n = fun θ : ℝ => gapG f n θ - gapA f n * Real.sin (2 * θ) := rfl
  rw [hgg]
  exact h3

theorem continuousOn_deriv_comp (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) {n : ℕ}
    (h : gapDelta n < Real.pi / 8) :
    ContinuousOn (fun θ : ℝ => deriv f (gapDelta n + gapC n * θ)) (Set.Icc 0 (Real.pi / 2)) := by
  have hderiv : ContinuousOn (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
    hf2.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hshift : Continuous (fun θ : ℝ => gapDelta n + gapC n * θ) := by fun_prop
  have h1 : ContinuousOn ((deriv f) ∘ fun θ : ℝ => gapDelta n + gapC n * θ)
      (Set.Icc 0 (Real.pi / 2)) :=
    ContinuousOn.comp hderiv hshift.continuousOn (fun θ hθ => gap_shift_mem_Ioo h hθ)
  simpa only [Function.comp_def] using h1

theorem integrableOn_deriv_comp_sq (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) {n : ℕ}
    (h : gapDelta n < Real.pi / 8) :
    IntegrableOn (fun θ : ℝ => (deriv f (gapDelta n + gapC n * θ)) ^ 2) Work.Spaces.Iθ :=
  Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn ((continuousOn_deriv_comp hf2 h).pow 2)

theorem integrableOn_deriv_comp (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) {n : ℕ}
    (h : gapDelta n < Real.pi / 8) :
    IntegrableOn (fun θ : ℝ => deriv f (gapDelta n + gapC n * θ)) Work.Spaces.Iθ := by
  have hsq := integrableOn_deriv_comp_sq hf2 h
  have hmaj : IntegrableOn
      (fun θ : ℝ => (1 / 2) * ((deriv f (gapDelta n + gapC n * θ)) ^ 2 + 1))
      Work.Spaces.Iθ := by
    have h1 : IntegrableOn
        (fun θ : ℝ => (deriv f (gapDelta n + gapC n * θ)) ^ 2 + 1) Work.Spaces.Iθ :=
      hsq.add (Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn continuousOn_const)
    exact h1.const_mul (1 / 2)
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · exact (continuousOn_deriv_comp hf2 h).aestronglyMeasurable measurableSet_Icc
  · refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => ?_)
    rw [Real.norm_eq_abs]
    have hsq_abs : |deriv f (gapDelta n + gapC n * θ)| ^ 2
        = deriv f (gapDelta n + gapC n * θ) ^ 2 := sq_abs _
    have hnn := sq_nonneg (|deriv f (gapDelta n + gapC n * θ)| - 1)
    nlinarith [abs_nonneg (deriv f (gapDelta n + gapC n * θ))]

theorem integrableOn_An_sq (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) {n : ℕ}
    (h : gapDelta n < Real.pi / 8) :
    IntegrableOn
      (fun θ : ℝ => (gapC n * deriv f (gapDelta n + gapC n * θ) - gapD f n / (Real.pi / 2)) ^ 2)
      Work.Spaces.Iθ := by
  have hx := integrableOn_deriv_comp hf2 h
  have hx2 := integrableOn_deriv_comp_sq hf2 h
  have h1 : IntegrableOn
      (fun θ : ℝ => gapC n ^ 2 * (deriv f (gapDelta n + gapC n * θ)) ^ 2
        - (2 * gapC n * (gapD f n / (Real.pi / 2))) * deriv f (gapDelta n + gapC n * θ)
        + (gapD f n / (Real.pi / 2)) ^ 2) Work.Spaces.Iθ :=
    ((hx2.const_mul (gapC n ^ 2)).sub (hx.const_mul (2 * gapC n * (gapD f n / (Real.pi / 2))))).add
      (Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn continuousOn_const)
  refine h1.congr_fun (fun θ _ => ?_) measurableSet_Icc
  ring

end ContInt

/-! ### The dilation identity -/

section Dilation

variable {f : ℝ → ℝ}

theorem gap_integral_An_eq (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) {n : ℕ}
    (h : gapDelta n < Real.pi / 8) :
    (∫ θ in Work.Spaces.Iθ,
        (gapC n * deriv f (gapDelta n + gapC n * θ) - gapD f n / (Real.pi / 2)) ^ 2)
      = gapC n * (∫ u in (gapDelta n)..(Real.pi / 2 - gapDelta n), (deriv f u) ^ 2)
        - (gapD f n) ^ 2 / (Real.pi / 2) := by
  set L : ℝ := Real.pi / 2 with hL
  set δ : ℝ := gapDelta n with hδ
  set c : ℝ := gapC n with hc
  set Δ : ℝ := gapD f n with hΔ
  have hLpos : 0 < L := by rw [hL]; positivity
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hδpos : 0 < δ := by rw [hδ]; exact gapDelta_pos n
  have hδ4 : δ < L / 4 := by rw [hδ, hL]; linarith [h]
  have hclt : δ < L - δ := by linarith
  have hcne : c ≠ 0 := by
    have := gapC_pos h
    rw [hc]
    exact ne_of_gt this
  have hcL : c * L = L - 2 * δ := by
    rw [hc, hL, hδ]
    exact gapC_mul_pi n
  have hb : δ + c * L = L - δ := by linarith
  -- substitution
  have key : (∫ x in (0 : ℝ)..L, (fun u => (c * deriv f u - Δ / L) ^ 2) (δ + c * x))
      = c⁻¹ * ∫ x in δ..(L - δ), (c * deriv f x - Δ / L) ^ 2 := by
    rw [intervalIntegral.integral_comp_add_mul (fun u => (c * deriv f u - Δ / L) ^ 2) hcne δ]
    simp only [smul_eq_mul]
    rw [show δ + c * 0 = δ by ring, hb]
  have hlink : (∫ θ in Work.Spaces.Iθ,
        (c * deriv f (δ + c * θ) - Δ / L) ^ 2)
      = ∫ x in (0 : ℝ)..L, (fun u => (c * deriv f u - Δ / L) ^ 2) (δ + c * x) := by
    rw [Work.FTS.EllipticEst.P9.Iθ_eq_interval]
  -- the derivative is continuous on the compact subinterval
  have hderiv : ContinuousOn (deriv f) (Set.Ioo 0 L) := by
    rw [hL]
    exact hf2.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hdc : ContinuousOn (deriv f) (Set.uIcc δ (L - δ)) := by
    refine hderiv.mono ?_
    intro x hx
    rw [Set.uIcc_of_le hclt.le, Set.mem_Icc] at hx
    exact ⟨by linarith [hx.1, hδpos], by linarith [hx.2, hδ4, hLpos]⟩
  have hi1 : IntervalIntegrable (fun x : ℝ => (deriv f x) ^ 2) volume δ (L - δ) :=
    (hdc.pow 2).intervalIntegrable
  have hi2 : IntervalIntegrable (fun x : ℝ => deriv f x) volume δ (L - δ) :=
    hdc.intervalIntegrable
  have hiA : IntervalIntegrable
      (fun x : ℝ => c ^ 2 * (deriv f x) ^ 2 - 2 * c * (Δ / L) * deriv f x) volume δ (L - δ) :=
    (hi1.const_mul (c ^ 2)).sub (hi2.const_mul (2 * c * (Δ / L)))
  have hiB : IntervalIntegrable (fun x : ℝ => (Δ / L) ^ 2) volume δ (L - δ) :=
    intervalIntegrable_const
  have hcongr : (∫ x in δ..(L - δ), (c * deriv f x - Δ / L) ^ 2)
      = ∫ x in δ..(L - δ),
          (c ^ 2 * (deriv f x) ^ 2 - 2 * c * (Δ / L) * deriv f x + (Δ / L) ^ 2) :=
    intervalIntegral.integral_congr (fun x _ => by ring)
  have hsplit1 : (∫ x in δ..(L - δ),
          (c ^ 2 * (deriv f x) ^ 2 - 2 * c * (Δ / L) * deriv f x + (Δ / L) ^ 2))
      = (∫ x in δ..(L - δ), (c ^ 2 * (deriv f x) ^ 2 - 2 * c * (Δ / L) * deriv f x))
        + (∫ x in δ..(L - δ), ((Δ / L) ^ 2)) :=
    intervalIntegral.integral_add hiA hiB
  have hsplit2 : (∫ x in δ..(L - δ), (c ^ 2 * (deriv f x) ^ 2 - 2 * c * (Δ / L) * deriv f x))
      = (∫ x in δ..(L - δ), c ^ 2 * (deriv f x) ^ 2)
        - (∫ x in δ..(L - δ), 2 * c * (Δ / L) * deriv f x) :=
    intervalIntegral.integral_sub (hi1.const_mul (c ^ 2)) (hi2.const_mul (2 * c * (Δ / L)))
  have hsplit3 : (∫ x in δ..(L - δ), c ^ 2 * (deriv f x) ^ 2)
      = c ^ 2 * (∫ x in δ..(L - δ), (deriv f x) ^ 2) :=
    intervalIntegral.integral_const_mul (c ^ 2) _
  have hsplit4 : (∫ x in δ..(L - δ), 2 * c * (Δ / L) * deriv f x)
      = (2 * c * (Δ / L)) * (∫ x in δ..(L - δ), deriv f x) :=
    intervalIntegral.integral_const_mul (2 * c * (Δ / L)) _
  have hsplit5 : (∫ x in δ..(L - δ), ((Δ / L) ^ 2)) = (L - δ - δ) * ((Δ / L) ^ 2) := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
  have hftc : (∫ x in δ..(L - δ), deriv f x) = Δ := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := f) (f' := deriv f) ?_ hi2]
    · rw [hΔ]
      rfl
    · intro x hx
      rw [Set.uIcc_of_le hclt.le, Set.mem_Icc] at hx
      have hx' : x ∈ Set.Ioo 0 L := ⟨by linarith [hx.1, hδpos], by linarith [hx.2, hδ4, hLpos]⟩
      exact ((hf2.contDiffAt (by rw [hL]; exact Ioo_mem_nhds hx'.1 hx'.2)).differentiableAt
        (by norm_num)).hasDerivAt
  rw [hlink, key, hcongr, hsplit1, hsplit2, hsplit3, hsplit4, hsplit5, hftc]
  rw [show L - δ - δ = c * L by linarith]
  field_simp
  ring

theorem gap_integral_An_le (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2) Work.Spaces.Iθ) {n : ℕ}
    (h : gapDelta n < Real.pi / 8) :
    (∫ θ in Work.Spaces.Iθ,
        (gapC n * deriv f (gapDelta n + gapC n * θ) - gapD f n / (Real.pi / 2)) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 := by
  rw [gap_integral_An_eq hf2 h]
  set L : ℝ := Real.pi / 2 with hL
  set δ : ℝ := gapDelta n with hδ
  set c : ℝ := gapC n with hc
  set I : ℝ := ∫ x in δ..(L - δ), (deriv f x) ^ 2 with hI
  have hLpos : 0 < L := by rw [hL]; positivity
  have hδ4 : δ < L / 4 := by rw [hδ, hL]; linarith [h]
  have hδpos : 0 < δ := by rw [hδ]; exact gapDelta_pos n
  have hclt : δ < L - δ := by linarith
  have hc0 : 0 ≤ c := by rw [hc]; exact gapC_nonneg n
  have hc1 : c ≤ 1 := by rw [hc]; exact gapC_le_one n
  have hInn : 0 ≤ I := by rw [hI]; exact intervalIntegral.integral_nonneg hclt.le (fun x _ => sq_nonneg _)
  have hle1 : I ≤ ∫ x in Work.Spaces.Iθ, (deriv f x) ^ 2 := by
    rw [hI, intervalIntegral.integral_of_le hclt.le,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
    · exact ae_restrict_of_forall_mem measurableSet_Icc (fun x _ => sq_nonneg _)
    · refine Filter.Eventually.of_forall (fun x hx => ?_)
      have hx' : δ ≤ x ∧ x ≤ L - δ := hx
      obtain ⟨hx1, hx2⟩ := hx'
      change x ∈ Set.Icc (0 : ℝ) (Real.pi / 2)
      rw [Set.mem_Icc]
      exact ⟨by linarith, by linarith [hL]⟩
  have hb1 : c * I ≤ I := by
    have := mul_le_mul_of_nonneg_right hc1 hInn
    simpa using this
  have hb2 : c * I - (gapD f n) ^ 2 / L ≤ c * I := by
    have : 0 ≤ (gapD f n) ^ 2 / L := div_nonneg (sq_nonneg _) hLpos.le
    linarith
  linarith

end Dilation

/-! ### The `L¹` limit of the squeezed family -/

section Limits

variable {f : ℝ → ℝ}

theorem tendsto_gapC_tendsto_one : Tendsto gapC atTop (𝓝 1) := by
  have h2 : Tendsto (fun n : ℕ => 2 * gapDelta n / (Real.pi / 2)) atTop (𝓝 0) := by
    have := (tendsto_gapDelta.const_mul 2).div_const (Real.pi / 2)
    simpa using this
  have h3 : Tendsto (fun n : ℕ => 1 - 2 * gapDelta n / (Real.pi / 2)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub h2
  have hgc : gapC = fun n : ℕ => 1 - 2 * gapDelta n / (Real.pi / 2) := rfl
  rw [hgc]
  simpa using h3

theorem tendsto_gapDelta_right :
    Tendsto (fun n : ℕ => Real.pi / 2 - gapDelta n) atTop (𝓝 (Real.pi / 2)) := by
  have h := (tendsto_const_nhds (x := Real.pi / 2) (f := atTop (α := ℕ))).sub tendsto_gapDelta
  simpa using h

theorem tendsto_f_gapDelta_left (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2))) :
    Tendsto (fun n : ℕ => f (gapDelta n)) atTop (𝓝 (f 0)) := by
  have hmem : ∀ᶠ n in atTop, gapDelta n ∈ Set.Icc 0 (Real.pi / 2) :=
    Filter.Eventually.of_forall (fun n => Set.mem_Icc.mpr ⟨gapDelta_nonneg n, by
      linarith [gapDelta_le_half n, Real.pi_pos]⟩)
  have ht : Tendsto gapDelta atTop (𝓝[Set.Icc 0 (Real.pi / 2)] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_gapDelta, hmem⟩
  have hcw : Tendsto f (𝓝[Set.Icc 0 (Real.pi / 2)] 0) (𝓝 (f 0)) :=
    hcont.continuousWithinAt (Set.left_mem_Icc.mpr (by positivity))
  simpa only [Function.comp_def] using hcw.comp ht

theorem tendsto_f_gapDelta_right (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2))) :
    Tendsto (fun n : ℕ => f (Real.pi / 2 - gapDelta n)) atTop (𝓝 (f (Real.pi / 2))) := by
  have hmem : ∀ᶠ n in atTop, Real.pi / 2 - gapDelta n ∈ Set.Icc 0 (Real.pi / 2) :=
    Filter.Eventually.of_forall (fun n => Set.mem_Icc.mpr ⟨by
      linarith [gapDelta_le_half n, Real.pi_pos], by linarith [gapDelta_nonneg n]⟩)
  have ht : Tendsto (fun n : ℕ => Real.pi / 2 - gapDelta n) atTop
      (𝓝[Set.Icc 0 (Real.pi / 2)] (Real.pi / 2)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_gapDelta_right, hmem⟩
  have hcw : Tendsto f (𝓝[Set.Icc 0 (Real.pi / 2)] (Real.pi / 2)) (𝓝 (f (Real.pi / 2))) :=
    hcont.continuousWithinAt (Set.right_mem_Icc.mpr (by positivity))
  simpa only [Function.comp_def] using hcw.comp ht

theorem tendsto_gapG_sub (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2))) (h0 : f 0 = 0)
    (hπ : f (Real.pi / 2) = 0) :
    Tendsto (fun n : ℕ => ∫ θ in Work.Spaces.Iθ, |gapG f n θ - f θ|) atTop (𝓝 0) := by
  obtain ⟨M₀, hM₀⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont
  set M : ℝ := max M₀ 0 with hM
  have hMnn : 0 ≤ M := le_max_right _ _
  have hMb : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |f θ| ≤ M := by
    intro θ hθ
    have h := hM₀ θ hθ
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  have hleft := tendsto_f_gapDelta_left hcont
  have hright := tendsto_f_gapDelta_right hcont
  have hD : Tendsto (fun n : ℕ => gapD f n) atTop (𝓝 0) := by
    have h3 := hright.sub hleft
    have h3' : Tendsto (fun n : ℕ => gapD f n) atTop (𝓝 (f (Real.pi / 2) - f 0)) := by
      have hfun : (fun n : ℕ => gapD f n)
          = fun n : ℕ => f (Real.pi / 2 - gapDelta n) - f (gapDelta n) := rfl
      rw [hfun]
      exact h3
    simpa [h0, hπ] using h3' 
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun θ : ℝ => |gapG f n θ - f θ|)
      (volume.restrict Work.Spaces.Iθ) := fun n =>
    ((continuousOn_gapG hcont n).sub hcont).abs.aestronglyMeasurable measurableSet_Icc
  have hintb : Integrable (fun _ : ℝ => 5 * M) (volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn continuousOn_const
  have hbnd : ∀ n : ℕ, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖|gapG f n θ - f θ|‖ ≤ 5 * M := by
    intro n
    refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact gapG_sub_f_bound hMb hMnn n hθ
  have hlim : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Tendsto (fun n : ℕ => |gapG f n θ - f θ|) atTop (𝓝 0) := by
    refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    rcases eq_or_lt_of_le hθ.1 with hzero | hpos
    · have : (fun n : ℕ => |gapG f n θ - f θ|) = fun _ => (0 : ℝ) := by
        funext n
        rw [← hzero, gapG_zero n, h0, sub_zero, abs_zero]
      rw [this]
      exact tendsto_const_nhds
    rcases eq_or_lt_of_le hθ.2 with hpi | hlt
    · have : (fun n : ℕ => |gapG f n θ - f θ|) = fun _ => (0 : ℝ) := by
        funext n
        rw [hpi, gapG_pi n, hπ, sub_zero, abs_zero]
      rw [this]
      exact tendsto_const_nhds
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hpos, hlt⟩
    have harg : Tendsto (fun n : ℕ => gapDelta n + gapC n * θ) atTop (𝓝 θ) := by
      have := tendsto_gapDelta.add (tendsto_gapC_tendsto_one.mul_const θ)
      simpa using this
    have hcf : Tendsto (fun n : ℕ => f (gapDelta n + gapC n * θ)) atTop (𝓝 (f θ)) :=
      (hcont.continuousAt (Icc_mem_nhds hθ'.1 hθ'.2)).tendsto.comp harg
    have hgM : Tendsto (fun n : ℕ => gapM f n θ) atTop (𝓝 0) := by
      have h4 : Tendsto (fun n : ℕ => f (gapDelta n) + (gapD f n / (Real.pi / 2)) * θ)
          atTop (𝓝 (0 + 0 * θ)) := by
        have h4' := hleft.add ((hD.div_const (Real.pi / 2)).mul_const θ)
        simpa [h0] using h4' 
      have hgm : (fun n : ℕ => gapM f n θ)
          = fun n : ℕ => f (gapDelta n) + (gapD f n / (Real.pi / 2)) * θ := by
        funext n; rw [gapM]
      rw [hgm]
      simpa [h0] using h4
    have h5 : Tendsto (fun n : ℕ => f (gapDelta n + gapC n * θ) - f θ) atTop (𝓝 0) := by
      have h5' := hcf.sub (tendsto_const_nhds (x := f θ) (f := atTop (α := ℕ)))
      simpa using h5' 
    have h6 := h5.sub hgM
    have h7 : Tendsto (fun n : ℕ => gapG f n θ - f θ) atTop (𝓝 0) := by
      have hgg : (fun n : ℕ => gapG f n θ - f θ)
          = fun n : ℕ => (f (gapDelta n + gapC n * θ) - f θ) - gapM f n θ := by
        funext n; rw [gapG]; ring
      rw [hgg]
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h6
    simpa using h7.abs
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict Work.Spaces.Iθ)
    (F := fun n θ => |gapG f n θ - f θ|) (f := fun _ : ℝ => (0 : ℝ))
    (fun _ => 5 * M) hmeas hintb hbnd hlim
  simpa using hmain

end Limits

/-! ### The per-`n` bounds -/

section Bounds2

variable {f : ℝ → ℝ}

/-- `|a_n|` is controlled by the `L¹` distance of `g_n` from `f`. -/
theorem gapA_abs_le (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2)))
    (horth : (∫ θ in Work.Spaces.Iθ, f θ * Work.Elliptic.sinCos2 θ) = 0) (n : ℕ) :
    |gapA f n| ≤ (15 / 4) * (∫ θ in Work.Spaces.Iθ, |gapG f n θ - f θ|) := by
  have hψ1 : ContinuousOn (fun θ : ℝ => gapG f n θ * Work.Elliptic.sinCos2 θ)
      (Set.Icc 0 (Real.pi / 2)) :=
    (continuousOn_gapG hcont n).mul Work.FTS.EllipticEst.P9.continuous_sinCos2.continuousOn
  have hψ2 : ContinuousOn (fun θ : ℝ => f θ * Work.Elliptic.sinCos2 θ)
      (Set.Icc 0 (Real.pi / 2)) :=
    hcont.mul Work.FTS.EllipticEst.P9.continuous_sinCos2.continuousOn
  have hψ3 : ContinuousOn (fun θ : ℝ => (gapG f n θ - f θ) * Work.Elliptic.sinCos2 θ)
      (Set.Icc 0 (Real.pi / 2)) :=
    ((continuousOn_gapG hcont n).sub hcont).mul
      Work.FTS.EllipticEst.P9.continuous_sinCos2.continuousOn
  have hInt1 : IntegrableOn (fun θ : ℝ => gapG f n θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn hψ1
  have hInt2 : IntegrableOn (fun θ : ℝ => f θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn hψ2
  have hInt3 : IntegrableOn (fun θ : ℝ => (gapG f n θ - f θ) * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn hψ3
  have hsplit : (∫ θ in Work.Spaces.Iθ, gapG f n θ * Work.Elliptic.sinCos2 θ)
      = (∫ θ in Work.Spaces.Iθ, (gapG f n θ - f θ) * Work.Elliptic.sinCos2 θ)
        + (∫ θ in Work.Spaces.Iθ, f θ * Work.Elliptic.sinCos2 θ) := by
    rw [← MeasureTheory.integral_add hInt3 hInt2]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    ring
  have hbound : |∫ θ in Work.Spaces.Iθ, (gapG f n θ - f θ) * Work.Elliptic.sinCos2 θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |gapG f n θ - f θ| := by
    have hInt4 : IntegrableOn
        (fun θ : ℝ => |(gapG f n θ - f θ) * Work.Elliptic.sinCos2 θ|) Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn hψ3.abs
    have hInt5 : IntegrableOn (fun θ : ℝ => |gapG f n θ - f θ|) Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn
        ((continuousOn_gapG hcont n).sub hcont).abs
    have hnm : |∫ θ in Work.Spaces.Iθ, (gapG f n θ - f θ) * Work.Elliptic.sinCos2 θ|
        ≤ ∫ θ in Work.Spaces.Iθ, |(gapG f n θ - f θ) * Work.Elliptic.sinCos2 θ| := by
      simpa only [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Work.Spaces.Iθ)
          (f := fun θ : ℝ => (gapG f n θ - f θ) * Work.Elliptic.sinCos2 θ))
    refine le_trans hnm ?_
    refine MeasureTheory.integral_mono_ae hInt4 hInt5 ?_
    refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => ?_)
    change |(gapG f n θ - f θ) * Work.Elliptic.sinCos2 θ| ≤ |gapG f n θ - f θ|
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _)
      (Work.FTS.EllipticEst.P9.abs_sinCos2_le_one θ)
  have h2 : |gapA f n| = (15 / 4) * |∫ θ in Work.Spaces.Iθ,
      (gapG f n θ - f θ) * Work.Elliptic.sinCos2 θ| := by
    unfold gapA
    rw [hsplit, horth, add_zero, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 15 / 4)]
  rw [h2]
  exact mul_le_mul_of_nonneg_left hbound (by norm_num)


end Bounds2

section Final

variable {f : ℝ → ℝ}

/-- The elementary pointwise bound for the corrected squeeze's derivative. -/
theorem gapF_pointwise (A : ℝ → ℝ) (a θ : ℝ) :
    (A θ - a * (2 * Real.cos (2 * θ))) ^ 2 ≤ (A θ) ^ 2 + 4 * |a| * |A θ| + 4 * a ^ 2 := by
  have hb : |2 * Real.cos (2 * θ)| ≤ 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [Real.abs_cos_le_one (2 * θ)]
  have hab : |a| * |2 * Real.cos (2 * θ)| ≤ 2 * |a| := by
    have h := mul_le_mul_of_nonneg_left hb (abs_nonneg a)
    rw [mul_comm 2 |a|]
    exact h
  have hkey : |A θ - a * (2 * Real.cos (2 * θ))| ≤ |A θ| + 2 * |a| := by
    calc |A θ - a * (2 * Real.cos (2 * θ))|
        ≤ |A θ| + |a * (2 * Real.cos (2 * θ))| := abs_sub _ _
      _ = |A θ| + |a| * |2 * Real.cos (2 * θ)| := by rw [abs_mul]
      _ ≤ |A θ| + 2 * |a| := by linarith [hab]
  have hleft : |A θ - a * (2 * Real.cos (2 * θ))| ^ 2 ≤ (|A θ| + 2 * |a|) ^ 2 := by
    refine sq_le_sq' ?_ hkey
    linarith [abs_nonneg (A θ - a * (2 * Real.cos (2 * θ)))]
  have hexp : (|A θ| + 2 * |a|) ^ 2 = (A θ) ^ 2 + 4 * |a| * |A θ| + 4 * a ^ 2 := by
    have h1 : |A θ| ^ 2 = (A θ) ^ 2 := sq_abs (A θ)
    have h2 : |a| ^ 2 = a ^ 2 := sq_abs a
    nlinarith [h1, h2]
  have hgoal : (A θ - a * (2 * Real.cos (2 * θ))) ^ 2 ≤ (|A θ| + 2 * |a|) ^ 2 := by
    rw [← sq_abs (A θ - a * (2 * Real.cos (2 * θ)))]
    exact hleft
  linarith [hgoal, hexp.le, hexp.ge]

/-- `f` is close to its squeeze in `L¹`. -/
theorem gapG_sq_ge (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2)))
    {M : ℝ} (hM : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |f θ| ≤ M) (hMnn : 0 ≤ M) (n : ℕ) :
    (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2)
        - 8 * M * (∫ θ in Work.Spaces.Iθ, |gapG f n θ - f θ|)
      ≤ ∫ θ in Work.Spaces.Iθ, (gapG f n θ) ^ 2 := by
  have hIntG : IntegrableOn (fun θ : ℝ => (gapG f n θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn ((continuousOn_gapG hcont n).pow 2)
  have hIntF : IntegrableOn (fun θ : ℝ => (f θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn (hcont.pow 2)
  have hIntE : IntegrableOn (fun θ : ℝ => |gapG f n θ - f θ|) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn
      ((continuousOn_gapG hcont n).sub hcont).abs
  have hIntD : IntegrableOn (fun θ : ℝ => (gapG f n θ) ^ 2 - (f θ) ^ 2) Work.Spaces.Iθ :=
    hIntG.sub hIntF
  have hdiff : (∫ θ in Work.Spaces.Iθ, (gapG f n θ) ^ 2) - (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, ((gapG f n θ) ^ 2 - (f θ) ^ 2) :=
    (MeasureTheory.integral_sub hIntG hIntF).symm
  have hbound : |∫ θ in Work.Spaces.Iθ, ((gapG f n θ) ^ 2 - (f θ) ^ 2)|
      ≤ 8 * M * (∫ θ in Work.Spaces.Iθ, |gapG f n θ - f θ|) := by
    have hnm : |∫ θ in Work.Spaces.Iθ, ((gapG f n θ) ^ 2 - (f θ) ^ 2)|
        ≤ ∫ θ in Work.Spaces.Iθ, |(gapG f n θ) ^ 2 - (f θ) ^ 2| := by
      simpa only [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Work.Spaces.Iθ)
          (f := fun θ : ℝ => (gapG f n θ) ^ 2 - (f θ) ^ 2))
    refine le_trans hnm ?_
    have hpt : ∀ θ ∈ Work.Spaces.Iθ,
        |(gapG f n θ) ^ 2 - (f θ) ^ 2| ≤ 8 * M * |gapG f n θ - f θ| := by
      intro θ hθ
      have h1 : |gapG f n θ| ≤ 4 * M := gapG_bound hM hMnn n hθ
      have h2 : |f θ| ≤ M := hM θ hθ
      have h3 : |gapG f n θ + f θ| ≤ 8 * M := by
        calc |gapG f n θ + f θ| ≤ |gapG f n θ| + |f θ| := abs_add_le _ _
          _ ≤ 8 * M := by linarith
      rw [show (gapG f n θ) ^ 2 - (f θ) ^ 2
          = (gapG f n θ - f θ) * (gapG f n θ + f θ) from by ring, abs_mul]
      calc |gapG f n θ - f θ| * |gapG f n θ + f θ|
          ≤ |gapG f n θ - f θ| * (8 * M) := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
        _ = 8 * M * |gapG f n θ - f θ| := by ring
    have hIntBig : IntegrableOn (fun θ : ℝ => 8 * M * |gapG f n θ - f θ|) Work.Spaces.Iθ :=
      hIntE.const_mul (8 * M)
    have hIntAbs : IntegrableOn (fun θ : ℝ => |(gapG f n θ) ^ 2 - (f θ) ^ 2|) Work.Spaces.Iθ :=
      hIntD.abs
    have h4 := MeasureTheory.integral_mono_ae hIntAbs hIntBig
      (ae_restrict_of_forall_mem measurableSet_Icc hpt)
    rwa [MeasureTheory.integral_const_mul] at h4
  have h1 : -(8 * M * (∫ θ in Work.Spaces.Iθ, |gapG f n θ - f θ|))
      ≤ (∫ θ in Work.Spaces.Iθ, (gapG f n θ) ^ 2) - (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2) := by
    rw [hdiff]
    linarith [neg_abs_le (∫ θ in Work.Spaces.Iθ, ((gapG f n θ) ^ 2 - (f θ) ^ 2)), hbound]
  linarith

/-- The correction `a_n sin 2θ` costs at most `8M|a_n|` pointwise. -/
theorem gapF_sq_ge (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2)))
    {M : ℝ} (hM : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |f θ| ≤ M) (hMnn : 0 ≤ M) (n : ℕ) :
    (∫ θ in Work.Spaces.Iθ, (gapG f n θ) ^ 2)
        - 8 * M * |gapA f n| * (Real.pi / 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (gapF f n θ) ^ 2 := by
  have hIntG : IntegrableOn (fun θ : ℝ => (gapG f n θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn ((continuousOn_gapG hcont n).pow 2)
  have hIntF : IntegrableOn (fun θ : ℝ => (gapF f n θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn ((continuousOn_gapF hcont n).pow 2)
  have hIntA : IntegrableOn (fun θ : ℝ => (gapG f n θ) ^ 2 - 8 * M * |gapA f n|)
      Work.Spaces.Iθ :=
    hIntG.sub (Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn continuousOn_const)
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      (gapG f n θ) ^ 2 - 8 * M * |gapA f n| ≤ (gapF f n θ) ^ 2 := by
    intro θ hθ
    have h1 : |gapG f n θ| ≤ 4 * M := gapG_bound hM hMnn n hθ
    have hs : |Real.sin (2 * θ)| ≤ 1 := by
      rw [abs_le]
      exact ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    have h2 : |gapG f n θ| * |Real.sin (2 * θ)| ≤ 4 * M := by
      have h3 : |gapG f n θ| * |Real.sin (2 * θ)| ≤ (4 * M) * 1 :=
        mul_le_mul h1 hs (abs_nonneg _) (by linarith)
      linarith
    have hsplit_abs : |2 * (gapG f n θ) * (gapA f n * Real.sin (2 * θ))|
        = 2 * |gapG f n θ| * (|gapA f n| * |Real.sin (2 * θ)|) := by
      simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    have habs : |2 * (gapG f n θ) * (gapA f n * Real.sin (2 * θ))| ≤ 8 * M * |gapA f n| := by
      rw [hsplit_abs]
      calc 2 * |gapG f n θ| * (|gapA f n| * |Real.sin (2 * θ)|)
          = 2 * (|gapA f n| * (|gapG f n θ| * |Real.sin (2 * θ)|)) := by ring
        _ ≤ 2 * (|gapA f n| * (4 * M)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)) (by norm_num)
        _ = 8 * M * |gapA f n| := by ring
    have hle : 2 * (gapG f n θ) * (gapA f n * Real.sin (2 * θ)) ≤ 8 * M * |gapA f n| :=
      le_trans (le_abs_self _) habs
    have hsq : (gapF f n θ) ^ 2 = (gapG f n θ) ^ 2
        - 2 * (gapG f n θ) * (gapA f n * Real.sin (2 * θ))
        + (gapA f n * Real.sin (2 * θ)) ^ 2 := by
      rw [gapF]; ring
    rw [hsq]
    have h9 : 0 ≤ (gapA f n * Real.sin (2 * θ)) ^ 2 := sq_nonneg _
    linarith [hle, h9]
  have hmono := MeasureTheory.integral_mono_ae hIntA hIntF
    (ae_restrict_of_forall_mem measurableSet_Icc hpt)
  have hsplit : (∫ θ in Work.Spaces.Iθ, ((gapG f n θ) ^ 2 - 8 * M * |gapA f n|))
      = (∫ θ in Work.Spaces.Iθ, (gapG f n θ) ^ 2) - 8 * M * |gapA f n| * (Real.pi / 2) := by
    rw [MeasureTheory.integral_sub hIntG
      (Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn continuousOn_const)]
    rw [MeasureTheory.setIntegral_const, Work.FTS.EllipticEst.P9.real_volume_Iθ, smul_eq_mul]
    ring
  linarith [hmono, hsplit.ge, hsplit.le]

/-- The `L²` bound for the derivative of the corrected squeeze. -/
theorem gapF_deriv_sq_le (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2) Work.Spaces.Iθ) {n : ℕ}
    (h : gapDelta n < Real.pi / 8) :
    (∫ θ in Work.Spaces.Iθ, (deriv (gapF f n) θ) ^ 2)
      ≤ (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2)
        + 2 * |gapA f n| * ((∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2) + Real.pi / 2)
        + 2 * Real.pi * (gapA f n) ^ 2 := by
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 with hB
  set a : ℝ := gapA f n with ha
  set A : ℝ → ℝ := fun θ => gapC n * deriv f (gapDelta n + gapC n * θ)
    - gapD f n / (Real.pi / 2) with hA
  have hIntA : IntegrableOn (fun θ : ℝ => A θ) Work.Spaces.Iθ := by
    rw [hA]
    exact ((integrableOn_deriv_comp hf2 h).const_mul (gapC n)).sub
      (Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn continuousOn_const)
  have hIntAbs : IntegrableOn (fun θ : ℝ => |A θ|) Work.Spaces.Iθ := hIntA.abs
  have hIntA2 : IntegrableOn (fun θ : ℝ => (A θ) ^ 2) Work.Spaces.Iθ := by
    rw [hA]
    exact integrableOn_An_sq hf2 h
  have hIntConst : IntegrableOn (fun _ : ℝ => (4 : ℝ) * a ^ 2) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn continuousOn_const
  have hIntBig : IntegrableOn (fun θ : ℝ => (A θ) ^ 2 + 4 * |a| * |A θ| + 4 * a ^ 2)
      Work.Spaces.Iθ :=
    (hIntA2.add (hIntAbs.const_mul (4 * |a|))).add hIntConst
  have hae : (fun θ : ℝ => deriv (gapF f n) θ) =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => A θ - a * (2 * Real.cos (2 * θ))) := by
    rw [ha, hA]
    rw [← Work.FTS.EllipticEst.P9.restrict_Ioo_eq_restrict_Iθ]
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => by
      show deriv (gapF f n) θ
        = (gapC n * deriv f (gapDelta n + gapC n * θ) - gapD f n / (Real.pi / 2))
          - gapA f n * (2 * Real.cos (2 * θ))
      rw [deriv_gapF hf2 h hθ, deriv_gapG hf2 h hθ])
  have hIntDerivF : IntegrableOn (fun θ : ℝ => (deriv (gapF f n) θ) ^ 2) Work.Spaces.Iθ := by
    have hw := Work.FTS.EllipticEst.P9.integrableOn_w_sq (gapF_contDiffOn hf2 h)
    have haeeq : (fun θ : ℝ => (Work.FTS.EllipticEst.P9.w (gapF f n) θ) ^ 2)
        =ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ : ℝ => (deriv (gapF f n) θ) ^ 2) := by
      filter_upwards [Work.FTS.EllipticEst.P9.w_ae_eq_deriv (gapF f n)] with θ hθ
      rw [hθ]
    exact MeasureTheory.Integrable.congr hw haeeq
  have hIntArg : IntegrableOn (fun θ : ℝ => (A θ - a * (2 * Real.cos (2 * θ))) ^ 2)
      Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.congr hIntDerivF ?_
    filter_upwards [hae] with θ hθ
    rw [hθ]
  have h1 : (∫ θ in Work.Spaces.Iθ, (deriv (gapF f n) θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (A θ - a * (2 * Real.cos (2 * θ))) ^ 2 := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hae] with θ hθ
    rw [hθ]
  rw [h1]
  have hmono := MeasureTheory.integral_mono_ae hIntArg hIntBig
    (ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => gapF_pointwise A a θ))
  have hExpBig : (∫ θ in Work.Spaces.Iθ, ((A θ) ^ 2 + 4 * |a| * |A θ| + 4 * a ^ 2))
      = (∫ θ in Work.Spaces.Iθ, (A θ) ^ 2) + 4 * |a| * (∫ θ in Work.Spaces.Iθ, |A θ|)
        + 4 * a ^ 2 * (Real.pi / 2) := by
    have e1 : (∫ θ in Work.Spaces.Iθ, ((A θ) ^ 2 + 4 * |a| * |A θ| + 4 * a ^ 2))
        = (∫ θ in Work.Spaces.Iθ, ((A θ) ^ 2 + 4 * |a| * |A θ|))
          + (∫ θ in Work.Spaces.Iθ, ((4 : ℝ) * a ^ 2)) :=
      MeasureTheory.integral_add (f := fun θ : ℝ => (A θ) ^ 2 + 4 * |a| * |A θ|)
        (g := fun _ : ℝ => (4 : ℝ) * a ^ 2)
        (hIntA2.add (hIntAbs.const_mul (4 * |a|))) hIntConst
    have e2 : (∫ θ in Work.Spaces.Iθ, ((A θ) ^ 2 + 4 * |a| * |A θ|))
        = (∫ θ in Work.Spaces.Iθ, (A θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (4 * |a| * |A θ|)) :=
      MeasureTheory.integral_add (f := fun θ : ℝ => (A θ) ^ 2)
        (g := fun θ : ℝ => 4 * |a| * |A θ|) hIntA2 (hIntAbs.const_mul (4 * |a|))
    have e3 : (∫ θ in Work.Spaces.Iθ, (4 * |a| * |A θ|))
        = 4 * |a| * (∫ θ in Work.Spaces.Iθ, |A θ|) :=
      MeasureTheory.integral_const_mul (4 * |a|) _
    have e4 : (∫ θ in Work.Spaces.Iθ, ((4 : ℝ) * a ^ 2)) = 4 * a ^ 2 * (Real.pi / 2) := by
      rw [MeasureTheory.setIntegral_const, Work.FTS.EllipticEst.P9.real_volume_Iθ, smul_eq_mul]
      ring
    rw [e1, e2, e3, e4]
  have hA2le : (∫ θ in Work.Spaces.Iθ, (A θ) ^ 2) ≤ B := by
    rw [hA, hB]
    exact gap_integral_An_le hf2 hint h
  have hAbsle : (∫ θ in Work.Spaces.Iθ, |A θ|) ≤ (B + Real.pi / 2) / 2 := by
    have hIntMaj : IntegrableOn (fun θ : ℝ => ((A θ) ^ 2 + 1) / 2) Work.Spaces.Iθ := by
      have h2 : IntegrableOn (fun θ : ℝ => (A θ) ^ 2 + 1) Work.Spaces.Iθ :=
        hIntA2.add (Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn continuousOn_const)
      have h3 := h2.const_mul (1 / 2)
      refine MeasureTheory.IntegrableOn.congr_fun h3 (fun θ _ => ?_) measurableSet_Icc
      ring
    have h1 : (∫ θ in Work.Spaces.Iθ, |A θ|) ≤ ∫ θ in Work.Spaces.Iθ, ((A θ) ^ 2 + 1) / 2 :=
      MeasureTheory.integral_mono_ae hIntAbs hIntMaj
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => by
          have hsq_abs : |A θ| ^ 2 = (A θ) ^ 2 := sq_abs _
          have hnn := sq_nonneg (|A θ| - 1)
          nlinarith [abs_nonneg (A θ)]))
    have h2 : (∫ θ in Work.Spaces.Iθ, ((A θ) ^ 2 + 1) / 2)
        = ((∫ θ in Work.Spaces.Iθ, (A θ) ^ 2) + Real.pi / 2) / 2 := by
      have h3 : (∫ θ in Work.Spaces.Iθ, ((A θ) ^ 2 + 1) / 2)
          = ∫ θ in Work.Spaces.Iθ, (1 / 2) * ((A θ) ^ 2 + 1) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
      rw [h3, MeasureTheory.integral_const_mul]
      rw [MeasureTheory.integral_add hIntA2
        (Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn continuousOn_const)]
      rw [MeasureTheory.setIntegral_const, Work.FTS.EllipticEst.P9.real_volume_Iθ, smul_eq_mul]
      ring
    linarith
  have h3 : (∫ θ in Work.Spaces.Iθ, (A θ - a * (2 * Real.cos (2 * θ))) ^ 2)
      ≤ B + 2 * |a| * (B + Real.pi / 2) + 2 * Real.pi * a ^ 2 := by
    have hstep : 4 * |a| * (∫ θ in Work.Spaces.Iθ, |A θ|) ≤ 4 * |a| * ((B + Real.pi / 2) / 2) :=
      mul_le_mul_of_nonneg_left hAbsle (by positivity)
    have heq : B + 4 * |a| * ((B + Real.pi / 2) / 2) + 4 * a ^ 2 * (Real.pi / 2)
        = B + 2 * |a| * (B + Real.pi / 2) + 2 * Real.pi * a ^ 2 := by ring
    linarith [hmono, hExpBig.le, hExpBig.ge, hA2le, hstep, heq]
  exact h3

/-- The corrected squeeze satisfies the solvability condition. -/
theorem gapF_moment (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2)))
    (horth : (∫ θ in Work.Spaces.Iθ, f θ * Work.Elliptic.sinCos2 θ) = 0) (n : ℕ) :
    (∫ θ in Work.Spaces.Iθ, gapF f n θ * Work.Elliptic.sinCos2 θ) = 0 := by
  have hcontψ : ContinuousOn Work.Elliptic.sinCos2 (Set.Icc 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.P9.continuous_sinCos2.continuousOn
  have hcont2 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)
      (Set.Icc 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn.mul hcontψ
  have hIntG : IntegrableOn (fun θ : ℝ => gapG f n θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn
      ((continuousOn_gapG hcont n).mul hcontψ)
  have hIntC : IntegrableOn
      (fun θ : ℝ => gapA f n * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ))
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn (continuousOn_const.mul hcont2)
  have hsplit : (∫ θ in Work.Spaces.Iθ, gapF f n θ * Work.Elliptic.sinCos2 θ)
      = (∫ θ in Work.Spaces.Iθ, gapG f n θ * Work.Elliptic.sinCos2 θ)
        - gapA f n * (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) := by
    have hpt : ∀ θ : ℝ, gapF f n θ * Work.Elliptic.sinCos2 θ
        = gapG f n θ * Work.Elliptic.sinCos2 θ
          - gapA f n * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) := by
      intro θ; rw [gapF]; ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [MeasureTheory.integral_sub hIntG hIntC]
    rw [MeasureTheory.integral_const_mul]
  have h45 : (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) = 4 / 15 := by
    rw [MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc
      (fun θ _ => mul_comm _ _)]
    simpa [Work.FTS.EllipticEst.P9.s2] using Work.FTS.EllipticEst.P9.integral_sinCos2_mul_s2
  rw [hsplit, h45]
  unfold gapA
  ring

end Final

theorem Gap9Open : ∀ f : ℝ → ℝ, ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    ContinuousOn f (Set.Icc 0 (Real.pi / 2)) → f 0 = 0 → f (Real.pi / 2) = 0 →
    MeasureTheory.IntegrableOn (fun θ => (deriv f θ) ^ 2) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, f θ * Work.Elliptic.sinCos2 θ) = 0 →
    9 * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 := by
  intro f hf2 hcont h0 hπ hint horth
  obtain ⟨M₀, hM₀⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont
  set M : ℝ := max M₀ 0 with hM
  have hMnn : 0 ≤ M := le_max_right _ _
  have hMb : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |f θ| ≤ M := by
    intro θ hθ
    have h := hM₀ θ hθ
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 with hA
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 with hB
  have hBnn : 0 ≤ B := by rw [hB]; exact integral_nonneg (fun θ => sq_nonneg _)
  set En : ℕ → ℝ := fun n => ∫ θ in Work.Spaces.Iθ, |gapG f n θ - f θ| with hEn
  have hEnnn : ∀ n, 0 ≤ En n := fun n => integral_nonneg (fun θ => abs_nonneg _)
  have htendEn : Tendsto En atTop (𝓝 0) := by
    rw [hEn]
    exact tendsto_gapG_sub hcont h0 hπ
  have hAg : ∀ n, |gapA f n| ≤ (15 / 4) * En n := by
    intro n
    rw [hEn]
    exact gapA_abs_le hcont horth n
  have hstrong : ∀ᶠ n in atTop,
      9 * (∫ θ in Work.Spaces.Iθ, (gapF f n θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, (deriv (gapF f n) θ) ^ 2 := by
    filter_upwards [eventually_gapDelta_lt_eighth] with n hn
    exact Work.FTS.EllipticEst.P9.slicePoincare9_fts (gapF f n) (gapF_contDiffOn hf2 hn)
      (gapF_zero n) (gapF_pi n) (gapF_moment hcont horth n)
  set Err : ℕ → ℝ := fun n => 2 * |gapA f n| * (B + Real.pi / 2) + 2 * Real.pi * (gapA f n) ^ 2
    + 72 * M * |gapA f n| * (Real.pi / 2) + 72 * M * En n with hErr
  set Err2 : ℕ → ℝ := fun n => 2 * ((15 / 4) * En n) * (B + Real.pi / 2)
    + 2 * Real.pi * ((15 / 4) * En n) ^ 2 + 72 * M * ((15 / 4) * En n) * (Real.pi / 2)
    + 72 * M * En n with hErr2
  have hErrnn : ∀ n, 0 ≤ Err n := by
    intro n
    rw [hErr]
    have ha : 0 ≤ |gapA f n| := abs_nonneg _
    have hb : 0 ≤ (gapA f n) ^ 2 := sq_nonneg _
    have h1 : 0 ≤ 2 * |gapA f n| * (B + Real.pi / 2) :=
      mul_nonneg (mul_nonneg (by norm_num) ha) (by linarith [hBnn, Real.pi_pos])
    have h2 : 0 ≤ 2 * Real.pi * (gapA f n) ^ 2 := mul_nonneg (by positivity) hb
    have h3 : 0 ≤ 72 * M * |gapA f n| * (Real.pi / 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hMnn) ha) (by positivity)
    have h4 : 0 ≤ 72 * M * En n := mul_nonneg (mul_nonneg (by norm_num) hMnn) (hEnnn n)
    linarith
  have hErrle : ∀ n, Err n ≤ Err2 n := by
    intro n
    have h1 := hAg n
    have h3 : (gapA f n) ^ 2 ≤ ((15 / 4) * En n) ^ 2 := by
      have h5 : |gapA f n| ≤ |(15 / 4) * En n| := by
        rw [abs_of_nonneg (by linarith [hEnnn n] : (0 : ℝ) ≤ (15 / 4) * En n)]
        exact h1
      calc (gapA f n) ^ 2 = |gapA f n| ^ 2 := (sq_abs _).symm
        _ ≤ |(15 / 4) * En n| ^ 2 :=
            sq_le_sq' (by linarith [h5, abs_nonneg (gapA f n)]) h5
        _ = ((15 / 4) * En n) ^ 2 := sq_abs _
    have e1 : 2 * |gapA f n| * (B + Real.pi / 2) ≤ 2 * ((15 / 4) * En n) * (B + Real.pi / 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith [hBnn, Real.pi_pos])
    have e2 : 2 * Real.pi * (gapA f n) ^ 2 ≤ 2 * Real.pi * ((15 / 4) * En n) ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have e3 : 72 * M * |gapA f n| * (Real.pi / 2)
        ≤ 72 * M * ((15 / 4) * En n) * (Real.pi / 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith [h1]) (by linarith [hMnn])
    rw [hErr, hErr2]
    linarith
  have htend2 : Tendsto Err2 atTop (𝓝 0) := by
    set φ : ℝ → ℝ := fun x => 2 * ((15 / 4) * x) * (B + Real.pi / 2)
      + 2 * Real.pi * ((15 / 4) * x) ^ 2 + 72 * M * ((15 / 4) * x) * (Real.pi / 2) + 72 * M * x
      with hφ
    have hφc : Continuous φ := by rw [hφ]; fun_prop
    have h1 : Tendsto (fun n => φ (En n)) atTop (𝓝 (φ 0)) := hφc.continuousAt.tendsto.comp htendEn
    have hφ0 : φ 0 = 0 := by rw [hφ]; ring
    have h2 : Tendsto (fun n => φ (En n)) atTop (𝓝 0) := by simpa [hφ0] using h1
    rw [hErr2]
    simpa [hφ, Function.comp_def] using h2
  have htendErr : Tendsto Err atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds (x := (0 : ℝ)) (f := atTop (α := ℕ))) htend2 hErrnn hErrle
  have hkey : ∀ᶠ n in atTop, 9 * A - B ≤ Err n := by
    filter_upwards [hstrong, eventually_gapDelta_lt_eighth] with n hn hsmall
    have h1 := gapG_sq_ge hcont hMb hMnn n
    have h2 := gapF_sq_ge hcont hMb hMnn n
    have h3 := gapF_deriv_sq_le hf2 hint hsmall
    rw [hB, hErr, hEn]
    linarith
  have hneg : Tendsto (fun n : ℕ => -(Err n)) atTop (𝓝 0) := by
    simpa using htendErr.neg
  have hkey' : ∀ᶠ n in atTop, -(Err n) ≤ -(9 * A - B) :=
    hkey.mono (fun n hn => by linarith)
  have hfin := le_of_tendsto hneg hkey'
  rw [hA, hB]
  linarith

end
