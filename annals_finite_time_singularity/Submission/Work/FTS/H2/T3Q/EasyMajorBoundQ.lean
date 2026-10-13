import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.T1EasyBound
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.H2.WPQ.Defs
import Submission.Work.FTS.H2.Transport3Aux.easySum_bound
import Submission.Work.FTS.LocData.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.T3Q

set_option maxHeartbeats 1000000

/-! ## The interior `f`-side pointwise bounds

These are the transport of `Work.FTS.H2.Transport3Aux.abs_dzIter_le_wlInf` /
`abs_mixed_le_wlInf` from the closed-quadrant class `Spaces.SmoothNbhd` to the interior class
`Work.FTS.LocData.SmoothQuad`, replacing the input by the interior-bound lemmas
`Work.FTS.H2.WPQ.DzIter_le_WlInf` (whose hypothesis is `θ ∈ Ioo 0 (π/2)`) and
`Work.FTS.H2.WPQ.Mixed_le_WlInf` (together with the slot comparison
`Work.FTS.H2.Transport3Aux.phi_le_two`). -/

/-- `|D_z^b f| ≤ 15 |f|_𝒲` for `b ≤ 4`, in the interior class. -/
theorem abs_dzIter_le_wlInf_Q {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) (hfm : Work.Spaces.WlInfMem α 4 f) {b : ℕ} (hb : b ≤ 4)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.DzIter b f z θ| ≤ 15 * Work.Spaces.WlInf α 4 f :=
  Work.FTS.H2.WPQ.DzIter_le_WlInf hf hfm hb hz hθ

/-- `|D_z^b D_θ^a f| ≤ 30 |f|_𝒲` for `1 ≤ a`, `a + b ≤ 4`, in the interior class. -/
theorem abs_mixed_le_wlInf_Q {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) (hfm : Work.Spaces.WlInfMem α 4 f) {a b : ℕ}
    (ha : 1 ≤ a) (hab : a + b ≤ 4) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.mixed b a f z θ| ≤ 30 * Work.Spaces.WlInf α 4 f := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have h := Work.FTS.H2.WPQ.Mixed_le_WlInf hα hf hfm ha hab hz hθ
  have hW0 : 0 ≤ Work.Spaces.WlInf α 4 f :=
    Work.FTS.H2.Transport3Aux.wlInf_nonneg α f hfm
  have hphi := Work.FTS.H2.Transport3Aux.phi_le_two α hα hα1 hθI
  calc |Work.Spaces.mixed b a f z θ|
      ≤ 15 * (Work.Spaces.WlInf α 4 f
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := h
    _ ≤ 15 * (Work.Spaces.WlInf α 4 f * 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hphi hW0) (by norm_num)
    _ = 30 * Work.Spaces.WlInf α 4 f := by ring

/-! ## The absolute-value forms of the Leibniz summands -/

/-- `|xD|` is bounded by the binomial coefficient times its factored form. -/
theorem abs_xD_le_Q (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (i b : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |xD f g i b z θ| ≤ (i.choose b : ℝ) * (|Work.Spaces.DzIter b f z θ| *
      (|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
        * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := by
  have hch : 0 ≤ (i.choose b : ℝ) := by positivity
  have hW : (Whz z θ) ^ 2 ≤ Wm α z θ * Whz z θ := Whz_sq_le_Wm_mul α hα hθ
  have hXYZ : 0 ≤ |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
      * |Work.Spaces.DzIter i g z θ| := by positivity
  simp only [xD, abs_mul, abs_sq, sq_abs, abs_of_nonneg hch]
  calc (i.choose b : ℝ) * (|Work.Spaces.DzIter b f z θ|
        * |Work.Spaces.mixed (i - b) 1 g z θ|
        * |Work.Spaces.DzIter i g z θ| * Whz z θ ^ 2)
      = (i.choose b : ℝ) * ((|Work.Spaces.DzIter b f z θ|
          * |Work.Spaces.mixed (i - b) 1 g z θ|
          * |Work.Spaces.DzIter i g z θ|) * Whz z θ ^ 2) := by ring
    _ ≤ (i.choose b : ℝ) * ((|Work.Spaces.DzIter b f z θ|
          * |Work.Spaces.mixed (i - b) 1 g z θ|
          * |Work.Spaces.DzIter i g z θ|) * (Wm α z θ * Whz z θ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW hXYZ) hch
    _ = (i.choose b : ℝ) * (|Work.Spaces.DzIter b f z θ|
          * (|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := by ring

/-- `|yM|` is bounded by the product of the binomial coefficients times its factored form. -/
theorem abs_yM_le_Q (α : ℝ) (f g : ℝ → ℝ → ℝ) (i j a b : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |yM α f g i j a b z θ| ≤ ((i.choose a : ℝ) * (j.choose b : ℝ)) *
      (|Work.Spaces.mixed b a f z θ|
        * (|Work.Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
        * (|Work.Spaces.mixed j i g z θ| * Wm α z θ)) := by
  have hch : 0 ≤ (i.choose a : ℝ) * (j.choose b : ℝ) := by positivity
  simp only [yM, abs_mul, abs_sq, sq_abs, abs_of_nonneg hch]
  exact le_of_eq (by ring)

/-! ## The pointwise bound of the individual summands -/

/-- The `D_z`-slot summands `xD` are bounded by `240 |f|_𝒲 · HkIntegrand α 4 g`. -/
theorem xD_bound_Q (α : ℝ) (hα : 0 < α) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) (hfm : Work.Spaces.WlInfMem α 4 f) (i b : ℕ) (hi : i ≤ 4)
    (hbi : b ≤ i) (hne : ¬(i = 4 ∧ b = 0)) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |xD f g i b z θ|
      ≤ 240 * (Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ) := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hW0 : 0 ≤ Work.Spaces.WlInf α 4 f := Work.FTS.H2.Transport3Aux.wlInf_nonneg α f hfm
  have hH0 : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hWH : 0 ≤ Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ :=
    mul_nonneg hW0 hH0
  -- the order of the mixed `g`-factor
  have hmb : 1 + (i - b) ≤ 4 := by
    by_contra hc
    push_neg at hc
    have hb0 : b = 0 := by omega
    have hi4 : i = 4 := by omega
    exact hne ⟨hi4, hb0⟩
  have hF : |Work.Spaces.DzIter b f z θ| ≤ 15 * Work.Spaces.WlInf α 4 f :=
    abs_dzIter_le_wlInf_Q hf hfm (by omega) hz hθ
  have hsqA : (|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    have h := Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ 1 (i - b) (le_refl 1) hmb
    simpa only [mul_pow, sq_abs, Wm, Work.Spaces.Wt] using h
  have hsqB : (|Work.Spaces.DzIter i g z θ| * Whz z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    have h := Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ i hi
    simpa only [mul_pow, sq_abs, Whz] using h
  have hAB : (|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
      * (|Work.Spaces.DzIter i g z θ| * Whz z θ) ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.FTS.H2.Transport3Aux.mul_self_le_of_sq_le
      (mul_nonneg (abs_nonneg _) (Wm_nonneg α hθI))
      (mul_nonneg (abs_nonneg _) (Whz_nonneg hθI)) hsqA hsqB
  have hstep : |Work.Spaces.DzIter b f z θ|
        * (|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
        * (|Work.Spaces.DzIter i g z θ| * Whz z θ)
      ≤ (15 * Work.Spaces.WlInf α 4 f) * Work.Spaces.HkIntegrand α 4 g z θ := by
    have hnn : 0 ≤ (|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
        * (|Work.Spaces.DzIter i g z θ| * Whz z θ) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (Wm_nonneg α hθI))
        (mul_nonneg (abs_nonneg _) (Whz_nonneg hθI))
    calc |Work.Spaces.DzIter b f z θ| * (|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ)
        = |Work.Spaces.DzIter b f z θ|
            * ((|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
            * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := by ring
      _ ≤ (15 * Work.Spaces.WlInf α 4 f)
            * ((|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
            * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := mul_le_mul_of_nonneg_right hF hnn
      _ ≤ (15 * Work.Spaces.WlInf α 4 f) * Work.Spaces.HkIntegrand α 4 g z θ :=
          mul_le_mul_of_nonneg_left hAB (by linarith)
  have hcoef : (i.choose b : ℝ) ≤ 16 := Work.FTS.H2.Transport3Aux.choose_le_sixteen (n := i) (k := b) hi
  have hnn : 0 ≤ |Work.Spaces.DzIter b f z θ|
      * (|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
      * (|Work.Spaces.DzIter i g z θ| * Whz z θ) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (Wm_nonneg α hθI)))
      (mul_nonneg (abs_nonneg _) (Whz_nonneg hθI))
  calc |xD f g i b z θ|
      ≤ (i.choose b : ℝ) * (|Work.Spaces.DzIter b f z θ|
          * (|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := abs_xD_le_Q α hα f g i b hθI
    _ ≤ 16 * ((15 * Work.Spaces.WlInf α 4 f) * Work.Spaces.HkIntegrand α 4 g z θ) :=
        mul_le_mul hcoef hstep hnn (by norm_num)
    _ = 240 * (Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ) := by ring

/-- The mixed-slot summands `yM` are bounded by `7680 |f|_𝒲 · HkIntegrand α 4 g`. -/
theorem yM_bound_Q (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) (hfm : Work.Spaces.WlInfMem α 4 f) (i j a b : ℕ)
    (hi : 1 ≤ i) (hij : i + j ≤ 4) (hai : a ≤ i) (hbj : b ≤ j)
    (hne : ¬(a = 0 ∧ b = 0 ∧ i + j = 4)) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |yM α f g i j a b z θ|
      ≤ 7680 * (Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ) := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hW0 : 0 ≤ Work.Spaces.WlInf α 4 f := Work.FTS.H2.Transport3Aux.wlInf_nonneg α f hfm
  have hH0 : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  -- the order of the first mixed `g`-factor
  have hord : (i - a + 1) + (j - b) ≤ 4 := by
    have hle : a + b ≤ i + j := by omega
    by_cases hab : a + b = 0
    · have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      have hij3 : i + j ≤ 3 := by
        by_contra hc
        exact hne ⟨ha0, hb0, by omega⟩
      omega
    · omega
  -- the `f`-factor
  have hF : |Work.Spaces.mixed b a f z θ| ≤ 30 * Work.Spaces.WlInf α 4 f := by
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · subst ha0
      rw [Work.Spaces.mixed_zero_right]
      have h := abs_dzIter_le_wlInf_Q hf hfm (b := b) (by omega) hz hθ
      linarith
    · exact abs_mixed_le_wlInf_Q hα hα1 hf hfm hapos (by omega) hz hθ
  -- the two `g`-slots
  have hsqA : (|Work.Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    have h := Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ (i - a + 1) (j - b) (by omega) hord
    simpa only [mul_pow, sq_abs, Wm, Work.Spaces.Wt] using h
  have hsqB : (|Work.Spaces.mixed j i g z θ| * Wm α z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    have h := Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i j hi hij
    simpa only [mul_pow, sq_abs, Wm, Work.Spaces.Wt] using h
  have hAB : (|Work.Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
      * (|Work.Spaces.mixed j i g z θ| * Wm α z θ) ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.FTS.H2.Transport3Aux.mul_self_le_of_sq_le
      (mul_nonneg (abs_nonneg _) (Wm_nonneg α hθI))
      (mul_nonneg (abs_nonneg _) (Wm_nonneg α hθI)) hsqA hsqB
  have hstep : |Work.Spaces.mixed b a f z θ|
        * ((|Work.Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
          * (|Work.Spaces.mixed j i g z θ| * Wm α z θ))
      ≤ (30 * Work.Spaces.WlInf α 4 f) * Work.Spaces.HkIntegrand α 4 g z θ := by
    have hnn : 0 ≤ (|Work.Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
        * (|Work.Spaces.mixed j i g z θ| * Wm α z θ) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (Wm_nonneg α hθI))
        (mul_nonneg (abs_nonneg _) (Wm_nonneg α hθI))
    exact le_trans (mul_le_mul_of_nonneg_right hF hnn)
      (mul_le_mul_of_nonneg_left hAB (by linarith))
  have hcoef : ((i.choose a : ℝ) * (j.choose b : ℝ)) ≤ 256 := by
    have h1 : (i.choose a : ℝ) ≤ 16 :=
      Work.FTS.H2.Transport3Aux.choose_le_sixteen (n := i) (k := a) (by omega)
    have h2 : (j.choose b : ℝ) ≤ 16 :=
      Work.FTS.H2.Transport3Aux.choose_le_sixteen (n := j) (k := b) (by omega)
    have h3 : (0 : ℝ) ≤ (i.choose a : ℝ) := by positivity
    have h4 : (0 : ℝ) ≤ (j.choose b : ℝ) := by positivity
    nlinarith [h1, h2, h3, h4]
  have hnn : 0 ≤ |Work.Spaces.mixed b a f z θ|
      * ((|Work.Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
        * (|Work.Spaces.mixed j i g z θ| * Wm α z θ)) :=
    mul_nonneg (abs_nonneg _)
      (mul_nonneg (mul_nonneg (abs_nonneg _) (Wm_nonneg α hθI))
        (mul_nonneg (abs_nonneg _) (Wm_nonneg α hθI)))
  calc |yM α f g i j a b z θ|
      ≤ ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (|Work.Spaces.mixed b a f z θ|
            * ((|Work.Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
              * (|Work.Spaces.mixed j i g z θ| * Wm α z θ))) := by
        simpa only [mul_assoc] using abs_yM_le_Q α f g i j a b hθI
    _ ≤ 256 * ((30 * Work.Spaces.WlInf α 4 f) * Work.Spaces.HkIntegrand α 4 g z θ) :=
        mul_le_mul hcoef hstep hnn (by norm_num)
    _ = 7680 * (Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ) := by ring

/-! ## The assembly -/

/-- The pointwise bound of `EasyMajor` at the explicit constant `4806000`. -/
theorem easyMajor_bound_aux (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (hfm : Work.Spaces.WlInfMem α 4 f) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    EasyMajor α f g z θ
      ≤ 4806000 * Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ := by
  have hW0 : 0 ≤ Work.Spaces.WlInf α 4 f := Work.FTS.H2.Transport3Aux.wlInf_nonneg α f hfm
  have hH0 : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hWH : 0 ≤ Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ := mul_nonneg hW0 hH0
  have h240 : 0 ≤ 240 * (Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ) :=
    mul_nonneg (by norm_num) hWH
  have h7680 : 0 ≤ 7680 * (Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ) :=
    mul_nonneg (by norm_num) hWH
  have h1200 : 0 ≤ 5 * (240 * (Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ)) :=
    mul_nonneg (by norm_num) h240
  have h38400 : 0 ≤ 5 * (7680 * (Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ)) :=
    mul_nonneg (by norm_num) h7680
  have h96000 : 0 ≤ 5 * (5 * (7680 * (Work.Spaces.WlInf α 4 f
      * Work.Spaces.HkIntegrand α 4 g z θ))) :=
    mul_nonneg (by norm_num) h38400
  have h480000 : 0 ≤ 5 * (5 * (5 * (7680 * (Work.Spaces.WlInf α 4 f
      * Work.Spaces.HkIntegrand α 4 g z θ)))) :=
    mul_nonneg (by norm_num) h96000
  -- Step 1: the `D_z`-slot sum
  have hS1 : (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
      (if i = 4 ∧ b = 0 then 0 else |xD f g i b z θ|))
      ≤ 6000 * (Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ) := by
    have hb : ∀ i : ℕ, i ≤ 4 → (∑ b ∈ Finset.range (i + 1),
        (if i = 4 ∧ b = 0 then 0 else |xD f g i b z θ|))
        ≤ 5 * (240 * (Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ)) := by
      intro i hi4
      refine Work.FTS.H2.Transport3Aux.sum_range_succ_le hi4 h240 ?_
      intro b hb'
      have hbi : b ≤ i := by have := Finset.mem_range.mp hb'; omega
      by_cases hc : i = 4 ∧ b = 0
      · rw [if_pos hc]; exact h240
      · rw [if_neg hc]
        exact xD_bound_Q α hα hf hfm i b hi4 hbi hc hz hθ
    have hpt : ∀ i ∈ Finset.range 5, (∑ b ∈ Finset.range (i + 1),
        (if i = 4 ∧ b = 0 then 0 else |xD f g i b z θ|))
        ≤ 5 * (240 * (Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ)) :=
      fun i hi' => hb i (Nat.le_of_lt_succ (Finset.mem_range.mp hi'))
    have h1 := Work.FTS.H2.Transport3Aux.sum_range_succ_le (n := 4) (by norm_num) h1200 hpt
    calc (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
          (if i = 4 ∧ b = 0 then 0 else |xD f g i b z θ|))
        ≤ 5 * (5 * (240 * (Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ))) := h1
      _ = 6000 * (Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ) := by ring
  -- Step 2: the mixed-slot sum
  have hS2 : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
      (if 1 ≤ i ∧ i + j ≤ 4 then
        ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b z θ|)
        else 0))
      ≤ 4800000 * (Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ) := by
    -- the innermost sum, over `b`, for fixed `i`, `j`, `a`
    have hb : ∀ (i j a : ℕ), i ≤ 4 → j ≤ 4 → 1 ≤ i → i + j ≤ 4 → a ≤ i →
        (∑ b ∈ Finset.range (j + 1),
          (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b z θ|))
          ≤ 5 * (7680 * (Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ)) := by
      intro i j a hi4 hj4 hi1 hij hai
      refine Work.FTS.H2.Transport3Aux.sum_range_succ_le hj4 h7680 ?_
      intro b hb'
      have hbj : b ≤ j := by have := Finset.mem_range.mp hb'; omega
      by_cases hc : a = 0 ∧ b = 0 ∧ i + j = 4
      · rw [if_pos hc]; exact h7680
      · rw [if_neg hc]
        exact yM_bound_Q α hα hα1 hf hfm i j a b hi1 hij hai hbj hc hz hθ
    -- the sum over `a`
    have ha : ∀ (i j : ℕ), i ≤ 4 → j ≤ 4 → 1 ≤ i → i + j ≤ 4 →
        (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b z θ|))
          ≤ 5 * (5 * (7680 * (Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ))) := by
      intro i j hi4 hj4 hi1 hij
      exact Work.FTS.H2.Transport3Aux.sum_range_succ_le (n := i) hi4 h38400
        (fun a ha' => hb i j a hi4 hj4 hi1 hij (by have := Finset.mem_range.mp ha'; omega))
    -- the sum over `j`
    have hj : ∀ i : ℕ, i ≤ 4 →
        (∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b z θ|)
            else 0))
          ≤ 5 * (5 * (5 * (7680 * (Work.Spaces.WlInf α 4 f
              * Work.Spaces.HkIntegrand α 4 g z θ)))) := by
      intro i hi4
      have hpt : ∀ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b z θ|)
            else 0)
          ≤ 5 * (5 * (7680 * (Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ))) := by
        intro j hj'
        have hj4 : j ≤ 4 := Nat.le_of_lt_succ (Finset.mem_range.mp hj')
        by_cases hc : 1 ≤ i ∧ i + j ≤ 4
        · rw [if_pos hc]
          exact ha i j hi4 hj4 hc.1 hc.2
        · rw [if_neg hc]
          exact h96000
      exact Work.FTS.H2.Transport3Aux.sum_range_succ_le (n := 4) (by norm_num) h96000 hpt
    -- the sum over `i`
    have hpt : ∀ i ∈ Finset.range 5,
        (∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b z θ|)
            else 0))
        ≤ 5 * (5 * (5 * (7680 * (Work.Spaces.WlInf α 4 f
            * Work.Spaces.HkIntegrand α 4 g z θ)))) :=
      fun i hi' => hj i (Nat.le_of_lt_succ (Finset.mem_range.mp hi'))
    have h1 := Work.FTS.H2.Transport3Aux.sum_range_succ_le (n := 4) (by norm_num) h480000 hpt
    calc (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b z θ|)
            else 0))
        ≤ 5 * (5 * (5 * (5 * (7680 * (Work.Spaces.WlInf α 4 f
            * Work.Spaces.HkIntegrand α 4 g z θ))))) := h1
      _ = 4800000 * (Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ) := by ring
  have hMajor : EasyMajor α f g z θ
      ≤ 6000 * (Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ)
        + 4800000 * (Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ) := by
    rw [EasyMajor]
    exact add_le_add hS1 hS2
  calc EasyMajor α f g z θ
      ≤ 6000 * (Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ)
        + 4800000 * (Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ) := hMajor
    _ = 4806000 * Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ := by ring

/-- The pointwise bound of the Leibniz majorant `EasyMajor` of the interior "easy part"
`T1Easy α f g = H4PairInt α (f·D_θg) g - T1Hard α f g`.

`EasyMajor α f g z θ` (`Submission/Work/FTS/H2/T1EasyBound.lean`) is the sum of the absolute
values of all the Leibniz summands (`xD`, `yM`) of the expansion of `H4PairInt α (f·D_θg) g` with
the five order-five summands removed.  On the interior (`z > 0`, `0 < θ < π/2`) it is bounded by
`C |f|_{𝒲^{4,∞}} · HkIntegrand α 4 g`, uniformly in `0 < α ≤ 1`, for `f` of class
`SmoothQuad` (genuine `C^∞` on the open quadrant) with finite `𝒲^{4,∞}`-norm.  No hypothesis on
`g` is needed (only the elementary slot comparisons `Work.Spaces.sq_le_HkIntegrand_z` /
`sq_le_HkIntegrand_mixed`).

ROUTE.  Copy `Submission/Work/FTS/H2/Transport3Aux/easySum_bound.lean` (`xD_bound`, `yM_bound`
and the assembly `easySum_bound_aux` — that file proves the same statement in the stronger
class `Spaces.SmoothNbhd f`, but it is stated for the *other* copy `Transport3Aux.xD`,
`Transport3Aux.yM`, `Transport3Aux.EasySum` of the same objects, so its proof must be transported
to `Work.FTS.H2.xD`/`yM`/`EasyMajor`), replacing the closed-quadrant `f`-bounds by the interior
ones `Work.FTS.H2.WPQ.DzIter_le_WlInf` (`|D_z^b f| ≤ 15 |f|_𝒲`) and
`Work.FTS.H2.WPQ.Mixed_le_WlInf` (together with `Work.FTS.H2.Transport3Aux.phi_le_two`, giving
`30 |f|_𝒲`), whose hypothesis is `θ ∈ Set.Ioo 0 (π/2)`.  The remaining ingredients are
class-free and can be reused verbatim: `Work.FTS.H2.Whz_le_Wm`, `Work.FTS.H2.Whz_sq_le_Wm_mul`,
`Work.FTS.H2.Whz_nonneg`, `Work.FTS.H2.Wm_nonneg`, `Work.Spaces.sq_le_HkIntegrand_z`,
`Work.Spaces.sq_le_HkIntegrand_mixed`, `Work.FTS.H2.Transport3Aux.choose_le_sixteen`,
`...sum_range_succ_le`, `...mul_self_le_of_sq_le`, `...whz_nonneg`, `...wm_nonneg`,
`...wlInf_nonneg`.  The template's constant `4806000` (or any larger one) suffices. -/
theorem EasyMajorBoundQ : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → Work.FTS.LocData.SmoothQuad f → Work.Spaces.WlInfMem α 4 f →
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.FTS.H2.EasyMajor α f g z θ
        ≤ C * Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ := by
  refine ⟨4806000, by norm_num, ?_⟩
  intro α f g hα hα1 hf hfm z hz θ hθ
  exact easyMajor_bound_aux α hα hα1 f g hf hfm hz hθ

end Work.FTS.H2.T3Q
