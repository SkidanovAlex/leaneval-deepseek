/-
Copyright: work module for the Elgindi finite-time singularity project.

# Pointwise bounds for `f` from `|∂_θ f|_{𝒲^{4,∞}}`

If `f` is smooth on the open strip, continuous on the closed quadrant, vanishes on the two
angular boundaries and `∂_θ f ∈ 𝒲^{4,∞}`, then

* `f` and all its `D_z`-derivatives are `O(sin 2θ · |∂_θ f|_𝒲)`,
* all the `D_z`/`D_θ`-derivatives of `f / sin 2θ` (order at most `4`) are `O(|∂_θ f|_𝒲)`.

The point is that `f` is the `θ`-integral of `∂_θ f`, so every `z`-derivative of `f` is the
corresponding integral of a `z`-derivative of `∂_θ f`; the latter is estimated by the
`𝒲^{4,∞}`-norm.  The `z`-derivatives under the `θ`-integral are obtained by a
difference-quotient argument (mean value theorem in `z` for the difference of two `θ`-slices,
then the fundamental theorem of calculus in `θ` for that difference).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.H2.STBasic
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.Spaces.pz_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Auxiliary: the `𝒲^{l,∞}`-norm is nonnegative -/

theorem WlInf_nonneg {α : ℝ} {l : ℕ} {f : ℝ → ℝ → ℝ} (hW : Spaces.WlInfMem α l f) :
    0 ≤ Spaces.WlInf α l f := by
  rw [Spaces.WlInf]
  exact add_nonneg (Spaces.wlZSum_nonneg α l f hW) (Spaces.wlThSum_nonneg α l f hW)

/-! ## Joint smoothness of the iterated `z`-partials -/

/-- The open strip on which `SmoothInt` functions are `C^∞`. -/
def strp : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)

theorem isOpen_strp : IsOpen strp := isOpen_Ioi.prod isOpen_Ioo

theorem contDiffOn_uncurry_pzIter {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) (m : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Spaces.pzIter m G)) V := by
  induction m with
  | zero => simpa using h
  | succ n ih => simpa [Spaces.pzIter_succ] using Work.Spaces.contDiffOn_uncurry_pz hV ih

/-- `∂_θ (∂_z^m f) = ∂_z^m (∂_θ f)` on an open set where `f` is `C^∞`. -/
theorem pth_pzIter_eq {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (m : ℕ) :
    Set.EqOn (Function.uncurry (Spaces.pth (Spaces.pzIter m f)))
      (Function.uncurry (Spaces.pzIter m (Spaces.pth f))) V := by
  induction m with
  | zero => intro p hp; rfl
  | succ n ih =>
      intro p hp
      have hsm_n : ContDiffOn ℝ ⊤ (Function.uncurry (Spaces.pzIter n f)) V :=
        contDiffOn_uncurry_pzIter hV h n
      have h2 : ContDiffAt ℝ 2 (Function.uncurry (Spaces.pzIter n f)) p :=
        (hsm_n.contDiffAt (hV.mem_nhds hp)).of_le (by simp)
      have key : Spaces.pth (Spaces.pz (Spaces.pzIter n f)) p.1 p.2
          = Spaces.pz (Spaces.pth (Spaces.pzIter n f)) p.1 p.2 :=
        (Work.Spaces.pz_pth_comm h2).symm
      have hcongr : Spaces.pz (Spaces.pth (Spaces.pzIter n f)) p.1 p.2
          = Spaces.pz (Spaces.pzIter n (Spaces.pth f)) p.1 p.2 :=
        Work.Spaces.pz_congr_of_isOpen hV ih hp
      show Spaces.pth (Spaces.pz (Spaces.pzIter n f)) p.1 p.2
          = Spaces.pz (Spaces.pzIter n (Spaces.pth f)) p.1 p.2
      rw [key, hcongr]

/-- A function vanishing at a fixed `θ` has all its `z`-derivatives vanishing there. -/
theorem pzIter_eq_zero_of_slice_zero {f : ℝ → ℝ → ℝ} {θ₀ : ℝ} (h : ∀ z, f z θ₀ = 0)
    (m : ℕ) (z : ℝ) : Spaces.pzIter m f z θ₀ = 0 := by
  induction m generalizing z with
  | zero => exact h z
  | succ n ih =>
      rw [Spaces.pzIter_succ, Spaces.pz]
      have : (fun z' => Spaces.pzIter n f z' θ₀) = fun _ => (0 : ℝ) := funext ih
      rw [this, deriv_const]

/-! ## The mean value bound on the `z`-difference quotient -/

/-- On `[a,b]` with `a ≥ 0`, the `z`-difference quotient of `pzIter j (∂_θ f)` is bounded by
`|∂_θf|_𝒲 / (1+a)^{j+1}`. -/
theorem mvt_pzIter_le {α : ℝ} {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothInt f)
    (hW : Spaces.WlInfMem α 4 (Spaces.pth f)) {j : ℕ} (hj : j + 1 ≤ 4)
    {s : ℝ} (hs : s ∈ Set.Ioo 0 (π / 2)) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    |Spaces.pzIter j (Spaces.pth f) b s - Spaces.pzIter j (Spaces.pth f) a s|
      ≤ Spaces.WlInf α 4 (Spaces.pth f) / (a + 1) ^ (j + 1) * (b - a) := by
  have hstrip : IsOpen strp := isOpen_strp
  have hpth_sm : ContDiffOn ℝ ⊤ (Function.uncurry (Spaces.pth f)) strp :=
    Work.Spaces.contDiffOn_uncurry_pth hstrip hsm.1
  have hjoint := contDiffOn_uncurry_pzIter hstrip hpth_sm j
  have hmem : ∀ ξ ∈ Set.Icc a b, (ξ, s) ∈ strp := fun ξ hξ =>
    ⟨by simp only [Set.mem_Ioi]; linarith [hξ.1, ha], hs⟩
  have hdiff : DifferentiableOn ℝ (fun ξ => Spaces.pzIter j (Spaces.pth f) ξ s)
      (Set.Icc a b) := by
    intro ξ hξ
    have h1 : ContDiffAt ℝ ⊤ (Function.uncurry (Spaces.pzIter j (Spaces.pth f))) (ξ, s) :=
      hjoint.contDiffAt (hstrip.mem_nhds (hmem ξ hξ))
    have h2 : DifferentiableAt ℝ (fun x : ℝ => (x, s)) ξ := by fun_prop
    exact ((h1.differentiableAt (by simp)).comp ξ h2).differentiableWithinAt
  have hderiv : ∀ ξ ∈ Set.Ico a b,
      HasDerivWithinAt (fun ξ => Spaces.pzIter j (Spaces.pth f) ξ s)
        (Spaces.pzIter (j + 1) (Spaces.pth f) ξ s) (Set.Ici ξ) ξ := by
    intro ξ hξ
    have h1 : ContDiffAt ℝ ⊤ (Function.uncurry (Spaces.pzIter j (Spaces.pth f))) (ξ, s) :=
      hjoint.contDiffAt (hstrip.mem_nhds (hmem ξ (Set.Ico_subset_Icc_self hξ)))
    have h2 : DifferentiableAt ℝ (fun x : ℝ => (x, s)) ξ := by fun_prop
    have hd : DifferentiableAt ℝ (fun ξ => Spaces.pzIter j (Spaces.pth f) ξ s) ξ := by
      have h3 := (h1.differentiableAt (by simp)).comp ξ h2
      simpa [Function.comp_def] using h3
    have hder : deriv (fun ξ => Spaces.pzIter j (Spaces.pth f) ξ s) ξ
        = Spaces.pzIter (j + 1) (Spaces.pth f) ξ s := by
      simp only [Spaces.pzIter_succ, Spaces.pz]
    rw [← hder]
    exact hd.hasDerivAt.hasDerivWithinAt
  have hbound : ∀ ξ ∈ Set.Ico a b,
      ‖Spaces.pzIter (j + 1) (Spaces.pth f) ξ s‖
        ≤ Spaces.WlInf α 4 (Spaces.pth f) / (a + 1) ^ (j + 1) := by
    intro ξ hξ
    have hξa : a ≤ ξ := hξ.1
    have hξz : 0 ≤ ξ := le_trans ha hξa
    have hsI : s ∈ Spaces.Iθ := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have h1 := Work.Spaces.pz_sup_bound α 4 (Spaces.pth f) hW (j + 1) hj ξ s
      (show ξ ∈ Spaces.Iz from hξz) hsI
    have h2 : (a + 1) ^ (j + 1) ≤ (ξ + 1) ^ (j + 1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have h2pos : (0 : ℝ) < (a + 1) ^ (j + 1) := pow_pos (by linarith) _
    calc ‖Spaces.pzIter (j + 1) (Spaces.pth f) ξ s‖
        ≤ Spaces.WlInf α 4 (Spaces.pth f) / (ξ + 1) ^ (j + 1) := h1
      _ ≤ Spaces.WlInf α 4 (Spaces.pth f) / (a + 1) ^ (j + 1) := by
          have h3 : (1:ℝ) / (ξ + 1) ^ (j + 1) ≤ 1 / (a + 1) ^ (j + 1) :=
            one_div_le_one_div_of_le h2pos h2
          calc Spaces.WlInf α 4 (Spaces.pth f) / (ξ + 1) ^ (j + 1)
              = Spaces.WlInf α 4 (Spaces.pth f) * (1 / (ξ + 1) ^ (j + 1)) := by ring
            _ ≤ Spaces.WlInf α 4 (Spaces.pth f) * (1 / (a + 1) ^ (j + 1)) :=
                mul_le_mul_of_nonneg_left h3 (WlInf_nonneg hW)
            _ = Spaces.WlInf α 4 (Spaces.pth f) / (a + 1) ^ (j + 1) := by ring
  have key := norm_image_sub_le_of_norm_deriv_right_le_segment hdiff.continuousOn hderiv hbound
    b (right_mem_Icc.mpr hab)
  have hsub : (fun ξ => Spaces.pzIter j (Spaces.pth f) ξ s) b
      - (fun ξ => Spaces.pzIter j (Spaces.pth f) ξ s) a
      = Spaces.pzIter j (Spaces.pth f) b s - Spaces.pzIter j (Spaces.pth f) a s := rfl
  rw [hsub] at key
  rwa [Real.norm_eq_abs] at key



/-! ## Continuity and `θ`-differentiability of the slices at interior points -/

theorem slice_continuousAt_of_joint {G : ℝ → ℝ → ℝ}
    (hG : ContDiffOn ℝ ⊤ (Function.uncurry G) strp) {j : ℕ} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContinuousAt (fun s => Spaces.pzIter j G z s) θ := by
  have hstrip : IsOpen strp := isOpen_strp
  have hjoint := contDiffOn_uncurry_pzIter hstrip hG j
  have hp : (z, θ) ∈ strp := ⟨by show (-1:ℝ) < z; linarith, hθ⟩
  have h1 : ContinuousAt (Function.uncurry (Spaces.pzIter j G)) (z, θ) :=
    (hjoint.contDiffAt (hstrip.mem_nhds hp)).continuousAt
  have h2 : ContinuousAt (fun s : ℝ => (z, s)) θ := by fun_prop
  have h3 : ContinuousAt (Function.uncurry (Spaces.pzIter j G) ∘ fun s : ℝ => (z, s)) θ :=
    h1.comp h2
  simpa [Function.comp_def] using h3

theorem pzIter_slice_continuousAt {f : ℝ → ℝ → ℝ} {j : ℕ} (hsm : Spaces.SmoothInt f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContinuousAt (fun s => Spaces.pzIter j f z s) θ :=
  slice_continuousAt_of_joint hsm.1 hz hθ

theorem pth_slice_continuousAt {f : ℝ → ℝ → ℝ} {j : ℕ} (hsm : Spaces.SmoothInt f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContinuousAt (fun s => Spaces.pzIter j (Spaces.pth f) z s) θ :=
  slice_continuousAt_of_joint (Work.Spaces.contDiffOn_uncurry_pth isOpen_strp hsm.1) hz hθ

/-- The `θ`-derivative of `pzIter j f` on the open strip. -/
theorem hasDerivAt_pzIter_slice {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothInt f) {j : ℕ}
    {z s : ℝ} (hz : 0 < z) (hs : s ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun s => Spaces.pzIter j f z s) (Spaces.pzIter j (Spaces.pth f) z s) s := by
  have hstrip : IsOpen strp := isOpen_strp
  have hjoint := contDiffOn_uncurry_pzIter hstrip hsm.1 j
  have hp : (z, s) ∈ strp := ⟨by show (-1:ℝ) < z; linarith, hs⟩
  have h1 : ContDiffAt ℝ ⊤ (Function.uncurry (Spaces.pzIter j f)) (z, s) :=
    hjoint.contDiffAt (hstrip.mem_nhds hp)
  have hd : DifferentiableAt ℝ (Function.uncurry (Spaces.pzIter j f)) (z, s) :=
    h1.differentiableAt (by simp)
  have h5 : (fderiv ℝ (Function.uncurry (Spaces.pzIter j f)) (z, s)) (0, 1)
      = Spaces.pth (Spaces.pzIter j f) z s := (Work.Spaces.pth_eq_fderiv hd).symm
  have h4 : Spaces.pth (Spaces.pzIter j f) z s
      = Spaces.pzIter j (Spaces.pth f) z s :=
    pth_pzIter_eq hstrip hsm.1 j hp
  have h2 : HasDerivAt (fun s' : ℝ => (z, s')) (0, (1:ℝ)) s := by
    simpa using (hasDerivAt_const s z).prodMk (hasDerivAt_id s)
  have h3 : HasDerivAt (fun s' => Function.uncurry (Spaces.pzIter j f) (z, s'))
      ((fderiv ℝ (Function.uncurry (Spaces.pzIter j f)) (z, s)) (0, 1)) s :=
    hd.hasFDerivAt.comp_hasDerivAt s h2
  rw [h5, h4] at h3
  simpa [Function.uncurry] using h3

/-- Interval integrability of the `θ`-slice of `∂_z^j ∂_θ f` on any subinterval of `Iθ`. -/
theorem intervalIntegrable_pzIter_pth_Icc {α : ℝ} {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothInt f)
    (hW : Spaces.WlInfMem α 4 (Spaces.pth f)) {j : ℕ} (hj : j ≤ 4)
    {x a b : ℝ} (hx : 0 < x) (ha : 0 ≤ a) (hb : b ≤ π / 2) (hab : a ≤ b) :
    IntervalIntegrable (fun s => Spaces.pzIter j (Spaces.pth f) x s) volume a b := by
  set W := Spaces.WlInf α 4 (Spaces.pth f) with hWdef
  have hWnn : 0 ≤ W := WlInf_nonneg hW
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  refine MeasureTheory.Integrable.mono' (MeasureTheory.integrableOn_const (C := W) ?_) ?_ ?_
  · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  · have hc : ContinuousOn (fun s => Spaces.pzIter j (Spaces.pth f) x s) (Set.Ioo a b) := by
      intro s hs
      have hs' : s ∈ Set.Ioo 0 (π / 2) := ⟨lt_of_le_of_lt ha hs.1, lt_of_lt_of_le hs.2 hb⟩
      exact (pth_slice_continuousAt hsm hx hs').continuousWithinAt
    have haesm1 : AEStronglyMeasurable (fun s => Spaces.pzIter j (Spaces.pth f) x s)
        (volume.restrict (Set.Ioo a b)) := hc.aestronglyMeasurable measurableSet_Ioo
    have hset : Set.Ioo a b =ᵐ[volume] Set.Icc a b := MeasureTheory.Ioo_ae_eq_Icc
    rwa [MeasureTheory.Measure.restrict_congr_set hset] at haesm1
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun s hs => ?_)
    have hsI : s ∈ Spaces.Iθ := ⟨le_trans ha hs.1, le_trans hs.2 hb⟩
    have h1 := Work.Spaces.pz_sup_bound α 4 (Spaces.pth f) hW j hj x s
      (show x ∈ Spaces.Iz from le_of_lt hx) hsI
    rw [Real.norm_eq_abs] at ⊢
    have h2 : (1:ℝ) ≤ (x + 1) ^ j := one_le_pow₀ (by linarith)
    have h3 : (1:ℝ) / (x + 1) ^ j ≤ 1 := by
      rw [div_le_one (by positivity)]; exact h2
    calc |Spaces.pzIter j (Spaces.pth f) x s| ≤ W / (x + 1) ^ j := h1
      _ = W * (1 / (x + 1) ^ j) := by ring
      _ ≤ W * 1 := mul_le_mul_of_nonneg_left h3 hWnn
      _ = W := mul_one _

/-- The `θ`-FTC for the difference of two `z`-slices, from `0`. -/
theorem diff_slice_ftc_zero {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothInt f)
    {α : ℝ} (hW : Spaces.WlInfMem α 4 (Spaces.pth f)) {j : ℕ} (hj : j ≤ 4)
    {z z' : ℝ} (hz : 0 < z) (hz' : 0 < z') {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hv : Tendsto (fun s => Spaces.pzIter j f z' s - Spaces.pzIter j f z s) (𝓝[>] 0) (𝓝 0)) :
    Spaces.pzIter j f z' θ - Spaces.pzIter j f z θ
      = ∫ s in (0:ℝ)..θ,
          (Spaces.pzIter j (Spaces.pth f) z' s - Spaces.pzIter j (Spaces.pth f) z s) := by
  have hab : (0:ℝ) < θ := hθ.1
  have hderiv : ∀ s ∈ Set.Ioo 0 θ,
      HasDerivAt (fun s => Spaces.pzIter j f z' s - Spaces.pzIter j f z s)
        (Spaces.pzIter j (Spaces.pth f) z' s - Spaces.pzIter j (Spaces.pth f) z s) s := by
    intro s hs
    have hs' : s ∈ Set.Ioo 0 (π / 2) := ⟨hs.1, lt_trans hs.2 hθ.2⟩
    exact (hasDerivAt_pzIter_slice hsm hz' hs').sub (hasDerivAt_pzIter_slice hsm hz hs')
  have hint : IntervalIntegrable
      (fun s => Spaces.pzIter j (Spaces.pth f) z' s - Spaces.pzIter j (Spaces.pth f) z s)
      volume 0 θ :=
    (intervalIntegrable_pzIter_pth_Icc hsm hW hj hz' le_rfl (le_of_lt hθ.2) (le_of_lt hθ.1)).sub
      (intervalIntegrable_pzIter_pth_Icc hsm hW hj hz le_rfl (le_of_lt hθ.2) (le_of_lt hθ.1))
  have hb : Tendsto (fun s => Spaces.pzIter j f z' s - Spaces.pzIter j f z s) (𝓝[<] θ)
      (𝓝 (Spaces.pzIter j f z' θ - Spaces.pzIter j f z θ)) :=
    (((pzIter_slice_continuousAt hsm hz' hθ).sub
      (pzIter_slice_continuousAt hsm hz hθ)).tendsto).mono_left nhdsWithin_le_nhds
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hab hderiv hint hv hb
  linarith [key]

/-- The `θ`-FTC for the difference of two `z`-slices, from `π/2`. -/
theorem diff_slice_ftc_pi {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothInt f)
    {α : ℝ} (hW : Spaces.WlInfMem α 4 (Spaces.pth f)) {j : ℕ} (hj : j ≤ 4)
    {z z' : ℝ} (hz : 0 < z) (hz' : 0 < z') {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hv : Tendsto (fun s => Spaces.pzIter j f z' s - Spaces.pzIter j f z s) (𝓝[<] (π / 2)) (𝓝 0)) :
    Spaces.pzIter j f z' θ - Spaces.pzIter j f z θ
      = -∫ s in θ..(π / 2),
          (Spaces.pzIter j (Spaces.pth f) z' s - Spaces.pzIter j (Spaces.pth f) z s) := by
  have hab : θ < π / 2 := hθ.2
  have hderiv : ∀ s ∈ Set.Ioo θ (π / 2),
      HasDerivAt (fun s => Spaces.pzIter j f z' s - Spaces.pzIter j f z s)
        (Spaces.pzIter j (Spaces.pth f) z' s - Spaces.pzIter j (Spaces.pth f) z s) s := by
    intro s hs
    have hs' : s ∈ Set.Ioo 0 (π / 2) := ⟨lt_trans hθ.1 hs.1, hs.2⟩
    exact (hasDerivAt_pzIter_slice hsm hz' hs').sub (hasDerivAt_pzIter_slice hsm hz hs')
  have hint : IntervalIntegrable
      (fun s => Spaces.pzIter j (Spaces.pth f) z' s - Spaces.pzIter j (Spaces.pth f) z s)
      volume θ (π / 2) :=
    (intervalIntegrable_pzIter_pth_Icc hsm hW hj hz' (le_of_lt hθ.1) le_rfl (le_of_lt hθ.2)).sub
      (intervalIntegrable_pzIter_pth_Icc hsm hW hj hz (le_of_lt hθ.1) le_rfl (le_of_lt hθ.2))
  have ha : Tendsto (fun s => Spaces.pzIter j f z' s - Spaces.pzIter j f z s) (𝓝[>] θ)
      (𝓝 (Spaces.pzIter j f z' θ - Spaces.pzIter j f z θ)) :=
    (((pzIter_slice_continuousAt hsm hz' hθ).sub
      (pzIter_slice_continuousAt hsm hz hθ)).tendsto).mono_left nhdsWithin_le_nhds
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hab hderiv hint ha hv
  linarith [key]
/-- The mean value bound for the difference of the `z`-differences of `∂_z^j ∂_θ f`. -/
theorem mvt_diff_le {α : ℝ} {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothInt f)
    (hW : Spaces.WlInfMem α 4 (Spaces.pth f)) {j : ℕ} (hj : j + 1 ≤ 4)
    {z z' : ℝ} (hz : 0 < z) (hz' : 0 < z') {s : ℝ} (hs : s ∈ Set.Ioo 0 (π / 2)) :
    |Spaces.pzIter j (Spaces.pth f) z' s - Spaces.pzIter j (Spaces.pth f) z s|
      ≤ |z' - z| * (Spaces.WlInf α 4 (Spaces.pth f) / (min z z' + 1) ^ (j + 1)) := by
  rcases le_total z z' with h | h
  · rw [min_eq_left h, abs_of_nonneg (by linarith : (0:ℝ) ≤ z' - z), mul_comm]
    exact mvt_pzIter_le hsm hW hj hs (le_of_lt hz) h
  · rw [min_eq_right h, abs_of_nonpos (by linarith : z' - z ≤ 0), neg_sub, abs_sub_comm,
      mul_comm]
    exact mvt_pzIter_le hsm hW hj hs (le_of_lt hz') h

/-- Triangle inequality in the form `|x - y| ≤ |x| + |y|`. -/
theorem abs_sub_le_abs_add (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  simpa [sub_eq_add_neg] using abs_add_le x (-y)

/-- **The bound on the `z`-derivatives of `f`.**  Both `|∂_z^j f(z,θ)| ≤ 100 θ |∂_θf|_𝒲/(1+z)^j`
and the same with `π/2 - θ` in place of `θ`. -/
theorem pzIter_bound_aux {α : ℝ} {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothInt f)
    (hcont : ContinuousOn (Function.uncurry f) (Spaces.Iz ×ˢ Spaces.Iθ))
    (hvt : Spaces.VanishTheta f) (hW : Spaces.WlInfMem α 4 (Spaces.pth f)) :
    ∀ j ≤ 4, (∀ z ∈ Set.Ioi (0:ℝ), ∀ θ ∈ Set.Ioo (0:ℝ) (π / 2),
        |Spaces.pzIter j f z θ| ≤ 100 * θ * Spaces.WlInf α 4 (Spaces.pth f) / (z + 1) ^ j)
      ∧ (∀ z ∈ Set.Ioi (0:ℝ), ∀ θ ∈ Set.Ioo (0:ℝ) (π / 2),
        |Spaces.pzIter j f z θ|
          ≤ 100 * (π / 2 - θ) * Spaces.WlInf α 4 (Spaces.pth f) / (z + 1) ^ j) := by
  intro j
  induction j with
  | zero =>
      intro _
      constructor
      · intro z hz θ hθ
        have hftc : f z θ = ∫ s in (0:ℝ)..θ, Spaces.pth f z s := by
          have hcs : ContinuousOn (fun s => f z s) (Set.Icc 0 θ) := by
            refine hcont.comp (continuous_const.prodMk continuous_id).continuousOn ?_
            intro s hs
            exact ⟨(Set.mem_Ioi.mp hz).le, hs.1, hs.2.trans hθ.2.le⟩
          have hder : ∀ s ∈ Set.Ioo 0 θ, HasDerivAt (fun s => f z s) (Spaces.pth f z s) s := by
            intro s hs
            exact hasDerivAt_pzIter_slice (j := 0) hsm hz ⟨hs.1, lt_trans hs.2 hθ.2⟩
          have hint := intervalIntegrable_pzIter_pth_Icc hsm hW (j := 0) (by norm_num) hz le_rfl
            (le_of_lt hθ.2) (le_of_lt hθ.1)
          have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hθ.1) hcs hder hint
          rw [hvt.1 z, sub_zero] at key
          exact key.symm
        have hbnd : ∀ s ∈ Set.uIoc (0:ℝ) θ,
            ‖Spaces.pth f z s‖ ≤ Spaces.WlInf α 4 (Spaces.pth f) := by
          intro s hs
          rw [Set.uIoc_of_le (le_of_lt hθ.1)] at hs
          have hsI : s ∈ Spaces.Iθ := ⟨hs.1.le, hs.2.trans hθ.2.le⟩
          have h1 := Work.Spaces.pz_sup_bound α 4 (Spaces.pth f) hW 0 (by norm_num) z s
            (show z ∈ Spaces.Iz from (Set.mem_Ioi.mp hz).le) hsI
          rw [Real.norm_eq_abs]
          simpa using h1
        have h2 := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
        rw [Real.norm_eq_abs, sub_zero, abs_of_pos hθ.1] at h2
        simp only [Spaces.pzIter_zero, pow_zero, div_one]
        rw [hftc]
        calc |∫ s in (0:ℝ)..θ, Spaces.pth f z s| ≤ Spaces.WlInf α 4 (Spaces.pth f) * θ := h2
          _ ≤ 100 * θ * Spaces.WlInf α 4 (Spaces.pth f) := by
              nlinarith [hθ.1, WlInf_nonneg hW]
      · intro z hz θ hθ
        have hftc : f z θ = -∫ s in θ..(π / 2), Spaces.pth f z s := by
          have hcs : ContinuousOn (fun s => f z s) (Set.Icc θ (π / 2)) := by
            refine hcont.comp (continuous_const.prodMk continuous_id).continuousOn ?_
            intro s hs
            exact ⟨(Set.mem_Ioi.mp hz).le, hθ.1.le.trans hs.1, hs.2⟩
          have hder : ∀ s ∈ Set.Ioo θ (π / 2),
              HasDerivAt (fun s => f z s) (Spaces.pth f z s) s := by
            intro s hs
            exact hasDerivAt_pzIter_slice (j := 0) hsm hz ⟨lt_trans hθ.1 hs.1, hs.2⟩
          have hint := intervalIntegrable_pzIter_pth_Icc hsm hW (j := 0) (by norm_num) hz
            (le_of_lt hθ.1) le_rfl (le_of_lt hθ.2)
          have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hθ.2) hcs hder hint
          rw [hvt.2 z] at key
          rw [key]; ring
        have hbnd : ∀ s ∈ Set.uIoc θ (π/2),
            ‖Spaces.pth f z s‖ ≤ Spaces.WlInf α 4 (Spaces.pth f) := by
          intro s hs
          rw [Set.uIoc_of_le (le_of_lt hθ.2)] at hs
          have hsI : s ∈ Spaces.Iθ := ⟨hθ.1.le.trans hs.1.le, hs.2⟩
          have h1 := Work.Spaces.pz_sup_bound α 4 (Spaces.pth f) hW 0 (by norm_num) z s
            (show z ∈ Spaces.Iz from (Set.mem_Ioi.mp hz).le) hsI
          rw [Real.norm_eq_abs]
          simpa using h1
        have h2 := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
        rw [Real.norm_eq_abs, abs_of_pos (by linarith [hθ.2] : (0:ℝ) < π / 2 - θ)] at h2
        simp only [Spaces.pzIter_zero, pow_zero, div_one]
        rw [hftc, abs_neg]
        calc |∫ s in θ..(π / 2), Spaces.pth f z s|
            ≤ Spaces.WlInf α 4 (Spaces.pth f) * (π / 2 - θ) := h2
          _ ≤ 100 * (π / 2 - θ) * Spaces.WlInf α 4 (Spaces.pth f) := by
              have hpos : (0:ℝ) < π / 2 - θ := by linarith [hθ.2]
              nlinarith [hpos, WlInf_nonneg hW]
  | succ i ih =>
      intro hj
      have hi4 : i ≤ 4 := by omega
      have hIH := ih hi4
      have hzero : ∀ z ∈ Set.Ioi (0:ℝ), ∀ z' ∈ Set.Ioi (0:ℝ),
          Tendsto (fun s => Spaces.pzIter i f z' s - Spaces.pzIter i f z s) (𝓝[>] 0) (𝓝 0) := by
        intro z hz z' hz'
        have h1 : ∀ s ∈ Set.Ioo (0:ℝ) (π / 2),
            |Spaces.pzIter i f z' s - Spaces.pzIter i f z s|
              ≤ (200 * Spaces.WlInf α 4 (Spaces.pth f)) * s := by
          intro s hs
          have h2 := hIH.1 z' hz' s hs
          have h3 := hIH.1 z hz s hs
          have h4 : (1:ℝ) ≤ (z' + 1) ^ i := one_le_pow₀ (by linarith [Set.mem_Ioi.mp hz'])
          have h5 : (1:ℝ) ≤ (z + 1) ^ i := one_le_pow₀ (by linarith [Set.mem_Ioi.mp hz])
          have hWnn := WlInf_nonneg hW
          have h6 : 100 * s * Spaces.WlInf α 4 (Spaces.pth f) / (z' + 1) ^ i
              ≤ 100 * s * Spaces.WlInf α 4 (Spaces.pth f) := by
            exact div_le_self (mul_nonneg (mul_nonneg (by norm_num) hs.1.le) hWnn) h4
          have h7 : 100 * s * Spaces.WlInf α 4 (Spaces.pth f) / (z + 1) ^ i
              ≤ 100 * s * Spaces.WlInf α 4 (Spaces.pth f) := by
            exact div_le_self (mul_nonneg (mul_nonneg (by norm_num) hs.1.le) hWnn) h5
          calc |Spaces.pzIter i f z' s - Spaces.pzIter i f z s|
              ≤ |Spaces.pzIter i f z' s| + |Spaces.pzIter i f z s| :=
                abs_sub_le_abs_add _ _
            _ ≤ 100 * s * Spaces.WlInf α 4 (Spaces.pth f)
                  + 100 * s * Spaces.WlInf α 4 (Spaces.pth f) :=
                add_le_add (le_trans h2 h6) (le_trans h3 h7)
            _ = (200 * Spaces.WlInf α 4 (Spaces.pth f)) * s := by ring
        have hg : Tendsto (fun s : ℝ => (200 * Spaces.WlInf α 4 (Spaces.pth f)) * s)
            (𝓝[>] 0) (𝓝 0) := by
          have h1 : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 (0:ℝ)) :=
            tendsto_nhdsWithin_of_tendsto_nhds
              (show Tendsto (fun s : ℝ => s) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) from tendsto_id)
          have h2 := h1.const_mul (200 * Spaces.WlInf α 4 (Spaces.pth f))
          simpa using h2
        have key : Tendsto (fun s => |Spaces.pzIter i f z' s - Spaces.pzIter i f z s|)
            (𝓝[>] 0) (𝓝 0) :=
          squeeze_zero' (Eventually.of_forall fun s => abs_nonneg _)
            (by filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < π/2 by positivity)]
                  with s hs
                exact h1 s hs) hg
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simpa [Real.norm_eq_abs] using key
      have hzero' : ∀ z ∈ Set.Ioi (0:ℝ), ∀ z' ∈ Set.Ioi (0:ℝ),
          Tendsto (fun s => Spaces.pzIter i f z' s - Spaces.pzIter i f z s)
            (𝓝[<] (π / 2)) (𝓝 0) := by
        intro z hz z' hz'
        have h1 : ∀ s ∈ Set.Ioo (0:ℝ) (π / 2),
            |Spaces.pzIter i f z' s - Spaces.pzIter i f z s|
              ≤ (200 * Spaces.WlInf α 4 (Spaces.pth f)) * (π / 2 - s) := by
          intro s hs
          have h2 := hIH.2 z' hz' s hs
          have h3 := hIH.2 z hz s hs
          have h4 : (1:ℝ) ≤ (z' + 1) ^ i := one_le_pow₀ (by linarith [Set.mem_Ioi.mp hz'])
          have h5 : (1:ℝ) ≤ (z + 1) ^ i := one_le_pow₀ (by linarith [Set.mem_Ioi.mp hz])
          have hWnn := WlInf_nonneg hW
          have h6 : 100 * (π / 2 - s) * Spaces.WlInf α 4 (Spaces.pth f) / (z' + 1) ^ i
              ≤ 100 * (π / 2 - s) * Spaces.WlInf α 4 (Spaces.pth f) := by
            exact div_le_self (mul_nonneg (mul_nonneg (by norm_num)
              (by linarith [hs.2] : (0:ℝ) ≤ π / 2 - s)) hWnn) h4
          have h7 : 100 * (π / 2 - s) * Spaces.WlInf α 4 (Spaces.pth f) / (z + 1) ^ i
              ≤ 100 * (π / 2 - s) * Spaces.WlInf α 4 (Spaces.pth f) := by
            exact div_le_self (mul_nonneg (mul_nonneg (by norm_num)
              (by linarith [hs.2] : (0:ℝ) ≤ π / 2 - s)) hWnn) h5
          calc |Spaces.pzIter i f z' s - Spaces.pzIter i f z s|
              ≤ |Spaces.pzIter i f z' s| + |Spaces.pzIter i f z s| :=
                abs_sub_le_abs_add _ _
            _ ≤ 100 * (π / 2 - s) * Spaces.WlInf α 4 (Spaces.pth f)
                  + 100 * (π / 2 - s) * Spaces.WlInf α 4 (Spaces.pth f) :=
                add_le_add (le_trans h2 h6) (le_trans h3 h7)
            _ = (200 * Spaces.WlInf α 4 (Spaces.pth f)) * (π / 2 - s) := by ring
        have hg : Tendsto (fun s : ℝ => (200 * Spaces.WlInf α 4 (Spaces.pth f))
            * (π / 2 - s)) (𝓝[<] (π / 2)) (𝓝 0) := by
          have h1 : Tendsto (fun s : ℝ => π / 2 - s) (𝓝[<] (π / 2)) (𝓝 (0:ℝ)) := by
            have h2 : Tendsto (fun s : ℝ => π / 2 - s) (𝓝 (π / 2)) (𝓝 (π / 2 - π / 2)) :=
              tendsto_const_nhds.sub
                (show Tendsto (fun s : ℝ => s) (𝓝 (π/2 : ℝ)) (𝓝 (π/2 : ℝ)) from tendsto_id)
            simpa using h2.mono_left nhdsWithin_le_nhds
          have h3 := h1.const_mul (200 * Spaces.WlInf α 4 (Spaces.pth f))
          simpa using h3
        have key : Tendsto (fun s => |Spaces.pzIter i f z' s - Spaces.pzIter i f z s|)
            (𝓝[<] (π / 2)) (𝓝 0) :=
          squeeze_zero' (Eventually.of_forall fun s => abs_nonneg _)
            (by filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < π/2 by positivity)]
                  with s hs
                exact h1 s hs) hg
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simpa [Real.norm_eq_abs] using key
      have hderiv0 : ∀ z ∈ Set.Ioi (0:ℝ), ∀ θ ∈ Set.Ioo (0:ℝ) (π / 2),
          HasDerivAt (fun x => Spaces.pzIter i f x θ) (Spaces.pzIter (i + 1) f z θ) z := by
        intro z hz θ hθ
        have hstrip : IsOpen strp := isOpen_strp
        have hjoint := contDiffOn_uncurry_pzIter hstrip hsm.1 i
        have hp : (z, θ) ∈ strp :=
          ⟨by show (-1:ℝ) < z; linarith [Set.mem_Ioi.mp hz], hθ⟩
        have h1 : ContDiffAt ℝ ⊤ (Function.uncurry (Spaces.pzIter i f)) (z, θ) :=
          hjoint.contDiffAt (hstrip.mem_nhds hp)
        have h2 : DifferentiableAt ℝ (fun x : ℝ => (x, θ)) z := by fun_prop
        have hd : DifferentiableAt ℝ (fun x => Spaces.pzIter i f x θ) z := by
          have h3 := (h1.differentiableAt (by simp)).comp z h2
          simpa [Function.comp_def] using h3
        have h4 := hd.hasDerivAt
        simpa [Spaces.pzIter_succ, Spaces.pz] using h4
      have hstep : ∀ z ∈ Set.Ioi (0:ℝ), ∀ θ ∈ Set.Ioo (0:ℝ) (π / 2),
          |Spaces.pzIter (i + 1) f z θ|
            ≤ 100 * θ * Spaces.WlInf α 4 (Spaces.pth f) / (z + 1) ^ (i + 1) := by
        intro z hz θ hθ
        set W := Spaces.WlInf α 4 (Spaces.pth f) with hWdef
        have hWnn : 0 ≤ W := WlInf_nonneg hW
        have hderiv := hderiv0 z hz θ hθ
        have htend : Tendsto
            (fun z' => ‖(Spaces.pzIter i f z' θ - Spaces.pzIter i f z θ) / (z' - z)‖)
            (𝓝[≠] z) (𝓝 ‖Spaces.pzIter (i + 1) f z θ‖) := by
          have h1 := (hasDerivAt_iff_tendsto_slope.mp hderiv).norm
          simpa [slope_def_field] using h1
        have hquot : ∀ z' ∈ Set.Ioi (0:ℝ), z' ≠ z →
            ‖(Spaces.pzIter i f z' θ - Spaces.pzIter i f z θ) / (z' - z)‖
              ≤ θ * W / (min z z' + 1) ^ (i + 1) := by
          intro z' hz' hzne
          have hv := hzero z hz z' hz'
          have hftc := diff_slice_ftc_zero hsm hW (j := i) hi4 hz hz' hθ hv
          have hbnd : ∀ s ∈ Set.uIoc (0:ℝ) θ,
              ‖Spaces.pzIter i (Spaces.pth f) z' s - Spaces.pzIter i (Spaces.pth f) z s‖
                ≤ |z' - z| * (W / (min z z' + 1) ^ (i + 1)) := by
            intro s hs
            rw [Set.uIoc_of_le (le_of_lt hθ.1)] at hs
            rw [Real.norm_eq_abs]
            exact mvt_diff_le hsm hW (by omega) hz hz'
              ⟨hs.1, lt_of_le_of_lt hs.2 hθ.2⟩
          have h2 := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
          rw [Real.norm_eq_abs, sub_zero, abs_of_pos hθ.1] at h2
          rw [hftc]
          simp only [norm_div, Real.norm_eq_abs]
          have h5 : (0:ℝ) < |z' - z| := abs_pos.mpr (sub_ne_zero.mpr hzne)
          rw [div_le_iff₀ h5]
          calc |∫ s in (0:ℝ)..θ,
                (Spaces.pzIter i (Spaces.pth f) z' s - Spaces.pzIter i (Spaces.pth f) z s)|
              ≤ (|z' - z| * (W / (min z z' + 1) ^ (i + 1))) * θ := h2
            _ = (θ * W / (min z z' + 1) ^ (i + 1)) * |z' - z| := by ring
        have hg : Tendsto (fun z' => θ * W / (min z z' + 1) ^ (i + 1)) (𝓝[≠] z)
            (𝓝 (θ * W / (z + 1) ^ (i + 1))) := by
          have h1 : Tendsto (fun z' : ℝ => min z z') (𝓝[≠] z) (𝓝 z) := by
            have h2 : Tendsto (fun z' : ℝ => min z z') (𝓝 z) (𝓝 (min z z)) :=
              tendsto_const_nhds.min (show Tendsto (fun z' : ℝ => z') (𝓝 z) (𝓝 z) from tendsto_id)
            simpa using h2.mono_left nhdsWithin_le_nhds
          have h2 : Tendsto (fun z' : ℝ => (min z z' + 1) ^ (i + 1)) (𝓝[≠] z)
              (𝓝 ((z + 1) ^ (i + 1))) :=
            (h1.add tendsto_const_nhds).pow (i + 1)
          exact tendsto_const_nhds.div h2 (by
            have hz1 : (0:ℝ) < z + 1 := by linarith [Set.mem_Ioi.mp hz]
            positivity)
        have hev : ∀ᶠ z' in 𝓝[≠] z,
            ‖(Spaces.pzIter i f z' θ - Spaces.pzIter i f z θ) / (z' - z)‖
              ≤ θ * W / (min z z' + 1) ^ (i + 1) := by
          filter_upwards [self_mem_nhdsWithin,
            Filter.Eventually.filter_mono nhdsWithin_le_nhds
              (Ioi_mem_nhds (Set.mem_Ioi.mp hz))]
            with z' hzne hz'pos
          exact hquot z' hz'pos hzne
        have hkey := le_of_tendsto_of_tendsto htend hg hev
        rw [Real.norm_eq_abs] at hkey
        calc |Spaces.pzIter (i + 1) f z θ| ≤ θ * W / (z + 1) ^ (i + 1) := hkey
          _ ≤ 100 * θ * W / (z + 1) ^ (i + 1) := by
              refine div_le_div_of_nonneg_right ?_ (pow_pos (by linarith [Set.mem_Ioi.mp hz]) _).le
              nlinarith [hθ.1.le, hWnn]
          _ = 100 * θ * Spaces.WlInf α 4 (Spaces.pth f) / (z + 1) ^ (i + 1) := by rw [hWdef]
      have hstep2 : ∀ z ∈ Set.Ioi (0:ℝ), ∀ θ ∈ Set.Ioo (0:ℝ) (π / 2),
          |Spaces.pzIter (i + 1) f z θ|
            ≤ 100 * (π / 2 - θ) * Spaces.WlInf α 4 (Spaces.pth f) / (z + 1) ^ (i + 1) := by
        intro z hz θ hθ
        set W := Spaces.WlInf α 4 (Spaces.pth f) with hWdef
        have hWnn : 0 ≤ W := WlInf_nonneg hW
        have hderiv := hderiv0 z hz θ hθ
        have htend : Tendsto
            (fun z' => ‖(Spaces.pzIter i f z' θ - Spaces.pzIter i f z θ) / (z' - z)‖)
            (𝓝[≠] z) (𝓝 ‖Spaces.pzIter (i + 1) f z θ‖) := by
          have h1 := (hasDerivAt_iff_tendsto_slope.mp hderiv).norm
          simpa [slope_def_field] using h1
        have hquot : ∀ z' ∈ Set.Ioi (0:ℝ), z' ≠ z →
            ‖(Spaces.pzIter i f z' θ - Spaces.pzIter i f z θ) / (z' - z)‖
              ≤ (π / 2 - θ) * W / (min z z' + 1) ^ (i + 1) := by
          intro z' hz' hzne
          have hv := hzero' z hz z' hz'
          have hftc := diff_slice_ftc_pi hsm hW (j := i) hi4 hz hz' hθ hv
          have hbnd : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc θ (π/2) →
              ‖Spaces.pzIter i (Spaces.pth f) z' s - Spaces.pzIter i (Spaces.pth f) z s‖
                ≤ |z' - z| * (W / (min z z' + 1) ^ (i + 1)) := by
            rw [MeasureTheory.ae_iff]
            refine measure_mono_null ?_ (measure_singleton (π / 2))
            intro s hs
            simp only [Set.mem_setOf_eq, not_imp] at hs
            obtain ⟨hsu, hnot⟩ := hs
            rw [Set.uIoc_of_le (le_of_lt hθ.2)] at hsu
            rcases lt_or_eq_of_le hsu.2 with hlt | heq
            · exact absurd (by
                rw [Real.norm_eq_abs]
                exact mvt_diff_le hsm hW (by omega) hz hz' ⟨lt_trans hθ.1 hsu.1, hlt⟩) hnot
            · exact heq
          have h2 := intervalIntegral.norm_integral_le_of_norm_le_const_ae hbnd
          rw [Real.norm_eq_abs,
            abs_of_pos (by linarith [hθ.2] : (0:ℝ) < π / 2 - θ)] at h2
          rw [hftc]
          simp only [neg_div, norm_neg, norm_div, Real.norm_eq_abs]
          have h5 : (0:ℝ) < |z' - z| := abs_pos.mpr (sub_ne_zero.mpr hzne)
          rw [div_le_iff₀ h5]
          calc |∫ s in θ..(π / 2),
                (Spaces.pzIter i (Spaces.pth f) z' s - Spaces.pzIter i (Spaces.pth f) z s)|
              ≤ (|z' - z| * (W / (min z z' + 1) ^ (i + 1))) * (π / 2 - θ) := h2
            _ = ((π / 2 - θ) * W / (min z z' + 1) ^ (i + 1)) * |z' - z| := by ring
        have hg : Tendsto (fun z' => (π / 2 - θ) * W / (min z z' + 1) ^ (i + 1)) (𝓝[≠] z)
            (𝓝 ((π / 2 - θ) * W / (z + 1) ^ (i + 1))) := by
          have h1 : Tendsto (fun z' : ℝ => min z z') (𝓝[≠] z) (𝓝 z) := by
            have h2 : Tendsto (fun z' : ℝ => min z z') (𝓝 z) (𝓝 (min z z)) :=
              tendsto_const_nhds.min (show Tendsto (fun z' : ℝ => z') (𝓝 z) (𝓝 z) from tendsto_id)
            simpa using h2.mono_left nhdsWithin_le_nhds
          have h2 : Tendsto (fun z' : ℝ => (min z z' + 1) ^ (i + 1)) (𝓝[≠] z)
              (𝓝 ((z + 1) ^ (i + 1))) :=
            (h1.add tendsto_const_nhds).pow (i + 1)
          exact tendsto_const_nhds.div h2 (by
            have hz1 : (0:ℝ) < z + 1 := by linarith [Set.mem_Ioi.mp hz]
            positivity)
        have hev : ∀ᶠ z' in 𝓝[≠] z,
            ‖(Spaces.pzIter i f z' θ - Spaces.pzIter i f z θ) / (z' - z)‖
              ≤ (π / 2 - θ) * W / (min z z' + 1) ^ (i + 1) := by
          filter_upwards [self_mem_nhdsWithin,
            Filter.Eventually.filter_mono nhdsWithin_le_nhds
              (Ioi_mem_nhds (Set.mem_Ioi.mp hz))]
            with z' hzne hz'pos
          exact hquot z' hz'pos hzne
        have hkey := le_of_tendsto_of_tendsto htend hg hev
        rw [Real.norm_eq_abs] at hkey
        calc |Spaces.pzIter (i + 1) f z θ| ≤ (π / 2 - θ) * W / (z + 1) ^ (i + 1) := hkey
          _ ≤ 100 * (π / 2 - θ) * W / (z + 1) ^ (i + 1) := by
              refine div_le_div_of_nonneg_right ?_
                (pow_pos (by linarith [Set.mem_Ioi.mp hz]) _).le
              nlinarith [(by linarith [hθ.2] : (0:ℝ) ≤ π / 2 - θ), hWnn]
          _ = 100 * (π / 2 - θ) * Spaces.WlInf α 4 (Spaces.pth f) / (z + 1) ^ (i + 1) := by
              rw [hWdef]
      exact ⟨hstep, hstep2⟩

end Work.FTS.H2
