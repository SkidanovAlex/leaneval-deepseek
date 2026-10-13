import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.H2W.SlotA.radialDerivPointwiseOpen
import Submission.Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The radial integration by parts with the cut-off `χ_n = cut n`

With `Fp u` and `Fd u` the two `z`-integrands of `AeI1Fts/Defs`
(`Fd u z θ = z·(z ∂_z u)·∂_θθ u·w²`, `Fp` the three-term integrand of the pointwise identity
`∂_z(Fd u · θ) = w²·Fp u · θ`), the cut-off `χ_n = cut n` of `interpol_trunc_defs` is equal to
`1` on `[2/(n+1), 2(n+1)]` and supported in `(1/(n+1), 3(n+1))`, so both boundary terms of the
fundamental theorem of calculus vanish:

  `∫_{z>0} χ_n w² Fp u · θ = -∫_{z>0} (z χ_n') (z ∂_z u) (∂_θθ u) w²`.

The proof is `MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul` at `a = 0` applied to the pair
`(χ_n, z ↦ Fd u z θ)`, with both `u · v' = χ_n·(w² Fp u)` and `u' · v = χ_n'·Fd u` integrable
because they are continuous and compactly supported inside `(0,∞)`.
-/

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 2000000

private theorem isOpen_qd : IsOpen qd := isOpen_Ioi.prod isOpen_Ioo

/-! ## The partial-derivative API on the open quadrant -/

/-- The curried `z`-partial of a `C^{n+1}` function is `C^n`, because it is the composition of
the Fréchet derivative with the evaluation at the direction `(1,0)`. -/
private theorem contDiffOn_uncurry_pz_succ {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) {n : ℕ} (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := by
    intro p hp
    exact Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (n := (n + 1 : ℕ)) (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := n) hV.uniqueDiffOn le_rfl
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- The curried `θ`-partial of a `C^{n+1}` function is `C^n`. -/
private theorem contDiffOn_uncurry_pth_succ {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) {n : ℕ} (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := by
    intro p hp
    exact Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (n := (n + 1 : ℕ)) (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := n) hV.uniqueDiffOn le_rfl
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

private theorem contDiffOn_pairMk (n : ℕ) (θ : ℝ) :
    ContDiffOn ℝ n (fun z : ℝ => (z, θ)) (Set.Ioi 0) :=
  contDiffOn_id.prodMk contDiffOn_const

/-- The `z`-slice of a jointly `C^n` function on the open quadrant is `C^n` on `(0,∞)`. -/
private theorem contDiffOn_slice {f : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ n (Function.uncurry f) qd) {θ : ℝ} (hθ : θ ∈ Iθo) :
    ContDiffOn ℝ n (fun z => f z θ) (Set.Ioi 0) := by
  have hpair : ContDiffOn ℝ n (fun z : ℝ => (z, θ)) (Set.Ioi 0) := contDiffOn_pairMk n θ
  exact (h.comp hpair (fun z hz => ⟨hz, hθ⟩)).congr (fun z _ => rfl)

/-- A slice of a jointly `C^n` function on the open quadrant is continuous on `(0,∞)`. -/
private theorem continuousOn_slice_of_contDiffOn {f : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ n (Function.uncurry f) qd) {θ : ℝ} (hθ : θ ∈ Iθo) :
    ContinuousOn (fun z => f z θ) (Set.Ioi 0) :=
  (contDiffOn_slice h hθ).continuousOn

/-! ## Continuity of the `z`-slices of the two integrands -/

private theorem continuousOn_wSq : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2)
    (Set.Ioi 0) := by
  have h : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
    show ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0)
    exact ((continuous_const.add continuous_id).pow 2).continuousOn.div
      ((continuous_id.pow 2).continuousOn) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  exact h.pow 2

private theorem continuousOn_slice_Fp {u : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ 3 (Function.uncurry u) qd) {θ : ℝ} (hθ : θ ∈ Iθo) :
    ContinuousOn (fun z => Fp u z θ) (Set.Ioi 0) := by
  have hA1 := contDiffOn_uncurry_pz_succ isOpen_qd (n := 2) hu
  have hA2 := contDiffOn_uncurry_pz_succ isOpen_qd (n := 1) hA1
  have hB1 := contDiffOn_uncurry_pth_succ isOpen_qd (n := 2) hu
  have hB2 := contDiffOn_uncurry_pth_succ isOpen_qd (n := 1) hB1
  have hC := contDiffOn_uncurry_pz_succ isOpen_qd (n := 0) hB2
  have hA1s : ContinuousOn (fun z : ℝ => Work.Spaces.pz u z θ) (Set.Ioi 0) :=
    continuousOn_slice_of_contDiffOn hA1 hθ
  have hA2s : ContinuousOn (fun z : ℝ => Work.Spaces.pzIter 2 u z θ) (Set.Ioi 0) :=
    continuousOn_slice_of_contDiffOn hA2 hθ
  have hB2s : ContinuousOn (fun z : ℝ => Work.Spaces.pthIter 2 u z θ) (Set.Ioi 0) :=
    continuousOn_slice_of_contDiffOn hB2 hθ
  have hCs : ContinuousOn (fun z : ℝ => Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
      (Set.Ioi 0) :=
    continuousOn_slice_of_contDiffOn hC hθ
  have hcw : ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.AngSecond.cw z) (Set.Ioi 0) := by
    show ContinuousOn (fun z : ℝ => 2 * (z - 1) / (1 + z)) (Set.Ioi 0)
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
    · exact (continuousOn_const.add continuousOn_id)
    · intro z hz
      have : (0 : ℝ) < z := hz
      linarith
  have hid : ContinuousOn (fun z : ℝ => z) (Set.Ioi 0) := continuousOn_id
  have hmain : ContinuousOn (fun z : ℝ =>
      (z ^ 2 * Work.Spaces.pzIter 2 u z θ) * Work.Spaces.pthIter 2 u z θ
        + Work.FTS.EllipticEst.AngSecond.cw z * (z * Work.Spaces.pz u z θ)
            * Work.Spaces.pthIter 2 u z θ
        + (z * Work.Spaces.pz u z θ) * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ))
      (Set.Ioi 0) :=
    (((hid.pow 2).mul hA2s).mul hB2s).add ((hcw.mul (hid.mul hA1s)).mul hB2s)
      |>.add ((hid.mul hA1s).mul (hid.mul hCs))
  exact hmain.congr (fun z _ => by simp only [Fp])

private theorem continuousOn_slice_Fd {u : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ 3 (Function.uncurry u) qd) {θ : ℝ} (hθ : θ ∈ Iθo) :
    ContinuousOn (fun z => Fd u z θ) (Set.Ioi 0) := by
  have hA1 := contDiffOn_uncurry_pz_succ isOpen_qd (n := 2) hu
  have hB1 := contDiffOn_uncurry_pth_succ isOpen_qd (n := 2) hu
  have hB2 := contDiffOn_uncurry_pth_succ isOpen_qd (n := 1) hB1
  have hA1s : ContinuousOn (fun z : ℝ => Work.Spaces.pz u z θ) (Set.Ioi 0) :=
    continuousOn_slice_of_contDiffOn hA1 hθ
  have hB2s : ContinuousOn (fun z : ℝ => Work.Spaces.pthIter 2 u z θ) (Set.Ioi 0) :=
    continuousOn_slice_of_contDiffOn hB2 hθ
  have hid : ContinuousOn (fun z : ℝ => z) (Set.Ioi 0) := continuousOn_id
  have hmain : ContinuousOn (fun z : ℝ =>
      z * (z * Work.Spaces.pz u z θ) * Work.Spaces.pthIter 2 u z θ
        * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
    (((hid.mul (hid.mul hA1s)).mul hB2s).mul continuousOn_wSq)
  exact hmain.congr (fun z _ => by simp only [Fd])

/-! ## The pointwise derivative identity for `Fd` -/

private theorem cut_differentiable (n : ℕ) :
    Differentiable ℝ (Work.FTS.EllipticEst.cut n) := by
  have hcut : ContDiff ℝ ∞ (Work.FTS.EllipticEst.cut n) := Work.FTS.EllipticEst.cut_contDiff n
  exact (contDiff_infty_iff_deriv.mp hcut).1

private theorem continuous_deriv_cut (n : ℕ) :
    Continuous (deriv (Work.FTS.EllipticEst.cut n)) := by
  have hcut : ContDiff ℝ ∞ (Work.FTS.EllipticEst.cut n) := Work.FTS.EllipticEst.cut_contDiff n
  exact ((contDiff_infty_iff_deriv.mp hcut).2).continuous

/-- The derivative of the square of the radial weight: `∂_z(w²) = -4 w²/((1+z)z)`. -/
private theorem hasDerivAt_wSq {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' : ℝ => (Work.Spaces.w z') ^ 2)
      (-4 * (Work.Spaces.w z) ^ 2 / ((1 + z) * z)) z := by
  have h : HasDerivAt (fun t : ℝ => ((1 + t) ^ 2 / t ^ 2) ^ 2)
      (-4 * ((1 + z) ^ 2 / z ^ 2) ^ 2 / ((1 + z) * z)) z := by
    have hnum : HasDerivAt (fun t : ℝ => (1 + t) ^ 2) (2 * (1 + z)) z := by
      have h0 : HasDerivAt (fun t : ℝ => 1 + t) 1 z := (hasDerivAt_id z).const_add 1
      have h1 := h0.pow 2
      convert h1 using 1
      ring
    have hden : HasDerivAt (fun t : ℝ => t ^ 2) (2 * z) z := by
      have h0 := hasDerivAt_pow 2 z
      convert h0 using 1
      ring
    have hdiv := hnum.div hden (by positivity : z ^ 2 ≠ 0)
    refine (hdiv.pow 2).congr_deriv ?_
    simp only [Pi.div_apply]
    field_simp
    ring_nf
    simp only [inv_pow]
    field_simp
  simpa only [Work.Spaces.w] using h

/-- The pointwise identity `∂_z(Fd u · θ) = w² · Fp u · θ` on the open quadrant. -/
private theorem hasDerivAt_Fd {u : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ 3 (Function.uncurry u) qd) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Iθo) :
    HasDerivAt (fun z' => Fd u z' θ) ((Work.Spaces.w z) ^ 2 * Fp u z θ) z := by
  have hz0 : (0 : ℝ) < z := hz
  -- the `z`-slice of `u` is `C³` and its derivative is `∂_z u`
  have hslice3 : ContDiffOn ℝ 3 (fun z' => u z' θ) (Set.Ioi 0) :=
    contDiffOn_slice (n := 3) hu hθ
  have hsliceD : ContDiffOn ℝ 2 (fun z' => Work.Spaces.pz u z' θ) (Set.Ioi 0) := by
    have h := hslice3.deriv_of_isOpen isOpen_Ioi (m := 2) (by norm_num)
    simpa only [Work.Spaces.pz] using h
  have hA : HasDerivAt (fun z' => Work.Spaces.pz u z' θ) (Work.Spaces.pzIter 2 u z θ) z := by
    have hd : DifferentiableAt ℝ (fun z' => Work.Spaces.pz u z' θ) z :=
      (hsliceD.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz0)
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
      using hd.hasDerivAt
  -- the `z`-slice of `∂_θθu` is `C¹` and its derivative is `∂_z∂_θθu`
  have hB : HasDerivAt (fun z' => Work.Spaces.pthIter 2 u z' θ)
      (Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) z := by
    have h1 := contDiffOn_uncurry_pth_succ isOpen_qd (n := 2) hu
    have h2 := contDiffOn_uncurry_pth_succ isOpen_qd (n := 1) h1
    have hsliceP : ContDiffOn ℝ 1 (fun z' => Work.Spaces.pthIter 2 u z' θ) (Set.Ioi 0) :=
      contDiffOn_slice (n := 1) h2 hθ
    have hd : DifferentiableAt ℝ (fun z' => Work.Spaces.pthIter 2 u z' θ) z :=
      (hsliceP.differentiableOn_one).differentiableAt (isOpen_Ioi.mem_nhds hz0)
    simpa only [Work.Spaces.pz] using hd.hasDerivAt
  -- the product rule for the four factors `z'`, `z'·∂_zu`, `∂_θθu`, `w²`
  have h1 : HasDerivAt (fun z' : ℝ => z') (1 : ℝ) z := hasDerivAt_id z
  have h2 : HasDerivAt (fun z' => z' * Work.Spaces.pz u z' θ)
      (1 * Work.Spaces.pz u z θ + z * Work.Spaces.pzIter 2 u z θ) z := h1.mul hA
  have h3 := (h1.mul h2).mul hB
  have h4 := hasDerivAt_wSq hz
  refine (h3.mul h4).congr_deriv ?_
  rw [Fp]
  rw [show Work.FTS.EllipticEst.AngSecond.cw z = 2 * (z - 1) / (1 + z) from rfl]
  simp only [Pi.mul_apply]
  field_simp
  ring

/-! ## Integrability on the half-line of a compactly supported continuous function -/

private theorem integrableOn_Ioi_of_Icc_support {f : ℝ → ℝ} {a b : ℝ} (_ha : 0 < a)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hzero : ∀ z, z ∉ Set.Icc a b → f z = 0) :
    IntegrableOn f (Set.Ioi 0) := by
  have hInd : Integrable ((Set.Icc a b).indicator f) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (hcont.integrableOn_compact isCompact_Icc)
  have hfun : f = (Set.Icc a b).indicator f := by
    funext z
    by_cases hz : z ∈ Set.Icc a b
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hzero z hz]
  rw [hfun]
  refine ⟨hInd.aestronglyMeasurable.mono_measure Measure.restrict_le_self, ?_⟩
  calc ∫⁻ z, ‖(Set.Icc a b).indicator f z‖₊ ∂(volume.restrict (Set.Ioi 0))
      ≤ ∫⁻ z, ‖(Set.Icc a b).indicator f z‖₊ ∂(volume : Measure ℝ) :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ < ⊤ := hInd.hasFiniteIntegral

/-! ## The cut-off `χ_n` vanishes outside its band, together with its derivative -/

private theorem deriv_cut_eq_zero_of_lt (n : ℕ) {z : ℝ} (hz : z < 1 / (n + 1 : ℝ)) :
    deriv (Work.FTS.EllipticEst.cut n) z = 0 := by
  have hEq : (fun y : ℝ => Work.FTS.EllipticEst.cut n y) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hz] with y hy
    exact Work.FTS.EllipticEst.cut_apply_zero_of_le n hy.le
  have := hEq.deriv_eq
  simpa using this

private theorem deriv_cut_eq_zero_of_gt (n : ℕ) {z : ℝ} (hz : 3 * (n + 1 : ℝ) < z) :
    deriv (Work.FTS.EllipticEst.cut n) z = 0 := by
  have hEq : (fun y : ℝ => Work.FTS.EllipticEst.cut n y) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact Work.FTS.EllipticEst.cut_apply_zero_of_ge n hy.le
  have := hEq.deriv_eq
  simpa using this

theorem zibp_cut {u : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ 3 (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (n : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (∫ z in Set.Ioi 0,
        Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.AeI1Fts.Fp u z θ)
      = - (∫ z in Set.Ioi 0,
          (z * deriv (Work.FTS.EllipticEst.cut n) z) * (z * Work.Spaces.pz u z θ)
            * (Work.Spaces.pthIter 2 u z θ) * (Work.Spaces.w z) ^ 2) := by
  have hθo : θ ∈ Iθo := hθ
  have hn : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  -- the compact band containing the support of `χ_n` and `χ_n'`
  set a : ℝ := 1 / (2 * (n + 1 : ℝ)) with ha_def
  set b : ℝ := 4 * (n + 1 : ℝ) with hb_def
  have ha : 0 < a := by rw [ha_def]; positivity
  have hab : a ≤ b := by
    rw [ha_def, hb_def]
    have h1 : 1 / (2 * (n + 1 : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have h2 : (1 : ℝ) ≤ 4 * (n + 1 : ℝ) := by linarith
    linarith
  have hIcc : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le ha hz.1
  have hhalf : 1 / (2 * (n + 1 : ℝ)) ≤ 1 / (n + 1 : ℝ) :=
    one_div_le_one_div_of_le hn (by linarith)
  -- the two support statements
  have hcut_zero : ∀ z, z ∉ Set.Icc a b → Work.FTS.EllipticEst.cut n z = 0 := by
    intro z hz
    simp only [Set.mem_Icc, not_and_or, not_le] at hz
    rcases hz with hzlt | hzgt
    · rw [ha_def] at hzlt
      exact Work.FTS.EllipticEst.cut_apply_zero_of_le n (by linarith)
    · rw [hb_def] at hzgt
      exact Work.FTS.EllipticEst.cut_apply_zero_of_ge n (by linarith)
  have hderivcut_zero : ∀ z, z ∉ Set.Icc a b → deriv (Work.FTS.EllipticEst.cut n) z = 0 := by
    intro z hz
    simp only [Set.mem_Icc, not_and_or, not_le] at hz
    rcases hz with hzlt | hzgt
    · rw [ha_def] at hzlt
      exact deriv_cut_eq_zero_of_lt n (by linarith)
    · rw [hb_def] at hzgt
      exact deriv_cut_eq_zero_of_gt n (by linarith)
  -- integrability of the two products
  have hint1 : IntegrableOn
      (fun z => Work.FTS.EllipticEst.cut n z
        * ((Work.Spaces.w z) ^ 2 * Fp u z θ)) (Set.Ioi 0) := by
    refine integrableOn_Ioi_of_Icc_support ha ?_ (fun z hz => by rw [hcut_zero z hz, zero_mul])
    exact ((((Work.FTS.EllipticEst.cut_contDiff n).continuous.continuousOn).mono hIcc).mul
      ((continuousOn_wSq.mono hIcc).mul ((continuousOn_slice_Fp hu hθo).mono hIcc)))
  have hint2 : IntegrableOn
      (fun z => deriv (Work.FTS.EllipticEst.cut n) z * Fd u z θ) (Set.Ioi 0) := by
    refine integrableOn_Ioi_of_Icc_support ha ?_
      (fun z hz => by rw [hderivcut_zero z hz, zero_mul])
    exact (((continuous_deriv_cut n).continuousOn).mono hIcc).mul
      ((continuousOn_slice_Fd hu hθo).mono hIcc)
  -- the two boundary limits
  have huv0 : Tendsto (fun z => Work.FTS.EllipticEst.cut n z * Fd u z θ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    have hmem : ∀ᶠ z in 𝓝[>] (0 : ℝ), z < 1 / (n + 1 : ℝ) :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (by positivity : (0 : ℝ) < 1 / (n + 1 : ℝ)))
    filter_upwards [hmem] with z hz
    rw [Work.FTS.EllipticEst.cut_apply_zero_of_le n hz.le, zero_mul]
  have huvtop : Tendsto (fun z => Work.FTS.EllipticEst.cut n z * Fd u z θ) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (3 * (n + 1 : ℝ))] with z hz
    rw [Work.FTS.EllipticEst.cut_apply_zero_of_ge n hz, zero_mul]
  -- the integration by parts
  have hIBP := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ))
    (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := fun z : ℝ => Work.FTS.EllipticEst.cut n z)
    (v := fun z : ℝ => Fd u z θ)
    (u' := fun z : ℝ => deriv (Work.FTS.EllipticEst.cut n) z)
    (v' := fun z : ℝ => (Work.Spaces.w z) ^ 2 * Fp u z θ)
    (fun z _ => (cut_differentiable n |>.differentiableAt).hasDerivAt)
    (fun z hz => hasDerivAt_Fd hu hz hθo) hint1 hint2 huv0 huvtop
  rw [show (∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2
        * Fp u z θ)
      = ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z
          * ((Work.Spaces.w z) ^ 2 * Fp u z θ) from
    setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)]
  rw [hIBP]
  rw [show (∫ z in Set.Ioi 0, (z * deriv (Work.FTS.EllipticEst.cut n) z)
        * (z * Work.Spaces.pz u z θ) * (Work.Spaces.pthIter 2 u z θ)
        * (Work.Spaces.w z) ^ 2)
      = ∫ z in Set.Ioi 0, deriv (Work.FTS.EllipticEst.cut n) z * Fd u z θ from
    setIntegral_congr_fun measurableSet_Ioi (fun z _ => by simp only [Fd]; ring)]
  ring

end

end Work.FTS.EllipticEst.AeI1Fts
