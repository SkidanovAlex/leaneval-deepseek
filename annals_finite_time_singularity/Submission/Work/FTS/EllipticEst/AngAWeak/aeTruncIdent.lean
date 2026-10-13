import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.remov.ibpZZ
import Submission.Work.FTS.EllipticEst.remov.ibpZ
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.AngAWeak.aeTruncAux
import Submission.Work.FTS.EllipticEst.AngAWeak.aeUMassBound
import Submission.Work.FTS.EllipticEst.AngAWeak.aeBoxMem
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.HkMemGradU
import Submission.Work.FTS.EllipticEst.H2W.Ae.TruncIdentAe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `aeTruncIdent` — the truncated energy identity in the almost-everywhere class

Target: for `AeData α u G`, a weight `W ∈ C²` with compact support, vanishing near `0`, the
truncated `w²`-energy identity

`∫_z W w² (∫_θ G u) = α² ∫_z W w² z² (∫_θ (∂_zu)²) + ∫_z W w² (∫_θ (L₀u) u)
   - (α²/2) ∫_z (W w² z²)'' (∫_θ u²) + (α(5+α)/2) ∫_z (W w² z)' (∫_θ u²)`

holds.  Here `Iz = [0,∞)`, `Iθ = [0,π/2]`, `w z = (1+z)²/z²`.

## Route

`bslOp α u = G` on the open quadrant, so the left-hand side may be written with `bslOp α u`; for
each fixed `θ ∈ (0,π/2)` the one-dimensional integration by parts in `z` of the slice
`z ↦ u z θ` against the radial weight `σ = W w²` gives (`remov.ibpZZ`, `remov.ibpZ`)

`∫_z σ z² ∂_zzu · u = ½ ∫_z (W w² z²)'' u² - ∫_z W w² z² (∂_zu)²`,
`∫_z σ z ∂_zu · u = -½ ∫_z (W w² z)' u²`

(no boundary terms: `σ` vanishes near `0` and at `∞`).  Integrating in `θ` and swapping the five
double integrals (Fubini) gives the identity.  The joint integrability that Fubini consumes is
supplied by the companion lemmas `aeUMassBound`, `aeBoxMem`, `AeJoint2.aeJointInt`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The `θ`-slice of a function that is smooth on the open quadrant is smooth on `(0,∞)`. -/
theorem contDiffOn_slice_z {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (n : ℕ) :
    ContDiffOn ℝ n (fun z => u z θ) (Set.Ioi 0) := by
  have hmap : MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi 0) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun z hz => ⟨hz, hθ⟩
  have hlin : ContDiffOn ℝ n (fun z : ℝ => (z, θ)) (Set.Ioi 0) := by fun_prop
  have hc := (hsm n).comp hlin hmap
  simpa [Function.comp_def, Function.uncurry] using hc

/-- `(w z)^2` is smooth on `(0,∞)` (`w z = (1+z)^2/z^2`). -/
theorem contDiffOn_wsq : ContDiffOn ℝ 2 (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have h1 : ContDiffOn ℝ 2 (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) := by
    refine ContDiffOn.div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro z hz
      have hz0 : z ≠ 0 := ne_of_gt hz
      positivity
  have h2 : ContDiffOn ℝ 2 (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Ioi 0) := h1.pow 2
  refine h2.congr ?_
  intro z hz
  rw [Work.Spaces.w, div_pow]

/-- A function continuous on `(0,∞)` which vanishes on `(0,δ]` and on `[R,∞)`, with `0 < δ ≤ R`,
is integrable on `(0,∞)`. -/
theorem integrableOn_Ioi_of_support {f : ℝ → ℝ} {δ R : ℝ} (hδ0 : 0 < δ) (hδR : δ ≤ R)
    (hcont : ContinuousOn f (Set.Ioi 0))
    (hδ : ∀ z, z < δ → f z = 0) (hR : ∀ z, R < z → f z = 0) :
    IntegrableOn f (Set.Ioi 0) := by
  have hsub : Set.Icc δ R ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le hδ0 hz.1
  have h1 : IntegrableOn f (Set.Icc δ R) := (hcont.mono hsub).integrableOn_compact isCompact_Icc
  have h2 : IntegrableOn f (Set.Ioo (0 : ℝ) δ) :=
    ((MeasureTheory.integrable_zero ℝ ℝ volume).integrableOn).congr_fun
      (fun z hz => (hδ z hz.2).symm) measurableSet_Ioo
  have h3 : IntegrableOn f (Set.Ioi R) :=
    ((MeasureTheory.integrable_zero ℝ ℝ volume).integrableOn).congr_fun
      (fun z hz => (hR z hz).symm) measurableSet_Ioi
  have hunion : Set.Ioo (0 : ℝ) δ ∪ Set.Icc δ R ∪ Set.Ioi R = Set.Ioi (0 : ℝ) := by
    ext z
    constructor
    · rintro ((hz | hz) | hz)
      · exact hz.1
      · exact lt_of_lt_of_le hδ0 hz.1
      · exact lt_of_lt_of_le hδ0 (le_of_lt (lt_of_le_of_lt hδR hz))
    · intro hz
      rcases lt_or_ge z δ with h | h
      · exact Or.inl (Or.inl ⟨hz, h⟩)
      · rcases le_or_gt z R with h2 | h2
        · exact Or.inl (Or.inr ⟨h, h2⟩)
        · exact Or.inr h2
  rw [← hunion]
  exact (h2.union h1).union h3

/-- `volume.restrict Iz` and `volume.restrict (0,∞)` give the same integrability. -/
theorem integrableOn_Iz_iff_Ioi {f : ℝ → ℝ} :
    IntegrableOn f Work.Spaces.Iz ↔ IntegrableOn f (Set.Ioi 0) := by
  have h : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  change MeasureTheory.Integrable f (MeasureTheory.volume.restrict Work.Spaces.Iz)
    ↔ MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
  rw [h]

/-- A function vanishing on `(0,δ)` has limit `0` at `0⁺` within `(0,∞)`. -/
theorem tendsto_nhdsWithin_zero_of_eq_zero {f : ℝ → ℝ} {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : ∀ z, z < δ → f z = 0) :
    Filter.Tendsto f (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)) (Iio_mem_nhds hδ0)] with z hz
  exact (hδ z hz).symm

/-- A function vanishing on `(R,∞)` has limit `0` at `∞`. -/
theorem tendsto_atTop_zero_of_eq_zero {f : ℝ → ℝ} {R : ℝ}
    (hR : ∀ z, R < z → f z = 0) :
    Filter.Tendsto f Filter.atTop (𝓝 0) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop R] with z hz
  exact (hR z hz).symm

/-- **The `∂_zz`-integration by parts of the truncated identity, slice by slice in `θ`.** -/
theorem sliceIBP_zz (α : ℝ) (u : ℝ → ℝ → ℝ) (W : ℝ → ℝ) (hW2 : ContDiff ℝ 2 W)
    {δ R θ : ℝ} (hδ0 : 0 < δ) (hδR : δ ≤ R) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hδW : ∀ z, z ≤ δ → W z = 0) (hRW : ∀ z, R ≤ z → W z = 0)
    (hslice : ContDiffOn ℝ 2 (fun z => u z θ) (Set.Ioi 0)) :
    (∫ z in Work.Spaces.Iz, (W z * (Work.Spaces.w z) ^ 2 * z ^ 2)
        * (Work.Spaces.pzIter 2 u z θ * u z θ))
      = (1 / 2) * (∫ z in Work.Spaces.Iz,
          deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z * (u z θ) ^ 2)
        - (∫ z in Work.Spaces.Iz, (W z * (Work.Spaces.w z) ^ 2 * z ^ 2)
            * (Work.Spaces.pz u z θ) ^ 2) := by
  set σ : ℝ → ℝ := fun z => W z * (Work.Spaces.w z) ^ 2 with hσdef
  set φ : ℝ → ℝ := fun z => u z θ with hφdef
  have hσsm : ContDiffOn ℝ 2 σ (Set.Ioi 0) := by
    rw [hσdef]; exact hW2.contDiffOn.mul contDiffOn_wsq
  have hσc : ContinuousOn σ (Set.Ioi 0) := hσsm.continuousOn
  have hφc : ContinuousOn φ (Set.Ioi 0) := by rw [hφdef]; exact hslice.continuousOn
  have hφ1sm : ContDiffOn ℝ 1 (deriv φ) (Set.Ioi 0) := by
    rw [hφdef]; exact hslice.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hφ1c : ContinuousOn (deriv φ) (Set.Ioi 0) := hφ1sm.continuousOn
  have hφ2c : ContinuousOn (fun z => deriv (deriv φ) z) (Set.Ioi 0) :=
    (hslice.deriv_of_isOpen (m := 1) isOpen_Ioi (by norm_num)).continuousOn_deriv_of_isOpen
      isOpen_Ioi (by norm_num)
  have hw2c : ContinuousOn (fun z => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
    contDiffOn_wsq.continuousOn
  -- vanishing of `σ` and of its derivatives below `δ` / above `R`
  have hσz : ∀ z, z ≤ δ → σ z = 0 := by
    intro z hz; rw [hσdef]; simp [hδW z hz]
  have hσzR : ∀ z, R ≤ z → σ z = 0 := by
    intro z hz; rw [hσdef]; simp [hRW z hz]
  have hσev : ∀ z, z < δ →
      (fun z' => z' ^ 2 * σ z') =ᶠ[𝓝 z] 0 := by
    intro z hz
    filter_upwards [IsOpen.mem_nhds isOpen_Iio hz] with z' hz'
    simp [hσz z' hz'.le]
  have hσevR : ∀ z, R < z →
      (fun z' => z' ^ 2 * σ z') =ᶠ[𝓝 z] 0 := by
    intro z hz
    filter_upwards [IsOpen.mem_nhds isOpen_Ioi hz] with z' hz'
    simp [hσzR z' hz'.le]
  have hd1 : ∀ z, z < δ → deriv (fun z' => z' ^ 2 * σ z') z = 0 := by
    intro z hz; rw [(hσev z hz).deriv_eq]; simp
  have hd1R : ∀ z, R < z → deriv (fun z' => z' ^ 2 * σ z') z = 0 := by
    intro z hz; rw [(hσevR z hz).deriv_eq]; simp
  have hd2 : ∀ z, z < δ → deriv (deriv (fun z' => z' ^ 2 * σ z')) z = 0 := by
    intro z hz
    have hev : (fun z' => deriv (fun z'' => z'' ^ 2 * σ z'') z') =ᶠ[𝓝 z] 0 := by
      filter_upwards [IsOpen.mem_nhds isOpen_Iio hz] with z' hz'
      exact hd1 z' hz'
    rw [hev.deriv_eq]; simp
  have hd2R : ∀ z, R < z → deriv (deriv (fun z' => z' ^ 2 * σ z')) z = 0 := by
    intro z hz
    have hev : (fun z' => deriv (fun z'' => z'' ^ 2 * σ z'') z') =ᶠ[𝓝 z] 0 := by
      filter_upwards [IsOpen.mem_nhds isOpen_Ioi hz] with z' hz'
      exact hd1R z' hz'
    rw [hev.deriv_eq]; simp
  -- continuity of the four integrands of `ibpZZ`
  have hσ2 : ContDiffOn ℝ 2 (fun z : ℝ => z ^ 2 * σ z) (Set.Ioi 0) :=
    (by fun_prop : ContDiffOn ℝ 2 (fun z : ℝ => z ^ 2) (Set.Ioi 0)).mul hσsm
  have hdσ1c : ContinuousOn (fun z => deriv (fun z' => z' ^ 2 * σ z') z) (Set.Ioi 0) :=
    hσ2.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hdσ2c : ContinuousOn (fun z => deriv (deriv (fun z' => z' ^ 2 * σ z')) z) (Set.Ioi 0) :=
    (hσ2.deriv_of_isOpen (m := 1) isOpen_Ioi (by norm_num)).continuousOn_deriv_of_isOpen
      isOpen_Ioi (by norm_num)
  have hc1 : ContinuousOn (fun z => z ^ 2 * σ z * φ z * deriv (deriv φ) z) (Set.Ioi 0) :=
    (((continuousOn_id.pow 2).mul hσc).mul hφc).mul hφ2c
  have hc2 : ContinuousOn (fun z => deriv (fun z' => z' ^ 2 * σ z') z * φ z * deriv φ z)
      (Set.Ioi 0) :=
    (hdσ1c.mul hφc).mul hφ1c
  have hc3 : ContinuousOn (fun z => σ z * (z * deriv φ z) ^ 2) (Set.Ioi 0) :=
    hσc.mul ((continuousOn_id.mul hφ1c).pow 2)
  have hc4 : ContinuousOn (fun z => deriv (deriv (fun z' => z' ^ 2 * σ z')) z * φ z ^ 2)
      (Set.Ioi 0) :=
    hdσ2c.mul (hφc.pow 2)
  -- integrability
  have hi1 : IntegrableOn (fun z => z ^ 2 * σ z * φ z * deriv (deriv φ) z) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support hδ0 hδR hc1
      (fun z hz => by rw [hσz z hz.le]; ring)
      (fun z hz => by rw [hσzR z hz.le]; ring)
  have hi2 : IntegrableOn (fun z => deriv (fun z' => z' ^ 2 * σ z') z * φ z * deriv φ z)
      (Set.Ioi 0) :=
    integrableOn_Ioi_of_support hδ0 hδR hc2
      (fun z hz => by rw [hd1 z hz]; ring)
      (fun z hz => by rw [hd1R z hz]; ring)
  have hi3 : IntegrableOn (fun z => σ z * (z * deriv φ z) ^ 2) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support hδ0 hδR hc3
      (fun z hz => by rw [hσz z hz.le]; ring)
      (fun z hz => by rw [hσzR z hz.le]; ring)
  have hi4 : IntegrableOn (fun z => deriv (deriv (fun z' => z' ^ 2 * σ z')) z * φ z ^ 2)
      (Set.Ioi 0) :=
    integrableOn_Ioi_of_support hδ0 hδR hc4
      (fun z hz => by rw [hd2 z hz]; ring)
      (fun z hz => by rw [hd2R z hz]; ring)
  -- boundary limits
  have hb0 : Filter.Tendsto (fun z => z ^ 2 * σ z * φ z * deriv φ z)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
    tendsto_nhdsWithin_zero_of_eq_zero hδ0 (fun z hz => by rw [hσz z hz.le]; ring)
  have hbT : Filter.Tendsto (fun z => z ^ 2 * σ z * φ z * deriv φ z) Filter.atTop (𝓝 0) :=
    tendsto_atTop_zero_of_eq_zero (fun z hz => by rw [hσzR z hz.le]; ring)
  have hb0' : Filter.Tendsto (fun z => deriv (fun z' => z' ^ 2 * σ z') z * φ z ^ 2)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
    tendsto_nhdsWithin_zero_of_eq_zero hδ0 (fun z hz => by rw [hd1 z hz]; ring)
  have hbT' : Filter.Tendsto (fun z => deriv (fun z' => z' ^ 2 * σ z') z * φ z ^ 2)
      Filter.atTop (𝓝 0) :=
    tendsto_atTop_zero_of_eq_zero (fun z hz => by rw [hd1R z hz]; ring)
  have hmain := Work.FTS.EllipticEst.remov.ibpZZ σ φ hσsm (by rw [hφdef]; exact hslice)
    hi1 hi2 hi3 hi4 hb0 hbT hb0' hbT'
  -- rewrite the four integrals into the shapes of the statement
  rw [hσdef, hφdef] at hmain
  have e1 : (∫ z in Set.Ioi (0 : ℝ), (fun z => W z * (Work.Spaces.w z) ^ 2) z * z ^ 2
        * deriv (deriv (fun z => u z θ)) z * u z θ)
      = ∫ z in Work.Spaces.Iz, (W z * (Work.Spaces.w z) ^ 2 * z ^ 2)
          * (Work.Spaces.pzIter 2 u z θ * u z θ) := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [show deriv (deriv (fun z => u z θ)) z = Work.Spaces.pzIter 2 u z θ from rfl]
    ring
  have e2 : (∫ z in Set.Ioi (0 : ℝ),
        deriv (deriv (fun z => z ^ 2 * (W z * (Work.Spaces.w z) ^ 2))) z * (u z θ) ^ 2)
      = ∫ z in Work.Spaces.Iz,
          deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z * (u z θ) ^ 2 := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [show (fun z' => z' ^ 2 * (W z' * (Work.Spaces.w z') ^ 2))
        = fun z' => W z' * (Work.Spaces.w z') ^ 2 * z' ^ 2 from by funext z'; ring]
  have e3 : (∫ z in Set.Ioi (0 : ℝ), (fun z => W z * (Work.Spaces.w z) ^ 2) z
        * (z * deriv (fun z' => u z' θ) z) ^ 2)
      = ∫ z in Work.Spaces.Iz, (W z * (Work.Spaces.w z) ^ 2 * z ^ 2)
          * (Work.Spaces.pz u z θ) ^ 2 := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [show deriv (fun z' => u z' θ) z = Work.Spaces.pz u z θ from rfl]
    ring
  rw [e1, e2, e3] at hmain
  exact hmain

/-- **The `∂_z`-integration by parts of the truncated identity, slice by slice in `θ`.** -/
theorem sliceIBP_z (α : ℝ) (u : ℝ → ℝ → ℝ) (W : ℝ → ℝ) (hW2 : ContDiff ℝ 2 W)
    {δ R θ : ℝ} (hδ0 : 0 < δ) (hδR : δ ≤ R) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hδW : ∀ z, z ≤ δ → W z = 0) (hRW : ∀ z, R ≤ z → W z = 0)
    (hslice : ContDiffOn ℝ 2 (fun z => u z θ) (Set.Ioi 0)) :
    (∫ z in Work.Spaces.Iz, (W z * (Work.Spaces.w z) ^ 2 * z)
        * (Work.Spaces.pz u z θ * u z θ))
      = -(1 / 2) * (∫ z in Work.Spaces.Iz,
          deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2) := by
  have hσsm : ContDiffOn ℝ 2 (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
    hW2.contDiffOn.mul contDiffOn_wsq
  have hσc : ContinuousOn (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
    hσsm.continuousOn
  have hφc : ContinuousOn (fun z : ℝ => u z θ) (Set.Ioi 0) := hslice.continuousOn
  have hφ1c : ContinuousOn (deriv (fun z : ℝ => u z θ)) (Set.Ioi 0) :=
    (hslice.deriv_of_isOpen (m := 1) isOpen_Ioi (by norm_num)).continuousOn
  have hσz : ∀ z, z ≤ δ → W z * (Work.Spaces.w z) ^ 2 = 0 := by
    intro z hz; rw [hδW z hz]; ring
  have hσzR : ∀ z, R ≤ z → W z * (Work.Spaces.w z) ^ 2 = 0 := by
    intro z hz; rw [hRW z hz]; ring
  have hσev : ∀ z, z < δ → (fun z' => z' * (W z' * (Work.Spaces.w z') ^ 2)) =ᶠ[𝓝 z] 0 := by
    intro z hz
    filter_upwards [IsOpen.mem_nhds isOpen_Iio hz] with z' hz'
    simp [hσz z' hz'.le]
  have hσevR : ∀ z, R < z → (fun z' => z' * (W z' * (Work.Spaces.w z') ^ 2)) =ᶠ[𝓝 z] 0 := by
    intro z hz
    filter_upwards [IsOpen.mem_nhds isOpen_Ioi hz] with z' hz'
    simp [hσzR z' hz'.le]
  have hd1 : ∀ z, z < δ → deriv (fun z' => z' * (W z' * (Work.Spaces.w z') ^ 2)) z = 0 := by
    intro z hz; rw [(hσev z hz).deriv_eq]; simp
  have hd1R : ∀ z, R < z → deriv (fun z' => z' * (W z' * (Work.Spaces.w z') ^ 2)) z = 0 := by
    intro z hz; rw [(hσevR z hz).deriv_eq]; simp
  have hσzs : ContDiffOn ℝ 2 (fun z : ℝ => z * (W z * (Work.Spaces.w z) ^ 2)) (Set.Ioi 0) :=
    (by fun_prop : ContDiffOn ℝ 2 (fun z : ℝ => z) (Set.Ioi 0)).mul hσsm
  have hi1 : IntegrableOn (fun z => z * (W z * (Work.Spaces.w z) ^ 2) * u z θ
      * deriv (fun z => u z θ) z) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support hδ0 hδR
      (((((by fun_prop : ContinuousOn (fun z : ℝ => z) (Set.Ioi 0)).mul hσc).mul hφc).mul hφ1c).congr fun z _ => rfl)
      (fun z hz => by rw [hσz z hz.le]; ring)
      (fun z hz => by rw [hσzR z hz.le]; ring)
  have hi2 : IntegrableOn (fun z => deriv (fun z' => z' * (W z' * (Work.Spaces.w z') ^ 2)) z
      * (u z θ) ^ 2) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support hδ0 hδR
      ((hσzs.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mul (hφc.pow 2))
      (fun z hz => by rw [hd1 z hz]; ring)
      (fun z hz => by rw [hd1R z hz]; ring)
  have hb0 : Filter.Tendsto (fun z => z * (W z * (Work.Spaces.w z) ^ 2) * (u z θ) ^ 2)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
    tendsto_nhdsWithin_zero_of_eq_zero hδ0 (fun z hz => by rw [hσz z hz.le]; ring)
  have hbT : Filter.Tendsto (fun z => z * (W z * (Work.Spaces.w z) ^ 2) * (u z θ) ^ 2)
      Filter.atTop (𝓝 0) :=
    tendsto_atTop_zero_of_eq_zero (fun z hz => by rw [hσzR z hz.le]; ring)
  have hmain := Work.FTS.EllipticEst.remov.ibpZ
    (fun z => W z * (Work.Spaces.w z) ^ 2) (fun z => u z θ) hσsm hslice
    hi1 hi2 hb0 hbT
  have e1 : (∫ z in Set.Ioi (0 : ℝ), (W z * (Work.Spaces.w z) ^ 2)
        * (z * deriv (fun z => u z θ) z) * u z θ)
      = ∫ z in Work.Spaces.Iz, (W z * (Work.Spaces.w z) ^ 2 * z)
          * (Work.Spaces.pz u z θ * u z θ) := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [show deriv (fun z => u z θ) z = Work.Spaces.pz u z θ from rfl]
    ring
  have e2 : (∫ z in Set.Ioi (0 : ℝ),
        deriv (fun z' => z' * (W z' * (Work.Spaces.w z') ^ 2)) z * (u z θ) ^ 2)
      = ∫ z in Work.Spaces.Iz,
          deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2 := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [show (fun z' => z' * (W z' * (Work.Spaces.w z') ^ 2))
        = fun z' => W z' * (Work.Spaces.w z') ^ 2 * z' from by funext z'; ring]
  rw [e1, e2] at hmain
  exact hmain

/-- **The truncated energy identity, slice by slice in `θ`.**  `hIntL` is the (a.e.-in-`θ`)
integrability of the `L₀`-pairing, which is what the joint integrability of the parent theorem
supplies. -/
theorem sliceIBP (α : ℝ) (u : ℝ → ℝ → ℝ) (W : ℝ → ℝ) (hW2 : ContDiff ℝ 2 W)
    {δ R θ : ℝ} (hδ0 : 0 < δ) (hδR : δ ≤ R) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hδW : ∀ z, z ≤ δ → W z = 0) (hRW : ∀ z, R ≤ z → W z = 0)
    (hslice : ContDiffOn ℝ 2 (fun z => u z θ) (Set.Ioi 0))
    (hIntL : IntegrableOn (fun z => W z * (Work.Spaces.w z) ^ 2
        * (Work.Elliptic.Lzero u z θ * u z θ)) Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
        * (Work.Elliptic.bslOp α u z θ * u z θ))
      = α ^ 2 * (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2 * z ^ 2
            * (Work.Spaces.pz u z θ) ^ 2)
        + (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
            * (Work.Elliptic.Lzero u z θ * u z θ))
        - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
            deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z * (u z θ) ^ 2)
        + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
            deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2) := by
  have hσc : ContinuousOn (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
    (hW2.contDiffOn.mul contDiffOn_wsq).continuousOn
  have hφc : ContinuousOn (fun z : ℝ => u z θ) (Set.Ioi 0) := hslice.continuousOn
  have hφ1c : ContinuousOn (deriv (fun z : ℝ => u z θ)) (Set.Ioi 0) :=
    (hslice.deriv_of_isOpen (m := 1) isOpen_Ioi (by norm_num)).continuousOn
  have hφ2c : ContinuousOn (fun z => deriv (deriv (fun z : ℝ => u z θ)) z) (Set.Ioi 0) :=
    ((hslice.deriv_of_isOpen (m := 1) isOpen_Ioi (by norm_num))).continuousOn_deriv_of_isOpen
      isOpen_Ioi (by norm_num)
  have hσz : ∀ z, z ≤ δ → W z * (Work.Spaces.w z) ^ 2 = 0 := by
    intro z hz; rw [hδW z hz]; ring
  have hσzR : ∀ z, R ≤ z → W z * (Work.Spaces.w z) ^ 2 = 0 := by
    intro z hz; rw [hRW z hz]; ring
  -- integrability of the two radial pieces
  have hcontA : ContinuousOn (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2
      * (Work.Spaces.pzIter 2 u z θ * u z θ)) (Set.Ioi 0) :=
    ((hσc.mul (by fun_prop : ContinuousOn (fun z : ℝ => z ^ 2) (Set.Ioi 0))).congr (fun z _ => by simp only [Pi.mul_apply])).mul
      (hφ2c.mul hφc)
  have hcontB : ContinuousOn (fun z => W z * (Work.Spaces.w z) ^ 2 * z
      * (Work.Spaces.pz u z θ * u z θ)) (Set.Ioi 0) :=
    ((hσc.mul (by fun_prop : ContinuousOn (fun z : ℝ => z) (Set.Ioi 0))).congr (fun z _ => by simp only [Pi.mul_apply])).mul (hφ1c.mul hφc)
  have hIA : IntegrableOn (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2
      * (Work.Spaces.pzIter 2 u z θ * u z θ)) Work.Spaces.Iz := by
    rw [integrableOn_Iz_iff_Ioi]
    exact integrableOn_Ioi_of_support hδ0 hδR hcontA
      (fun z hz => by rw [hσz z hz.le]; ring)
      (fun z hz => by rw [hσzR z hz.le]; ring)
  have hIB : IntegrableOn (fun z => W z * (Work.Spaces.w z) ^ 2 * z
      * (Work.Spaces.pz u z θ * u z θ)) Work.Spaces.Iz := by
    rw [integrableOn_Iz_iff_Ioi]
    exact integrableOn_Ioi_of_support hδ0 hδR hcontB
      (fun z hz => by rw [hσz z hz.le]; ring)
      (fun z hz => by rw [hσzR z hz.le]; ring)
  have hA2 : IntegrableOn (fun z => α ^ 2 * ((W z * (Work.Spaces.w z) ^ 2 * z ^ 2)
      * (Work.Spaces.pzIter 2 u z θ * u z θ))) Work.Spaces.Iz := hIA.const_mul _
  have hB2 : IntegrableOn (fun z => (α * (5 + α)) * ((W z * (Work.Spaces.w z) ^ 2 * z)
      * (Work.Spaces.pz u z θ * u z θ))) Work.Spaces.Iz := hIB.const_mul _
  have hAB2 : IntegrableOn (fun z => α ^ 2 * ((W z * (Work.Spaces.w z) ^ 2 * z ^ 2)
      * (Work.Spaces.pzIter 2 u z θ * u z θ))
        + (α * (5 + α)) * ((W z * (Work.Spaces.w z) ^ 2 * z)
      * (Work.Spaces.pz u z θ * u z θ))) Work.Spaces.Iz := hA2.add hB2
  have hkey : (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
        * (Work.Elliptic.bslOp α u z θ * u z θ))
      = (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
            * (Work.Elliptic.Lzero u z θ * u z θ))
        - (α ^ 2 * (∫ z in Work.Spaces.Iz, (W z * (Work.Spaces.w z) ^ 2 * z ^ 2)
              * (Work.Spaces.pzIter 2 u z θ * u z θ))
          + (α * (5 + α)) * (∫ z in Work.Spaces.Iz, (W z * (Work.Spaces.w z) ^ 2 * z)
              * (Work.Spaces.pz u z θ * u z θ))) := by
    rw [show (fun z => W z * (Work.Spaces.w z) ^ 2
          * (Work.Elliptic.bslOp α u z θ * u z θ))
        = fun z => W z * (Work.Spaces.w z) ^ 2 * (Work.Elliptic.Lzero u z θ * u z θ)
            - (α ^ 2 * ((W z * (Work.Spaces.w z) ^ 2 * z ^ 2)
                * (Work.Spaces.pzIter 2 u z θ * u z θ))
              + (α * (5 + α)) * ((W z * (Work.Spaces.w z) ^ 2 * z)
                * (Work.Spaces.pz u z θ * u z θ))) from by
      funext z; rw [Work.Elliptic.bslOp_apply]; ring]
    simp only [MeasureTheory.integral_sub hIntL hAB2, MeasureTheory.integral_add hA2 hB2,
      MeasureTheory.integral_const_mul]
  rw [hkey]
  simp only [sliceIBP_zz α u W hW2 hδ0 hδR hθ hδW hRW hslice,
    sliceIBP_z α u W hW2 hδ0 hδR hθ hδW hRW hslice]
  ring

/-- **The truncated energy identity**, in the form in which `Fubini` is applied: the angular
integration is over the *open* interval `(0,π/2)`, and the five joint integrability statements
are hypotheses. -/
theorem aeTruncIdent_core (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (W : ℝ → ℝ) (hW2 : ContDiff ℝ 2 W)
    (δ R : ℝ) (hδ0 : 0 < δ) (hδR : δ ≤ R)
    (hδW : ∀ z, z ≤ δ → W z = 0) (hRW : ∀ z, R ≤ z → W z = 0)
    (hJ1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => W p.1 * (Work.Spaces.w p.1) ^ 2
        * (Work.Elliptic.bslOp α u p.1 p.2 * u p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))))
    (hJ2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => W p.1 * (Work.Spaces.w p.1) ^ 2 * p.1 ^ 2
        * (Work.Spaces.pz u p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))))
    (hJ3 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) p.1 * (u p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))))
    (hJ4 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) p.1 * (u p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))))
    (hJ5 : MeasureTheory.Integrable (fun p : ℝ × ℝ => W p.1 * (Work.Spaces.w p.1) ^ 2
        * (Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))) :
    (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), G z θ * u z θ))
      = α ^ 2 * (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2 * z ^ 2
            * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Work.Spaces.pz u z θ) ^ 2))
        + (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
            * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.Elliptic.Lzero u z θ * u z θ))
        - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
            deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
              * (∫ θ in Set.Ioo 0 (Real.pi / 2), (u z θ) ^ 2))
        + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
            deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z
              * (∫ θ in Set.Ioo 0 (Real.pi / 2), (u z θ) ^ 2)) := by
  -- ## Step 1: replace `G` by `bslOp α u` in the left-hand side
  have hbsl : (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), G z θ * u z θ))
      = ∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.Elliptic.bslOp α u z θ * u z θ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z hz => ?_
    by_cases hzδ : z ≤ δ
    · rw [hδW z hzδ]; ring
    · have hz0 : 0 < z := lt_of_lt_of_le hδ0 (le_of_lt (lt_of_not_ge hzδ))
      congr 1
      exact MeasureTheory.integral_congr_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => by
          show G z θ * u z θ = Work.Elliptic.bslOp α u z θ * u z θ
          rw [h.eq z hz0 θ hθ.1 hθ.2]))
  -- ## Step 2: Fubini on the left-hand side
  have hfub1 : (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.Elliptic.bslOp α u z θ * u z θ))
      = ∫ θ in Set.Ioo 0 (Real.pi / 2), ∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
        * (Work.Elliptic.bslOp α u z θ * u z θ) := by
    rw [show (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.Elliptic.bslOp α u z θ * u z θ))
        = (∫ z in Work.Spaces.Iz, ∫ θ in Set.Ioo 0 (Real.pi / 2),
            W z * (Work.Spaces.w z) ^ 2 * (Work.Elliptic.bslOp α u z θ * u z θ)) from by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
      rw [MeasureTheory.integral_const_mul]]
    exact MeasureTheory.integral_integral_swap
      (f := fun z θ => W z * (Work.Spaces.w z) ^ 2
        * (Work.Elliptic.bslOp α u z θ * u z θ))
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) hJ1
  -- ## Step 3: the slicewise identity, a.e. in `θ`
  have hslice_lz : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))),
      IntegrableOn (fun z => W z * (Work.Spaces.w z) ^ 2
        * (Work.Elliptic.Lzero u z θ * u z θ)) Work.Spaces.Iz :=
    hJ5.prod_left_ae
  have hper : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))),
      (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
          * (Work.Elliptic.bslOp α u z θ * u z θ))
        = α ^ 2 * (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2 * z ^ 2
              * (Work.Spaces.pz u z θ) ^ 2)
          + (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
              * (Work.Elliptic.Lzero u z θ * u z θ))
          - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
              deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z * (u z θ) ^ 2)
          + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
              deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo] at hslice_lz ⊢
    filter_upwards [hslice_lz] with θ hIntL hθmem
    exact sliceIBP α u W hW2 hδ0 hδR hθmem hδW hRW
      (contDiffOn_slice_z h.smooth hθmem 2) (hIntL hθmem)
  -- ## Step 4: integrate in `θ` and use linearity
  have hI2 : MeasureTheory.Integrable (fun θ => ∫ z in Work.Spaces.Iz,
      W z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := hJ2.integral_prod_right
  have hI3 : MeasureTheory.Integrable (fun θ => ∫ z in Work.Spaces.Iz,
      deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z * (u z θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := hJ3.integral_prod_right
  have hI4 : MeasureTheory.Integrable (fun θ => ∫ z in Work.Spaces.Iz,
      deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := hJ4.integral_prod_right
  have hI5 : MeasureTheory.Integrable (fun θ => ∫ z in Work.Spaces.Iz,
      W z * (Work.Spaces.w z) ^ 2 * (Work.Elliptic.Lzero u z θ * u z θ))
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := hJ5.integral_prod_right
  have hcomb : (∫ θ in Set.Ioo 0 (Real.pi / 2), ∫ z in Work.Spaces.Iz,
        W z * (Work.Spaces.w z) ^ 2 * (Work.Elliptic.bslOp α u z θ * u z θ))
      = ∫ θ in Set.Ioo 0 (Real.pi / 2), (α ^ 2 * (∫ z in Work.Spaces.Iz,
              W z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2)
          + (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
              * (Work.Elliptic.Lzero u z θ * u z θ))
          - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
              deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z * (u z θ) ^ 2)
          + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
              deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2)) :=
    MeasureTheory.integral_congr_ae hper
  have hI2' : MeasureTheory.Integrable (fun θ => α ^ 2 * (∫ z in Work.Spaces.Iz,
      W z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := hI2.const_mul _
  have hI3' : MeasureTheory.Integrable (fun θ => (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
      deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z * (u z θ) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := hI3.const_mul _
  have hI4' : MeasureTheory.Integrable (fun θ => (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
      deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := hI4.const_mul _
  have hAB' : MeasureTheory.Integrable (fun θ => α ^ 2 * (∫ z in Work.Spaces.Iz,
      W z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2)
        + (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
            * (Work.Elliptic.Lzero u z θ * u z θ)))
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := hI2'.add hI5
  have hABC' : MeasureTheory.Integrable (fun θ => (α ^ 2 * (∫ z in Work.Spaces.Iz,
      W z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2)
        + (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
            * (Work.Elliptic.Lzero u z θ * u z θ)))
        - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
            deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z * (u z θ) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := hAB'.sub hI3'
  have hlin : (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (α ^ 2 * (∫ z in Work.Spaces.Iz,
            W z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2)
          + (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
              * (Work.Elliptic.Lzero u z θ * u z θ))
          - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
              deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z * (u z θ) ^ 2)
          + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
              deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2)))
      = α ^ 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), ∫ z in Work.Spaces.Iz,
            W z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2)
        + (∫ θ in Set.Ioo 0 (Real.pi / 2), ∫ z in Work.Spaces.Iz,
            W z * (Work.Spaces.w z) ^ 2 * (Work.Elliptic.Lzero u z θ * u z θ))
        - (α ^ 2 / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2), ∫ z in Work.Spaces.Iz,
            deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z * (u z θ) ^ 2)
        + (α * (5 + α) / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2), ∫ z in Work.Spaces.Iz,
            deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2) := by
    simp only [MeasureTheory.integral_add hABC' hI4', MeasureTheory.integral_sub hAB' hI3',
      MeasureTheory.integral_add hI2' hI5, MeasureTheory.integral_const_mul]
  rw [hbsl, hfub1, hcomb, hlin]
  -- ## Step 5: Fubini back for the four terms
  have f1 : (∫ θ in Set.Ioo 0 (Real.pi / 2), ∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
        * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2)
      = ∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2 * z ^ 2
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Work.Spaces.pz u z θ) ^ 2) := by
    rw [← MeasureTheory.integral_integral_swap hJ2]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [MeasureTheory.integral_const_mul]
  have f2 : (∫ θ in Set.Ioo 0 (Real.pi / 2), ∫ z in Work.Spaces.Iz,
        deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z * (u z θ) ^ 2)
      = ∫ z in Work.Spaces.Iz,
          deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
            * (∫ θ in Set.Ioo 0 (Real.pi / 2), (u z θ) ^ 2) := by
    rw [← MeasureTheory.integral_integral_swap hJ3]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [MeasureTheory.integral_const_mul]
  have f3 : (∫ θ in Set.Ioo 0 (Real.pi / 2), ∫ z in Work.Spaces.Iz,
        deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2)
      = ∫ z in Work.Spaces.Iz,
          deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z
            * (∫ θ in Set.Ioo 0 (Real.pi / 2), (u z θ) ^ 2) := by
    rw [← MeasureTheory.integral_integral_swap hJ4]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [MeasureTheory.integral_const_mul]
  have f4 : (∫ θ in Set.Ioo 0 (Real.pi / 2), ∫ z in Work.Spaces.Iz,
        W z * (Work.Spaces.w z) ^ 2 * (Work.Elliptic.Lzero u z θ * u z θ))
      = ∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.Elliptic.Lzero u z θ * u z θ) := by
    rw [← MeasureTheory.integral_integral_swap hJ5]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [MeasureTheory.integral_const_mul]
  rw [f1, f2, f3, f4]

theorem aeTruncIdent : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    ∀ W : ℝ → ℝ, ContDiff ℝ 2 W → HasCompactSupport W →
      (∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, z ≤ δ → W z = 0) →
      (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, G z θ * u z θ))
        = α ^ 2 * (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2 * z ^ 2
              * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz u z θ) ^ 2))
          + (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
              * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ))
          - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
              deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
                * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))
          + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
              deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z
                * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)) := by
  intro α u G hAe W hW2 hcpt hδex
  exact Work.FTS.EllipticEst.H2W.Ae.TruncIdentAe α u G hAe
    (Work.FTS.EllipticEst.H2W.AngBW.S3.hkMem_u α u G hAe)
    (Work.FTS.EllipticEst.H2W.AngBW.S3.hkMem_gradU α u G hAe)
    W hW2 hcpt hδex

end Work.FTS.EllipticEst.AngAWeak
