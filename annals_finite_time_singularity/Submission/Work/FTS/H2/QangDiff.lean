import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.H2.QangAux
import Submission.Work.FTS.H2.QangBox

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

/-! ## The primitive identity for the angular moments

`Qang g j` is a primitive of `x ↦ Qang g (j+1) x / x` on `(0,∞)`, for `j ≤ 3`.  This is the
identity from which both halves of `QangDiff` follow. -/

/-- **The primitive identity for `z₀ ≤ z`.**  For every `j ≤ 3` and `0 < z₀ ≤ z`,

  `Qang g j z - Qang g j z₀ = ∫_{z₀}^{z} Qang g (j+1) x / x dx`.

The proof integrates the slice formula
`D_z^j g z θ - D_z^j g z₀ θ = ∫_{z₀}^{z} D_z^{j+1} g x θ / x dx`
(`QangSliceFTC`) against `Ktheta` and swaps the two integrations with Fubini on the box
`uIoc z₀ z ×ˢ uIoc 0 (π/2)`, whose joint integrability is `QangBoxIntegrable`. -/
theorem Qang_primitive_le (α : ℝ) (g : ℝ → ℝ → ℝ) (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) {j : ℕ} (hj : j ≤ 3) {z z₀ : ℝ} (hz : 0 < z)
    (hz₀ : 0 < z₀) (hle : z₀ ≤ z) :
    Work.Elliptic.Qang g j z - Work.Elliptic.Qang g j z₀
      = ∫ x in z₀..z, Work.Elliptic.Qang g (j + 1) x / x := by
  -- integral integrability of the two angular slices over `0..π/2`
  have hslice : ∀ {w : ℝ}, 0 < w →
      IntervalIntegrable (fun θ : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g w θ)
        volume 0 (π/2) := by
    intro w hw
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ π / 2)]
    refine (QangSliceIntegrable hsm hmem (by omega : j ≤ 4) hw).mono_set ?_
    rw [Work.Spaces.Iθ]
    exact Set.Ioc_subset_Icc_self
  have hIi_z := hslice hz
  have hIi_z₀ := hslice hz₀
  -- Step 1: split the difference of the two θ-integrals
  have h1 : Work.Elliptic.Qang g j z - Work.Elliptic.Qang g j z₀
      = ∫ θ in (0 : ℝ)..(π / 2), (Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ
          - Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z₀ θ) := by
    rw [Qang_eq_intervalIntegral g j z, Qang_eq_intervalIntegral g j z₀]
    exact (intervalIntegral.integral_sub hIi_z hIi_z₀).symm
  -- Step 2: factor out the angular weight
  have h2 : (∫ θ in (0 : ℝ)..(π / 2), (Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ
        - Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z₀ θ))
      = ∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.Ktheta θ
          * (Work.Spaces.DzIter j g z θ - Work.Spaces.DzIter j g z₀ θ) := by
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    ring
  -- Step 3: the slice formula
  have h3 : (∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.Ktheta θ
        * (Work.Spaces.DzIter j g z θ - Work.Spaces.DzIter j g z₀ θ))
      = ∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.Ktheta θ
          * (∫ x in z₀..z, Work.Spaces.DzIter (j + 1) g x θ / x) := by
    refine intervalIntegral.integral_congr_ae ?_
    refine ae_imp_uIoc (fun θ hθ1 hθ2 => ?_)
    rw [QangSliceFTC hsm j hz hz₀ ⟨hθ1, hθ2⟩]
  -- Step 4: pull the angular weight inside the inner integral
  have h4 : (∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.Ktheta θ
        * (∫ x in z₀..z, Work.Spaces.DzIter (j + 1) g x θ / x))
      = ∫ θ in (0 : ℝ)..(π / 2), ∫ x in z₀..z,
          Work.Elliptic.Ktheta θ * (Work.Spaces.DzIter (j + 1) g x θ / x) := by
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    exact (intervalIntegral.integral_const_mul (Work.Elliptic.Ktheta θ)
      (fun x => Work.Spaces.DzIter (j + 1) g x θ / x)).symm
  -- Step 5: Fubini on the box
  have hFbox : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
        * (Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1))
      (Set.uIoc z₀ z ×ˢ Set.uIoc 0 (π / 2)) :=
    (QangBoxIntegrable hsm hmem hj hz₀ hle).1.congr_fun (fun p _ => by ring)
      ((measurableSet_uIoc).prod measurableSet_uIoc)
  have h5 : (∫ θ in (0 : ℝ)..(π / 2), ∫ x in z₀..z,
        Work.Elliptic.Ktheta θ * (Work.Spaces.DzIter (j + 1) g x θ / x))
      = ∫ x in z₀..z, ∫ θ in (0 : ℝ)..(π / 2),
          Work.Elliptic.Ktheta θ * (Work.Spaces.DzIter (j + 1) g x θ / x) :=
    (MeasureTheory.intervalIntegral_intervalIntegral_swap
      (F := fun x θ => Work.Elliptic.Ktheta θ
        * (Work.Spaces.DzIter (j + 1) g x θ / x)) hFbox).symm
  -- Step 6: identify the inner integral with `Qang g (j+1) x / x`
  have h6 : (∫ x in z₀..z, ∫ θ in (0 : ℝ)..(π / 2),
        Work.Elliptic.Ktheta θ * (Work.Spaces.DzIter (j + 1) g x θ / x))
      = ∫ x in z₀..z, Work.Elliptic.Qang g (j + 1) x / x := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    have hq : Work.Elliptic.Qang g (j + 1) x
        = ∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.Ktheta θ * Work.Spaces.DzIter (j + 1) g x θ :=
      Qang_eq_intervalIntegral g (j + 1) x
    have hfun : (fun θ : ℝ => Work.Elliptic.Ktheta θ
          * (Work.Spaces.DzIter (j + 1) g x θ / x))
        = fun θ : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter (j + 1) g x θ / x := by
      funext θ; ring
    rw [hfun, hq, intervalIntegral.integral_div]
  rw [h1, h2, h3, h4, h5, h6]

/-- **The primitive identity.**  For every `j ≤ 3` and every `z, z₀ > 0`,

  `Qang g j z - Qang g j z₀ = ∫_{z₀}^{z} Qang g (j+1) x / x dx`. -/
theorem Qang_primitive (α : ℝ) (g : ℝ → ℝ → ℝ) (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) {j : ℕ} (hj : j ≤ 3) {z z₀ : ℝ} (hz : 0 < z)
    (hz₀ : 0 < z₀) :
    Work.Elliptic.Qang g j z - Work.Elliptic.Qang g j z₀
      = ∫ x in z₀..z, Work.Elliptic.Qang g (j + 1) x / x := by
  rcases le_total z₀ z with hle | hle
  · exact Qang_primitive_le α g hsm hmem hj hz hz₀ hle
  · have h := Qang_primitive_le α g hsm hmem hj hz₀ hz hle
    rw [intervalIntegral.integral_symm z₀ z] at h
    linarith [h]

/-- `z ↦ Qang g (j+1) z / z` is continuous at every `z > 0`, for `j ≤ 2`: this is the
integrand of the primitive identity, and it is continuous because `Qang g (j+1)` is
(`j + 1 ≤ 3`) and `z ≠ 0`. -/
theorem continuousAt_Qang_div {g : ℝ → ℝ → ℝ} {j : ℕ} {z : ℝ}
    (hcont : ContinuousOn (fun w => Work.Elliptic.Qang g (j + 1) w) (Set.Ioi 0))
    (hz : 0 < z) :
    ContinuousAt (fun x => Work.Elliptic.Qang g (j + 1) x / x) z :=
  (hcont.continuousAt (isOpen_Ioi.mem_nhds hz)).div continuousAt_id (ne_of_gt hz)

/-- `Qang g j` is continuous on `(0,∞)` for `j ≤ 3`: it is (a constant plus) the primitive of
`x ↦ Qang g (j+1) x / x`, which is integrable on every compact subinterval of `(0,∞)`. -/
theorem continuousOn_Qang (α : ℝ) (g : ℝ → ℝ → ℝ) (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) {j : ℕ} (hj : j ≤ 3) :
    ContinuousOn (fun z => Work.Elliptic.Qang g j z) (Set.Ioi 0) := by
  intro z hz
  have hzpos : 0 < z := hz
  have hz2pos : 0 < z / 2 := by linarith
  have hle1 : z / 2 ≤ 2 * z := by linarith
  -- integrability of the integrand on a closed interval around `z`
  obtain ⟨-, hint⟩ := QangBoxIntegrable hsm hmem hj hz2pos hle1
  have hintIcc : MeasureTheory.IntegrableOn (fun x => Work.Elliptic.Qang g (j + 1) x / x)
      (Set.uIcc (z / 2) (2 * z)) := by
    rw [Set.uIcc_of_le hle1]
    refine (integrableOn_Icc_iff_integrableOn_Ioc (a := z / 2)
      (f := fun x => Work.Elliptic.Qang g (j + 1) x / x)).mpr ?_
    rwa [Set.uIoc_of_le hle1] at hint
  have hcont := intervalIntegral.continuousOn_primitive_interval hintIcc
  -- the primitive is `Qang g j · - Qang g j (z/2)` on the interval
  have hcongr : Set.EqOn (fun x => ∫ t in z / 2..x, Work.Elliptic.Qang g (j + 1) t / t)
      (fun x => Work.Elliptic.Qang g j x - Work.Elliptic.Qang g j (z / 2))
      (Set.uIcc (z / 2) (2 * z)) := by
    intro x hx
    have hxpos : 0 < x := by
      rw [Set.uIcc_of_le hle1] at hx
      linarith [hx.1]
    exact (Qang_primitive α g hsm hmem hj hxpos hz2pos).symm
  have hcont2 : ContinuousOn
      (fun x => Work.Elliptic.Qang g j x - Work.Elliptic.Qang g j (z / 2))
      (Set.uIcc (z / 2) (2 * z)) := hcont.congr hcongr.symm
  have hnhds : Set.uIcc (z / 2) (2 * z) ∈ 𝓝 z := by
    rw [Set.uIcc_of_le hle1]
    exact Icc_mem_nhds (by linarith) (by linarith)
  have hcat : ContinuousAt
      (fun x => Work.Elliptic.Qang g j x - Work.Elliptic.Qang g j (z / 2)) z :=
    hcont2.continuousAt hnhds
  exact ((hcat.add_const (Work.Elliptic.Qang g j (z / 2))).congr
    (Filter.Eventually.of_forall (fun x => by ring))).continuousWithinAt

/-- **`Qang g j` is differentiable on `(0,∞)` for `j ≤ 2`, with derivative
`Qang g (j+1) z / z`**: the primitive identity exhibits it as the primitive of a function
which is continuous at `z` (`continuousOn_Qang` at level `j + 1 ≤ 3`). -/
theorem hasDerivAt_Qang (α : ℝ) (g : ℝ → ℝ → ℝ) (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) {j : ℕ} (hj : j ≤ 2) {z : ℝ} (hz : 0 < z)
    (hcont : ContinuousOn (fun w => Work.Elliptic.Qang g (j + 1) w) (Set.Ioi 0)) :
    HasDerivAt (fun z => Work.Elliptic.Qang g j z)
      (Work.Elliptic.Qang g (j + 1) z / z) z := by
  have hz2pos : 0 < z / 2 := by linarith
  have hle1 : z / 2 ≤ z := by linarith
  obtain ⟨-, hint⟩ := QangBoxIntegrable hsm hmem (by omega : j ≤ 3) hz2pos hle1
  have hInt : IntervalIntegrable (fun x => Work.Elliptic.Qang g (j + 1) x / x) volume
      (z / 2) z := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle1]
    rwa [Set.uIoc_of_le hle1] at hint
  have hcontAt := continuousAt_Qang_div hcont hz
  have hcontOn : ContinuousOn (fun x => Work.Elliptic.Qang g (j + 1) x / x) (Set.Ioi 0) :=
    hcont.div continuousOn_id (fun x hx => ne_of_gt hx)
  have hsmAt := ContinuousOn.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioi hcontOn z hz
  have hprim : HasDerivAt (fun u => ∫ x in z / 2..u, Work.Elliptic.Qang g (j + 1) x / x)
      (Work.Elliptic.Qang g (j + 1) z / z) z :=
    intervalIntegral.integral_hasDerivAt_right hInt hsmAt hcontAt
  have heq : (fun u => Work.Elliptic.Qang g j u - Work.Elliptic.Qang g j (z / 2))
      =ᶠ[𝓝 z] (fun u => ∫ x in z / 2..u, Work.Elliptic.Qang g (j + 1) x / x) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with u hu
    exact Qang_primitive α g hsm hmem (by omega : j ≤ 3) hu hz2pos
  have h1 := hprim.congr_of_eventuallyEq heq
  have h2 := h1.add_const (Work.Elliptic.Qang g j (z / 2))
  exact h2.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u => by ring))

/-- `z`-differentiation of the angular moments `Qang g j z = ∫_θ Ktheta θ · D_z^j g z θ dθ`
in the interior class `SmoothQuad g + HkMem α 4 g` (no analyticity/`SmoothNbhd`):
`Qang g j` is continuous on `(0,∞)` for `j ≤ 3`, and for `j ≤ 2` it is differentiable at every
`z > 0` with `∂_z (Qang g j) z = Qang g (j+1) z / z`.

Route.  For each `θ ∈ (0,π/2)` the slice `z ↦ D_z^j g z θ` is `C^∞` on `Ioi (-1)`
(`Work.FTS.LocData.SmoothQuad.curry_z`), and `z·∂_z(D_z^j g) = D_z^{j+1} g`, so the primitive
formula (FTC) on `z₀..z` gives
`D_z^j g z θ - D_z^j g z₀ θ = ∫_{z₀}^z D_z^{j+1} g x θ / x dx` for every `θ ∈ (0,π/2)`.
Multiply by `Ktheta θ` and integrate in `θ`: the difference of the two `θ`-integrals is the
`θ`-integral of the difference (each `θ ↦ Ktheta θ · D_z^j g z θ` is integrable on `Iθ` for
`z > 0`, by Cauchy–Schwarz with `∫_θ (D_z^j g z θ)² < ∞`; the latter follows from `hmem.1` and
the pointwise domination of `(D_z^j g)²` by the `j`-th summand of `HkIntegrand α 4 g`, which is
`Work.Spaces.sq_le_HkIntegrand_z`).  Then Fubini/Tonelli on the box
`[min z z₀, max z z₀] × Iθ`: the joint integrand `(x,θ) ↦ Ktheta θ · D_z^{j+1} g x θ / x` is
integrable there because `|Ktheta| ≤ 3` and Cauchy–Schwarz bounds it by
`(∫∫ (D_z^{j+1} g)²/x²)^{1/2}`, while on the box `1/x² ≤ C·w(x)²·sin(2θ)^{-η}`
(`w ≥ w_min > 0` since `x ≥ min z z₀ > 0`, and `sin(2θ)^{-η} ≥ 1`) and the `(j+1)`-th pure
`D_z` slot of `HkIntegrand α 4 g` is integrable over `Iz × Iθ` by `hmem`; continuity of the
joint integrand on the box gives measurability.  This yields, for all `z, z₀ > 0`,
`Qang g j z - Qang g j z₀ = ∫_{z₀}^z Qang g (j+1) x / x dx`, and also that
`x ↦ Qang g (j+1) x / x` is integrable on each compact subinterval of `(0,∞)`.
Consequently `Qang g j` is continuous on `(0,∞)` (it is a primitive plus a constant), and for
`j ≤ 2` the right-hand integrand `x ↦ Qang g (j+1) x / x` is continuous at `z` (continuity of
`Qang g (j+1)`, obtained at the level `j+1 ≤ 3`), so
`HasDerivAt (Qang g j) (Qang g (j+1) z / z) z`.
(`j ≤ 3` in the continuity part is sharp: continuity of `Qang g 3` uses the Fubini identity at
level 3, hence the 4-th pure `D_z` slot of `HkMem α 4 g`.)
Useful existing siblings (all with the analyticity hypothesis `Spaces.SmoothNbhd`, which must
NOT be used): `Work.Elliptic.Qang_deriv_mul`, `Work.Elliptic.L12Iterate` (and
`Work.EllipticEst.Blocks.L12Gen.L12Iterate_k`), `Work.Elliptic.L12k0`. -/
theorem QangDiff (α : ℝ) (g : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    (∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
        HasDerivAt (Work.Elliptic.Qang g j) (Work.Elliptic.Qang g (j + 1) z / z) z) ∧
      (∀ j : ℕ, j ≤ 3 → ContinuousOn (Work.Elliptic.Qang g j) (Set.Ioi 0)) := by
  have hcont : ∀ j : ℕ, j ≤ 3 → ContinuousOn (fun z => Work.Elliptic.Qang g j z) (Set.Ioi 0) :=
    fun j hj => continuousOn_Qang α g hsm hmem hj
  refine ⟨?_, hcont⟩
  intro j hj z hz
  exact hasDerivAt_Qang α g hsm hmem hj hz (hcont (j + 1) (by omega))

end Work.FTS.H2
