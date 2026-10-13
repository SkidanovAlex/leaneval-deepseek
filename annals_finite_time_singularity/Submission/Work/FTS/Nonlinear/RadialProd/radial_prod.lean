import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.integral_sin_two_rpow_neg
import Submission.Work.FTS.H2.HQ.HardyZQ
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.H2.LinfQ
import Submission.Work.FTS.H2.HkSqSwap
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.RadialProd

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## Vocabulary

This file proves `radial_prod`: the product of a function `r` of `z` alone with a general
`SmoothQuad` function `g` is bounded in the `ℋ⁴`-norm by the product of the two `ℋ⁴`-norms,
with a *universal* constant (no loss in `γ - 1 = α/10`).

The whole bound is obtained from the radial Hardy inequality `Work.FTS.H2.HQ.HardyZQ`
(constant `1`, no `α`-loss) applied slicewise in `z`.  The two quantities that appear are
`Rr r` (the `z`-integral of `Σ_{i≤4}(D_z^i r)²w²`, which is `HkSq α 4 (fun z θ => r z)`
divided by `∫_θ sin(2θ)^{-η} ≥ π/2`), and `Qg g θ` (the `z`-integral of `(D_z g)²w²` at the
angle `θ`). -/

/-- The angular weight `σ θ = sin(2θ)^(-η)`. -/
noncomputable def smE (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The angular weight `τ α θ = sin(2θ)^(-γ(α))`. -/
noncomputable def smG (α θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

/-- `K_θ = ∫_θ σ θ dθ = ∫_θ sin(2θ)^(-η) dθ`, a universal constant `≥ 1`. -/
noncomputable def Kth : ℝ := ∫ θ in Work.Spaces.Iθ, smE θ

/-- `Rint r z = Σ_{i≤4} (D_z^i r z)² w(z)²`: the radial density of the `ℋ⁴`-norm. -/
noncomputable def Rint (r : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2

/-- `Rr r = ∫_z Σ_{i≤4} (D_z^i r z)² w(z)² dz`, the radial quantity that appears in the
product bound.  `HkSq α 4 (fun z θ => r z) = Rr r * Kth`. -/
noncomputable def Rr (r : ℝ → ℝ) : ℝ := ∫ z in Work.Spaces.Iz, Rint r z

/-- `Qg g θ = ∫_z (D_z g(z,θ))² w(z)² dz`, the radial `H¹`-density of `g` at the angle `θ`. -/
noncomputable def Qg (g : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (Work.Spaces.DzIter 1 g z θ) ^ 2 * (Work.Spaces.w z) ^ 2

/-! ## Elementary facts about the weights -/

theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem smE_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ smE θ :=
  Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

theorem smG_nonneg {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ smG α θ :=
  Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

/-- The squared light weight: `(A · w/sin(2θ)^{η/2})² = A² w² σ`. -/
theorem light_sq (A z θ : ℝ) (hsin : 0 < Real.sin (2 * θ)) :
    (A * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = A ^ 2 * (Work.Spaces.w z) ^ 2 * smE θ := by
  have h1 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [pow_two, ← Real.rpow_add hsin, show Work.Spaces.eta / 2 + Work.Spaces.eta / 2
      = Work.Spaces.eta by ring]
  rw [mul_pow, div_pow, h1, smE, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hsin)]
  ring

/-- The squared heavy weight: `(A · Wt α z θ)² = A² w² τ` on the open interval. -/
theorem heavy_sq (α A z θ : ℝ) (hsin : 0 < Real.sin (2 * θ)) :
    (A * Work.Spaces.Wt α z θ) ^ 2 = A ^ 2 * (Work.Spaces.w z) ^ 2 * smG α θ := by
  have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [pow_two, ← Real.rpow_add hsin,
      show -(Work.Spaces.gam α / 2) + -(Work.Spaces.gam α / 2)
        = -(Work.Spaces.gam α) by ring]
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, smG, mul_pow, mul_pow, h1]
  ring

/-- `σ ≥ 1` on the open interval. -/
theorem one_le_smE {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 1 ≤ smE θ := by
  have hsin : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have := Real.rpow_le_rpow_of_nonpos hsin hle
    (by linarith [Work.Spaces.eta_pos] : -(Work.Spaces.eta) ≤ 0)
  rwa [Real.one_rpow] at this

/-- `1 ≤ w z` for `z > 0`. -/
theorem one_le_w {z : ℝ} (hz : 0 < z) : (1 : ℝ) ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (pow_pos hz 2)]
  nlinarith

/-- `∫_θ (1 : ℝ) = π/2` over `Iθ`. -/
theorem integral_one_Iθ : ∫ _θ in Work.Spaces.Iθ, (1 : ℝ) = Real.pi / 2 := by
  rw [Work.Elliptic.integral_Iθ_eq_interval (fun _ : ℝ => (1 : ℝ))]
  simp

/-- `K_θ ≥ 1`. -/
theorem one_le_Kth : 1 ≤ Kth := by
  have hInt : MeasureTheory.IntegrableOn (fun θ : ℝ => smE θ) Work.Spaces.Iθ :=
    (Work.FTS.LocData.integral_sin_two_rpow_neg Work.Spaces.eta Work.Spaces.eta_pos
      Work.Spaces.eta_lt_one).1
  have hne : MeasureTheory.volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    integrableOn_const hne
  have hae : (fun _ : ℝ => (1 : ℝ)) ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] smE := by
    filter_upwards [Work.H2.T1Q.ae_mem_Ioo_Iθ] with θ hθ
    exact one_le_smE hθ
  have hmono := MeasureTheory.integral_mono_ae hone hInt hae
  rw [integral_one_Iθ] at hmono
  rw [Kth]
  linarith [Real.pi_gt_three]

/-! ## The Leibniz rules for a radial factor -/

/-- The `D_z`-Leibniz rule for a radial factor: `D_z^j (r·g) = Σ_b C(j,b) (D_z^b r)(D_z^{j-b} g)`
on the open quadrant. -/
theorem DzIter_mul_rad (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ)
    (hr : Work.FTS.LocData.SmoothQuad (fun z θ => r z))
    (hg : Work.FTS.LocData.SmoothQuad g) (j : ℕ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.DzIter j (fun z θ => r z * g z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.DzIter (j - b) g z θ) := by
  intro z hz θ hθ
  rw [Work.FTS.H2.HQ.DzIter_mul_quad j (fun z θ => r z) g hr hg z hz θ hθ]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Work.Elliptic.DzIter_rad r b z θ]

/-- The mixed Leibniz rule for a radial factor:
`D_z^j D_θ^i (r·g) = Σ_b C(j,b) (D_z^b r)(D_z^{j-b} D_θ^i g)` for `i ≥ 1`
on the open quadrant (the `D_θ`-derivatives all fall on `g`). -/
theorem mixed_mul_rad (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ)
    (hr : Work.FTS.LocData.SmoothQuad (fun z θ => r z))
    (hg : Work.FTS.LocData.SmoothQuad g) (j i : ℕ) (hi : 1 ≤ i) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.mixed (j - b) i g z θ) := by
  intro z hz θ hθ
  rw [Work.FTS.H2.HQ.mixed_mul_eq_quad j i (fun z θ => r z) g hr hg z hz θ hθ]
  -- kill the summands with `a ≥ 1`: `D_θ^a` of a radial function vanishes
  have hzero : ∀ a ∈ Finset.range (i + 1), a ≠ 0 →
      (∑ b ∈ Finset.range (j + 1), ((i.choose a : ℝ) * (j.choose b : ℝ))
        * (Work.Spaces.mixed b a (fun z θ => r z) z θ
            * Work.Spaces.mixed (j - b) (i - a) g z θ)) = 0 := by
    intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [show Work.Spaces.mixed b a (fun z θ => r z) z θ = 0 from
      congrFun (congrFun (Work.Elliptic.mixed_rad_eq_zero r (by omega)) z) θ]
    ring
  rw [Finset.sum_eq_single 0 hzero (by intro h; exact absurd (Finset.mem_range.mpr (by omega)) h)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Nat.choose_zero_right, Nat.sub_zero, Work.Spaces.mixed_zero_right,
    Work.Elliptic.DzIter_rad r b z θ]
  ring

/-! ## The radial reduction of `HkSq` -/

theorem Rint_nonneg (r : ℝ → ℝ) (z : ℝ) : 0 ≤ Rint r z :=
  Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem Rr_nonneg (r : ℝ → ℝ) : 0 ≤ Rr r :=
  integral_nonneg fun z => Rint_nonneg r z

/-- The inner `θ`-integral of the `ℋ⁴`-integrand of a radial function. -/
theorem integral_HkIntegrand_rad (α : ℝ) (r : ℝ → ℝ) (z : ℝ) :
    ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (fun z θ => r z) z θ
      = Rint r z * Kth := by
  have hkey : (fun θ => Work.Spaces.HkIntegrand α 4 (fun z θ => r z) z θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] (fun θ => Rint r z * smE θ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Work.Elliptic.HkIntegrand_rad α 4 r z hθ, Rint, Finset.sum_mul, smE]
  rw [MeasureTheory.integral_congr_ae hkey, MeasureTheory.integral_const_mul]
  rfl

/-- The exact value of `HkSq` of a radial function: `HkSq α 4 (fun z θ => r z) = Rr r * K_θ`. -/
theorem HkSq_rad_eq (α : ℝ) (r : ℝ → ℝ) :
    Work.Spaces.HkSq α 4 (fun z θ => r z) = Rr r * Kth := by
  rw [Work.Elliptic.HkSq_rad α 4 r]
  simp only [Rr, Rint, Kth, smE]

/-- `Rr` is dominated by the `ℋ⁴`-norm of the radial lift (via `K_θ ≥ 1`). -/
theorem Rr_le_HkSq (α : ℝ) (r : ℝ → ℝ) :
    Rr r ≤ Work.Spaces.HkSq α 4 (fun z θ => r z) := by
  rw [HkSq_rad_eq]
  nlinarith [Rr_nonneg r, one_le_Kth]

/-- `Rr` is finite (honest integrability of the radial density) whenever the radial lift is
in `ℋ⁴`. -/
theorem integrable_Rint (α : ℝ) (r : ℝ → ℝ)
    (hmem : Work.Spaces.HkMem α 4 (fun z θ => r z)) :
    MeasureTheory.IntegrableOn (Rint r) Work.Spaces.Iz := by
  have h := hmem.2
  rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (fun z θ => r z) z θ)
      = fun z => Rint r z * Kth from funext fun z => integral_HkIntegrand_rad α r z] at h
  have hK : Kth ≠ 0 := by linarith [one_le_Kth]
  refine h.mul_const Kth⁻¹ |>.congr (Filter.Eventually.of_forall fun z => ?_)
  show Rint r z * Kth * Kth⁻¹ = Rint r z
  rw [mul_assoc, mul_inv_cancel₀ hK, mul_one]

/-! ## Smoothness and measurability of the radial iterates -/

theorem one_lt_pi_div_two : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]

/-- Every `D_z`-iterate of a radial `SmoothQuad` function is `C^∞` on `(-1,∞)`. -/
theorem contDiffOn_DzdIter (r : ℝ → ℝ)
    (hsq : Work.FTS.LocData.SmoothQuad (fun z θ => r z)) (b : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Work.Elliptic.DzdIter b r) (Set.Ioi (-1)) := by
  have h1 := (hsq.DzIter b).curry_z (θ := 1) ⟨one_pos, one_lt_pi_div_two⟩
  exact h1.congr (fun z _ => (Work.Elliptic.DzIter_rad r b z 1).symm)

theorem continuousOn_DzdIter (r : ℝ → ℝ)
    (hsq : Work.FTS.LocData.SmoothQuad (fun z θ => r z)) (b : ℕ) :
    ContinuousOn (fun z => Work.Elliptic.DzdIter b r z) (Set.Ioi (-1)) :=
  (contDiffOn_DzdIter r hsq b).continuousOn

theorem aesm_DzdIter_sq_w_sq (r : ℝ → ℝ)
    (hsq : Work.FTS.LocData.SmoothQuad (fun z θ => r z)) (b : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => (Work.Elliptic.DzdIter b r s) ^ 2 * (Work.Spaces.w s) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hc := (continuousOn_DzdIter r hsq b).mono
    (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0))
  have hw : ContinuousOn (fun s : ℝ => (Work.Spaces.w s) ^ 2) (Set.Ioi (0 : ℝ)) := by
    have hfun : (fun s : ℝ => (Work.Spaces.w s) ^ 2)
        = fun s : ℝ => ((1 + s) ^ 2 / s ^ 2) ^ 2 := by
      funext s; rw [Work.Spaces.w]
    rw [hfun]
    exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) (fun s hs => pow_ne_zero 2 (ne_of_gt hs))).pow 2
  exact Work.H2.T1Q.aesm_Iz_of_continuousOn (hc.pow 2 |>.mul hw)

/-- A single radial slot `(D_z^b r)² w²` is integrable over `Iz` for `b ≤ 4`. -/
theorem integrable_DzdIter_sq (α : ℝ) (r : ℝ → ℝ)
    (hsq : Work.FTS.LocData.SmoothQuad (fun z θ => r z))
    (hmem : Work.Spaces.HkMem α 4 (fun z θ => r z)) (b : ℕ) (hb : b ≤ 4) :
    MeasureTheory.IntegrableOn
      (fun s => (Work.Elliptic.DzdIter b r s) ^ 2 * (Work.Spaces.w s) ^ 2)
      Work.Spaces.Iz := by
  refine MeasureTheory.Integrable.mono' (integrable_Rint α r hmem)
    (aesm_DzdIter_sq_w_sq r hsq b) ?_
  filter_upwards with s
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact Finset.single_le_sum
    (f := fun i => (Work.Elliptic.DzdIter i r s) ^ 2 * (Work.Spaces.w s) ^ 2)
    (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (Finset.mem_range.mpr (by omega))

/-! ## The radial Hardy bound -/

/-- **The radial Hardy bound.**  For `b ≤ 3` and `z > 0`,
`(D_z^b r z)² ≤ Rr r`: this is `HardyZQ` (constant `1`, *no* `γ - 1` loss) applied to the
`z`-slice `D_z^b r`, whose Hardy integrand `(D_z^{b+1} r)²w²` is a slot of the radial density. -/
theorem DzdIter_sq_le_Rr (α : ℝ) (r : ℝ → ℝ)
    (hsq : Work.FTS.LocData.SmoothQuad (fun z θ => r z))
    (hmem : Work.Spaces.HkMem α 4 (fun z θ => r z))
    (hdec : ∀ b : ℕ, b ≤ 4 → Filter.Tendsto (Work.Elliptic.DzdIter b r) Filter.atTop (nhds 0))
    {b : ℕ} (hb : b ≤ 3) {z : ℝ} (hz : 0 < z) :
    (Work.Elliptic.DzdIter b r z) ^ 2 ≤ Rr r := by
  have hb4 : b + 1 ≤ 4 := by omega
  have hcd : ContDiffOn ℝ 1 (Work.Elliptic.DzdIter b r) (Set.Ioi (0 : ℝ)) :=
    (contDiffOn_DzdIter r hsq b).mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0))
      |>.of_le (by simp [Work.Stability.smoothOrder])
  have hint : MeasureTheory.IntegrableOn
      (fun s => (s * deriv (Work.Elliptic.DzdIter b r) s) ^ 2 * (Work.Spaces.w s) ^ 2)
      Work.Spaces.Iz := by
    have h := integrable_DzdIter_sq α r hsq hmem (b + 1) hb4
    refine h.congr (Filter.Eventually.of_forall fun s => ?_)
    simp only [Work.Elliptic.DzdIter_succ, Work.Elliptic.Dzd]
  have hH := Work.FTS.H2.HQ.HardyZQ (Work.Elliptic.DzdIter b r) hcd (hdec b (by omega)) hint z
    (Set.mem_Ioi.mpr hz)
  refine le_trans hH ?_
  rw [show MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iz)
        (fun s => (s * deriv (Work.Elliptic.DzdIter b r) s) ^ 2 * (Work.Spaces.w s) ^ 2)
      = MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iz)
        (fun s => (Work.Elliptic.DzdIter (b + 1) r s) ^ 2 * (Work.Spaces.w s) ^ 2) from
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => by
      simp only [Work.Elliptic.DzdIter_succ, Work.Elliptic.Dzd])]
  rw [Rr]
  refine MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun s => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (integrable_Rint α r hmem)
    (Filter.Eventually.of_forall fun s => ?_)
  exact Finset.single_le_sum
    (f := fun i => (Work.Elliptic.DzdIter i r s) ^ 2 * (Work.Spaces.w s) ^ 2)
    (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (Finset.mem_range.mpr (by omega))

/-! ## The radial `H¹`-density `Qg` of `g` -/

/-- The `z`-density of `Qg`: `ψ z θ = (D_z g(z,θ))² w(z)²`. -/
noncomputable def psiZ (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.DzIter 1 g z θ) ^ 2 * (Work.Spaces.w z) ^ 2

/-- The weighted version `Ψ z θ = σ θ · ψ z θ`. -/
noncomputable def PsiZ (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ := smE θ * psiZ g z θ

theorem Qg_def_eq (g : ℝ → ℝ → ℝ) (θ : ℝ) :
    Qg g θ = ∫ z in Work.Spaces.Iz, psiZ g z θ := rfl

theorem Qg_nonneg (g : ℝ → ℝ → ℝ) (θ : ℝ) : 0 ≤ Qg g θ :=
  integral_nonneg fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem psiZ_nonneg (g : ℝ → ℝ → ℝ) (z θ : ℝ) : 0 ≤ psiZ g z θ :=
  mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **The radial Hardy inequality for `g`.**  For `z > 0` and `θ` in the open angular
interval, `(g z θ)² ≤ Qg g θ`: `HardyZQ` applied to the `z`-slice `g(·,θ)`, whose Hardy
integrand `(D_z g)²w²` is exactly the defining integrand of `Qg`. -/
theorem g_sq_le_Qg (g : ℝ → ℝ → ℝ) (hsq : Work.FTS.LocData.SmoothQuad g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hdec : Filter.Tendsto (fun z => g z θ) Filter.atTop (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun s => psiZ g s θ) Work.Spaces.Iz)
    {z : ℝ} (hz : 0 < z) :
    (g z θ) ^ 2 ≤ Qg g θ := by
  have hcd : ContDiffOn ℝ 1 (fun z => g z θ) (Set.Ioi (0 : ℝ)) :=
    (hsq.curry_z hθ).mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0))
      |>.of_le (by simp [Work.Stability.smoothOrder])
  have h := Work.FTS.H2.HQ.HardyZQ (fun z => g z θ) hcd hdec hint z (Set.mem_Ioi.mpr hz)
  rw [show Qg g θ = MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iz)
      (fun s => (s * deriv (fun z => g z θ) s) ^ 2 * (Work.Spaces.w s) ^ 2) from rfl]
  exact h

/-- On the closed angular interval, `Ψ z θ` is dominated by the `ℋ⁴`-integrand of `g`. -/
theorem PsiZ_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    PsiZ g z θ ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  rcases lt_or_eq_of_le (sin_two_nonneg_of_mem_Iθ hθ) with hpos | heq
  · have h1 : PsiZ g z θ
        = (Work.Spaces.DzIter 1 g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      rw [PsiZ, psiZ, light_sq (Work.Spaces.DzIter 1 g z θ) z θ hpos]
      ring
    rw [h1]
    exact Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ 1 (by norm_num)
  · rw [PsiZ, psiZ, smE, ← heq,
      Real.zero_rpow (by linarith [Work.Spaces.eta_pos] : -(Work.Spaces.eta) ≠ 0), zero_mul]
    exact Work.Spaces.HkIntegrand_nonneg α 4 g z θ

/-! ## Measurability and the Fubini bookkeeping for `Qg` -/

theorem continuousOn_smE_snd :
    ContinuousOn (fun p : ℝ × ℝ => smE p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have hne : ∀ p ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)),
      Real.sin (2 * p.2) ≠ 0 :=
    fun p hp => ne_of_gt (Work.FTS.H2.HQ.sin_pos_of_quadQ p hp)
  simpa only [smE] using hsin.rpow_const (fun p hp => Or.inl (hne p hp))

theorem continuousOn_w_fst :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rw [Work.Spaces.w]
  rw [hfun]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))

theorem continuousOn_psiZ (g : ℝ → ℝ → ℝ) (hsq : Work.FTS.LocData.SmoothQuad g) :
    ContinuousOn (fun p : ℝ × ℝ => psiZ g p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hdz : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter 1 g p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hsq 1).continuousOn).mono
      Work.FTS.H2.HQ.quadQ_subset_quadU
  have hpsi : (fun p : ℝ × ℝ => psiZ g p.1 p.2)
      = fun p : ℝ × ℝ => (Work.Spaces.DzIter 1 g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2 := rfl
  rw [hpsi]
  exact (hdz.pow 2).mul (continuousOn_w_fst.pow 2)

theorem aesm_PsiZ_prod (α : ℝ) (g : ℝ → ℝ → ℝ) (hsq : Work.FTS.LocData.SmoothQuad g) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => PsiZ g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => PsiZ g p.1 p.2)
    (continuousOn_smE_snd.mul (continuousOn_psiZ g hsq))

theorem integrable_uncurry_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hsq : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  (Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun z θ => Work.Spaces.HkIntegrand α 4 g z θ)
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
    (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 4 g hsq))
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hmem.1 z hz))
    hmem.2).1

/-- Integrability of the uncurried `Ψ` on the product measure. -/
theorem integrable_uncurry_PsiZ (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hsq : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => PsiZ g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hAESM := aesm_PsiZ_prod α g hsq
  refine (MeasureTheory.integrable_prod_iff hAESM).mpr ⟨?_, ?_⟩
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
    rcases lt_or_eq_of_le (show (0 : ℝ) ≤ z from hz) with hzpos | rfl
    · have hθcont : ContinuousOn (fun θ : ℝ => PsiZ g z θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
        have h1 : ContinuousOn (fun θ : ℝ => smE θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
          have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ))
              (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
            (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
          have h := hsin.rpow_const (p := -(Work.Spaces.eta))
            (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo hθ)))
          simpa only [smE] using h
        have h2 : ContinuousOn (fun θ : ℝ => Work.Spaces.DzIter 1 g z θ)
            (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
          ((Work.FTS.LocData.contDiffOn_slice_θ
            (G := fun z θ => Work.Spaces.DzIter 1 g z θ)
            (Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hsq 1) (z := z)
            (Set.mem_Ioi.mpr (by linarith)))).continuousOn
        exact h1.mul ((h2.pow 2).mul continuousOn_const)
      refine MeasureTheory.Integrable.mono' (hmem.1 z hz)
        (Work.H2.T1Q.aesm_Iθ_of_continuousOn hθcont) ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      simp only [PsiZ]
      rw [Real.norm_of_nonneg (mul_nonneg (smE_nonneg hθ) (psiZ_nonneg g z θ))]
      exact PsiZ_le_HkIntegrand α g hθ
    · have hzero : (fun θ : ℝ => PsiZ g 0 θ) = fun _ => (0 : ℝ) := by
        funext θ
        rw [PsiZ, psiZ]
        simp [Work.Spaces.w]
      rw [hzero]
      exact integrable_zero _ _ _
  · refine MeasureTheory.Integrable.mono' hmem.2
      ((hAESM.norm).integral_prod_right') ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => norm_nonneg _)]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => norm_nonneg _) (hmem.1 z hz) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    show ‖PsiZ g z θ‖ ≤ Work.Spaces.HkIntegrand α 4 g z θ
    simp only [PsiZ]
    rw [Real.norm_of_nonneg (mul_nonneg (smE_nonneg hθ) (psiZ_nonneg g z θ))]
    exact PsiZ_le_HkIntegrand α g hθ

/-- The Fubini swap for `Ψ`. -/
theorem PsiZ_swap (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hsq : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, PsiZ g z θ)
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, PsiZ g z θ :=
  MeasureTheory.integral_integral_swap (f := fun z θ => PsiZ g z θ)
    (integrable_uncurry_PsiZ α g hsq hmem)

/-- **The `Qg`-integral bound.**  `θ ↦ σ θ · Qg g θ` is integrable on `Iθ` and its integral is
at most `HkSq α 4 g` — the single `ℋ⁴`-slot `(D_z g)²w²σ` of `g`. -/
theorem integrable_smE_Qg_and_le (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hsq : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    MeasureTheory.IntegrableOn (fun θ => smE θ * Qg g θ) Work.Spaces.Iθ ∧
      ∫ θ in Work.Spaces.Iθ, smE θ * Qg g θ ≤ Work.Spaces.HkSq α 4 g := by
  have hIntPsi := integrable_uncurry_PsiZ α g hsq hmem
  have hswap := PsiZ_swap α g hsq hmem
  have hpts : ∀ θ, (∫ z in Work.Spaces.Iz, PsiZ g z θ) = smE θ * Qg g θ := fun θ =>
    MeasureTheory.integral_const_mul (smE θ) (fun z => psiZ g z θ)
  have hle : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, PsiZ g z θ)
      ≤ Work.Spaces.HkSq α 4 g := by
    rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun z =>
      MeasureTheory.integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem
        measurableSet_Icc (fun θ hθ => mul_nonneg (smE_nonneg hθ) (psiZ_nonneg g z θ))))
      hmem.2 ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
    exact MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg (smE_nonneg hθ) (psiZ_nonneg g z θ)))
      (hmem.1 z hz)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => PsiZ_le_HkIntegrand α g hθ))
  refine ⟨?_, ?_⟩
  · have h := MeasureTheory.Integrable.integral_prod_right
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun p : ℝ × ℝ => PsiZ g p.1 p.2) hIntPsi
    rw [show (fun θ => ∫ z, PsiZ g z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) = fun θ => smE θ * Qg g θ from
      funext hpts] at h
    exact h
  · rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => (hpts θ).symm),
      ← hswap]
    exact hle

/-! ## The pointwise bound on the `ℋ⁴`-integrand of the product -/

/-- Binomial coefficients of a small order are bounded by `16`. -/
theorem choose_le_sixteen {i b : ℕ} (hi : i ≤ 4) : ((i.choose b : ℕ) : ℝ) ≤ 16 := by
  have h1 : i.choose b ≤ 2 ^ i := Nat.choose_le_two_pow i b
  have h2 : 2 ^ i ≤ 16 := by
    calc 2 ^ i ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hi
      _ = 16 := by norm_num
  exact_mod_cast le_trans h1 h2

/-- **Pointwise bound of one pure `D_z`-slot of the product.**  For `i ≤ 3` the Leibniz
expansion `D_z^i(r·g) = Σ_b C(i,b)(D_z^b r)(D_z^{i-b}g)` is dominated by
`C·Rr·HkIntegrand α 4 g`, with a universal `C`. -/
theorem pure_slot_le (α : ℝ) (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ)
    (hr : Work.FTS.LocData.SmoothQuad (fun z θ => r z))
    (hg : Work.FTS.LocData.SmoothQuad g)
    (hI : ∀ b : ℕ, b ≤ 3 → ∀ z : ℝ, 0 < z → (Work.Elliptic.DzdIter b r z) ^ 2 ≤ Rr r)
    {i : ℕ} (hi : i ≤ 3) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 65536 * (Rr r) * Work.Spaces.HkIntegrand α 4 g z θ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hDz := DzIter_mul_rad r g hr hg i z hzI θ hθ
  set F : ℕ → ℝ := fun b => (i.choose b : ℝ)
    * (Work.Elliptic.DzdIter b r z
        * (Work.Spaces.DzIter (i - b) g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) with hF
  have hkey : Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      = ∑ b ∈ Finset.range (i + 1), F b := by
    rw [hDz, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by simp only [hF]; ring
  rw [hkey]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1)) (f := F)
  have hcard : ((Finset.range (i + 1)).card : ℝ) = (i : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hcard5 : ((Finset.range (i + 1)).card : ℝ) ≤ 5 := by
    rw [hcard]; exact_mod_cast (by omega : i + 1 ≤ 5)
  have hnn : ∀ b ∈ Finset.range (i + 1), 0 ≤ F b ^ 2 := fun b _ => sq_nonneg _
  have hterm : ∀ b ∈ Finset.range (i + 1), F b ^ 2 ≤ 256 * (Rr r * Work.Spaces.HkIntegrand α 4 g z θ) := by
    intro b hb
    have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hb3 : b ≤ 3 := le_trans hbi hi
    have hib : i - b ≤ 4 := by omega
    have h1 : ((i.choose b : ℕ) : ℝ) ^ 2 ≤ 256 := by
      have h := choose_le_sixteen (i := i) (b := b) (by omega)
      have h0 : (0 : ℝ) ≤ ((i.choose b : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [h, h0]
    have h2 : (Work.Elliptic.DzdIter b r z) ^ 2 ≤ Rr r := hI b hb3 z hz
    have h3 : (Work.Spaces.DzIter (i - b) g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ (i - b) hib
    have h4 : 0 ≤ Rr r := Rr_nonneg r
    have h5 : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
    have h7 : 0 ≤ (Work.Spaces.DzIter (i - b) g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := sq_nonneg _
    have hprod : (Work.Elliptic.DzdIter b r z) ^ 2
          * (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Rr r * Work.Spaces.HkIntegrand α 4 g z θ :=
      mul_le_mul h2 h3 h7 h4
    have hprod2 : ((i.choose b : ℝ)) ^ 2
          * ((Work.Elliptic.DzdIter b r z) ^ 2
              * (Work.Spaces.DzIter (i - b) g z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ 256 * (Rr r * Work.Spaces.HkIntegrand α 4 g z θ) :=
      mul_le_mul h1 hprod (by positivity) (by norm_num)
    rw [hF]
    have hgoal : ((i.choose b : ℝ) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
        = ((i.choose b : ℝ)) ^ 2
          * ((Work.Elliptic.DzdIter b r z) ^ 2
              * (Work.Spaces.DzIter (i - b) g z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by ring
    rw [hgoal]
    exact hprod2
  have hsum : (∑ b ∈ Finset.range (i + 1), F b ^ 2)
      ≤ 5 * (256 * (Rr r * Work.Spaces.HkIntegrand α 4 g z θ)) := by
    calc (∑ b ∈ Finset.range (i + 1), F b ^ 2)
        ≤ ∑ _b ∈ Finset.range (i + 1), (256 * (Rr r * Work.Spaces.HkIntegrand α 4 g z θ)) :=
          Finset.sum_le_sum hterm
      _ = ((Finset.range (i + 1)).card : ℝ) * (256 * (Rr r * Work.Spaces.HkIntegrand α 4 g z θ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 5 * (256 * (Rr r * Work.Spaces.HkIntegrand α 4 g z θ)) := by
          have h0 : 0 ≤ 256 * (Rr r * Work.Spaces.HkIntegrand α 4 g z θ) := by
            have h4 : 0 ≤ Rr r := Rr_nonneg r
            have h5 : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
            positivity
          exact mul_le_mul_of_nonneg_right hcard5 h0
  have hfinal : (∑ b ∈ Finset.range (i + 1), F b) ^ 2
      ≤ 65536 * (Rr r) * Work.Spaces.HkIntegrand α 4 g z θ := by
    have h4 : 0 ≤ Rr r := Rr_nonneg r
    have h5 : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
    nlinarith [hcs, hcard5, hsum, h4, h5]
  exact hfinal

/-- **Pointwise bound of the top pure `D_z`-slot** (`i = 4`).  The term in which all four
`D_z`-derivatives fall on `r` is paired with `g` itself, which is bounded by the radial Hardy
inequality for `g` (whose Hardy integrand is the `ℋ¹`-slot `(D_z g)²w²σ` of `g`). -/
theorem pure_slot_four_le (α : ℝ) (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ)
    (hr : Work.FTS.LocData.SmoothQuad (fun z θ => r z))
    (hg : Work.FTS.LocData.SmoothQuad g)
    (hI : ∀ b : ℕ, b ≤ 3 → ∀ z : ℝ, 0 < z → (Work.Elliptic.DzdIter b r z) ^ 2 ≤ Rr r)
    {θ : ℝ} (hQg : ∀ z : ℝ, 0 < z → (g z θ) ^ 2 ≤ Qg g θ)
    {z : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.DzIter 4 (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 65536 * (Rr r) * Work.Spaces.HkIntegrand α 4 g z θ
        + 65536 * (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2 * smE θ * Qg g θ := by
  have hsin : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hDz := DzIter_mul_rad r g hr hg 4 z hzI θ hθ
  set F : ℕ → ℝ := fun b => ((4 : ℕ).choose b : ℝ)
    * (Work.Elliptic.DzdIter b r z
        * (Work.Spaces.DzIter (4 - b) g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) with hF
  have hkey : Work.Spaces.DzIter 4 (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      = ∑ b ∈ Finset.range 5, F b := by
    rw [hDz, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by simp only [hF]; ring
  rw [hkey]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range 5) (f := F)
  have hcard : ((Finset.range 5).card : ℝ) = 5 := by rw [Finset.card_range]; norm_num
  -- every square of `F`
  have hterm : ∀ b ∈ Finset.range 5, F b ^ 2
      ≤ 256 * (Rr r * Work.Spaces.HkIntegrand α 4 g z θ)
        + 256 * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2 * smE θ * Qg g θ) := by
    intro b hb
    have hb4 : b ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have h1 : (((4 : ℕ).choose b : ℕ) : ℝ) ^ 2 ≤ 256 := by
      have h := choose_le_sixteen (i := 4) (b := b) (by norm_num)
      have h0 : (0 : ℝ) ≤ (((4 : ℕ).choose b : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [h, h0]
    have h4nn : 0 ≤ Rr r := Rr_nonneg r
    have h5nn : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
    rw [hF]
    have hgoal : (((4 : ℕ).choose b : ℝ) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.DzIter (4 - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
        = (((4 : ℕ).choose b : ℝ)) ^ 2
          * ((Work.Elliptic.DzdIter b r z) ^ 2
              * (Work.Spaces.DzIter (4 - b) g z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by ring
    rw [hgoal]
    rcases (by omega : b ≤ 3 ∨ b = 4) with hb3 | hb4'
    · have h2 : (Work.Elliptic.DzdIter b r z) ^ 2 ≤ Rr r := hI b hb3 z hz
      have h3 : (Work.Spaces.DzIter (4 - b) g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ (4 - b) (by omega)
      have hprod : (Work.Elliptic.DzdIter b r z) ^ 2
            * (Work.Spaces.DzIter (4 - b) g z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ Rr r * Work.Spaces.HkIntegrand α 4 g z θ :=
        mul_le_mul h2 h3 (sq_nonneg _) h4nn
      have hprod2 := mul_le_mul h1 hprod (by positivity) (by norm_num : (0:ℝ) ≤ 256)
      have hle : (((4 : ℕ).choose b : ℝ)) ^ 2
            * ((Work.Elliptic.DzdIter b r z) ^ 2
                * (Work.Spaces.DzIter (4 - b) g z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ 256 * (Rr r * Work.Spaces.HkIntegrand α 4 g z θ) := hprod2
      have hsecond : 0 ≤ 256 * ((Work.Elliptic.DzdIter 4 r z) ^ 2
          * (Work.Spaces.w z) ^ 2 * smE θ * Qg g θ) := by
        have := smE_nonneg (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
        have := Qg_nonneg g θ
        positivity
      linarith
    · subst hb4'
      have h3 : (Work.Spaces.DzIter (4 - 4) g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        norm_num
      have hls : (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * smE θ :=
        light_sq (g z θ) z θ hsin
      have hQg' : (g z θ) ^ 2 ≤ Qg g θ := hQg z hz
      have hw : 0 ≤ (Work.Spaces.w z) ^ 2 * smE θ := by
        have := smE_nonneg (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
        positivity
      have hkey4 : (Work.Elliptic.DzdIter 4 r z) ^ 2
            * (Work.Spaces.DzIter (4 - 4) g z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2 * smE θ * Qg g θ := by
        have hI4 : 0 ≤ (Work.Elliptic.DzdIter 4 r z) ^ 2 := sq_nonneg _
        rw [h3, hls]
        have hstep : (g z θ) ^ 2 * (Work.Spaces.w z ^ 2 * smE θ)
            ≤ Qg g θ * (Work.Spaces.w z ^ 2 * smE θ) :=
          mul_le_mul_of_nonneg_right hQg' hw
        have hstep2 := mul_le_mul_of_nonneg_left hstep hI4
        nlinarith [hstep2]
      have hprod2 := mul_le_mul h1 hkey4 (by positivity) (by norm_num : (0:ℝ) ≤ 256)
      have hfirst : 0 ≤ 256 * (Rr r * Work.Spaces.HkIntegrand α 4 g z θ) := by positivity
      linarith
  have hsum : (∑ b ∈ Finset.range 5, F b ^ 2)
      ≤ 5 * (256 * (Rr r * Work.Spaces.HkIntegrand α 4 g z θ)
        + 256 * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2 * smE θ * Qg g θ)) := by
    calc (∑ b ∈ Finset.range 5, F b ^ 2)
        ≤ ∑ _b ∈ Finset.range 5, (256 * (Rr r * Work.Spaces.HkIntegrand α 4 g z θ)
            + 256 * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2 * smE θ
                * Qg g θ)) := Finset.sum_le_sum hterm
      _ = ((Finset.range 5).card : ℝ) * (256 * (Rr r * Work.Spaces.HkIntegrand α 4 g z θ)
            + 256 * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2 * smE θ
                * Qg g θ)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = 5 * (256 * (Rr r * Work.Spaces.HkIntegrand α 4 g z θ)
            + 256 * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2 * smE θ
                * Qg g θ)) := by rw [hcard]
  have hfinal : (∑ b ∈ Finset.range 5, F b) ^ 2
      ≤ 65536 * (Rr r) * Work.Spaces.HkIntegrand α 4 g z θ
        + 65536 * (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2 * smE θ * Qg g θ := by
    have h4 : 0 ≤ Rr r := Rr_nonneg r
    have h5 : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
    have h6 : 0 ≤ smE θ := smE_nonneg (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    have h7 : 0 ≤ Qg g θ := Qg_nonneg g θ
    nlinarith [hcs, hcard, hsum, h4, h5, h6, h7, sq_nonneg (Work.Elliptic.DzdIter 4 r z),
      sq_nonneg (Work.Spaces.w z)]
  exact hfinal

/-- **Pointwise bound of one mixed slot of the product.** -/
theorem mixed_slot_le (α : ℝ) (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ)
    (hr : Work.FTS.LocData.SmoothQuad (fun z θ => r z))
    (hg : Work.FTS.LocData.SmoothQuad g)
    (hI : ∀ b : ℕ, b ≤ 3 → ∀ z : ℝ, 0 < z → (Work.Elliptic.DzdIter b r z) ^ 2 ≤ Rr r)
    {j i : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 4) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 65536 * (Rr r) * Work.Spaces.HkIntegrand α 4 g z θ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hj3 : j ≤ 3 := by omega
  have hDz := mixed_mul_rad r g hr hg j i hi z hzI θ hθ
  set F : ℕ → ℝ := fun b => (j.choose b : ℝ)
    * (Work.Elliptic.DzdIter b r z * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ))
    with hF
  have hkey : Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ
      = ∑ b ∈ Finset.range (j + 1), F b := by
    rw [hDz, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by simp only [hF]; ring
  rw [hkey]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1)) (f := F)
  have hcard : ((Finset.range (j + 1)).card : ℝ) ≤ 5 := by
    rw [Finset.card_range]; exact_mod_cast (by omega : j + 1 ≤ 5)
  have hterm : ∀ b ∈ Finset.range (j + 1), F b ^ 2
      ≤ 256 * (Rr r * Work.Spaces.HkIntegrand α 4 g z θ) := by
    intro b hb
    have hbj : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hb3 : b ≤ 3 := le_trans hbj hj3
    have h1 : ((j.choose b : ℕ) : ℝ) ^ 2 ≤ 256 := by
      have h := choose_le_sixteen (i := j) (b := b) (by omega)
      have h0 : (0 : ℝ) ≤ ((j.choose b : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [h, h0]
    have h2 : (Work.Elliptic.DzdIter b r z) ^ 2 ≤ Rr r := hI b hb3 z hz
    have h3 : (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i (j - b) hi (by omega)
    have h4 : 0 ≤ Rr r := Rr_nonneg r
    have hprod : (Work.Elliptic.DzdIter b r z) ^ 2
          * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Rr r * Work.Spaces.HkIntegrand α 4 g z θ :=
      mul_le_mul h2 h3 (sq_nonneg _) h4
    have hprod2 := mul_le_mul h1 hprod (by positivity) (by norm_num : (0:ℝ) ≤ 256)
    rw [hF]
    have hgoal : ((j.choose b : ℝ) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ))) ^ 2
        = ((j.choose b : ℝ)) ^ 2
          * ((Work.Elliptic.DzdIter b r z) ^ 2
              * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ) ^ 2) := by ring
    rw [hgoal]
    exact hprod2
  have hsum : (∑ b ∈ Finset.range (j + 1), F b ^ 2)
      ≤ 5 * (256 * (Rr r * Work.Spaces.HkIntegrand α 4 g z θ)) := by
    calc (∑ b ∈ Finset.range (j + 1), F b ^ 2)
        ≤ ∑ _b ∈ Finset.range (j + 1), (256 * (Rr r * Work.Spaces.HkIntegrand α 4 g z θ)) :=
          Finset.sum_le_sum hterm
      _ = ((Finset.range (j + 1)).card : ℝ)
            * (256 * (Rr r * Work.Spaces.HkIntegrand α 4 g z θ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 5 * (256 * (Rr r * Work.Spaces.HkIntegrand α 4 g z θ)) := by
          have h0 : 0 ≤ 256 * (Rr r * Work.Spaces.HkIntegrand α 4 g z θ) := by
            have h4 : 0 ≤ Rr r := Rr_nonneg r
            have h5 : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
              Work.Spaces.HkIntegrand_nonneg α 4 g z θ
            positivity
          exact mul_le_mul_of_nonneg_right hcard h0
  have h4 : 0 ≤ Rr r := Rr_nonneg r
  have h5 : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  nlinarith [hcs, hcard, hsum, h4, h5]

/-- **The pointwise bound on the `ℋ⁴`-integrand of the product.** -/
theorem HkIntegrand_prod_le (α : ℝ) (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ)
    (hr : Work.FTS.LocData.SmoothQuad (fun z θ => r z))
    (hg : Work.FTS.LocData.SmoothQuad g)
    (hI : ∀ b : ℕ, b ≤ 3 → ∀ z : ℝ, 0 < z → (Work.Elliptic.DzdIter b r z) ^ 2 ≤ Rr r)
    {θ : ℝ} (hQg : ∀ z : ℝ, 0 < z → (g z θ) ^ 2 ≤ Qg g θ)
    {z : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) z θ
      ≤ 4194304 * (Rr r) * Work.Spaces.HkIntegrand α 4 g z θ
        + 65536 * (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2 * smE θ * Qg g θ := by
  rw [Work.Spaces.HkIntegrand]
  have h4 : 0 ≤ Rr r := Rr_nonneg r
  have h5 : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  set B : ℝ := 65536 * (Rr r) * Work.Spaces.HkIntegrand α 4 g z θ with hB
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  -- the pure part
  have hZ : (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 5 * B + 65536 * (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2 * smE θ
          * Qg g θ := by
    rw [Finset.sum_range_succ (fun i => (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) 4]
    have hlow : (∑ i ∈ Finset.range 4, (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ 4 * B := by
      calc _ ≤ ∑ _i ∈ Finset.range 4, B := by
            refine Finset.sum_le_sum fun i hi => ?_
            exact le_trans (pure_slot_le α r g hr hg hI
              (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hz hθ) (le_of_eq hB)
        _ = 4 * B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
    have htop := pure_slot_four_le α r g hr hg hI hQg hz hθ
    linarith
  -- the mixed part
  have hM : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)) ≤ 25 * B := by
    have hinner : ∀ i ∈ Finset.range 5,
        (∑ j ∈ Finset.range 5, (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)) ≤ 5 * B := by
      intro i hi
      calc _ ≤ ∑ _j ∈ Finset.range 5, B := by
            refine Finset.sum_le_sum fun j hj => ?_
            by_cases hc : 1 ≤ i ∧ i + j ≤ 4
            · simp only [ite_eq_left hc]
              exact le_trans (mixed_slot_le α r g hr hg hI hc.1 hc.2 hz hθ) (le_of_eq hB)
            · simp only [ite_eq_right hc]
              exact hBnn
        _ = 5 * B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
    calc _ ≤ ∑ _i ∈ Finset.range 5, (5 * B) := Finset.sum_le_sum hinner
      _ = 25 * B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have htot := add_le_add hZ hM
  have hfin : 5 * B + 65536 * (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2 * smE θ
        * Qg g θ + 25 * B
      ≤ 4194304 * (Rr r) * Work.Spaces.HkIntegrand α 4 g z θ
        + 65536 * (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2 * smE θ * Qg g θ := by
    have h6 : 0 ≤ smE θ := smE_nonneg (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    have h7 : 0 ≤ Qg g θ := Qg_nonneg g θ
    rw [hB] at *
    nlinarith [h4, h5, h6, h7, sq_nonneg (Work.Elliptic.DzdIter 4 r z),
      sq_nonneg (Work.Spaces.w z)]
  have hRk : 0 ≤ (Rr r) * Work.Spaces.HkIntegrand α 4 g z θ := mul_nonneg h4 h5
  have hX : 0 ≤ (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2 * smE θ * Qg g θ := by
    have h6 : 0 ≤ smE θ := smE_nonneg (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    have h7 : 0 ≤ Qg g θ := Qg_nonneg g θ
    positivity
  linarith [htot, hfin, hRk, hX]

/-! ## Integration and the `ℋ⁴`-bound for the product -/

theorem HkSq_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : 0 ≤ Work.Spaces.HkSq α k f :=
  integral_nonneg fun _ => integral_nonneg fun _ => Work.Spaces.HkIntegrand_nonneg α k f _ _

/-- Inside the open angular interval, a `z`-slice of `psiZ` is dominated by the `ℋ⁴`-integrand
of `g`. -/
theorem psiZ_le_HkIntegrand_of_Ioo (α : ℝ) (g : ℝ → ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (s : ℝ) :
    psiZ g s θ ≤ Work.Spaces.HkIntegrand α 4 g s θ := by
  have hsin : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  have h1 : psiZ g s θ * smE θ
      = (Work.Spaces.DzIter 1 g s θ
          * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [psiZ, light_sq (Work.Spaces.DzIter 1 g s θ) s θ hsin]
  calc psiZ g s θ = psiZ g s θ * 1 := by ring
    _ ≤ psiZ g s θ * smE θ :=
        mul_le_mul_of_nonneg_left (one_le_smE hθ) (psiZ_nonneg g s θ)
    _ = _ := h1
    _ ≤ Work.Spaces.HkIntegrand α 4 g s θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 g s θ 1 (by norm_num)

/-- The angular-slice bound at a fixed `z > 0`. -/
theorem slice_le (α : ℝ) (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ)
    (hr : Work.FTS.LocData.SmoothQuad (fun z θ => r z))
    (hg : Work.FTS.LocData.SmoothQuad g)
    (hgm : Work.Spaces.HkMem α 4 g)
    (hI : ∀ b : ℕ, b ≤ 3 → ∀ z : ℝ, 0 < z → (Work.Elliptic.DzdIter b r z) ^ 2 ≤ Rr r)
    (hQg : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z : ℝ, 0 < z → (g z θ) ^ 2 ≤ Qg g θ)
    {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) z θ)
      ≤ 4194304 * (Rr r) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        + 65536 * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, smE θ * Qg g θ) := by
  have hK3 := integrable_smE_Qg_and_le α g hg hgm
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hstep1 : (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, (4194304 * (Rr r) * Work.Spaces.HkIntegrand α 4 g z θ
          + 65536 * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
            * (smE θ * Qg g θ)) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)
      ((hgm.1 z hzI).const_mul _ |>.add (hK3.1.const_mul _)) ?_
    filter_upwards [hQg, Work.H2.T1Q.ae_mem_Ioo_Iθ] with θ hQ hθ
    exact (HkIntegrand_prod_le α r g hr hg hI hQ hz hθ).trans (le_of_eq (by ring))
  have hstep2 : (∫ θ in Work.Spaces.Iθ,
        (4194304 * (Rr r) * Work.Spaces.HkIntegrand α 4 g z θ
          + 65536 * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
            * (smE θ * Qg g θ)))
      = 4194304 * (Rr r) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        + 65536 * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, smE θ * Qg g θ) := by
    rw [MeasureTheory.integral_add ((hgm.1 z hzI).const_mul _) (hK3.1.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  refine le_trans hstep1 ?_
  rw [hstep2]

/-- **The `ℋ⁴`-bound for the product**, integrated. -/
theorem HkSq_prod_le (α : ℝ) (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ)
    (hr : Work.FTS.LocData.SmoothQuad (fun z θ => r z))
    (hg : Work.FTS.LocData.SmoothQuad g)
    (hrm : Work.Spaces.HkMem α 4 (fun z θ => r z))
    (hgm : Work.Spaces.HkMem α 4 g)
    (hI : ∀ b : ℕ, b ≤ 3 → ∀ z : ℝ, 0 < z → (Work.Elliptic.DzdIter b r z) ^ 2 ≤ Rr r)
    (hQg : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z : ℝ, 0 < z → (g z θ) ^ 2 ≤ Qg g θ) :
    Work.Spaces.HkSq α 4 (fun z θ => r z * g z θ)
      ≤ 4294967296 * (Rr r) * Work.Spaces.HkSq α 4 g := by
  have hK3 := integrable_smE_Qg_and_le α g hg hgm
  have hPint : MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz := integrable_DzdIter_sq α r hr hrm 4 (by norm_num)
  have hPle : (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2) ≤ Rr r := by
    rw [Rr]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (integrable_Rint α r hrm) (Filter.Eventually.of_forall fun z => ?_)
    exact Finset.single_le_sum
      (f := fun i => (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Finset.mem_range.mpr (by norm_num))
  have hRnn : 0 ≤ Rr r := Rr_nonneg r
  have hDnn : 0 ≤ Work.Spaces.HkSq α 4 g := HkSq_nonneg α 4 g
  have hK3nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, smE θ * Qg g θ :=
    MeasureTheory.integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem
      measurableSet_Icc (fun θ hθ => mul_nonneg (smE_nonneg hθ) (Qg_nonneg g θ)))
  set G : ℝ → ℝ := fun z => 4194304 * (Rr r)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
      + 65536 * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, smE θ * Qg g θ) with hG
  have hGint : MeasureTheory.Integrable G (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [hG]
    exact (hgm.2.const_mul _).add ((hPint.const_mul 65536).mul_const _)
  have hmono : Work.Spaces.HkSq α 4 (fun z θ => r z * g z θ)
      ≤ ∫ z in Work.Spaces.Iz, G z := by
    rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => integral_nonneg fun θ => ?_) hGint ?_
    · exact Work.Spaces.HkIntegrand_nonneg α 4 _ z θ
    · have hmeas : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
          = MeasureTheory.volume.restrict Work.Spaces.Iz :=
        MeasureTheory.Measure.restrict_congr_set
          (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))
      rw [← hmeas]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
      rw [hG]
      exact slice_le α r g hr hg hgm hI hQg hz
  have hval : (∫ z in Work.Spaces.Iz, G z)
      = 4194304 * (Rr r) * Work.Spaces.HkSq α 4 g
        + 65536 * (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, smE θ * Qg g θ) := by
    rw [hG]
    simp only []
    rw [MeasureTheory.integral_add (hgm.2.const_mul _)
        ((hPint.const_mul 65536).mul_const _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const,
      MeasureTheory.integral_const_mul]
    rfl
  rw [hval] at hmono
  have hPK : (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
      * (∫ θ in Work.Spaces.Iθ, smE θ * Qg g θ) ≤ (Rr r) * Work.Spaces.HkSq α 4 g :=
    mul_le_mul hPle hK3.2 hK3nn hRnn
  have hPK2 : 65536 * ((∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
      * (∫ θ in Work.Spaces.Iθ, smE θ * Qg g θ))
      ≤ 65536 * ((Rr r) * Work.Spaces.HkSq α 4 g) :=
    mul_le_mul_of_nonneg_left hPK (by norm_num)
  nlinarith [hmono, hPK2, hRnn, hDnn]

/-! ## The universal constant -/

/-- The universal constant of `radial_prod`. -/
def Cconst : ℝ := 4096

theorem Cconst_pos : 0 < Cconst := by norm_num [Cconst]

/-- **The lossless radial product of design §3.2** (`radial_prod`): multiplying a function `g`
of the interior class by a function of `z` alone loses nothing in the weight `γ - 1 = α/10` of
the `ℋ⁴`-norm, because the `z`-direction embedding (`Work.FTS.H2.HQ.HardyZQ`, tex 1047) has no
`γ - 1` factor.  `∀ C` is taken outside `∀ α r g`, so `C` is a universal constant.

Route.  (i) Inside the open quadrant the Leibniz rules of the interior class
(`Work.FTS.H2.HQ.DzIter_mul_quad`, `Work.FTS.H2.HQ.mixed_mul_eq_quad`) give
`D_z^i (r·g) = Σ_b C(i,b)(D_z^b r)(D_z^{i-b} g)` and, since `D_θ r = 0`,
`D_z^j D_θ^i (r g) = Σ_b C(j,b)(D_z^b r)(D_z^{j-b}D_θ^i g)`.  Substitute into
`Work.Spaces.HkIntegrand` and expand the squares (finitely many terms).
(ii) For a term `(D_z^b r)·h` bound the factor of *smaller* `D_z`-order `≤ 2` pointwise by
`Work.FTS.H2.HQ.HardyZQ` applied to it (as a function of `z`, at fixed `θ`): its order is `≤ 2`,
so the next iterate has order `≤ 3 ≤ 4` and its weighted square is one of the `ℋ⁴`-slots of that
factor; `HardyZQ` gives `v(z)² ≤ ∫_s (s v'(s))² w(s)²` with constant `1` (no loss in `α`).
(iii) Integrate over `θ` and `z` (monotonicity of the Bochner integral — `HkMem` gives the
honest integrability of the total integrand, and for a.e. `θ` of the `θ`-slices) and identify the
surviving slots with `HkSq α 4` of the two factors: for the radial factor
`HkSq α 4 (fun z θ => r z) = (∫_θ sin(2θ)^{-η}) · Σ_{i≤4} ∫_z (D_z^i r)² w²`, and likewise each
slot of `g` is dominated by `HkSq α 4 g`.  The constant comes out universal (the reciprocal of
`∫_θ sin(2θ)^{-η} ≥ π/2` times a small binomial constant). -/
theorem radial_prod :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ),
      Work.FTS.LocData.SmoothQuad (fun z θ => r z) →
      Work.FTS.LocData.SmoothQuad g →
      Work.Spaces.HkMem α 4 (fun z θ => r z) →
      Work.Spaces.HkMem α 4 g →
      (∀ b : ℕ, b ≤ 4 →
        Filter.Tendsto (fun z : ℝ => Work.Spaces.DzIter b (fun z θ => r z) z 0)
          Filter.atTop (nhds 0)) →
      (∀ b : ℕ, b ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Filter.Tendsto (fun z : ℝ => Work.Spaces.DzIter b g z θ) Filter.atTop (nhds 0)) →
      Work.Spaces.HkMem α 4 (fun z θ => r z * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => r z * g z θ)
        ≤ C * Work.FTS.Nonlin.Xn α (fun z θ => r z) * Work.FTS.Nonlin.Xn α g := by
  refine ⟨65536, by norm_num, ?_⟩
  intro α hα hα1 r g hr hg hrm hgm hdecr hdecg
  have hdecr' : ∀ b : ℕ, b ≤ 4 →
      Filter.Tendsto (Work.Elliptic.DzdIter b r) Filter.atTop (nhds 0) := by
    intro b hb
    have h := hdecr b hb
    simpa only [Work.Elliptic.DzIter_rad] using h
  have hI : ∀ b : ℕ, b ≤ 3 → ∀ z : ℝ, 0 < z → (Work.Elliptic.DzdIter b r z) ^ 2 ≤ Rr r :=
    fun b hb z hz => DzdIter_sq_le_Rr α r hr hrm hdecr' hb hz
  have hrg : Work.FTS.LocData.SmoothQuad (fun z θ => r z * g z θ) :=
    Work.FTS.LocData.smoothQuad_mul hr hg
  have hQg_ae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z : ℝ, 0 < z → (g z θ) ^ 2 ≤ Qg g θ := by
    have hswap := Work.H2.T1Q.HkSqSwapQ α g hg hgm
    filter_upwards [hswap.2.2, Work.H2.T1Q.ae_mem_Ioo_Iθ] with θ hint hθ
    intro z hz
    have hintpsi : MeasureTheory.IntegrableOn (fun s => psiZ g s θ) Work.Spaces.Iz := by
      refine MeasureTheory.Integrable.mono' hint ?_ ?_
      · refine Work.H2.T1Q.aesm_Iz_of_continuousOn ?_
        exact (continuousOn_psiZ g hg).comp
          ((continuous_id.prodMk continuous_const).continuousOn)
          (fun s hs => ⟨hs, hθ⟩)
      · filter_upwards with s
        rw [Real.norm_of_nonneg (psiZ_nonneg g s θ)]
        exact psiZ_le_HkIntegrand_of_Ioo α g hθ s
    exact g_sq_le_Qg g hg hθ (hdecg 0 (by norm_num) θ hθ) hintpsi hz
  have hsq := HkSq_prod_le α r g hr hg hrm hgm hI hQg_ae
  have hK3 := integrable_smE_Qg_and_le α g hg hgm
  have hPint := integrable_DzdIter_sq α r hr hrm 4 (by norm_num)
  have hGint : MeasureTheory.Integrable (fun z : ℝ => 4194304 * (Rr r)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
      + 65536 * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, smE θ * Qg g θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (hgm.2.const_mul _).add ((hPint.const_mul 65536).mul_const _)
  have hmem_prod : Work.Spaces.HkMem α 4 (fun z θ => r z * g z θ) := by
    constructor
    · intro z hz
      rcases lt_or_eq_of_le (show (0 : ℝ) ≤ z from hz) with hzpos | rfl
      · have haesm : MeasureTheory.AEStronglyMeasurable
            (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) z θ)
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
          Work.H2.T1Q.aesm_Iθ_of_continuousOn
            ((Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 4 _ hrg).comp
              ((continuous_const.prodMk continuous_id).continuousOn)
              (fun θ hθ => ⟨hzpos, hθ⟩))
        have hInt : MeasureTheory.IntegrableOn (fun θ : ℝ => 4194304 * (Rr r)
              * Work.Spaces.HkIntegrand α 4 g z θ
            + 65536 * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * (smE θ * Qg g θ)) Work.Spaces.Iθ :=
          ((hgm.1 z hz).const_mul _).add (hK3.1.const_mul
            (65536 * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)))
        have hle : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
            ‖Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) z θ‖
              ≤ 4194304 * (Rr r) * Work.Spaces.HkIntegrand α 4 g z θ
                + 65536 * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
                  * (smE θ * Qg g θ) := by
          filter_upwards [hQg_ae, Work.H2.T1Q.ae_mem_Ioo_Iθ] with θ hQ hθ
          rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)]
          exact (HkIntegrand_prod_le α r g hr hg hI hQ hzpos hθ).trans (le_of_eq (by ring))
        exact MeasureTheory.Integrable.mono' hInt haesm hle
      · have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) 0 θ)
            = fun _ => (0 : ℝ) := by
          funext θ
          simp [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.w]
        rw [hzero]
        exact integrableOn_zero
    · have haesm : MeasureTheory.AEStronglyMeasurable
          (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) z θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
        (Work.Spaces.aesm_of_continuousOn_Qd
          (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) p.1 p.2)
          (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 4 _ hrg)).integral_prod_right'
      refine MeasureTheory.Integrable.mono' hGint haesm ?_
      have hmeas : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
          = MeasureTheory.volume.restrict Work.Spaces.Iz :=
        MeasureTheory.Measure.restrict_congr_set
          (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))
      rw [← hmeas]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)]
      exact slice_le α r g hr hg hgm hI hQg_ae hz
  refine ⟨hmem_prod, ?_⟩
  have hRle : Rr r ≤ Work.Spaces.HkSq α 4 (fun z θ => r z) := Rr_le_HkSq α r
  have hDnn : 0 ≤ Work.Spaces.HkSq α 4 g := HkSq_nonneg α 4 g
  have h1 : Work.Spaces.HkSq α 4 (fun z θ => r z * g z θ)
      ≤ (65536 * Real.sqrt (Rr r) * Real.sqrt (Work.Spaces.HkSq α 4 g)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (Rr_nonneg r), Real.sq_sqrt hDnn]
    calc Work.Spaces.HkSq α 4 (fun z θ => r z * g z θ)
        ≤ 4294967296 * (Rr r) * Work.Spaces.HkSq α 4 g := hsq
      _ = 65536 ^ 2 * ((Rr r) * Work.Spaces.HkSq α 4 g) := by norm_num; ring
      _ = 65536 ^ 2 * (Rr r) * Work.Spaces.HkSq α 4 g := by ring
  have h2 := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq (by positivity)] at h2
  have h3 : Real.sqrt (Rr r) ≤ Work.Spaces.HkNorm α 4 (fun z θ => r z) := by
    simp only [Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt hRle
  show Work.Spaces.HkNorm α 4 (fun z θ => r z * g z θ)
      ≤ 65536 * Work.Spaces.HkNorm α 4 (fun z θ => r z) * Work.Spaces.HkNorm α 4 g
  simp only [Work.Spaces.HkNorm]
  exact h2.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 65536)) (Real.sqrt_nonneg _))

end Work.FTS.Nonlinear.RadialProd
