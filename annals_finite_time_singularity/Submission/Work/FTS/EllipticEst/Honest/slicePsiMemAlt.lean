import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Honest.SliceSetup
import Submission.Work.FTS.EllipticEst.Honest.SliceMain
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false

local notation "sg" => Work.FTS.EllipticEst.AngSecond.sig

/-! ## Elementary measure-theoretic helpers -/

/-- `σ` is measurable. -/
theorem measurable_sig : Measurable sg := by
  show Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
  exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _

/-- `σ ∈ L¹((0,π/2))`. -/
theorem integrableOn_sig_Ioo : IntegrableOn sg (Set.Ioo 0 (Real.pi / 2)) := by
  have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
    (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_nonneg])).1
  have h2 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Set.Ioo 0 (Real.pi / 2)) := h.mono_set Set.Ioo_subset_Icc_self
  exact h2.congr_fun (fun θ _ => rfl) measurableSet_Ioo

/-- `σ ≥ 1` on the open quadrant. -/
theorem one_le_sg {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 1 ≤ sg θ :=
  Work.FTS.EllipticEst.AngSecond.one_le_sig hθ

/-- The `σ`-weighted square of a continuous function is a.e. strongly measurable. -/
theorem aestronglyMeasurable_sq_mul_sig {f : ℝ → ℝ} {s : Set ℝ} (hm : MeasurableSet s)
    (hf : ContinuousOn f s) :
    AEStronglyMeasurable (fun θ => f θ ^ 2 * sg θ) ((volume : Measure ℝ).restrict s) :=
  ((hf.aestronglyMeasurable hm).pow 2).mul measurable_sig.aestronglyMeasurable

/-- From `∫ f² σ < ∞` on a subinterval of the quadrant, get `∫ f² < ∞` (as `σ ≥ 1` there). -/
theorem integrableOn_sq_of_sq_mul_sig {f : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hsub : s ⊆ Set.Ioo 0 (Real.pi / 2))
    (hmeas : AEStronglyMeasurable f ((volume : Measure ℝ).restrict s))
    (hf : IntegrableOn (fun θ => f θ ^ 2 * sg θ) s) :
    IntegrableOn (fun θ => f θ ^ 2) s := by
  refine MeasureTheory.Integrable.mono' hf (hmeas.pow 2) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem hs] with θ hθ
  have h1 : 1 ≤ sg θ := one_le_sg (hsub hθ)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_nonneg (f θ), h1]

/-- On a finite-measure set, `f² ∈ L¹` implies `f ∈ L¹`. -/
theorem integrableOn_of_sq_integrable {f : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hfin : (volume : Measure ℝ) s ≠ ⊤)
    (hmeas : AEStronglyMeasurable f ((volume : Measure ℝ).restrict s))
    (h2 : IntegrableOn (fun x => f x ^ 2) s) :
    IntegrableOn f s := by
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) s :=
    MeasureTheory.integrableOn_const (C := (1 : ℝ)) hfin
  refine MeasureTheory.Integrable.mono' (h2.add hconst) hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem hs] with x hx
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|f x| - 1), sq_abs (f x), abs_nonneg (f x)]

/-- **Gluing**: integrability on two adjacent open pieces gives it on the union. -/
theorem integrableOn_Ioo_glue {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : IntegrableOn f (Set.Ioo a b)) (h2 : IntegrableOn f (Set.Ioo b c)) :
    IntegrableOn f (Set.Ioo a c) := by
  have h1' : IntegrableOn f (Set.Ioc a b) :=
    h1.congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc (a := a) (b := b)).symm
  have h2' : IntegrableOn f (Set.Ioc b c) :=
    h2.congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc (a := b) (b := c)).symm
  have hu : IntegrableOn f (Set.Ioc a b ∪ Set.Ioc b c) := h1'.union h2'
  rw [Set.Ioc_union_Ioc_eq_Ioc hab hbc] at hu
  exact hu.congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc (a := a) (b := c))

/-! ## The bound on `u'` near `0` -/

/-- `∫ (u'')² σ < ∞` bounds `u'` on `(0,π/8)`: `u'' ∈ L¹` there (`σ ≥ 1`, `u''` continuous),
so `u'` has a finite limit at `0`; the rest is compactness. -/
theorem deriv_u_bdd_near_zero {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hX : IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2))) :
    ∃ M : ℝ, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 8), |deriv u θ| ≤ M := by
  have hπ := Real.pi_pos
  have hsub8 : Set.Ioo (0 : ℝ) (Real.pi / 8) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨hx.1, lt_trans hx.2 (by linarith)⟩
  have hu'c : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hu''c : ContinuousOn (deriv (deriv u)) (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_deriv_deriv hu
  have hXsq : IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_sq_of_sq_mul_sig measurableSet_Ioo (fun θ hθ => hθ)
      (hu''c.aestronglyMeasurable measurableSet_Ioo) hX
  have hXsq8 : IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 8)) :=
    hXsq.mono_set hsub8
  have hu''L1 : IntegrableOn (deriv (deriv u)) (Set.Ioo (0 : ℝ) (Real.pi / 8)) := by
    have hmeas : AEStronglyMeasurable (deriv (deriv u))
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 8))) :=
      (hu''c.mono hsub8).aestronglyMeasurable measurableSet_Ioo
    refine MeasureTheory.Integrable.mono'
      (hXsq8.add (MeasureTheory.integrableOn_const (C := (1 : ℝ))
        (show (volume : Measure ℝ) (Set.Ioo (0 : ℝ) (Real.pi / 8)) ≠ ⊤ from by
          rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)))
      hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (deriv (deriv u) x), abs_nonneg (deriv (deriv u) x),
      sq_abs (deriv (deriv u) x)]
  have hderivDeriv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 8),
      HasDerivAt (deriv u) (deriv (deriv u) x) x := by
    intro x hx
    have h1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
      hu.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
    exact ((h1.contDiffAt (isOpen_Ioo.mem_nhds (hsub8 hx))).differentiableAt
      (by norm_num)).hasDerivAt
  obtain ⟨L0, hL0⟩ := Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv
    (δ := Real.pi / 8) (by linarith) hderivDeriv hu''L1
  have hev : {θ : ℝ | deriv u θ ∈ Set.Ioo (L0 - 1) (L0 + 1)} ∈ 𝓝[>] (0 : ℝ) :=
    hL0.eventually (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  obtain ⟨u0, hu0gt, hu0sub⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (show (0 : ℝ) < 1 by norm_num)).mp hev
  have hu0gt' : (0 : ℝ) < u0 := hu0gt
  have hbdd_on : ∀ θ ∈ Set.Ioo (0 : ℝ) u0, |deriv u θ| ≤ |L0| + 1 := by
    intro θ hθ
    have hb := hu0sub hθ
    rw [abs_le]
    exact ⟨by linarith [hb.1, neg_abs_le L0], by linarith [hb.2, le_abs_self L0]⟩
  by_cases hcase : Real.pi / 8 ≤ u0
  · exact ⟨|L0| + 1, fun θ hθ => hbdd_on θ ⟨hθ.1, lt_of_lt_of_le hθ.2 hcase⟩⟩
  · push_neg at hcase
    have hsubK : Set.Icc (u0 / 2) (Real.pi / 8) ⊆ Set.Ioo 0 (Real.pi / 2) := by
      intro x hx
      exact ⟨by linarith [hx.1, hu0gt'], lt_of_le_of_lt hx.2 (by linarith)⟩
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := u0 / 2) (b := Real.pi / 8)).exists_bound_of_continuousOn
      (hu'c.mono hsubK)
    refine ⟨max (|L0| + 1) C, fun θ hθ => ?_⟩
    rcases lt_or_ge θ u0 with hlt | hge
    · exact le_trans (hbdd_on θ ⟨hθ.1, hlt⟩) (le_max_left _ _)
    · have hmem : θ ∈ Set.Icc (u0 / 2) (Real.pi / 8) :=
        ⟨by linarith [hge, hu0gt'], hθ.2.le⟩
      exact le_trans (by simpa [Real.norm_eq_abs] using hC θ hmem) (le_max_right _ _)

/-! ## The two halves of the slice integrability -/

/-- **The near-`0` half.**  With `ψ = u/cos`, both `ψ²σ` and `(ψ')²σ` are integrable on
`(0,π/8)`: `ψ² ≤ 4u²`, `(ψ')² ≤ 32u² + 32 M²` where `M` bounds `u'` on `(0,π/8)`. -/
theorem psi_sq_mem_left {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hB : IntegrableOn (fun θ => (u θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2)))
    (hX : IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2))) :
    IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 * sg θ) (Set.Ioo (0 : ℝ) (Real.pi / 8)) ∧
    IntegrableOn (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 8)) := by
  set ψ : ℝ → ℝ := fun θ => u θ / Real.cos θ with hψ
  have hsub8 : Set.Ioo (0 : ℝ) (Real.pi / 8) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨hx.1, lt_trans hx.2 (by linarith [Real.pi_pos])⟩
  have hcos : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 < Real.cos θ := fun θ hθ =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hψcont : ContinuousOn ψ (Set.Ioo 0 (Real.pi / 2)) := by
    rw [hψ]
    exact (hu.div Real.contDiff_cos.contDiffOn fun θ hθ => ne_of_gt (hcos θ hθ)).continuousOn
  have hψ'c : ContinuousOn (deriv ψ) (Set.Ioo 0 (Real.pi / 2)) := by
    rw [hψ]; exact continuousOn_deriv_div_cos hu
  have hsig8 : IntegrableOn sg (Set.Ioo (0 : ℝ) (Real.pi / 8)) :=
    integrableOn_sig_Ioo.mono_set hsub8
  have hB8 : IntegrableOn (fun θ => (u θ) ^ 2 * sg θ) (Set.Ioo (0 : ℝ) (Real.pi / 8)) :=
    hB.mono_set hsub8
  obtain ⟨M0, hM0⟩ := deriv_u_bdd_near_zero hu hX
  have hM0nn : 0 ≤ M0 := by
    have h : |deriv u (Real.pi / 16)| ≤ M0 :=
      hM0 _ ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    linarith [abs_nonneg (deriv u (Real.pi / 16))]
  -- the derivative formula for `ψ`
  have hψ'formula : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 8),
      deriv ψ θ = (deriv u θ * Real.cos θ + u θ * Real.sin θ) / Real.cos θ ^ 2 := by
    intro θ hθ
    have hcid : ContDiffAt ℝ 2 u θ := hu.contDiffAt (isOpen_Ioo.mem_nhds (hsub8 hθ))
    have hUd : DifferentiableAt ℝ u θ := hcid.differentiableAt (by norm_num)
    simp only [hψ]
    change deriv (u / Real.cos) θ = _
    rw [deriv_div hUd Real.differentiableAt_cos (ne_of_gt (hcos θ (hsub8 hθ))),
      Real.deriv_cos]
    ring
  have hcos8 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 8), (1 : ℝ) / 2 ≤ Real.cos θ := by
    intro θ hθ
    have h1 : Real.cos (Real.pi / 3) ≤ Real.cos θ :=
      Real.cos_le_cos_of_nonneg_of_le_pi hθ.1.le (by linarith [Real.pi_pos])
        (by linarith [hθ.2, Real.pi_pos])
    rwa [Real.cos_pi_div_three] at h1
  -- `ψ² σ`
  have hpsi_sq : IntegrableOn (fun θ => (ψ θ) ^ 2 * sg θ) (Set.Ioo (0 : ℝ) (Real.pi / 8)) := by
    refine MeasureTheory.Integrable.mono' (hB8.const_mul 4)
      (aestronglyMeasurable_sq_mul_sig measurableSet_Ioo (hψcont.mono hsub8)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hc : (1 : ℝ) / 2 ≤ Real.cos θ := hcos8 θ hθ
    have hcpos : 0 < Real.cos θ := hcos θ (hsub8 hθ)
    have hsig : 0 ≤ sg θ := le_trans zero_le_one (one_le_sg (hsub8 hθ))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hsig]
    have h1 : (ψ θ) ^ 2 = (u θ) ^ 2 / Real.cos θ ^ 2 := by
      rw [hψ]; simp only; rw [div_pow]
    have h2 : (u θ) ^ 2 / Real.cos θ ^ 2 ≤ 4 * (u θ) ^ 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.cos θ ^ 2)]
      have h4 : (1 : ℝ) ≤ 4 * Real.cos θ ^ 2 := by nlinarith [hc, hcpos]
      have h5 := mul_le_mul_of_nonneg_left h4 (sq_nonneg (u θ))
      linarith [h5]
    have h3 : (ψ θ) ^ 2 ≤ 4 * (u θ) ^ 2 := by rw [h1]; exact h2
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h3 hsig
  -- `(ψ')² σ`
  have hpsi'_sq : IntegrableOn (fun θ => (deriv ψ θ) ^ 2 * sg θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 8)) := by
    refine MeasureTheory.Integrable.mono'
      ((hB8.const_mul 32).add (hsig8.const_mul (32 * M0 ^ 2)))
      (aestronglyMeasurable_sq_mul_sig measurableSet_Ioo (hψ'c.mono hsub8)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 8) := hθ
    have hc : (1 : ℝ) / 2 ≤ Real.cos θ := hcos8 θ hθ'
    have hcpos : 0 < Real.cos θ := hcos θ (hsub8 hθ')
    have hsig : 0 ≤ sg θ := le_trans zero_le_one (one_le_sg (hsub8 hθ'))
    have hM := hM0 θ hθ'
    have hnum : |deriv u θ * Real.cos θ + u θ * Real.sin θ| ≤ M0 + |u θ| := by
      have h1 : |deriv u θ * Real.cos θ + u θ * Real.sin θ| ≤ |deriv u θ| + |u θ| := by
        calc |deriv u θ * Real.cos θ + u θ * Real.sin θ|
            ≤ |deriv u θ * Real.cos θ| + |u θ * Real.sin θ| := abs_add_le _ _
          _ ≤ |deriv u θ| + |u θ| := by
              rw [abs_mul, abs_mul]
              have hc1 : |Real.cos θ| ≤ 1 :=
                abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
              have hs1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
              nlinarith [abs_nonneg (deriv u θ), abs_nonneg (u θ), hc1, hs1]
      linarith [h1, hM]
    have hψ' : |deriv ψ θ| ≤ 4 * (M0 + |u θ|) := by
      rw [hψ'formula θ hθ', abs_div, abs_of_pos (pow_pos hcpos 2)]
      rw [div_le_iff₀ (show (0 : ℝ) < Real.cos θ ^ 2 from pow_pos hcpos 2)]
      have hcs : (1 : ℝ) / 4 ≤ Real.cos θ ^ 2 := by nlinarith [hc, hcpos]
      have hcs' : (1 : ℝ) ≤ 4 * Real.cos θ ^ 2 := by linarith
      have h4 := mul_le_mul_of_nonneg_left hcs' (by positivity : (0 : ℝ) ≤ M0 + |u θ|)
      linarith [hnum, h4]
    have hsq : (4 * (M0 + |u θ|)) ^ 2 ≤ 32 * M0 ^ 2 + 32 * (u θ) ^ 2 := by
      have h1 : |u θ| ^ 2 = (u θ) ^ 2 := sq_abs (u θ)
      nlinarith [sq_nonneg (M0 - |u θ|), h1]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hsig]
    have h5 : (deriv ψ θ) ^ 2 ≤ 32 * M0 ^ 2 + 32 * (u θ) ^ 2 := by
      have h6 : (deriv ψ θ) ^ 2 = |deriv ψ θ| ^ 2 := (sq_abs (deriv ψ θ)).symm
      rw [h6]
      exact le_trans (pow_le_pow_left₀ (abs_nonneg _) hψ' 2) hsq
    have h7 : (deriv ψ θ) ^ 2 * sg θ
        ≤ 32 * (u θ) ^ 2 * sg θ + (32 * M0 ^ 2) * sg θ := by
      have h8 := mul_le_mul_of_nonneg_right h5 hsig
      linarith [h8]
    simp only [Pi.add_apply]
    linarith [h7]
  rw [hψ] at hpsi_sq hpsi'_sq
  exact ⟨hpsi_sq, hpsi'_sq⟩

/-- **The near-`π/2` half.**  With `ψ = u/cos`: `(ψ')²σ` is integrable on `(π/4,π/2)` by
hypothesis (`sin²θ ≥ 1/2` there), hence `ψ' ∈ L¹` near `π/2`, so `ψ` has a finite limit at
`π/2` and is therefore bounded there; the middle piece `(π/8,π/4)` is compact. -/
theorem psi_sq_mem_right {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hY : IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2))) :
    IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 * sg θ) (Set.Ioo (Real.pi / 8) (Real.pi / 2)) ∧
    IntegrableOn (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ)
      (Set.Ioo (Real.pi / 8) (Real.pi / 2)) := by
  set ψ : ℝ → ℝ := fun θ => u θ / Real.cos θ with hψ
  have h8 : (0 : ℝ) < Real.pi / 8 := by linarith [Real.pi_pos]
  have h4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hsub44 : Set.Ioo (Real.pi / 8) (Real.pi / 4) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨lt_trans h8 hx.1, lt_trans hx.2 (by linarith [Real.pi_pos])⟩
  have hsub42 : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨lt_trans h4 hx.1, hx.2⟩
  have hsubIcc44 : Set.Icc (Real.pi / 8) (Real.pi / 4) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨lt_of_lt_of_le h8 hx.1, lt_of_le_of_lt hx.2 (by linarith [Real.pi_pos])⟩
  have hcos : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 < Real.cos θ := fun θ hθ =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hψcd : ContDiffOn ℝ 2 ψ (Set.Ioo 0 (Real.pi / 2)) := by
    rw [hψ]
    exact hu.div Real.contDiff_cos.contDiffOn fun θ hθ => ne_of_gt (hcos θ hθ)
  have hψc : ContinuousOn ψ (Set.Ioo 0 (Real.pi / 2)) := hψcd.continuousOn
  have hψ'c : ContinuousOn (deriv ψ) (Set.Ioo 0 (Real.pi / 2)) := by
    rw [hψ]; exact continuousOn_deriv_div_cos hu
  have hsig44 : IntegrableOn sg (Set.Ioo (Real.pi / 8) (Real.pi / 4)) :=
    integrableOn_sig_Ioo.mono_set hsub44
  -- the middle piece: boundedness on the compact `[π/8, π/4]`
  have hmid : IntegrableOn (fun θ => (ψ θ) ^ 2 * sg θ) (Set.Ioo (Real.pi / 8) (Real.pi / 4)) ∧
      IntegrableOn (fun θ => (deriv ψ θ) ^ 2 * sg θ) (Set.Ioo (Real.pi / 8) (Real.pi / 4)) := by
    obtain ⟨C1, hC1⟩ := (isCompact_Icc (a := Real.pi / 8) (b := Real.pi / 4)).exists_bound_of_continuousOn
      (hψc.mono hsubIcc44)
    obtain ⟨C2, hC2⟩ := (isCompact_Icc (a := Real.pi / 8) (b := Real.pi / 4)).exists_bound_of_continuousOn
      (hψ'c.mono hsubIcc44)
    constructor
    · refine MeasureTheory.Integrable.mono' (hsig44.const_mul (C1 ^ 2))
        (aestronglyMeasurable_sq_mul_sig measurableSet_Ioo (hψc.mono hsub44)) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hmem : θ ∈ Set.Icc (Real.pi / 8) (Real.pi / 4) := ⟨hθ.1.le, hθ.2.le⟩
      have hsig : 0 ≤ sg θ := le_trans zero_le_one (one_le_sg (hsub44 hθ))
      have h1 : |ψ θ| ≤ C1 := by simpa [Real.norm_eq_abs] using hC1 θ hmem
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hsig]
      exact mul_le_mul_of_nonneg_right (by nlinarith [abs_nonneg (ψ θ), h1, sq_abs (ψ θ)]) hsig
    · refine MeasureTheory.Integrable.mono' (hsig44.const_mul (C2 ^ 2))
        (aestronglyMeasurable_sq_mul_sig measurableSet_Ioo (hψ'c.mono hsub44)) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hmem : θ ∈ Set.Icc (Real.pi / 8) (Real.pi / 4) := ⟨hθ.1.le, hθ.2.le⟩
      have hsig : 0 ≤ sg θ := le_trans zero_le_one (one_le_sg (hsub44 hθ))
      have h1 : |deriv ψ θ| ≤ C2 := by simpa [Real.norm_eq_abs] using hC2 θ hmem
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hsig]
      exact mul_le_mul_of_nonneg_right
        (by nlinarith [abs_nonneg (deriv ψ θ), h1, sq_abs (deriv ψ θ)]) hsig
  -- the piece `(π/4, π/2)`: `(ψ')²σ` from the hypothesis
  have hsq42' : IntegrableOn (fun θ => (deriv ψ θ) ^ 2 * sg θ)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    have hY' : IntegrableOn (fun θ => (Real.sin θ) ^ 2 * (deriv ψ θ) ^ 2 * sg θ)
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
      rw [hψ] at hY
      exact hY.mono_set hsub42
    refine MeasureTheory.Integrable.mono' (hY'.const_mul 2)
      (aestronglyMeasurable_sq_mul_sig measurableSet_Ioo (hψ'c.mono hsub42)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hθ' : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2) := hθ
    have hsin : (1 : ℝ) / 2 ≤ Real.sin θ ^ 2 := by
      have h1 : Real.sin (Real.pi / 4) ≤ Real.sin θ :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi / 4) (y := θ)
          (by linarith [Real.pi_pos]) (by linarith [hθ'.2, Real.pi_pos]) hθ'.1.le
      rw [Real.sin_pi_div_four] at h1
      have h2 : (Real.sqrt 2 / 2) ^ 2 = (1 : ℝ) / 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
      have h4 : (Real.sqrt 2 / 2) ^ 2 ≤ Real.sin θ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      linarith [h2, h4]
    have hsig : 0 ≤ sg θ := le_trans zero_le_one (one_le_sg (hsub42 hθ'))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hsig]
    have h4 : (deriv ψ θ) ^ 2 ≤ 2 * (Real.sin θ ^ 2 * (deriv ψ θ) ^ 2) := by
      nlinarith [sq_nonneg (deriv ψ θ), hsin]
    calc (deriv ψ θ) ^ 2 * sg θ ≤ 2 * (Real.sin θ ^ 2 * (deriv ψ θ) ^ 2) * sg θ :=
          mul_le_mul_of_nonneg_right h4 hsig
      _ = 2 * (Real.sin θ ^ 2 * (deriv ψ θ) ^ 2 * sg θ) := by ring
  -- `ψ' ∈ L¹` there, so `ψ` has a limit at `π/2`
  have hsq42 : IntegrableOn (fun θ => (deriv ψ θ) ^ 2) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    integrableOn_sq_of_sq_mul_sig measurableSet_Ioo hsub42
      ((hψ'c.mono hsub42).aestronglyMeasurable measurableSet_Ioo) hsq42'
  have hL1 : IntegrableOn (deriv ψ) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    integrableOn_of_sq_integrable measurableSet_Ioo
      (show (volume : Measure ℝ) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) ≠ ⊤ from by
        rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      ((hψ'c.mono hsub42).aestronglyMeasurable measurableSet_Ioo) hsq42
  obtain ⟨Lπ, hLπ⟩ := exists_tendsto_nhdsLT_of_integrableOn_deriv (a := Real.pi / 4)
    (b := Real.pi / 2) (by linarith [Real.pi_pos])
    (fun x hx => ((hψcd.contDiffAt (isOpen_Ioo.mem_nhds (hsub42 hx))).differentiableAt
      (by norm_num)).hasDerivAt) hL1
  -- `ψ` is bounded near `π/2`
  obtain ⟨δp, hδp_pos, hδp_lt, hδp_bdd⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < Real.pi / 4 ∧
      ∀ θ ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), |ψ θ| ≤ |Lπ| + 1 := by
    have hev : {θ : ℝ | ψ θ ∈ Set.Ioo (Lπ - 1) (Lπ + 1)} ∈ 𝓝[<] (Real.pi / 2) :=
      hLπ.eventually (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
    obtain ⟨t, ht_lt, htsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).mp hev
    have ht_lt' : t < Real.pi / 2 := ht_lt
    refine ⟨min (Real.pi / 2 - t) (Real.pi / 8), lt_min (by linarith) (by linarith),
      lt_of_le_of_lt (min_le_right _ _) (by linarith), fun θ hθ => ?_⟩
    have hδle : min (Real.pi / 2 - t) (Real.pi / 8) ≤ Real.pi / 2 - t := min_le_left _ _
    have hmem : θ ∈ Set.Ioo t (Real.pi / 2) := ⟨by linarith [hθ.1, hδle], hθ.2⟩
    have hb := htsub hmem
    rw [abs_le]
    exact ⟨by linarith [hb.1, neg_abs_le Lπ], by linarith [hb.2, le_abs_self Lπ]⟩
  have hsub_tail : Set.Ioo (Real.pi / 2 - δp) (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨by linarith [hδp_pos, hδp_lt, hx.1], hx.2⟩
  have hsq_tail : IntegrableOn (fun θ => (ψ θ) ^ 2 * sg θ)
      (Set.Ioo (Real.pi / 2 - δp) (Real.pi / 2)) := by
    refine MeasureTheory.Integrable.mono'
      ((integrableOn_sig_Ioo.mono_set hsub_tail).const_mul ((|Lπ| + 1) ^ 2))
      (aestronglyMeasurable_sq_mul_sig measurableSet_Ioo (hψc.mono hsub_tail)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hsig : 0 ≤ sg θ := le_trans zero_le_one (one_le_sg (hsub_tail hθ))
    have h1 : |ψ θ| ≤ |Lπ| + 1 := hδp_bdd θ hθ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hsig]
    exact mul_le_mul_of_nonneg_right (by nlinarith [abs_nonneg (ψ θ), h1, sq_abs (ψ θ)]) hsig
  have hsub_mid : Set.Ioo (Real.pi / 4) (Real.pi / 2 - δp) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨lt_trans h4 hx.1, lt_trans hx.2 (by linarith [Real.pi_pos])⟩
  have hsubIcc_mid : Set.Icc (Real.pi / 4) (Real.pi / 2 - δp) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨lt_of_lt_of_le h4 hx.1, lt_of_le_of_lt hx.2 (by linarith [Real.pi_pos])⟩
  have hsq_mid : IntegrableOn (fun θ => (ψ θ) ^ 2 * sg θ)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2 - δp)) := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := Real.pi / 4)
      (b := Real.pi / 2 - δp)).exists_bound_of_continuousOn (hψc.mono hsubIcc_mid)
    refine MeasureTheory.Integrable.mono'
      ((integrableOn_sig_Ioo.mono_set hsub_mid).const_mul (C ^ 2))
      (aestronglyMeasurable_sq_mul_sig measurableSet_Ioo (hψc.mono hsub_mid)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hmem : θ ∈ Set.Icc (Real.pi / 4) (Real.pi / 2 - δp) := ⟨hθ.1.le, hθ.2.le⟩
    have hsig : 0 ≤ sg θ := le_trans zero_le_one (one_le_sg (hsub_mid hθ))
    have h1 : |ψ θ| ≤ C := by simpa [Real.norm_eq_abs] using hC θ hmem
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hsig]
    exact mul_le_mul_of_nonneg_right (by nlinarith [abs_nonneg (ψ θ), h1, sq_abs (ψ θ)]) hsig
  have hsq42 : IntegrableOn (fun θ => (ψ θ) ^ 2 * sg θ) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    integrableOn_Ioo_glue (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      hsq_mid hsq_tail
  have hsq82 : IntegrableOn (fun θ => (ψ θ) ^ 2 * sg θ) (Set.Ioo (Real.pi / 8) (Real.pi / 2)) :=
    integrableOn_Ioo_glue (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hmid.1 hsq42
  have hsq82' : IntegrableOn (fun θ => (deriv ψ θ) ^ 2 * sg θ)
      (Set.Ioo (Real.pi / 8) (Real.pi / 2)) :=
    integrableOn_Ioo_glue (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hmid.2 hsq42'
  rw [hψ] at hsq82 hsq82'
  exact ⟨hsq82, hsq82'⟩

/-- **`∫ ψ² σ < ∞` and `∫ (ψ')² σ < ∞` on a slice**, from the honest slice hypotheses
(`σ θ = sin(2θ)^{-η}`, `ψ = u/cos θ`). -/
theorem slice_psi_mem_alt (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hu0 : u 0 = 0) (hu1 : u (Real.pi / 2) = 0)
    (hB : IntegrableOn (fun θ => (u θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2)))
    (hX : IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2)))
    (hY : IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2))) :
    IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2)) ∧
    IntegrableOn (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  obtain ⟨h1, h1'⟩ := psi_sq_mem_left hu hB hX
  obtain ⟨h2, h2'⟩ := psi_sq_mem_right hu hY
  exact ⟨integrableOn_Ioo_glue (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) h1 h2,
    integrableOn_Ioo_glue (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) h1' h2'⟩

end Work.FTS.EllipticEst.Honest
