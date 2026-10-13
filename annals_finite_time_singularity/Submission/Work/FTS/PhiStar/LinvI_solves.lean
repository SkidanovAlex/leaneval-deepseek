/-
# `Work.FTS.PhiStar.LinvI_solves` — the zero-moment Dirichlet inverse solves `L₀u = h`

With `μ θ = sin²θ cos³θ`, `Linv h = -μ⁻¹ ∫_0^θ μ h / sin 2θ` and `LinvI h = ∫_0^θ Linv h`, the
claim is `Lzero1 (sin 2θ · LinvI h) = h` on `(0, π/2)`.  On `(0, π/2)` the factor `sin 2θ`
cancels one `sin`, so `μ h / sin 2θ = (sin θ cos²θ / 2) h` is bounded and the two fundamental
theorems of calculus apply with only boundedness of `h` at `θ = 0⁺`.

The proof is the direct computation (reducing it to the substitution identity of
`lzero_sin_cos_mul`)

  `Lzero1 (sin 2θ · v) = -sin 2θ · v'' + (6 - 10 cos²θ) · v'`

together with the explicit derivatives `v' = Linv h`, `v'' = (Linv h)'`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.H2.StarPkg.LzeroSubst.lzero_sin_cos_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Notation: the weight `μ`, the integrand and its primitive -/

/-- `μ θ = sin²θ cos³θ`, the weight of the `Linv` integral. -/
def LinvMu (θ : ℝ) : ℝ := Real.sin θ ^ 2 * Real.cos θ ^ 3

/-- The integrand `μ θ · h θ / sin 2θ` of the `Linv` integral. -/
def LinvInt (h : ℝ → ℝ) (θ : ℝ) : ℝ := LinvMu θ * h θ / Work.Construction.s2 θ

/-- `∫_0^θ μ h / sin 2θ`, so that `Linv h = -μ⁻¹ · LinvPrim h`. -/
def LinvPrim (h : ℝ → ℝ) (θ : ℝ) : ℝ := ∫ θ' in (0 : ℝ)..θ, LinvInt h θ'

lemma Linv_eq (h : ℝ → ℝ) :
    Linv h = fun θ => -((LinvMu θ)⁻¹ * LinvPrim h θ) := rfl

/-! ## Elementary facts about `μ`, `sin 2θ` and `h` -/

lemma linv_sin_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin θ :=
  Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_gt_three])

lemma linv_cos_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩

lemma linv_s2_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Work.Construction.s2 θ := by
  rw [Work.Construction.s2_eq, Real.sin_two_mul]
  exact mul_pos (mul_pos two_pos (linv_sin_pos hθ)) (linv_cos_pos hθ)

lemma linv_s2_ne_zero {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Construction.s2 θ ≠ 0 := ne_of_gt (linv_s2_pos hθ)

lemma continuous_LinvMu : Continuous LinvMu := by
  unfold LinvMu; fun_prop

lemma continuous_s2 : Continuous Work.Construction.s2 := by
  rw [show Work.Construction.s2 = fun θ : ℝ => Real.sin (2 * θ) from
    funext Work.Construction.s2_eq]
  fun_prop

lemma LinvMu_ne_zero_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    LinvMu θ ≠ 0 := by
  have hs : Real.sin θ ≠ 0 := ne_of_gt (linv_sin_pos hθ)
  have hc : Real.cos θ ≠ 0 := ne_of_gt (linv_cos_pos hθ)
  simp only [LinvMu]
  exact mul_ne_zero (pow_ne_zero 2 hs) (pow_ne_zero 3 hc)

lemma continuousAt_LinvInt {h : ℝ → ℝ} (hcont : ContinuousOn h (Set.Ioo 0 (Real.pi / 2)))
    {t : ℝ} (ht : t ∈ Set.Ioo 0 (Real.pi / 2)) : ContinuousAt (LinvInt h) t := by
  have h1 : ContinuousAt (fun s => LinvMu s * h s) t :=
    continuous_LinvMu.continuousAt.mul (hcont.continuousAt (isOpen_Ioo.mem_nhds ht))
  have h2 : ContinuousAt Work.Construction.s2 t := continuous_s2.continuousAt
  exact h1.div h2 (linv_s2_ne_zero ht)

/-- The integrand of `Linv` equals `sin θ cos²θ h θ / 2` (identically, both sides being `0`
where `sin 2θ = 0`). -/
lemma LinvInt_eq (h : ℝ → ℝ) (t : ℝ) :
    LinvInt h t = Real.sin t * Real.cos t ^ 2 / 2 * h t := by
  rw [LinvInt, LinvMu, Work.Construction.s2_eq, Real.sin_two_mul]
  field_simp

lemma abs_LinvInt_le {h : ℝ → ℝ} {θ t M : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hM : ∀ s ∈ Set.Ioo 0 (Real.pi / 2), |h s| ≤ M) (ht : t ∈ Set.Ioc 0 θ) :
    |LinvInt h t| ≤ M / 2 := by
  have ht' : t ∈ Set.Ioo 0 (Real.pi / 2) := ⟨ht.1, lt_of_le_of_lt ht.2 hθ.2⟩
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM t ht')
  rw [LinvInt_eq h t, abs_mul]
  have h1 : |Real.sin t * Real.cos t ^ 2 / 2| ≤ 1 / 2 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2),
      abs_of_nonneg (sq_nonneg (Real.cos t))]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    have hs : |Real.sin t| ≤ 1 := Real.abs_sin_le_one t
    have hc : Real.cos t ^ 2 ≤ 1 := Real.cos_sq_le_one t
    nlinarith [abs_nonneg (Real.sin t), sq_nonneg (Real.cos t)]
  have h2 : |h t| ≤ M := hM t ht'
  calc |Real.sin t * Real.cos t ^ 2 / 2| * |h t| ≤ 1 / 2 * M :=
        mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = M / 2 := by ring

/-! ## Derivative of the weight -/

lemma hasDerivAt_LinvMu (θ : ℝ) :
    HasDerivAt LinvMu (2 * Real.sin θ * Real.cos θ ^ 4 - 3 * Real.sin θ ^ 3 * Real.cos θ ^ 2)
      θ := by
  have h1 : HasDerivAt (fun t : ℝ => Real.sin t ^ 2) (2 * Real.sin θ * Real.cos θ) θ := by
    have h := (Real.hasDerivAt_sin θ).pow 2
    convert h using 1
    · ring
  have h2 : HasDerivAt (fun t : ℝ => Real.cos t ^ 3) (-3 * Real.sin θ * Real.cos θ ^ 2) θ := by
    have h := (Real.hasDerivAt_cos θ).pow 3
    convert h using 1
    ring
  have hmain := h1.mul h2
  convert hmain using 1
  · funext t
    simp only [LinvMu, Pi.mul_apply]
  · ring

lemma Linv_apply (h : ℝ → ℝ) (θ : ℝ) :
    Linv h θ = -((LinvMu θ)⁻¹ * LinvPrim h θ) := rfl

/-! ## The substitution identity for `Lzero1` -/

theorem Lzero1_sin2_mul {v : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hd1 : DifferentiableOn ℝ v (Set.Ioo 0 (Real.pi / 2)))
    (hd2 : DifferentiableOn ℝ (deriv v) (Set.Ioo 0 (Real.pi / 2))) :
    Work.FTS.EllipticEst.Lzero1 (fun t => Real.sin (2 * t) * v t) θ
      = -Real.sin (2 * θ) * deriv (deriv v) θ
        + (6 - 10 * Real.cos θ ^ 2) * deriv v θ := by
  have hw1 : DifferentiableOn ℝ (fun t : ℝ => 2 * v t) (Set.Ioo 0 (Real.pi / 2)) :=
    fun t ht => (hd1 t ht).const_mul 2
  have hw2 : DifferentiableOn ℝ (deriv (fun t : ℝ => 2 * v t)) (Set.Ioo 0 (Real.pi / 2)) := by
    intro t ht
    have heq : deriv (fun s : ℝ => 2 * v s) = fun s => 2 * deriv v s := by
      funext s; rw [Work.Spaces.deriv_const_mul']
    rw [heq]
    exact (hd2 t ht).const_mul 2
  have hsub := Work.FTS.H2.StarPkg.LzeroSubst.lzero_sin_cos_mul (fun _ t : ℝ => 2 * v t)
    (z := 0) (θ := θ) hθ hw1 hw2
  have hpth : Work.Spaces.pth (fun _ s : ℝ => 2 * v s) 0 θ = 2 * deriv v θ := by
    rw [Work.Spaces.pth, Work.Spaces.deriv_const_mul']
  have hpth2 : Work.Spaces.pthIter 2 (fun _ s : ℝ => 2 * v s) 0 θ
      = 2 * deriv (deriv v) θ := by
    show deriv (fun t : ℝ => Work.Spaces.pth (fun _ s : ℝ => 2 * v s) 0 t) θ = _
    have hev : (fun t : ℝ => Work.Spaces.pth (fun _ s : ℝ => 2 * v s) 0 t)
        = fun t : ℝ => 2 * deriv v t := by
      funext t; rw [Work.Spaces.pth, Work.Spaces.deriv_const_mul']
    rw [hev, Work.Spaces.deriv_const_mul']
  have hfun : (fun x t : ℝ => Real.sin (2 * t) * v t)
      = fun x t : ℝ => Real.sin t * Real.cos t * (2 * v t) := by
    funext x t; rw [Real.sin_two_mul]; ring
  rw [Work.FTS.EllipticEst.Lzero1_eq_Lzero]
  simp only []
  rw [hfun, hsub, hpth, hpth2, Real.sin_two_mul]
  rw [show Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 by linarith [Real.sin_sq_add_cos_sq θ]]
  ring

/-! ## The two fundamental-theorem-of-calculus steps for `Linv` -/

lemma intervalIntegrable_LinvInt {h : ℝ → ℝ} (hcont : ContinuousOn h (Set.Ioo 0 (Real.pi / 2)))
    (hbdd : ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |h θ| ≤ M)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    IntervalIntegrable (LinvInt h) volume 0 θ := by
  obtain ⟨M, hM⟩ := hbdd
  have hcontIoo : ContinuousOn (LinvInt h) (Set.Ioo 0 θ) := fun t ht =>
    (continuousAt_LinvInt hcont ⟨ht.1, lt_trans ht.2 hθ.2⟩).continuousWithinAt
  have haes : AEStronglyMeasurable (LinvInt h) (volume.restrict (Set.Ioc 0 θ)) := by
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    exact hcontIoo.aestronglyMeasurable measurableSet_Ioo
  rw [intervalIntegrable_iff, Set.uIoc_of_le (le_of_lt hθ.1)]
  refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top haes M ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  refine Filter.Eventually.of_forall (fun x hx => ?_)
  rw [Real.norm_eq_abs]
  refine le_trans (abs_LinvInt_le hθ hM hx) ?_
  linarith [le_trans (abs_nonneg (h θ)) (hM θ hθ)]

lemma hasDerivAt_LinvPrim {h : ℝ → ℝ} (hcont : ContinuousOn h (Set.Ioo 0 (Real.pi / 2)))
    (hbdd : ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |h θ| ≤ M)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (LinvPrim h) (LinvInt h θ) θ := by
  have hInt := intervalIntegrable_LinvInt hcont hbdd hθ
  have hmeas : StronglyMeasurableAtFilter (LinvInt h) (𝓝 θ) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
      (fun x hx => continuousAt_LinvInt hcont hx) θ hθ
  exact intervalIntegral.integral_hasDerivAt_right hInt hmeas (continuousAt_LinvInt hcont hθ)

lemma abs_LinvInt_le_sin {h : ℝ → ℝ} {θ M : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hM : ∀ s ∈ Set.Ioo 0 (Real.pi / 2), |h s| ≤ M) {t : ℝ} (ht : t ∈ Set.Ioc 0 θ) :
    ∀ u ∈ Set.Icc 0 t, |LinvInt h u| ≤ M / 2 * Real.sin u := by
  intro u hu
  rcases eq_or_lt_of_le hu.1 with h0 | h0
  · subst h0
    have hzero : LinvInt h 0 = 0 := by simp [LinvInt, LinvMu]
    rw [hzero, abs_zero, Real.sin_zero, mul_zero]
  · have hu' : u ∈ Set.Ioo 0 (Real.pi / 2) :=
      ⟨h0, lt_of_le_of_lt hu.2 (lt_of_le_of_lt ht.2 hθ.2)⟩
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM u hu')
    have hsin : 0 ≤ Real.sin u := le_of_lt (linv_sin_pos hu')
    rw [LinvInt_eq h u, abs_mul]
    have h1 : |Real.sin u * Real.cos u ^ 2 / 2| ≤ Real.sin u / 2 := by
      rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_nonneg hsin,
        abs_of_nonneg (sq_nonneg (Real.cos u))]
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
      have hc : Real.cos u ^ 2 ≤ 1 := Real.cos_sq_le_one u
      nlinarith [sq_nonneg (Real.cos u)]
    calc |Real.sin u * Real.cos u ^ 2 / 2| * |h u| ≤ Real.sin u / 2 * M :=
          mul_le_mul h1 (hM u hu') (abs_nonneg _) (by linarith)
      _ = M / 2 * Real.sin u := by ring

lemma abs_LinvPrim_le {h : ℝ → ℝ} {M : ℝ} (hcont : ContinuousOn h (Set.Ioo 0 (Real.pi / 2)))
    (hM : ∀ s ∈ Set.Ioo 0 (Real.pi / 2), |h s| ≤ M)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) {t : ℝ} (ht : t ∈ Set.Ioc 0 θ) :
    |LinvPrim h t| ≤ M * t ^ 2 / 4 := by
  have ht' : t ∈ Set.Ioo 0 (Real.pi / 2) := ⟨ht.1, lt_of_le_of_lt ht.2 hθ.2⟩
  have hInt := intervalIntegrable_LinvInt hcont ⟨M, hM⟩ ⟨ht.1, lt_of_le_of_lt ht.2 hθ.2⟩
  have hInt2 : IntervalIntegrable (fun u : ℝ => M / 2 * Real.sin u) volume 0 t :=
    (continuous_const.mul Real.continuous_sin).intervalIntegrable _ _
  have hval : (∫ u in (0:ℝ)..t, M / 2 * Real.sin u) = M / 2 * (1 - Real.cos t) := by
    rw [intervalIntegral.integral_const_mul, integral_sin, Real.cos_zero]
  rw [LinvPrim]
  refine le_trans (intervalIntegral.abs_integral_le_integral_abs (le_of_lt ht.1)) ?_
  have hmono := intervalIntegral.integral_mono_on (le_of_lt ht.1) hInt.abs hInt2
    (fun u hu => abs_LinvInt_le_sin hθ hM ht u hu)
  rw [hval] at hmono
  refine le_trans hmono ?_
  have hcos : 1 - Real.cos t ≤ t ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := t)]
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM θ hθ)
  nlinarith

lemma abs_Linv_le {h : ℝ → ℝ} {θ t M : ℝ}
    (hcont : ContinuousOn h (Set.Ioo 0 (Real.pi / 2)))
    (hM : ∀ s ∈ Set.Ioo 0 (Real.pi / 2), |h s| ≤ M)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (ht : t ∈ Set.Ioc 0 θ) :
    |Linv h t| ≤ M / (1 - 2 / Real.pi * θ) ^ 3 := by
  set c0 := 1 - 2 / Real.pi * θ with hc0def
  have hc0 : 0 < c0 := by
    have h2 : 2 / Real.pi * θ < 1 := by
      rw [show 2 / Real.pi * θ = 2 * θ / Real.pi by ring,
        div_lt_one (by positivity : (0:ℝ) < Real.pi)]
      linarith [hθ.2]
    rw [hc0def]; linarith
  have htpos : 0 < t := ht.1
  have htlt : t < Real.pi / 2 := lt_of_le_of_lt ht.2 hθ.2
  have ht' : t ∈ Set.Ioo 0 (Real.pi / 2) := ⟨htpos, htlt⟩
  have hsin : 0 < Real.sin t := linv_sin_pos ht'
  have hcos : 0 < Real.cos t := linv_cos_pos ht'
  have hsin2 : t / 2 ≤ Real.sin t := by
    have h1 : 2 / Real.pi * t ≤ Real.sin t := Real.mul_le_sin (le_of_lt htpos) (le_of_lt htlt)
    have h2 : t / 2 ≤ 2 / Real.pi * t := by
      have h3 : (1:ℝ) / 2 ≤ 2 / Real.pi := by
        rw [le_div_iff₀ Real.pi_pos]
        linarith [Real.pi_lt_four]
      nlinarith [htpos]
    linarith
  have hcos2 : c0 ≤ Real.cos t := by
    have h1 : 1 - 2 / Real.pi * t ≤ Real.cos t :=
      Real.one_sub_mul_le_cos (le_of_lt htpos) (le_of_lt htlt)
    have h2 : c0 ≤ 1 - 2 / Real.pi * t := by
      rw [hc0def]
      have h3 : 2 / Real.pi * t ≤ 2 / Real.pi * θ :=
        mul_le_mul_of_nonneg_left ht.2 (by positivity)
      linarith
    linarith
  have hden : t ^ 2 / 4 * c0 ^ 3 ≤ |LinvMu t| := by
    rw [LinvMu, abs_of_pos (mul_pos (pow_pos hsin 2) (pow_pos hcos 3))]
    have h1 : t ^ 2 / 4 ≤ Real.sin t ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ t / 2) hsin2 2
      nlinarith [h]
    have h2 : c0 ^ 3 ≤ Real.cos t ^ 3 := pow_le_pow_left₀ (le_of_lt hc0) hcos2 3
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hnum : |LinvPrim h t| ≤ M * t ^ 2 / 4 :=
    abs_LinvPrim_le hcont hM hθ ht
  have hdenpos : 0 < t ^ 2 / 4 * c0 ^ 3 := by positivity
  have hmuabs : 0 < |LinvMu t| := abs_pos.mpr (LinvMu_ne_zero_of_mem_Ioo ht')
  rw [Linv_apply, abs_neg, abs_mul, abs_inv]
  have ht0 : t ≠ 0 := ne_of_gt htpos
  have hc00 : c0 ≠ 0 := ne_of_gt hc0
  calc |LinvMu t|⁻¹ * |LinvPrim h t|
      ≤ (t ^ 2 / 4 * c0 ^ 3)⁻¹ * (M * t ^ 2 / 4) :=
        mul_le_mul ((inv_le_inv₀ hmuabs hdenpos).mpr hden) hnum (abs_nonneg _)
          (by positivity)
    _ = M / c0 ^ 3 := by
        field_simp

lemma intervalIntegrable_Linv {h : ℝ → ℝ} (hcont : ContinuousOn h (Set.Ioo 0 (Real.pi / 2)))
    (hbdd : ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |h θ| ≤ M)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    IntervalIntegrable (Linv h) volume 0 θ := by
  obtain ⟨M, hM⟩ := hbdd
  have hcontIoo : ContinuousOn (Linv h) (Set.Ioo 0 θ) := by
    rw [Linv_eq]
    refine ContinuousOn.neg (ContinuousOn.mul ?_ ?_)
    · exact ContinuousOn.inv₀ continuous_LinvMu.continuousOn
        (fun t ht => LinvMu_ne_zero_of_mem_Ioo ⟨ht.1, lt_trans ht.2 hθ.2⟩)
    · exact fun t ht => (hasDerivAt_LinvPrim hcont ⟨M, hM⟩
        ⟨ht.1, lt_trans ht.2 hθ.2⟩).continuousAt.continuousWithinAt
  have haes : AEStronglyMeasurable (Linv h) (volume.restrict (Set.Ioc 0 θ)) := by
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    exact hcontIoo.aestronglyMeasurable measurableSet_Ioo
  rw [intervalIntegrable_iff, Set.uIoc_of_le (le_of_lt hθ.1)]
  refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top haes
    (M / (1 - 2 / Real.pi * θ) ^ 3) ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  exact Filter.Eventually.of_forall (fun x hx => by
    rw [Real.norm_eq_abs]
    exact abs_Linv_le hcont hM hθ hx)

lemma hasDerivAt_LinvI {h : ℝ → ℝ} (hcont : ContinuousOn h (Set.Ioo 0 (Real.pi / 2)))
    (hbdd : ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |h θ| ≤ M)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (LinvI h) (Linv h θ) θ := by
  obtain ⟨M, hM⟩ := hbdd
  have hcontAt : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), ContinuousAt (Linv h) x := by
    intro x hx
    rw [Linv_eq]
    exact ((ContinuousAt.inv₀ continuous_LinvMu.continuousAt
      (LinvMu_ne_zero_of_mem_Ioo hx)).mul
        (hasDerivAt_LinvPrim hcont ⟨M, hM⟩ hx).continuousAt).neg
  exact intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_Linv hcont ⟨M, hM⟩ hθ)
    (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo hcontAt θ hθ) (hcontAt θ hθ)

lemma hasDerivAt_Linv {h : ℝ → ℝ} (hcont : ContinuousOn h (Set.Ioo 0 (Real.pi / 2)))
    (hbdd : ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |h θ| ≤ M)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (Linv h)
      ((2 * Real.sin θ * Real.cos θ ^ 4 - 3 * Real.sin θ ^ 3 * Real.cos θ ^ 2)
          / (LinvMu θ) ^ 2 * LinvPrim h θ
        - h θ / Work.Construction.s2 θ) θ := by
  obtain ⟨M, hM⟩ := hbdd
  have hμ : LinvMu θ ≠ 0 := LinvMu_ne_zero_of_mem_Ioo hθ
  have hs2 : Work.Construction.s2 θ ≠ 0 := linv_s2_ne_zero hθ
  have hinv : HasDerivAt (fun t => (LinvMu t)⁻¹)
      (-(2 * Real.sin θ * Real.cos θ ^ 4 - 3 * Real.sin θ ^ 3 * Real.cos θ ^ 2)
          / (LinvMu θ) ^ 2) θ :=
    (hasDerivAt_LinvMu θ).inv hμ
  have hprod := hinv.mul (hasDerivAt_LinvPrim hcont ⟨M, hM⟩ hθ)
  rw [Linv_eq]
  convert hprod.neg using 1
  rw [LinvInt]
  field_simp
  ring

/-! ## The final trigonometric algebra -/

lemma linvI_algebra {S C P hal : ℝ} (h1 : S ^ 2 + C ^ 2 = 1) (hS : S ≠ 0) (hC : C ≠ 0) :
    -(2 * S * C) * ((2 * S * C ^ 4 - 3 * S ^ 3 * C ^ 2) / (S ^ 2 * C ^ 3) ^ 2 * P
        - hal / (2 * S * C))
      + (6 - 10 * C ^ 2) * (-((S ^ 2 * C ^ 3)⁻¹ * P)) = hal := by
  field_simp
  ring_nf
  rw [show C ^ 2 = 1 - S ^ 2 by linarith]
  ring

theorem LinvI_solves {h : ℝ → ℝ}
    (hcont : ContinuousOn h (Set.Ioo 0 (π / 2)))
    (hbdd : ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 (π / 2), |h θ| ≤ M)
    (hint : MeasureTheory.IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hmom : (∫ θ in Work.Spaces.Iθ, h θ * Work.Elliptic.sinCos2 θ) = 0) :
    ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Construction.s2 θ' * Work.FTS.PhiStar.LinvI h θ') θ = h θ := by
  intro θ hθ
  have hS : Real.sin θ ≠ 0 := ne_of_gt (linv_sin_pos hθ)
  have hC : Real.cos θ ≠ 0 := ne_of_gt (linv_cos_pos hθ)
  have hd1 : DifferentiableOn ℝ (LinvI h) (Set.Ioo 0 (Real.pi / 2)) := fun t ht =>
    (hasDerivAt_LinvI hcont hbdd ht).differentiableAt.differentiableWithinAt
  have hd2 : DifferentiableOn ℝ (deriv (LinvI h)) (Set.Ioo 0 (Real.pi / 2)) := by
    intro t ht
    have heq : deriv (LinvI h) =ᶠ[𝓝 t] Linv h := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact (hasDerivAt_LinvI hcont hbdd hs).deriv
    exact (DifferentiableAt.congr_of_eventuallyEq
      (hasDerivAt_Linv hcont hbdd ht).differentiableAt heq).differentiableWithinAt
  have hsub := Lzero1_sin2_mul (v := LinvI h) hθ hd1 hd2
  have hD1 : deriv (LinvI h) θ = Linv h θ := (hasDerivAt_LinvI hcont hbdd hθ).deriv
  have hD2 : deriv (deriv (LinvI h)) θ
      = (2 * Real.sin θ * Real.cos θ ^ 4 - 3 * Real.sin θ ^ 3 * Real.cos θ ^ 2)
          / (LinvMu θ) ^ 2 * LinvPrim h θ
        - h θ / Work.Construction.s2 θ := by
    have heq : deriv (LinvI h) =ᶠ[𝓝 θ] Linv h := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with s hs
      exact (hasDerivAt_LinvI hcont hbdd hs).deriv
    rw [heq.deriv_eq]
    exact (hasDerivAt_Linv hcont hbdd hθ).deriv
  simp only [Work.Construction.s2_eq]
  rw [hsub, hD2, hD1, Linv_apply]
  simp only [LinvMu, Work.Construction.s2_eq, Real.sin_two_mul]
  have halg := linvI_algebra (S := Real.sin θ) (C := Real.cos θ) (P := LinvPrim h θ)
    (hal := h θ) (Real.sin_sq_add_cos_sq θ) hS hC
  convert halg using 1 <;> ring

end Work.FTS.PhiStar
