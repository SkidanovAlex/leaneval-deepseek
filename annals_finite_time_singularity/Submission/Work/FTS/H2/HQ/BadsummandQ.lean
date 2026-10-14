import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Blocks.HkIntegrand_mul_angular_le
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Vocab
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.EllipticEst.Vop_bound_reg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Vop_bound_reg`: the `ℋ⁴`-bound for the `V`-operator of the elliptic residual

Target (`Work.FTS.EllipticEst.Vop_bound_reg`): there is a universal constant `C > 0` such that
for every `0 < α ≤ 1/4` and every pair `(F, Ψ)` with `EllHypQ α 4 F Ψ` (the interior data class
of `RegQ.lean`) and `OrthCond (Ψ + Gsing α F · sin 2θ)`,

* `SmoothQuad` of `Vop α (EllResid α F Ψ)`,
* `HkMem α 4` of it,
* `Xn α (Vop α (EllResid α F Ψ)) ≤ C * Xn α F`   (`Xn α f = HkNorm α 4 f`).

The operator is `Vop α Ψ = ∂_θΨ - tan θ · Ψ` (paper (Relations), tex 1320), and the residual is
`EllResid α F Ψ = Ψ - (1/(4α)) sin 2θ · L₁₂(F)`.

## The structure of the argument — and the state of this file

**The key structural point (proved here).**  The three operators of (Relations) (tex 1320) are
*not* independent:

  `Vop α Ψ = Rop α Ψ + tan θ · Uop α Ψ`,   i.e. `V = R + tan θ · U`

(`Vop_eq_Rop_add_tan_Uop`), and `tan θ · U = 2 sin²θ · (U / sin 2θ)` on the open quadrant
(`tan_mul_Uop_eq`).  Since `2 sin²θ` is bounded and vanishes on the angular boundary, the
`ℋ⁴`-bound for `V` follows from the two bounds for `R` and for `U / sin 2θ`:

  `Xn α (Vop α W) ≤ C · (Xn α (Rop α W) + Xn α (Uop α W / sin 2θ))`

(`Xn_Vop_le`, proved below, built on `HkSq_two_sinsq_mul_le`, `HkMem_two_sinsq_mul`,
`HkIntegrand_two_sinsq_mul_le`, `HkSq_le_of_pointwise`).  In particular `Vop_bound_reg` is a
*corollary* of the two sibling targets `Rop_bound_reg` and `Uop_bound_reg`.

**What the residual `W = EllResid α F Ψ` carries.**  `W = Ψ + Gstar α F · sin 2θ`
(`EllResid_eq_Psi_add_Gstar`) and `W = Ψ̂ - Gbar α F · sin 2θ` with
`Ψ̂ = Ψ + Gsing α F · sin 2θ` (`EllResid_eq_PsiHat_sub_Gbar`); `Vop` of a radial `sin 2θ`-multiple
is `λ · (2cos 2θ - tan θ sin 2θ) = λ · 2(1 - 3 sin²θ)` on the open quadrant
(`Vop_sin_two_mul`, `vop_factor_eq`, `vop_factor_abs_le`), whence `Vop_EllResid_eq`.

**What is still missing (the analytic content).**  For `W := EllResid α F Ψ` with
`EllHypQ α 4 F Ψ` and `OrthCond (Ψ + Gsing α F sin 2θ)` one still needs

* `SmoothOpen`/`HkMem α 4` of `Rop α W` and of `Uop α W / sin 2θ` (and of `Vop α W`, here
  derived from them), and
* the two *bounds* `Xn α (Rop α W) ≤ C Xn α F`, `Xn α (Uop α W / sin 2θ) ≤ C Xn α F`

— i.e. the `ℛ`- and `U`-halves of the paper's Theorem `RemovingL12` together with the
`DivisionBySin` proposition (the contents of the sibling files
`EllipticEst/Rop_bound_reg.lean` and `EllipticEst/Uop_bound_reg.lean`).  The present file proves
everything around that reduction: the algebra, the operator identity `V = R + tan θ U`, and the
`HkSq`/`HkMem` transfers for the bounded angular profile `2 sin²θ`.

An equivalent route, also recorded here, works with the *straightened* stream function
`Ψ̂ = Ψ + Gsing α F · sin 2θ = W + Gbar α F · sin 2θ`: by `bslOp_sing_source`,
`bslOp α Ψ̂ = orthSource F`, and `F_*(orthSource F) = 0` (`Fstar_orthSource`) while the hypothesis
is exactly `F_*(Ψ̂) = 0`; so `(orthSource F, Ψ̂)` is a datum of the *orthogonal* elliptic problem,
and the `V`-companion of Theorem `RemovingL12` (with the `Gbar` layer, controlled by the paper's
Lemma `HardyInequality4`) gives the bound.  That is the route of the in-flight request
`EllipticEst/RegQ/Vop_orth_le_k4`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## The algebraic reduction -/



/-- `Vop` of a `sin 2θ`-multiple with radial amplitude `λ`: `λ(z)·(2cos 2θ - tan θ sin 2θ)`.
(`Real.tan` is totalised, so the value at `θ = π/2` is junk; the identity is used on the open
quadrant.) -/
theorem Vop_sin_two_mul (α : ℝ) (lam : ℝ → ℝ) :
    Vop α (fun z θ => lam z * Real.sin (2 * θ))
      = fun z θ => lam z * (2 * Real.cos (2 * θ) - Real.tan θ * Real.sin (2 * θ)) := by
  funext z θ
  have h1 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using h
  have h2 := h1.const_mul (lam z)
  show deriv (fun θ' : ℝ => lam z * Real.sin (2 * θ')) θ - Real.tan θ * (lam z * Real.sin (2 * θ))
      = lam z * (2 * Real.cos (2 * θ) - Real.tan θ * Real.sin (2 * θ))
  rw [h2.deriv]
  ring

/-- On the open interval `(-π/2, π/2)` the angular factor is the bounded trigonometric
polynomial `2(1 - 3 sin²θ)`. -/
theorem vop_factor_eq (θ : ℝ) (hθ : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    2 * Real.cos (2 * θ) - Real.tan θ * Real.sin (2 * θ)
      = 2 * (1 - 3 * Real.sin θ ^ 2) := by
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo hθ)
  have ht : Real.tan θ = Real.sin θ / Real.cos θ := Real.tan_eq_sin_div_cos θ
  have hs : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  have hc : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  have hsc := Real.sin_sq_add_cos_sq θ
  rw [ht, hs, hc]
  field_simp
  nlinarith [hsc]



/-! ## The transfer identities of the `R`-`U`-`V` triangle (paper (Relations), tex 1320) -/

/-- **`V = R + tan θ · U`.**  The three operators of (Relations) are not independent:
`Rop α Ψ + tan θ · Uop α Ψ = Vop α Ψ`.  Consequently the `ℋ⁴`-bound for `Vop` follows from the
two bounds for `Rop` and for `Uop / sin 2θ` (`Xn_Vop_le` below). -/
theorem Vop_eq_Rop_add_tan_Uop (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) (hcos : Real.cos θ ≠ 0) :
    Vop α Ψ z θ = Rop α Ψ z θ + Real.tan θ * Uop α Ψ z θ := by
  simp only [Vop, Rop, Uop]
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-- `HkNorm` only sees the open quadrant. -/
theorem HkNorm_congr_open' (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    Work.Spaces.HkNorm α k f = Work.Spaces.HkNorm α k g := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, Work.FTS.EllipticEst.HkSq_congr_open α k h]

/-- `tan θ · Uop = 2 sin²θ · (Uop / sin 2θ)` on the open quadrant: the second factor is the
quantity of the paper's `DivisionBySin` proposition, and `2 sin²θ` is the bounded angular
profile of `Blocks.HkIntegrand_mul_angular_le`. -/
theorem tan_mul_Uop_eq (α : ℝ) (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Real.tan θ * Uop α Ψ z θ
      = (2 * Real.sin θ ^ 2) * (Uop α Ψ z θ / Real.sin (2 * θ)) := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  have hsin : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul]
  field_simp

/-! ## The `HkSq`-transfer for the bounded angular profile `2 sin²θ` -/

/-- The `HkIntegrand` is nonnegative, so a pointwise domination on the *open* quadrant (where the
two boundary lines have integrand `0` on both sides) integrates to a `HkSq`-domination, provided
the dominating integrand is honest. -/
theorem HkSq_le_of_pointwise (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hmg : Work.Spaces.HkMem α k g)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k f z θ ≤ C * Work.Spaces.HkIntegrand α k g z θ) :
    Work.Spaces.HkSq α k f ≤ C * Work.Spaces.HkSq α k g := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
        ≤ C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ := by
    intro z hz
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α k f z θ)
      (g := fun θ => C * Work.Spaces.HkIntegrand α k g z θ)
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
      ((hmg.1 z hz).const_mul C)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => hpt z hz θ hθ))
    refine hmono.trans_eq ?_
    rw [MeasureTheory.integral_const_mul]
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  have houter := MeasureTheory.integral_mono_of_nonneg
    (μ := volume.restrict Work.Spaces.Iz)
    (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
    (g := fun z => C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
    (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α k f z θ)
    (hmg.2.const_mul C)
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  refine houter.trans_eq ?_
  rw [MeasureTheory.integral_const_mul]

/-- The `HkIntegrand` vanishes on the axis `z = 0` (the radial weight `w` has a zero there). -/
theorem HkIntegrand_eq_zero_of_z_eq_zero' (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt]

/-- The `HkIntegrand` vanishes on the angular boundary `sin 2θ = 0` (both weights are singular
powers of `sin 2θ`, and `0^p = 0` for `p ≠ 0`). -/
theorem HkIntegrand_eq_zero_of_sin_eq_zero' (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (hα : 0 < α)
    {z θ : ℝ} (h : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α k f z θ = 0 := by
  have hη : (0 : ℝ) ^ (Work.Spaces.eta / 2) = 0 :=
    Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
  have hgam : Work.Spaces.gam α / 2 ≠ 0 := by
    rw [Work.Spaces.gam]; intro hc; linarith
  have hγ : (0 : ℝ) ^ (-(Work.Spaces.gam α / 2)) = 0 := Real.zero_rpow (neg_ne_zero.mpr hgam)
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, h, hη, hγ]
  simp

/-- The pointwise multiplication bound of `Blocks.HkIntegrand_mul_angular_le` for the profile
`2 sin²θ`. -/
theorem HkIntegrand_two_sinsq_mul_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen g → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      Work.Spaces.HkIntegrand α k (fun z θ => (2 * Real.sin θ ^ 2) * g z θ) z θ
        ≤ C * Work.Spaces.HkIntegrand α k g z θ := by
  obtain ⟨Ca, hCapos, hCaf⟩ :=
    Work.FTS.EllipticEst.Blocks.HkIntegrand_mul_angular_le k
  refine ⟨4 * Ca, by positivity, ?_⟩
  intro α g hα hα1 hg z θ hz hθ0 hθ1
  obtain ⟨_hCa1, hCa2⟩ := hCaf α g hα hα1 hg
  have h1 : Work.Spaces.HkIntegrand α k (fun z θ => (2 * Real.sin θ ^ 2) * g z θ) z θ
      = 4 * Work.Spaces.HkIntegrand α k
          (fun z θ => Real.sin θ ^ 2 * g z θ) z θ := by
    rw [show (fun z θ => (2 * Real.sin θ ^ 2) * g z θ)
          = fun z θ => (2 : ℝ) * (Real.sin θ ^ 2 * g z θ) from by
        funext z' θ'; ring,
      Work.FTS.LocData.HkIntegrand_const_mul]
    norm_num
  rw [h1]
  have h2 := hCa2 z θ hz hθ0 hθ1
  have h3 := Work.Spaces.HkIntegrand_nonneg α k g z θ
  nlinarith [h2, h3, hCapos.le]

/-- The `HkSq`-form of the multiplication bound for `2 sin²θ`. -/
theorem HkSq_two_sinsq_mul_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α k g →
    Work.Spaces.HkSq α k (fun z θ => (2 * Real.sin θ ^ 2) * g z θ)
      ≤ C * Work.Spaces.HkSq α k g := by
  obtain ⟨C, hCpos, hC⟩ := HkIntegrand_two_sinsq_mul_le k
  refine ⟨C, hCpos, ?_⟩
  intro α g hα hα1 hg hmem
  refine HkSq_le_of_pointwise α k hCpos.le hmem ?_
  intro z hz θ hθ
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with h0 | h0
  · rw [← h0, HkIntegrand_eq_zero_of_z_eq_zero']
    exact mul_nonneg hCpos.le (Work.Spaces.HkIntegrand_nonneg α k g 0 θ)
  · by_cases hs : Real.sin (2 * θ) = 0
    · rw [HkIntegrand_eq_zero_of_sin_eq_zero' α k _ hα hs]
      exact mul_nonneg hCpos.le (Work.Spaces.HkIntegrand_nonneg α k g z θ)
    · have hθ' : 0 < θ ∧ θ < Real.pi / 2 := by
        rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
        refine ⟨?_, ?_⟩
        · rcases eq_or_lt_of_le hθ.1 with h | h
          · rw [← h] at hs; exact absurd (by simp) hs
          · exact h
        · rcases lt_or_eq_of_le hθ.2 with h | h
          · exact h
          · rw [h] at hs
            exact absurd (by rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]) hs
      exact hC α g hα hα1 hg z θ h0 hθ'.1 hθ'.2

/-- The `HkMem`-form of the multiplication bound for `2 sin²θ`. -/
theorem HkMem_two_sinsq_mul (k : ℕ) {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => (2 * Real.sin θ ^ 2) * g z θ) := by
  obtain ⟨C, hCpos, hC⟩ := HkIntegrand_two_sinsq_mul_le k
  have hfsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (2 * Real.sin θ ^ 2) * g z θ) := by
    show ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun z θ => (2 * Real.sin θ ^ 2) * g z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => (2 : ℝ) * Real.sin p.2 ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by fun_prop
    have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hg
    exact h1.mul h2
  refine Work.FTS.LocData.HkMem_of_majorant α k
    (f := fun z θ => (2 * Real.sin θ ^ 2) * g z θ)
    (M := fun z θ => C * Work.Spaces.HkIntegrand α k g z θ)
    (hfsm.continuousOn_HkIntegrand α k) ?_ ?_ ?_
  · intro z hz
    exact (hmem.1 z hz).const_mul C
  · refine (hmem.2.const_mul C).congr ?_
    filter_upwards with z
    rw [MeasureTheory.integral_const_mul]
  · intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with h0 | h0
    · rw [← h0, HkIntegrand_eq_zero_of_z_eq_zero']
      exact mul_nonneg hCpos.le (Work.Spaces.HkIntegrand_nonneg α k g 0 θ)
    · by_cases hs : Real.sin (2 * θ) = 0
      · rw [HkIntegrand_eq_zero_of_sin_eq_zero' α k _ hα hs]
        exact mul_nonneg hCpos.le (Work.Spaces.HkIntegrand_nonneg α k g z θ)
      · have hθ' : 0 < θ ∧ θ < Real.pi / 2 := by
          rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
          refine ⟨?_, ?_⟩
          · rcases eq_or_lt_of_le hθ.1 with h | h
            · rw [← h] at hs; exact absurd (by simp) hs
            · exact h
          · rcases lt_or_eq_of_le hθ.2 with h | h
            · exact h
            · rw [h] at hs
              exact absurd (by rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]) hs
        exact hC α g hα hα1 hg z θ h0 hθ'.1 hθ'.2

/-- **The `V`-bound from the `R`- and `U`-bounds.**  For `W` whose `R`- and `U`-transforms are
smooth and honest on the open quadrant,

`Xn α (Vop α W) ≤ C · (Xn α (Rop α W) + Xn α (Uop α W / sin 2θ))`.

This is the identity `V = R + tan θ · U` combined with `tan θ U = 2 sin²θ (U/sin 2θ)` and the
`HkSq`-bound for the bounded angular profile `2 sin²θ`. -/
theorem Xn_Vop_le (α : ℝ) (W : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hRsm : Work.FTS.EllipticEst.SmoothOpen (Rop α W))
    (hUsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Uop α W z θ / Real.sin (2 * θ)))
    (hRmem : Work.Spaces.HkMem α 4 (Rop α W))
    (hUmem : Work.Spaces.HkMem α 4 (fun z θ => Uop α W z θ / Real.sin (2 * θ))) :
    ∃ C : ℝ, 0 < C ∧ Work.FTS.Nonlin.Xn α (Vop α W)
      ≤ C * (Work.FTS.Nonlin.Xn α (Rop α W)
          + Work.FTS.Nonlin.Xn α (fun z θ => Uop α W z θ / Real.sin (2 * θ))) := by
  obtain ⟨C, hCpos, hC⟩ := HkSq_two_sinsq_mul_le 4
  set GU : ℝ → ℝ → ℝ := fun z θ => Uop α W z θ / Real.sin (2 * θ) with hGUdef
  set G2 : ℝ → ℝ → ℝ := fun z θ => (2 * Real.sin θ ^ 2) * GU z θ with hG2def
  have hG2mem : Work.Spaces.HkMem α 4 G2 := HkMem_two_sinsq_mul 4 hα hα1 hUsm hUmem
  have hG2sq : Work.Spaces.HkSq α 4 G2 ≤ C * Work.Spaces.HkSq α 4 GU :=
    hC α GU hα hα1 hUsm hUmem
  have hG2sm : Work.FTS.EllipticEst.SmoothOpen G2 := by
    show ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun z θ => (2 * Real.sin θ ^ 2) * GU z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => (2 : ℝ) * Real.sin p.2 ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by fun_prop
    have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry GU)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hUsm
    exact h1.mul h2
  -- the pointwise identity `V = R + G2` on the open quadrant
  have hVop : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Vop α W z θ = Rop α W z θ + G2 z θ := by
    intro z θ hz hθ0 hθ1
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ0], hθ1⟩)
    rw [Vop_eq_Rop_add_tan_Uop α W z θ hcos,
      tan_mul_Uop_eq α W (show θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨hθ0, hθ1⟩)]
  have hnorm : Work.FTS.Nonlin.Xn α (Vop α W)
      = Work.FTS.Nonlin.Xn α (fun z θ => Rop α W z θ + G2 z θ) :=
    HkNorm_congr_open' α 4 hVop
  -- the squared estimate
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (fun z θ => Rop α W z θ + G2 z θ) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α 4 (Rop α W) z θ
          + 2 * Work.Spaces.HkIntegrand α 4 G2 z θ :=
    HkIntegrand_add_le_of_contDiffOn α 4 hRsm hG2sm
  have hsqsum : Work.Spaces.HkSq α 4 (fun z θ => Rop α W z θ + G2 z θ)
      ≤ 2 * Work.Spaces.HkSq α 4 (Rop α W) + 2 * Work.Spaces.HkSq α 4 G2 :=
    HkSq_add_le_of_pointwise α 4 hRmem hG2mem hpt
  have hXR : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 4 (Rop α W)) := Real.sqrt_nonneg _
  have hXG : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 4 GU) := Real.sqrt_nonneg _
  refine ⟨Real.sqrt 2 * (1 + Real.sqrt C), by positivity, ?_⟩
  rw [hnorm]
  have hstep1 : Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => Rop α W z θ + G2 z θ))
      ≤ Real.sqrt 2 * (Real.sqrt (Work.Spaces.HkSq α 4 (Rop α W))
          + Real.sqrt C * Real.sqrt (Work.Spaces.HkSq α 4 GU)) := by
    refine (Real.sqrt_le_sqrt hsqsum).trans ?_
    have h2 : Real.sqrt (2 * Work.Spaces.HkSq α 4 (Rop α W) + 2 * Work.Spaces.HkSq α 4 G2)
        ≤ Real.sqrt 2 * (Real.sqrt (Work.Spaces.HkSq α 4 (Rop α W))
            + Real.sqrt (Work.Spaces.HkSq α 4 G2)) :=
      sqrt_two_mul_add_le (Work.Spaces.HkSq_nonneg α 4 (Rop α W))
        (Work.Spaces.HkSq_nonneg α 4 G2)
    refine h2.trans ?_
    have h3 : Real.sqrt (Work.Spaces.HkSq α 4 G2)
        ≤ Real.sqrt C * Real.sqrt (Work.Spaces.HkSq α 4 GU) := by
      refine (Real.sqrt_le_sqrt hG2sq).trans (le_of_eq ?_)
      rw [Real.sqrt_mul hCpos.le]
    have h4 := Real.sqrt_nonneg C
    nlinarith [h3, h4, hXR, hXG, Real.sqrt_nonneg (2 : ℝ)]
  refine hstep1.trans ?_
  have hXR' : 0 ≤ Work.FTS.Nonlin.Xn α (Rop α W) := Real.sqrt_nonneg _
  have hXG' : 0 ≤ Work.FTS.Nonlin.Xn α GU := Real.sqrt_nonneg _
  have h6 : Real.sqrt 2 * (Work.FTS.Nonlin.Xn α (Rop α W)
        + Real.sqrt C * Work.FTS.Nonlin.Xn α GU)
      ≤ (Real.sqrt 2 * (1 + Real.sqrt C)) * (Work.FTS.Nonlin.Xn α (Rop α W)
        + Work.FTS.Nonlin.Xn α GU) := by
    have h7 : 0 ≤ Real.sqrt C := Real.sqrt_nonneg C
    have h8 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg (2 : ℝ)
    have hkey : Real.sqrt 2 * (Work.FTS.Nonlin.Xn α (Rop α W)
          + Real.sqrt C * Work.FTS.Nonlin.Xn α GU)
        = Real.sqrt 2 * Work.FTS.Nonlin.Xn α (Rop α W)
          + (Real.sqrt 2 * Real.sqrt C) * Work.FTS.Nonlin.Xn α GU := by ring
    have hkey2 : (Real.sqrt 2 * (1 + Real.sqrt C)) * (Work.FTS.Nonlin.Xn α (Rop α W)
          + Work.FTS.Nonlin.Xn α GU)
        = Real.sqrt 2 * Work.FTS.Nonlin.Xn α (Rop α W)
          + Real.sqrt 2 * Work.FTS.Nonlin.Xn α GU
          + (Real.sqrt 2 * Real.sqrt C) * Work.FTS.Nonlin.Xn α (Rop α W)
          + (Real.sqrt 2 * Real.sqrt C) * Work.FTS.Nonlin.Xn α GU := by ring
    rw [hkey, hkey2]
    nlinarith [mul_nonneg h8 hXR', mul_nonneg (mul_nonneg h8 h7) hXR']
  exact h6


end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.H2.HQ.BadsummandQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.HQ

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open Work.Spaces
open Work.FTS.LocData (SmoothQuad)

/-! ## Private scaffolding: the pairs of the Leibniz expansion of `mixed 3 1 (f·g)` -/

/-- The pair `(a,b)` of the Leibniz expansion of `D_z^3D_θ^1(fg)`:
`(D_z^bD_θ^a f) · (D_z^{3-b}D_θ^{1-a} g)`. -/
private def bqT (f g : ℝ → ℝ → ℝ) (p : ℕ × ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => mixed p.2 p.1 f z θ * mixed (3 - p.2) (1 - p.1) g z θ

/-- The weighted pair of the Leibniz expansion. -/
private def bqY (α : ℝ) (f g : ℝ → ℝ → ℝ) (p : ℕ × ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => bqT f g p z θ * Wt α z θ

/-- The binomial coefficient of the pair `p = (a,b)`, `C(1,a)·C(3,b)`. -/
private def bqC (p : ℕ × ℕ) : ℝ := (Nat.choose 1 p.1 : ℝ) * (Nat.choose 3 p.2 : ℝ)

/-- The eight pairs `a ≤ 1`, `b ≤ 3` of the Leibniz expansion of `D_z^3D_θ^1(fg)`. -/
private def bqP : Finset (ℕ × ℕ) := Finset.range 2 ×ˢ Finset.range 4

private lemma bqP_card : bqP.card = 8 := by
  simp [bqP, Finset.card_product]

private lemma bqC_sq_le : ∀ p ∈ bqP, (bqC p) ^ 2 ≤ 9 := by
  intro p hp
  obtain ⟨a, b⟩ := p
  simp only [bqP, Finset.mem_product, Finset.mem_range] at hp
  obtain ⟨ha, hb⟩ := hp
  interval_cases a <;> interval_cases b <;> simp only [bqC] <;> norm_num

/-! ## The weight `Wt` vanishes on the boundary lines

`RegQ` constrains `f` only on the *open* quadrant, so every pointwise estimate below has to be
taken where `Wt α z θ = w z · sin(2θ)^{-γ/2}` does not vanish.  On the two lines `θ = 0`,
`θ = π/2` and on `z = 0` the weight is `0` (Lean's totalised division and `Real.zero_rpow`),
which makes the pointwise estimates at those lines trivial. -/

/-- `Wt α 0 θ = 0`: the radial weight vanishes at `z = 0`. -/
private theorem Wt_zero_left (α θ : ℝ) : Wt α 0 θ = 0 := by
  simp [Wt, w]

/-- `Wt α z 0 = 0` for `α > 0`: the angular weight vanishes at `θ = 0`. -/
private theorem Wt_zero_theta_zero (α z : ℝ) (hα : 0 < α) : Wt α z 0 = 0 := by
  have hgam : 0 < gam α := by rw [gam]; linarith
  have hexp : -(gam α / 2) ≠ 0 := by linarith
  rw [Wt, wTheta, show Real.sin (2 * 0) = 0 by norm_num, Real.zero_rpow hexp, mul_zero]

/-- `Wt α z (π/2) = 0` for `α > 0`: the angular weight vanishes at `θ = π/2`. -/
private theorem Wt_zero_theta_pi (α z : ℝ) (hα : 0 < α) : Wt α z (π / 2) = 0 := by
  have hgam : 0 < gam α := by rw [gam]; linarith
  have hexp : -(gam α / 2) ≠ 0 := by linarith
  rw [Wt, wTheta, show 2 * (π / 2) = π by ring, Real.sin_pi, Real.zero_rpow hexp, mul_zero]

/-- The weight vanishes on the boundary of the closed quadrant. -/
private theorem Wt_eq_zero_of_boundary (α z θ : ℝ) (hα : 0 < α) (hz : z ∈ Iz) (hθ : θ ∈ Iθ)
    (h : ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2)) : Wt α z θ = 0 := by
  by_cases hz0 : z = 0
  · subst hz0
    exact Wt_zero_left α θ
  · have hzpos : 0 < z := lt_of_le_of_ne (Set.mem_Ici.mp hz) (Ne.symm hz0)
    have hθ' : θ = 0 ∨ θ = π / 2 := by
      rcases Set.mem_Icc.mp hθ with ⟨h1, h2⟩
      by_contra hc
      push_neg at hc
      exact h ⟨hzpos, lt_of_le_of_ne h1 (Ne.symm hc.1), lt_of_le_of_ne h2 hc.2⟩
    rcases hθ' with rfl | rfl
    · exact Wt_zero_theta_zero α z hα
    · exact Wt_zero_theta_pi α z hα

/-! ## Leibniz expansion of `mixed 3 1 (f·g)`, followed by Cauchy–Schwarz

The interior Leibniz rule `mixed_mul_eq_quad` is available for `z ∈ Iz`, `0 < θ < π/2`; at the
two lines `θ = 0`, `θ = π/2` both sides of the inequality vanish because `Wt` does. -/

private lemma bqYsq (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ)
    (hf : SmoothQuad f) (hg : SmoothQuad g) :
    ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      (mixed 3 1 (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        ≤ 72 * ∑ p ∈ bqP, (bqY α f g p z θ) ^ 2 := by
  intro z hz θ hθ
  by_cases hθi : θ ∈ Set.Ioo 0 (π / 2)
  · have hexp : mixed 3 1 (fun z θ => f z θ * g z θ) z θ * Wt α z θ
        = ∑ p ∈ bqP, bqC p * bqY α f g p z θ := by
      rw [mixed_mul_eq_quad 3 1 f g hf hg z hz θ hθi]
      simp only [bqP, Finset.sum_product, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
      simp only [bqC, bqY, bqT]
      ring
    rw [hexp]
    have h1 := sq_sum_le_card_mul_sum_sq (s := bqP)
      (f := fun p => bqC p * bqY α f g p z θ)
    calc (∑ p ∈ bqP, bqC p * bqY α f g p z θ) ^ 2
        ≤ (bqP.card : ℝ) * ∑ p ∈ bqP, (bqC p * bqY α f g p z θ) ^ 2 := h1
      _ = 8 * ∑ p ∈ bqP, (bqC p * bqY α f g p z θ) ^ 2 := by rw [bqP_card]; norm_num
      _ ≤ 8 * ∑ p ∈ bqP, 9 * (bqY α f g p z θ) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          refine Finset.sum_le_sum fun p hp => ?_
          calc (bqC p * bqY α f g p z θ) ^ 2
              = (bqC p) ^ 2 * (bqY α f g p z θ) ^ 2 := by ring
            _ ≤ 9 * (bqY α f g p z θ) ^ 2 :=
                mul_le_mul_of_nonneg_right (bqC_sq_le p hp) (sq_nonneg _)
      _ = 72 * ∑ p ∈ bqP, (bqY α f g p z θ) ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum]; ring_nf
  · have hW : Wt α z θ = 0 :=
      Wt_eq_zero_of_boundary α z θ hα hz hθ (fun hc => hθi ⟨hc.2.1, hc.2.2⟩)
    have hL : (mixed 3 1 (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2 = 0 := by
      rw [hW]; ring
    have hR : 0 ≤ 72 * ∑ p ∈ bqP, (bqY α f g p z θ) ^ 2 :=
      mul_nonneg (by norm_num) (Finset.sum_nonneg fun p _ => sq_nonneg _)
    rw [hL]; exact hR

/-! ## Strong measurability of the weighted product of two interior slots -/

/-- Strong measurability of `(D_z^bD_θ^a f · D_z^jD_θ^i h · W)²` on the product measure, for
`f, h` smooth on the open quadrant. -/
private lemma bqAesmJoint (α : ℝ) (f h : ℝ → ℝ → ℝ) (hf : SmoothQuad f) (hh : SmoothQuad h)
    (b a j i : ℕ) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ =>
        (mixed b a f p.1 p.2 * mixed j i h p.1 p.2 * Wt α p.1 p.2) ^ 2)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
  (aesm_sq_prod_quad α (Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hf b a)
    (Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hh j i)).1

/-- Strong measurability of `(D_z^bD_θ^a f · D_z^jD_θ^i h · W)²` on every angular slice. -/
private lemma bqAesmSlice (α : ℝ) (f h : ℝ → ℝ → ℝ) (hf : SmoothQuad f) (hh : SmoothQuad h)
    (b a j i : ℕ) :
    ∀ z ∈ Iz, AEStronglyMeasurable
      (fun θ => (mixed b a f z θ * mixed j i h z θ * Wt α z θ) ^ 2)
      (volume.restrict Iθ) :=
  fun z hz => (aesm_sq_prod_quad α
    (Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hf b a)
    (Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hh j i)).2 z hz

/-! ## The bound on one "good" pair

An `L^∞`-bounded factor of order `≤ 2` (from `PwBd`) times an `ℋ⁴`-slot carrying an angular
derivative.  The proof follows `Work.Spaces.GoodTermSqBound`, with the measurability data
supplied by `aesm_sq_prod_quad`. -/

private theorem goodPair (α : ℝ) (hα : 0 < α) (f h : ℝ → ℝ → ℝ) (Cf : ℝ)
    (hf : SmoothQuad f) (hCfb : PwBd α f Cf) (hh : SmoothQuad h) (hhmem : HkMem α 4 h)
    {b a j i : ℕ} (hab : a + b ≤ 2) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    (∀ z ∈ Iz, IntegrableOn (fun θ => (mixed b a f z θ * mixed j i h z θ * Wt α z θ) ^ 2) Iθ)
      ∧ IntegrableOn (fun z => ∫ θ in Iθ,
          (mixed b a f z θ * mixed j i h z θ * Wt α z θ) ^ 2) Iz
      ∧ (∫ z in Iz, ∫ θ in Iθ, (mixed b a f z θ * mixed j i h z θ * Wt α z θ) ^ 2)
          ≤ Cf / (gam α - 1) * HkSq α 4 f * HkSq α 4 h := by
  have hγ : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hCf : 0 ≤ Cf := hCfb.nonneg
  have hMnn : 0 ≤ Cf / (gam α - 1) * HkSq α 4 f :=
    mul_nonneg (div_nonneg hCf hγ.le) (HkSq_nonneg α 4 f)
  have hHknn : ∀ z θ, 0 ≤ HkIntegrand α 4 h z θ := by
    intro z θ
    rw [HkIntegrand]
    exact add_nonneg (hkZSum_nonneg α 4 h z θ) (hkMixedSum_nonneg α 4 h z θ)
  -- the pointwise domination by `M · HkIntegrand`
  have hpt : ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      (mixed b a f z θ * mixed j i h z θ * Wt α z θ) ^ 2
        ≤ (Cf / (gam α - 1) * HkSq α 4 f) * HkIntegrand α 4 h z θ := by
    intro z hz θ hθ
    by_cases hc : 0 < z ∧ 0 < θ ∧ θ < π / 2
    · have h1 : (mixed b a f z θ) ^ 2 ≤ Cf / (gam α - 1) * HkSq α 4 f :=
        hCfb.bound b a hab z hc.1 θ hc.2.1 hc.2.2
      have h2 : (mixed j i h z θ * Wt α z θ) ^ 2 ≤ HkIntegrand α 4 h z θ :=
        sq_le_HkIntegrand_mixed α 4 h z θ i j hi hij
      have hfeq : (mixed b a f z θ * mixed j i h z θ * Wt α z θ) ^ 2
          = (mixed b a f z θ) ^ 2 * (mixed j i h z θ * Wt α z θ) ^ 2 := by ring
      rw [hfeq]
      exact le_trans (mul_le_mul_of_nonneg_right h1 (sq_nonneg _))
        (mul_le_mul_of_nonneg_left h2 hMnn)
    · have hW : Wt α z θ = 0 :=
        Wt_eq_zero_of_boundary α z θ hα hz hθ (fun hc' => hc hc')
      have h0 : (mixed b a f z θ * mixed j i h z θ * Wt α z θ) ^ 2 = 0 := by
        rw [hW]; ring
      rw [h0]
      exact mul_nonneg hMnn (hHknn z θ)
  -- integrability of every angular slice
  have hslice : ∀ z ∈ Iz, IntegrableOn
      (fun θ => (mixed b a f z θ * mixed j i h z θ * Wt α z θ) ^ 2) Iθ := by
    intro z hz
    refine MeasureTheory.Integrable.mono'
      ((hhmem.1 z hz).const_mul (Cf / (gam α - 1) * HkSq α 4 f))
      (bqAesmSlice α f h hf hh b a j i z hz) ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpt z hz θ hθ
  -- dominated bound for the inner integral
  have hinner : ∀ z ∈ Iz, ∫ θ in Iθ, (mixed b a f z θ * mixed j i h z θ * Wt α z θ) ^ 2
      ≤ (Cf / (gam α - 1) * HkSq α 4 f) * ∫ θ in Iθ, HkIntegrand α 4 h z θ := by
    intro z hz
    calc ∫ θ in Iθ, (mixed b a f z θ * mixed j i h z θ * Wt α z θ) ^ 2
        ≤ ∫ θ in Iθ, (Cf / (gam α - 1) * HkSq α 4 f) * HkIntegrand α 4 h z θ := by
          refine integral_mono_ae (hslice z hz)
            ((hhmem.1 z hz).const_mul (Cf / (gam α - 1) * HkSq α 4 f)) ?_
          filter_upwards [ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)]
            with θ hθ
          exact hpt z hz θ hθ
      _ = (Cf / (gam α - 1) * HkSq α 4 f) * ∫ θ in Iθ, HkIntegrand α 4 h z θ := by
          rw [integral_const_mul]
  -- integrability over `Iz`
  have houter : IntegrableOn (fun z => ∫ θ in Iθ,
      (mixed b a f z θ * mixed j i h z θ * Wt α z θ) ^ 2) Iz := by
    refine MeasureTheory.Integrable.mono'
      (hhmem.2.const_mul (Cf / (gam α - 1) * HkSq α 4 f))
      (bqAesmJoint α f h hf hh b a j i).integral_prod_right' ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact hinner z hz
  refine ⟨hslice, houter, ?_⟩
  calc ∫ z in Iz, ∫ θ in Iθ, (mixed b a f z θ * mixed j i h z θ * Wt α z θ) ^ 2
      ≤ ∫ z in Iz, (Cf / (gam α - 1) * HkSq α 4 f) * ∫ θ in Iθ, HkIntegrand α 4 h z θ := by
        refine integral_mono_ae houter
          (hhmem.2.const_mul (Cf / (gam α - 1) * HkSq α 4 f)) ?_
        filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
        exact hinner z hz
    _ = Cf / (gam α - 1) * HkSq α 4 f * HkSq α 4 h := by
        rw [integral_const_mul]; rfl

/-- The same bound with the two factors in the opposite order. -/
private theorem goodPairSwap (α : ℝ) (hα : 0 < α) (f h : ℝ → ℝ → ℝ) (Cf : ℝ)
    (hf : SmoothQuad f) (hCfb : PwBd α f Cf) (hh : SmoothQuad h) (hhmem : HkMem α 4 h)
    {b a j i : ℕ} (hab : a + b ≤ 2) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    (∀ z ∈ Iz, IntegrableOn (fun θ => (mixed j i h z θ * mixed b a f z θ * Wt α z θ) ^ 2) Iθ)
      ∧ IntegrableOn (fun z => ∫ θ in Iθ,
          (mixed j i h z θ * mixed b a f z θ * Wt α z θ) ^ 2) Iz
      ∧ (∫ z in Iz, ∫ θ in Iθ, (mixed j i h z θ * mixed b a f z θ * Wt α z θ) ^ 2)
          ≤ Cf / (gam α - 1) * HkSq α 4 f * HkSq α 4 h := by
  obtain ⟨h1, h2, h3⟩ := goodPair α hα f h Cf hf hCfb hh hhmem hab hi hij
  have hEq : ∀ z θ, (mixed j i h z θ * mixed b a f z θ * Wt α z θ) ^ 2
      = (mixed b a f z θ * mixed j i h z θ * Wt α z θ) ^ 2 := fun z θ => by ring
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact MeasureTheory.IntegrableOn.congr_fun (h1 z hz)
      (fun θ _ => (hEq z θ).symm) measurableSet_Icc
  · refine MeasureTheory.IntegrableOn.congr_fun h2 (fun z _ => ?_) measurableSet_Ici
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun θ => (hEq z θ).symm)
  · rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z =>
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => (hEq z θ)))]
    exact h3

/-- A finite sum of functions integrable on a set is integrable on that set. -/
private theorem integrableOn_finsetSumQ {ι : Type*} {s : Set ℝ} {φ : ι → ℝ → ℝ}
    (t : Finset ι) (h : ∀ i ∈ t, IntegrableOn (φ i) s) :
    IntegrableOn (fun x => ∑ i ∈ t, φ i x) s := by
  classical
  induction t using Finset.induction with
  | empty =>
      simpa using (integrableOn_zero :
        IntegrableOn (fun _ : ℝ => (0 : ℝ)) s (μ := volume))
  | insert a t ha ih =>
      have hfun : (fun x => ∑ i ∈ insert a t, φ i x)
          = (fun x => φ a x) + (fun x => ∑ i ∈ t, φ i x) := by
        funext x; rw [Finset.sum_insert ha]; rfl
      rw [hfun]
      exact (h a (Finset.mem_insert_self a t)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- **The exceptional `(j,i) = (3,1)` summand of the interior product rule `HProdQ`.**

This is `Work.Spaces.HProductRule_Badsummand` (proved) with the unusable class
`Spaces.SmoothNbhd` (analyticity on a neighbourhood of the closed quadrant) replaced by the
interior class `RegQ` and the pointwise `L^∞`-bound of order `≤ 2` supplied abstractly by
`PwBd`.  The two exceptional Leibniz summands `(0,3) = (D_z³f)(D_θg)` and
`(1,0) = (D_θf)(D_z³g)` are handled by `Work.Spaces.BadTermSqBound` in the `SmoothNbhd`
setting; here the two *packages* it returns (square-integrability plus the bound
`100/(γ-1)·|f|²_{ℋ⁴}·|g|²_{ℋ⁴}` of the weighted products `D_z³f · D_θg · Wt` and
`D_θf · D_z³g · Wt`) are taken as hypotheses — they are produced by
`Work.FTS.H2.HQ.BadPackageQ` from the two interior Hardy inequalities
(`Work.FTS.H2.HQ.HardyThetaQ`, `Work.FTS.H2.HQ.HardyZQ`) and the limits of `BdryTraces`.

The conclusion carries the factor `(1 + Cf + Cg)` rather than `(Cf + Cg)`: the six *good* terms
of the Leibniz expansion each keep one `PwBd`-bounded factor of order `≤ 2` and hence carry
`Cf` or `Cg`, while the two exceptional terms are bounded by the two packages alone
(`2·100/(γ-1)·|f|²|g|²`).

Route: copy the proof of `Submission/Work/Spaces/HProductRule_Badsummand.lean`, using
`Work.FTS.H2.HQ.mixed_mul_eq_quad` for the Leibniz expansion (valid for `z ∈ Iz`,
`0 < θ < π/2`, so take the pointwise steps a.e. in `θ`), the two packages in place of
`Work.Spaces.BadTermSqBound`, `Work.FTS.H2.HQ.PwBd` in place of
`Work.Spaces.MixedSqPointwiseBound`, `Work.FTS.H2.HQ.aesm_sq_prod_quad` in place of
`Work.Spaces.AesmSqProdSmooth`, and `Work.Spaces.GoodTermSqBound`,
`Work.Spaces.L2Sq_mixed_le_HkSq`, `Work.Spaces.sq_le_HkIntegrand_mixed` unchanged (they take
their measurability data as hypotheses and are smoothness-free).  The sibling
`Work.FTS.H2.HQ.MsummandQ` (`Submission/Work/FTS/H2/HQ/MsummandQ.lean`, proved) already contains
the reusable boundary-layer bookkeeping (`Wt` vanishing on the lines `z = 0`, `θ = 0`,
`θ = π/2`) and the case analysis for the six good pairs.
Traps: (i) `PwBd` is stated on the *open* quadrant only, while `GoodTermSqBound`'s `hUb` is
asked for all of `Iz ×ˢ Iθ` — the bounded factor may be truncated on the boundary lines (where
`Wt α z θ = 0` and `w 0 = 0`, so every pointwise inequality becomes trivial), or those steps
may be taken a.e.; (ii) `RegQ` constrains nothing on the lines `θ = 0, π/2` and `z = 0`. -/
theorem BadsummandQ : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : Work.FTS.Galerkin.Fn)
    (Cf Cg : ℝ), 0 < α → α ≤ 1 → Work.FTS.Nonlin.RegQ α 4 f → Work.FTS.Nonlin.RegQ α 4 g →
    Work.FTS.H2.HQ.PwBd α f Cf → Work.FTS.H2.HQ.PwBd α g Cg →
    (Work.Spaces.L2Mem (fun z θ => Work.Spaces.DzIter 3 f z θ * Work.Spaces.Dth g z θ
        * Work.Spaces.Wt α z θ)
      ∧ Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter 3 f z θ * Work.Spaces.Dth g z θ
          * Work.Spaces.Wt α z θ)
        ≤ 100 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f * Work.Spaces.HkSq α 4 g) →
    (Work.Spaces.L2Mem (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.DzIter 3 g z θ
        * Work.Spaces.Wt α z θ)
      ∧ Work.Spaces.L2Sq (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.DzIter 3 g z θ
          * Work.Spaces.Wt α z θ)
        ≤ 100 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 g * Work.Spaces.HkSq α 4 f) →
      Work.Spaces.L2Mem (fun z θ => Work.Spaces.mixed 3 1 (fun z θ => f z θ * g z θ) z θ
          * Work.Spaces.Wt α z θ)
      ∧ Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 3 1 (fun z θ => f z θ * g z θ) z θ
          * Work.Spaces.Wt α z θ)
        ≤ C / (Work.Spaces.gam α - 1) * (1 + Cf + Cg) * Work.Spaces.HkSq α 4 f
            * Work.Spaces.HkSq α 4 g := by
  refine ⟨10 ^ 12, by norm_num, ?_⟩
  intro α f g Cf Cg hα hα1 hregf hregg hCfb hCgb hpkg1 hpkg2
  obtain ⟨hfsq, hmemf, _⟩ := hregf
  obtain ⟨hgsq, hmemg, _⟩ := hregg
  have hγ : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hCf : 0 ≤ Cf := hCfb.nonneg
  have hCg : 0 ≤ Cg := hCgb.nonneg
  have hsmFG : SmoothQuad (fun z θ => f z θ * g z θ) :=
    Work.FTS.LocData.smoothQuad_mul hfsq hgsq
  -- the pointwise Cauchy–Schwarz step
  have hYsq := bqYsq α hα f g hfsq hgsq
  -- the uniform per-pair constant and the three numerical steps
  have hXnn : 0 ≤ (gam α - 1)⁻¹ * (HkSq α 4 f * HkSq α 4 g) :=
    mul_nonneg (inv_nonneg.mpr hγ.le)
      (mul_nonneg (HkSq_nonneg α 4 f) (HkSq_nonneg α 4 g))
  have hKnn : 0 ≤ 100 / (gam α - 1) * (1 + Cf + Cg) * HkSq α 4 f * HkSq α 4 g := by
    have h1 : 0 ≤ 1 + Cf + Cg := by linarith
    have h2 : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr hγ.le
    rw [div_eq_mul_inv]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h2) h1)
      (HkSq_nonneg α 4 f)) (HkSq_nonneg α 4 g)
  have hstep_f : ∀ X : ℝ, X ≤ Cf / (gam α - 1) * HkSq α 4 f * HkSq α 4 g →
      X ≤ 100 / (gam α - 1) * (1 + Cf + Cg) * HkSq α 4 f * HkSq α 4 g := by
    intro X hX
    refine hX.trans ?_
    have h1 : Cf ≤ 100 * (1 + Cf + Cg) := by nlinarith
    have hL : Cf / (gam α - 1) * HkSq α 4 f * HkSq α 4 g
        = Cf * ((gam α - 1)⁻¹ * (HkSq α 4 f * HkSq α 4 g)) := by
      rw [div_eq_mul_inv]; ring
    have hR : 100 / (gam α - 1) * (1 + Cf + Cg) * HkSq α 4 f * HkSq α 4 g
        = (100 * (1 + Cf + Cg)) * ((gam α - 1)⁻¹ * (HkSq α 4 f * HkSq α 4 g)) := by
      rw [div_eq_mul_inv]; ring
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_right h1 hXnn
  have hstep_g : ∀ X : ℝ, X ≤ Cg / (gam α - 1) * HkSq α 4 g * HkSq α 4 f →
      X ≤ 100 / (gam α - 1) * (1 + Cf + Cg) * HkSq α 4 f * HkSq α 4 g := by
    intro X hX
    refine hX.trans ?_
    have h1 : Cg ≤ 100 * (1 + Cf + Cg) := by nlinarith
    have hXnng : 0 ≤ (gam α - 1)⁻¹ * (HkSq α 4 g * HkSq α 4 f) :=
      mul_nonneg (inv_nonneg.mpr hγ.le)
        (mul_nonneg (HkSq_nonneg α 4 g) (HkSq_nonneg α 4 f))
    have hL : Cg / (gam α - 1) * HkSq α 4 g * HkSq α 4 f
        = Cg * ((gam α - 1)⁻¹ * (HkSq α 4 g * HkSq α 4 f)) := by
      rw [div_eq_mul_inv]; ring
    have hR : 100 / (gam α - 1) * (1 + Cf + Cg) * HkSq α 4 f * HkSq α 4 g
        = (100 * (1 + Cf + Cg)) * ((gam α - 1)⁻¹ * (HkSq α 4 g * HkSq α 4 f)) := by
      rw [div_eq_mul_inv]; ring
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_right h1 hXnng
  have hstep_bad : ∀ X : ℝ, X ≤ 100 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g →
      X ≤ 100 / (gam α - 1) * (1 + Cf + Cg) * HkSq α 4 f * HkSq α 4 g := by
    intro X hX
    refine hX.trans ?_
    have h1 : (100 : ℝ) ≤ 100 * (1 + Cf + Cg) := by nlinarith
    have hL : 100 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g
        = 100 * ((gam α - 1)⁻¹ * (HkSq α 4 f * HkSq α 4 g)) := by
      rw [div_eq_mul_inv]; ring
    have hR : 100 / (gam α - 1) * (1 + Cf + Cg) * HkSq α 4 f * HkSq α 4 g
        = (100 * (1 + Cf + Cg)) * ((gam α - 1)⁻¹ * (HkSq α 4 f * HkSq α 4 g)) := by
      rw [div_eq_mul_inv]; ring
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_right h1 hXnn
  have hstep_bad2 : ∀ X : ℝ, X ≤ 100 / (gam α - 1) * HkSq α 4 g * HkSq α 4 f →
      X ≤ 100 / (gam α - 1) * (1 + Cf + Cg) * HkSq α 4 f * HkSq α 4 g := by
    intro X hX
    refine hX.trans ?_
    have h1 : (100 : ℝ) ≤ 100 * (1 + Cf + Cg) := by nlinarith
    have hXnng : 0 ≤ (gam α - 1)⁻¹ * (HkSq α 4 g * HkSq α 4 f) :=
      mul_nonneg (inv_nonneg.mpr hγ.le)
        (mul_nonneg (HkSq_nonneg α 4 g) (HkSq_nonneg α 4 f))
    have hL : 100 / (gam α - 1) * HkSq α 4 g * HkSq α 4 f
        = 100 * ((gam α - 1)⁻¹ * (HkSq α 4 g * HkSq α 4 f)) := by
      rw [div_eq_mul_inv]; ring
    have hR : 100 / (gam α - 1) * (1 + Cf + Cg) * HkSq α 4 f * HkSq α 4 g
        = (100 * (1 + Cf + Cg)) * ((gam α - 1)⁻¹ * (HkSq α 4 g * HkSq α 4 f)) := by
      rw [div_eq_mul_inv]; ring
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_right h1 hXnng
  -- the per-pair integrability and integral bound
  have hTerm : ∀ p ∈ bqP,
      (∀ z ∈ Iz, IntegrableOn (fun θ => (bqY α f g p z θ) ^ 2) Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Iθ, (bqY α f g p z θ) ^ 2) Iz ∧
      (∫ z in Iz, ∫ θ in Iθ, (bqY α f g p z θ) ^ 2)
        ≤ 100 / (gam α - 1) * (1 + Cf + Cg) * HkSq α 4 f * HkSq α 4 g := by
    intro p hp
    obtain ⟨a, b⟩ := p
    simp only [bqP, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨ha, hb⟩ := hp
    interval_cases a <;> interval_cases b
    · -- (a,b) = (0,0): `f · D_z³D_θg`
      have hlY : bqY α f g (0, 0)
          = fun z θ => (mixed 0 0 f z θ * mixed 3 1 g z θ) * Wt α z θ := by
        funext z θ; rfl
      rw [hlY]
      have hres := goodPair α hα f g Cf hfsq hCfb hgsq hmemg (b := 0) (a := 0)
        (j := 3) (i := 1) (by norm_num) (by norm_num) (by norm_num)
      exact ⟨hres.1, hres.2.1, hstep_f _ hres.2.2⟩
    · -- (a,b) = (0,1): `D_zf · D_z²D_θg`
      have hlY : bqY α f g (0, 1)
          = fun z θ => (mixed 1 0 f z θ * mixed 2 1 g z θ) * Wt α z θ := by
        funext z θ; rfl
      rw [hlY]
      have hres := goodPair α hα f g Cf hfsq hCfb hgsq hmemg (b := 1) (a := 0)
        (j := 2) (i := 1) (by norm_num) (by norm_num) (by norm_num)
      exact ⟨hres.1, hres.2.1, hstep_f _ hres.2.2⟩
    · -- (a,b) = (0,2): `D_z²f · D_zD_θg`
      have hlY : bqY α f g (0, 2)
          = fun z θ => (mixed 2 0 f z θ * mixed 1 1 g z θ) * Wt α z θ := by
        funext z θ; rfl
      rw [hlY]
      have hres := goodPair α hα f g Cf hfsq hCfb hgsq hmemg (b := 2) (a := 0)
        (j := 1) (i := 1) (by norm_num) (by norm_num) (by norm_num)
      exact ⟨hres.1, hres.2.1, hstep_f _ hres.2.2⟩
    · -- (a,b) = (0,3): the exceptional term `D_z³f · D_θg`
      have hlY : bqY α f g (0, 3)
          = fun z θ => DzIter 3 f z θ * Dth g z θ * Wt α z θ := by
        funext z θ
        simp only [bqY, bqT, mixed_zero_left, mixed_zero_right]
        norm_num
      rw [hlY]
      exact ⟨hpkg1.1.1, hpkg1.1.2, hstep_bad _ hpkg1.2⟩
    · -- (a,b) = (1,0): the exceptional term `D_θf · D_z³g`
      have hlY : bqY α f g (1, 0)
          = fun z θ => Dth f z θ * DzIter 3 g z θ * Wt α z θ := by
        funext z θ
        simp only [bqY, bqT, mixed_zero_left, mixed_zero_right]
        norm_num
      rw [hlY]
      exact ⟨hpkg2.1.1, hpkg2.1.2, hstep_bad2 _ hpkg2.2⟩
    · -- (a,b) = (1,1): `D_zD_θf · D_z²g`
      have hlY : bqY α f g (1, 1)
          = fun z θ => (mixed 1 1 f z θ * mixed 2 0 g z θ) * Wt α z θ := by
        funext z θ; rfl
      rw [hlY]
      have hres := goodPairSwap α hα g f Cg hgsq hCgb hfsq hmemf (b := 2) (a := 0)
        (j := 1) (i := 1) (by norm_num) (by norm_num) (by norm_num)
      exact ⟨hres.1, hres.2.1, hstep_g _ hres.2.2⟩
    · -- (a,b) = (1,2): `D_z²D_θf · D_zg`
      have hlY : bqY α f g (1, 2)
          = fun z θ => (mixed 2 1 f z θ * mixed 1 0 g z θ) * Wt α z θ := by
        funext z θ; rfl
      rw [hlY]
      have hres := goodPairSwap α hα g f Cg hgsq hCgb hfsq hmemf (b := 1) (a := 0)
        (j := 2) (i := 1) (by norm_num) (by norm_num) (by norm_num)
      exact ⟨hres.1, hres.2.1, hstep_g _ hres.2.2⟩
    · -- (a,b) = (1,3): `D_z³D_θf · g`
      have hlY : bqY α f g (1, 3)
          = fun z θ => (mixed 3 1 f z θ * mixed 0 0 g z θ) * Wt α z θ := by
        funext z θ; rfl
      rw [hlY]
      have hres := goodPairSwap α hα g f Cg hgsq hCgb hfsq hmemf (b := 0) (a := 0)
        (j := 3) (i := 1) (by norm_num) (by norm_num) (by norm_num)
      exact ⟨hres.1, hres.2.1, hstep_g _ hres.2.2⟩
  -- the majorant sums
  have hGslice : ∀ z ∈ Iz, IntegrableOn
      (fun θ => 72 * ∑ p ∈ bqP, (bqY α f g p z θ) ^ 2) Iθ :=
    fun z hz => (integrableOn_finsetSumQ bqP (fun p hp => (hTerm p hp).1 z hz)).const_mul 72
  have hGhat : IntegrableOn
      (fun z => 72 * ∑ p ∈ bqP, ∫ θ in Iθ, (bqY α f g p z θ) ^ 2) Iz :=
    (integrableOn_finsetSumQ bqP (fun p hp => (hTerm p hp).2.1)).const_mul 72
  -- strong measurability of the target
  have hTslice_meas : ∀ z ∈ Iz, AEStronglyMeasurable
      (fun θ => (mixed 3 1 (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2)
      (volume.restrict Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
    · subst h0
      have hzero : (fun θ => (mixed 3 1 (fun z θ => f z θ * g z θ) 0 θ * Wt α 0 θ) ^ 2)
          = fun _ => (0 : ℝ) := by
        funext θ; rw [Wt_zero_left]; ring
      rw [hzero]
      exact aestronglyMeasurable_const
    · exact aesm_slice_mixed_Wt_sq α (fun z θ => f z θ * g z θ) hsmFG 3 1 hpos
  -- integrability of the angular slices of the target
  have hTslice_int : ∀ z ∈ Iz, IntegrableOn
      (fun θ => (mixed 3 1 (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2) Iθ := by
    intro z hz
    refine MeasureTheory.Integrable.mono' (hGslice z hz) (hTslice_meas z hz) ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hYsq z hz θ hθ
  -- the slicewise domination of the angular integral
  have hslice_le : ∀ z ∈ Iz,
      ∫ θ in Iθ, (mixed 3 1 (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        ≤ 72 * ∑ p ∈ bqP, ∫ θ in Iθ, (bqY α f g p z θ) ^ 2 := by
    intro z hz
    have h2 : ∫ θ in Iθ, 72 * ∑ p ∈ bqP, (bqY α f g p z θ) ^ 2
        = 72 * ∑ p ∈ bqP, ∫ θ in Iθ, (bqY α f g p z θ) ^ 2 := by
      rw [MeasureTheory.integral_const_mul]
      congr 1
      exact integral_finsetSum bqP (fun p hp => (hTerm p hp).1 z hz)
    rw [← h2]
    exact integral_mono_ae (hTslice_int z hz) (hGslice z hz)
      (ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => hYsq z hz θ hθ)
  -- integrability of the outer integral of the target
  have hTouter_int : IntegrableOn (fun z => ∫ θ in Iθ,
      (mixed 3 1 (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2) Iz := by
    refine MeasureTheory.Integrable.mono' hGhat
      ((aesm_mixed_Wt_sq_prod_quad α (fun z θ => f z θ * g z θ) hsmFG 3 1).integral_prod_right')
      ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact hslice_le z hz
  refine ⟨⟨hTslice_int, hTouter_int⟩, ?_⟩
  calc L2Sq (fun z θ => mixed 3 1 (fun z θ => f z θ * g z θ) z θ * Wt α z θ)
      = ∫ z in Iz, ∫ θ in Iθ,
          (mixed 3 1 (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2 := rfl
    _ ≤ ∫ z in Iz, 72 * ∑ p ∈ bqP, ∫ θ in Iθ, (bqY α f g p z θ) ^ 2 :=
        integral_mono_ae hTouter_int hGhat
          (ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hslice_le z hz)
    _ = 72 * ∑ p ∈ bqP, ∫ z in Iz, ∫ θ in Iθ, (bqY α f g p z θ) ^ 2 := by
        rw [MeasureTheory.integral_const_mul]
        congr 1
        exact integral_finsetSum bqP (fun p hp => (hTerm p hp).2.1)
    _ ≤ 72 * ∑ p ∈ bqP,
          (100 / (gam α - 1) * (1 + Cf + Cg) * HkSq α 4 f * HkSq α 4 g) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum fun p hp => (hTerm p hp).2.2
    _ = 72 * (8 * (100 / (gam α - 1) * (1 + Cf + Cg) * HkSq α 4 f * HkSq α 4 g)) := by
        congr 1
        rw [Finset.sum_const, bqP_card, nsmul_eq_mul]
        norm_num
    _ ≤ 10 ^ 12 / (gam α - 1) * (1 + Cf + Cg) * HkSq α 4 f * HkSq α 4 g := by
        have h1nn : 0 ≤ 1 + Cf + Cg := by linarith
        have hL : 72 * (8 * (100 / (gam α - 1) * (1 + Cf + Cg) * HkSq α 4 f * HkSq α 4 g))
            = (72 * 8 * 100)
              * ((1 + Cf + Cg) * ((gam α - 1)⁻¹ * (HkSq α 4 f * HkSq α 4 g))) := by
          rw [div_eq_mul_inv]; ring
        have hR : 10 ^ 12 / (gam α - 1) * (1 + Cf + Cg) * HkSq α 4 f * HkSq α 4 g
            = (10 ^ 12)
              * ((1 + Cf + Cg) * ((gam α - 1)⁻¹ * (HkSq α 4 f * HkSq α 4 g))) := by
          rw [div_eq_mul_inv]; ring
        rw [hL, hR]
        exact mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg h1nn hXnn)

end Work.FTS.H2.HQ
end
end
