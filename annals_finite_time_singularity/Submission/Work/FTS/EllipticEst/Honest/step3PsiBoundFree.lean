/-
Copyright: work module for the Elgindi finite-time singularity project.

# `step3PsiBoundFree`: the `I₄`/`Ψ̄`-bound of Step 3 of `prop:H2`, self-contained

Target (`Work.FTS.EllipticEst.Honest.step3PsiBoundFree`): in the honest class `Hon α F Ψ`
of `Honest/Basic.lean` there is a universal `C > 0` with

  `√(HkSq α 0 (POf Ψ)) ≤ C (√(HkSq α 0 Ψ) + √(HkSq α 0 (∂_θθΨ)))`,

where `POf Ψ = sin θ · ∂_θ(Ψ / cos θ)` is the `I₄`-quantity whose norm the positivity
`I_{4,2}` of Elgindi, Annals **194** (2021), tex 890--905 controls.

## Route

At level `0` the `HkIntegrand` of `Work.Spaces` is `α`-free: for `k = 0` the mixed-derivative
double sum is empty and only the term `i = 0` of the `D_z`-sum survives
(`Honest.HkIntegrand_zero_eq`), so `HkSq α 0 g` and `HkMem α 0 g` do not depend on `α`
(`step3free_HkIntegrand_zero_alpha`, `step3free_HkSq_zero_alpha`,
`step3free_HkMem_zero_alpha`).  The statement is therefore the `α = 0` instance

  `√(HkSq 0 0 (sin θ · ∂_θ(Ψ/cos θ))) ≤ C (√(HkSq 0 0 Ψ) + √(HkSq 0 0 (∂_θθΨ)))`,

proved here as `step3free_psiBar_aux`.  The proof is the slice argument of
`TanTheta.slice_ident`: at each `z > 0` the slice `u = Ψ z ·` is `C²` on `(0,π/2)` with
`u 0 = u (π/2) = 0` (`Hon.sm`, `Hon.d0`, `Hon.dπ`), its honest `σ`-weighted `L²`-data are
integrable (`Hon.memB`, `Hon.memG`), and

* `slice_psi_mem_alt` supplies `∫ (u/cos θ)²σ < ∞` and `∫ ((u/cos θ)')²σ < ∞`;
* `psi_boundary_vanish` supplies the four boundary limits of `wrho·(u/cos)²` and
  `wrho·((u/cos)')²` needed to integrate by parts;
* `slice_ident_honest` is the (twice-integrated-by-parts) `I₄` identity
  `∫ sinθ ψ' u'' σ = ((1-η)/2)∫ cos2θ ψ² σ - ∫ acoef·ψ'² σ`;
* `slice_sq_le_of_ident` turns it into `∫ sin²θ ψ'² σ ≤ ∫ u''² σ + 2 ∫ u² σ`.

The `z`-assembly (`step3free_bar_of_slice_le`) multiplies by `w z²`, integrates in `z`, uses
`HkMem` for the three integrability statements in `z`, and identifies the weighted integrals
with `HkSq 0 0` (`hkSq_zero_eq_sliceW`, `hkIntegrand_zero_integral_eq`).

This file is *self-contained* within its own import cone: it neither imports
`Honest.step3PsiBar` (whose import `TanTheta.slice_hypotheses` does not compile in this
toolchain) nor the `TT` chapter; it re-runs the (short) assembly on top of `slicePsiMemAlt`.
The statement is the same as that of the sibling
`Work.FTS.EllipticEst.Honest.step3PsiBoundClean`, which reaches it through the `TT` module.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.step3Defs
import Submission.Work.FTS.EllipticEst.Mine.slice_ident_bound_fts
import Submission.Work.FTS.EllipticEst.Honest.SliceMain
import Submission.Work.FTS.EllipticEst.Honest.slicePsiMemAlt
import Submission.Work.FTS.EllipticEst.Honest.psi_boundary_vanish
import Submission.Work.FTS.EllipticEst.Honest.slice_ident_honest

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
set_option linter.unusedVariables false

/-- Local abbreviation for the angular weight `σ θ = sin(2θ)^{-η}`
(`Work.FTS.EllipticEst.AngSecond.sig`). -/
local notation "sg" => Work.FTS.EllipticEst.AngSecond.sig

/-! ## The level-`0` objects are independent of `α` -/

/-- **The level-`0` `HkIntegrand` does not depend on `α`.**  At level `0` the
mixed-derivative sum of `Work.Spaces.HkIntegrand` is empty and only the term `i = 0` of the
`D_z`-sum survives, so the integrand is the single square
`(g z θ · w z / sin(2θ)^{η/2})²` (`Honest.HkIntegrand_zero_eq`). -/
theorem step3free_HkIntegrand_zero_alpha (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ = Work.Spaces.HkIntegrand 0 0 g z θ := by
  rw [HkIntegrand_zero_eq, HkIntegrand_zero_eq]

/-- **`HkSq α 0` does not depend on `α`.** -/
theorem step3free_HkSq_zero_alpha (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 g = Work.Spaces.HkSq 0 0 g := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ =>
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ =>
      step3free_HkIntegrand_zero_alpha α g z θ

/-- **`HkMem α 0` does not depend on `α`.** -/
theorem step3free_HkMem_zero_alpha {α : ℝ} {g : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkMem α 0 g) : Work.Spaces.HkMem 0 0 g := by
  have hpt : ∀ z θ, Work.Spaces.HkIntegrand 0 0 g z θ = Work.Spaces.HkIntegrand α 0 g z θ :=
    fun z θ => (step3free_HkIntegrand_zero_alpha α g z θ).symm
  constructor
  · intro z hz
    exact (h.1 z hz).congr_fun (fun θ _ => hpt z θ) measurableSet_Icc
  · exact h.2.congr_fun (fun z _ => MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ _ => hpt z θ)) measurableSet_Ici

/-! ## The `α = 0` slice bound (Elgindi's `I_{4,2}` positivity) -/

/-- `√(a+b) ≤ √a + √b` for `a, b ≥ 0`. -/
theorem step3free_sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- **The `z`-assembly.**  If the slicewise estimate
`∫ sin²θ (∂_θ(Ψ/cos θ))² σ ≤ ∫ (∂_θθΨ)² σ + 2 ∫ Ψ² σ` holds at every `z > 0`, then the
honest `HkSq`-bound holds with constant `2`. -/
theorem step3free_bar_of_slice_le (Ψ : ℝ → ℝ → ℝ)
    (hmemΨ : Work.Spaces.HkMem 0 0 Ψ)
    (hmemB : Work.Spaces.HkMem 0 0 (Work.Spaces.pthIter 2 Ψ))
    (hmemG : Work.Spaces.HkMem 0 0 (fun z θ => Real.sin θ
      * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ))
    (hsl : ∀ z : ℝ, 0 < z →
      (∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin θ) ^ 2
          * (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sg θ)
        ≤ (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sg θ)
          + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)) :
    Real.sqrt (Work.Spaces.HkSq 0 0 (fun z θ => Real.sin θ
        * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ))
      ≤ 2 * (Real.sqrt (Work.Spaces.HkSq 0 0 Ψ)
        + Real.sqrt (Work.Spaces.HkSq 0 0 (Work.Spaces.pthIter 2 Ψ))) := by
  set G : ℝ → ℝ → ℝ := fun z θ => Real.sin θ
    * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ with hG
  set B : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ with hB
  have hmemG' : Work.Spaces.HkMem 0 0 G := hmemG
  have hmemB' : Work.Spaces.HkMem 0 0 B := hmemB
  -- the pointwise (in `z`) inequality, weighted by `w²`
  have hpt : ∀ z ∈ Work.Spaces.Iz,
      (Work.Spaces.w z) ^ 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ)
        ≤ (Work.Spaces.w z) ^ 2 * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
            + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)) := by
    intro z hz
    have hz' : (0 : ℝ) ≤ z := hz
    rcases eq_or_lt_of_le hz' with h | h
    · subst h
      have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
      simp [hw0]
    · have h1 : (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ)
          ≤ (∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
            + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ) := by
        have hG2 : ∀ θ : ℝ, (G z θ) ^ 2 * sg θ = (Real.sin θ) ^ 2
            * (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sg θ := by
          intro θ; rw [hG]; ring
        have hB2 : ∀ θ : ℝ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sg θ
            = (B z θ) ^ 2 * sg θ := by
          intro θ; rw [hB]
        calc (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ)
            = (∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin θ) ^ 2
                * (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sg θ) :=
              MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hG2 θ)
          _ ≤ (∫ θ in Set.Ioo 0 (Real.pi / 2), (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sg θ)
                + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ) := hsl z h
          _ = (∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
                + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ) := by
              rw [show (∫ θ in Set.Ioo 0 (Real.pi / 2),
                    (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sg θ)
                  = ∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ from
                MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hB2 θ)]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  -- integrability of the three `z`-integrands
  have hintG : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ)) Work.Spaces.Iz := by
    refine hmemG'.2.congr_fun (fun z hz => ?_) measurableSet_Ici
    exact hkIntegrand_zero_integral_eq hmemG' hz
  have hintB : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)) Work.Spaces.Iz := by
    refine hmemB'.2.congr_fun (fun z hz => ?_) measurableSet_Ici
    exact hkIntegrand_zero_integral_eq hmemB' hz
  have hintP : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)) Work.Spaces.Iz := by
    refine hmemΨ.2.congr_fun (fun z hz => ?_) measurableSet_Ici
    exact hkIntegrand_zero_integral_eq hmemΨ hz
  have hintR : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
        + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ))) Work.Spaces.Iz := by
    refine (hintB.add (hintP.const_mul 2)).congr_fun (fun z _ => ?_) measurableSet_Ici
    simp only [Pi.add_apply]
    ring
  have hmono : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ))
      ≤ (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
          + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ))) :=
    MeasureTheory.setIntegral_mono_on hintG hintR measurableSet_Ici hpt
  have eL : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ))
      = Work.Spaces.HkSq 0 0 G := (hkSq_zero_eq_sliceW hmemG').symm
  have eR : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
      * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
        + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)))
      = Work.Spaces.HkSq 0 0 B + 2 * Work.Spaces.HkSq 0 0 Ψ := by
    have hsplit : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
          + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)))
        = (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ))
          + 2 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)) := by
      rw [show (fun z => (Work.Spaces.w z) ^ 2
            * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
              + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)))
          = (fun z => (Work.Spaces.w z) ^ 2
              * (∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
            + 2 * ((Work.Spaces.w z) ^ 2
              * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ))) from by
        funext z; ring]
      rw [MeasureTheory.integral_add hintB (hintP.const_mul 2),
        MeasureTheory.integral_const_mul]
    rw [hsplit, hkSq_zero_eq_sliceW hmemB', hkSq_zero_eq_sliceW hmemΨ]
  have hmain : Work.Spaces.HkSq 0 0 G ≤ Work.Spaces.HkSq 0 0 B + 2 * Work.Spaces.HkSq 0 0 Ψ := by
    rw [← eL, ← eR]
    exact hmono
  have hBnn : 0 ≤ Work.Spaces.HkSq 0 0 B := HkSq_zero_nonneg 0 B
  have hPnn : 0 ≤ Work.Spaces.HkSq 0 0 Ψ := HkSq_zero_nonneg 0 Ψ
  have h2 : Real.sqrt 2 ≤ 2 := by
    have h := Real.sqrt_two_lt_three_halves
    linarith
  have h3 := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg (Work.Spaces.HkSq 0 0 Ψ))
  calc Real.sqrt (Work.Spaces.HkSq 0 0 G)
      ≤ Real.sqrt (Work.Spaces.HkSq 0 0 B + 2 * Work.Spaces.HkSq 0 0 Ψ) :=
        Real.sqrt_le_sqrt hmain
    _ ≤ Real.sqrt (Work.Spaces.HkSq 0 0 B) + Real.sqrt (2 * Work.Spaces.HkSq 0 0 Ψ) :=
        step3free_sqrt_add_le_sqrt_add_sqrt hBnn (by positivity)
    _ = Real.sqrt (Work.Spaces.HkSq 0 0 B)
          + Real.sqrt 2 * Real.sqrt (Work.Spaces.HkSq 0 0 Ψ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * (Real.sqrt (Work.Spaces.HkSq 0 0 Ψ) + Real.sqrt (Work.Spaces.HkSq 0 0 B)) := by
        linarith [Real.sqrt_nonneg (Work.Spaces.HkSq 0 0 B)]

/-- **The `I₄`/`Ψ̄`-bound of Step 2 of `prop:H2` (`α = 0`).**  Under the honest slice
hypotheses (smoothness on the open quadrant, the two Dirichlet data as values, and the three
honest weighted `L²`-integrals), the `σ`-weighted `L²`-norm of `sin θ · ∂_θ(Ψ/cos θ)` is
controlled by the norms of `Ψ` and of `∂_θθΨ` — the positivity `I_{4,2}` of Elgindi,
Annals **194** (2021), tex 890--905.  The constant is `2`.

This is `Honest.step3PsiBar` with the broken import `Honest.slice_psi_mem` replaced by the
clean-cone `Honest.slice_psi_mem_alt`; the rest of the proof is unchanged. -/
theorem step3free_psiBar_aux : ∃ C : ℝ, 0 < C ∧ ∀ (Ψ : ℝ → ℝ → ℝ),
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
    (∀ z, Ψ z 0 = 0) → (∀ z, Ψ z (Real.pi / 2) = 0) →
    Work.Spaces.HkMem 0 0 Ψ →
    Work.Spaces.HkMem 0 0 (Work.Spaces.pthIter 2 Ψ) →
    Work.Spaces.HkMem 0 0
      (fun z θ => Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) →
    Real.sqrt (Work.Spaces.HkSq 0 0
        (fun z θ => Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ))
      ≤ C * (Real.sqrt (Work.Spaces.HkSq 0 0 Ψ)
        + Real.sqrt (Work.Spaces.HkSq 0 0 (Work.Spaces.pthIter 2 Ψ))) := by
  refine ⟨2, by norm_num, ?_⟩
  intro Ψ hsm h0 h1 hmemΨ hmemB hmemG
  refine step3free_bar_of_slice_le Ψ hmemΨ hmemB hmemG ?_
  intro z hz
  -- the slice hypotheses
  have hu : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_slice_of_hsm hsm hz 2
  have hB : IntegrableOn (fun θ => (Ψ z θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (integrableOn_sq_mul_sig_of_hkMem hmemΨ hz).mono_set Set.Ioo_subset_Icc_self
  have hX : IntegrableOn (fun θ => (deriv (deriv (fun θ' => Ψ z θ')) θ) ^ 2 * sg θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine ((integrableOn_sq_mul_sig_of_hkMem hmemB hz).mono_set
      Set.Ioo_subset_Icc_self).congr_fun (fun θ _ => ?_) measurableSet_Ioo
    show Work.Spaces.pthIter 2 Ψ z θ ^ 2 * sg θ
      = deriv (deriv (fun θ' => Ψ z θ')) θ ^ 2 * sg θ
    rw [pthIter_two_apply]
  have hY : IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2)) := by
    refine ((integrableOn_sq_mul_sig_of_hkMem hmemG hz).mono_set
      Set.Ioo_subset_Icc_self).congr_fun (fun θ _ => ?_) measurableSet_Ioo
    show (Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sg θ
      = (Real.sin θ) ^ 2 * (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2 * sg θ
    rw [pth_div_apply]
    ring
  obtain ⟨hA, hA'⟩ := slice_psi_mem_alt (fun θ => Ψ z θ) hu (h0 z) (h1 z) hB hX hY
  obtain ⟨hv1, hv2, hv3, hv4⟩ :=
    psi_boundary_vanish (fun θ => Ψ z θ) hu (h0 z) (h1 z) hB hX hY hA hA'
  have hident := slice_ident_honest (fun θ => Ψ z θ) hu (h0 z) (h1 z) hB hX hY hA hA'
    hv1 hv2 hv3 hv4
  have hpth : ∀ θ : ℝ, Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ
      = deriv (fun θ' => Ψ z θ' / Real.cos θ') θ := fun θ => pth_div_apply Ψ z θ
  have hpth2 : ∀ θ : ℝ, Work.Spaces.pthIter 2 Ψ z θ
      = deriv (deriv (fun θ' => Ψ z θ')) θ := fun θ => pthIter_two_apply Ψ z θ
  simpa only [hpth, hpth2] using
    slice_sq_le_of_ident (fun θ => Ψ z θ) hu hA hA' hB hX hY hident

/-! ## The target -/

theorem step3PsiBoundFree : ∃ C : ℝ, 0 < C ∧
  ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ →
    Work.Spaces.HkMem α 0 Ψ →
    Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ) →
    Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) →
    Work.Spaces.HkMem α 0 (POf Ψ) →
    Real.sqrt (Work.Spaces.HkSq α 0 (POf Ψ))
      ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
        + Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))) := by
  obtain ⟨C, hC, hbar⟩ := step3free_psiBar_aux
  refine ⟨C, hC, ?_⟩
  intro α F Ψ hHon hΨ hB _hpsi hP
  have hΨ0 : Work.Spaces.HkMem 0 0 Ψ := step3free_HkMem_zero_alpha hΨ
  have hB0 : Work.Spaces.HkMem 0 0 (Work.Spaces.pthIter 2 Ψ) :=
    step3free_HkMem_zero_alpha hB
  have hP0 : Work.Spaces.HkMem 0 0 (fun z θ => Real.sin θ
      * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) := hP
  have hres := hbar Ψ hHon.sm hHon.d0 hHon.dπ hΨ0 hB0 hP0
  rw [step3free_HkSq_zero_alpha α (POf Ψ),
    step3free_HkSq_zero_alpha α Ψ,
    step3free_HkSq_zero_alpha α (Work.Spaces.pthIter 2 Ψ)]
  exact hres

end Work.FTS.EllipticEst.Honest
