/-
Copyright: work module for the Elgindi finite-time singularity project.

# Order transfer for the angular iterates: `Gγ α i u` against the lower iterates

This module proves

`Work.FTS.EllipticEst.TT.iter_le_of_lower_u`,

the estimate

`Gγ α i u ≤ K i · ( Gη u + ∑_{k=1}^{i-2} Gγ α k (D2 u) + ∑_{k=1}^{i-1} Gγ α k u )`

for every `i ≥ 2`, every `α ∈ (0, 1/4]` and every smooth `θ`-slice `u`, with constants
`K i` independent of `α` and `u`.

Proof route.  Let `m = i - 2`, `A θ = sin(2θ)²`, `B θ = 2 cos(2θ)`, `g = D2 u = u''` and
`h = D_θ u`.  The second order identity

  `D_θ² u = A · g + B · h`

(valid on the open neighbourhood of `Iθ` on which `u` is smooth) propagates through the
iterate `D_θ^m`, and the Leibniz rule for the derivation `D_θ = sin(2θ) ∂_θ` with binomial
coefficients, followed by Cauchy–Schwarz on the finite sum, gives the pointwise bound

`(D_θ^i u θ)² ≤ 2 (m+1) ∑_{j ≤ m} C(m,j)² ( (D_θ^j A θ)² (D_θ^{m-j} g θ)²
   + (D_θ^j B θ)² (D_θ^{m-j} h θ)² )`.

Since `D_θ^j A` vanishes like `sin(2θ)²` while `D_θ^j B` is bounded, and since
`sin(2θ)^{4-γ} ≤ sin(2θ)^{-η}` (`γ = 1 + α/10 ≤ 1.025`, `η = 99/100`), multiplying by the
weight `sin(2θ)^{-γ}` and integrating turns the terms with `m - j ≥ 1` into the `Gγ` sums
and the single term with `m - j = 0` into `Gη`.  The integrability hypotheses make every
integral honest, so the pointwise bound may be integrated termwise.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.SliceCoercDefs
import Submission.Work.FTS.EllipticEst.TT.Dth1Iter_mul_sq_le
import Submission.Work.FTS.EllipticEst.TT.Dth1Iter_add_of_smooth
import Submission.Work.FTS.EllipticEst.TT.Dth1Iter_eventuallyEq
import Submission.Work.FTS.EllipticEst.TT.Dth1Iter_sin_sq_bdd
import Submission.Work.FTS.EllipticEst.TT.iterFamilyA_le
import Submission.Work.FTS.EllipticEst.TT.iterFamilyB_le
import Submission.Work.FTS.EllipticEst.Dth1IterTwoCosBoundN

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-- The open neighbourhood `(-1, π/2 + 1)` of the closed interval `Iθ = [0, π/2]`; it is
exactly the domain of `Work.Elliptic.SmoothSlice`. -/
private def SU : Set ℝ := Set.Ioo (-1) (Real.pi / 2 + 1)

private theorem mem_Iθ_iff {θ : ℝ} : θ ∈ Work.Spaces.Iθ ↔ 0 ≤ θ ∧ θ ≤ Real.pi / 2 :=
  Iff.rfl

private theorem Iθ_subset_SU : Work.Spaces.Iθ ⊆ SU := by
  intro θ hθ
  obtain ⟨h1, h2⟩ := mem_Iθ_iff.mp hθ
  exact ⟨by linarith [h1], by linarith [h2, Real.pi_pos]⟩

private theorem isOpen_SU : IsOpen SU := isOpen_Ioo

/-! ## Smoothness of the auxiliary functions -/

private theorem contDiffOn_deriv {u : ℝ → ℝ} (hu : Work.Elliptic.SmoothSlice u) :
    ContDiffOn ℝ ⊤ (deriv u) SU :=
  hu.deriv_of_isOpen isOpen_Ioo le_top

/-- `u''` is smooth on `SU` when `u` is. -/
private theorem smoothSlice_D2 {u : ℝ → ℝ} (hu : Work.Elliptic.SmoothSlice u) :
    Work.Elliptic.SmoothSlice (D2 u) :=
  (contDiffOn_deriv hu).deriv_of_isOpen isOpen_Ioo le_top

private theorem contDiffOn_sin_two : ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) SU := by
  have h : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
  exact h.contDiffOn

private theorem contDiffOn_two_cos : ContDiffOn ℝ ⊤ (fun θ : ℝ => 2 * Real.cos (2 * θ)) SU := by
  have h : ContDiff ℝ ⊤ (fun θ : ℝ => 2 * Real.cos (2 * θ)) :=
    contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))
  exact h.contDiffOn

/-- `D_θ u = sin(2θ) u'` is smooth on `SU` when `u` is. -/
private theorem smoothSlice_Dth1 {u : ℝ → ℝ} (hu : Work.Elliptic.SmoothSlice u) :
    Work.Elliptic.SmoothSlice (Work.Elliptic.Dth1 u) := by
  have h := contDiffOn_sin_two.mul (contDiffOn_deriv hu)
  exact h

private theorem smoothSlice_mul {F G : ℝ → ℝ} (hF : Work.Elliptic.SmoothSlice F)
    (hG : Work.Elliptic.SmoothSlice G) :
    Work.Elliptic.SmoothSlice (fun θ => F θ * G θ) := hF.mul hG

private theorem smoothSlice_add {F G : ℝ → ℝ} (hF : Work.Elliptic.SmoothSlice F)
    (hG : Work.Elliptic.SmoothSlice G) :
    Work.Elliptic.SmoothSlice (fun θ => F θ + G θ) := hF.add hG

private theorem smoothSlice_sin_sq :
    Work.Elliptic.SmoothSlice (fun θ : ℝ => Real.sin (2 * θ) ^ 2) := by
  have h : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ) ^ 2) := by fun_prop
  exact h.contDiffOn

private theorem smoothSlice_two_cos :
    Work.Elliptic.SmoothSlice (fun θ : ℝ => 2 * Real.cos (2 * θ)) :=
  contDiffOn_two_cos

private theorem contDiffAt_deriv_of_mem {u : ℝ → ℝ} (hu : Work.Elliptic.SmoothSlice u)
    {θ : ℝ} (hθ : θ ∈ SU) : DifferentiableAt ℝ (deriv u) θ :=
  ((contDiffOn_deriv hu).contDiffAt (isOpen_SU.mem_nhds hθ)).differentiableAt (by simp)

/-! ## The second order identity `D_θ² u = sin(2θ)² u'' + 2 cos(2θ) D_θ u` -/

private theorem Dth1Iter_two_eq (u : ℝ → ℝ) (hu : Work.Elliptic.SmoothSlice u) {θ : ℝ}
    (hθ : θ ∈ SU) :
    Work.Elliptic.Dth1Iter 2 u θ
      = (Real.sin (2 * θ)) ^ 2 * D2 u θ + 2 * Real.cos (2 * θ) * Work.Elliptic.Dth1 u θ := by
  have hdu : DifferentiableAt ℝ (deriv u) θ := contDiffAt_deriv_of_mem hu hθ
  have hderiv : deriv (Work.Elliptic.Dth1 u) θ
      = 2 * Real.cos (2 * θ) * deriv u θ + Real.sin (2 * θ) * D2 u θ := by
    have h1 : HasDerivAt (fun τ : ℝ => 2 * τ) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h2 : HasDerivAt (fun τ : ℝ => Real.sin (2 * τ)) (Real.cos (2 * θ) * 2) θ :=
      (Real.hasDerivAt_sin (2 * θ)).comp θ h1
    have h3 := h2.mul hdu.hasDerivAt
    have h4 : deriv (fun τ : ℝ => Real.sin (2 * τ) * deriv u τ) θ
        = (Real.cos (2 * θ) * 2) * deriv u θ + Real.sin (2 * θ) * deriv (deriv u) θ :=
      h3.deriv
    rw [show deriv (Work.Elliptic.Dth1 u) θ
        = deriv (fun τ : ℝ => Real.sin (2 * τ) * deriv u τ) θ from rfl, h4]
    simp only [D2]
    ring
  simp only [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1Iter_zero, Work.Elliptic.Dth1]
  rw [hderiv]
  ring

/-! ## Composition of the iterates -/

private theorem Dth1Iter_add_index (m n : ℕ) (f : ℝ → ℝ) :
    Work.Elliptic.Dth1Iter (m + n) f = Work.Elliptic.Dth1Iter m (Work.Elliptic.Dth1Iter n f) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [Nat.succ_add, Work.Elliptic.Dth1Iter_succ, ih]

/-! ## The weights `sEta` and `sGam` -/

/-- On `Iθ`, `sin(2θ)⁴ · sin(2θ)^{-γ} ≤ sin(2θ)^{-γ}`. -/
private theorem sin_sq_sq_mul_sGam_le_sGam (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    ((Real.sin (2 * θ)) ^ 2) ^ 2 * sGam α θ ≤ sGam α θ := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h4 : ((Real.sin (2 * θ)) ^ 2) ^ 2 ≤ 1 := by
    have hs2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := pow_le_one₀ hs0 hs1
    exact pow_le_one₀ (sq_nonneg _) hs2
  have hnn : 0 ≤ sGam α θ := sGam_nonneg α hθ
  calc ((Real.sin (2 * θ)) ^ 2) ^ 2 * sGam α θ
      ≤ 1 * sGam α θ := mul_le_mul_of_nonneg_right h4 hnn
    _ = sGam α θ := one_mul _

/-- On `Iθ`, `sin(2θ)⁴ · sin(2θ)^{-γ} ≤ sin(2θ)^{-η}` (the exponent `4 - γ ≥ -η`). -/
private theorem sin_sq_sq_mul_sGam_le_sEta (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    ((Real.sin (2 * θ)) ^ 2) ^ 2 * sGam α θ ≤ sEta θ := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam2 : Work.Spaces.gam α ≤ 2 := by
    rw [Work.Spaces.gam]
    linarith
  have hexp : -(Work.Spaces.eta) ≤ 4 - Work.Spaces.gam α := by
    have h1 : (0 : ℝ) < Work.Spaces.eta := Work.Spaces.eta_pos
    linarith
  have hsGam : sGam α θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := rfl
  have hsEta : sEta θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := rfl
  have hgamne : -(Work.Spaces.gam α) ≠ 0 :=
    neg_ne_zero.mpr (ne_of_gt (Work.Spaces.gam_pos hα))
  have hetane : -(Work.Spaces.eta) ≠ 0 :=
    neg_ne_zero.mpr (ne_of_gt Work.Spaces.eta_pos)
  rw [hsGam, hsEta]
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h]
    rw [Real.zero_rpow hgamne, Real.zero_rpow hetane]
    norm_num
  · have hexp' : -(Work.Spaces.eta) ≤ (((4 : ℕ) : ℝ) + -(Work.Spaces.gam α)) := by
      push_cast
      linarith
    have hmain : (Real.sin (2 * θ)) ^ (((4 : ℕ) : ℝ) + -(Work.Spaces.gam α))
        ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Real.rpow_le_rpow_of_exponent_ge h hs1 hexp'
    have hpow : ((Real.sin (2 * θ)) ^ 2) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = (Real.sin (2 * θ)) ^ (((4 : ℕ) : ℝ) + -(Work.Spaces.gam α)) := by
      rw [show ((Real.sin (2 * θ)) ^ 2) ^ 2 = (Real.sin (2 * θ)) ^ (((4 : ℕ) : ℝ)) by
            rw [Real.rpow_natCast]; ring,
        ← Real.rpow_add h (((4 : ℕ) : ℝ)) (-(Work.Spaces.gam α))]
    rw [hpow]
    exact hmain

/-! ## Reindexing a sum over `Icc 1 n` as a sum over `range n` -/

private theorem sum_Icc_one_eq_sum_range (n : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 n, f k = ∑ k ∈ Finset.range n, f (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih, Finset.sum_range_succ]

/-! ## The constant -/

/-- The constant of the pointwise (and hence integral) estimate, as a function of the
coefficient families `cA` (for `D_θ^j (sin(2θ)²)`) and `cB` (for `D_θ^j (2 cos 2θ)`). -/
private noncomputable def Kc (i : ℕ) (cA cB : ℕ → ℝ) : ℝ :=
  2 * (((i - 2 : ℕ) : ℝ) + 1) *
    ((∑ j ∈ Finset.range (i - 2 + 1), (4 : ℝ) ^ (i - 2) * cA j)
      + (∑ j ∈ Finset.range (i - 2 + 1), (4 : ℝ) ^ (i - 2) * cB j) + 1)

private theorem Kc_nonneg {cA cB : ℕ → ℝ} (hcA : ∀ j, 0 ≤ cA j) (hcB : ∀ j, 0 ≤ cB j)
    (i : ℕ) : 0 ≤ Kc i cA cB := by
  have hCA : 0 ≤ ∑ j ∈ Finset.range (i - 2 + 1), (4 : ℝ) ^ (i - 2) * cA j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg (by norm_num) _) (hcA j)
  have hCB : 0 ≤ ∑ j ∈ Finset.range (i - 2 + 1), (4 : ℝ) ^ (i - 2) * cB j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg (by norm_num) _) (hcB j)
  unfold Kc
  exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (by linarith)

private theorem Kc_eq (i : ℕ) {cA cB : ℕ → ℝ} {CA CB : ℝ}
    (hCA : CA = ∑ j ∈ Finset.range (i - 2 + 1), (4 : ℝ) ^ (i - 2) * cA j)
    (hCB : CB = ∑ j ∈ Finset.range (i - 2 + 1), (4 : ℝ) ^ (i - 2) * cB j) :
    Kc i cA cB = 2 * (((i - 2 : ℕ) : ℝ) + 1) * (CA + CB + 1) := by
  rw [Kc, ← hCA, ← hCB]

/-! ## The pointwise bound

For `θ` in the open interval `(0, π/2)` the iterate `D_θ^i u` splits as
`D_θ^{i-2}(sin(2θ)² u'') + D_θ^{i-2}(2 cos(2θ) D_θ u)`; Leibniz plus Cauchy–Schwarz bounds the
square of each piece by a finite sum, and the coefficient bounds for the iterates of
`sin(2θ)²` and of `2 cos(2θ)` (together with the weight comparisons
`sin(2θ)⁴ sin(2θ)^{-γ} ≤ sin(2θ)^{-η}` and `sin(2θ)⁴ sin(2θ)^{-γ} ≤ sin(2θ)^{-γ}`) turn the
result into the bracket of the theorem. -/

private theorem pointwise_bound {cA cB : ℕ → ℝ}
    (hcA : ∀ j θ, (Work.Elliptic.Dth1Iter j (fun τ : ℝ => Real.sin (2 * τ) ^ 2) θ) ^ 2
      ≤ cA j * (Real.sin (2 * θ)) ^ 4)
    (hcB : ∀ j θ, (Work.Elliptic.Dth1Iter j (fun τ : ℝ => 2 * Real.cos (2 * τ)) θ) ^ 2 ≤ cB j)
    (hcApos : ∀ j, 0 ≤ cA j) (hcBpos : ∀ j, 0 ≤ cB j)
    (i : ℕ) (hi : 2 ≤ i) (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (u : ℝ → ℝ)
    (hu : Work.Elliptic.SmoothSlice u) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Elliptic.Dth1Iter i u θ) ^ 2 * sGam α θ ≤ Kc i cA cB *
        ((D2 u θ) ^ 2 * sEta θ
          + ∑ k ∈ Finset.range (i - 2),
              (Work.Elliptic.Dth1Iter (k + 1) (D2 u) θ) ^ 2 * sGam α θ
          + ∑ k ∈ Finset.range (i - 1),
              (Work.Elliptic.Dth1Iter (k + 1) u θ) ^ 2 * sGam α θ) := by
  intro θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hθU : θ ∈ SU := ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hsGam_nn : 0 ≤ sGam α θ := sGam_nonneg α hθI
  have hsEta_nn : 0 ≤ sEta θ := sEta_nonneg hθI
  -- the building blocks
  set Asq : ℝ → ℝ := fun τ : ℝ => Real.sin (2 * τ) ^ 2 with hAsq
  set Bc : ℝ → ℝ := fun τ : ℝ => 2 * Real.cos (2 * τ) with hBc
  set g : ℝ → ℝ := D2 u with hg
  set hh : ℝ → ℝ := Work.Elliptic.Dth1 u with hhh
  have hAsm : Work.Elliptic.SmoothSlice Asq := by rw [hAsq]; exact smoothSlice_sin_sq
  have hBsm : Work.Elliptic.SmoothSlice Bc := by rw [hBc]; exact smoothSlice_two_cos
  have hgsm : Work.Elliptic.SmoothSlice g := by rw [hg]; exact smoothSlice_D2 hu
  have hhsm : Work.Elliptic.SmoothSlice hh := by rw [hhh]; exact smoothSlice_Dth1 hu
  -- the second order identity, propagated through `D_θ^{i-2}`
  have hi_eq : i = (i - 2) + 2 := by omega
  have hev : Work.Elliptic.Dth1Iter 2 u =ᶠ[𝓝 θ] (fun τ : ℝ => Asq τ * g τ + Bc τ * hh τ) := by
    filter_upwards [isOpen_SU.mem_nhds hθU] with τ hτ
    rw [hAsq, hBc, hg, hhh]
    exact Dth1Iter_two_eq u hu hτ
  have hX : Work.Elliptic.Dth1Iter i u θ
      = Work.Elliptic.Dth1Iter (i - 2) (fun τ : ℝ => Asq τ * g τ) θ
        + Work.Elliptic.Dth1Iter (i - 2) (fun τ : ℝ => Bc τ * hh τ) θ := by
    have h1 : Work.Elliptic.Dth1Iter i u
        = Work.Elliptic.Dth1Iter (i - 2) (Work.Elliptic.Dth1Iter 2 u) := by
      conv_lhs => rw [show i = (i - 2) + 2 by omega]
      exact Dth1Iter_add_index (i - 2) 2 u
    rw [h1, Dth1Iter_eventuallyEq (i - 2) hev,
      Dth1Iter_add_of_smooth (i - 2) (smoothSlice_mul hAsm hgsm) (smoothSlice_mul hBsm hhsm) hθU]
  set X : ℝ := Work.Elliptic.Dth1Iter (i - 2) (fun τ : ℝ => Asq τ * g τ) θ with hXdef
  set Y : ℝ := Work.Elliptic.Dth1Iter (i - 2) (fun τ : ℝ => Bc τ * hh τ) θ with hYdef
  have hsq : (Work.Elliptic.Dth1Iter i u θ) ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := by
    rw [hX]
    nlinarith [sq_nonneg (X - Y)]
  -- the Leibniz + Cauchy–Schwarz bound for the two pieces
  set SA : ℝ := ∑ j ∈ Finset.range (i - 2 + 1), ((i - 2).choose j : ℝ) ^ 2 *
      ((Work.Elliptic.Dth1Iter j Asq θ) ^ 2 * (Work.Elliptic.Dth1Iter ((i - 2) - j) g θ) ^ 2)
    with hSA
  set SB : ℝ := ∑ j ∈ Finset.range (i - 2 + 1), ((i - 2).choose j : ℝ) ^ 2 *
      ((Work.Elliptic.Dth1Iter j Bc θ) ^ 2 * (Work.Elliptic.Dth1Iter ((i - 2) - j) hh θ) ^ 2)
    with hSB
  have hX2 : X ^ 2 ≤ (((i - 2 : ℕ) : ℝ) + 1) * SA := by
    rw [hXdef, hSA]
    exact Dth1Iter_mul_sq_le (i - 2) hAsm hgsm hθU
  have hY2 : Y ^ 2 ≤ (((i - 2 : ℕ) : ℝ) + 1) * SB := by
    rw [hYdef, hSB]
    exact Dth1Iter_mul_sq_le (i - 2) hBsm hhsm hθU
  -- the coefficient collections
  set CA : ℝ := ∑ j ∈ Finset.range (i - 2 + 1), (4 : ℝ) ^ (i - 2) * cA j with hCAdef
  set CB : ℝ := ∑ j ∈ Finset.range (i - 2 + 1), (4 : ℝ) ^ (i - 2) * cB j with hCBdef
  have hCAnn : 0 ≤ CA := by
    rw [hCAdef]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg (by norm_num) _) (hcApos j)
  have hCBnn : 0 ≤ CB := by
    rw [hCBdef]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg (by norm_num) _) (hcBpos j)
  -- the two families of terms
  set brA : ℝ := (g θ) ^ 2 * sEta θ
      + ∑ k ∈ Finset.range (i - 2), (Work.Elliptic.Dth1Iter (k + 1) g θ) ^ 2 * sGam α θ
    with hbrA
  set brB : ℝ := ∑ k ∈ Finset.range (i - 2 + 1),
      (Work.Elliptic.Dth1Iter k hh θ) ^ 2 * sGam α θ with hbrB
  have hbrAnn : 0 ≤ brA := by
    rw [hbrA]
    exact add_nonneg (mul_nonneg (sq_nonneg _) hsEta_nn)
      (Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) hsGam_nn)
  have hbrBnn : 0 ≤ brB := by
    rw [hbrB]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) hsGam_nn
  have hSAb : SA * sGam α θ ≤ CA * brA := by
    rw [hSA, hCAdef, hbrA]
    exact iterFamilyA_le (cA := cA) hcA hcApos (i - 2) α hα hα4 g hθ
  have hSBb : SB * sGam α θ ≤ CB * brB := by
    rw [hSB, hCBdef, hbrB]
    exact iterFamilyB_le (cB := cB) hcB hcBpos (i - 2) α hθ hh
  -- `D_θ^k (D_θ u) = D_θ^{k+1} u`
  have hbrB_eq : brB = ∑ k ∈ Finset.range (i - 1),
      (Work.Elliptic.Dth1Iter (k + 1) u θ) ^ 2 * sGam α θ := by
    rw [hbrB, show i - 2 + 1 = i - 1 by omega]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hcomp : Work.Elliptic.Dth1Iter k hh = Work.Elliptic.Dth1Iter (k + 1) u := by
      rw [hhh]
      exact (Dth1Iter_add_index k 1 u).symm
    rw [hcomp]
  -- the assembly
  have hXb : X ^ 2 * sGam α θ ≤ (((i - 2 : ℕ) : ℝ) + 1) * (CA * brA) := by
    calc X ^ 2 * sGam α θ ≤ ((((i - 2 : ℕ) : ℝ) + 1) * SA) * sGam α θ :=
          mul_le_mul_of_nonneg_right hX2 hsGam_nn
      _ = (((i - 2 : ℕ) : ℝ) + 1) * (SA * sGam α θ) := by ring
      _ ≤ (((i - 2 : ℕ) : ℝ) + 1) * (CA * brA) :=
          mul_le_mul_of_nonneg_left hSAb (by positivity)
  have hYb : Y ^ 2 * sGam α θ ≤ (((i - 2 : ℕ) : ℝ) + 1) * (CB * brB) := by
    calc Y ^ 2 * sGam α θ ≤ ((((i - 2 : ℕ) : ℝ) + 1) * SB) * sGam α θ :=
          mul_le_mul_of_nonneg_right hY2 hsGam_nn
      _ = (((i - 2 : ℕ) : ℝ) + 1) * (SB * sGam α θ) := by ring
      _ ≤ (((i - 2 : ℕ) : ℝ) + 1) * (CB * brB) :=
          mul_le_mul_of_nonneg_left hSBb (by positivity)
  have hstep : (Work.Elliptic.Dth1Iter i u θ) ^ 2 * sGam α θ
      ≤ 2 * (((i - 2 : ℕ) : ℝ) + 1) * (CA * brA + CB * brB) := by
    calc (Work.Elliptic.Dth1Iter i u θ) ^ 2 * sGam α θ
        ≤ (2 * X ^ 2 + 2 * Y ^ 2) * sGam α θ := mul_le_mul_of_nonneg_right hsq hsGam_nn
      _ = 2 * (X ^ 2 * sGam α θ) + 2 * (Y ^ 2 * sGam α θ) := by ring
      _ ≤ 2 * ((((i - 2 : ℕ) : ℝ) + 1) * (CA * brA))
            + 2 * ((((i - 2 : ℕ) : ℝ) + 1) * (CB * brB)) := by linarith [hXb, hYb]
      _ = 2 * (((i - 2 : ℕ) : ℝ) + 1) * (CA * brA + CB * brB) := by ring
  have hfin : 2 * (((i - 2 : ℕ) : ℝ) + 1) * (CA * brA + CB * brB)
      ≤ 2 * (((i - 2 : ℕ) : ℝ) + 1) * (CA + CB + 1) * (brA + brB) := by
    have h1 : 0 ≤ 2 * (((i - 2 : ℕ) : ℝ) + 1) := by positivity
    have h2 : CA * brA + CB * brB ≤ (CA + CB + 1) * (brA + brB) := by
      nlinarith [hCAnn, hCBnn, hbrAnn, hbrBnn]
    nlinarith [h1, h2]
  have hK : Kc i cA cB = 2 * (((i - 2 : ℕ) : ℝ) + 1) * (CA + CB + 1) :=
    Kc_eq i hCAdef hCBdef
  rw [hK]
  calc (Work.Elliptic.Dth1Iter i u θ) ^ 2 * sGam α θ
      ≤ 2 * (((i - 2 : ℕ) : ℝ) + 1) * (CA * brA + CB * brB) := hstep
    _ ≤ 2 * (((i - 2 : ℕ) : ℝ) + 1) * (CA + CB + 1) * (brA + brB) := hfin
    _ = 2 * (((i - 2 : ℕ) : ℝ) + 1) * (CA + CB + 1) *
          ((D2 u θ) ^ 2 * sEta θ
            + ∑ k ∈ Finset.range (i - 2),
                (Work.Elliptic.Dth1Iter (k + 1) (D2 u) θ) ^ 2 * sGam α θ
            + ∑ k ∈ Finset.range (i - 1),
                (Work.Elliptic.Dth1Iter (k + 1) u θ) ^ 2 * sGam α θ) := by
        rw [hbrB_eq, hbrA, hg]

theorem iter_le_of_lower_u : ∃ K : ℕ → ℝ, (∀ i, 0 < K i) ∧
    ∀ (i : ℕ), 2 ≤ i → ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.Elliptic.SmoothSlice u →
      MeasureTheory.IntegrableOn (fun θ => (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      (∀ k ∈ Finset.Icc 1 i, MeasureTheory.IntegrableOn
        (fun θ => (Work.Elliptic.Dth1Iter k (Work.FTS.EllipticEst.TT.D2 u) θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ) Work.Spaces.Iθ) →
      (∀ k ∈ Finset.Icc 1 i, MeasureTheory.IntegrableOn
        (fun θ => (Work.Elliptic.Dth1Iter k u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ) Work.Spaces.Iθ) →
      Work.FTS.EllipticEst.TT.Gγ α i u ≤ K i * (Work.FTS.EllipticEst.TT.Gη u
        + ∑ k ∈ Finset.Icc 1 (i - 2), Work.FTS.EllipticEst.TT.Gγ α k (Work.FTS.EllipticEst.TT.D2 u)
        + ∑ k ∈ Finset.Icc 1 (i - 1), Work.FTS.EllipticEst.TT.Gγ α k u) := by
  classical
  -- the two coefficient families
  have hA : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ,
      (Work.Elliptic.Dth1Iter j (fun τ : ℝ => Real.sin (2 * τ) ^ 2) θ) ^ 2
        ≤ C * (Real.sin (2 * θ)) ^ 4 := fun j => Dth1Iter_sin_sq_bdd j
  choose cA hcA using hA
  have hcApos : ∀ j, 0 ≤ cA j := fun j => le_of_lt (hcA j).1
  have hcAbdd : ∀ j θ, (Work.Elliptic.Dth1Iter j (fun τ : ℝ => Real.sin (2 * τ) ^ 2) θ) ^ 2
      ≤ cA j * (Real.sin (2 * θ)) ^ 4 := fun j θ => (hcA j).2 θ
  have hB : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ,
      (Work.Elliptic.Dth1Iter j (fun τ : ℝ => 2 * Real.cos (2 * τ)) θ) ^ 2 ≤ C := by
    intro j
    rcases Nat.eq_zero_or_pos j with h0 | hj
    · subst h0
      refine ⟨4, by norm_num, fun θ => ?_⟩
      have h2 : (2 * Real.cos (2 * θ)) ^ 2 ≤ 4 := by
        nlinarith [Real.abs_cos_le_one (2 * θ), sq_abs (Real.cos (2 * θ)),
          sq_nonneg (Real.cos (2 * θ)), abs_nonneg (Real.cos (2 * θ))]
      simpa using h2
    · obtain ⟨M, hMpos, hM⟩ := Work.FTS.EllipticEst.Dth1IterTwoCosBoundN j hj
      refine ⟨M ^ 2, sq_nonneg M, fun θ => ?_⟩
      have hs2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by
        nlinarith [Real.sin_le_one (2 * θ), Real.neg_one_le_sin (2 * θ)]
      have hle : |Work.Elliptic.Dth1Iter j (fun τ : ℝ => 2 * Real.cos (2 * τ)) θ| ≤ M := by
        calc |Work.Elliptic.Dth1Iter j (fun τ : ℝ => 2 * Real.cos (2 * τ)) θ|
            ≤ M * (Real.sin (2 * θ)) ^ 2 := hM θ
          _ ≤ M * 1 := mul_le_mul_of_nonneg_left hs2 hMpos.le
          _ = M := mul_one M
      calc (Work.Elliptic.Dth1Iter j (fun τ : ℝ => 2 * Real.cos (2 * τ)) θ) ^ 2
          = |Work.Elliptic.Dth1Iter j (fun τ : ℝ => 2 * Real.cos (2 * τ)) θ| ^ 2 :=
            (sq_abs _).symm
        _ ≤ M ^ 2 := by nlinarith [abs_nonneg (Work.Elliptic.Dth1Iter j
            (fun τ : ℝ => 2 * Real.cos (2 * τ)) θ), hle]
  choose cB hcB using hB
  have hcBpos : ∀ j, 0 ≤ cB j := fun j => (hcB j).1
  have hcBbdd : ∀ j θ, (Work.Elliptic.Dth1Iter j (fun τ : ℝ => 2 * Real.cos (2 * τ)) θ) ^ 2
      ≤ cB j := fun j θ => (hcB j).2 θ
  refine ⟨fun i => Kc i cA cB + 1, fun i => by
    have := Kc_nonneg hcApos hcBpos i
    linarith, ?_⟩
  intro i hi α u hα hα4 hsm hGint h2int h3int
  -- the a.e. pointwise bound, transported from the open interval to `Iθ`
  have hμ : volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) = volume.restrict Work.Spaces.Iθ :=
    Measure.restrict_congr_set (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)
  set F1 : ℝ → ℝ := fun θ => (D2 u θ) ^ 2 * sEta θ with hF1
  set F2 : ℝ → ℝ := fun θ => ∑ k ∈ Finset.Icc 1 (i - 2),
      (Work.Elliptic.Dth1Iter k (D2 u) θ) ^ 2 * sGam α θ with hF2
  set F3 : ℝ → ℝ := fun θ => ∑ k ∈ Finset.Icc 1 (i - 1),
      (Work.Elliptic.Dth1Iter k u θ) ^ 2 * sGam α θ with hF3
  set Rfun : ℝ → ℝ := F1 + F2 + F3 with hRfun
  have hRfun_range : ∀ θ : ℝ, Rfun θ = (D2 u θ) ^ 2 * sEta θ
      + ∑ k ∈ Finset.range (i - 2), (Work.Elliptic.Dth1Iter (k + 1) (D2 u) θ) ^ 2 * sGam α θ
      + ∑ k ∈ Finset.range (i - 1), (Work.Elliptic.Dth1Iter (k + 1) u θ) ^ 2 * sGam α θ := by
    intro θ
    simp only [hRfun, hF1, hF2, hF3, Pi.add_apply]
    rw [sum_Icc_one_eq_sum_range (i - 2)
          (fun k => (Work.Elliptic.Dth1Iter k (D2 u) θ) ^ 2 * sGam α θ),
      sum_Icc_one_eq_sum_range (i - 1)
          (fun k => (Work.Elliptic.Dth1Iter k u θ) ^ 2 * sGam α θ)]
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Elliptic.Dth1Iter i u θ) ^ 2 * sGam α θ ≤ (Kc i cA cB + 1) * Rfun θ := by
    rw [← hμ]
    refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hpt := pointwise_bound hcAbdd hcBbdd hcApos hcBpos i hi α hα hα4 u hsm θ hθ
    rw [hRfun_range θ]
    have hnn : 0 ≤ (D2 u θ) ^ 2 * sEta θ
        + ∑ k ∈ Finset.range (i - 2), (Work.Elliptic.Dth1Iter (k + 1) (D2 u) θ) ^ 2 * sGam α θ
        + ∑ k ∈ Finset.range (i - 1), (Work.Elliptic.Dth1Iter (k + 1) u θ) ^ 2 * sGam α θ := by
      refine add_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) (sEta_nonneg hθI)) ?_) ?_
      · exact Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (sGam_nonneg α hθI)
      · exact Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (sGam_nonneg α hθI)
    nlinarith [hpt, hnn]
  -- integrability of the pieces
  have h1i : IntegrableOn F1 Work.Spaces.Iθ := hGint
  have h2i : IntegrableOn F2 Work.Spaces.Iθ := by
    rw [hF2]
    exact integrable_finsetSum _ (fun k hk => h2int k (Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hk).1, le_trans (Finset.mem_Icc.mp hk).2 (Nat.sub_le i 2)⟩))
  have h3i : IntegrableOn F3 Work.Spaces.Iθ := by
    rw [hF3]
    exact integrable_finsetSum _ (fun k hk => h3int k (Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hk).1, le_trans (Finset.mem_Icc.mp hk).2 (Nat.sub_le i 1)⟩))
  have h12i : IntegrableOn (F1 + F2) Work.Spaces.Iθ := h1i.add h2i
  have hRi : IntegrableOn Rfun Work.Spaces.Iθ := by
    rw [hRfun]
    exact h12i.add h3i
  have hLHSi : IntegrableOn (fun θ => (Work.Elliptic.Dth1Iter i u θ) ^ 2 * sGam α θ)
      Work.Spaces.Iθ :=
    h3int i (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  -- integrate the pointwise bound
  have hmono : ∫ θ in Work.Spaces.Iθ, (Work.Elliptic.Dth1Iter i u θ) ^ 2 * sGam α θ
      ≤ ∫ θ in Work.Spaces.Iθ, (Kc i cA cB + 1) * Rfun θ := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hRi.const_mul _) hae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (sGam_nonneg α hθ)
  -- the integral of the bracket
  have hIntR : ∫ θ in Work.Spaces.Iθ, Rfun θ
      = Gη u + (∑ k ∈ Finset.Icc 1 (i - 2), Gγ α k (D2 u))
        + (∑ k ∈ Finset.Icc 1 (i - 1), Gγ α k u) := by
    have hIF1 : ∫ θ in Work.Spaces.Iθ, (F1 + F2) θ
        = (∫ θ in Work.Spaces.Iθ, F1 θ) + (∫ θ in Work.Spaces.Iθ, F2 θ) :=
      MeasureTheory.integral_add h1i h2i
    have hIF2 : ∫ θ in Work.Spaces.Iθ, ((F1 + F2) + F3) θ
        = (∫ θ in Work.Spaces.Iθ, (F1 + F2) θ) + (∫ θ in Work.Spaces.Iθ, F3 θ) :=
      MeasureTheory.integral_add h12i h3i
    have hSF1 : (∫ θ in Work.Spaces.Iθ, F1 θ) = Gη u := rfl
    have hSF2 : (∫ θ in Work.Spaces.Iθ, F2 θ)
        = ∑ k ∈ Finset.Icc 1 (i - 2), Gγ α k (D2 u) := by
      rw [hF2]
      exact MeasureTheory.integral_finsetSum _ (fun k hk => h2int k (Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hk).1, le_trans (Finset.mem_Icc.mp hk).2 (Nat.sub_le i 2)⟩))
    have hSF3 : (∫ θ in Work.Spaces.Iθ, F3 θ)
        = ∑ k ∈ Finset.Icc 1 (i - 1), Gγ α k u := by
      rw [hF3]
      exact MeasureTheory.integral_finsetSum _ (fun k hk => h3int k (Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hk).1, le_trans (Finset.mem_Icc.mp hk).2 (Nat.sub_le i 1)⟩))
    rw [hRfun, hIF2, hIF1, hSF1, hSF2, hSF3]
  calc Gγ α i u
      = ∫ θ in Work.Spaces.Iθ, (Work.Elliptic.Dth1Iter i u θ) ^ 2 * sGam α θ := rfl
    _ ≤ ∫ θ in Work.Spaces.Iθ, (Kc i cA cB + 1) * Rfun θ := hmono
    _ = (Kc i cA cB + 1) * ∫ θ in Work.Spaces.Iθ, Rfun θ :=
        MeasureTheory.integral_const_mul _ _
    _ = (Kc i cA cB + 1) * (Gη u + (∑ k ∈ Finset.Icc 1 (i - 2), Gγ α k (D2 u))
          + (∑ k ∈ Finset.Icc 1 (i - 1), Gγ α k u)) := by rw [hIntR]

end Work.FTS.EllipticEst.TT
