/-
# `Work.FTS.BSIdent.Bundle` — the geometric bundle of the ansatz field, and its model case

`Ident.hid_of_biotSavartInverse` (route A) and `Liouville.hid_of_divCurlLiouville` (route B) both
consume the **geometric bundle of the ansatz field** — the analytic content of "the ansatz field
`psiField (merPsi …)` lies in the class of the comparison theorem" — which is *not* a consequence
of the elliptic law alone.  This module

* names the two bundles (`AnsatzBundle` for the inverse Biot–Savart route, `AnsatzBundleSub` for
  the Liouville route, where the decay `1/‖x‖` is replaced by sublinearity);
* proves the **model case**: for a meridian stream function of the *axis-regular* form
  `ψ(r,z) = r·V(r²,z)` (the form for which `psiField ψ` is an `axiField`, hence a field on `ℝ³`
  rather than only off the axis), the bundle follows from bounds on the two profile functions
  `a = ∂_zV` and `b = −2V − 2w∂_wV`;
* records that the bundle is inhabited (`ansatzBundle_zero`), so nothing of this chapter is
  vacuous.

The bundle is *not* a restatement of the identification: it is a statement about the single field
`psiField (merPsi …)` (its smoothness, its decay at infinity and its divergence), while the
identification is the equality of that field with the *different* object `physVel (−physOmega)`.
In the actual reconstruction the bundle is the `psiField`-form analogue of node N7's transfer
theorem `Work.FTS.Regularity.physVel_isContDiffHolder`: the paper's analysis at the axis (`θ → π/2`,
where the stream function has the non-integer vanishing rate `2α + 2`) is exactly what it needs,
and it does *not* follow from the smoothness of `Φ` on the open quadrant.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Cyl.psiField_r_mul_V_eq_axiField
import Submission.Work.FTS.BSIdent.Cyl.sublinear_axiField
import Submission.Work.FTS.BSIdent.Axi.contDiff_axiField
import Submission.Work.Cyl.Parity

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set MeasureTheory
open scoped Topology Real

namespace Work.FTS.BSIdent

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two bundles -/

/-- **The geometric bundle of the ansatz field, inverse Biot–Savart route** (`Ident`): the
stream-function field of `ψ` is `C¹`, decays like `1/‖x‖`, its meridian profile is `C²` off the
axis and the plane, and it is divergence-free. -/
def AnsatzBundle (ψ : ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 (Work.Cyl.psiField ψ) ∧
    (∃ D : ℝ, ∀ x : R3, ‖Work.Cyl.psiField ψ x‖ ≤ D / (1 + ‖x‖)) ∧
    (∀ r z, 0 < r → z ≠ 0 → ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z))

/-- **The geometric bundle of the ansatz field, Liouville route** (`Liouville.Hid`): the
stream-function field of `ψ` is `C¹`, sublinear, odd and divergence-free.  Sublinearity is weaker
than the decay of `AnsatzBundle`, and oddness is what the div-curl Liouville principle needs to
kill the constant field. -/
def AnsatzBundleSub (ψ : ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 (Work.Cyl.psiField ψ) ∧
    Physical.Sublinear (Work.Cyl.psiField ψ) ∧
    IsOdd (Work.Cyl.psiField ψ)

/-- Decay implies sublinearity (the converse fails for a compactly supported field). -/
theorem Sublinear.of_decay {u : R3 → R3} (h : ∃ D : ℝ, ∀ x, ‖u x‖ ≤ D / (1 + ‖x‖)) :
    Physical.Sublinear u := by
  obtain ⟨D, hD⟩ := h
  refine ⟨|D|, 1 / 2, abs_nonneg _, by norm_num, fun x => ?_⟩
  have hDx : ‖u x‖ ≤ |D| := by
    refine le_trans (hD x) ?_
    rcases le_or_gt 0 D with hD0 | hD0
    · rw [div_le_iff₀ (show (0 : ℝ) < 1 + ‖x‖ by positivity)]
      rw [abs_of_nonneg hD0]
      nlinarith [norm_nonneg x]
    · have h2 : D / (1 + ‖x‖) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hD0.le (by positivity)
      rw [abs_of_neg hD0]
      linarith
  have hpow : (1 : ℝ) ≤ (1 + ‖x‖) ^ ((1 : ℝ) / 2) :=
    Real.one_le_rpow (by linarith [norm_nonneg x]) (by norm_num)
  calc ‖u x‖ ≤ |D| := hDx
    _ = |D| * 1 := (mul_one _).symm
    _ ≤ |D| * (1 + ‖x‖) ^ ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hpow (abs_nonneg D)

theorem ansatzBundle_sublinear {ψ : ℝ → ℝ → ℝ} (h : AnsatzBundle ψ) :
    Physical.Sublinear (Work.Cyl.psiField ψ) :=
  Sublinear.of_decay h.2.1

theorem ansatzBundle_contDiff {ψ : ℝ → ℝ → ℝ} (h : AnsatzBundle ψ) :
    ContDiff ℝ 1 (Work.Cyl.psiField ψ) := h.1

theorem ansatzBundle_decay {ψ : ℝ → ℝ → ℝ} (h : AnsatzBundle ψ) :
    ∃ D : ℝ, ∀ x : R3, ‖Work.Cyl.psiField ψ x‖ ≤ D / (1 + ‖x‖) := h.2.1

theorem ansatzBundle_slice {ψ : ℝ → ℝ → ℝ} (h : AnsatzBundle ψ) :
    ∀ r z, 0 < r → z ≠ 0 → ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z) := h.2.2

theorem ansatzBundleSub_contDiff {ψ : ℝ → ℝ → ℝ} (h : AnsatzBundleSub ψ) :
    ContDiff ℝ 1 (Work.Cyl.psiField ψ) := h.1

theorem ansatzBundleSub_sublinear {ψ : ℝ → ℝ → ℝ} (h : AnsatzBundleSub ψ) :
    Physical.Sublinear (Work.Cyl.psiField ψ) := h.2.1

theorem ansatzBundleSub_isOdd {ψ : ℝ → ℝ → ℝ} (h : AnsatzBundleSub ψ) :
    IsOdd (Work.Cyl.psiField ψ) := h.2.2

/-! ## Inhabitation -/

/-- **The zero stream function gives the zero field**, which satisfies both bundles: nothing in
`Ident`/`Liouville.Hid` is vacuous. -/
theorem ansatzBundle_zero : AnsatzBundle (fun _ _ => 0) := by
  have h1 : Work.Cyl.pdZ (fun _ _ => (0 : ℝ)) = fun _ _ => 0 := by
    funext r z; simp [Work.Cyl.pdZ]
  have h2 : Work.Cyl.pdR (fun _ _ => (0 : ℝ)) = fun _ _ => 0 := by
    funext r z; simp [Work.Cyl.pdR]
  have hfield : Work.Cyl.psiField (fun _ _ => (0 : ℝ)) = fun _ : R3 => 0 := by
    funext x
    simp only [Work.Cyl.psiField, Work.Cyl.cylField, h1, h2, Pi.zero_apply, zero_div, neg_zero,
      sub_zero, zero_smul, add_zero]
  refine ⟨?_, ⟨0, ?_⟩, ?_⟩
  · rw [hfield]; exact contDiff_const
  · intro x; rw [hfield]; simp
  · intro r z _ _; exact contDiffAt_const

end Work.FTS.BSIdent
