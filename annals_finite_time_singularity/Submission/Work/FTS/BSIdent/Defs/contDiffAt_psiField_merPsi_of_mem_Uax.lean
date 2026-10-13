import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Defs.contDiffAt_merPsi_slice
import Submission.Work.Cyl.FieldDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `C¹` regularity of the ansatz field `psiField (merPsi … · t)` on `Uax`

`Work.Cyl.psiField ψ = cylField (∂_zψ) (-(ψ/r) - ∂_rψ)` is built from the polar data
`(r,z) ↦ (ψ, ∂_rψ, ∂_zψ)`.  Hence, off the axis (`r > 0`), `psiField ψ` is one order smoother
than `ψ`:

* if `ψ` is `C³` at `(r,z)`, then `psiField ψ` is `C²` at the corresponding point of `ℝ³`
  (`Work.FTS.FireFix.Clauses.psiField_contDiffAt_two`),
* if `ψ` is `C²` at `(r,z)`, then `psiField ψ` is `C¹` — the statement proved here
  (`psiField_contDiffAt_one`).

The second fact is what the Biot–Savart identification needs: the meridian slice of `merPsi` is
`C²` off the degenerate set `{r = 0} ∪ {z = 0}` (`contDiffAt_merPsi_slice`, from the `C²` hypothesis
`hsm` on the profile), and `Uax` is exactly the set on which the point coordinates give
`r > 0`, `z ≠ 0`.  Combining the two gives the `C¹`-clause of the geometric bundle of the ansatz
field on `Uax`.

The ingredient of the `C¹`-from-`C²` transfer is the pair
`contDiffAt_pdZ_uncurry_one`, `contDiffAt_pdR_uncurry_one`: the partial derivatives
`(r,z) ↦ ∂_zψ`, `(r,z) ↦ ∂_rψ` are `C¹` as soon as `ψ` is `C²`, because each of them is the
first derivative `fderiv ℝ (uncurry ψ)` evaluated in a fixed direction
(`Work.Cyl.fderiv_prod_apply_snd`, `Work.Cyl.fderiv_prod_apply_fst`) and `fderiv` of a `C²`
function is `C¹` (`ContDiffAt.fderiv_right`).
-/

set_option autoImplicit false

namespace Work.FTS.BSIdent.Defs

/-! ## The partial derivatives of a `C²` stream function -/

/-- The axial partial derivative `(r,z) ↦ ∂_zψ(r,z)` of a `C²` stream function is `C¹`. -/
theorem contDiffAt_pdZ_uncurry_one {ψ : ℝ → ℝ → ℝ} {r z : ℝ}
    (hψ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z)) :
    ContDiffAt ℝ 1 (fun p : ℝ × ℝ => Work.Cyl.pdZ ψ p.1 p.2) (r, z) := by
  -- `ψ` is differentiable on a neighbourhood of `(r,z)`
  have hev : ∀ᶠ p : ℝ × ℝ in nhds (r, z),
      DifferentiableAt ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p :=
    (hψ.eventually (by norm_num)).mono fun p hp => hp.differentiableAt (by norm_num)
  -- `fderiv ℝ ψ` is `C¹` at `(r,z)`
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ (fun p : ℝ × ℝ => ψ p.1 p.2)) (r, z) :=
    hψ.fderiv_right (m := 1) (by norm_num)
  -- evaluating it in the fixed direction `(0,1)` preserves smoothness
  have hΦ : ContDiffAt ℝ 1
      (fun p : ℝ × ℝ => (fderiv ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p) (0, 1)) (r, z) :=
    hfd.clm_apply contDiffAt_const
  -- and on a neighbourhood it agrees with `∂_zψ`
  refine hΦ.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  exact (Work.Cyl.fderiv_prod_apply_snd ψ p.1 p.2 hp).symm

/-- The radial partial derivative `(r,z) ↦ ∂_rψ(r,z)` of a `C²` stream function is `C¹`. -/
theorem contDiffAt_pdR_uncurry_one {ψ : ℝ → ℝ → ℝ} {r z : ℝ}
    (hψ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z)) :
    ContDiffAt ℝ 1 (fun p : ℝ × ℝ => Work.Cyl.pdR ψ p.1 p.2) (r, z) := by
  have hev : ∀ᶠ p : ℝ × ℝ in nhds (r, z),
      DifferentiableAt ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p :=
    (hψ.eventually (by norm_num)).mono fun p hp => hp.differentiableAt (by norm_num)
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ (fun p : ℝ × ℝ => ψ p.1 p.2)) (r, z) :=
    hψ.fderiv_right (m := 1) (by norm_num)
  have hΦ : ContDiffAt ℝ 1
      (fun p : ℝ × ℝ => (fderiv ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p) (1, 0)) (r, z) :=
    hfd.clm_apply contDiffAt_const
  refine hΦ.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  exact (Work.Cyl.fderiv_prod_apply_fst ψ p.1 p.2 hp).symm

/-! ## `psiField` of a `C²` stream function is `C¹` off the axis -/

/-- `x ↦ radial x = √(x₀² + x₁²)` is `C¹` at `x` provided `radial x > 0`. -/
theorem contDiffAt_radial_one {x : Work.FTS.BSIdent.R3} (hx : 0 < Work.Cyl.radial x) :
    ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 => Work.Cyl.radial y) x := by
  have hsq : ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 => Work.Cyl.radSq y) x := by
    show ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 => y 0 ^ 2 + y 1 ^ 2) x
    fun_prop
  have hpos : 0 < Work.Cyl.radSq x := Real.sqrt_pos.mp hx
  exact (Real.contDiffAt_sqrt (ne_of_gt hpos)).comp x hsq

/-- **`psiField` of a `C²` stream function is `C¹` off the axis.** -/
theorem psiField_contDiffAt_one {ψ : ℝ → ℝ → ℝ} {x : Work.FTS.BSIdent.R3}
    (hx : 0 < Work.Cyl.radial x)
    (hψ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (Work.Cyl.radial x, Work.Cyl.axial x)) :
    ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 => Work.Cyl.psiField ψ y) x := by
  have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hx
  -- the polar data are `C¹` at `x`
  have hrad := contDiffAt_radial_one hx
  have hax : ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 => Work.Cyl.axial y) x := by
    show ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 => y 2) x
    fun_prop
  have hP : ContDiffAt ℝ 1
      (fun y : Work.FTS.BSIdent.R3 => (Work.Cyl.radial y, Work.Cyl.axial y)) x :=
    hrad.prodMk hax
  -- the profile data are `C¹` at `(radial x, axial x)`
  have hpdZ : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => Work.Cyl.pdZ ψ p.1 p.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) := contDiffAt_pdZ_uncurry_one hψ
  have hpdR : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => Work.Cyl.pdR ψ p.1 p.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) := contDiffAt_pdR_uncurry_one hψ
  have hψ1 : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => ψ p.1 p.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) := hψ.of_le (by norm_num)
  have hpdZc : ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 =>
      Work.Cyl.pdZ ψ (Work.Cyl.radial y) (Work.Cyl.axial y)) x := by
    convert hpdZ.comp x hP using 1
    ext y; rfl
  have hpdRc : ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 =>
      Work.Cyl.pdR ψ (Work.Cyl.radial y) (Work.Cyl.axial y)) x := by
    convert hpdR.comp x hP using 1
    ext y; rfl
  have hψc : ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 =>
      ψ (Work.Cyl.radial y) (Work.Cyl.axial y)) x := by
    convert hψ1.comp x hP using 1
    ext y; rfl
  -- the two components of `cylField`, as functions of `x`
  have hA : ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 =>
      Work.Cyl.pdZ ψ (Work.Cyl.radial y) (Work.Cyl.axial y) / Work.Cyl.radial y) x :=
    hpdZc.div hrad hrne
  have hB : ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 =>
      -(ψ (Work.Cyl.radial y) (Work.Cyl.axial y) / Work.Cyl.radial y)
        - Work.Cyl.pdR ψ (Work.Cyl.radial y) (Work.Cyl.axial y)) x :=
    (hψc.div hrad hrne).neg.sub hpdRc
  have hrv : ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 => Work.Cyl.radialVec y) x := by
    rw [show Work.Cyl.radialVec = fun y : Work.FTS.BSIdent.R3 =>
        (y 0) • Work.Cyl.e0 + (y 1) • Work.Cyl.e1 from by
      funext y; ext i; fin_cases i <;>
        simp [Work.Cyl.radialVec, Work.Cyl.e0, Work.Cyl.e1, FiniteTimeSingularity.e]]
    fun_prop
  have hmain : ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 =>
      (Work.Cyl.pdZ ψ (Work.Cyl.radial y) (Work.Cyl.axial y) / Work.Cyl.radial y)
          • Work.Cyl.radialVec y
        + (-(ψ (Work.Cyl.radial y) (Work.Cyl.axial y) / Work.Cyl.radial y)
            - Work.Cyl.pdR ψ (Work.Cyl.radial y) (Work.Cyl.axial y)) • Work.Cyl.eZ) x :=
    (hA.smul hrv).add (hB.smul (contDiffAt_const (c := Work.Cyl.eZ)))
  refine hmain.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext y
  simp only [Work.Cyl.psiField, Work.Cyl.cylField]

/-! ## The `C¹` clause of the ansatz bundle on `Uax` -/

theorem contDiffAt_psiField_merPsi_of_mem_Uax (α : ℝ) (A B : ℝ → ℝ)
    (Φ : Work.FTS.BSIdent.Fam) (C : Physical.PhysClock) (t : ℝ)
    (hB : 0 < B (Physical.clockInv C t))
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < Real.pi / 2 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    {x : Work.FTS.BSIdent.R3} (hx : x ∈ Work.FTS.BSIdent.Uax) :
    ContDiffAt ℝ 1
      (Work.Cyl.psiField (fun r z => Work.FTS.BSIdent.merPsi α A B Φ C r z t)) x := by
  have hr : 0 < Work.Cyl.radial x := Work.FTS.BSIdent.radial_pos_of_mem_Uax hx
  have hz : Work.Cyl.axial x ≠ 0 := Work.FTS.BSIdent.axial_ne_zero_of_mem_Uax hx
  exact psiField_contDiffAt_one hr
    (Work.FTS.BSIdent.Defs.contDiffAt_merPsi_slice α A B Φ C t hB hsm hr hz)

end Work.FTS.BSIdent.Defs
