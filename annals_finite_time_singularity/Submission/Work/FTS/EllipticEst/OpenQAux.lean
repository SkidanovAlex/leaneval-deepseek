/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary lemmas for the open-quadrant `H^k` estimate `|F_*(F)·sin 2θ|_{H^k} ≤ C_k |F|_{H^k}`

This module collects the auxiliary lemmas of the proof of
`Work.FTS.EllipticEst.Fstar_Hk_le_open` which do not depend on the deferred analytic cores of
the chapter (`moment_relation`, `integrableOn_slice_l2`, `integrableOn_box_of_slice`,
`PsiInt_sq_mul_w_le_open`):

* `SmoothOpen.aesm_slice_mul` : a.e. strong measurability of the angular slice of
  `D_z^j F · φ` for a continuous `φ`;
* the radial iterates `radIter φ j` of a function of `z` alone, with the product rule
  `D_z^j (φ(z)·χ(θ)) = (radIter φ j)(z)·χ(θ)` (`DzIter_radial_mul_ang`).  This is the
  unconditional (`deriv`-junk-tolerant) form of "`D_z` sees only the radial factor";
* `integrableOn_DzIter_mul_sinCos2` : the angular moment of `D_z^j F` is honest, i.e.
  `θ ↦ D_z^j F z θ · sinθcos²θ` is integrable on `Iθ` for every `z > 0`, as soon as
  `F ∈ ℋ^k` — the `L¹(sinθcos²θ)` companion of the `L²`-slice information in `HkMem`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.OpenQAng

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {F G : ℝ → ℝ → ℝ}

/-! ## Measurability of the slices of `D_z^j F · φ` -/

/-- The angular slice of `D_z^j F · φ`, for a continuous `φ`, is a.e. strongly measurable
whenever `F` is `C^∞` on the open quadrant. -/
theorem SmoothOpen.aesm_slice_mul (hF : SmoothOpen F) (j : ℕ) {z : ℝ} (hz : 0 < z)
    (φ : ℝ → ℝ) (hφ : Continuous φ) :
    AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.DzIter j F z θ * φ θ)
      (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Spaces.DzIter j F p.1 p.2 * φ p.2)
    ((hF.DzIter j).continuousOn.mul (hφ.comp continuous_snd).continuousOn) hz

/-! ## Radial iterates: `D_z` on a product of a radial and an angular factor -/

/-- **The radial iterate** `radIter φ j z := (D_z^j (φ(·)))(z)`: the `j`-th `D_z`-derivative of
a function of `z` alone, evaluated at `z` (the auxiliary angular argument of the curried
representative is irrelevant, so it is fixed to `0`). -/
def radIter (φ : ℝ → ℝ) (j : ℕ) (z : ℝ) : ℝ :=
  Work.Spaces.DzIter j (fun z _ : ℝ => φ z) z 0

@[simp] theorem radIter_zero (φ : ℝ → ℝ) (z : ℝ) : radIter φ 0 z = φ z := rfl

/-- The recursion `radIter φ (j+1) z = z·(radIter φ j)'(z)`. -/
theorem radIter_succ (φ : ℝ → ℝ) (j : ℕ) (z : ℝ) :
    radIter φ (j + 1) z = z * deriv (radIter φ j) z := by
  show Work.Spaces.DzIter (j + 1) (fun z _ : ℝ => φ z) z 0 = _
  rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
  rfl

/-- A `D_z`-iterate of a function of `z` alone does not depend on the angle. -/
theorem DzIter_z_indep (φ : ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z _ : ℝ => φ z) z θ = radIter φ j z := by
  induction j generalizing z with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz, radIter_succ]
      congr 1
      exact Filter.EventuallyEq.deriv_eq (Eventually.of_forall fun z' => ih z')

/-- **`D_z` ignores an angular factor**: `D_z^j (φ(z)·χ(θ)) = (radIter φ j)(z)·χ(θ)`.  The
statement is unconditional in the differentiability of `φ`: Lean's `deriv` is junk-tolerant and
both sides carry the same junk at the points where `φ` fails to be differentiable. -/
theorem DzIter_radial_mul_ang (φ : ℝ → ℝ) (χ : ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z θ => φ z * χ θ) z θ = radIter φ j z * χ θ := by
  induction j generalizing z with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      have hfun : (fun z' : ℝ => Work.Spaces.DzIter n (fun z θ => φ z * χ θ) z' θ)
          = fun z' : ℝ => radIter φ n z' * χ θ := by
        funext z'
        exact ih z'
      rw [hfun]
      have hderiv : deriv (fun z' : ℝ => radIter φ n z' * χ θ) z
          = deriv (radIter φ n) z * χ θ := by
        rw [show (fun z' : ℝ => radIter φ n z' * χ θ)
            = fun z' : ℝ => χ θ * radIter φ n z' from by
          funext z'; ring]
        rw [deriv_const_mul_field (χ θ) (v := fun z' => radIter φ n z'), mul_comm]
      rw [hderiv, radIter_succ]
      ring

/-- The pure `D_z`-iterate of `F_*(F)(z)·sin 2θ`. -/
theorem DzIter_fstarSin_eq (R : ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z θ => R z * Real.sin (2 * θ)) z θ
      = radIter R j z * Real.sin (2 * θ) :=
  DzIter_radial_mul_ang (fun z => R z) (fun θ => Real.sin (2 * θ)) j z θ

/-- The mixed derivative `D_z^j D_θ^i` of `F_*(F)(z)·sin 2θ` is
`(D_z^j F_*)(z)·(D_θ^i sin 2θ)`. -/
theorem mixed_fstarSin_eq (R : ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => R z * Real.sin (2 * θ)) z θ
      = radIter R j z * sinProf i θ := by
  rw [Work.Spaces.mixed,
    DthIter_radial_mul (fun z => R z) (fun z θ => Real.sin (2 * θ)) i]
  have hfun : (fun z θ => R z * Work.Spaces.DthIter i (fun z θ => Real.sin (2 * θ)) z θ)
      = fun z θ => R z * sinProf i θ := by
    funext z θ
    rw [DthIter_sin_eq_sinProf]
  rw [hfun, DzIter_radial_mul_ang]

/-! ## The angular moment of `D_z^j F` is honest -/

/-- `sinθcos²θ` vanishes at the angles where `sin 2θ` does. -/
theorem sinCos2_eq_zero_of_sin_two_eq_zero {θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    Work.Elliptic.sinCos2 θ = 0 := by
  have h2 : Real.sin θ * Real.cos θ = 0 := by
    have h3 : 2 * (Real.sin θ * Real.cos θ) = 0 := by
      rw [← h, Real.sin_two_mul]; ring
    exact (mul_eq_zero.mp h3).resolve_left (by norm_num)
  rcases mul_eq_zero.mp h2 with h3 | h3
  · simp [Work.Elliptic.sinCos2, h3]
  · simp [Work.Elliptic.sinCos2, h3]

/-- **`θ ↦ D_z^j F z θ · sinθcos²θ` is integrable on `Iθ`** for every `z > 0` and `j ≤ k`,
as soon as `F ∈ ℋ^k`: AM–GM against the weighted `L²`-slice information of `HkMem`, using
`|sinθcos²θ|·sin(2θ)^{η/2} ≤ 1` on `Iθ`. -/
theorem integrableOn_DzIter_mul_sinCos2 (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ : ℝ => Work.Spaces.DzIter j F z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (le_of_lt hz)
  have hsq := integrableOn_zSummand α k hF hmem j hj hzI
  have hwpos : 0 < Work.Spaces.w z := by
    rw [Work.Spaces.w]
    exact div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)
  -- the auxiliary angular function `ψ = sinθcos²θ · sin(2θ)^{η/2} / w z`
  set ψ : ℝ → ℝ := fun θ => Work.Elliptic.sinCos2 θ
    * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) / Work.Spaces.w z with hψdef
  -- (1) `|ψ| ≤ 1/w z` on `Iθ`
  have hψ : ∀ θ ∈ Work.Spaces.Iθ, |ψ θ| ≤ 1 / Work.Spaces.w z := by
    intro θ hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) := FstarHkOpen.sin_two_nonneg hθ
    have h3 : 0 ≤ (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_nonneg hs0 _
    have hkey : |Work.Elliptic.sinCos2 θ| * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ 1 := by
      have h1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
        Real.rpow_le_one hs0 (FstarHkOpen.sin_two_le_one θ) (by rw [Work.Spaces.eta]; norm_num)
      have h2 : |Work.Elliptic.sinCos2 θ| ≤ 1 := FstarHkOpen.abs_sinCos2_le_one hθ
      nlinarith [h1, h2, h3, abs_nonneg (Work.Elliptic.sinCos2 θ)]
    rw [hψdef, abs_div, abs_mul, abs_of_nonneg h3, abs_of_pos hwpos]
    rw [div_le_div_iff_of_pos_right hwpos]
    exact hkey
  -- (2) `D_z^j F z θ · sinθcos²θ = (D_z^j F z θ · W θ) · ψ θ`
  have hid : ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.DzIter j F z θ * Work.Elliptic.sinCos2 θ
      = (Work.Spaces.DzIter j F z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) * ψ θ := by
    intro θ hθ
    by_cases hs : Real.sin (2 * θ) = 0
    · have hc : Work.Elliptic.sinCos2 θ = 0 := sinCos2_eq_zero_of_sin_two_eq_zero hs
      have hψ0 : ψ θ = 0 := by
        show Work.Elliptic.sinCos2 θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
          / Work.Spaces.w z = 0
        rw [hc, zero_mul, zero_div]
      rw [hc, mul_zero, hψ0, mul_zero]
    · have hspos : 0 < Real.sin (2 * θ) :=
        lt_of_le_of_ne (FstarHkOpen.sin_two_nonneg hθ) (Ne.symm hs)
      have hsne : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≠ 0 :=
        (Real.rpow_pos_of_pos hspos _).ne'
      have hwne : Work.Spaces.w z ≠ 0 := hwpos.ne'
      rw [hψdef, div_eq_mul_inv, div_eq_mul_inv]
      field_simp
      try ring
  -- (3) pointwise AM–GM bound
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      ‖Work.Spaces.DzIter j F z θ * Work.Elliptic.sinCos2 θ‖
        ≤ (1 / 2) * (Work.Spaces.DzIter j F z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          + (1 / 2) * (1 / Work.Spaces.w z) ^ 2 := by
    intro θ hθ
    rw [hid θ hθ, Real.norm_eq_abs, abs_mul]
    have hAM := mul_le_mul_of_nonneg_left (hψ θ hθ) (abs_nonneg (Work.Spaces.DzIter j F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
    refine le_trans hAM ?_
    have hsq : |Work.Spaces.DzIter j F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| ^ 2
        = (Work.Spaces.DzIter j F z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := sq_abs _
    nlinarith [sq_nonneg (|Work.Spaces.DzIter j F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|
        - 1 / Work.Spaces.w z), hsq]
  refine Integrable.mono'
    (g := fun θ : ℝ => (1 / 2) * (Work.Spaces.DzIter j F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      + (1 / 2) * (1 / Work.Spaces.w z) ^ 2)
    ?_ (hF.aesm_slice_mul j hz _ (by unfold Work.Elliptic.sinCos2; fun_prop)) ?_
  · refine (hsq.const_mul (1 / 2)).add (integrableOn_const (s := Work.Spaces.Iθ)
      (C := (1 / 2) * (1 / Work.Spaces.w z) ^ 2) ?_)
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  · rw [ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from by
      rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
    exact Eventually.of_forall fun θ hθ => hpt θ hθ

/-! ## The radial moments `B_j = F_*(D_z^j F)` -/

/-- **The `j`-th radial moment of `F`**: `Bmom F j z = ∫_θ D_z^j F(z,θ)·sinθcos²θ dθ`.  For
`j = 0` it is the angular moment `F_*(F)`, and its `radIter`-iterate `(D_z^j F_*)(z)` is the
coefficient of `sin 2θ` in `D_z^j (F_*(F)(z)·sin 2θ)` (`DzIter_fstarSin_eq`,
`GzIter_PsiInt_mul`). -/
def Bmom (F : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) : ℝ := PsiInt F j z

theorem Bmom_zero (F : ℝ → ℝ → ℝ) (z : ℝ) : Bmom F 0 z = Work.Elliptic.Fstar F z := by
  simp only [Bmom, Work.FTS.EllipticEst.PsiInt, Work.Spaces.DzIter_zero,
    Work.Elliptic.Fstar]

theorem Bmom_eq_Fstar_DzIter (F : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) :
    Bmom F j z = Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z := by
  simp only [Bmom, Work.FTS.EllipticEst.PsiInt, Work.Elliptic.Fstar]

end Work.FTS.EllipticEst
